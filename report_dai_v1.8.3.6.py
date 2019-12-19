#!/usr/bin/env python

# ----------------------------------------------------------------------------------------------
# Modules
# ----------------------------------------------------------------------------------------------
from __future__ import print_function, division
import argparse
import calendar
import base64
import io
import json
import logging
import os
import pandas as pd
import re
import sqlite3
import sys
import tempfile
import time
import xml.dom.minidom as minidom
from collections import Counter, defaultdict, OrderedDict
from datetime import datetime
from termcolor import colored
from xml.etree import ElementTree

try:
    # For Python 3.0 and later
    from urllib.parse import urlparse, parse_qs
    from urllib.request import urlopen
except ImportError:
    # Fall back to Python 2's urllib2
    from urlparse import urlparse, parse_qs, parse_qsl
    from urllib2 import urlopen

__version__ = "1.8.3.6"


# ----------------------------------------------------------------------------------------------
# Constants
# ----------------------------------------------------------------------------------------------
PASS = "<font color='lime'>(PASS) </font>"
FAIL = "<font color='red'>(FAIL) </font>"
SKIP = "<font color='yellow'>(SKIP) </font>"
FOUND = "<font color='lime'>Present</font>"
MISSING = "<font color='red'>Missing</font>"


class SimpleGrep:
    """
    A set of regular expressions used to parse certain Dynamic Ad Insertion events from
    the AP player.log.
    """

    # Adaptive Player Device Information
    _regex_device_info = re.compile(
        r'^\d{4}/\d{2}/\d{2}\s\d{2}:\d{2}:\d{2}.*WeatherHelper:'
        r'(?=.*ip addr: = (?P<ip>\b\d{1,3}\.\d{1,3}\.\d{1,3}\.\d{1,3}\b))?'
        r'(?=.*deviceType = (?P<device_type>.*$))?'
        r'(?=.*devicePlatform = (?P<device_platform>.*$))?'
        r'(?=.*deviceModel = (?P<device_model>.*$))?'
    )

    # Adaptive Player's Quantum Virtual Timeline (QVT)
    _regex_qvt_parsed = re.compile(
        r'^(?=(?P<logline>.*AdaptiveVideo Timeline loaded:.*$))'
        r'^(?=.*AdaptiveVideo Timeline loaded: (?P<data>{".*ad_info.*ad_breaks.*}(\s|$)))'
    )

    # Adaptive Player's Ad Request
    _regex_ad_request = re.compile(
        r'^(?=(?P<logline>.*$))'
        r'^(?=(?P<timestamp>\d{4}/\d{2}/\d{2}\s\d{2}:\d{2}:\d{2}))'
        r'^(?=.*FWAdPod adRequest url: (?P<url>.*$))'
    )

    # FreeWheel's SmartXML Ad Response
    _regex_xml_response = re.compile(
        r'^(?=(?P<logline>.*FWAdPod response body.*$))'
        r'^(?=(?P<timestamp>\d{4}/\d{2}/\d{2}\s\d{2}:\d{2}:\d{2}))'
        r'^(?=.*FWAdPod response body = (?P<xml>.*$))'
    )

    # Adaptive Player's Video Group Impression (Internal)
    _regex_avg_beacon = re.compile(
        r'^(?=(?P<logline>.*firing avg beaconEvent.*$))'
        r'(?=.*firing avg beaconEvent (?P<beacon_event>\w+) at)'
        r'(?=.*"adBreakId":(?P<slot_id>\d+))'
        r'(?=.*"contentTime":(?P<time_position>\d+))'
        r'(?=.*"utcTime":(?P<utc>\d+))?'
        r'(?=.*"adId":"(?P<ad_id>\d+))?.*$'
    )

    # FreeWheel and 3rd Party Impressions (External)
    _regex_fw_beacon = re.compile(
        r'^(?=(?P<logline>^.*FWAdPod \w+ firing \w+ \w+.*$))'
        r'(?=.*FWAdPod \w+ firing \w+ \w+:(?P<beacon_event>\w+))'
        r'(?=.*url: (?P<url>.*$))'
        r'(?=.*&t=(?P<utc>\d{10}))?'
        r'(?=.*&adid=(?P<ad_id>\d+))?'
        r'(?=.*&cn=(?P<impression>\w+))?'
        r'(?=.*&tpos=(?P<time_position>\d+))?'
        r'(?=.*&slid=(?P<slot_id>\d+))?.*$'
    )

    # FreeWheel and 3rd Party Tracking Callbacks (Response)
    _regex_fw_callback = re.compile(
        r'^(?=(?P<logline>^.*FWAdPod \w+ callback \w+.*$))'
        r'(?=.*FWAdPod \w+ callback.+responseCode: (?P<response_code>\d+))'
        r'(?=.*url = (?P<url>.*$))'
        r'(?=.*&t=(?P<utc>\d{10}))?'
        r'(?=.*&adid=(?P<ad_id>\d+))?'
        r'(?=.*&cn=(?P<impression>\w+))?'
        r'(?=.*&tpos=(?P<time_position>\d+))?'
        r'(?=.*&slid=(?P<slot_id>\d+))?.*$'
    )

    # SM3PointsCacheItem
    _regex_sm3_points = re.compile(
        r'^(?=(?P<logline>.*SM3PointsCacheItem Updated SM3 Points.*$))'
        r'^(?=(?P<timestamp>\d{4}/\d{2}/\d{2}\s\d{2}:\d{2}:\d{2}))'
        r'^(?=.*SM3PointsCacheItem.*JSON File: (?P<json>{".*}$))'
    )

    # Newer releases of the Adaptive Player contain Impression events which use a
    # different terminology for DAI events (e.g., "Point" vs "Beacon"), additional
    # fields, and span multiple lines to make them human readable.
    _regex_ap_internal = re.compile(
        r'^(?=(?P<logline>^.*$))'
        r'(?=.*AdaptiveVideoGroup\s+Firing\s+AVG\s+Point)'
        r'(?=.*subType:\s(?P<beacon_event>Ad\w+))'
        r'(?=.*assetGuid\s:\s(?P<asset_guid>[A-Za-z0-9]+))?'
        r'(?=.*adBreakId\s:\s(?P<slot_id>\d+))?'
        r'(?=.*adId\s:\s(?P<ad_id>\w+(\.\w+)?))?'
        r'(?=.*duration\s:\s(?P<duration>\d+))?'
        r'(?=.*fireTime\s:\s(?P<fire_time>(?:\w+|\d+)))?'
        r'(?=.*currentTime\s:\s(?P<current_time>\w+))?'
    )

    _regex_ap_external = re.compile(
        r'^(?=(?P<logline>^.*$))'
        r'(?=.*FWBeaconPacingTask\s+Firing\s+External\s+Point)'
        r'(?=.*subType:\s(?P<beacon_event>Ad\w+))?'
        r'(?=.*assetGuid\s:\s(?P<asset_guid>[A-Za-z0-9]+))?'
        r'(?=.*adBreakId\s:\s(?P<slot_id>\d+))?'
        r'(?=.*adId\s:\s(?P<ad_id>\w+(\.\w+)?))?'
        r'(?=.*duration\s:\s(?P<duration>\d+))?'
        r'(?=.*fireTime\s:\s(?P<fire_time>(?:\w+|\d+)))?'
        r'(?=.*currentTime\s:\s(?P<current_time>\w+))?'
        r'(?=.*url\s:\s(?P<url>.*$))'
        r'(?=.*&cn=(?P<impression>\w+))?'
        r'(?=.*&tpos=(?P<time_position>\d+))?.*$'
    )

    _regex_ap_response = re.compile(
        r'^(?=(?P<logline>^.*$))'
        r'(?=.*FWBeaconPacingTask\s+External\s+Point\s+Response)'
        r'(?=.*subType:\s(?P<beacon_event>Ad\w+))?'
        r'(?=.*assetGuid\s:\s(?P<asset_guid>[A-Za-z0-9]+))?'
        r'(?=.*adBreakId\s:\s(?P<slot_id>\d+))?'
        r'(?=.*adId\s:\s(?P<ad_id>\w+(\.\w+)?))?'
        r'(?=.*duration\s:\s(?P<duration>\d+))?'
        r'(?=.*fireTime\s:\s(?P<fire_time>(?:\w+|\d+)))?'
        r'(?=.*currentTime\s:\s(?P<current_time>\w+))?'
        r'(?=.*responseCode\s:\s(?P<response_code>\d+))?'
        r'(?=.*url\s:\s(?P<url>.*$))'
        r'(?=.*&cn=(?P<impression>\w+))?'
        r'(?=.*&tpos=(?P<time_position>\d+))?.*$'
    )

    __slots__ = [
        'device_info', 'qvt_parsed', 'ad_request', 'xml_response', 'sm3_points',
        'avg_beacon', 'fw_beacon', 'fw_callback', 'ap_internal', 'ap_external',
        'ap_response'
    ]

    def __init__(self, logline):
        """ Match the log entry against the specific regular expressions and store the matched object. """
        self.qvt_parsed = self._regex_qvt_parsed.match(logline)
        self.ad_request = self._regex_ad_request.match(logline)
        self.xml_response = self._regex_xml_response.match(logline)
        self.sm3_points = self._regex_sm3_points.match(logline)
        self.avg_beacon = self._regex_avg_beacon.match(logline)
        self.fw_beacon = self._regex_fw_beacon.match(logline)
        self.fw_callback = self._regex_fw_callback.match(logline)
        self.ap_internal = self._regex_ap_internal.match(logline)
        self.ap_external = self._regex_ap_external.match(logline)
        self.ap_response = self._regex_ap_response.match(logline)
        self.device_info = self._regex_device_info.match(logline)


class Journal:
    """ Work in progress  """
    def __init__(self):
        self.pod_id = 1
        self.slot_id = 0
        self.time_position = 0
        self.dictionary = OrderedDefaultDict()
        self.dictionary['Metrics'] = defaultdict(Counter)

    def get_dictionary(self):
        return self.dictionary

    def get_current_pod_id(self):
        return len(self.dictionary['XML Index'])

    def get_current_slot_id(self):
        return self.slot_id

    def insert_slot_element(self, pod_id, slot_id, time_position):
        """ Inserts a blank slot element associated with the given Slot ID. """
        self.pod_id = pod_id
        self.slot_id = slot_id
        self.time_position = time_position
        self._insert_slot_element()
        self._insert_time_position_param()
        self._insert_qvt_params()
        self._insert_request_params()

    #
    # The following methods are used to pre-fabricate the Slot, Quartile, and Tracking Impressions and parameters
    #
    def _insert_slot_element(self):
        """ Insert a blank template for the Slot Impression. """
        self.dictionary['XML Index'][self.pod_id]['Slot ID'][self.slot_id] = self.generate_dict('slot')

    def _insert_time_position_param(self):
        """ Insert the Time Position Parameter for the Slot Impression. """
        self.dictionary['XML Index'][self.pod_id]['Slot ID'][self.slot_id]['Time Position'] = self.time_position

    def insert_quartile_element(self, pod_id, slot_id, ad_id):
        """ Inserts a blank quartile element associated with the given Ad ID. """
        self.dictionary['XML Index'][pod_id]['Slot ID'][slot_id]['Ad References'][ad_id] = \
            self.generate_dict('quartile')
        self.dictionary['XML Index'][pod_id]['Slot ID'][slot_id]['Ad References'][ad_id]['Metrics'] = \
            defaultdict(Counter)

    def add_tracking_url(self, pod_id, slot_id, ad_id, event, tracking_num):
        """ Inserts a blank tracking template and updates the counter for the expected number of Tracking URLs. """
        url_dict = self.dictionary['XML Index'][pod_id]['Slot ID'][slot_id]['Ad References'][ad_id][event]
        if 'TrackingURLs' in url_dict:
            url_dict['TrackingURLs'].update(([(tracking_num, self.generate_dict('tracking'))]))
        else:
            url_dict['TrackingURLs'] = OrderedDict([(tracking_num, self.generate_dict('tracking'))])
        self.metric_trackingurl_expected(pod_id, slot_id, ad_id, event)

    def insert_creative(self, pod_id, slot_id, ad_id, creative_url, duration):
        """ Inserts the creative Ad URL and duration associated with the given Ad ID. """
        self.dictionary['XML Index'][pod_id]['Slot ID'][slot_id]['Ad References'][ad_id]['Creative'] = \
            creative_url.encode('utf-8')
        self.dictionary['XML Index'][pod_id]['Slot ID'][slot_id]['Ad References'][ad_id]['Duration'] = duration

    def _insert_qvt_params(self):
        """ Insert a blank template for the QVT Parameters. """
        self.dictionary['XML Index'][self.pod_id]['Parameters']['QVT'] = self.generate_dict('params')

    def _insert_request_params(self):
        """ Insert a blank template for the Ad Request Parameters. """
        self.dictionary['XML Index'][self.pod_id]['Parameters']['Ad Request'] = self.generate_dict('params')

    #
    # The following methods are used to update the counter of the expected and observed impressions.
    #
    def metric_expected(self, pod_id, slot_id, ad_id, event):
        """ Increments the count of the number of Impressions's expected. """
        self.dictionary['Metrics']['Expected'][event] += 1  # Overall total metrics
        self.dictionary['XML Index'][pod_id]['Slot ID'][slot_id]['Ad References'][ad_id][
            'Metrics']['Expected'][event] += 1

    def metric_impression(self, impression):
        """ Increments the count of the number of Impressions's encountered. """
        if 'slot' in impression.impression:
            self.dictionary['Metrics'][impression.source][impression.beacon_event] += 1
        else:
            # TODO: Need to determine what to do with the metrics for the slotImpression
            self.dictionary['XML Index'][impression.pod_id]['Slot ID'][impression.slot_id]['Ad References'][
                impression.ad_id]['Metrics'][impression.source][impression.beacon_event] += 1

    def metric_trackingurl_expected(self, pod_id, slot_id, ad_id, event):
        """ Increments the count of the number of Tracking URLs expected. """
        self.dictionary['Metrics']['TrackingURL Expected'][event] += 1
        self.dictionary['XML Index'][pod_id]['Slot ID'][slot_id]['Ad References'][ad_id]['Metrics'][
            'TrackingURL Expected'][event] += 1

    def metric_trackingurl(self, impression):
        """ Increments the count of the overall and Ad specific number of Tracking URLs encountered. """
        if impression.tracking_direction == 'Sent':
            self.dictionary['Metrics']['TrackingURL Sent'][impression.beacon_event] += 1
            self.dictionary['XML Index'][impression.pod_id]['Slot ID'][impression.slot_id]['Ad References'][
                impression.ad_id]['Metrics']['TrackingURL Sent'][impression.beacon_event] += 1
        elif impression.tracking_direction == 'Received':
            self.dictionary['Metrics']['TrackingURL Received'][impression.beacon_event] += 1
            self.dictionary['XML Index'][impression.pod_id]['Slot ID'][impression.slot_id]['Ad References'][
                impression.ad_id]['Metrics']['TrackingURL Received'][impression.beacon_event] += 1

    #
    # The following methods are used to store and retrieve info about the QVT
    #
    def qvt_retrieve_url(self):
        """ Returns the most recent URL for the QVT. """
        return self.dictionary.get('QVT').get('URL', '')

    def qvt_retrieve_logline(self):
        """ Returns the most recent QVT log entry. """
        return self.dictionary.get('QVT').get('Logline', '')

    def qvt_retrieve_params(self, pod_id):
        """ Returns the dictionary of QVT parameters. """
        return self.dictionary['XML Index'][pod_id]['Parameters']['QVT']

    def qvt_archive_params(self, data, pod_id):
        """ Stores the parameter data of the most recent QVT. """
        self.dictionary['XML Index'][pod_id]['Parameters']['QVT'] = data

    def qvt_archive_json(self, data, pod_id):
        """ Stores the parameter data of the most recent QVT. """
        self.dictionary['XML Index'][pod_id]['QVT'] = data

    def qvt_store_url(self, url):
        """ Stores the URL of the most recent QVT. """
        self.dictionary['QVT']['URL'] = url

    def qvt_store_logline(self, log):
        """ Stores the most recent QVT which was previously downloaded and parsed by the Adaptive Player. """
        self.dictionary['QVT']['Logline'] = log

    def update_qvt(self, pod_id):
        """ Copies the most recent QVT to a specific Ad Pod ID. """
        # index = self.get_current_index()
        self.dictionary['XML Index'][pod_id]['QVT']['URL'] = self.qvt_retrieve_url()
        self.dictionary['XML Index'][pod_id]['QVT']['Logline'] = self.qvt_retrieve_logline()
        # self.dictionary['XML Index'][pod_id]['QVT']['URL'] = self.qvt_retrieve_url()
        # self.dictionary['XML Index'][pod_id]['QVT']['Logline'] = self.qvt_retrieve_logline()

    #
    # The following methods pertain to storing and retrieving info about the Ad Request
    #
    def ad_request_retrieve_url(self):
        """ Returns the most recent URL for the Ad Request. """
        return self.dictionary.get('Ad Request', '')

    def ad_request_store_params(self, data, pod_id):
        """ Stores the parameter data of the most recent Ad Request. """
        self.dictionary['XML Index'][pod_id]['Parameters']['Ad Request'] = data

    def ad_request_store_url(self, log):
        """ Stores the URL of the most recent Ad Request submitted to FreeWheel. """
        self.dictionary['Ad Request'] = log

    def update_ad_request(self, pod_id):
        """ Copies the most recent Ad Request to a specific Ad Pod ID. """
        self.dictionary['XML Index'][pod_id]['Ad Request'] = self.ad_request_retrieve_url()

    def retrieve_qvt_ad_request_params(self, pod_id):
        """ Retrieves the parameters of the Ad Request and QVT dictionary. """
        return self.dictionary['XML Index'][pod_id]['Parameters']

    def set_error(self, journal_index, message):
        """ Overwrites the 'slot' dictionary with a message. """
        self.dictionary['XML Index'][journal_index] = message

    #
    # The following methods record the occurrence of a valid impression.
    #
    def catalog_slot_impression(self, impression):
        """ Records the slot impression in the dictionary. """
        self.dictionary['XML Index'][impression.pod_id]['Slot ID'][impression.slot_id][impression.beacon_event][
            impression.source] = impression.logline
        self.metric_impression(impression)

    def catalog_quartile_impression(self, impression):
        """ Records the quartile impression in the dictionary. """
        self.dictionary['XML Index'][impression.pod_id]['Slot ID'][impression.slot_id]['Ad References'][
            impression.ad_id][impression.beacon_event][impression.source] = impression.logline
        self.metric_impression(impression)

    def catalog_tracking_impression(self, impression):
        """ Records the tracking impression in the dictionary. """
        logline = impression.logline.replace('url:', 'trackingurl:')
        self.dictionary['XML Index'][impression.pod_id]['Slot ID'][impression.slot_id]['Ad References'][
            impression.ad_id][impression.beacon_event]['TrackingURLs'][impression.tracking_num].update(
            {impression.tracking_direction: logline})
        self.metric_trackingurl(impression)

        if 'Received' in impression.tracking_direction:
            response_code = int(impression.response_code)
            # response_msg = '\033[31m Missing \033[0m'
            response_msg = colored('Missing', 'red')
            if response_code == 200:
                response_msg = colored('{0} -> Success'.format(response_code), 'green')
            elif response_code == 204:
                response_msg = colored('{0} -> Success (no content)'.format(response_code), 'green')
            elif response_code == 400:
                response_msg = colored('{0} -> Bad Request'.format(response_code), 'red')
            elif response_code == 401:
                response_msg = colored('{0} -> Access Refused'.format(response_code), 'red')
            elif response_code == 404:
                response_msg = colored('{0} -> Not Found'.format(response_code), 'red')
            elif response_code < 200 or response_code > 400:
                response_msg = colored('Received HTTP Error {0}'.format(response_code), 'red')
            self.dictionary['XML Index'][impression.pod_id]['Slot ID'][
                impression.slot_id]['Ad References'][impression.ad_id][impression.beacon_event]['TrackingURLs'][
                impression.tracking_num].update({'Status': response_msg})

    def generate_dict(self, element):
        """
        Provides a predefined template.

        Returns an empty beacon source or Advertisement Slot ID (e.g., Slot Impression), or Advertisement ID
        (e.g., Quartiles), or 3rd-Party Tracking Impressions.
        """
        # missing = '\033[31m Missing \033[0m'  # Red font
        missing = colored('Missing', 'red')

        if element == 'source':
            return OrderedDict([
                ('Internal', missing),
                ('External', missing),
                ('Response', missing)
            ])
        elif element == 'slot':
            return OrderedDict([
                ('Time Position', ''),
                ('Parameters', {'QVT': missing, 'Ad Request': missing}),
                ('AdBreakStartEvent', self.generate_dict('source')),
                ('Ad References', OrderedDict()),
                ('AdBreakCompleteEvent', {'Internal': missing})
            ])
        elif element == 'quartile':
            return OrderedDict([
                ('AdStartEvent', self.generate_dict('source')),
                ('AdQuartile1Event', self.generate_dict('source')),
                ('AdMidwayEvent', self.generate_dict('source')),
                ('AdQuartile3Event', self.generate_dict('source')),
                ('AdCompleteEvent', self.generate_dict('source'))
            ])
        elif element == 'tracking':
            return OrderedDict([
                ('Sent', missing),
                ('Received', missing)
            ])
        elif element == 'params':
            return OrderedDict([
                ('Ads Service URL', missing),
                ('Channel Name', missing),
                ('Cue Point Number (SlotID)', missing),
                ('Enable Server Vast Translation', missing),
                ('Expected Multiple Creative Rendition', missing),
                ('Maximum Duration', missing),
                ('Minimum Duration', missing),
                ('Network ID', missing),
                ('Profile', missing),
                ('Record Video View', missing),
                ('Requires Quartile Callback URLs', missing),
                ('Site Section Owner NetworkID', missing),
                ('Slot Time Position Class', missing),
                ('Supports Slot Callback', missing)
            ])
        else:
            return None


class ParseAdRequest:
    """
    Create an object view of the Adaptive Player's Ad Request.
    """

    def __init__(self, log):
        self.adrequest_qsl = list()
        self.log = log
        self.missing = 'Missing'
        self.params = dict()
        self.re_datetime = r'^(?P<date>\d{4}[/.-]\d{2}[/.-]\d{2}\s\d{2}:\d{2}:\d{2})'
        self.re_url = r'^.* (?P<url>http.*$)'
        self.re_ads_urls = r'^(?P<adapt_url>http://.+)(?P<fw_url>http.+g/1)'
        self.timestamp = self.missing
        self.url = self.missing
        self._values = dict()
        self._parse()

    def _parse(self):
        """ Initializes Ad Request parameters. """
        # The Ad Request URL parameters contain the following four sections:
        expected_params = {
            # 1) Global info about the URL request as a whole.
            'flag', 'nw', 'resp', 'prof', 'csid', 'caid', 'ssnw',
            'asnw', 'vdur', 'pvrn', 'vprn', 'metr', 'afid', 'sfid', 'ssto',
            # 2) FreeWheel Capabilities
            #'emcr', 'esvt', 'exvt', 'rste', 'sync', 'qtcb', 'slcb',
            # 3) Slot info and type of ad request
            'cpsq', 'envp', 'slid', 'tpcl', 'ptgt', 'maxd', 'mind', 'slau',
            'tpos',
            # 4) Site specific values
            'adapt_url', 'ads_url', '_fw_nielsen_app_id', '_fw_vcid2',
            'comscore_device', 'comscore_did_x', 'comscore_impl_type',
            'comscore_platform', 'feature, module', 'fw_url', 'fw_vcid',
            'nielsen_dev_group', 'nielsen_os_group', 'nielsen_os_version',
            'mode', 'roku_rida', 'vip',
        }

        # Initialize expected parameters as 'Missing'
        self.params.update((key, self.missing) for key in expected_params)

        if self.log:
            self.timestamp = re.match(self.re_datetime, self.log).group(1)
            self.url = re.match(self.re_url, self.log).group(1)

        # Parse the Ad Request URL to obtain its parameters
        parsed = urlparse(self.url)
        self.params.update((k, v) for k, v in parse_qs(parsed.query).items())

        # Update the values of some of the expected parameters
        self.params['ads_url'] = parsed.path.strip('/')
        self.params['flag'] = [self.params['flag'][0].strip()]

        # Store the Adapt and FreeWheel URLs from Ad Service URL
        if self.missing not in self.params['ads_url']:
            m = re.match(self.re_ads_urls, self.url)
            if m:
                self.params.update(m.groupdict())

        for i in range(len(self.params['slid'])):
            for key in self.params.keys():
                if isinstance(self.params[key], list):
                    if len(self.params[key]) > 1:
                        self._values[key] = self.params[key][i]
                    elif len(self.params[key]) == 1:
                        self._values[key] = self.params[key][0]
                else:
                    self._values[key] = self.params[key]
            self.adrequest_qsl.append(self._values.copy())


class Impression:
    """
    Create an object view of the Impression parameters, such as Advertisement
    Slot ID (e.g., slotImpression), Advertisement IDs (e.g., Quartiles), and
    3rd-party Tracking Impressions.
    """

    # Map FreeWheel impression terms to terms found in the Adaptive Player log.
    event_table = OrderedDict([
        ('slotImpression', 'AdBreakStartEvent'),
        ('defaultImpression', 'AdStartEvent'),
        ('firstQuartile', 'AdQuartile1Event'),
        ('midPoint', 'AdMidwayEvent'),
        ('thirdQuartile', 'AdQuartile3Event'),
        ('complete', 'AdCompleteEvent'),
        ('slotCompleted', 'AdBreakCompleteEvent')
    ])

    def __init__(self, source, **kwargs):
        self.ad_id = None  # Advertisment ID
        self.asset_guid = None  # GUID of the asset in which the ad plays
        self.beacon_event = None  # Adaptive Player term
        self.beacon_type = None  # e.g., slot, quartile, tracking
        self.creativeId = None  # Id of the ad media
        self.creativeRenditionId = None
        self.current_time = None  # Time the impression actually fired
        self.duration = None  # Duration of the impression's Ad
        self.fire_time = None  # When the impression should have fired
        self.impression = None  # FreeWheel term
        self.is_valid = None  # Tracks if the impression is valid or not
        self.logline = None  # Log entry from the player.log
        self.pk = None  # primary key for the impression
        self.pod_id = None  # Identifies which Ads a response belongs to
        self.replicaId = None
        self.response_code = None  # HTTP response
        self.slot_id = None  # Id of the ad opportunity
        self.source = source  # The origin of the log entry
        self.tech_type = None  # Server-side (sm3) or client-side ad stitching
        self.time_position_class = None  # e.g., pre-roll, mid-roll, post-roll
        self.time_position = None  # Slot's time position
        self.tracking_direction = None  # e.g., sent or received
        self.tracking_num = None  # Index of the tracking impression
        self.url = None  # The beacon's url
        self.utc = None

        self.__dict__.update((key, value) for key, value in kwargs.items())
        self.identify_missing_beacon_values()
        self.identify_beacon_event_type()
        self.print_params()

    def identify_missing_beacon_values(self):
        """ Determine the origin of the log entry. """
        # Internal Beacons generated by the Adaptive Player
        if 'AdaptiveVideoGroup' in self.logline:
            self.impression = self.swap_event_term(self.beacon_event)

        # External Beacons sent to FreeWheel and 3rd-party systems
        elif 'firing beacon event' in self.logline:
            if not all([self.impression, self.slot_id, self.time_position]):
                self.beacon_type = 'tracking'
                self.tracking_direction = 'Sent'
                self.impression = self.swap_event_term(self.beacon_event)

        # Responses received from FreeWheel and 3rd-party systems
        elif 'beacon callback responseCode' in self.logline:
            if not all([self.impression, self.slot_id, self.time_position]):
                self.beacon_type = 'tracking'
                self.tracking_direction = 'Received'
            self.beacon_event = self.swap_event_term(self.impression)

        # SM3 - External Tracking Beacons sent to 3rd-party systems
        elif 'Firing External Point' in self.logline:
            if self.impression is None:
                self.impression = self.swap_event_term(self.beacon_event)
                self.tracking_direction = 'Sent'
                self.new_identify_beacon_event_type()

        # SM3 - External Tracking Beacons received from 3rd-party systems
        elif 'External Point Response' in self.logline:
            if self.impression is None:
                self.impression = self.swap_event_term(self.beacon_event)
                self.tracking_direction = 'Received'
                self.new_identify_beacon_event_type()

    def new_identify_beacon_event_type(self):
        """Identify the beacon event type. """
        with SQLiteDB(row=True) as cursor:
            cursor.execute('SELECT type from impression_table WHERE url=?;', (self.url,))
            record = cursor.fetchone()
            if record:
                self.beacon_type = record['type']

    def identify_beacon_event_type(self):
        """Identify the beacon event type. """
        if self.beacon_type:
            return
        elif 'slot' in self.impression:
            self.beacon_type = 'slot'
        else:
            self.beacon_type = 'quartile'

    def swap_event_term(self, event):
        """
        Replace the Adaptive Player's terminology (i.e., AdStartEvent) with
        FreeWheel's terminology (defaultImpression) or vice versa.
        """
        if event is None:
            return None
        for key, value in self.event_table.items():
            if value in event:
                return key
            elif key in event:
                return value

    def print_params(self):
        """ Pretty print the object to make it easier for humans to read. """
        keylist = sorted(self.__dict__.keys())
        for key in keylist:
            logging.debug('{0}: {1}={2}'.format(str(self.__class__.__name__), key, self.__dict__[key]))

    @property
    def info(self):
        msg = 'source={source}, beacon_event={beacon_event}, slot_id={slot_id}, ad_id={ad_id}, logline={logline}'
        return msg.format(**self.__dict__)


class SQLiteDB:
    """ Database connection context manager. """
    # Initialize database
    def __init__(self, row=False):
        self.row_module = row
        directory = tempfile.gettempdir()
        #filename = 'file::memory:?cache=shared'
        filename = 'report_dai_sqlite.db'
        self.path = '/'.join([directory, filename])

    # On enter, connect to the database and return a cursor
    def __enter__(self):
        self.connection = sqlite3.connect(self.path)
        if self.row_module:
            self.connection.row_factory = sqlite3.Row
        # Sacrifice integrity for speed
        # self.connection.cursor().execute('PRAGMA journal_mode = OFF')
        # self.connection.cursor().execute('PRAGMA synchronous = OFF')
        # self.connection.cursor().execute('PRAGMA TEMP_STORE = 2')
        # self.connection.cursor().execute('PRAGMA locking_mode = EXCLUSIVE')
        return self.connection.cursor()

    # On exit, commit the transaction and close
    def __exit__(self, type, value, traceback):
        if isinstance(value, Exception):
            self.connection.rollback()
        else:
            self.connection.commit()
        self.connection.close()

    def delete_database_file(self):
        if os.path.isfile(self.path):
            os.remove(self.path)


class OrderedDefaultDict(OrderedDict):
    def __missing__(self, key):
        val = self[key] = OrderedDefaultDict()
        return val


def parse_qvt(logline):
    """ Parses QVT information from the log and returns the values. """

    # Schedule QVTs are used for both live and lookback content.
    # Entitlement QVTs are used for SVOD and TVOD

    def compute_slot_duration(qvt):
        """ Returns the duration of the Slot Impression in seconds. """
        stop_unix_ts = qvt['stop_offset']
        start_unix_ts = qvt['start_offset']
        if all([stop_unix_ts, start_unix_ts]):
            duration = float(stop_unix_ts) - float(start_unix_ts)
            return str(int(round(duration)))
        else:
            return 0

    def compute_time_position(qvt):
        """ Returns the time position of the Slot Impression. """
        start_offset_unix_ts = qvt['start_offset']
        anchor_time_unix_ts = qvt['anchor_time']
        if all([start_offset_unix_ts, anchor_time_unix_ts]):
            tpos = float(start_offset_unix_ts) - float(anchor_time_unix_ts)
            return str(format(tpos, '.3f'))
        else:
            return 0

    def compute_start_offset_with_delay(qvt):
        """ Returns the duration of the Slot Impression in seconds. """
        start_unix_ts = qvt['start_offset']
        playback_delay = qvt['playback_delay']
        if all([start_unix_ts, playback_delay]):
            return float(start_unix_ts) + float(playback_delay)
        else:
            return 0

    def compute_stop_offset_with_delay(qvt):
        """ Returns the duration of the Slot Impression in seconds. """
        stop_unix_ts = qvt['stop_offset']
        playback_delay = qvt['playback_delay']
        if all([stop_unix_ts, playback_delay]):
            return float(stop_unix_ts) + float(playback_delay)
        else:
            return 0

    def traverse(obj):
        """ Walks the Ad Break and returns the key-values. """
        if isinstance(obj, dict):
            return {str(k): traverse(v) for k, v in obj.items()}
        elif isinstance(obj, list):
            return [traverse(elem) for elem in obj]
        else:
            return obj

    try:
        json_data = ''
        # Verify the 'Ad Break' section exists in the QVT.
        if re.search(r'"ad_info":.*"ad_breaks":\[{"', logline):
            m = re.match(r'^.*loaded: (?P<qvt>{".*}(\s|$))', logline)
            if m:
                json_data = json.loads(m.group('qvt'))
                ad_info = json_data.get('playback_info').get('ad_info')
                ad_breaks = ad_info.get('ad_breaks', {})
                fw_info = ad_info.get('fw_capabilities', {})
        else:
            msg = 'Skipped parsing the QVT because the Ad Break section is absent.'
            logging.debug(msg)
            return None
    except Exception as ex:
        msg = 'Encountered exception while attempting to parse QVT at timestamp: {0}.'
        logging.error(msg.format(logline[:26]))
        logging.error(format_exception(ex))
    else:
        # This block of code is executed only if no exceptions were raised.
        # Attempt to parse the QVT for the Dynamic Advertisement related
        # parameters and store them in a dictionary so that we can update
        # the qvt_table in the database using named placeholders.
        try:
            qvt_records = list()
            missing = 'Missing'
            qvt = {}
            qvt['log'] = logline
            qvt['playback_delay'] = json_data.get('playback_delay', 0)
            qvt['url'] = json_data.get('self', missing)
            qvt['title'] = json_data['shows'][0]['title']

            # Ad properties
            qvt['ads_service_url'] = ad_info.get('ads_service_url', missing)
            qvt['afid'] = ad_info.get('fallback_asset_id', missing)
            qvt['asnw'] = ad_info.get('programmer_network_id', missing)
            qvt['caid'] = ad_info.get('programmer_asset_id', missing)
            qvt['channel'] = ad_info.get('channel_name', missing)
            qvt['nw'] = ad_info.get('network_id', missing)
            qvt['ssnw'] = ad_info.get('network_id', missing)
            qvt['prof'] = ad_info.get('profile', missing)

            # FreeWheel Capabilities
            qvt['emcr'] = fw_info.get('expectedMultipleCreativeRenditions', missing)
            qvt['esvt'] = fw_info.get('enableServerVastTranslation', missing)
            qvt['exvt'] = fw_info.get('recordVideoView', missing)
            qvt['qtcb'] = fw_info.get('requiresQuartileCallbackUrls', missing)
            qvt['slcb'] = fw_info.get('supportsSlotCallbacks', missing)
            qvt['flag'] = ' '.join([qvt[k] for k in ('exvt', 'qtcb', 'emcr', 'slcb', 'esvt')]) + ' sync rste'

            # Linear properties
            linear_info = json_data.get('playback_info', {}).get('linear_info', {})
            qvt['anchor_time'] = linear_info.get('anchor_time', '0')
            qvt['allow_seeking'] = linear_info.get('allow_seeking', missing)

            # Content Type
            if linear_info.get('anchor_time', False):
                qvt['content_type'] = 'live'
            else:
                qvt['content_type'] = 'vod'

            # Channel Service ID (CSID)
            device_name = device_lookup_table()
            channel_name = qvt['channel']
            content_type = qvt['content_type']
            qvt['csid'] = '_'.join(['otto', device_name, channel_name, content_type])

            # FIXME: Python 3.6 is throwing the following exception:
            #  An exception of type TypeError occurred. Arguments:
            #  ("a bytes-like object is required, not 'str'",).
            # Retrieve the Adapt and FreeWheel URLs from Ads Service URL
            if missing not in qvt['ads_service_url']:
                re_urls = r'^(?P<adapt_url>http://.+)(?P<fw_url>http.*)'
                m = re.match(re_urls, qvt['ads_service_url'])
                if m:
                    qvt.update(m.groupdict())

            # Append the provider's name to the profile to match the same
            # parameter from the Ad Request
            if missing not in qvt['prof']:
                qvt['prof'] = ad_info.get('profile', missing).join(['', ':sling'])

            # Parse and store the key-values from the Ad Break section.
            # This section may contain one or more commercial breaks.
            for ad_break in traverse(ad_breaks):
                #qvt.update(ad_break)
                qvt['cue_point_number'] = ad_break.get('cue_point_number')
                qvt['method'] = ad_break.get('method')
                qvt['start_offset'] = ad_break.get('start_offset', 0)
                qvt['stop_offset'] = ad_break.get('stop_offset', 0)
                qvt['type'] = ad_break.get('type')
                qvt['duration'] = compute_slot_duration(qvt)
                qvt['mind'] = qvt['duration']
                qvt['maxd'] = qvt['duration']
                qvt['start_offset_with_delay'] = compute_start_offset_with_delay(qvt)
                qvt['stop_offset_with_delay'] = compute_stop_offset_with_delay(qvt)
                # qvt['start_offset_with_delay'] = float(qvt['start_offset']) + qvt['playback_delay']
                # qvt['stop_offset_with_delay'] = float(qvt['stop_offset']) + qvt['playback_delay']
                qvt['tpos'] = compute_time_position(qvt)
                qvt_records.append(qvt.copy())
            return qvt_records

            # Condition: Ad Break section contains a single commercial break.
            # if isinstance(ad_breaks, dict):
            #     qvt['slot_id'] = ad_breaks.get('cue_point_number')
            #     qvt['method'] = ad_breaks.get('method')
            #     qvt['tpcl'] = ad_breaks.get('type')
            #     qvt['start_offset'] = float(ad_breaks['start_offset'])
            #     qvt['stop_offset'] = float(ad_breaks['stop_offset'])
            #     qvt['duration'] = compute_slot_duration(qvt['stop_offset'], qvt['start_offset'])
            #     qvt['maxd'] = qvt['duration']
            #     qvt['mind'] = qvt['duration']
            #     qvt['tpos'] = compute_time_position(qvt['start_offset'], qvt['anchor_time'])
            #     qvt['start_offset_with_delay'] = qvt['start_offset'] + qvt['playback_delay']
            #     qvt['stop_offset_with_delay'] = qvt['stop_offset'] + qvt['playback_delay']
            #     qvt_records.append(qvt.copy())
            #
            # # Condition: Ad Break section contains multiple commercial breaks.
            # elif isinstance(ad_breaks, list):
            #     for ad_break in ad_breaks:
            #         qvt['slot_id'] = ad_break.get('cue_point_number')
            #         qvt['method'] = ad_break.get('method')
            #         qvt['tpcl'] = ad_break.get('type')
            #         qvt['start_offset'] = float(ad_break['start_offset'])
            #         qvt['stop_offset'] = float(ad_break['stop_offset'])
            #         qvt['duration'] = compute_slot_duration(qvt['stop_offset'], qvt['start_offset'])
            #         qvt['maxd'] = qvt['duration']
            #         qvt['mind'] = qvt['duration']
            #         qvt['tpos'] = compute_time_position(qvt['start_offset'], qvt['anchor_time'])
            #         qvt['start_offset_with_delay'] = qvt['start_offset'] + qvt['playback_delay']
            #         qvt['stop_offset_with_delay'] = qvt['stop_offset'] + qvt['playback_delay']
            #         qvt_records.append(qvt.copy())
        except Exception as ex:
            logging.error('Problem encountered while processing the QVT.')
            logging.error(format_exception(ex))


def db_catalog_qvt(values):
    """

    Inserts information about the QVT into the database only if the QVT
    information is unique.

    The Adaptive Player fetches the QVT every 15 secs and so the majority of
    the QVT log entries are duplicates. Typically the QVT required to verify
    the Ad Request occurs after the Adaptive Player has submitted the Ad
    Request to FreeWheel. Usually, the QVT prior to the Ad Request won't
    contain the information needed to validate the Ad Request.
    """
    # For each dict in the 'values' list, take the keys from the dict as
    # SQL parameters and execute the SQL statement.
    if values is not None:
        with SQLiteDB() as cursor:
            cursor.executemany('''
                INSERT OR IGNORE INTO qvt_table
                VALUES (
                    :cue_point_number, :afid, :asnw, :caid, :channel, :nw, 
                    :ssnw, :prof, :flag, :emcr, :esvt, :exvt, :qtcb, :slcb, 
                    :type, :anchor_time, :allow_seeking, :method, :start_offset, 
                    :stop_offset, :playback_delay, :start_offset_with_delay, 
                    :stop_offset_with_delay, :duration, :maxd, :mind, :tpos, 
                    :title, :ads_service_url, :adapt_url, :fw_url, :url, 
                    :content_type, :log, :csid
                );
            ''', values)
            count = cursor.rowcount
            logging.debug('Number of rows inserted: {0}'.format(count))


def process(line):
    # type: (str, Journal) -> None
    """
    Determine if the log entry from the Adaptive Player matches any significant
    Dynamic Ad Insertion events.
    """
    try:
        # if line.startswith("2018/12/28 16:16:44.167344"):
        #     logging.warning(line)
        match = SimpleGrep(line)

        if match.qvt_parsed:
            logging.debug('Found parsed QVT')
            handle_qvt(line)

        elif match.device_info:
            logging.debug('Found Device Information')
            handle_device_info(**match.device_info.groupdict())

        elif match.ad_request:
            logging.debug('Found Ad Request submitted to FreeWheel')
            handle_ad_request(match.ad_request)

        elif match.xml_response:
            logging.debug('Found FreeWheel\'s Ad Response')
            handle_ad_response(match.xml_response)

        elif match.sm3_points:
            logging.debug('Found SM3PointsCacheItem')
            sm3_handle_points(match.sm3_points)

        # These next three conditions are for Adaptive Player's older DAI events
        elif match.avg_beacon:
            logging.debug('Found AP Internal Beacon')
            beacon = Impression('Internal', **match.avg_beacon.groupdict())
            beacon = correlate_beacon_params(beacon)
            catalog(beacon)
            db_catalog_beacon(beacon)

        elif match.fw_beacon:
            logging.debug('Found External Beacon')
            beacon = Impression('External', **match.fw_beacon.groupdict())
            beacon = correlate_beacon_params(beacon)
            catalog(beacon)
            db_catalog_beacon(beacon)

        elif match.fw_callback:
            logging.debug('Found Response Beacon')
            beacon = Impression('Response', **match.fw_callback.groupdict())
            beacon = correlate_beacon_params(beacon)
            catalog(beacon)
            db_catalog_beacon(beacon)
            db_catalog_http_status(beacon)

        # These next three conditions are for Adaptive Player's newer DAI events
        # (e.g., using SM3 and 'Points')
        elif match.ap_internal:
            logging.debug('Found AP Internal Beacon (SM3)')
            beacon = Impression('Internal', **match.ap_internal.groupdict())
            beacon = correlate_sm3_beacon_params(beacon)
            catalog(beacon)
            db_catalog_beacon(beacon)

        elif match.ap_external:
            logging.debug('Found External Beacon (SM3)')
            beacon = Impression('External', **match.ap_external.groupdict())
            beacon = correlate_sm3_beacon_params(beacon)
            catalog(beacon)
            db_catalog_beacon(beacon)

        elif match.ap_response:
            logging.debug('Found Response Beacon (SM3)')
            beacon = Impression('Response', **match.ap_response.groupdict())
            beacon = correlate_sm3_beacon_params(beacon)
            catalog(beacon)
            db_catalog_beacon(beacon)
            db_catalog_http_status(beacon)
    except Exception as ex:
        logging.error(format_exception(ex))


def handle_device_info(**kwargs):
    """ Stores the Adaptive Player Device Information found in the AP log file. """
    try:
        device_info.update((k, v) for k, v in kwargs.items() if v is not None)
    except Exception as ex:
        logging.error(format_exception(ex))


def handle_qvt(line):
    """ Process the QVT received by the Adaptive Player. """
    try:
        qvt_records = parse_qvt(line)
        db_catalog_qvt(qvt_records)
    except Exception as ex:
        logging.error('Problem encountered while processing the QVT: {0}.'.format(line))
        logging.error(format_exception(ex))


def handle_ad_request(match):
    """ Process the Ad Request submitted to FreeWheel from the Adaptive Player. """
    try:
        log = match.group('logline')
        ad_request = ' '.join([match.group('timestamp'), match.group('url')])
        with SQLiteDB() as cursor:
            cursor.execute('''
                INSERT INTO dai_events_table (ad_request) 
                     VALUES (?);
                ''', (ad_request,))
        #db_catalog_ad_request(log)
    except Exception as ex:
        msg = 'Problem encountered while processing the following FreeWheel Ad Request: {0}.'
        logging.error(msg.format(log))
        logging.error(format_exception(ex))


def db_catalog_ad_request(values):
    # ad_request = ParseAdRequest(log)
    # params = ad_request.params
    # list_of_ad_requests = list()
    # values = dict()
    #
    # for i in range(len(params['slid'])):
    #     for key in params.keys():
    #         if isinstance(params[key], list) and len(params[key]) > 1:
    #             values[key] = params[key][i]
    #         elif isinstance(params[key], list) and len(params[key]) == 1:
    #             values[key] = params[key][0]
    #         else:
    #             values[key] = params[key]
    #     list_of_ad_requests.append(values.copy())

    if values is not None:
        with SQLiteDB() as cursor:
            cursor.executemany('''
                INSERT INTO ad_request_table
                VALUES (
                    :_fw_nielsen_app_id, :_fw_vcid2, :adapt_url, :ads_url, 
                    :afid, :asnw, :caid, :comscore_device, :comscore_did_x, 
                    :comscore_impl_type, :comscore_platform, :cpsq, :csid, 
                    :envp, :feature, :flag, :fw_url, :fw_vcid, :maxd, :metr, 
                    :mind, :mode, :module, :nielsen_dev_group, 
                    :nielsen_os_group, :nielsen_os_version, :nw, :prof, :ptgt, 
                    :pvrn, :resp, :roku_rida, :sfid, :slau, :slid, :ssnw, :ssto,
                    :tpcl, :tpos, :vdur, :vip, :vprn
                );
            ''', values)
            count = cursor.rowcount
            logging.debug('Number of rows inserted: {0}'.format(count))


def handle_ad_response(match):
    # type: (SimpleGrep) -> object
    """
    Processes FreeWheel's SmartXML Ad Response.

    :param SimpleGrep match: Instance of SimpleGrep
    :returns: None
    """
    def fetch_pod_id():
        """
        Retrieves the pod_id where we've previously encountered the Ad Request
        that the Adaptive Player submitted to FreeWheel, but have not yet
        processed FreeWheel's Ad Response.
        """
        with SQLiteDB() as cursor:
            cursor.execute('''
                SELECT pod_id
                  FROM dai_events_table 
                 WHERE ad_request IS NOT NULL 
                   AND ad_response is NULL;
            ''')
            return cursor.fetchone()[0]

    def update_db(pod_id, response):
        """ Stores FreeWheel's Ad Response in the database. """
        with SQLiteDB() as cursor:
            cursor.execute('''
                UPDATE dai_events_table 
                   SET ad_response = ? 
                 WHERE pod_id = ?;
            ''', (response, pod_id))

    try:
        timestamp = match.group('timestamp')
        xml_string = match.group('xml')
        response = ' '.join([timestamp, xml_string])
        pod_id = fetch_pod_id()
        if pod_id:
            logging.debug('Processing FreeWheel\'s XML Ad Response #{0}.'.format(pod_id))
            update_db(pod_id, response)
            # Load and parse the XML document for all of the Impressions and Ad Creatives
            tree = ElementTree.ElementTree(ElementTree.fromstring(xml_string))
            # If debug is enabled, save the XML to disk and report the
            # Advertisement's Slot IDs and Time Position
            if logging.getLogger().isEnabledFor(logging.DEBUG):
                write_ad_response_to_file(pod_id, xml_string)
                path = 'siteSection/videoPlayer/videoAsset/adSlots/temporalAdSlot/[@customId]'
                for elem in tree.findall(path):
                    slot_id = elem.attrib.get('customId')
                    time_position = str(int(float(elem.attrib.get('timePosition', '0'))))
                    template = 'FreeWheel\'s XML Ad Response #{0} contains Slot ID:{1} and Time Position:{2}.'
                    msg = template.format(pod_id, slot_id, time_position)
                    logging.debug(msg)
            # Parse the XML document for the impressions and Ad Creatives; store results in the database.
            fill_impression_table(collect_impression_info(pod_id, tree))
            fill_creative_table(collect_creatives(pod_id, tree))
            # FIXME: Need to work on removing the following function:
            populate_template(pod_id)
    except Exception as ex:
        logging.error('Problem processing FreeWheel\'s XML Ad Response')
        logging.error(format_exception(ex))


def collect_impression_info(pod_id, tree):
    """
    Parse the FreeWheel SmartXML Ad Response for the Event Callback information and return a list of Impressions.
    The Event Callback section contains information about all the Impression Events, such as the Advertisement
    Slot IDs (e.g., slotImpression), Advertisement IDs (e.g., Quartiles), and 3rd-party Tracking Impressions.

    :param int pod_id: The ID of the Ad Request submitted to FreeWheel.
    :param xml.etree.ElementTree.ElementTree tree: XML document
    :return: list of impressions found in the XML document
    :rtype: list of dictionaries
    """
    logging.debug('Retrieving impression events from FreeWheel\'s Ad Response #{0}'.format(pod_id))
    list_of_impressions = list()
    path = 'siteSection/videoPlayer/videoAsset/adSlots/temporalAdSlot/[@customId]'
    # Loop through each of the Slot IDs
    for element in tree.findall(path):
        slot_id = element.attrib.get('customId')
        time_position = str(int(float(element.attrib.get('timePosition', 0))))
        event = element.find('eventCallbacks').find("eventCallback[@name='slotImpression']").attrib.get('name')
        url = element.find('eventCallbacks').find("eventCallback[@name='slotImpression']").attrib.get('url')
        list_of_impressions.append({
            'pod_id': pod_id,
            'slot_id': slot_id,
            'time_position': time_position,
            'ad_id': None,
            'type': 'slot',
            'event': event,
            'url': url,
            'tracking_num': None
        })
        subpath = "[@customId='{slot_id}']//*[@adId]"
        for elem in element.findall(subpath.format(slot_id=slot_id)):
            ad_id = elem.attrib.get('adId')
            # Loop through each of the Impression Events
            for impression in ['defaultImpression', 'firstQuartile', 'midPoint', 'thirdQuartile', 'complete']:
                quartile_path = ".//temporalAdSlot/[@customId='{slot_id}']//*[@adId='{ad_id}']//*[@type='IMPRESSION']" \
                                "[@name='{impression}']"
                # Retrieve the Quartile Impressions for the Impression Event
                for quartile in tree.findall(quartile_path.format(slot_id=slot_id, ad_id=ad_id, impression=impression)):
                    url = quartile.attrib.get('url')
                    list_of_impressions.append({
                        'pod_id': pod_id,
                        'slot_id': slot_id,
                        'time_position': time_position,
                        'ad_id': ad_id,
                        'type': 'quartile',
                        'event': impression,
                        'url': url,
                        'tracking_num': None
                    })
                    # Retrieve the Tracking Impressions for the Impression Event
                    tracking_path = ".//temporalAdSlot/[@customId='{slot_id}']//*[@adId='{ad_id}']//trackingURLs/*" \
                                    "[@name='{impression}']"
                    for count, item in enumerate(tree.findall(tracking_path.format(
                            slot_id=slot_id, ad_id=ad_id, impression=impression)), 1):
                        url = item.attrib.get('value')
                        list_of_impressions.append({
                            'pod_id': pod_id,
                            'slot_id': slot_id,
                            'time_position': time_position,
                            'ad_id': ad_id,
                            'type': 'tracking',
                            'event': impression,
                            'url': url,
                            'tracking_num': count
                        })

    # Append the slotCompleted event to the end of each slotImpression
    list_of_impressions.append({
        'pod_id': pod_id,
        'slot_id': slot_id,
        'time_position': time_position,
        'ad_id': None,
        'type': 'slot',
        'event': 'slotCompleted',
        'url': '',
        'tracking_num': None
    })
    return list_of_impressions


def collect_creatives(pod_id, tree):
    # type: (int, xml.etree.ElementTree.ElementTree) -> Union[List[Dict[str, str]], List]
    """
    Parse the FreeWheel SmartXML Ad Response for information related to the Creative Advertisements.

    :param int pod_id: The ID of the Ad Request submitted to FreeWheel.
    :param xml.etree.ElementTree.ElementTree tree: FreeWheel's SmartXML document
    :return: list of the impressions found in the XML document
    :rtype: list of dictionaries
    """
    list_of_ad_creatives = list()
    path = 'creatives/creative'
    rendition_path = path + '/creativeRenditions/creativeRendition'
    asset_path = rendition_path + '/asset'
    logging.debug('Retrieving creatives from FreeWheel\'s Ad Response #{0}'.format(pod_id))

    # Loop through and retrieve each of the Creative Advertisements
    for element in tree.findall('ads/ad'):
        list_of_ad_creatives.append({
            'pod_id': pod_id,
            'ad_adId': element.get('adId'),
            'ad_adUnit': element.get('adUnit'),
            'creative_adUnit': element.find(path).attrib.get('adUnit'),
            'creative_baseUnit': element.find(path).attrib.get('baseUnit'),
            'creative_creativeId': element.find(path).attrib.get('creativeId'),
            'creative_duration': int(float(element.find(path).attrib.get('duration', 0))),
            'creativeRendition_adReplicaId': element.find(rendition_path).attrib.get('adReplicaId'),
            'creativeRendition_creativeApi': element.find(rendition_path).attrib.get('creativeApi'),
            'creativeRendition_creativeRenditionId': element.find(rendition_path).attrib.get('creativeRenditionId'),
            'creativeRendition_height': element.find(rendition_path).attrib.get('height'),
            'creativeRendition_preference': element.find(rendition_path).attrib.get('preference'),
            'creativeRendition_width': element.find(rendition_path).attrib.get('width'),
            'asset_bytes': element.find(asset_path).attrib.get('bytes'),
            'asset_contentType': element.find(asset_path).attrib.get('contentType'),
            'asset_mimeType': element.find(asset_path).attrib.get('mimeType'),
            'asset_url': element.find(asset_path).attrib.get('url')
        })
    return list_of_ad_creatives


def fill_impression_table(data):
    # type: (List[Dict[str, str]]) -> None
    """
    Stores impressions in a SQL database so it can be queried later when impressions are fired.

    :param list data: A list of dicts so we can use sqlite3 db adapter with named parameters in the form :keyname
    :return: None
    """
    # Retrieve the index to identify which occurrence of the FreeWheel Ad Response this data belongs to.
    pod_id = data[0]['pod_id']

    # For each dict in the 'data' list, take the keys from the dict as SQL parameters and execute the SQL statement.
    with SQLiteDB() as cursor:
        logging.debug('Storing Impressions from FreeWheel\'s Ad Response into the database:')
        cursor.executemany('''
            INSERT INTO impression_table
                (pod_id, slot_id, time_position, ad_id, type, event, url, tracking_num)
            VALUES
                (:pod_id, :slot_id, :time_position, :ad_id, :type, :event, :url, :tracking_num);
            ''', data)

        # Provide debugging output per user's request
        if logging.getLogger().isEnabledFor(logging.DEBUG):
            cursor.execute('SELECT * FROM impression_table WHERE pod_id=?', (pod_id,))
            column_names = tuple(map(lambda x: x[0], cursor.description))
            rows = cursor.fetchall()
            table = '\n'.join(map(str, rows))
            msg = 'Number of Impressions in FreeWheel\'s Ad Response #{0}: {1}\n{2}\n{3}'
            logging.debug(msg.format(pod_id, len(rows), column_names, table))


def fill_creative_table(data):
    # type: (List[Dict[str, str]]) -> None
    """
    Store the information about the Creative Advertisements in the SQL database.

    :param list data: A list of dicts so we can use sqlite3 db adapter with named parameters in the form :keyname
    :return: None
    """
    try:
        # Retrieve the Ad Pod ID to identify which occurrence of the Ad Response this data belongs to.
        if data:
            pod_id = data[0]['pod_id']
        else:
            logging.warning('Empty Ad Creatives found in FreeWheel\'s Ad Response.')
            return None

        # For each dict in the 'data' list, take the keys from the dict as SQL parameters and execute the SQL statement.
        with SQLiteDB() as cursor:
            logging.debug('Storing Creatives from FreeWheel\'s Ad Response into the database:')
            cursor.executemany('''
                INSERT INTO creative_table (
                    pod_id, ad_adId, ad_adUnit, creative_adUnit, creative_baseUnit, creative_creativeId,
                    creative_duration, creativeRendition_adReplicaId, creativeRendition_creativeApi,
                    creativeRendition_creativeRenditionId, creativeRendition_height, creativeRendition_preference,
                    creativeRendition_width, asset_bytes, asset_contentType, asset_mimeType, asset_url
                    )
                VALUES (
                    :pod_id, :ad_adId, :ad_adUnit, :creative_adUnit, :creative_baseUnit, :creative_creativeId,
                    :creative_duration, :creativeRendition_adReplicaId, :creativeRendition_creativeApi,
                    :creativeRendition_creativeRenditionId, :creativeRendition_height, :creativeRendition_preference,
                    :creativeRendition_width, :asset_bytes, :asset_contentType, :asset_mimeType, :asset_url
                    ); 
            ''', data)

            # Update the Impression's Creative Ad URL and the Ad's Duration
            logging.debug('Updating the Impression records with Creative Advertisement information')
            cursor.executemany('''
                UPDATE impression_table 
                   SET creative_url = :asset_url, duration = :creative_duration 
                 WHERE ad_id = :ad_adId 
                   AND type = 'quartile'  
            ''', data)

            # Provide debugging output per user's request
            if logging.getLogger().isEnabledFor(logging.DEBUG):
                cursor.execute('SELECT * FROM creative_table WHERE pod_id=?', (pod_id, ))
                column_names = tuple(map(lambda x: x[0], cursor.description))
                rows = cursor.fetchall()
                table = '\n'.join(map(str, rows))
                msg = 'Number of Creatives in FreeWheel\'s Ad Response #{0}: {1}\n{2}\n{3}'
                logging.debug(msg.format(pod_id, len(rows), column_names, table))
                print()

    except Exception as ex:
        logging.error(format_exception(ex))


# def db_connect():
#     """ Establish connection to a SQLite database file """
#     connection = sqlite3.connect('/tmp/sqlite::memory:?cache=shared')
#     connection.row_factory = sqlite3.Row
#     cursor = connection.cursor()
#     return connection, cursor


def init_database():
    # type: () -> None
    """ Create a databases to store and retrieve Impression information. """
    with SQLiteDB() as cursor:
        logging.debug('Creating database.')
        script = '''
            DROP TABLE IF EXISTS impression_table;
            CREATE TABLE IF NOT EXISTS impression_table (
                pk INTEGER PRIMARY KEY, 
                pod_id INTEGER NOT NULL, 
                slot_id TEXT NOT NULL DEFAULT '', 
                time_position TEXT DEFAULT '', 
                ad_id TEXT DEFAULT '', 
                type TEXT NOT NULL DEFAULT '', 
                event TEXT NOT NULL DEFAULT '', 
                url TEXT NOT NULL, 
                sent TEXT,
                received TEXT,
                active TEXT NOT NULL DEFAULT '',
                tracking_num INTEGER,
                creative_url TEXT NOT NULL DEFAULT '',
                duration INTEGER,
                internal_log TEXT NOT NULL DEFAULT '',
                sent_log TEXT NOT NULL DEFAULT '',
                received_log TEXT NOT NULL DEFAULT '',
                http_status TEXT NOT NULL DEFAULT '',
                http_status_msg TEXT NOT NULL DEFAULT '',
                beacon_firing_order TEXT NOT NULL DEFAULT '',
                overall_firing_order TEXT NOT NULL DEFAULT '',
                qvt_firing_time REAL NOT NULL DEFAULT '0',
                actual_firing_time REAL NOT NULL DEFAULT '0',
                expected_firing_time REAL NOT NULL DEFAULT '0',
                delta_firing_time REAL NOT NULL DEFAULT '0',
                beacons_found TEXT NOT NULL DEFAULT '',
                fire_time TEXT DEFAULT '',
                current_time TEXT DEFAULT ''
            );
                
            DROP TABLE IF EXISTS creative_table;
            CREATE TABLE IF NOT EXISTS creative_table (
                pk INTEGER PRIMARY KEY,
                pod_id INTEGER NOT NULL, 
                ad_adId INTEGER,
                ad_adUnit INTEGER,
                creative_adUnit TEXT,
                creative_baseUnit TEXT,
                creative_creativeId INTEGER,
                creative_duration INTEGER,
                creativeRendition_adReplicaId INTEGER,
                creativeRendition_creativeApi TEXT, 
                creativeRendition_creativeRenditionId INTEGER,
                creativeRendition_height INTEGER,
                creativeRendition_preference INTEGER,
                creativeRendition_width INTEGER,
                asset_bytes INTEGER,
                asset_contentType TEXT,
                asset_mimeType TEXT,
                asset_url TEXT 
            ); 
            
            DROP TABLE IF EXISTS qvt_table;
            CREATE TABLE IF NOT EXISTS qvt_table (
                cue_point_number TEXT NOT NULL DEFAULT 'QVT Missing',
                afid TEXT NOT NULL DEFAULT 'QVT Missing',
                asnw TEXT NOT NULL DEFAULT 'QVT Missing',
                caid TEXT NOT NULL DEFAULT 'QVT Missing',
                channel TEXT NOT NULL DEFAULT 'QVT Missing',
                nw TEXT NOT NULL DEFAULT 'QVT Missing',
                ssnw TEXT NOT NULL DEFAULT 'QVT Missing',
                prof TEXT NOT NULL DEFAULT 'QVT Missing',
                flag TEXT NOT NULL DEFAULT 'QVT Missing',
                emcr TEXT NOT NULL DEFAULT 'QVT Missing',
                esvt TEXT NOT NULL DEFAULT 'QVT Missing',
                exvt TEXT NOT NULL DEFAULT 'QVT Missing',
                qtcb TEXT NOT NULL DEFAULT 'QVT Missing',
                slcb TEXT NOT NULL DEFAULT 'QVT Missing',
                type TEXT NOT NULL DEFAULT 'QVT Missing', 
                anchor_time TEXT NOT NULL DEFAULT 'QVT Missing',
                allow_seeking TEXT NOT NULL DEFAULT 'QVT Missing',
                method TEXT NOT NULL DEFAULT 'QVT Missing',
                /* start_offset REAL NOT NULL DEFAULT 0,            */
                start_offset TEXT NOT NULL DEFAULT 'QVT Missing',
                /* stop_offset REAL NOT NULL DEFAULT 0,             */
                stop_offset TEXT NOT NULL DEFAULT 'QVT Missing',
                playback_delay TEXT NOT NULL DEFAULT 'QVT Missing',
                /* start_offset_with_delay REAL NOT NULL DEFAULT 0, */
                start_offset_with_delay TEXT NOT NULL DEFAULT 'QVT Missing',
                /* stop_offset_with_delay REAL NOT NULL DEFAULT 0,  */
                stop_offset_with_delay TEXT NOT NULL DEFAULT 'QVT Missing',
                /* duration REAL NOT NULL DEFAULT 0,                */
                duration TEXT NOT NULL DEFAULT 'QVT Missing',
                maxd TEXT NOT NULL DEFAULT 'QVT Missing',
                mind TEXT NOT NULL DEFAULT 'QVT Missing',
                /* tpos REAL NOT NULL DEFAULT 0,                    */
                tpos TEXT NOT NULL DEFAULT 'QVT Missing',
                title TEXT NOT NULL DEFAULT 'QVT Missing',
                ads_service_url TEXT NOT NULL DEFAULT 'QVT Missing',
                adapt_url TEXT NOT NULL DEFAULT 'QVT Missing',
                fw_url TEXT NOT NULL DEFAULT 'QVT Missing',
                url TEXT NOT NULL DEFAULT 'QVT Missing',
                content_type TEXT NOT NULL DEFAULT 'QVT Missing',
                log TEXT NOT NULL DEFAULT 'QVT Missing',
                csid TEXT NOT NULL DEFAULT 'QVT Missing'
            ); 
            CREATE UNIQUE INDEX idx_qvt_cue_point_number ON qvt_table (cue_point_number);
           
            DROP TABLE IF EXISTS ad_request_table;
            CREATE TABLE IF NOT EXISTS ad_request_table (
                _fw_nielsen_app_id TEXT NOT NULL DEFAULT '',
                _fw_vcid2 TEXT NOT NULL DEFAULT '',
                adapt_url TEXT NOT NULL DEFAULT '',
                ads_url TEXT NOT NULL DEFAULT '',
                afid TEXT NOT NULL DEFAULT '',
                asnw TEXT NOT NULL DEFAULT '',
                caid TEXT NOT NULL DEFAULT '',
                comscore_device TEXT NOT NULL DEFAULT '',
                comscore_did_x TEXT NOT NULL DEFAULT '',
                comscore_impl_type TEXT NOT NULL DEFAULT '',
                comscore_platform TEXT NOT NULL DEFAULT '',
                cpsq TEXT NOT NULL DEFAULT '',
                csid TEXT NOT NULL DEFAULT '',
                envp TEXT NOT NULL DEFAULT '',
                feature TEXT NOT NULL DEFAULT '',
                flag TEXT NOT NULL DEFAULT '',
                fw_url TEXT NOT NULL DEFAULT '',
                fw_vcid TEXT NOT NULL DEFAULT '',
                maxd TEXT NOT NULL DEFAULT '',
                metr TEXT NOT NULL DEFAULT '',
                mind TEXT NOT NULL DEFAULT '',
                mode TEXT NOT NULL DEFAULT '',
                module TEXT NOT NULL DEFAULT '',
                nielsen_dev_group TEXT NOT NULL DEFAULT '',
                nielsen_os_group TEXT NOT NULL DEFAULT '',
                nielsen_os_version TEXT NOT NULL DEFAULT '',
                nw TEXT NOT NULL DEFAULT '',
                prof TEXT NOT NULL DEFAULT '',
                ptgt TEXT NOT NULL DEFAULT '',
                pvrn TEXT NOT NULL DEFAULT '',
                resp TEXT NOT NULL DEFAULT '',
                roku_rida TEXT NOT NULL DEFAULT '',
                sfid TEXT NOT NULL DEFAULT '',
                slau TEXT NOT NULL DEFAULT '',
                slid TEXT NOT NULL DEFAULT '',
                ssnw TEXT NOT NULL DEFAULT '',
                ssto TEXT NOT NULL DEFAULT '',
                tpcl TEXT NOT NULL DEFAULT '',
                tpos TEXT NOT NULL DEFAULT '',
                vdur TEXT NOT NULL DEFAULT '',
                vip TEXT NOT NULL DEFAULT '',
                vprn TEXT NOT NULL DEFAULT ''
            );
            CREATE UNIQUE INDEX idx_adreq_slot_id ON ad_request_table (slid);

            DROP TABLE IF EXISTS unmatched_table;
            CREATE TABLE IF NOT EXISTS unmatched_table (
                pk INTEGER PRIMARY KEY, 
                log TEXT NOT NULL DEFAULT '',
                actual_firing_time REAL NOT NULL DEFAULT '0'
            );
                
            DROP TABLE IF EXISTS dai_events_table;
            CREATE TABLE IF NOT EXISTS dai_events_table (
                pod_id INTEGER PRIMARY KEY,
                ad_request TEXT,
                ad_response TEXT,
                sm3pointscacheitem TEXT DEFAULT ''
            );
                
            DROP TABLE IF EXISTS dai_report_table;
            CREATE TABLE IF NOT EXISTS dai_report_table (
                pk INTEGER PRIMARY KEY, 
                pod_id INTEGER NOT NULL,
                slot_id TEXT NOT NULL DEFAULT '', 
                content TEXT NOT NULL DEFAULT ''
            );
            
            DROP TABLE IF EXISTS device_table;
            CREATE TABLE IF NOT EXISTS device_table (
                pk INTEGER PRIMARY KEY, 
                device_type TEXT,
                device_platform TEXT,
                device_model TEXT
            );
        '''
        cursor.executescript(script)


def remove_db(filename):
    """
    Removes the SQLite3 database file from the filesystem.

    :param filename:
    :return: None
    """
    if os.path.isfile(filename):
        os.remove(filename)
        logging.debug('Successfully removed SQLite database file: {0}'.format(filename))
    else:
        logging.error('Failed to remove SQLite database file: {0}'.format(filename))


def update_db_successfully_sent_impression(record):
    # type: (sqlite3.Row) -> None
    """
    Update the 'sent' status for the entry in the database that corresponds to the primary key

    :param sqlite3.Row record:
    :return: None
    """
    with SQLiteDB() as cursor:
        cursor.execute("UPDATE impression_table SET sent='True' WHERE pk=?;", (record['pk'],))


def update_db_successfully_received_impression(record):
    # type: (sqlite3.Row) -> None
    """
    Update the 'received' status for the entry in the database that corresponds to the primary key

    :param sqlite3.Row record:
    :return: None
    """
    with SQLiteDB() as cursor:
        cursor.execute("UPDATE impression_table SET received='True' WHERE pk=?;", (record['pk'],))


def update_db_identify_active_pod(record):
    # type: (sqlite3.Row) -> None
    """
    Update the records in the database to reflect which FreeWheel Ad Response the Adaptive Player is using.

    :param sqlite3.Row record:
    :return: None

    Important:
        Now that we've encountered a Slot Impression, we have some information about which Ad Response the Adaptive
        Player is using.  To compensate for the lack of information about the impressions being sent, this function
        is used to set the 'active' field of all of the records to be 'True' and all other Ad Pod ID's are flagged
        as inactive or 'False'.
    """
    pod_id = record['pod_id']
    with SQLiteDB() as cursor:
        logging.debug('Marking the records in the database to identify pod_id={0} as active.'.format(pod_id))
        cursor.execute("UPDATE impression_table SET active='False';")
        cursor.execute("UPDATE impression_table SET active='True' WHERE pod_id=?;", (pod_id,))


def print_database():
    """
    Displays all the records in the SQL database.  The records are all of the Slot, Quartile, and 3rd-Party Tracking
    Impressions parsed from FreeWheel's SmartXML Ad Response.
    """
    with SQLiteDB() as cursor:
        cursor.execute("UPDATE impression_table SET sent='False' WHERE sent IS NULL")
        cursor.execute("UPDATE impression_table SET received='False' WHERE received IS NULL")

        # Provide debugging output per user's request
        if logging.getLogger().isEnabledFor(logging.DEBUG):
            cursor.execute('''
                SELECT pk, pod_id, sent, received, slot_id, time_position, ad_id, event, url, creative_url 
                FROM impression_table
            ''')
            column_names = tuple(map(lambda x: x[0], cursor.description))
            rows = cursor.fetchall()
            table = '\n'.join(map(str, rows))
            msg = 'Total Number of Records in the Database: {0}\n{1}\n{2}'
            logging.debug(msg.format(len(rows), column_names, table))
            print()


def correlate_sm3_beacon_params(beacon):
    # type: (Impression) -> Impression
    """
    Attempt to correlate and update missing beacon parameters which are not
    present or available when parsing the parameters from the Adaptive
    Player log event.

    Note:
        If we previously encountered a FreeWheel Ad Response, then ideally we've
        parsed the XML body for the Ad Slot ID and prepared it as key in the
        template dictionary.
        If, for some reason, we haven't seen an Ad Response, then the key won't
        exist and we'll throw a key error.
          - Internal events: generated by the AP & can't be validated against the XML
          - External events: slot/quartile/tracking events sent to FreeWheel and 3rd parties
          - Response events: Ad event callbacks (i.e., slotImpression, quartile callbacks, and tracking events)

    :param Impression beacon:
    :return: beacon
    :rtype: Impression
    """
    # Prepared SQL Statements
    table = 'impression_table'
    # Suppressing the "active='True'" to see if it helps catalog beacons
    query_internal_slot = \
        "SELECT * FROM {tn} WHERE " \
        "slot_id={slot_id} AND event='{impression}' AND sent is NULL ORDER BY pk LIMIT 1"
    query_internal_quartile = \
        "SELECT * FROM {tn} WHERE " \
        "slot_id='{slot_id}' AND ad_id='{ad_id}' AND event='{impression}' AND type='quartile' ORDER BY pk DESC LIMIT 1"
    query_external_slot = \
        "SELECT * FROM {tn} WHERE " \
        "type='{beacon_type}' AND event='{impression}' AND url='{url}' AND sent is NULL"
    query_external_quartile = \
        "SELECT * FROM {tn} WHERE " \
        "slot_id='{slot_id}' AND ad_id='{ad_id}' AND type='{beacon_type}' AND event='{impression}' AND url='{url}' " \
        "AND sent is NULL"
    query_external_tracking = \
        "SELECT * FROM {tn} WHERE " \
        "slot_id='{slot_id}' AND ad_id='{ad_id}' AND type='{beacon_type}' AND event='{impression}' AND url='{url}' " \
        "AND sent IS NULL"
    query_response_slot = \
        "SELECT * FROM {tn} WHERE " \
        "slot_id='{slot_id}' AND type='{beacon_type}' AND event='{impression}' AND url='{url}' " \
        "AND received is NULL"
    query_response_quartile = \
        "SELECT * FROM {tn} WHERE " \
        "slot_id='{slot_id}' AND ad_id='{ad_id}' AND type='{beacon_type}' AND event='{impression}' AND url='{url}' " \
        "AND received is NULL"
    query_response_tracking = \
        "SELECT * FROM {tn} WHERE slot_id='{slot_id}' AND ad_id='{ad_id}' AND url='{url}' AND received is NULL"
    try:
        # Initialize local variables
        beacon_type = beacon.beacon_type
        source = beacon.source

        # Connect to the database
        with SQLiteDB(row=True) as cursor:
            # TODO: Need to determine if we want to catalog the internal 'slotCompleted' or 'AdBreakCompleteEvents'.
            #  Currently, these type of events are being marked as invalid and are not being cataloged.
            #  Example: Failed to catalog invalid beacon: source=Internal, beacon_event=AdBreakCompleteEvent,
            #  slot_id=97076, ad_id=None

            # Internal Fired Events
            if 'Internal' in source:
                if 'slot' in beacon_type:
                    record = cursor.execute(query_internal_slot.format(tn=table, **vars(beacon))).fetchone()
                    if record:
                        update_db_identify_active_pod(record)
                        beacon = beacon_update_from_sql_record(beacon, record)
                elif 'quartile' in beacon_type:
                    record = cursor.execute(query_internal_quartile.format(tn=table, **vars(beacon))).fetchone()
                    if record:
                        update_db_identify_active_pod(record)
                        beacon = beacon_update_from_sql_record(beacon, record)

            # External Fired Events
            elif 'External' in source:
                if 'slot' in beacon_type:
                    # stupid; the slot_id isn't consistent it's 1073834654 in the XML and 0!? in the Impression's URL.
                    record = cursor.execute(query_external_slot.format(tn=table, **vars(beacon))).fetchone()
                    if record:
                        update_db_successfully_sent_impression(record)
                        update_db_identify_active_pod(record)
                        beacon = beacon_update_from_sql_record(beacon, record)
                    else:
                        logging.warning("Failed to match beacon against FreeWheel\'s XML")
                elif 'quartile' in beacon_type:
                    record = cursor.execute(query_external_quartile.format(tn=table, **vars(beacon))).fetchone()
                    if record:
                        update_db_successfully_sent_impression(record)
                        beacon = beacon_update_from_sql_record(beacon, record)
                    else:
                        logging.warning("Failed to match beacon against FreeWheel\'s XML")
                elif 'tracking' in beacon_type:
                    record = cursor.execute(query_external_tracking.format(tn=table, **vars(beacon))).fetchone()
                    if record:
                        update_db_successfully_sent_impression(record)
                        beacon = beacon_update_from_sql_record(beacon, record)
                    else:
                        logging.warning("Failed to match beacon against FreeWheel\'s XML")

            # Response Fired Events
            elif 'Response' in source:
                if 'slot' in beacon_type:
                    record = cursor.execute(query_response_slot.format(tn=table, **vars(beacon))).fetchone()
                    if record:
                        update_db_successfully_received_impression(record)
                        beacon = beacon_update_from_sql_record(beacon, record)
                    else:
                        logging.warning("Failed to match beacon against FreeWheel\'s XML")
                elif 'quartile' in beacon_type:
                    record = cursor.execute(query_response_quartile.format(tn=table, **vars(beacon))).fetchone()
                    if record:
                        update_db_successfully_received_impression(record)
                        beacon_update_from_sql_record(beacon, record)
                    else:
                        logging.warning("Failed to match beacon against FreeWheel\'s XML")
                elif 'tracking' in beacon_type:
                    record = cursor.execute(query_response_tracking.format(tn=table, **vars(beacon))).fetchone()
                    if record:
                        update_db_successfully_received_impression(record)
                        beacon = beacon_update_from_sql_record(beacon, record)
                    else:
                        logging.warning("Failed to match beacon against FreeWheel\'s XML")
            return beacon

    except Exception as ex:
        logging.error(format_exception(ex))


def correlate_beacon_params(beacon):
    # type: (Impression) -> Impression
    """
    Attempt to correlate and update missing beacon parameters which are not present or available when parsing the
    parameters from the Adaptive Player log event.

    Note:
        If we previously encountered a FreeWheel Ad Response, then ideally we've parsed the XML body for the Ad Slot ID
        and prepared it as key in the template dictionary.  If, for some reason, we haven't seen an Ad Response, then
        the key won't exist and we'll throw a key error.
          - Internal events: generated by the Adaptive Player and can't be validated against the XML
          - External events: slot/quartile/tracking events sent to FreeWheel and 3rd parties
          - Response events: Ad event callbacks (i.e., slotImpression, quartile callbacks, and tracking events)

    :param Impression beacon:
    :return: beacon
    :rtype: Impression
    """
    table = 'impression_table'
    sql_query_internal_slot = \
        "SELECT * FROM {tn} WHERE " \
        "slot_id={slot_id} AND event='{impression}' AND sent is NULL ORDER BY pk DESC LIMIT 1"
    sql_query_internal_quartile = \
        "SELECT * FROM {tn} WHERE " \
        "slot_id='{slot_id}' AND ad_id='{ad_id}' AND event='{impression}' AND type='quartile' ORDER BY pk DESC LIMIT 1"
    sql_query_external_slot = \
        "SELECT * FROM {tn} WHERE " \
        "time_position={time_position} AND type='{beacon_type}' AND event='{impression}' AND url='{url}' " \
        "AND sent is NULL"
    sql_query_external_quartile = \
        "SELECT * FROM {tn} WHERE " \
        "time_position={time_position} AND ad_id='{ad_id}' AND type='{beacon_type}' AND event='{impression}' " \
        "AND url='{url}' AND sent is NULL AND active='True'"
    sql_query_external_tracking = \
        "SELECT * FROM {tn} WHERE " \
        "type='{beacon_type}' AND event='{impression}' AND url='{url}' AND sent IS NULL AND active='True'"
    sql_query_response_slot = \
        "SELECT * FROM {tn} WHERE " \
        "time_position={time_position} AND type='{beacon_type}' AND event='{impression}' AND url='{url}' " \
        "AND received is NULL AND active='True'"
    sql_query_response_quartile = \
        "SELECT * FROM {tn} WHERE " \
        "time_position={time_position} AND ad_id='{ad_id}' AND type='{beacon_type}' AND event='{impression}' " \
        "AND url='{url}' AND received is NULL AND active='True'"
    sql_query_response_tracking = \
        "SELECT * FROM {tn} WHERE url='{url}' AND received is NULL AND active='True'"

    try:
        beacon_type = beacon.beacon_type
        source = beacon.source
        with SQLiteDB(row=True) as cursor:
            # TODO: Need to determine if we want to catalog the internal 'slotCompleted' or 'AdBreakCompleteEvents'.
            #  Currently, these type of events are being marked as invalid and are not being cataloged.
            #  Example: Failed to catalog invalid beacon: source=Internal, beacon_event=AdBreakCompleteEvent,
            #  slot_id=97076, ad_id=None

            # Internal Fired Events
            if 'Internal' in source:
                if 'slot' in beacon_type:
                    record = cursor.execute(sql_query_internal_slot.format(tn=table, **vars(beacon))).fetchone()
                    if record:
                        beacon = beacon_update_from_sql_record(beacon, record)
                elif 'quartile' in beacon_type:
                    record = cursor.execute(sql_query_internal_quartile.format(tn=table, **vars(beacon))).fetchone()
                    if record:
                        beacon = beacon_update_from_sql_record(beacon, record)

            # External Fired Events
            elif 'External' in source:
                if 'slot' in beacon_type:
                    # stupid; the slot_id isn't consistent it's '1073834654' in the XML and '0' in the Impression's URL.
                    record = cursor.execute(sql_query_external_slot.format(tn=table, **vars(beacon))).fetchone()
                    if record:
                        update_db_successfully_sent_impression(record)
                        update_db_identify_active_pod(record)
                        beacon = beacon_update_from_sql_record(beacon, record)
                    else:
                        logging.warning("Failed to match beacon against FreeWheel\'s XML")
                elif 'quartile' in beacon_type:
                    record = cursor.execute(sql_query_external_quartile.format(tn=table, **vars(beacon))).fetchone()
                    if record:
                        update_db_successfully_sent_impression(record)
                        beacon = beacon_update_from_sql_record(beacon, record)
                    else:
                        logging.warning("Failed to match beacon against FreeWheel\'s XML")
                elif 'tracking' in beacon_type:
                    record = cursor.execute(sql_query_external_tracking.format(tn=table, **vars(beacon))).fetchone()
                    if record:
                        update_db_successfully_sent_impression(record)
                        beacon = beacon_update_from_sql_record(beacon, record)
                    else:
                        logging.warning("Failed to match beacon against FreeWheel\'s XML")

            # Response Fired Events
            elif 'Response' in source:
                if 'slot' in beacon_type:
                    record = cursor.execute(sql_query_response_slot.format(tn=table, **vars(beacon))).fetchone()
                    if record:
                        update_db_successfully_received_impression(record)
                        beacon = beacon_update_from_sql_record(beacon, record)
                    else:
                        logging.warning("Failed to match beacon against FreeWheel\'s XML")
                elif 'quartile' in beacon_type:
                    record = cursor.execute(sql_query_response_quartile.format(tn=table, **vars(beacon))).fetchone()
                    if record:
                        update_db_successfully_received_impression(record)
                        beacon_update_from_sql_record(beacon, record)
                    else:
                        logging.warning("Failed to match beacon against FreeWheel\'s XML")
                elif 'tracking' in beacon_type:
                    record = cursor.execute(sql_query_response_tracking.format(tn=table, **vars(beacon))).fetchone()
                    if record:
                        update_db_successfully_received_impression(record)
                        beacon = beacon_update_from_sql_record(beacon, record)
                    else:
                        logging.warning("Failed to match beacon against FreeWheel\'s XML")
            return beacon

    except Exception as ex:
        logging.error(format_exception(ex))


def beacon_update_from_sql_record(beacon, record):
    # type: (Impression, sqlite3.Row) -> Impression
    """
    Use the record's values to update missing values missing from the beacon.

    :param Impression beacon:
    :param sqlite3.Row record:
    :return: The object view of the Impression
    :rtype: Impression
    """
    keys = ['ad_id', 'pk', 'pod_id', 'slot_id', 'time_position', 'tracking_num', 'type', 'url']
    for key in keys:
        beacon.__dict__[key] = record[key]
    beacon.impression = record['event']
    beacon.beacon_event = swap_event_term(beacon.impression)
    beacon.is_valid = True
    return beacon


def catalog(beacon):
    # type: (Impression) -> None
    """
    Use the template to record the occurrence of the Adaptive Player event.

    :param Impression beacon:
    :return: None
    """
    beacon_type = beacon.beacon_type
    event = beacon.beacon_event
    source = beacon.source

    try:
        logging.debug('Attempting to catalog the following beacon:')
        beacon.print_params()
        if beacon.is_valid:
            if 'slot' in beacon_type and event in ('AdBreakStartEvent', 'AdBreakCompleteEvent'):
                logging.debug('{0:-^100}'.format(''))
                logging.debug(event)
                logging.debug('{0:-^100}'.format(''))
            if 'slot' in beacon_type:
                journal.catalog_slot_impression(beacon)
            elif 'quartile' in beacon_type:
                journal.catalog_quartile_impression(beacon)
            elif 'tracking' in beacon_type and source in ['External', 'Response']:
                journal.catalog_tracking_impression(beacon)

            logging.debug('Successfully cataloged {0}'.format(event))
        else:
            logging.error('Failed to catalog invalid beacon: {0}'.format(beacon.info))

    except KeyError as error:
        logging.error('KeyError: {0} - Invalid dictionary key while parsing log file'.format(error))
        logging.error('KeyError: {0} - Extracted values - {1}'.format(error, **beacon.__dict__.viewitems()))
        logging.error('KeyError: {0} - Offending log entry -- {1}'.format(error, beacon.logline))

    except Exception as ex:
        logging.error(format_exception(ex))


def db_catalog_beacon(beacon):
    """
    Update the database to record the occurrence of the Adaptive Player event.

    :param Impression beacon:
    :return: None
    """
    sql_statement = {
        'Internal': 'UPDATE impression_table SET internal_log=? WHERE pk=?;',
        'External': 'UPDATE impression_table SET sent_log=? WHERE pk=?;',
        'Response': 'UPDATE impression_table SET received_log=? WHERE pk=?;',
        'Invalid': 'INSERT INTO unmatched_table (log, pk) VALUES (?, ?);'
    }
    try:
        with SQLiteDB() as cursor:
            if beacon.is_valid:
                cursor.execute(sql_statement[beacon.source], (beacon.logline, beacon.pk))
                logging.debug('Valid Beacon. Updating database: {0}'.format(vars(beacon)))
            else:
                cursor.execute(sql_statement['Invalid'], (beacon.logline, beacon.pk))
                logging.debug('Invalid Beacon. Unable to catalog in the database: {0}'.format(vars(beacon)))
    except Exception as ex:
        logging.error('Problem updating the database records.')
        logging.error(format_exception(ex))


def db_catalog_http_status(beacon):
    # type: (Impression) -> None
    """
    Updates the Impression's HTTP Status in the database.

    :param impression beacon:
    :return None
    """
    if beacon.is_valid:
        with SQLiteDB() as cursor:
            cursor.execute('''
                UPDATE impression_table 
                   SET http_status = ? 
                 WHERE pk = ?;
            ''', (beacon.response_code, beacon.pk))
    else:
        msg = 'Invalid Beacon. Unable to catalog in the database: {0}'
        logging.warning(msg.format(vars(beacon)))


def populate_template(pod_id):
    # type: (object) -> None
    """
    Use the data from FreeWheel's XML Ad Response to prepare a template in
    another dictionary (e.g., journal) with the expected Advertisement
    Slot ID (e.g., slotImpression), Advertisement IDs (e.g., Quartiles),
    and 3rd-party Tracking Impressions.

    :param int pod_id: The ID of the Ad Request submitted to FreeWheel.
    :return: None
    """
    with SQLiteDB(row=True) as cursor:
        table = 'impression_table'

        # Gets the unique creative renditions
        # SQL = '''SELECT DISTINCT
        #          impression_table.index, impression_table.slot_id, impression_table.ad_id, creative_table.url
        #          FROM impression_table INNER JOIN creative_table on creative_table.ad_id = impression_table.ad_id'''

        slot = "SELECT DISTINCT pod_id, slot_id, time_position FROM {tn} WHERE pod_id={pod_id} AND type=='slot'"
        for record in cursor.execute(slot.format(tn=table, pod_id=pod_id)):
            msg = 'Inserting Slot Impression: pod_id={0} slot_id={1} time_position={2}'
            logging.debug(msg.format(*record))
            journal.insert_slot_element(**record)

        quartile = "SELECT DISTINCT pod_id, slot_id, ad_id FROM {tn} WHERE pod_id={pod_id} AND type=='quartile'"
        for record in cursor.execute(quartile.format(tn=table, pod_id=pod_id)):
            msg = 'Inserting Quartile Impression: pod_id={0} slot_id={1} ad_id={2}'
            logging.debug(msg.format(*record))
            journal.insert_quartile_element(**record)
            # Hack to track the metrics
            for impression in Impression.event_table:
                event = swap_event_term(impression)
                pargs = record['pod_id'], record['slot_id'], record['ad_id'], event
                journal.metric_expected(*pargs)

        tracking = "SELECT DISTINCT pod_id, slot_id, ad_id, event, tracking_num FROM {tn} " \
                   "WHERE pod_id={pod_id} AND type=='tracking'"
        for record in cursor.execute(tracking.format(tn=table, pod_id=pod_id)):
            msg = "Inserting Tracking Impression: pod_id={0} slot_id={1} ad_id={2} event={3} tracking_num={4}"
            logging.debug(msg.format(*record))
            event = swap_event_term(record['event'])
            pargs = record['pod_id'], record['slot_id'], record['ad_id'], event, record['tracking_num']
            journal.add_tracking_url(*pargs)

        creative = "SELECT DISTINCT pod_id, slot_id, ad_id, creative_url, duration FROM {tn} " \
                   "WHERE pod_id={pod_id} AND type='quartile' AND event='defaultImpression'"
        for record in cursor.execute(creative.format(tn=table, pod_id=pod_id)):
            msg = 'Inserting Creative: pod_id={0} slot_id={1} ad_id={2} creative_url={3} duration={4}'
            logging.debug(msg.format(*record))
            journal.insert_creative(**record)


def sm3_handle_points(match):
    """
    Process the SM3PointsCacheItem. Each time we encounter it, we compare it
    against the last one seen.  If they are identical, then we update the
    existing entry so we have a recent timestamp.  Otherwise, we save
    the current SM3PointsCacheItem so we can compare it against subsequent
    ones and reference it later when needed.

    :param _sre.SRE_Match match: The SM3PointsCacheItem object.
    :returns: None
    """

    try:
        logging.debug('Processing SM3PointsCacheItem from: {0}.'.format(match.group('timestamp')))
        with SQLiteDB() as cursor:
            logging.debug('Fetching the previous SM3PointsCacheItem log entry.')
            cursor.execute("SELECT sm3pointscacheitem FROM dai_events_table ORDER BY pod_id DESC LIMIT 1")
            record = cursor.fetchone()
        if record:
            logging.debug('Comparing the previous SM3PointsCacheItem log entry to the current one.')
            previous = sm3_remove_debug_info(re.match(r'^.*JSON File: (?P<json>{".*}$)', record[0]))
            current = sm3_remove_debug_info(match)
            if previous == current:
                logging.debug('Previous SM3PointsCacheItem is identical to the current one. Nothing updated.')
            else:
                logging.debug('Previous SM3PointsCacheItem is different from the current one. Saving in the database.')
                pod_id = sm3_store_log(match)
                sm3_store_ad_request(match, pod_id)
                sm3_store_ad_response(match, pod_id)
                sm3_collect_info(match, pod_id)
                populate_template(pod_id)
        else:
            logging.debug('No previous SM3PointsCacheItem found. Saving the current one in the database.')
            pod_id = sm3_store_log(match)
            sm3_store_ad_request(match, pod_id)
            sm3_store_ad_response(match, pod_id)
            sm3_collect_info(match, pod_id)
            populate_template(pod_id)
    except Exception as ex:
        logging.error('Problem processing SM3 Points Cache Item #{0}')
        logging.error(format_exception(ex))


def sm3_store_log(match):
    """
    Stores the log entry for the SM3PointsCacheItem.

    :param object match: The SM3PointsCacheItem object.
    :return: lastrowid: The ID of the last row inserted.
    :rtype: int
    """
    with SQLiteDB() as cursor:
        cursor.execute('''
            INSERT INTO dai_events_table (sm3pointscacheitem) 
            VALUES (?);
        ''', (match.group("logline"),))
        return cursor.lastrowid


def sm3_store_ad_request(match, pod_id):
    """
    Parses the SM3PointsCacheItem object for the Advertisement Request URL
    submitted to FreeWheel and stores it.

    :param _sre.SRE_Match match: The SM3PointsCacheItem object.
    :param int pod_id: The ID of the Ad Request submitted to FreeWheel.
    :return: None
    """
    timestamp = match.group('timestamp')
    points = json.loads(match.group('json')).get('points')
    for point in points:
        if point.get('_debug'):
            url = point.get('_debug').get('vmapRequestUrl')
            if url:
                url = ' '.join([timestamp, url])
                with SQLiteDB() as cursor:
                    cursor.execute('''
                        UPDATE dai_events_table 
                           SET ad_request = ? 
                         WHERE pod_id = ?;
                    ''', (url, pod_id))
                    break


def sm3_store_ad_response(match, pod_id):
    """
    Parses the SM3PointsCacheItem object for the Advertisement Response from
    FreeWheel and stores it.

    :param object match: The SM3PointsCacheItem object.
    :param int pod_id: The ID of the Ad Request submitted to FreeWheel.
    :return: None
    """
    timestamp = match.group('timestamp')
    points = json.loads(match.group('json')).get('points')
    for point in points:
        if point.get('_debug'):
            vmap_response = point.get('_debug').get('vmapResponse')
            if vmap_response:
                xml = ' '.join([timestamp, base64.b64decode(vmap_response)])
                with SQLiteDB() as cursor:
                    cursor.execute('''
                        UPDATE dai_events_table 
                           SET ad_response = ? 
                         WHERE pod_id = ?;
                    ''', (xml, pod_id))
                    break


def sm3_drop_db_duplicates():
    """
    Removes the duplicate SM3PointsCacheItems for the Event Callback information
    stored in the database.
    """
    with SQLiteDB() as cursor:
        logging.debug('Removing duplicate SM3 Points Cache records from the database.')
        cursor.execute('''
            DELETE FROM impression_table 
             WHERE ROWID NOT IN (
                SELECT MIN(rowid) 
                  FROM impression_table 
                 GROUP BY slot_id, ad_id, event, type, url
                )
        ''')


def sm3_collect_info(match, pod_id):
    """
    Parse the SM3PointsCacheItem for the Event Callback information and store
    them in the database.  This object contains information about all the
    Impression Events, such as the Advertisement Slot IDs (e.g., slotImpression),
    Advertisement IDs (e.g., Quartiles), and 3rd-party Tracking Impressions.

    :param object match: The SM3PointsCacheItem object.
    :param int pod_id: The ID of the Ad Request submitted to FreeWheel.
    :return: None
    """
    events = ['AdBreakStart', 'AdStart', 'AdQuartile1', 'AdMidway', 'AdQuartile3', 'AdComplete', 'AdBreakComplete']
    results = list()
    # Convert the json string to a json dictionary and retrieve the "points" object
    points = json.loads(match.group('json')).get('points')
    # Loop through the points object and retrieve the information about the points
    for point in points:
        # Determine if the point is a Slot Impression (e.g., AdBreakStart and AdBreakComplete)
        if point.get('adBreakId') and point.get('events') and point.get('type') in [events[0], events[-1]]:
            for event in point['events']:
                for url in event['trackingUrls']:
                    results.append({
                        'pod_id': pod_id,
                        'slot_id': point['adBreakId'],
                        'ad_id': None,
                        'type': 'slot',
                        'event': swap_event_term(point['type']),
                        'duration': round(point['duration']/1000),
                        'fire_time': None,
                        'tracking_num': None,
                        'url': url
                    })

        # Determine if the point is an Ad Quartile (e.g., AdStartEvent, AdQuartile1Event, etc)
        elif point.get('adBreakId') and point.get('events') and point.get('type') in events[1:6]:
            for event in point['events']:
                # With SM3PointsCacheItems, there is no distinction between quartiles and tracking events.  Instead,
                # the events are in one list which makes it a bit more difficult to generate a properly formatted DAI
                # report for the QA team to validate when we can't easily distinguish between a quartile (important)
                # and a tracking event (less important).
                if point['type'] == 'AdStart':
                    # Seems the 'AdStart' events have 'http://adStatsElb' as their first entry, so it needs to be
                    # re-inserted after the quartile event to classify it as a tracking event.
                    if 'http://adStatsElb' in event['trackingUrls'][0]:
                        event['trackingUrls'].insert(1, event['trackingUrls'].pop(0))
                for index, url in enumerate(event['trackingUrls']):
                    # Attempt to separate quartile events from tracking events based on the index of the list.
                    # Quartiles appear to be first and the remaining items should be tracking events.
                    if index == 0:
                        beacon_type = 'quartile'
                        tracking_index = None
                    else:
                        beacon_type = 'tracking'
                        tracking_index = index
                    results.append({
                        'pod_id': pod_id,
                        'slot_id': point['adBreakId'],
                        'ad_id': point['adId'],
                        'type': beacon_type,
                        'event': swap_event_term(point['type']),
                        'duration': round(point['duration']/1000),
                        'fire_time': point['assetTime'],
                        'tracking_num': tracking_index,
                        'url': url
                    })

    # For each impression in the list of results, take keys from the dict as
    # SQL params and execute the SQL statement.
    with SQLiteDB() as cursor:
        logging.debug('Storing Impressions from SM3 Points Cache Item into the database:')
        cursor.executemany('''
            INSERT INTO impression_table
                (pod_id, slot_id, ad_id, type, event, url, duration, fire_time, tracking_num)
            VALUES
                (:pod_id, :slot_id, :ad_id, :type, :event, :url, :duration, :fire_time, :tracking_num);
            ''', results)

        # Provide debugging output per user's request
        if logging.getLogger().isEnabledFor(logging.DEBUG):
            cursor.execute("SELECT * FROM impression_table WHERE pod_id=?", (pod_id,))
            column_names = tuple(map(lambda x: x[0], cursor.description))
            rows = cursor.fetchall()
            table = "\n".join(map(str, rows))
            msg = "Number of Impressions in SM3\'s Ad Response #{0}: {1}\n{2}\n{3}"
            logging.debug(msg.format(pod_id, len(rows), column_names, table))


def sm3_remove_debug_info(match):
    # type: (object) -> object
    """
    Remove the debug information from the SM3PointsCacheItem. In order to
    determine if the previous and current SM3PointsCacheItems are identical
    or not, the '_debug' information needs to be removed before performing
    the comparision.

    :param object match: Instance of SimpleGrep
    :returns: points
    :rtype: json
    """
    points = json.loads(match.group('json')).get('points')
    for point in points:
        if '_debug' in point:
            del point['_debug']
            return points
    else:
        return points


def swap_event_term(event):
    # type: (str) -> str
    """
    Returns the Adaptive Player's terminology with FreeWheel's terminology or
    vice versa. Example: swaps the 'slotImpression' term used by FreeWheel
    with 'AdBreakStartEvent' used the Adaptive Player log.

    :param str event: Impression event.
    :returns: The terminology that matches the corresponding event.
    :rtype: str
    """
    event_table = OrderedDict([
        ('slotImpression', 'AdBreakStartEvent'),
        ('defaultImpression', 'AdStartEvent'),
        ('firstQuartile', 'AdQuartile1Event'),
        ('midPoint', 'AdMidwayEvent'),
        ('thirdQuartile', 'AdQuartile3Event'),
        ('complete', 'AdCompleteEvent'),
        ('slotCompleted', 'AdBreakCompleteEvent')
    ])
    for key, value in event_table.items():
        if event in value:
            return key
        elif event in key:
            return value


def print_border_long():
    print('{0:-^91}'.format(''))


def print_short_border():
    print('{0:-^45}'.format(''))


def write_ad_response_to_file(pod_id, xml_string):
    # type: (int, str) -> None
    """
    Saves FreeWheel's SmartXML Response to a temporary directory as a JSON.

    :param int pod_id: The ID of the Ad Request submitted to FreeWheel.
    :param str xml_string: Contains FreeWheel's SmartXML document
    :return None
    """
    try:
        directory = tempfile.gettempdir()
        filename = 'FreeWheel_XML_Ad_Response_num_{0}.xml'.format(str(pod_id).zfill(2))
        filepath = '/'.join([directory, filename])
        logging.info("Writing FreeWheel\'s Ad Response #{0} to {1}".format(pod_id, filepath))
        xml = minidom.parseString(xml_string).toprettyxml(indent='    ')
        with io.open(filepath, 'w', encoding='utf-8') as outfile:
            outfile.write(xml)
    except Exception as ex:
        logging.error("Problem writing FreeWheel\'s XML Ad Response out to disk.")
        logging.error(format_exception(ex))


def write_sm3_to_file(pod_id, string):
    # type: (int, str) -> None
    """
    Saves the SM3PointsCacheItem to a temporary directory as a JSON.

    :param int pod_id: The ID of the Ad Request submitted to FreeWheel.
    :param str string: Contains SM3 Points Cache Item log entry from the player.log
    :return None
    """
    try:
        directory = tempfile.gettempdir()
        filename = 'SM3PointsCacheItem_num_{0}.txt'.format(str(pod_id).zfill(2))
        filepath = '/'.join([directory, filename])
        logging.info('Writing SM3 Points Cache Item #{0} to {1}'.format(pod_id, filepath))
        with open(filepath, 'w') as outfile:
            outfile.write(string)
    except Exception as ex:
        logging.error('Problem writing SM3 Cache Point Items out to disk.')
        logging.error(format_exception(ex))


def save_html_report_to_disk(pod_id, slot_id, content):
    # type: (int, unicode, str) -> None
    """
    Saves the Dynamic Ad Insertion report to a temporary directory.

    :param int pod_id: The ID of the Ad Request submitted to FreeWheel.
    :param unicode slot_id: Slot Impression Id
    :param str content: The HTML document
    :return None
    """
    try:
        directory = ((sys.argv[2][::-1]).split('\\', 1))[1][::-1]
        ##directory = tempfile.gettempdir()
        filename = 'Ad_Response_num_{0}_Slot_ID_{1}.html'.format(str(pod_id).zfill(2), slot_id)
        filepath = '/'.join([directory, filename])
        logging.info('Writing Ad Response #{0} for Slot_ID {1} to {2}'.format(pod_id, slot_id, filepath))
        with open(filepath, 'w') as outfile:
            outfile.write(content)
    except Exception as ex:
        logging.error('Problem writing DAI Validation Report out to disk.')
        logging.error(format_exception(ex))


def save_html_report_to_database(pod_id, slot_id, content):
    """ Saves the DAI Validation Report to the database. """
    with SQLiteDB() as cursor:
        sql = "INSERT into dai_report_table (pod_id, slot_id, content) VALUES (?, ?, ?);"
        cursor.execute(sql, (pod_id, slot_id, content))


def fetch_html_report_from_database(slot_id=None):
    """ Retrieves the HTML DAI Validation Report from the database. """
    with SQLiteDB(row=True) as cursor:
        if slot_id is None:
            cursor.execute("SELECT * FROM dai_report_table;")
        else:
            cursor.execute("SELECT * FROM dai_report_table WHERE slot_id=?;", (slot_id,))
        for row in cursor.fetchall():
            save_html_report_to_disk(row['pod_id'], row['slot_id'], row['content'])


def write_journal():
    # type: () -> None
    """ Saves the contents of the journal to disk for debugging. """
    directory = tempfile.gettempdir()
    filename = 'journal.json'
    filepath = '/'.join([directory, filename])
    with open(filepath, 'w') as outfile:
        json.dump(journal.dictionary, outfile)


def pandas_set_options():
    """ Sets some options in Pandas to define how the output should be displayed. """
    pd.set_option('display.expand_frame_repr', False)  # Prevent the table from line wrapping
    pd.set_option('display.float_format', '{:.0f}'.format)
    pd.set_option('display.max_colwidth', 255)
    pd.set_option('display.max_columns', None)
    pd.set_option('display.max_rows', None)
    pd.set_option('colheader_justify', 'center')


def pandas_to_csv():
    directory = tempfile.gettempdir()
    filename = 'report_dai_output.csv'
    filepath = '/'.join([directory, filename])
    connection = sqlite3.connect(SQLiteDB().path)
    query = '''
            SELECT pk, pod_id, slot_id, time_position, ad_id, event, sent, received, creative_url 
            FROM impression_table
            '''
    df = pd.io.sql.read_sql_query(query, connection, index_col='pk')
    df.to_csv(filepath)
    print('Saving CSV file to {0}'.format(filepath))


def display_qvt_and_ad_request_parameters(data):
    """
    Compare QVT params to the corresponding Ad Request params.
    """
    pd.set_option('colheader_justify', 'center')
    pd.set_option('display.expand_frame_repr', False)  # Prevent the table from line wrapping
    pd.set_option('display.max_columns', None)
    pd.set_option('max_colwidth', -1)
    df = pd.DataFrame(data)
    df.index.name = 'Parameter Name:'
    df['Values Match'] = df['Ad Request'] == (df['QVT'])
    df = df[['Values Match', 'QVT', 'Ad Request']]
    output = df.to_string()
    output = re.sub('True', colored('True', 'green'), output.rstrip())
    output = re.sub('False', colored('False', 'red'), output.rstrip())
    print(output)


def pandas_summarize_slot_and_quartile_metrics():
    # type: () -> None
    """
    Use the pandas library to provide a metrics summary of the Slot
    and Quartile impressions.
    """

    # TODO: Look into using the records from the SQL database as
    #  a source to generate metrics from
    # df = pd.io.sql.read_sql_query(
    #       "SELECT
    #           pk, pod_id, sent, received, slot_id, time_position, ad_id, event, url
    #        FROM
    #           impression_table", conn, index_col='pk'
    # )

    print_border_long()
    print('Summary: Number of Impressions by Impressions Type')
    print_border_long()

    columns = ['Expected', 'Internal', 'External', 'Response']
    rows = Impression.event_table.values()  # Store the list of indices

    # Read the Metrics dictionary into Pandas DataFrame
    df = pd.DataFrame([])
    for item in columns:
        df[item] = pd.Series(journal.dictionary['Metrics'][item])

    df.index.name = 'Impression Type'  # Change the name of the index
    df = df[columns]  # Re-order the columns in the correct sequence
    # Attempt to fix future warning about passing list-likes to .loc
    # df = df.reindex(rows)  # Re-order the indices in the correct sequence
    df = df.loc[rows, :]  # Re-order the indices in the correct sequence
    # abce = df.loc['AdBreakCompleteEvent', :]
    df = df.drop('AdBreakCompleteEvent')  # Drop observations about the AdBreakCompleteEvent (unused)
    total = df.sum()  # Return the sum of each of the columns
    success_rate = ((df.sum() / df['Expected'].sum()).apply('{:.0%}'.format))
    # df = abce
    df.loc['Total'] = total  # Add a row with the total sum of each column
    df.loc['Success Rate'] = success_rate  # Add a row with the calculated success rate
    df = df.fillna('-')  # Fill the 'NaN's with a hyphen
    print('{0}'.format(df))
    print_border_long()
    print('Note:')
    print('\tColumn    Description')
    print('\tExpected: Number of Impressions expected as seen in FreeWheel\'s SmartXML')
    print('\tInternal: Number of Impressions fired by Adaptive Player')
    print('\tExternal: Number of Impressions fired by FWAdPod')
    print('\tResponse: Number of Responses received from FreeWheel')
    print('\t\'AdBreakCompleteEvent\' is internal to the Adaptive Player (not included in calculations).')


def pandas_summarize_tracking_metrics():
    # type: () -> None
    """
    Use the pandas library to provide metrics of the Tracking impressions.
    """
    print('\n\n\n\n')
    print_border_long()
    print('Summary: Number of Tracking URLs by Impressions Type')
    print_border_long()

    # Read the Metrics dictionary into Pandas DataFrame
    df = pd.DataFrame([])
    rows = Impression.event_table.values()  # Store the list of indices
    trk_columns = ['TrackingURL Expected', 'TrackingURL Sent', 'TrackingURL Received']
    for item in trk_columns:
        df[item] = pd.Series(journal.dictionary['Metrics'][item])
    if not df.empty:
        df = df.rename(columns={'TrackingURL Expected': 'Expected',
                                'TrackingURL Sent': 'Sent',
                                'TrackingURL Received': 'Response'})
        df.index.name = 'Impression Type'  # Change the name of the index
        # df = df.loc[rows, :]  # Re-order the indices in the correct sequence
        # Attempt to fix future warning about passing list-likes to .loc
        df = df.reindex(rows)  # Re-order the indices in the correct sequence
        df = df.drop('AdBreakCompleteEvent')  # Drop observations about the AdBreakCompleteEvent (unused)
        total = df.sum()  # Return the sum of each of the columns
        success_rate = ((df.sum() / df['Expected'].sum()).apply('{:.0%}'.format))
        df.loc['Total'] = total  # Add a row with the total sum of each column
        df.loc['Success Rate'] = success_rate  # Add a row with the calculated success rate
        df = df.fillna('-')  # Fill the 'NaN's with a hyphen
        print('{0}'.format(df))
        print_border_long()
        print('Note:')
        print('\tColumn    Description')
        print('\tExpected: Number of expected 3rd Party Tracking Impressions')
        print('\tSent:     Number of Impression Fired by Adaptive Player')
        print('\tResponse: Number of Responses Received from 3rd Parties')
    else:
        print('No Tracking Impressions Found:')


def print_pandas_groupby_summary():
    # type: () -> None
    pd.set_option('display.max_columns', None)
    pd.set_option('display.max_rows', None)
    pd.set_option('display.max_colwidth', -1)
    query = '''
            SELECT pk, pod_id, slot_id, time_position, ad_id, event, sent, received, creative_url 
              FROM impression_table 
            '''
    connection = sqlite3.connect('/tmp/sqlite::memory:?cache=shared')
    df = pd.io.sql.read_sql_query(query, connection, index_col='pk')

    df.rename(columns={
        'index': 'Ad Pod ID',
        'slot_id': 'Slot ID',
        'time_position': 'Time Position',
        'ad_id': 'Advertisement ID',
        'event': 'Impression',
        'sent': 'Sent',
        'received': 'Received'
    }, inplace=True)
    columns = ['XML Response', 'Slot ID', 'Time Position', 'Advertisement ID', 'Impression']
    grouped = df.groupby(columns, sort=False)[['Sent', 'Received']].count()

    print_border_long()
    print('Summary: Number of Impressions by Impressions Type')
    print_border_long()
    print(grouped)
    logging.debug('Report: \n{0}'.format(grouped))


def format_exception(ex):
    template = 'An exception of type {0} occurred. Arguments: {1!r}.'
    return template.format(type(ex).__name__, ex.args)


def merge_multiple_lines(source):
    """
    Merges log entries spanning multiple lines into one line.

    Newer releases of the Adaptive Player have log entries that span multiple
    lines to make them more human readable. This function determines if the
    log entry starts with a timestamp (e.g., YYYY/MM/DD HH:MM:SS), and if it
    does not, begins collapsing those multiple lines into one.

    :param file source: Adaptive Player's player.log file
    :rtype: Iterator[str]
    """
    previous_line = ''
    timestamp = r"^\d{4}[/.-]\d{2}[/.-]\d{2}\s\d{2}:\d{2}:\d{2}"
    for logline in source:
        if re.search(timestamp, logline):
            if memoryview:
                yield ' '.join(previous_line.split())
                previous_line = logline.strip()
        else:
            previous_line = ' '.join([previous_line, logline.strip()])
    yield ' '.join(previous_line.split())


def to_html():
    # type: () -> None
    """ Generates the DAI Validation Report in HTML format. """
    # Query the database for all of the Ad Responses (pod_ids) encountered in
    # the player.log; Convert results to a list.
    pod_ids = db_fetch_pod_ids()
    # Loop through each of the Ad Responses found in the database.
    for pod_id in pod_ids:
        # Query the database for the Ad Breaks (slot_IDs) contained with each
        # of the Ad Responses.
        # So far we've encountered three scenarios for the Ad Responses:
        # 1) One Slot ID (normal use case)
        # 2) Multiple Slot IDs (unusual)
        # 3) No Slot IDs (unusual)
        slot_ids = db_fetch_slot_ids(pod_id)
        # Loop through each of the Ad Breaks contained within the Ad Response
        for slot_id in slot_ids:
            # Query the database for the QVT information with this slot ID;
            # generate an empty one if necessary
            qvt_record = db_fetch_qvt_record(slot_id)
            generate_html_report(pod_id, slot_id, qvt_record)


def db_fetch_pod_ids():
    with SQLiteDB(row=True) as cursor:
        cursor.execute("SELECT DISTINCT(pod_id) FROM impression_table;")
        return [row['pod_id'] for row in cursor.fetchall()]


def db_fetch_slot_ids(pod_id):
    with SQLiteDB(row=True) as cursor:
        cursor.execute("SELECT DISTINCT(slot_id) FROM impression_table WHERE pod_id=?;", (pod_id,))
        return [row['slot_id'] for row in cursor.fetchall()]


def db_fetch_qvt_record(slot_id):
    with SQLiteDB(row=True) as cursor:
        cursor.execute("SELECT * FROM qvt_table WHERE cue_point_number=?", (slot_id,))
        record = cursor.fetchone()
        if record is None:
            logging.warning('No QVT records found for slot_id={0}. Generating an empty set.'.format(slot_id))
            cursor.execute("INSERT INTO qvt_table (cue_point_number) VALUES (?);", (slot_id,))
            cursor.execute("SELECT * FROM qvt_table WHERE cue_point_number=?", (slot_id,))
            record = cursor.fetchone()
        return dict_from_row(record)


def generate_html_report(pod_id, slot_id, qvt_record):
    """ Generate the HTML Report to display to the end user. """
    content = to_html_display_title(slot_id)
    content += to_html_display_program_version_info()
    content += to_html_display_channel_info(pod_id, slot_id, qvt_record)
    content += to_html_display_controls()
    content += to_html_display_qvt_link(qvt_record)
    content += to_html_display_ad_request_url(pod_id)
    content += to_html_display_validated_ad_request_url(pod_id, qvt_record)
    content += to_html_display_ad_response_xml(pod_id, qvt_record)
    #content += to_html_display_media_m3u8_extension(pod_id)
    content += to_html_display_beacon_summary(pod_id, slot_id)
    content += to_html_display_beacon_validation(slot_id)
    content += to_html_display_unmatched_beacons_and_responses(slot_id)
    save_html_report_to_database(pod_id, slot_id, content)


def to_html_display_title(slot_id):
    # type: (unicode) -> str
    """
    Provides the initial HTML heading and style for the HTML output.

    :param unicode slot_id:
    :return: html
    :rtype: str
    """

    html = "<!DOCTYPE html>"
    html += "<head>"
    html += "<title>slid: {0} </title>".format(slot_id)
    html += "<style>"
    html += "body { background-color: black; color: white; }"
    html += "a { color: rgb(250,162,30); }"  # Sling TV Orange
    html += ".title { font-size: 2em; font-weight: bold; text-align: center; color: rgb(250,162,30); }"  # Orange
    html += ".info { display: flex; font_size: 1.25em; }"
    html += ".beacon { display: flex; font-size: 10pt; font-family: Courier New; }"
    html += ".subtitle { font-size: 1.5em; text-decoration:underline; color: rgb(20,171,224); }"  # Blue
    html += ".indent { margin-left: 2em; }"
    html += ".double_indent { margin-left: 4em; }"
    html += ".triple_indent { margin-left: 6em; }"
    html += ".quad_indent { margin-left: 8em; }"
    html += ".no_wrap { white-space: nowrap; }"
    html += ".date_time { color: cyan; }"
    html += ".code { color: magenta; }"
    html += ".overlay_able { position: relative; display: inline-block; }"
    html += ".overlay { white-space: nowrap; visibility: hidden; background-color: grey; text-align: left; "
    html += "border-radius: 6px; padding: 5px; position: absolute; z-index: 1; bottom: 100%; left: 0%; "
    html += "opacity: 0; transition: opacity 1s; }"
    html += ".overlay_able:hover .overlay { visibility: visible; opacity: 1; }"
    html += "</style>"
    html += "</head>"

    html += "<body>"

    html += "<script>"
    html += "document.addEventListener('keydown', function (event) {"
    html += "if (event.keyCode == 72) { document.getElementById('Home').scrollIntoView(); }"
    html += "else if (event.keyCode == 49) { document.getElementById('QVT Link').scrollIntoView(); }"
    html += "else if (event.keyCode == 50) { document.getElementById('Ad Request URL').scrollIntoView(); }"
    html += "else if (event.keyCode == 51) { document.getElementById('Ad Response XML').scrollIntoView(); }"
    html += "else if (event.keyCode == 52) { document.getElementById('Beacon Validation').scrollIntoView(); }"
    html += "});"

    html += "function toggleQVTJSONContent() {"
    html += "var x = document.getElementById('qvt_json_content');"
    html += "var button = document.getElementById('qvt_json_content_button');"
    html += "if (x.style.display === 'none') { x.style.display = 'block'; button.innerText = 'HIDE'; }"
    html += "else { x.style.display = 'none'; button.innerText = 'SHOW'; }"
    html += "}"

    html += "function toggleXMLContent() {"
    html += "var x = document.getElementById('xml_content');"
    html += "var button = document.getElementById('xml_content_button');"
    html += "if (x.style.display === 'none') { x.style.display = 'block'; button.innerText = 'HIDE'; }"
    html += "else { x.style.display = 'none'; button.innerText = 'SHOW'; }"
    html += "}"
    html += "</script>"
    return html


def to_html_display_program_version_info():
    html = "<div align=right><font size='2'>{0}</font></div>"
    return html.format(__version__)


def to_html_display_channel_info(pod_id, slot_id, qvt_record):
    """
    Wraps info about the Channel, its Asset, the Start/End Times, and Duration in HTML.

    :param int pod_id: The ID of the Ad Request submitted to FreeWheel.
    :param sqlite3.dbapi2.Row qvt_record:
    :param unicode slot_id:
    :return: html
    :rtype: str
    """

    if 'Missing' in qvt_record['title']:
        title = MISSING
    else:
        title = qvt_record['title']

    if 'Missing' in qvt_record['channel']:
        channel = MISSING
    else:
        channel = qvt_record['channel']

    duration = qvt_record['duration']
    start_time = convert_epoch_to_datestr(qvt_record['start_offset_with_delay'])
    end_time = convert_epoch_to_datestr(qvt_record['stop_offset_with_delay'])

    html = "<div class='title' id='Home'>"
    html += "DAI Validation Report for Ad Request Number: {0}<br>".format(pod_id)
    html += "Slot ID: {0}<br>".format(slot_id)
    html += "</div>"
    html += "<div class='info'>"
    html += "<div>"
    html += "Channel:<br>"
    html += "Asset:<br>"
    html += "Start Time:<br>"
    html += "End Time:<br>"
    html += "Duration:<br>"
    html += "</div>"
    html += "<div style='margin-left: 1em;'>"
    html += "{0}<br>".format(channel)
    html += "{0}<br>".format(title)
    html += "<span class='date_time'>{0}</span><br>".format(start_time)
    html += "<span class='date_time'>{0}</span><br>".format(end_time)
    html += "<span class='date_time'>{0}</span> seconds<br>".format(duration)
    html += "</div>"
    html += "</div>"
    return html


def to_html_display_controls():
    # type: () -> str
    """
    Display controls to provide the ability to navigate the HTML document via mouse or keyboard.

    :return: html
    :rtype: str
    """
    html = "<hr>"
    html += "<button onclick=\"document.getElementById('Home').scrollIntoView();\">"
    html += "Go Home (or Press: \'H\')</button> "
    html += "<button onclick=\"document.getElementById('QVT Link').scrollIntoView();\">"
    html += "Go to: QVT Link (or Press: \'1\')</button> "
    html += "<button onclick=\"document.getElementById('Ad Request URL').scrollIntoView();\">"
    html += "Go to: Ad Request URL (or Press: \'2\')</button> "
    html += "<button onclick=\"document.getElementById('Ad Response XML').scrollIntoView();\">"
    html += "Go to: Ad Response XML (or Press: \'3\')</button> "
    html += "<button onclick=\"document.getElementById('Beacon Validation').scrollIntoView();\">"
    html += "Go to: Beacon Validation (or Press: \'4\')</button>"
    html += "<hr>"
    return html


def to_html_display_qvt_link(qvt_record):
    # type: (sqlite3.Row) -> str
    """
    Displays the URL for the QVT and the JSON object of the entire QVT.

    :param sqlite3.dbapi2.Row qvt_record: Contains parameters related to the QVT
    :return: html: The QVT Link Section of the HTML document
    :rtype: str
    """
    logline = qvt_record['log']
    json_html = "<font color='red'>{QVT:Missing}</font>"
    timestamp = MISSING
    url = 'Missing'
    if re.search(r"ad_info.*ad_breaks", logline):
        qvt_string = re.match(r'^.*AdaptiveVideo Timeline loaded: (?P<qvt>{".*}(\s|$))', logline).group('qvt')
        if qvt_string:
            json_data = json.loads(qvt_string)
            json_html = json.dumps(json_data, indent=4).replace('    ', '&emsp;&emsp;').replace('\n', '<br>')
            timestamp = re.match(r'^(?P<date>\d{4}/\d{2}/\d{2}\s\d{2}:\d{2}:\d{2})', logline).group(1)
            url = qvt_record['url']
    html = "<div id='QVT Link'>"
    html += "<div class='subtitle'>QVT Link:</div><br>"
    html += "Date and Time: <span class='date_time'>{0}</span><br>".format(timestamp)
    html += "<span class='no_wrap'>URL: <a href='{0}' target='_blank'> {0}</a></span><br>".format(url)
    html += "JSON: <button id=\"qvt_json_content_button\" onclick=\"toggleQVTJSONContent()\">HIDE</button><br>"
    html += "<div id='qvt_json_content'>{0}</div>".format(json_html)
    html += "</div></div>"
    return html


def to_html_display_ad_request_url(pod_id):
    """
    Displays the parameters from the Ad Request URL submitted to FreeWheel.

    :param int pod_id: The ID of the Ad Request submitted to FreeWheel.
    :return: HTML formatted output
    :rtype: str
    """
    params = [
        'flag', 'nw', 'csid', 'caid', 'asnw', 'ssnw', 'prof', 'afid', 'fw_vcid',
        '_fw_vcid2', 'slid', 'tpcl', 'tpos', 'maxd', 'mind', 'cpsq', 'ssto'
    ]

    with SQLiteDB() as cursor:
        cursor.execute('''
            SELECT ad_request 
              FROM dai_events_table 
             WHERE pod_id=?;
        ''', (pod_id,))
        ad_request_log = cursor.fetchone()[0]
        ad_request = ParseAdRequest(ad_request_log)

    ts = ad_request.timestamp
    url = ad_request.url

    html = "<hr>"
    html += "<div id='Ad Request URL'>"
    html += "<div class='subtitle'>Ad Request URL:</div><br>"
    html += "Date and Time: <span class='date_time'>{0}</span><br>".format(ts)
    html += "<span class='no_wrap'>URL: {0}</span><br>".format(url)

    # Loop through the Ad Request parameters by importance.
    html += "Parameters:<br>"
    html += "<div class='indent'>"
    html += "<table>"
    html += "<tr><td>--- Important ---</td></tr>"
    for key in params:
        html += "<tr>"
        html += "<td>{0}:</td>".format(key)
        html += "<td><span class='code'>{0}</span></td>".format(ad_request.params[key])
        # html += "<td><span class='code'>{0}</span></td>".format(ad_request.params[key][0])
        html += "</tr>"
    html += "<tr><td><br></td></tr>"

    # Loop through the less important Ad Request parameters
    # and exclude any parameters where the values are missing.
    html += "<tr><td>--- Secondary ---</td></tr>"
    for key, value in ad_request.params.items():
        if key not in params and "Missing" not in value:
            html += "<tr>"
            html += "<td>{0}:</td>".format(key)
            html += "<td><span class='code'>{0}</span></td>".format(ad_request.params[key])
            html += "</tr>"
    html += "</table></div></div>"
    return html


def to_html_display_validated_ad_request_url(pod_id, qvt_record):
    """
    Displays the validated parameters from the Ad Request URL.

    :param int pod_id: The ID of the Ad Request submitted to FreeWheel.
    :param obj qvt_record: Info about the QVT
    :return: HTML formatted output
    :rtype: str
    """
    validated = validate_ad_request_url(pod_id, qvt_record)
    html = "<hr>"
    html += "<div id='Validated Ad Request URL'>"
    html += "<div class='subtitle'>Validated Ad Request URL:</div><br>"
    for section in validated:
        html += section + ":<br>"
        html += "<div class='indent'>"
        if validated[section]['pass'] == 'True':
            html += '{0}'.format(PASS)
        elif validated[section]['pass'] == 'False':
            html += '{0}'.format(FAIL)
        else:
            html += '{0}'.format(SKIP)
        html += "<br>"
        html += "<div class='indent'>"
        html += "<div style='display: flex;'>"
        html += "<div>"
        html += "Found:<br>"
        html += "Expected:"
        html += "</div>"
        html += "<div style='margin-left: 1em;'>"
        html += "<span class='code'>" + validated[section]['found'] + "</span><br>"
        html += "<span class='code'>" + validated[section]['expected'] + "</span>"
        html += "</div>"
        html += "</div>"
        html += "</div>"
        html += "</div>"
    html += "</div>"
    return html


def validate_ad_request_url(pod_id, qvt_info):
    """ Validates the parameters in the Ad Request URL against the QVT. """

    def compare(expected, found):
        """ Compares QVT params (expected) against the Ad Request's (found). """
        if expected == found:
            result = 'True'
        else:
            result = 'False'

        # Temporary kludge until we can handle missing keys in QVT
        if expected == '0':
            expected = 'Missing Parameter in QVT'

        # Print dashes if the param is not present for both QVT and Ad Request.
        if 'Missing' in expected and 'Missing' in found:
            expected = found = '-----'
            result = 'Skip'
        return {'found': found, 'expected': expected, 'pass': result}

    def fetch_request(pod_id, slot_id):
        """ Retrieves a specific Ad Request. """
        with SQLiteDB() as cursor:
            cursor.execute('''
                SELECT ad_request 
                  FROM dai_events_table 
                 WHERE pod_id=?;
            ''', (pod_id,))
            r = ParseAdRequest(cursor.fetchone()[0])
            for request in r.adrequest_qsl:
                if request['slid'] == slot_id:
                    return request

    # Initialize variables
    missing = 'Missing'
    results = OrderedDefaultDict()
    ad_request = fetch_request(pod_id, qvt_info['cue_point_number'])
    key_order = [
        # Key order (Param, QVT, Ad Request)
        ('Adapt URL', 'adapt_url', 'adapt_url'),
        ('AFID', 'afid', 'afid'),
        ('ASNW', 'asnw', 'asnw'),
        ('CAID', 'caid', 'caid'),
        ('FW URL', 'fw_url', 'fw_url'),
        ('FW Capabilities', 'flag', 'flag'),
        ('NW',   'nw', 'nw'),
        ('SSNW', 'ssnw', 'ssnw'),
        ('PROF', 'prof', 'prof'),
        ('MIND', 'mind', 'mind'),
        ('MAXD', 'maxd', 'maxd'),
        ('TPCL', 'type', 'tpcl'),
        ('CSID', 'csid', 'csid'),
        ('SLID', 'cue_point_number', 'slid'),
        ('CPSQ', 'cue_point_number', 'cpsq'),
        ('SSTO', 'cue_point_number', 'ssto'),
        ('TPOS', 'tpos', 'tpos')
    ]

    for keys in key_order:
        x, y, z = keys
        expected, found = qvt_info[y], ad_request[z]
        if x not in ['AFID', 'TPOS']:
            results[x] = compare(expected, found)
        elif x == 'AFID':
            #if missing not in expected and missing not in found:
            results[x] = compare(expected, found)
        elif x == 'TPOS':
            if is_float(expected):
                expected = float(expected)
                if expected.is_integer():
                    expected = str(int(expected))
                else:
                    expected = str(expected)
            results[x] = compare(expected, found)
    results = cdn_property_validation(results, qvt_info)
    return results


def cdn_property_validation(results, qvt):
    """ Validate parameters against expected values for the CDN Property. """
    error = 'Error: Incorrect QVT value for CDN environment ({0})'
    cdn_mapping = {
        # Production Environment
        'cbd46b77.cdn.cms.movetv.com': {
            'Adapt URL': 'http://p-adapt.movetv.com',
            'FW URL': 'http://5d40b.s.fwmrm.net/ad/g/1',
            'NW': '381963',
            'SSNW': '381963',
            'PROF': '381963:sling'
        },
        # Beta Environment
        '93a256a7.cdn.cms.movetv.com': {
            'Adapt URL': 'http://b-adapt.movetv.com',
            'FW URL': 'http://5d40a.s.fwmrm.net/ad/g/1',
            'NW': '381962',
            'SSNW': '381962',
            'PROF': '381962:sling'
        }
    }
    for cdn in cdn_mapping:
        if cdn in qvt['url']:
            for key, value in cdn_mapping[cdn].items():
                if value not in results[key]['found']:
                    results[key]['pass'] = 'False'
                    results[key]['expected'] = ' '.join([value, error.format(cdn)])
    return results


def to_html_display_ad_response_xml(pod_id, qvt):
    # type: (str) -> str
    """
    Displays the XML Ad Response in HTML format so it can be displayed properly
    in the DAI Validation Report.

    :param int pod_id: The ID of the Ad Request submitted to FreeWheel.
    :returns: HTML formatted output for the Ad Response XML Section.
    :rtype: str
    """
    with SQLiteDB() as cursor:
        cursor.execute('''
            SELECT ad_response 
              FROM dai_events_table 
             WHERE pod_id = ?;
        ''', (pod_id,))
        response = cursor.fetchone()
    if response[0] is not None:
        ts = response[0][:19]
        xml_string = response[0].split(' ', 2)[2]
        html_validate_xml = validate_xml(xml_string, qvt)
    else:
        xml_string = '''
            <?xml version="1.0" encoding="UTF-8"?>
            <errors><error name="MISSING XML"/></errors>
        '''
    html = "<hr>"
    html += "<div id='Ad Response XML'>"
    html += "<div class='subtitle'>Ad Response XML:</div><br>"
    html += "Date and Time: <span class='date_time'>{0}</span><br>".format(ts)
    tree = ElementTree.ElementTree(ElementTree.fromstring(xml_string))
    errors = tree.find('errors')
    if errors is not None:
        error_list = list()
        html += "<div class='indent'>XML Errors:</div>"
        for elem in errors.iter(tag='error'):
            error_list.append((elem.get('id'), elem.get('name'), elem.get('severity')))
        for error in error_list:
            html += "<div class='double_indent'>"
            html += "<font color='red'>"
            html += "Error ID:{0} Name:{1} Severity:{2}".format(error[0], error[1], error[2])
            html += "</font></div>"
    else:
        html += "<div class='indent'>XML Errors: None</div>"
    html += "<br>"
    html += "<button id='xml_content_button' onclick='toggleXMLContent()'>HIDE</button><br>"
    html += "<div class='no_wrap'</div>"
    html += "<div id='xml_content'>"
    html += '{0}'.format(
                    minidom.parseString(xml_string)
                           .toprettyxml(indent='    ')
                           .replace('    ', '&emsp;&emsp;')
                           .replace('<', '&lt;')
                           .replace('>', '&gt;')
                           .replace('\n', '<br>')
                    )
    html += "</div></div>"
    html += html_validate_xml
    return html


def to_html_display_media_m3u8_extension(pod_id):

    def ad_creatives(pod_id):
        """ Retrieve Ad Creative records. """
        with SQLiteDB(row=True) as cursor:
            cursor.execute('''
                SELECT *
                  FROM creative_table
                 WHERE pod_id = ?;
            ''', (pod_id,))
            return cursor.fetchall()

    def endswith_m3u8(row):
        """ Return whether or not the Ad URL ends with m3u8. """
        if row['asset_url'].endswith('m3u8'):
            return FOUND
        else:
            return MISSING

    html = '''
        <br>
        <hr>
        <div class='subtitle' id=>Media File Extension:</div><br>
        <div class='indent'>
        <table border=1 >
        <tr>
        <th>Ad ID</th>
        <th>M3U8</th>
        <th>Asset URL</th>
        </tr>
    '''

    for row in ad_creatives(pod_id):
        html += "<tr>"
        html += "<td valign='top' align='center'> {0} </td>"
        html += "<td valign='top' align='center'> {1} </td>"
        html += "<td valign='top' align='left'>   {2} </td>"
        html += "</tr>"
        html.format(row['ad_adId'], endswith_m3u8(row), row['asset_url'])
    html += "</table></div><br>"
    return html


# TODO: Need to come up with a way to obtain metrics without using the journal.dictionary
def to_html_display_beacon_summary(pod_id, slot_id):
    # type: (int, unicode) -> str
    """
    Displays the Beacon Summary in HTML format so it can be displayed properly
    in the DAI report. This is needed to properly display the metrics about
    the Tracking Impression.

    :param int pod_id: The ID of the Ad Request submitted to FreeWheel.
    :param unicode slot_id: The slotImpression ID
    :returns: HTML formatted output for the Beacon Summary Section.
    :rtype: str
    """
    data = journal.dictionary['XML Index'][pod_id]['Slot ID'][slot_id]
    time_position = data['Time Position']
    ad_count = len(data['Ad References'])
    slot_duration = fetch_slot_impression_duration(slot_id)

    html = "<hr>"
    html += "<div class='subtitle' id=>Beacon Summary:</div><br>"
    html += "<div class='indent'>"
    html += "<table>"
    html += "<tr><td>FreeWheel Ad Response Number:</td><td>{0}</td></tr>".format(pod_id)
    html += "<tr><td>Slot ID:</td><td>{0}</td></tr>".format(slot_id)
    html += "<tr><td>Time Position:</td><td>{0}</td></tr>".format(time_position)
    html += "<tr><td>Number of Advertisments:</td><td>{0}</td></tr>".format(ad_count)
    html += "<tr><td>Total Ad Duration (secs):</td><td>{0}</td></tr>".format(slot_duration)
    html += "</table>"
    html += "</div>"
    html += "<br>"

    styles = [
        hover(),
        dict(selector='th', props=[('font-size', '14px'),
                                   # ('font-family', 'Helvetica, Arial, sans-serif'),
                                   ('color', 'white'),
                                   ('background-color', 'rgb(10, 10, 10)'),
                                   ('text-align', 'center')]),
        dict(selector='td', props=[('font-size', '14px'),
                                   # ('font-family', 'Helvetica, Arial, sans-serif'),
                                   ('text-align', 'center')]),
        dict(selector='tr', props=[('line-height', '11px')]),
        dict(selector='caption', props=[('caption-side', 'top')])
    ]

    count = 0
    ad_ids = data['Ad References'].keys()
    for ad_id in ad_ids:
        count += 1
        html += "<div class='double_indent'>"
        columns = ['Expected', 'Internal', 'External', 'Response']
        rows = Impression.event_table.values()  # Store the list of indices

        # Use Pandas module to ingest Quartile metrics.
        df1 = pd.DataFrame([])
        for item in columns:
            df1[item] = pd.Series(data['Ad References'][ad_id]['Metrics'][item])

        df1.index.name = 'Impression Type'  # Change the name of the index
        df1 = df1[columns]  # Re-order the columns in the correct sequence
        df1 = df1.loc[rows, :]  # Re-order the indices in the correct sequence
        # Drop observations about the AdBreakStartEvent and AdBreakCompleteEvent
        df1.drop(['AdBreakStartEvent', 'AdBreakCompleteEvent'], inplace=True)
        total = df1.sum()  # Return the sum of each of the columns
        success_rate = ((df1.sum() / df1['Expected'].sum()).apply('{:.0%}'.format))
        df1.loc['Total'] = total  # Add a row with the total sum of each column
        df1.loc['Success Rate'] = success_rate  # Add a row with the calculated success rate
        df1 = df1.fillna('-')  # Fill the 'NaN's with a hyphen

        # Use Pandas module to ingest Tracking metrics.
        df2 = pd.DataFrame([])
        rows = Impression.event_table.values()  # Store the list of indices
        trk_columns = ['TrackingURL Expected', 'TrackingURL Sent', 'TrackingURL Received']
        for item in trk_columns:
            df2[item] = pd.Series(data['Ad References'][ad_id]['Metrics'][item])
        if not df2.empty:
            df2 = df2.rename(columns={'TrackingURL Sent': 'Sent', 'TrackingURL Received': 'Received'})
            df2.index.name = 'Impression Type'  # Change the name of the index
            # Attempt to fix future warning about passing list-likes to .loc
            # df2 = df2.loc[rows, :]  # Re-order the indices in the correct sequence
            df2 = df2.reindex(rows)  # Re-order the indices in the correct sequence
            # Drop observations about the AdBreakStartEvent and AdBreakCompleteEvent
            df2.drop(['AdBreakStartEvent', 'AdBreakCompleteEvent'], inplace=True)
            total = df2.sum()  # Return the sum of each of the columns
            success_rate = ((df2.sum() / df2['TrackingURL Expected'].sum()).apply('{:.0%}'.format))
            df2.loc['Total'] = total  # Add a row with the total sum of each column
            df2.loc['Success Rate'] = success_rate  # Add a row with the calculated success rate
            df2 = df2.fillna('-')  # Fill the 'NaN's with a hyphen

            # Glue the Quartile & Tracking DataFrames together and use the Pandas styler to format the HTML table
            result = pd.concat([df1, df2], axis=1, sort=False)
            html += (result.style.applymap(color_red, subset=['Internal', 'External', 'Response', 'Sent', 'Received'])
                     .set_table_styles(styles)
                     .set_properties(**{'text-align': 'center'})
                     .set_caption('Ad #:{}&emsp;&emsp;[Ad Id: {}]'.format(count, ad_id))
                     .render())
        else:
            # If the Advertisement didn't include Tracking Impressions, then don't include the Tracking Metrics.
            # TODO:  See about fixing the FutureWarning KeyError when passing list-lickes to .loc
            html += (df1.style.applymap(color_red, subset=['Internal', 'External', 'Response', 'Sent', 'Received'])
                     .set_table_styles(styles)
                     .set_properties(**{'text-align': 'center'})
                     .set_caption('Ad #:{}&emsp;&emsp;[Ad Id: {}]'.format(count, ad_id))
                     .render())
        html += "</div>"
        html += "<br>"
    return html


def to_html_display_beacon_validation(slot_id):
    # type: (unicode) -> object
    """
    Queries the SQL database for the given Slot Impression ID and identifies
    the event so it can be wrapped in HTML and displayed properly in the
    Beacon Validation Section of the DAI report.

    :param unicode slot_id: The Slot Impression ID.
    :returns: HTML formatted output
    :rtype: str
    """
    count = 0
    html = "<hr><div id='Beacon Validation'>"
    html += "<div class='subtitle'>Beacon Validation:</div><br>"
    with SQLiteDB(row=True) as cursor:
        cursor.execute("SELECT * FROM impression_table WHERE slot_id=?;", (slot_id,))
        records = cursor.fetchall()
        for record in records:
            if 'slotImpression' in record['event']:
                count = 0
                html += "<div class='indent'>"
                html += "SlotImpression ID : {slot_id}<br>".format(**record)
                html += to_html_beacon_event_info(record)
            elif 'quartile' in record['type']:
                if 'defaultImpression' in record['event']:
                    count += 1
                    html += to_html_advertisement_info(count, record)
                    html += to_html_beacon_event_info(record)
                else:
                    html += to_html_beacon_event_info(record)
            elif 'tracking' in record['type']:
                html += to_html_tracking_event_info(record)
            elif 'slotCompleted' in record['event']:
                html += "<br>"
                html += "<div class='indent'>Beacon Event : {event}<br>".format(**record)
                html += "<div class='indent beacon'><span class='no_wrap'>"
                html += "Internal: {internal_log}</span><br></div></div>".format(**record)
        return html


def to_html_display_unmatched_beacons_and_responses(slot_id):
    # type: () -> str
    """
    Queries a specific time frame to determine if the Adaptive Player sent any
    superfluous beacons pertaining to a given Slot ID.

    To determine the time frame of the slot ID being validated, the timestamp
    of the Ad Request is the "start time" (e.g., t0) and the slotImpression's
    expected_firing_time (e.g., t2), plus the sum of the duration of each Ad
    in the slot (e.g., d0), plus a time delay becomes the "end_time" (e.g,. tn)
    In essence, tn = t0 + t2 + d0 + ... + dn + time_delay.

    # -------------------------------------------------------------------------
    # Example:
    # -------------------------------------------------------------------------
          |--> Ad Request (start time)
          |   |--> Ad Response
          |   |   |--> slotImpression
          |   |   |--> unmatched beacon (defect)
          |   |   |--> defaultImpression
          |   |   |
          |   |   |   |--> firstQuartile
          |   |   |   |--> unmatched beacon (defect)
          |   |   |   |   ...
          |   |   |   |   ...
          |   |   |   |      |-> slotCompleted
          |   |   |   |      |   |--> unmatched beacon (defect)
          |   |   |   |      |   |    ...
          |   |   |   |      |   |                  |--> (end time)
      |---t0--t1--t2--t3-----t7--tn---[time delay]--tn-------------->
    # -------------------------------------------------------------------------

    Each result is wrapped in HTML so the records can be displayed properly in
    the Unmatched section of the DAI Validation report.

    :param unicode slot_id: The Slot Impression ID.
    :returns: HTML formatted output for the Unmatched Beacons Section.
    :rtype: str
    """
    def get_start_time(slot_id):
        """ Returns a UNIX timestamp of the Ad Request for this Slot ID. """
        milliseconds = '.000'
        with SQLiteDB() as cursor:
            cursor.execute('''
                    SELECT substr(ad_request, 1, 19)
                      FROM dai_events_table
                     WHERE ad_request
                      LIKE '%slid={slot_id}%';
            '''.format(slot_id=slot_id))
            date_string = cursor.fetchone()[0]
            date_string = date_string + milliseconds
            unix_ts = convert_datestr_to_unix_timestamp(date_string)
            return unix_ts

    def get_stop_time(slot_id):
        """ Returns a UNIX timestamp for when to stop searching. """
        time_delay_secs = 180
        with SQLiteDB() as cursor:
            cursor.execute('''
                    SELECT SUM(expected_firing_time + duration)
                      FROM impression_table
                     WHERE slot_id = :slot_id 
                       AND type = 'slot'
                       AND event = 'slotImpression'
            ''', {'slot_id': slot_id})
            unix_ts = cursor.fetchone()[0]
            return unix_ts + time_delay_secs

    def get_unmatched_impressions(start_ts, end_ts):
        """ Returns records found between this time frame. """
        with SQLiteDB(row=True) as cursor:
            cursor.execute('''
                SELECT log 
                  FROM unmatched_table
                 WHERE actual_firing_time 
               BETWEEN :start AND :end;
            ''', {'start': start_ts, 'end': end_ts})
            return cursor.fetchall()

    def to_html(line):
        """ Returns line wrapped in HTML. """
        return '''
            <div class='indent beacon'>
            <font color='red'><span class='no_wrap'>{0}</span>
            </font><br></div>
        '''.format(line)

    html = "<hr>"
    html += "<div id='Unmatched Beacons and Responses'>"
    html += "<div class='subtitle'>Unmatched Beacons and Responses:</div>"
    html += "<br>"

    t0 = get_start_time(slot_id)
    tn = get_stop_time(slot_id)
    if all([t0, tn]):
        records = get_unmatched_impressions(t0, tn)
        if records:
            for i, rec in enumerate(records):
                line = ' : '.join([str(i), rec['log'].encode('ascii', 'ignore')])
                html += to_html(line)
    else:
        html += '''
            <div class='indent beacon'>
            <font color='lime'>
            (PASS) No Unmatched Beacons
            </font><br></div>
        '''
    html += "</div><br><hr>"
    return html


def to_html_advertisement_info(count, record):
    # type: (object, sqlite3.Row) -> str
    """ Returns the Advertisement information wrapped in HTML.

    :param int count: Advertisement counter.
    :param sqlite3.Row record: The sqlite3 row object.
    :returns: Advertisement information wrapped in HTML
    :rtype: str
    """
    player = "http://demo.theoplayer.com/test-your-stream-with-statistics?url="
    html = '''
        <br><div class='indent'><hr>
        Ad Number   : {count}<br>
        Ad ID       : {ad_id}<br>
        Ad Duration : {duration} seconds<br>
        Ad Creative: <a href='{player}{creative_url}'target='_blank'>Click here to see the video</a><br>
        <hr></div>
    '''
    return html.format(count=count, player=player, **record)


def to_html_beacon_event_info(record):
    # type: (sqlite3.Row) -> str
    """ Returns the Impression Quartile information wrapped in HTML.

    :param object record: The sqlite3 row object
    :returns: Beacon information wrapped in HTML
    :rtype: str
    """
    html = '''
       <br>
       <div class='indent'>Beacon Event : {event}<br>
       <div class='indent beacon'><span class='no_wrap'>Internal: {internal_log}</span><br></div>
       <div class='indent beacon'><span class='no_wrap'>External: {sent_log}</span><br></div>
       <div class='indent beacon'><span class='no_wrap'>Response: {received_log}</span><br></div>
       <br>
       <div class='indent'>Tests:<br>
       <div class='indent beacon'>{beacons_found}: Expected Firing Time: {0} [delta: {delta_firing_time} secs]<br></div>
       <div class='indent beacon'>{beacons_found}: All Beacons Fired<br></div>
       <div class='indent beacon'>{beacon_firing_order}: Valid Firing Sequence for this Impression<br></div>
       <div class='indent beacon'>{http_status_msg}: HTTP Status: {http_status}<br></div>
       </div></div>
    '''
    firing_time = convert_epoch_to_datestr(record["expected_firing_time"])
    return html.format(firing_time, **record)


def to_html_tracking_event_info(record):
    # type: (sqlite3.Row) -> str
    """ Returns the Tracking information wrapped in HTML.

    :param object record: The sqlite3 row object
    :return: Tracking info wrapped in HTML.
    :rtype: str
    """
    html = '''
        <br><div class='indent'>
        <div class='double_indent'>Tracking URL #: {tracking_num}<br>
        <div class='indent beacon'><span class='no_wrap'>Sent: {sent_log}</span><br></div>
        <div class='indent beacon'><span class='no_wrap'>Received: {received_log}</span><br></div>
        <div class='indent beacon'><span class='no_wrap'>{http_status_msg}: HTTP Status: {http_status}<br></div>
        <div class='indent beacon'><span class='no_wrap'>{beacon_firing_order}: Valid Firing Sequence for this Impression<br></div>
        </div></div>
    '''
    return html.format(**record)


def calculate_actual_firing_time_for_adaptive_player():
    # type: () -> None
    """
    Updates the timestamp of the "actual_firing_time" parameter according
    to the timestamp of the log entry.  For each Impression in the database,
    attempt to parse the date-time string at the beginning of the log entry
    from the Adaptive Player log.  If the pattern matches, convert the
    date-time to a Unix timestamp.  Then, update the record's "actual_firing_time"
    parameter with this Unix timestamp to identify when the Adaptive Player
    "fired" the Impression.
    """
    re_datetime = r'^\d{4}[/.-]\d{2}[/.-]\d{2}\s\d{2}:\d{2}:\d{2}[.]\d+'
    with SQLiteDB(row=True) as cursor:
        cursor.execute("SELECT pk, sent_log FROM impression_table WHERE sent_log <> '';")
        for row in cursor.fetchall():
            pk, sent_log = row
            m = re.match(re_datetime, sent_log)
            if m:
                date_string = m.group()
                unix_timestamp = convert_datestr_to_unix_timestamp(date_string)
                cursor.execute('''
                    UPDATE impression_table 
                       SET actual_firing_time = ? 
                     WHERE pk = ?;
                    ''', (unix_timestamp, pk)
                )
                msg = 'pk={0} actual_firing_time={1} sent_log={2}'
                logging.debug(msg.format(pk, unix_timestamp, sent_log))


def calculate_actual_firing_time_for_unmatched_beacons():
    # type: () -> None
    """
    Updates the timestamp of the "actual_firing_time" parameter according
    to the timestamp of the log entry.  For each Impression in the database,
    attempt to parse the date-time string at the beginning of the log entry
    from the Adaptive Player log.  If the pattern matches, convert the
    date-time to a Unix timestamp.  Then, update the record's "actual_firing_time"
    parameter with this Unix timestamp to identify when the Adaptive Player
    "fired" the Impression.
    """
    re_datetime = r'^\d{4}[/.-]\d{2}[/.-]\d{2}\s\d{2}:\d{2}:\d{2}[.]\d+'
    with SQLiteDB(row=True) as cursor:
        cursor.execute("SELECT pk, log FROM unmatched_table WHERE log <> '';")
        for row in cursor.fetchall():
            pk, log = row
            m = re.match(re_datetime, log)
            if m:
                date_string = m.group()
                unix_timestamp = convert_datestr_to_unix_timestamp(date_string)
                cursor.execute('''
                    UPDATE unmatched_table
                       SET actual_firing_time = ? 
                     WHERE pk = ?;
                    ''', (unix_timestamp, pk)
                               )
                msg = 'pk={0} actual_firing_time={1} log={2}'
                logging.debug(msg.format(pk, unix_timestamp, log))


def calculate_duration_for_slot_impression():
    # type: () -> None
    """
    Calculates the duration of each slotImpression.  The total duration
    of a slotImpression is calculated by adding up the duration of each
    of the individual Advertisements found within the slotImpression.
    """
    with SQLiteDB(row=True) as cursor:
        cursor.execute("SELECT DISTINCT(slot_id) FROM impression_table;")
        for row in cursor.fetchall():
            slot_id = row['slot_id']
            cursor.execute('''
                UPDATE impression_table 
                   SET duration = (
                        SELECT IFNULL(SUM(duration), 0)
                          FROM impression_table 
                         WHERE event = 'defaultImpression' 
                           AND type = 'quartile' 
                           AND slot_id = :slot_id
                        )
                WHERE event = 'slotImpression' 
                  AND type = 'slot' 
                  AND slot_id = :slot_id
            ''', {"slot_id": slot_id})


def calculate_expected_firing_time_for_slot_impression():
    # type: () -> None
    """
    Updates the timestamp of the slotImpression's "expected_firing_time"
    parameter using the start_offset_with_delay from the QVT table.

    The Slot Impression's expected_firing_time (t0) is the value taken from
    the QVT's start_offset_with_delay. This timestamp determines when the
    Adaptive Player is supposed to send the Impression. It is calculated
    when processing the Ad Break section QVT.

    # -------------------------------------------------------------------------
    # Example:
    # -------------------------------------------------------------------------
          |--> slotImpression
          |    t0 = qvt(start_offset_w/_delay = start_offset + playback_delay)
      |---t0-------------[Time]---->
    # -------------------------------------------------------------------------
    """
    with SQLiteDB(row=True) as cursor:
        cursor.execute('''
            UPDATE impression_table 
               SET expected_firing_time = (
                        SELECT start_offset_with_delay 
                          FROM qvt_table 
                         WHERE qvt_table.cue_point_number = impression_table.slot_id
                   ) 
             WHERE impression_table.type = 'slot' 
               AND impression_table.event = 'slotImpression' 
               AND EXISTS (
                        SELECT start_offset_with_delay 
                          FROM qvt_table 
                         WHERE qvt_table.cue_point_number = impression_table.slot_id
                   );
            ''')


def calculate_expected_firing_time_for_default_impression():
    # type: () -> None
    """
    Updates the timestamp of the defaultImpression's "expected_firing_time" parameter.

    A defaultImpression represents when an individual Ad is starting and the Adaptive
    Player is expected to send Impressions at scheduled times and the value of this
    timestamp is used to determine if the Adaptive Player sent the defaultImpression
    when it was supposed to.

    The timestamp for the expected_firing_time must be the same (i.e., t0) for the
    slotImpression and the defaultImpression of the first Ad. When the slotImpression
    contains multiple Ads, the slotImpression and Ad #1's defaultImpression will be
    sent at t0. Then, after the first Ad's duration (d0), the defaultImpression of
    Ad #2 will be sent at t1 (i.e., t1 = t0 + d0). Subsequent defaultImpressions
    will be sent after t0 plus the sum of the previous Ad's duration.
    In essence, tn = t0 + d0 + d1 + ... + dn

    # -------------------------------------------------------------------------
    # Example:
    # -------------------------------------------------------------------------
          |--> slotImpression
          |--> defaultImpression (Ad #1)
          |    t0 = t0
          |
          |    |--> defaultImpression (Ad #2)
          |    |    t1 = (t0 + d0)
          |    |
          |    |    |--> defaultImpression (Ad #3)
          |<d0>|<d1>|    t2 = (t0 + d0 + d1)
          |    |    |
      |---t0---t1---t2---[Time]---->
    # -------------------------------------------------------------------------
    """
    with SQLiteDB(row=True) as cursor:
        # Retrieve all of the slotImpressions.
        cursor.execute('''
            SELECT slot_id, expected_firing_time 
              FROM impression_table 
             WHERE event = 'slotImpression'
               AND expected_firing_time != 0;
        ''')
        slot_impression_records = cursor.fetchall()
        # Retrieve all of the defaultImpressions for a given slotImpression.
        for slot_record in slot_impression_records:
            slot_id, slot_impression_timestamp = slot_record
            total_ad_duration = 0
            cursor.execute('''
                SELECT pk, duration 
                  FROM impression_table 
                 WHERE slot_id = ?
                   AND type = 'quartile' 
                   AND event = 'defaultImpression' 
                   AND expected_firing_time = 0;
                ''', (slot_id, )
            )
            default_impression_records = cursor.fetchall()
            # Step through each of the defaultImpressions and calculate the
            # start_time of the defaultImpression. Add the Ad's duration
            # to the running total and use the sum of this value to calculate
            # the timestamp of when the next defaultImpression is to be sent.
            for default_record in default_impression_records:
                pk, ad_duration = default_record
                expected_firing_time = slot_impression_timestamp + total_ad_duration
                total_ad_duration += ad_duration
                cursor.execute('''
                    UPDATE impression_table 
                       SET expected_firing_time = ? 
                     WHERE pk = ?;
                    ''', (expected_firing_time, pk)
                )


def calculate_expected_firing_time_for_quartile_impression():
    # type: () -> None
    """
    Updates the timestamp of each of the Quartile's "expected_firing_time" parameter.

    Every Advertisement is divided into four equal intervals called quartiles and they
    measure how much of the Ad the viewer watched. Each Ad's quartile has a timestamp
    to determine if the Adaptive Player sent the Impression when it was supposed to.

    # --------------------------------------------------------------------------
    # Example:
    # --------------------------------------------------------------------------
          |--> slotImpression
          |--> defaultImpression
          |       |--> firstQuartile
          |       |       |--> midPoint
          |       |       |       |--> thirdQuartile
          |       |       |       |        |--> complete
          |       |       |       |        |
          |< 25% >|< 50% >|< 75% >|< 100% >|
          |       |       |       |        |
      |---t0------t1------t2------t3------t4---[Time]---->
    # --------------------------------------------------------------------------
    """
    quartiles = [('firstQuartile', 0.25), ('midPoint', 0.5), ('thirdQuartile', 0.75), ('complete', 0.90)]
    with SQLiteDB(row=True) as cursor:
        # Retrieve all of the defaultImpressions.
        cursor.execute('''
            SELECT pk, slot_id, ad_id, duration, expected_firing_time
              FROM impression_table
             WHERE type = 'quartile' 
               AND event = 'defaultImpression';
        ''')
        default_impression_records = cursor.fetchall()
        # Step through each defaultImpression and use its expected_firing_time
        # to compute when each of the remaining Ad quartiles should be sent.
        for row in default_impression_records:
            pk, slot_id, ad_id, ad_duration, expected_firing_time = row
            for quartile in quartiles:
                scheduled_start_time = expected_firing_time + (ad_duration * quartile[1])
                cursor.execute('''
                    UPDATE impression_table 
                       SET expected_firing_time = ? 
                     WHERE slot_id = ? 
                       AND ad_id = ? 
                       AND event = ?;
                    ''', (scheduled_start_time, slot_id, ad_id, quartile[0])
                )
                msg = 'slot_id={0}, ad_id={1}, quartile={2}, event_percent={3}, schedule_start_time={4}'
                logging.debug(msg.format(slot_id, ad_id, quartile[0], quartile[1], scheduled_start_time))


def calculate_difference_in_beacon_firing_times():
    # type: () -> None
    """
    For every Impression the Adaptive Player sent, calculate the delta between
    when the Adaptive Player was scheduled to send the Impression and when it
    was actually sent.  Then update the Impression's record with this delta.

    Note: A negative delta value indicates the actual firing time occurred
    before it was scheduled (i.e., too early). A positive delta value indicates
    the actual firing time occurred some time after the Adaptive Player was
    expected to send it.
    """
    values = list()
    with SQLiteDB(row=True) as cursor:
        cursor.execute('''
            SELECT pk, sent_log, expected_firing_time, actual_firing_time 
              FROM impression_table;
            ''')
        for row in cursor.fetchall():
            pk, sent_log, expected, actual = row
            if sent_log:
                delta = round(actual - expected, 2)
            else:
                delta = 0
            values.append({'pk': pk, 'delta': delta})
            msg = 'Delta in Firing Times: pk={0}, expected={1}, actual={2}, delta={3}, sent_log={4}'
            logging.debug(msg.format(pk, expected, actual, delta, sent_log))

        cursor.executemany('''
            UPDATE impression_table 
               SET delta_firing_time = :delta
             WHERE pk = :pk;
            ''', values
        )


def identify_missing_beacons():
    missing = 'Missing'
    with SQLiteDB(row=True) as cursor:
        cursor.execute("UPDATE impression_table SET internal_log=? WHERE internal_log='';", (missing,))
        cursor.execute("UPDATE impression_table SET sent_log=? WHERE sent_log='';", (missing,))
        cursor.execute("UPDATE impression_table SET received_log=? WHERE received_log='';", (missing,))


def color_beacons(args):
    """ Colors the log entry to indicate if it passed (green) or failed (red). """
    values = list()
    logs = ['internal_log', 'sent_log', 'received_log']
    with SQLiteDB(row=True) as cursor:
        cursor.execute('''
            SELECT pk, internal_log, sent_log, received_log 
              FROM impression_table;
        ''')
        for row in cursor.fetchall():
            row_as_dict = dict_from_row(row)
            # Determine if the timestamps begin with a 4 digit year
            for log in logs:
                logline = row_as_dict[log]
                if args.html:
                    if logline[:4].isdigit():
                        logline = "<font color='lime'>{0}</font>".format(logline)
                    else:
                        logline = "<font color='red'>{0}</font>".format(logline)
                if args.text:
                    if logline[:4].isdigit():
                        logline = colored('{0}'.format(logline), 'green')
                    else:
                        logline = colored('{0}'.format(logline), 'red')
                row_as_dict[log] = logline
            values.append(row_as_dict)

        cursor.executemany('''
            UPDATE impression_table 
               SET internal_log = :internal_log, 
                   sent_log = :sent_log, 
                   received_log = :received_log 
             WHERE pk = :pk;
        ''', values)


def validate_beacon_fired():
    # type: () -> None
    """
    Examines each impression in the database to see if the Adaptive Player sent
    the impression and received a response.
    """
    with SQLiteDB() as cursor:
        cursor.execute('''
            SELECT pk, sent_log, received_log 
              FROM impression_table;
        ''')
        for row in cursor.fetchall():
            pk, sent_log, received_log = row
            if all([sent_log[:4].isdigit(), received_log[:4].isdigit()]):
                result = PASS
            else:
                result = FAIL
            cursor.execute('''
                UPDATE impression_table 
                   SET beacons_found = ? 
                 WHERE pk = ?;
            ''', (result, pk))


def validate_beacon_firing_order():
    # type: () -> None
    """
    Queries all the records in the impression table and, for each beacon fired,
    determines if Adaptive Player reports the event in the correct sequence.
    Specifically, does the timestamp of when the beacon was sent occur before
    the timestamp of the beacon response.  Technically, it isn't possible for
    Adaptive Player to receive a response before a beacon is sent, so we're just
    checking to ensure the AP is logging the events in the correct sequence.
    """
    regex_timefmt = r'^(?P<date>\d{4}[/.-]\d{2}[/.-]\d{2}\s\d{2}:\d{2}:\d{2}[.]\d+).*'
    timestampfmt = '%Y/%m/%d %H:%M:%S.%f'
    with SQLiteDB() as cursor:
        cursor.execute("SELECT pk, sent_log, received_log FROM impression_table;")
        for row in cursor.fetchall():
            pk, sent_log, received_log = row
            time_sent = re.sub(regex_timefmt, r'\g<date>', sent_log)
            time_received = re.sub(regex_timefmt, r'\g<date>', received_log)
            # Determine if the timestamps begin with a 4 digit year
            if not all([time_sent[:4].isdigit(), time_received[:4].isdigit()]):
                result = FAIL
            else:
                result = datetime.strptime(time_sent, timestampfmt) \
                         < datetime.strptime(time_received, timestampfmt)
                msg = "Beacon Firing Order: key={0} result={1} sent='{2}' received='{3}'"
                logging.debug(msg.format(pk, result, time_sent, time_received))
                if result:
                    result = PASS
                else:
                    result = FAIL
            cursor.execute("UPDATE impression_table SET beacon_firing_order=? WHERE pk=?;", (result, pk))


def validate_overall_beacon_firing_order():
    # type: () -> None
    """
    Queries the records in the database and for each beacon fired and determines
    if Adaptive Player reports the event in the correct sequence. Specifically,
    does the timestamp of when the beacon was sent occur before the timestamp
    of the beacon response. Technically, it isn't possible for Adaptive Player
    to receive a response before a beacon is sent, so we're just checking the
    logging of events.
    """
    previous_event = ''
    previous_firing_time = ''
    previous_pk = ''
    with SQLiteDB(row=True) as cursor:
        cursor.execute("SELECT pk, event, actual_firing_time * FROM impression_table;")
        for row in cursor.fetchall():
            pk, event, actual_firing_time = row
            result = previous_firing_time <= actual_firing_time
            if result:
                logging.debug("True - '{0}' fired BEFORE '{1}'".format(previous_event, event))
            else:
                logging.debug("False - '{0}' fired AFTER '{1}'".format(previous_event, event))
                logging.debug('Updating primary_key: {0}'.format(previous_pk))
            previous_firing_time = actual_firing_time
            previous_event = event
            previous_pk = pk
            cursor.execute("UPDATE impression_table SET beacon_firing_order=? WHERE pk=?;", (result, pk))


def validate_http_response_status():
    # type: () -> None
    """ Determines if the HTTP response is valid. """
    with SQLiteDB(row=True) as cursor:
        cursor.execute("SELECT pk, http_status FROM impression_table;")
        for row in cursor.fetchall():
            pk, http_status = row
            response_code = int(http_status.strip() or 0)
            if response_code == 200 or response_code == 204:
                result = PASS
            else:
                result = FAIL
            cursor.execute("UPDATE impression_table SET http_status_msg=? WHERE pk=?;", (result, pk))


def to_text_impression_info():
    """ Displays information about the Impressions in text format. """
    count = 0
    with SQLiteDB(row=True) as cursor:
        for record in cursor.execute("SELECT * from impression_table;"):
            if 'slot' in record['type']:
                if 'Impression' in record['event']:
                    count = 0
                    print('\n')
                    print('{0:-^150}'.format(''))
                    print('Slot ID : {}'.format(record['slot_id']))
                    print('{0:-^150}'.format(''))
                    print('\tBeacon Event : {}'.format(record['event']))
                    print('\t\t\tInternal : {}'.format(record['internal_log']))
                    print('\t\t\tSent     : {}'.format(record['sent_log']))
                    print('\t\t\tReceived : {}'.format(record['received_log']))
                elif 'Completed' in record['event']:
                    print('\tBeacon Event : {}'.format(record['event']))
                    print('\t\t\tInternal : {}'.format(record['internal_log']))
                    print('\t\t\tSent     : {}'.format(record['sent_log']))
                    print('\t\t\tReceived : {}'.format(record['received_log']))
            elif 'quartile' in record['type']:
                if 'defaultImpression' in record['event']:
                    count += 1
                    print('\n{0:8}{1:-^50}'.format('', ''))
                    print('\t\tAd Number   : {}'.format(count))
                    print('\t\tAd ID       : {}'.format(record['ad_id']))
                    print('\t\tAd Duration : {} seconds'.format(record['duration']))
                    print('\t\tAd Creative : {}'.format(record['creative_url']))
                    print('{0:8}{1:-^50}\n'.format('', ''))
                    print('\t\t\tBeacon Event : {}'.format(swap_event_term(record['event'])))
                    print('\t\t\t\tInternal : {}'.format(record['internal_log']))
                    print('\t\t\t\tSent     : {}'.format(record['sent_log']))
                    print('\t\t\t\tReceived : {}'.format(record['received_log']))
                else:
                    print('\n\t\t\tBeacon Event : {}'.format(swap_event_term(record['event'])))
                    print('\t\t\t\tInternal : {}'.format(record['internal_log']))
                    print('\t\t\t\tSent     : {}'.format(record['sent_log']))
                    print('\t\t\t\tReceived : {}'.format(record['received_log']))
            elif 'tracking' in record['type']:
                print('\n\t\t\t\t{} {}'.format(record['type']
                                               .capitalize()
                                               .replace('Tracking', 'Tracking URL #:'),
                                               record['tracking_num']))
                print('\t\t\t\t\tSent     : {}'.format(record['sent_log']))
                print('\t\t\t\t\tReceived : {}'.format(record['received_log']))
                print('\t\t\t\t\tHTTP Response Code : {}'.format(record['http_status']))


def fetch_slot_impression_duration(slot_id):
    """ Returns the duration of the Slot Impression in seconds. """
    with SQLiteDB() as cursor:
        cursor.execute('''
            SELECT duration 
              FROM impression_table 
             WHERE slot_id = ? 
               AND event = 'slotImpression';
        ''', (slot_id,))
        return cursor.fetchone()[0]


def hover(hover_color='#424851'):
    return dict(selector='tr:hover', props=[('background-color', '{0}'.format(hover_color))])


def color_red(value):
    # type: (Union[str, float]) -> str
    """
    Colors numbers in a Pandas dateframe lime green if they're positive and
    red if they're negative. Does not color NaN values.
    """
    if isinstance(value, str) and "-" not in value:
        if float(value.rstrip('%')) < 100:
            color = 'red'
        elif float(value.rstrip('%')) == 100:
            color = 'lime'
    else:
        color = 'white'
    return 'color: {0}'.format(color)


def convert_epoch_to_datestr(epoch, date_format='%Y/%m/%d %H:%M:%S.%f'):
    """ Convert Epoch (time in secs) to a formatted timestamp in UTC. """
    if is_float(epoch):
        return datetime.utcfromtimestamp(float(epoch)).strftime(date_format)


def convert_datestr_to_unix_timestamp(date_string, date_format='%Y/%m/%d %H:%M:%S.%f'):
    """ Convert Date and Time string to a Unix Timestamp (time in secs since Unix Epoch). """
    return calendar.timegm(time.strptime(date_string, date_format))


def is_float(value):
    try:
        float(value)
        return True
    except ValueError:
        False


def post_process_information():
    """ Massages the data. """
    calculate_actual_firing_time_for_adaptive_player()
    calculate_actual_firing_time_for_unmatched_beacons()
    calculate_duration_for_slot_impression()
    calculate_expected_firing_time_for_slot_impression()
    calculate_expected_firing_time_for_default_impression()
    calculate_expected_firing_time_for_quartile_impression()
    calculate_difference_in_beacon_firing_times()
    identify_missing_beacons()


def validate_information():
    """ Validates the information. """
    validate_beacon_fired()
    validate_beacon_firing_order()
    validate_http_response_status()


def parse_args():
    """
    Parses the command line arguments.

    :return: The arguments provided on the command line.
    :rtype: namespace object
    """
    parser = argparse.ArgumentParser(
        formatter_class=argparse.RawDescriptionHelpFormatter,
        description='Parse Ad events found in the Adaptive Player logfile and report discrepancies.',
        epilog="The script parses the Adaptive Player log file (player.log)\n"
               "looking for the following events: Ad Request submitted to FreeWheel,\n"
               "FreeWheel's SmartXML Ad Response, and the slot, quartile, and tracking\n"
               "impressions sent and responses received by the Adaptive Player.\n"
               "For each Ad Response received by FreeWheel, the script reports the\n"
               "discrepancies between the Ad Response and the impressions sent and\n"
               "received by the Adaptive Player.\n\n",
        usage="\n  %(prog)s [OPTION]... [FILE]"
              "\n  %(prog)s --html player.log | less -SR"
    )

    parser.add_argument('filename', help='input file (e.g., AP\'s player.log)')
    parser.add_argument('-d', '--debug', dest='loglevel', help='Enable debug output', action='store_const',
                        const=logging.DEBUG, default=logging.INFO)
    parser.add_argument('--html', dest='html', help='display output in html', action='store_true')
    parser.add_argument('-s', '--slot', dest='slot', help='display report for this slot_id or cue_point_number')
    parser.add_argument('-t', '--text', dest='text', help='display output in text', action='store_true')
    parser.add_argument('-v', '--version', version='%(prog)s {version}'.format(version=__version__), action='version')

    # parser.add_argument('-l', '--log', dest='loglevel', help='set the logging level', type=str, choices=[
    #     'DEBUG', 'INFO', 'WARNING', 'ERROR', 'CRITICAL'], default=logging.INFO)

    # parser.add_argument('-m', '--metrics', dest='metrics', help='display metrics', action='store_true')
    # parser.add_argument('--csv', dest='csv', help='specify filename to output CSV to', action='store_true')
    # parser.add_argument('-csv', '--csv', help='CSV filename to output CSV to', action='store', nargs='?',
    #                    type=argparse.FileType('w'), default=sys.stdout)

    opts = parser.parse_args()

    if not opts.filename:
        parser.error('Please specify a logfile (e.g., /tmp/player.log)')
    return opts

def cleanup():
    logging.debug('Performing cleanup:')
    logging.debug('- Removing the following database: {0}'.format(SQLiteDB().path))
    SQLiteDB().delete_database_file()


def dict_from_row(row):
    """ Convert a sqlite3.Row to a dict to support the dict API. """
    return dict(zip(row.keys(), row))


def validate_xml(xml_string, qvt):
    """
    Validate the FreeWheel SmartXML Ad Response for the Event Callback information.
    The Event Callback section contains information about all the Impression Events,
    such as the Advertisement Slot IDs (e.g., slotImpression), Advertisement IDs
    (e.g., Quartiles), and 3rd-party Tracking Impressions.
    """
    def required_events():
        """ Set the state of impressions to missing by default. """
        return OrderedDict([
            ('defaultImpression', MISSING),
            ('firstQuartile', MISSING),
            ('midPoint', MISSING),
            ('thirdQuartile', MISSING),
            ('complete', MISSING)
        ])

    def convert_to_html(data):
        """ Kludge to convert the dict to an HTML table. """
        html = '''
            <br>
            <hr>
            <div class='subtitle' id=>Ad Response XML Validation:</div><br>
            <div class='indent'>
            <table border=1 ><tr>
            <th>Slot ID</th>
            <th>Advertisement ID</th>
            <th>defaultImpression</th>
            <th>firstQuartile</th>
            <th>midPoint</th>
            <th>thirdQuartile</th>
            <th>complete</th></tr>
        '''
        for slot_id, ad_ids in data.items():
            html += "<tr><td valign='top' align='center'>{0}</td>".format(slot_id)
            for ad_id, quartiles in ad_ids.items():
                html += "<td valign='top' align='center'>{0}</td>".format(ad_id)
                for quartile, state in quartiles.items():
                    html += "<td valign='top' align='center'>{0}</td>".format(state)
                html += "</tr><td></td>"
        html += "</table></div><br>"
        return html

    logging.debug('Validating FreeWheel SmartXML Ad Response.')
    try:
        pod = OrderedDict()
        base_path = 'siteSection/videoPlayer/videoAsset/adSlots/temporalAdSlot/[@customId]'
        tree = ElementTree.ElementTree(ElementTree.fromstring(xml_string))
        # Loop through each of the Slot IDs.
        for element in tree.findall(base_path):
            slot_id = element.attrib.get('customId')
            if slot_id == qvt['cue_point_number']:
                pod[slot_id] = OrderedDict()
                tpos = str(int(float(element.attrib.get('timePosition', '0'))))
                # Loop through each of the Advertisment IDs.
                for elem in element.findall("[@customId='{0}']//*[@adId]".format(slot_id)):
                    ad_id = elem.attrib.get('adId')
                    pod[slot_id][ad_id] = required_events()
                    for impression in ['defaultImpression', 'firstQuartile', 'midPoint', 'thirdQuartile', 'complete']:
                        query = ".//temporalAdSlot/[@customId='{0}']//*[@adId='{1}']//*[@type='IMPRESSION'][@name='{2}']"
                        # Search for Event Callback's containing the Slot ID, Ad ID, and Ad Impression.
                        event_callback = tree.find(query.format(slot_id, ad_id, impression))
                        if event_callback is not None:
                            url = event_callback.attrib.get('url')
                            re_pattern = 'adid=' + ad_id + '.*cn=' + impression + '.*tpos=' + tpos
                            # Verify the URL contains the expected values
                            if re.search(re_pattern, url):
                                state = FOUND
                            else:
                                state = MISSING
                        else:
                            state = MISSING
                        pod[slot_id][ad_id][impression] = state
        content = convert_to_html(pod)
        return content
    except Exception as ex:
        logging.error('Problem processing FreeWheel\'s XML Ad Response.')
        logging.error(format_exception(ex))


def device_lookup_table():
    """ Determines device information for Channel Service ID. """
    if device_info:
        if 'Android TV' in device_info['device_platform'] \
            and 'AIRTV PLAYER' in device_info['device_model']:
            result = 'airtvplayer'
        elif 'Android TV' in device_info['device_platform']:
            result = 'android_tv'
        elif 'Android Phone' in device_info['device_platform']:
            result = 'android_phone'
        elif 'Android Tablet' in device_info['device_platform']:
            result = 'android_tablet'
        elif 'Roku' in device_info['device_platform']:
            result = 'roku'
        elif 'Apple TV' in device_info['device_model']:
            result = 'tvos'
        elif 'iPhone' in device_info['device_model']:
            result = 'iphone'
        elif 'iPad' in device_info['device_model']:
            result = 'ipad'
    else:
        result = 'Unknown'
    return result

    # keys = ['device', 'csid_param', 'platform', 'type', 'model']
    # values = [
    #     ('Roku', 'roku', 'Roku', None, None),
    #     ('Android TV', 'android_tv', 'Android TV', None, None),
    #     ('AirTV player', 'airtvplayer', 'Android TV', None, 'AIRTV PLAYER'),
    #     ('Android Phone', 'android_phone', 'Android Phone', 'phone', None),
    #     ('Android Tab', 'android_tablet', 'Android Tablet', 'tablet', None),
    #     ('iPhone', 'iphone', 'iPhone', 'phone', 'iPhone'),
    #     ('iPad', 'ipad', 'iPad', 'tablet', 'iPad'),
    #     ('Apple TV', 'tvos', 'Apple TV 4K, Apple TV 4th Gen', None, 'Apple TV')
    # ]
    # devices = [dict(zip(values, v)) for v in keys]
    #return next((device for device in device_info if device['platform'] == platform), None)


# ----------------------------------------------------------------------------------------------
# Main
# ----------------------------------------------------------------------------------------------
if __name__ == "__main__":

    try:
        # Global Dictionaries
        journal = Journal()  # Used to record Impressions (Beacons) fired by the Adaptive Player.
        device_info = dict()

        # Parse the command line arguments
        args = parse_args()

        # Initialize the SQLite database
        init_database()

        # Some imported module is setting a logging handler and is causing logging.basicConf to
        # be a no-op, so this is a work around to clear the handler before configuring the
        # logging level specified on the command line
        logging.getLogger('').handlers = []
        logging.basicConfig(
            level=args.loglevel,
            format='%(asctime)s %(levelname)s %(module)s - %(funcName)s: %(message)s',
            datefmt='%Y-%m-%d %H:%M:%S'
        )

        logging.info('Processing the following file: {0}'.format(args.filename))
        with io.open(args.filename, 'r', encoding='utf-8') as f:
            for line in merge_multiple_lines(f):
                process(line)

        # Post-process and validate the data
        post_process_information()
        validate_information()

        # Generate CSV file
        # if args.csv:
        #     pandas_to_csv()

        # Generates the DAI Validation Report in HTML format and determine if there was
        # a request for a specific slot impression; otherwise fetch all of them.
        if args.html:
            color_beacons(args)
            to_html()
            if args.slot:
                fetch_html_report_from_database(args.slot)
            else:
                fetch_html_report_from_database()

        # Display output in standard text
        if args.text:
            color_beacons(args)
            to_text_impression_info()

        # Display metrics in standard text
        # if args.metrics:
        #     pandas_set_options()
        #     pandas_summarize_slot_and_quartile_metrics()
        #     pandas_summarize_tracking_metrics()

        # TODO: Need to fix the loglevel command argument (should be something else, ie., verbose)
        # if args.loglevel:
        #     print_database()
        #     write_journal()

        # group by slot id, time_position, and then advertisement ID
        # print_pandas_groupby_summary()

        cleanup()
        logging.debug('Finished processing: {0}'.format(args.filename))
    except (KeyboardInterrupt, SystemExit):
        cleanup()

#!/usr/bin/env python

# ----------------------------------------------------------------------------------------------
# Modules
# ----------------------------------------------------------------------------------------------
from __future__ import print_function, division
import argparse
import base64
import json
import logging
import os
import pandas as pd
import re
import sqlite3
import tempfile
import sys
import xml.dom.minidom as minidom
from collections import OrderedDict
from datetime import datetime
from io import open
from xml.etree import ElementTree

try:
    # For Python 3.0 and later
    from urllib.parse import urlparse, parse_qs, parse_qsl
    from urllib.request import urlopen
except ImportError:
    # Fall back to Python 2's urllib2
    from urlparse import urlparse, parse_qs, parse_qsl
    from urllib2 import urlopen

__version__ = "1.8.3.8-devb"


# ----------------------------------------------------------------------------------------------
# Constants
# ----------------------------------------------------------------------------------------------
PASS = "<span class='text-pass'>(PASS)</span>"
FAIL = "<span class='text-fail'>(FAIL)</span>"
SKIP = "<span class='text-skip'>(SKIP) </span>"
FOUND = "<span class='text-found'>Present</span>"
MISSING = "<span class='text-missing'>Missing</span>"
PLAYER = "http://demo.theoplayer.com/test-your-stream-with-statistics?url="


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


class ParseAdRequest:
    """
    Creates an object view of the Adaptive Player's Ad Request.
    """
    important = {
        'adapt_url', 'ads_url', 'flag', 'nw', 'csid', 'caid', 'asnw', 'ssnw',
        'prof', 'afid', 'fw_vcid', '_fw_vcid2', 'slid', 'tpcl', 'tpos',
        'maxd', 'mind', 'cpsq', 'ssto'
    }
    non_important = {
        '_fw_nielsen_app_id', 'comscore_device', 'comscore_did_x', 'comscore_impl_type',
        'comscore_platform', 'envp', 'feature', 'module', 'metr', 'mode', 'nielsen_dev_group',
        'nielsen_os_group', 'nielsen_os_version', 'ptgt', 'pvrn', 'resp', 'roku_rida',
        'sfid', 'slau', 'vdur', 'vip', 'vprn'
    }

    def __init__(self, request):
        self.request = request
        self.expected_params = ParseAdRequest.important | ParseAdRequest.non_important
        self.missing = MISSING
        self.timestamp = self.missing
        self.url = self.missing
        if isinstance(self.request, str):
            self._valid()
        elif self.request is None:
            self._invalid()
        else:
            raise TypeError('Expecting a string, but received:{} '.format(type(request)))

    def _invalid(self):
        """ Parse the Ad Request URL to obtain its parameters. """
        self.params = {}
        self.params.update((key, self.missing) for key in self.expected_params)
        self.parsed_requests = [self.params.copy()]

    def _loose_ordering(self):
        """ Store the Ad Request parameters and disregard the parsing sequence. """
        self.params.update((k, v) for k, v in parse_qs(self.parsed.query).items())

    def _identify_missing_params(self):
        """ Identify Ad Request parameters missing from the Request. """
        self.params.update((k, self.missing) for k in self.expected_params if k not in self.params)

    def _identify_multiple_slot_ids(self):
        """
        Generates a list of Ad Requests whenever the request includes multiple Ad Breaks.
        Usually an Ad Request is for a single Ad Break or Slot ID, however, an Ad Request
        may ask for multiple Ad Breaks. When this occurs, parse the query params in a way
        that makes these multiple Slot ID requests appear as individual Ad Requests.
        This should make it easier to validate the Ad Request for a specific Slot ID.
        """
        self.parsed_requests = []
        self._request = OrderedDefaultDict()
        for index in range(len(self.params['slid'])):
            for key in self.params:
                if isinstance(self.params[key], list):
                    if len(self.params[key]) > 1:
                        self._request[key] = self.params[key][index]
                    elif len(self.params[key]) == 1:
                        self._request[key] = self.params[key][0]
                else:
                    self._request[key] = self.params[key]
            self.parsed_requests.append(self._request.copy())

    def _parse(self):
        """ Parse the Ad Request URL to obtain its parameters. """
        self.parsed = urlparse(self.url)

    def _rank_parameters(self):
        """ Sort the Ad Request parameters by their importance. """
        self.important_params = OrderedDefaultDict()
        self.non_important_params = OrderedDefaultDict()
        for key, value in self.params.items():
            if key in ParseAdRequest.important:
                self.important_params[key] = value
            elif key in ParseAdRequest.non_important and self.missing not in value:
                self.non_important_params[key] = value

    def _strict_ordering(self):
        """ Store the Ad Request parameters in a strict sequence. """
        self.params = OrderedDefaultDict()
        m = re.match(self._re_ads_service_urls, self.url)
        if m:
            self.params['adapt_url'] = [m.group('adapt_url')]
            self.params['ads_url'] = [m.group('ads_url')]
        for key, value in parse_qsl(self.parsed.query):
            if key in self.params:
                self.params[key].append(value)
            else:
                self.params[key] = [value]
        self.params['flag'] = [self.params['flag'][0].strip()]

    def _valid(self):
        """ Parse the Ad Request URL to obtain its parameters. """
        self._re_ads_service_urls = r'^(?P<adapt_url>http://.+)(?P<ads_url>http.+g/1)'
        self._re_datetime = r'^(?P<date>\d{4}[/.-]\d{2}[/.-]\d{2}\s\d{2}:\d{2}:\d{2})'
        self._re_url = r'^.* (?P<url>http.*$)'
        if re.search(self._re_url, self.request):
            self.timestamp = re.match(self._re_datetime, self.request).group(1)
            self.url = re.match(self._re_url, self.request).group(1)
            self._parse()
            self._strict_ordering()
            self._identify_missing_params()
            self._identify_multiple_slot_ids()
            self._rank_parameters()
        else:
            self._invalid()

    def retrieve_ad_request(self):
        """ Returns the parsed Ad Request params and values. """
        return self.params

    def retrieve_ad_slot_id(self, slot_id):
        """ Returns the parsed Ad Request for a specific Slot ID. """
        for request in self.parsed_requests:
            if slot_id == request['slid']:
                return request


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
        self.ad_id = None  # Advertisement ID
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
            if self.impression is None and self.slot_id is None and self.time_position is None:
                self.beacon_type = 'tracking'
                self.tracking_direction = 'Sent'
                self.impression = self.swap_event_term(self.beacon_event)

        # Responses received from FreeWheel and 3rd-party systems
        elif 'beacon callback responseCode' in self.logline:
            if self.impression is None and self.slot_id is None and self.time_position is None:
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
            cursor.execute('SELECT type from Impressions WHERE url=?;', (self.url,))
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
        filename = 'report_dai_sqlite.db'
        self.path = '/'.join([directory, filename])

    # On enter, connect to the database and return a cursor
    def __enter__(self):
        self.connection = sqlite3.connect(self.path)
        if self.row_module:
            self.connection.row_factory = sqlite3.Row
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

    def addition(a, b):
        """ Returns the sum. """
        return float(a) + float(b) if all([is_float(a), is_float(b)]) else 0

    def subtraction(a, b):
        """ Returns the difference. """
        return float(a) - float(b) if all([is_float(a), is_float(b)]) else 0

    def compute_slot_duration(stop_offset, start_offset, **kwargs):
        """ Returns the duration of the Slot Impression in seconds. """
        return str(int(round(subtraction(stop_offset, start_offset))))

    def compute_time_position(start_offset, anchor_time, **kwargs):
        """ Returns the time position of the Slot Impression. """
        return str(format(subtraction(start_offset, anchor_time), '.3f'))

    def compute_start_with_delay(start_offset, playback_delay, **kwargs):
        """ Returns the start time plus the playback_delay. """
        return addition(start_offset, playback_delay)

    def compute_stop_with_delay(stop_offset, playback_delay, **kwargs):
        """ Returns the stop time plus the playback_delay. """
        return addition(stop_offset, playback_delay)

    def channel_service_id(channel, content_type, **kwargs):
        """ Returns the Channel Service ID. """
        return '_'.join(['otto', device_lookup_table(), channel, content_type])

    def traverse(obj):
        """ Returns the key-values of the Ad Break section of the QVT. """
        if isinstance(obj, dict):
            return {str(key): traverse(value) for key, value in obj.items()}
        elif isinstance(obj, list):
            return [traverse(elem) for elem in obj]
        else:
            return obj

    try:
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
        msg = 'ERROR Encountered exception while attempting to parse QVT at timestamp: {0}.'
        logging.debug(msg.format(logline[:26]))
        logging.debug(format_exception(ex))
    else:
        # This block of code is executed only if no exceptions were raised.
        # Attempt to parse the QVT for the Dynamic Advertisement related
        # parameters and store them in a dictionary so that we can update
        # the qvt_table in the database using named placeholders.
        try:
            missing = 'Missing'
            qvt_records = []
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
            qvt['csid'] = channel_service_id(**qvt)

            # FIXME: Python 3.6 is throwing the following exception:
            #  An exception of type TypeError occurred. Arguments:
            #  ("a bytes-like object is required, not 'str'",).
            # Retrieve the Adapt and FreeWheel URLs from Ads Service URL
            if missing not in qvt['ads_service_url']:
                re_urls = r'^(?P<adapt_url>http://.+)(?P<ads_url>http.*)'
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
                qvt['cue_point_number'] = ad_break.get('cue_point_number', missing)
                qvt['method'] = ad_break.get('method', missing)
                qvt['start_offset'] = ad_break.get('start_offset', 0)
                qvt['stop_offset'] = ad_break.get('stop_offset', 0)
                qvt['type'] = ad_break.get('type', missing)
                qvt['duration'] = qvt['mind'] = qvt['maxd'] = compute_slot_duration(**qvt)
                qvt['start_offset_with_delay'] = compute_start_with_delay(**qvt)
                qvt['stop_offset_with_delay'] = compute_stop_with_delay(**qvt)
                qvt['tpos'] = compute_time_position(**qvt)
                qvt_records.append(qvt.copy())
            return qvt_records

        except Exception as ex:
            logging.debug('ERROR Problem encountered while processing the QVT.')
            logging.debug(format_exception(ex))


def process(line):
    # type: (str) -> None
    """
    Determine if the log entry from the Adaptive Player matches any significant
    Dynamic Ad Insertion events.
    """
    try:
        # if line.startswith("2018/12/28 16:41:46.684441"):
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
            db_catalog_beacon(beacon)

        elif match.fw_beacon:
            logging.debug('Found External Beacon')
            beacon = Impression('External', **match.fw_beacon.groupdict())
            beacon = correlate_beacon_params(beacon)
            db_catalog_beacon(beacon)

        elif match.fw_callback:
            logging.debug('Found Response Beacon')
            beacon = Impression('Response', **match.fw_callback.groupdict())
            beacon = correlate_beacon_params(beacon)
            db_catalog_beacon(beacon)
            db_catalog_http_status(beacon)

        # These next three conditions are for Adaptive Player's newer DAI events
        # (e.g., using SM3 and 'Points')
        elif match.ap_internal:
            logging.debug('Found AP Internal Beacon (SM3)')
            beacon = Impression('Internal', **match.ap_internal.groupdict())
            beacon = correlate_sm3_beacon_params(beacon)
            db_catalog_beacon(beacon)

        elif match.ap_external:
            logging.debug('Found External Beacon (SM3)')
            beacon = Impression('External', **match.ap_external.groupdict())
            beacon = correlate_sm3_beacon_params(beacon)
            db_catalog_beacon(beacon)

        elif match.ap_response:
            logging.debug('Found Response Beacon (SM3)')
            beacon = Impression('Response', **match.ap_response.groupdict())
            beacon = correlate_sm3_beacon_params(beacon)
            db_catalog_beacon(beacon)
            db_catalog_http_status(beacon)
    except Exception as ex:
        logging.debug(format_exception(ex))


def handle_device_info(**kwargs):
    """ Stores the Adaptive Player Device Information found in the AP log file. """
    try:
        device_info.update((k, v) for k, v in kwargs.items() if v is not None)
    except Exception as ex:
        logging.debug(format_exception(ex))


def handle_qvt(line):
    """ Process the QVT received by the Adaptive Player. """
    try:
        qvt_records = parse_qvt(line)
        db_catalog_qvt(qvt_records)
    except Exception as ex:
        logging.debug('ERROR Problem encountered while processing the QVT: {0}.'.format(line))
        logging.debug(format_exception(ex))


def handle_ad_request(match):
    """ Process the Ad Request submitted to FreeWheel from the Adaptive Player. """
    try:
        ad_request = ' '.join([match.group('timestamp'), match.group('url')])
        with SQLiteDB() as cursor:
            cursor.execute("INSERT INTO AdPods (request) VALUES (?);", (ad_request,))
            logging.debug('Number of rows inserted: {0}'.format(cursor.rowcount))
        db_catalog_ad_request(ad_request, cursor.lastrowid)
    except Exception as ex:
        logging.debug('ERROR Problem encountered while processing FreeWheel Ad Request.')
        logging.debug(format_exception(ex))


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
            cursor.execute("SELECT pod_id FROM AdPods WHERE request IS NOT NULL AND response IS NULL;")
            row = cursor.fetchone()
            if row:
                return row[0]

    def update_db(_pod_id, _response):
        """ Stores FreeWheel's Ad Response in the database. """
        with SQLiteDB() as cursor:
            cursor.execute("UPDATE AdPods SET response = ? WHERE pod_id = ?;", (_response, _pod_id))

    def insert_db(_response):
        """ Stores FreeWheel's Ad Response in the database. """
        with SQLiteDB() as cursor:
            cursor.execute("INSERT INTO AdPods (response) VALUES (?);", (_response,))
            return cursor.lastrowid

    try:
        timestamp = match.group('timestamp')
        xml_string = match.group('xml')
        response = ' '.join([timestamp, xml_string])
        pod_id = fetch_pod_id()
        if pod_id:
            logging.debug('Processing FreeWheel\'s XML Ad Response #{0}.'.format(pod_id))
            update_db(pod_id, response)
        else:
            pod_id = insert_db(response)

        # Load and parse the XML document for all of the Impressions and Ad Creatives
        tree = ElementTree.ElementTree(ElementTree.fromstring(xml_string))
        # Provide debugging output per user's request; save the XML to disk.
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
        logging.debug('ERROR Problem processing FreeWheel\'s XML Ad Response')
        logging.debug(format_exception(ex))


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
    list_of_impressions = []
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
    list_of_ad_creatives = []
    path = 'creatives/creative'
    rendition_path = path + '/creativeRenditions/creativeRendition'
    asset_path = rendition_path + '/asset'
    logging.debug('Retrieving Creative Ads from FreeWheel\'s Ad Response #{0}'.format(pod_id))
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
            INSERT INTO Impressions
                (pod_id, slot_id, time_position, ad_id, type, event, url, tracking_num)
            VALUES
                (:pod_id, :slot_id, :time_position, :ad_id, :type, :event, :url, :tracking_num);
            ''', data)

        # Provide debugging output per user's request
        if logging.getLogger().isEnabledFor(logging.DEBUG):
            cursor.execute('SELECT * FROM Impressions WHERE pod_id=?', (pod_id,))
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
            logging.debug('WARNING Empty Ad Creatives found in FreeWheel\'s Ad Response.')
            return None

        # For each dict in the 'data' list, take the keys from the dict as SQL parameters and execute the SQL statement.
        with SQLiteDB() as cursor:
            logging.debug('Storing Creatives from FreeWheel\'s Ad Response into the database:')
            cursor.executemany('''
                INSERT INTO Creatives (
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

            logging.debug('Updating the Impression records with Creative Advertisement information')
            cursor.executemany('''
                UPDATE Impressions 
                   SET creative_url = :asset_url, duration = :creative_duration 
                 WHERE ad_id = :ad_adId 
                   AND type = 'quartile'  
            ''', data)

            # Provide debugging output per user's request
            if logging.getLogger().isEnabledFor(logging.DEBUG):
                cursor.execute('SELECT * FROM Creatives WHERE pod_id=?', (pod_id, ))
                column_names = tuple(map(lambda x: x[0], cursor.description))
                rows = cursor.fetchall()
                table = '\n'.join(map(str, rows))
                msg = 'Number of Creatives in FreeWheel\'s Ad Response #{0}: {1}\n{2}\n{3}'
                logging.debug(msg.format(pod_id, len(rows), column_names, table))

    except Exception as ex:
        logging.debug(format_exception(ex))


def init_database():
    # type: () -> None
    """ Create a databases to store and retrieve Impression information. """
    with SQLiteDB() as cursor:
        logging.debug('Creating database.')
        script = '''
            DROP TABLE IF EXISTS Impressions;
            CREATE TABLE IF NOT EXISTS Impressions (
                pk INTEGER PRIMARY KEY, 
                pod_id INTEGER NOT NULL DEFAULT '', 
                slot_id TEXT NOT NULL DEFAULT '', 
                time_position TEXT DEFAULT '', 
                ad_id TEXT DEFAULT '', 
                type TEXT NOT NULL DEFAULT '', 
                event TEXT NOT NULL DEFAULT '', 
                url TEXT DEFAULT '', 
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
                current_time TEXT DEFAULT '',
                sent_counter INTEGER NOT NULL DEFAULT 0,
                received_counter INTEGER NOT NULL DEFAULT 0
            );
                
            DROP TABLE IF EXISTS Creatives;
            CREATE TABLE IF NOT EXISTS Creatives (
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
                start_offset TEXT NOT NULL DEFAULT 'QVT Missing',
                stop_offset TEXT NOT NULL DEFAULT 'QVT Missing',
                playback_delay TEXT NOT NULL DEFAULT 'QVT Missing',
                start_offset_with_delay TEXT NOT NULL DEFAULT 'QVT Missing',
                stop_offset_with_delay TEXT NOT NULL DEFAULT 'QVT Missing',
                duration TEXT NOT NULL DEFAULT 'QVT Missing',
                maxd TEXT NOT NULL DEFAULT 'QVT Missing',
                mind TEXT NOT NULL DEFAULT 'QVT Missing',
                tpos TEXT NOT NULL DEFAULT 'QVT Missing',
                title TEXT NOT NULL DEFAULT 'QVT Missing',
                ads_service_url TEXT NOT NULL DEFAULT 'QVT Missing',
                adapt_url TEXT NOT NULL DEFAULT 'QVT Missing',
                ads_url TEXT NOT NULL DEFAULT 'QVT Missing',
                url TEXT NOT NULL DEFAULT 'QVT Missing',
                content_type TEXT NOT NULL DEFAULT 'QVT Missing',
                log TEXT NOT NULL DEFAULT 'QVT Missing',
                csid TEXT NOT NULL DEFAULT 'QVT Missing'
            ); 
            CREATE UNIQUE INDEX idx_qvt_cue_point_number ON qvt_table (cue_point_number);
           
            DROP TABLE IF EXISTS Requests;
            CREATE TABLE IF NOT EXISTS Requests (
                pod_id INTEGER NOT NULL, 
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
                _fw_nielsen_app_id TEXT NOT NULL DEFAULT '',
                _fw_vcid2 TEXT NOT NULL DEFAULT '',
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
            CREATE UNIQUE INDEX idx_adreq_slot_id ON Requests (slid);

            DROP TABLE IF EXISTS unmatched_table;
            CREATE TABLE IF NOT EXISTS unmatched_table (
                pk INTEGER PRIMARY KEY, 
                log TEXT NOT NULL DEFAULT '',
                actual_firing_time REAL NOT NULL DEFAULT '0'
            );
                
            DROP TABLE IF EXISTS AdPods;
            CREATE TABLE IF NOT EXISTS AdPods (
                pod_id INTEGER PRIMARY KEY,
                request TEXT,
                response TEXT,
                sm3pointscacheitem TEXT DEFAULT ''
            );
                
            DROP TABLE IF EXISTS Reports;
            CREATE TABLE IF NOT EXISTS Reports (
                pk INTEGER PRIMARY KEY, 
                pod_id INTEGER NOT NULL,
                slot_id TEXT NOT NULL DEFAULT '', 
                content TEXT NOT NULL DEFAULT ''
            );
            
            DROP TABLE IF EXISTS Ad_Request_URL_params;
            CREATE TABLE IF NOT EXISTS Ad_Request_URL_params(
                pk INTEGER PRIMARY KEY, 
                pod_id INTEGER NOT NULL DEFAULT '', 
                slot_id TEXT NOT NULL DEFAULT '', 
                param TEXT NOT NULL DEFAULT '',
                expected TEXT NOT NULL DEFAULT '',
                found TEXT NOT NULL DEFAULT '',
                state TEXT NOT NULL DEFAULT '',
                status TEXT NOT NULL DEFAULT ''
            );
        '''
        cursor.executescript(script)


def db_catalog_ad_request(ad_request, pod_id):
    """ Stores the Ad Request in the database. """
    values = []
    for request in ParseAdRequest(ad_request).parsed_requests:
        request['pod_id'] = pod_id
        values.append(request)

    with SQLiteDB() as cursor:
        cursor.executemany('''
            INSERT INTO Requests
            VALUES (
                :pod_id, :adapt_url, :ads_url, :afid, :asnw, :caid, :comscore_device,
                :comscore_did_x, :comscore_impl_type, :comscore_platform,
                :cpsq, :csid, :envp, :feature, :flag, :_fw_nielsen_app_id,
                :_fw_vcid2, :fw_vcid, :maxd, :metr, :mind, :mode, :module,
                :nielsen_dev_group, :nielsen_os_group, :nielsen_os_version,
                :nw, :prof, :ptgt, :pvrn, :resp, :roku_rida, :sfid, :slau,
                :slid, :ssnw, :ssto, :tpcl, :tpos, :vdur, :vip, :vprn
            );
        ''', values)
        logging.debug('Number of rows inserted: {0}'.format(cursor.rowcount))


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
                    :title, :ads_service_url, :adapt_url, :ads_url, :url, 
                    :content_type, :log, :csid
                );
            ''', values)
            count = cursor.rowcount
            logging.debug('Number of rows inserted: {0}'.format(count))


def db_catalog_beacon(beacon):
    """
    Update the database to record the occurrence of the Adaptive Player event.

    :param Impression beacon:
    :return: None
    """
    sql_statement = {
        'Internal': 'UPDATE Impressions SET internal_log = ? WHERE pk=?;',
        'External': 'UPDATE Impressions SET sent_log = ? WHERE pk = ?;',
        'Response': 'UPDATE Impressions SET received_log = ? WHERE pk = ?;',
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
        logging.debug('ERROR Problem updating the database records.')
        logging.debug(format_exception(ex))


def db_catalog_http_status(beacon):
    # type: (Impression) -> None
    """ Updates the Impression's HTTP Status in the database. """
    if beacon.is_valid:
        with SQLiteDB() as cursor:
            cursor.execute("UPDATE Impressions SET http_status=? WHERE pk=?;", (beacon.response_code, beacon.pk))
    else:
        msg = 'WARNING Invalid Beacon. Unable to catalog in the database: {0}'
        logging.debug(msg.format(vars(beacon)))


def db_fetch_pod_ids():
    """ Retrieves the Pod IDs. """
    with SQLiteDB(row=True) as cursor:
        cursor.execute("SELECT DISTINCT(pod_id) FROM AdPods;")
        rows = cursor.fetchall()
        return [row['pod_id'] for row in rows]


def db_fetch_slot_ids(pod_id):
    """ Retrieves the Slot IDs a given pod. """
    with SQLiteDB(row=True) as cursor:
        cursor.execute("SELECT DISTINCT(slid) FROM Requests WHERE pod_id=?;", (pod_id,))
        rows = cursor.fetchall()
        if not rows:
            rows = [{'slid': '0'}]
        return [row['slid'] for row in rows]


def db_fetch_ad_request(pod_id):
    """ Retrieves an Ad Request for a given pod. """
    with SQLiteDB() as cursor:
        cursor.execute("SELECT request FROM AdPods WHERE pod_id=?;", (pod_id,))
        row = cursor.fetchone()
        # TODO: determine why this is returning a tuple (None,) instead of just 'None'.
        if all(row):
            return row[0]


def db_fetch_ad_response(pod_id):
    """ Retrieves an Ad Response for a given pod. """
    with SQLiteDB() as cursor:
        cursor.execute("SELECT response FROM AdPods WHERE pod_id=?;", (pod_id,))
        row = cursor.fetchone()
        if all(row):
            return row[0]


def db_fetch_qvt_record(slot_id):
    """ Retrieves the QVT record for a given Slot ID and creates one if it doesn't exist. """
    with SQLiteDB(row=True) as cursor:
        cursor.execute("SELECT * FROM qvt_table WHERE cue_point_number=?", (slot_id,))
        record = cursor.fetchone()
        if record is None:
            logging.debug('WARNING No QVT records found for slot_id={0}. Generating an empty set.'.format(slot_id))
            cursor.execute("INSERT INTO qvt_table (cue_point_number) VALUES (?);", (slot_id,))
            cursor.execute("SELECT * FROM qvt_table WHERE cue_point_number=?", (slot_id,))
            record = cursor.fetchone()
        return dict_from_row(record)


def db_fetch_validated_url_params(pod_id, slot_id):
    """ Retrieves the Slot IDs a given pod. """
    with SQLiteDB(row=True) as cursor:
        cursor.execute('''
            SELECT * FROM Ad_Request_URL_params 
             WHERE pod_id = :pod_id 
               AND slot_id = :slot_id
          ORDER BY pk;
        ''', {'pod_id': pod_id, 'slot_id': slot_id})
        rows = cursor.fetchall()
    if rows:
        return [dict_from_row(row) for row in rows]


def db_fetch_dai_info():
    """ Returns the Dynamic Ad Information for each Ad Pod. """
    with SQLiteDB() as cursor:
        cursor.execute('''
              SELECT AdPods.pod_id, Requests.slid, AdPods.request, AdPods.response
                FROM Requests
          INNER JOIN AdPods 
                  ON Requests.pod_id = AdPods.pod_id
               UNION
              SELECT AdPods.pod_id, Impressions.slot_id, AdPods.request, AdPods.response
                FROM Impressions
          INNER JOIN AdPods 
                  ON Impressions.pod_id = AdPods.pod_id
            ORDER BY AdPods.pod_id
        ''')
        rows = cursor.fetchall()
        return rows


def db_fetch_impressions(pod_id, slot_id):
    """ Returns the Quartile and Tracking Impressions for a given Pod and Slot ID. """
    with SQLiteDB(row=True) as cursor:
        cursor.execute('''
            SELECT pod_id, slot_id, ad_id, type, event, sent, received 
              FROM Impressions
             WHERE (type = 'quartile' OR type = 'tracking')
               AND pod_id = :pod_id
               AND slot_id = :slot_id
          ORDER BY pk;
        ''', {'pod_id': pod_id, 'slot_id': slot_id})
        rows = cursor.fetchall()
    if rows:
        return [dict_from_row(row) for row in rows]


def db_fetch_slot_impression_duration(slot_id):
    """ Returns the duration of the Slot Impression in seconds. """
    with SQLiteDB() as cursor:
        cursor.execute('''
            SELECT duration 
              FROM Impressions 
             WHERE slot_id = ? 
               AND event = 'slotImpression';
        ''', (slot_id,))
        duration = cursor.fetchone()
    if duration:
        return duration[0]


def db_remove(filename):
    """ Removes the SQLite3 database file from the filesystem. """
    if os.path.isfile(filename):
        os.remove(filename)
        logging.debug('Successfully removed SQLite database file: {0}'.format(filename))
    else:
        logging.debug('ERROR Failed to remove SQLite database file: {0}'.format(filename))


def update_db_successfully_sent_impression(record):
    # type: (sqlite3.Row) -> None
    """
    Update the 'sent' status for the entry in the database that corresponds to the primary key

    :param sqlite3.Row record:
    :return: None
    """
    with SQLiteDB() as cursor:
        cursor.execute('''
            UPDATE Impressions 
               SET sent = 'True',
                   sent_counter = sent_counter + 1 
             WHERE pk = ?;
            ''', (record['pk'],))


def update_db_successfully_received_impression(record):
    # type: (sqlite3.Row) -> None
    """
    Update the 'received' status for the entry in the database that corresponds to the primary key

    :param sqlite3.Row record:
    :return: None
    """
    with SQLiteDB() as cursor:
        cursor.execute('''
            UPDATE Impressions 
               SET received = 'True',
                   received_counter = received_counter + 1 
             WHERE pk = ?;
            ''', (record['pk'],))


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
        cursor.execute("UPDATE Impressions SET active='False';")
        cursor.execute("UPDATE Impressions SET active='True' WHERE pod_id=?;", (pod_id,))


def db_insert_validated_request_params(values):
    """
    Inserts Ad Request parameters into the database.

    :param list values: A list of dicts; sqlite3 db adapter uses named parameters in the form :keyname
    """
    with SQLiteDB() as cursor:
        cursor.executemany('''
            INSERT INTO Ad_Request_URL_params
                (pod_id, slot_id, param, expected, found, state, status)
            VALUES
                (:pod_id, :slot_id, :param, :expected, :found, :state, :status)
        ''', values)


def print_database():
    """
    Displays all the records in the SQL database.  The records are all of the Slot, Quartile, and 3rd-Party Tracking
    Impressions parsed from FreeWheel's SmartXML Ad Response.
    """
    with SQLiteDB() as cursor:
        cursor.execute("UPDATE Impressions SET sent='False' WHERE sent IS NULL")
        cursor.execute("UPDATE Impressions SET received='False' WHERE received IS NULL")

        # Provide debugging output per user's request
        if logging.getLogger().isEnabledFor(logging.DEBUG):
            cursor.execute('''
                SELECT pk, pod_id, sent, received, slot_id, time_position, ad_id, event, url, creative_url 
                FROM Impressions
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
    table = 'Impressions'
    # Suppressing the "active='True'" to see if it helps catalog beacons
    query_internal_slot = '''
        SELECT * FROM {tn} 
         WHERE slot_id={slot_id} AND event='{impression}' AND sent is NULL ORDER BY pk LIMIT 1;
        '''
    query_internal_quartile = '''
        SELECT * FROM {tn} 
         WHERE slot_id='{slot_id}' AND ad_id='{ad_id}' AND event='{impression}' AND type='quartile' 
         ORDER BY pk DESC LIMIT 1;
        '''
    query_external_slot = '''
        SELECT * FROM {tn} 
         WHERE type='{beacon_type}' AND event='{impression}' AND url='{url}' AND sent is NULL;
        '''
    # query_external_quartile = '''
    #     SELECT * FROM {tn}
    #      WHERE slot_id='{slot_id}' AND ad_id='{ad_id}' AND type='{beacon_type}' AND event='{impression}'
    #        AND url='{url}' AND sent is NULL
    #     '''
    # query_external_tracking = '''
    #     SELECT * FROM {tn}
    #      WHERE slot_id='{slot_id}' AND ad_id='{ad_id}' AND type='{beacon_type}' AND event='{impression}'
    #        AND url='{url}' AND sent IS NULL;
    #     '''

    query_external_quartile = '''
        SELECT * FROM {tn} 
         WHERE slot_id='{slot_id}' AND ad_id='{ad_id}' AND type='{beacon_type}' AND event='{impression}' 
           AND url='{url}'; 
        '''
    query_external_tracking = '''
        SELECT * FROM {tn} 
         WHERE slot_id='{slot_id}' AND ad_id='{ad_id}' AND type='{beacon_type}' AND event='{impression}' 
           AND url='{url}';
        '''

    query_response_slot = '''
        SELECT * FROM {tn} 
         WHERE slot_id='{slot_id}' AND type='{beacon_type}' AND event='{impression}' 
           AND url='{url}' AND received is NULL;
        '''
    # query_response_quartile = '''
    #     SELECT * FROM {tn}
    #      WHERE slot_id='{slot_id}' AND ad_id='{ad_id}' AND type='{beacon_type}' AND event='{impression}'
    #        AND url='{url}' AND received is NULL;
    #     '''
    # query_response_tracking = '''
    #     SELECT * FROM {tn}
    #      WHERE slot_id='{slot_id}' AND ad_id='{ad_id}' AND url='{url}' AND received is NULL;
    #     '''

    query_response_quartile = '''
        SELECT * FROM {tn} 
         WHERE slot_id='{slot_id}' AND ad_id='{ad_id}' AND type='{beacon_type}' AND event='{impression}' 
           AND url='{url}';
        '''
    query_response_tracking = '''
        SELECT * FROM {tn} 
         WHERE slot_id='{slot_id}' AND ad_id='{ad_id}' AND url='{url}';
        '''

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
                        logging.debug("WARNING Failed to match beacon against FreeWheel\'s XML")
                elif 'quartile' in beacon_type:
                    record = cursor.execute(query_external_quartile.format(tn=table, **vars(beacon))).fetchone()
                    if record:
                        update_db_successfully_sent_impression(record)
                        beacon = beacon_update_from_sql_record(beacon, record)
                    else:
                        logging.debug("WARNING Failed to match beacon against FreeWheel\'s XML")
                elif 'tracking' in beacon_type:
                    record = cursor.execute(query_external_tracking.format(tn=table, **vars(beacon))).fetchone()
                    if record:
                        update_db_successfully_sent_impression(record)
                        beacon = beacon_update_from_sql_record(beacon, record)
                    else:
                        logging.debug("WARNING Failed to match beacon against FreeWheel\'s XML")

            # Response Fired Events
            elif 'Response' in source:
                if 'slot' in beacon_type:
                    record = cursor.execute(query_response_slot.format(tn=table, **vars(beacon))).fetchone()
                    if record:
                        update_db_successfully_received_impression(record)
                        beacon = beacon_update_from_sql_record(beacon, record)
                    else:
                        logging.debug("WARNING Failed to match beacon against FreeWheel\'s XML")
                elif 'quartile' in beacon_type:
                    record = cursor.execute(query_response_quartile.format(tn=table, **vars(beacon))).fetchone()
                    if record:
                        update_db_successfully_received_impression(record)
                        beacon_update_from_sql_record(beacon, record)
                    else:
                        logging.debug("WARNING Failed to match beacon against FreeWheel\'s XML")
                elif 'tracking' in beacon_type:
                    record = cursor.execute(query_response_tracking.format(tn=table, **vars(beacon))).fetchone()
                    if record:
                        update_db_successfully_received_impression(record)
                        beacon = beacon_update_from_sql_record(beacon, record)
                    else:
                        logging.debug("WARNING Failed to match beacon against FreeWheel\'s XML")
            return beacon

    except Exception as ex:
        logging.debug(format_exception(ex))


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
    table = 'Impressions'
    sql_query_internal_slot = '''
        SELECT * FROM {tn} 
         WHERE slot_id={slot_id} AND event='{impression}' AND sent is NULL ORDER BY pk DESC LIMIT 1;
        '''
    sql_query_internal_quartile = '''
        SELECT * FROM {tn} 
         WHERE slot_id='{slot_id}' AND ad_id='{ad_id}' AND event='{impression}' AND type='quartile' 
         ORDER BY pk DESC LIMIT 1;
        '''
    sql_query_external_slot = '''
        SELECT * FROM {tn} 
         WHERE time_position={time_position} AND type='{beacon_type}' AND event='{impression}' AND url='{url}'
           AND sent is NULL;
        '''
    # sql_query_external_quartile = '''
    #     SELECT * FROM {tn}
    #      WHERE time_position={time_position} AND ad_id='{ad_id}' AND type='{beacon_type}' AND event='{impression}'
    #        AND url='{url}' AND sent is NULL AND active='True';
    #     '''
    # sql_query_external_tracking = '''
    #     SELECT * FROM {tn}
    #      WHERE type='{beacon_type}' AND event='{impression}' AND url='{url}' AND sent IS NULL AND active='True';
    #     '''

    sql_query_external_quartile = '''
        SELECT * FROM {tn} 
         WHERE time_position={time_position} AND ad_id='{ad_id}' AND type='{beacon_type}' AND event='{impression}'
           AND url='{url}' AND active='True';
        '''

    sql_query_external_tracking = '''
        SELECT * FROM {tn} 
         WHERE type='{beacon_type}' AND event='{impression}' AND url='{url}' AND active='True';
        '''

    # sql_query_response_slot = '''
    #     SELECT * FROM {tn}
    #      WHERE time_position={time_position} AND type='{beacon_type}' AND event='{impression}' AND url='{url}'
    #        AND received is NULL AND active='True';
    #     '''
    # sql_query_response_quartile = '''
    #     SELECT * FROM {tn}
    #      WHERE time_position={time_position} AND ad_id='{ad_id}' AND type='{beacon_type}' AND event='{impression}'
    #        AND url='{url}' AND received is NULL AND active='True';
    #     '''

    sql_query_response_slot = '''
        SELECT * FROM {tn} 
         WHERE time_position={time_position} AND type='{beacon_type}' AND event='{impression}' AND url='{url}'
           AND active='True';
        '''
    sql_query_response_quartile = '''
        SELECT * FROM {tn} 
         WHERE time_position={time_position} AND ad_id='{ad_id}' AND type='{beacon_type}' AND event='{impression}'
           AND url='{url}' AND active='True';
        '''
    sql_query_response_tracking = '''
        SELECT * FROM {tn} WHERE url='{url}' AND received is NULL AND active='True';
        '''

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
                        logging.debug("WARNING Failed to match beacon against FreeWheel\'s XML")
                elif 'quartile' in beacon_type:
                    record = cursor.execute(sql_query_external_quartile.format(tn=table, **vars(beacon))).fetchone()
                    if record:
                        update_db_successfully_sent_impression(record)
                        beacon = beacon_update_from_sql_record(beacon, record)
                    else:
                        logging.debug("WARNING Failed to match beacon against FreeWheel\'s XML")
                elif 'tracking' in beacon_type:
                    record = cursor.execute(sql_query_external_tracking.format(tn=table, **vars(beacon))).fetchone()
                    if record:
                        update_db_successfully_sent_impression(record)
                        beacon = beacon_update_from_sql_record(beacon, record)
                    else:
                        logging.debug("WARNING Failed to match beacon against FreeWheel\'s XML")

            # Response Fired Events
            elif 'Response' in source:
                if 'slot' in beacon_type:
                    record = cursor.execute(sql_query_response_slot.format(tn=table, **vars(beacon))).fetchone()
                    if record:
                        update_db_successfully_received_impression(record)
                        beacon = beacon_update_from_sql_record(beacon, record)
                    else:
                        logging.debug("WARNING Failed to match beacon against FreeWheel\'s XML")
                elif 'quartile' in beacon_type:
                    record = cursor.execute(sql_query_response_quartile.format(tn=table, **vars(beacon))).fetchone()
                    if record:
                        update_db_successfully_received_impression(record)
                        beacon_update_from_sql_record(beacon, record)
                    else:
                        logging.debug("WARNING Failed to match beacon against FreeWheel\'s XML")
                elif 'tracking' in beacon_type:
                    record = cursor.execute(sql_query_response_tracking.format(tn=table, **vars(beacon))).fetchone()
                    if record:
                        update_db_successfully_received_impression(record)
                        beacon = beacon_update_from_sql_record(beacon, record)
                    else:
                        logging.debug("WARNING Failed to match beacon against FreeWheel\'s XML")
            return beacon

    except Exception as ex:
        logging.debug(format_exception(ex))


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
        table = 'Impressions'
        slot = "SELECT DISTINCT pod_id, slot_id, time_position FROM {tn} WHERE pod_id={pod_id} AND type=='slot'"
        for record in cursor.execute(slot.format(tn=table, pod_id=pod_id)):
            msg = 'Inserting Slot Impression: pod_id={0} slot_id={1} time_position={2}'
            logging.debug(msg.format(*record))

        quartile = "SELECT DISTINCT pod_id, slot_id, ad_id FROM {tn} WHERE pod_id={pod_id} AND type=='quartile'"
        for record in cursor.execute(quartile.format(tn=table, pod_id=pod_id)):
            msg = 'Inserting Quartile Impression: pod_id={0} slot_id={1} ad_id={2}'
            logging.debug(msg.format(*record))

        tracking = "SELECT DISTINCT pod_id, slot_id, ad_id, event, tracking_num FROM {tn} " \
                   "WHERE pod_id={pod_id} AND type=='tracking'"
        for record in cursor.execute(tracking.format(tn=table, pod_id=pod_id)):
            msg = "Inserting Tracking Impression: pod_id={0} slot_id={1} ad_id={2} event={3} tracking_num={4}"
            logging.debug(msg.format(*record))

        creative = "SELECT DISTINCT pod_id, slot_id, ad_id, creative_url, duration FROM {tn} " \
                   "WHERE pod_id={pod_id} AND type='quartile' AND event='defaultImpression'"
        for record in cursor.execute(creative.format(tn=table, pod_id=pod_id)):
            msg = 'Inserting Creative: pod_id={0} slot_id={1} ad_id={2} creative_url={3} duration={4}'
            logging.debug(msg.format(*record))


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
            cursor.execute("SELECT sm3pointscacheitem FROM AdPods ORDER BY pod_id DESC LIMIT 1")
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
        logging.debug('ERROR Problem processing SM3 Points Cache Item #{0}')
        logging.debug(format_exception(ex))


def sm3_store_log(match):
    """
    Stores the log entry for the SM3PointsCacheItem.

    :param object match: The SM3PointsCacheItem object.
    :return: lastrowid: The ID of the last row inserted.
    :rtype: int
    """
    with SQLiteDB() as cursor:
        cursor.execute('''
            INSERT INTO AdPods (sm3pointscacheitem) 
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
                        UPDATE AdPods 
                           SET request = ? 
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
                        UPDATE AdPods 
                           SET response = ? 
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
            DELETE FROM Impressions 
             WHERE ROWID NOT IN (
                SELECT MIN(rowid) 
                  FROM Impressions 
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
    results = []
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
            INSERT INTO Impressions
                (pod_id, slot_id, ad_id, type, event, url, duration, fire_time, tracking_num)
            VALUES
                (:pod_id, :slot_id, :ad_id, :type, :event, :url, :duration, :fire_time, :tracking_num);
            ''', results)

        # Provide debugging output per user's request
        if logging.getLogger().isEnabledFor(logging.DEBUG):
            cursor.execute("SELECT * FROM Impressions WHERE pod_id=?", (pod_id,))
            column_names = tuple(map(lambda x: x[0], cursor.description))
            rows = cursor.fetchall()
            table = "\n".join(map(str, rows))
            msg = "Number of Impressions in SM3\'s Ad Response #{0}: {1}\n{2}\n{3}"
            logging.debug(msg.format(pod_id, len(rows), column_names, table))


def sm3_remove_debug_info(match):
    # type: (SimpleGrep) -> object
    """
    Remove the debug information from the SM3PointsCacheItem. In order to
    determine if the previous and current SM3PointsCacheItems are identical
    or not, the '_debug' information needs to be removed before performing
    the comparision.

    :param SimpleGrep match: Instance of SimpleGrep
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
        with open(filepath, 'w', encoding='utf-8') as outfile:
            outfile.write(xml)
    except Exception as ex:
        logging.debug("ERROR Problem writing FreeWheel\'s XML Ad Response out to disk.")
        logging.debug(format_exception(ex))


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
        logging.debug('ERROR Problem writing SM3 Cache Point Items out to disk.')
        logging.debug(format_exception(ex))


def save_html_report_to_disk(pod_id, slot_id, content):
    # type: (int, str, str) -> None
    """
    Saves the Dynamic Ad Insertion report to a temporary directory.

    :param int pod_id: The ID of the Ad Request submitted to FreeWheel.
    :param str slot_id: The Ad Request Slot ID (aka SLID) submitted to FreeWheel.
    :param str content: The HTML document
    :return None
    """
    try:
        #directory = tempfile.gettempdir()
        directory = ((sys.argv[2][::-1]).split('\\', 1))[1][::-1]
        filename = 'Ad_Response_num_{0}_Slot_ID_{1}.html'.format(str(pod_id).zfill(2), slot_id)
        filepath = '/'.join([directory, filename])
        logging.info('Writing Ad Response #{0} for Slot_ID {1} to file://{2}'.format(pod_id, slot_id, filepath))
        with open(filepath, 'w') as outfile:
            outfile.write(content)
    except Exception as ex:
        logging.debug('ERROR Problem writing DAI Validation Report out to disk.')
        logging.debug(format_exception(ex))


def save_html_report_to_database(pod_id, slot_id, content):
    """ Saves the DAI Validation Report to the database. """
    with SQLiteDB() as cursor:
        if not pod_id:
            pod_id = 1
        if not slot_id:
            slot_id = 1
        if not content:
            content = 'Missing Everything (e.g., Ad Request, Ad Response, QVT)'
        cursor.execute('''
            INSERT into Reports (pod_id, slot_id, content) 
            VALUES (?, ?, ?);
        ''', (pod_id, slot_id, content))


def fetch_html_report_from_database(slot_id=None):
    """ Retrieves the HTML DAI Validation Report from the database. """
    with SQLiteDB() as cursor:
        if slot_id is None:
            cursor.execute("SELECT pod_id, slot_id, content FROM Reports;")
        else:
            cursor.execute("SELECT pod_id, slot_id, content FROM Reports WHERE slot_id=?;", (slot_id,))
        for row in cursor.fetchall():
            save_html_report_to_disk(*row)


def pandas_set_options():
    """ Sets some options in Pandas to define how the output should be displayed. """
    pd.set_option('display.expand_frame_repr', False)  # Prevent the table from line wrapping
    pd.set_option('display.float_format', '{:.0f}'.format)
    pd.set_option('display.max_colwidth', 255)
    pd.set_option('display.max_columns', None)
    pd.set_option('display.max_rows', None)
    pd.set_option('colheader_justify', 'center')
    pd.set_option('precision', 2)


def format_section_error(error_msg):
    return "<div class='indent'><span class='text-fail'>{}</span></div>".format(error_msg)


def format_section_success(msg):
    return "<div class='indent'><span class='text-pass'>{}</span></div>".format(msg)


def format_missing(value):
    return "<span class='text-missing'>{}</span>".format(value)


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

    :param TextIO source: Adaptive Player's player.log file
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


def create_html_section_header(heading):
    return "<hr><h2 class='subtitle-blue' id='{0}'>{0}:</h2>".format(heading)


def create_list_item(desc, item, width='short'):
    return '''
        <ul class='flex-container'>
            <li class='flex-{0}-desc'>{1}:</li>
            <li class='flex-item'>{2}</li>
        </ul>
    '''.format(width, desc, item)


def to_html():
    """
    Query the database for all the Ad Breaks encountered in the player.log and
    use the results to generate the HTML report.

    Encountered the following scenarios thus far:
        1) Single Slot ID (normal).
        2) Multiple Slot IDs (unusual).
        3) Missing Slot ID(s) (unusual).
        4) Missing Ad Request (unusual).
        5) Missing Ad Response (unusual).
    """
    rows = db_fetch_dai_info()
    if rows:
        for row in rows:
            pod_id, slot_id, request_str, response_str = row
            qvt_record = db_fetch_qvt_record(slot_id)
            generate_html_report(pod_id, slot_id, request_str, response_str, qvt_record)
    else:
        no_data = (None,)*5
        generate_html_report(*no_data)


def generate_html_report(pod_id, slot_id, request_str, response_str, qvt_record):
    """
    Generate the HTML Report to display to the end user.

    :param int pod_id:  The ID of the Advertisement Pod.
    :param str slot_id: The Ad Request Slot ID (aka SLID) submitted to FreeWheel.
    :param str request_str: The Ad Request submitted to Freewheel.
    :param str response_str:  The Ad Response received from FreeWheel
    :param dict qvt_record: Information about the QVT.
    """
    global display_controls
    display_controls = []
    content = to_html_title_element(slot_id)
    content += to_html_style_element()
    content += to_html_keycode_script_element()
    content += to_html_toggle_script_element()
    content += to_html_display_program_version_info()
    content += to_html_display_report_heading(pod_id, slot_id)
    content += to_html_display_controls()
    content += to_html_display_channel_info(qvt_record)
    content += to_html_display_qvt_link(qvt_record)
    content += to_html_display_ad_request_url(request_str)
    content += to_html_display_validated_ad_request_url(pod_id, slot_id)
    content += to_html_display_ad_response_xml(response_str)
    content += to_html_display_ad_response_xml_validation(response_str, slot_id)
    content += to_html_display_media_m3u8_extension(pod_id, slot_id)
    content += to_html_display_beacon_summary(pod_id, slot_id, qvt_record)
    content += to_html_display_beacon_validation(slot_id)
    content += to_html_display_duplicate_beacons_and_responses(slot_id)
    content += to_html_display_unmatched_beacons_and_responses(slot_id)
    content = to_html_display_controls(content)
    save_html_report_to_database(pod_id, slot_id, content)


def to_html_title_element(slot_id):
    # type: (str) -> str
    """ Provides the initial HTML head and title elements for the HTML document. """
    html = '''
        <!DOCTYPE html>
        <html lang="en-US">
        <head>
        <title>Slot ID: {0}</title>
        <meta charset='UTF-8'>
        <meta name="viewport" content="width=device-width, initial-scale=1.0">
    '''
    return html.format(slot_id)


def to_html_style_element():
    # type: () -> str
    """ Provides internal CSS stylesheet for the HTML document. """
    html = '''
        <style>
            html {
                font-family: sans-serif;
                -ms-text-size-adjust: 100%;
                -webkit-text-size-adjust: 100%;
            }
                      
            body {
                background-color: black;
                color: white;
            }

            a {
                background: #000000;
                color: #faa21e;
                background-color: transparent;
                padding:1px;
            }

            a:focus,a:hover {
                color: #faa21e;
                text-decoration: underline;
                background-color: transparent;
            }

            a.text-error:focus,a.text-error:hover { 
                color: #843534 ;
            }

            table {
                border=0;
                border-collapse: collapse;
                border-spacing: 0;
            }

            th {
                padding: 5px;
            }

            td {
                padding: 1px;
            }
            
            ul {
                width: 100%;
                list-style-type: none;
                margin: auto;
                white-space: nowrap;
            }
            
            .beacon {
                display: flex;
                font-size: 10pt;
                font-family: CourierNew;
            }

            .btn {
                display: inline-block;
                margin-bottom: 5px;
                font-weight: 500;
                text-align: center;
                white-space: nowrap;
                vertical-align: middle;
                -ms-touch-action: manipulation;
                touch-action: manipulation;
                cursor: pointer;
                background-image: none;
                border: 1px solid transparent;
                padding: 2px 8px;
                font-size: 12px;
                line-height: 1.42857143;
                border-radius: 4px;
                -webkit-user-select: none;
                -moz-user-select: none;
                -ms-user-select: none;
                user-select: none;
            }

            .btn-fail {
                color: #fff;
                background-color: #d9534f;
                border-color: #d43f3a;
            }

            .btn-fail.focus,
            .btn-fail:focus {
                color: #fff;
                background-color: #c9302c;
                border-color: #761c19;
            }

            .btn-fail:hover {
                color: #fff;
                background-color: #c9302c;
                border-color: #ac2925;
            }

            .btn-success {
                color: #fff;
                background-color: #5cb85c;
                border-color: #4cae4c;
            }

            .btn-success.focus,
            .btn-success:focus {
                color: #fff;
                background-color: #449d44;
                border-color: #255625;
            }

            .btn-success:hover {
                color: #fff;
                background-color: #449d44;
                border-color: #398439;
            }

            .code {
                color: magenta;
            }

            .container {
                padding-right: 15px;
                padding-left: 15px;
                margin-right: auto;
                margin-left: auto;
            }

            .double_indent {
                margin-left: 4em;
            }

            .indent {
                margin-left: 2em;
            }

            .info {
                display: flex;
                font_size: 1.25em;
            }

            .log {
                display: flex;
                font-size: 10pt;
                font-family: CourierNew;
            }

            .overlay_able {
                position: relative;
                display: inline-block;
            }

            .overlay {
                white-space: nowrap;
                visibility: hidden;
                background-color: grey;
                text-align: left;
                border-radius: 6px;
                padding: 5px;
                position: absolute;
                z-index: 1;
                bottom: 100%;
                left: 0%;
                opacity: 0;
                transition: opacity1s;
            }

            .overlay_able:hover.overlay {
                visibility: visible;
                opacity: 1;
            }

            .subtitle-blue {
                font-size: 1.5em;
                text-decoration: underline;
                color: rgb(20, 171, 224);
            }

            span.nowrap {
                white-space: nowrap;
            }

            .text-left {
                text-align: left;
            }

            .text-right {
                text-align: right;
            }

            .text-center {
                text-align: center;
            }

            .text-justify {
                text-align: justify;
            }

            .text-nowrap {
                white-space: nowrap;
            }

            .text-lowercase {
                text-transform: lowercase;
            }

            .text-uppercase {
                text-transform: uppercase;
            }

            .text-capitalize {
                text-transform: capitalize;
            }

            .text-error {
                color: red;
            }

            .text-pass,
            .text-found {
                color: lime;
            }

            .text-fail,
            .text-missing {
                color: red;
            }

            .text-skip {
                color: yellow;
            }

            .text-version {
                text-align: right;
                font-family: monospace, monospace;
                font-size: small;
                color: rgb(181, 181, 181);
            }

            .title-orange {
                font-size: 2em;
                font-weight: bold;
                text-align: center;
                color: rgb(250, 162, 30);
            }

            .value {
                color: white;
            }

            /* Commented the th and td borders*/
            /*
            th {
                border-bottom: 1px solid #ddd; 
                padding:5px
            } 

            td {
                border-bottom: 1px solid #ddd; 
                padding:1px
            } 
            */

            .flex-container {
                padding: 0;
                margin: 0;
                list-style: none;
                padding-left: 15px;

                display: -webkit-box;
                display: -moz-box;
                display: -ms-flexbox;
                display: -webkit-flex;
                display: flex;

                -webkit-flex-flow: row wrap;
                /* justify-content: space-around; */
                justify-content: flex-start;
            }

            .flex-short-desc {
                padding: 0px;
                width: 140px; 
                /* height: 150px;*/
                /* margin-top: 10px; */
                /* line-height: 150px; */
                color: white;
                /* font-weight: bold; */
                font-size: 1em;
                text-align: left;
            }

            .flex-long-desc {
                padding: 0px;
                width: 230px; 
                color: white;
                font-size: 1em;
                text-align: left;
            }

            .flex-item {
                padding: 0px;
                /* width: 130px;     */
                /* height: 150px;    */
                /* margin-top: 10px; */
                /* line-height: 150px; */
                color: white;
                /* font-weight: bold; */
                font-size: 1em;
                text-align: left;
            }

            .flex-document {
                margin-left: 9em;
                padding: 0px;
                color: white;
                /* font-weight: bold; */
                font-size: 1em;
                text-align: left;
            }
        </style>
        </head>
    '''
    return html


def to_html_keycode_script_element():
    # type: () -> str
    """ Provides client-side scripting statements for keyboard events. """
    html = ''' 
        <body>
        <script>
            document.addEventListener('keydown',
                function (event) {
                    if (event.keyCode == 48 || event.keyCode == 72) {
                        document.getElementById('Home').scrollIntoView();
                    } else if (event.keyCode == 49) {
                        document.getElementById('QVT Link').scrollIntoView();
                    } else if (event.keyCode == 50) {
                        document.getElementById('Ad Request URL').scrollIntoView();
                    } else if (event.keyCode == 51) {
                        document.getElementById('Validated Ad Request URL').scrollIntoView();
                    } else if (event.keyCode == 52) {
                        document.getElementById('Ad Response XML').scrollIntoView();
                    } else if (event.keyCode == 53) {
                        document.getElementById('Ad Response XML Validation').scrollIntoView();
                    } else if (event.keyCode == 54) {
                        document.getElementById('Media File Extension').scrollIntoView();
                    } else if (event.keyCode == 55) {
                        document.getElementById('Beacon Validation').scrollIntoView();
                    } else if (event.keyCode == 56) {
                        document.getElementById('Duplicate Beacons and Responses').scrollIntoView();
                    } else if (event.keyCode == 57) {
                        document.getElementById('Unmatched Beacons and Responses').scrollIntoView(); 
                    }
                }
            );
        </script>
    '''
    return html


def to_html_toggle_script_element():
    # type: () -> str
    """ Provides client-side scripting statements for toggling HTML sections. """
    html = ''' 
        <script>
            function toggleQVTJSONContent() {
                var x = document.getElementById('show_qvt');
                var button = document.getElementById('qvt_button');
                if (x.style.display === 'none') {
                    x.style.display = 'block';
                    button.innerText = 'HIDE';
                } else {
                    x.style.display = 'none';
                    button.innerText = 'SHOW';
                }
            }
            
            function toggleXMLContent() {
                var x = document.getElementById('show_xml');
                var button = document.getElementById('xml_button');
                if (x.style.display === 'none') { 
                    x.style.display = 'block'; 
                    button.innerText = 'HIDE'; 
                } else { 
                    x.style.display = 'none'; 
                    button.innerText = 'SHOW'; 
                }
            }

            function toggleAdRequestParams() {
                var x = document.getElementById('show_request');
                var button = document.getElementById('request_button');
                if (x.style.display === 'none') { 
                    x.style.display = 'block'; 
                    button.innerText = 'HIDE'; 
                } else { 
                    x.style.display = 'none'; 
                    button.innerText = 'SHOW'; 
                }
            }
        </script>
    '''
    return html


def to_html_display_program_version_info():
    """ Displays the version of this program in the upper right corner of the DAI Validation Report. """
    return "<div class='text-version'>v{}</div>".format(__version__)


def to_html_display_report_heading(pod_id, slot_id):
    """ Displays the title of the DAI Validation Report.
    :return: HTML formatted string
    """
    section = "Home"
    header = '''
        <div class='title-orange' id='{section}'>
            DAI Validation Report for Ad Request Number: {pod_id}<br>
            Slot ID: {slot_id}<br>
        </div>
    '''
    return header.format(section=section, pod_id=pod_id, slot_id=slot_id)


def to_html_display_controls(content=None):
    # type: (str) -> str
    """
    Display controls to provide the ability to navigate the HTML document via mouse or keyboard.

    :param str content: The HTML document.
    :return: HTML formatted string
    :rtype: str
    """
    section = "Display Controls"
    header = '''<hr><div id="{section}" class="container">{buttons}</div>'''
    embedded_str = 'embedded_kludge_for_display_controls'
    if not content:
        return embedded_str
    buttons = ''.join(update_button_status(index, k, v) for index, (k, v) in enumerate(display_controls))
    html_display_buttons = header.format(section=section, buttons=buttons)
    return content.replace(embedded_str, html_display_buttons)


def to_html_display_channel_info(qvt):
    # type: (dict) -> str
    """
    Displays information about the Channel, Asset, Start and End Times, and Duration.

    :param dict qvt: Information about the QVT.
    :return: HTML formatted string
    :rtype: str
    :raises AttributeError
    :raises TypeError: if the qvt is None.
    """
    section = "Channel"
    header = create_html_section_header(section)
    try:
        if 'Missing' not in qvt['channel']:
            channel = qvt['channel']
        else:
            channel = MISSING

        if 'Missing' not in qvt['title']:
            title = qvt['title']
        else:
            title = MISSING

        if 'Missing' not in qvt['start_offset_with_delay']:
            start_time = convert_epoch_to_datestr(qvt['start_offset_with_delay'])
        else:
            start_time = MISSING

        if 'Missing' not in qvt['stop_offset_with_delay']:
            end_time = convert_epoch_to_datestr(qvt['stop_offset_with_delay'])
        else:
            end_time = MISSING

        if 'Missing' not in qvt['duration']:
            duration = qvt['duration']
        else:
            duration = MISSING
    except (AttributeError, TypeError):
        channel, title, start_time, end_time, duration = (MISSING,)*5

    info = [
        ('Channel', channel),
        ('Asset', title),
        ('Start Time', start_time),
        ('End Time',  end_time),
        ('Duration (secs)', duration)
    ]
    block_element = ''.join(create_list_item(k, v) for k, v in info)
    html = ''.join([header, block_element])
    update_display_controls(html, section)
    return html


def to_html_display_qvt_link(qvt):
    # type: (dict) -> str
    """
    Displays the URL for the QVT and the JSON object of the entire QVT.

    :param dict qvt: Information about the QVT.
    :return: HTML formatted string
    :rtype: str
    """
    section = "QVT Link"
    header = create_html_section_header(section)
    button = "<button id='qvt_button' onclick='toggleQVTJSONContent()'> HIDE </button>"
    json_html = MISSING.replace('Missing', '{Missing QVT Object}')
    timestamp, log, qvt_url = (MISSING,)*3
    try:
        if 'Missing' not in qvt['log']:
            log = qvt['log']
        else:
            log = MISSING

        if 'Missing' not in qvt['url']:
            url = qvt['url']
        else:
            url = qvt_url = MISSING

        qvt_string = re.match(r'^.*AdaptiveVideo Timeline loaded: (?P<qvt>{".*}(\s|$))', log).group('qvt')
        if qvt_string:
            json_data = json.loads(qvt_string)
            json_html = json.dumps(json_data, indent=4).replace('    ', '&emsp;&emsp;').replace('\n', '<br>')
            timestamp = re.match(r'^(?P<date>\d{4}/\d{2}/\d{2}\s\d{2}:\d{2}:\d{2})', log).group(1)
            qvt_url = "<a href='{0}' target='_blank'> {0}</a>".format(url)
    except (AttributeError, TypeError):
        timestamp, log, qvt_url = (MISSING,)*3
        pass

    info = [
        ('Date and Time', timestamp),
        ('URL', qvt_url),
        ('JSON', button)
    ]
    template = '''
        <div class='flex-document' id='show_qvt'>
            {json}
        </div>
    '''
    block_element = ''.join(create_list_item(k, v) for k, v in info)
    html = ''.join([header, block_element, template.format(json=json_html)])
    update_display_controls(html, section)
    return html


def to_html_display_ad_request_url(request_str):
    # type: (str) -> str
    """
    Displays the Ad Request parameters submitted to FreeWheel by importance.

    :param str request_str: The Ad Request submitted to Freewheel.
    :return: HTML formatted output
    :rtype: str
    """
    section = "Ad Request URL"
    header = create_html_section_header(section)
    button = "<button id='request_button' onclick='toggleAdRequestParams()'> HIDE </button>"
    body = '''
        <ul class='flex-container'>
            <li class='flex-short-desc'>Date and Time:</li>
            <li class='flex-item'>{date}</li>
        </ul>
        <ul class='flex-container nowrap'>
            <li class='flex-short-desc'>URL:</li>
            <span class='flex-short-desc nowrap'>{url}</span>
        </ul>
        <ul class='flex-container'>
            <li class='flex-short-desc'>Parameters:</li>
            <li class='flex-item'>{button}</li>
        </ul>
        <div class='flex-document' id='show_request'>
            <br>
            <div class='flex-container indent'>
            <table>
                <tr> <td>--- Important ---</td></tr>
                        {table_1}
                <tr> <td> <br> </td> </tr>
                <tr> <td>--- Secondary ---</td> </tr>
                        {table_2}
            </table>
          </div>
        </div>
    '''
    tr = "<tr><td>{}:</td><td>{}</td></tr>"

    if request_str is None:
        date = url = MISSING
        primary = secondary = '<tr><td>{}</td></tr>'.format(MISSING)
    else:
        request_obj = ParseAdRequest(request_str)
        date = request_obj.timestamp
        url = request_obj.url
        primary = ''.join(tr.format(k, v) for k, v in request_obj.important_params.items())
        secondary = ''.join(tr.format(k, v) for k, v in request_obj.non_important_params.items())
    html = ''.join([header, body]).format(button=button, date=date, table_1=primary, table_2=secondary, url=url)
    update_display_controls(html, section)
    return html


def to_html_display_validated_ad_request_url(pod_id, slot_id):
    # type: (int, str) -> str
    """
    Displays the Ad Request parameters that were validated against the QVT.

    :param int pod_id: The ID of the Ad Request submitted to FreeWheel.
    :param str slot_id: The Ad Request Slot ID (aka SLID) submitted to FreeWheel.
    :return: HTML formatted output
    :rtype: str
    """
    section = "Validated Ad Request URL"
    header = create_html_section_header(section)
    end = '</div>'
    validated_params = db_fetch_validated_url_params(pod_id, slot_id)
    if validated_params:
        body = "<div class='indent'>"
        for data in validated_params:
            body += ''' 
                {param}:<br>
                <div class='indent'>
                    {status} <br>
                    <div class='indent'>
                        <div style='display: flex;'>
                            <div>
                                Found:<br>
                                Expected:
                            </div>
                            <div style='margin-left: 1em;'>
                                <span class='value'>
                                    {found}
                                </span><br>
                                    {expected}
                            </div>
                        </div>
                    </div>
                </div>
            '''.format(**data)
    else:
        body = format_section_error('(FAILED) Unable to Validate Ad Request URL.')
    html = ''.join([header, body, end])
    update_display_controls(html, section)
    return html


def to_html_display_ad_response_xml(xml_response_str):
    # type: (str) -> str
    """
    Displays the XML Ad Response in HTML format so it can be displayed properly
    in the Ad Response XML Section of the DAI Validation Report.

    :param str xml_response_str: The Ad Response received from FreeWheel.
    :returns: HTML formatted output for the Ad Response XML Section.
    :rtype: str
    """
    section = "Ad Response XML"
    button = "<button id='xml_button' onclick='toggleXMLContent()'>HIDE</button><br>"
    header = create_html_section_header(section)
    body = '''
            <div class='flex-document' id='show_xml'>
                <span class='flex-container indent nowrap'>
                    {xml_doc}
                </span>
            </div>
        '''
    try:
        timestamp = xml_response_str[:19]
        xml_string = xml_response_str.split(' ', 2)[2]
        tree = ElementTree.ElementTree(ElementTree.fromstring(xml_string))
        errors = tree.find('errors')
        if errors is not None:
            xml_errors = ''
            for elem in errors.iter(tag='error'):
                xml_errors += '''
                    <span class='text-fail nowrap'>
                        Error_ID:{0} Name: {1} Severity: {2}
                    </span><br>
                '''.format(elem.get('id'), elem.get('name'), elem.get('severity'))
        else:
            xml_errors = 'None'

        xml_doc = format(
            minidom.parseString(xml_string)
            .toprettyxml(indent='    ')
            .replace('    ', '&emsp;&emsp;')
            .replace('<', '&lt;')
            .replace('>', '&gt;')
            .replace('\n', '<br>')
        )

        info = [
            ('Date and Time', timestamp),
            ('XML Errors', xml_errors),
            ('XML Document', button)
        ]
        block_element = ''.join(create_list_item(k, v) for k, v in info)
        html = ''.join([header, block_element, body]).format(xml_doc=xml_doc)
    except TypeError:
        error_msg = format_section_error('(FAILED) Missing XML Response')
        html = ''.join([header, error_msg])
    except ElementTree.ParseError:
        error_msg = format_section_error('(FAILED) Unable to Parse XML')
        html = ''.join([header, error_msg])
    update_display_controls(html, section)
    return html


def to_html_display_ad_response_xml_validation(xml_response_str, expected_slot_id):
    # type: (str, str) -> str
    """
    Validate the FreeWheel SmartXML Ad Response for the Event Callback information.
    The Event Callback section contains information about all the Impression Events,
    such as the Advertisement Slot IDs (e.g., slotImpression), Advertisement IDs
    (e.g., Quartiles), and 3rd-party Tracking Impressions.

    :param str xml_response_str: FreeWheel's Ad Response XML.
    :param str expected_slot_id: The Ad Request Slot ID (aka SLID) submitted to FreeWheel.
    :returns: HTML formatted output for the Ad Response XML Validation Section.
    :rtype: str
    """
    def required_events(keys):
        """ Initialize the default state of impression events to missing. """
        return dict.fromkeys(keys, MISSING)

    def convert_to_html(keys, data):
        """ Kludge to convert the dict to an HTML table. """
        df = pd.DataFrame(data)
        df = df.reindex(keys)
        df = df.transpose()
        df = df.reset_index()
        df.index = df.index + 1
        df.rename(columns={'index': 'Advertisment ID'}, inplace=True)
        return (df.style.set_table_styles(table_style()).set_properties(**{'text-align': 'center'})).render() + '<br>'

    def table_style():
        """ Returns the styling instructions for Pandas. """
        return [hover(), table_header(), table_row(), table_caption()]

    section = "Ad Response XML Validation"
    header = create_html_section_header(section)
    body = "<div class='indent'> {table_data} </div> <br>"
    try:
        logging.debug('Validating FreeWheel SmartXML Ad Response.')
        events = ['defaultImpression', 'firstQuartile', 'midPoint', 'thirdQuartile', 'complete']
        query = ".//temporalAdSlot/[@customId='{0}']//*[@adId='{1}']//*[@type='IMPRESSION'][@name='{2}']"
        xml_string = xml_response_str.split(' ', 2)[2]
        pod = OrderedDefaultDict()
        base_path = 'siteSection/videoPlayer/videoAsset/adSlots/temporalAdSlot/[@customId]'
        tree = ElementTree.ElementTree(ElementTree.fromstring(xml_string))
        # Loop through each of the Slot IDs.
        for element in tree.findall(base_path):
            slot_id = element.attrib.get('customId')
            if slot_id == expected_slot_id:
                tpos = str(int(float(element.attrib.get('timePosition', '0'))))
                # Loop through each of the Advertisment IDs.
                for elem in element.findall("[@customId='{0}']//*[@adId]".format(slot_id)):
                    ad_id = elem.attrib.get('adId')
                    pod[slot_id][ad_id] = required_events(events)
                    for impression in events:
                        # Search for Event Callback's containing the Slot ID, Ad ID, and Ad Impression.
                        event_callback = tree.find(query.format(slot_id, ad_id, impression))
                        if event_callback is not None:
                            url = event_callback.attrib.get('url')
                            re_pattern = ''.join(['adid=', ad_id, '.*cn=', impression, '.*tpos=', tpos])
                            # Verify the URL contains the expected values
                            if re.search(re_pattern, url):
                                state = FOUND
                            else:
                                state = MISSING
                        else:
                            state = MISSING
                        pod[slot_id][ad_id][impression] = state
        html = ''.join([header, body]).format(table_data=convert_to_html(events, pod[expected_slot_id]))
    except AttributeError:
        error_msg = format_section_error('(FAILED) Missing XML Response')
        html = ''.join([header, error_msg])
    except Exception:
        error_msg = format_section_error('(FAILED) Encountered error while processing XML Ad Response.')
        html = ''.join([header, error_msg])
    update_display_controls(html, section)
    return html


def to_html_display_media_m3u8_extension(pod_id, slot_id):
    # type: (int, str) -> str
    """
    Verifies the M3U8 extensions exists for the Advertisement.

    :param int pod_id: The ID of the Ad Request submitted to FreeWheel.
    :param str slot_id: The Ad Request Slot ID (aka SLID) submitted to FreeWheel.
    :returns: HTML formatted output for the M3U8 Summary Section.
    :rtype: str
    """
    def ad_creatives(_pod_id):
        """ Retrieve Ad Creative records for a given Pod ID. """
        with SQLiteDB(row=True) as cursor:
            cursor.execute('''
                SELECT ad_adId AS 'Advertisement ID', 
                       asset_url AS 'Asset URL'
                  FROM Creatives
                 WHERE pod_id = ?;
            ''', (_pod_id,))
            rows = cursor.fetchall()
        if rows:
            return [dict_from_row(row) for row in rows]

    def has_m3u8(string):
        """ Return whether or not the Ad URL ends with m3u8. """
        if 'ad.m3u8' in string:
            return FOUND
        return MISSING

    def table_style():
        """ Returns the styling instructions for Pandas. """
        return [hover(), table_header(), table_row(), table_caption()]

    section = "Media File Extension"
    header = create_html_section_header(section)
    body = "<div class='indent'>"
    end = "</div><br></div><br>"
    link = "<a href='{0}{1}' target='_blank'>{2}</a>"

    recs = ad_creatives(pod_id)
    if not recs or not slot_id:
        error_msg = format_section_error('(FAILED) Missing XML Response.')
        return ''.join([header, error_msg])

    for rec in recs:
        rec['Advertisement ID'] = link.format(PLAYER, rec['Asset URL'], rec['Advertisement ID'])
        rec['M3U8 Status'] = has_m3u8(rec['Asset URL'])

    df = pd.DataFrame(recs)
    df.index = df.index + 1
    df.drop(['Asset URL'], inplace=True, axis=1)
    table = (df.style.set_table_styles(table_style()).set_properties(**{'text-align': 'center'})).render()
    html = ''.join([header, body, table, end])
    update_display_controls(html, section)
    return html


def to_html_display_beacon_summary(pod_id, slot_id, qvt):
    # type: (int, str, dict) -> str
    """
    Displays the Beacon Summary in HTML format so it can be displayed properly in the DAI report.
    This is needed to properly display the metrics about the Tracking Impression.

    :param int pod_id: The ID of the Ad Request submitted to FreeWheel.
    :param str slot_id: The Ad Request Slot ID submitted to FreeWheel.
    :param dict qvt: Information about the QVT.
    :returns: HTML formatted output for the Beacon Summary Section.
    :rtype: str
    """
    def color_table_caption(string, dataframe):
        """ Returns a the caption tagged as pass or fail according to the success rate. """
        tag = "<span class='{}'>{}</span>"
        if any(dataframe.loc['Success Rate'].values != '100%'):
            return tag.format('text-fail', string)
        return tag.format('text-pass', string)

    def color_value(value):
        """ Returns a color attribute according to the value from a Pandas Dataframe. """
        color = 'white'
        if isinstance(value, str) and '-' not in value and 'nan' not in value:
            if float(value.rstrip('%')) != 100:
                color = 'red'
            elif float(value.rstrip('%')) == 100:
                color = 'lime'
        return 'color: {0}'.format(color)

    def table_style():
        """ Returns the styling instructions for Pandas. """
        return [hover(), table_header(), table_row(), table_caption()]

    section = "Beacon Summary"
    header = create_html_section_header(section)
    body = "<div class='double_indent'><br>"
    end = "</div><br>"

    try:
        time_position = qvt['tpos']
    except (AttributeError, TypeError):
        time_position = MISSING

    try:
        duration = db_fetch_slot_impression_duration(slot_id)
        records = db_fetch_impressions(pod_id, slot_id)
        ad_ids = list(dict.fromkeys(rec['ad_id'] for rec in records))
        ad_count = len(ad_ids)
        info = [
            ('FreeWheel Ad Response', pod_id),
            ('Slot ID', slot_id),
            ('Time Position', time_position),
            ('Number of Advertisements', ad_count),
            ('Total Ad Duration (secs)', duration),
        ]
        block_element = ''.join(create_list_item(k, v, 'long') for k, v in info)
    except (AttributeError, TypeError):
        error_msg = format_section_error('(FAILED) Missing XML Response')
        return ''.join([header, error_msg])

    try:
        index_name = 'Impression Event'
        events = ['defaultImpression', 'firstQuartile', 'midPoint', 'thirdQuartile', 'complete']
        quartile_columns = {'Expected': 'Expected', 'sent': 'Fired', 'received': 'Response'}
        tracking_columns = {'Trk_Expected': 'Trk_Expected', 'sent': 'Trk_Fired', 'received': 'Trk_Response'}
        tables = ''
        pandas_set_options()
        df = pd.DataFrame(records)
        df = df.replace('True', 1)
        df = df.fillna(value=0)

        # TODO: At some point, need to work on collapsing this to remove redundant code.
        for index, ad_id in enumerate(ad_ids, 1):
            # Advertisement with Quartile Impressions.
            caption = 'Ad #:{0}&emsp;&emsp;[Ad Id: {1}]'.format(index, ad_id)
            df_ad_id = df[df['ad_id'] == ad_id].copy()
            df_ad_id.drop(['pod_id', 'slot_id', 'ad_id'], inplace=True, axis=1)
            df_quartile = df_ad_id[df_ad_id['type'] == 'quartile'].copy()
            df_quartile.drop('type', inplace=True, axis=1)
            df_quartile['Expected'] = 1
            df_quartile.set_index('event', inplace=True)
            df_quartile.index.name = index_name
            df_quartile.rename(columns=quartile_columns, inplace=True)
            df_quartile = df_quartile.reindex(columns=quartile_columns.values())
            df_quartile = df_quartile.reindex(events)
            sum_qt_expected = df_quartile['Expected'].sum()
            sum_qt_columns = df_quartile.sum()
            qt_success_rate = ((sum_qt_columns / sum_qt_expected).apply('{:.0%}'.format))
            qt_success_rate.replace('inf%', value='0%', inplace=True)
            df_quartile.loc['Total'] = df_quartile.sum()
            df_quartile.loc['Success Rate'] = qt_success_rate

            # Advertisement with Tracking Impressions.
            df_tracking = df_ad_id[df_ad_id['type'] == 'tracking'].copy()
            if not df_tracking.empty:
                style_columns = ['Fired', 'Response', 'Trk_Fired', 'Trk_Response']
                df_tracking.drop('type', inplace=True, axis=1)
                df_tracking['Trk_Expected'] = 1
                df_tracking.set_index('event', inplace=True)
                df_tracking.index.name = index_name
                df_tracking = df_tracking.groupby(index_name).sum()
                df_tracking.rename(columns=tracking_columns, inplace=True)
                df_tracking = df_tracking.reindex(columns=tracking_columns.values())
                df_tracking = df_tracking.reindex(events)
                sum_trk_expected = df_tracking['Trk_Expected'].sum()
                sum_trk_columns = df_tracking.sum()
                trk_success_rate = ((sum_trk_columns / sum_trk_expected).apply('{:.0%}'.format))
                trk_success_rate.replace('inf%', value='0%', inplace=True)
                df_tracking.loc['Total'] = df_tracking.sum()
                df_tracking.loc['Success Rate'] = trk_success_rate
                result = pd.concat([df_quartile, df_tracking], axis=1, sort=False)
            else:
                # Advertisement without Tracking Impressions.
                style_columns = ['Fired', 'Response']
                result = df_quartile
            result.fillna('-', inplace=True)
            tables += (result.style
                       .applymap(color_value, subset=style_columns)
                       .set_table_styles(table_style())
                       .set_properties(**{'text-align': 'center'})
                       .set_caption(color_table_caption(caption, result))
                       .render())
            tables += '<br>'
        return ''.join([header, block_element, body, tables, end])
    except (AttributeError, TypeError, ValueError):
        error_msg = format_section_error('(FAILED) Encountered error while processing this section.')
        return ''.join([header, error_msg])


def to_html_display_beacon_validation(slot_id):
    # type: (str) -> str
    """
    Queries the SQL database for the given Slot Impression ID and identifies
    the event so it can be wrapped in HTML and displayed properly in the
    Beacon Validation Section of the DAI report.

    :param str slot_id: The Ad Request Slot ID (aka SLID) submitted to FreeWheel.
    :returns: HTML formatted output for the Beacon Validation Section.
    :rtype: str
    """
    section = "Beacon Validation"
    header = create_html_section_header(section)
    html = header
    with SQLiteDB(row=True) as cursor:
        cursor.execute("SELECT * FROM Impressions WHERE slot_id=?;", (slot_id,))
        rows = cursor.fetchall()
    count = 0
    if rows:
        for row in rows:
            record = dict_from_row(row)
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
                html += "<br></div>"
                # ==============================================================
                # NOTE: The STSE team doesn't want Internal information displayed
                # in the report, however, they would like to keep the logic
                # intact so that some point in the future it can be re-enabled.
                # ==============================================================
                # html += "<div class='indent'>Beacon Event : {event}<br>".format(**record)
                # html += "<div class='indent beacon'><span class='text-nowrap'>"
                # html += "<!--Internal: {internal_log}</span><br></div></div> -->".format(**record)
    else:
        html += "<div class='indent'><span class='text-fail'>(FAILED) Missing XML Response.</span></div>"
    update_display_controls(html, 'Beacon Validation')
    return html


def to_html_display_duplicate_beacons_and_responses(slot_id):
    """
    Queries a specific Slot Impression to determine if the Adaptive Player
    sent or received any duplicate impressions.
    """
    def table_style():
        """ Returns the styling instructions for Pandas. """
        return [hover(), table_header(), table_row(), table_data('red'), table_caption()]

    def find_duplicate_impressions(_slot_id):
        """ Returns records sent and received more than once. """
        with SQLiteDB(row=True) as cursor:
            cursor.execute('''
                SELECT ad_id AS 'Ad ID', 
                       type  AS 'Impression Type', 
                       event AS 'Impression Event',
                       sent_counter - 1 AS 'Sent',
                       received_counter - 1 AS 'Received'
                  FROM Impressions
                 WHERE slot_id = :slot_id
                   AND (sent_counter > 1 OR received_counter > 1)
              ORDER BY pk;
            ''', {'slot_id': _slot_id})
            column_names = list(map(lambda x: x[0], cursor.description))
            _rows = cursor.fetchall()
            return [dict_from_row(row) for row in _rows], column_names

    section = "Duplicate Beacons and Responses"
    header = create_html_section_header(section)
    body = "<div class='double_indent'>"
    error_msg = "<font class='text-fail'>(FAILED) Found Duplicates</font>"
    end = '</div><br>'
    rows, table_headings = find_duplicate_impressions(slot_id)
    if rows:
        df = pd.DataFrame(rows)
        df = df.reindex(columns=table_headings)
        df.index = df.index + 1
        body += (df.style
                 .set_table_styles(table_style())
                 .set_properties(**{'text-align': 'center'})
                 .set_caption(error_msg)
                 .render())
    else:
        body = format_section_success("(PASS) No Duplicates Found.")
    html = ''.join([header, body, end])
    update_display_controls(html, section)
    return html


def to_html_display_unmatched_beacons_and_responses(slot_id):
    # type: (str) -> str
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

    :param str slot_id: The Ad Request Slot ID (aka SLID) submitted to FreeWheel.
    :returns: HTML formatted output for the Unmatched Beacons Section.
    :rtype: str
    """
    def get_start_time(_slot_id):
        """ Returns a UNIX timestamp of the Ad Request for this Slot ID. """
        milliseconds = '.000'
        with SQLiteDB() as cursor:
            cursor.execute('''
                    SELECT substr(request, 1, 19)
                      FROM AdPods
                     WHERE request
                      LIKE '%slid={slot_id}%';
            '''.format(slot_id=_slot_id))
            date_time = cursor.fetchone()
        if date_time:
            date_str = date_time[0] + milliseconds
            unix_ts = convert_datestr_to_unix_timestamp(date_str)
            return unix_ts

    def get_stop_time(_slot_id):
        """ Returns a UNIX timestamp for when to stop searching. """
        time_delay_secs = 180
        with SQLiteDB() as cursor:
            cursor.execute('''
                    SELECT SUM(expected_firing_time + duration)
                      FROM Impressions
                     WHERE slot_id = :slot_id 
                       AND type = 'slot'
                       AND event = 'slotImpression'
            ''', {'slot_id': _slot_id})
            unix_ts = cursor.fetchone()
            if all(unix_ts):
                return unix_ts[0] + time_delay_secs

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

    section = "Unmatched Beacons and Responses"
    header = create_html_section_header(section)
    template = "<div class='double_indent'>"

    t0 = get_start_time(slot_id)
    tn = get_stop_time(slot_id)
    if all([t0, tn]):
        records = get_unmatched_impressions(t0, tn)
        if records:
            element = "<span class='beacon text-fail'>{}</span>"
            body = "<div class='beacon text-nowrap'>"
            body += ''.join(element.format(str(index) + ' : ' + rec['log']) for index, rec in enumerate(records))
        else:
            template = ''
            body = format_section_success("(PASS) No Unmatched Beacons Found.")
    else:
        template = ''
        body = format_section_error('FAILED) Missing Ad Request and/or XML Response.')
    html = ''.join([header, template, body, "</body></html>"])
    update_display_controls(html, section)
    return html


def to_html_advertisement_info(count, record):
    # type: (int, dict) -> str
    """ Returns the Advertisement information wrapped in HTML.

    :param int count: Advertisement counter.
    :param dict record: Information about the impression.
    :returns: Advertisement information wrapped in HTML
    :rtype: str
    """
    html = '''
        <br>
        <div class='indent'><hr>
            Ad Number   : {count}<br>
            Ad ID       : {ad_id}<br>
            Ad Duration : {duration} seconds<br>
            Ad Creative: <a href='{player}{creative_url}' target='_blank'>Click here to see the video</a>
        <br>
        <hr>
        </div>
    '''
    return html.format(count=count, player=PLAYER, **record)


def to_html_beacon_event_info(record):
    # type: (dict) -> str
    """ Returns the Impression Quartile information wrapped in HTML.

    :param dict record: Information about the impression.
    :returns: Beacon information wrapped in HTML
    :rtype: str
    """
    html = '''
        <br>
        <div class='indent'>Beacon Event : {event}<br>
            <div class='indent beacon'>
                <div>
                    External:<br>
                    Response:<br>
                </div>
                <div style='margin-left: 1em;'>
                    <span class='text-nowrap'>{sent_log}</span><br>
                    <span class='text-nowrap'>{received_log}</span><br> 
                </div> 
            </div> 
            <br>
            <div class='indent'>Tests:<br>
                <div class='indent beacon'>
                    {beacons_found}: Expected Firing Time: {0} [delta: {delta_firing_time} secs] <br>
                </div>
                <div class='indent beacon'>
                    {beacons_found}: All Beacons Fired <br>
                </div>
                <div class='indent beacon'>
                    {beacon_firing_order}: Valid Firing Sequence for this Impression <br>
                </div>
                <div class='indent beacon'>
                    {http_status_msg}: HTTP Status: {http_status} <br>
                </div>
            </div>
        </div>
    '''
    firing_time = convert_epoch_to_datestr(record["expected_firing_time"])
    return html.format(firing_time, **record)


def to_html_tracking_event_info(record):
    # type: (dict) -> str
    """ Returns the Tracking information wrapped in HTML.

    :param dict record: Information about the impression.
    :return: Tracking info wrapped in HTML.
    :rtype: str
    """
    html = '''
        <br>
        <div class='double_indent'>Tracking URL #: {tracking_num}<br>
            <div class='indent beacon'>
                <div>
                    Sent:<br>
                    Received:<br>
                </div>
                <div style='margin-left: 1em;'>
                    <span class='text-nowrap'>{sent_log}</span><br>
                    <span class='text-nowrap'>{received_log}</span><br> 
                </div> 
            </div> 
            <div class='indent beacon'>
                <div>
                    {http_status_msg}:<br>
                    {beacon_firing_order}:<br>
                </div>
                <div style='margin-left: 1em;'>
                    <span class='text-nowrap'>HTTP Status: {http_status}</span><br>
                    <span class='text-nowrap'>Valid Firing Sequence for this Impression</span><br>
                </div>
            </div>
        </div>
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
        cursor.execute("SELECT pk, sent_log FROM Impressions WHERE sent_log <> '';")
        for row in cursor.fetchall():
            pk, sent_log = row
            m = re.match(re_datetime, sent_log)
            if m:
                date_string = m.group()
                dt_object = datetime.strptime(date_string, '%Y/%m/%d %H:%M:%S.%f')
                unix_ts = to_unix_timestamp(dt_object)
                cursor.execute('''
                    UPDATE Impressions 
                       SET actual_firing_time = :unix_ts 
                     WHERE pk = :pk;
                    ''', {'unix_ts': unix_ts, 'pk': pk})
                msg = 'pk={0} actual_firing_time={1} sent_log={2}'
                logging.debug(msg.format(pk, unix_ts, sent_log))


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
                dt_object = datetime.strptime(date_string, '%Y/%m/%d %H:%M:%S.%f')
                unix_ts = to_unix_timestamp(dt_object)
                cursor.execute('''
                    UPDATE unmatched_table
                       SET actual_firing_time = :unix_ts 
                     WHERE pk = :pk;
                    ''', {'unix_ts': unix_ts, 'pk': pk})
                msg = 'pk={0} actual_firing_time={1} log={2}'
                logging.debug(msg.format(pk, unix_ts, log))


def calculate_duration_for_slot_impression():
    # type: () -> None
    """
    Calculates the duration of each slotImpression.  The total duration
    of a slotImpression is calculated by adding up the duration of each
    of the individual Advertisements found within the slotImpression.
    """
    with SQLiteDB(row=True) as cursor:
        cursor.execute("SELECT DISTINCT(slot_id) FROM Impressions;")
        for row in cursor.fetchall():
            slot_id = row['slot_id']
            cursor.execute('''
                UPDATE Impressions 
                   SET duration = (
                        SELECT IFNULL(SUM(duration), 0)
                          FROM Impressions 
                         WHERE event = 'defaultImpression' 
                           AND type = 'quartile' 
                           AND slot_id = :slot_id
                        )
                WHERE event = 'slotImpression' 
                  AND type = 'slot' 
                  AND slot_id = :slot_id
            ''', {'slot_id': slot_id})


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
            UPDATE Impressions 
               SET expected_firing_time = (
                        SELECT start_offset_with_delay 
                          FROM qvt_table 
                         WHERE qvt_table.cue_point_number = Impressions.slot_id
                   ) 
             WHERE Impressions.type = 'slot' 
               AND Impressions.event = 'slotImpression' 
               AND EXISTS (
                    SELECT start_offset_with_delay 
                      FROM qvt_table 
                     WHERE qvt_table.cue_point_number = Impressions.slot_id
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
              FROM Impressions 
             WHERE event = 'slotImpression'
               AND expected_firing_time != 0;
        ''')
        slot_impression_records = cursor.fetchall()
        # Retrieve all of the defaultImpressions for a given slotImpression.
        for slot_record in slot_impression_records:
            slot_id, slot_timestamp = slot_record
            total_ad_duration = 0
            cursor.execute('''
                SELECT pk, duration 
                  FROM Impressions 
                 WHERE slot_id = :slot_id
                   AND type = 'quartile' 
                   AND event = 'defaultImpression' 
                   AND expected_firing_time = 0;
            ''', {'slot_id': slot_id})
            default_impression_records = cursor.fetchall()
            # Step through each of the defaultImpressions and calculate the
            # start_time of the defaultImpression. Add the Ad's duration
            # to the running total and use the sum of this value to calculate
            # the timestamp of when the next defaultImpression is to be sent.
            for default_record in default_impression_records:
                pk, ad_duration = default_record
                scheduled_firing_time = slot_timestamp + total_ad_duration
                total_ad_duration += ad_duration
                cursor.execute('''
                    UPDATE Impressions 
                       SET expected_firing_time = :scheduled_firing_time 
                     WHERE pk = :pk;
                ''', {'scheduled_firing_time': scheduled_firing_time, 'pk': pk})


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
              FROM Impressions
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
                    UPDATE Impressions 
                       SET expected_firing_time = ? 
                     WHERE slot_id = ? 
                       AND ad_id = ? 
                       AND event = ?;
                ''', (scheduled_start_time, slot_id, ad_id, quartile[0]))
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
    values = []
    with SQLiteDB(row=True) as cursor:
        cursor.execute('''
            SELECT pk, sent_log, expected_firing_time, actual_firing_time 
              FROM Impressions
             WHERE type != 'tracking';
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
            UPDATE Impressions
               SET delta_firing_time = :delta
             WHERE pk = :pk;
        ''', values)


def identify_missing_beacons():
    missing = 'Missing'
    with SQLiteDB(row=True) as cursor:
        cursor.execute("UPDATE Impressions SET internal_log=? WHERE internal_log='';", (missing,))
        cursor.execute("UPDATE Impressions SET sent_log=? WHERE sent_log='';", (missing,))
        cursor.execute("UPDATE Impressions SET received_log=? WHERE received_log='';", (missing,))


def color_beacons(_args):
    """ Colors the log entry to indicate if it passed (green) or failed (red). """
    values = []
    logs = ['internal_log', 'sent_log', 'received_log']
    with SQLiteDB(row=True) as cursor:
        cursor.execute('''
            SELECT pk, internal_log, sent_log, received_log 
              FROM Impressions;
        ''')
        for row in cursor.fetchall():
            row_as_dict = dict_from_row(row)
            # Determine if the timestamps begin with a 4 digit year
            for log in logs:
                logline = row_as_dict[log]
                if _args.html:
                    if logline[:4].isdigit():
                        logline = "<span class='text-pass'>{0}</span>".format(logline)
                    else:
                        logline = "<span class='text-fail'>{0}</span>".format(logline)
                row_as_dict[log] = logline
            values.append(row_as_dict)

        cursor.executemany('''
            UPDATE Impressions
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
              FROM Impressions;
        ''')
        for row in cursor.fetchall():
            pk, sent_log, received_log = row
            if all([sent_log[:4].isdigit(), received_log[:4].isdigit()]):
                result = PASS
            else:
                result = FAIL
            cursor.execute('''
                UPDATE Impressions 
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
        cursor.execute("SELECT pk, sent_log, received_log FROM Impressions;")
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
            cursor.execute("UPDATE Impressions SET beacon_firing_order=? WHERE pk=?;", (result, pk))


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
        cursor.execute("SELECT pk, event, actual_firing_time * FROM Impressions;")
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
            cursor.execute("UPDATE Impressions SET beacon_firing_order=? WHERE pk=?;", (result, pk))


def validate_http_response_status():
    # type: () -> None
    """ Determines if the HTTP response is valid. """
    with SQLiteDB(row=True) as cursor:
        cursor.execute("SELECT pk, http_status FROM Impressions;")
        for row in cursor.fetchall():
            pk, http_status = row
            response_code = int(http_status.strip() or 0)
            if response_code == 200 or response_code == 204:
                result = PASS
            else:
                result = FAIL
            cursor.execute("UPDATE Impressions SET http_status_msg=? WHERE pk=?;", (result, pk))


def validate_ad_request_url():
    """ Validates the parameters in the Ad Request URL ('found') against the QVT ('expected'). """

    def add_keys(_pod_id, _slot_id, param_list):
        """ Inserts the Pod, Slot, and parameter key-values into each param element. """
        # FIXME: when we longer need python 2.7 compatibility.
        # return [{'pod_id':pod_id, 'slot_id':slot_id, 'param': k, **v} for k, v in param_list.items()]
        rec = {}
        records = []
        for key, value in param_list.items():
            rec.update({'pod_id': _pod_id, 'slot_id': _slot_id, 'param': key})
            rec.update(value)
            records.append(rec.copy())
        return records

    def compare(key, expected, found):
        """ Compares QVT params (expected) against the Ad Request's (found). """
        if key == 'TPOS':
            if is_float(expected):
                expected = float(expected)
                if expected.is_integer():
                    expected = str(int(expected))
                else:
                    expected = str(expected)

        if expected == found:
            result = 'True'
            status = PASS
        elif 'QVT Missing' in expected:
            expected = format_missing(expected)
            result = 'False'
            status = FAIL
        else:
            result = 'False'
            found = format_missing(found)
            status = FAIL

        # Temporary kludge until we can handle missing keys in QVT
        if expected == '0':
            expected = format_missing('Missing Parameter in QVT')

        # Display dashes if the param is not present for both QVT and Ad Request.
        if 'QVT Missing' in expected and 'Missing' in found:
            expected = found = '-----'
            result = 'Skip'
            status = SKIP
        return {'found': found, 'expected': expected, 'state': result, 'status': status}

    def cdn_property_validation(params, cdn_url):
        """ Return parameters validated against expected values for the CDN Property. """
        error_msg = '<br>Error: Incorrect QVT value for CDN environment ({0})'
        param = ('Adapt URL', 'FW URL', 'NW', 'SSNW', 'PROF')
        prod = ('http://p-adapt.movetv.com', 'http://5d40b.s.fwmrm.net/ad/g/1', '381963', '381963', '381963:sling')
        beta = ('http://b-adapt.movetv.com', 'http://5d40a.s.fwmrm.net/ad/g/1', '381962', '381962', '381962:sling')
        cdn_mapping = {
            'cbd46b77.cdn.cms.movetv.com': dict(zip(param, prod)),
            '93a256a7.cdn.cms.movetv.com': dict(zip(param, beta))
        }
        for cdn in cdn_mapping:
            if cdn in cdn_url:
                for key, value in cdn_mapping[cdn].items():
                    if value not in params[key]['expected']:
                        params[key]['state'] = 'False'
                        expected = ' '.join([value, error_msg.format(cdn)])
                        params[key]['expected'] = format_missing(expected)
        return params

    def compare_url_parameters(qvt_dict, request_dict):
        """ From a list of URL parameters, compares the QVT to the Ad Request. """
        key_order = [
            # E.g., [(Param Name, QVT, Ad Request), ...]
            ('Adapt URL', 'adapt_url', 'adapt_url'),
            ('AFID', 'afid', 'afid'),
            ('ASNW', 'asnw', 'asnw'),
            ('CAID', 'caid', 'caid'),
            ('FW URL', 'ads_url', 'ads_url'),
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
        params = OrderedDefaultDict()
        for key in key_order:
            params[key[0]] = compare(key[0], qvt_dict[key[1]], request_dict[key[2]])
        return params

    try:
        rows = db_fetch_dai_info()
        for row in rows:
            pod_id, slot_id, request_str, response_str = row
            request = ParseAdRequest(request_str).retrieve_ad_slot_id(slot_id)
            qvt = db_fetch_qvt_record(slot_id)
            if not all([slot_id, request_str, qvt, request]):
                return
            else:
                results = compare_url_parameters(qvt, request)
                results = cdn_property_validation(results, qvt['url'])
                results = add_keys(pod_id, slot_id, results)
                db_insert_validated_request_params(results)
    except (AttributeError, TypeError):
        pass


def hover(hover_color='#424851'):
    """ Style table row when hovering. """
    return dict(selector='tr:hover', props=[
        ('background-color', '{0}'.format(hover_color))])


def table_caption(color='white'):
    """ Style table caption. """
    return dict(selector='caption', props=[
        ('caption-side', 'top'),
        ('color', '{}'.format(color))])


def table_header(color='white'):
    """ Style table header. """
    return dict(selector='th', props=[
        ('font-size', '14px'),
        ('text-align', 'center'),
        ('color', '{}'.format(color)),
        ('background-color', 'rgb(10, 10, 10)')])


def table_row():
    """ Style table row. """
    return dict(selector='tr', props=[
        ('line-height', '11px')])


def table_data(color):
    """ Style table data. """
    return dict(selector='td', props=[
        ('font-size', '14px'),
        ('text-align', 'center'),
        ('color', '{}'.format(color))])


def convert_epoch_to_datestr(epoch, date_format='%Y/%m/%d %H:%M:%S.%f'):
    """ Convert Epoch (time in secs) to a formatted timestamp in UTC. """
    if is_float(epoch):
        return datetime.utcfromtimestamp(float(epoch)).strftime(date_format)


def convert_datestr_to_unix_timestamp(date_string, date_format='%Y/%m/%d %H:%M:%S.%f'):
    """ Convert Date and Time string to a Unix Timestamp. """
    dt_object = datetime.strptime(date_string, date_format)
    return to_unix_timestamp(dt_object)


def to_unix_timestamp(dt_obj):
    # type: (object) -> float
    """ Convert Date Time object to a Unix Timestamp (time in secs since Unix Epoch). """
    if isinstance(dt_obj, datetime):
        epoch = datetime.utcfromtimestamp(0)
        delta = dt_obj - epoch
        return delta.total_seconds()


def unix_time_milliseconds(dt):
    """ Return Unix timestamp in milliseconds. """
    if isinstance(dt, datetime):
        return int(to_unix_timestamp(dt) * 1000)


def is_float(value):
    """ Check if the value is a float. """
    try:
        float(value)
        return True
    except ValueError:
        return False


def update_display_controls(content, section):
    """
    Updates the status of the HTML buttons at the top of the DAI Validation Report
    to indicate if a section has errors. Uses a global variable to track status.
    """
    has_failed = check_section_content_for_errors(content)
    display_controls.append((section, has_failed))


def check_section_content_for_errors(content):
    """ Searches the content for CSS styles which indicate this section failed. """
    return any(['text-missing' in content, 'text-fail' in content])


def update_button_status(index, doc_id, error_status):
    """ Styles the button to indicate whether or not a section contains errors. """
    if error_status:
        button_status = 'btn-fail'
    else:
        button_status = 'btn-success'
    button_tag = '''
        <button
            type="button"
            class="btn {status}"
            onclick="document.getElementById('{doc_id}').scrollIntoView();"
            >{doc_id} (Press: \'{index}\')
        </button>
    '''
    return button_tag.format(status=button_status, doc_id=doc_id, index=index)


def dict_from_row(row):
    """ Convert a sqlite3.Row to a dict. """
    return dict(zip(row.keys(), row))


def device_lookup_table():
    """ Determines device information for Channel Service ID. """
    result = 'Unknown'
    if device_info:
        platform = device_info['device_platform']
        model = device_info['device_model']
        if 'Android TV' in platform and 'AIRTV PLAYER' in model:
            result = 'airtvplayer'
        elif 'Android TV' in platform:
            result = 'android_tv'
        elif 'Android Phone' in platform:
            result = 'android_phone'
        elif 'Android Tablet' in platform:
            result = 'android_tablet'
        elif 'Roku' in platform:
            result = 'roku'
        elif 'Apple TV' in model:
            result = 'tvos'
        elif 'iPhone' in model:
            result = 'iphone'
        elif 'iPad' in model:
            result = 'ipad'
    return result


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
    parser.add_argument('-v', '--version', version='%(prog)s {version}'.format(version=__version__), action='version')
    opts = parser.parse_args()

    if not opts.filename:
        parser.error('Please specify a logfile (e.g., /tmp/player.log)')
    return opts


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
    validate_ad_request_url()


def cleanup():
    logging.debug('Performing cleanup:')
    logging.debug('- Removing the following database: {0}'.format(SQLiteDB().path))
    SQLiteDB().delete_database_file()


# ----------------------------------------------------------------------------------------------
# Main
# ----------------------------------------------------------------------------------------------
if __name__ == "__main__":

    try:
        # Global Dictionaries
        device_info = {}

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
        with open(args.filename, 'r', encoding='utf-8') as f:
            for line in merge_multiple_lines(f):
                process(line)

        # Post-process and validate the data
        post_process_information()
        validate_information()

        # Generates the DAI Validation Report in HTML format and determine if there was
        # a request for a specific slot impression; otherwise fetch all of them.
        if args.html:
            color_beacons(args)
            to_html()
            if args.slot:
                fetch_html_report_from_database(args.slot)
            else:
                fetch_html_report_from_database()

        cleanup()
        logging.debug('Finished processing: {0}'.format(args.filename))
    except (KeyboardInterrupt, SystemExit):
        cleanup()

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
import sys
import sqlite3
import tempfile
import time
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

__version__ = "1.8.3.9-dev-a"


# ----------------------------------------------------------------------------------------------
# Constants
# ----------------------------------------------------------------------------------------------
PASS = "<span class='text-pass'>(PASS)</span>"
FAIL = "<span class='text-fail'>(FAIL)</span>"
SKIP = "<span class='text-skip'>(SKIP) </span>"
FOUND = "<span class='text-found'>Present</span>"
MISSING = "<span class='text-missing'>Missing</span>"
PLAYER = "http://demo.theoplayer.com/test-your-stream-with-statistics?url="


class MatchLogEvent:
    """
    A set of regular expressions used to parse certain Dynamic Ad Insertion
    events from the AP player.log.
    """
    # Adaptive Player version information
    _regex_ap_build = re.compile(
        r'^\d{4}/\d{2}/\d{2}\s\d{2}:\d{2}:\d{2}.*User-Agent: Mozilla.*'
        r'QSP; (?P<ap_client>.+); AP; (?P<ap_build>\b\d+\.\d+\.\d+.\d+\b)'
    )

    # Adaptive Player Device Information
    _regex_device = re.compile(
        r'^\d{4}/\d{2}/\d{2}\s\d{2}:\d{2}:\d{2}.*WeatherHelper:'
        r'(?=.*ip addr: = (?P<ip>\b\d{1,3}\.\d{1,3}\.\d{1,3}\.\d{1,3}\b))?'
        r'(?=.*deviceType = (?P<device_type>.*$))?'
        r'(?=.*devicePlatform = (?P<device_platform>.*$))?'
        r'(?=.*deviceModel = (?P<device_model>.*$))?'
    )

    # Adaptive Player 4.x Quantum Virtual Timeline (QVT)
    _regex_qvt = re.compile(
        r'^(?P<logline>.*AdaptiveVideo Timeline loaded:.*ad_info.*ad_breaks.*$)'
    )

    # iOS AP 5.x release has a different message for Quantum Virtual Timeline.
    _regex_ap_5x_ios_qvt = re.compile(
#        r'^(?P<logline>.*AdaptiveVideo.*timeline:.*ad_info.*ad_breaks.*$)'
        r'^(?P<logline>.*Timeline loaded:.*ad_info.*ad_breaks.*$)'
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
        r'^(?=.*FWAdPod response body = (?P<xml>.*</adResponse>))'
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

    # Newer releases of the Adaptive Player contain Impression events which use
    # a different terminology for DAI events (e.g., "Point" vs "Beacon"),
    # additional fields, and span multiple lines to make them human readable.
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

    # The Adaptive Player 5.x release is missing supplemental information
    # for the Response Impression such as: Ad Break ID, Advertisement ID, and
    # Event Type.
    _regex_ap_5x_response = re.compile(
        r'^(?=(?P<logline>^.*$))'
        r'(?=.*FWBeaconPacingTask\s+External\s+Point\s+Response)'
        r'(?=.*responseCode:\s(?P<response_code>\d+))?'
        r'(?=.*url:\s(?P<url>.*$))'
        r'(?=.*&adid=(?P<ad_id>\d+))?'
        r'(?=.*&cn=(?P<impression>\w+))?'
        r'(?=.*&tpos=(?P<time_position>\d+))?.*$'
    )

    __slots__ = [
        'device', 'qvt', 'ad_request', 'xml_response', 'sm3_points',
        'avg_beacon', 'fw_beacon', 'fw_callback', 'ap_internal', 'ap_external',
        'ap_response', 'ap_build', 'ap_5x_response', 'ap_5x_ios_qvt'
    ]

    def __init__(self, logline):
        """
        Match the log entry against the specific regular expressions and store
        the matched object.
        """
        self.ap_build = self._regex_ap_build.match(logline)
        self.ad_request = self._regex_ad_request.match(logline)
        self.xml_response = self._regex_xml_response.match(logline)
        self.sm3_points = self._regex_sm3_points.match(logline)
        self.avg_beacon = self._regex_avg_beacon.match(logline)
        self.fw_beacon = self._regex_fw_beacon.match(logline)
        self.fw_callback = self._regex_fw_callback.match(logline)
        self.ap_internal = self._regex_ap_internal.match(logline)
        self.ap_external = self._regex_ap_external.match(logline)
        self.ap_response = self._regex_ap_response.match(logline)
        self.ap_5x_response = self._regex_ap_5x_response.match(logline)
        self.device = self._regex_device.match(logline)
        self.qvt = self._regex_qvt.match(logline)
        self.ap_5x_ios_qvt = self._regex_ap_5x_ios_qvt.match(logline)


class Device:
    """
    Create an object view of the Device the Adaptive Player is running on.
    """
    info = {}
    hardware = [
        'Android Phone',
        'Android Tablet',
        'Android TV',
        'Apple TV',
        'iPad',
        'iPhone',
        'Roku',
    ]
    model = None
    platform = None
    ap_build = None
    ap_client = None

    def __init__(self):
        pass

    @classmethod
    def csid(cls):
        """ Retrieves the stored Channel Service ID. """
        return cls.info.get('csid', 'Unknown')

    @classmethod
    def identify_csid(cls):
        """ Finds and returns the Channel Service ID. """
        for device in cls.hardware:
            if device in cls.platform and 'AIRTV PLAYER' in cls.model:
                return 'airtvplayer'
            elif device in cls.platform and 'Apple TV' in cls.model:
                return 'tvos'
            elif device in cls.platform:
                return device.lower().replace(' ', '_')
        else:
            return 'unknown'

    @classmethod
    def set_csid(cls):
        """ Stores Channel Service ID. """
        cls.info.update({'csid': cls.identify_csid()})

    @classmethod
    def update(cls, dct):
        """ Stores key-values of the device information. """
        cls.info.update((k, v) for k, v in dct.items() if v is not None)
        cls.model = cls.info.get('device_model', '')
        cls.platform = cls.info.get('device_platform', '')
        cls.ap_build = cls.info.get('ap_build', 'Unknown Player Version')
        cls.ap_client = cls.info.get('ap_client', 'Unknown Client Version')
        cls.set_csid()

    def __repr__(self):
        return repr(Device.info)

    def __str__(self):
        return str(Device.info)


class ButtonControls:
    """ Create an object view of the Button Controls. """
    info = []

    def __init__(self):
        pass

    @classmethod
    def reset(cls):
        cls.info = []

    def __repr__(self):
        return repr(ButtonControls.info)

    def __str__(self):
        return str(ButtonControls.info)


class Impression(object):
    """
    Creates an object view of the Impression parameters, such as Advertisement
    Slot ID (e.g., slotImpression), Advertisement IDs (e.g., Quartiles), and
    3rd-party Tracking Impressions.
    """

    # Map FreeWheel impression terms to terms found in the Adaptive Player log.
    event_table = [
        ('slotImpression', 'AdBreakStartEvent'),
        ('defaultImpression', 'AdStartEvent'),
        ('firstQuartile', 'AdQuartile1Event'),
        ('midPoint', 'AdMidwayEvent'),
        ('thirdQuartile', 'AdQuartile3Event'),
        ('complete', 'AdCompleteEvent'),
        ('slotCompleted', 'AdBreakCompleteEvent'),
    ]

    def __init__(self, **kwargs):
        self.ad_id = None  # Advertisement ID
        self.asset_guid = None  # GUID of the asset in which the ad plays
        self.beacon_event = None  # Adaptive Player term
        self.beacon_type = None  # e.g., slot, quartile, tracking
        self.creativeId = None  # Id of the ad media
        self.creativeRenditionId = None
        self.current_time = None  # Time the impression actually fired
        self.duration = None  # Duration of the impression's Ad
        self.fire_time = None  # When the impression should have fired
        self.impression = None  # FreeWheel term (e.g., defaultImpression)
        self.is_valid = None  # Tracks if the impression is valid or not
        self.logline = None  # Log entry from the player.log
        self.new_logging_style = False
        self.pk = None  # primary key for the impression
        self.pod_id = None  # Identifies which Ads a response belongs to
        self.replicaId = None
        self.response_code = None  # HTTP response
        self.slot_id = None  # Id of the ad opportunity
        self.source = None  # The origin of the log entry
        self.tech_type = None  # Server-side (sm3) or client-side ad stitching
        self.time_position_class = None  # e.g., pre-roll, mid-roll, post-roll
        self.time_position = None  # Slot's time position
        self.tracking_direction = None  # e.g., sent or received
        self.tracking_num = None  # Index of the tracking impression
        self.url = None  # The beacon's url
        self.utc = None
        self.__dict__.update((key, value) for key, value in kwargs.items())

    def display_params(self):
        """ Pretty print the object to make it easier for readability. """
        print(self)

    def log_params(self):
        """ Display the object attributes in the log. """
        if logging.getLogger().isEnabledFor(logging.DEBUG):
            logging.debug(self)

    def identify_beacon_event_type(self):
        """Identify the beacon event type. """
        if self.beacon_type:
            return
        elif 'slot' in self.impression:
            self.beacon_type = 'slot'
        else:
            self.beacon_type = 'quartile'

    def set_received_tracking_attributes(self):
        if self.impression is None:
            self.tracking_direction = 'Received'
            self.impression = self.swap_event_term(self.beacon_event)
            self.beacon_type = db_identify_beacon_event_type(self.url)

    def set_sent_tracking_attributes(self):
        if self.impression is None:
            self.tracking_direction = 'Sent'
            self.impression = self.swap_event_term(self.beacon_event)
            self.beacon_type = db_identify_beacon_event_type(self.url)

    def swap_event_term(self, event):
        """
        Replace the Adaptive Player's terminology (i.e., AdStartEvent) with
        FreeWheel's terminology (defaultImpression) or vice versa.
        """
        if event is None:
            return None
        for key, value in self.event_table:
            if value in event:
                return key
            elif key in event:
                return value

    def update_from_sql(self, record):
        """
        Uses the record's values to update values missing from the beacon and
        returns the beacon.
        """
        keys = [
            'ad_id', 'pk', 'pod_id', 'slot_id', 'time_position', 'tracking_num',
            'type', 'url',
        ]
        self.__dict__.update((k, record[k]) for k in keys)
        self.impression = record['event']
        self.beacon_event = self.swap_event_term(self.impression)
        self.is_valid = True

    def __repr__(self):
        return repr(self.__dict__)

    def __str__(self):
        msg = '{0}: {1}={2}\n'
        name = str(self.__class__.__name__)
        keys = sorted(self.__dict__.keys())
        return str(''.join([msg.format(str(name), k, self.__dict__[k]) for k in keys]))


class InternalBeacon(Impression):
    """ Internal Beacons generated by the Adaptive Player. """
    def __init__(self, **kwargs):
        super(InternalBeacon, self).__init__(**kwargs)
        self.source = 'Internal'
        if 'AdaptiveVideoGroup' in self.logline:
            self.impression = self.swap_event_term(self.beacon_event)
        if 'Firing AVG Point' in self.logline:
            self.new_logging_style = True
        self.identify_beacon_event_type()


class ExternalBeacon(Impression):
    """ External Beacons sent to FreeWheel and 3rd-party systems. """
    def __init__(self, **kwargs):
        super(ExternalBeacon, self).__init__(**kwargs)
        self.source = 'External'
        # Original AP log event.
        if 'firing beacon event' in self.logline:
            if self.impression is None and self.slot_id is None and self.time_position is None:
                self.beacon_type = 'tracking'
                self.tracking_direction = 'sent'
                self.impression = self.swap_event_term(self.beacon_event)
        # SM3 - External Tracking Beacons sent to 3rd-party systems
        elif 'Firing External Point' in self.logline:
            self.new_logging_style = True
            self.set_sent_tracking_attributes()
        self.identify_beacon_event_type()


class ResponseBeacon(Impression):
    """ Responses received from FreeWheel and 3rd-party systems. """
    def __init__(self, **kwargs):
        super(ResponseBeacon, self).__init__(**kwargs)
        self.source = 'Response'
        # Original AP log event.
        if 'beacon callback responseCode' in self.logline:
            if self.impression is None and self.slot_id is None and self.time_position is None:
                self.beacon_type = 'tracking'
                self.tracking_direction = 'received'
            self.beacon_event = self.swap_event_term(self.impression)
        # SM3 - External Tracking Beacons received from 3rd-party systems
        elif 'External Point Response' in self.logline:
            self.new_logging_style = True
            self.set_received_tracking_attributes()
        self.identify_beacon_event_type()


class ResponseBeaconAP5x(Impression):
    """
    Adaptive Player 5.x Responses received from FreeWheel and 3rd-party systems.
    The Response message in the AP 5.x version has been stripped of information
    around the Impression.  This class is to accommodate the changes that were
    made to the 5.x Responses where all of the supplemental information (e.g.,
    Ad Break ID, Ad ID, and Event Type) was removed around the response.
    """
    def __init__(self, **kwargs):
        super(ResponseBeaconAP5x, self).__init__(**kwargs)
        self.source = 'Response'
        self.new_logging_style = False
        self.set_received_tracking_attributes()
        self.identify_beacon_event_type()


class SQLiteDB(object):
    """ Database connection context manager. """
    def __init__(self, row=False, filename=None):
        self.row_module = row
        if filename is None:
            filename = 'report_dai_sqlite.db'
        self.path = '/'.join([tempfile.gettempdir(), filename])

    def __enter__(self):
        """ On enter, connect to the database and return a cursor. """
        self._connection = sqlite3.connect(self.path)
        if self.row_module:
            self._connection.row_factory = sqlite3.Row
        self._cursor = self._connection.cursor()
        return self

    def __exit__(self, exception_type, exception_value, traceback):
        """ On exit, commit the transaction and close. """
        if isinstance(exception_value, Exception):
            self.connection.rollback()
        else:
            self.connection.commit()
        self.connection.close()

    @property
    def connection(self):
        return self._connection

    @property
    def cursor(self):
        return self._cursor

    def commit(self):
        self.connection.commit()

    @property
    def description(self):
        return self.cursor.description

    def execute(self, sql, params=None):
        self.cursor.execute(sql, params or ())
        return self

    def executemany(self, sql, params=None):
        self.cursor.executemany(sql, params or ())
        return self

    def executescript(self, sql_script):
        self.cursor.executescript(sql_script)

    def fetchall(self):
        return self.cursor.fetchall()

    def fetchone(self):
        return self.cursor.fetchone()

    @property
    def lastrowid(self):
        return self.cursor.lastrowid

    @property
    def rowcount(self):
        return self.cursor.rowcount

    def row_factory(self):
        """ Enables row factory to access values via column name. """
        self._connection.row_factory = sqlite3.Row
        self._cursor = self._connection.cursor()

    def query(self, sql, params=None):
        self.cursor.execute(sql, params or ())
        return self.fetchall()

    def query_w_row_factory(self, sql, params=None):
        self.row_factory()
        self.cursor.execute(sql, params or ())
        return self.fetchall()

    def delete_database_file(self):
        if os.path.isfile(self.path):
            os.remove(self.path)

    @staticmethod
    def dict_from_row(row):
        """ Convert a sqlite3.Row to a dict. """
        return dict(zip(row.keys(), row))


class SQLQueryStatements(object):
    """ These SQL queries are used for the newer style AP log formats. """
    def __new__(cls, event=None, source=None):
        """
        Internal: generated by the AP; can't be validated against the XML
        External: events sent to FreeWheel and 3rd parties.
        Response: acknowledgements received from FreeWheel and 3rd parties.
        """
        dispatch = {
            'slot': {
                'Internal': cls.slot_internal(),
                'External': cls.slot_external(),
                'Response': cls.slot_response(),
            },
            'quartile': {
                'Internal': cls.quartile_internal(),
                'External': cls.quartile_external(),
                'Response': cls.quartile_response(),
            },
            'tracking': {
                'Internal': cls.tracking_internal(),
                'External': cls.tracking_external(),
                'Response': cls.tracking_response(),
            },
        }
        query = dispatch.get(event, '').get(source, '')
        return ' '.join(query.split())

    @classmethod
    def slot_internal(cls):
        return '''
            SELECT * FROM Impressions
            WHERE pod_id = {pod_id} 
              AND slot_id = '{slot_id}' 
              AND event = '{impression}' 
              AND sent is NULL 
         ORDER BY pk LIMIT 1; '''

    @classmethod
    def slot_external(cls):
        return '''
           SELECT * FROM Impressions 
            WHERE pod_id = {pod_id} 
              AND slot_id = '{slot_id}' 
              AND event = '{impression}' 
              AND type = 'slot' 
              AND url = '{url}' 
              AND sent is NULL;'''

    @classmethod
    def slot_response(cls):
        return '''
            SELECT * FROM Impressions 
             WHERE pod_id = {pod_id}
               AND slot_id = '{slot_id}' 
               AND event = '{impression}' 
               AND type = 'slot' 
               AND url = '{url}' 
               AND received is NULL;'''

    @classmethod
    def quartile_internal(cls):
        return '''
            SELECT * FROM Impressions 
             WHERE pod_id={pod_id} 
               AND slot_id='{slot_id}' 
               AND ad_id='{ad_id}' 
               AND type='quartile' 
               AND event='{impression}' 
          ORDER BY pk DESC LIMIT 1;'''

    @classmethod
    def quartile_external(cls):
        return '''
            SELECT * FROM Impressions 
             WHERE pod_id={pod_id} 
               AND slot_id='{slot_id}' 
               AND ad_id='{ad_id}' 
               AND type='quartile' 
               AND event='{impression}' 
               AND url='{url}';'''

    @classmethod
    def quartile_response(cls):
        return '''
            SELECT * FROM Impressions 
             WHERE pod_id={pod_id} 
               AND slot_id='{slot_id}' 
               AND ad_id='{ad_id}' 
               AND type='quartile' 
               AND event='{impression}' 
               AND url='{url}';'''

    @classmethod
    def tracking_internal(cls):
        pass

    @classmethod
    def tracking_external(cls):
        return ''' 
            SELECT * FROM Impressions 
            WHERE pod_id={pod_id} 
            AND slot_id='{slot_id}' 
            AND ad_id='{ad_id}' 
            AND type='tracking' 
            AND event='{impression}' 
            AND url='{url}';'''

    @classmethod
    def tracking_response(cls):
        return '''
            SELECT * FROM Impressions 
            WHERE pod_id={pod_id} 
            AND slot_id='{slot_id}' 
            AND ad_id='{ad_id}' 
            AND url='{url}';'''


class SQLQueryStatementsFormer(object):
    """
    These SQL queries are for the older style AP log formats. We should be
    able to remove these once all of the devices are using the newer style.
    """
    def __new__(cls, event=None, source=None):
        """
        Internal: generated by the AP; can't be validated against the XML
        External: events sent to FreeWheel and 3rd parties.
        Response: acknowledgements received from FreeWheel and 3rd parties.
        """
        dispatch = {
            'slot': {
                'Internal': cls.slot_internal(),
                'External': cls.slot_external(),
                'Response': cls.slot_response(),
            },
            'quartile': {
                'Internal': cls.quartile_internal(),
                'External': cls.quartile_external(),
                'Response': cls.quartile_response(),
            },
            'tracking': {
                'Internal': cls.tracking_internal(),
                'External': cls.tracking_external(),
                'Response': cls.tracking_response(),
            },
        }
        query = dispatch.get(event, '').get(source, '')
        return ' '.join(query.split())

    @classmethod
    def slot_internal(cls):
        return '''
            SELECT * FROM Impressions 
             WHERE pod_id={pod_id} 
               AND slot_id={slot_id} 
               AND event='{impression}' 
               AND sent is NULL 
          ORDER BY pk DESC LIMIT 1; '''

    @classmethod
    def slot_external(cls):
        return '''
            SELECT * FROM Impressions 
             WHERE pod_id={pod_id} 
               AND time_position={time_position} 
               AND type='{beacon_type}' 
               AND event='{impression}' 
               AND url='{url}'
               AND sent is NULL;'''

    @classmethod
    def slot_response(cls):
        return '''
            SELECT * FROM Impressions 
             WHERE pod_id={pod_id} 
              AND time_position={time_position} 
              AND type='{beacon_type}' 
              AND event='{impression}' 
              AND url='{url}'; '''

    @classmethod
    def quartile_internal(cls):
        return ''' 
            SELECT * FROM Impressions 
             WHERE pod_id={pod_id} 
               AND slot_id='{slot_id}' 
               AND ad_id='{ad_id}' 
               AND event='{impression}' 
               AND type='quartile'
          ORDER BY pk DESC LIMIT 1; '''

    @classmethod
    def quartile_external(cls):
        return '''
            SELECT * FROM Impressions 
             WHERE pod_id={pod_id} 
               AND time_position={time_position} 
               AND ad_id='{ad_id}' 
               AND type='{beacon_type}' 
               AND event='{impression}'
               AND url='{url}'; '''

    @classmethod
    def quartile_response(cls):
        return '''
            SELECT * FROM Impressions 
             WHERE pod_id={pod_id} 
               AND time_position={time_position} 
               AND ad_id='{ad_id}' 
               AND type='{beacon_type}' 
               AND event='{impression}'
               AND url='{url}'; '''

    @classmethod
    def tracking_internal(cls):
        pass

    @classmethod
    def tracking_external(cls):
        return ''' 
            SELECT * FROM Impressions 
             WHERE pod_id={pod_id} 
               AND type='{beacon_type}' 
               AND event='{impression}' 
               AND url='{url}'; '''

    @classmethod
    def tracking_response(cls):
        return '''
            SELECT * FROM Impressions 
             WHERE pod_id={pod_id} 
               AND url='{url}' 
               AND received is NULL; '''


class SQLStatements(object):

    @property
    def sql_catalog_request(self):
        """ Inserts information about the Ad Request. """
        return '''
            INSERT INTO Requests
            VALUES (
                :pod_id, :adapt_url, :ads_url, :afid, :asnw, :caid, 
                :comscore_device, :comscore_did_x, :comscore_impl_type, 
                :comscore_platform, :cpsq, :csid, :envp, :feature, :flag, 
                :_fw_nielsen_app_id, :_fw_vcid2, :fw_vcid, :maxd, :metr, 
                :mind, :mode, :module, :nielsen_dev_group, :nielsen_os_group, 
                :nielsen_os_version, :nw, :prof, :ptgt, :pvrn, :resp, 
                :roku_rida, :sfid, :slau, :slid, :ssnw, :ssto, :tpcl, :tpos, 
                :vdur, :vip, :vprn); '''

    @property
    def sql_catalog_qvt(self):
        """ Inserts information about the QVT. """
        return '''
            INSERT OR IGNORE INTO QVTs
            VALUES (
                :cue_point_number, :afid, :asnw, :caid, :channel, :nw, :ssnw, 
                :prof, :flag, :emcr, :esvt, :exvt, :qtcb, :slcb, 
                :type, :anchor_time, :allow_seeking, :method, :start_offset, 
                :stop_offset, :playback_delay, :start_offset_with_delay, 
                :stop_offset_with_delay, :duration, :maxd, :mind, :tpos, 
                :title, :ads_service_url, :adapt_url, :ads_url, :url, 
                :content_type, :log, :csid); '''

    @property
    def sql_insert_creative(self):
        """ Inserts Creatives from the Ad Response. """
        return '''
            INSERT INTO Creatives (
                pod_id, ad_adId, ad_adUnit, creative_adUnit, creative_baseUnit, 
                creative_creativeId, creative_duration, 
                creativeRendition_adReplicaId, creativeRendition_creativeApi, 
                creativeRendition_creativeRenditionId, creativeRendition_height, 
                creativeRendition_preference, creativeRendition_width, 
                asset_bytes, asset_contentType, asset_mimeType, asset_url
                )
            VALUES (
                :pod_id, :ad_adId, :ad_adUnit, :creative_adUnit, 
                :creative_baseUnit, :creative_creativeId, :creative_duration, 
                :creativeRendition_adReplicaId, :creativeRendition_creativeApi,
                :creativeRendition_creativeRenditionId, 
                :creativeRendition_height, :creativeRendition_preference,
                :creativeRendition_width, :asset_bytes, :asset_contentType, 
                :asset_mimeType, :asset_url
                );'''

    @property
    def sql_insert_impression_event(self):
        """ Inserts Impression information. """
        return '''
            INSERT INTO Impressions 
                (pod_id, slot_id, time_position, ad_id, type, event, url, 
                tracking_num)
            VALUES 
                (:pod_id, :slot_id, :time_position, :ad_id, :type, :event, :url, 
                :tracking_num); '''

    @property
    def sql_insert_request_into_adpods_table(self):
        return "INSERT INTO AdPods (request) VALUES (?);"

    @property
    def sql_insert_blank_qvt_record(self):
        """ Inserts a blank QVT record for a given Slot ID. """
        return "INSERT INTO QVTs (cue_point_number) VALUES (?);"

    @property
    def sql_insert_report(self):
        """ Inserts the DAI Report. """
        return '''
            INSERT into Reports 
                (pod_id, slot_id, content, status)
            VALUES 
                (?, ?, ?, ?);'''

    @property
    def sql_insert_response_without_pod_id(self):
        """ Inserts the Ad Response and returns the id of the record. """
        return "INSERT INTO AdPods (response) VALUES (?);"

    @property
    def sql_insert_unmatched_impression(self):
        """ Inserts the Impression's log into the Unmatched table. """
        return "INSERT INTO Unmatched (log, pk) VALUES (?, ?);"

    @property
    def sql_insert_validated_requests(self):
        """ Inserts Ad Request parameters into the database. """
        return '''
            INSERT INTO Validated_Requests
                (pod_id, slot_id, param, expected, found, state, status)
            VALUES
                (:pod_id, :slot_id, :param, :expected, :found, :state, 
                :status); '''

    @property
    def sql_query_impressions_actual_firing_time(self):
        """ Return when the Impressions were sent. """
        return '''
            SELECT pk, event, actual_firing_time 
              FROM Impressions
             WHERE actual_firing_time > 0;'''

    @property
    def sql_query_empty_quartile_placement_status(self):
        """ Returns Impressions where the quartile placement msg is empty. """
        return '''
            SELECT pk, event, valid_quartile_placement_msg, 
                   valid_quartile_placement_status
              FROM Impressions
             WHERE (valid_quartile_placement_status is NULL
                OR valid_quartile_placement_status = '');'''

    @property
    def sql_query_active_ad_pod_id(self):
        """ Return the Active Pod ID. """
        return "SELECT MAX(pod_id) FROM AdPods;"

    @property
    def sql_query_ad_pod_records(self):
        """ Returns the Dynamic Ad Information for each Ad Pod. """
        return '''
            SELECT AdPods.pod_id, Requests.slid, 
                   AdPods.request, AdPods.response
              FROM Requests
        INNER JOIN AdPods 
                ON Requests.pod_id = AdPods.pod_id
             UNION
            SELECT AdPods.pod_id, Impressions.slot_id, 
                   AdPods.request, AdPods.response
              FROM Impressions
        INNER JOIN AdPods 
                ON Impressions.pod_id = AdPods.pod_id
          ORDER BY AdPods.pod_id;'''

    @property
    def sql_query_ad_request_timestamp(self):
        return '''
            SELECT substr(request, 1, 19)
              FROM AdPods
             WHERE request
              LIKE '%slid={}%';'''

    @property
    def sql_query_creatives(self):
        """ Returns the Ad ID and URL for a given Pod ID and Slot ID. """
        # TODO: Need to verify this statement works as expected.
        return '''
            SELECT c.ad_adId AS 'Advertisement ID', 
                   c.asset_url as 'Asset URL' 
              FROM Creatives c 
         LEFT JOIN (SELECT pk, pod_id, slot_id, ad_id 
                      FROM Impressions 
                     WHERE type='quartile' 
                       AND event='defaultImpression') i 
             WHERE c.ad_adId = i.ad_id 
               AND c.pod_id = i.pod_id 
               AND i.pod_id = ? 
               AND i.slot_id = ? 
               ORDER BY i.pk;'''

    @property
    def sql_query_html_report(self):
        """ Returns the HTML DAI Validation Report. """
        return '''
            SELECT pod_id, slot_id, content, status 
                  FROM Reports 
                 WHERE slot_id = ? 
                    OR slot_id is NOT NULL;'''

    @property
    def sql_query_impression_sent_received_logs(self):
        """ Return the Sent and Received logs for all Impressions. """
        return "SELECT pk, sent_log, received_log FROM Impressions;"

    @property
    def sql_query_incomplete_pod_id(self):
        """
        Returns the Ad Pod ID where we've previously seen the Ad Request that
        the Adaptive Player submitted to FreeWheel, but have not yet processed
        FreeWheel's Ad Response.
        """
        return '''
            SELECT MAX(pod_id)
              FROM AdPods 
             WHERE request IS NOT NULL 
               AND response IS NULL; '''

    @property
    def sql_query_impressions(self):
        """ Returns Impressions for the given Pod ID and Slot ID. """
        return '''
            SELECT * 
              FROM Impressions 
             WHERE pod_id = ?
               AND slot_id = ?;'''

    @property
    def sql_query_slot_complete(self):
        """ Returns the timestamp of when the Slot Impression should be complete. """
        return '''
            SELECT SUM(expected_firing_time + duration)
              FROM Impressions
             WHERE pod_id = ?
               AND slot_id = ?
               AND type = 'slot'
               AND event = 'slotImpression'; '''

    @property
    def sql_query_impressions_http_status(self):
        return "SELECT pk, http_status FROM Impressions;"

    @property
    def sql_query_quartile_tracking_impressions(self):
        """ Returns the Quartile and Tracking Impressions. """
        return '''
            SELECT pod_id, slot_id, ad_id, type, event, sent, received 
              FROM Impressions
             WHERE (type = 'quartile' OR type = 'tracking')
               AND pod_id = ?
               AND slot_id = ?
          ORDER BY pk;'''

    @property
    def sql_query_qvt_records(self):
        """ Returns the QVT record for a given Slot ID. """
        return "SELECT * FROM QVTs WHERE cue_point_number = ?;"

    @property
    def sql_query_slot_impression_duration(self):
        """ Returns the duration of a specific slot impression. """
        return '''
            SELECT duration
              FROM Impressions
             WHERE slot_id = ?
               AND event = 'slotImpression'; '''

    @property
    def sql_query_validated_requests(self):
        """ Returns validated Request params for a given Pod ID and Slot ID. """
        return '''
            SELECT * FROM Validated_Requests 
             WHERE pod_id = ?
               AND slot_id = ?
          ORDER BY pk;'''

    @property
    def sql_query_unmatched_impressions_with_range(self):
        return '''
                SELECT log 
                  FROM Unmatched
                 WHERE actual_firing_time 
               BETWEEN ? AND ?
                    OR actual_firing_time IS NOT NULL;'''

    @property
    def sql_update_beacon_event_firing_order(self):
        return '''
            UPDATE Impressions 
               SET beacon_event_firing_order_status = ? 
             WHERE pk = ?;'''

    @property
    def sql_update_http_status(self):
        return '''
            UPDATE Impressions 
               SET http_status_msg = ? 
             WHERE pk = ?;'''

    @property
    def sql_update_impressions_with_ad_info(self):
        """ Updates Impression records with Creative Advertisement info. """
        return '''
            UPDATE Impressions 
               SET creative_url = :asset_url, 
                   duration = :creative_duration 
             WHERE ad_id = :ad_adId 
               AND type = 'quartile'; '''

    @property
    def sql_update_impression_received_status(self):
        """
        Update the 'received' status and increments a counter for the entry
        in the database that corresponds to the primary key.
        """
        return '''
            UPDATE Impressions 
               SET received = 'True', 
                   received_counter = received_counter + 1, 
                   received_log = ?,
                   http_status = ? 
             WHERE pk = ?; '''

    @property
    def sql_update_impression_sent_status(self):
        """
        Update the 'sent' status and increments a counter for the entry
        in the database that corresponds to the primary key.
        """
        return '''
            UPDATE Impressions 
               SET sent = 'True', 
                   sent_counter = sent_counter + 1, 
                   sent_log = ? 
             WHERE pk = ?; '''

    @property
    def sql_update_impression_valid_quartile_placement(self):
        return '''
            UPDATE Impressions 
               SET valid_quartile_placement_status = ?,
                   valid_quartile_placement_msg = ?
             WHERE pk = ?;'''

    @property
    def sql_update_internal_log(self):
        """ Updates the 'Internal' log corresponding to this primary key. """
        return " UPDATE Impressions SET internal_log = ? WHERE pk = ?;"

    @property
    def sql_update_response_with_pod_id(self):
        """ Updates the Ad Response for a given Ad Pod ID. """
        return "UPDATE AdPods SET response = ? WHERE pod_id = ?;"


class DatabaseOps(SQLiteDB, SQLStatements):
    def __init__(self, row=False):
        super(DatabaseOps, self).__init__(row=row)

    def catalog_request(self, params):
        """ Creates an Ad Request record. """
        self.executemany(self.sql_catalog_request, params)

    def catalog_qvt(self, params):
        """ Creates a QVT record. """
        self.executemany(self.sql_catalog_qvt, params)

    def fetch_active_pod_id(self):
        """ Return the Active Commerical Break Pod ID. """
        pod_id = self.execute(self.sql_query_active_ad_pod_id).fetchone()
        if pod_id:
            return pod_id[0]

    def fetch_ad_creatives(self, pod_id, slot_id):
        """ Returns the Ad ID and URL for a given Pod and Slot ID. """
        return self.query(self.sql_query_creatives, (pod_id, slot_id))

    def fetch_ad_pod_records(self):
        """ Returns the Dynamic Ad Information for each Ad Pod. """
        return self.query(self.sql_query_ad_pod_records)

    def fetch_ad_request_timestamp(self, slot_id):
        """ Returns the timestamp of when the Ad Request was sent. """
        sql = self.sql_query_ad_request_timestamp.format(slot_id)
        return self.execute(sql).fetchone()

    def fetch_html_report(self, slot_id):
        """ Returns the HTML DAI Validation Report. """
        return self.query(self.sql_query_html_report, (slot_id,))

    def fetch_impressions(self, pod_id, slot_id):
        """ Returns the Slot, Quartile, and Tracking Impressions. """
        return self.query(self.sql_query_impressions, (pod_id, slot_id))

    def fetch_impressions_http_status(self):
        return self.query(self.sql_query_impressions_http_status)

    def fetch_impressions_actual_firing_time(self):
        """ Returns when each Impression was sent.. """
        return self.query(self.sql_query_impressions_actual_firing_time)

    def fetch_empty_quartile_placements(self):
        return self.query(self.sql_query_empty_quartile_placement_status)

    def fetch_impressions_sent_received_logs(self):
        """ Returns the Slot, Quartile, and Tracking Impressions. """
        return self.query(self.sql_query_impression_sent_received_logs)

    def fetch_incomplete_pod_record(self):
        """
        Retrieves the Ad Pod ID where we've previously seen the Ad Request that
        the Adaptive Player submitted to FreeWheel, but have not yet processed
        FreeWheel's Ad Response.
        """
        pod_id = self.execute(self.sql_query_incomplete_pod_id).fetchone()
        if pod_id:
            return pod_id[0]

    def fetch_quartile_tracking_impressions(self, pod_id, slot_id):
        """ Returns the Quartile and Tracking Impressions. """
        self.row_factory()
        sql = self.sql_query_quartile_tracking_impressions
        rows = self.query(sql, (pod_id, slot_id))
        if rows:
            return [self.dict_from_row(row) for row in rows]

    def fetch_qvt_record(self, slot_id):
        """
        Returns QVT for a given Slot ID or, if the QVT doesn't exist, a new QVT
        record is created with the specific Slot ID and all of the QVT params
        are flagged as 'Missing'.
        """
        self.row_factory()
        row = self.execute(self.sql_query_qvt_records, (slot_id,)).fetchone()
        if row:
            return self.dict_from_row(row)
        else:
            self.insert_blank_qvt_record(slot_id)
            return self.fetch_qvt_record(slot_id)

    def fetch_slot_impression_duration(self, slot_id):
        """ Returns the duration of the Slot Impression in seconds. """
        sql = self.sql_query_slot_impression_duration
        duration = self.execute(sql, (slot_id,)).fetchone()
        if duration:
            return duration[0]

    def fetch_slot_end_time(self, pod_id, slot_id):
        """ Returns a timestamp for when the Slot Impression is finished. """
        sql = self.sql_query_slot_complete
        return self.execute(sql, (pod_id, slot_id)).fetchone()

    def fetch_unmatched_impressions_with_range(self, start_time, end_time):
        """ Returns records found between this time frame. """
        sql = self.sql_query_unmatched_impressions_with_range
        return self.query(sql, (start_time, end_time))

    def fetch_validated_url_params(self, pod_id, slot_id):
        """ Returns validated Request params for a given Pod ID and Slot ID. """
        self.row_factory()
        sql = self.sql_query_validated_requests
        rows = self.query(sql, (pod_id, slot_id))
        if rows:
            return [self.dict_from_row(row) for row in rows]

    def insert_blank_qvt_record(self, slot_id):
        """ Inserts an empty QVT record. """
        self.execute(self.sql_insert_blank_qvt_record, (slot_id,))

    def insert_creative(self, dct):
        """ Inserts Creatives from the Ad Response. """
        self.execute(self.sql_insert_creative, dct)

    def insert_impression(self, dct):
        """ Inserts the Impression event from the Ad Response. """
        self.execute(self.sql_insert_impression_event, dct)

    def insert_report(self, pod_id, slot_id, content, status):
        """ Inserts the DAI Report. """
        self.execute(self.sql_insert_report, (pod_id, slot_id, content, status))
        return self.lastrowid

    def insert_request(self, request):
        """ Inserts the Ad Request and returns the id of the record. """
        self.execute(self.sql_insert_request_into_adpods_table, (request,))
        return self.lastrowid

    def insert_response(self, response_str):
        """
        Determine if the last known Ad Pod record is incomplete. Meaning,
        we've previously encountered an Ad Request, but there is currently no
        corresponding Ad Response. If the incomplete record exists, then update
        the record using this Ad Response to make the record complete.
        Otherwise, insert this Ad Response as a new record because we've
        somehow missed the previous Ad Request.
        """
        pod_id = self.fetch_incomplete_pod_record()
        if pod_id:
            self.update_response_having_pod_id(pod_id, response_str)
        else:
            pod_id = self.insert_response_without_pod_id(response_str)
        return pod_id

    def insert_response_without_pod_id(self, response_str):
        """ Inserts a new Ad Response. """
        self.execute(self.sql_insert_response_without_pod_id, (response_str,))
        return self.lastrowid

    def insert_unmatched_impression(self, pk, log):
        """ Inserts the Impression's log into the Unmatched table. """
        self.execute(self.sql_insert_unmatched_impression, (log, pk))

    def insert_validated_requests(self, params):
        """ Inserts Ad Request parameters. """
        self.executemany(self.sql_insert_validated_requests, params)

    def update_beacon_event_firing_order(self, pk, status):
        """ Updates the status of the Impression's firing order. """
        self.execute(self.sql_update_beacon_event_firing_order, (status, pk))

    def update_impressions_valid_quartile_placement(self, pk, msg, status):
        sql = self.sql_update_impression_valid_quartile_placement
        return self.query(sql, (status, msg, pk))

    def update_impressions_with_ad_info(self, dct):
        self.execute(self.sql_update_impressions_with_ad_info, dct)

    def update_internal_log(self, pk, log):
        self.execute(self.sql_update_internal_log, (log, pk))

    def update_received_impression(self, pk, log, resp_code):
        sql = self.sql_update_impression_received_status
        self.execute(sql, (log, resp_code, pk))

    def update_response_having_pod_id(self, pod_id, response_str):
        sql = self.sql_update_response_with_pod_id
        self.execute(sql, (response_str, pod_id))

    def update_sent_impression(self, pk, log):
        self.execute(self.sql_update_impression_sent_status, (log, pk))

    def update_http_status(self, pk, status):
        self.execute(self.sql_update_http_status, (status, pk))


class ParseAdRequest:
    """
    Creates an object view of the Adaptive Player's Ad Request.
    """
    counter = 0
    important = [
        'adapt_url', 'ads_url', 'flag', 'nw', 'csid', 'caid', 'asnw', 'ssnw',
        'prof', 'afid', 'fw_vcid', '_fw_vcid2', 'slid', 'tpcl', 'tpos', 'maxd',
        'mind', 'cpsq', 'ssto',
    ]
    non_important = [
        '_fw_nielsen_app_id', 'comscore_device', 'comscore_did_x',
        'comscore_impl_type', 'comscore_platform', 'envp', 'feature', 'module',
        'metr', 'mode', 'nielsen_dev_group', 'nielsen_os_group',
        'nielsen_os_version', 'ptgt', 'pvrn', 'resp', 'roku_rida', 'sfid',
        'slau', 'vdur', 'vip', 'vprn',
    ]

    def __init__(self, request=None):
        self.missing = 'Missing'
        self.request = request
        self.expected_params = self.important + self.non_important
        self.timestamp = self.missing
        self.url = self.missing
        self.important_params = OrderedDefaultDict()
        self.non_important_params = OrderedDefaultDict()
        self.params = None
        self._parsed_obj = None
        self.parsed_requests = []
        ParseAdRequest.counter += 1

        if self.request:
            self._valid(self.request)
        else:
            self._invalid()

    @property
    def request(self):
        return self.__request

    @request.setter
    def request(self, request):
        """ Determines if the content of the string meets our criteria. """
        if request is None:
            self.__request = ''
        elif 'adapt.movetv.com' in request:
            self.__request = request
        else:
            self.__request = ''

    @request.deleter
    def request(self):
        del self.request

    @classmethod
    def from_url(cls, url):
        cls(url)

    def _invalid(self):
        """ Parses the Ad Request URL to obtain its parameters. """
        self.params = {}
        self.params.update((key, self.missing) for key in self.expected_params)
        self.parsed_requests = [self.params.copy()]

    def _loose_ordering(self):
        """ Stores the Ad Request parameters and disregard the parsing sequence. """
        self.params.update(
            (k, v) for k, v in parse_qs(self._parsed_obj.query).items())

    def _identify_missing_params(self):
        """ Identifies Ad Request parameters missing from the Request. """
        self.params.update(
            (k, self.missing) for k in self.expected_params if k not in self.params)

    def _identify_multiple_slot_ids(self):
        """
        Generates a list of Ad Requests whenever the request includes multiple
        Ad Breaks. Usually an Ad Request is for a single Ad Break or Slot ID,
        however, an Ad Request may ask for multiple Ad Breaks. When this occurs,
        parse the query params in a way that makes these multiple Slot ID
        requests appear as individual Ad Requests. This should make it easier
        to validate the Ad Request for a specific Slot ID.
        """
        dct = OrderedDefaultDict()
        for index in range(len(self.params['slid'])):
            for key in self.params:
                if isinstance(self.params[key], list):
                    if len(self.params[key]) > 1:
                        dct[key] = self.params[key][index]
                    elif len(self.params[key]) == 1:
                        dct[key] = self.params[key][0]
                else:
                    dct[key] = self.params[key]
            self.parsed_requests.append(dct.copy())

    def _rank_parameters(self):
        """ Sorts the Ad Request parameters by their importance. """
        for key, value in self.params.items():
            if key in ParseAdRequest.important:
                self.important_params[key] = value
            elif key in ParseAdRequest.non_important and self.missing not in value:
                self.non_important_params[key] = value

    def _strict_ordering(self):
        """
        Stores the Ad Request query parameters in the exact sequence in which
        they appear in the Ad Request URL.
        """
        self.params = OrderedDefaultDict()
        re_ads_service_urls = r'^(?P<adapt_url>http://.+)(?P<ads_url>http.+g/1)'
        m = re.match(re_ads_service_urls, self.url)
        if m:
            self.params['adapt_url'] = [m.group('adapt_url')]
            self.params['ads_url'] = [m.group('ads_url')]
        for key, value in parse_qsl(self._parsed_obj.query):
            if key in self.params:
                self.params[key].append(value)
            else:
                self.params[key] = [value]
        self.params['flag'] = [self.params['flag'][0].strip()]

    def _valid(self, request):
        """ Parses the Ad Request URL to obtain its parameters. """
        re_datetime = r'^(?P<date>\d{4}[/.-]\d{2}[/.-]\d{2}\s\d{2}:\d{2}:\d{2})'
        re_url = r'^.* (?P<url>http.*$)'
        if re.search(re_url, request):
            self.timestamp = re.match(re_datetime, request).group(1)
            self.url = re.match(re_url, request).group(1)
            self._parsed_obj = urlparse(self.url)
            self._strict_ordering()
            self._rank_parameters()
            self._identify_missing_params()
            self._identify_multiple_slot_ids()
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

    def insert_pod_id(self, index):
        """ Inserts the Pod ID into each Ad Request. """
        for request in self.parsed_requests:
            request['pod_id'] = index


class ParseQVT:
    """
    Parses QVT for Dynamic Advertisement related parameters from the Adaptive
    Player log or a string containing the QVT.
    """
    counter = 0

    def __init__(self, string=None):
        self.string = string
        self.missing = 'Missing'
        self.dct = {}
        self.records = []
        ParseQVT.counter += 1

        try:
            # Parse the string for the JSON object (ie. QVT)
            self.json_dict = self.deserialize(self.search(string))
            if self.json_dict:
                # Store the required sections.
                self.playback_info = self.json_dict.get('playback_info')
                self.ad_info = self.playback_info.get('ad_info')
                self.ad_breaks = self.ad_info.get('ad_breaks', {})
                self.fw_info = self.ad_info.get('fw_capabilities', {})
                self.linear_info = self.playback_info.get('linear_info', {})
                # Parse for QVT info.
                self.dct.update(self.get_qvt_info())
                self.dct.update(self.get_ad_properties())
                self.dct.update(self.get_freewheel_capabilities())
                self.dct.update(self.get_linear_properties())
                self.dct.update(self.get_adapt_fw_urls())
                self.parse_ad_breaks()
            else:
                raise ValueError('missing json object')
        except Exception as ex:
            logging.debug('ERROR Problem encountered while processing the QVT.')
            logging.debug(format_exception(ex))
            raise

    @property
    def string(self):
        return self.__string

    @string.setter
    def string(self, string):
        """ Determine if the content of the string meets our criteria. """
        if string is None:
            raise TypeError('Argument must be a string containing QVT')
        elif 'ad_info' in string and 'ad_breaks' in string:
            self.__string = string
        else:
            raise ValueError('Argument missing Ad Info and Ad Break sections')

    @string.deleter
    def string(self):
        del self.string

    @staticmethod
    def search(string):
        """
        Scan through the string looking for a match to the pattern, returning
        the JSON string (i.e, QVT), or None if no match was found.
        """
        re_json = r'^[^\{]*(?P<qvt>\{.*ad_info":.*"ad_breaks".+\})[^}]*$'
        try:
            m = re.search(re_json, string)
            if m:
                return m.group('qvt')
        except Exception as ex:
            msg = 'ERROR Problem encountered while extracting QVT object.'
            logging.debug(msg)
            logging.debug(format_exception(ex))
            raise

    @staticmethod
    def deserialize(json_str):
        try:
            if json_str:
                return json.loads(json_str)
        except ValueError:
            return None

    @staticmethod
    def addition(a, b):
        """ Returns the sum. """
        try:
            return float(a) + float(b)
        except ValueError:
            return 0

    @staticmethod
    def subtraction(a, b):
        """ Returns the difference. """
        try:
            return float(a) - float(b)
        except ValueError:
            return 0

    def compute_slot_duration(self, stop_offset, start_offset):
        """ Returns the duration of the Slot Impression in seconds. """
        return str(int(round(self.subtraction(stop_offset, start_offset))))

    def compute_time_position(self, start_offset, anchor_time):
        """ Returns the time position of the Slot Impression. """
        return str(format(self.subtraction(start_offset, anchor_time), '.3f'))

    def compute_start_with_delay(self, start_offset, playback_delay):
        """ Returns the start time plus the playback_delay. """
        return self.addition(start_offset, playback_delay)

    def compute_stop_with_delay(self, stop_offset, playback_delay):
        """ Returns the stop time plus the playback_delay. """
        return self.addition(stop_offset, playback_delay)

    def get_qvt_info(self):
        return {
            'csid': self.get_channel_service_id(),
            'title': self.get_show_title(),
            'log': self.string,
            'url': self.get_qvt_url(),
            'playback_delay': self.get_playback_delay(),
        }

    def get_ad_break(self, data):
        anchor_time = self.get_anchor_time()
        delay = self.get_playback_delay()
        start = data.get('start_offset', 0)
        stop = data.get('stop_offset', 0)

        return {
            'cue_point_number': data.get('cue_point_number', self.missing),
            'method': data.get('method', self.missing),
            'start_offset': start,
            'stop_offset': stop,
            'type': data.get('type', self.missing),
            'duration': self.compute_slot_duration(stop, start),
            'mind': self.compute_slot_duration(stop, start),
            'maxd': self.compute_slot_duration(stop, start),
            'start_offset_with_delay': self.compute_start_with_delay(start, delay),
            'stop_offset_with_delay': self.compute_stop_with_delay(stop, delay),
            'tpos': self.compute_time_position(start, anchor_time),
        }

    def get_ad_properties(self):
        return {
            'ads_service_url': self.get_ads_service_url(),
            'afid': self.get_fallback_asset_id(),
            'asnw': self.get_programmer_network_id(),
            'caid': self.get_programmer_asset_id(),
            'channel': self.get_channel_name(),
            'nw': self.get_network_id(),
            'ssnw': self.get_site_section_owner_network_id(),
            'prof': self.get_profile(),
        }

    def get_freewheel_capabilities(self):
        return {
            'emcr': self.get_expected_multiple_creative_renditions(),
            'esvt': self.get_enable_server_vast_translation(),
            'exvt': self.get_record_video_view(),
            'qtcb': self.get_requires_quartile_callback_urls(),
            'slcb': self.get_supports_slot_callbacks(),
            'flag': self.get_flags(),
        }

    def get_linear_properties(self):
        return {
            'anchor_time': self.get_anchor_time(),
            'allow_seeking': self.get_allow_seeking(),
            'content_type': self.get_content_type(),
        }

    def get_playback_delay(self):
        return self.json_dict.get('playback_delay', 0)

    def get_qvt_url(self):
        return self.json_dict.get('self', self.missing)

    def get_show_title(self):
        return self.json_dict['shows'][0]['title']

    # Advertisement properties.
    def get_ads_service_url(self):
        return self.ad_info.get('ads_service_url', self.missing)

    def get_fallback_asset_id(self):
        return self.ad_info.get('fallback_asset_id', self.missing)

    def get_programmer_network_id(self):
        return self.ad_info.get('programmer_network_id', self.missing)

    def get_programmer_asset_id(self):
        return self.ad_info.get('programmer_asset_id', self.missing)

    def get_channel_name(self):
        return self.ad_info.get('channel_name', self.missing)

    def get_network_id(self):
        return self.ad_info.get('network_id', self.missing)

    def get_site_section_owner_network_id(self):
        return self.ad_info.get('network_id', self.missing)

    def get_profile(self):
        if self.missing not in self.ad_info.get('profile', self.missing):
            return self.ad_info.get('profile').join(['', ':sling'])
        else:
            return self.ad_info.get('profile', self.missing)

    # FreeWheel properties.
    def get_expected_multiple_creative_renditions(self):
        return self.fw_info.get('expectedMultipleCreativeRenditions', self.missing)

    def get_enable_server_vast_translation(self):
        return self.fw_info.get('enableServerVastTranslation', self.missing)

    def get_record_video_view(self):
        return self.fw_info.get('recordVideoView', self.missing)

    def get_requires_quartile_callback_urls(self):
        return self.fw_info.get('requiresQuartileCallbackUrls', self.missing)

    def get_supports_slot_callbacks(self):
        return self.fw_info.get('supportsSlotCallbacks', self.missing)

    def get_flags(self):
        flags = ' '.join([
            self.get_record_video_view(),
            self.get_requires_quartile_callback_urls(),
            self.get_expected_multiple_creative_renditions(),
            self.get_supports_slot_callbacks(),
            self.get_enable_server_vast_translation(),
        ])
        return flags + ' sync rste'

    # Linear properties.
    def get_anchor_time(self):
        return self.linear_info.get('anchor_time', '0')

    def get_allow_seeking(self):
        return self.linear_info.get('allow_seeking', self.missing)

    def get_content_type(self):
        if self.linear_info.get('anchor_time', False):
            return 'live'
        else:
            return 'vod'

    def get_channel_service_id(self):
        """ Returns the Channel Service ID. """
        csid = Device.csid()
        channel = self.get_channel_name()
        content = self.get_content_type()
        return '_'.join(['otto', csid, channel, content])

    def get_adapt_fw_urls(self):
        """ Retrieve the Adapt and FreeWheel URLs from Ads Service URL. """
        re_urls = r'^(?P<adapt_url>http://.+)(?P<ads_url>http.*)'
        if self.missing not in self.get_ads_service_url():
            m = re.match(re_urls, self.get_ads_service_url())
            if m:
                return m.groupdict()

    def retrieve_cue_point_number(self, slot_id):
        """ Returns the QVT for a specific Slot ID or Cue Point Number. """
        for record in self.records:
            if slot_id == record['cue_point_number']:
                return record

    def parse_ad_breaks(self):
        """
        Parse and store the key-values from the Ad Break section.
        An Ad Break section may contain one or more commercial breaks.
        """
        for ad_break in self.traverse(self.ad_breaks):
            self.dct.update(self.get_ad_break(ad_break))
            self.records.append(self.dct.copy())

    def traverse(self, obj):
        """ Returns the key-values of the Ad Break section of the QVT. """
        if isinstance(obj, dict):
            return {str(key): self.traverse(value) for key, value in obj.items()}
        elif isinstance(obj, list):
            return [self.traverse(elem) for elem in obj]
        else:
            return obj


class OrderedDefaultDict(OrderedDict):
    def __missing__(self, key):
        val = self[key] = OrderedDefaultDict()
        return val


def process(log_entry):
    # type: (str) -> None
    """
    Determines if the log entry from the Adaptive Player matches any significant
    Dynamic Ad Insertion events like QVT, Ad Request, Ad Response, or Impression
    Events, such as the Advertisement Slot IDs (e.g., slotImpression),
    Advertisement IDs (e.g., Quartiles), or 3rd-party Tracking Impressions.
    """
    # if line.startswith("2019/08/12 16:48:43.813368"):
    #     logging.warning(log_entry)
    # if 'responseCode' in log_entry:
    #     logging.info(log_entry)
    beacon = None
    try:
        match = MatchLogEvent(log_entry)
        if match.qvt:
            logging.debug('Found QVT')
            handle_qvt(match.qvt)
        elif match.ap_5x_ios_qvt:
            logging.debug('Found QVT (iOS AP 5.x)')
            handle_qvt(match.ap_5x_ios_qvt)
        elif match.device:
            logging.debug('Found Device Information')
            handle_device_info(match.device)
        elif match.ap_build:
            logging.debug('Found AP Build Version')
            handle_device_info(match.ap_build)
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
            beacon = InternalBeacon(**match.avg_beacon.groupdict())
        elif match.fw_beacon:
            logging.debug('Found External Beacon')
            beacon = ExternalBeacon(**match.fw_beacon.groupdict())
        elif match.fw_callback:
            logging.debug('Found Response Beacon')
            beacon = ResponseBeacon(**match.fw_callback.groupdict())
        # These next three conditions are for Adaptive Player's newer DAI events
        # (e.g., using SM3 and 'Points')
        elif match.ap_internal:
            logging.debug('Found AP Internal Beacon (SM3)')
            beacon = InternalBeacon(**match.ap_internal.groupdict())
        elif match.ap_external:
            logging.debug('Found External Beacon (SM3)')
            beacon = ExternalBeacon(**match.ap_external.groupdict())
        elif match.ap_response:
            logging.debug('Found Response Beacon (SM3)')
            beacon = ResponseBeacon(**match.ap_response.groupdict())
        # Condition to match the changes in the AP 5.x release.
        elif match.ap_5x_response:
            logging.debug('Found Response Beacon (AP 5.x)')
            beacon = ResponseBeaconAP5x(**match.ap_5x_response.groupdict())
        if beacon is not None:
            beacon = correlate_beacon_params(beacon)
            db_catalog_beacon(beacon)
    except Exception as ex:
        logging.debug(format_exception(ex))


def handle_device_info(match):
    """
    Stores the Adaptive Player Device Information found in the AP log.

    :param _sre.SRE_Match match: The match object of the Ad Request.
    :returns: None
    """
    try:
        dct = match.groupdict()
        Device.update(dct)
    except Exception as ex:
        logging.debug('ERROR Problem encountered while processing device info.')
        logging.debug(format_exception(ex))


def handle_qvt(match):
    """
    Process the QVT received by the Adaptive Player and store it's parameters.

    :param _sre.SRE_Match match: The match object of the QVT.
    :returns: None
    """
    try:
        qvt_str = match.group('logline')
        qvt_obj = ParseQVT(qvt_str)
        qvt_params_list = qvt_obj.records
        with DatabaseOps() as db:
            db.catalog_qvt(qvt_params_list)
    except Exception as ex:
        logging.debug('ERROR Problem encountered while processing the QVT.')
        logging.debug(format_exception(ex))


def handle_ad_request(match):
    """
    Process the Ad Request submitted to FreeWheel from the Adaptive Player.

    Use the Ad Pod ID to identify and store the Ad Request, then parse the
    Ad Request for it's parameters and save them to a separate db table.

    :param _sre.SRE_Match match: The match object of the Ad Request.
    :returns: None
    """
    try:
        timestamp = match.group('timestamp')
        url = match.group('url')
        request_str = ' '.join([timestamp, url])
        request_obj = ParseAdRequest(request_str)
        with DatabaseOps() as db:
            pod_id = db.insert_request(request_str)
            request_obj.insert_pod_id(pod_id)
            request_params = request_obj.parsed_requests
            db.catalog_request(request_params)
    except Exception as ex:
        logging.debug('ERROR Problem encountered while processing Ad Request.')
        logging.debug(format_exception(ex))


def handle_ad_response(match):
    """
    Processes FreeWheel's SmartXML Ad Response.

    First, check to see if we have previously encountered an Ad Request, then
    we'll update it's pod_id using this Ad Response.  IOW, the previous Request
    and this Response will be in the same record (pod_id).

    However, in situations where the Ad Request is missing from the player log
    file, then we never created a record for the Request and the pod_id won't
    exist.  Therefore, this Ad Response won't have a corresponding Ad Request
    and we'll need to create a new record.

    :param _sre.SRE_Match match: The match object of the Ad Response.
    :returns: None
    """
    try:
        timestamp = match.group('timestamp')
        xml_str = match.group('xml')
        response_str = ' '.join([timestamp, xml_str])
        tree = ElementTree.ElementTree(ElementTree.fromstring(xml_str))
        with DatabaseOps() as db:
            pod_id = db.insert_response(response_str)
            logging.debug('Processing Ad Response #{0}.'.format(pod_id))
            for event in collect_impression_info(pod_id, tree):
                db.insert_impression(event)
            for creative in collect_creatives(pod_id, tree):
                db.insert_creative(creative)
                db.update_impressions_with_ad_info(creative)
    except ElementTree.ParseError as ex:
        logging.debug('ERROR Problem parsing XML Ad Response')
        logging.debug(format_exception(ex))
    except Exception as ex:
        logging.debug('ERROR Problem processing Ad Response')
        logging.debug(format_exception(ex))


def collect_impression_info(pod_id, tree):
    """
    Parse the FreeWheel SmartXML Ad Response for the Event Callback information
    and return a list of Impressions. The Event Callback section contains
    information about all the Impression Events, such as the Advertisement
    Slot IDs (e.g., slotImpression), Advertisement IDs (e.g., Quartiles), and
    3rd-party Tracking Impressions.

    :param int pod_id: The ID of the Ad Request submitted to FreeWheel.
    :param xml.etree.ElementTree.ElementTree tree: XML document
    :return: list of impressions found in the XML document
    :rtype: list of dictionaries
    """
    logging.debug('Retrieving impression events from FreeWheel\'s Ad Response #{0}'.format(pod_id))
    slot_id = ''
    time_position = ''
    path = 'siteSection/videoPlayer/videoAsset/adSlots/temporalAdSlot/[@customId]'
    # Loop through each of the Slot IDs
    for element in tree.findall(path):
        slot_id = element.attrib.get('customId')
        time_position = str(int(float(element.attrib.get('timePosition', 0))))
        event = element.find('eventCallbacks').find("eventCallback[@name='slotImpression']").attrib.get('name')
        url = element.find('eventCallbacks').find("eventCallback[@name='slotImpression']").attrib.get('url')
        yield {
            'pod_id': pod_id,
            'slot_id': slot_id,
            'time_position': time_position,
            'ad_id': None,
            'type': 'slot',
            'event': event,
            'url': url,
            'tracking_num': None
        }
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
                    yield {
                        'pod_id': pod_id,
                        'slot_id': slot_id,
                        'time_position': time_position,
                        'ad_id': ad_id,
                        'type': 'quartile',
                        'event': impression,
                        'url': url,
                        'tracking_num': None
                    }
                    # Retrieve the Tracking Impressions for the Impression Event
                    tracking_path = ".//temporalAdSlot/[@customId='{slot_id}']//*[@adId='{ad_id}']//trackingURLs/*" \
                                    "[@name='{impression}']"
                    for count, item in enumerate(tree.findall(tracking_path.format(
                            slot_id=slot_id, ad_id=ad_id, impression=impression)), 1):
                        url = item.attrib.get('value')
                        yield {
                            'pod_id': pod_id,
                            'slot_id': slot_id,
                            'time_position': time_position,
                            'ad_id': ad_id,
                            'type': 'tracking',
                            'event': impression,
                            'url': url,
                            'tracking_num': count
                        }
    # Append the slotCompleted event to the end of each slotImpression
    yield {
        'pod_id': pod_id,
        'slot_id': slot_id,
        'time_position': time_position,
        'ad_id': None,
        'type': 'slot',
        'event': 'slotCompleted',
        'url': '',
        'tracking_num': None
    }


def collect_creatives(pod_id, tree):
    """
    Parse the FreeWheel SmartXML Ad Response for information related to the Creative Advertisements.

    :param int pod_id: The ID of the Ad Request submitted to FreeWheel.
    :param xml.etree.ElementTree.ElementTree tree: FreeWheel's SmartXML document
    :return: list of the impressions found in the XML document
    :rtype: list of dictionaries
    """
    path = 'creatives/creative'
    rendition_path = path + '/creativeRenditions/creativeRendition'
    asset_path = rendition_path + '/asset'
    logging.debug('Retrieving Creative Ads from FreeWheel\'s Ad Response #{0}'.format(pod_id))
    for element in tree.findall('ads/ad'):
        yield {
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
        }


def init_database():
    """ Create a database to store and retrieve information. """
    with SQLiteDB() as db:
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
                beacon_event_firing_order_status TEXT NOT NULL DEFAULT '',
                valid_quartile_placement_status TEXT NOT NULL DEFAULT '',
                valid_quartile_placement_msg TEXT NOT NULL DEFAULT '',
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
            
            DROP TABLE IF EXISTS QVTs;
            CREATE TABLE IF NOT EXISTS QVTs (
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
            -- Prevent duplicate QVTs
            CREATE UNIQUE INDEX idx_qvt_cue_point_number ON QVTs (cue_point_number);
           
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
            -- Prevent duplicate Ad Requests 
            CREATE UNIQUE INDEX idx_adreq_slot_id ON Requests (slid);

            DROP TABLE IF EXISTS Unmatched;
            CREATE TABLE IF NOT EXISTS Unmatched (
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
                content TEXT NOT NULL DEFAULT '',
                status TEXT NOT NULL DEFAULT 'False'
            );
            
            DROP TABLE IF EXISTS Validated_Requests;
            CREATE TABLE IF NOT EXISTS Validated_Requests(
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
        db.executescript(script)


def db_catalog_beacon(beacon):
    """
    Update the database to record the occurrence of the Adaptive Player event.

    :param Impression beacon:
    :return: None
    """
    try:
        pk, log, response = beacon.pk, beacon.logline, beacon.response_code
        with DatabaseOps() as db:
            if beacon.is_valid:
                if 'Internal' in beacon.source:
                    db.update_internal_log(pk, log)
                elif 'External' in beacon.source:
                    db.update_sent_impression(pk, log)
                elif 'Response' in beacon.source:
                    db.update_received_impression(pk, log, response)
            else:
                db.insert_unmatched_impression(pk, log)
    except (AttributeError, KeyError, TypeError, Exception) as ex:
        logging.debug('ERROR Problem updating the database records.')
        logging.debug(format_exception(ex))


def db_identify_active_pod():
    """
    Return the Active Pod ID.

    :return: int pod_id
    """
    with SQLiteDB() as cursor:
        cursor.execute("SELECT MAX(pod_id) FROM AdPods;")
        pod_id = cursor.fetchone()
    if pod_id:
        return pod_id[0]


def db_identify_beacon_event_type(url):
    """ Returns the beacon event type. """
    with SQLiteDB(row=True) as cursor:
        cursor.execute('SELECT type FROM Impressions WHERE url = ?;', (url,))
        record = cursor.fetchone()
        if record:
            return record['type']


def correlate_beacon_params(beacon=None):
    # type: (Impression) -> Impression
    """
    Attempt to correlate and update missing slotImpressions, Quartiles, and
    Tracking Impression parameters which are not present or available when
    parsing the parameters from the line in the Adaptive Player log.

    If we previously encountered a FreeWheel Ad Response, then ideally we've
    parsed and extracted the XML and have created records in the database
    of the Impressions we expect to see from the Adaptive Player.

    :param Impression beacon:
    :return: beacon
    :rtype: Impression
    """
    try:
        event = beacon.beacon_type
        source = beacon.source
        beacon.pod_id = db_identify_active_pod()
        if beacon.new_logging_style:
            template = SQLQueryStatements(event, source)
        else:
            template = SQLQueryStatementsFormer(event, source)

        with SQLiteDB(row=True) as cursor:
            sql_query = template.format(**vars(beacon))
            cursor.execute(sql_query)
            record = cursor.fetchone()
        if record:
            beacon.update_from_sql(record)
        else:
            msg = "WARNING Failed to match beacon against FreeWheel's XML"
            logging.debug(msg)
        return beacon
    except Exception as ex:
        logging.debug(format_exception(ex))


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
        else:
            logging.debug('No previous SM3PointsCacheItem found. Saving the current one in the database.')
            pod_id = sm3_store_log(match)
            sm3_store_ad_request(match, pod_id)
            sm3_store_ad_response(match, pod_id)
            sm3_collect_info(match, pod_id)
    except Exception as ex:
        logging.debug('ERROR Problem processing SM3 Points Cache Item #{0}')
        logging.debug(format_exception(ex))


def sm3_store_log(match):
    """
    Stores the log entry for the SM3PointsCacheItem.

    :param _sre.SRE_Match match: The SM3PointsCacheItem object.
    :return: lastrowid: The ID of the last row inserted.
    :rtype: int
    """
    with SQLiteDB() as cursor:
        cursor.execute('''
            INSERT INTO AdPods (sm3pointscacheitem) 
            VALUES (?);''', (match.group("logline"),))
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
                         WHERE pod_id = ?;''', (url, pod_id))
                    break


def sm3_store_ad_response(match, pod_id):
    """
    Parses the SM3PointsCacheItem object for the Advertisement Response from
    FreeWheel and stores it.

    :param _sre.SRE_Match match: The SM3PointsCacheItem object.
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
                         WHERE pod_id = ?;''', (xml, pod_id))
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
                )''')


def sm3_collect_info(match, pod_id):
    """
    Parse the SM3PointsCacheItem for the Event Callback information and store
    them in the database.  This object contains information about all the
    Impression Events, such as the Advertisement Slot IDs (e.g., slotImpression),
    Advertisement IDs (e.g., Quartiles), and 3rd-party Tracking Impressions.

    :param _sre.SRE_Match match: The SM3PointsCacheItem object.
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
                (:pod_id, :slot_id, :ad_id, :type, :event, :url, :duration, :fire_time, :tracking_num);''', results)

        # Provide debugging output per user's request
        if logging.getLogger().isEnabledFor(logging.DEBUG):
            cursor.execute("SELECT * FROM Impressions WHERE pod_id=?", (pod_id,))
            column_names = tuple(map(lambda x: x[0], cursor.description))
            rows = cursor.fetchall()
            table = "\n".join(map(str, rows))
            msg = "Number of Impressions in SM3\'s Ad Response #{0}: {1}\n{2}\n{3}"
            logging.debug(msg.format(pod_id, len(rows), column_names, table))


def sm3_remove_debug_info(match):
    """
    Remove the debug information from the SM3PointsCacheItem. In order to
    determine if the previous and current SM3PointsCacheItems are identical
    or not, the '_debug' information needs to be removed before performing
    the comparision.

    :param _sre.SRE_Match match: The SM3PointsCacheItem object.
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


def write_ad_response_to_file(pod_id, xml_str):
    # type: (int, str) -> None
    """
    Saves FreeWheel's SmartXML Response to a temporary directory as a JSON.

    :param int pod_id: The ID of the Ad Request submitted to FreeWheel.
    :param str xml_str: Contains FreeWheel's SmartXML document
    :return None
    """
    try:
        directory = tempfile.gettempdir()
        filename = 'FreeWheel_XML_Ad_Response_num_{0}.xml'.format(str(pod_id).zfill(2))
        filepath = '/'.join([directory, filename])
        logging.info("Writing FreeWheel\'s Ad Response #{0} to {1}".format(pod_id, filepath))
        xml = minidom.parseString(xml_str).toprettyxml(indent='    ')
        with open(filepath, 'w', encoding='utf-8') as outfile:
            outfile.write(xml)
    except Exception as ex:
        logging.debug("ERROR Problem writing FreeWheel's XML Ad Response out to disk.")
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


def insert_validated_requests_into_db(results):
    """ Inserts validated Ad Request info into the database. """
    with DatabaseOps() as db:
        db.insert_validated_requests(results)


def retrieve_ad_pod_records():
    """ Retrieves the Ad Pod from the database. """
    with DatabaseOps() as db:
        return db.fetch_ad_pod_records()


def retrieve_qvt_record(slot_id):
    """ Retrieves the QVT from the database. """
    with DatabaseOps() as db:
        return db.fetch_qvt_record(slot_id)


def fetch_report_from_database(slot_id=None):
    """ Retrieves the HTML DAI Validation Report from the database. """
    with DatabaseOps() as db:
        return db.fetch_html_report(slot_id)


def save_report(slot_id):
    """ Saves the DAI Validation Report(s) to Disk. """
    for report in fetch_report_from_database(slot_id):
        save_report_to_disk(*report)


def save_report_to_disk(pod_id, slot_id, content, status):
    # type: (int, str, str, str) -> None
    """
    Saves the Dynamic Ad Insertion report to a temporary directory.

    :param int pod_id: The ID of the Ad Request submitted to FreeWheel.
    :param str slot_id: The Ad Request Slot ID (aka SLID) submitted to FreeWheel.
    :param str content: The HTML document
    :param str status: The error status of the HTML document.
    :return None
    """
    try:
        template = 'Ad_Response_num_{0}_Slot_ID_{1}_{2}_{3}.html'
        now = time.strftime("%F-%H%M%S", time.localtime(time.time()))
        status = status.lower()
        #directory = tempfile.gettempdir()
        directory = ((sys.argv[2][::-1]).split('\\', 1))[1][::-1]
        filename = template.format(str(pod_id).zfill(2), slot_id, now, status)
        filepath = '/'.join([directory, filename])
        msg = 'Writing Ad Response #{0} for Slot_ID {1} to file://{2}'
        logging.info(msg.format(pod_id, slot_id, filepath))
        with open(filepath, 'w') as outfile:
            outfile.write(content)
    except Exception as ex:
        logging.debug('ERROR Problem writing DAI Validation Report out to disk.')
        logging.debug(format_exception(ex))


def save_report_to_database(pod_id=1, slot_id='1', report=None):
    """ Stores the DAI Validation Report in the database. """
    try:
        status = report_status(report)
        if not report:
            report = 'Missing Everything (e.g., Ad Request, Ad Response, QVT)'
            status = 'FAIL'
        with DatabaseOps() as db:
            pk = db.insert_report(pod_id, slot_id, report, status)
            msg = 'PK:{0}, Ad Response:{1}, Slot_ID:{2}, Status:{3}'
            logging.debug(msg.format(pk, pod_id, slot_id, status))
    except Exception as ex:
        logging.debug('ERROR Problem saving the report to the database.')
        logging.debug(format_exception(ex))


def pandas_set_options():
    """ Sets options in Pandas to define how the output should be displayed. """
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
    Query the database for all the Ad Breaks encountered while processing the
    Adaptive Player log file (e.g., player.log) and use the results to generate
    the HTML report.
    """
    rows = retrieve_ad_pod_records()
    if rows:
        for row in rows:
            pod_id, slot_id, request_str, response_str = row
            qvt_record = retrieve_qvt_record(slot_id)
            report = generate_html_report(qvt_record, *row)
            save_report_to_database(pod_id, slot_id, report)
    else:
        report = generate_html_report()
        save_report_to_database(report=report)


def generate_html_report(qvt_record=None, pod_id=None, slot_id=None,
                         request_str=None, response_str=None):
    """
    Generate the HTML Report to display to the end user.

    :param int pod_id:  The ID of the Advertisement Pod.
    :param str slot_id: The Ad Request Slot ID (aka SLID) sent to FreeWheel.
    :param str request_str: The Ad Request submitted to Freewheel.
    :param str response_str:  The Ad Response received from FreeWheel
    :param dict qvt_record: Information about the QVT.
    """
    try:
        ButtonControls.reset()
        content = [
            to_html_title_element(slot_id),
            to_html_style_element(),
            to_html_keycode_script_element(),
            to_html_toggle_script_element(),
            to_html_display_program_version_info(),
            to_html_display_report_heading(pod_id, slot_id),
            to_html_display_ap_build_version_info(),
            to_html_display_channel_info(qvt_record),
            to_html_display_qvt_link(qvt_record),
            to_html_display_ad_request_url(request_str),
            to_html_display_validated_ad_request_url(pod_id, slot_id),
            to_html_display_ad_response_xml(response_str),
            to_html_display_ad_response_xml_validation(response_str, slot_id),
            to_html_display_media_m3u8_extension(pod_id, slot_id),
            to_html_display_beacon_summary(pod_id, slot_id, qvt_record),
            to_html_display_beacon_validation(pod_id, slot_id),
            to_html_display_duplicate_beacons_and_responses(pod_id, slot_id),
            to_html_display_unmatched_beacons_and_responses(pod_id, slot_id),
            to_html_footer()
        ]
        content.insert(7, to_html_display_controls())
        html_report = ''.join(content)
        return html_report
    except Exception as ex:
        logging.debug(format_exception(ex))


def to_html_title_element(slot_id):
    # type: (str) -> str
    """ Provides the initial HTML head/title elements for the HTML document. """
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
            
            footer {
                text-align: center;
                font-family: monospace, monospace;
                font-size: small;
                color: rgb(181, 181, 181);
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
            
            .text-ap-version {
                text-align: left;
                font-family: monospace, monospace;
                font-size: 75%;
                color: red;
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


def to_html_display_ap_build_version_info():
    """ Displays the build version of the Adaptive Player. """
    msg = 'Player Version: {0}_{1}'.format(Device.ap_client, Device.ap_build)
    return "<div class='text-ap-version'>{}</div>".format(msg)


def to_html_display_program_version_info():
    """ Displays the version of this program in the upper right corner. """
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


def to_html_display_controls():
    """
    Display controls to provide the ability to navigate the HTML document via
    mouse or keyboard.

    :return: HTML formatted string
    :rtype: str
    """
    section = "Display Controls"
    header = '''<hr><div id="{section}" class="container">{buttons}</div>'''
    buttons = ''.join(update_button_status(
        index, k, v) for index, (k, v) in enumerate(ButtonControls.info))
    return header.format(section=section, buttons=buttons)


def to_html_display_channel_info(qvt):
    # type: (dict) -> str
    """
    Displays information about the Channel, Asset, Start Time, End Time,
    and Duration.

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
    re_json = re.compile(
        r"""
            ^[^{]*  # from the start, match anything that isn't an open brace
                (?P<json>{.+})  # open capture group to grab the json substring
             [^}]*$  # from the closing brace onwards, match everything
        """, re.VERBOSE)

    try:
        if 'Missing' not in qvt['log']:
            log = qvt['log']
        else:
            log = MISSING

        if 'Missing' not in qvt['url']:
            url = qvt['url']
        else:
            url = qvt_url = MISSING

        qvt_string = re_json.match(log).group('json')
        if qvt_string:
            json_data = json.loads(qvt_string)
            json_html = json.dumps(json_data, indent=4).replace('    ', '&emsp;&emsp;').replace('\n', '<br>')
            timestamp = re.match(r'^(?P<date>\d{4}/\d{2}/\d{2}\s\d{2}:\d{2}:\d{2})', log).group(1)
            qvt_url = "<a href='{0}' target='_blank'> {0}</a>".format(url)
    except (AttributeError, TypeError):
        timestamp, log, qvt_url = (MISSING,)*3

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


def to_html_display_ad_request_url(request_str=None):
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
    with DatabaseOps(row=True) as db:
        validated_params = db.fetch_validated_url_params(pod_id, slot_id)
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


def to_html_display_ad_response_xml(xml_response_str=None):
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
        xml_str = xml_response_str.split(' ', 2)[2]
        tree = ElementTree.ElementTree(ElementTree.fromstring(xml_str))
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
            minidom.parseString(xml_str)
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
    :param str expected_slot_id: Ad Request Slot ID submitted to FreeWheel.
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
    events = ['defaultImpression', 'firstQuartile', 'midPoint', 'thirdQuartile', 'complete']
    query = ".//temporalAdSlot/[@customId='{0}']//*[@adId='{1}']//*[@type='IMPRESSION'][@name='{2}']"
    base_path = 'siteSection/videoPlayer/videoAsset/adSlots/temporalAdSlot/[@customId]'
    try:
        logging.debug('Validating FreeWheel SmartXML Ad Response.')
        xml_str = xml_response_str.split(' ', 2)[2]
        pod = OrderedDefaultDict()
        tree = ElementTree.ElementTree(ElementTree.fromstring(xml_str))
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
    except Exception as ex:
        logging.debug(format_exception(ex))
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
    records = []

    with DatabaseOps() as db:
        rows = db.fetch_ad_creatives(pod_id, slot_id)

    if not rows or not slot_id:
        error_msg = format_section_error('(FAILED) Missing XML Response.')
        return ''.join([header, error_msg])

    for row in rows:
        ad_id, asset_url = row
        records.append({
            'Advertisement ID': link.format(PLAYER, asset_url, ad_id),
            'M3U8 Status': has_m3u8(asset_url)
        })

    df = pd.DataFrame(records)
    df.index = df.index + 1
    table = (df.style.set_table_styles(table_style()).set_properties(**{'text-align': 'center'})).render()
    html = ''.join([header, body, table, end])
    update_display_controls(html, section)
    return html


def to_html_display_beacon_summary(pod_id, slot_id, qvt):
    # type: (int, str, dict) -> str
    """
    Displays the Beacon Summary in HTML format so it can be displayed properly
    in the DAI report. This is needed to properly display the metrics about the
    Tracking Impression.

    :param int pod_id: The ID of the Ad Request submitted to FreeWheel.
    :param str slot_id: The Ad Request Slot ID submitted to FreeWheel.
    :param dict qvt: Information about the QVT.
    :returns: HTML formatted output for the Beacon Summary Section.
    :rtype: str
    """
    def color_table_caption(string, dataframe):
        """ Returns a caption tagged as pass or fail according to the success rate. """
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

    with DatabaseOps() as db:
        duration = db.fetch_slot_impression_duration(slot_id)
        records = db.fetch_quartile_tracking_impressions(pod_id, slot_id)

    try:
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


def to_html_display_beacon_validation(pod_id, slot_id):
    # type: (int, str) -> str
    """
    Queries the SQL database for the given Slot Impression ID and identifies
    the event so it can be wrapped in HTML and displayed properly in the
    Beacon Validation Section of the DAI report.

    :param int pod_id: AdPod ID of the Ad Request submitted to FreeWheel.
    :param str slot_id: Ad Request Slot ID (aka SLID) submitted to FreeWheel.
    :returns: HTML formatted output for the Beacon Validation Section.
    :rtype: str
    """
    section = "Beacon Validation"
    header = create_html_section_header(section)
    html = header
    with DatabaseOps(row=True) as db:
        rows = db.fetch_impressions(pod_id, slot_id)
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
    html += "</div>"
    update_display_controls(html, 'Beacon Validation')
    return html


def to_html_display_duplicate_beacons_and_responses(pod_id, slot_id):
    """
    Queries a specific Slot Impression to determine if the Adaptive Player
    sent or received any duplicate impressions.
    """
    def table_style():
        """ Returns the styling instructions for Pandas. """
        return [hover(), table_header(), table_row(), table_data('red'), table_caption()]

    def find_duplicate_impressions(_pod_id, _slot_id):
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
            ''', {'pod_id': _pod_id, 'slot_id': _slot_id})
            column_names = list(map(lambda x: x[0], cursor.description))
            _rows = cursor.fetchall()
            return [dict_from_row(row) for row in _rows], column_names

    section = "Duplicate Beacons and Responses"
    header = create_html_section_header(section)
    body = "<div class='double_indent'>"
    error_msg = "<font class='text-fail'>(FAILED) Found Duplicates</font>"
    end = '</div><br>'
    rows, table_headings = find_duplicate_impressions(pod_id, slot_id)
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


def to_html_display_unmatched_beacons_and_responses(pod_id, slot_id):
    # type: (int, str) -> str
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

    :param int pod_id: The ID of the Ad Request submitted to FreeWheel.
    :param str slot_id: The Ad Request Slot ID (aka SLID) submitted to FreeWheel.
    :returns: HTML formatted output for the Unmatched Beacons Section.
    :rtype: str
    """
    def get_start_time(slot_id_):
        """ Returns a UNIX timestamp of the Ad Request for this Slot ID. """
        milliseconds = '.000'
        with DatabaseOps() as db:
            date_time = db.fetch_ad_request_timestamp(slot_id_)
        if date_time:
            date_str = date_time[0] + milliseconds
            return convert_datestr_to_unix_timestamp(date_str)

    def get_stop_time(pod_id_, slot_id_):
        """ Returns a UNIX timestamp for when to stop searching. """
        time_delay_secs = 180
        with DatabaseOps() as db:
            unix_ts = db.fetch_slot_end_time(pod_id_, slot_id_)
        if all(unix_ts):
            return unix_ts[0] + time_delay_secs

    def get_unmatched_impressions(start_ts, end_ts):
        """ Returns records found between this time frame. """
        with DatabaseOps(row=True) as db:
            return db.fetch_unmatched_impressions_with_range(start_ts, end_ts)

    section = "Unmatched Beacons and Responses"
    header = create_html_section_header(section)
    element = "<span class='beacon double_indent text-fail text-nowrap'>{}</span>"

    t0 = get_start_time(slot_id)
    tn = get_stop_time(pod_id, slot_id)
    if all([t0, tn]):
        rows = get_unmatched_impressions(t0, tn)
        if rows:
            body = format_section_error("(FAILED) Unmatched Beacon(s) Found.")
            body += "<br>"
            body += "".join(element.format(
                str(i) + ' : ' + rec['log']) for i, rec in enumerate(rows, 1))
            body += "</div>"
        else:
            body = format_section_success("(PASS) No Unmatched Beacons Found.")
    else:
        body = format_section_error("FAILED) Missing Ad Request and/or XML Response.")
    html = "".join([header, body])
    update_display_controls(html, section)
    return html


def to_html_footer():
    html = '''
        <hr>
            <footer>
                {}<br>
                Copyright 2019, Sling TV, All Rights Reserved
            </footer>
        </body>
        </html>
    '''
    return html.format(datetime.now())


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
                    {beacon_event_firing_order_status}: Valid Firing Sequence for this Impression <br>
                </div>
                <div class='indent beacon'>
                    {valid_quartile_placement_status}: Valid Quartile Placement 
                    {valid_quartile_placement_msg}<br>
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
                    {beacon_event_firing_order_status}:<br>
                    {valid_quartile_placement_status}:<br>
                </div>
                <div style='margin-left: 1em;'>
                    <span class='text-nowrap'>HTTP Status: {http_status}</span><br>
                    <span class='text-nowrap'>Valid Firing Sequence for this Impression</span><br>
                    <span class='text-nowrap'>Valid Quartile Placement {valid_quartile_placement_msg}</span><br>
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
        cursor.execute("SELECT pk, log FROM Unmatched WHERE log <> '';")
        for row in cursor.fetchall():
            pk, log = row
            m = re.match(re_datetime, log)
            if m:
                date_string = m.group()
                dt_object = datetime.strptime(date_string, '%Y/%m/%d %H:%M:%S.%f')
                unix_ts = to_unix_timestamp(dt_object)
                cursor.execute('''
                    UPDATE Unmatched
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
                          FROM QVTs 
                         WHERE QVTs.cue_point_number = Impressions.slot_id
                   ) 
             WHERE Impressions.type = 'slot' 
               AND Impressions.event = 'slotImpression' 
               AND EXISTS (
                    SELECT start_offset_with_delay 
                      FROM QVTs 
                     WHERE QVTs.cue_point_number = Impressions.slot_id
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
    quartiles = [
        ('firstQuartile', 0.25),
        ('midPoint', 0.5),
        ('thirdQuartile', 0.75),
        ('complete', 0.90)
    ]
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


def validate_beacon_event_firing_order():
    # type: () -> None
    """
    Queries all the records in the Impression table and, for each beacon event,
    determines if Adaptive Player reports the event in the correct sequence.
    Specifically, does the timestamp of when the beacon was sent occur before
    the timestamp of the beacon response.  Technically, it isn't possible for
    the Adaptive Player to receive a response before a beacon is sent, so we're
    just ensuring the AP is logging the events in the correct sequence.
    """
    re_timefmt = r'^(?P<date>\d{4}[/.-]\d{2}[/.-]\d{2}\s\d{2}:\d{2}:\d{2}[.]\d+).*'
    timestampfmt = '%Y/%m/%d %H:%M:%S.%f'
    with DatabaseOps() as db:
        rows = db.fetch_impressions_sent_received_logs()
        for row in rows:
            pk, sent_log, received_log = row
            time_sent = re.sub(re_timefmt, r'\g<date>', sent_log)
            time_received = re.sub(re_timefmt, r'\g<date>', received_log)
            if not all([time_sent[:4].isdigit(), time_received[:4].isdigit()]):
                result = FAIL
            else:
                time_sent = datetime.strptime(time_sent, timestampfmt)
                time_received = datetime.strptime(time_received, timestampfmt)
                if time_sent < time_received:
                    result = PASS
                else:
                    result = FAIL
            db.update_beacon_event_firing_order(pk, result)


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
    previous_event = None
    previous_firing_time = float(0)
    previous_pk = None
    with DatabaseOps() as db:
        rows = db.fetch_impressions_actual_firing_time()
        for row in rows:
            pk, event, actual_firing_time = row
            result = previous_firing_time <= actual_firing_time
            if result:
                logging.debug("True - '{0}' fired BEFORE '{1}'".format(previous_event, event))
                result = PASS
            else:
                logging.debug("False - '{0}' fired AFTER '{1}'".format(previous_event, event))
                logging.debug('Updating primary_key: {0}'.format(previous_pk))
                result = FAIL
            previous_firing_time = actual_firing_time
            previous_event = event
            previous_pk = pk
            db.execute("UPDATE Impressions SET overall_firing_order=? WHERE pk=?;", (result, pk))


def validate_beacon_placement():
    # type: () -> None
    """
    Queries the Impressions in the database to determine if the Impression was
    sent in the order it was expected (e.g., defaultImpression, firstQuartile,
    midPoint, thirdQuartile, complete).

    In scenarios where the AP failed to send the Impression, the placement
    status is marked as failed so that the 'Valid Quartile Placement' field
    appears as '(FAIL)' in the output of the report.
    """
    with DatabaseOps() as db:
        rows = db.fetch_impressions_actual_firing_time()
        for expected, actual in zip(rows, sorted(rows, key=lambda x: x[2])):
            pk = expected[0]
            quartile = actual[1]
            if expected == actual:
                result = PASS
                msg = ''
            else:
                result = FAIL
                msg = '(found in {})'.format(quartile)
            db.update_impressions_valid_quartile_placement(pk, msg, result)
        rows = db.fetch_empty_quartile_placements()
        for row in rows:
            pk, event, msg, status = row
            if not status:
                db.update_impressions_valid_quartile_placement(pk, '', FAIL)


def validate_http_response_status():
    # type: () -> None
    """ Determines if the HTTP response is valid. """
    with DatabaseOps() as db:
        rows = db.fetch_impressions_http_status()
        for row in rows:
            pk, http_status = row
            response_code = int(http_status.strip() or 0)
            if response_code == 200 or response_code == 204:
                result = PASS
            else:
                result = FAIL
            db.update_http_status(pk, result)


def validate_ad_request_url():
    """
    Validates the parameters in the Ad Request URL ('found') against the QVT ('expected').
    """
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
            '93a256a7.cdn.cms.movetv.com': dict(zip(param, beta)),
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
            ('TPOS', 'tpos', 'tpos'),
        ]
        params = OrderedDefaultDict()
        for key in key_order:
            params[key[0]] = compare(key[0], qvt_dict[key[1]], request_dict[key[2]])
        return params

    try:
        rows = retrieve_ad_pod_records()
        for row in rows:
            pod_id, slot_id, request_str, response_str = row
            request = ParseAdRequest(request_str).retrieve_ad_slot_id(slot_id)
            qvt = retrieve_qvt_record(slot_id)
            if not all([slot_id, request_str, request, qvt]):
                return
            else:
                results = compare_url_parameters(qvt, request)
                results = cdn_property_validation(results, qvt['url'])
                results = add_keys(pod_id, slot_id, results)
                insert_validated_requests_into_db(results)
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
    ButtonControls.info.append((section, has_failed))


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


def report_status(report):
    if 'class="btn btn-fail"' in report:
        return 'FAIL'
    else:
        return 'PASS'


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
    validate_beacon_event_firing_order()
    validate_beacon_placement()
    validate_http_response_status()
    validate_ad_request_url()


def cleanup():
    logging.debug('Performing cleanup:')
    logging.debug('- Removing the following database: {0}'.format(SQLiteDB().path))
    SQLiteDB().delete_database_file()


def has_failures_in_report():
    """ Returns True if any of the DAI Reports has validation errors. """
    for report in fetch_report_from_database():
        pod_id, slot_id, content, status = report
        if 'FAIL' in status:
            return True
    return False


# ----------------------------------------------------------------------------------------------
# Main
# ----------------------------------------------------------------------------------------------
if __name__ == "__main__":

    # t0 = time.time()
    exit_code_status = 0
    args = parse_args()
    try:
        # Initialize
        init_database()

        # Some imported module is setting a logging handler and is causing logging.basicConf to
        # be a no-op, so this is a work around to clear the handler before configuring the
        # logging level specified on the command line
        logging.getLogger('').handlers = []
        logging.basicConfig(
            level=args.loglevel,
            format='%(asctime)s %(levelname)s %(module)s - %(funcName)s: %(message)s',
            datefmt='%Y-%m-%d %H:%M:%S')

        logging.info('Processing the following file: {0}'.format(args.filename))
        with open(args.filename, 'r', encoding='utf-8') as f:
            for line in merge_multiple_lines(f):
                process(line)

        # Post-process and validate the data
        post_process_information()
        validate_information()

        # Generates the DAI Validation Report in HTML format.
        if args.html:
            color_beacons(args)
            to_html()
            save_report(args.slot)

        # As part of the automated testing, determine if there are any failures in any
        # of the DAI Validation Reports and, if so, exit with a non-zero status.
        if has_failures_in_report():
            exit_code_status = 1

    except (AttributeError, TypeError, ValueError) as exception:
        logging.debug(format_exception(exception))
    except (KeyboardInterrupt, SystemExit):
        logging.debug('User cancelled the operation, stopping...')
    finally:
        cleanup()
        # t1 = time.time()
        logging.info('Finished processing: {0}'.format(args.filename))
        logging.info('Exiting with exit code status of: {0}'.format(exit_code_status))
        # logging.info("Took {0:.2f} seconds".format(t1 - t0))
        sys.exit(exit_code_status)

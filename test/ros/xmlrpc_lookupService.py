#!/usr/bin/env python

import os
import xmlrpclib

caller_id = '/script'
m = xmlrpclib.ServerProxy(os.environ['ROS_MASTER_URI'])
test = m.lookupService(caller_id,'add_two_ints')
print(test)	

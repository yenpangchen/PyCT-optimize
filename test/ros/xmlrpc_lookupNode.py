#!/usr/bin/env python

import os
import xmlrpclib

caller_id = '/script'
m = xmlrpclib.ServerProxy(os.environ['ROS_MASTER_URI'])
test = m.lookupNode(caller_id,'hello_python_node')
print(test)	

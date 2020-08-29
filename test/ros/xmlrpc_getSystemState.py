import xmlrpclib
import os

# server = xmlrpclib.ServerProxy(os.environ['ROS_MASTER_URI'],verbose=False)

# print server.getSystemState('/rosout')


import os
import xmlrpclib
caller_id = '/script'
m = xmlrpclib.ServerProxy(os.environ['ROS_MASTER_URI'])

code, msg, val = m.getSystemState(caller_id)
if code == 1:
    pubs, subs, srvs = val
    print(val)
else:
    print "call failed", code, msg
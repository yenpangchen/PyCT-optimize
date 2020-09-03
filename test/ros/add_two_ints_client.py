#!/usr/bin/env python

import sys
import rospy
from rospy_tutorials.srv import *

def add_two_ints_client(x, y):
    rospy.wait_for_service('add_two_ints')
    try:
        add_two_ints = rospy.ServiceProxy('add_two_ints', AddTwoInts)
        resp1 = add_two_ints(x, y)
        return resp1.sum
    except rospy.ServiceException as e:
        print(f"Service call failed: {e}")

def usage():
    return f"{sys.argv[0]} [x y]"

if __name__ == "__main__":
    if len(sys.argv) == 3:
        x = int(sys.argv[1])
        y = int(sys.argv[2])
    else:
        print(usage())
        sys.exit(1)
    print(f"Requesting {x}+{y}")
    print(f"{x} + {y} = {add_two_ints_client(x, y)}")

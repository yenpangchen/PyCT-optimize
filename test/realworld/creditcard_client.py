#######################################################################################
# To make this example work, we have to upcast hosts and ports to their primitive types
# in the function getaddrinfo in line 901 of the file /usr/lib/python3.8/socket.py with
# the following two statements:
# if isinstance(host, str): host = str.__str__(host)
# if isinstance(port, int): port = int.__int__(port), and
# replace "return IMM_INTS_LOADER[tag]" in line 357 of the file /home/alan23273850/.local/share/virtualenvs/1_CODE_py-conbyte-AGrb4DSq/lib/python3.8/site-packages/rpyc/core/brine.py
# with "return int.__int__(IMM_INTS_LOADER[tag])" beforehand!
#######################################################################################

import rpyc

def startswith(x, prefixes):
    while x > 0:
        if x in prefixes: return True
        x //= 10
    return False

# https://en.wikipedia.org/wiki/Payment_card_number#Issuer_identification_number_(IIN)
def creditcard_client(x: int) -> str:
    proxy = rpyc.connect("localhost", 8080).root
    if proxy:
        if pow(10, 15-1) <= x and proxy.check_luhn(x):
            if pow(10, 16-1) <= x:
                if x < pow(10, 19):
                    if startswith(x, range(3528, 3590)):
                        return 'JCB'
                    if x < pow(10, 16) and (startswith(x, range(51, 56)) or startswith(x, range(2221, 2721))):
                        return 'Mastercard'
            elif startswith(x, (34, 37)):
                return 'American Express'
        return 'Unknown'
    # return 'Server Error'

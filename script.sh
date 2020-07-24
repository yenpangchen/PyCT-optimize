#!/bin/bash

declare -A arr

# arr["test/build_in.py"]=[0,0] # OK
# arr["test/call_obj.py"]=[0,0] # OK
# arr["test/do_abs.py"]=[0,0] # OK
# arr["test/do_array.py"]=[0,0] # OK
# arr["test/do_numbers.py"]=[0,0] # OK
# arr["test/do_range.py"]=[0,0] # OK
# arr["test/list_dict.py"]=[0,0] # OK
# arr["test/loop.py"]=[0,0] # OK
# arr["test/while_loop.py"]=[0,0] # OK
# --------------------------------------------------------------------
arr["test/strings/string_find.py"]='["",""]' # OK
# arr["test/strings/string_in.py"]='["",""]' # OK
# arr["test/strings/string_iter.py"]='["",""]' # OK
# arr["test/strings/string_others.py"]='["",""]' # OK
# arr["test/strings/string_replace.py"]='["",""]' # OK
# arr["test/strings/string_slice.py"]='["",""]' # OK
# arr["test/strings/string_startswith.py"]='["",""]' # OK
# --------------------------------------------------------------------
# arr["test/targets/count_emma.py"]='[""]' # OK
# arr["test/targets/multiplication_or_sum.py"]=[0,0] # OK
# arr["test/targets/regex.py"]='["007 James Bond"]' # OK
# --------------------------------------------------------------------
# arr["test/targets/leetcode/add_digits.py"]=[0] # OK
arr["test/targets/leetcode/findUnsortedSubarray.py"]=[[]] # OK
# arr["test/targets/leetcode/fraction_to_decimal.py"]=[-50,8] # OK
# arr["test/targets/leetcode/isLongPressedName.py"]='["",""]' # OK
arr["test/targets/leetcode/numDecodings.py"]='[""]' # OK
# arr["test/targets/leetcode/restoreIpAddresses.py"]='["25525511135"]' # OK
# arr["test/targets/leetcode/reverseCheck.py"]=[0] # OK
# arr["test/targets/leetcode/substring.py"]='[""]' # OK
# arr["test/targets/leetcode/substring2.py"]='[""]' # OK
# arr["test/targets/leetcode/ugly_number.py"]=[0] # OK
# --------------------------------------------------------------------
# arr["target_int/leetcode_int/add_binary.py"]='["",""]' # OK
# arr["target_int/leetcode_int/addStrings.py"]='["923","123"]' # OK
# arr["target_int/leetcode_int/numDecodings.py"]='[""]' # OK
# arr["target_int/leetcode_int/restoreIpAddresses.py"]='[""]' # OK
# arr["target_int/leetcode_int/validIPAddress.py"]='[""]' # OK
# arr["target_int/leetcode_int/validWordAbbreviation.py"]='["",""]' # OK
# --------------------------------------------------------------------
# arr["target_int/lib_int/datetime__parse_hh_mm_ss_ff.py"]='[""]' # OK
# arr["target_int/lib_int/datetime__parse_isoformat_date.py"]='[""]' # OK
# arr["target_int/lib_int/distutils_get_build_version.py"]='["MSC v.1212 abc"]' # OK
# arr["target_int/lib_int/email__parsedate_tz.py"]='["Mon, 16 Nov 2009 13:32:02 +0100"]' # OK (poor, and str.split() not implemented)
# arr["target_int/lib_int/http_parse_request.py"]='["HTTP/1.0"]' # OK
# arr["target_int/lib_int/ipaddress__ip_int_from_string.py"]='[""]' # OK (but very slow)
# arr["target_int/lib_int/nntplib__parse_datetime.py"]='["20190723121212"]' # OK
# arr["target_int/lib_int/smtpd_parseargs.py"]='["",""]' # OK
# arr["target_int/lib_int/wsgiref_check_status.py"]='[""]' # OK
# --------------------------------------------------------------------
# arr["test/xss/make_server.py"]='[""]'
# arr["test/temp.py"]=[[0,0,0,0,0]]

for key in ${!arr[@]}; do
    echo "============== current testcase =============:" ${key} ${arr[${key}]}
    if [ "${key}" = "target_int/leetcode_int/add_binary.py" ]; then
        ./py-conbyte.py ${key} "${arr[${key}]}" -s cvc4 -m 30 -t 3 --ss
    elif [ "${key}" = "target_int/lib_int/datetime__parse_hh_mm_ss_ff.py" ]; then
        ./py-conbyte.py ${key} "${arr[${key}]}" -s cvc4 -m 40 -t 3
    elif [ "${key}" = "target_int/leetcode_int/addStrings.py" ]; then
        ./py-conbyte.py ${key} "${arr[${key}]}" -s cvc4 -m 50 -t 3
    else
        ./py-conbyte.py ${key} "${arr[${key}]}" -s cvc4 -m 30 -t 3
    fi
done

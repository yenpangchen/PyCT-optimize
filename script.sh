#!/bin/bash

declare -A arr

# arr["test/build_in.py"]=[5,2] # assert radd in integer because of sum
# arr["test/call_obj.py"]=[5,2] # OK
# arr["test/do_abs.py"]=[5,2] # OK
# arr["test/do_array.py"]=[5,2] # OK
# arr["test/do_numbers.py"]=[5,2] # OK
# arr["test/do_range.py"]=[5,2] # assert sub in integer because of range
# arr["test/list_dict.py"]=[5,2] # OK
# arr["test/loop.py"]=[5,2] # OK
# arr["test/while_loop.py"]=[5,2] # OK
# arr["test/sub_import.py"]=
# arr["test/sub_sub_import.py"]=
# arr["test/d_import.py"]=
# --------------------------------------------------------------------
# arr["test/strings/string_find.py"]='["a","b"]' # OK
# arr["test/strings/string_in.py"]='["a","b"]' # OK
# arr["test/strings/string_iter.py"]='["a","b"]' # for ch in string
# arr["test/strings/string_others.py"]='["a","b"]' # lower in string, count in string, split in string
# arr["test/strings/string_replace.py"]='["a","b"]' # OK
# arr["test/strings/string_slice.py"]='["a","b"]' # OK
# arr["test/strings/string_startswith.py"]='["a","b"]' # OK
# --------------------------------------------------------------------
# arr["test/targets/count_emma.py"]='["EMMA"]' # assert le in integer because of range
# arr["test/targets/multiplication_or_sum.py"]=[5,2] # OK
# arr["test/targets/regex.py"]='["a"]' # not implement rsub in integer
# --------------------------------------------------------------------
# arr["test/targets/leetcode/add_digits.py"]=[52] # OK
# arr["test/targets/leetcode/findUnsortedSubarray.py"]=
# arr["test/targets/leetcode/fraction_to_decimal.py"]=[-50,8] # __str__ in integer because of circular import
# arr["test/targets/leetcode/isLongPressedName.py"]='["",""]' # for ch in string
# arr["test/targets/leetcode/numDecodings.py"]='["226"]' # rmul in ??? (還沒實作 concolic list)
# arr["test/targets/leetcode/restoreIpAddresses.py"]='["25525511135"]' # assert sub in integer because of range, get_slice in string
# arr["test/targets/leetcode/reverseCheck.py"]=[0] # OK
# arr["test/targets/leetcode/substring.py"]='[""]' # 答案錯 ???
# arr["test/targets/leetcode/substring2.py"]='[""]' # 答案錯 ???
# arr["test/targets/leetcode/ugly_number.py"]=[0] # OK
# --------------------------------------------------------------------
# arr["target_int/leetcode_int/add_binary.py"]='["0","0"]' # __int__ in string, 以及為什麼要 ss 選項呢?
# arr["target_int/leetcode_int/addStrings.py"]='["923","123"]' # __int__ in string
# arr["target_int/leetcode_int/numDecodings.py"]='["226"]' # rmul in ??? (還沒實作 concolic list)
# arr["target_int/leetcode_int/restoreIpAddresses.py"]='["25525511135"]' # sub in integer because of range, get_slice in string
# arr["target_int/leetcode_int/validIPAddress.py"]='["172.16.254.1"]' # split in string
# arr["target_int/leetcode_int/validWordAbbreviation.py"]='["internationalization","i12iz4n"]' # assert le in integer because of range, sub in integer because of range, __str__ in integer because of circular import
# --------------------------------------------------------------------
# arr["target_int/lib_int/datetime__parse_hh_mm_ss_ff.py"]='["12:01:23.123456"]' # sub in integer because of range, __int__ in string
# arr["target_int/lib_int/datetime__parse_isoformat_date.py"]='["2019-07-19"]' # __int__ in string, 答案的比對還沒實作 list
# arr["target_int/lib_int/distutils_get_build_version.py"]='["MSC v.1212 abc"]' # split in string
# arr["target_int/lib_int/email__parsedate_tz.py"]='["Mon, 16 Nov 2009 13:32:02 +0100"]' # split in string
# arr["target_int/lib_int/http_parse_request.py"]='["HTTP/1.0"]' # split in string
# arr["target_int/lib_int/ipaddress__ip_int_from_string.py"]='["25525511135"]' # split in string, ipv6 cannot run
# arr["target_int/lib_int/nntplib__parse_datetime.py"]='["20190723121212"]' # __int__ in string
# arr["target_int/lib_int/smtpd_parseargs.py"]='["localhost:8025","localhost:25"]' # OK
# arr["target_int/lib_int/wsgiref_check_status.py"]='["200 ok"]' # split in string

for key in ${!arr[@]}; do
    echo "============== current testcase =============:" ${key} ${arr[${key}]}
    ./py-conbyte.py -s cvc4 -m 30 -t 3 --input "${arr[${key}]}" ${key}
done

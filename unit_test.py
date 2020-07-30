#!/usr/bin/env python3
import os, sys, unittest
import conbyte.explore, conbyte.global_utils

class TestEndpoints(unittest.TestCase):
    def test_codes(self):
        for fi in [
                    ("test/build_in.py", [0,0]), # OK
                    ("test/call_obj.py", [0,0]), # OK with deadcode [11, 26]
                    ("test/do_abs.py", [0,0]), # OK
                    ("test/do_array.py", [0,0]), # OK
                    ("test/do_numbers.py", [0,0]), # OK
                    ("test/do_range.py", [0,0]), # OK
                    ("test/list_dict.py", [0,0]), # OK
                    ("test/loop.py", [0,0]), # OK
                    ("test/while_loop.py", [0,0]), # OK
                    # --------------------------------------------------------------------
                    ("test/strings/string_find.py", ["",""]), # OK
                    ("test/strings/string_in.py", ["",""]), # OK
                    ("test/strings/string_iter.py", ["",""]), # OK
                    ("test/strings/string_others.py", ["",""]), # OK
                    ("test/strings/string_replace.py", ["",""]), # OK
                    ("test/strings/string_slice.py", ["",""]), # OK
                    ("test/strings/string_startswith.py", ["",""]), # OK
                    # --------------------------------------------------------------------
                    ("test/targets/count_emma.py", [""]), # OK
                    ("test/targets/multiplication_or_sum.py", [0,0]), # OK with restriction by solver ability [6]
                    # ("test/targets/regex.py", [""]), # TODO
                    # --------------------------------------------------------------------
                    ("test/targets/lib/email__header_value_parser.py", [""]), # OK
                    # ("test/targets/lib/httplib2___negotiatehttp.py", [["1", "2", "3"]]), # TODO
                    # --------------------------------------------------------------------
                    ("test/targets/leetcode/add_digits.py", [0]), # OK
                    ("test/targets/leetcode/findUnsortedSubarray.py", [[]]), # OK
                    ("test/targets/leetcode/fraction_to_decimal.py", [-50,8]), # OK
                    ("test/targets/leetcode/isLongPressedName.py", ["",""]), # OK
                    ("test/targets/leetcode/numDecodings.py", [""]), # OK
                    ("test/targets/leetcode/restoreIpAddresses.py", ["25525511135"]), # OK
                    ("test/targets/leetcode/reverseCheck.py", [0]), # OK
                    ("test/targets/leetcode/substring.py", [""]), # OK
                    ("test/targets/leetcode/substring2.py", [""]), # OK
                    ("test/targets/leetcode/ugly_number.py", [0]), # OK
                    # --------------------------------------------------------------------
                    ("target_int/leetcode_int/add_binary.py", ["",""]), # OK
                    ("target_int/leetcode_int/addStrings.py", ["",""]), # OK
                    ("target_int/leetcode_int/numDecodings.py", [""]), # OK
                    ("target_int/leetcode_int/restoreIpAddresses.py", ["25525511135"]), # OK
                    # ("target_int/leetcode_int/validIPAddress.py", [""]), # TODO 本來就還不行
                    ("target_int/leetcode_int/validWordAbbreviation.py", ["",""]), # OK
                    # --------------------------------------------------------------------
                    ("target_int/lib_int/datetime__parse_hh_mm_ss_ff.py", [""]), # OK
                    ("target_int/lib_int/datetime__parse_isoformat_date.py", [""]), # OK
                    ("target_int/lib_int/distutils_get_build_version.py", ["MSC v.1212 abc"]), # OK with deadcode [26, 30]
                    # ("target_int/lib_int/email__parsedate_tz.py", ["Mon, 16 Nov 2009 13:32:02 +0100"]), # TODO 本來就還不行
                    ("target_int/lib_int/http_parse_request.py", ["HTTP/1.0"]), # OK
                    # ("target_int/lib_int/ipaddress__ip_int_from_string.py", [""]), # TODO 本來就還不行
                    ("target_int/lib_int/nntplib__parse_datetime.py", ["20190723121212"]), # OK
                    ("target_int/lib_int/smtpd_parseargs.py", ["",""]), # OK with deadcode [28, 35, 40]
                    ("target_int/lib_int/wsgiref_check_status.py", [""]), # OK
                    # --------------------------------------------------------------------
                    ("test/xss/make_server.py", [""]), # OK
                ]:
            with self.subTest(filename=fi[0], inputs=fi[1]):
                # 這邊又用到 fork 伎倆是因為 coverage 資料不知道為什麼無法初始化，
                # 這樣會造成不同 testcase 之間的評比互相混淆，所以暫時出此下策。
                import multiprocessing, os
                parent, child = multiprocessing.Pipe()
                pid = os.fork()
                if pid == 0: # child process
                    base_name = os.path.basename(fi[0])
                    sys.path.append(os.path.abspath(fi[0]).replace(base_name, ""))
                    module = base_name.replace(".py", "") # the 1st argument in the following constructor
                    conbyte.global_utils.engine = conbyte.explore.ExplorationEngine(module, None)
                    conbyte.global_utils.engine.explore('cvc4', fi[1], 100, 5)
                    _, _, missing_lines, _ = conbyte.global_utils.engine.coverage_statistics()
                    conbyte.global_utils.engine.coverage_data.erase()
                    child.send(missing_lines)
                    child.close()
                    os._exit(os.EX_OK)
                else:
                    missing_lines = parent.recv()
                    parent.close()
                    self.check_coverage(os.path.abspath(fi[0]), missing_lines)

    def check_coverage(self, abspath, missing_lines):
        if abspath.endswith("test/call_obj.py"):
            self.assertEqual(missing_lines, {abspath: [11, 26]})
        elif abspath.endswith("test/targets/multiplication_or_sum.py"):
            self.assertEqual(missing_lines, {abspath: [6]})
        elif abspath.endswith("target_int/lib_int/distutils_get_build_version.py"):
            self.assertEqual(missing_lines, {abspath: [26, 30]})
        elif abspath.endswith("target_int/lib_int/smtpd_parseargs.py"):
            self.assertEqual(missing_lines, {abspath: [28, 35, 40]})
        else:
            self.assertFalse(missing_lines)

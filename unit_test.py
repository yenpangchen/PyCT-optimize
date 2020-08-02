#!/usr/bin/env python3
import unittest
import conbyte.explore

class TestCodeSnippets(unittest.TestCase):
    def test_01(self): self._execute("test/build_in.py", [0, 0]) # OK
    def test_02(self): self._execute("test/call_obj.py", [0, 0]) # OK with deadcode [11, 26]
    def test_03(self): self._execute("test/do_abs.py", [0, 0]) # OK
    def test_04(self): self._execute("test/do_array.py", [0, 0]) # OK
    def test_05(self): self._execute("test/do_numbers.py", [0, 0]) # OK
    def test_06(self): self._execute("test/do_range.py", [0, 0]) # OK
    def test_07(self): self._execute("test/list_dict.py", [0, 0]) # OK
    def test_08(self): self._execute("test/loop.py", [0, 0]) # OK
    def test_09(self): self._execute("test/while_loop.py", [0, 0]) # OK
    def test_10(self): self._execute("test/strings/string_find.py", ["", ""]) # OK
    def test_11(self): self._execute("test/strings/string_in.py", ["", ""]) # OK
    def test_12(self): self._execute("test/strings/string_iter.py", ["", ""]) # OK
    def test_13(self): self._execute("test/strings/string_others.py", ["", ""]) # OK
    def test_14(self): self._execute("test/strings/string_replace.py", ["", ""]) # OK
    def test_15(self): self._execute("test/strings/string_slice.py", ["", ""]) # OK
    def test_16(self): self._execute("test/strings/string_startswith.py", ["", ""]) # OK
    def test_17(self): self._execute("test/targets/count_emma.py", [""]) # OK
    def test_18(self): self._execute("test/targets/multiplication_or_sum.py", [0, 0]) # OK with restriction by solver ability [6]
    # def test_19(self): self._execute("test/targets/regex.py", [""]) # TODO
    def test_20(self): self._execute("test/targets/lib/email__header_value_parser.py", [""]) # OK
    # def test_21(self): self._execute("test/targets/lib/httplib2___negotiatehttp.py", [["1", "2", "3"]]) # TODO
    def test_22(self): self._execute("test/targets/leetcode/add_digits.py", [0]) # OK
    def test_23(self): self._execute("test/targets/leetcode/findUnsortedSubarray.py", [[0]]) # OK
    def test_24(self): self._execute("test/targets/leetcode/fraction_to_decimal.py", [-50, 8]) # OK
    def test_25(self): self._execute("test/targets/leetcode/isLongPressedName.py", ["", ""]) # OK
    def test_26(self): self._execute("test/targets/leetcode/numDecodings.py", [""]) # OK
    def test_27(self): self._execute("test/targets/leetcode/restoreIpAddresses.py", ["25525511135"]) # OK
    def test_28(self): self._execute("test/targets/leetcode/reverseCheck.py", [0]) # OK
    def test_29(self): self._execute("test/targets/leetcode/substring.py", [""]) # OK
    def test_30(self): self._execute("test/targets/leetcode/substring2.py", [""]) # OK
    def test_31(self): self._execute("test/targets/leetcode/ugly_number.py", [0]) # OK
    def test_32(self): self._execute("target_int/leetcode_int/add_binary.py", ["", ""]) # OK
    def test_33(self): self._execute("target_int/leetcode_int/addStrings.py", ["", ""]) # OK
    def test_34(self): self._execute("target_int/leetcode_int/numDecodings.py", [""]) # OK
    def test_35(self): self._execute("target_int/leetcode_int/restoreIpAddresses.py", [""]) # OK
    # def test_36(self): self._execute("target_int/leetcode_int/validIPAddress.py", [""]) # TODO 本來就還不行
    def test_37(self): self._execute("target_int/leetcode_int/validWordAbbreviation.py", ["", ""]) # OK
    def test_38(self): self._execute("target_int/lib_int/datetime__parse_hh_mm_ss_ff.py", [""]) # OK
    def test_39(self): self._execute("target_int/lib_int/datetime__parse_isoformat_date.py", [""]) # OK
    def test_40(self): self._execute("target_int/lib_int/distutils_get_build_version.py", ["MSC v.1212 abc"]) # OK with deadcode [26, 30]
    # def test_41(self): self._execute("target_int/lib_int/email__parsedate_tz.py", ["Mon, 16 Nov 2009 13:32:02 +0100"]) # TODO 本來就還不行
    def test_42(self): self._execute("target_int/lib_int/http_parse_request.py", ["HTTP/1.0"]) # OK
    # def test_43(self): self._execute("target_int/lib_int/ipaddress__ip_int_from_string.py", [""]) # TODO 本來就還不行
    def test_44(self): self._execute("target_int/lib_int/nntplib__parse_datetime.py", ["20190723121212"]) # OK (備註：每數次獨立測試中會有一次是失誤的，即便固定 random-seed 也是一樣)
    def test_45(self): self._execute("target_int/lib_int/smtpd_parseargs.py", ["", ""]) # OK with deadcode [28, 35, 40]
    def test_46(self): self._execute("target_int/lib_int/wsgiref_check_status.py", [""]) # OK
    def test_47(self): self._execute("test/xss/make_server.py", [""]) # OK

    def _execute(self, filename, inputs):
        self.iteration_max = 3
        engine = conbyte.explore.ExplorationEngine()
        iteration = 0
        while iteration == 0 or self._check_coverage(iteration, filename, missing_lines):
            engine.explore('cvc4', filename, None, inputs, 100, 5)
            _, _, missing_lines, _ = engine.coverage_statistics()
            print(filename, list(zip(engine.inputs, engine.results)))
            iteration += 1

    def _check_coverage(self, iteration, filename, missing_lines):
        if missing_lines: # we only care about the main file
            missing_lines = list(missing_lines.values())[0]
        status = True
        if filename == "test/call_obj.py":
            status &= self.assert_equal(iteration, missing_lines, [11, 26])
        elif filename == "test/targets/multiplication_or_sum.py":
            status &= self.assert_equal(iteration, missing_lines, [6])
        elif filename == "target_int/lib_int/distutils_get_build_version.py":
            status &= self.assert_equal(iteration, missing_lines, [26, 30])
        elif filename == "target_int/lib_int/smtpd_parseargs.py":
            status &= self.assert_equal(iteration, missing_lines, [28, 35, 40])
        else:
            status &= self.assert_false(iteration, missing_lines)
        return not (iteration == self.iteration_max or status) # termination condition

    def assert_equal(self, iteration, a, b):
        if iteration == self.iteration_max: self.assertEqual(a, b)
        return a == b

    def assert_false(self, iteration, a):
        if iteration == self.iteration_max: self.assertFalse(a)
        return not a

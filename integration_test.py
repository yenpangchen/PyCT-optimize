#!/usr/bin/env python3
import os, subprocess, unittest
import conbyte.explore

class TestCodeSnippets(unittest.TestCase):
    dump = bool(os.environ.get('dump', False))
    def test_01(self): self._execute('01', "test", "build_in", [0, 0]) # OK
    def test_02(self): self._execute('02', "test", "call_obj", [0, 0]) # OK with deadcode [11, 26]
    def test_03(self): self._execute('03', "test", "do_abs", [0, 0]) # OK
    def test_04(self): self._execute('04', "test", "do_array", [0, 0]) # OK
    def test_05(self): self._execute('05', "test", "do_numbers", [0, 0]) # OK
    def test_06(self): self._execute('06', "test", "do_range", [0, 0]) # OK
    def test_07(self): self._execute('07', "test", "list_dict", [0, 0]) # OK
    def test_08(self): self._execute('08', "test", "loop", [0, 0]) # OK
    def test_09(self): self._execute('09', "test", "while_loop", [0, 0]) # OK
    def test_10(self): self._execute('10', "test/strings", "string_find", ["", ""]) # OK
    def test_11(self): self._execute('11', "test/strings", "string_in", ["", ""]) # OK
    def test_12(self): self._execute('12', "test/strings", "string_iter", ["", ""]) # OK
    def test_13(self): self._execute('13', "test/strings", "string_others", ["", ""]) # OK
    def test_14(self): self._execute('14', "test/strings", "string_replace", ["", ""]) # OK
    def test_15(self): self._execute('15', "test/strings", "string_slice", ["", ""]) # OK
    def test_16(self): self._execute('16', "test/strings", "string_startswith", ["", ""]) # OK
    def test_17(self): self._execute('17', "test/targets", "count_emma", [""]) # OK
    def test_18(self): self._execute('18', "test/targets", "multiplication_or_sum", [0, 0]) # OK with restriction by solver ability [6]
    def test_19(self): self._execute('19', "test/targets", "regex", [""]) # TODO
    def test_20(self): self._execute('20', "test/targets/lib", "email__header_value_parser", [""]) # OK
    def test_21(self): self._execute('21', "test/targets/lib", "httplib2___negotiatehttp", [["1", "2", "3"]]) # TODO: We currently do not support concolic lists.
    def test_22(self): self._execute('22', "test/targets/leetcode", "add_digits", [0]) # OK
    def test_23(self): self._execute('23', "test/targets/leetcode", "findUnsortedSubarray", [[0]]) # TODO: We currently do not support concolic lists.
    def test_24(self): self._execute('24', "test/targets/leetcode", "fraction_to_decimal", [2, 3]) # OK (but [0,0] cannot lead to full coverage...)
    def test_25(self): self._execute('25', "test/targets/leetcode", "isLongPressedName", ["", ""]) # OK
    def test_26(self): self._execute('26', "test/targets/leetcode", "numDecodings", [""]) # OK
    def test_27(self): self._execute('27', "test/targets/leetcode", "restoreIpAddresses", [""]) # OK
    def test_28(self): self._execute('28', "test/targets/leetcode", "reverseCheck", [0]) # OK
    def test_29(self): self._execute('29', "test/targets/leetcode", "substring", [""]) # OK
    def test_30(self): self._execute('30', "test/targets/leetcode", "substring2", [""]) # OK
    def test_31(self): self._execute('31', "test/targets/leetcode", "ugly_number", [0]) # OK
    def test_32(self): self._execute('32', "test/target_int/leetcode_int", "add_binary", ["", ""]) # OK
    def test_33(self): self._execute('33', "test/target_int/leetcode_int", "addStrings", ["", ""]) # OK
    def test_34(self): self._execute('34', "test/target_int/leetcode_int", "numDecodings", [""]) # OK
    def test_35(self): self._execute('35', "test/target_int/leetcode_int", "restoreIpAddresses", [""]) # OK
    def test_36(self): self._execute('36', "test/target_int/leetcode_int", "validIPAddress", [""]) # TODO 本來就還不行
    def test_37(self): self._execute('37', "test/target_int/leetcode_int", "validWordAbbreviation", ["", ""]) # OK
    def test_38(self): self._execute('38', "test/target_int/lib_int", "datetime__parse_hh_mm_ss_ff", [""]) # OK
    def test_39(self): self._execute('39', "test/target_int/lib_int", "datetime__parse_isoformat_date", [""]) # OK
    def test_40(self): self._execute('40', "test/target_int/lib_int", "distutils_get_build_version", ["MSC v.1212 abc"]) # OK with deadcode [26, 30], but [""] cannot lead to full coverage...
    def test_41(self): self._execute('41', "test/target_int/lib_int", "email__parsedate_tz", ["Mon, 16 Nov 2009 13:32:02 +0100"]) # TODO 本來就還不行
    def test_42(self): self._execute('42', "test/target_int/lib_int", "http_parse_request", [""]) # OK
    def test_43(self): self._execute('43', "test/target_int/lib_int", "ipaddress__ip_int_from_string", [""]) # TODO 本來就還不行
    def test_44(self): self._execute('44', "test/target_int/lib_int", "nntplib__parse_datetime", ["000000000000"]) # OK, at least 11 digits for avoiding errors, and 12 digits for full coverage
    def test_45(self): self._execute('45', "test/target_int/lib_int", "smtpd_parseargs", ["", ""]) # OK with deadcode [28, 35, 40]
    def test_46(self): self._execute('46', "test/target_int/lib_int", "wsgiref_check_status", [""]) # OK
    def test_47(self): self._execute('47', "test/feature", "read_str_from_file", ["", ""]) # OK
    # def test_48(self): self._executesrv('48', "test.realworld.rpyc.client", [0]) # OK
    def test_49(self): self._execute('49', "test/realworld", "docxmlrpcserver", ["", "", ""]) # OK

    # def _executesrv(self, _id, modpath, inputs):
    #     pid = subprocess.Popen(["python3", "test/realworld/rpyc/server.py"]).pid
    #     import time; time.sleep(1) # this short wait is very important!!! (for the client to connect)
    #     self._execute(_id, modpath, inputs)
    #     os.system(f'kill -KILL {pid}')

    def _execute(self, _id, root, modpath, inputs):
        if not self._omit(_id):
            self.iteration_max = 1
            engine = conbyte.explore.ExplorationEngine()
            iteration = 0
            while iteration == 0 or self._check_coverage(iteration, _id, missing_lines):
                engine.explore(modpath, inputs, root=root, deadcode=self._missing_lines(modpath))
                total_lines, executed_lines, missing_lines = engine.coverage_statistics() # missing_lines: dict
                iteration += 1
            col_3 = str(list(zip(engine.inputs, engine.results)))[1:-1]
            print(modpath + ':', col_3)
        if self.dump: # Logging output section
            if self._omit(_id):
                with open(f'{_id}.csv', 'w') as f:
                    f.write(f'{_id}|-|-|-\n')
            else:
                col_1 = "{}/{} ({:.2%})".format(executed_lines, total_lines, (executed_lines/total_lines) if total_lines > 0 else 0)
                col_2 = str(sorted(list(missing_lines.values())[0]) if missing_lines else '')
                if col_2 == str(sorted(self._missing_lines(modpath))):
                    col_1 += ' >> (100.00%)' #; col_2 += ' (dead code)'
                with open(f'{_id}.csv', 'w') as f:
                    f.write(f'{_id}|{col_1}|{col_2}|{col_3}\n')

    def _omit(self, _id):
        return _id in ('19', '21', '23', '36', '41', '43')

    @staticmethod
    def _missing_lines(_id):
        if _id == "02":
            return {11, 26}
        if _id == "18":
            return {6}
        if _id == "40":
            return {26, 30}
        if _id == "45":
            return {28, 35, 40}
        return {} # empty dictionary

    def _check_coverage(self, iteration, _id, missing_lines: dict):
        if missing_lines: # we only care about the primary file
            missing_lines = list(missing_lines.values())[0]
        status = self.assert_equal(iteration, missing_lines, self._missing_lines(_id))
        return not (iteration == self.iteration_max or status) # := not (termination condition)

    def assert_equal(self, iteration, a, b):
        if iteration == self.iteration_max: self.assertEqual(a, b)
        return a == b

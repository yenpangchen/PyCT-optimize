#!/usr/bin/env python3
import os, subprocess, unittest
import conbyte.explore

class TestCodeSnippets(unittest.TestCase):
    dump = bool(os.environ.get('dump', False))
    def test_01(self): self._execute('01', "test", "abs_test", {'a':0, 'b':0}) # OK
    def test_02(self): self._execute('02', "test", "andor", {'x':0, 'y':0}) # OK
    def test_03(self): self._execute('03', "test", "arrayindex2", {'i':0}) # OK
    def test_04(self): self._execute('04', "test", "bad_eq", {'i':0}) # OK
    def test_05(self): self._execute('05', "test", "bignum", {'a':0}) # OK
    def test_06(self): self._execute('06', "test", "binary_search", {'k':0}, {9, 14}) # OK
    def test_07(self): self._execute('07', "test", "bitwidth", {'a':0, 'b':0}, {3}) # OK
    # def test_08(self): self._execute('08', "test", "complex", {'x':0, 'y':0}) # TODO
    def test_09(self): self._execute('09', "test", "cseppento1", {'x':0, 'y':0}, {14, 19}) # OK
    def test_10(self): self._execute('10', "test", "cseppento2", {'a':0, 'b':0}, {5}) # OK
    def test_11(self): self._execute('11', "test", "cseppento3", {'x':0}) # OK
    def test_12(self): self._execute('12', "test", "decorator_dict", {'d':{42:6}}, {8}) # TODO: dict type is not supported yet
    def test_13(self): self._execute('13', "test", "decorator", {'a':0, 'b':0, 'c':0}) # OK
    def test_14(self): self._execute('14', "test", "diamond", {'x':0, 'y':0, 'z':0}) # OK
    def test_15(self): self._execute('15', "test", "dict", {'x':0}) # OK
    def test_16(self): self._execute('16', "test", "dictionary", {'in1':0}) # OK
    def test_17(self): self._execute('17', "test", "elseif", {'in1':0}, {26}) # OK
    def test_18(self): self._execute('18', "test", "expand", {'in1':0, 'in2':0}) # OK
    def test_19(self): self._execute('19', "test", "expressions", {'in1':0, 'in2':0}, {9}) # TODO: CVC4 cannot solve (in1) * (in2 + 47) == 53
    def test_20(self): self._execute('20', "test", "filesys", {'x':0}, {18, 20}) # OK
    def test_21(self): self._execute('21', "test", "gcd", {'x':0, 'y':0}, {69}) # OK
    def test_22(self): self._execute('22', "test", "hashval", {'key':0}, {12}) # OK
    def test_23(self): self._execute('23', "test", "len_test", {'a':0}) # OK
    def test_24(self): self._execute('24', "test", "list", {'a':0, 'b':0}) # OK
    def test_25(self): self._execute('25', "test", "logical_op", {'in1':0, 'in2':0}, {5,6,8,12}) # TODO: logical operator is not supported yet
    def test_26(self): self._execute('26', "test", "loop", {'in1':0, 'in2':0}, {5}) # OK
    def test_27(self): self._execute('27', "test", "many_branches", {'in1':0, 'in2':0, 'in3':0}, {29}) # OK
    def test_28(self): self._execute('28', "test", "maxtest", {'a':0, 'b':0, 'c':0, 'd':0}, {16}) # OK
    def test_29(self): self._execute('29', "test", "mod", {'x':0, 'y':0}) # OK
    def test_30(self): self._execute('30', "test", "modulo", {'in1':0}) # OK
    def test_31(self): self._execute('31', "test", "modulo2", {'in1':0}) # OK
    def test_32(self): self._execute('32', "test", "mult_assmt", {'in1':0, 'in2':0, 'in3':0}) # OK
    def test_33(self): self._execute('33', "test", "polyspace", {'i':0}, {14}) # OK
    def test_34(self): self._execute('34', "test", "power", {'x':0}, {10}) # TODO: CVC4 cannot solve (x+2) ** 2 == 4
    def test_35(self): self._execute('35', "test", "power2", {'x':0}, {9}) # OK
    def test_36(self): self._execute('36', "test", "powtest", {'in1':0}, {6}) # OK
    def test_37(self): self._execute('37', "test", "reverse", {'x':0}) # OK
    def test_38(self): self._execute('38', "test", "set", {'x':0}) # OK
    def test_39(self): self._execute('39', "test", "shallow_branches", {'in1':0, 'in2':0, 'in3':0, 'in4':0, 'in5':0}) # OK
    def test_40(self): self._execute('40', "test", "simple", {'x':0}) # OK
    def test_41(self): self._execute('41', "test", "swap", {'in1':0, 'in2':0}, {10}) # OK
    def test_42(self): self._execute('42', "test", "tuplecmp", {'a0':0, 'a1':0, 'b0':0, 'b1':0}) # OK
    def test_43(self): self._execute('43', "test", "unnecessary_condition", {'in1':0, 'in2':0}, {5}) # OK
    def test_44(self): self._execute('44', "test", "unnecessary_condition2", {'in1':0, 'in2':0}, {6}) # OK
    def test_45(self): self._execute('45', "test", "unnecessary_condition3", {'in1':0}) # OK
    def test_46(self): self._execute('46', "test", "unnecessary_condition4", {'in1':0}) # OK
    def test_47(self): self._execute('47', "test", "weird", {'x':0, 'y':0}) # OK
    def test_48(self): self._execute('48', "test", "whileloop", {'x':0}) # OK
    def test_49(self): self._execute('49', "test/cvc", "effectivebool", {'string':'', 'num':0}) # OK
    def test_50(self): self._execute('50', "test/cvc", "emptystr", {'s':''}) # OK
    def test_51(self): self._execute('51', "test/cvc", "escape", {'string':''}) # OK
    def test_52(self): self._execute('52', "test/cvc", "none", {'c':0}, {7}) # OK
    def test_53(self): self._execute('53', "test/cvc", "strcontains", {'s':''}) # OK
    def test_54(self): self._execute('54', "test/cvc", "strcount", {'s':''}) # OK
    def test_55(self): self._execute('55', "test/cvc", "strfind", {'s':''}) # OK
    def test_56(self): self._execute('56', "test/cvc", "strfindbeg", {'s':''}) # OK
    def test_57(self): self._execute('57', "test/cvc", "strindex", {'s':''}) # OK
    def test_58(self): self._execute('58', "test/cvc", "stringadd", {'s':''}) # OK
    def test_59(self): self._execute('59', "test/cvc", "stringtest", {'s':''}) # OK
    def test_60(self): self._execute('60', "test/cvc", "strmiddle", {'s':''}) # OK
    def test_61(self): self._execute('61', "test/cvc", "strreplace", {'s':''}) # OK
    def test_62(self): self._execute('62', "test/cvc", "strslice", {'s':''}) # OK
    def test_63(self): self._execute('63', "test/cvc", "strsplit", {'s':''}) # OK
    def test_64(self): self._execute('64', "test/cvc", "strstartswith", {'s':''}) # OK
    def test_65(self): self._execute('65', "test/cvc", "strstrip", {'s':''}) # OK
    def test_66(self): self._execute('66', "test/cvc", "strsubstring", {'s':''}) # OK
    def test_67(self): self._execute('67', "fail", "arrayindex", {'i':0}, {13}) # TODO: still not able to pick another list element
    def test_68(self): self._execute('67', "fail", "dictbool", {'d':{}}, {8}) # TODO: dict type is not supported yet
    def test_69(self): self._execute('69', "fail", "divzero", {'in1':0, 'in2':0}, {10}) # OK
    def test_70(self): self._execute('70', "fail", "git", {'a':0, 'b':0}) # OK
    def test_71(self): self._execute('71', "fail", "pow", {'x':0}, {7}) # TODO: CVC4 cannot solve 4 == x**2
    def test_72(self): self._execute('72', "fail", "sqrttest", {'in1':0}, {8,9,10}) # TODO: sqrt is still handled concretely

    def _execute(self, _id, root, modpath, inputs, _missing_lines=set(), *, lib=None):
        if not self._omit(_id):
            self.iteration_max = 1
            engine = conbyte.explore.ExplorationEngine()
            iteration = 0
            while iteration == 0 or self._check_coverage(iteration, _missing_lines, missing_lines):
                engine.explore(modpath, inputs, root='../PyExZ3/' + root, deadcode=_missing_lines, include_exception=True, lib='../PyExZ3/', file_as_total=False)
                total_lines, executed_lines, missing_lines = engine.coverage_statistics() # missing_lines: dict
                iteration += 1
                # print(total_lines, executed_lines, missing_lines)
            col_3 = str(list(map(lambda x: (list(x[0].values()), x[1]), engine.in_out)))[1:-1]
            print(modpath + ':', col_3)
            print(modpath + ':', _missing_lines)
        if self.dump: # Logging output section
            if self._omit(_id):
                with open(f'{_id}.csv', 'w') as f:
                    f.write(f'{_id}|-|-|-\n')
            else:
                col_1 = "{}/{} ({:.2%})".format(executed_lines, total_lines, (executed_lines/total_lines) if total_lines > 0 else 0)
                col_2 = str(sorted(list(missing_lines.values())[0]) if missing_lines else '')
                if col_2 == str(sorted(_missing_lines)):
                    col_1 += ' >> (100.00%)' #; col_2 += ' (dead code)'
                with open(f'{_id}.csv', 'w') as f:
                    f.write(f'{_id}|{col_1}|{col_2}|{col_3}\n')

    def _omit(self, _id):
        return False #_id in ('19', '21', '23', '36', '41', '43')

    def _check_coverage(self, iteration, _missing_lines, missing_lines: dict):
        if missing_lines: # we only care about the primary file
            missing_lines = list(missing_lines.values())[0]
        else:
            missing_lines = set()
        status = self.assert_equal(iteration, missing_lines, _missing_lines)
        return not (iteration == self.iteration_max or status) # := not (termination condition)

    def assert_equal(self, iteration, a, b):
        if iteration == self.iteration_max: self.assertEqual(a, b) # self.assertTrue(a.issubset(b))
        return a == b

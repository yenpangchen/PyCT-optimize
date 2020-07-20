import logging
import time
import os
from subprocess import Popen, PIPE, STDOUT
from hashlib import sha224
import subprocess
from string import Template

log = logging.getLogger("ct.solver")

class Solver(object):
    options = {"lan": "smt.string_solver=z3str3", "stdin": "-in"}
    cvc_options = ["--produce-models", "--lang", "smt", "--quiet", "--strings-exp"]
    cnt = 0

    def __init__(self, query_store, solver_type, ss):
        self.query = None
        self.asserts = None
        self.prefix = None
        self.ending = None
        self.variables = dict()
        self.query_store = query_store
        self.solver_type = solver_type
        self.ss = ss

        if solver_type == "z3seq":
            self.cmd = "z3 -in"
        elif solver_type == "z3str":
            self.cmd = "z3"
            for option in self.options:
                self.cmd = self.cmd + " " + self.options[option]
        elif solver_type == "trauc":
            self.cmd = "trauc"
            for option in self.options:
                self.cmd = self.cmd + " " + self.options[option]
        elif solver_type == "cvc4":
            self.cmd = "cvc4"
            for option in self.cvc_options:
                self.cmd = self.cmd + " " + option



    def set_variables(self, variables):
        self.varables = variables
        for v in variables:
            self.variables[v] = variables[v]


    def find_constraint_model(self, constraint, extend_vars, extend_queries, timeout=None):
        start_time = time.process_time()
        if "z3" in self.solver_type or  "trauc" in self.solver_type:
            if timeout is not None:
                cmd = self.cmd + " -T:" + str(timeout)
            else:
                cmd = self.cmd + " -T:1"
        else:
            if timeout is not None:
                cmd = self.cmd + (" --tlimit=%s" % (int(timeout) * 1000))
            else:
                cmd = self.cmd + " --tlimit=1000"
        self.asserts, self.query = constraint.get_asserts_and_query()
        model = self._find_model(cmd, extend_vars, extend_queries)
        endtime = time.process_time()
        solve_time = endtime - start_time
        return model


    def _find_model(self, cmd, extend_vars, extend_queries):

        formulas = self._build_expr(extend_vars, extend_queries)

        # log.debug("\n" + formulas)
        if self.query_store is not None:
            #smthash = sha224(bytes(str(self.query), 'UTF-8')).hexdigest()
            #filename = os.path.join(self.query_store, "{}.smt2".format(smthash))
            filename = os.path.join(self.query_store, "{}.smt2".format(self.cnt))
            with open(filename, 'w') as f:
                f.write(formulas)

        model = None
        try:
            process = Popen(cmd, shell=True, stdin=PIPE, stdout=PIPE, stderr=PIPE)
        except subprocess.CalledProcessError as e:
            print(e.output)

        # print(formulas)
        stdout, stderr = process.communicate(input=formulas.encode())

        log.debug("\n" + stdout.decode())

        output = stdout.decode()
        # if 'unknown' in output:
        #     print(formulas)
        #     print(output)

        if output is None or len(output) == 0:
            status = "UNKNOWN"
        else:
            output = output.splitlines()
            while "error" in output[0]:
                print('solver error:', output[0])
                print(formulas)
                quit()
                # output.pop(0)
            status = output[0].lower()
            if "unsat" in status:
                status = "UNSAT"
            elif "sat" in status:
                status = "SAT"
                model = self._get_model(output[1:])
            elif "timeout" in status:
                status = "TIMEOUT"
            elif "unknown" in status and "error" not in stdout.decode():
                model = self._get_model(output[1:])
            else:
                status = "UNKNOWN"

        log.debug("%s smt, Result: %s" % (self.cnt, status))
        self.cnt += 1
        return model

    ########################################################
    # Here are examples of expressions of lists of integers.
    # 1. (list (store (store ((as const (Array Int Int)) 0) 4 15) 2 5) 0)
    # 2. (list (store ((as const (Array Int Int)) 0) 2 (- 2)) 1)
    # 3. (list ((as const (Array Int Int)) 0) 0)
    ########################################################
    def _get_list_of_int(self, expr):
        ans_dict = dict()
        ans_default = None
        ans_len = None
        assert expr.startswith('(list ') and expr.endswith(')')
        expr = expr[6:-1] # take away '(list ' and ')'
        assert not expr.endswith(')') # to ensure that the length of a list is nonnegative
        ans_len = expr.split(' ')[-1]
        expr = expr[:-(len(ans_len)+1)] # take away the last number and the prepended whitespace
        ans_len = int(ans_len)
        while True:
            if expr.startswith('((as const (Array Int Int)) ') and expr.endswith(')'):
                expr = expr[1:-1] # take away '(' and ')'
                ans_default = int(expr.split(' ')[-1])
                break
            elif expr.startswith('(store ') and expr.endswith(')'):
                expr = expr[7:-1] # take away '(store ' and ')'
                # Ex1: (...) 1 (- 1)
                # Ex2: (...) 1 20
                temp = expr.split(' ')
                if not expr.endswith(')'):
                    key = temp[-2]
                    value = temp[-1]
                    expr = ' '.join(temp[:-2])
                else:
                    key = temp[-3]
                    value = ''.join(temp[-2:])[1:-1]
                    expr = ' '.join(temp[:-3])
                ans_dict[int(key)] = int(value)
            else:
                raise NotImplementedError
        ans_list = [ans_default] * ans_len
        for key, value in ans_dict.items():
            if key < len(ans_list):
                ans_list[key] = value
        return ans_list

    ########################################################
    # Here are examples of expressions of lists of strings.
    # 1. (list (store (store ((as const (Array Int String)) "") 0 "1""\\2) 3") 1 "45 6") 2)
    ########################################################
    def _get_list_of_str(self, expr):
        ans_dict = dict()
        ans_default = None
        ans_len = None
        assert expr.startswith('(list ') and expr.endswith(')')
        expr = expr[6:-1] # take away '(list ' and ')'
        assert not expr.endswith(')') # to ensure that the length of a list is nonnegative
        ans_len = expr.split(' ')[-1]
        expr = expr[:-(len(ans_len)+1)] # take away the last number and the prepended whitespace
        ans_len = int(ans_len)
        while True:
            if expr.startswith('((as const (Array Int String)) ') and expr.endswith(')'):
                expr = expr[1:-1] # take away '(' and ')'
                ans_default = expr.split(' ')[-1]
                break
            elif expr.startswith('(store ') and expr.endswith(')'):
                expr = expr[7:-1] # take away '(store ' and ')'
                # Ex1: (......) 0 "1\\2) 3"
                # Ex2: (......) 0 "1""\\2) 3"
                #      <--- i ---> temp[<= i] is computed as the left after the while loop.
                temp = expr.split('"')
                i = -1
                while len(temp[i]) == 0:
                    i -= 2
                value = '"'.join(temp[i+1:]).replace('""','"')
                key = int(temp[i].split(' ')[-2])
                expr = ' '.join('"'.join(temp[:i+1]).split(' ')[:-2])
                ans_dict[key] = value
                # In fact "temp" in this section can be simply "expr,"
                # but this leads to poor readability.
            else:
                raise NotImplementedError
        ans_list = [ans_default] * ans_len
        for key, value in ans_dict.items():
            if key < len(ans_list):
                ans_list[key] = value
        return ans_list

    def _get_model(self, models):
        model = dict()
        for line in models:
            assert line.startswith('((') and line.endswith('))')
            name, value = line[2:-2].split(" ", 1)
            if self.variables[name] == "Int":
                if "(" in value:
                    value = -int(value.replace("(", "").replace(")", "").split(" ")[1])
                else:
                    value = int(value)
            elif self.variables[name] == "String":
                assert value.startswith('"') and value.endswith('"')
                value = value[1:-1] # .replace("\"", "", 1).replace("\"", "", -1)
                value = value.replace('""', '"')
            elif self.variables[name] == "ListOfInt":
                value = self._get_list_of_int(value)
            elif self.variables[name] == "ListOfStr":
                value = self._get_list_of_str(value)
            else:
                raise NotImplementedError

            if name.startswith("_ARR_"):
                name = name.replace("_ARR_", "").split("_", 1)[1]
                if name not in model:
                    model[name] = list()
                model[name].append(value)
            else:
                model[name] = value
        return model


    def _build_expr(self, extend_vars, extend_queries):
        f_template = Template("""
$declarevars

$query

(check-sat)

$getvars
""")
        assignments = dict()
        assignments['declarevars'] = "\n"
        assignments['declarevars'] += "(declare-datatypes ((ListOfInt 0)) (((list (array (Array Int Int)) (__len__ Int)))))\n"
        assignments['declarevars'] += "(declare-datatypes ((ListOfStr 0)) (((list (array (Array Int String)) (__len__ Int)))))\n"

        for (name, var) in self.variables.items():
            # if var != "List":
            assignments['declarevars'] += "(declare-fun {} () {})\n".format(name, var)
            if var.startswith("List"):
                assignments['declarevars'] += "(assert (>= (__len__ {}) 0))\n".format(name)

        for (name, var) in extend_vars.items():
            assignments['declarevars'] += "(declare-fun {} () {})\n".format(name, var)

        assignments['query'] = "\n".join(assertion.get_formula() for assertion in self.asserts)
        assignments['query'] += self.query.get_formula()
        if self.ss:
            assignments['query'] += "(assert (str.in.re a (re.+ (re.range \"0\" \"1\"))))\n"
            assignments['query'] += "(assert (str.in.re b (re.+ (re.range \"0\" \"1\"))))\n"

        for query in extend_queries:
            assignments['query'] += "%s\n" % query

        assignments['getvars'] = "\n"
        for name, var in self.variables.items():
            # if var != "List":
            assignments['getvars'] += "(get-value ({}))\n".format(name)
        return f_template.substitute(assignments).strip()

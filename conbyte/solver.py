import logging, os, string, subprocess, sys
import conbyte.global_utils

log = logging.getLogger("ct.solver")

class Solver:
    options = {"lan": "smt.string_solver=z3str3", "stdin": "-in"}
    cnt = 0 # for query_store

    @staticmethod
    def find_model_from_constraint(engine, solver, constraint, timeout=10, query_store=None):
        ######################################################################################
        # Build the command from the solver type
        if solver == "z3seq":
            cmd = "z3 -in".split(' ')
        elif solver == "z3str":
            cmd = ["z3"] + self.options.values()
        elif solver == "trauc":
            cmd = ["trauc"] + self.options.values()
        elif solver == "cvc4":
            cmd = ["cvc4"] + ["--produce-models", "--lang", "smt", "--quiet", "--strings-exp"]
        else:
            raise NotImplementedError
        ######################################################################################
        # Build the command from the timeout parameter
        if isinstance(timeout, str): timeout = int(timeout)
        assert isinstance(timeout, int)
        if "z3" in solver or  "trauc" in solver:
            cmd += ["-T:" + str(timeout)]
        else:
            timeout *= 1000
            cmd += ["--tlimit=" + str(timeout)]
        ######################################################################################
        formulas = Solver._build_formulas_from_constraint(engine, constraint)
        # print(formulas)
        ######################################################################################
        if query_store is not None:
            filename = os.path.join(query_store, f"{Solver.cnt}.smt2")
            with open(filename, 'w') as f:
                f.write(formulas)
        ######################################################################################
        try: completed_process = subprocess.run(cmd, input=formulas.encode(), capture_output=True)
        except subprocess.CalledProcessError as e: print(e.output)
        output = completed_process.stdout.decode()
        model = None
        if output is None or len(output) == 0:
            status = "UNKNOWN"
        else:
            outputs = output.splitlines()
            if "error" in outputs[0]:
                print('solver error:', outputs[0])
                print(formulas)
                sys.exit(1)
            status = outputs[0].lower()
            if "unsat" in status:
                status = "UNSAT"
            elif "sat" in status:
                status = "SAT"
                model = Solver._get_model(engine, outputs[1:])
            elif "timeout" in status:
                status = "TIMEOUT"
            elif "unknown" in status and "error" not in output:
                model = Solver._get_model(engine, outputs[1:])
            else:
                status = "UNKNOWN"
        log.debug("%s smt, Result: %s" % (Solver.cnt, status))
        Solver.cnt += 1
        return model

    ########################################################
    # Here are examples of expressions of lists of integers.
    # 1. (list (store (store ((as const (Array Int Int)) 0) 4 15) 2 5) 0)
    # 2. (list (store ((as const (Array Int Int)) 0) 2 (- 2)) 1)
    # 3. (list ((as const (Array Int Int)) 0) 0)
    ########################################################
    @staticmethod
    def _get_list_of_int(expr):
        ans_dict = {}
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
            if expr.startswith('(store ') and expr.endswith(')'):
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
    @staticmethod
    def _get_list_of_str(expr):
        ans_dict = {}
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
            if expr.startswith('(store ') and expr.endswith(')'):
                expr = expr[7:-1] # take away '(store ' and ')'
                # Ex1: (......) 0 "1\\2) 3"
                # Ex2: (......) 0 "1""\\2) 3"
                #      <--- i ---> temp[<= i] is computed as the left after the while loop.
                temp = expr.split('"')
                i = -1
                while len(temp[i]) == 0:
                    i -= 2
                value = '"'.join(temp[i+1:]).replace('""', '"')
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

    @staticmethod
    def _get_model(engine, models):
        model = {}
        for line in models:
            # print('LINE', line)
            assert line.startswith('((') and line.endswith('))')
            name, value = line[2:-2].split(" ", 1)
            if engine.var_to_types[name] == "Int":
                if "(" in value:
                    value = -int(value.replace("(", "").replace(")", "").split(" ")[1])
                else:
                    value = int(value)
            elif engine.var_to_types[name] == "String":
                assert value.startswith('"') and value.endswith('"')
                value = value[1:-1]
                value = value.replace('""', '"').replace("\\t", "\t").replace("\\n", "\n").replace("\\r", "\r").replace("\\\\", "\\")
                # Note the order above must be in reverse with its encoding method (line 18 in concolic_str.py)
            elif engine.var_to_types[name] == "ListOfInt":
                value = Solver._get_list_of_int(value)
            elif engine.var_to_types[name] == "ListOfStr":
                value = Solver._get_list_of_str(value)
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

    @staticmethod
    def _build_formulas_from_constraint(engine, constraint):
        asserts, query, extend_vars, extend_queries = constraint.get_asserts_and_query()
        declare_vars = "(declare-datatypes ((ListOfInt 0)) (((list (array (Array Int Int)) (__len__ Int)))))\n"
        declare_vars += "(declare-datatypes ((ListOfStr 0)) (((list (array (Array Int String)) (__len__ Int)))))\n"
        for (name, var) in engine.var_to_types.items():
            declare_vars += f"(declare-fun {name} () {var})\n"
            if var.startswith("List"):
                declare_vars += f"(assert (>= (__len__ {name}) 0))\n"
        for (name, var) in extend_vars.items():
            declare_vars += f"(declare-fun {name} () {var})\n"
        queries = "\n".join(assertion.get_formula() for assertion in asserts)
        queries += '\n' + query.get_formula() + '\n'
        queries += "\n".join(extend_queries)
        get_vars = "\n".join(f"(get-value ({name}))" for name in engine.var_to_types.keys())
        return f"\n{declare_vars}\n{queries}\n(check-sat)\n{get_vars}"

import logging, os, subprocess, sys
from conbyte.concolic import Concolic
from conbyte.predicate import Predicate
from conbyte.utils import py2smt

log = logging.getLogger("ct.solver")

class Solver:
    options = {"lan": "smt.string_solver=z3str3", "stdin": "-in"}
    cnt = 0 # for query_store

    @staticmethod
    def find_model_from_constraint(engine, solver, constraint, timeout=10, query_store=None):
        ######################################################################################
        # Build the command from the solver type
        if solver == "cvc4":
            cmd = ["cvc4"] + ["--produce-models", "--lang", "smt", "--quiet", "--strings-exp"]
        # elif solver == "z3seq":
        #     cmd = "z3 -in".split(' ')
        # elif solver == "z3str":
        #     cmd = ["z3"] + self.options.values()
        # elif solver == "trauc":
        #     cmd = ["trauc"] + self.options.values()
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
            # print(status)
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

    @staticmethod
    def _get_model(engine, models):
        model = {}
        for line in models:
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
                # Note the order above must be in reverse with its encoding method (line 18 in str.py)
            else:
                raise NotImplementedError
            model[name] = value
        return model

    @staticmethod
    def _build_formulas_from_constraint(engine, constraint):
        declare_vars = "\n".join(f"(declare-const {name} {_type})" for (name, _type) in engine.var_to_types.items())
        queries = "\n".join(assertion.get_formula() for assertion in constraint.get_all_asserts())
        get_vars = "\n".join(f"(get-value ({name}))" for name in engine.var_to_types.keys())
        return f"\n{declare_vars}\n{queries}\n(check-sat)\n{get_vars}"

    @staticmethod
    def _expr_has_engines_and_equals_value(expr, value):
        if e:=Concolic.find_engine_in_expr(expr):
            return e # This line is used to disable the value validation feature temporarily.
            cmd = ["cvc4", "--produce-models", "--lang", "smt", "--quiet", "--strings-exp", "--tlimit=5000"]
            if isinstance(value, float): # TODO: Floating point operations may cause subtle errors.
                formulas = f"(assert (and (<= (- (/ 1 1000000000000000)) (- {Predicate.get_formula_shallow(expr)} {py2smt(value)})) (<= (- {Predicate.get_formula_shallow(expr)} {py2smt(value)}) (/ 1 1000000000000000))))\n(check-sat)"
            else:
                formulas = f"(assert (= {Predicate.get_formula_shallow(expr)} {py2smt(value)}))\n(check-sat)"
            try: completed_process = subprocess.run(cmd, input=formulas.encode(), capture_output=True)
            except subprocess.CalledProcessError as e: print(e.output)
            try:
                if completed_process.stdout.decode().splitlines()[0] == 'sat': return e
                raise Exception # move to the following block
            except:
                print(formulas); print(completed_process.stdout.decode().splitlines()); print()
                import traceback; traceback.print_stack(); sys.exit(0)
        return None

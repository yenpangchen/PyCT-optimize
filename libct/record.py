import time

class ConcolicTestRecorder:
    def __init__(self):
        self.sat = []
        self.unsat = []
        self.unknown = []
        self.gen_constraint = []
        self.solve_constraint = []
        self.iter_wall_time = []
        self.iter_cpu_time = []
        self.execute_wall_time = []
        self.execute_cpu_time = []
        self.solve_constraint_wall_time = []
        self.solve_constraint_cpu_time = []
        
        self.total_wall_time = None
        self.total_cpu_time = None
        self.total_iter = None

        self._pre_sat = 0
        self._pre_unsat = 0
        self._pre_unk = 0


    def iter_start(self):
        self._iter_start_wall_time = time.time()        
        self._iter_start_cpu_time = time.process_time()


    def iter_end(self, solver_stats, solve_constr_num):
        self.iter_wall_time.append(time.time() - self._iter_start_wall_time)
        self.iter_cpu_time.append(time.process_time() - self._iter_start_cpu_time)

        self.solve_constraint.append(solve_constr_num)

        # sat, unsat, unknown
        self.sat.append(solver_stats['sat_number'] - self._pre_sat)
        self.unsat.append(solver_stats['unsat_number'] - self._pre_unsat)
        self.unknown.append(solver_stats['otherwise_number'] - self._pre_unk)

        self._pre_sat = solver_stats['sat_number']
        self._pre_unsat = solver_stats['unsat_number']
        self._pre_unk = solver_stats['otherwise_number']


    def execution_start(self):
        self._execute_wall_time = time.time()
        self._execute_cpu_time = time.process_time()

    def execution_end(self):
        self.execute_wall_time.append(time.time() - self._execute_wall_time)
        self.execute_cpu_time.append(time.process_time() - self._execute_cpu_time)
        

    def solve_constr_start(self):
        self._solve_wall_time = time.time()
        self._solve_cpu_time = time.process_time()

    def solve_constr_end(self):
        self.solve_constraint_wall_time.append(time.time() - self._solve_wall_time)
        self.solve_constraint_cpu_time.append(time.process_time() - self._solve_cpu_time)


    def start(self):
        self._start_wall_time = time.time()
        self._start_cpu_time = time.process_time()

    def end(self, iter):
        self.total_wall_time = time.time() - self._start_wall_time
        self.total_cpu_time = time.process_time() - self._start_cpu_time
        self.total_iter = iter


    def output_stats_dict(self):
        res = {
            "total": dict(),
            "iters": dict(),
        }

        res['total']['total_wall_time'] = self.total_wall_time
        res['total']['total_cpu_time'] = self.total_cpu_time
        res['total']['total_iter'] = self.total_iter


        res['iters']['sat'] = self.sat
        res['iters']['unsat'] = self.unsat
        res['iters']['unknown'] = self.unknown
        res['iters']['gen_constraint'] = self.gen_constraint
        res['iters']['solve_constraint'] = self.solve_constraint
        res['iters']['iter_wall_time'] = self.iter_wall_time
        res['iters']['iter_cpu_time'] = self.iter_cpu_time
        res['iters']['execute_wall_time'] = self.execute_wall_time
        res['iters']['execute_cpu_time'] = self.execute_cpu_time
        res['iters']['solve_constraint_wall_time'] = self.solve_constraint_wall_time
        res['iters']['solve_constraint_cpu_time'] = self.solve_constraint_cpu_time


        return res


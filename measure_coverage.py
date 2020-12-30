#!/usr/bin/env python3
import argparse, coverage, func_timeout, importlib, inspect, multiprocessing, os, pickle, signal, subprocess, sys, time

TIMEOUT = 15
parser = argparse.ArgumentParser(); parser.add_argument("mode"); parser.add_argument("project"); args = parser.parse_args()

if args.mode != '2':
    from conbyte.utils import get_module_from_rootdir_and_modpath
    from conbyte.utils import get_function_from_module_and_funcname
    import conbyte.explore; _complete_primitive_arguments = conbyte.explore.ExplorationEngine._complete_primitive_arguments
else:
    import symbolic.loader; get_funcobj_from_modpath_and_funcname = symbolic.loader.Loader.get_funcobj_from_modpath_and_funcname
    import symbolic.invocation; _complete_primitive_arguments = symbolic.invocation.FunctionInvocation._complete_primitive_arguments

rootdir = os.path.abspath(args.project) + '/'; lib = rootdir + '.venv/lib/python3.8/site-packages'
sys.path.insert(0, lib); sys.path.insert(0, rootdir); project_name = rootdir[:-1].split('/')[-1]

def f1(r0, r):
    if r0.poll(TIMEOUT + 5): # may get stuck here for some unknown reason
        return r.recv()

# cont = False
func_inputs = {}
coverage_data = coverage.CoverageData()
coverage_accumulated_missing_lines = {}
cov = coverage.Coverage(data_file=None, source=[rootdir], omit=['**/__pycache__/**', '**/.venv/**'])
start2 = time.time()
os.system(f'rm ./project_statistics/{project_name}/incomplete_functions.txt')
for dirpath, _, files in os.walk(f"./project_statistics/{project_name}"):
    for file in files:
        if file == 'inputs.pkl':
            try:
                with open(os.path.abspath(dirpath + '/' + file), 'rb') as f:
                    inputs = pickle.load(f)
            except: continue
            func_inputs[(dirpath.split('/')[-2], dirpath.split('/')[-1])] = inputs
            start = time.time()
            small_missing_lines = set(); our_filename = rootdir + dirpath.split('/')[-2].replace('.', '/') + '.py'; is_first = True
            for i in inputs:
                r, s = multiprocessing.Pipe(); r0, s0 = multiprocessing.Pipe()
                def child_process(is_first, small_missing_lines):
                    sys.dont_write_bytecode = True # same reason mentioned in the concolic environment
                    cov.start()
                    module = get_module_from_rootdir_and_modpath(rootdir, dirpath.split('/')[-2])
                    execute = get_function_from_module_and_funcname(module, dirpath.split('/')[-1])
                    print('currently measuring >>>', dirpath.split('/')[-2], dirpath.split('/')[-1])
                    pri_args, pri_kwargs = _complete_primitive_arguments(execute, i)
                    try:
                        func_timeout.func_timeout(TIMEOUT, execute, args=pri_args, kwargs=pri_kwargs)
                    except: pass
                    cov.stop(); coverage_data.update(cov.get_data())
                    if is_first:
                        small_missing_lines = set(cov.analysis(our_filename)[2])
                        is_first = False
                    else:
                        small_missing_lines = small_missing_lines.intersection(set(cov.analysis(our_filename)[2]))
                    for file in coverage_data.measured_files(): # "file" is absolute here.
                        _, _, missing_lines, _ = cov.analysis(file)
                        if file not in coverage_accumulated_missing_lines:
                            coverage_accumulated_missing_lines[file] = set(missing_lines)
                        else:
                            coverage_accumulated_missing_lines[file] = coverage_accumulated_missing_lines[file].intersection(set(missing_lines))
                    s0.send(0) # just a notification to the parent process that we're going to send data
                    s.send((coverage_data, coverage_accumulated_missing_lines, small_missing_lines, is_first, inspect.getsourcelines(execute)[0]))
                process = multiprocessing.Process(target=child_process, args=(is_first, small_missing_lines)); process.start()
                try: (coverage_data, coverage_accumulated_missing_lines, small_missing_lines, is_first, func_lines) = func_timeout.func_timeout(TIMEOUT + 5 + 1, f1, args=(r0, r))
                except: pass
                r.close(); s.close(); r0.close(); s0.close()
                if process.is_alive(): process.kill()
                if time.time() - start > 15 * 60: break
            # if time.time() - start2 > 3 * 60 * 60: break
            for i, e in enumerate(func_lines):
                if e.strip().startswith('def'):
                    offset = i
                    func_def = e[:-1]
                    break
            try: completed_process = subprocess.run(f"grep -Fn '{func_def}' {our_filename}", shell=True, capture_output=True) #, stdout=sys.stdout, stderr=sys.stderr)
            except subprocess.CalledProcessError as e: print(e.output)
            lb = int(completed_process.stdout.decode('utf-8').split(':')[0]) - offset
            ub = lb + len(func_lines) - 1
            mylist = sorted([x for x in small_missing_lines if lb <= x <= ub])
            with open(f'./project_statistics/{project_name}/incomplete_functions.txt', 'a') as fmf:
                try: n = min(mylist)
                except: n = 0
                fmf.write(f"{our_filename}:{n}, {func_def.strip()}, {mylist}, ./py-conbyte.py -r '/root/04_Python' '{our_filename[len('/root/04_Python/'):-len('.py')].replace('/', '.')}' -s {func_def.strip()[len('def '):].split('(')[0]} {{}} -m 200 --lib '/root/04_Python/.venv/lib/python3.8/site-packages' --include_exception --total_timeout=900\n")
end = time.time()
print(f"Time(sec.): {end-start2}")

content = ''
for dirpath, _, files in os.walk(f"./project_statistics/{project_name}"):
    for file in files:
        if file == 'exception.txt':
            with open(os.path.join(dirpath, file), 'r') as f:
                for e in f.readlines():
                    content += e
with open(os.path.abspath(f"./project_statistics/{project_name}/exceptions.txt"), 'w') as f:
    f.write(content)

total_lines = 0
executed_lines = 0
with open(os.path.abspath(f"./project_statistics/{project_name}/missing_lines.txt"), 'w') as f:
    for file in coverage_data.measured_files():
        _, executable_lines, _, _ = cov.analysis(file)
        m_lines = coverage_accumulated_missing_lines[file]
        total_lines += len(set(executable_lines))
        executed_lines += len(set(executable_lines)) - len(m_lines)
        if m_lines:
            print(file, sorted(m_lines), file=f)
print("\nTotal line coverage {}/{} ({:.2%})".format(executed_lines, total_lines, (executed_lines/total_lines) if total_lines > 0 else 0))

with open(os.path.abspath(f"./project_statistics/{project_name}/inputs_and_coverage.txt"), 'w') as f:
    for (func, inputs) in func_inputs.items():
        print(func, inputs, file=f)
    print("\nTotal line coverage {}/{} ({:.2%})".format(executed_lines, total_lines, (executed_lines/total_lines) if total_lines > 0 else 0), file=f)
    try:
        with open(os.path.abspath(f"./project_statistics/{project_name}/coverage_time.txt"), 'r') as f2:
            print(f2.readlines()[0], end='', file=f)
    except: pass

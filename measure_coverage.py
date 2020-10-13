#!/usr/bin/env python3
import argparse, coverage, importlib, inspect, multiprocessing, os, pickle, signal, subprocess, sys, time

TIMEOUT = 15
def timeout_handler(signum, frame):
    raise TimeoutError()
signal.signal(signal.SIGALRM, timeout_handler)

parser = argparse.ArgumentParser(); parser.add_argument("mode"); parser.add_argument("project"); args = parser.parse_args()

if args.mode != '2':
    from conbyte.utils import get_funcobj_from_modpath_and_funcname
    import conbyte.explore; _complete_primitive_arguments = conbyte.explore.ExplorationEngine._complete_primitive_arguments
else:
    import symbolic.loader; get_funcobj_from_modpath_and_funcname = symbolic.loader.Loader.get_funcobj_from_modpath_and_funcname
    import symbolic.invocation; _complete_primitive_arguments = symbolic.invocation.FunctionInvocation._complete_primitive_arguments

rootdir = os.path.abspath(args.project) + '/'; lib = rootdir + '.venv/lib/python3.8/site-packages'
sys.path.insert(0, lib); sys.path.insert(0, rootdir); project_name = rootdir[:-1].split('/')[-1]

# cont = False
func_inputs = {}
coverage_data = coverage.CoverageData()
coverage_accumulated_missing_lines = {}
cov = coverage.Coverage(data_file=None, source=[rootdir], omit=['**/__pycache__/**', '**/.venv/**'])
start2 = time.time()
for dirpath, _, files in os.walk(f"./project_statistics/{project_name}"):
    for file in files:
        if file == 'inputs.pkl':
            try:
                with open(os.path.abspath(dirpath + '/' + file), 'rb') as f:
                    inputs = pickle.load(f)
            except: continue
            func_inputs[(dirpath.split('/')[-2], dirpath.split('/')[-1])] = inputs
            start = time.time()
            for i in inputs:
                r, s = multiprocessing.Pipe()
                def child_process():
                    sys.dont_write_bytecode = True # same reason mentioned in the concolic environment
                    cov.start(); execute = get_funcobj_from_modpath_and_funcname(dirpath.split('/')[-2], dirpath.split('/')[-1])
                    print('currently measuring >>>', dirpath.split('/')[-2], dirpath.split('/')[-1])
                    pri_args, pri_kwargs = _complete_primitive_arguments(execute, i)
                    try:
                        signal.alarm(TIMEOUT)
                        execute(*pri_args, **pri_kwargs)
                    except: pass
                    signal.alarm(0)
                    cov.stop(); coverage_data.update(cov.get_data())
                    for file in coverage_data.measured_files(): # "file" is absolute here.
                        _, _, missing_lines, _ = cov.analysis(file)
                        if file not in coverage_accumulated_missing_lines:
                            coverage_accumulated_missing_lines[file] = set(missing_lines)
                        else:
                            coverage_accumulated_missing_lines[file] = coverage_accumulated_missing_lines[file].intersection(set(missing_lines))
                    s.send((coverage_data, coverage_accumulated_missing_lines))
                process = multiprocessing.Process(target=child_process); process.start()
                try:
                    signal.alarm(TIMEOUT * 4)
                    if r.poll(TIMEOUT * 4): # may get stuck here for some unknown reason
                        (coverage_data, coverage_accumulated_missing_lines) = r.recv()
                except: pass
                signal.alarm(0); r.close(); s.close()
                if process.is_alive(): process.kill()
                if time.time() - start > 15 * 60: break
            if time.time() - start2 > 3 * 60 * 60: break
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
            print(f2.readlines()[0], file=f)
    except: pass

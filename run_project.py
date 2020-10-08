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
os.system(f"rm -rf './project_statistics/{project_name}'")

for dirpath, _, _ in os.walk(rootdir):
    dirpath = os.path.abspath(dirpath) + '/'
    if dirpath != rootdir and not dirpath.startswith(rootdir + '.') and '__pycache__' not in dirpath:
        print(dirpath)
        os.system(f"touch '{dirpath}/__init__.py'")

# Please note this function must be executed in a child process, or
# the import action will affect the coverage measurement later.
def extract_function_list_from_modpath(modpath):
    ans = []#; print(modpath, '==> ', end='')
    try:
        signal.alarm(10) # imported scripts may contain blocking inputs...
        mod = importlib.import_module(modpath)#; print(mod, end='')
        for _, obj in inspect.getmembers(mod):
            if inspect.isclass(obj):
                for _, o in inspect.getmembers(obj):
                    if inspect.isfunction(o) and inspect.signature(o).parameters:
                        if get_funcobj_from_modpath_and_funcname(modpath, o.__qualname__):
                            ans.append(o.__qualname__)#; print(o.__qualname__)
            elif inspect.isfunction(obj) and inspect.signature(obj).parameters:
                if get_funcobj_from_modpath_and_funcname(modpath, obj.__qualname__):
                    ans.append(obj.__qualname__)#; print(obj.__qualname__)
    except Exception as e:
        pass
        # print('Exception: ' + str(e), end='')
    # print()
    signal.alarm(0)
    return ans

# cont = False
start = time.time()
pid = None
try:
    signal.alarm(6*60*60)
    for dirpath, _, files in os.walk(rootdir):
        dirpath += '/'
        for file in files:
            if file.endswith('.py'):
                modpath = os.path.abspath(dirpath + file)[len(rootdir):-3].replace('/', '.')
                if not modpath.startswith('.venv'):
                    # if 'src.flask.sessions' in modpath: cont = True
                    # if not cont: continue
                    if (pid := os.fork()) == 0: # child process
                        funcs = extract_function_list_from_modpath(modpath)
                        for f in funcs:
                            if '<locals>' not in f: # cannot access nested functions
                                if len(f.split('.')) == 2:
                                    (a, b) = f.split('.')
                                    if b.startswith('__') and not b.endswith('__'): b = '_' + a + b
                                    f = a + '.' + b
                                if args.mode == '1': cmd = f"./py-conbyte.py -r '{rootdir}' '{modpath}' -s {f} {{}} -m 20 --lib '{lib}' --include_exception --dump_projstats"
                                elif args.mode == '2': cmd = f"./pyexz3.py -r '{rootdir}' '{modpath}' -s {f} {{}} -m 20 --lib '{lib}' --dump_projstats"
                                else: cmd = f"./py-conbyte.py -r '{rootdir}' '{modpath}' -s {f} {{}} -m 1 --lib '{lib}' --include_exception --dump_projstats"
                                print(modpath, '+', f, '>>>'); print(cmd)
                                try: completed_process = subprocess.run(cmd, shell=True, stdout=sys.stdout, stderr=sys.stderr)
                                except subprocess.CalledProcessError as e: print(e.output)
                        os._exit(os.EX_OK)
                    os.wait(); pid = None
except TimeoutError:
    if pid:
        os.system(f"kill -KILL {pid}")
        os.wait()
signal.alarm(0)

func_inputs = {}
coverage_data = coverage.CoverageData()
coverage_accumulated_missing_lines = {}
cov = coverage.Coverage(data_file=None, include=[rootdir + '**'])
for dirpath, _, files in os.walk(f"./project_statistics/{project_name}"):
    for file in files:
        if file == 'inputs.pkl':
            with open(os.path.abspath(dirpath + '/' + file), 'rb') as f:
                inputs = pickle.load(f)
            func_inputs[(dirpath.split('/')[-2], dirpath.split('/')[-1])] = inputs
            for i in inputs:
                r, s = multiprocessing.Pipe()
                def child_process():
                    sys.dont_write_bytecode = True # same reason mentioned in the concolic environment
                    cov.start(); execute = get_funcobj_from_modpath_and_funcname(dirpath.split('/')[-2], dirpath.split('/')[-1])
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
                    signal.alarm(TIMEOUT * 2)
                    if r.poll(TIMEOUT * 2): # may get stuck here for some unknown reason
                        (coverage_data, coverage_accumulated_missing_lines) = r.recv()
                except: pass
                signal.alarm(0); r.close(); s.close()
                if process.is_alive(): process.kill()
total_lines = 0
executed_lines = 0
for file in coverage_data.measured_files():
    _, executable_lines, _, _ = cov.analysis(file)
    m_lines = coverage_accumulated_missing_lines[file]
    total_lines += len(set(executable_lines))
    executed_lines += len(set(executable_lines)) - len(m_lines)
    # print(file, executed_lines, total_lines)
end = time.time()

with open(os.path.abspath(f"./project_statistics/{project_name}/inputs_and_coverage.txt"), 'w') as f:
    for (func, inputs) in func_inputs.items():
        print(func, inputs, file=f)
    print("\nTotal line coverage {}/{} ({:.2%})".format(executed_lines, total_lines, (executed_lines/total_lines) if total_lines > 0 else 0), file=f)
    print(f"Time(sec.): {end-start}", file=f)
print("\nTotal line coverage {}/{} ({:.2%})".format(executed_lines, total_lines, (executed_lines/total_lines) if total_lines > 0 else 0))
print(f"Time(sec.): {end-start}")

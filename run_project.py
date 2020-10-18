#!/usr/bin/env python3
import argparse, coverage, importlib, inspect, multiprocessing, os, pickle, signal, subprocess, sys, time

TIMEOUT = 15
def timeout_handler(signum, frame):
    raise TimeoutError()
signal.signal(signal.SIGALRM, timeout_handler)
class JumpOutOfLoop(Exception): pass

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
    if dirpath != rootdir and not dirpath.startswith(rootdir + '.') and '__pycache__' not in dirpath and '.venv' not in dirpath:
        print(dirpath)
        os.system(f"touch '{dirpath}/__init__.py'")

# Please note this function must be executed in a child process, or
# the import action will affect the coverage measurement later.
def extract_function_list_from_modpath(modpath):
    ans = []; print(modpath, '==> ', end='')
    try:
        signal.alarm(10) # imported scripts may contain blocking inputs...
        mod = importlib.import_module(modpath); print(mod, end='')
        for _, obj in inspect.getmembers(mod):
            if inspect.isclass(obj):
                for _, o in inspect.getmembers(obj):
                    if inspect.isfunction(o): # and inspect.signature(o).parameters:
                        if get_funcobj_from_modpath_and_funcname(modpath, o.__qualname__):
                            ans.append(o.__qualname__)#; print(o.__qualname__)
            elif inspect.isfunction(obj): # and inspect.signature(obj).parameters:
                if get_funcobj_from_modpath_and_funcname(modpath, obj.__qualname__):
                    ans.append(obj.__qualname__)#; print(obj.__qualname__)
    except Exception as e:
        print('Exception: ' + str(e), end='')
        if 'No module named' in str(e):
            print(' Raise Exception!!!', end='')
            raise e
    print()
    signal.alarm(0)
    return ans

# Decide whether to use given functions or not.
read_functions = False; function_domain = []
try:
    with open('../' + project_name + '/' + project_name + '_function_domain.pkl', 'rb') as f:
        function_domain = pickle.load(f)
        read_functions = True
except: pass

# cont = False
pid = None
start = time.time()
try:
    for dirpath, _, files in os.walk(rootdir):
        dirpath += '/'
        for file in files:
            if file.endswith('.py'):
                modpath = os.path.abspath(dirpath + file)[len(rootdir):-3].replace('/', '.')
                if not modpath.startswith('.venv') and '__pycache__' not in modpath:
                    # if 'solutions.system_design.mint.mint_mapreduce' not in modpath: continue #cont = True
                    # if not cont: continue
                    r, s = multiprocessing.Pipe()
                    if (pid := os.fork()) == 0: # child process
                        funcs = extract_function_list_from_modpath(modpath)
                        for f in funcs:
                            if read_functions:
                                if (modpath, f) not in function_domain: continue
                            if '<locals>' not in f: # cannot access nested functions
                                if len(f.split('.')) == 2:
                                    (a, b) = f.split('.')
                                    if b.startswith('__') and not b.endswith('__'): b = '_' + a + b
                                    f = a + '.' + b
                                try:
                                    signal.alarm(15*60)
                                    if args.mode == '1': cmd = f"./py-conbyte.py -r '{rootdir}' '{modpath}' -s {f} {{}} -m 20 --lib '{lib}' --include_exception --dump_projstats"
                                    elif args.mode == '2': cmd = f"./pyexz3.py -r '{rootdir}' '{modpath}' -s {f} {{}} -m 20 --lib '{lib}' --dump_projstats"
                                    else: cmd = f"./py-conbyte.py -r '{rootdir}' '{modpath}' -s {f} {{}} -m 1 --lib '{lib}' --include_exception --dump_projstats"
                                    print(modpath, '+', f, '>>>'); print(cmd)
                                    try: completed_process = subprocess.run(cmd, shell=True, stdout=sys.stdout, stderr=sys.stderr)
                                    except subprocess.CalledProcessError as e: print(e.output)
                                except TimeoutError: pass
                                signal.alarm(0)
                        os._exit(os.EX_OK)
                    os.wait(); r.close(); s.close(); pid = None
                end = time.time()
                #if not read_functions and end - start > 3 * 60 * 60:
                #    raise JumpOutOfLoop()
except:
    if pid:
        os.system(f"kill -KILL {pid}")
        os.wait()

with open(os.path.abspath(f"./project_statistics/{project_name}/coverage_time.txt"), 'w') as f:
    print(f"Time(sec.): {end-start}", file=f)

# Save inputs to the parent directory if necessary.
if not read_functions:
    with open('../' + project_name + '_function_domain_' + args.mode + '.pkl', 'wb') as f:
        pickle.dump(function_domain, f)

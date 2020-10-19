#!/usr/bin/env python3
import argparse, coverage, importlib, inspect, multiprocessing, os, pickle, signal, subprocess, sys, time
os.system('/usr/bin/Xorg -noreset +extension GLX +extension RANDR +extension RENDER -config /etc/X11/xorg.conf :1 &')

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
        now_dir = os.getcwd()
        os.chdir(os.path.abspath(os.path.dirname(os.path.join(rootdir, modpath.replace('.', '/') + '.py'))))
        sys.path.insert(0, os.path.abspath(os.path.dirname(os.path.join(rootdir, modpath.replace('.', '/') + '.py'))))
        signal.alarm(10); mod = importlib.import_module(modpath); signal.alarm(0); print(mod, end='')
        for _, obj in inspect.getmembers(mod):
            if inspect.isclass(obj):
                for _, o in inspect.getmembers(obj):
                    if (inspect.isfunction(o) or inspect.ismethod(o)) and o.__module__ == modpath: # and inspect.signature(o).parameters:
                        ans.append(o.__qualname__)#; print(o.__qualname__)
            elif (inspect.isfunction(obj) or inspect.ismethod(obj)) and obj.__module__ == modpath: # and inspect.signature(obj).parameters:
                ans.append(obj.__qualname__)#; print(obj.__qualname__)
        i = 0
        while i < len(ans):
            if '<locals>' in ans[i]: del ans[i]; continue # cannot access nested functions
            if len(ans[i].split('.')) == 2:
                (a, b) = ans[i].split('.')
                if b.startswith('__') and not b.endswith('__'): b = '_' + a + b
                ans[i] = a + '.' + b
            get_funcobj_from_modpath_and_funcname(modpath, ans[i]) # assert 的效果
            i += 1
    except TimeoutError: pass
    except Exception as e:
        signal.alarm(0)
        print('Exception: ' + str(e), end='', flush=True)
        print('\nWe\'re going to get stuck here...', flush=True)
        while True: pass
        if 'No module named' in str(e):
            print(' Raise Exception!!!', end='')
            raise e
    print()
    signal.alarm(0); os.chdir(now_dir)
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
                    if (pid := os.fork()) == 0: # child process
                        funcs = extract_function_list_from_modpath(modpath)
                        for f in funcs:
                            if read_functions and (modpath, f) not in function_domain: continue
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
                    os.wait(); pid = None
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

print('End of running project.')

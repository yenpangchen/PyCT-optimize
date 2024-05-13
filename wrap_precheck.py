import inspect
import arg_wrapper
import os
import sys
import pprint

def precheck(module,recursive_idx):
      
    if recursive_idx>4:
        print("!!!!!!!!!!!!!!!!!!!!!!excess recursive limit!!!!!!!!!!!!!!!!!!!!!!")
        return
    else:
        recursive_idx+=1
    wrapper_func = arg_wrapper.get_wrapper()
    print()
    for func_name, func in inspect.getmembers(module, inspect.isfunction):
        
        print(f"processing function: {module.__name__}.{func_name}")
        wrap_function(wrapper_func,module,func_name, func)
        print(f"[Wrap Import Method] {module.__name__}.{func_name} has been wrapped")
        # inspect.getfile(module)
        print("frame:")
        pprint.pprint(inspect.stack()[0].frame.f_locals)
        precheck(func,recursive_idx)
        

        print(f"All object in function: {module} processed finish!")

    for class_name, class_obj in inspect.getmembers(module, inspect.isclass):
        # relpath = os.path.relpath(inspect.getfile(class_obj), os.getcwd())
        print(f"processing class: {module.__name__}.{class_name}")
        relpath = None
        # try:
        #     relpath = os.path.relpath(inspect.getfile(class_obj), os.getcwd())
        # except Exception as e:
        #     print("[ERROR]: Cannot get relpath maybe it is built-in function", e)
        #     continue


        # if not relpath.startswith("src/transformers"):
        #     continue
        # class 'transformers.models.albert.modeling_albert.AlbertModel'
        # if class_name == 'AlbertModel':
        #     print()
        class_methods = inspect.getmembers(class_obj, inspect.isfunction)

        for func_name, func in class_methods:
            print(f"processing class: {class_name}'s method: {func_name}")
            
            # module_name = relpath.replace('/', '.').replace('.py', '')
            
            # if module_name == "src.transformers.configuration_utils":
            #     print()
            wrap_function(wrapper_func,class_obj,func_name, func)
            # print("frame:")
            # pprint.pprint(inspect.stack()[0].frame.f_locals)
            precheck(func,recursive_idx)
            print(f"[Wrap Class Method] {class_name}.{func_name} has been wrapped")
            ##################### END 對此模組的所有函式進行包裝 #####################

def wrap_function(wrapper_func,module,func_name, func):
    
    # relpath = os.path.relpath(inspect.getfile(module), os.getcwd())
    realpath = None
    try:
        relpath = os.path.relpath(inspect.getfile(module), os.getcwd())
    except Exception as e:
        print("[ERROR]: Cannot get relpath maybe it is built-in function", e)
        return
    
    setattr(module, func_name, wrapper_func(func))
    
def _get_module_from_name(self, name):
    __import__(name)
    return sys.modules[name]

def _get_name_from_path(self, path):
        if path == self._top_level_dir:
            return '.'
        path = _jython_aware_splitext(os.path.normpath(path))

        _relpath = os.path.relpath(path, self._top_level_dir)
        assert not os.path.isabs(_relpath), "Path must be within the project"
        assert not _relpath.startswith('..'), "Path must be within the project"

        name = _relpath.replace(os.path.sep, '.')
        return name

def _jython_aware_splitext(path):
    if path.lower().endswith('$py.class'):
        return path[:-9]
    return os.path.splitext(path)[0]
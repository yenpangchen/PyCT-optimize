# 一定要在最一開始import此模組，後續取得自動import的模組清單才不會錯
import sys
import inspect
import json
import os
from collections import defaultdict
import pickle
import re
import time
import functools
from try_run_pyct import pyct_test_transformers
import logging

auto_imported_modules = set(sys.modules.keys())
# import sys
# sys.path.insert(0, "/home/jack/coverage/PyCT/libct")


def is_builtin_function(name):
    pattern = r'^__\w+__$'
    return re.match(pattern, name) is not None


def is_able_to_wrap(funcname):
    # filter_tuple = ("method_wrapper", "get_config", "to_dict")
    # filter_tuple = ("method_wrapper")
    
    filter_set = set()
    if os.path.exists("error_func_list.txt"):
        with open('error_func_list.txt', 'r') as f:
            error_func_list = f.read().splitlines()
            filter_set = set(error_func_list)
    filter_set.update(["method_wrapper", "get_config", "to_dict"])
    
    # 0323 測試拿掉_
    # if funcname not in filter_set and not is_builtin_function(funcname) and not funcname.startswith('_'):
    #     print(f"{funcname} is_able_to_wrap")
    #     return True
    if funcname not in filter_set and not is_builtin_function(funcname):
        print(f"{funcname} is_able_to_wrap")
        return True
    else:
        print(f"{funcname} isn't_able_to_wrap, funcname not in filter_set: ",funcname not in filter_set," and not is_builtin_function(funcname): ",not is_builtin_function(funcname)," and not funcname.startswith('_'): ",not funcname.startswith('_'))
        return False


def get_args_types(func, class_name=None):
    sig = inspect.signature(func)
    
    @functools.wraps(func)
    def method_wrapper(*args, **kwargs):
        module_name = func.__module__
        func_name = func.__name__

        # py_abs_path = inspect.getfile(func)

        # print("abs path:", py_abs_path)
        # print(f"Function {func_name} in module {module_name} arguments:")
        
        try:
            for name, value in zip(sig.parameters, args):
                atype = type(value).__name__
                # print(f"\t{name} ({atype}) : {value}")
                save_arg(name, atype, value, module_name, func_name)

            for name, value in kwargs.items():
                atype = type(value).__name__
                # print(f"\t{name} ({atype}) : {value}")
                save_arg(name, atype, value, module_name, func_name)
                
        except RecursionError as e:
            print()
            print("@@@@@[RecursionError]", e)
            print(f'error func: "{func.__name__}"' )
            with open('error_func_list.txt', 'a') as f:
                f.write(f'{func.__name__}\n')
            # print(e.pribt_stack())
        except Exception as e:
            print("method_wrapper error:", e)
            print(f'error func: "{func.__name__}"' )
            with open('error_func_list.txt', 'a') as f:
                f.write(f'{func.__name__}\n')

        return func(*args, **kwargs)
        
    if is_able_to_wrap(func.__name__):
        return method_wrapper
    else:
        return func


def empty_wrpper(func, class_name=None):
    sig = inspect.signature(func)
    
    @functools.wraps(func)
    def method_wrapper(*args, **kwargs):
        module_name = func.__module__
        func_name = func.__name__

        return func(*args, **kwargs)
        
    if is_able_to_wrap(func.__name__):
        return method_wrapper
    else:
        return func



def unit_test_run_pyct(func, has_self, *args, **kwargs):
    module_name = func.__module__
    func_name = func.__qualname__
    
    # if module_name.startswith("transformers"):
    file = inspect.getfile(func)

    in_dict = dict()
    params = inspect.signature(func).parameters.items()
    can_concolic = False
    primitive_type = (bool, float, int, str)
    primitive_args = dict()
    
    if has_self != None:
        # has_self 代表這是某個class的method所以要把self加進去，所以has_self要傳入該物件
        in_dict['self'] = has_self
    
    for i, ((p_name, p_obj), arg) in enumerate(zip(params, args)):
        if p_obj.kind == inspect.Parameter.VAR_POSITIONAL:
            # *args
            in_dict["*args"] = []
            primitive_args["*args"] = []
            for arg in args[i:]:
                if type(arg) in primitive_type:
                    can_concolic = True
                    primitive_args["*args"].append(arg)
                else:
                    primitive_args["*args"].append("NOT_PRIMITIVE")
                    
                in_dict["*args"].append(arg)
                
            break
                            
        if type(arg) in primitive_type:
            primitive_args[p_name] = arg
            can_concolic = True
        else:
            primitive_args[p_name] = "NOT_PRIMITIVE"

        in_dict[p_name] = arg
    
    for p_name, arg in kwargs.items():
        if type(arg) in primitive_type:
            primitive_args[p_name] = arg
            can_concolic = True
        else:
            primitive_args[p_name] = "NOT_PRIMITIVE"
            
        in_dict[p_name] = arg
    
    if can_concolic:
        # FORMAT = '%(asctime)s %(funcName)s %(levelname)s: %(message)s'
        # time_result = time.localtime(time.time())
        # fileName=f'/home/ray/pyct-coverage/coverage/transformers/log/unit_test_transformer_{module_name}_{func_name}.log'
        # print(f'fileNamein={fileName}')
        logger=logging.getLogger('ct')
        # handler=logging.FileHandler(fileName,mode='a')
        # formatter=logging.Formatter(FORMAT)
        # handler.setFormatter(formatter)


        print()
        print("[pyct_test_transformers]", '@' * 100)
        print(f"{file} {module_name} {func_name}")
        logger.info('@' * 100)
        logger.info(f"this function can use concolic testing:")
        logger.info(f"{module_name}.{func_name}")
        # logger.info(f"primitive_args:")
        # logger.info(json.dumps(primitive_args, indent='\t'))
        
        history = dict()
        if os.path.exists('manual_fork_pyct_func.json'):
            with open('manual_fork_pyct_func.json', 'r') as f:
                history = json.load(f)

        if file not in history:
            history[file] = dict()
        
        if func_name not in history[file]:
            history[file][func_name] = primitive_args
            with open('manual_fork_pyct_func.json', 'w') as f:
                json.dump(history, f, indent='\t')
        
        
        pyct_test_transformers(file, func_name, in_dict)


skip_func_list = ['ErnieMTokenizer.is_punct', 'ErnieMTokenizer.is_punct',
                  'SamImageProcessor.post_process_masks', 'SamProcessor.post_process_masks',
                  'Pix2StructImageProcessor.extract_flattened_patches',
                  'M2M100Tokenizer.get_lang_token', 'M2M100Tokenizer.get_lang_id',
                  'MarkupLMTokenizerFast.get_xpath_seq','utils/pyct_attack_exp_research_question']
def pyct_wrpper(func):
    # params = dict(inspect.signature(func).parameters.items()).copy()
        
    @functools.wraps(func)
    def method_wrapper(*args, **kwargs):
        
        module_name = func.__module__
        func_name = func.__qualname__  
        print("\n")
        # print("arg: ",args)
        try:
            if not module_name.startswith("unittest.case"):
                file = inspect.getfile(func)

                in_dict = dict()
                params = inspect.signature(func).parameters.items()
                
                can_concolic = False
                primitive_type = (bool, float, int, str)
                # primitive_type = (bool, float, int)
                primitive_args = dict()
                for i, ((p_name, p_obj), arg) in enumerate(zip(params, args)):
                    print(f"param: {((p_name, p_obj), type(arg))} ,kind: {p_obj.kind}")
                    if p_obj.kind == inspect.Parameter.VAR_POSITIONAL:
                    # *args
                        in_dict["*args"] = []
                        primitive_args["*args"] = []
                        
                        for arg in args[i:]:
                            print(f"checking arg: {arg}")
                            if type(arg) in primitive_type:
                                can_concolic = True
                                primitive_args["*args"].append(arg)
                            else:
                                primitive_args["*args"].append("NOT_PRIMITIVE")
                            
                            in_dict["*args"].append(arg)
                        
                        break
                                    
                    if type(arg) in primitive_type:
                        primitive_args[p_name] = arg
                        can_concolic = True
                    else:
                        primitive_args[p_name] = "NOT_PRIMITIVE"

                    in_dict[p_name] = arg
            
                for p_name, arg in kwargs.items():
                    if type(arg) in primitive_type:
                        primitive_args[p_name] = arg
                        can_concolic = True
                    else:
                        primitive_args[p_name] = "NOT_PRIMITIVE"
                    
                    in_dict[p_name] = arg
                print(f"{module_name}.{func_name} is called and can_concolic :{can_concolic} ,func_name not in skip_func_list :{func_name not in skip_func_list}")
                print(f"in_dict: {in_dict}")
                #logging.info(f"{module_name}.{func_name} is called and can_concolic :{can_concolic} ,func_name not in skip_func_list :{func_name not in skip_func_list}")
                if can_concolic and func_name not in skip_func_list:
                #小呆節省效能用
                    history = dict()
                    if os.path.exists('can_fork_pyct_func.json'):
                        with open('can_fork_pyct_func.json', 'r') as f:
                            history = json.load(f)
                
                    if file not in history:
                        history[file] = dict()

                #print(f"{func_name} can_concolic, not in skip_func_list, not in history: {func_name not in history[file]}")
                
                    if func_name not in history[file]:
                        history[file][func_name] = primitive_args
                        with open('can_fork_pyct_func.json', 'w') as f:
                            json.dump(history, f, indent='\t')
                    
                    
                    logging.info('@' * 100)
                    logging.info(f"this function can use concolic testing:{module_name}.{func_name}")
                    # logging.info(f"primitive_args:")
                    # logging.info(json.dumps(primitive_args, indent='\t'))
                    print("="*15,f"this function can use concolic testing:{module_name}.{func_name}", "="*15)
                    
                    pyct_test_transformers(file, func_name, in_dict)
                    
                
                """
                print()
                logging.info('@' * 100)
                logging.info(f"this function can use concolic testing:")
                logging.info(f"{module_name}.{func_name}")
                logging.info(f"primitive_args:")
                logging.info(json.dumps(primitive_args, indent='\t'))
                """
                        
                
                
                    
        finally:
            return func(*args, **kwargs)
        #return func
        
    if is_able_to_wrap(func.__name__):
        return method_wrapper
    else:
        return func


def get_wrapper():
    # return get_args_types
    # return empty_wrpper
    # print("wrapper get!")
    return pyct_wrpper



def check_serializable(obj, serialize_type):
    if serialize_type == "json":
        try:
            json.dumps(obj)
            return True
        except Exception as e:
            return False
    elif serialize_type == "pickle":
        try:
            pickle.dumps(obj, protocol=pickle.HIGHEST_PROTOCOL)
            return True
        except Exception as e:
            return False
    else:
        return False
        # raise Exception("Unknown serialize type")

# def check_serializable(obj, serialize_type):
#     if serialize_type == "json":
#         try:
#             if isinstance(obj, (dict, list, tuple, str, int, float, bool, type(None))):
#                 for item in obj:
#                     if not check_serializable(item, serialize_type):
#                         return False
#                 return True
#             else:
#                 return False
#         except Exception as e:
#             return False
#     elif serialize_type == "pickle":
#         try:
#             pickle.dumps(obj, protocol=pickle.HIGHEST_PROTOCOL)
#             return True
#         except Exception as e:
#             return False
#     else:
#         raise Exception("Unknown serialize type")


def save_arg(arg_name, atype, value, module_name, func_name):
    # arg_type = defaultdict(lambda: defaultdict(dict))
    arg_type = dict()
    # print(module_name, func_name)
    if os.path.exists("arg_type.pickle"):
        with open("arg_type.pickle", "rb") as f:
            arg_type = pickle.load(f)
    
    # if os.path.exists("arg_type.json"):
    #     with open("arg_type.json", "r") as f:
    #         arg_type = json.load(f)

    if module_name not in arg_type:
        arg_type[module_name] = dict()

    if func_name not in arg_type[module_name]:
        arg_type[module_name][func_name] = dict()
        
    if arg_name in arg_type[module_name][func_name]:
        # 已經除存過得就不要存了
        # print(module_name, func_name, 'has saved')
        return False
    else:
        pass
        # print(module_name, func_name, 'has saved')

    dump_value = None
    if check_serializable(value, "json"):
        dump_value = value
    elif check_serializable(value, "pickle"):
        dump_value = "[Serialized]"
    else:
        dump_value = "[Not Serializable]"
    
    arg_type[module_name][func_name][arg_name] = {
        'type': atype, 'value': dump_value
    }
    
    with open("arg_type.json", "w") as f:
        json.dump(arg_type, f, indent=4)
        
    with open("arg_type.pickle", "wb") as f:
        pickle.dump(arg_type, f, protocol=pickle.HIGHEST_PROTOCOL)
    
    
    
    # if isinstance(value, (dict, list, tuple, str, int, float, bool, type(None))):
    #     arg_type[module_name][func_name][arg_name] = {
    #         'type': atype, 'value': value
    #     }
    # else:
    #     arg_type[module_name][func_name][arg_name] = {
    #         'type': atype, 'value': "[Not JSON Serializable]"
    #     }

    # try:
    #     with open("arg_type.json", "w") as f:
    #         json.dump(arg_type, f, indent=4)
    # except Exception as e:
    #     e.print_stack()
                
    # try:
    #     with open("arg_type.pickle", "wb") as f:
    #         pickle.dump(arg_type, f, protocol=pickle.HIGHEST_PROTOCOL)
    # except Exception as e:
    #     e.print_stack()


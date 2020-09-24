# Py-Conbyte

This project is a Python concolic testing tool taking advantage of inheritance from primitive types along with operator/function overriding and AST rewriting.

It refers to the framework proposed in
[Deconstructing Dynamic Symbolic Execution](http://research.microsoft.com/apps/pubs/?id=233035),
[A Peer Architecture for Lightweight Symbolic Execution](http://hoheinzollern.files.wordpress.com/2008/04/seer1.pdf)
and the tool [PyExZ3](https://github.com/GroundPound/PyExZ3).

接下來是比較偏 methodology 的部分，要寫得比較正式的話需要點時間，之後再補。

---

## Functionality

The main objective of Py-Conbyte is to achieve as much coverage of the source file as possible where the target function belongs to by feeding various input arguments. The currently supported concolic types are `bool -> ConcolicBool`, `float -> ConcolicFloat`, `int -> ConcolicInt`, `range -> ConcolicRange`, and `str -> ConcolicStr`. However, the input arguments can only be `ConcolicInt` and `ConcolicStr`. Of course, not all operations of concolic types are supported yet. For more details, please refer to the folder `conbyte/concolic/*.py` (especially `int.py` and `str.py`).

最後這句話之後應該會被展開成細項分別說明有哪些功能。

---

## Flow of Execution

---

## How / Why It Works

---

## Prerequisite
- [Python](https://www.python.org/downloads/) version == 3.8.2<br>
  It should also work for other versions not lower than 3.8.<br>

- [CVC4](https://github.com/CVC4/CVC4) == [d43f7760866a1a26769dfdebdffebdaf35309f9c](https://github.com/CVC4/CVC4/tree/d43f7760866a1a26769dfdebdffebdaf35309f9c)<br>
  The commit version above is used in our testing process. Maybe other later versions are also fine.<br>
  Please ensure the command `cvc4` can be automatically found by the operating system. ~~Our program will also do it, so it doesn't matter if the user fails to do so.~~<br>
  Latest releases can be found [here](https://cvc4.github.io/downloads.html), but if you want to stay at the above version the [installation process](https://github.com/CVC4/CVC4/blob/d43f7760866a1a26769dfdebdffebdaf35309f9c/INSTALL.md) may be a little bit trivial.

- [pipenv](https://pypi.org/project/pipenv/)

- Other packages required for your target function to run

<!---
([Z3](https://github.com/Z3Prover/z3)
-->

---

## Installation

1. Clone our project to the local repository.<br>
Run `$ git clone git@github.com:alan23273850/py-conbyte.git`,<br>
or `$ git clone https://github.com/alan23273850/py-conbyte.git`<br>
2. `$ cd py-conbyte` and `$ pipenv shell`.<br>
3. `$ pipenv install`<br>
This is used to create a virtual environment.

---

## Usage

Keep in mind that always do `$ pipenv shell` first when entering this project directory.
```
usage: py-conbyte.py [-h] [-r ROOT] [-s FUNC] [-m ITER] [--lib LIB] [--safety SAFETY] [-t TIMEOUT] [--timeout2 TIMEOUT2] [--ignore_return] [-v VERBOSE] [-l LOGFILE]
                     [-d FORMULA] [--dump_projstats] [--solver SOLVER]
                     path.to.module input_dict

positional arguments:
  path.to.module        absolute import path to the target module (file) relative to the project root
                        Ex1: ./a/b/c.py -> a.b.c
                        Ex2: ./def.py -> def

  input_dict            dictionary of initial arguments to be passed into the target function
                        Please note that the double quotes outside the dictionary cannot be omitted!
                        Ex1: func(a=1,b=2) -> "{'a':1,'b':2}"
                        Ex2: func(a='',b='') -> "{'a':'','b':''}"


optional arguments:
  -h, --help            show this help message and exit

  -r ROOT, --root ROOT  path to the project root which the target function belongs to [default = path/to/this/project]
                        This option should always be provided if the target function belongs to another project.
                        If the target project is put inside this project (i.e., the latter's root path is a prefix of the former's),
                        the scope of coverage is only the target "file." Otherwise, the scope covers the whole "project."

  -s FUNC, --func FUNC  name of the target function
                        (*) If the function "func" belongs to a class "CLASS", this name should be "CLASS.func".
                        (*) If the function name is the same as that of the target file, this option can be omitted.

  -m ITER, --iter ITER  maximum number of iterations [default = 200]

  --lib LIB             another library path to be inserted at the beginning of sys.path
                        For example, if the target function belongs to another project requiring a virtual environment,
                        you may want to do "--lib ~/.local/share/virtualenvs/projectname-projectid/lib/python3.8/site-packages".

  --safety SAFETY       indicates the behavior when the values in Python and in SMTLIB2 of a concolic object are not equal. [default = 0]
                        (0) The expression in a concolic object is still preserved even if the values are different.
                        (1) The expression in a concolic object will be erased if the values are different, but the program still continues.
                        (2) The expression in a concolic object will be erased if the values are different, and the program exits soon.
                        Only in level 0 don't we verify return values of the target function since some objects in fact are not picklable,
                        and therefore information about return values will not printed in the end.

  -t TIMEOUT, --timeout TIMEOUT
                        timeout (sec.) for the solver to solve a constraint [default = 10]

  --timeout2 TIMEOUT2   timeout (sec.) for the explorer to go through one iteration [default = 15]

  --ignore_return       disable examination of return values in case they are not picklable.

  -v VERBOSE, --verbose VERBOSE
                        logging level [default = 1]
                        (0) Show messages whose levels not lower than WARNING.
                        (1) Show messages from (0), plus basic iteration information.
                        (2) Show messages from (1), plus solver information.
                        (3) Show messages from (2), plus all concolic objects' information.

  -l LOGFILE, --logfile LOGFILE
                        name of the log file
                        (*) When this argument is an empty string, all logging messages will not be dumped either to screens or to files.
                        (*) When this option is not set, the logging messages will be dumped to screens.

  -d FORMULA, --formula FORMULA
                        name of directory or file to store smtlib2 formulas
                        (*) When this argument is a pure positive integer N, it means that we only want to store the N_th constraint
                        where N is the number "SMT-id" shown in the log. The file should be named {N}.smt2 in the current directory.
                        (*) Otherwise, this argument names the directory, and all constraints will be stored in this directory whose
                        names follow the rule mentioned above.
                        In either case, these *.smt2 files should be able to be called by a solver directly.

  --dump_projstats      dump project statistics under the directory "./project_statistics/{project_name}/{path.to.module}/{func_name}/**".

  --solver SOLVER       solver type [default = cvc4]
                        We currently only support CVC4.

```

For example, to test the target function `build_in(a, b)` in the target file `test/build_in.py` (Note that they have the same name.), and to let the two initial arguments be `a = 0` and `b = 0`, we can simply use the following command.
```
 $ ./py-conbyte.py -r test build_in "{'a':0,'b':0}"
```
The output would be:
```
  ct.explore    INFO     Inputs: {'a': 0, 'b': 0}
  ct.explore    INFO     Return: 1
  ct.explore    INFO     Not Covered Yet: /mnt/d/ALAN_FOLDER/2020_RESEARCH/1_CODE_py-conbyte/test/build_in.py {11}
  ct.explore    INFO     === Iterations: 1 ===
  ct.explore    INFO     Inputs: {'a': 100, 'b': 0}
  ct.explore    INFO     Return: 0

Total iterations: 1

Generated inputs
[{'a': 0, 'b': 0}, {'a': 100, 'b': 0}]

Line coverage 9/9 (100.00%)

# of input vectors: 2
[({'a': 0, 'b': 0}, 1), ({'a': 100, 'b': 0}, 0)]

```

To leave this virtual environment, simply type `$ exit` in the terminal.

---

## TODO

---

## Known Issues

Although this project aims to provide an error-free concolic testing environment, this goal in fact can be proven almost impossible! The most significant obstacle is "exact type checking." When a program performs this kind of checking, it probably wants to do something that only accepts primitive types. However, whether to unwrap the concolic objects automatically when facing this check solely depends on the purpose of the code, and of course the purpose can not be recognized by softwares nowadays. Besides, we've not come up with a method to unwrap these arguments if they are immutable objects and enclosed in another function. For example, the C source code of socket implementations expects the input arguments to be primitive. In this case we can replace the Python-level socket function with our custom one which unwraps the arguments first. As another example, some network libraries may need to know whether the object to be sent is primitive or not, so that it can decide whether to run the operations designed specifically for non-primitive objects. In this case we should not unwrap the concolic objects automatically. Currently we can only manually adjust the code case by case.

1. To replace an existing function with your custom one, you can refer to the `prepare()` function in `conbyte/explore.py`.

2. To disable wrapping a module when importing it, you can refer to line 144 in `conbyte/wrapper.py`.

---

## How to Contribute

blablabla...

Finally you may want to run the (parallel) integration test (in `integration_test.py`) to ensure the contribution is correct. The command is `pytest integration_test.py --workers [# of processes] -x`, and it takes almost 11 minutes to run.

If you want to create the csv file of the testing result, run `echo "ID|Line Coverage|Missing Lines|Inputs & Outputs" > output.csv2 && dump=True pytest integration_test.py --workers [# of processes] -x && cp /dev/null output.csv && cat *.csv >> output.csv2 && rm -f *.csv && mv output.csv2 output.csv`. Make sure there are no existing *.csv files in the current directory before running the test. Our file content is separated by "|" since "," is already contained in the data.

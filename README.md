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
usage: py-conbyte.py [-h] [-e ENTRY] [-m ITERATION] [--safety SAFETY] [-t TIMEOUT] [--timeout2 TIMEOUT2] [-f FORMULA] [-l LOGFILE] [-v VERBOSE] [-s SOLVER]
                     filename.py input_args

positional arguments:
  filename.py           target file
  input_args            input arguments of the target function

optional arguments:
  -h, --help            show this help message and exit
  -e ENTRY, --entry ENTRY
                        name of the target function
                        If the function name is the same as that of the target file, this option can be omitted.
  -m ITERATION, --iter ITERATION
                        maximum number of iterations [default = 200]
  --safety SAFETY       indicates the behavior when the values in Python and in SMTLIB2 of a concolic object are not equal. [default = 0]
                        (0) The expression in a concolic object is still preserved even if the values are different.
                        (1) The expression in a concolic object will be erased if the values are different, but the process still continues.
                        (2) The expression in a concolic object will be erased if the values are different, and the process terminates soon afterwards.
  -t TIMEOUT, --timeout TIMEOUT
                        timeout (sec.) for the solver to solve a constraint [default = 10]
  --timeout2 TIMEOUT2   timeout (sec.) for the explorer to go through one iteration [default = 15]
  -f FORMULA, --formula FORMULA
                        name of directory or file to store smtlib2 formulas
                        (*) When this argument is a pure positive integer N, it means that we only want to store the N_th constraint
                        where N is the number "SMT-id" shown in the log. The file should be named {N}.smt2 in the current directory.
                        (*) Otherwise, this argument names the directory, and all constraints will be stored in this directory whose
                        names follow the rule mentioned above.
                        In either case, these *.smt2 files should be able to be called by solvers directly.
  -l LOGFILE, --logfile LOGFILE
                        name of the log file
                        (*) When this argument is an empty string, all logging messages will not be dumped either to screens or to files.
                        (*) When this option is not set, the logging messages will be dumped to screens.
  -v VERBOSE, --verbose VERBOSE
                        logging level [default = 1]
                        (0) Show messages whose levels not lower than WARNING.
                        (1) Show messages from (0), plus basic iteration information.
                        (2) Show messages from (1), plus solver information
                        (3) Show messages from (2), plus all concolic object's information.
  -s SOLVER, --solver SOLVER
                        solver type [default = cvc4]
                        We currently only support CVC4.
```

Example:
```
 $ ./py-conbyte.py test/do_numbers.py [0,0] -s cvc4
```

To leave this virtual environment, simply type `$ exit` in the shell.

---

## TODO

---

## How to Contribute

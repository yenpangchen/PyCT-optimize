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

Keep in mind always do `$ pipenv shell` first when entering this project directory.
```
usage: py-conbyte.py [-h] [-e ENTRY] [-m ITERATION] [--safety SAFETY] [-t TIMEOUT] [--timeout2 TIMEOUT2] [-f FORMULA] [-l LOGFILE] [-v VERBOSE] [-s SOLVER] path_to_file.py input_args

positional arguments:
  path_to_file.py       the target file
  input_args            the input arguments

optional arguments:
  -h, --help            show this help message and exit
  -e ENTRY, --entry ENTRY
                        entry point, if different from path_to_file.py
  -m ITERATION, --iter ITERATION
                        maximum number of iterations
  --safety SAFETY       expression value safety level
  -t TIMEOUT, --timeout TIMEOUT
                        solver timeout (default = 10 sec)
  --timeout2 TIMEOUT2   execution timeout (default = 15 sec)
  -f FORMULA, --formula FORMULA
                        folder or file to store smtlib2 formulas
  -l LOGFILE, --logfile LOGFILE
                        store log
  -v VERBOSE, --verbose VERBOSE
                        set the verbosity level
  -s SOLVER, --solver SOLVER
                        solver=[z3seq, z3str, trauc, cvc4]. Currently only support cvc4.
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

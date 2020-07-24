# py-conbyte 

# Requirements
- Python version == 3.8.2
- SMT-solver installed ([Z3](https://github.com/Z3Prover/z3) or [CVC4](https://github.com/CVC4/CVC4)) 

A Python concolic testing tool taking advantage of the inheritance method ~~running on bytecode level~~.

This project takes refer to the structure purposed in 
[Deconstructing Dynamic Symbolic Execution](http://research.microsoft.com/apps/pubs/?id=233035),  
[A Peer Architecture for Lightweight Symbolic Execution](http://hoheinzollern.files.wordpress.com/2008/04/seer1.pdf)
and the tool [PyExZ3](https://github.com/GroundPound/PyExZ3).   
We use the same path_to_constraints structure in our tool.
The main difference is how we instrument the code.   
PyExZ3 substitutes the formal parameters with self-defined symbolic objects
in the program to analysis. It runs the program, and records symbolic values 
for each variables and branches. One drawback of this approach is that
it did not encode operations outside these self-defined objects. For example, it
degrades to int concrete value when executing `int(<string>)` since `int()` is a
built-in function and cannot be overwritten in self-defined objects.   
Py-Conbyte instead maintains an independent symbolic environment.   
It collects the bytecodes being executed as the program runs, and
executes them simultaneously in this symbolic environment. With this approach
we have full control on encoding the program behaviors into symbolic semantics,
or easily gets the concrete value from the original program when it's hard 
to encode.



py-conbyte currently supports:
- Builtin functions: 
  - `len()`
  - `int()`
  - `str()`
  ~~- `dict()`~~
  ~~- `list()`~~
  - `range()`
  - `sum()`
  - `max()`
  - `min()`
  - `abs()`
- Types: 
  - Integer
  - String
  - Array
  ~~- Dictionary~~
  - Class containing these types
See `test/` for supported syntaxes.   

Formal parameters of the program to analysis can only be integers,
strings, array containing integer and string.

## Installation (新式套件管理器改用 pipenv)
Make sure you have z3/cvc4 installed in your system.   
Use `pip` to install python packages.
```
$ pip install -r requirements.txt
```

## Usage
```
usage: py-conbyte.py [-h] [-e ENTRY] [-m ITERATION] [-t TIMEOUT] [--ss] [-d] [-q QUERY] [--quiet] [-l LOGFILE] [--json] [-s SOLVER] path_to_target_file.py input_args

positional arguments:
  path_to_target_file.py
                        specify the target file
  input_args            specify the input arguments

optional arguments:
  -h, --help            show this help message and exit
  -e ENTRY, --entry ENTRY
                        specify entry point, if different from path_to_target_file.py
  -m ITERATION, --max_iter ITERATION
                        specify max iterations
  -t TIMEOUT, --timeout TIMEOUT
                        specify solver timeout (default = 1sec)
  --ss                  special constraint for add_binays.py
  -d, --debug           enable debug logging
  -q QUERY, --query QUERY
                        store smt queries
  --quiet               no logging
  -l LOGFILE, --logfile LOGFILE
                        store log
  --json                print JSON format to stdout
  -s SOLVER, --solver SOLVER
                        solver=[z3seq, z3str, trauc, cvc4], default to z3
```

Example:
```
 $ ./py-conbyte.py -s cvc4 test/do_numbers.py -i [0,0]
```

使用方式:
1. `$ git clone git@github.com:alan23273850/py-conbyte.git` 或 `$ git clone https://github.com/alan23273850/py-conbyte.git`
2. 進入專案根目錄，建立套件環境 `$ pipenv shell`。(可能要先安裝 pipenv: `$ sudo apt install pipenv`)
3. 安裝所需套件 `$ pipenv install`。
4. 所有的測資都寫在 script.sh 裡面，可以自行使用。以後每次測試之前都要先打 `$ pipenv shell` 進入虛擬環境才能使用。

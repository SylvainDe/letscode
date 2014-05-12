letscode
========

Command-line interface to perform the usual actions (create "hello-world" code, compile, check, run, debug, retrieve info, generate doc, etc) for different programming languages.


Why this script ?
-----------------

I love working on little pieces of codes in different programming languages and I've spent too much time doing the same things again and again :
 * look for the exact syntax for an hello world in a given language
 * struggle to get the code to compile with the right options
 * forget the different static analysers that one can use
 * write a script and call `chmod +x` because I have forgotten to give the right permissions
 * go through my notes to find the one link that can save me some googling

Also, I wanted to have some fun and discover new things (Python concepts & programming languages).


Examples:
---------

**File creation**

 * `letscode.py hello.cpp -a create -l cpp` creates an hello-world in C++ (language is provided)
 * `letscode.py hello.cpp -a create` does the same (language is detected based on the file extension and/or content)
 * `letscode.py hello -a create -l cpp` does the same (file extension will be added based on the language used)
 * `letscode.py hello.py -a create -l python3` does the same (language is provided to know which version of Python is to be used)


**Compilation**
 * `letscode.py hello.cpp -a compile` compiles with the relevant compiler (`g++` for C++) 
 * `letscode.py hello.go -a compile` compiles with the Go compiler

**Run**
 * `letscode.py hello.cpp -a run` runs the hello world previously compiled
 * `letscode.py hello.py -a run` runs the hello world with the relevant Python interpreter

Actions can be combined:
 * `letscode.py hello.cpp -a compile -a run` compiles the helo world and runs the corresponding code

**Other actions**

Other actions can be/are defined.


Programming languages (partially) supported:
--------------------------------------------

 * C
 * C++
 * Java
 * Haskell
 * Python (2 & 3)
 * Shell
 * Bash
 * Zsh
 * Ruby
 * Javascript
 * Perl
 * PHP
 * Vim Script
 * Julia
 * Lua
 * DOT
 * Go
 * Clojure
 * Lisp
 * Scheme
 * Racket
 * Caml
 * Scala
 * Rust
 * LaTeX
 * SQL
 * HTML
 * XML

Implementation:
---------------

In the current implementation, all programming languages inherit from a common `Language` class used for common code. All languages inherit from `Language` either directly or through other abtsract classes (`CompiledLanguage`, `ScriptingLanguage`). The organisation is not so much based on the paradigms (functionnal, OOP, logic) but on the actions that one can perform on the code (such as compilation). Also, at the moment C++ "inherits" from C not because it makes sense from a historical/theoretical point of view but just because they have so much in common - the inheritance could have been done the other way round without any problem.

Next steps :
------------

Re-organisation in multiple smaller files.


Installation :
--------------

The installation of the script itself is as simple as it could be : get it and you are done.
However, it calls a lot of other executables. Here's a non exhaustive list of them :

 * clisp - sudo apt-get install clisp
 * scheme / mit-scheme - sudo apt-get install mit-scheme
 * golang - sudo apt-get install golang
 * gccgo - sudo apt-get install gccgo
 * ghc - sudo apt-get install ghc
 * julia - sudo apt-get install julia
 * lua - sudo apt-get install lua5.2
 * pyflakes - sudo apt-get install pyflakes
 * pylint - sudo apt-get install pylint
 * pychecker - sudo apt-get install pychecker
 * pep8 - sudo apt-get install pep8
 * clojure - wget http://central.maven.org/maven2/org/clojure/clojure/1.6.0/clojure-1.6.0.jar
 * sloccount (for asm_count, c_count, cobol_count, f90_count, fortran_count, haskell_count, lex_count, ml_count, modula3_count, objc_count, perl_count, python_count)- sudo apt-get install sloccount

(I should have kept track of things as I was needing them but it is too late now).



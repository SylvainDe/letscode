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
 * `letscode.py hello.cpp -a compile -a run` compiles the hello world and runs the corresponding code

**Other actions**

Other actions can be/are defined :
 * `display`: shows the code that would be put in the file during creation
 * `info`: provides useful information about the language
 * `man`: opens the relevant manual (compiler or interpreter)
 * `debug`: launches the debugger
 * `shell`: starts a shell
 * `interactive`: runs the file and starts an intereractive shell
 * and more to be added.

Programming languages (partially) supported:
--------------------------------------------
 * Languages with compiling (and running) Hello World :
    * C
    * C++
    * Java
    * Objective C
    * Vala
    * D
    * Go
    * Haskell
    * Verilog
    * Rust
    * Fortran
    * Cobol
    * Ada
    * Pascal
    * Oz
    * Icon
    * LaTeX
    * reST
    * DOT

 * Languages with running (interpreted) Hello World :
    * Python (2 & 3)
    * Ruby
    * Julia
    * Lua
    * Perl
    * PHP
    * Groovy
    * Lisp
    * Javascript
    * Vim Script
    * Clojure
    * Shell
    * Bash
    * Csh
    * Tcsh
    * Ksh
    * Ash
    * Dash
    * Zsh
    * Yash
    * Tcl
    * FishShell
    * Pike
    * Scala
    * Nimrod
    * Scheme
    * Smalltalk
    * Racket
    * Forth
    * Swift (not the Apple one)
    * S-Lang
    * Prolog
    * R
    * Scilab
    * Octave
    * Genius

 * Languages with minimal support at the moment (basic information about the language):
    * C#
    * F#
    * J
    * Eiffel
    * Caml
    * Coq
    * Ceylon
    * Elm
    * Erlang
    * Elixir
    * Idris
    * APL
    * CoffeeScript
    * TypeScript
    * JSX
    * Dart
    * Agda
    * SQL
    * EcmaScript
    * ActionScript
    * PostScript
    * Markdown
    * HTML
    * XML
    * YAML
    * HAML
    * CSS
    * Spark
    * Factor
    * Mars
    * Kotlin
    * AMPL


Status:
-------
[![Build Status](https://travis-ci.org/SylvainDe/letscode.svg?branch=master)](https://travis-ci.org/SylvainDe/letscode)


Implementation:
---------------

In the current implementation, all programming languages inherit from a common `Language` class used for common code. All languages inherit from `Language` either directly or through other abstract classes (`CompilableLanguage`, `InterpretableLanguage`). The organisation is not so much based on the paradigms (functionnal, OOP, logic) but on the actions that one can perform on the code (such as compilation). Also, at the moment C++ "inherits" from C not because it makes sense from a historical/theoretical point of view but just because they have so much in common - the inheritance could have been done the other way round without any problem.

Next steps :
------------

Re-organisation in multiple smaller files.


Installation :
--------------

The installation of the script itself is as simple as it could be : get it and you are done.
However, it calls a lot of other executables. Here's a non exhaustive list of them :

 * zsh - sudo apt-get install zsh
 * csh - sudo apt-get install csh
 * ash - sudo apt-get install ash
 * dash - sudo apt-get install dash
 * ksh - sudo apt-get install ksh
 * yash - sudo apt-get install yash
 * tcsh - sudo apt-get install tcsh
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
 * gfortran - sudo apt-get install gfortran
 * erl - sudo apt-get install erlang
 * gnat - sudo apt-get install gnat
 * fpc - sudo apt-get install fpc
 * gdc - sudo apt-get install gdc
 * valac - sudo apt-get install valac
 * gobjc - sudo apt-get install gobjc / sudo apt-get install gobjc++
 * dot - sudo apt-get install graphviz
 * swipl - sudo apt-get install swi-prolog
 * scilab - sudo apt-get install scilab
 * octave - sudo apt-get install octave
 * rhino - sudo apt-get install rhino
 * racket - sudo apt-get install racket
 * scala - sudo apt-get install scala
 * cobc - sudo apt-get install open-cobol
 * gforth - sudo apt-get install gforth
 * coq - sudo apt-get install coq
 * r - sudo apt-get install r-base r-base-dev
 * fsharpc - sudo apt-get install fsharp
 * gst - sudo apt-get install gnu-smalltalk
 * groovy - sudo apt-get install groovy
 * genius - sudo apt-get install genius
 * pike - sudo apt-get install pike7.8
 * fish - sudo apt-get install fish
 * ozc - sudo apt-get install mozart
 * iverilog - sudo apt-get install verilog
 * agda - sudo apt-get install agda
 * swift - wget http://swiftlang.org/packages/swift-0.94.1.tar.gz && tar xfz swift-0.94.1.tar.gz && export PATH=$PATH:/path/to/swift-0.94.1/bin
 * slsh - sudo apt-get install slsh
 * icont - sudo apt-get install icont
 * clojure - wget http://central.maven.org/maven2/org/clojure/clojure/1.6.0/clojure-1.6.0.jar
 * ceylon - wget http://staging.ceylon-lang.org/download/dist/1_0_Milestone1_deb && sudo dpkg -i 1_0_Milestone1_deb
 * factor - wget http://downloads.factorcode.org/releases/0.96/factor-linux-x86-32-0.96.tar.gz
 * sloccount (for asm_count, c_count, cobol_count, f90_count, fortran_count, haskell_count, lex_count, ml_count, modula3_count, objc_count, perl_count, python_count, ada_count, awk_count, csh_count, erlang_count, exp_count, lisp_count, makefile_count, ruby_count, sed_count, sh_count, tcl_count)- sudo apt-get install sloccount

(I should have kept track of things as I was needing them but it is too late now).

Related projects :
------------------

A few projects that are doing somewhat related tasks and are much more developped (had I known about them before, I probably wouldn't have worked on letscode) :

 * Syntastic : https://github.com/scrooloose/syntastic : integration of different syntax checkers in Vim
 * SingleCompile : https://github.com/xuhdev/SingleCompile : integration of multiple compilers/interpreters in Vim
 * CookieCutter : https://github.com/audreyr/cookiecutter : command line tool to create project from templates (I haven't look at it much yet).
 * Linguist : https://github.com/github/linguist : language detection
 * Rockstack : https://github.com/rockstack/rock : command line tool to simplify building, testing and running applications. Looks pretty similar but also much better. I might contribute to it quite soon.

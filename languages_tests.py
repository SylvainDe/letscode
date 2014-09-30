#!/usr/bin/python3
# -*- coding: utf-8
"""Unit tests for code in languages.py."""

from languages import Ada, Ash, Awk, Bash, CLanguage, Clojure, Cobol, Cpp, \
    Csh, Dash, DLanguage, Dot, FishShell, Forth, Fortran, Go, Groovy, Haskell, \
    Icon, Java, JavaScript, Julia, Ksh, Latex, Lisp, Lua, ObjectiveC, Nimrod, \
    Octave, Oz, Pascal, Perl, Php, Pike, Prolog, Python, Python2, Python3, \
    Racket, reST, RLanguage, Ruby, Rust, Scala, Scheme, Scilab, Shell, SLang, \
    SmallTalk, Swift, Tcl, Tcsh, Vala, Verilog, Yash, Zsh
from modeline import MODELINE_SUPPORTED_EDITORS
from collections import namedtuple
import tempfile
import unittest
import os
from helper import subprocess_call_wrapper, print_warning


# Idea - maybe interpretable language itself should inherit from unittest...
class TestableInterpretableLanguage(unittest.TestCase):
    """Unit tests for interpretable languages"""
    def interpreter_flow(self, klass):
        """Tests stuff"""
        namespace = namedtuple(
            'Namespace',
            'filename extension_mode override_file modeline text_editors style')
        filename = os.path.join(tempfile.mkdtemp(
            prefix='letscode' + klass.name + '_'), "filename")
        args = namespace(
            filename, 'auto', 'n', 'both', MODELINE_SUPPORTED_EDITORS, None)
        real_file = klass.get_actual_filename_to_use(args)

        # Cannot run if file does not exist
        self.assertFalse(os.path.isfile(real_file))
        self.assertFalse(klass.perform_action('run', args))

        # Can create
        self.assertTrue(klass.perform_action('create', args))
        self.assertTrue(os.path.isfile(real_file))

        if klass.is_ready():
            # Can run
            self.assertTrue(klass.perform_action('run', args))

            # Can run on its own
            if klass.nb_line_shebang:
                self.assertTrue(subprocess_call_wrapper([real_file]))
        else:
            print_warning("%s is not ready to be run" % klass.name)

        # Removing file -> code does not run
        os.remove(real_file)
        self.assertFalse(klass.perform_action('run', args))

    def test_python(self):
        """Tests stuff"""
        self.interpreter_flow(Python)
        self.interpreter_flow(Python2)
        self.interpreter_flow(Python3)

    def test_php(self):
        """Tests stuff"""
        self.interpreter_flow(Php)

    def test_julia(self):
        """Tests stuff"""
        self.interpreter_flow(Julia)

    def test_lua(self):
        """Tests stuff"""
        self.interpreter_flow(Lua)

    def test_ruby(self):
        """Tests stuff"""
        self.interpreter_flow(Ruby)

    def test_tcl(self):
        """Tests stuff"""
        self.interpreter_flow(Tcl)

    def test_shell(self):
        """Tests stuff"""
        self.interpreter_flow(Shell)

    def test_bash(self):
        """Tests stuff"""
        self.interpreter_flow(Bash)

    def test_zsh(self):
        """Tests stuff"""
        self.interpreter_flow(Zsh)

    def test_csh(self):
        """Tests stuff"""
        self.interpreter_flow(Csh)

    def test_tcsh(self):
        """Tests stuff"""
        self.interpreter_flow(Tcsh)

    def test_ksh(self):
        """Tests stuff"""
        self.interpreter_flow(Ksh)

    def test_ash(self):
        """Tests stuff"""
        self.interpreter_flow(Ash)

    def test_dash(self):
        """Tests stuff"""
        self.interpreter_flow(Dash)

    def test_yash(self):
        """Tests stuff"""
        self.interpreter_flow(Yash)

    def test_fishshell(self):
        """Tests stuff"""
        self.interpreter_flow(FishShell)

    def test_awk(self):
        """Tests stuff"""
        self.interpreter_flow(Awk)

    def test_scala(self):
        """Tests stuff"""
        self.interpreter_flow(Scala)

    def test_perl(self):
        """Tests stuff"""
        self.interpreter_flow(Perl)

    def test_nimrod(self):
        """Tests stuff"""
        self.interpreter_flow(Nimrod)

    def test_groovy(self):
        """Tests stuff"""
        self.interpreter_flow(Groovy)

    def test_smalltalk(self):
        """Tests stuff"""
        self.interpreter_flow(SmallTalk)

    def test_racket(self):
        """Tests stuff"""
        self.interpreter_flow(Racket)

    def test_javascript(self):
        """Tests stuff"""
        self.interpreter_flow(JavaScript)

    def test_swift(self):
        """Tests stuff"""
        self.interpreter_flow(Swift)

    def test_pike(self):
        """Tests stuff"""
        self.interpreter_flow(Pike)

    def test_forth(self):
        """Tests stuff"""
        self.interpreter_flow(Forth)

    def test_lisp(self):
        """Tests stuff"""
        self.interpreter_flow(Lisp)

    def test_scheme(self):
        """Tests stuff"""
        self.interpreter_flow(Scheme)

    def test_clojure(self):
        """Tests stuff"""
        self.interpreter_flow(Clojure)

    def test_slang(self):
        """Tests stuff"""
        self.interpreter_flow(SLang)

    def test_scilab(self):
        """Tests stuff"""
        self.interpreter_flow(Scilab)

    def test_octave(self):
        """Tests stuff"""
        self.interpreter_flow(Octave)

    def test_prolog(self):
        """Tests stuff"""
        self.interpreter_flow(Prolog)

    def test_r(self):
        """Tests stuff"""
        self.interpreter_flow(RLanguage)


class TestableCompilableLanguage(unittest.TestCase):
    """Unit tests for compilable languages"""
    def compilation_flow(self, klass):
        """Tests stuff"""
        namespace = namedtuple(
            'Namespace',
            'filename extension_mode override_file modeline text_editors style')
        filename = os.path.join(tempfile.mkdtemp(
            prefix='letscode' + klass.name + '_'), "filename")
        args = namespace(
            filename, 'auto', 'n', 'both', MODELINE_SUPPORTED_EDITORS, None)
        real_file = klass.get_actual_filename_to_use(args)
        output_file = klass.get_output_filename(real_file)

        # Cannot compile or run if file does not exist
        self.assertFalse(os.path.isfile(real_file))
        self.assertFalse(os.path.isfile(output_file))
        self.assertFalse(klass.perform_action('compile', args))
        self.assertFalse(klass.perform_action('run', args))

        # Cannot run before compilation
        self.assertTrue(klass.perform_action('create', args))
        self.assertFalse(klass.perform_action('run', args))

        # Can create
        self.assertTrue(klass.perform_action('create', args))
        self.assertTrue(os.path.isfile(real_file))
        self.assertFalse(os.path.isfile(output_file))

        if klass.is_ready():
            # Can compile and run
            self.assertTrue(klass.perform_action('compile', args))
            self.assertTrue(os.path.isfile(output_file))
            self.assertTrue(klass.perform_action('run', args))

            # Removing output file -> cannot run
            os.remove(output_file)
            self.assertFalse(os.path.isfile(output_file))
            self.assertFalse(klass.perform_action('run', args))

            # Can run after re-compilation
            self.assertTrue(klass.perform_action('compile', args))
            self.assertTrue(os.path.isfile(output_file))
            self.assertTrue(klass.perform_action('run', args))
        else:
            print_warning("%s is not ready to be run" % klass.name)

        os.remove(real_file)

        if klass.is_ready():
            # Removing file -> code is still running and compilation fails
            self.assertTrue(klass.perform_action('run', args))
            self.assertFalse(klass.perform_action('compile', args))

    def test_cpp(self):
        """Tests stuff"""
        self.compilation_flow(Cpp)

    def test_objc(self):
        """Tests stuff"""
        if False:
            self.compilation_flow(ObjectiveC)

    def test_c(self):
        """Tests stuff"""
        self.compilation_flow(CLanguage)

    def test_cobol(self):
        """Tests stuff"""
        self.compilation_flow(Cobol)

    def test_java(self):
        """Tests stuff"""
        self.compilation_flow(Java)

    def test_vala(self):
        """Tests stuff"""
        self.compilation_flow(Vala)

    def test_fortran(self):
        """Tests stuff"""
        self.compilation_flow(Fortran)

    def test_pascal(self):
        """Tests stuff"""
        self.compilation_flow(Pascal)

    def test_ada(self):
        """Tests stuff"""
        self.compilation_flow(Ada)

    def test_rust(self):
        """Tests stuff"""
        self.compilation_flow(Rust)

    def test_haskell(self):
        """Tests stuff"""
        self.compilation_flow(Haskell)

    def test_verilog(self):
        """Tests stuff"""
        self.compilation_flow(Verilog)

    def test_d(self):
        """Tests stuff"""
        self.compilation_flow(DLanguage)

    def test_go(self):
        """Tests stuff"""
        self.compilation_flow(Go)

    def test_oz(self):
        """Tests stuff"""
        self.compilation_flow(Oz)

    def test_icon(self):
        """Tests stuff"""
        self.compilation_flow(Icon)

    def test_latex(self):
        """Tests stuff"""
        self.compilation_flow(Latex)

    def test_rest(self):
        """Tests stuff"""
        self.compilation_flow(reST)

    def test_dot(self):
        """Tests stuff"""
        self.compilation_flow(Dot)

# vim: filetype=python tabstop=8 expandtab shiftwidth=4 softtabstop=4

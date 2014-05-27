#!/usr/bin/python3
# -*- coding: utf-8
"""Letscode is just a language-aware tool to quickly perform a bunch of usual
actions on a piece of code.

Letscode provides some kind of convenient abstraction over the different
languages you are working with and the related tools (compiler, interpreter,
etc). You might not want to remember how to write a simple hello-world, launch
your tests, compile, build the documentation, start the static analysis or
just run your code for all the languages you are working with. Also, it
provides a quick access to the relevant offline/online documents.

Letscode will guess what your code file is all about and do things for you.
For instance, in Vim, "letscode.py % -a compile" will launch letscode on the
current file, detect its language and compile it.

The different languages derive from a common class Language. Adding a new
language is pretty straightforward, one just need to inherit from Language
and override the different attributes (name, extensions, information, etc).
Then, the different actions can be defined via class methods. Code can be
re-used by inheriting from classes implementing usual behaviors such as
InterpretableLanguage or CompilableLanguage.
"""

# Ideas : Add option to tell whether we want to build stuff when
# we want to run and output file does not exist

# When code can be run or compiled, check if compiled version exists and if
# it is older or newer

# Use meta-stuff to get the list of actions automatically

# Check if multiple actions can be added in one-go : -a compile,run

# Add a way to pass additional parameter to command-line

# Add default actions (create?)

# Next steps are :
# - source control
# - refactoring (splitting into files) + adding unit tests

import argparse
import subprocess
import os
import stat
import myshutil as shutil
import unittest
import re
import tempfile
from collections import namedtuple
from textwrap import dedent


def print_info(*objs):
    """Prints INFO level messages"""
    # print('INFO:', *objs, file=sys.stdout)
    print('INFO: %s' % (objs))


def print_error(*objs):
    """Prints ERROR level messages"""
    # print('ERROR:', *objs, file=sys.stderr)
    print('ERROR: %s' % (objs))


def print_warning(*objs):
    """Prints WARNING level messages"""
    # print('WARNING:', *objs, file=sys.stderr)
    print('WARNING: %s' % (objs))


def print_debug(*objs):
    """Prints DEBUG level messages"""
    print('DEBUG: %s' % (objs))


def subprocess_call_wrapper(lst, stdin=None):
    """Wrapper around the subprocess.call functions."""
    print_debug('About to run "%s"' % ' '.join(lst))
    try:
        ret = subprocess.call(lst, stdin=stdin)
    except (OSError, IOError):
        ret = 127  # an error code
    except IndexError:
        ret = 127  # an error code
    except KeyboardInterrupt:
        ret = 127  # an error code
    print_debug('Command "%s" returned %d' % (lst[0] if lst else '', ret))
    return ret == 0


class Language(object):
    """A generic class for programming languages.

    Attributes:
        name        Name of the language (alphanumerical lowercase string)
        extensions  Extensions (list of string without leading dot)
        information Additional information about the language (useful links)
        comments    Pair of string defining how to begin and end comments."""
    name = None
    extensions = None
    information = None
    comments = (None, None)

    @classmethod
    def function_not_implemented(cls, function):
        """Default behavior for non-implemented functions."""
        print_error('%s not implemented for %s' % (function, cls.name))
        return False

    @classmethod
    def perform_actions(cls, args):
        """Perform the actions on the file - entry point for the class"""
        assert args.failure in ['stop', 'continue']
        stop_on_failure = args.failure == 'stop'
        results = []
        for action in args.action:
            ret = cls.perform_action(action, args)
            results.append((action, ret))
            if not ret and stop_on_failure:
                break
        # This should be moved outside the function - refactoring required
        greentick = '\033[92m✔'
        redcross = '\033[91m✘'
        undocolor = '\033[0m'
        for action, ret in results:
            print_info(
                (greentick if ret else redcross) +
                undocolor + ' ' + action)
        return all(res for _, res in results)

    @classmethod
    def perform_action(cls, action, args):
        """Perform a single on the file."""
        if hasattr(cls, action):
            return getattr(cls, action)(args)
        else:
            return cls.function_not_implemented(action)

    @classmethod
    def info(cls, _):
        """Gets information about the language. Wrapper around the information
            class member performing some pretty printing."""
        if cls.information is None:
            return cls.function_not_implemented('info')
        assert cls.name is not None
        corner, side, top = '+', '|', '-'
        title = ' Information about ' + cls.name + ' '
        line = corner + top * len(title) + corner
        print('\n'.join([line, side + title + side, line, cls.information]))
        return True

    @classmethod
    def get_actual_filename_to_use(cls, args):
        """Returns the filename to be used based on the name and an eventual
        extension."""
        filename, extmode = args.filename, args.extension_mode
        assert extmode in ['auto', 'never', 'always']

        # if extension mode is auto, we check if the extension is required
        # (if it is not in the list of extensions) and fallback to always/never
        if extmode == 'auto':
            extmode = 'never' if (os.path.splitext(filename)[1].lower() in
                            ("." + e for e in cls.extensions)) else 'always'
        assert extmode in ['never', 'always']

        # if extension is required, add the first one
        if extmode == 'always':
            filename += "." + cls.extensions[0]

        return filename

    @classmethod
    def create(cls, args):
        """Creates and ensures readiness of a file (shebang, boiler-plate code,
        execution rights, etc). Wrapper around real_create."""
        filename = cls.get_actual_filename_to_use(args)
        if os.path.isfile(filename):
            assert(args.override_file in ['n', 'y'])
            if args.override_file == 'n':
                print_info("File %s already exists" % filename)
                return True
        try:
            cls.real_create(filename)
        except IOError:
            print_error("Error while creating file" % filename)
            return False
        return True

    @classmethod
    def real_create(cls, filename):
        """Creates and ensures readiness of a file (shebang, boiler-plate code,
        execution rights, etc)."""
        with open(filename, 'w') as filed:
            filed.write(cls.get_header_info() + cls.get_file_content(filename))

    @classmethod
    def get_file_content(cls, _):
        """Returns the content to be put in the file."""
        return ""

    @classmethod
    def get_header_info(cls):
        """Get information to put at the top of the file."""
        return cls.comment_string("Generated by letscode")

    @classmethod
    def comment_string(cls, string):
        """Comment string."""
        beg, end = cls.comments
        if beg is None or end is None:
            print_warning('Cannot comment string for %s' % (cls.name))
            return ''  # Empty string is safe and shoudn't cause troubles
        assert beg  # beg is mandatory, end is conditionnal
        return '\n'.join(beg + ' ' +
                         s.strip().replace(end, '') +  # safety substitution
                         (' ' + end if end else '')
                         for s in string.split('\n')) + '\n'


class CompilableLanguage(Language):
    """A generic class for compilable languages.

    Attributes:
        compiler            Command to use to compile
        compiler_options    Options to give to the compiler."""
    compiler = None
    compiler_options = []

    @classmethod
    def man(cls, _):
        """Gets the manual"""
        return subprocess_call_wrapper(['man', cls.compiler])

    @classmethod
    def get_output_filename(cls, filename):
        """Gets the name of the output file"""
        return os.path.splitext(filename)[0] + '_out'

    @classmethod
    def compile(cls, args):
        """Compiles the file"""
        filename = cls.get_actual_filename_to_use(args)
        output = cls.get_output_filename(filename)
        return subprocess_call_wrapper(
            [cls.compiler] + cls.compiler_options + [filename, '-o', output])

    @classmethod
    def run(cls, args):
        """Runs the code"""
        # We do not look in '.' by default, let's use the abs path
        output = os.path.abspath(
            cls.get_output_filename(
                cls.get_actual_filename_to_use(args)))
        return subprocess_call_wrapper([output])


class CompiledDescriptionLanguages(CompilableLanguage):
    """A generic class for compiled descriptions languages : a compiler is used
    but there is nothing to run, just files to open."""

    @classmethod
    def run(cls, args):
        """Checks that the output file exists"""
        output = cls.get_output_filename(cls.get_actual_filename_to_use(args))
        if os.path.isfile(output):
            print_info("File %s can be open" % output)
            return True
        else:
            print_error("File %s does not exist" % output)
            return False


class CLanguage(CompilableLanguage):
    """C"""
    name = 'c'
    code_extensions = ['c']
    header_extensions = ['h']
    extensions = code_extensions + header_extensions
    compiler = 'gcc'
    compiler_options = ['-Wall', '-Wextra', '-std=c99']
    comments = ('//', '')  # or ('/*', '*/') but it's a bit more complicated
    information = dedent('''
- Wikipedia page : http://en.wikipedia.org/wiki/C_%28programming_language%29
- Official site :
- Documentation :
    * FAQ http://www.c-faq.com/
- Subreddit : http://www.reddit.com/r/C_Programming/
- Tools online :
    * Compiler (with ASM output - no run) http://gcc.godbolt.org/
    * Compiler (with ASM output - no run) http://assembly.ynh.io/
    * C gibberish <-> English http://cdecl.org/
    * Demangler : http://demangler.com/
    * Online compiler (run) http://coliru.stacked-crooked.com/
- Learn in Y minutes : http://learnxinyminutes.com/docs/c/
- RosettaCode : http://rosettacode.org/wiki/Category:C
''')

    @classmethod
    def debug(cls, args):
        """Launches the debugger"""
        output = cls.get_output_filename(cls.get_actual_filename_to_use(args))
        return subprocess_call_wrapper(['gdb', output])

    @classmethod
    def pretty(cls, args):
        """Makes the code prettier"""
        filename = cls.get_actual_filename_to_use(args)
        # or maybe using astyle
        return subprocess_call_wrapper(['indent', filename])

    @classmethod
    def get_header_content(cls, symbol):
        """Gets code for a header file"""
        return dedent('''
            #ifndef %s
            #define %s
            #endif
            ''') % (symbol, symbol)

    @classmethod
    def get_code_content(cls, included):
        """Gets code for an implementation file"""
        return dedent('''
            #include <stdio.h>
            //#include "%s"

            int main(int argc, char* argv[])
            {
                printf("Hello, world!\\n");
                return 0;
            }
            ''') % included

    @classmethod
    def get_file_content(cls, filename):
        """Returns the content to be put in the file."""
        # Different file content for implementations files and headers
        realfilename = os.path.split(filename)[1]
        base, ext = os.path.splitext(realfilename)
        if ext in ('.' + e for e in cls.header_extensions):
            return cls.get_header_content(
                '__%s__' % re.sub('[^A-Z]', '_', base.upper()))
        else:
            assert ext in ('.' + e for e in cls.code_extensions)
            return cls.get_code_content(base + '.' + cls.header_extensions[0])

    @classmethod
    def check(cls, args):
        """Calls static checker"""
        filename = cls.get_actual_filename_to_use(args)
        commands = {
            'cppcheck': ['--enable=all']
        }
        return_values = [
            subprocess_call_wrapper([c] + opt + [filename])
            for c, opt in commands.items()]
        return all(return_values)

    @classmethod
    def metrics(cls, args):
        """Gets metrics for code"""
        # to be done cppncss and cccc
        filename = cls.get_actual_filename_to_use(args)
        return subprocess_call_wrapper(['c_count', filename])


class ObjectiveC(CLanguage):
    """ObjectiveC"""
    name = 'objectivec'
    code_extensions = ['m', 'mm']
    header_extensions = ['h']
    extensions = code_extensions + header_extensions
    compiler_options = ['-Wall', '-Wextra']
    information = dedent('''
- Wikipedia page : http://en.wikipedia.org/wiki/Objective-C
- Official site : https://developer.apple.com/library/mac/documentation/cocoa/conceptual/ProgrammingWithObjectiveC/Introduction/Introduction.html
- Documentation :
- Tools online :
    * Try Objective C: http://tryobjectivec.codeschool.com/
    * Compile online : http://www.compileonline.com/compile_objective-c_online.php
- Subreddit : http://www.reddit.com/r/ObjectiveC/
- Learn in Y minutes : http://learnxinyminutes.com/docs/objective-c/
- RosettaCode : http://rosettacode.org/wiki/Category:Objective-C
''')


class Cpp(CLanguage):
    """Cpp"""
    name = 'cpp'
    code_extensions = ['cpp', 'cc', 'cxx', 'c++']
    header_extensions = ['hpp', 'hh', 'h', 'hxx', 'h++']
    extensions = code_extensions + header_extensions
    compiler = 'g++'
    compiler_options = ['-Wall', '-Wextra']
    information = dedent('''
- Wikipedia page : http://en.wikipedia.org/wiki/C++
- Official site : http://isocpp.org/
- Documentation : http://en.cppreference.com/
- Misc :
    * Guru of the week http://www.gotw.ca/gotw/
- Subreddit : http://www.reddit.com/r/cpp/
- Tools online :
    * Compiler (with ASM output - no run) http://gcc.godbolt.org/
    * Compiler (with ASM output - no run) http://assembly.ynh.io/
    * C gibberish <-> English http://cdecl.org/
    * Demangler : http://demangler.com/
    * Online compiler (run) http://coliru.stacked-crooked.com/
- RosettaCode : http://rosettacode.org/wiki/Category:C%2B%2B
''')

    @classmethod
    def get_code_content(cls, included):
        """Gets code for an implementation file"""
        return dedent('''
            #include <iostream>
            //#include "%s"

            int main(int argc, char* argv[])
            {
                std::cout << "Hello, world!" << std::endl;
                return 0;
            }
            ''') % included


class Java(CompilableLanguage):
    """Java"""
    name = 'java'
    extensions = ['java', 'class', 'jar']
    compiler = 'javac'  # support for gcj could be added if needed
    comments = ('//', '')
    information = dedent('''
- Wikipedia page : http://en.wikipedia.org/wiki/Java_%28programming_language%29
- Official site : http://www.java.com/
- Documentation : http://docs.oracle.com/javase/7/docs/api/
- Subreddit : http://www.reddit.com/r/java/
- Tools online :
    * Visualiser : http://cscircles.cemc.uwaterloo.ca/java_visualize/
    * Visualiser : http://visualize.learneroo.com/
    * Demangler : http://demangler.com/
    * REPL : http://www.javarepl.com/console.html
- Learn in Y minutes : http://learnxinyminutes.com/docs/java/
- RosettaCode : http://rosettacode.org/wiki/Category:Java
- Misc ressources :
    * Hidden features (StackOverflow) : http://stackoverflow.com/questions/15496/hidden-features-of-java
    ''')

    @classmethod
    def get_output_filename(cls, filename):
        """Gets the name of the output file"""
        return cls.get_classfile(filename) + '.class'

    @classmethod
    def get_classfile(cls, filename):
        """Gets the name of the file without extensions (name of the class)"""
        return os.path.splitext(filename)[0]

    @classmethod
    def get_file_content(cls, filename):
        """Returns the content to be put in the file."""
        classname = os.path.split(cls.get_classfile(filename))[1]
        return dedent('''
            public class %s {
                public static void main(String[] args) {
                    System.out.println("Hello, world!");
                }
            }''') % classname

    @classmethod
    def compile(cls, args):
        """Compiles the file"""
        filename = cls.get_actual_filename_to_use(args)
        return subprocess_call_wrapper(
            [cls.compiler, filename] + cls.compiler_options)

    @classmethod
    def run(cls, args):
        """Runs the code"""
        classfile = cls.get_classfile(cls.get_actual_filename_to_use(args))
        classpath, classname = os.path.split(classfile)
        return subprocess_call_wrapper(
            ['java', '-classpath', classpath, classname])

    @classmethod
    def debug(cls, args):
        """Launches the debugger"""
        classfile = cls.get_classfile(cls.get_actual_filename_to_use(args))
        classpath, classname = os.path.split(classfile)
        return subprocess_call_wrapper(
            ['jdb', '-classpath', classpath, classname])


class Vala(CompilableLanguage):
    """Vala"""
    name = 'vala'
    extensions = ['vala', 'vapi']
    compiler = 'valac'
    comments = ('//', '')
    information = dedent('''
- Wikipedia page : http://en.wikipedia.org/wiki/Vala_%28programming_language%29
- Official site : https://wiki.gnome.org/Projects/Vala
- Documentation : https://wiki.gnome.org/Projects/Vala/Documentation
- Subreddit : http://www.reddit.com/r/vala
- RosettaCode : http://rosettacode.org/wiki/Category:Vala
    ''')

    @classmethod
    def get_file_content(cls, _):
        """Returns the content to be put in the file."""
        return dedent('''
            int main () {
                print ("Hello, world!\\n");
                return 0;
            }
            ''')


class Pascal(CompilableLanguage):
    """Pascal"""
    name = 'pascal'
    extensions = ['pas']
    compiler = 'fpc'
    comments = ('//', '')  # or ('(*', '*)') or ('{', '}')
    information = dedent('''
- Wikipedia page : http://en.wikipedia.org/wiki/Pascal_%28programming_language%29
- Official site :
- Documentation :
- Subreddit :
    * http://www.reddit.com/r/pascal/
    * http://www.reddit.com/r/delphi/
- RosettaCode : http://rosettacode.org/wiki/Category:Pascal
    ''')

    @classmethod
    def get_file_content(cls, _):
        """Returns the content to be put in the file."""
        return dedent('''
            program HelloWorld;

            begin
                writeln('Hello, world!');
            end.
            ''')

    @classmethod
    def compile(cls, args):
        """Compiles the file"""
        filename = cls.get_actual_filename_to_use(args)
        output = cls.get_output_filename(filename)
        return subprocess_call_wrapper(
            [cls.compiler] + cls.compiler_options + [filename, '-o' + output])

    @classmethod
    def debug(cls, args):
        """Launches the debugger"""
        output = cls.get_output_filename(cls.get_actual_filename_to_use(args))
        return subprocess_call_wrapper(['gdb', output])


class Ada(CompilableLanguage):
    """Ada"""
    name = 'ada'
    extensions = ['adb', 'ads']
    compiler = 'gnat'  # many options - documentation with 'html' for instance
    compiler_options = ['make']
    comments = ('--', '')
    information = dedent('''
- Wikipedia page : http://en.wikipedia.org/wiki/Ada_(programming_language)
- Official site : http://www.adaic.org/
- Documentation :
- Subreddit : http://www.reddit.com/r/ada/
- RosettaCode : http://rosettacode.org/wiki/Category:Ada
    ''')

    @classmethod
    def get_procname(cls, filename):
        """Gets the name of the file without extensions (name of the procedure)"""
        return os.path.splitext(filename)[0]

    @classmethod
    def get_file_content(cls, filename):
        """Returns the content to be put in the file."""
        procname = os.path.split(cls.get_procname(filename))[1]
        return dedent('''
            with Ada.Text_IO; use Ada.Text_IO;
            procedure %s is
            begin
                Put_Line ("Hello, world!");
            end %s;
            ''') % (procname, procname)


class Fortran(CompilableLanguage):
    """Fortran"""
    name = 'fortran'
    extensions = ['f', 'for', 'f90', 'f95']
    compiler = 'gfortran'
    compiler_options = ['--free-form']
    comments = ('!', '')
    information = dedent('''
- Wikipedia page : http://en.wikipedia.org/wiki/Fortran
- Official site :
- Documentation : http://www.fortran90.org/
- Subreddit : http://www.reddit.com/r/fortran/
- RosettaCode : http://rosettacode.org/wiki/Category:Fortran
    ''')

    @classmethod
    def get_file_content(cls, _):
        """Returns the content to be put in the file."""
        return dedent('''
            program helloworld
            print *, "Hello, world!"
            end program helloworld
            ''')

    @classmethod
    def debug(cls, args):
        """Launches the debugger"""
        output = cls.get_output_filename(cls.get_actual_filename_to_use(args))
        return subprocess_call_wrapper(['gdb', output])

    @classmethod
    def metrics(cls, args):
        """Gets metrics for code"""
        filename = cls.get_actual_filename_to_use(args)
        return subprocess_call_wrapper(['fortran_count', filename])


class Cobol(CompilableLanguage):
    """Cobol"""
    name = 'cobol'
    extensions = ['cob', 'cbl']
    comments = ('       *', '')
    compiler = 'cobc'
    compiler_options = ['-x']
    information = dedent('''
- Wikipedia page : http://en.wikipedia.org/wiki/COBOL
- Subreddit : http://www.reddit.com/r/cobol
- Tools online :
    * Compile online : http://www.compileonline.com/compile_cobol_online.php
- RosettaCode : http://rosettacode.org/wiki/Category:COBOL
    ''')

    @classmethod
    def get_file_content(cls, _):
        """Returns the content to be put in the file."""
        # No dedent here - leading spaces matter
        return '''
       IDENTIFICATION DIVISION.
       PROGRAM-ID. HELLO-WORLD.
       PROCEDURE DIVISION.
           DISPLAY 'Hello world!'.
           STOP RUN.
        '''

    @classmethod
    def metrics(cls, args):
        """Gets metrics for code"""
        filename = cls.get_actual_filename_to_use(args)
        return subprocess_call_wrapper(['cobol_count', filename])


class Haskell(CompilableLanguage):
    """Haskell"""
    name = 'haskell'
    extensions = ['hs', 'lhs']
    compiler = 'ghc'
    comments = ('--', '')
    information = dedent('''
- Wikipedia page : http://en.wikipedia.org/wiki/Haskell_%28programming_language%29
- Official site : http://www.haskell.org/
- Documentation : http://www.haskell.org/ghc/docs/7.6-latest/html/libraries/index.html
- Subreddit : http://www.reddit.com/r/haskell/
- Tools online :
    * Try Haskell : http://tryhaskell.org/
- Learn in Y minutes : http://learnxinyminutes.com/docs/haskell/
- RosettaCode : http://rosettacode.org/wiki/Category:Haskell
''')

    @classmethod
    def get_file_content(cls, _):
        """Returns the content to be put in the file."""
        return dedent('''
            main = putStrLn "Hello, world!"
            ''')

    @classmethod
    def debug(cls, args):
        """Launches the debugger"""
        # Another option is to use GHCi
        output = cls.get_output_filename(cls.get_actual_filename_to_use(args))
        return subprocess_call_wrapper(['gdb', output])

    @classmethod
    def metrics(cls, args):
        """Gets metrics for code"""
        filename = cls.get_actual_filename_to_use(args)
        return subprocess_call_wrapper(['haskell_count', filename])


class DLanguage(CompilableLanguage):
    """D"""
    name = 'd'
    extensions = ['d']
    compiler = 'gdc'
    comments = ('//', '')
    information = dedent('''
- Wikipedia page : http://en.wikipedia.org/wiki/D_%28programming_language%29
- Official site : http://dlang.org/
- Documentation :
    * Language reference : http://dlang.org/spec.html
    * Library reference : dlang.org/phobos/index.html
- Subreddit :
    * D Paste : http://dpaste.dzfl.pl/
    * Compile Online : http://www.compileonline.com/compile_d_online.php
- Tools online : http://www.reddit.com/r/d_language/
- RosettaCode : http://rosettacode.org/wiki/Category:D
''')

    @classmethod
    def get_file_content(cls, _):
        """Returns the content to be put in the file."""
        return dedent('''
            import std.stdio;

            void main()
            {
                writeln("Hello, world!");
            }
            ''')

    @classmethod
    def debug(cls, args):
        """Launches the debugger"""
        output = cls.get_output_filename(cls.get_actual_filename_to_use(args))
        return subprocess_call_wrapper(['gdb', output])


class MarkupLanguage(Language):
    """A generic class for markup languages"""
    comments = ('<!--', '-->')


class HTML(MarkupLanguage):
    """HTML"""
    name = 'html'
    extensions = ['html']
    information = dedent('''
- Wikipedia page : http://en.wikipedia.org/wiki/HTML
- Official site : http://www.w3.org/
- Subreddit : http://www.reddit.com/r/html
- Tools online :
    * W3C Validator : http://validator.w3.org/
    * HTML Obfuscator : http://htmlobfuscator.com/
''')

    @classmethod
    def pretty(cls, args):
        """Makes the code prettier"""
        filename = cls.get_actual_filename_to_use(args)
        return subprocess_call_wrapper(
            ['xmllint', '--format', '--html', filename])


class XML(MarkupLanguage):
    """XML"""
    name = 'xml'
    extensions = ['xml']
    information = dedent('''
- Wikipedia page : http://en.wikipedia.org/wiki/XML
- Learn in Y minutes : http://learnxinyminutes.com/docs/xml/
''')

    @classmethod
    def pretty(cls, args):
        """Makes the code prettier"""
        filename = cls.get_actual_filename_to_use(args)
        return subprocess_call_wrapper(['xmllint', '--format', filename])


class CSS(Language):
    """CSS"""
    name = 'css'
    extensions = ['css']
    comments = ('/*', '*/')
    information = dedent('''
- Wikipedia page : http://en.wikipedia.org/wiki/Cascading_Style_Sheets
- Official site : http://www.w3.org/Style/CSS/Overview.en.html
- Documentation :
- Tools online :
    * CSS Lint : http://csslint.net/
- Learn in Y minutes : http://learnxinyminutes.com/docs/css/
''')


class JSON(Language):
    """JSON"""
    name = 'json'
    extensions = ['json']
    comments = (None, None)  # No comment in JSON
    information = dedent('''
- Wikipedia page : http://en.wikipedia.org/wiki/JSON
- Official site : http://www.json.org/
- Documentation :
- Tools online :
    * JSON Lint : http://jsonlint.com/
    * JSON Schema Lint : http://jsonschemalint.com
    * JSON Selector : http://jsonselector.com/
    * Geo JSON Lint : http://geojsonlint.com/
- Learn in Y minutes : http://learnxinyminutes.com/docs/json/
''')


class YAML(Language):
    """YAML"""
    name = 'yaml'
    extensions = ['yaml']
    comments = ('#', '')
    information = dedent('''
- Wikipedia page : http://en.wikipedia.org/wiki/YAML
- Official site : http://yaml.org/
- Documentation : http://www.yaml.org/spec/1.2/spec.html
- Tools online :
    * YAML Lint : http://yamllint.com/
- Learn in Y minutes : http://learnxinyminutes.com/docs/yaml/
''')


class CoffeeScript(Language):
    """CoffeeScript"""
    name = 'coffeescript'
    extensions = ['coffee']
    comments = ('#', '')
    information = dedent('''
- Wikipedia page : http://en.wikipedia.org/wiki/CoffeeScript
- Official site : http://coffeescript.org/
- Documentation :
- Tools online :
    * JS to Coffee : http://js2coffee.org/
    * Coffee Lint : http://www.coffeelint.org/
- Learn in Y minutes : http://learnxinyminutes.com/docs/coffeescript/
''')


class Markdown(Language):
    """Markdown"""
    name = 'markdown'
    extensions = ['md']
    # From http://stackoverflow.com/questions/4823468/store-comments-in-markdown-syntax
    comments = ('[//]: # (', ')')
    information = dedent('''
- Wikipedia page : http://en.wikipedia.org/wiki/Markdown
- Official site : http://daringfireball.net/projects/markdown/
- Misc :
    * Github flavored markdown : https://help.github.com/articles/github-flavored-markdown
- Documentation :
    * Basic https://help.github.com/articles/markdown-basics
- Tools online :
    * Markdown editors/viewers:
        http://daringfireball.net/projects/markdown/dingus
        http://www.markdownviewer.com/
        http://markable.in/editor/
        http://dillinger.io/
        https://stackedit.io/
    * HTML to text http://www.aaronsw.com/2002/html2text/
''')


class InterpretableLanguage(Language):
    """A generic class for interpretable languages.

    Attributes:
        interpreter (via get_interpreter_name) Name of the interpreter
        interpreter_options Options for the interpreter."""
    interpreter_options = []
    comments = ('#', '')

    @classmethod
    def get_interpreter_name(cls):
        """Gets the name of the interpreter"""
        return cls.name

    @classmethod
    def man(cls, _):
        """Gets the manual"""
        return subprocess_call_wrapper(['man', cls.get_interpreter_name()])

    @classmethod
    def run(cls, args):
        """Runs the code"""
        filename = cls.get_actual_filename_to_use(args)
        return subprocess_call_wrapper(
            [cls.get_interpreter_name()] +
            cls.interpreter_options +
            [filename])

    @classmethod
    def real_create(cls, filename):
        """Creates and ensures readiness of a file (shebang, boiler-plate code,
        execution rights, etc)."""
        with open(filename, 'w') as filed:
            filed.write(cls.get_shebang_line() +
                        cls.get_closing_shebang_line() +
                        cls.get_header_info() +
                        cls.get_file_content(filename))
        InterpretableLanguage.give_exec_rights(filename)

    @classmethod
    def get_shebang_line(cls):
        """Return the shebang line"""
        interpreter = cls.get_interpreter_name()
        path = shutil.which(interpreter)
        if path is None:
            return cls.comment_string('interpreter "%s" not found' % interpreter)
        return '#!' + ' '.join([path] + cls.interpreter_options) + '\n'

    @classmethod
    def get_closing_shebang_line(cls):
        """Return the tag to close the shebang line"""
        return ''

    @staticmethod
    def give_exec_rights(filename):
        """Give the execution rights on a file"""
        os.chmod(filename, os.stat(filename).st_mode | stat.S_IEXEC)


class Shell(InterpretableLanguage):
    """A generic class for shell scripts"""
    name = 'sh'
    extensions = ['sh']
    comments = ('#', '')
    information = dedent('''
- Wikipedia page :
- Official site :
- Documentation :
- Tool online:
    * Explain shell http://explainshell.com/
- Subreddit :
''')

    @classmethod
    def get_file_content(cls, _):
        """Returns the content to be put in the file."""
        return dedent('''
            echo "Hello, world!"
            ''')

    @classmethod
    def metrics(cls, args):
        """Gets metrics for code"""
        filename = cls.get_actual_filename_to_use(args)
        return subprocess_call_wrapper(['sh_count', filename])


class Bash(Shell):
    """Bash"""
    name = 'bash'
    extensions = ['sh']
    information = dedent('''
- Wikipedia page : http://en.wikipedia.org/wiki/Bash_%28Unix_shell%29
- Official site : https://www.gnu.org/software/bash/
- Documentation :
    * Bash reference manual http://www.gnu.org/software/bash/manual/bashref.html
    * Bash scripting guide www.tldp.org/LDP/abs/html/
    * Bash guide http://mywiki.wooledge.org/BashGuide
- Subreddit : http://www.reddit.com/r/bash/
- Learn in Y minutes : http://learnxinyminutes.com/docs/bash/
''')


class Zsh(Shell):
    """Zsh"""
    name = 'zsh'
    extensions = ['sh']
    information = dedent('''
- Wikipedia page : http://en.wikipedia.org/wiki/Z_shell
- Official site : http://zsh.sourceforge.net/
- Documentation : http://zsh.sourceforge.net/Doc/Release/zsh_toc.html
- Wiki : http://zshwiki.org/home/
- Subreddit : http://www.reddit.com/r/zsh
- Tools online :
- RosettaCode :
''')


class Tcl(Shell):
    """Tcl"""
    name = 'tcl'
    extensions = ['tcl']
    information = dedent('''
- Wikipedia page : http://en.wikipedia.org/wiki/Tcl
- Official site : http://www.tcl.tk/
- Documentation :
    * http://www.tcl.tk/doc/
    * http://www.tkdocs.com/
- Subreddit : http://www.reddit.com/r/tcl
- Tools online :
- RosettaCode : http://rosettacode.org/wiki/Category:Tcl
''')

    @classmethod
    def get_interpreter_name(cls):
        """Gets the name of the interpreter"""
        return 'tclsh'

    @classmethod
    def get_file_content(cls, _):
        """Returns the content to be put in the file."""
        return dedent('''
            puts "Hello, world!"
            ''')

    @classmethod
    def metrics(cls, args):
        """Gets metrics for code"""
        filename = cls.get_actual_filename_to_use(args)
        return subprocess_call_wrapper(['tcl_count', filename])


class Awk(InterpretableLanguage):
    """Awk"""
    name = 'awk'
    extensions = ['awk']
    interpreter_options = ['-f']
    information = dedent('''
- Wikipedia page : http://en.wikipedia.org/wiki/AWK
- Official site : http://www.cs.bell-labs.com/cm/cs/awkbook/index.html
- Documentation :
    * http://awk.info/
    * http://www.grymoire.com/Unix/Awk.html
    * http://www.gnu.org/software/gawk/manual/gawk.html
    * http://www.pement.org/awk/awk1line.txt
- Subreddit : http://www.reddit.com/r/awk
- Tools online :
    * http://www.compileonline.com/execute_awk_online.php
- RosettaCode : http://rosettacode.org/wiki/Category:AWK
''')

    @classmethod
    def get_file_content(cls, _):
        """Returns the content to be put in the file."""
        return "BEGIN { print \"Hello, world!\" }"


class Ruby(InterpretableLanguage):
    """Ruby"""
    name = 'ruby'
    extensions = ['rb', 'rbw']
    information = dedent('''
- Wikipedia page : http://en.wikipedia.org/wiki/Ruby_%28programming_language%29
- Official site : https://www.ruby-lang.org/fr/
- Online tools :
    * Visualise Ruby : http://www.onlinerubytutor.com/exercise/D000
    * Execute Ruby online : http://www.compileonline.com/execute_ruby_online.php
    * Try Ruby : http://tryruby.org/
- Subreddit : http://www.reddit.com/r/ruby/
- Learn in Y minutes : http://learnxinyminutes.com/docs/ruby/
- RosettaCode : http://rosettacode.org/wiki/Category:Ruby
    ''')

    @classmethod
    def get_file_content(cls, _):
        """Returns the content to be put in the file."""
        return dedent('''
            puts "Hello, world!"
            ''')

    @classmethod
    def debug(cls, args):
        """Launches the debugger"""
        filename = cls.get_actual_filename_to_use(args)
        return subprocess_call_wrapper(
            [cls.get_interpreter_name(), '-rdebug', filename])

    @classmethod
    def interactive(cls, args):
        """Executes the script and enters interactive mode"""
        # irb does not look in '.' by default, let's give it the abs path
        filename = os.path.abspath(cls.get_actual_filename_to_use(args))
        return subprocess_call_wrapper(['irb', '-r', filename])

    @classmethod
    def metrics(cls, args):
        """Gets metrics for code"""
        filename = cls.get_actual_filename_to_use(args)
        return subprocess_call_wrapper(['ruby_count', filename])

    @classmethod
    def check(cls, args):
        """Calls static checker"""
        filename = cls.get_actual_filename_to_use(args)
        commands = {
            cls.get_interpreter_name(): ['-c']
        }
        return_values = [
            subprocess_call_wrapper([c] + opt + [filename])
            for c, opt in commands.items()]
        return all(return_values)


class JavaScript(InterpretableLanguage):
    """JavaScript"""
    name = 'javascript'
    extensions = ['js']
    comments = ('//', '')
    information = dedent('''
- Wikipedia page : http://en.wikipedia.org/wiki/JavaScript
- "Official" sites :
    * https://developer.mozilla.org/en-US/docs/Web/JavaScript
    * http://www.ecmascript.org/
- Subreddit : http://www.reddit.com/r/javascript/
- Tools online :
    * JS Bin http://jsbin.com/
    * JS Hint http://www.jshint.com/
    * JS Lint http://www.jslint.com/
    * JS Lint http://www.javascriptlint.com/online_lint.php
    * JS Perf http://jsperf.com/
    * JS Fiddle http://jsfiddle.net/
    * JS Compress http://jscompress.com/
    * JS Compressor http://www.jscompressor.com/
    * JS Minifier http://javascript-minifier.com/
    * JS Mini http://www.jsmini.com/
    * JS Obfuscator http://packer.50x.eu/
    * JS Obfuscator http://javascriptobfuscator.com/
    * JS Obfuscate http://www.jsobfuscate.com/
    * UglifyJS http://lisperator.net/uglifyjs/#demo
    * Visualise Javascript http://jstutor.herokuapp.com/
    * Javascript interpreter (with pause and undo) http://wthimbleby.github.io/tailspin/
    * Google playground (Google APIs) http://code.google.com/apis/ajax/playground/
    * Fun : Sound of JS http://soundofjs.com
- Learn in Y minutes : http://learnxinyminutes.com/docs/javascript/
- RosettaCode : http://rosettacode.org/wiki/Category:JavaScript
    ''')

    @classmethod
    def get_interpreter_name(cls):
        """Gets the name of the interpreter"""
        return 'rhino'

    @classmethod
    def get_file_content(cls, _):
        """Returns the content to be put in the file."""
        interpreter = cls.get_interpreter_name()
        if interpreter == 'rhino':
            return "print('Hello, world!');"
        elif interpreter == 'console':
            return "console.log('Hello, world!');"
        elif interpreter == 'html':
            return "document.write('Hello, world!');"
        elif interpreter == 'alert':
            return "alert('Hello, world!');"
        assert False


class Perl(InterpretableLanguage):
    """Perl"""
    name = 'perl'
    extensions = ['pl']
    information = dedent('''
- Wikipedia page : http://en.wikipedia.org/wiki/Perl
- Official site : http://www.perl.org/
- Documentation : http://perldoc.perl.org/
- Other ressources :
    * http://www.cpan.org/
    * www.perlfoundation.org
    * http://www.perlmonks.org/
    * http://www.catonmat.net/blog/perl-one-liners-explained-part-one/
- Subreddit : http://www.reddit.com/r/perl/
- Learn in Y minutes : http://learnxinyminutes.com/docs/perl/
- RosettaCode : http://rosettacode.org/wiki/Category:Perl
    ''')

    @classmethod
    def get_file_content(cls, _):
        """Returns the content to be put in the file."""
        return dedent('''
            use strict;
            use warnings;
            print "Hello, world!\n";
            ''')

    @classmethod
    def metrics(cls, args):
        """Gets metrics for code"""
        filename = cls.get_actual_filename_to_use(args)
        return subprocess_call_wrapper(['perl_count', filename])


class Php(InterpretableLanguage):
    """Php"""
    name = 'php'
    extensions = ['php', 'php3', 'php4', 'php5', 'phtml']
    information = dedent('''
- Wikipedia page : http://en.wikipedia.org/wiki/PHP
- Official site : http://www.php.net/
- Documentation : http://www.php.net/manual/en/
- Subreddit : http://www.reddit.com/r/php
- Tools online :
    * Sandbox with multiple versions http://sandbox.onlinephpfunctions.com/
    * Performances on 100+ PHP versions http://3v4l.org/
    * PHP Fiddle http://phpfiddle.org/
    * PHP Sandbox http://www.exorithm.com/algorithm/sandbox
    * PHP Lint www.icosaedro.it/phplint/phplint-on-line.html
- Learn in Y minutes : http://learnxinyminutes.com/docs/php/
- RosettaCode : http://rosettacode.org/wiki/Category:PHP
    ''')

    @classmethod
    def get_file_content(cls, _):
        """Returns the content to be put in the file."""
        return dedent('''<?php print("Hello, world!\\n");?>''')

    @classmethod
    def check(cls, args):
        """Calls static checker"""
        filename = cls.get_actual_filename_to_use(args)
        commands = {
            cls.get_interpreter_name(): ['-l']
        }
        return_values = [
            subprocess_call_wrapper([c] + opt + [filename])
            for c, opt in commands.items()]
        return all(return_values)

    @classmethod
    def metrics(cls, args):
        """Gets metrics for code"""
        filename = cls.get_actual_filename_to_use(args)
        return subprocess_call_wrapper(['php_count', filename])


# Maybe this should inherit from interpretable language and compilable
# language but I am too scared at the moment. Let's write tests first
class Python(InterpretableLanguage):
    """Python"""
    name = 'python'
    extensions = ['py', 'pyc', 'pyo']
    information = dedent('''
- Wikipedia page : http://en.wikipedia.org/wiki/Python_%28programming_language%29
- Official site : https://www.python.org/
- List of PEPs : http://legacy.python.org/dev/peps/
    * PEP 8 : http://legacy.python.org/dev/peps/pep-0008/
    * PEP 20: The Zen of Python http://legacy.python.org/dev/peps/pep-0020/
- Documentation by version : https://www.python.org/doc/versions/
    * Python 2.7 : https://docs.python.org/release/2.7.6/
        # Library Reference : https://docs.python.org/release/2.7.6/library/index.html
    * Python 3.4 : https://docs.python.org/release/3.4.0
        # Library Reference : https://docs.python.org/release/3.4.0/library/index.html
    * The Hitchhiker’s Guide to Python : http://docs.python-guide.org/
- Wiki : https://wiki.python.org/moin/
- Videos : http://www.pyvideo.org/
- Subreddit : http://www.reddit.com/r/Python/
- Tools online :
    * PEP 8 online : http://pep8online.com/
    * Python tutor - visualisation : http://www.pythontutor.com/visualize.html
    * Python shell : http://shell.appspot.com/
    * Python interpreter : http://mathcs.holycross.edu/~kwalsh/python/
    * Learn Python with interactive console : http://www.learnpython.org/
    * Python Anywhere https://www.pythonanywhere.com/try-ipython/
    * Client side Python interpreter http://www.skulpt.org/
    * Python checker http://pych.atomidata.com/
    * Python Obfuscator http://pyobf.herokuapp.com/
- Learn in Y minutes :
    * http://learnxinyminutes.com/docs/python/
    * http://learnxinyminutes.com/docs/python3/
- RosettaCode : http://rosettacode.org/wiki/Category:Python
- Misc ressources :
    * Hidden features (StackOverflow) : http://stackoverflow.com/questions/101268/hidden-features-of-python
    * Snippets/tips/tricks (/r/Python) : http://www.reddit.com/r/Python/comments/19dir2/whats_the_one_code_snippetpython_tricketc_did_you/
    ''')

    @classmethod
    def get_file_content(cls, _):
        """Returns the content to be put in the file."""
        return dedent('''
            """Docstring for Python module"""


            def main():
                """Main function"""
                print("Hello, world!")


            if __name__ == "__main__":
                main()
            ''')

    @classmethod
    def get_module_name(cls, filename):
        """Gets the name of the file without extensions (name of the module)"""
        return os.path.splitext(filename)[0]

    @classmethod
    def unittest(cls, args):
        """Runs the unit tests"""
        filename = cls.get_actual_filename_to_use(args)
        return subprocess_call_wrapper(
            [cls.get_interpreter_name(), '-m', 'unittest', filename])

    @classmethod
    def compile(cls, args):
        """Compiles the code"""
        # Could be done with py_compile - don't know the difference
        # Options can be added for optimisations
        # Maybe this could use Multiple Inheritance and that would be damn sexy
        filename = cls.get_actual_filename_to_use(args)
        return subprocess_call_wrapper(
            [cls.get_interpreter_name(), '-m', 'compileall', filename])

    @classmethod
    def profile(cls, args):
        """Launches the profiler"""
        filename = cls.get_actual_filename_to_use(args)
        # using profile but cProfile works too
        return subprocess_call_wrapper(
            [cls.get_interpreter_name(), '-m', 'profile', filename])

    @classmethod
    def doctest(cls, args):
        """Runs the tests in documentation using the doctest module"""
        filename = cls.get_actual_filename_to_use(args)
        return subprocess_call_wrapper(
            [cls.get_interpreter_name(), '-m', 'doctest', '-v', filename])

    @classmethod
    def debug(cls, args):
        """Launches the debugger"""
        filename = cls.get_actual_filename_to_use(args)
        return subprocess_call_wrapper(
            [cls.get_interpreter_name(), '-m', 'pdb', filename])

    @classmethod
    def gendoc(cls, args):
        """Generates the documentation"""
        module = cls.get_module_name(cls.get_actual_filename_to_use(args))
        return subprocess_call_wrapper(
            [cls.get_interpreter_name(), '-m', 'pydoc', module])

    @classmethod
    def interactive(cls, args):
        """Executes the script and enters interactive mode"""
        filename = cls.get_actual_filename_to_use(args)
        return subprocess_call_wrapper(
            [cls.get_interpreter_name(), '-i', filename])

    @classmethod
    def uml(cls, args):
        """Generated UML Graph"""
        filename = cls.get_actual_filename_to_use(args)
        # Other options exist : http://modeling-languages.com/uml-tools/#python
        return cls.pyreverse(filename)

    @classmethod
    def pyreverse(cls, filename):
        """Calls pyreverse to get UML Graph"""
        return subprocess_call_wrapper(['pyreverse', filename, '-p', filename])

    @classmethod
    def check(cls, args):
        """Calls static checker"""
        filename = cls.get_actual_filename_to_use(args)
        commands = {
            'pep8':      [],
            'pylint':    [],
            'pyflakes':  [],
            'pychecker': ['--limit', '100']
        }
        return_values = [
            subprocess_call_wrapper([c] + opt + [filename])
            for c, opt in commands.items()]
        return all(return_values)

    @classmethod
    def metrics(cls, args):
        """Gets metrics for code"""
        filename = cls.get_actual_filename_to_use(args)
        return subprocess_call_wrapper(['python_count', filename])


class Python2(Python):
    """Python 2"""
    name = 'python2'

    @classmethod
    def to_py3(cls, args):
        """Converts code from Python 2 to Python 3"""
        filename = cls.get_actual_filename_to_use(args)
        return subprocess_call_wrapper(['2to3', filename])


class Python3(Python):
    """Python 3"""
    name = 'python3'


class Julia(InterpretableLanguage):
    """Julia"""
    name = 'julia'
    extensions = ['jl']
    information = dedent('''
- Wikipedia page : http://en.wikipedia.org/wiki/Julia_%28programming_language%29
- Official site : http://julialang.org/
- Documentation : http://docs.julialang.org/en/latest
- Subreddit : http://www.reddit.com/r/Julia/
- Learn in Y minutes : http://learnxinyminutes.com/docs/julia/
- RosettaCode : http://rosettacode.org/wiki/Category:Julia
''')

    @classmethod
    def get_file_content(cls, _):
        """Returns the content to be put in the file."""
        return dedent('''
            println("Hello, world!")
            ''')


class VimScript(InterpretableLanguage):
    """VimScript"""
    name = 'vimscript'
    extensions = ['vim']
    comments = ('"', '')
    information = dedent('''
- Wikipedia page : http://en.wikipedia.org/wiki/Vim_script
- Official site : http://www.vim.org/
- Documentation :
    * http://vimdoc.sourceforge.net/htmldoc/usr_41.html
    * http://learnvimscriptthehardway.stevelosh.com/
    * Examples http://www.vim.org/scripts/
- Subreddit : http://www.reddit.com/r/vim/
- RosettaCode : http://rosettacode.org/wiki/Category:Vim_Script
''')

    @classmethod
    def get_file_content(cls, _):
        """Returns the content to be put in the file."""
        return dedent('''
            echo "Hello, world!"
        ''')

    @classmethod
    def get_interpreter_name(cls):
        """Gets the name of the interpreter"""
        return 'vim'

    @classmethod
    def run(cls, args):
        """Runs the code"""
        filename = cls.get_actual_filename_to_use(args)
        return subprocess_call_wrapper(
            [cls.get_interpreter_name(), '-u', filename, '-c', ':q'])

    @classmethod
    def debug(cls, args):
        """Launches the debugger"""
        filename = cls.get_actual_filename_to_use(args)
        return subprocess_call_wrapper(
            [cls.get_interpreter_name(), '-D', '-u', filename, '-c', ':q'])


class Lua(InterpretableLanguage):
    """Lua"""
    name = 'lua'
    extensions = ['lua']
    comments = ('--', '')
    information = dedent('''
- Wikipedia page : http://en.wikipedia.org/wiki/Lua_%28programming_language%29
- Official site : http://www.lua.org/
- Documentation : www.lua.org/docs.html
- Subreddit : http://www.reddit.com/r/lua/
- Tools online :
    * Demo http://www.lua.org/demo.html
- Learn in Y minutes : http://learnxinyminutes.com/docs/lua/
- RosettaCode : http://rosettacode.org/wiki/Category:Lua
''')

    @classmethod
    def get_file_content(cls, _):
        """Returns the content to be put in the file."""
        return dedent('''
            print("Hello, world!")
        ''')


class DatabaseLanguage(Language):
    """A generic class for database languages"""


class SQL(DatabaseLanguage):
    """SQL"""
    name = 'sql'
    extensions = ['sql']
    comments = ('--', '')
    information = dedent('''
- Wikipedia page : http://en.wikipedia.org/wiki/SQL
- Official site :
- Documentation :
- Subreddit : http://www.reddit.com/r/SQL/
- Tools online :
    * SQL Fiddle http://sqlfiddle.com/
    * SQL query visualisation http://queryviz.com/online/
    * SQL Hands on http://www.headfirstlabs.com/sql_hands_on/
    * SQL sandbox http://coderzone.org/sqlsandbox/
- RosettaCode : http://rosettacode.org/wiki/Category:SQL
''')


class Dot(CompiledDescriptionLanguages):
    """Graph description language"""
    name = "dot"
    extensions = ['gv', 'dot']
    compilers = [  # change order of compilers for other types of graph
        'dot',    # directed graphs
        'neato',  # undirected graphs
        'twopi',  # radial layouts of graphs
        'circo',  # circular layouts of graphs
        'fdp',    # undirected graphs
        'sfdp',   # large undirected graphs
    ]
    compiler = compilers[0]
    compiler_options = []
    comments = ('//', '')
    information = dedent('''
- Wikipedia page : http://en.wikipedia.org/wiki/DOT_%28graph_description_language%29
- Official site : http://www.graphviz.org/
- Documentation : http://www.graphviz.org/Documentation.php
- Tools online :
    * Visualization :
        http://graphviz-dev.appspot.com/
        http://sandbox.kidstrythisathome.com/erdos/index.html
        http://rise4fun.com/agl
        http://ashitani.jp/gv/
        http://oodavid.com/gviz/
''')

    @classmethod
    def get_output_filename(cls, filename):
        """Gets the name of the output file"""
        return os.path.splitext(filename)[0] + '_' + cls.compiler + '.png'

    @classmethod
    def compile(cls, args):
        """Compiles the code"""
        filename = cls.get_actual_filename_to_use(args)
        return subprocess_call_wrapper([
            cls.compiler,
            '-Tpng',
            filename,
            '-o',
            cls.get_output_filename(filename)])

    @classmethod
    def get_file_content(cls, _):
        """Returns the content to be put in the file."""
        return dedent('''
            digraph G
            {
                Hello->World
            }
            ''')


class Latex(CompiledDescriptionLanguages):
    """LaTeX (or TeX - it doesn't really matter here, does it?)"""
    name = 'latex'
    extensions = ['tex']
    compiler = None
    compiler_options = []
    comments = ('%', '')
    information = dedent('''
- Wikipedia page :
    * http://en.wikipedia.org/wiki/TeX
    * http://en.wikipedia.org/wiki/LaTeX
- Official site : http://www.latex-project.org/
- Other ressources :
    * http://www.ctan.org/
- Documentation : http://latex-project.org/guides/
- Subreddit : http://www.reddit.com/r/LaTeX/
- Tools online :
    * Online collaborative LaTeX editor : https://www.writelatex.com/
    * Equation editor : http://www.codecogs.com/latex/eqneditor.php
    * Detexify (symbol classifier) : http://detexify.kirelabs.org/classify.html
    * Texify http://www.texify.com/
    * BibTeX Concerter http://www.bibtex.org/Convert/
    * Compile Latex Online : http://www.compileonline.com/try_latex_online.php
- RosettaCode : http://rosettacode.org/wiki/Category:LaTeX
''')

    @classmethod
    def man(cls, _):
        """Gets the manual"""
        return subprocess_call_wrapper(['man', cls.name])

    @classmethod
    def metrics(cls, args):
        """Gets metrics for code"""
        filename = cls.get_actual_filename_to_use(args)
        return subprocess_call_wrapper(['lex_count', filename])

    @classmethod
    def get_file_content(cls, _):
        """Returns the content to be put in the file."""
        return dedent('''
            % LaTeX example
            \\documentclass{article}
            \\begin{document}
            Hello, world!
            \\end{document}
            ''')

    @classmethod
    def call_pdflatex(cls, basename):
        """Calls pdflatex."""
        filedir = os.path.split(basename)[0]
        return subprocess_call_wrapper([
            'pdflatex',
            '-interaction=nonstopmode',  # trying to avoid prompts
            '-halt-on-error',            # as it makes unittest tedious
            '-output-directory',
            filedir,
            basename])

    @classmethod
    def call_latex(cls, basename):
        """Calls latex."""
        return subprocess_call_wrapper(['latex', basename])

    @classmethod
    def call_bibtex(cls, basename):
        """Calls bibtex."""
        return subprocess_call_wrapper(['bibtex', basename])

    @classmethod
    def compile(cls, args):
        """Compiles the file"""
        # Things are a bit more complicated for latex because multiple
        # compilations might be required. Also, the default compiler
        # should be latex but PDFs are usually more convenient.
        basename = os.path.splitext(cls.get_actual_filename_to_use(args))[0]
        print(basename)
        status = cls.call_pdflatex(basename) and \
            cls.call_pdflatex(basename)
        if status and cls.call_bibtex(basename):
            # If bibtex is successful, we need yet another compilation
            status = cls.call_pdflatex(basename)
        return status

    @classmethod
    def get_output_filename(cls, filename):
        """Gets the name of the output file"""
        return os.path.splitext(filename)[0] + '.pdf'


class Go(CompilableLanguage):
    """Go"""
    name = 'go'
    extensions = ['go']
    compiler = 'gccgo'
    compiler_options = ['-g']
    comments = ('//', '')
    information = dedent('''
- Wikipedia page : http://en.wikipedia.org/wiki/Go_%28programming_language%29
- Official site : http://golang.org/
- Documentation : http://golang.org/doc/
- Subreddit : http://www.reddit.com/r/golang/
- Tools online :
    * Playground : http://play.golang.org/
- Learn in Y minutes : http://learnxinyminutes.com/docs/go/
- RosettaCode : http://rosettacode.org/wiki/Category:Go
''')

    @classmethod
    def get_file_content(cls, _):
        """Returns the content to be put in the file."""
        return dedent('''
            package main
            import "fmt"
            func main() {
                    fmt.Printf("hello, world\\n")
            }''')


class Clojure(Language):
    """Clojure"""
    name = 'clojure'
    extensions = ['clj', 'edn']
    comments = (';', '')
    information = dedent('''
- Wikipedia page : http://en.wikipedia.org/wiki/Clojure
- Official site : http://clojure.org/
- Documentation :
- Subreddit : http://www.reddit.com/r/Clojure/
- Tools online :
    * Try Clojure http://tryclj.com/
    * Clojure compiler http://closure-compiler.appspot.com/home
    * Clojure REPL http://himera.herokuapp.com/index.html
    * Interactive problems https://www.4clojure.com/
- Learn in Y minutes :
    * http://learnxinyminutes.com/docs/clojure/
    * http://learnxinyminutes.com/docs/clojure-macros/
- RosettaCode : http://rosettacode.org/wiki/Category:Clojure
''')
    cmd_launch_jar = ['java', '-cp', 'clojure-1.6.0.jar', 'clojure.main']

    @classmethod
    def get_file_content(cls, _):
        """Returns the content to be put in the file."""
        return dedent('''
            (println "Hello world!")
            ''')

    @classmethod
    def run(cls, args):
        """Runs the code"""
        filename = cls.get_actual_filename_to_use(args)
        return subprocess_call_wrapper(cls.cmd_launch_jar + [filename])

    @classmethod
    def man(cls, _):
        """Gets the manual"""
        return subprocess_call_wrapper(cls.cmd_launch_jar + ['--help'])


class Erlang(Language):
    """Erlang"""
    name = 'erlang'
    extensions = ['erl', 'hrl']
    comments = ('%', '')
    information = dedent('''
- Wikipedia page : http://en.wikipedia.org/wiki/Erlang_%28programming_language%29
- Official site : http://www.erlang.org/
- Documentation :
    * http://www.erlang.org/doc.html
    * http://erldocs.com/
    * http://learnyousomeerlang.com/content
    * http://www.erlang.org/course/course.html
- Subreddit : http://www.reddit.com/r/erlang/
- Tools online :
    * Try Erlang http://www.tryerlang.org/
    * Compile Erlang Online http://www.compileonline.com/compile_erlang_online.php
- Learn in Y minutes : http://learnxinyminutes.com/docs/erlang/
- RosettaCode : http://rosettacode.org/wiki/Category:Erlang
''')

    @classmethod
    def metrics(cls, args):
        """Gets metrics for code"""
        filename = cls.get_actual_filename_to_use(args)
        return subprocess_call_wrapper(['erlang_count', filename])


class Elixir(Language):
    """Elixir"""
    name = 'elixir'
    extensions = ['ex', 'exs']
    comments = ('#', '')
    information = dedent('''
- Wikipedia page : http://en.wikipedia.org/wiki/Elixir_%28programming_language%29
- Official site : http://elixir-lang.org/
- Documentation : http://elixir-lang.org/docs.html
- Subreddit : http://www.reddit.com/r/elixir
- Tools online :
    * Try Elixir : http://try-elixir.herokuapp.com/
- Learn in Y minutes : http://learnxinyminutes.com/docs/elixir/
- RosettaCode : http://rosettacode.org/wiki/Category:Elixir
''')


# Maybe this should inherit from interpretable and compilable
# language but I am too scared at the moment. Let's write tests first
class Lisp(InterpretableLanguage):
    """Lisp"""
    name = 'lisp'
    extensions = ['lisp']
    comments = (';', '')
    information = dedent('''
- Wikipedia page :
    * http://en.wikipedia.org/wiki/Lisp_%28programming_language%29
    * http://en.wikipedia.org/wiki/Common_Lisp
- Official site :
- Documentation :
    * Common lisp wiki http://www.cliki.net/
- Subreddit :
    * http://www.reddit.com/r/lisp/
    * http://www.reddit.com/r/common_lisp
- Tools online :
- Learn in Y minutes :
    * http://learnxinyminutes.com/docs/common-lisp/
    * http://learnxinyminutes.com/docs/elisp/
- RosettaCode :
    * http://rosettacode.org/wiki/Category:Lisp
    * http://rosettacode.org/wiki/Common_Lisp
''')

    @classmethod
    def get_file_content(cls, _):
        """Returns the content to be put in the file."""
        return dedent('''
            (princ "Hello, world!")
            ''')

    @classmethod
    def get_interpreter_name(cls):
        """Gets the name of the interpreter"""
        return 'clisp'


class Scheme(InterpretableLanguage):
    """Scheme"""
    name = 'scheme'
    extensions = ['scm', 'ss']
    comments = (';', '')
    information = dedent('''
- Wikipedia page : http://en.wikipedia.org/wiki/Scheme_%28programming_language%29
- Official site :
- Documentation :
- Subreddit : http://www.reddit.com/r/scheme
- Tools online :
- RosettaCode : http://rosettacode.org/wiki/Category:Scheme
''')

    @classmethod
    def get_file_content(cls, _):
        """Returns the content to be put in the file."""
        return dedent('''
            (display "Hello, world!")
            ''')

    @classmethod
    def get_shebang_line(cls):
        """Return the shebang line"""
        return ''  # Something is different with Scheme

    @classmethod
    def run(cls, args):
        """Runs the code"""
        filename = cls.get_actual_filename_to_use(args)
        try:
            with open(filename) as infile:
                return subprocess_call_wrapper([cls.get_interpreter_name()], stdin=infile)
        except IOError:
            return False

    @classmethod
    def interactive(cls, args):
        """Executes the script and enters interactive mode"""
        filename = cls.get_actual_filename_to_use(args)
        return subprocess_call_wrapper([cls.get_interpreter_name(), '--load', filename])


class Racket(InterpretableLanguage):
    """Racket"""
    name = 'racket'
    extensions = ['rkt', 'rktl', 'rktd', 'plt', 'scrbl']
    comments = (';', '')
    information = dedent('''
- Wikipedia page : http://en.wikipedia.org/wiki/Racket_%28programming_language%29
- Official site : http://racket-lang.org/
- Documentation : http://docs.racket-lang.org/index.html
    * Guide http://docs.racket-lang.org/guide/
    * Reference http://docs.racket-lang.org/reference/
- Subreddit : http://www.reddit.com/r/Racket
- Tools online :
- Learn in Y minutes : http://learnxinyminutes.com/docs/racket/
- RosettaCode : http://rosettacode.org/wiki/Category:Racket
''')

    @classmethod
    def get_file_content(cls, _):
        """Returns the content to be put in the file."""
        return dedent('''
                #lang racket
                "Hello, World!"
            ''')


class Caml(Language):
    """Caml"""
    name = 'caml'
    extensions = ['ml', 'mli']
    comments = ('(*', '*)')
    information = dedent('''
- Wikipedia page : http://en.wikipedia.org/wiki/Caml
- Official site : http://caml.inria.fr/
- Documentation :
- Subreddit :
- Tools online :
- RosettaCode : http://rosettacode.org/wiki/Category:Caml
''')


class Scala(InterpretableLanguage):  # it can be compiled too but that's for later
    """Scala"""
    name = 'scala'
    extensions = ['scala']
    comments = ('//', '')
    information = dedent('''
- Wikipedia page : http://en.wikipedia.org/wiki/Scala_%28programming_language%29
- Official site : http://www.scala-lang.org/
- Documentation : http://docs.scala-lang.org/
- Subreddit : http://www.reddit.com/r/scala/
- Tools online :
    * Scala tutorials http://scalatutorials.com/tour/
    * Scala fiddle http://scalafiddle.net/console
    * Scala JS Fiddle http://www.scala-js-fiddle.com/
- Learn in Y minutes : http://learnxinyminutes.com/docs/scala/
- RosettaCode : http://rosettacode.org/wiki/Category:Scala
''')

    @classmethod
    def get_closing_shebang_line(cls):
        """Return the tag to close the shebang line"""
        return '!#\n'

    @classmethod
    def get_file_content(cls, _):
        """Returns the content to be put in the file."""
        # Apparently, there are many ways to write an hello-world in Scala
        return dedent('''
            object HelloWorld {
                def main(args: Array[String]) {
                    println("Hello, world!")
                }
            }''')

    @classmethod
    def interactive(cls, args):
        """Executes the script and enters interactive mode"""
        filename = cls.get_actual_filename_to_use(args)
        return subprocess_call_wrapper(
            [cls.get_interpreter_name(), '-i', filename])


class Rust(CompilableLanguage):
    """Rust"""
    name = 'rust'
    extensions = ['rs']
    compiler = 'rustc'
    compiler_options = ['-g']
    comments = ('//', '')
    information = dedent('''
- Wikipedia page : http://en.wikipedia.org/wiki/Rust_%28programming_language%29
- Official site : http://www.rust-lang.org/
- Documentation : http://static.rust-lang.org/doc/master/rust.html
- Wiki : https://github.com/mozilla/rust/wiki
- Subreddit : http://www.reddit.com/r/rust/
- Tools online :
- RosettaCode : http://rosettacode.org/wiki/Category:Rust
''')

    @classmethod
    def get_file_content(cls, _):
        """Returns the content to be put in the file."""
        return dedent('''
            fn main() {
                println!("Hello, world!");
            }''')

    @classmethod
    def debug(cls, args):
        """Launches the debugger"""
        output = cls.get_output_filename(cls.get_actual_filename_to_use(args))
        return subprocess_call_wrapper(['gdb', output])


class Elm(Language):
    """Elm"""
    name = 'elm'
    extensions = ['elm']
    comments = ('--', '')
    information = dedent('''
- Wikipedia page : http://en.wikipedia.org/wiki/Elm_%28programming_language%29
- Official site : http://elm-lang.org/
- Documentation :
    * Syntax http://elm-lang.org/learn/Syntax.elm
    * Librairies http://elm-lang.org/Libraries.elm
- Subreddit : http://www.reddit.com/r/elm
- Tools online :
    * Try Elm : http://elm-lang.org/try
- RosettaCode : http://rosettacode.org/wiki/Category:Elm
''')


class Dart(Language):
    """Dart"""
    name = 'dart'
    extensions = ['dart']
    comments = ('//', '')
    information = dedent('''
- Wikipedia page : http://en.wikipedia.org/wiki/Dart_%28programming_language%29
- Official site : https://www.dartlang.org/
- Documentation :
    * Programmer's guide https://www.dartlang.org/docs/
    * API http://api.dartlang.org/
    * Language specifications https://www.dartlang.org/docs/spec/
- Subreddit : http://www.reddit.com/r/dartlang/
- Tools online :
    * Try Dart : http://try.dartlang.org/
- Learn in Y minutes : http://learnxinyminutes.com/docs/dart/
- RosettaCode : http://rosettacode.org/wiki/Category:Dart
''')


class Prolog(InterpretableLanguage):
    """Prolog"""
    name = 'prolog'
    interpreter_options = ['-t', 'goal', '-s']
    extensions = ['pl', 'pro', 'p']
    comments = ('%', '')
    information = dedent('''
- Wikipedia page : http://en.wikipedia.org/wiki/Prolog
- Official sites (different implementations) :
    * http://www.swi-prolog.org/
    * http://www.gprolog.org/
- Documentation :
    * http://www.swi-prolog.org/pldoc/doc_for?object=manual
    * http://www.gprolog.org/manual/gprolog.html
- Subreddit : http://www.reddit.com/r/prolog/
- Tools online :
    * http://ioctl.org/logic/prolog-latest
- RosettaCode : http://rosettacode.org/wiki/Category:Prolog
''')

    @classmethod
    def get_interpreter_name(cls):
        """Gets the name of the interpreter"""
        return 'swipl'

    @classmethod
    def get_file_content(cls, _):
        """Returns the content to be put in the file."""
        return dedent('''
            goal :- write('Hello World'), nl,
                    halt.
            ''')


class PostScript(Language):
    """PostScript"""
    name = 'postscript'
    extensions = ['ps']
    comments = ('%', '')
    information = dedent('''
- Wikipedia page : http://en.wikipedia.org/wiki/PostScript
- Official site : http://www.adobe.com/products/postscript/
- Documentation :
    * http://www.adobe.com/products/postscript/pdfs/PLRM.pdf
- Subreddit : http://www.reddit.com/r/PostScript
- Tools online :
    * PS 2 PDF http://www.ps2pdf.com/convert.htm
- RosettaCode : http://rosettacode.org/wiki/Category:PostScript
''')


class Scilab(InterpretableLanguage):
    """Scilab"""
    name = 'scilab'
    extensions = [
        'sce',  # Executable statements
        'sci',  # Scilab or user defined functions
        ]
    comments = ('//', '')
    interpreter_options = ['-nwni', '-f']
    information = dedent('''
- Wikipedia page : http://en.wikipedia.org/wiki/Scilab
- Official site : http://www.scilab.org/
- Documentation : http://www.scilab.org/resources/documentation
- Tools online :
    * http://cloud.scilab.in/
    * http://hotcalcul.com/on-line-calculator/scilab
- RosettaCode : http://rosettacode.org/wiki/Category:Scilab
''')

    @classmethod
    def get_file_content(cls, _):
        """Returns the content to be put in the file."""
        return dedent('''
            mprintf('Hello, world!\\n');
            quit
            ''')

    @classmethod
    def get_shebang_line(cls):
        """Return the shebang line"""
        return ''  # to be fixed

    @classmethod
    def run(cls, args):
        """Runs the code"""
        filename = cls.get_actual_filename_to_use(args)
        # Check that file exists not to get stuck during unit tests
        if os.path.isfile(filename):
            return subprocess_call_wrapper(
                [cls.get_interpreter_name()] +
                cls.interpreter_options +
                [filename])
        else:
            print_error("File %s does not exist" % filename)
            return False


class Octave(InterpretableLanguage):
    """Octave"""
    name = 'octave'
    extensions = ['m']
    comments = ('#', '')
    information = dedent('''
- Wikipedia page : http://en.wikipedia.org/wiki/GNU_Octave
- Official site : https://gnu.org/software/octave/
- Documentation : http://www.gnu.org/software/octave/doc/interpreter/index.html
- Subreddit : http://www.reddit.com/r/octave
- Tools online :
    * Octave Online : http://octave-online.net/
    * Execute Matlab/Octave online : http://www.compileonline.com/execute_matlab_online.php
- RosettaCode : http://rosettacode.org/wiki/Category:Octave
''')

    @classmethod
    def get_file_content(cls, _):
        """Returns the content to be put in the file."""
        return dedent('''
            printf ("Hello, world!\\n");
            ''')


class Nimrod(Language):
    """Nimrod"""
    name = 'nimrod'
    extensions = ['nim']
    comments = ('#', '')
    information = dedent('''
- Wikipedia page : Not yet?
- Official site : http://nimrod-lang.org/
- Documentation : http://nimrod-lang.org/documentation.html
- Subreddit : http://www.reddit.com/r/nimrod
- RosettaCode : http://rosettacode.org/wiki/Category:Nimrod
''')

    @classmethod
    def get_file_content(cls, _):
        """Returns the content to be put in the file."""
        return dedent('''
            echo("Hello, world!")
            ''')


class ActionScript(Language):
    """ActionScript"""
    name = 'actionscript'
    extensions = ['as']
    comments = ('//', '')
    information = dedent('''
- Wikipedia page : http://en.wikipedia.org/wiki/ActionScript
- Official site :
    * http://www.adobe.com/devnet/actionscript.html
- Documentation :
- Subreddit : http://www.reddit.com/r/actionscript
- RosettaCode : http://rosettacode.org/wiki/Category:ActionScript
''')


class EcmaScript(Language):
    """EcmaScript"""
    name = 'ecmascript'
    extensions = ['es']
    comments = ('//', '')
    information = dedent('''
- Wikipedia page : http://en.wikipedia.org/wiki/ECMAScript
- Official site :
- Documentation :
''')


class ExampleLanguage(Language):
    """Example"""
    name = None
    extensions = None
    comments = (None, None)
    information = dedent('''
- Wikipedia page :
- Official site :
- Documentation :
- Subreddit :
- Tools online :
- Learn in Y minutes :
- RosettaCode :
''')


def get_subclasses(klass):
    """Gets the list of direct/indirect subclasses of a class"""
    subclasses = klass.__subclasses__()
    for derived in list(subclasses):
        subclasses.extend(get_subclasses(derived))
    return subclasses

LANGUAGES = [l for l in get_subclasses(Language) if l.name is not None]
LANGUAGE_NAMES = {l.name: l for l in LANGUAGES}


def get_extensions_map():
    """Gets dictionnary mapping extensions to the list of potential languages"""
    extensions = dict()
    for lang in LANGUAGES:
        for ext in lang.extensions:
            extensions.setdefault("." + ext, []).append(lang.name)
    return extensions


def infer_language_from_filecontent(filename, potential_languages):
    """Detects the programming language from the content of a file"""
    try:
        with open(filename) as filed:
            line = filed.readline().strip().lower()
            # Looking for shebangs
            if line.startswith('#!'):
                for lang in LANGUAGE_NAMES:
                    if line.endswith(lang):
                        return [lang]
    except IOError:
        pass
    return potential_languages


def detect_language_from_filename(filename):
    """Detects the language for a language based on the extension
    and if required and if it exists, on the content."""
    extension = os.path.splitext(filename)[1].lower()
    languages = get_extensions_map().get(extension)
    if languages is None:
        return None
    assert len(languages) >= 1
    if len(languages) > 1:
        languages = infer_language_from_filecontent(filename, languages)
        if languages is None:
            return None
    ret = languages[0]  # defaults to first language
    assert ret in LANGUAGE_NAMES
    return ret


class TestSubprocessCallWrapper(unittest.TestCase):
    """Unit tests for subprocess_call_wrapper()"""
    def test_true(self):
        """Tests that `true` returns True."""
        self.assertTrue(subprocess_call_wrapper(['true']))

    def test_false(self):
        """Tests that `false` returns False."""
        self.assertFalse(subprocess_call_wrapper(['false']))

    def test_empty(self):
        """Tests that `` returns False."""
        self.assertFalse(subprocess_call_wrapper([]))

    def test_empty_string(self):
        """Tests that `` returns False."""
        self.assertFalse(subprocess_call_wrapper(['']))

    def test_does_not_exist(self):
        """Tests that `command_does_not_exist` returns False."""
        self.assertFalse(subprocess_call_wrapper(['command_does_not_exist']))


class TestLanguageDetection(unittest.TestCase):
    """Unit tests related to language detection"""
    def test_get_extensions_map(self):
        """Unit tests for get_extensions_map()"""
        ext = get_extensions_map()
        self.assertIn('.php', ext)
        self.assertIn('php', ext['.php'])
        self.assertIn('.cpp', ext)
        self.assertIn('cpp', ext['.cpp'])

    def test_detect_language(self):
        """Unit tests for detect_language_from_filename()"""
        self.assertIsNone(detect_language_from_filename('a'))
        self.assertIsNone(detect_language_from_filename('a.xyz'))
        self.assertEqual(detect_language_from_filename('a.c'), 'c')
        self.assertEqual(detect_language_from_filename('a.cpp'), 'cpp')
        self.assertEqual(detect_language_from_filename('./a.c'), 'c')
        self.assertEqual(detect_language_from_filename('./a.cpp'), 'cpp')
        self.assertEqual(detect_language_from_filename('b/a.c'), 'c')
        self.assertEqual(detect_language_from_filename('b/a.cpp'), 'cpp')
        self.assertEqual(detect_language_from_filename('/b/a.c'), 'c')
        self.assertEqual(detect_language_from_filename('/b/a.cpp'), 'cpp')


# Idea - maybe interpreted language itself should inherit from unittest...
class TestableInterpretableLanguage(unittest.TestCase):
    """Unit tests for interpreted languages"""
    def interpreter_flow(self, klass, executable_file=True):
        """Tests stuff"""
        namespace = namedtuple('Namespace', 'filename extension_mode override_file')
        filename = os.path.join(tempfile.mkdtemp(
            prefix='letscode' + klass.name + '_'), "filename")
        args = namespace(filename, 'auto', 'n')
        real_file = klass.get_actual_filename_to_use(args)

        # Cannot run if file does not exist
        self.assertFalse(os.path.isfile(real_file))
        self.assertFalse(klass.perform_action('run', args))

        # Can create
        self.assertTrue(klass.perform_action('create', args))
        self.assertTrue(os.path.isfile(real_file))

        # Can run
        self.assertTrue(klass.perform_action('run', args))

        # Can run on its own
        if executable_file:
            self.assertTrue(subprocess_call_wrapper([real_file]))

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

    def test_awk(self):
        """Tests stuff"""
        self.interpreter_flow(Awk)

    def test_scala(self):
        """Tests stuff"""
        self.interpreter_flow(Scala)

    def test_perl(self):
        """Tests stuff"""
        self.interpreter_flow(Perl)

    def test_racket(self):
        """Tests stuff"""
        self.interpreter_flow(Racket)

    def test_javascript(self):
        """Tests stuff"""
        self.interpreter_flow(JavaScript)

    def test_lisp(self):
        """Tests stuff"""
        self.interpreter_flow(Lisp)

    def test_scheme(self):
        """Tests stuff"""
        self.interpreter_flow(Scheme, False)

    def test_clojure(self):
        """Tests stuff"""
        self.interpreter_flow(Clojure, False)

    def test_scilab(self):
        """Tests stuff"""
        self.interpreter_flow(Scilab, False)

    def test_octave(self):
        """Tests stuff"""
        self.interpreter_flow(Octave)

    def test_prolog(self):
        """Tests stuff"""
        self.interpreter_flow(Prolog)


class TestableCompilableLanguage(unittest.TestCase):
    """Unit tests for compilable languages"""
    def compilation_flow(self, klass):
        """Tests stuff"""
        namespace = namedtuple('Namespace', 'filename extension_mode override_file')
        filename = os.path.join(tempfile.mkdtemp(
            prefix='letscode' + klass.name + '_'), "filename")
        args = namespace(filename, 'auto', 'n')
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

        # Can create, compile and run
        self.assertTrue(klass.perform_action('create', args))
        self.assertTrue(os.path.isfile(real_file))
        self.assertFalse(os.path.isfile(output_file))
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

        # Removing file -> code is still running and compilation fails
        os.remove(real_file)
        self.assertTrue(klass.perform_action('run', args))
        self.assertFalse(klass.perform_action('compile', args))

    def test_cpp(self):
        """Tests stuff"""
        self.compilation_flow(Cpp)

    def test_objc(self):
        """Tests stuff"""
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

    def test_d(self):
        """Tests stuff"""
        self.compilation_flow(DLanguage)

    def test_go(self):
        """Tests stuff"""
        self.compilation_flow(Go)

    def test_latex(self):
        """Tests stuff"""
        self.compilation_flow(Latex)

    def test_dot(self):
        """Tests stuff"""
        self.compilation_flow(Dot)


def main():
    """Main"""
    parser = argparse.ArgumentParser(
        description='Makes your code easy to edit/compile/run/test/check')
    parser.add_argument(
        'filename',
        help=('filename (with or without the extension)'))
    parser.add_argument(
        '--language', '-l',
        help=('programming language to consider'),
        choices=list(LANGUAGE_NAMES.keys()) + ['autodetect'],
        default='autodetect')
    parser.add_argument(
        '--action', '-a',
        action='append',
        help=('action(s) to perform'),
        choices=[
            'create', 'edit', 'run', 'check', 'compile', 'coverage',
            'debug', 'info', 'upload', 'minify', 'pretty',
            'obfuscate', 'doctest', 'interactive', 'gendoc',
            'to_py3', 'uml', 'man', 'unittest', 'functionlist',
            'profile', 'metrics'],
        # this list could be generated
        default=[])
    parser.add_argument(
        '--failure', '-f',
        help=('behavior on failure'),
        choices=['stop', 'continue'],
        default='stop')
    parser.add_argument(
        '--extension_mode', '-e',
        help=('extension mode'),
        choices=['auto', 'never', 'always'],
        default='auto')
    parser.add_argument(
        '--override_file', '-o',
        help=('override already existing file'),
        choices=['n', 'y'],
        default='n')
    args = parser.parse_args()

    filename = args.filename
    language = args.language
    if language == 'autodetect':
        language = detect_language_from_filename(filename)
        print_info('Detected language is %s' % language)
        if language is None:
            return
    assert language in LANGUAGE_NAMES
    return LANGUAGE_NAMES[language].perform_actions(args)

if __name__ == '__main__':
    main()

# vim: filetype=python tabstop=8 expandtab shiftwidth=4 softtabstop=4

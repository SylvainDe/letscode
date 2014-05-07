#!/usr/bin/python3
# -*- coding: utf-8
"""Letscode is just a language-aware tool to quickly perform a bunch of usual
actions on a piece of code.

Letscode provides some kind of convenient abstraction over the different
languages you are working with and the related tools (compiler, interpreter,
etc). You might not want to remember how to write a simple hello-world, compile,
build the documentation, launch your tests, start the static analysis or just
run your code for all the languages you are working with. Also, it provides a
quick access to the relevant offline/online documents.

Letscode will guess what your code file is all about and do things for you.
For instance, in Vim, "letscode.py % -a compile" will lauch letscode on the
current file, detect its language and compile it.

The different languages derive from a common class Language. Adding a new
language is pretty straightforward, one just need to inherit from Language
and override the name and extensions attributes. Then, the different
actions can be defined via class methods. Code can be re-used by inheriting
from classes implementing usual behaviors such as ScriptingLanguage or
CompiledLanguages.
"""

# Ideas : Add option to tell whether we want to build stuff when
# we want to run and output file does not exist

# When code can be run or compiler, check if compiled version exists and if
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
import shutil
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


def subprocess_call_wrapper(lst):
    """Wrapper around the subprocess.call functions."""
    print_debug('About to run "%s"' % ' '.join(lst))
    try:
        ret = subprocess.call(lst)
    except FileNotFoundError:
        ret = 127  # an error code
    except IndexError:
        ret = 127  # an error code
    except PermissionError:
        ret = 127  # an error code
    print_debug('Command "%s" returned %d' % (lst[0] if lst else '', ret))
    return ret == 0


class Language(object):
    """A generic class for programming languages"""
    name = None
    extensions = None
    information = None

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
            print_info((greentick if ret else redcross) + undocolor +
                ' ' + action)
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
        line = corner + top*len(title) + corner
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
            extmode = 'never' if (os.path.splitext(filename)[1].lower() in ("." + e for e in cls.extensions)) else 'always'
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
            filed.write(cls.get_file_content(filename))

    @classmethod
    def get_file_content(cls, _):
        """Returns the content to be put in the file."""
        return ""


class CompiledLanguages(Language):
    """A generic class for compiled languages"""
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
            [cls.compiler, filename, '-o', output] + cls.compiler_options)

    @classmethod
    def run(cls, args):
        """Runs the code"""
        # We do not look in '.' by default, let's use the abs path
        output = os.path.abspath(
            cls.get_output_filename(
                cls.get_actual_filename_to_use(args)))
        return subprocess_call_wrapper([output])


class CLanguage(CompiledLanguages):
    """C"""
    name = 'c'
    code_extensions = ['c']
    header_extensions = ['h']
    extensions = code_extensions + header_extensions
    compiler = 'gcc'
    compiler_options = ['-Wall', '-Wextra', '-std=c99']
    information = dedent('''
- Wikipedia page : http://en.wikipedia.org/wiki/C_%28programming_language%29
- Official site :
- Documentation :
    * FAQ http://www.c-faq.com/
- Subreddit : http://www.reddit.com/r/C_Programming/
- Tools online :
    * Compiler (with ASM output) http://gcc.godbolt.org/
    * C gibberish <-> English http://cdecl.org/
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
        # to be done
        filename = cls.get_actual_filename_to_use(args)
        commands = {
            'cppncss': [],
            'cccc': [],
            'sloccount': [],
        }
        return True


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
- Official site :
- Documentation :
- Misc :
    * Guru of the week http://www.gotw.ca/gotw/
- Subreddit :
- Tools online :
    * Compiler (with ASM output) http://gcc.godbolt.org/
    * C gibberish <-> English http://cdecl.org/
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


class Java(CompiledLanguages):
    """Java"""
    name = 'java'
    extensions = ['java', 'class', 'jar']
    compiler = 'javac'

    information = dedent('''
- Wikipedia page : http://en.wikipedia.org/wiki/Java_%28programming_language%29
- Official site : http://www.java.com/
- Documentation : http://docs.oracle.com/javase/7/docs/api/
- Subreddit : http://www.reddit.com/r/java/
- Tools online :
    * Visualiser : http://cscircles.cemc.uwaterloo.ca/java_visualize/
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


class Haskell(CompiledLanguages):
    """Haskell"""
    name = 'haskell'
    extensions = ['hs', 'lhs']
    compiler = 'ghc'
    information = dedent('''
- Wikipedia page : http://en.wikipedia.org/wiki/Haskell_%28programming_language%29
- Official site : http://www.haskell.org/
- Documentation : http://www.haskell.org/ghc/docs/7.6-latest/html/libraries/index.html
- Subreddit : http://www.reddit.com/r/haskell/
- Tools online :
    * Try Haskell : http://tryhaskell.org/
- RosettaCode : http://rosettacode.org/wiki/Category:Haskell
''')

    @classmethod
    def get_file_content(cls, _):
        """Returns the content to be put in the file."""
        return dedent('''
            main = putStrLn "Hello, world!"
            ''')


class MarkupLanguage(Language):
    """A generic class for markup languages"""


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
''')

    @classmethod
    def pretty(cls, args):
        """Makes the code prettier"""
        filename = cls.get_actual_filename_to_use(args)
        return subprocess_call_wrapper(['xmllint', '--format', filename])


class ScriptingLanguage(Language):
    """A generic class for scripting languages"""
    vim_modeline = '# vim: tabstop=8 expandtab shiftwidth=4 softtabstop=4'
    comment_begin = '#'
    comment_end = ''

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
        return subprocess_call_wrapper([cls.get_interpreter_name(), filename])

    @classmethod
    def real_create(cls, filename):
        """Creates and ensures readiness of a file (shebang, boiler-plate code,
        execution rights, etc)."""
        with open(filename, 'w') as filed:
            filed.write(cls.get_file_content(filename))
        ScriptingLanguage.give_exec_rights(filename)

    @classmethod
    def get_file_content(cls, _):
        """Returns the content to be put in the file."""
        return cls.get_shebang_line() + "\n" + cls.vim_modeline + "\n"

    @classmethod
    def get_shebang_line(cls):
        """Return the shebang line"""
        interpreter = cls.get_interpreter_name()
        path = shutil.which(interpreter)
        if path is None:
            return '# interpreter "%s" not found' % interpreter
        return '#!' + path

    @staticmethod
    def give_exec_rights(filename):
        """Give the execution rights on a file"""
        os.chmod(filename, os.stat(filename).st_mode | stat.S_IEXEC)


class Shell(ScriptingLanguage):
    """A generic class for shell scripts"""
    name = 'sh'
    extensions = ['sh']
    information = dedent('''
- Wikipedia page :
- Official site :
- Documentation :
- Subreddit :
''')


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


class Ruby(ScriptingLanguage):
    """Ruby"""
    name = 'ruby'
    extensions = ['rb', 'rbw']
    information = dedent('''
- Wikipedia page : http://en.wikipedia.org/wiki/Ruby_%28programming_language%29
- Official site : https://www.ruby-lang.org/fr/
- Subreddit : http://www.reddit.com/r/ruby/
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


class Javascript(ScriptingLanguage):
    """Javascript"""
    name = 'javascript'
    extensions = ['js']
    information = dedent('''
- Wikipedia page : http://en.wikipedia.org/wiki/JavaScript
- "Official" sites :
    * https://developer.mozilla.org/en-US/docs/Web/JavaScript
    * http://www.ecmascript.org/
- Subreddit : http://www.reddit.com/r/javascript/
    ''')


class Perl(ScriptingLanguage):
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
- Subreddit : http://www.reddit.com/r/perl/
- RosettaCode : http://rosettacode.org/wiki/Category:Java
    ''')


class Php(ScriptingLanguage):
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
- RosettaCode : http://rosettacode.org/wiki/Category:PHP
    ''')


class Python(ScriptingLanguage):
    """Python"""
    name = 'python'
    extensions = ['py', 'pyc', 'pyo']
    vim_modeline = '# vim: filetype=python tabstop=8 expandtab shiftwidth=4 softtabstop=4'
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
- Wiki : https://wiki.python.org/moin/
- Videos : http://www.pyvideo.org/
- Subreddit : http://www.reddit.com/r/Python/
- Tools online :
    * PEP 8 online : http://pep8online.com/
- RosettaCode : http://rosettacode.org/wiki/Category:Python
- Misc ressources :
    * Hidden features (StackOverflow) : http://stackoverflow.com/questions/101268/hidden-features-of-python
    * Snippets/tips/tricks (/r/Python) : http://www.reddit.com/r/Python/comments/19dir2/whats_the_one_code_snippetpython_tricketc_did_you/
    ''')

    @classmethod
    def get_file_content(cls, _):
        """Returns the content to be put in the file."""
        return cls.get_shebang_line() + "\n" + cls.vim_modeline + dedent('''
            """Docstring for Python module"""


            def main():
                """Main function"""
                pass


            if __name__ == "__main__":
                main()
            ''')

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
    def pydoc(cls, args):
        """Generates the documentation"""
        filename = cls.get_actual_filename_to_use(args)
        return subprocess_call_wrapper(
            [cls.get_interpreter_name(), '-m', 'pydoc', filename])

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


class Julia(ScriptingLanguage):
    """Julia"""
    name = 'julia'
    extensions = ['jl']
    information = dedent('''
- Wikipedia page : http://en.wikipedia.org/wiki/Julia_%28programming_language%29
- Official site : http://julialang.org/
- Documentation : http://docs.julialang.org/en/release-0.1/
- Subreddit : http://www.reddit.com/r/Julia/
- RosettaCode : http://rosettacode.org/wiki/Category:Julia
''')


class Lua(ScriptingLanguage):
    """Lua"""
    name = 'lua'
    extensions = ['lua']
    information = dedent('''
- Wikipedia page : http://en.wikipedia.org/wiki/Lua_%28programming_language%29
- Official site : http://www.lua.org/
- Documentation : www.lua.org/docs.html
- Subreddit : http://www.reddit.com/r/lua/
- Tools online :
    * Demo http://www.lua.org/demo.html
- RosettaCode : http://rosettacode.org/wiki/Category:Lua
''')


class DatabaseLanguage(Language):
    """A generic class for database languages"""


class SQL(DatabaseLanguage):
    """SQL"""
    name = 'sql'
    extensions = ['sql']
    information = dedent('''
- Wikipedia page : http://en.wikipedia.org/wiki/SQL
- Official site :
- Documentation :
- Subreddit : http://www.reddit.com/r/SQL/
- Tools online :
- RosettaCode : http://rosettacode.org/wiki/Category:SQL
''')


class DOT(Language):
    """Graph description language"""
    name = "dot"
    extensions = ['gv', 'dot']
    information = dedent('''
- Wikipedia page : http://en.wikipedia.org/wiki/DOT_%28graph_description_language%29
- Official site : http://www.graphviz.org/
- Documentation : http://www.graphviz.org/Documentation.php
- Tools online :
    * Visualization :
        http://graphviz-dev.appspot.com/
        http://sandbox.kidstrythisathome.com/erdos/index.html
        http://rise4fun.com/agl
''')

    @classmethod
    def man(cls, _):
        """Gets the manual"""
        return subprocess_call_wrapper(['man', cls.name])

    @classmethod
    def run(cls, args):
        """Runs the code"""
        filename = cls.get_actual_filename_to_use(args)
        basename = os.path.splitext(filename)[0]
        commands = [
            'dot',    # directed graphs
            'neato',  # undirected graphs
            'twopi',  # radial layouts of graphs
            'circo',  # circular layouts of graphs
            'fdp',    # undirected graphs
            'sfdp',   # large undirected graphs
            ]
        results = [subprocess_call_wrapper(
            [c, '-Tpng', filename, '-o', basename + '_' + c + '.png'])
            for c in commands]
        return all(results)


class Latex(Language):
    """LaTeX (or TeX - it doesn't really matter here, does it?)"""
    name = 'latex'
    extensions = ['tex']
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
- RosettaCode : http://rosettacode.org/wiki/Category:LaTeX
''')

    @classmethod
    def man(cls, _):
        """Gets the manual"""
        return subprocess_call_wrapper(['man', cls.name])


class Go(CompiledLanguages):
    """Go"""
    name = 'go'
    extensions = ['go']
    compiler = 'gccgo'
    compiler_options = ['-g']
    information = dedent('''
- Wikipedia page : http://en.wikipedia.org/wiki/Go_%28programming_language%29
- Official site : http://golang.org/
- Documentation : http://golang.org/doc/
- Subreddit : http://www.reddit.com/r/golang/
- Tools online :
    * Playground : http://play.golang.org/
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
    name = 'closure'
    extensions = ['clj', 'edn']
    information = dedent('''
- Wikipedia page : http://en.wikipedia.org/wiki/Clojure
- Official site : http://clojure.org/
- Documentation :
- Subreddit : http://www.reddit.com/r/Clojure/
- Tools online :
    * Try Clojure http://tryclj.com/
    * Interactive problems https://www.4clojure.com/
- RosettaCode : http://rosettacode.org/wiki/Category:Clojure
''')


class Lisp(Language):
    """Lisp"""
    name = 'lisp'
    extensions = ['lisp']
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
- RosettaCode :
    * http://rosettacode.org/wiki/Category:Lisp
    * http://rosettacode.org/wiki/Common_Lisp
''')


class Scheme(Lisp):
    """Scheme"""
    name = 'scheme'
    extensions = ['scm', 'ss']


class Caml(Language):
    """Caml"""
    name = 'caml'
    extensions = ['ml', 'mli']
    information = dedent('''
- Wikipedia page : http://en.wikipedia.org/wiki/Caml
- Official site : http://caml.inria.fr/
- Documentation :
- Subreddit :
- Tools online :
- RosettaCode : http://rosettacode.org/wiki/Category:Caml
''')


class Scala(Language):
    """Scala"""
    name = 'scala'
    extensions = ['scala']
    information = dedent('''
- Wikipedia page : http://en.wikipedia.org/wiki/Scala_%28programming_language%29
- Official site : http://www.scala-lang.org/
- Documentation : http://docs.scala-lang.org/
- Subreddit : http://www.reddit.com/r/scala/
- Tools online :
    * Scala tutorials http://scalatutorials.com/tour/
- RosettaCode : http://rosettacode.org/wiki/Category:Scala
''')


class Rust(CompiledLanguages):
    """Rust"""
    name = 'rust'
    extensions = ['rs']
    compiler = 'rustc'
    compiler_options = ['-g']
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


class ExampleLanguage(Language):
    """Example"""
    name = None
    extensions = None
    information = dedent('''
- Wikipedia page :
- Official site :
- Documentation :
- Subreddit :
- Tools online :
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


class TestCompiledLanguage(unittest.TestCase):
    """Unit tests for compiled languages"""
    def compilation_flow(self, klass):
        """Tests stuff"""
        namespace = namedtuple('Namespace', 'filename extension_mode override_file')
        filename = tempfile.mkdtemp(prefix=klass.name + '_') + "filename"
        args = namespace(filename, 'auto', 'n')

        # Cannot compile or run if file does not exist
        self.assertFalse(klass.perform_action('compile', args))
        self.assertFalse(klass.perform_action('run', args))

        # Cannot create before compilation
        self.assertTrue(klass.perform_action('create', args))
        self.assertFalse(klass.perform_action('run', args))

        # Can create, compile and run
        self.assertTrue(klass.perform_action('create', args))
        self.assertTrue(klass.perform_action('compile', args))
        self.assertTrue(klass.perform_action('run', args))

        # Removing output file -> cannot run
        real_file = filename + "." + klass.extensions[0]
        output_file = klass.get_output_filename(filename)
        os.remove(output_file)
        self.assertFalse(klass.perform_action('run', args))

        # Can run after re-compilation
        self.assertTrue(klass.perform_action('compile', args))
        self.assertTrue(klass.perform_action('run', args))

        # Removing file -> code is still running and compilation fails
        os.remove(real_file)
        self.assertTrue(klass.perform_action('run', args))
        self.assertFalse(klass.perform_action('compile', args))

    def test_cpp(self):
        self.compilation_flow(Cpp)

    def test_c(self):
        self.compilation_flow(CLanguage)

    def test_java(self):
        self.compilation_flow(Java)

    def test_rust(self):
        self.compilation_flow(Rust)

    def test_haskell(self):
        self.compilation_flow(Haskell)

    def test_go(self):
        self.compilation_flow(Go)


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
            'obfuscate', 'doctest', 'interactive', 'pydoc',
            'to_py3', 'uml', 'man', 'unittest', 'functionlist',
            'profile'],
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

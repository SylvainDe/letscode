#!/usr/bin/python3
# -*- coding: utf-8
"""Abstract and concrete classes used to define the different languages."""


import os
import stat
import re
import myshutil as shutil
from helper import print_error, print_info, subprocess_call_wrapper
from codestyles import CODESTYLES
from modeline import get_modelines
from comments import comment_string
from textwrap import dedent


class Language(object):
    """A generic class for programming languages.

    Attributes:
        name        Name of the language (alphanumerical lowercase string)
        extensions  Extensions (list of string without leading dot). First
                        extension will be used by default for file creation
        information Additional information about the language (useful links)
        inline_comment  String how inline comments begin
        block_comment   Pair of string describing how block comments begin and
                        end
        styles      Code styles for the language (first one is the default)."""
    name = None
    extensions = None
    information = None
    inline_comment = None
    block_comment = None
    styles = []

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
        return results

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
            extmode = 'never' if (
                os.path.splitext(filename)[1].lower() in
                ("." + e.lower() for e in cls.extensions)
            ) else 'always'
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
            cls.real_create(filename, args)
            if args.filename != filename:
                print_info("File %s created" % filename)
            return True
        except IOError:
            print_error("Error while creating file" % filename)
            return False

    @classmethod
    def display(cls, args):
        """Show code that would be displayed when creating the file."""
        print(cls.get_content_to_write(args))
        return True

    @classmethod
    def get_code_style(cls, args):
        """Retrieve the relevant code style for the language taking into
        account the preference given in the arguments."""
        style_arg = args.style
        if style_arg is not None:
            assert style_arg in CODESTYLES
            return CODESTYLES[style_arg]
        return cls.styles[0] if cls.styles else {}

    @classmethod
    def get_content_to_write(cls, args):
        """Get content to be writen in the file - includes header and code."""
        mod_pos, editors = args.modeline, args.text_editors
        assert mod_pos in ['none', 'top', 'bottom', 'both']
        top, bottom = mod_pos in ['both', 'top'], mod_pos in ['both', 'bottom']
        modeline = get_modelines(editors, cls.get_code_style(args)) if top or bottom else ''
        filename = cls.get_actual_filename_to_use(args)
        return cls.get_header_info(modeline if top else '') + \
            cls.get_file_content(filename) + \
            cls.get_footer_info(modeline if bottom else '')

    @classmethod
    def real_create(cls, filename, args):
        """Creates and ensures readiness of a file (shebang, boiler-plate code,
        execution rights, etc)."""
        with open(filename, 'w') as filed:
            filed.write(cls.get_content_to_write(args))

    @classmethod
    def get_file_content(cls, _):
        """Returns the content to be put in the file."""
        return ""

    @classmethod
    def get_shebang_line(cls):
        """Return the shebang line.

        This method returns an empty string in the default case but can be
        overriden (in InterpretableLanguage for instance) to have an actual
        shebang on the very first line."""
        return ""

    @classmethod
    def get_header_info(cls, string):
        """Get information to put at the top of the file."""
        return cls.get_shebang_line() + \
            cls.comment_string(string) + \
            cls.comment_string("Generated by letscode")

    @classmethod
    def get_footer_info(cls, string):
        """Get information to put at the top of the file."""
        return cls.comment_string(string)

    @classmethod
    def comment_string(cls, string):
        """Comment string."""
        return comment_string(string, cls.inline_comment, cls.block_comment)


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

    @classmethod
    def is_ready(cls):
        """Check if language is 'ready' (as in compiler can be found)."""
        return shutil.which(cls.compiler) is not None


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
    inline_comment = '//'
    block_comment = ('/*', '*/')
    styles = [CODESTYLES['c-kernel'], CODESTYLES['c-apache']]
    information = dedent('''
- Wikipedia page : http://en.wikipedia.org/wiki/C_%28programming_language%29
- Official site :
- Documentation :
    * FAQ : http://www.c-faq.com/
- Subreddit : http://www.reddit.com/r/C_Programming/
- Tools online :
    * Compiler (with ASM output - no run) : http://gcc.godbolt.org/
    * Compiler (with ASM output - no run) : http://assembly.ynh.io/
    * C gibberish <-> English : http://cdecl.org/
    * Demangler : http://demangler.com/
    * Online compiler (run) : http://coliru.stacked-crooked.com/
- Learn in Y minutes : http://learnxinyminutes.com/docs/c/
- Code samples :
    * LiteratePrograms : http://en.literateprograms.org/Category:Programming_language:C
    * Progopedia : http://progopedia.com/language/c/
    * RosettaCode : http://rosettacode.org/wiki/Category:C
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
        if ext.lower() in ('.' + e for e in cls.header_extensions):
            return cls.get_header_content(
                '__%s__' % re.sub('[^A-Z]', '_', base.upper()))
        else:
            assert ext.lower() in ('.' + e for e in cls.code_extensions)
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
    styles = [CODESTYLES['objc-google']]
    information = dedent('''
- Wikipedia page : http://en.wikipedia.org/wiki/Objective-C
- Official site : https://developer.apple.com/library/mac/documentation/cocoa/conceptual/ProgrammingWithObjectiveC/Introduction/Introduction.html
- Documentation :
- Tools online :
    * Try Objective C: http://tryobjectivec.codeschool.com/
    * Compile online : http://www.compileonline.com/compile_objective-c_online.php
- Subreddit : http://www.reddit.com/r/ObjectiveC/
- Learn in Y minutes : http://learnxinyminutes.com/docs/objective-c/
- Code samples :
    * LiteratePrograms : http://en.literateprograms.org/Category:Programming_language:Objective-C
    * Progopedia : http://progopedia.com/language/objective-c/
    * RosettaCode : http://rosettacode.org/wiki/Category:Objective-C
''')


class Cpp(CLanguage):
    """Cpp"""
    name = 'cpp'
    code_extensions = ['cpp', 'cc', 'cxx', 'c++']
    header_extensions = ['hpp', 'hh', 'h', 'hxx', 'h++']
    extensions = code_extensions + header_extensions
    compiler = 'g++'
    compiler_options = ['-Wall', '-Wextra']
    styles = [CODESTYLES['cpp-google'], CODESTYLES['cpp-boost']]
    information = dedent('''
- Wikipedia page : http://en.wikipedia.org/wiki/C++
- Official site : http://isocpp.org/
- Documentation : http://en.cppreference.com/
- Misc :
    * Guru of the week : http://www.gotw.ca/gotw/
- Subreddit : http://www.reddit.com/r/cpp/
- Learn in Y minutes : http://learnxinyminutes.com/docs/c++/
- Tools online :
    * Compiler (with ASM output - no run) : http://gcc.godbolt.org/
    * Compiler (with ASM output - no run) : http://assembly.ynh.io/
    * C gibberish <-> English : http://cdecl.org/
    * Demangler : http://demangler.com/
    * Online compiler (run) : http://coliru.stacked-crooked.com/
- Code samples :
    * LiteratePrograms : http://en.literateprograms.org/Category:Programming_language:C_Plus_Plus
    * Progopedia : http://progopedia.com/language/c-plus-plus/
    * RosettaCode : http://rosettacode.org/wiki/Category:C%2B%2B
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
    inline_comment = '//'
    block_comment = ('/*', '*/')
    styles = [CODESTYLES['java-google'], CODESTYLES['java-oracle']]
    information = dedent('''
- Wikipedia page : http://en.wikipedia.org/wiki/Java_%28programming_language%29
- Official site : http://www.java.com/
- Documentation : http://docs.oracle.com/javase/7/docs/api/
- Subreddit : http://www.reddit.com/r/java/
- Tools online :
    * Paste and run : https://www.ktbyte.com/paste
    * Visualiser : http://cscircles.cemc.uwaterloo.ca/java_visualize/
    * Visualiser : http://visualize.learneroo.com/
    * Demangler : http://demangler.com/
    * Javabytes (disassembler) : http://javabytes.herokuapp.com/
    * REPL : http://www.javarepl.com/console.html
- Learn in Y minutes : http://learnxinyminutes.com/docs/java/
- Code samples :
    * LiteratePrograms : http://en.literateprograms.org/Category:Programming_language:Java
    * Progopedia : http://progopedia.com/language/java/
    * RosettaCode : http://rosettacode.org/wiki/Category:Java
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
    def check(cls, args):
        """Calls static checker"""
        filename = cls.get_actual_filename_to_use(args)
        return subprocess_call_wrapper(
            [cls.compiler, filename] + cls.compiler_options + ['-Xlint:all'])

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
    inline_comment = '//'
    block_comment = ('/*', '*/')
    information = dedent('''
- Wikipedia page : http://en.wikipedia.org/wiki/Vala_%28programming_language%29
- Official site : https://wiki.gnome.org/Projects/Vala
- Documentation : https://wiki.gnome.org/Projects/Vala/Documentation
- Subreddit : http://www.reddit.com/r/vala
- Code samples :
    * RosettaCode : http://rosettacode.org/wiki/Category:Vala
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
    inline_comment = '//'
    block_comment = ('(*', '*)')  # or ('{', '}')
    styles = [CODESTYLES['pascal-gnu']]
    information = dedent('''
- Wikipedia page : http://en.wikipedia.org/wiki/Pascal_%28programming_language%29
- Official site :
- Documentation :
- Subreddit :
    * http://www.reddit.com/r/pascal/
    * http://www.reddit.com/r/delphi/
- Code samples :
    * LiteratePrograms : http://en.literateprograms.org/Category:Programming_language:Pascal
    * Progopedia : http://progopedia.com/language/pascal/
    * RosettaCode : http://rosettacode.org/wiki/Category:Pascal
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
    # also for https://gcc.gnu.org/onlinedocs/gnat_ugn_unw/Style-Checking.html
    compiler_options = ['make']
    inline_comment = '--'
    styles = [CODESTYLES['ada-gnat']]
    information = dedent('''
- Wikipedia page : http://en.wikipedia.org/wiki/Ada_(programming_language)
- Official site : http://www.adaic.org/
- Documentation :
- Subreddit : http://www.reddit.com/r/ada/
- Code samples :
    * LiteratePrograms : http://en.literateprograms.org/Category:Programming_language:Ada
    * Progopedia : http://progopedia.com/language/ada/
    * RosettaCode : http://rosettacode.org/wiki/Category:Ada
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
    inline_comment = '!'
    information = dedent('''
- Wikipedia page : http://en.wikipedia.org/wiki/Fortran
- Official site :
- Documentation : http://www.fortran90.org/
- Subreddit : http://www.reddit.com/r/fortran/
- Code samples :
    * LiteratePrograms : http://en.literateprograms.org/Category:Programming_language:Fortran
    * Progopedia : http://progopedia.com/language/fortran/
    * RosettaCode : http://rosettacode.org/wiki/Category:Fortran
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
    inline_comment = '       *'
    compiler = 'cobc'
    compiler_options = ['-x']
    information = dedent('''
- Wikipedia page : http://en.wikipedia.org/wiki/COBOL
- Subreddit : http://www.reddit.com/r/cobol
- Tools online :
    * Compile online : http://www.compileonline.com/compile_cobol_online.php
- Code samples :
    * Progopedia : http://progopedia.com/language/cobol/
    * RosettaCode : http://rosettacode.org/wiki/Category:COBOL
    ''')

    @classmethod
    def get_file_content(cls, _):
        """Returns the content to be put in the file."""
        # No dedent here - leading spaces matter
        return '''
       IDENTIFICATION DIVISION.
       PROGRAM-ID. HELLO-WORLD.
       PROCEDURE DIVISION.
           DISPLAY 'Hello, world!'.
           STOP RUN.
        '''

    @classmethod
    def metrics(cls, args):
        """Gets metrics for code"""
        filename = cls.get_actual_filename_to_use(args)
        return subprocess_call_wrapper(['cobol_count', filename])


# hlint
class Haskell(CompilableLanguage):
    """Haskell"""
    name = 'haskell'
    extensions = ['hs', 'lhs']
    compiler = 'ghc'
    inline_comment = '--'
    block_comment = ('{-', '-}')
    styles = [CODESTYLES['haskell']]
    information = dedent('''
- Wikipedia page : http://en.wikipedia.org/wiki/Haskell_%28programming_language%29
- Official site : http://www.haskell.org/
- Documentation : http://www.haskell.org/ghc/docs/7.6-latest/html/libraries/index.html
- Subreddit : http://www.reddit.com/r/haskell/
- Tools online :
    * Try Haskell : http://tryhaskell.org/
- Learn in Y minutes : http://learnxinyminutes.com/docs/haskell/
- Code samples :
    * LiteratePrograms : http://en.literateprograms.org/Category:Programming_language:Haskell
    * Progopedia : http://progopedia.com/language/haskell/
    * RosettaCode : http://rosettacode.org/wiki/Category:Haskell
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
    inline_comment = '//'
    block_comment = ('/*', '*/')
    styles = [CODESTYLES['d']]
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
- Code samples :
    * LiteratePrograms : http://en.literateprograms.org/Category:Programming_language:D
    * Progopedia : http://progopedia.com/language/d/
    * RosettaCode : http://rosettacode.org/wiki/Category:D
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


class AppleScript(Language):
    """AppleScript"""
    name = 'applescript'
    extensions = ['scpt', 'AppleScript']
    inline_comment = '--'  # and more recently '#'
    block_comment = ('(*', '*)')
    information = dedent('''
- Wikipedia page : http://en.wikipedia.org/wiki/AppleScript
- Official site : http://www.macosxautomation.com/applescript/
- Documentation : https://developer.apple.com/library/mac/documentation/AppleScript/Conceptual/AppleScriptLangGuide/introduction/ASLR_intro.html
- Subreddit : http://www.reddit.com/r/applescript
- Code samples :
    * LiteratePrograms : http://en.literateprograms.org/Category:Programming_language:AppleScript
    * RosettaCode : http://rosettacode.org/wiki/Category:AppleScript
''')


class Qi(Language):
    """Qi"""
    name = 'qi'
    extensions = ['qi']
    block_comment = ('\\', '\\')
    information = dedent('''
- Wikipedia page : http://en.wikipedia.org/wiki/Qi_(programming_language)
- Official site : http://www.lambdassociates.org/
- Code samples :
    * RosettaCode : http://rosettacode.org/wiki/Category:Qi
''')


class Shen(Language):
    """Shen"""
    name = 'shen'
    extensions = ['shen']
    inline_comment = '\\\\'
    block_comment = ('\\*', '*\\')
    information = dedent('''
- Wikipedia page : http://en.wikipedia.org/wiki/Shen_(programming_language)
- Official site : http://www.shenlanguage.org/
- Documentation : http://www.shenlanguage.org/learn-shen/index.html
- Code samples :
    * RosettaCode : http://rosettacode.org/wiki/Category:Shen
''')


class MarkupLanguage(Language):
    """A generic class for markup languages"""
    block_comment = ('<!--', '-->')


class HTML(MarkupLanguage):
    """HTML"""
    name = 'html'
    extensions = ['html']
    styles = [CODESTYLES['html-google']]
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
- Tools online :
    * XML Playground : http://xmlplayground.com/
    * XML Beautify/Viewer : http://codebeautify.org/xmlviewer/
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
    block_comment = ('/*', '*/')
    styles = [CODESTYLES['css']]
    information = dedent('''
- Wikipedia page : http://en.wikipedia.org/wiki/Cascading_Style_Sheets
- Official site : http://www.w3.org/Style/CSS/Overview.en.html
- Documentation :
- Tools online :
    * CSS Lint : http://csslint.net/
    * CSS Desk : http://www.cssdesk.com/
    * CSS Comb (in progress) : http://csscomb.com/
- Learn in Y minutes : http://learnxinyminutes.com/docs/css/
''')


class JSON(Language):
    """JSON"""
    name = 'json'
    extensions = ['json']
    # No comment in JSON
    information = dedent('''
- Wikipedia page : http://en.wikipedia.org/wiki/JSON
- Official site : http://www.json.org/
- Documentation :
- Tools online :
    * JSON Lint : http://jsonlint.com/
    * JSON Fiddle : http://jsonfiddle.net/
    * JSON Schema Lint : http://jsonschemalint.com
    * JSON Selector : http://jsonselector.com/
    * Geo JSON Lint : http://geojsonlint.com/
    * JSON Processor : https://jqplay.org/
- Learn in Y minutes : http://learnxinyminutes.com/docs/json/
''')


class YAML(Language):
    """YAML"""
    name = 'yaml'
    extensions = ['yaml', 'yml']
    inline_comment = '#'
    information = dedent('''
- Wikipedia page : http://en.wikipedia.org/wiki/YAML
- Official site : http://yaml.org/
- Documentation : http://www.yaml.org/spec/1.2/spec.html
- Tools online :
    * YAML Lint : http://yamllint.com/
    * Online parser : http://yaml-online-parser.appspot.com/
    * YAML to JSON : http://yamltojson.com/
    * JSON to YAML : http://jsontoyaml.com/
- Learn in Y minutes : http://learnxinyminutes.com/docs/yaml/
''')


class HAML(Language):
    """HAML  (HTML Abstraction Markup Language)"""
    name = 'haml'
    extensions = ['haml']
    inline_comment = '-#'
    information = dedent('''
- Wikipedia page : http://en.wikipedia.org/wiki/Haml
- Official site : http://haml.info/
- Documentation : http://haml.info/docs.html
- Tools online :
    * HAML to ERB : http://haml2erb.herokuapp.com/
    * HAML to HTML : http://www.haml-converter.com/
    * HTML to HAML : http://htmltohaml.com/
''')


class reST(CompiledDescriptionLanguages):
    """reStructuredText"""
    name = 'rest'
    extensions = ['rst']
    inline_comment = '..'
    compiler = 'rst2html'
    # other compilers : rst2html rst2latex rst2man rst2odt rst2odt_prepstyles
    # rst2pseudoxml rst2s5 rst2xetex rst2xml
    information = dedent('''
- Wikipedia page : http://en.wikipedia.org/wiki/ReStructuredText
- Official site : http://docutils.sourceforge.net/rst.html
- Documentation : http://docutils.sourceforge.net/docs/ref/rst/restructuredtext.html
- Cheatsheet : http://docutils.sourceforge.net/docs/user/rst/cheatsheet.txt
''')

    @classmethod
    def get_file_content(cls, _):
        """Returns the content to be put in the file."""
        return dedent('''
            Section Header
            ==============

            Subsection Header
            -----------------

            Hello, world!
            ''')

    @classmethod
    def get_output_filename(cls, filename):
        """Gets the name of the output file"""
        return os.path.splitext(filename)[0] + '.html'

    @classmethod
    def compile(cls, args):
        """Compiles the file"""
        filename = cls.get_actual_filename_to_use(args)
        output = cls.get_output_filename(filename)
        return subprocess_call_wrapper(
            [cls.compiler] + cls.compiler_options + [filename, output])


class CoffeeScript(Language):
    """CoffeeScript"""
    name = 'coffeescript'
    extensions = ['coffee']
    inline_comment = '#'
    shell_stop = 'process.exit()'  # not relevant but in order not to forget
    styles = [CODESTYLES['coffeescript']]
    information = dedent('''
- Wikipedia page : http://en.wikipedia.org/wiki/CoffeeScript
- Official site : http://coffeescript.org/
- Documentation :
- Tools online :
    * JS to Coffee : http://js2coffee.org/
    * Coffee Lint : http://www.coffeelint.org/
    * Try Coffee Script : http://coffeescript.org/
- Learn in Y minutes : http://learnxinyminutes.com/docs/coffeescript/
- Subreddit : http://www.reddit.com/r/coffeescript/
''')

    @classmethod
    def get_file_content(cls, _):
        """Returns the content to be put in the file."""
        return JavaScript.get_file_content(_)


class Move(Language):
    """Move"""
    name = 'move'
    extensions = ['mv']
    inline_comment = '#'
    information = dedent('''
- Wikipedia page : Not yet
- Official site : http://movelang.org/
- Documentation :
    * Language : http://movelang.org/language/
    * Library : http://movelang.org/library/
- Tools online :
    * Try Move : http://movelang.org/try/
''')


class TypeScript(Language):
    """TypeScript"""
    name = 'typescript'
    extensions = ['ts']
    inline_comment = '//'
    information = dedent('''
- Wikipedia page : http://en.wikipedia.org/wiki/TypeScript
- Official site : http://www.typescriptlang.org/
- Documentation : http://www.typescriptlang.org/Handbook
- Tools online :
    * Playground : http://www.typescriptlang.org/Playground
- Subreddit : http://www.reddit.com/r/typescript/
- Learn in Y minutes : http://learnxinyminutes.com/docs/typescript/
''')


class JSX(Language):
    """JSX"""
    name = 'jsx'
    extensions = ['jsx']
    inline_comment = '//'
    information = dedent('''
- Wikipedia page :
- Official site : http://jsx.github.io
- Documentation : http://jsx.github.io/doc.html
- Tools online :
    * Try on Web : http://jsx.github.io/try-on-web/
- Subreddit :
''')

    @classmethod
    def get_file_content(cls, _):
        """Returns the content to be put in the file."""
        return dedent('''
            class _Main {
              static function main(args : string[]) :void {
                log "Hello, world!";
              }
            }
            ''')


class Markdown(Language):
    """Markdown"""
    name = 'markdown'
    extensions = ['md']
    # From http://stackoverflow.com/questions/4823468/store-comments-in-markdown-syntax
    block_comment = ('[//]: # (', ')')
    information = dedent('''
- Wikipedia page : http://en.wikipedia.org/wiki/Markdown
- Official site :
    * http://standardmarkdown.com/
    * (Use to be http://daringfireball.net/projects/markdown/ )
- Misc :
    * Github flavored markdown : https://help.github.com/articles/github-flavored-markdown
- Documentation :
    * Basic : https://help.github.com/articles/markdown-basics
- Tools online :
    * Markdown editors/viewers:
        http://try.standardmarkdown.com/
        http://daringfireball.net/projects/markdown/dingus
        http://www.markdownviewer.com/
        http://markable.in/editor/
        http://dillinger.io/
        https://stackedit.io/
    * HTML to text : http://www.aaronsw.com/2002/html2text/
''')


class InterpretableLanguage(Language):
    """A generic class for interpretable languages.

    Attributes:
        interpreter (via get_interpreter_name) Name of the interpreter
        interpreter_options Options for the interpreter
        nb_line_shebang     Number of lines of shebang
        shell (via get_shell_name) Name of the shell
        shell_options       Options to lauch the shell
        shell_stop          String to stop the shell."""
    interpreter_options = []
    inline_comment = '#'
    nb_line_shebang = 1  # 0 is no shebang, 1 is normal, 2 is multiline
    shell_options = []
    shell_stop = None

    @classmethod
    def get_interpreter_name(cls):
        """Gets the name of the interpreter"""
        return cls.name

    @classmethod
    def get_shell_name(cls):
        """Gets the name of the interactive interpreter"""
        return cls.get_interpreter_name()

    @classmethod
    def shell(cls, _):
        """Start the shell"""
        if cls.shell_stop is None:
            return cls.function_not_implemented('shell')
        print_info("Enter %s to exit." % cls.shell_stop)
        return subprocess_call_wrapper([cls.get_shell_name()] + cls.shell_options)

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
    def real_create(cls, filename, args):
        """Creates and ensures readiness of a file (shebang, boiler-plate code,
        execution rights, etc)."""
        with open(filename, 'w') as filed:
            filed.write(cls.get_content_to_write(args))
        InterpretableLanguage.give_exec_rights(filename)

    @classmethod
    def is_ready(cls):
        """Check if language is 'ready' (as in interpreter can be found)."""
        return shutil.which(cls.get_interpreter_name()) is not None

    @classmethod
    def get_shebang_line(cls):
        """Return the shebang line.

        Overriden in InterpretableLanguage to return an actual path to the
        interpreter with the relevant options."""
        if cls.nb_line_shebang:
            interpreter = cls.get_interpreter_name()
            path = shutil.which(interpreter)
            if path is None:
                return cls.comment_string('interpreter "%s" not found' % interpreter)
            return '#! ' + ' '.join([path] + cls.interpreter_options) + '\n' + \
                ('!#\n' if cls.nb_line_shebang > 1 else '')
        return ''

    @staticmethod
    def give_exec_rights(filename):
        """Give the execution rights on a file"""
        os.chmod(filename, os.stat(filename).st_mode | stat.S_IEXEC)


class Shell(InterpretableLanguage):
    """A generic class for shell scripts"""
    name = 'sh'
    extensions = ['sh']
    shell_stop = 'exit'
    styles = [CODESTYLES['shell-google']]
    information = dedent('''
- Wikipedia page :
- Official site :
- Documentation :
- Tool online:
    * Explain shell : http://explainshell.com/
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
    information = dedent('''
- Wikipedia page : http://en.wikipedia.org/wiki/Bash_%28Unix_shell%29
- Official site : https://www.gnu.org/software/bash/
- Documentation :
    * Bash reference manual : http://www.gnu.org/software/bash/manual/bashref.html
    * Bash scripting guide www.tldp.org/LDP/abs/html/
    * Bash guide : http://mywiki.wooledge.org/BashGuide
- Subreddit : http://www.reddit.com/r/bash/
- Learn in Y minutes : http://learnxinyminutes.com/docs/bash/
''')


class Zsh(Shell):
    """Zsh"""
    name = 'zsh'
    information = dedent('''
- Wikipedia page : http://en.wikipedia.org/wiki/Z_shell
- Official site : http://zsh.sourceforge.net/
- Documentation : http://zsh.sourceforge.net/Doc/Release/zsh_toc.html
- Wiki : http://zshwiki.org/home/
- Subreddit : http://www.reddit.com/r/zsh
''')


class Csh(Shell):
    """Csh"""
    name = 'csh'
    information = dedent('''
- Wikipedia page : http://en.wikipedia.org/wiki/C_shell
''')


class Tcsh(Shell):
    """Tcsh"""
    name = 'tcsh'
    information = dedent('''
- Wikipedia page : http://en.wikipedia.org/wiki/Tcsh
- Official site : http://www.tcsh.org/Welcome
''')


class Ksh(Shell):
    """Ksh"""
    # Other implementations : mksh and pdksh
    name = 'ksh'
    information = dedent('''
- Wikipedia page : http://en.wikipedia.org/wiki/Korn_shell
- Official site : www.kornshell.org
- Documentation : http://www.kornshell.org/doc/
- Tools online :
    * Ksh online : http://www.compileonline.com/execute_ksh_online.php
''')


class Ash(Shell):
    """Ash"""
    name = 'ash'
    information = dedent('''
- Wikipedia page : http://en.wikipedia.org/wiki/Almquist_shell
- Code samples :
    * RosettaCode : http://rosettacode.org/wiki/Almquist_Shell
''')


class Dash(Shell):
    """Dash"""
    name = 'dash'
    information = dedent('''
- Wikipedia page : http://en.wikipedia.org/wiki/Debian_Almquist_shell
- Code samples :
    * RosettaCode : http://rosettacode.org/wiki/Debian_Almquist_Shell
''')


class Yash(Shell):
    """Yash"""
    name = 'dash'
    information = dedent('''
- Official site : http://www.samiam.org/software/yash.html
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
- Code samples :
    * LiteratePrograms : http://en.literateprograms.org/Category:Programming_language:Tcl
    * Progopedia : http://progopedia.com/language/tcl/
    * RosettaCode : http://rosettacode.org/wiki/Category:Tcl
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


class FishShell(Shell):
    """FishShell"""
    name = 'fishshell'
    information = dedent('''
- Wikipedia page : http://en.wikipedia.org/wiki/Friendly_interactive_shell
- Official site : http://fishshell.com/
- Documentation : http://fishshell.com/docs/current/index.html
- Subreddit : http://www.reddit.com/r/fishshell/
''')

    @classmethod
    def get_interpreter_name(cls):
        """Gets the name of the interpreter"""
        return 'fish'


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
- Code samples :
    * LiteratePrograms : http://en.literateprograms.org/Category:Programming_language:AWK
    * Progopedia : http://progopedia.com/language/awk/
    * RosettaCode : http://rosettacode.org/wiki/Category:AWK
''')

    @classmethod
    def get_file_content(cls, _):
        """Returns the content to be put in the file."""
        return "BEGIN { print \"Hello, world!\" }"


class Ruby(InterpretableLanguage):
    """Ruby"""
    name = 'ruby'
    extensions = ['rb', 'rbw']
    shell_stop = 'exit'  # or quit, irb_exit
    styles = [CODESTYLES['ruby']]
    information = dedent('''
- Wikipedia page : http://en.wikipedia.org/wiki/Ruby_%28programming_language%29
- Official site : https://www.ruby-lang.org/fr/
- Online tools :
    * Visualise Ruby : http://www.onlinerubytutor.com/exercise/D000
    * Execute Ruby online : http://www.compileonline.com/execute_ruby_online.php
    * Try Ruby : http://tryruby.org/
    * RubyBytes (disassembler) : http://rubybytes.herokuapp.com/
- Subreddit : http://www.reddit.com/r/ruby/
- Learn in Y minutes : http://learnxinyminutes.com/docs/ruby/
- Code samples :
    * LiteratePrograms : http://en.literateprograms.org/Category:Programming_language:Ruby
    * Progopedia : http://progopedia.com/language/ruby/
    * RosettaCode : http://rosettacode.org/wiki/Category:Ruby
    ''')

    @classmethod
    def get_shell_name(cls):
        """Gets the name of the interactive interpreter"""
        return 'irb'

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
        return subprocess_call_wrapper([cls.get_shell_name, '-r', filename])

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
    inline_comment = '//'
    block_comment = ('/*', '*/')
    shell_stop = 'quit()'  # in rhino
    styles = [CODESTYLES['javascript']]
    information = dedent('''
- Wikipedia page : http://en.wikipedia.org/wiki/JavaScript
- "Official" sites :
    * https://developer.mozilla.org/en-US/docs/Web/JavaScript
    * http://www.ecmascript.org/
- Subreddit : http://www.reddit.com/r/javascript/
- Tools online :
    * JS Bin : http://jsbin.com/
    * JS Hint : http://www.jshint.com/
    * JS Lint : http://www.jslint.com/
    * JS Lint : http://www.javascriptlint.com/online_lint.php
    * JS Perf : http://jsperf.com/
    * JS Fiddle : http://jsfiddle.net/
    * JS Compress : http://jscompress.com/
    * JS Compressor : http://www.jscompressor.com/
    * JS Nice : http://www.jsnice.org/
    * JS Minifier : http://javascript-minifier.com/
    * JS Mini : http://www.jsmini.com/
    * JS Obfuscator : http://packer.50x.eu/
    * JS Obfuscator : http://javascriptobfuscator.com/
    * JS Obfuscate : http://www.jsobfuscate.com/
    * UglifyJS : http://lisperator.net/uglifyjs/#demo
    * Visualise Javascript : http://jstutor.herokuapp.com/
    * Javascript interpreter (with pause and undo) : http://wthimbleby.github.io/tailspin/
    * Google playground (Google APIs) : http://code.google.com/apis/ajax/playground/
    * Fun : Sound of JS : http://soundofjs.com
- Learn in Y minutes : http://learnxinyminutes.com/docs/javascript/
- Code samples :
    * LiteratePrograms : http://en.literateprograms.org/Category:Programming_language:JavaScript
    * Progopedia : http://progopedia.com/dialect/javascript/
    * RosettaCode : http://rosettacode.org/wiki/Category:JavaScript
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
    shell_options = ['-d', '-e', '1']
    shell_stop = 'q'
    styles = [CODESTYLES['perl']]
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
- Code samples :
    * LiteratePrograms : http://en.literateprograms.org/Category:Programming_language:Perl
    * Progopedia : http://progopedia.com/language/perl/
    * RosettaCode : http://rosettacode.org/wiki/Category:Perl
    ''')

    @classmethod
    def check(cls, args):
        """Calls static checker"""
        filename = cls.get_actual_filename_to_use(args)
        return subprocess_call_wrapper(
            [cls.get_interpreter_name(), '-c'] +
            cls.interpreter_options +
            [filename])

    @classmethod
    def get_file_content(cls, _):
        """Returns the content to be put in the file."""
        return dedent('''
            use strict;
            use warnings;
            print "Hello, world!\\n";
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
    styles = [
        CODESTYLES['php-zend'],
        CODESTYLES['php-symfony'],
        CODESTYLES['php-pear'],
        CODESTYLES['php-drupal'],
        CODESTYLES['php-fig']]
    shell_options = ['-a']
    shell_stop = 'exit'  # or quit
    information = dedent('''
- Wikipedia page : http://en.wikipedia.org/wiki/PHP
- Official site : http://www.php.net/
- Documentation : http://www.php.net/manual/en/
- Subreddit : http://www.reddit.com/r/php
- Tools online :
    * Sandbox with multiple versions : http://sandbox.onlinephpfunctions.com/
    * Performances on 100+ PHP versions : http://3v4l.org/
    * PHP Fiddle : http://phpfiddle.org/
    * PHP Sandbox : http://www.exorithm.com/algorithm/sandbox
    * PHP Lint : www.icosaedro.it/phplint/phplint-on-line.html
    * PHP Repl : http://phpepl.cloudcontrolled.com/
- Learn in Y minutes : http://learnxinyminutes.com/docs/php/
- Code samples :
    * LiteratePrograms : http://en.literateprograms.org/Category:Programming_language:PHP
    * Progopedia : http://progopedia.com/language/php/
    * RosettaCode : http://rosettacode.org/wiki/Category:PHP
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
    styles = [CODESTYLES['python']]
    shell_stop = 'exit()'
    information = dedent('''
- Wikipedia page : http://en.wikipedia.org/wiki/Python_%28programming_language%29
- Official site : https://www.python.org/
- List of PEPs : http://legacy.python.org/dev/peps/
    * PEP 8 : http://legacy.python.org/dev/peps/pep-0008/
    * PEP 20: The Zen of Python : http://legacy.python.org/dev/peps/pep-0020/
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
    * Python console : http://www.brython.info/console.html
    * Python interpreter : http://mathcs.holycross.edu/~kwalsh/python/
    * Learn Python with interactive console : http://www.learnpython.org/
    * Python Anywhere : https://www.pythonanywhere.com/try-ipython/
    * Client side Python interpreter : http://www.skulpt.org/
    * Python checker : http://pych.atomidata.com/
    * Python Obfuscator : http://pyobf.herokuapp.com/
- Learn in Y minutes :
    * http://learnxinyminutes.com/docs/python/
    * http://learnxinyminutes.com/docs/python3/
- Code samples :
    * LiteratePrograms : http://en.literateprograms.org/Category:Programming_language:Python
    * Progopedia : http://progopedia.com/language/python/
    * RosettaCode : http://rosettacode.org/wiki/Category:Python
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
            'pep8': [],
            'pylint': [],
            'pyflakes': [],
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
    shell_stop = 'exit()'
    styles = [CODESTYLES['julia']]
    information = dedent('''
- Wikipedia page : http://en.wikipedia.org/wiki/Julia_%28programming_language%29
- Official site : http://julialang.org/
- Documentation : http://docs.julialang.org/en/latest
- Subreddit : http://www.reddit.com/r/Julia/
- Learn in Y minutes : http://learnxinyminutes.com/docs/julia/
- Code samples :
    * RosettaCode : http://rosettacode.org/wiki/Category:Julia
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
    inline_comment = '"'
    information = dedent('''
- Wikipedia page : http://en.wikipedia.org/wiki/Vim_script
- Official site : http://www.vim.org/
- Documentation :
    * http://vimdoc.sourceforge.net/htmldoc/usr_41.html
    * http://learnvimscriptthehardway.stevelosh.com/
    * Examples : http://www.vim.org/scripts/
- Subreddit : http://www.reddit.com/r/vim/
- Code samples :
    * RosettaCode : http://rosettacode.org/wiki/Category:Vim_Script
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
    inline_comment = '--'
    compiler = 'luac'
    shell_stop = 'os.exit()'
    styles = [CODESTYLES['lua']]
    information = dedent('''
- Wikipedia page : http://en.wikipedia.org/wiki/Lua_%28programming_language%29
- Official site : http://www.lua.org/
- Documentation : www.lua.org/docs.html
- Subreddit : http://www.reddit.com/r/lua/
- Tools online :
    * Demo : http://www.lua.org/demo.html
- Learn in Y minutes : http://learnxinyminutes.com/docs/lua/
- Code samples :
    * LiteratePrograms : http://en.literateprograms.org/Category:Programming_language:Lua
    * Progopedia : http://progopedia.com/language/lua/
    * RosettaCode : http://rosettacode.org/wiki/Category:Lua
''')

    @classmethod
    def get_file_content(cls, _):
        """Returns the content to be put in the file."""
        return dedent('''
            print("Hello, world!")
        ''')

    @classmethod
    def check(cls, args):
        """Calls static checker"""
        filename = cls.get_actual_filename_to_use(args)
        return subprocess_call_wrapper(
            [cls.compiler, '-p', filename])


class DatabaseLanguage(Language):
    """A generic class for database languages"""


class SQL(DatabaseLanguage):
    """SQL"""
    name = 'sql'
    extensions = ['sql']
    inline_comment = '--'
    information = dedent('''
- Wikipedia page : http://en.wikipedia.org/wiki/SQL
- Official site :
- Documentation :
- Subreddit : http://www.reddit.com/r/SQL/
- Tools online :
    * SQL Fiddle : http://sqlfiddle.com/
    * SQL query visualisation : http://queryviz.com/online/
    * SQL Hands on : http://www.headfirstlabs.com/sql_hands_on/
    * SQL sandbox : http://coderzone.org/sqlsandbox/
- Code samples :
    * LiteratePrograms : http://en.literateprograms.org/Category:Programming_language:SQL
    * Progopedia : http://progopedia.com/language/sql/
    * RosettaCode : http://rosettacode.org/wiki/Category:SQL
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
    inline_comment = '//'
    block_comment = ('/*', '*/')
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
    compiler = 'pdflatex'
    inline_comment = '%'
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
    * Texify : http://www.texify.com/
    * BibTeX Concerter : http://www.bibtex.org/Convert/
    * Compile Latex Online : http://www.compileonline.com/try_latex_online.php
- Code samples :
    * Progopedia : http://progopedia.com/language/tex/
    * RosettaCode : http://rosettacode.org/wiki/Category:LaTeX
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
    inline_comment = '//'
    block_comment = ('/*', '*/')
    styles = [CODESTYLES['go']]
    information = dedent('''
- Wikipedia page : http://en.wikipedia.org/wiki/Go_%28programming_language%29
- Official site : http://golang.org/
- Documentation : http://golang.org/doc/
- Subreddit : http://www.reddit.com/r/golang/
- Tools online :
    * Playground : http://play.golang.org/
- Learn in Y minutes : http://learnxinyminutes.com/docs/go/
- Code samples :
    * LiteratePrograms : http://en.literateprograms.org/Category:Programming_language:Go
    * Progopedia : http://progopedia.com/language/go/
    * RosettaCode : http://rosettacode.org/wiki/Category:Go
''')

    @classmethod
    def get_file_content(cls, _):
        """Returns the content to be put in the file."""
        return dedent('''
            package main
            import "fmt"
            func main() {
                    fmt.Printf("hello, world!\\n")
            }''')


class Clojure(InterpretableLanguage):
    """Clojure"""
    name = 'clojure'
    extensions = ['clj', 'edn']
    inline_comment = ';'
    nb_line_shebang = 0
    information = dedent('''
- Wikipedia page : http://en.wikipedia.org/wiki/Clojure
- Official site : http://clojure.org/
- Documentation :
- Subreddit : http://www.reddit.com/r/Clojure/
- Tools online :
    * Try Clojure : http://tryclj.com/
    * Clojure compiler : http://closure-compiler.appspot.com/home
    * Clojure REPL : http://himera.herokuapp.com/index.html
    * Interactive problems : https://www.4clojure.com/
- Learn in Y minutes :
    * http://learnxinyminutes.com/docs/clojure/
    * http://learnxinyminutes.com/docs/clojure-macros/
- Code samples :
    * LiteratePrograms : http://en.literateprograms.org/Category:Programming_language:Clojure
    * Progopedia : http://progopedia.com/dialect/clojure/
    * RosettaCode : http://rosettacode.org/wiki/Category:Clojure
''')
    path_to_clojure_jar = \
        '/home/sylvaindesodt/TmpCode/.tmp/letscode/clojure-1.6.0.jar'
    interpreter_options = [
        '-cp',
        path_to_clojure_jar,
        'clojure.main']

    @classmethod
    def get_interpreter_name(cls):
        """Gets the name of the interpreter"""
        return 'java'

    @classmethod
    def get_file_content(cls, _):
        """Returns the content to be put in the file."""
        return dedent('''
            (println "Hello, world!")
            ''')

    @classmethod
    def man(cls, _):
        """Gets the manual"""
        return subprocess_call_wrapper(
            [cls.get_interpreter_name()] +
            cls.interpreter_options +
            ['--help'])

    @classmethod
    def is_ready(cls):
        """Check if language is 'ready'."""
        return shutil.which(cls.get_interpreter_name()) is not None and \
            os.path.isfile(cls.path_to_clojure_jar)


class Erlang(Language):
    """Erlang"""
    name = 'erlang'
    extensions = ['erl', 'hrl']
    inline_comment = '%'
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
    * Try Erlang : http://www.tryerlang.org/
    * Compile Erlang Online : http://www.compileonline.com/compile_erlang_online.php
- Learn in Y minutes : http://learnxinyminutes.com/docs/erlang/
- Code samples :
    * LiteratePrograms : http://en.literateprograms.org/Category:Programming_language:Erlang
    * Progopedia : http://progopedia.com/language/erlang/
    * RosettaCode : http://rosettacode.org/wiki/Category:Erlang
''')

    @classmethod
    def get_file_content(cls, _):
        """Returns the content to be put in the file."""
        return dedent('''
            io:format("~s~n", ["Hello, world!"])
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
    inline_comment = '#'
    information = dedent('''
- Wikipedia page : http://en.wikipedia.org/wiki/Elixir_%28programming_language%29
- Official site : http://elixir-lang.org/
- Documentation : http://elixir-lang.org/docs.html
- Subreddit : http://www.reddit.com/r/elixir
- Tools online :
    * Try Elixir : http://try-elixir.herokuapp.com/
- Learn in Y minutes : http://learnxinyminutes.com/docs/elixir/
- Code samples :
    * RosettaCode : http://rosettacode.org/wiki/Category:Elixir
''')


# Maybe this should inherit from interpretable and compilable
# language but I am too scared at the moment. Let's write tests first
class Lisp(InterpretableLanguage):
    """Lisp"""
    name = 'lisp'
    extensions = ['lisp']
    inline_comment = ';'
    block_comment = ('#|', '|#')
    shell_stop = '(ext:exit)'
    information = dedent('''
- Wikipedia page :
    * http://en.wikipedia.org/wiki/Lisp_%28programming_language%29
    * http://en.wikipedia.org/wiki/Common_Lisp
- Official site :
- Documentation :
    * Common lisp wiki : http://www.cliki.net/
- Subreddit :
    * http://www.reddit.com/r/lisp/
    * http://www.reddit.com/r/common_lisp
- Tools online :
- Learn in Y minutes :
    * http://learnxinyminutes.com/docs/common-lisp/
    * http://learnxinyminutes.com/docs/elisp/
- Code samples :
    * LiteratePrograms : http://en.literateprograms.org/Category:Programming_language:Lisp
    * Progopedia : http://progopedia.com/language/lisp/
    * RosettaCode :
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
    inline_comment = ';'
    block_comment = ('#|', '|#')
    nb_line_shebang = 0
    information = dedent('''
- Wikipedia page : http://en.wikipedia.org/wiki/Scheme_%28programming_language%29
- Official site :
- Documentation :
- Subreddit : http://www.reddit.com/r/scheme
- Tools online :
- Code samples :
    * LiteratePrograms : en.literateprograms.org/Category:Programming_language:Scheme
    * Progopedia : http://progopedia.com/dialect/scheme/
    * RosettaCode : http://rosettacode.org/wiki/Category:Scheme
''')

    @classmethod
    def get_file_content(cls, _):
        """Returns the content to be put in the file."""
        return dedent('''
            (display "Hello, world!")
            ''')

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
    inline_comment = ';'
    block_comment = ('#|', '|#')
    information = dedent('''
- Wikipedia page : http://en.wikipedia.org/wiki/Racket_%28programming_language%29
- Official site : http://racket-lang.org/
- Documentation : http://docs.racket-lang.org/index.html
    * Guide : http://docs.racket-lang.org/guide/
    * Reference : http://docs.racket-lang.org/reference/
- Subreddit : http://www.reddit.com/r/Racket
- Tools online :
- Learn in Y minutes : http://learnxinyminutes.com/docs/racket/
- Code samples :
    * RosettaCode : http://rosettacode.org/wiki/Category:Racket
''')

    @classmethod
    def get_file_content(cls, _):
        """Returns the content to be put in the file."""
        return dedent('''
                #lang racket
                "Hello, world!"
            ''')


class Arc(Language):
    """Arc"""
    name = 'arc'
    extensions = ['arc']
    information = dedent('''
- Wikipedia page : http://en.wikipedia.org/wiki/Arc_%28programming_language%29
- Official site : http://arclanguage.org/
- Code samples :
    * RosettaCode : http://rosettacode.org/wiki/Category:Arc
''')


class Caml(Language):
    """Caml"""
    name = 'caml'
    extensions = ['ml', 'mli']
    block_comment = ('(*', '*)')
    styles = [CODESTYLES['caml']]
    information = dedent('''
- Wikipedia page : http://en.wikipedia.org/wiki/Caml
- Official site : http://caml.inria.fr/
- Documentation :
- Subreddit :
- Tools online :
- Code samples :
    * LiteratePrograms : http://en.literateprograms.org/Category:Programming_language:Standard_ML
    * Progopedia : http://progopedia.com/language/standard-ml/
    * RosettaCode : http://rosettacode.org/wiki/Category:Caml
''')


class Scala(InterpretableLanguage):  # it can be compiled too but that's for later
    """Scala"""
    name = 'scala'
    extensions = ['scala']
    inline_comment = '//'
    block_comment = ('/*', '*/')
    nb_line_shebang = 2
    styles = [CODESTYLES['scala']]
    information = dedent('''
- Wikipedia page : http://en.wikipedia.org/wiki/Scala_%28programming_language%29
- Official site : http://www.scala-lang.org/
- Documentation : http://docs.scala-lang.org/
- Subreddit : http://www.reddit.com/r/scala/
- Tools online :
    * Scala tutorials : http://scalatutorials.com/tour/
    * Scala fiddle : http://scalafiddle.net/console
    * Scala JS Fiddle : http://www.scala-js-fiddle.com/
- Learn in Y minutes : http://learnxinyminutes.com/docs/scala/
- Code samples :
    * LiteratePrograms : http://en.literateprograms.org/Category:Programming_language:Scala
    * Progopedia : http://progopedia.com/language/scala/
    * RosettaCode : http://rosettacode.org/wiki/Category:Scala
''')

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
    inline_comment = '//'
    block_comment = ('/*', '*/')
    styles = [CODESTYLES['rust']]
    information = dedent('''
- Wikipedia page : http://en.wikipedia.org/wiki/Rust_%28programming_language%29
- Official site : http://www.rust-lang.org/
- Documentation : http://static.rust-lang.org/doc/master/rust.html
- Wiki : https://github.com/mozilla/rust/wiki
- Subreddit : http://www.reddit.com/r/rust/
- Tools online :
    * CompileOnline : http://www.compileonline.com/compile_rust_online.php
- Learn in Y minutes : http://learnxinyminutes.com/docs/rust/
- Code samples :
    * Progopedia : http://progopedia.com/language/rust/
    * RosettaCode : http://rosettacode.org/wiki/Category:Rust
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
    inline_comment = '--'
    information = dedent('''
- Wikipedia page : http://en.wikipedia.org/wiki/Elm_%28programming_language%29
- Official site : http://elm-lang.org/
- Documentation :
    * Syntax : http://elm-lang.org/learn/Syntax.elm
    * Librairies : http://elm-lang.org/Libraries.elm
- Subreddit : http://www.reddit.com/r/elm
- Tools online :
    * Try Elm : http://elm-lang.org/try
- Code samples :
    * RosettaCode : http://rosettacode.org/wiki/Category:Elm
''')


class Dart(Language):
    """Dart"""
    name = 'dart'
    extensions = ['dart']
    inline_comment = '//'
    styles = [CODESTYLES['dart']]
    information = dedent('''
- Wikipedia page : http://en.wikipedia.org/wiki/Dart_%28programming_language%29
- Official site : https://www.dartlang.org/
- Documentation :
    * Programmer's guide : https://www.dartlang.org/docs/
    * API : http://api.dartlang.org/
    * Language specifications : https://www.dartlang.org/docs/spec/
- Subreddit : http://www.reddit.com/r/dartlang/
- Tools online :
    * Try Dart : http://try.dartlang.org/
- Learn in Y minutes : http://learnxinyminutes.com/docs/dart/
- Code samples :
    * Progopedia : http://progopedia.com/language/dart/
    * RosettaCode : http://rosettacode.org/wiki/Category:Dart
''')


class Prolog(InterpretableLanguage):
    """Prolog"""
    name = 'prolog'
    interpreter_options = ['-t', 'goal', '-s']
    extensions = ['pl', 'pro', 'p']
    inline_comment = '%'
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
- Code samples :
    * LiteratePrograms : http://en.literateprograms.org/Category:Programming_language:Prolog
    * Progopedia : http://progopedia.com/language/prolog/
    * RosettaCode : http://rosettacode.org/wiki/Category:Prolog
''')

    @classmethod
    def get_interpreter_name(cls):
        """Gets the name of the interpreter"""
        return 'swipl'

    @classmethod
    def get_file_content(cls, _):
        """Returns the content to be put in the file."""
        return dedent('''
            goal :- write('Hello, world!'), nl,
                    halt.
            ''')


class PostScript(Language):
    """PostScript"""
    name = 'postscript'
    extensions = ['ps']
    inline_comment = '%'
    information = dedent('''
- Wikipedia page : http://en.wikipedia.org/wiki/PostScript
- Official site : http://www.adobe.com/products/postscript/
- Documentation :
    * http://www.adobe.com/products/postscript/pdfs/PLRM.pdf
- Subreddit : http://www.reddit.com/r/PostScript
- Tools online :
    * PS 2 PDF : http://www.ps2pdf.com/convert.htm
- Code samples :
    * LiteratePrograms : http://en.literateprograms.org/Category:Programming_language:PostScript
    * RosettaCode : http://rosettacode.org/wiki/Category:PostScript
''')


class Scilab(InterpretableLanguage):
    """Scilab"""
    name = 'scilab'
    extensions = [
        'sce',  # Executable statements
        'sci',  # Scilab or user defined functions
    ]
    inline_comment = '//'
    interpreter_options = ['-nwni', '-f']
    nb_line_shebang = 0
    information = dedent('''
- Wikipedia page : http://en.wikipedia.org/wiki/Scilab
- Official site : http://www.scilab.org/
- Documentation : http://www.scilab.org/resources/documentation
- Tools online :
    * http://cloud.scilab.in/
    * http://hotcalcul.com/on-line-calculator/scilab
- Code samples :
    * RosettaCode : http://rosettacode.org/wiki/Category:Scilab
''')

    @classmethod
    def get_file_content(cls, _):
        """Returns the content to be put in the file."""
        return dedent('''
            mprintf('Hello, world!\\n');
            quit
            ''')

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
    information = dedent('''
- Wikipedia page : http://en.wikipedia.org/wiki/GNU_Octave
- Official site : https://gnu.org/software/octave/
- Documentation : http://www.gnu.org/software/octave/doc/interpreter/index.html
- Subreddit : http://www.reddit.com/r/octave
- Tools online :
    * Octave Online : http://octave-online.net/
    * Execute Matlab/Octave online : http://www.compileonline.com/execute_matlab_online.php
- Code samples :
    * RosettaCode : http://rosettacode.org/wiki/Category:Octave
''')

    @classmethod
    def get_file_content(cls, _):
        """Returns the content to be put in the file."""
        return dedent('''
            printf ("Hello, world!\\n");
            ''')


class Genius(InterpretableLanguage):
    """Genius"""
    name = 'genius'
    extensions = ['gel']
    shell_stop = 'quit'
    information = dedent('''
- Wikipedia page : http://en.wikipedia.org/wiki/Genius_%28mathematics_software%29
- Official site : http://www.jirka.org/genius.html
- Documentation : http://www.jirka.org/genius-documentation/index.html
''')

    @classmethod
    def get_file_content(cls, _):
        """Returns the content to be put in the file."""
        return dedent('''
            "Hello, world!"
            ''')


class Swift(InterpretableLanguage):
    """Swift - parallel scripting language"""
    name = 'swift'
    extensions = ['swift']
    information = dedent('''
- Wikipedia page : http://en.wikipedia.org/wiki/Swift_%28parallel_scripting_language%29
- Official site : http://swift-lang.org/
''')

    @classmethod
    def get_file_content(cls, _):
        """Returns the content to be put in the file."""
        return 'tracef("%s\\n", "Hello, world!");\n'


class Forth(InterpretableLanguage):
    """Forth"""
    name = 'forth'
    extensions = ['fs', 'fth']
    inline_comment = '\\'
    information = dedent('''
- Wikipedia page : http://en.wikipedia.org/wiki/Forth_%28programming_language%29
- Official site : http://www.forth.org/
- Documentation : http://www.forth.org/literature.html
- Subreddit : http://www.reddit.com/r/Forth/
- Tools online :
    * JSForth (interpreter in JS) : http://www.forthfreak.net/jsforth.html
    * Forth online : http://www.compileonline.com/execute_forth_online.php
 http://rosettacode.org/wiki/Category:Forth- Code samples :
    * LiteratePrograms : http://en.literateprograms.org/Category:Programming_language:Forth
    * Progopedia : http://progopedia.com/language/forth/
    * RosettaCode : http://rosettacode.org/wiki/Category:Forth
''')

    @classmethod
    def get_interpreter_name(cls):
        """Gets the name of the interpreter"""
        return 'gforth'

    @classmethod
    def get_file_content(cls, _):
        """Returns the content to be put in the file."""
        return dedent('''
            .( Hello, world!) CR
            bye
            ''')


class Nimrod(InterpretableLanguage):
    """Nimrod"""
    name = 'nimrod'
    extensions = ['nim']
    inline_comment = '#'
    nb_line_shebang = 0
    interpreter_options = ['c', '--r']
    information = dedent('''
- Wikipedia page : http://en.wikipedia.org/wiki/Nimrod_%28programming_language%29
- Official site : http://nimrod-lang.org/
- Documentation : http://nimrod-lang.org/documentation.html
- Subreddit : http://www.reddit.com/r/nimrod
- Learn in Y minutes : http://learnxinyminutes.com/docs/nim/
- Code samples :
    * Progopedia : http://progopedia.com/language/nimrod/
    * RosettaCode : http://rosettacode.org/wiki/Category:Nimrod
''')

    @classmethod
    def get_file_content(cls, _):
        """Returns the content to be put in the file."""
        return dedent('''
            echo "Hello, world!"
            ''')


class ActionScript(Language):
    """ActionScript"""
    name = 'actionscript'
    extensions = ['as']
    inline_comment = '//'
    information = dedent('''
- Wikipedia page : http://en.wikipedia.org/wiki/ActionScript
- Official site :
    * http://www.adobe.com/devnet/actionscript.html
- Documentation :
- Subreddit : http://www.reddit.com/r/actionscript
- Code samples :
    * RosettaCode : http://rosettacode.org/wiki/Category:ActionScript
''')


class LiveScript(Language):
    """LiveScript"""
    name = 'livescript'
    extensions = ['ls']
    inline_comment = '//'  # or '#'
    block_comment = ('/*', '*/')
    styles = [CODESTYLES['livescript']]
    information = dedent('''
- Wikipedia page : http://en.wikipedia.org/wiki/LiveScript
- Official site : http://livescript.net/
- Documentation : http://livescript.net/#introduction
- Subreddit : http://www.reddit.com/r/livescript/
- Tools online :
    * Compile/run/AST : http://livescript.net/
- Learn in Y minutes : http://learnxinyminutes.com/docs/livescript/
- Code samples :
    * RosettaCode : http://rosettacode.org/wiki/Category:LiveScript
''')


class EcmaScript(Language):
    """EcmaScript"""
    name = 'ecmascript'
    extensions = ['es']
    inline_comment = '//'
    information = dedent('''
- Wikipedia page : http://en.wikipedia.org/wiki/ECMAScript
- Official site :
- Documentation :
''')


class MoonScript(Language):
    """MoonScript"""
    name = 'moonscript'
    extensions = ['moon']
    inline_comment = '--'
    information = dedent('''
- Wikipedia page : Not yet
- Official site : http://moonscript.org/
- Documentation : http://moonscript.org/reference/
- Subreddit : http://www.reddit.com/r/moonscript/
- Tools online :
    * Compile to Lua and/or run : http://moonscript.org/compiler/
- Code samples :
    * RosettaCode : http://rosettacode.org/wiki/Category:MoonScript
''')


class Ceylon(Language):
    """Ceylon"""
    name = 'ceylon'
    extensions = ['ceylon']
    inline_comment = '//'
    information = dedent('''
- Wikipedia page : http://en.wikipedia.org/wiki/Ceylon_%28programming_language%29
- Official site : http://ceylon-lang.org/
- Documentation : http://ceylon-lang.org/documentation/current/
- Subreddit :
- Tools online :
    * Try Ceylon : http://try.ceylon-lang.org/
- Learn in Y minutes :
- Code samples :
    * Progopedia : http://progopedia.com/language/ceylon/
    * RosettaCode :
''')
    compiler = 'ceylonc'


class Coq(Language):
    """Coq"""
    name = 'coq'
    extensions = ['v']
    block_comment = ('(*', '*)')
    compiler = 'coqc'  # interpreter is coqtop
    information = dedent('''
- Wikipedia page : http://en.wikipedia.org/wiki/Coq
- Official site : http://coq.inria.fr/
- Documentation : http://coq.inria.fr/documentation
- Wiki : http://coq.inria.fr/cocorico
- Subreddit : http://www.reddit.com/r/Coq
- Code samples :
    * RosettaCode : http://rosettacode.org/wiki/Category:Coq
''')

    @classmethod
    def get_file_content(cls, _):
        """Returns the content to be put in the file."""
        return dedent('''
            Require Import ssreflect.

            Variable P:Prop.

            Theorem helloworld: P -> P.
            Proof.
              done.
              Qed.

              Check helloworld.
            ''')


class Agda(Language):
    """Agda"""
    name = 'agda'
    extensions = ['agda', 'lagda']
    inline_comment = '--'
    block_comment = ('{-', '-}')
    information = dedent('''
- Wikipedia page : http://en.wikipedia.org/wiki/Agda_%28programming_language%29
- Official site : http://wiki.portal.chalmers.se/agda/pmwiki.php
- Documentation : http://wiki.portal.chalmers.se/agda/pmwiki.php?n=Main.Documentation
- Subreddit : http://www.reddit.com/r/agda/
- Code samples :
    * Progopedia : http://progopedia.com/language/agda/
    * RosettaCode : http://rosettacode.org/wiki/Category:Agda
''')


class RLanguage(InterpretableLanguage):
    """R"""
    name = 'r'
    extensions = ['R']
    styles = [CODESTYLES['r-google']]
    information = dedent('''
- Wikipedia page : http://en.wikipedia.org/wiki/R_%28programming_language%29
- Official site : http://www.r-project.org/
- Documentation : http://www.r-project.org/other-docs.html
- Subreddit : http://www.reddit.com/r/Rlanguage
- Tools online :
    * Try R Code School : http://tryr.codeschool.com/
- Learn in Y minutes : http://learnxinyminutes.com/docs/r/
- Code samples :
    * RosettaCode : http://rosettacode.org/wiki/Category:R
''')

    @classmethod
    def get_interpreter_name(cls):
        """Gets the name of the interpreter"""
        return 'Rscript'

    @classmethod
    def get_file_content(cls, _):
        """Returns the content to be put in the file."""
        return dedent('''
            cat ("Hello, world!\\n")
            ''')


class SAS(Language):
    """SAS"""
    name = 'sas'
    extensions = ['sas']
    block_comment = ('/*', '*/')
    information = dedent('''
- Wikipedia page : http://en.wikipedia.org/wiki/SAS_language
''')


class CSharp(Language):
    """C#"""
    name = 'csharp'
    extensions = ['cs']
    inline_comment = '//'
    block_comment = ('/*', '*/')
    styles = [CODESTYLES['csharp']]
    information = dedent('''
- Wikipedia page : http://en.wikipedia.org/wiki/C_Sharp_%28programming_language%29
- Official site :
- Documentation :
- Subreddit : http://www.reddit.com/r/csharp
- Tools online :
    * C# format : http://www.manoli.net/csharpformat/
    * JSON to C# : http://json2csharp.com
- Learn in Y minutes : http://learnxinyminutes.com/docs/csharp/
- Code samples :
    * LiteratePrograms : http://en.literateprograms.org/Category:Programming_language:C_Sharp
    * Progopedia : http://progopedia.com/language/c-sharp/
    * RosettaCode : http://rosettacode.org/wiki/Category:C_sharp
- Misc ressources :
    * Hidden features (StackOverflow) : http://stackoverflow.com/questions/9033/hidden-features-of-c
''')

    @classmethod
    def get_file_content(cls, _):
        """Returns the content to be put in the file."""
        return dedent('''
            using System;

            class Program
            {
                static void Main()
                {
                    Console.WriteLine("Hello, world!");
                }
            }
            ''')


class FSharp(Language):
    """F#"""
    name = 'fsharp'  # fsharpc
    extensions = ['fsx', 'fssscript']
    inline_comment = '//'
    information = dedent('''
- Wikipedia page : http://en.wikipedia.org/wiki/F_Sharp_%28programming_language%29
- Official site : http://fsharp.org/
- Documentation : http://fsharp.org/about/index.html#documentation
- Subreddit : http://www.reddit.com/r/fsharp
- Tools online :
    * Try F# : http://www.tryfsharp.org/Create
    * F# Code formatting : http://fantomasweb.apphb.com
- Learn in Y minutes : http://learnxinyminutes.com/docs/fsharp/
- Code samples :
    * LiteratePrograms : http://en.literateprograms.org/Category:Programming_language:F_Sharp
    * Progopedia : http://progopedia.com/language/f-sharp/
    * RosettaCode : http://rosettacode.org/wiki/Category:F_Sharp
''')

    @classmethod
    def get_file_content(cls, _):
        """Returns the content to be put in the file."""
        return dedent('''
            printfn "Hello, world!"
            ''')


class Factor(Language):
    """Factor"""
    name = 'factor'
    extensions = ['factor']
    inline_comment = '!'
    information = dedent('''
- Wikipedia page : http://en.wikipedia.org/wiki/Factor_%28programming_language%29
- Official site : http://factorcode.org/
- Documentation : http://docs.factorcode.org/content/article-handbook.html
- Subreddit : http://www.reddit.com/r/factor
- Code samples :
    * Progopedia : http://progopedia.com/language/factor/
    * RosettaCode : http://rosettacode.org/wiki/Category:Factor
''')

    @classmethod
    def get_file_content(cls, _):
        """Returns the content to be put in the file."""
        return dedent('''
            "Hello, world!" print
            ''')


class SmallTalk(InterpretableLanguage):
    """SmallTalk"""
    name = 'smalltalk'
    extensions = ['st']
    block_comment = ('"', '"')
    information = dedent('''
- Wikipedia page : http://en.wikipedia.org/wiki/Smalltalk
- Official site : http://www.smalltalk.org/
- Documentation : http://www.smalltalk.org/smalltalk/learning.html
- Subreddit : http://www.reddit.com/r/smalltalk/
- Tools online :
    * Compile online : http://www.compileonline.com/execute_smalltalk_online.php
- Learn in Y minutes :
- Code samples :
    * LiteratePrograms : http://en.literateprograms.org/Category:Programming_language:Smalltalk
    * Progopedia : http://progopedia.com/language/smalltalk/
    * RosettaCode : http://rosettacode.org/wiki/Category:Smalltalk
''')

    @classmethod
    def get_interpreter_name(cls):
        """Gets the name of the interpreter"""
        return 'gst'

    @classmethod
    def get_file_content(cls, _):
        """Returns the content to be put in the file."""
        return dedent('''
            Transcript show: 'Hello, world!
            '.
            ''')

    @classmethod
    def run(cls, args):
        """Runs the code"""
        filename = cls.get_actual_filename_to_use(args)
        # gst does not return error code so let's fail beautifully
        if not os.path.isfile(filename):
            return False
        return subprocess_call_wrapper(
            [cls.get_interpreter_name()] +
            cls.interpreter_options +
            [filename])


class Groovy(InterpretableLanguage):
    """Groovy"""
    name = 'groovy'
    extensions = ['groovy', 'gvy', 'gy', 'gsh']
    inline_comment = '//'
    block_comment = ('/*', '*/')
    information = dedent('''
- Wikipedia page : http://en.wikipedia.org/wiki/Groovy_(programming_language)
- Official site : http://groovy.codehaus.org/
- Documentation : http://groovy.codehaus.org/Documentation
- Subreddit : http://www.reddit.com/r/groovy
- Tools online :
    * Groovy web console : http://groovyconsole.appspot.com/
    * Execute online : http://www.compileonline.com/execute_groovy_online.php
- Learn in Y minutes : http://learnxinyminutes.com/docs/groovy/
- Code samples :
    * LiteratePrograms : http://en.literateprograms.org/Category:Programming_language:Groovy
    * Progopedia : http://progopedia.com/language/groovy/
    * RosettaCode : http://rosettacode.org/wiki/Category:Groovy
''')

    @classmethod
    def get_file_content(cls, _):
        """Returns the content to be put in the file."""
        return dedent('''
            println("Hello, world!")
            ''')


class Eiffel(Language):
    """Eiffel"""
    name = 'eiffel'
    extensions = ['e']
    inline_comment = '--'
    information = dedent('''
- Wikipedia page : http://en.wikipedia.org/wiki/Eiffel_%28programming_language%29
- Official site : https://dev.eiffel.com/Main_Page
- Documentation : https://docs.eiffel.com/
- Code samples :
    * LiteratePrograms : http://en.literateprograms.org/Category:Programming_language:Eiffel
    * RosettaCode : http://rosettacode.org/wiki/Category:Eiffel
''')

    @classmethod
    def get_file_content(cls, _):
        """Returns the content to be put in the file."""
        return dedent('''
            class
                HELLO_WORLD
            create
                make
            feature
                make
                    do
                        print ("Hello, world!%N")
                    end
            end
            ''')


class JLanguage(Language):
    """J"""
    name = 'j'
    extensions = ['ijs']
    inline_comment = 'NB.'
    information = dedent('''
- Wikipedia page : http://en.wikipedia.org/wiki/J_(programming_language)
- Official site : http://www.jsoftware.com/
- Documentation : http://www.jsoftware.com/jwiki/System/Documentation
- Wiki : http://www.jsoftware.com/jwiki/
- Subreddit : http://www.reddit.com/r/jlang
- Code samples :
    * LiteratePrograms : http://en.literateprograms.org/Category:Programming_language:J
    * Progopedia : http://progopedia.com/language/j/
    * RosettaCode : http://rosettacode.org/wiki/Category:J
''')

    @classmethod
    def get_file_content(cls, _):
        """Returns the content to be put in the file."""
        return dedent('''
            'Hello, world!'
            ''')


class WolframLanguage(Language):
    """Wolfram"""
    name = 'wolfram'
    extensions = ['wl', 'nb', 'm']
    block_comment = ('/*', '*/')
    information = dedent('''
- Wikipedia page : http://en.wikipedia.org/wiki/Wolfram_Language
- Official site : http://reference.wolfram.com/language/
- Subreddit : http://www.reddit.com/r/wolframlanguage/
- Code samples :
    * Progopedia : http://progopedia.com/language/wolfram-mathematica/
    * RosettaCode : http://rosettacode.org/wiki/Category:Wolfram_Language
''')


class Idris(Language):
    """Idris"""
    name = 'idris'
    extensions = ['idr', 'lidr']
    inline_comment = '--'
    shell_stop = ':q'  # or :quit
    information = dedent('''
- Wikipedia page : http://en.wikipedia.org/wiki/Idris_%28programming_language%29
- Official site : http://www.idris-lang.org/
- Documentation : http://www.idris-lang.org/documentation/
- Subreddit : http://www.reddit.com/r/Idris
- Code samples :
    * RosettaCode : http://rosettacode.org/wiki/Category:Idris
''')

    @classmethod
    def get_file_content(cls, _):
        """Returns the content to be put in the file."""
        return dedent('''
            module Main

             main : IO ()
             main = putStrLn "Hello, world!"
            ''')


class APL(Language):
    """APL"""
    name = 'apl'
    extensions = ['apl']
    inline_comment = '@'  # '⍝' seems to be suggested sometimes
    information = dedent('''
- Wikipedia page : http://en.wikipedia.org/wiki/APL_%28programming_language%29
- Official site :
- Documentation :
- Subreddit : http://www.reddit.com/r/apljk/
- Tools online :
    * APL Demo : http://ngn.github.io/apl/web/index.html
    * Try APL : http://tryapl.org/
    * Gnu APL.js : http://baruchel.hd.free.fr/apps/apl/
- Learn in Y minutes :
- Code samples :
    * LiteratePrograms : http://en.literateprograms.org/Category:Programming_language:APL
    * Progopedia : http://progopedia.com/language/apl/
    * RosettaCode : http://rosettacode.org/wiki/Category:APL
''')

    @classmethod
    def get_file_content(cls, _):
        """Returns the content to be put in the file."""
        return 'Hello, world!'


class Pike(InterpretableLanguage):
    """Pike"""
    name = 'pike'
    extensions = ['pike']
    inline_comment = '//'
    block_comment = ('/*', '*/')
    shell_stop = 'exit'
    information = dedent('''
- Wikipedia page : http://en.wikipedia.org/wiki/Pike_%28programming_language%29
- Official site : http://pike.lysator.liu.se/
- Documentation : http://pike.lysator.liu.se/docs/
- Code samples :
    * Progopedia : http://progopedia.com/language/pike/
    * RosettaCode : http://rosettacode.org/wiki/Category:Pike
''')

    @classmethod
    def get_file_content(cls, _):
        """Returns the content to be put in the file."""
        return dedent('''
            int main() {
                write("Hello, world!\\n");
                return 0;
            }
            ''')


class Oz(CompilableLanguage):
    """Oz"""
    name = 'oz'
    extensions = ['oz']
    inline_comment = '%'
    block_comment = ('/*', '*/')
    compiler = 'ozc'
    compiler_options = ['-x']
    information = dedent('''
- Wikipedia page : http://en.wikipedia.org/wiki/Oz_%28programming_language%29
- Official site : http://mozart.github.io/
- Documentation : http://mozart.github.io/documentation/
- Code samples :
    * LiteratePrograms : http://en.literateprograms.org/Category:Programming_language:Oz
    * Progopedia : http://progopedia.com/language/oz/
    * RosettaCode : http://rosettacode.org/wiki/Category:Oz
''')

    @classmethod
    def get_file_content(cls, _):
        """Returns the content to be put in the file."""
        return dedent('''
            functor
            import
               Application
               System

            define
               {System.showInfo 'Hello, world!'}
               {Application.exit 0}

            end
            ''')


class Verilog(CompilableLanguage):
    """Verilog"""
    name = 'verilog'
    extensions = ['v']
    inline_comment = '//'
    block_comment = ('/*', '*/')
    compiler = 'iverilog'
    compiler_options = ['-N']
    information = dedent('''
- Wikipedia page : http://en.wikipedia.org/wiki/Verilog
- Official site : http://www.verilog.com/
- Subreddit : http://www.reddit.com/r/Verilog
- Tools online :
    * Verilog online : http://iverilog.com/
- Learn in Y minutes :
- Code samples :
    * LiteratePrograms : http://en.literateprograms.org/Category:Programming_language:Verilog
    * RosettaCode : http://rosettacode.org/wiki/Category:Verilog
''')

    @classmethod
    def get_file_content(cls, _):
        """Returns the content to be put in the file."""
        return dedent('''
            module main;
              initial
                begin
                  $display("Hello, world!");
                  $finish;
                end
            endmodule
            ''')


class SLang(InterpretableLanguage):
    """SLang"""
    name = 'slang'
    extensions = ['sl']
    inline_comment = '%'
    shell_stop = 'quit'
    information = dedent('''
- Wikipedia page : http://en.wikipedia.org/wiki/S-Lang_%28programming_language%29
- Official site : http://www.jedsoft.org/slang/index.html
- Documentation : http://www.jedsoft.org/slang/docs.html
- Code samples :
    * Progopedia : http://progopedia.com/language/s-lang/
    * RosettaCode : http://rosettacode.org/wiki/Category:S-lang
''')

    @classmethod
    def get_file_content(cls, _):
        """Returns the content to be put in the file."""
        return 'printf("Hello, world!\\n");'

    @classmethod
    def get_interpreter_name(cls):
        """Gets the name of the interpreter"""
        return 'slsh'


class Spark(Language):
    """Spark"""
    name = 'spark'
    extensions = ['spark']
    inline_comment = '#'
    information = dedent('''
- Wikipedia page : http://en.wikipedia.org/wiki/SPARK_%28programming_language%29
- Code samples :
    * RosettaCode : http://rosettacode.org/wiki/Category:SPARK
''')


class Icon(CompilableLanguage):  # Could also be interpreted
    """Icon"""
    name = 'icon'
    extensions = ['icn']
    inline_comment = '#'
    compiler = 'icont'
    information = dedent('''
- Wikipedia page : http://en.wikipedia.org/wiki/Icon_programming_language
- Official site : http://www.cs.arizona.edu/icon/
- Documentation :
    * http://www.cs.arizona.edu/icon/refernce/ref.htm
    * http://www.cs.arizona.edu/icon/v951/docguide.htm
- Code samples :
    * LiteratePrograms : http://en.literateprograms.org/Category:Programming_language:Icon
    * Progopedia : http://progopedia.com/language/icon/
    * RosettaCode : http://rosettacode.org/wiki/Category:Icon
''')

    @classmethod
    def get_file_content(cls, _):
        """Returns the content to be put in the file."""
        return dedent('''
            procedure main()
                write("Hello, world!")
            end
            ''')

    @classmethod
    def compile(cls, args):
        """Compiles the file"""
        filename = cls.get_actual_filename_to_use(args)
        output = cls.get_output_filename(filename)
        return subprocess_call_wrapper(
            [cls.compiler, '-o', output] + cls.compiler_options + [filename])


class Mars(Language):
    """Mars"""
    name = 'mars'
    extensions = ['mar']
    inline_comment = '#'
    information = dedent('''
- Wikipedia page :
- Official site : http://mars-lang.appspot.com/
- Documentation :
    * General doc : http://mars-lang.appspot.com/docs/index.html
    * Language ref : http://mars-lang.appspot.com/docs/ref/index.html
    * Library ref : http://mars-lang.appspot.com/docs/lib/index.html
''')


class Kotlin(Language):
    """Kotlin"""
    name = 'kotlin'
    extensions = ['kt']
    inline_comment = '//'
    styles = [CODESTYLES['kotlin']]
    information = dedent('''
- Wikipedia page : http://en.wikipedia.org/wiki/Kotlin_%28programming_language%29
- Official site : http://kotlinlang.org/
- Documentation : http://kotlinlang.org/docs/reference/
- Subreddit : http://www.reddit.com/r/Kotlin
- Tools online :
    * Kotlin Web Demo : http://kotlin-demo.jetbrains.com/?_ga=1.9307441.522235683.1405500063
- Code samples :
    * LiteratePrograms :
    * Progopedia :
    * RosettaCode : http://rosettacode.org/wiki/Category:Kotlin
''')


class AMPL(Language):
    """AMPL"""
    name = 'ampl'
    extensions = ['ampl', 'mod', 'dat', 'run']
    inline_comment = '#'
    information = dedent('''
- Wikipedia page : http://en.wikipedia.org/wiki/AMPL
- Official site : http://ampl.com/
- Tools online :
    * Try AMPL Online : http://ampl.com/try-ampl/start/
- Code samples :
    * RosettaCode : http://rosettacode.org/wiki/Category:AMPL
''')

    @classmethod
    def get_file_content(cls, _):
        """Returns the content to be put in the file."""
        return dedent('''
            printf "Hello, world!\\n";
            ''')


class Gosu(Language):
    """Gosu"""
    name = 'gosu'
    extensions = ['gsp', 'gs', 'gst', 'gsx']
    inline_comment = '//'
    block_comment = ('/*', '*/')
    information = dedent('''
- Wikipedia page : http://en.wikipedia.org/wiki/Gosu_%28programming_language%29
- Official site : http://gosu-lang.org
- Documentation : http://gosu-lang.github.io/docs.html
- Tools online :
    * Play : http://gosu-lang.github.io/play.html
- Code samples :
    * RosettaCode : http://rosettacode.org/wiki/Category:Gosu
''')

    @classmethod
    def get_file_content(cls, _):
        """Returns the content to be put in the file."""
        return dedent('''
            print('Hello, world!')
            ''')


class Nemerle(Language):
    """Nemerle"""
    name = 'nemerle'
    extensions = ['n']
    inline_comment = '//'
    block_comment = ('/*', '*/')
    information = dedent('''
- Wikipedia page : http://en.wikipedia.org/wiki/Nemerle
- Official site : http://nemerle.org
- Code samples :
    * Progopedia : http://progopedia.com/language/nemerle/
    * RosettaCode : http://rosettacode.org/wiki/Category:Nemerle
''')


class Zimbu(Language):
    """Zimbu"""
    name = 'zimbu'
    extensions = ['zu']
    inline_comment = '#'
    information = dedent('''
- Official site : http://www.zimbu.org/
''')

    @classmethod
    def get_file_content(cls, _):
        """Returns the content to be put in the file."""
        return dedent('''
            FUNC Main() int
              IO.write("Hello, World!\n")
                RETURN 0
            }
            ''')


class Mirah(Language):
    """Mirah"""
    name = 'mirah'
    extensions = ['mirah']
    inline_comment = '#'
    information = dedent('''
- Official site : http://www.mirah.org/
''')


class QKx(Language):
    """Q (Programming Language from Kx Systems"""
    name = 'q-kx'
    extensions = ['q']
    inline_comment = ' /'  # space is important
    information = dedent('''
- Wikipedia page : http://en.wikipedia.org/wiki/Q_%28programming_language_from_Kx_Systems%29
- Official site :
- Documentation :
- Code samples :
    * RosettaCode : http://rosettacode.org/wiki/Category:Q
''')


class QEquational(Language):  # Interpretable with 'q'
    """Q (Equational Programming Language)"""
    name = 'q-eq'
    extensions = ['q']
    inline_comment = '//'
    block_comment = ('/*', '*/')
    information = dedent('''
- Wikipedia page : http://en.wikipedia.org/wiki/Q_%28equational_programming_language%29
- Official site : http://q-lang.sourceforge.net/
- Documentation : http://q-lang.sourceforge.net/documentation.html
''')

    @classmethod
    def get_file_content(cls, filename):
        """Returns the content to be put in the file."""
        return dedent('''
            hello = writes "Hello, world!";''')


class Pure(Language):  # Interpretable AND compilable with 'pure'
    """Pure"""
    name = 'pure'
    extensions = ['pure']
    inline_comment = '//'
    block_comment = ('/*', '*/')
    information = dedent('''
- Wikipedia page : http://en.wikipedia.org/wiki/Pure_%28programming_language%29
- Official site : http://purelang.bitbucket.org/
- Documentation : http://puredocs.bitbucket.org/pure.html
- Code samples :
    * RosettaCode : http://rosettacode.org/wiki/Category:Pure
''')

    @classmethod
    def get_file_content(cls, filename):
        """Returns the content to be put in the file."""
        return dedent('''
            using system;
            puts "Hello, world!";''')


class Kaya(Language):
    """Kaya"""
    name = 'kaya'
    extensions = ['k']
    inline_comment = '//'
    block_comment = ('/*', '*/')
    information = dedent('''
- Wikipedia page : http://en.wikipedia.org/wiki/Kaya_%28programming_language%29
- Official site : http://kayalang.org/
- Documentation : http://kayalang.org/tutorial
- Code samples :
    * Progopedia :
    * RosettaCode : http://rosettacode.org/wiki/Category:Kaya
''')

    @classmethod
    def get_file_content(cls, filename):
        """Returns the content to be put in the file."""
        return dedent('''
            program hello;

            Void main() {
                putStrLn("Hello, world!");
            }
            ''')


class Haxe(Language):
    """Haxe"""
    name = 'haxe'
    extensions = ['hx', 'hxml']
    inline_comment = '//'
    block_comment = ('/*', '*/')
    information = dedent('''
- Wikipedia page : http://en.wikipedia.org/wiki/Haxe
- Official site : http://haxe.org/
- Documentation : http://haxe.org/documentation/introduction/
- Subreddit : http://www.reddit.com/r/haxe/
- Tools online : http://try.haxe.org/
- Learn in Y minutes : http://learnxinyminutes.com/docs/haxe/
- Code samples :
    * RosettaCode : http://rosettacode.org/wiki/Category:Haxe
''')

    @classmethod
    def get_file_content(cls, filename):
        """Returns the content to be put in the file."""
        return dedent('''
            class HelloWorld {
                static public function main() {
                    trace("Hello, world!");
                }
            }
            ''')


class ExampleLanguage(Language):
    """Example"""
    name = None
    extensions = None
    inline_comment = None
    block_comment = None
    information = dedent('''
- Wikipedia page :
- Official site :
- Documentation :
- Subreddit :
- Tools online :
- Learn in Y minutes :
- Code samples :
    * LiteratePrograms :
    * Progopedia :
    * RosettaCode :
''')


def get_subclasses(klass):
    """Gets the list of direct/indirect subclasses of a class"""
    subclasses = klass.__subclasses__()
    for derived in list(subclasses):
        subclasses.extend(get_subclasses(derived))
    return subclasses

LANGUAGES = [l for l in get_subclasses(Language) if l.name is not None]
LANGUAGE_NAMES = {l.name: l for l in LANGUAGES}

# vim: filetype=python tabstop=8 expandtab shiftwidth=4 softtabstop=4

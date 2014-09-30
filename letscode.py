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

# Next steps are :
# - change design to split things related to the language itself and things
#   related to the compiler/intepreter/etc. It could be a good idea to use
#   composition over inheritance.

import argparse
from helper import print_info
from modeline import MODELINE_SUPPORTED_EDITORS
from languages import LANGUAGE_NAMES
from codestyles import CODESTYLES
from detectlanguage import detect_language_from_filename


def main():
    """Main"""
    default_actions = ['create']
    default_editors = ['style_desc', 'vim']
    parser = argparse.ArgumentParser(
        description='Makes your code easy to edit/compile/run/test/check')
    parser.add_argument(
        'filename',
        help=('filename (with or without the extension)'))
    parser.add_argument(
        '--language', '-l',
        help=('programming language to consider (default: %(default)s)'),
        choices=sorted(LANGUAGE_NAMES.keys()) + ['autodetect'],
        default='autodetect')
    parser.add_argument(
        '--style', '-s',
        help=('code style to be used (default is to get the one specific to the language - if any)'),
        choices=sorted(CODESTYLES.keys()))
    parser.add_argument(
        '--action', '-a',
        action='append',
        help=('action(s) to perform (default: %s)' % default_actions),
        choices=[
            'create', 'edit', 'run', 'check', 'compile', 'coverage',
            'debug', 'info', 'upload', 'minify', 'pretty',
            'obfuscate', 'doctest', 'interactive', 'gendoc',
            'to_py3', 'uml', 'man', 'unittest', 'functionlist',
            'profile', 'metrics', 'display', 'shell'],
        # this list could be generated
        default=[])
    parser.add_argument(
        '--failure', '-f',
        help=('behavior on failure (default: %(default)s)'),
        choices=['stop', 'continue'],
        default='stop')
    parser.add_argument(
        '--extension_mode', '-e',
        help=('extension mode (default: %(default)s)'),
        choices=['auto', 'never', 'always'],
        default='auto')
    parser.add_argument(
        '--override_file', '-o',
        help=('override already existing file (default: %(default)s)'),
        choices=['n', 'y'],
        default='n')
    parser.add_argument(
        '--modeline', '-m',
        help=('location for modeline (editor settings) (default: %(default)s)'),
        choices=['top', 'bottom', 'both', 'none'],
        default='top')
    parser.add_argument(
        '--text-editors', '-t',
        action='append',
        help=('text editors for modelines (default: %s)' % default_editors),
        choices=MODELINE_SUPPORTED_EDITORS,
        default=[])
    args = parser.parse_args()

    # Workaround issue http://bugs.python.org/issue16399
    if not args.action:
        args.action = default_actions
    if not args.text_editors:
        args.text_editors = default_editors

    language = args.language
    if language == 'autodetect':
        language = detect_language_from_filename(args.filename)
        print_info('Detected language is %s' % language)
        if language is None:
            return
    assert language in LANGUAGE_NAMES
    results = LANGUAGE_NAMES[language].perform_actions(args)
    greentick = '\033[92m✔'
    redcross = '\033[91m✘'
    undocolor = '\033[0m'
    for action, ret in results:
        print_info(
            (greentick if ret else redcross) +
            undocolor + ' ' + action)
    return all(res for _, res in results)


if __name__ == '__main__':
    main()

# vim: filetype=python tabstop=8 expandtab shiftwidth=4 softtabstop=4

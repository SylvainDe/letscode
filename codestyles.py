#!/usr/bin/python3
# -*- coding: utf-8
"""Container of the different code styles. Used to generate modelines."""

CODESTYLE_LIST = [
    {
        'name': 'kernel',
        'ref': 'https://www.kernel.org/doc/Documentation/CodingStyle',
        'indentation_level': 8,
        'tab_width': 8,
    },
    {
        'name': 'objc-google',
        'ref': 'http://google-styleguide.googlecode.com/svn/trunk/objcguide.xml',
        'indentation_level': 2,
        'tab_width': 2,
        'expand_tab': True,
    },
    {
        'name': 'cpp-google',
        'ref': 'http://google-styleguide.googlecode.com/svn/trunk/cppguide.xml',
        'indentation_level': 2,
        'tab_width': 2,
        'expand_tab': True,
    },
    {
        'name': 'java-google',
        'ref': 'http://google-styleguide.googlecode.com/svn/trunk/javaguide.html',
        'indentation_level': 2,
        'tab_width': 2,
        'expand_tab': True,
    },
    {
        'name': 'java-oracle',
        'ref': 'http://www.oracle.com/technetwork/java/codeconventions-150003.pdf',
        'indentation_level': 4,
        'tab_width': 8,
        'expand_tab': True,
    },
    {
        'name': 'html-google',
        'ref': 'http://google-styleguide.googlecode.com/svn/trunk/htmlcssguide.xml#Indentation',
        'indentation_level': 2,
        'tab_width': 2,
        'expand_tab': True,
    },
    {
        'name': 'css',
        'ref': 'https://github.com/csswizardry/CSS-Guidelines',
        'indentation_level': 4,
        'tab_width': 4,
        'expand_tab': True,
    },
    {
        'name': 'coffeescript',
        'ref': 'https://github.com/polarmobile/coffeescript-style-guide',
        'indentation_level': 4,
        'tab_width': 4,
        'expand_tab': True,
    },
    {
        'name': 'shell-google',
        'ref': 'https://google-styleguide.googlecode.com/svn/trunk/shell.xml',
        'indentation_level': 2,
        'tab_width': 2,
        'expand_tab': True,
    },
    {
        'name': 'ruby',
        'ref': 'https://github.com/bbatsov/ruby-style-guide https://github.com/styleguide/ruby',
        'indentation_level': 2,
        'tab_width': 2,
        'expand_tab': True,
    },
    {
        'name': 'javascript',
        'ref': 'https://github.com/styleguide/javascript',
        'indentation_level': 2,
        'tab_width': 2,
        'expand_tab': True,
    },
    {
        'name': 'php-zend',
        'ref': 'http://framework.zend.com/manual/1.12/en/coding-standard.html',
        'indentation_level': 4,
        'tab_width': 4,
        'expand_tab': True,
    },
    {
        'name': 'php-symfony',
        'ref': 'http://trac.symfony-project.org/wiki/HowToContributeToSymfony#CodingStandards',
        'indentation_level': 2,
        'tab_width': 2,
        'expand_tab': True,
    },
    {
        'name': 'php-pear',
        'ref': 'http://pear.php.net/manual/en/standards.indenting.php',
        'indentation_level': 4,
        'tab_width': 4,
        'expand_tab': True,
    },
    {
        'name': 'python',
        'ref': 'http://legacy.python.org/dev/peps/pep-0008/',
        'indentation_level': 4,
        'tab_width': 4,
        'expand_tab': True,
    },
    {
        'name': 'rust',
        'ref': 'https://github.com/rust-lang/rust-guidelines',
        'indentation_level': 4,
        'tab_width': 4,
        'expand_tab': True,
    },
    {
        'name': 'r-google',
        'ref': 'http://google-styleguide.googlecode.com/svn/trunk/Rguide.xml',
        'indentation_level': 2,
        'tab_width': 2,
        'expand_tab': True,
    },
    {
        'name': 'kotlin',
        'ref': 'http://kotlinlang.org/docs/reference/coding-conventions.html',
        'indentation_level': 4,
        'tab_width': 4,
        'expand_tab': True,
    },

]

CODESTYLES = {s['name']: s for s in CODESTYLE_LIST}

#!/usr/bin/python3
# -*- coding: utf-8
"""Helper functions for letscode."""

import subprocess


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

# vim: filetype=python tabstop=8 expandtab shiftwidth=4 softtabstop=4

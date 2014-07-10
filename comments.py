#!/usr/bin/python3
# -*- coding: utf-8
"""Functions to comment string."""

from helper import print_warning


def comment_string_with_inline(string, inline_comment):
    """Return string commented using inline comments"""
    if not string:
        return string
    return '\n'.join(inline_comment + ' ' +
             s.strip() for s in string.split('\n')) + '\n'


def comment_string_with_block(string, block_comment):
    """Return string commented using block comments"""
    if not string:
        return string
    beg, end = block_comment
    return beg + ' ' + string.replace(beg, '').replace(end, '') + ' ' + end


def comment_string(string, inline_comment, block_comment):
    """Return string commented in the best way"""
    if block_comment is not None and (inline_comment is None or '\n' in string):
        return comment_string_with_block(string, block_comment)
    elif inline_comment is not None:
        assert block_comment is None or '\n' not in string
        return comment_string_with_inline(string, inline_comment)
    else:
        print_warning('Cannot comment string')
        return ''  # Empty string is safe and shoudn't cause troubles


# vim: filetype=python tabstop=8 expandtab shiftwidth=4 softtabstop=4

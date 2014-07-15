#!/usr/bin/python3
# -*- coding: utf-8
"""Unit tests for code in comments.py."""

from comments import comment_string_with_inline, \
    comment_string_with_block, \
    comment_string
import unittest


class TestCommentString(unittest.TestCase):
    """Unit tests related to string commenting"""
    def test_inline_comment(self):
        """Unit tests related to inline comments"""
        self.assertEqual(comment_string_with_inline('', None), '')
        self.assertEqual(comment_string_with_inline('', '#'), '')
        self.assertEqual(comment_string_with_inline('a', '#'), '# a\n')
        self.assertEqual(comment_string_with_inline('a\nb', '#'), '# a\n# b\n')

    def test_block_comment(self):
        """Unit tests related to block comments"""
        self.assertEqual(comment_string_with_block('', None), '')
        self.assertEqual(comment_string_with_block('', ('/*', '*/')), '')
        self.assertEqual(comment_string_with_block('a', ('/*', '*/')), '/* a */')
        self.assertEqual(comment_string_with_block('a\nb', ('/*', '*/')), '/* a\nb */')

    def test_comment(self):
        """Unit tests related to inline comments"""
        self.assertEqual(comment_string('', None, None), '')
        self.assertEqual(comment_string('a', None, None), '')
        self.assertEqual(comment_string('a', '#', None), '# a\n')
        self.assertEqual(comment_string('a', None, ('/*', '*/')), '/* a */')
        self.assertEqual(comment_string('a', '#', ('/*', '*/')), '# a\n')
        self.assertEqual(comment_string('a\nb', '#', None), '# a\n# b\n')
        self.assertEqual(comment_string('a\nb', '#', ('/*', '*/')), '/* a\nb */')

# vim: filetype=python tabstop=8 expandtab shiftwidth=4 softtabstop=4

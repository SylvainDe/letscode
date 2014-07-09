#!/usr/bin/python3
# -*- coding: utf-8
"""Unit tests for code in detectlanguage.py."""

from detectlanguage import get_extensions_map, detect_language_from_filename
import unittest


class TestLanguageDetection(unittest.TestCase):
    """Unit tests related to language detection"""
    def test_get_extensions_map(self):
        """Unit tests for get_extensions_map()"""
        ext = get_extensions_map()
        self.assertIn('.php', ext)
        self.assertIn('php', ext['.php'])
        self.assertIn('.cpp', ext)
        self.assertIn('cpp', ext['.cpp'])
        self.assertIn('r', ext['.r'])

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
        self.assertEqual(detect_language_from_filename('/b/a.R'), 'r')
        self.assertEqual(detect_language_from_filename('/b/a.r'), 'r')

# vim: filetype=python tabstop=8 expandtab shiftwidth=4 softtabstop=4

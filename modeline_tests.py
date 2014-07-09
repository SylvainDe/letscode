#!/usr/bin/python3
# -*- coding: utf-8
"""Unit tests for code in modeline.py."""

from modeline import MODELINE_SUPPORTED_EDITORS, get_modeline, get_modelines
import unittest


class TestModelineGeneration(unittest.TestCase):
    """Unit test for get_modeline()"""
    test_settings = {
        'indentation_level': 4,
        'tab_width': 8,
        'expand_tab': True,
        'invalid_option': 10
    }

    def test_modelinegeneration(self):
        """Just checking that we do not throw at the moment."""
        for editor in MODELINE_SUPPORTED_EDITORS | {'invalid-editor'}:
            get_modeline(editor, self.test_settings)

    def test_multiplemodelinegeneration(self):
        """Just checking that we do not throw at the moment."""
        get_modelines(
            MODELINE_SUPPORTED_EDITORS | {'invalid-editor'},
            self.test_settings)

# vim: filetype=python tabstop=8 expandtab shiftwidth=4 softtabstop=4

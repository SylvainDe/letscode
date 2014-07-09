#!/usr/bin/python3
# -*- coding: utf-8
"""Unit tests for code in helper.py."""

from helper import subprocess_call_wrapper
import unittest


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

# vim: filetype=python tabstop=8 expandtab shiftwidth=4 softtabstop=4

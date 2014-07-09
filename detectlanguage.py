#!/usr/bin/python3
# -*- coding: utf-8
"""Detection of the languages once given a filename."""

from languages import LANGUAGE_NAMES, LANGUAGES
import os


def get_extensions_map():
    """Gets dictionnary mapping file extensions to related languages"""
    extensions = dict()
    for lang in LANGUAGES:
        for ext in lang.extensions:
            extensions.setdefault("." + ext.lower(), []).append(lang.name)
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

# vim: filetype=python tabstop=8 expandtab shiftwidth=4 softtabstop=4

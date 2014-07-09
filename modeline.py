#!/usr/bin/python3
# -*- coding: utf-8
"""Code to generate modelines for different editors and different settings."""


MODELINE_VIMLIKE_EDITORS = {
    'vim',
    'vi',
}

MODELINE_OPTIONS = {
    # http://vimdoc.sourceforge.net/htmldoc/usr_21.html#21.6
    'vim': {
        'start': ': set ',  # there will be a hack here for vimlike editors
        'end': ':',
        'link': ' ',
        'indentation_level': 'shiftwidth=',
        'tab_width': 'tabstop=',
        'textwidth': 'textwidth=',
        'expand_tab': ('noexpandtab', 'expandtab'),
    },
    # http://www.gnu.org/software/emacs/manual/html_node/emacs/File-Variables.html#File-Variables
    'emacs': {
        'start': 'Local variables:\n',
        'end': 'End:',
        'link': '\n',
        'indentation_level': 'c-basic-offset: ',
        'tab_width': 'tab-width: ',
        'textwidth': 'fill-column: ',
        'expand_tab': ('indent-tabs-mode: nil', 'indent-tabs-mode: t'),
    },
    # http://www.jedit.org/users-guide/buffer-local.html
    'jedit': {
        'start': ':',
        'end': '',
        'link': ':',
        'indentation_level': 'indentSize=',
        'tab_width': 'tabSize=',
        'textwidth': 'maxLineLen=',
        'expand_tab': ('noTabs=false', 'noTabs=true')
    },
    # http://docs.kde.org/stable/en/applications/kate/config-variables.html
    'kate': {
        'start': 'kate: ',
        'end': '',
        'link': '; ',
        'indentation_level': 'indent-width ',
        'tab_width': 'tab-width ',
        'textwidth': 'word-wrap-column ',
        'expand_tab': ('replace-tabs off', 'replace-tabs on')
    },
    # Pending :
    # Gedit : https://help.gnome.org/users/gedit/stable/gedit-plugins-modelines.html.en
    # Komodo : http://community.activestate.com/forum/komode-modeline-support-komodo
}

MODELINE_SUPPORTED_EDITORS = \
    set(MODELINE_OPTIONS.keys()) | MODELINE_VIMLIKE_EDITORS


def get_modeline(editor, settings):
    """Return modeline corresponding to the settings for an editor."""
    ret = ''
    ed_opt = MODELINE_OPTIONS.get(
        'vim' if editor in MODELINE_VIMLIKE_EDITORS else editor)
    if ed_opt is not None:
        link = ed_opt['link']
        for opt, val in settings.items():
            flag = ed_opt.get(opt)
            if flag is not None:
                ret += (flag[val] if isinstance(flag, tuple)
                        else flag+str(val)) + link
        if ret:
            ret = (editor if editor in MODELINE_VIMLIKE_EDITORS else '') + \
                ed_opt['start'] + \
                ret + ed_opt['end']
    return ret


def get_modelines(editors, settings):
    """Return modeline corresponding to the settings for different editors."""
    return '\n'.join(m for m in (get_modeline(e, settings) for e in editors) if m)

# vim: filetype=python tabstop=8 expandtab shiftwidth=4 softtabstop=4

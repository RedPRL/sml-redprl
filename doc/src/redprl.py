from pygments.lexer import RegexLexer, include, bygroups, using, \
     this, combined, ExtendedRegexLexer, default
from pygments.token import *

class RedPRLLexer(RegexLexer):
    """
    Lexer for `RedPRL <http://www.redprl.org/>`_ source code.
    """

    name = 'RedPRL'
    aliases = ['redprl']
    filenames = ['*.prl']

    exprs = ['ax', 'fcom', 'bool', 'tt', 'ff', 'if', 'nat', 'zero', 'succ',
             'nat-rec', 'int', 'negsucc', 'int-rec', 'void', 'S1', 'base',
             'loop', 'S1-rec', 'lam', 'record', 'tuple', 'path', 'line',
             'pushout', 'left', 'right', 'glue', 'pushout-rec', 'coeq', 'cecod',
             'cedom', 'coeq-rec', 'mem', 'ni', 'box', 'cap', 'V', 'VV', 'WU',
             'Vin', 'Vproj', 'U', 'abs', 'hcom', 'com', 'ghcom', 'gcom', 'coe',
             'lmax', 'omega']
    tacs = ['auto', 'auto-step', 'case', 'cut-lemma', 'elim', 'else', 'exact',
            'goal', 'hyp', 'id', 'lemma', 'let', 'claim', 'match', 'of',
            'print', 'trace', 'progress', 'query', 'reduce', 'refine', 'repeat',
            'rewrite', 'symmetry', 'then', 'unfold', 'use', 'with', 'without',
            'fail', 'inversion', 'concl', 'assumption', '\;']
    cmds = ['Print', 'Extract', 'Quit', 'Def', 'Tac', 'Thm']
    misc = ['at', 'by', 'in', 'true', 'type', 'synth', 'discrete', 'kan', 'pre',
            'dim', 'hyp', 'exp', 'lvl', 'tac', 'jdg', 'knd']
    types = ['bool', 'nat', 'int', 'void', 's1', 'fun', 'record', 'path',
             'line', 'pushout', 'coeq', 'eq', 'fcom', 'V', 'universe', 'hcom',
             'coe', 'subtype', 'universe']

    # earlier rules take precedence
    tokens = {
        'root': [
            (r'\s+', Whitespace),

            (r'//.*?$', Comment.Singleline),
            (r'/\*', Comment.Multiline, 'comment'),

            ('/[\w/]+|\\b'.join(types), Name.Builtin),
            ('|\\b'.join(exprs), Name.Builtin),
            ('\$|\*|!|@|=(?!>)|\+|->|~>|<~', Name.Builtin),

            ('|\\b'.join(tacs), Keyword),
            (';|`|=>|<=', Keyword),

            ('|\\b'.join(cmds), Keyword.Declaration),

            ('|\\b'.join(misc), Name.Builtin),

            ('\#', Name.Builtin),

            (r'\(|\)|\[|\]|\.|:|,|\{|\}|_', Punctuation),
            (r'\b\d+', Number),

            ('[A-Z][a-zA-Z0-9\'/-]*', Name.Function),
            ('[a-z][a-zA-Z0-9\'/-]*', Name.Variable),
            ('\?[a-zA-Z0-9\'/-]*', Name.Exception),
        ],

        'comment': [
            (r'[^*/]', Comment.Multiline),
            (r'/\*', Comment.Multiline, '#push'),
            (r'\*/', Comment.Multiline, '#pop'),
            (r'[*/]', Comment.Multiline)
        ],
    }

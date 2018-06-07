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

    exprs = ['ax', 'fcom', 'bool', 'tt', 'ff', 'if', 'nat-rec', 'nat', 'zero',
             'succ', 'int-rec', 'int', 'negsucc', 'void', 'S1-rec', 'S1',
             'base', 'loop', 'lam', 'record', 'tuple', 'path', 'line',
             'pushout-rec', 'pushout', 'left', 'right', 'glue', 'coeq-rec',
             'self', 'rec', 'coeq', 'cecod', 'cedom', 'mem', 'ni', 'box', 'cap',
             'V', 'Vin', 'Vproj', 'U', 'abs', 'hcom', 'com',
             'ghcom', 'gcom', 'ecom', 'coe', 'lmax', 'omega']
    tacs = ['auto', 'auto-step', 'case', 'cut-lemma', 'elim', 'else', 'exact',
            'goal', 'hyp', 'id', 'lemma', 'let', 'claim', 'match', 'of',
            'print', 'trace', 'progress', 'query', 'reduce', 'refine', 'repeat',
            'rewrite', 'symmetry', 'then', 'unfold', 'use', 'with', 'without',
            'fail', 'inversion', 'concl', 'assumption', '\;']
    cmds = ['data', 'print', 'extract', 'quit', 'define', 'tactic', 'theorem']
    misc = ['at', 'by', 'in', 'true', 'type', 'synth', 'discrete', 'kan', 'pre',
            'dim', 'hyp', 'exp', 'lvl', 'tac', 'jdg', 'knd']
    types = ['bool', 'nat', 'int', 'void', 's1', 'fun', 'record', 'path',
             'line', 'pushout', 'coeq', 'eq', 'fcom', 'V', 'universe', 'hcom',
             'coe', 'subtype', 'universe']

    def joiner(arr):
        return '|'.join(map(lambda str: '\\b' + str + '\\b', arr))

    # earlier rules take precedence
    tokens = {
        'root': [
            (r'\s+', Text),

            (r'//.*?$', Comment.Singleline),
            (r'/\*', Comment.Multiline, 'comment'),

            (joiner(map(lambda str: str + '/[\w/]+', types)), Name.Builtin),
            (joiner(exprs), Name.Builtin),
            (joiner(types), Name.Builtin),
            (r'\$|\*|!|@|=(?!>)|\+|->|~>|<~', Name.Builtin),

            (joiner(tacs), Keyword),
            (r';|`|=>|<=', Keyword),

            (joiner(cmds), Keyword.Declaration),

            (joiner(misc), Name.Builtin),

            (r'\#[a-zA-Z0-9\'/-]*', Name.Variable),
            (r'\%[a-zA-Z0-9\'/-]*', Name.Variable),

            (r'\(|\)|\[|\]|\.|:|,|\{|\}|_', Punctuation),
            (r'\b\d+', Number),

            # for typesetting rules:
            (r'^\|', Generic.Traceback),
            (r'>>', Name.Keyword),
            (r'<-', Name.Keyword),
            (r'/=', Name.Keyword),
            (r'<', Name.Keyword),
            (r'ext', Name.Keyword),
            (r'where', Name.Keyword),

            (r'\|', Punctuation),
            (r'[A-Z][a-zA-Z0-9\'/-]*', Name.Function),
            (r'[a-z][a-zA-Z0-9\'/-]*', Name.Variable),
            (r'\?[a-zA-Z0-9\'/-]*', Name.Exception),
            (r'-+$', Punctuation),
        ],

        'comment': [
            (r'[^*/]', Comment.Multiline),
            (r'/\*', Comment.Multiline, '#push'),
            (r'\*/', Comment.Multiline, '#pop'),
            (r'[*/]', Comment.Multiline)
        ],
    }

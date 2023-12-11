
import pprint
from base64 import b64decode

from pyparsing import *


def verifyLen(s, l, t):
    t = t[0]
    if t.len is not None:
        t1len = len(t[1])
        if t1len != t.len:
            raise ParseFatalException(s, l, "invalid data of length %d, expected %s" % (t1len, t.len))
    return t[1]


# define punctuation literals
LPAR, RPAR, LBRK, RBRK, LBRC, RBRC, VBAR = list(map(Suppress, "()[]{}|"))

decimal = Regex(r'-?0|-?[0-9]\d*').setParseAction(lambda t: ('Int', int(t[0])))
hexadecimal = ("#x" + OneOrMore(Word(hexnums))) \
    .setParseAction(lambda t: (['BitVec', ('Int', 4 * len(t[1]))], int("".join(t[1:]), 16)))
bytes = Word(printables)
raw = Group(decimal("len") + Suppress(":") + bytes).setParseAction(verifyLen)
token = Word(alphanums + "-./_:*+=")
base64_ = Group(Optional(decimal | hexadecimal, default=None)("len") + VBAR
                + OneOrMore(Word(alphanums + "+/=")).setParseAction(lambda t: b64decode("".join(t)))
                + VBAR).setParseAction(verifyLen)

qString = Group(Optional(decimal, default=None)("len") +
                dblQuotedString.setParseAction(removeQuotes)).setParseAction(verifyLen)
# simpleString = base64_ | raw | decimal | token | hexadecimal | qString

# extended definitions

real = Regex(r"[+-]?\d+\.\d*([eE][+-]?\d+)?").setParseAction(lambda tokens: float(tokens[0]))
token = Word(alphanums + "-./_:*+=!<>").setParseAction(lambda t: ('Bool', 1) if t[0] == 'true' else \
    ('Bool', 0) if t[0] == 'false' else t)

simpleString = real | base64_ | raw | decimal | token | hexadecimal | qString

display = LBRK + simpleString + RBRK
string_ = Optional(display) + simpleString

sexp = Forward()
sexpList = Group(LPAR + ZeroOrMore(sexp) + RPAR)
sexp <<= (string_ | sexpList)

######### Test data ###########
# test001 = """(#03#)"""
# test00 = """(snicker "abc" (#03# |YWJj|))"""
test01 = """(certificate
 (issuer
  (name
   (public-key
    rsa-with-md5
    (e 15 |NFGq/E3wh9f4rJIQVXhS|)
    (n |d738/4ghP9rFZ0gAIYZ5q9y6iskDJwASi5rEQpEQq8ZyMZeIZzIAR2I5iGE=|))
   aid-committee))
 (subject
  (ref
   (public-key
    rsa-with-md5
    (e |NFGq/E3wh9f4rJIQVXhS|)
    (n |d738/4ghP9rFZ0gAIYZ5q9y6iskDJwASi5rEQpEQq8ZyMZeIZzIAR2I5iGE=|))
   tom
   mother))
 (not-before "1997-01-01_09:00:00")
 (not-after "1998-01-01_09:00:00")
 (tag
  (spend (account "12345678") (* numeric range "1" "1000"))))
"""
test02 = """(lambda (x) (* x x))"""
test03 = """(def length
   (lambda (x)
      (cond
         ((not x) 0)
         (   t   (+ 1 (length (cdr x))))
      )
   )
)
"""
# test04 = """(2:XX "abc" (#03# |YWJj|))"""
test05 = """(if (is (window_name) "XMMS") (set_workspace 2))"""
test06 = """(if
  (and
    (is (application_name) "Firefox")
    (or
      (contains (window_name) "Enter name of file to save to")
      (contains (window_name) "Save As")
      (contains (window_name) "Save Image")
      ()
    )
  )
  (geometry "+140+122")
)
"""
test07 = """(defun factorial (x)
   (if (zerop x) 1
       (* x (factorial (- x 1)))))
       """
# test51 = """(2:XX "abc" (#30# |YWJj|))"""
# test51error = """(3:XX "abc" (#30# |YWJj|))"""

test52 = """ 
    (and 
      (or (> uid 1000) 
          (!= gid 20) 
      ) 
      (> quota 5.0e+03) 
    ) 
    """
test53 = """
((set-logic BV)

(define-fun hd01 ((x (BitVec 32))) (BitVec 32) (bvand x (bvsub x #x00000001)))

(synth-fun f ((x (BitVec 32))) (BitVec 32)
    ((Start (BitVec 32) ((bvand Start Start)
                         (bvsub Start Start)
                         x
                         #x00000001))))

(declare-var x (BitVec 32))
(constraint (= (hd01 x) (f x)))
(check-synth)
)
"""

test54 = """
(hex false)
"""


# # Run tests

def main():
    t = None
    alltests = [  # test001,
        # test00,
        test01,
        test02,
        test03,
        # test04,
        test05,
        test06,
        test07,
        # test51,
        test52,
        test53,
        test54]

    for t in alltests:
        print(('-' * 50))
        print(t)
        try:
            sexpr = sexp.parseString(t, parseAll=True)
            pprint.pprint(sexpr.asList())
        except ParseFatalException as pfe:
            print("Error:", pfe.msg)
            print(pfe.markInputline('^'))
        print()


if __name__ == '__main__':
    main()

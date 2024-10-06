from net import *
from equal import *

unchecked Check: P -> P -> Bits -> (P, P, u24)
(Check P/Era P/None path) = (P/Era, P/None, 1)
(Check (P/Lam var bod) (P/Arrow A B) path) =
  let res = (APP (P/Lam var bod) (P/Ann $x A λ$A(*) (Bits/O path)))
  let (res, B, chk) = (Check res B (Bits/I path))
  ((LAM λ$x res), (P/Arrow $A B), chk)
(Check (P/Ann value type1 return_type1 path1) type2 path2) =
  let (type1, type2, eql) = (P/Equal type1 type2 path2)
  let * = (return_type1 type1)
  (value, type2, eql)
(Check (P/Var (Var/Node value)) type path) = (Check value type path)
(Check value (P/Var (Var/Node type)) path) = (Check value type path)
(Check a b path) = (a, b, 0)

from net import *
from equal import *
from affine import *

Check: P -> P -> Bits -> (P, P, u24)
(Check P/Era P/None path) = (P/Era, P/None, 1)
(Check (P/Lam var bod) (P/Arrow A B) path) =
  let (A_ret, A_f) = PChannel
  let (xp, xn) = Wire
  let (opath, ipath) = (Bits/split path)
  let res = (APP (P/Lam var bod) (P/Ann xp A A_f opath))
  let (res, B, chk) = (Check res B ipath)
  ((P/Lam xn res), (P/Arrow A_ret B), chk)
(Check (P/Ann value type1 return_type1 path1) type2 path2) =
  let (type1, type2, eql) = (P/Equal type1 type2 path2)
  let * = (return_type1 type1)
  (value, type2, eql)
(Check (P/Var (Var/Node value)) type path) = (Check value type path)
(Check value (P/Var (Var/Node type)) path) = (Check value type path)
(Check a b path) = (a, b, 0)

# from net import *

Check: P -> P -> (P, P, u24)
(Check P/Era P/None) = (P/Era, P/None, 1)
(Check (P/Lam var bod) (P/Arrow A B)) =
  let res = (APP (P/Lam var bod) (P/Ann P/Era A))
  let (res, B, chk) = (Check res B)
  let * = (Erase B)
  (P/Era, P/Era, chk)
(Check (P/Ann value type1) type2) =
  let (type1, type2, eql) = (Equal type1 type2)
  let * = (Erase type1)
  (value, type2, eql)
(Check (P/Var (Var/Node x)) type) = (Check x type)
(Check a b) = (a, b, 0)

Equal: P -> P -> (P, P, u24)
(Equal P/None P/None) = (P/None, P/None, 1)
(Equal a b) = (a, b, 0)



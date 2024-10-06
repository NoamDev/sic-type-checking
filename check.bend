# from net import *

unchecked Check: P -> P -> (P, P, u24)
(Check P/Era P/None) = (P/Era, P/None, 1)
(Check (P/Lam var bod) (P/Arrow A B)) =
  let res = (APP (P/Lam var bod) (P/Ann $x A λ$A(*)))
  let (res, B, chk) = (Check res B)
  ((LAM λ$x res), (P/Arrow $A B), chk)
(Check (P/Ann value type1 return_type1) type2) =
  let (type1, type2, eql) = (Equal type1 type2)
  let * = (return_type1 type1)
  (value, type2, eql)
(Check (P/Var (Var/Node value)) type) = (Check value type)
(Check value (P/Var (Var/Node type))) = (Check value type)
(Check a b) = (a, b, 0)

Equal: P -> P -> (P, P, u24)
(Equal (P/Var (Var/Node a)) b) = (Equal a b)
(Equal a (P/Var (Var/Node b))) = (Equal a b)
(Equal P/None P/None) = (P/None, P/None, 1)
(Equal (P/Arrow A0 B0) (P/Arrow A1 B1)) =
  let (A0, B0, eql0) = (Equal A0 B0)
  let (A1, B1, eql1) = (Equal A1 B1)
  ((P/Arrow A0 B0), (P/Arrow A1 B1), (& eql0 eql1))
(Equal a b) = (a, b, 0)

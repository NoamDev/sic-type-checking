from net import *
from equal import *
from affine import *

Check: P -> P -> Bits -> (P, u24)
(Check P/Era P/None path) = (P/Era, 1)
(Check (P/Lam var bod) (P/Arrow A B) path) =
  let (xp, xn) = Wire
  let (opath, ipath) = (Bits/split path)
  let (oopath, iopath) = (Bits/split opath)
  let (A, is_aff_type) = (IsAff A)
  let res = (APP (P/Lam var bod) (P/Ann (P/Sym xp iopath P/History/E is_aff_type) A oopath))
  let (res, chk) = (Check res B ipath)
  ((P/Lam xn res), chk)
(Check (P/Lam var bod) (P/Forall from to_func) path) =
  let (xp, xn) = Wire
  let (opath, ipath) = (Bits/split path)
  let (oopath, iopath) = (Bits/split opath)
  let (from, is_aff_type) = (IsAff from)
  let (post_var, to_type) = (to_func (P/Ann (P/Sym xp iopath P/History/E is_aff_type) from oopath))
  let res = (APP (P/Lam var bod) post_var)
  let (res, chk) = (Check res to_type ipath)
  ((P/Lam xn res), chk)

(Check (P/Ann value type1 path1) type2 path2) =
  let (type1, type2, eql) = (RefinementOf type1 type2 path2)
  let * = (Erase type1)
  let * = (Erase type2)
  (value, eql)
(Check (P/Var (Var/Node value)) type path) = (Check value type path)
(Check value (P/Var (Var/Node type)) path) = (Check value type path)
(Check a b path) = 
  let * = (Erase b)
  (a, 0)

# PseudoEqual: N -> Bits -> u24 -> N
# (PseudoEqual (N/Var f) path aff) =
#   let (path0, path1) = (Bits/duplicate path)
#   let idx = (Bits/to_u24 path0)
#   let arg = (Equal/fold f idx)
#   match arg {
#     FoldArg/Node: (PseudoEqual arg.node path1 aff)
#     FoldArg/Data: arg.var
#   }
# (PseudoEqual N/Era path aff) = N/Era
# (PseudoEqual N/Error path aff) = N/Error
# (PseudoEqual (N/App arg res) path aff) = (N/App arg res)
# (PseudoEqual (N/Dup a b) path aff) =
#   let (path0, path1) = 
#   (
#     if aff {
#       Bits/duplicate
#     } else {
#       Bits/split
#     }
#     path
#   )
#   let a = (PseudoEqual a path0 aff)
#   let b = (PseudoEqual b path1 aff)
#   (N/Dup a b)

IsAff: P -> (P, u24)
(IsAff (P/Aff a)) = ((P/Aff a), 1)
(IsAff (P/Var (Var/Node a))) = (IsAff a)
(IsAff a) = (a, 0)

RefinementOf: P -> P -> Bits -> (P, P, u24)
(RefinementOf a b path) = (RefinementOfInternal (NormalAff a) (NormalAff b) path)

RefinementOfInternal: P -> P -> Bits -> (P, P, u24)
(RefinementOfInternal (P/Aff a) (P/Aff b) path) = (P/Equal (P/Aff a) (P/Aff b) path)
(RefinementOfInternal (P/Aff a) b path) =
  let (a, b, eql) = (P/Equal a b path)
  ((P/Aff a), b, eql)
(RefinementOfInternal a b path) = (P/Equal a b path)

NormalAff: P -> P
(NormalAff (P/Var (Var/Node a))) = (NormalAff a)
(NormalAff (P/Aff (P/Var (Var/Node a)))) = (NormalAff (P/Aff a))
(NormalAff (P/Aff (P/Aff a))) = (NormalAff (P/Aff (NormalAff a)))
(NormalAff a) = a

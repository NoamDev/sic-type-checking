# from net import *

unchecked Check: P -> P -> (P, P, u24)
(Check P/Era P/None) = (P/Era, P/None, 1)
(Check (P/Lam var bod) (P/Arrow A B)) =
  let res = (APP (P/Lam var bod) (P/Ann $x A λ$A(*)))
  let (res, B, chk) = (Check res B)
  ((LAM λ$x res), (P/Arrow $A B), chk)
(Check (P/Ann value type1 return_type1) type2) =
  let (type1, type2, eql) = (P/Equal type1 type2)
  let * = (return_type1 type1)
  (value, type2, eql)
(Check (P/Var (Var/Node value)) type) = (Check value type)
(Check value (P/Var (Var/Node type))) = (Check value type)
(Check a b) = (a, b, 0)

(N/EqualFoldArgs (FoldArg/Node a) (FoldArg/Node b) path) =
  (N/Equal a b path)

(N/EqualFoldArgs (FoldArg/Node a) (FoldArg/Data data var) path) =
  (a, var, 0)

(N/EqualFoldArgs (FoldArg/Data data var) (FoldArg/Node b) path) =
  (var, b, 0)

(N/EqualFoldArgs (FoldArg/Data data0 var0) (FoldArg/Data data1 var1) path) =
  (var0, var1, (== data0 data1))

N/Equal: N -> N -> Bits -> (N, N, u24)
(N/Equal N/Error b path) = (N/Error, b, 0)
(N/Equal a N/Error path) = (a, N/Error, 0)

(N/Equal (N/Var f0) (N/Var f1) path) =
  let idx = (Bits/to_u24 path)
  let arg0 = (Net/fold f0 idx)
  let arg1 = (Net/fold f1 idx)
  (N/EqualFoldArgs arg0 arg1 path)

(N/Equal (N/Var f) b path) =
  let idx = (Bits/to_u24 path)
  let arg = (Net/fold f idx)
  (
    match arg {
      FoldArg/Node: λb (N/Equal arg.node b path)
      FoldArg/Data: λb (arg.var, b, 0)
    }
    b
  )

(N/Equal a (N/Var f) path) =
  let idx = (Bits/to_u24 path)
  let arg = (Net/fold f idx)
  (
    match arg {
      FoldArg/Node: λa (N/Equal a arg.node path)
      FoldArg/Data: λa (a, arg.var, 0)
    }
    a
  )

(N/Equal (N/Dup a0 a1) (N/Dup b0 b1) path) =
  let (a0, b0, eql0) = (N/Equal a0 b0 (Bits/O path))
  let (a1, b1, eql1) = (N/Equal a1 b1 (Bits/I path))
  ((N/Dup a0 a1), (N/Dup b0 b1), (& eql0 eql1))

(N/Equal (N/Dup a0 a1) b path) =
  let (b0, b1) = (SUP b)
  (N/Equal (N/Dup a0 a1) (N/Dup b0 b1) path)

(N/Equal a (N/Dup b0 b1) path) =
  let (a0, a1) = (SUP a)
  (N/Equal (N/Dup a0 a1) (N/Dup b0 b1) path)

(N/Equal N/Era N/Era path) = (N/Era, N/Era, 1)
(N/Equal N/Era b path) = (N/Era, b, 0)
(N/Equal a N/Era path) = (a, N/Era, 0)

(N/Equal (N/App arg0 res0) (N/App arg1 res1) path) =
  let (arg0, arg1, eql_arg) = (P/Equal arg0 arg1 (Bits/O path))
  let (res0, res1, eql_res) = (N/Equal res0 res1 (Bits/I path))
  ((N/App arg0 res0), (N/App arg1 res1), (& eql_arg eql_res))

P/Equal: P -> P -> (P, P, u24)
(P/Equal (P/Var (Var/Node a)) b) = (P/Equal a b)
(P/Equal a (P/Var (Var/Node b))) = (P/Equal a b)
(P/Equal (P/Var (Var/Fold data0 f0)) (P/Var (Var/Fold data1 f1))) =
  let (w0p, w0n) = Wire
  let (w1p, w1n) = Wire
  let eql = (== data0 data1)
  let * = (f0 (FoldArg/Data data1 w0n))
  let * = (f1 (FoldArg/Data data0 w1n))
  (w0p, w1p, eql)
(P/Equal (P/Var (Var/Fold data f)) b) =
  let (wp, wn) = Wire
  let * = (f (FoldArg/Data 0 wn))
  (wp, b, 0)
(P/Equal a (P/Var (Var/Fold data f))) =
  let (wp, wn) = Wire
  let * = (f (FoldArg/Data 0 wn))
  (a, wp, 0)

(P/Equal P/Error b) = (P/Error,b, 0)
(P/Equal a P/Error) = (a, P/Error, 0)

(P/Equal (P/Sup a0 a1) (P/Sup b0 b1)) =
  let (a0, b0, eql0) = (P/Equal a0 b0)
  let (a1, b1, eql1) = (P/Equal a1 b1)
  ((P/Sup a0 a1), (P/Sup b0 b1), (& eql0 eql1))

(P/Equal (P/Sup a0 a1) b) =
  let (b0, b1) = (DUP b)
  (P/Equal (P/Sup a0 a1) (P/Sup b0 b1))

(P/Equal a (P/Sup b0 b1)) =
  let (a0, a1) = (DUP a)
  (P/Equal (P/Sup a0 a1) (P/Sup b0 b1))


(P/Equal P/None P/None) = (P/None, P/None, 1)
(P/Equal P/None b) = (P/None, b, 0)
(P/Equal P/Era P/Era) = (P/Era, P/Era, 1)
(P/Equal P/Era b) = (P/Era, b, 0)
(P/Equal a P/Era) = (a, P/Era, 0)


(P/Equal (P/Lam var0 bod0) (P/Lam var1 bod1)) =
  let (var0, var1, eql_var) = (N/Equal var0 var1)
  let (bod0, bod1, eql_bod) = (P/Equal bod0 bod1)
  ((P/Lam var0 bod0), (P/Lam var1 bod1), (& eql_var eql_bod))

(P/Equal (P/Arrow A0 B0) (P/Arrow A1 B1)) =
  let (A0, B0, eql0) = (P/Equal A0 B0)
  let (A1, B1, eql1) = (P/Equal A1 B1)
  ((P/Arrow A0 B0), (P/Arrow A1 B1), (& eql0 eql1))
  
# (P/Equal a b) = (a, b, 0)

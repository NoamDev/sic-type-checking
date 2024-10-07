from net import *
from utils import *

N/EqualFoldArgs: (FoldArg u24) -> (FoldArg u24) -> Bits -> (N, N, u24)
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
  let (path1, path2) = (Bits/duplicate path)
  let (idx1, idx2) = (u24/duplicate (Bits/to_u24 path1))
  let arg0 = (Equal/fold f0 idx1)
  let arg1 = (Equal/fold f1 idx2)
  (N/EqualFoldArgs arg0 arg1 path2)

(N/Equal (N/Var f) b path) =
  let (path1, path2) = (Bits/duplicate path)
  let idx = (Bits/to_u24 path1)
  let arg = (Equal/fold f idx)
  (
    match arg {
      FoldArg/Node: λb (N/Equal arg.node b path2)
      FoldArg/Data: λb (arg.var, b, 0)
    }
    b
  )

(N/Equal a (N/Var f) path) =
  let (path1, path2) = (Bits/duplicate path)
  let idx = (Bits/to_u24 path1)
  let arg = (Equal/fold f idx)
  (
    match arg {
      FoldArg/Node: λa (N/Equal a arg.node path2)
      FoldArg/Data: λa (a, arg.var, 0)
    }
    a
  )

(N/Equal (N/Dup a0 a1) (N/Dup b0 b1) path) =
  let (opath, ipath) = (Bits/split path)
  let (a0, b0, eql0) = (N/Equal a0 b0 opath)
  let (a1, b1, eql1) = (N/Equal a1 b1 ipath)
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
  let (opath, ipath) = (Bits/split path)
  let (arg0, arg1, eql_arg) = (P/Equal arg0 arg1 opath)
  let (res0, res1, eql_res) = (N/Equal res0 res1 ipath)
  ((N/App arg0 res0), (N/App arg1 res1), (& eql_arg eql_res))

P/Equal: P -> P -> Bits -> (P, P, u24)
(P/Equal (P/Var (Var/Node a)) b path) = (P/Equal a b path)
(P/Equal a (P/Var (Var/Node b)) path) = (P/Equal a b path)
(P/Equal (P/Var (Var/Fold (Fold/Equal data0 f0))) (P/Var (Var/Fold (Fold/Equal data1 f1))) path) =
  let (w0p, w0n) = Wire
  let (w1p, w1n) = Wire
  let (data0_0, data0_1) = (u24/duplicate data0)
  let (data1_0, data1_1) = (u24/duplicate data1)
  let eql = (== data0_0 data1_0)
  let * = (f0 (FoldArg/Data data1_1 w0n))
  let * = (f1 (FoldArg/Data data0_1 w1n))
  (w0p, w1p, eql)

(P/Equal (P/Var (Var/Fold (Fold/Equal data f))) (P/Sup b0 b1) path) =
  let (a0, a1) = (DUP (P/Var (Var/Fold (Fold/Equal data f))))
  (P/Equal (P/Sup a0 a1) (P/Sup b0 b1) path)

(P/Equal (P/Sup a0 a1) (P/Var (Var/Fold (Fold/Equal data f))) path) =
  let (b0, b1) = (DUP (P/Var (Var/Fold (Fold/Equal data f))))
  (P/Equal (P/Sup a0 a1) (P/Sup b0 b1) path)

(P/Equal (P/Var (Var/Fold (Fold/Equal data f))) (P/Lam var1 bod1) path) =
  let (var0p, var0n) = Wire
  let bod0 = (APP (P/Var (Var/Fold (Fold/Equal data f))) var0p)
  (P/Equal (P/Lam var0n bod0) (P/Lam var1 bod1) path)

(P/Equal (P/Lam var0 bod0) (P/Var (Var/Fold (Fold/Equal data f))) path) =
  let (var1p, var1n) = Wire
  let bod1 = (APP (P/Var (Var/Fold (Fold/Equal data f))) var1p)
  (P/Equal (P/Lam var0 bod0) (P/Lam var1n bod1) path)

(P/Equal (P/Var (Var/Fold (Fold/Equal data f))) b path) =
  let (wp, wn) = Wire
  let * = (f (FoldArg/Data 0 wn))
  (wp, b, 0)
(P/Equal a (P/Var (Var/Fold (Fold/Equal data f))) path) =
  let (wp, wn) = Wire
  let * = (f (FoldArg/Data 0 wn))
  (a, wp, 0)

(P/Equal (P/Var (Var/Fold other)) b path) =
  let * = (Fold other N/Error)
  (P/Error, b, 0)

(P/Equal a (P/Var (Var/Fold other)) path) =
  let * = (Fold other N/Error)
  (a, P/Error, 0)


(P/Equal P/Error b path) = (P/Error,b, 0)
(P/Equal a P/Error path) = (a, P/Error, 0)

(P/Equal (P/Sup a0 a1) (P/Sup b0 b1) path) =
  let (opath, ipath) = (Bits/split path)
  let (a0, b0, eql0) = (P/Equal a0 b0 opath)
  let (a1, b1, eql1) = (P/Equal a1 b1 ipath)
  ((P/Sup a0 a1), (P/Sup b0 b1), (& eql0 eql1))

(P/Equal (P/Sup a0 a1) b path) =
  let (b0, b1) = (DUP b)
  (P/Equal (P/Sup a0 a1) (P/Sup b0 b1) path)

(P/Equal a (P/Sup b0 b1) path) =
  let (a0, a1) = (DUP a)
  (P/Equal (P/Sup a0 a1) (P/Sup b0 b1) path)

(P/Equal P/None P/None path) = (P/None, P/None, 1)
(P/Equal P/None b path) = (P/None, b, 0)
(P/Equal P/Era P/Era path) = (P/Era, P/Era, 1)
(P/Equal P/Era b path) = (P/Era, b, 0)

(P/Equal (P/Lam var0 bod0) (P/Lam var1 bod1) path) =
  let (opath, ipath) = (Bits/split path)
  let (var0, var1, eql_var) = (N/Equal var0 var1 opath)
  let (bod0, bod1, eql_bod) = (P/Equal bod0 bod1 ipath)
  ((P/Lam var0 bod0), (P/Lam var1 bod1), (& eql_var eql_bod))

(P/Equal (P/Lam var bod) b path) = ((P/Lam var bod), b, 0)

(P/Equal (P/Arrow A0 B0) (P/Arrow A1 B1) path) =
  let (opath, ipath) = (Bits/split path)
  let (A0, B0, eql0) = (P/Equal A0 B0 opath)
  let (A1, B1, eql1) = (P/Equal A1 B1 ipath)
  ((P/Arrow A0 B0), (P/Arrow A1 B1), (& eql0 eql1))

(P/Equal (P/Arrow A B) b path) = ((P/Arrow A B), b, 0)

(P/Equal (P/Ann value0 type0 return_type0 ann_path0) (P/Ann value1 type1 return_type1 ann_path1) path) =
  let (value0, value1, eql) = (P/Equal value0 value1 path)
  ((P/Ann value0 type0 return_type0 ann_path0), (P/Ann value1 type1 return_type1 ann_path1), eql)
(P/Equal (P/Ann value0 type0 return_type0 ann_path) b path) =
  ((P/Ann value0 type0 return_type0 ann_path), b, 0)

unchecked Equal/fold: (Var -> None) -> u24 -> (FoldArg u24)
(Equal/fold var_fun data) =
  let * = (var_fun (Var/Fold (Fold/Equal data λ$arg(*))))
  $arg

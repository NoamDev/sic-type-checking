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
(N/Equal (N/Sym wrapped0 id0 history0 aff0) (N/Sym wrapped1 id1 history1 aff1) path) =
  let id_eql = (Bits/equal id0 id1)
  let history_eql = (N/History/Equal history0 history1)
  ((N/Sym wrapped0 id0 history0 aff0), (N/Sym wrapped1 id1 history1 aff1), (& id_eql history_eql))
(N/Equal a (N/Sym wrapped id history aff) path) =
  (a, (N/Sym wrapped id history aff), 0)
(N/Equal (N/Sym wrapped id history aff) b path) =
  ((N/Sym wrapped id history aff), b, 0)
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
(P/Equal P/Type P/Type path) = (P/Type, P/Type, 1)
(P/Equal P/Type b path) = (P/Type, b, 0)
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

(P/Equal (P/Ann value0 type0 ann_path0 ann_chk0) (P/Ann value1 type1 ann_path1 ann_chk1) path) =
  let (value0, value1, eql) = (P/Equal value0 value1 path)
  ((P/Ann value0 type0 ann_path0 ann_chk0), (P/Ann value1 type1 ann_path1 ann_chk1), eql)
(P/Equal (P/Ann value0 type0 ann_path ann_chk) b path) =
  ((P/Ann value0 type0 ann_path ann_chk), b, 0)

(P/Equal (P/Aff type0) (P/Aff type1) path) =
  let (type0, type1, eql) = (P/Equal type0 type1 path)
  ((P/Aff type0), (P/Aff type1), eql)

(P/Equal (P/Aff type0) b path) =
  ((P/Aff type0), b, 0)

(P/Equal (P/Forall from0 to_func0) (P/Forall from1 to_func1) path) =
  let (opath, ipath) = (Bits/split path)
  let (oopath, iopath) = (Bits/split opath)
  let (oipath, iipath) = (Bits/split ipath)
  let (from0, from1, from_eql) = (P/Equal from0 from1 oopath)
  let (x0p, x0n) = Wire
  let (x1p, x1n) = Wire
  let (pre_var0, pre_var1, pre_var_eql) = (N/Equal x0n x1n iopath)
  let (post_var0, to_type0) = (to_func0 x0p)
  let (post_var1, to_type1) = (to_func1 x1p)
  let (post_var0, post_var1, post_var_eql) = (P/Equal post_var0 post_var1 oipath)
  let (to_type0, to_type1, to_type_eql) = (P/Equal to_type0 to_type1 iipath)
  (
    (P/Forall from0 λx0
      let * = (Interact x0 pre_var0)
      (post_var0, to_type0)
    ),
    (P/Forall from1 λx1
      let * = (Interact x1 pre_var1)
      (post_var1, to_type1)
    ),
    (& (& from_eql pre_var_eql) (& post_var_eql to_type_eql))
  ) 
(P/Equal (P/Forall from to_func) b path) =
  ((P/Forall from to_func), b, 0)
(P/Equal (P/Sym wrapped0 id0 history0 aff0) (P/Sym wrapped1 id1 history1 aff1) path) =
  let id_eql = (Bits/equal id0 id1)
  let history_eql = (P/History/Equal history0 history1)
  ((P/Sym wrapped0 id0 history0 aff0), (P/Sym wrapped1 id1 history1 aff1), (& id_eql history_eql))
(P/Equal (P/Sym wrapped0 id0 history0 aff0) b path) =
  ((P/Sym wrapped0 id0 history0 aff0), b, 0)
(P/Equal (P/Hole f) b path) = ((P/Hole f), b, 0)
(P/Equal a (P/Hole f) path) = (a, (P/Hole f), 0)

unchecked Equal/fold: (Var -> None) -> u24 -> (FoldArg u24)
(Equal/fold var_fun data) =
  let * = (var_fun (Var/Fold (Fold/Equal data λ$arg(*))))
  $arg

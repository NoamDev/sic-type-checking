from utils import *
from dsl import *
# from check import *

type P:
  Era
  Lam {var: N, bod: P}
  Sup {fst: P, snd: P}
  Var {v: Var}
  Ann {value: P, type: P, return_type: P -> None, path: Bits}
  None
  Arrow {from: P, to: P}
  Error

type N:
  Era
  App {arg: P, res: N}
  Dup {fst: N, snd: N}
  Var {f: Var -> None}
  Error

type Var:
  Node {node: P}
  Fold {fold: Fold}

type Fold:
  Show {data: String, f: FoldArg(String) -> None }
  Equal {data: u24, f: FoldArg(u24) -> None}
  Affine {data: u24, f: FoldArg(u24) -> None}

type FoldArg(T):
  Node {node: N}
  Data {data: T, var: N}

unchecked Wire: (P, N)
(Wire) = ((P/Var $a), (N/Var λ$a *))

Interact: P -> N -> None
(Interact (P/Var (Var/Node a)) b) = 
  let * = (Interact a b)
  *
(Interact a (N/Var b)) = 
  let * = (b (Var/Node a))
  *
(Interact (P/Var (Var/Fold f)) b) = (Fold f b)
(Interact a (N/Dup fst snd)) = (Duplicate a fst snd)
(Interact a (N/App arg res)) = (Apply a arg res)
(Interact a N/Era) = (Erase a)
(Interact a N/Error) = (Error a)

Duplicate: P -> N -> N -> None
(Duplicate P/Era fst snd) =
  let * = (Interact P/Era fst)
  let * = (Interact P/Era snd)
  *
(Duplicate P/None fst snd) =
  let * = (Interact P/None fst)
  let * = (Interact P/None snd)
  *
(Duplicate P/Error fst snd) =
  let * = (Interact P/Error fst)
  let * = (Interact P/Error snd)
  *
(Duplicate (P/Sup a0 a1) b0 b1) =
  let * = (Interact a0 b0)
  let * = (Interact a1 b1)
  *
(Duplicate (P/Lam var bod) f0 f1) =
  let (var0p, var0n) = Wire
  let (var1p, var1n) = Wire
  let (bod0, bod1) = (DUP bod)
  let * = (Interact (P/Sup var0p var1p) var)
  let * = (Interact (P/Lam var0n bod0) f0)
  let * = (Interact (P/Lam var1n bod1) f1)
  *
(Duplicate (P/Ann value type return_type path) fst snd) =
  let (value0, value1) = (DUP value)
  let (type0, type1) = (DUP type)
  let (type0_ret, type0_f) = PChannel
  let (type1_ret, type1_f) = PChannel
  let (opath, ipath) = (Bits/split path)
  let * = (Interact (P/Ann value0 type0 type0_f opath) fst)
  let * = (Interact (P/Ann value1 type1 type1_f ipath) snd)
  let * = (return_type (P/Sup type0_ret type1_ret))
  *
(Duplicate (P/Arrow A B) fst snd) =
  let (A0, A1) = (DUP A)
  let (B0, B1) = (DUP B)
  let * = (Interact (P/Arrow A0 B0) fst)
  let * = (Interact (P/Arrow A1 B1) snd)
  *
(Duplicate (P/Var v) fst snd) =
  let * = (Interact (P/Var v) (N/Dup fst snd))
  *

Apply: P -> P -> N -> None
(Apply P/Era arg res) =
  let * = (Erase arg)
  let * = (Interact P/Era res)
  *
(Apply P/None arg res) =
  let * = (Error arg)
  let * = (Interact P/Error res)
  *
(Apply P/Error arg res) =
  let * = (Error arg)
  let * = (Interact P/Error res)
  *
(Apply (P/Lam var bod) arg res) =
  let * = (Interact arg var)
  let * = (Interact bod res)
  *
(Apply (P/Sup f0 f1) arg res) =
  let (res0p, res0n) = Wire
  let (res1p, res1n) = Wire
  let (arg0, arg1) = (DUP arg)
  let * = (Interact f0 (N/App arg0 res0n))
  let * = (Interact f1 (N/App arg1 res1n))
  let * = (Interact (P/Sup res0p res1p) res)
  *
(Apply (P/Var v) arg res) =
  let * = (Interact (P/Var v) (N/App arg res))
  *
(Apply (P/Ann value (P/Arrow A B) return_type path) arg res) =
  let (opath, ipath) = (Bits/split path)
  let (arg, A, chk) = (arg, A, 0)#(Check arg A opath)
  (
    if chk {
      λvalueλAλBλreturn_typeλargλres
      let (B_ret, B_f) = PChannel
      let * = (return_type (P/Arrow A B_ret))
      let * = (Interact (P/Ann (APP value arg) B B_f ipath) res)
      *
    } else {
      λvalueλAλBλreturn_typeλargλres
      let * = (Error value)
      let * = (return_type (P/Arrow A B))
      let * = (Error arg)
      let * = (Interact P/Error res)
      *
    }
    value A B return_type arg res
  )

(Apply (P/Ann value type return_type path) arg res) =
  let * = (Error value)
  let * = (return_type type)
  let * = (Error arg)
  let * = (Interact P/Error res)
  *
(Apply (P/Arrow A B) arg res) =
  let * = (Error A)
  let * = (Error B)
  let * = (Error arg)
  let * = (Interact P/Error res)
  *

Erase: P -> None
(Erase P/Era) = *
(Erase P/None) = *
(Erase P/Error) = *
(Erase (P/Lam arg res)) =
  let * = (Erase arg)
  let * = (Interact P/Era res)
  *
(Erase (P/Sup fst snd)) =
  let * = (Erase fst)
  let * = (Erase snd)
  *
(Erase (P/Var v)) =
  let * = (Interact (P/Var v) N/Era)
  *
(Erase (P/Ann value type return_type path)) =
  let * = (Erase value)
  let * = (return_type type)
  *
(Erase (P/Arrow A B)) =
  let * = (Erase A)
  let * = (Erase B)
  *

Error: P -> None
(Error P/Era) = *
(Error P/None) = *
(Error P/Error) = *
(Error (P/Sup fst snd)) =
  let * = (Error fst)
  let * = (Error snd)
  *
(Error (P/Ann value type return_type path)) =
  let * = (Error value)
  let * = (return_type type)
  *
(Error (P/Lam var bod)) =
  let * = (Interact P/Error var)
  let * = (Error bod)  
  *
(Error (P/Arrow A B)) =
  let * = (Error A)
  let * = (Error B)
  *
(Error (P/Var v)) =
  let * = (Interact (P/Var v) N/Error)
  *

(Fold (Fold/Show data f) b) =
  let * = (f (FoldArg/Node b))
  *

(Fold (Fold/Equal data f) b) =
  let * = (f (FoldArg/Node b))
  *

(Fold (Fold/Affine data f) b) =
  let * = (f (FoldArg/Node b))
  *
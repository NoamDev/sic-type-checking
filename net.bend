from utils import *
from dsl import *
from check import *

type P:
  Era
  Lam {var: N, bod: P}
  Sup {fst: P, snd: P}
  Var {v: Var}
  Ann {value: P, type: P, path: Bits}
  None
  Arrow {from: P, to: P}
  Aff {type: P}
  Error
  Forall {from: P, to_fun: P -> (P, P)}
  Sym {wrapped: P, id: Bits, history: P/History}  

type N:
  Era
  App {arg: P, res: N}
  Dup {fst: N, snd: N}
  Var {f: Var -> None}
  Error
  Sym {wrapped: N, id: Bits, history: N/History}  


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

type P/History:
  E
  LamVar {prev: N/History}
  AppRes {prev: P/History}
  DupFst {prev: P/History}
  DupSnd {prev: P/History}

type N/History:
  E
  AppArg {prev: P/History}
  LamBod {prev: N/History}
  SupFst {prev: N/History}
  SupSnd {prev: N/History}
  AnnVal {prev: N/History}
  AnnTyp {prev: N/History}
  ArrA   {prev: N/History}
  ArrB   {prev: N/History}
  Aff    {prev: N/History}
  FrlFrm {prev: N/History}
  FrlTo1 {prev: N/History}
  FrlTo2 {prev: N/History}


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
(Interact a (N/Sym wrapped id history)) = (Sym a wrapped id history)

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
(Duplicate (P/Ann value type path) fst snd) =
  let (value0, value1) = (DUP value)
  let (type0, type1) = (DUP type)
  let (opath, ipath) = (Bits/split path)
  let * = (Interact (P/Ann value0 type0 opath) fst)
  let * = (Interact (P/Ann value1 type1 ipath) snd)
  *
(Duplicate (P/Arrow A B) fst snd) =
  let (A0, A1) = (DUP A)
  let (B0, B1) = (DUP B)
  let * = (Interact (P/Arrow A0 B0) fst)
  let * = (Interact (P/Arrow A1 B1) snd)
  *
(Duplicate (P/Aff type) fst snd) =
  let (type0, type1) = (DUP type)
  let * = (Interact (P/Aff type0) fst)
  let * = (Interact (P/Aff type1) snd)
  *
(Duplicate (P/Forall from to_func) fst snd) =
  let (from0, from1) = (DUP from)
  let (xp, xn) = Wire
  let (x0p, x0n) = Wire
  let (x1p, x1n) = Wire
  let (var, type) = (to_func (P/Sup x0p x1p))
  let (var0, var1) = (DUP var)
  let (type0, type1) = (DUP type)
  let * = (Interact
            (P/Forall from0 λx0
              let * = (Interact x0 x0n) 
              (var0, type0)
            )
            fst
          )
  let * = (Interact
            (P/Forall from0 λx1
              let * = (Interact x1 x1n) 
              (var1, type1)
            )
            snd
          )
  *
(Duplicate (P/Var v) fst snd) =
  let * = (Interact (P/Var v) (N/Dup fst snd))
  *  
(Duplicate (P/Sym wrapped id history) fst snd) =
  let (fstp, fstn) = Wire
  let (sndp, sndn) = Wire
  let * = (Duplicate wrapped fstn sndn)
  let * = (Interact (P/Sym fstp id (P/History/DupFst history)) fst)
  let * = (Interact (P/Sym sndp id (P/History/DupFst history)) snd)
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

(Apply (P/Ann value (P/Arrow A B) path) arg res) =
  let (opath, ipath) = (Bits/split path)
  let (arg, chk) = (Check arg A opath)
  (
    if chk {
      λvalueλBλargλres
      let * = (Interact (P/Ann (APP value arg) B ipath) res)
      *
    } else {
      λvalueλBλargλres
      let * = (Interact value N/Error)
      let * = (Interact B N/Error)
      let * = (Interact arg N/Error)
      let * = (Interact P/Error res)
      *
    }
    value B arg res
  )

(Apply (P/Ann value type path) arg res) =
  let * = (Interact value N/Error)
  let * = (Interact type N/Error)
  let * = (Interact arg N/Error)
  let * = (Interact P/Error res)
  *
(Apply (P/Arrow A B) arg res) =
  let * = (Error A)
  let * = (Error B)
  let * = (Error arg)
  let * = (Interact P/Error res)
  *
(Apply (P/Aff type) arg res) =
  let * = (Error type)
  let * = (Error arg)
  let * = (Interact P/Error res)
  *
(Apply (P/Forall from to_func) arg res) =
  let * = (Interact arg N/Error)
  let * = (Interact P/Error res)
  let * = (Interact from N/Error)
  let (value, type) = (to_func P/Error)
  let * = (Interact value N/Error)
  let * = (Interact type N/Error)
  *
(Apply (P/Sym wrapped id history) arg res) =
  let (argp, argn) = Wire
  let (resp, resn) = Wire
  let * = (Apply wrapped argp resn)
  let * = (Interact arg (N/Sym argn id (N/History/AppArg history)))
  let * = (Interact (P/Sym resp id (P/History/AppRes history)) res)
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
(Erase (P/Ann value type path)) =
  let * = (Erase value)
  let * = (Erase type)
  *
(Erase (P/Arrow A B)) =
  let * = (Erase A)
  let * = (Erase B)
  *

(Erase (P/Aff type)) =
  let * = (Erase type)
  *
(Erase (P/Forall from to_func)) =
  let * = (Erase from)
  let (var, type) = (to_func P/Era)
  let * = (Erase var)
  let * = (Erase type)
  *
(Erase (P/Sym wrapped id history)) = (Erase wrapped)

Error: P -> None
(Error P/Era) = *
(Error P/None) = *
(Error P/Error) = *
(Error (P/Sup fst snd)) =
  let * = (Error fst)
  let * = (Error snd)
  *
(Error (P/Ann value type path)) =
  let * = (Error value)
  let * = (Erase type)
  *
(Error (P/Lam var bod)) =
  let * = (Interact P/Error var)
  let * = (Error bod)  
  *
(Error (P/Arrow A B)) =
  let * = (Error A)
  let * = (Error B)
  *
(Error (P/Aff type)) =
  let * = (Error type)
  *
(Error (P/Var v)) =
  let * = (Interact (P/Var v) N/Error)
  *
(Error (P/Forall from to_func)) =
  let * = (Error from)
  let (var, type) = (to_func P/Error)
  let * = (Error var)
  let * = (Error type)
  *
(Error (P/Sym wrapped id history)) = (Error wrapped)

(Fold (Fold/Show data f) b) =
  let * = (f (FoldArg/Node b))
  *

(Fold (Fold/Equal data f) b) =
  let * = (f (FoldArg/Node b))
  *

(Fold (Fold/Affine data f) b) =
  let * = (f (FoldArg/Node b))
  *

Sym: P -> N -> Bits -> N/History -> None
# (Sym P/Era wrapped id history) = (Interact P/Era wrapped)
# (Sym P/None wrapped id history) = (Interact P/None wrapped)
# (Sym P/Error wrapped id history) = (Interact P/Error wrapped)
# (Sym (P/Lam var bod) wrapped id history) =
#   let (varp, varn) = Wire
#   let (bodp, bodn) = Wire
#   let * = (Interact (P/Lam varn bodp) wrapped)
#   let * = (Interact (P/Sym varp id (P/History/LamVar history)) var)
#   let * = (Interact bod (N/Sym bodn id (N/History/LamBod history)))
#   *
# (Sym (P/Sup fst snd) wrapped id history) =
#   let (fstp, fstn) = Wire
#   let (sndp, sndn) = Wire
#   let * = (Interact (P/Sup fstp sndp) wrapped)
#   let * = (Interact fst (N/Sym fstn id (N/History/SupFst history)))
#   let * = (Interact snd (N/Sym sndn id (N/History/SupSnd history)))
#   *
# (Sym (P/Var v) wrapped id history) =
#   (Interact (P/Var v) (N/Sym wrapped id history))
# (Sym (P/Ann value type ann_path) wrapped id history) =
#   let (valp, valn) = Wire
#   let (typp, typn) = Wire
#   let * = (Interact (P/Ann valp typp ann_path) wrapped)
#   let * = (Interact value (N/Sym valn id (N/History/AnnVal history)))
#   let * = (Interact type (N/Sym typn id (N/History/AnnTyp history)))
#   *
# (Sym (P/Arrow A B) wrapped id history) =
#   let (Ap, An) = Wire
#   let (Bp, Bn) = Wire
#   let * = (Interact (P/Arrow Ap Bp) wrapped)
#   let * = (Interact A (N/Sym An id (N/History/ArrA history)))
#   let * = (Interact B (N/Sym Bn id (N/History/ArrB history)))
#   *
# (Sym (P/Aff type) wrapped id history) =
#   let (typp, typn) = Wire
#   let * = (Interact (P/Aff typp) wrapped)
#   let * = (Interact type (N/Sym typn id (N/History/Aff history)))
#   *
# (Sym (P/Forall from to_fun) wrapped id history) =
#   let (fromp, fromn) = Wire
#   let (xp, xn) = Wire
#   let (post_varp, post_varn) = Wire
#   let (to_typep, to_typen) = Wire
#   let (post_var, to_type) = (to_fun xp)
#   let * = (Interact
#             (P/Forall 
#               fromp
#               λx
#                 let * = (Interact x xn)
#                 (post_varp, to_typep)
#             )
#             wrapped
#           )
#   let * = (Interact from (N/Sym fromn id (N/History/FrlFrm history)))
#   let * = (Interact post_var (N/Sym post_varn id (N/History/FrlTo1 history)))
#   let * = (Interact to_type (N/Sym to_typen id (N/History/FrlTo2 history)))
#   *

# (Sym (P/Sym wrapped0 id0 history0) wrapped1 id1 history1) =
#   (Interact wrapped0 wrapped1)
(Sym a wrapped id history) = (Interact a wrapped)

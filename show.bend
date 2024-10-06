from net import *
from utils import *

P/Show: P -> Bits -> (P, String)
(P/Show (P/Era) path) = (P/Era, "*")
(P/Show (P/Lam var bod) path) = 
  let (var, var_str) = (N/Show var (Bits/O path))
  let (bod, bod_str) = (P/Show bod (Bits/I path))
  let str = (List/join [
    "("
    var_str
    " "
    bod_str
    ")"
  ])
  ((P/Lam var bod), str)
(P/Show (P/Sup fst snd) path) =
  # let (fst, fst_str) = (P/Show fst (Bits/O path))
  # let (snd, snd_str) = (P/Show snd (Bits/I path))
  # let str = (List/join [
  # "["
  # fst_str
  # " "
  # snd_str
  # "]"
  # ])
  let str = ""
  ((P/Sup fst snd), str)
(P/Show (P/Var (Var/Node a)) path) = (P/Show a path)
(P/Show (P/Var (Var/Fold data f)) path) =
  let (wp, wn) = Wire
  let * = (f (FoldArg/Data "" wn))
  (wp, data)

(P/Show P/None path) = (P/None, "None")
(P/Show P/Error path) = (P/Error, "Error")
(P/Show (P/Ann value type) path) =
  let (value, value_str) = (P/Show value (Bits/O path))
  let (type, type_str) = (P/Show type (Bits/I path))
  let str = (List/join [
    "{"
    value_str
    ":"
    type_str
    "}"
  ])
  ((P/Ann value type), str)
(P/Show (P/Arrow A B) path) = 
  let (A, A_str) = (P/Show A (Bits/O path))
  let (B, B_str) = (P/Show B (Bits/I path))
  let str = (List/join [
    A_str
    "->"
    B_str
  ])
  ((P/Arrow A B), str)

N/Show: N -> Bits -> (N, String)
(N/Show (N/Era) path) = (N/Era, "*")
(N/Show (N/Error) path) = (N/Error, "Error")
(N/Show (N/App arg res) path) = 
  let (arg, arg_str) = (P/Show arg (Bits/O path))
  let (res, res_str) = (N/Show res (Bits/I path))
  let str = (List/join [
    "("
    arg_str
    " "
    res_str
    ")"
  ])
  ((N/App arg res), str)
(N/Show (N/Dup fst snd) path) = 
  let (fst, fst_str) = (N/Show fst (Bits/O path))
  let (snd, snd_str) = (N/Show snd (Bits/I path))
  let str = (List/join [
    "["
    fst_str
    " "
    snd_str
    "]"
  ])
  ((N/Dup fst snd), str)
(N/Show (N/Var f) path) =
  let idx = (u24/to_string (Bits/to_u24 path))
  let arg = (Net/fold f idx)
  match arg {
    FoldArg/Node: (N/Show arg.node path)
    FoldArg/Data: (arg.var, idx)
  }

Print: P -> (P, String)
(Print x) = (P/Show x Bits/E)
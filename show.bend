from net import *
from utils import *

P/Show: P -> Bits -> (P, String)
(P/Show (P/Era) path) = (P/Era, "*")
(P/Show (P/Lam var bod) path) = 
  let (opath, ipath) = (Bits/split path)
  let (var, var_str) = (N/Show var opath)
  let (bod, bod_str) = (P/Show bod ipath)
  let str = (List/join [
    "("
    var_str
    " "
    bod_str
    ")"
  ])
  ((P/Lam var bod), str)
(P/Show (P/Sup fst snd) path) =
  let (opath, ipath) = (Bits/split path)
  let (fst, fst_str) = (P/Show fst opath)
  let (snd, snd_str) = (P/Show snd ipath)
  let str = (List/join [
  "["
  fst_str
  " "
  snd_str
  "]"
  ])
  ((P/Sup fst snd), str)
(P/Show (P/Var (Var/Node a)) path) = (P/Show a path)
(P/Show (P/Var (Var/Fold (Fold/Show data f))) path) =
  let (wp, wn) = Wire
  let * = (f (FoldArg/Data "" wn))
  (wp, data)

(P/Show (P/Var (Var/Fold (Fold/Equal data f))) path) =
  let * = (f (FoldArg/Node N/Error))
  (P/Error, "Error")

(P/Show P/None path) = (P/None, "None")
(P/Show P/Error path) = (P/Error, "Error")
(P/Show (P/Ann value type return_type ann_path) path) =
  let (opath, ipath) = (Bits/split path)
  let (value, value_str) = (P/Show value opath)
  let (type, type_str) = (P/Show type ipath)
  let str = (List/join [
    "{"
    value_str
    ":"
    type_str
    "}"
  ])
  ((P/Ann value type return_type ann_path), str)
(P/Show (P/Arrow A B) path) = 
  let (opath, ipath) = (Bits/split path)
  let (A, A_str) = (P/Show A opath)
  let (B, B_str) = (P/Show B ipath)
  let str = (List/join [
    "("
    A_str
    "->"
    B_str
    ")"
  ])
  ((P/Arrow A B), str)

N/Show: N -> Bits -> (N, String)
(N/Show (N/Era) path) = (N/Era, "*")
(N/Show (N/Error) path) = (N/Error, "Error")
(N/Show (N/App arg res) path) = 
  let (opath, ipath) = (Bits/split path)
  let (arg, arg_str) = (P/Show arg opath)
  let (res, res_str) = (N/Show res ipath)
  let str = (List/join [
    "("
    arg_str
    " "
    res_str
    ")"
  ])
  ((N/App arg res), str)
(N/Show (N/Dup fst snd) path) = 
  let (opath, ipath) = (Bits/split path)
  let (fst, fst_str) = (N/Show fst opath)
  let (snd, snd_str) = (N/Show snd ipath)
  let str = (List/join [
    "["
    fst_str
    " "
    snd_str
    "]"
  ])
  ((N/Dup fst snd), str)
(N/Show (N/Var f) path) =
  let (path1, path2) = (Bits/duplicate path)
  let (idx1, idx2) = (String/duplicate (u24/to_string (Bits/to_u24 path1)))
  let arg = (Show/fold f idx1)
  match arg {
    FoldArg/Node: (N/Show arg.node path2)
    FoldArg/Data: (arg.var, idx2)
  }

unchecked Show/fold: (Var -> None) -> String -> (FoldArg String)
(Show/fold var_fun data) =
  let * = (var_fun (Var/Fold (Fold/Show data λ$arg(*))))
  $arg

Print: P -> (P, String)
(Print x) = (P/Show x Bits/E)
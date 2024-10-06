from net import *
from utils import *

P/Show: P -> Bits -> String
(P/Show (P/Era) path) = "*"
(P/Show (P/Lam var bod) path) = (List/join [
  "("
  (N/Show var (Bits/O path))
  " "
  (P/Show bod (Bits/I path))
  ")"
])
(P/Show (P/Sup fst snd) path) = (List/join [
  "["
  (P/Show fst (Bits/O path))
  " "
  (P/Show snd (Bits/I path))
  "]"
])
(P/Show (P/Var (Var/Node a)) path) = (P/Show a path)
(P/Show (P/Var (Var/Fold data f)) path) =
  let * = (f (FoldArg/Data *))
  data

(P/Show P/None path) = "None"
(P/Show P/Error path) = "Error"
(P/Show (P/Ann value type) path) = (List/join [
  "{"
  (P/Show value (Bits/O path))
  ":"
  (P/Show type (Bits/I path))
  "}"
])
(P/Show (P/Arrow A B) path) = (List/join [
  (P/Show A (Bits/O path))
  "->"
  (P/Show B (Bits/I path))
])

N/Show: N -> Bits -> String
(N/Show (N/Era) path) = "*"
(N/Show (N/Error) path) = "Error"
(N/Show (N/App arg res) path) = (List/join [
  "("
  (P/Show arg (Bits/O path))
  " "
  (N/Show res (Bits/I path))
  ")"
])
(N/Show (N/Dup fst snd) path) = (List/join [
  "["
  (N/Show fst (Bits/O path))
  " "
  (N/Show snd (Bits/I path))
  "]"
])
(N/Show (N/Var f) path) =
  let idx = (u24/to_string (Bits/to_u24 path))
  let arg = (Net/fold f idx)
  match arg {
    FoldArg/Node: (N/Show arg.node path)
    FoldArg/Data: idx
  }

Print: P -> String
(Print x) = (P/Show x Bits/E)
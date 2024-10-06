from net import *

LAM: (P -> P) -> P
(LAM f) =
  let (vp, vn) = Wire
  (P/Lam vn (f vp))

APP: P -> P -> P
(APP fun arg) =
  let (resp, resn) = Wire
  let * = (Interact fun (N/App arg resn))
  resp

DUP: P -> (P, P)
(DUP x) =
  let (x0p, x0n) = Wire
  let (x1p, x1n) = Wire
  let * = (Interact x (N/Dup x0n x1n))
  (x0p, x1p)

SUP: P -> P -> P
(SUP fst snd) =
  (P/Sup fst snd)

ERA: P -> None
(ERA x) = (Interact x N/Era)
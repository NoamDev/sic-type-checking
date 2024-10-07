from net import *
from show import *
from dsl import *
from check import *
from equal import *

main = 
  # let f = (LAM λ$x $y)
  # let g = (LAM λ$y $x)
  # let (_, _, f_chk) = (Check f (P/Arrow P/None P/None) (Bits/O Bits/E))
  # let (_, _, g_chk) = (Check g (P/Arrow P/None P/None) (Bits/I Bits/E))
  # (f_chk, g_chk)
  # let (a, a_aff) = (P/Affine (LAM λx let (x0, x1) = (DUP x) (APP x0 x1)) Bits/E)
  # (a_aff, b_aff) 
  # let p = Bits/E
  # let (p0, p1) = (Bits/split p)
  # let (p1, p2) = (Bits/split p1)
  # let term =(LAM λ$x
  #            let ($x0, $x1) = (DUP $x)
  #            let * = (ERA $x0_)
  #            $x1_)
  # let (term, type, chk) = (Check  (P/Arrow (P/Aff P/None) P/None) p0)
  # let ($x0_, $x1_, eql) = (P/Equal $x0 $x1 p1)
  # (eql, chk)
  # let (f, _, f_chk) = (Check (LAM λ$x $x_) (P/Arrow P/None P/None) p0)
  # let (g, _, g_chk) = (Check (LAM λ$y $y_) (P/Arrow P/None P/None) p1)
  # str
  # $x
  # λf (f f_chk g_chk eql)
  # let (w0p, w0n) = Wire
  # let (w1p, w1n) = Wire
  # let w0n = (PseudoEqual w0n p0)
  # let w1n = (PseudoEqual w1n p1)
  # let (a, b, c) = (P/Equal w0p w1p p2)
  # c
  let pi = (P/Forall (P/Aff P/None) λT
                                      let (T0, T1) = (DUP T)
                                      (P/Era, (P/Arrow T0 T1)))
  let f = (LAM λx (LAM λx x))
  let (f, pi, chk) = (Check f pi Bits/E)
  chk
  # let (pi, str) = (Print pi)
  # str

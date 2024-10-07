from net import *
from show import *
from dsl import *
from check import *
from equal import *

checked main = 
  # let f = (LAM λ$x $y)
  # let g = (LAM λ$y $x)
  # let (_, _, f_chk) = (Check f (P/Arrow P/None P/None) (Bits/O Bits/E))
  # let (_, _, g_chk) = (Check g (P/Arrow P/None P/None) (Bits/I Bits/E))
  # (f_chk, g_chk)
  let (a, a_aff) = (P/Affine (LAM λx let (x0, x1) = (DUP x) (APP x0 x1)) Bits/E)
  let (b, b_aff) = (P/Affine (LAM λx x) Bits/E)
  (a_aff, b_aff) 
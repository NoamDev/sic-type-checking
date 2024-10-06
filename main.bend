from net import *
from show import *
from dsl import *
from check import *
from equal import *

main = 
  let f = (LAM λ$x $y)
  let g = (LAM λ$y $x)
  let (_, _, f_chk) = (Check f (P/Arrow P/None P/None) (Bits/O Bits/E))
  let (_, _, g_chk) = (Check g (P/Arrow P/None P/None) (Bits/I Bits/E))
  (f_chk, g_chk)
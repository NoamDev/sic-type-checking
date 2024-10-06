from net import *
from show import *
from dsl import *
from check import *
from equal import *

main: u24
main = 
  let (a, b, c) = (P/Equal (LAM λf (LAM λx (APP f x))) (LAM λf f) Bits/E)
  # let (a, b, c) = (P/Equal (LAM λx let (x0, x1) = (DUP x) (P/Sup x0 x1)) (LAM λf f) Bits/E)
  c
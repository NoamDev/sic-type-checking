from net import *
from show import *
from dsl import *
from check import *

main = 
  let (a, b, c) = (Check (LAM λf (LAM λx (APP f x))) (P/Arrow (P/Arrow P/None P/None) (P/Arrow P/None P/None)))
  c  
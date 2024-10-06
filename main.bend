from net import *
from show import *
from dsl import *
from check import *
from equal import *

main: u24
main = 
  let (a, b, c) = (P/Equal (LAM λx let (a, b) = (DUP x) (P/Sup a b)) (LAM λx x) Bits/E)
  c
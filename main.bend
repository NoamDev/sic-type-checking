from net import *
from show import *
from dsl import *
from check import *

main = 
  # let (a, b, c) = (Check (LAM λx x) (P/Arrow P/None P/None))
  # c
  let net = (LAM λx 
    let (x0, x1) = (DUP x)
    let * = (Erase x0)
    x1
  )
  let (net, str) = (Print net)
  let (net, str) = (Print net)
  let (net, str) = (Print net)
  let (net, str) = (Print net)
  let (net, str) = (Print net)
  let (net, str) = (Print net)
  let (net, str) = (Print net)
  let (net, str) = (Print net)
  str
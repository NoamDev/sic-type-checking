from net import *

test1 =
  let id1 = (LAM λx x)
  let id2 = (LAM λx x)
  let (id1, id2, eql) = (P/Equal id1 id2 Bits/E)
  eql

test2 =
  let f = (LAM λ$x $y)
  let g = (LAM λ$y $x)
  let (f, g, eql) = (P/Equal f g Bits/E)
  eql

checked test3 =
  let x = (P/Sym P/Era Bits/E P/History/E 1)
  let (x0, x1) = (DUP x)
  let t0 = (APP x0 P/Era)
  let t1 = (APP x1 P/Era)
  let (t0, t1, eql) = (P/Equal t0 t1 Bits/E)
  eql

main =
  with IO {
    ask * = (IO/println (u24/to_string test1))
    ask * = (IO/println (u24/to_string test2))
    ask * = (IO/println (u24/to_string test3))
    (wrap *)
  }
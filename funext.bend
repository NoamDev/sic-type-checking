from net import *
from show import *

PI: P -> (P -> P) -> P
(PI T F) =
  (P/Forall
    (P/Aff T)
    λx
      let (x0, x1) = (DUP x)
      (
        x0,
        (F x1)
      )
  )

# Eq = (T: Type) (P: T -> Type) (h: P a) -> P b
Eq: P -> P -> P -> P
Eq = 
    λT
      λa
      λb
      (PI (P/Arrow T P/Type)
          λP
          let (P0, P1) = (DUP P)
          (P/Arrow (APP P0 a) (APP P1 b))
      )

funext_type: P = 
# (
#   PI P/Type
#   λT
  let T = (P/None)
  let (T0, T1) = (DUP T)
  let (T00, T01) = (DUP T0)
  let (T10, T11) = (DUP T1)
  # (
  #   PI P/Type
  #   λU
    let U = P/None
    let (U0, U1) = (DUP U)
    let (U00, U01) = (DUP U0)
    let (U10, U11) = (DUP U1)
    # (
    #   PI (P/Arrow T00 U00)
    #   λf
      let f = (LAM λx x)
      let (f0, f1) = (DUP f)
      # (
      #   PI (P/Arrow T01 U01)
      #   λg
        let g = (LAM λx x)
        let (g0, g1) = (DUP g)
        # (P/Arrow 
          # (PI T10
          #   λt
          #   let (t0, t1) = (DUP t)
          #   (Eq U10 (APP f0 t0) (APP g0 t1))
          # )
          # P/None
          # (Eq (P/Arrow T11 U11) f1 g1)
          (PI (P/Arrow (P/Arrow P/None P/None) P/Type)
            λP
            # let P = (LAM λt let * = (ERA t) P/None)
            let (P0, P1) = (DUP P)
            (P/Arrow (APP P0 (LAM λx x)) (APP P1 (LAM λx x)))
          )
        # )
      # )
    # )
  # )
# )



checked try =  
  # let funext =
  # (LAM λT
  #   let * = (ERA T)
    # (LAM λU
    #   let * = (ERA U)
      # (LAM λf
      #   let * = (ERA f)
        # (LAM λg
        #   let * = (ERA g)
          # (LAM λh
          #   let * = (ERA h)
            # (LAM λP
            #   let * = (ERA P)
              # (LAM λa
              # let * = (ERA a)
              #   a
              # )
            # )
          # )
        # )
      # )
    # )
  # )


  let funext = (P/Lam N/Era P/Era)
  let (funext, chk) = (Check funext funext_type Bits/E)
  let (funext, str) = (P/Show funext Bits/E)
  str
  # (P/CleanSymbols funext Bits/E)
  # funext

checked try2 =
  let var = N/Era
  let bod = P/Era
  let path = Bits/E
  let from = (P/Arrow (P/Arrow P/None P/None) P/Type)
  let f1 = (LAM λx x)
  let g1 = (LAM λx x)
  # let to_func = λP
  #               let (P0, P1) = (DUP P)
  #               let to_type = (P/Arrow (APP P0 f1) (APP P1 g1))
  #               let var = P/Era
  #               (var, to_type)

  let (xp, xn) = Wire
  let (opath, ipath) = (Bits/split path)
  let (oopath, iopath) = (Bits/split opath)
  # let (post_var, to_type) = (to_func (P/Ann (P/Sym xp iopath P/History/E 0) from oopath 1))
  # let * = (Erase post_var)
  let res = P/Era#(APP (P/Lam var bod) post_var)
  # let (res, chk) = (Check res to_type ipath)
  let chk = 0
  # let (term, chk) = ((P/Lam xn res), chk)
  # term
  # let (x0, x1) = (DUP xp)
  # let P0 = (P/Ann xp from oopath 1)
  # let P1 = (P/Ann x1 from oopath 1)
  # let to_type = (P/Arrow (APP P0 f1) (APP P1 g1))
  # let to_type = (APP P0 f1)
  let (xp, xn) = Wire
  let (top, ton) = Wire
  let (yp, yn) = Wire
  let * = (Apply (P/Ann xp (P/Arrow (P/Arrow P/None P/None) P/Type) Bits/E 1) (P/Lam yn yp) ton)
  let term = (P/Lam xn top)
  # let (term, str) = (P/Show term Bits/E)
  xp

checked try3 =
  # let (xp, xn) = Wire
  let (top, ton) = Wire
  let (yp, yn) = Wire
  # let * = (Apply (P/Ann xp (P/Arrow (P/Arrow P/None P/None) P/Type) Bits/E 1) (P/Lam yn yp) ton)
  let (opath, ipath) = (Bits/split Bits/E)
  # let A = (P/Arrow P/None P/None)
  # let B = P/Type
  let (arg, chk) = (Check (P/Lam yn yp) (P/Arrow P/None P/None) (Bits/O Bits/E))
  # let * = (Interact (P/Ann (APP xp arg) B ipath (& 1 chk)) ton)
  # let term = (P/Lam xn top)
  # let (term, str) = (P/Show term Bits/E)
  let (arg, str) = (P/Show arg Bits/E)
  str

checked try4 =
  let path = Bits/E
  # let (bod, var) = Wire
  let (xp, xn) = Wire
  # let (opath, ipath) = (Bits/split path)
  # let (oopath, iopath) = (Bits/split opath)
  # let res = 
  # let (res, chk) = (Check res P/None ipath)
  # let (arg, chk) = ((P/Lam xn res), chk)
  let arg = (P/Lam xn (P/Sym P/Era Bits/E P/History/E 0))
  let (arg, str) = (P/Show arg Bits/E)
  str




main = try

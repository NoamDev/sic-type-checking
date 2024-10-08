from net import *
from show import *
from dsl import *
from check import *
from equal import *

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





funext_type: P
funext_type =
  # (PI
  #   P/Type
  #   λT
    # let T = P/None
    # let (T0, T1) = (DUP T)
    # let (T00, T01) = (DUP T0)
    # let (T10, T11) = (DUP T1)
    # (PI P/Type
    #   λU
      # let U = P/None
      # let (U0, U1) = (DUP U)
      # let (U00, U01) = (DUP U0)
      # let (U10, U11) = (DUP U1)
      # (PI (P/Arrow T00 U00)
      #   λf
        let f = (LAM λx x)
        let (f0, f1) = (DUP f)
        # (PI (P/Arrow T01 U01)
        #   λg
        let g = (LAM λx x)
          let (g0, g1) = (DUP g)
          # let * = (ERA f0)
          # let * = (ERA f1)
          # let * = (ERA g0)
          # let * = (ERA g1)
          # let * = (ERA U00)
          # let * = (ERA U01)
          # let * = (ERA U10)
          # let * = (ERA U11)
          # let * = (ERA T00)
          # let * = (ERA T01)
          # let * = (ERA T10)
          # let * = (ERA T11)
          
          (P/Arrow 
            (PI P/None
              λt
              let (t0, t1) = (DUP t)
              (Eq P/None (APP f0 t0) (APP g0 t1))
            )
            # P/None
            (Eq (P/Arrow P/None P/None) f1 g1)
            # (PI (P/Arrow (P/Arrow T11 U11) P/Type)
            #   λP
            #     let (P0, P1) = (DUP P)
            #     # let * = (ERA P)
            #     (P/Arrow (APP P0 f1) (APP P1 g1))
            #     # P/None
            # )
          )
        # )
      # )
    # )
  # )

unchecked funext: P -> P
(funext hole1 hole2 hole3) =
  # (LAM λT
  #   let * = (Erase T)
    # (LAM λU
    #   let * = (Erase U)
      # (LAM λf
      #   let * = (Erase f)
      #   (LAM λg
      #     let * = (Erase g)
          (LAM λh
            # let * = (Erase h)
            (LAM λP
              # let * = (Erase P)
              # hole
              # P/Era
                (LAM λa
                  # let * = (Erase a)
                  # a
  #                 # P/Era
                  # hole1
                  (APP
                    (APP
                      (APP
                        h
                        hole1
                      )
                      # (LAM λu let * = (Erase u) P/None)
                      # (LAM λu 
                      #   (APP P (LAM λ$t u))
                      # )
                      hole2
                    )
                    a
                  )
                )
            )
          )
        # )
      # )
    # )
  # )

(IO/println x) = (IO/print (List/join [x "\n"]))

main = 
  # let none_eq_none_type = (Eq P/Type P/None P/None)
  # let none_eq_none = (LAM λP let * = (ERA P) (LAM λx x))
  # let (z, chk) = (Check none_eq_none none_eq_none_type Bits/E)
  let type = 
  (P/Arrow
    (P/Arrow
      P/None
      (P/Arrow
        (P/Arrow P/None (P/Arrow P/None P/None))
        P/None
      )
    )
    P/None
  )
  let term = 
  (LAM λh
    (APP
      (APP h $t)
      (LAM λu (LAM λ$t u))
    )
  )
  # h: P/None -> (P/None -> P/None) -> P/None
  # ((h $t) λ$t P/Era)
  # let hole1 = (P/Hole λ$T *)
  # let hole2 = (P/Hole λ$U *)
  # let hole3 = (P/Hole λ$V *)
  # let funext = (funext hole1 hole2 hole3)
  let (t, chk) = (Check term type Bits/E)
  # let (funext, chk) = (Check funext funext_type Bits/E)
  # # let (funext_type, funext_type_str) = (Print funext_type)
  # # let (funext, funext_str) = (Print funext)
  # let (_, h1) = (Print $T)
  # let (_, h2) = (Print $U)
  # let (_, h3) = (Print $V)
  with IO {
  # # # # #   # ask * = (IO/println funext_type_str)
  # # # # #   # ask * = (IO/println funext_str)
  #   # ask * = (IO/println h1)
  #   # ask * = (IO/println h2)
  #   # ask * = (IO/println h3)
    ask * = (IO/println (u24/to_string chk))
    (wrap chk)
  }
  # hole_type_str
  # $T
  # Pa
  # (Print Pa)
  # (P, P0)
  # Pa
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
  (PI
    P/Type
    λT
    let (T0, T1) = (DUP T)
    let (T00, T01) = (DUP T0)
    let (T10, T11) = (DUP T1)
    (PI P/Type
      λU
      let (U0, U1) = (DUP U)
      let (U00, U01) = (DUP U0)
      let (U10, U11) = (DUP U1)
      (PI (P/Arrow T00 U00)
        λf
        let (f0, f1) = (DUP f)
        (PI (P/Arrow T01 U01)
          λg
          let (g0, g1) = (DUP g)
          (P/Arrow 
            (PI T10
              λt
              let (t0, t1) = (DUP t)
              (Eq U10 (APP f0 t0) (APP g0 t1))
            )
            (Eq (P/Arrow T11 U11) f1 g1)
          )
        )
      )
    )
  )

unchecked funext: P
funext =
  (LAM λT
    let * = (Erase T)
    (LAM λU
      let * = (Erase U)
      (LAM λf
        let * = (Erase f)
        (LAM λg
          let * = (Erase g)
          (LAM λh
            # let * = (Erase h)
            (LAM λP
              # let * = (Erase P)
                (LAM λa
                  (APP
                    (APP
                      (APP
                        h
                        $t
                      )
                      (LAM λu 
                        (APP P (LAM λ$t u))
                      )
                    )
                    a
                  )
                )
            )
          )
        )
      )
    )
  )

(IO/println x) = (IO/print (List/join [x "\n"]))

checked main = 
  # let none_eq_none_type = (Eq P/Type P/None P/None)
  # let none_eq_none = (LAM λP let * = (ERA P) (LAM λx x))
  # let (z, chk) = (Check none_eq_none none_eq_none_type Bits/E)

  let (funext, chk) = (Check funext funext_type Bits/E)
  let (funext_type, funext_type_str) = (Print funext_type)
  let (funext, funext_str) = (Print funext)
  with IO {
    ask * = (IO/println funext_type_str)
    ask * = (IO/println funext_str)
    ask * = (IO/println (u24/to_string chk))
    (wrap *)
  }
  # Pa
  # (Print Pa)
  # (P, P0)
  # Pa
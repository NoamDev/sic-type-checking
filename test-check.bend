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

H_type =
  (PI P/None
    λt
    let (t0, t1) = (DUP t)
    (Eq P/None t0 t1)
  )

Goal_type = (Eq (P/Arrow P/None P/None) (LAM λx x) (LAM λx x))

(Log list) = (IO/println (List/join list))

test1 =
    let h = (P/Ann P/Era H_type (Bits/O Bits/E) 1)
    let (h_type, h_type_str) = (Print H_type)
    let (h, h_str) = (Print h)
    let h_era = (APP h $t)
    let (h_era, h_era_str) = (Print h_era)
    let proof = (
      LAM λP
        let (P, $Pstr) = (Print P)
        (LAM λa
          let (a, $astr) = (Print a)
          let h_e_u = (
            APP
            h_era
            (LAM λu
 
              (APP P (LAM λ$t u))
              # P/None
            )
          )
          let (h_e_u, $h_e_u_str) = (Print h_e_u)
          h_e_u
        )
        # let Pu = (APP P (LAM λu
        #   (LAM λ$t u)
        # ))
        # let (Pu, $Pustr) = (Print Pu)
        # Pu
    )
    let (proof, chk) = (Check proof Goal_type (Bits/I Bits/E))
  with IO {
    ask * = (Log ["h_type:" h_type_str])
    ask * = (Log ["h:" h_str])
    ask * = (Log ["h_era:" h_era_str])
    ask * = (Log ["P:" $Pstr])
    ask * = (Log ["a:" $astr])
    ask * = (Log ["h_e_u:" $h_e_u_str])
    # ask * = (Log ["Pu:" $Pustr])
    (wrap *)
  }

test2 =
    # let h = (P/Ann P/Era H_type Bits/E 1)
    # let (h_type, h_type_str) = (Print H_type)
    # let h_era = (APP h P/Era)
    let path = Bits/E
    let arg  = P/Era
    let ann_chk = 1
    let from = (P/Aff P/None)
    let to_fun = λt
                  let (t0, t1) = (DUP t)
                  let (t1, t2) = (DUP t1)
                  (t2, (Eq P/None t0 t1))
    let value = P/Era
    let (resp, resn) = Wire
    let res = resn

    let (opath, ipath) = (Bits/split path)
    let (arg, chk) = (Check arg from opath)
    let (post_var, to_type) = (to_fun arg)
    let * = (Interact (P/Ann (APP value post_var) to_type ipath (& chk ann_chk)) res)
    let (h_era, h_era_str) = (Print resp)
    # let (h_era, h_era_str) = (Print h)
  with IO {
    # ask * = (IO/println h_type_str)
    # ask * = (IO/println h_str)
    # ask * = (IO/println h_era_str)
    (wrap h_era_str)
  }

test3 =
  let T = P/None
  let FT = (P/Arrow T T)
  let PT = (P/Aff (P/Arrow T P/Type))
  let PT_ = (P/Arrow T P/Type)
  let PFT = (P/Aff (P/Arrow FT P/Type))
  let PF = (P/Ann P/Era PFT Bits/E 1)
  let P = (LAM λu 
            # let * = (ERA u)
            # let u = (P/Ann (P/Sym P/Era Bits/E P/History/E 1) P/None Bits/E 1)
            let (u, $ustr) = (Print u)
            (APP PF (LAM λt let * = (ERA t)  u))
            # P/None
          )
  let (P, chk) = (Check P (P/Arrow P/None P/Type) Bits/E)
  let (P, aff) = (P/Affine P Bits/E)
  let (P, Pstr) = (Print P)
  with IO {
    ask * = (Log ["P: " Pstr])
    ask * = (Log ["u: " $ustr])
    (wrap (aff,chk))
    # P
  }
  
test4 =
  let T = P/None
  let FT = (P/Arrow T T)
  let PT = (P/Aff (P/Arrow T P/Type))
  let PT_ = (P/Arrow T P/Type)
  let PFT = (P/Arrow FT P/Type)
  let PF = (P/Ann P/Era PFT Bits/E 1)
  let (varp, varn) = Wire
  let (xp, xn) = Wire
  let A = P/None
  let B = P/Type
  let path = Bits/E

  let (opath, ipath) = (Bits/split path)
  let (oopath, iopath) = (Bits/split opath)
  let (tp, tn) = Wire
  # let boo = (P/Lam tn let * = (ERA tp) (P/Ann (P/Sym xp iopath P/History/E 1) A oopath 1))
  # let (boo, chk) = (Check boo FT Bits/E)
  # let * = (ERA boo)
  # let var = varn
            # let * = (ERA u)
            # let u = (P/Ann (P/Sym P/Era Bits/E P/History/E 1) P/None Bits/E 1)
            # let res = (APP PF )
            # P/None
          # )
  # let (A, is_aff_type) = (IsAff A)
  # let res = (APP (P/Lam var bod) (P/Ann (P/Sym xp iopath P/History/E 1) A oopath 1))
  # let (res, chk) = (Check res B ipath)
  # let lam = (P/Lam xn res)
  # (Print lam)
  # res
  # xn
  let boo = (P/Lam N/Era xp)
  let * = (ERA boo)
  (Print (P/Lam xn P/Era))
  # res
  # boo

test5 =
  let (xp, xn) = Wire
  # let boo = (P/Lam N/Era xp)
  # let * = (Interact (P/Lam N/Era xp) N/Era)
  # let * = (Erase (P/Lam N/Era xp))
  let * = (Erase xp)
  (Print (P/Lam xn P/Era))
  # xn


main =
  test1
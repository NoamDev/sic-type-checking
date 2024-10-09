from net import *
from equal import *
from affine import *

Check: P -> P -> Bits -> (P, u24)
(Check P/Era P/None path) = (P/Era, 1)
(Check (P/Lam var bod) (P/Arrow A B) path) =
  let (xp, xn) = Wire
  let (opath, ipath) = (Bits/split path)
  let (oopath, iopath) = (Bits/split opath)
  let (A, is_aff_type) = (IsAff A)
  let res = (APP (P/Lam var bod) (P/Ann (P/Sym xp iopath P/History/E is_aff_type) A oopath 1))
  let (res, chk) = (Check res B ipath)
  ((P/Lam xn (P/CleanSymbols res path)), chk)
(Check (P/Lam var bod) (P/Forall from to_func) path) =
  let (xp, xn) = Wire
  let (opath, ipath) = (Bits/split path)
  let (oopath, iopath) = (Bits/split opath)
  let (from, is_aff_type) = (IsAff from)
  let (post_var, to_type) = (to_func (P/Ann (P/Sym xp iopath P/History/E is_aff_type) from oopath 1))
  let res = (APP (P/Lam var bod) post_var)
  let (res, chk) = (Check res to_type ipath)
  ((P/Lam xn (P/CleanSymbols res path)), chk)
(Check (P/Ann value type1 path1 ann_chk) type2 path2) =
  let (type1, type2, eql) = (RefinementOf type1 type2 path2)
  let * = (Erase type1)
  let * = (Erase type2)
  (value, (& eql ann_chk))
(Check value (P/Aff T) path) =
  let (opath, ipath) = (Bits/split path)
  let (value, aff) = (P/Affine value opath)
  let (value, chk) = (Check value T ipath)
  (value, chk)
(Check P/None P/Type path) = (P/None, 1)
(Check (P/Var (Var/Node value)) type path) = (Check value type path)
(Check value (P/Var (Var/Node type)) path) = (Check value type path)
(Check value (P/Ann type meta_type ann_path ann_chk) path) =
  let (value, chk) = (Check value type path)
  (value, (& chk ann_chk))
(Check (P/Hole f) type path) =
  let * = (f type)
  (P/Era, 1)
(Check a b path) = 
  let * = (Erase b)
  (a, 0)

IsAff: P -> (P, u24)
(IsAff (P/Aff a)) = ((P/Aff a), 1)
(IsAff (P/Var (Var/Node a))) = (IsAff a)
(IsAff a) = (a, 0)

RefinementOf: P -> P -> Bits -> (P, P, u24)
(RefinementOf a b path) = (RefinementOfInternal (NormalAff a) (NormalAff b) path)

RefinementOfInternal: P -> P -> Bits -> (P, P, u24)
(RefinementOfInternal (P/Aff a) (P/Aff b) path) = (P/Equal (P/Aff a) (P/Aff b) path)
(RefinementOfInternal (P/Aff a) b path) =
  let (a, b, eql) = (P/Equal a b path)
  ((P/Aff a), b, eql)
(RefinementOfInternal a b path) = (P/Equal a b path)

NormalAff: P -> P
(NormalAff (P/Var (Var/Node a))) = (NormalAff a)
(NormalAff (P/Aff (P/Var (Var/Node a)))) = (NormalAff (P/Aff a))
(NormalAff (P/Aff (P/Aff a))) = (NormalAff (P/Aff (NormalAff a)))
(NormalAff a) = a

P/CleanSymbols: P -> Bits -> P
(P/CleanSymbols (P/Var (Var/Node node)) path) = (P/CleanSymbols node path)
(P/CleanSymbols (P/Var (Var/Fold (Fold/CleanSymbols data f))) path) =
  let (wp, wn) = Wire
  let * = (f (FoldArg/Data * wn))
  wp
(P/CleanSymbols (P/Var (Var/Fold f)) path) =
  let * = (Fold f N/Error)
  P/Error
(P/CleanSymbols P/Era path) = P/Era
(P/CleanSymbols P/Error path) = P/Error
(P/CleanSymbols (P/Lam var bod) path) =
  (P/Lam
    (N/CleanSymbols var path)
    (P/CleanSymbols bod path)
  )
(P/CleanSymbols (P/Sup fst snd) path) =
  (P/Sup
    (P/CleanSymbols fst path)
    (P/CleanSymbols snd path)
  )
(P/CleanSymbols (P/Ann value typ ann_path ann_chk) path) =
  (P/Ann
    (P/CleanSymbols value path)
    (P/CleanSymbols typ path)
    ann_path
    ann_chk
  )
(P/CleanSymbols P/None path) = P/None
(P/CleanSymbols P/Type path) = P/Type
(P/CleanSymbols (P/Arrow from to) path) =
  (P/Arrow
    (P/CleanSymbols from path)
    (P/CleanSymbols to path)
  )
(P/CleanSymbols (P/Aff typ) path) =
  (P/Aff (P/CleanSymbols typ path))
(P/CleanSymbols (P/Forall from to_fun) path) =
  let (xp, xn) = Wire
  let (post_var, type_to) = (to_fun xp)
  (P/Forall
    (P/CleanSymbols from path)
    λx
      let * = (Interact x xn)
      ((P/CleanSymbols post_var path), (P/CleanSymbols type_to path))
  )
(P/CleanSymbols (P/Sym wrapped id history aff) path) =
  (
    if (Bits/startsWith id path) {
      λwrapped
        wrapped
    } else {
      λwrapped
        (P/Sym wrapped id history aff)
    }
    wrapped
  )
(P/CleanSymbols (P/Hole f) path) = (P/Hole f)

N/CleanSymbols: N -> Bits -> N
(N/CleanSymbols N/Era path) = N/Era
(N/CleanSymbols (N/App arg res) path) =
  (N/App
    (P/CleanSymbols arg path)
    (N/CleanSymbols res path)
  )
(N/CleanSymbols (N/Dup fst snd) path) =
  (N/Dup
    (N/CleanSymbols fst path)
    (N/CleanSymbols snd path)
  )
(N/CleanSymbols (N/Var f) path) =
  let arg = (CleanSymbols/fold f *)
  match arg {
    FoldArg/Node: (N/CleanSymbols arg.node path)
    FoldArg/Data: arg.var
  }
(N/CleanSymbols N/Error path) = N/Error
(N/CleanSymbols (N/Sym wrapped id history aff) path) =
  (
    if (Bits/startsWith id path) {
      λwrapped
        wrapped
    } else {
      λwrapped
        (N/Sym wrapped id history aff)
    }
    wrapped
  )

unchecked CleanSymbols/fold: (Var -> None) -> None -> (FoldArg None)
(CleanSymbols/fold var_fun data) =
  let * = (var_fun (Var/Fold (Fold/CleanSymbols data λ$arg(*))))
  $arg
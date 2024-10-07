P/Affine: P -> Bits -> (P, u24)
(P/Affine P/Error path) = (P/Error, 0)
(P/Affine P/Era path) = (P/Era, 1)
(P/Affine (P/Lam var bod) path) =
  let (path0, path1) = (Bits/duplicate path)
  let (var, var_aff) = (N/Affine var path0)
  let (bod, bod_aff) = (P/Affine bod path1)
  ((P/Lam var bod), (& var_aff bod_aff))
(P/Affine (P/Sup a b) path) =
  let (path0, path1) = (Bits/duplicate path)
  let (a, a_aff) = (P/Affine a path0)
  let (b, b_aff) = (P/Affine b path1)
  (((P/Sup a b)), 0)
(P/Affine (P/Var (Var/Node node)) path) = (P/Affine node path)
(P/Affine (P/Var (Var/Fold (Fold/Affine idx0 f))) path) =
  let idx1 = (Bits/to_u24 path)
  let (idx1_0, idx1_1) = (u24/duplicate idx1)
  if (== idx0 idx1_0) {
    let (wp, wn) = Wire
    let * = (f (FoldArg/Data idx1_1 wn))
    (wp, 1)
  } else {
    let * = (f (FoldArg/Node N/Error))
    (P/Error, 0)
  }
(P/Affine (P/Var (Var/Fold other)) path) =
  let * = (Fold other N/Error)
  (P/Error, 0)
(P/Affine P/None path) = (P/None, 1)
(P/Affine (P/Arrow A B) path) =
  let (path0, path1) = (Bits/duplicate path)
  let (A, A_aff) = (P/Affine A path0)
  let (B, B_aff) = (P/Affine B path1)
  ((P/Arrow A B), (& A_aff B_aff))
(P/Affine (P/Ann value type return_type ann_path) path) =
  let (value, value_aff) = (P/Affine value path)
  let (type, type_aff) = (P/Affine value path)
  ((P/Ann value type return_type ann_path), (& value_aff type_aff))

N/Affine: N -> Bits -> (N, u24)
(N/Affine a path) = (a, 0)
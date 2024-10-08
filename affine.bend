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
(P/Affine (P/Ann value type ann_path) path) =
  let (value, value_aff) = (P/Affine value path)
  let (type, type_aff) = (P/Affine value path)
  ((P/Ann value type ann_path), (& value_aff type_aff))
(P/Affine (P/Aff type) path) =
  let (type, type_aff) = (P/Affine type path)
  ((P/Aff type), type_aff)
(P/Affine (P/Forall from to_func) path) =
  let (opath, ipath) = (Bits/split path)
  let (oopath, iopath) = (Bits/split opath)
  let (oipath, iipath) = (Bits/split ipath)
  let (from, from_aff) = (P/Affine from oopath)
  let (xp, xn) = Wire
  let (pre_var, pre_var_aff) = (N/Affine xn oipath)
  let (post_var, to_type) = (to_func xp)
  let (post_var, post_var_aff) = (P/Affine post_var iopath)
  let (to_type, to_type_aff) = (P/Affine to_type iipath)
  (
    (P/Forall from λx
      let * = (Interact x pre_var)
      (post_var, to_type)
    ),
    (& (& from_aff pre_var_aff) (& post_var_aff to_type_aff))
  )

N/Affine: N -> Bits -> (N, u24)
(N/Affine N/Error path) = (N/Error, 0)
(N/Affine N/Era path) = (N/Era, 1)
(N/Affine (N/App arg res) path) =
  let (path0, path1) = (Bits/duplicate path)
  let (arg, arg_aff) = (P/Affine arg path0)
  let (res, res_aff) = (N/Affine res path1)
  ((N/App arg res), (& arg_aff res_aff))
(N/Affine (N/Dup a b) path) =
  let (path0, path1) = (Bits/duplicate path)
  let (a, a_aff) = (N/Affine a path0)
  let (b, b_aff) = (N/Affine b path1)
  ((N/Dup a b), 0)
(N/Affine (N/Var f) path) =
  let (path0, path1) = (Bits/duplicate path)
  let idx = (Bits/to_u24 path0)
  let arg = (Affine/fold f idx)
  match arg {
    FoldArg/Node: (N/Affine arg.node path1)
    FoldArg/Data: (arg.var, 1)
  }

unchecked Affine/fold: (Var -> None) -> u24 -> (FoldArg u24)
(Affine/fold f data) =
  let *= (f (Var/Fold (Fold/Affine data λ$arg(*))))
  $arg
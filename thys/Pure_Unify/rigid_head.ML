
(*Pattern.rigid_head of the pattern patches*)
fun rigid_head env t =
  (case head_of (Envir.head_norm env t) of
    Var _ => false
  | Abs _ => false
  | _ => true);

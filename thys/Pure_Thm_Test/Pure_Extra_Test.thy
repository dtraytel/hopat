section \<open>Testing the Generated Code of the Data of Theorems\<close>

theory Pure_Extra_Test
  imports Pure_Bicompose_Test_Base
begin

text \<open>
  The operations of theory \<^theory_text>\<open>Pure_Extra\<close>, with which the wrappers compute the sort
  hypotheses, hypotheses and sort constraints of theorems, are compared with Pure's
  \<open>Term_Ord\<close>, \<open>Ord_List\<close>, \<open>Sorts\<close> and \<open>Envir\<close>, and with a copy of the (local) constraint
  operations of \<open>thm.ML\<close>, on the propositions, types and sorts of the theorems of HOL and on the
  type environments of their unifiable types. Results must agree exactly.
\<close>

ML \<open>
local
  structure G = Bicompose_Generated;
  val thy = \<^theory>;

  fun gord LESS = G.LESS | gord EQUAL = G.EQUAL | gord GREATER = G.GREATER;

  val props =
    Global_Theory.all_thms_of thy false
    |> map (Thm.prop_of o #2)
    |> take 3000;
  val typs = fold (fold_types (fn T => insert (op =) T)) props [] |> take 600;
  fun atyp_sort (TFree (_, S)) = S | atyp_sort (TVar (_, S)) = S | atyp_sort _ = [];
  val sorts = map atyp_sort (fold Term.add_tfrees props [] |> map TFree)
    @ map (single) (Sign.all_classes thy) |> distinct (op =) |> take 300;

  val fails = Unsynchronized.ref 0;
  fun check what ok = if ok then () else (fails := ! fails + 1; warning ("mismatch: " ^ what));

  fun zipt xs ys = let val n = Int.min (length xs, length ys) in take n xs ~~ take n ys end;
  fun pairs xs = zipt xs (tl xs @ [hd xs]) @ zipt xs (rev xs);

  (* orders *)
  val _ = pairs props |> List.app (fn (t, u) =>
    check "fast_term_ord" (G.fast_term_ord t u = gord (Term_Ord.fast_term_ord (t, u))));
  val _ = pairs typs |> List.app (fn (T, U) =>
    check "typ_ord" (G.typ_ord T U = gord (Term_Ord.typ_ord (T, U))));
  val _ = pairs sorts |> List.app (fn (S, S') =>
    check "sort_ord" (G.sort_ord S S' = gord (Term_Ord.sort_ord (S, S'))));

  (* hypotheses *)
  fun chunks n xs = if length xs <= n then [xs] else take n xs :: chunks n (drop n xs);
  val hyps_lists = chunks 7 props |> map (Ord_List.make Term_Ord.fast_term_ord);
  val ord_union = Ord_List.union Term_Ord.fast_term_ord;
  val _ = pairs hyps_lists |> List.app (fn (hs1, hs2) =>
    check "union_hyps" (G.union_hyps hs1 hs2 = ord_union hs1 hs2));
  val _ = (zipt hyps_lists props) |> List.app (fn (hs, A) =>
    (check "insert_hyps" (G.insert_hyps A hs = Ord_List.insert Term_Ord.fast_term_ord A hs);
     check "remove_hyps" (G.remove_hyps A hs = Ord_List.remove Term_Ord.fast_term_ord A hs);
     List.app (fn h =>
       check "remove_hyps (member)" (G.remove_hyps h hs = Ord_List.remove Term_Ord.fast_term_ord h hs)) hs));

  (* sort hypotheses *)
  val sorts_lists = map (fn t => Sorts.insert_term t []) props;
  val _ = (zipt props sorts_lists) |> List.app (fn (t, Ss) =>
    check "insert_term" (G.insert_term_sorts t [] = Ss));
  val _ = pairs sorts_lists |> List.app (fn (Ss1, Ss2) =>
    check "union of sorts" (G.sorts_union Ss1 Ss2 = Sorts.union Ss1 Ss2));

  (* type environments: unifiers of the types of the propositions, renamed apart *)
  val envs =
    pairs typs |> map_filter (fn (T, U) =>
      let
        val varify = map_atyps (fn TFree (a, S) => TVar ((a, 0), S) | T => T);
        val T' = Logic.incr_tvar 1 (varify T) and U' = Logic.incr_tvar 3 (varify U);
        val maxidx = Int.max (maxidx_of_typ T', maxidx_of_typ U');
      in
        SOME (Envir.Envir {maxidx = #2 (Sign.typ_unify thy (T', U') (Vartab.empty, maxidx)),
          tenv = Vartab.empty, tyenv = #1 (Sign.typ_unify thy (T', U') (Vartab.empty, maxidx))})
        handle Type.TUNIFY => NONE
      end);
  val _ = writeln ("type environments: " ^ string_of_int (length envs));
  val _ = (zipt envs (sorts_lists @ sorts_lists)) |> List.app (fn (env, Ss) =>
    check "insert_sorts" (G.env_insert_sorts (Envir.type_env env) Ss = Envir.insert_sorts env Ss));

  (* constraints: a copy of the operations of thm.ML *)
  type constraint = {theory: theory, typ: typ, sort: sort};
  val constraint_ord : constraint ord =
    Context.theory_id_ord o apply2 (Context.theory_id o #theory)
    ||| Term_Ord.typ_ord o apply2 #typ
    ||| Term_Ord.sort_ord o apply2 #sort;
  val smash_atyps =
    map_atyps (fn TVar (_, S) => Term.aT S | TFree (_, S) => Term.aT S | T => T);
  val union_constraints = Ord_List.union constraint_ord;
  fun insert_constraints _ (_, []) = I
    | insert_constraints thy (T, S) =
        let
          val ignored =
            (case T of
              TFree (_, S') => S = S'
            | TVar (_, S') => S = S'
            | _ => false);
        in
          if ignored then I
          else Ord_List.insert constraint_ord {theory = thy, typ = smash_atyps T, sort = S}
        end;
  fun insert_constraints_env thy env =
    let
      val tyenv = Envir.type_env env;
      val normT = Envir.norm_type tyenv;
      fun insert ([], _) = I
        | insert (S, T) = insert_constraints thy (normT T, S);
    in tyenv |> Vartab.fold (insert o #2) end;

  fun tord thy1 thy2 = gord (Context.theory_id_ord (Context.theory_id thy1, Context.theory_id thy2));
  val to_g = map (fn {theory, typ, sort} => (theory, (typ, sort)));
  val named = map (fn (th, x) => (Context.theory_long_name th, x));
  fun eq_cs (cs1, cs2) = named cs1 = named cs2;
  val thys = [thy, Theory.get_pure (), hd (Theory.parents_of thy)];
  val TSs =
    zipt typs (sorts @ sorts @ sorts) @ map (fn T => (T, atyp_sort T)) typs
    @ map (fn S => (TVar (("'a", 0), S), S)) sorts;
  val css =
    chunks 5 (map_index I TSs)
    |> map (fn l => fold (fn (i, TS) => insert_constraints (nth thys (i mod 3)) TS) l []);
  val _ = writeln ("constraint lists: " ^ string_of_int (length css));
  val _ = (map_index I TSs) |> List.app (fn (i, TS) =>
    let val cs = nth css (i mod length css) and th = nth thys (i mod 3) in
      check "insert_constraints"
        (eq_cs (G.insert_constraint tord th TS (to_g cs), to_g (insert_constraints th TS cs)))
    end);
  val _ = pairs css |> List.app (fn (cs1, cs2) =>
    check "union_constraints" (eq_cs (G.union_constraints tord (to_g cs1) (to_g cs2), to_g (union_constraints cs1 cs2))));
  val _ = (zipt envs (css @ css @ css)) |> List.app (fn (env, cs) =>
    check "insert_constraints_env"
      (case G.env_insert_constraints tord thy (Envir.type_env env) (to_g cs) of
        SOME (G.Ok cs') => eq_cs (cs', to_g (insert_constraints_env thy env cs))
      | _ => false));
in
  val _ = writeln ("propositions: " ^ string_of_int (length props) ^ ", types: " ^ string_of_int (length typs) ^
    ", sorts: " ^ string_of_int (length sorts) ^ ", mismatches: " ^ string_of_int (! fails));
  val _ = \<^assert> (! fails = 0);
end
\<close>

end

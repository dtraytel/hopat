section \<open>Checking the Results of \<open>Thm.match\<close>\<close>

theory Match_Check
  imports "Pure_Pattern.Pure_Test_Support"
begin

text \<open>
  \<open>Thm.match\<close> and \<open>Thm.first_order_match\<close> belong to the kernel: they make certified types and
  terms from the instantiation that \<open>Pattern.match\<close> returns, without certifying them, and record
  the maximal index and the sorts of the object as theirs. \<open>Thm.instantiate\<close> relies on these
  records. This test checks, on patterns and objects from the theorems of HOL, what the kernel
  assumes of each instance: its term is well-typed and closed (it can be certified) and has the
  recorded type, the recorded maximal index bounds its indices, the instance of the pattern is
  the object modulo \<open>\<beta>\<eta>\<close>, and the sort hypotheses of a theorem instantiated with the result
  cover the sorts of its proposition.
\<close>

ML \<open>
local
  val thy = \<^theory>;
  val cert = Thm.global_cterm_of thy;
  fun freeze t =
    t |> Term.map_aterms (fn Var ((x, i), T) => Free (x ^ "_" ^ string_of_int i, T) | u => u)
      |> Term.map_types (Term.map_atyps (fn TVar ((a, i), S) => TFree (a ^ "_" ^ string_of_int i, S)
        | T => T));
  (*instances of the type variables only, with schematic variables left*)
  fun freezeT t =
    t |> Term.map_types (Term.map_atyps (fn TVar ((a, i), S) => TFree (a ^ "_" ^ string_of_int i, S)
        | T => T))
      |> Logic.incr_indexes ([], 2);
  fun subterms (t as u $ v) = t :: subterms u @ subterms v
    | subterms (t as Abs (_, _, b)) = t :: subterms b
    | subterms t = [t];
  fun closed_subterms t = filter_out Term.is_open (subterms t);
  fun head t = (case Term.head_of t of Const (c, _) => SOME c | _ => NONE);

  val props =
    Global_Theory.all_thms_of thy true |> map (Thm.prop_of o snd)
    |> filter (fn t => size_of_term t < 80) |> take 1500;
  (*patterns: propositions, their conclusions and the sides of equations*)
  fun parts t =
    let val c = Logic.strip_imp_concl t in
      t :: c ::
        (case try (HOLogic.dest_eq o HOLogic.dest_Trueprop) c of SOME (l, r) => [l, r] | NONE => []) @
        (case try Logic.dest_equals c of SOME (l, r) => [l, r] | NONE => [])
    end;
  val pats = maps parts props |> filter (fn t => not (Term.is_open t)) |> distinct (op aconv) |> take 3000;
  (*objects by their head constant*)
  val objs = maps (take 12 o closed_subterms o freeze) (take 800 props) @
    maps (take 6 o closed_subterms) (take 400 props);
  val tab = fold (fn t => (case head t of SOME c => Symtab.cons_list (c, t) | NONE => I)) objs Symtab.empty;
  fun problems p =
    (p, freeze p) :: (p, freezeT p) ::
      (case head p of SOME c => map (pair p) (take 4 (Symtab.lookup_list tab c)) | NONE => []);
  val probs = maps problems pats |> map_filter (fn (p, obj) => try (apply2 cert) (p, obj));

  val norm = Envir.beta_eta_contract;
  (*NONE: no match; SOME []: a result that passes; SOME msgs: a result with defects*)
  fun check match (cp, cobj) =
    (case try match (cp, cobj) of
      NONE => NONE
    | SOME (instT, inst) =>
        let
          val obj = Thm.term_of cobj;
          fun typ ((_, _), cT) =
            let val T = Thm.typ_of cT in
              [(can (Thm.global_ctyp_of thy) T, "type instance is not certifiable"),
               (Term.maxidx_of_typ T <= Thm.maxidx_of_ctyp cT, "maximal index of a type instance")]
            end;
          fun term ((_, T), ct) =
            let val t = Thm.term_of ct in
              [(can cert t, "instance is not certifiable"),
               (Thm.typ_of_cterm ct = T, "recorded type differs from the type of the variable"),
               (try fastype_of t = SOME T, "instance has another type"),
               (Term.maxidx_of_term t <= Thm.maxidx_of_cterm ct, "maximal index of an instance")]
            end;
          val inst_ok =
            (case try (Thm.instantiate_cterm (instT, inst)) cp of
              SOME cp' =>
                [(norm (Thm.term_of cp') aconv norm obj, "the instance of the pattern is not the object"),
                 (Term.maxidx_of_term (Thm.term_of cp') <= Thm.maxidx_of_cterm cp',
                    "maximal index of the instance of the pattern")]
            | NONE => [(false, "instantiate_cterm fails")]);
          val thm_ok =
            (case try (Thm.instantiate (instT, inst)) (Thm.reflexive cp) of
              SOME th =>
                [(subset (op =) (Sorts.insert_term (Thm.prop_of th) [], Thm.shyps_of th),
                    "sort of the instantiated theorem is no sort hypothesis"),
                 (Term.maxidx_of_term (Thm.prop_of th) <= Thm.maxidx_of th,
                    "maximal index of the instantiated theorem"),
                 (can cert (Thm.prop_of th), "instantiated theorem is not certifiable")]
            | NONE => [(false, "instantiate fails")]);
        in
          SOME (map #2 (filter_out #1
            (maps typ (TVars.dest instT) @ maps term (Vars.dest inst) @ inst_ok @ thm_ok)))
        end);
  fun run name match =
    let
      val rs = map (check match) probs;
      val matches = map_filter I rs;
      val bad = filter_out null matches;
    in (name, length rs, length matches, bad) end;
  val results = [run "match" Thm.match, run "first_order_match" Thm.first_order_match];
in
  val _ = results |> List.app (fn (name, n, m, bad) =>
    writeln (name ^ ": " ^ string_of_int n ^ " problems, " ^ string_of_int m ^ " matches, " ^
      string_of_int (length bad) ^ " with defects" ^
      (case bad of msgs :: _ => " (" ^ commas msgs ^ ")" | [] => "")));
  val _ = results |> List.app (fn (name, _, m, bad) =>
    if m = 0 then error ("No matches: " ^ name)
    else if not (null bad) then error ("Defects of the results of " ^ name)
    else ());
end
\<close>

end

section \<open>Testing the Generated Code of \<open>strip_shyps\<close>\<close>

theory Pure_Strip_Shyps_Test
  imports Pure_Proofterm_Test_Base
begin

text \<open>
  The generated code of theory \<^theory_text>\<open>Pure_Sorts\<close> is compared with \<open>Sorts.minimize_sort\<close>,
  \<open>Sorts.witness_sorts\<close> and \<open>Thm.strip_shyps\<close>: the sort hypotheses of the result, and the
  mapping of the types of classic and tight proofs. The theorems have additional sort hypotheses
  from hidden type variables (by \<open>forall_intr\<close> and \<open>forall_elim\<close> of a variable that does
  not occur in the proposition). The reference of the proof operations is the code of
  \<open>Thm.strip_shyps\<close>, applied to synthetic proofs with hidden types, including a type without
  replacement (\<open>Fail\<close>).
\<close>

ML \<open>
local
  structure G = Bicompose_Generated;
  val thy = \<^theory>;
  val algebra = Sign.classes_of thy;
  val gts = Sign.logical_types thy;
  val run = Proofterm_Test.run;
  val zrun = Proofterm_Test.zrun;
  (*the comparison of values by their string representation*)
  fun outcome f x =
    (case Exn.result (Timeout.apply (seconds 5.0) f) x of
      Exn.Res y => y
    | Exn.Exn exn => "EXN " ^ Bicompose_Test.exn_name exn);
  fun scompare name show f g xs : Proofterm_Test.report =
    let val results = map (fn x => (show x, outcome f x, outcome g x)) xs
    in {name = name, tests = length xs, mismatches = filter (fn (_, a, b) => a <> b) results} end;

  val sorts =
    [[], [\<^class>\<open>type\<close>], [\<^class>\<open>ord\<close>], [\<^class>\<open>linorder\<close>], [\<^class>\<open>ord\<close>, \<^class>\<open>plus\<close>],
     [\<^class>\<open>finite\<close>], [\<^class>\<open>semiring_char_0\<close>], [\<^class>\<open>field\<close>], [\<^class>\<open>linordered_field\<close>],
     [\<^class>\<open>equal\<close>], [\<^class>\<open>dense_linorder\<close>], [\<^class>\<open>order\<close>, \<^class>\<open>linorder\<close>],
     [\<^class>\<open>finite\<close>, \<^class>\<open>linorder\<close>], [\<^class>\<open>field\<close>, \<^class>\<open>finite\<close>]];

  (*minimize_sort*)
  val r_min = scompare "minimize_sort" \<^make_string>
    (\<^make_string> o Sorts.minimize_sort algebra) (\<^make_string> o G.minimize_sort algebra) sorts;

  (*witness_sorts: hypotheses of present type variables, and sorts*)
  val hyps_list = [[], [(TFree ("'a", [\<^class>\<open>ord\<close>]), [\<^class>\<open>ord\<close>])],
    [(TFree ("'a", [\<^class>\<open>field\<close>]), [\<^class>\<open>field\<close>]), (TVar (("'b", 0), [\<^class>\<open>finite\<close>]), [\<^class>\<open>finite\<close>])]];
  val wins = maps (fn hs => map (pair hs) (sorts :: map single sorts)) hyps_list;
  val r_wit = scompare "witness_sorts" \<^make_string>
    (fn (hs, ss) => \<^make_string> (Sorts.witness_sorts algebra gts hs ss))
    (fn (hs, ss) => \<^make_string> (G.witness_sorts algebra gts hs ss)) wins;

  (*theorems with hidden type variables of the given sorts*)
  fun hide (S, i) th =
    let
      val T = if i = 0 then TFree ("'h" ^ string_of_int i, S) else TVar (("'h", i), S);
      val x = Thm.global_cterm_of thy (Free ("hx" ^ string_of_int i, T));
      val t = Thm.global_cterm_of thy (if i = 0 then Free ("hy", T) else Var (("hy", i), T));
    in Thm.forall_elim t (Thm.forall_intr x th) end;
  val base = [@{thm refl}, @{thm conjI}, @{thm order_refl}, @{thm add.commute}, @{thm finite.emptyI},
    @{thm Suc_le_mono}, @{thm subset_refl}, Thm.assume (Thm.global_cterm_of thy \<^prop>\<open>(x::'a::ord) \<le> y\<close>)];
  val thms = base @
    maps (fn th => map (fn S => hide (S, 0) th) sorts) base @
    maps (fn th => map (fn (S1, S2) => hide (S2, 1) (hide (S1, 0) th))
      [([\<^class>\<open>field\<close>], [\<^class>\<open>linordered_field\<close>]), ([\<^class>\<open>dense_linorder\<close>], [\<^class>\<open>linorder\<close>]),
       ([\<^class>\<open>linordered_field\<close>], [\<^class>\<open>field\<close>, \<^class>\<open>dense_linorder\<close>]),
       ([\<^class>\<open>ord\<close>], [\<^class>\<open>field\<close>])]) base;
  fun show th = \<^make_string> (Thm.shyps_of th, Thm.full_prop_of th);
  fun data th =
    G.strip_shyps_rep algebra gts (Thm.shyps_of th) (Thm.hyps_of th) (Bicompose_Test.rep_of th);
  val r_shyps = scompare "strip_shyps (sort hypotheses)" show
    (fn th => \<^make_string> (Thm.shyps_of (Thm.strip_shyps th)))
    (fn th => \<^make_string> (case data th of NONE => Thm.shyps_of th | SOME d => G.sd_shyps d)) thms;
  val r_atyps = scompare "strip_shyps (present types)" show
    (fn th => \<^make_string> (Types.list_set (Types.build (Thm.fold_terms {hyps = true} Types.add_atyps th))))
    (fn th => \<^make_string> (G.thm_atyps (Thm.hyps_of th) (Thm.tpairs_of th) (Thm.prop_of th))) thms;

  (*the reference: map_atyp of Thm.strip_shyps*)
  fun map_atyp_of th =
    let
      val shyps = Thm.shyps_of th;
      val le = Sorts.sort_le algebra;
      fun lt (S1, S2) = le (S1, S2) andalso not (le (S2, S1));
      val present_set = Types.build (th |> Thm.fold_terms {hyps = true} Types.add_atyps);
      val {present, extra} = Logic.present_sorts shyps present_set;
      val (witnessed, non_witnessed) =
        Sign.witness_sorts thy present extra ||> map (`(Sorts.minimize_sort algebra));
      val extra' =
        non_witnessed |> map_filter (fn (S, _) =>
          if non_witnessed |> exists (fn (S', _) => lt (S', S)) then NONE else SOME S)
        |> Sorts.make;
      val types = present @ witnessed @ map (`Logic.dummy_tfree) extra';
      fun get_type S = types |> get_first (fn (T', S') => if le (S', S) then SOME T' else NONE);
    in
      Same.function_eq (op =) (fn T =>
        if Types.defined present_set T then raise Same.SAME
        else
          (case get_type (Type.sort_of_atyp T) of
            SOME T' => T'
          | NONE => raise Fail "strip_shyps: bad type variable in proof term"))
    end;

  (*synthetic proofs with hidden types: those of the theorem, and one without replacement*)
  val bad = TFree ("'bad", [\<^class>\<open>linordered_field\<close>, \<^class>\<open>finite\<close>]);
  fun hidden th = Thm.shyps_of th |> map_index (fn (i, S) => TFree ("'hidden" ^ string_of_int i, S));
  fun psynth b th =
    fold (fn T => fn p => Abst ("h", SOME T, p) % SOME (Free ("hz", T)))
      (hidden th @ (if b then [bad] else [])) (Proofterm_Test.synth th);
  fun zsynth b th =
    let
      val zT = map ZTerm.ztyp_of (hidden th @ (if b then [bad] else []));
      val p = Proofterm_Test.zsynth th;
    in
      fold (fn T => fn p =>
        ZTerm.ZAppps (ZAppt (ZAbst ("h", T, p), ZVar (("hz", ~1), T)),
          [OFCLASSp (T, \<^class>\<open>type\<close>), ZHyp (ZApp (ZConst1 ("hc", T), ZVar (("hz", 0), T)))])) zT p
    end;
  val pins = maps (fn th => [(false, th), (true, th)]) (filter (not o null o Thm.shyps_of) thms);
  fun pref (b, th) =
    ([], Proofterm.map_proof_types (Term.map_atyps_same (map_atyp_of th)) (psynth b th));
  fun pgen (b, th) = run (G.strip_shyps_proof algebra (data th) (psynth b th));
  val r_p = Proofterm_Test.compare "strip_shyps (proofs)" (show o snd) pref pgen pins;
  fun zref (b, th) =
    let
      val map_atyp = map_atyp_of th;
      val map_ztyp =
        ZTypes.apply_unsynchronized_cache
          (ZTerm.subst_type_same (ZTerm.ztyp_of o map_atyp o ZTerm.typ_of o ZTVar));
    in ([], ZTerm.beta_norm_prooft (ZTerm.map_proof_types {hyps = true} map_ztyp (zsynth b th))) end;
  fun zgen (b, th) = zrun (G.zstrip_shyps_proof algebra (data th) (zsynth b th));
  val r_z = Proofterm_Test.zcompare "strip_shyps (tight proofs)" (show o snd) zref zgen pins;
  val rs = [r_min, r_wit, r_shyps, r_atyps, r_p, r_z];
in
  val _ = writeln (cat_lines (map Proofterm_Test.report rs));
  val _ = Proofterm_Test.check rs;
end
\<close>

end

section \<open>Testing the Generated Code of \<open>unconstrainT\<close>\<close>

theory Pure_Unconstrain_Test
  imports Pure_Proofterm_Test_Base
begin

text \<open>
  The generated code of theory \<^theory_text>\<open>Pure_Unconstrain\<close> is compared with \<open>Thm.unconstrainT\<close>
  on theorems of HOL, also with hidden type variables of sorts that have witnesses and of a sort
  without witness (an extra sort hypothesis), and on theorems that it rejects: the logical part
  and the exceptions, the classic proof (with the header and body of the box of Isabelle), and
  the tight proof. Isabelle2026 has no patch \<open>zterm-unconstrain\<close>: the tight proof of the model
  is compared with its box (without the class proofs it is applied to), whose proposition
  differs if there is an extra sort hypothesis, and with the box of the proposition of the
  theorem, which the patch gives.
\<close>

class zbar = fixes zb :: 'a assumes zbar_neq: "zb \<noteq> zb"

ML \<open>
local
  structure G = Bicompose_Generated;
  val thy = \<^theory>;
  val ta = Proofterm_Test.ztypargs thy;
  val rep_of = Bicompose_Test.rep_of;
  fun outcome f x =
    (case Exn.result (Timeout.apply (seconds 10.0) f) x of
      Exn.Res y => y
    | Exn.Exn exn => "EXN " ^ Bicompose_Test.exn_name exn);
  fun scompare name show f g xs : Proofterm_Test.report =
    let val results = map (fn x => (show x, outcome f x, outcome g x)) xs
    in {name = name, tests = length xs, mismatches = filter (fn (_, a, b) => a <> b) results} end;
  fun with_proofs n f x =
    let
      val proofs = ! Proofterm.proofs;
      val _ = Proofterm.proofs := n;
      val r = Exn.result f x;
      val _ = Proofterm.proofs := proofs;
    in Exn.release r end;

  (*theorems: with hidden type variables, with an extra sort, rejected ones*)
  fun hide S th =
    let
      val x = Thm.global_cterm_of thy (Var (("hx", 7), TVar (("'h", 7), S)));
    in Thm.forall_elim x (Thm.forall_intr x th) end;
  val base = map (Thm.transfer thy)
    [@{thm refl}, @{thm conjI}, @{thm order_refl}, @{thm add.commute}, @{thm finite.emptyI},
     @{thm Suc_le_mono}, @{thm subset_refl}, @{thm mult.assoc}, @{thm le_less_trans},
     @{thm Groups.add_0}, @{thm list.map_comp}, @{thm card_mono}, @{thm TrueI}];
  val hidden = maps (fn th => [hide [\<^class>\<open>linorder\<close>] th, hide [\<^class>\<open>zbar\<close>] th]) base;
  val rejected =
    [Thm.assume (Thm.global_cterm_of thy \<^prop>\<open>(x::'a::ord) \<le> y\<close>),
     Thm.legacy_freezeT @{thm order_refl}, Thm.legacy_freezeT @{thm conjI}];
  val thms = base @ hidden @ rejected @
    map (Thm.transfer thy) (take 150 (map snd (Global_Theory.all_thms_of thy false)));

  (*the logical part*)
  fun isa_logic th =
    let val th' = with_proofs 0 Thm.unconstrainT th
    in \<^make_string> (Thm.prop_of th', Thm.maxidx_of th', Thm.shyps_of th', Thm.hyps_of th', Thm.tpairs_of th') end;
  fun model_logic th =
    let
      val th1 = Thm.strip_shyps th;
      val r = Bicompose_Test.run (Context.Theory thy) (th1, th1)
        (G.unconstrainT_rep Name.invent_global_types (Thm.shyps_of th1) (Thm.hyps_of th1) (rep_of th1));
    in \<^make_string> (G.th_prop r, G.th_maxidx r, [[]] : sort list, [] : term list, G.th_tpairs r) end;
  val r_logic = scompare "unconstrainT (logical part)" (Syntax.string_of_term_global thy o Thm.prop_of)
    isa_logic model_logic thms;

  (*the classic proof, with the header and body of the box of Isabelle*)
  val ok_thms = filter (can (with_proofs 0 Thm.unconstrainT)) thms;
  val proved = map (fn th => (th, with_proofs 2 Thm.unconstrainT th)) ok_thms;
  fun isa_proof (_, th') = Proofterm_Test.dump (Thm.proof_of th');
  fun model_proof (th, th') =
    let
      val th1 = Thm.strip_shyps th;
      val (PThm ({serial, command_pos, theory_name, thm_name, ...}, body), _) =
        Proofterm.strip_combt (Thm.proof_of th');
      fun box prop = (Proofterm.thm_header serial command_pos theory_name thm_name prop NONE, body);
    in
      (case G.unconstrain_thm_proof box Name.invent_global_types (Thm.shyps_of th1) (Thm.prop_of th1) of
        SOME (G.Ok p) => Proofterm_Test.dump p
      | SOME (G.Err exn) => Proofterm_Test.raise_exn exn
      | NONE => raise Fail "undefined result")
    end;
  val r_proof = scompare "unconstrainT (classic proofs)" (Syntax.string_of_term_global thy o Thm.prop_of o #1)
    isa_proof model_proof proved;

  (*the tight proof: the box of Isabelle without the class proofs, and the box of the proposition*)
  fun strip_args (ZAppp (p, OFCLASSp _)) = strip_args p
    | strip_args p = p;
  fun zname (ZConstp ((ZThm n, _), _)) = n
    | zname _ = raise Fail "no box";
  fun model_zproof th =
    let
      val th1 = Thm.strip_shyps th;
      val n = zname (strip_args (Thm.zproof_of (with_proofs 4 Thm.unconstrainT th)));
    in
      Proofterm_Test.zdump (#2 (Proofterm_Test.zrun
        (G.zunconstrain_proof ta n Name.invent_global_types (Thm.shyps_of th1) (Thm.prop_of th1))))
    end;
  fun isa_zproof th = Proofterm_Test.zdump (strip_args (Thm.zproof_of (with_proofs 4 Thm.unconstrainT th)));
  fun zprop (ZConstp ((_, A), _)) = A
    | zprop _ = raise Fail "no box";
  fun patched_zprop th = \<^make_string> (ZTerm.zterm_of thy (Thm.prop_of (with_proofs 4 Thm.unconstrainT th)));
  fun model_zprop th =
    let
      val th1 = Thm.strip_shyps th;
      val n = zname (strip_args (Thm.zproof_of (with_proofs 4 Thm.unconstrainT th)));
    in
      \<^make_string> (zprop (#2 (Proofterm_Test.zrun
        (G.zunconstrain_proof ta n Name.invent_global_types (Thm.shyps_of th1) (Thm.prop_of th1)))))
    end;
  fun extra th =
    let val present = Sorts.insert_term (Thm.prop_of th) []
    in exists (fn S => not (member (op =) present S)) (Thm.shyps_of (Thm.strip_shyps th)) end;
  val r_zproof = scompare "unconstrainT (tight proofs, without extra sorts)"
    (Syntax.string_of_term_global thy o Thm.prop_of) isa_zproof model_zproof (filter_out extra ok_thms);
  val r_zproof' = scompare "unconstrainT (tight proofs, patched: the proposition of the box)"
    (Syntax.string_of_term_global thy o Thm.prop_of) patched_zprop model_zprop ok_thms;
  val n_extra = length (filter extra ok_thms);
in
  val _ = writeln (cat_lines (map Proofterm_Test.report [r_logic, r_proof, r_zproof, r_zproof']) ^
    "\n(theorems with an extra sort hypothesis: " ^ string_of_int n_extra ^ ")");
  val _ = Proofterm_Test.check [r_logic, r_proof, r_zproof, r_zproof'];
end
\<close>

end

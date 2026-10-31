section \<open>Theorems with proofs\<close>

theory Thm_Proof
  imports Proof_Bicompose
begin

text \<open>
  The proofs of the theorems of the model (theory \<open>Thm_Type\<close>) are kept with an invariant
  (@{const prf_wf_csig.thm_prf_inv}): they have no schematic variables, are valid modulo the
  flex-flex pairs, and their terms and types can be normalized. Biresolution lifts the proof of
  the rule (\<open>Proofterm.lift_proof\<close>), renames it as the new premises, and composes it with the
  proof of the proof state (\<open>Proofterm.bicompose_proof\<close>); this never warns or raises an
  exception, and the result satisfies the invariant again.
\<close>

context prf_wf_csig
begin

subsection \<open>Hypotheses\<close>

lemma prf_ok_mono_H: "prf_ok V H Ts Hs p \<phi> \<Longrightarrow> H \<subseteq> H' \<Longrightarrow> prf_ok V H' Ts Hs p \<phi>"
  by (induction rule: prf_ok.induct) (auto intro: prf_ok.intros)

lemma prf_valid_mono_H: "prf_valid alg ar W H tps p P \<Longrightarrow> H \<subseteq> H' \<Longrightarrow> prf_valid alg ar W H' tps p P"
  unfolding prf_valid_def by (blast intro: prf_ok_mono_H)


subsection \<open>Proofs of lifted rules\<close>

lemma prf_vars_prf_all: "prf_vars p = {} \<longleftrightarrow> prf_all (\<lambda>t. vars t = {}) (\<lambda>_. True) p"
proof (induction p)
  case (PThm x)
  then show ?case by (cases x) simp
qed (auto split: option.splits)

lemma remove_types_map_types:
  "f dummyT = dummyT \<Longrightarrow> remove_types (map_types f t) = map_types f (remove_types t)"
  by (induction t) simp_all

definition incrA :: "integer \<Rightarrow> (indexname \<times> psort) set \<Rightarrow> (indexname \<times> psort) set" where
  "incrA inc A = (\<lambda>(v, S). (incr_ix inc v, S)) ` A"

lemma ann0_incr:
  assumes "ann0 A t"
  shows "ann0 (incrA inc A) (map_types (incr_tvar inc) t)"
proof -
  from assms obtain t0 Ts T where rt: "remove_types t = remove_types t0"
    and ht: "has_type (\<lambda>_. propT) Ts t0 T" and v: "vars t0 = {}" and tA: "\<forall>U\<in>set Ts \<union> tys t0. tyA ar A U"
    and tt: "\<forall>U\<in>tys t. tvars U \<subseteq> A"
    by (auto simp: ann0_def)
  have lv: "lift_venv [] inc (\<lambda>_. propT) (\<lambda>_. propT)" by (simp add: lift_venv_def)
  from has_type_incr_idx[OF ht lv] v
  have "has_type (\<lambda>_. propT) (map (incr_tvar inc) Ts) (map_types (incr_tvar inc) t0) (incr_tvar inc T)"
    by (simp add: incr_idx_no_vars)
  moreover have "remove_types (map_types (incr_tvar inc) t) = remove_types (map_types (incr_tvar inc) t0)"
    using rt by (simp add: remove_types_map_types dummyT_def)
  moreover have "\<forall>U\<in>set (map (incr_tvar inc) Ts) \<union> tys (map_types (incr_tvar inc) t0). tyA ar (incrA inc A) U"
    using tA tyA_incr_tvar by (auto simp: tys_map_types incrA_def)
  moreover have "\<forall>U\<in>tys (map_types (incr_tvar inc) t). tvars U \<subseteq> incrA inc A"
    using tt by (simp add: tys_map_types tvars_incr_tvar incrA_def) (blast intro: image_mono)
  ultimately show ?thesis using v unfolding ann0_def by fastforce
qed

lemma prf_all_lift_prf:
  assumes "prf_all P Q p" "prf_vars p = {}"
    and "\<And>t. P t \<Longrightarrow> vars t = {} \<Longrightarrow> P' (map_types (incr_tvar inc) t)" and "\<And>U. Q U \<Longrightarrow> Q' (incr_tvar inc U)"
  shows "prf_all P' Q' (lift_prf inc Ts lev p)"
  using assms(1,2)
proof (induction p arbitrary: lev)
  case (PThm x)
  then show ?case using assms(4) by (cases x) (auto simp: hd_set_types_simps)
qed (use assms(3,4) in \<open>auto simp: incr_idx_no_vars split: option.splits\<close>)

lemma prf_all_foldr_mk_app:
  assumes "prf_all P Q p" "\<And>x. 0 \<le> x \<Longrightarrow> P (Bound x)"
  shows "integer_of_nat (length (filter Not bs)) \<le> b + 1 \<Longrightarrow> prf_all P Q (snd (snd (foldr mk_app bs (a, b, p))))"
proof (induction bs)
  case Nil
  then show ?case using assms(1) by (simp add: mk_app_def)
next
  case (Cons x bs)
  have "integer_of_nat (length (filter Not bs)) \<le> b + 1"
    using Cons.prems by (cases x) (auto simp: integer_of_nat_Suc)
  note IH = Cons.IH[OF this]
  show ?case
  proof (cases x)
    case False
    then have "0 \<le> b - integer_of_nat (length (filter Not bs))" using Cons.prems by (simp add: integer_of_nat_Suc)
    then show ?thesis unfolding foldr_mk_app_Cons using IH assms(2) False by simp
  next
    case True
    show ?thesis unfolding foldr_mk_app_Cons using IH True by simp
  qed
qed

lemma prf_all_lift_prems:
  assumes "\<And>x. 0 \<le> x \<Longrightarrow> P (Bound x)"
  shows "(\<And>Ts'. prf_all P Q (lift_prf inc Ts' 0 pf)) \<Longrightarrow> j = integer_of_nat (length (filter Not bs)) \<Longrightarrow>
    prf_all P Q (lift_prems inc k pf Ts bs i j G)"
proof (induction inc k pf Ts bs i j G rule: lift_prems.induct)
  case (1 inc k pf Ts bs i j c U A B)
  then show ?case
    by (auto simp: prf_all_proof_combP integer_of_nat_Suc intro!: prf_all_foldr_mk_app assms)
next
  case (2 inc k pf Ts bs i j c U a T t)
  then show ?case
    by (auto simp: prf_all_proof_combP integer_of_nat_Suc intro!: prf_all_foldr_mk_app assms)
qed (auto simp: prf_all_proof_combP intro!: prf_all_foldr_mk_app assms)

lemma prf_all_lift_proof:
  assumes "\<And>Ts'. prf_all P Q (lift_prf inc Ts' 0 pf)" "\<And>x. 0 \<le> x \<Longrightarrow> P (Bound x)"
  shows "prf_all P Q (lift_proof G inc As pf)"
proof -
  have z: "(0::integer) = integer_of_nat (length (filter Not ([]::bool list)))"
    using Code_Numeral.integer_of_nat_0 by simp
  show ?thesis unfolding lift_proof_def prf_all_mk_AbsP by (rule prf_all_lift_prems[OF assms(2) assms(1) z])
qed

text \<open>The parameters of the subgoal, as \<open>lift_proof\<close> collects them.\<close>

lemma lift_Ts_lsplit: "lsplit G = (p, G0) \<Longrightarrow> lift_Ts Ts G = rev (Bicompose_Typing.csig.ptys p) @ Ts"
proof (induction G arbitrary: p G0 Ts rule: lsplit.induct)
  case (1 t)
  show ?case
  proof (cases "dest_imp t")
    case (Some HB)
    then obtain H B U where t: "t = Const STR ''Pure.imp'' U $ H $ B" and d: "dest_imp t = Some (H, B)"
      by (cases HB) (auto simp: dest_imp_Some)
    obtain p' t0 where ls: "lsplit B = (p', t0)" by (cases "lsplit B")
    with "1.prems" d have p: "p = LImp (fun_of (fun_of t)) H # p'" by (simp add: lsplit.simps[of t])
    from "1.IH"(2)[OF d HOL.refl ls] t p show ?thesis by simp
  next
    case None
    show ?thesis
    proof (cases "dest_all t")
      case (Some aTb)
      then obtain a T b U where t: "t = Const STR ''Pure.all'' U $ Abs a T b" and d: "dest_all t = Some (a, T, b)"
        by (cases aTb; cases t rule: dest_all.cases) (auto split: if_splits)
      obtain p' t0 where ls: "lsplit b = (p', t0)" by (cases "lsplit b")
      with "1.prems" None d have p: "p = LAll (fun_of t) a T # p'" by (simp add: lsplit.simps[of t])
      from "1.IH"(1)[OF None d HOL.refl HOL.refl ls, of "T # Ts"] t p show ?thesis by simp
    next
      case None': None
      with "1.prems" None have "p = []" by (simp add: lsplit.simps[of t])
      moreover have "lift_Ts Ts t = Ts"
        using None None' by (cases "(Ts, t)" rule: lift_Ts.cases) (auto split: if_splits)
      ultimately show ?thesis by simp
    qed
  qed
qed

text \<open>
  The hypotheses of theorems have no schematic variables, no type variables and no loose bound
  variables.
\<close>

lemma psubst_ground: "vars t = {} \<Longrightarrow> \<forall>U\<in>tys t. tvars U = {} \<Longrightarrow> psubst \<rho> \<theta> lev t = t"
  by (induction t arbitrary: lev) (auto simp: tsubst_no_tvars')

lemma hyp_ok_props:
  assumes "hyp_ok ar h"
  shows "vars h = {}" "\<forall>U\<in>tys h. tvars U = {}" "\<not> loose_bvar h 0"
proof -
  from assms have v: "vars h = {}" and w: "wt_term ar {} (\<lambda>_. propT) (-1) h propT"
    by (auto simp: hyp_ok_def)
  show "vars h = {}" by (rule v)
  show "\<forall>U\<in>tys h. tvars U = {}" using w by (auto simp: wt_term_def tyA_def)
  have ht: "has_type (\<lambda>_. propT) [] h propT" using w by (simp add: wt_term_def)
  show "\<not> loose_bvar h 0" using has_type_loose_bvar[OF ht] by simp
qed


subsection \<open>Composition\<close>

text \<open>
  The proof of a result of \<^const>\<open>biresolution\<close>: the proof of the rule, lifted over the subgoal
  and renamed as the new premises, composed with the proof of the proof state. If the proofs of
  the proof state and the rule satisfy the invariant, its computation returns without warnings
  or exceptions, and it satisfies the invariant with the hypotheses of both.
\<close>

theorem biresolution_prf_inv:
  assumes br: "okT (biresolution trace match_flg rep brules i state) s0"
    and res: "brresult (unify_ops cfg vl) alg rep s0 (x, (eres_flg, rule))"
    and cfg: "cfg_alg cfg = alg" and vl: "\<And>xs. length (vl xs) = length xs"
    and d: "okT (dest_state state i) (stpairs, Bs, Bi, C)"
    and st: "thm_typeds ar 0 \<Sigma>s state" and ru: "thm_typeds ar 0 \<Sigma>r (rep rule)"
    and si: "thm_prf_inv (th_maxidx state) (th_tpairs state) (th_prop state) Hs sprf"
    and ri: "thm_prf_inv (th_maxidx (rep rule)) (th_tpairs (rep rule)) (th_prop (rep rule)) Hr rprf"
    and hs: "\<forall>h\<in>Hr. hyp_ok ar h"
  defines "inc \<equiv> th_maxidx state + 1"
  shows "\<exists>p. bicompose_proof (br_env x) (th_maxidx state) True Bs (na_As (br_newas x)) (br_A x)
      (na_oldAs (br_newas x)) (na_n (br_newas x)) (count_prems (strip_all_body Bi) + (if eres_flg then -1 else 0) + 1)
      (ren_prf (na_ren (br_newas x)) (lift_proof Bi inc (map (lift_all inc Bi) (strip_imp_prems (th_prop (rep rule)))) rprf))
      sprf = returnP p \<and> thm_prf_inv (maxidx (br_env x)) (br_tpairs x) (br_prop x) (Hs \<union> Hr) p"
proof -
  from br res obtain stpairs' Bs' Bi' C' goal where d': "okT (dest_state state i) (stpairs', Bs', Bi', C')"
    and g: "okT (cprem_of state i) goal" and r: "(eres_flg, rule) \<in> set brules"
    and xq: "\<exists>xq0. okT (bicompose_aux (unify_ops cfg vl) alg True match_flg True (pthm_of state)
      (stpairs', Bs', Bi', C') True eres_flg (pthm_of (lift_rule goal (th_maxidx state) (rep rule)))
      (nprems_of (rep rule))) xq0 \<and> bresult (unify_ops cfg vl) xq0 x"
    by (rule biresolution_result)
  from okT_det[OF d d'] have e: "stpairs' = stpairs" "Bs' = Bs" "Bi' = Bi" "C' = C" by simp_all
  let ?smax = "th_maxidx state" and ?R = "rep rule"
  let ?lr = "lift_rule goal ?smax ?R"
  from si obtain As Ws where As: "finite As" "scons As" "tcert alg As"
    "\<forall>q\<in>As. 0 \<le> snd (fst q) \<and> snd (fst q) \<le> ?smax" "\<forall>x. tyA ar As (Ws x)"
    and wS: "wt_thm ar As Ws ?smax (th_tpairs state) (th_prop state)"
    and sv0: "prf_valid alg ar Ws Hs (th_tpairs state) sprf (th_prop state)"
    and sw0: "prf_all (ann0 As) (tyA ar As) sprf" and sp0: "prf_vars sprf = {}"
    by (auto simp: thm_prf_inv_def)
  from ri obtain Ar Wr where Ar: "finite Ar" "scons Ar" "tcert alg Ar"
    "\<forall>q\<in>Ar. 0 \<le> snd (fst q) \<and> snd (fst q) \<le> th_maxidx ?R" "\<forall>x. tyA ar Ar (Wr x)"
    and wR: "wt_thm ar Ar Wr (th_maxidx ?R) (th_tpairs ?R) (th_prop ?R)"
    and rv0: "prf_valid alg ar Wr Hr (th_tpairs ?R) rprf (th_prop ?R)"
    and rw0: "prf_all (ann0 Ar) (tyA ar Ar) rprf" and rp0: "prf_vars rprf = {}"
    by (auto simp: thm_prf_inv_def)
  from st have sm: "-1 \<le> ?smax" and Slo: "\<forall>x\<in>vars_thm (th_tpairs state) (th_prop state). 0 \<le> snd x"
    by (auto simp: thm_typeds_def)
  from ru have nn: "\<forall>x\<in>vars_thm (th_tpairs ?R) (th_prop ?R). 0 \<le> snd x" and rm: "-1 \<le> th_maxidx ?R"
    by (auto simp: thm_typeds_def)
  have Asb: "\<forall>p\<in>As. snd (fst p) \<le> ?smax" "\<forall>p\<in>As. 0 \<le> snd (fst p)" using As(4) by auto
  define A where "A = As \<union> (\<lambda>(v, S). (incr_ix (?smax + 1) v, S)) ` Ar"
  define W where "W = (\<lambda>x. if snd x \<le> ?smax then Ws x
      else foldr fun_type (Bicompose_Typing.csig.ptys (fst (lsplit Bi)))
        (incr_tvar (?smax + 1) (Wr (fst x, snd x - (?smax + 1)))))"
  note ct = compose_typed_explicit[OF d g As(1,2) Asb(1) As(5) wS sm Asb(2) Slo Ar(1,2,4,5) wR nn rm]
  have c: "finite A" "scons A" "\<forall>p\<in>A. snd (fst p) \<le> max (th_maxidx ?lr) ?smax"
    "\<forall>x. tyA ar A (W x)"
    "wt_thm ar A W ?smax stpairs (list_implies (Bs @ [Bi]) C)"
    "ibelow ?smax (list_implies (Bs @ [Bi]) C)"
    "wt_thm ar A W (th_maxidx ?lr) (th_tpairs ?lr) (th_prop ?lr)"
    "lifted_over ?smax Bi (th_prop ?lr) (nprems_of ?R)"
    "th_tpairs state = stpairs" "th_prop state = list_implies (Bs @ [Bi]) C" "goal = Bi"
    "-1 \<le> th_maxidx ?lr"
    "(0::integer) \<le> 0 \<Longrightarrow> \<forall>p\<in>A. 0 \<le> snd (fst p)"
    "(0::integer) \<le> 0 \<Longrightarrow> \<forall>x\<in>vars_thm stpairs (list_implies (Bs @ [Bi]) C) \<union> vars_thm (th_tpairs ?lr) (th_prop ?lr).
      0 \<le> snd x"
    unfolding A_def W_def by (rule ct; assumption)+
  have A0: "\<forall>p\<in>A. 0 \<le> snd (fst p)" and nnc: "\<forall>x\<in>vars_thm stpairs (list_implies (Bs @ [Bi]) C) \<union>
      vars_thm (th_tpairs ?lr) (th_prop ?lr). 0 \<le> snd x"
    using c(13,14) by simp_all
  have cA: "tcert alg A" using As(3) Ar(3) by (auto simp: A_def tcert_def)
  from xq obtain xq0 where ok: "okT (bicompose_aux (unify_ops cfg vl) alg True match_flg True
      (?smax, stpairs, list_implies (Bs @ [Bi]) C) (stpairs, Bs, Bi, C) True eres_flg
      (th_maxidx ?lr, th_tpairs ?lr, th_prop ?lr) (nprems_of ?R)) xq0"
    and rx: "bresult (unify_ops cfg vl) xq0 x"
    using c(9,10) e by (auto simp: pthm_of_def)
  have ns: "0 \<le> nprems_of ?R" "nprems_of ?R \<le> count_prems (th_prop ?lr)"
    using count_prems_nonneg nprems_lift_rule by (auto simp: nprems_of_def)
  have er: "0 < nprems_of ?R" if eres_flg
  proof (rule ccontr)
    assume "\<not> 0 < nprems_of ?R"
    with ns(1) have "nprems_of ?R = 0" by simp
    with ok that bicompose_aux_eres_no_prems show False by fastforce
  qed
  text \<open>The proofs with the common typing.\<close>
  have imp: "tyA ar A imp_type" using c(5) by (auto simp: wt_thm_def wt_term_def tys_list_implies)
  then have wfp: "wft ar propT" by (simp add: tyA_def imp_type_def)
  have sv: "prf_valid alg ar W (Hs \<union> Hr) stpairs sprf (list_implies (Bs @ [Bi]) C)"
  proof (rule prf_valid_mono_H[OF prf_valid_cong])
    show "prf_valid alg ar Ws Hs stpairs sprf (list_implies (Bs @ [Bi]) C)" using sv0 c(9,10) by simp
    show "\<forall>x\<in>vars_thm stpairs (list_implies (Bs @ [Bi]) C). W x = Ws x"
      using wt_thm_below[OF wS] c(9,10) by (auto simp: W_def)
  qed (use sp0 in auto)
  let ?As = "strip_imp_prems (th_prop ?R)" and ?B = "strip_imp_concl (th_prop ?R)"
  let ?rprf = "lift_proof Bi inc (map (lift_all inc Bi) ?As) rprf"
  have cR: "cok (th_prop ?R)" using wR by (simp add: wt_thm_def)
  have PR: "th_prop ?R = list_implies ?As ?B" by (rule list_implies_strip_imp[OF cR])
  have rv: "prf_valid alg ar W (Hs \<union> Hr) (th_tpairs ?lr) ?rprf (th_prop ?lr)"
  proof -
    have Hc: "\<forall>h\<in>Hr. vars h = {} \<and> (\<forall>U\<in>tys h. tvars U = {}) \<and> \<not> loose_bvar h 0"
      using hs hyp_ok_props by blast
    have inc0: "0 \<le> inc" using sm by (simp add: inc_def)
    have P: "prf_valid alg ar Wr Hr (th_tpairs ?R) rprf (list_implies ?As ?B)" using rv0 PR by simp
    have tps: "\<forall>(t, u)\<in>set (th_tpairs ?R). \<exists>T. wty Wr [] t T \<and> wty Wr [] u T"
    proof (intro ballI, clarify)
      fix t u assume tu: "(t, u) \<in> set (th_tpairs ?R)"
      from wR tu obtain T where "wt_term ar Ar Wr (th_maxidx ?R) t T" "wt_term ar Ar Wr (th_maxidx ?R) u T"
        by (auto simp: wt_thm_def)
      moreover have "\<forall>v\<in>vars t. 0 \<le> snd v" "\<forall>v\<in>vars u. 0 \<le> snd v"
        using nn tu by (auto simp: vars_thm_def)
      ultimately show "\<exists>T. wty Wr [] t T \<and> wty Wr [] u T" by (auto simp: wt_term_def wty_def)
    qed
    have wRp: "wty Wr [] (list_implies ?As ?B) propT"
      using wR nn PR by (auto simp: wt_thm_def wt_term_def wty_def vars_thm_def)
    have wBi: "wt_term ar A W ?smax Bi propT"
      using wt_term_list_implies(1)[of ar A W ?smax "Bs @ [Bi]" C] c(5) by (simp add: wt_thm_def)
    have G: "wty W [] Bi propT"
      using wBi Slo c(10) by (auto simp: wt_term_def wty_def vars_thm_def vars_list_implies)
    obtain p G0 where ls: "lsplit Bi = (p, G0)" by (cases "lsplit Bi")
    have V2: "lift_venv (rev (lift_Ts [] Bi)) inc Wr W"
      unfolding lift_venv_def lift_Ts_lsplit[OF ls] using sm
      by (auto simp: W_def ls inc_def)
    from prf_valid_lift[OF Hc inc0 P tps wRp G V2]
    have "prf_valid alg ar W Hr (th_tpairs ?lr) ?rprf (th_prop ?lr)"
      using c(11) by (simp add: lift_rule_def Let_def inc_def)
    then show ?thesis by (rule prf_valid_mono_H) blast
  qed
  have rp0': "prf_vars ?rprf = {}"
    unfolding prf_vars_prf_all
    by (rule prf_all_lift_proof[OF prf_all_lift_prf[OF rp0[unfolded prf_vars_prf_all] rp0]]) simp_all
  have sw: "prf_all (\<lambda>t. ann0 A t \<and> (\<forall>U\<in>tys t. \<forall>(v, S)\<in>tvars U. snd v \<le> ?smax))
      (\<lambda>U. tyA ar A U \<and> (\<forall>(v, S)\<in>tvars U. snd v \<le> ?smax)) sprf"
  proof (rule prf_all_mono[OF sw0])
    fix t assume a: "ann0 As t"
    have "As \<subseteq> A" by (simp add: A_def)
    with a have "ann0 A t" by (rule ann0_mono)
    moreover have "\<forall>U\<in>tys t. \<forall>(v, S)\<in>tvars U. snd v \<le> ?smax"
    proof (intro ballI, clarify)
      fix U v S assume "U \<in> tys t" "(v, S) \<in> tvars U"
      with a have "(v, S) \<in> As" by (auto simp: ann0_def)
      with Asb(1) show "snd v \<le> ?smax" by auto
    qed
    ultimately show "ann0 A t \<and> (\<forall>U\<in>tys t. \<forall>(v, S)\<in>tvars U. snd v \<le> ?smax)" by blast
  next
    fix U assume "tyA ar As U"
    then show "tyA ar A U \<and> (\<forall>(v, S)\<in>tvars U. snd v \<le> ?smax)"
      using Asb(1) by (fastforce simp: tyA_def A_def)
  qed
  have rw: "prf_all (ann0 A) (tyA ar A) ?rprf"
  proof (rule prf_all_lift_proof)
    have iA: "incrA inc Ar \<subseteq> A" by (auto simp: incrA_def A_def inc_def)
    show "prf_all (ann0 A) (tyA ar A) (lift_prf inc Ts' 0 rprf)" for Ts'
    proof (rule prf_all_lift_prf[OF rw0 rp0])
      show "ann0 A (map_types (incr_tvar inc) t)" if "ann0 Ar t" for t
        by (rule ann0_mono[OF ann0_incr[OF that] iA])
      show "tyA ar A (incr_tvar inc U)" if "tyA ar Ar U" for U
        using tyA_mono[OF tyA_incr_tvar[OF that] iA[unfolded incrA_def]] .
    qed
    show "ann0 A (Bound j)" if "0 \<le> j" for j by (rule ann0_Bound[OF that wfp])
  qed
  have "\<exists>p. bicompose_proof (br_env x) ?smax True Bs (na_As (br_newas x)) (br_A x) (na_oldAs (br_newas x))
      (na_n (br_newas x)) (count_prems (strip_all_body Bi) + (if eres_flg then -1 else 0) + 1)
      (ren_prf (na_ren (br_newas x)) ?rprf) sprf = returnP p \<and>
    thm_prf_inv (maxidx (br_env x)) (br_tpairs x) (br_prop x) (Hs \<union> Hr) p"
    by (rule bicompose_proof_valid[OF ok rx cfg c(1) c(5,6) c(7) _ c(2) _ c(4) ns er _ vl cA sm A0 nnc sv rv sp0 rp0' sw rw])
      (use c(3,8) in auto)
  then show ?thesis by (simp add: inc_def)
qed

end


subsection \<open>Theorems of the model with proofs\<close>

text \<open>
  A theorem of the model with its (classic) proof term. The judgment on proofs is parametric in
  the propositions of axioms, oracles and theorems (@{const prf_csig.atom_prop}); since the
  theorems are built by \<open>Thm.trivial\<close>, \<open>Thm.assume\<close> and biresolution only, their proofs are
  valid for every choice of them.
\<close>

record thm_prf = thm_cert +
  th_proof :: "prf"

definition prf_thm_ok :: "thm_prf \<Rightarrow> bool" where
  "prf_thm_ok th \<longleftrightarrow> thm_ok (thm_cert.truncate th) \<and>
    (\<forall>ac aty. prf_wf_csig ac aty (sg_alg (th_cert th)) (sg_ar (th_cert th)) \<longrightarrow>
      prf_wf_csig.thm_prf_inv (sg_consts (th_cert th)) ac aty (sg_alg (th_cert th)) (sg_ar (th_cert th))
        (th_maxidx th) (th_tpairs th) (th_prop th) (set (th_hyps th)) (th_proof th))"

text \<open>\<open>Thm.trivial\<close> with the proof \<open>\<^bold>\<lambda>H. H\<close>.\<close>

definition trivial_prf_thm :: thm_prf where
  "trivial_prf_thm = thm_cert.extend trivial_thm (thm_prf.fields (AbsP (STR ''H'') None (PBound 0)))"

lemma prf_thm_ok_trivial: "prf_thm_ok trivial_prf_thm"
proof -
  let ?A = "Var (STR ''A'', 0) propT" and ?ar = "\<lambda>_ :: name. 0 :: nat" and ?ct = "\<lambda>_ :: name. None :: ptyp option"
  have "prf_wf_csig.thm_prf_inv ?ct ac aty undefined ?ar 0 [] (implies $ ?A $ ?A) {} (AbsP (STR ''H'') None (PBound 0))"
    if "prf_wf_csig ac aty undefined ?ar" for ac aty
  proof -
    interpret prf_wf_csig ?ct ac aty undefined ?ar by fact
    have wp: "wft ?ar propT" "wft ?ar imp_type" by (simp_all add: propT_def imp_type_def tarity_def)
    have h: "has_type (\<lambda>_. propT) [] (implies $ ?A $ ?A) propT"
      by (simp add: has_type_implies has_type.Var)
    have ty: "tys (implies $ ?A $ ?A) = {imp_type, propT}" by (auto simp: implies_imp_type)
    then have w: "wt_term ?ar {} (\<lambda>_. propT) 0 (implies $ ?A $ ?A) propT"
      using h wp by (simp add: wt_term_def swf_tm_def implies_imp_type below_def tyA_def imp_type_def propT_def)
    have wt: "wt_thm ?ar {} (\<lambda>_. propT) 0 [] (implies $ ?A $ ?A)"
      using w has_type_cok[OF h] by (simp add: wt_thm_def)
    have v: "prf_valid undefined ?ar (\<lambda>_. propT) {} [] (AbsP (STR ''H'') None (PBound 0)) (implies $ ?A $ ?A)"
      unfolding prf_valid_def
    proof (intro allI impI)
      fix V' \<rho> \<theta> assume ty: "inst_typed (\<lambda>_. propT) V' [] \<rho> \<theta>"
      have a: "wty V' [] (\<theta> (STR ''A'', 0)) propT" using inst_typedD[OF ty, of "(STR ''A'', 0)"] by simp
      have "prf_ok V' {} [] [\<theta> (STR ''A'', 0)] (PBound 0) (\<theta> (STR ''A'', 0))"
        using prf_ok.PBound[of 0 "[\<theta> (STR ''A'', 0)]" V' "[]" "{}"] a by simp
      then have "prf_ok V' {} [] [] (AbsP (STR ''H'') None (PBound 0)) (implies $ \<theta> (STR ''A'', 0) $ \<theta> (STR ''A'', 0))"
        using a by (intro prf_ok.AbsP) simp_all
      then show "prf_ok V' {} [] [] (prf_inst \<rho> \<theta> 0 (AbsP (STR ''H'') None (PBound 0)))
          (psubst \<rho> \<theta> 0 (implies $ ?A $ ?A))"
        by (simp add: implies_def imp_type_def propT_def incr_boundvars_def)
    qed
    show ?thesis unfolding thm_prf_inv_def
      by (intro conjI exI[of _ "{}"] exI[of _ "\<lambda>_. propT"])
        (use wt v wp in \<open>simp_all add: scons_def tcert_def tyA_def propT_def\<close>)
  qed
  then show ?thesis using thm_ok_trivial
    by (simp add: prf_thm_ok_def trivial_prf_thm_def trivial_thm_def thm_cert.defs thm_prf.defs)
qed

typedef (overloaded) prf_thm = "{th. prf_thm_ok th}"
  morphisms rep_prf_thm Abs_prf_thm
  using prf_thm_ok_trivial by blast

abbreviation prf_rep_of :: "prf_thm \<Rightarrow> thm_rep" where
  "prf_rep_of th \<equiv> thm_rep.truncate (rep_prf_thm th)"

abbreviation prf_cert_of :: "prf_thm \<Rightarrow> sign" where
  "prf_cert_of th \<equiv> th_cert (rep_prf_thm th)"

abbreviation proof_of :: "prf_thm \<Rightarrow> prf" where
  "proof_of th \<equiv> th_proof (rep_prf_thm th)"

text \<open>\<open>Thm.assume\<close> with the proof \<open>Hyp A\<close>.\<close>

definition assume_prf_thm :: "sign \<Rightarrow> pterm \<Rightarrow> thm_prf" where
  "assume_prf_thm c A = thm_cert.extend (assume_thm c A) (thm_prf.fields (Hyp A))"

lemma prf_thm_ok_assume:
  assumes A: "csig.hyp_ok (sg_consts c) (sg_ar c) A"
  shows "prf_thm_ok (assume_prf_thm c A)"
proof -
  obtain alg ar ct where c: "c = \<lparr>sg_alg = alg, sg_ar = ar, sg_consts = ct\<rparr>" by (cases c) auto
  have "prf_wf_csig.thm_prf_inv ct ac aty alg ar (-1) [] A {A} (Hyp A)" if "prf_wf_csig ac aty alg ar" for ac aty
  proof -
    interpret prf_wf_csig ct ac aty alg ar by fact
    from A have hA: "hyp_ok ar A" by (simp add: c)
    then have v: "vars A = {}" and w: "wt_term ar {} (\<lambda>_. propT) (-1) A propT" and cA: "cok A"
      by (auto simp: hyp_ok_def)
    note hp = hyp_ok_props[OF hA]
    have wp: "wft ar propT"
      using w by (intro has_type_wft[of "\<lambda>_. propT" "[]" A]) (auto simp: wt_term_def tyA_def)
    have "prf_valid alg ar (\<lambda>_. propT) {A} [] (Hyp A) A"
      unfolding prf_valid_def
    proof (intro allI impI)
      fix V' \<rho> \<theta>
      have "has_type V' [] A propT" using w v by (auto simp: wt_term_def intro: has_type_vars)
      then have "prf_ok V' {A} [] [] (Hyp A) A" using v by (intro prf_ok.Hyp) (simp_all add: wty_def)
      then show "prf_ok V' {A} [] [] (prf_inst \<rho> \<theta> 0 (Hyp A)) (psubst \<rho> \<theta> 0 A)"
        using psubst_ground[OF hp(1,2)] by simp
    qed
    then show ?thesis unfolding thm_prf_inv_def
      by (intro conjI exI[of _ "{}"] exI[of _ "\<lambda>_. propT"])
        (use w cA wp in \<open>simp_all add: scons_def tcert_def tyA_def wt_thm_def propT_def\<close>)
  qed
  then show ?thesis using thm_ok_assume[OF A]
    by (simp add: prf_thm_ok_def assume_prf_thm_def assume_thm_def thm_cert.defs thm_prf.defs c)
qed

subsection \<open>Biresolution of theorems with proofs\<close>

text \<open>
  The proof of a new theorem: the proof term that \<open>Thm.bicompose_aux\<close> builds
  (\<open>Proofterm.bicompose_proof\<close> applied to the lifted proof of the rule, renamed as the new
  premises, and the proof of the proof state). The value of a computation of the proof is its
  result if it returns; it always returns, without warnings (theorem
  \<open>biresolution_prf_thms_results\<close> below).
\<close>

definition val_P :: "prf P \<Rightarrow> prf" where
  "val_P m = (case m of Some (_, Ok p) \<Rightarrow> p | _ \<Rightarrow> MinProof)"

definition bres_proof :: "thm_prf \<Rightarrow> thm_prf \<Rightarrow> integer \<Rightarrow> bool \<Rightarrow> bres \<Rightarrow> prf P" where
  "bres_proof st ru i e x =
    (case SOME d. csig.okT (dest_state (thm_rep.truncate st) i) d of (stpairs, Bs, Bi, C) \<Rightarrow>
      bicompose_proof (br_env x) (th_maxidx st) True Bs (na_As (br_newas x)) (br_A x) (na_oldAs (br_newas x))
        (na_n (br_newas x)) (count_prems (strip_all_body Bi) + (if e then -1 else 0) + 1)
        (prf_wf_csig.ren_prf (na_ren (br_newas x))
          (lift_proof Bi (th_maxidx st + 1) (map (lift_all (th_maxidx st + 1) Bi) (strip_imp_prems (th_prop ru)))
            (th_proof ru)))
        (th_proof st))"

definition bres_prf_rec :: "sign \<Rightarrow> thm_prf \<Rightarrow> thm_prf \<Rightarrow> integer \<Rightarrow> bool \<Rightarrow> bres \<Rightarrow> thm_prf" where
  "bres_prf_rec c st ru i e x = thm_cert.extend (bres_rec c (thm_cert.truncate st) (thm_cert.truncate ru) x)
    (thm_prf.fields (val_P (bres_proof st ru i e x)))"

definition biresolution_prf_thms :: "cfg \<Rightarrow> (name list \<Rightarrow> name list) \<Rightarrow> bool \<Rightarrow> bool \<Rightarrow> (bool \<times> prf_thm) list \<Rightarrow>
    integer \<Rightarrow> prf_thm \<Rightarrow> (prf_thm \<times> (bool \<times> prf_thm)) list option" where
  "biresolution_prf_thms cfg vl trace match_flg brules i state =
    (let c = prf_cert_of state;
      R = (\<lambda>xs. \<exists>s0. csig.okT (biresolution trace match_flg prf_rep_of brules i (prf_rep_of state)) s0 \<and>
        csig.brevals (unify_ops cfg vl) (sg_alg c) prf_rep_of s0 xs)
     in if wf_algebra (sg_alg c) (sg_ar c) \<and> cfg_alg cfg = sg_alg c \<and> (\<forall>xs. length (vl xs) = length xs) \<and>
          (\<forall>r\<in>set brules. prf_cert_of (snd r) = c) \<and> (\<exists>xs. R xs)
       then Some (map (\<lambda>(x, r). (Abs_prf_thm (bres_prf_rec c (rep_prf_thm state) (rep_prf_thm (snd r)) i (fst r) x), r))
         (THE xs. R xs))
       else None)"

text \<open>A choice of the propositions of axioms, oracles and theorems (any choice satisfies the invariant).\<close>

lemma prf_wf_csig_some: "wf_algebra alg ar \<Longrightarrow> prf_wf_csig (\<lambda>_. Free STR ''x'' propT) (\<lambda>_. []) alg ar"
  by (simp add: prf_wf_csig_def prf_csig_def propT_def csig.vars.simps csig.tys.simps)

lemma truncate_truncate[simp]: "thm_rep.truncate (thm_cert.truncate r) = thm_rep.truncate r"
  by (simp add: thm_rep.truncate_def thm_cert.truncate_def)

lemma truncate_sel[simp]:
  "th_maxidx (thm_rep.truncate r) = th_maxidx r" "th_tpairs (thm_rep.truncate r) = th_tpairs r"
  "th_prop (thm_rep.truncate r) = th_prop r" "th_cert (thm_cert.truncate r') = th_cert r'"
  "th_hyps (thm_cert.truncate r') = th_hyps r'"
  by (simp_all add: thm_rep.truncate_def thm_cert.truncate_def)

lemma truncate_extend[simp]: "thm_cert.truncate (thm_cert.extend r m) = r"
  by (cases r) (simp add: thm_cert.truncate_def thm_cert.extend_def)

theorem bres_prf_rec_ok:
  fixes recf :: "'a \<Rightarrow> thm_prf"
  assumes wf: "wf_algebra (sg_alg (th_cert st)) (sg_ar (th_cert st))"
    and br: "csig.okT (biresolution trace match_flg (\<lambda>r. thm_rep.truncate (recf r)) brules i
      (thm_rep.truncate st)) s0"
    and res: "csig.brresult (unify_ops cfg vl) (sg_alg (th_cert st)) (\<lambda>r. thm_rep.truncate (recf r)) s0
      (x, (e, rule))"
    and cfg: "cfg_alg cfg = sg_alg (th_cert st)" and vl: "\<And>xs. length (vl xs) = length xs"
    and state_ok: "prf_thm_ok st"
    and rules: "\<forall>r\<in>set brules. prf_thm_ok (recf (snd r)) \<and> th_cert (recf (snd r)) = th_cert st"
  shows "prf_thm_ok (bres_prf_rec (th_cert st) st (recf rule) i e x)"
    "bres_proof st (recf rule) i e x = returnP (th_proof (bres_prf_rec (th_cert st) st (recf rule) i e x))"
proof -
  obtain alg ar ct where c: "th_cert st = \<lparr>sg_alg = alg, sg_ar = ar, sg_consts = ct\<rparr>"
    by (cases "th_cert st") (rule that)
  have wf': "wf_algebra alg ar" using wf by (simp add: c)
  have okc: "thm_ok (bres_rec (th_cert st) (thm_cert.truncate st) (thm_cert.truncate (recf rule)) x)"
  proof -
    have "thm_ok (bres_rec (th_cert (thm_cert.truncate st)) (thm_cert.truncate st) ((thm_cert.truncate \<circ> recf) rule) x)"
    proof (rule bres_rec_ok[where recf = "thm_cert.truncate \<circ> recf" and rule = rule])
      show "wf_algebra (sg_alg (th_cert (thm_cert.truncate st))) (sg_ar (th_cert (thm_cert.truncate st)))"
        using wf by simp
      show "csig.okT (biresolution trace match_flg (\<lambda>r. thm_rep.truncate ((thm_cert.truncate \<circ> recf) r)) brules i
          (thm_rep.truncate (thm_cert.truncate st))) s0"
        using br by (simp add: truncate_truncate comp_def)
      show "csig.brresult (unify_ops cfg vl) (sg_alg (th_cert (thm_cert.truncate st)))
          (\<lambda>r. thm_rep.truncate ((thm_cert.truncate \<circ> recf) r)) s0 (x, (e, rule))"
        using res by (simp add: comp_def)
      show "cfg_alg cfg = sg_alg (th_cert (thm_cert.truncate st))" using cfg by simp
      show "thm_ok (thm_cert.truncate st)" using state_ok by (simp add: prf_thm_ok_def)
      show "\<forall>r\<in>set brules. thm_ok ((thm_cert.truncate \<circ> recf) (snd r)) \<and>
          th_cert ((thm_cert.truncate \<circ> recf) (snd r)) = th_cert (thm_cert.truncate st)"
        using rules by (simp add: prf_thm_ok_def)
    qed (rule vl)
    then show ?thesis by simp
  qed
  interpret wf_csig ct alg ar using wf' by (simp add: wf_csig_def)
  note res' = res[unfolded c, simplified]
  from biresolution_result[OF br res'] obtain stpairs Bs Bi C goal
    where d: "okT (dest_state (thm_rep.truncate st) i) (stpairs, Bs, Bi, C)" and r: "(e, rule) \<in> set brules"
    by (rule biresolution_result[OF br res'], rule that, assumption+)
  have okr: "prf_thm_ok (recf rule)" "th_cert (recf rule) = th_cert st" using rules r by force+
  have sm: "(SOME d. okT (dest_state (thm_rep.truncate st) i) d) = (stpairs, Bs, Bi, C)"
    using okT_det[OF someI[where P = "okT (dest_state (thm_rep.truncate st) i)", OF d] d] .
  have cs: "thm_cert.truncate st \<lparr>th_cert := \<lparr>sg_alg = alg, sg_ar = ar, sg_consts = ct\<rparr>\<rparr> = thm_cert.truncate st"
    using c by (simp add: thm_cert.truncate_def)
  text \<open>The invariant for any choice of the propositions of axioms, oracles and theorems.\<close>
  have inv: "\<exists>p. bres_proof st (recf rule) i e x = returnP p \<and>
      prf_wf_csig.thm_prf_inv ct ac aty alg ar (maxidx (br_env x)) (br_tpairs x) (br_prop x)
        (set (th_hyps st) \<union> set (th_hyps (recf rule))) p"
    if pw: "prf_wf_csig ac aty alg ar" for ac aty
  proof -
    interpret P: prf_wf_csig ct ac aty alg ar by (rule pw)
    have cst: "th_cert (thm_cert.truncate st) = \<lparr>sg_alg = alg, sg_ar = ar, sg_consts = ct\<rparr>"
      using c by (simp add: thm_cert.truncate_def)
    have cru: "th_cert (thm_cert.truncate (recf rule)) = \<lparr>sg_alg = alg, sg_ar = ar, sg_consts = ct\<rparr>"
      using c okr(2) by (simp add: thm_cert.truncate_def)
    have tst: "thm_ok (thm_cert.truncate st)" "thm_ok (thm_cert.truncate (recf rule))"
      using state_ok okr(1) by (simp_all add: prf_thm_ok_def)
    note pst = thm_ok_parts_rec[OF tst(1) cst] and pru = thm_ok_parts_rec[OF tst(2) cru]
    have si: "P.thm_prf_inv (th_maxidx (thm_rep.truncate st)) (th_tpairs (thm_rep.truncate st))
        (th_prop (thm_rep.truncate st)) (set (th_hyps st)) (th_proof st)"
      using state_ok pw c by (simp add: prf_thm_ok_def thm_rep.truncate_def)
    have ri: "P.thm_prf_inv (th_maxidx (thm_rep.truncate (recf rule))) (th_tpairs (thm_rep.truncate (recf rule)))
        (th_prop (thm_rep.truncate (recf rule))) (set (th_hyps (recf rule))) (th_proof (recf rule))"
      using okr pw c by (simp add: prf_thm_ok_def thm_rep.truncate_def)
    have hs: "\<forall>h\<in>set (th_hyps (recf rule)). hyp_ok ar h" using pru(2) by (simp add: thm_cert.truncate_def)
    from P.biresolution_prf_inv[OF br res' cfg[unfolded c, simplified] vl d
        pst(1)[unfolded truncate_truncate] pru(1)[unfolded truncate_truncate] si ri hs]
    show ?thesis by (simp add: bres_proof_def sm)
  qed
  from inv[OF prf_wf_csig_some[OF wf']] obtain p0 where p0: "bres_proof st (recf rule) i e x = returnP p0"
    by blast
  have pr: "th_proof (bres_prf_rec (th_cert st) st (recf rule) i e x) = p0"
    by (simp add: bres_prf_rec_def p0 val_P_def returnP_def thm_cert.defs thm_prf.defs)
  show "bres_proof st (recf rule) i e x = returnP (th_proof (bres_prf_rec (th_cert st) st (recf rule) i e x))"
    by (simp add: pr p0)
  show "prf_thm_ok (bres_prf_rec (th_cert st) st (recf rule) i e x)"
    unfolding prf_thm_ok_def
  proof (intro conjI allI impI)
    show "thm_ok (thm_cert.truncate (bres_prf_rec (th_cert st) st (recf rule) i e x))"
      using okc by (simp add: bres_prf_rec_def)
    fix ac aty
    assume "prf_wf_csig ac aty
      (sg_alg (th_cert (bres_prf_rec (th_cert st) st (recf rule) i e x)))
      (sg_ar (th_cert (bres_prf_rec (th_cert st) st (recf rule) i e x)))"
    then have pw: "prf_wf_csig ac aty alg ar"
      by (simp add: bres_prf_rec_def bres_rec_def thm_cert.defs thm_prf.defs c)
    from inv[OF pw] p0 have "prf_wf_csig.thm_prf_inv ct ac aty alg ar (maxidx (br_env x)) (br_tpairs x) (br_prop x)
        (set (th_hyps st) \<union> set (th_hyps (recf rule))) p0"
      by (auto simp: returnP_def)
    then show "prf_wf_csig.thm_prf_inv (sg_consts (th_cert (bres_prf_rec (th_cert st) st (recf rule) i e x))) ac aty
      (sg_alg (th_cert (bres_prf_rec (th_cert st) st (recf rule) i e x)))
      (sg_ar (th_cert (bres_prf_rec (th_cert st) st (recf rule) i e x)))
      (th_maxidx (bres_prf_rec (th_cert st) st (recf rule) i e x))
      (th_tpairs (bres_prf_rec (th_cert st) st (recf rule) i e x))
      (th_prop (bres_prf_rec (th_cert st) st (recf rule) i e x))
      (set (th_hyps (bres_prf_rec (th_cert st) st (recf rule) i e x)))
      (th_proof (bres_prf_rec (th_cert st) st (recf rule) i e x))"
      using pr by (simp add: bres_prf_rec_def bres_rec_def thm_cert.defs thm_prf.defs c Un_commute)
  qed
qed

text \<open>
  Soundness: the results of \<^const>\<open>biresolution_prf_thms\<close> are the new theorems of the results of
  \<^const>\<open>biresolution\<close>, with the proofs that \<open>Proofterm.bicompose_proof\<close> computes without
  warnings or exceptions; as theorems with proofs, they are well-typed and valid, and their
  proofs are valid.
\<close>

theorem biresolution_prf_thms_results:
  assumes "biresolution_prf_thms cfg vl trace match_flg brules i state = Some ys" "(th, r) \<in> set ys"
  shows "\<exists>s0 x. csig.okT (biresolution trace match_flg prf_rep_of brules i (prf_rep_of state)) s0 \<and>
      csig.brresult (unify_ops cfg vl) (cfg_alg cfg) prf_rep_of s0 (x, r) \<and>
      rep_prf_thm th = bres_prf_rec (prf_cert_of state) (rep_prf_thm state) (rep_prf_thm (snd r)) i (fst r) x \<and>
      bres_proof (rep_prf_thm state) (rep_prf_thm (snd r)) i (fst r) x = returnP (proof_of th) \<and>
      prf_thm_ok (rep_prf_thm th)"
    and "prf_cert_of th = prf_cert_of state"
proof -
  let ?c = "prf_cert_of state"
  let ?R = "\<lambda>xs. \<exists>s0. csig.okT (biresolution trace match_flg prf_rep_of brules i (prf_rep_of state)) s0 \<and>
    csig.brevals (unify_ops cfg vl) (sg_alg ?c) prf_rep_of s0 xs"
  from assms(1) have g: "wf_algebra (sg_alg ?c) (sg_ar ?c)" "cfg_alg cfg = sg_alg ?c" "\<forall>xs. length (vl xs) = length xs"
    "\<forall>r\<in>set brules. prf_cert_of (snd r) = ?c" and ex: "\<exists>xs. ?R xs"
    and ys: "ys = map (\<lambda>(x, r). (Abs_prf_thm (bres_prf_rec ?c (rep_prf_thm state) (rep_prf_thm (snd r)) i (fst r) x), r))
      (THE xs. ?R xs)"
    by (auto simp: biresolution_prf_thms_def Let_def split: if_splits)
  from ex obtain s0 xs where br: "csig.okT (biresolution trace match_flg prf_rep_of brules i (prf_rep_of state)) s0"
    and ev: "csig.brevals (unify_ops cfg vl) (sg_alg ?c) prf_rep_of s0 xs"
    by blast
  have "(THE xs. ?R xs) = xs"
    by (rule the_equality) (use br ev in \<open>auto dest: csig.okT_det csig.brevals_det\<close>)
  with ys assms(2) obtain x where x: "(x, r) \<in> set xs"
    and th: "th = Abs_prf_thm (bres_prf_rec ?c (rep_prf_thm state) (rep_prf_thm (snd r)) i (fst r) x)"
    by auto
  have res: "csig.brresult (unify_ops cfg vl) (sg_alg ?c) prf_rep_of s0 (x, r)" by (rule csig.brevals_brresult[OF ev x])
  obtain e rule where r: "r = (e, rule)" by (cases r)
  have rules: "\<forall>r\<in>set brules. prf_thm_ok (rep_prf_thm (snd r)) \<and> prf_cert_of (snd r) = ?c"
    using g(4) rep_prf_thm by blast
  note ok = bres_prf_rec_ok[where recf = rep_prf_thm, OF g(1) br res[unfolded r] g(2) _ rep_prf_thm[simplified] rules]
  have okt: "prf_thm_ok (bres_prf_rec ?c (rep_prf_thm state) (rep_prf_thm (snd r)) i (fst r) x)"
    using ok(1) g(3) by (simp add: r)
  then have rep: "rep_prf_thm th = bres_prf_rec ?c (rep_prf_thm state) (rep_prf_thm (snd r)) i (fst r) x"
    by (simp add: th Abs_prf_thm_inverse)
  then show "prf_cert_of th = ?c" by (simp add: bres_prf_rec_def bres_rec_def thm_cert.defs thm_prf.defs)
  have "bres_proof (rep_prf_thm state) (rep_prf_thm (snd r)) i (fst r) x = returnP (proof_of th)"
    using ok(2) g(3) rep by (simp add: r)
  then show "\<exists>s0 x. csig.okT (biresolution trace match_flg prf_rep_of brules i (prf_rep_of state)) s0 \<and>
      csig.brresult (unify_ops cfg vl) (cfg_alg cfg) prf_rep_of s0 (x, r) \<and>
      rep_prf_thm th = bres_prf_rec ?c (rep_prf_thm state) (rep_prf_thm (snd r)) i (fst r) x \<and>
      bres_proof (rep_prf_thm state) (rep_prf_thm (snd r)) i (fst r) x = returnP (proof_of th) \<and>
      prf_thm_ok (rep_prf_thm th)"
    using br res g(2) rep okt by auto
qed

end

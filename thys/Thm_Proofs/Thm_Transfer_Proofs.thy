section \<open>Proofs: Thm_Transfer\<close>

theory Thm_Transfer_Proofs
  imports "Thm_Soundness.Thm_Transfer" Thm_Unconstrain_Proofs
begin

text \<open>
  The classic and tight proofs of the results of the rules of theory \<open>Thm_Transfer\<close> are valid
  (the part of the invariant of theorems that session \<open>Thm_Soundness\<close> leaves out).
\<close>

context sig_ext
begin

lemma erase_zdec_ext: "erase (S'.zdec t) = erase (S.zdec t)"
  by (induction t) auto

end

text \<open>
  A tight proof records the constants of its terms by name; it is decoded with the types that the
  signature declares (\<^const>\<open>pure_sig_gen.zdec\<close>), and a constant that only the extension declares is
  decoded differently in the extension. This does not affect the validity of the proof: the
  hypotheses of a valid proof are hypotheses of the theorem and the propositions of its proof
  constants are atoms of proofs, so both mention only constants of the signature; all other
  terms of the proof are annotations, of which the proof judgment erases the types of constants.
\<close>

fun zterm_consts :: "zterm \<Rightarrow> name set" where
  "zterm_consts (ZConst0 c) = {c}"
| "zterm_consts (ZConst1 c T) = {c}"
| "zterm_consts (ZConst c Ts) = {c}"
| "zterm_consts (ZAbs a T t) = zterm_consts t"
| "zterm_consts (ZApp t u) = zterm_consts t \<union> zterm_consts u"
| "zterm_consts _ = {}"

definition zt_decl :: "(name \<Rightarrow> ptyp option) \<Rightarrow> zterm \<Rightarrow> bool" where
  "zt_decl ct t \<longleftrightarrow> (\<forall>n\<in>zterm_consts t. n = STR ''Pure.imp'' \<or> n = STR ''Pure.all'' \<or> ct n \<noteq> None)"

lemma zt_decl_const_decl: "zt_decl ct t \<longleftrightarrow> (\<forall>n\<in>zterm_consts t. const_decl ct n)"
  by (simp add: zt_decl_def const_decl_def)

context pure_sig
begin

lemma zterm_consts_zdec: "zterm_consts t \<subseteq> term_consts (zdec t)"
  by (induction t) auto

lemma zt_decl_zdec: "\<forall>n\<in>term_consts (zdec t). const_decl ctab n \<Longrightarrow> zt_decl ctab t"
  using zterm_consts_zdec by (auto simp: zt_decl_const_decl)

end

text \<open>Proofs that differ in the types of the constants and abstractions of their annotations:\<close>

inductive prf_teq :: "prf \<Rightarrow> prf \<Rightarrow> bool" where
  refl: "prf_teq p p"
| Abst: "prf_teq p q \<Longrightarrow> prf_teq (Abst a T p) (Abst a T q)"
| AbsP: "rel_option (\<lambda>t t'. erase t = erase t') t t' \<Longrightarrow> prf_teq p q \<Longrightarrow> prf_teq (AbsP a t p) (AbsP a t' q)"
| PAppt: "prf_teq p q \<Longrightarrow> rel_option (\<lambda>t t'. erase t = erase t') t t' \<Longrightarrow> prf_teq (PAppt p t) (PAppt q t')"
| PAppp: "prf_teq p p' \<Longrightarrow> prf_teq q q' \<Longrightarrow> prf_teq (PAppp p q) (PAppp p' q')"

lemma prf_teq_foldl_PAppt:
  "list_all2 (rel_option (\<lambda>t t'. erase t = erase t')) ts ts' \<Longrightarrow> prf_teq p q \<Longrightarrow>
    prf_teq (foldl PAppt p ts) (foldl PAppt q ts')"
  by (induction arbitrary: p q rule: list_all2_induct) (auto intro: prf_teq.PAppt)

lemma prf_teq_foldl_PAppt_Some:
  "list_all2 (\<lambda>t t'. erase t = erase t') ts ts' \<Longrightarrow> prf_teq p q \<Longrightarrow>
    prf_teq (foldl (\<lambda>p t. PAppt p (Some t)) p ts) (foldl (\<lambda>p t. PAppt p (Some t)) q ts')"
  by (induction arbitrary: p q rule: list_all2_induct) (auto simp: prf_teq.PAppt)

lemma prf_atoms_foldl_PAppt [simp]: "prf_atoms (foldl PAppt p ts) = prf_atoms p"
  by (induction ts arbitrary: p) auto

lemma prf_atoms_foldl_PAppt_Some [simp]: "prf_atoms (foldl (\<lambda>p t. PAppt p (Some t)) p ts) = prf_atoms p"
  by (induction ts arbitrary: p) auto

text \<open>The class proofs of another proof of the same shape:\<close>

lemma prf_reclass_self: "pcerase w = pcerase a \<Longrightarrow> prf_reclass a w = w"
  by (induction a arbitrary: w; case_tac w; auto)

lemma prf_teq_reclass:
  "prf_teq a b \<Longrightarrow> pcerase w = pcerase a \<Longrightarrow> prf_teq w (prf_reclass b w)"
proof (induction arbitrary: w rule: prf_teq.induct)
  case (refl p)
  then show ?case by (simp add: prf_reclass_self prf_teq.refl)
next
  case (Abst p q a T)
  from Abst.prems obtain w1 where w: "w = Abst a T w1" "pcerase w1 = pcerase p" by (cases w) auto
  with Abst.IH[of w1] show ?case by (simp add: prf_teq.Abst)
next
  case (AbsP t t' p q a)
  from AbsP.prems obtain w1 where w: "w = AbsP a t w1" "pcerase w1 = pcerase p" by (cases w) auto
  with AbsP.IH[of w1] AbsP.hyps(1) show ?case by (simp add: prf_teq.AbsP)
next
  case (PAppt p q t t')
  from PAppt.prems obtain w1 where w: "w = PAppt w1 t" "pcerase w1 = pcerase p" by (cases w) auto
  with PAppt.IH[of w1] PAppt.hyps(2) show ?case by (simp add: prf_teq.PAppt)
next
  case (PAppp p p' q q')
  from PAppp.prems obtain w1 w2 where w: "w = PAppp w1 w2" "pcerase w1 = pcerase p" "pcerase w2 = pcerase q"
    by (cases w) auto
  with PAppp.IH(1)[of w1] PAppp.IH(2)[of w2] show ?case by (simp add: prf_teq.PAppp)
qed

context prf_sig
begin

lemma prf_teq_aeq: "prf_teq p q \<Longrightarrow> prf_aeq (prf_ap \<rho> \<sigma> p) (prf_ap \<rho> \<sigma> q)"
proof (induction rule: prf_teq.induct)
  case (AbsP t t' p q a)
  have "ann_eq (map_option (ap \<rho> \<sigma>) t) (map_option (ap \<rho> \<sigma>) t')"
    using AbsP.hyps(1) by (cases t; cases t') (auto simp: ann_eq_def dest: erase_ap_cong[of _ _ \<rho> \<sigma>])
  with AbsP.IH show ?case by (simp add: prf_ap_def prf_aeq.AbsP)
next
  case (PAppt p q t t')
  have "ann_eq (map_option (ap \<rho> \<sigma>) t) (map_option (ap \<rho> \<sigma>) t')"
    using PAppt.hyps(2) by (cases t; cases t') (auto simp: ann_eq_def dest: erase_ap_cong[of _ _ \<rho> \<sigma>])
  with PAppt.IH show ?case by (simp add: prf_ap_def prf_aeq.PAppt)
qed (auto simp: prf_ap_def intro: prf_aeq.intros)

lemma prf_ok_atoms: "prf_ok ax H E e Hs p \<phi> \<Longrightarrow> A \<in> prf_atoms p \<Longrightarrow> ax A"
  by (induction rule: prf_ok.induct) auto

lemma prf_valid_atoms:
  assumes "prf_valid ax H tps w \<phi>" "A \<in> prf_atoms w"
  shows "ax A"
proof -
  have "prf_ok ax H (pmap (ap (\<lambda>v S. TVar v S) (\<lambda>x T. Var x T)) (set tps)) (\<lambda>_. propT) []
      (prf_ap (\<lambda>v S. TVar v S) (\<lambda>x T. Var x T) w) (ap (\<lambda>v S. TVar v S) (\<lambda>x T. Var x T) \<phi>)"
    by (rule prf_validD[OF assms(1) cinst_TVar gsubst_Var])
  from prf_ok_atoms[OF this] assms(2) show ?thesis by (simp add: prf_ap_def)
qed

end

context sig_ext
begin

lemma zdec_ext: "zt_decl ctab t \<Longrightarrow> S'.zdec t = S.zdec t"
  by (induction t) (auto simp: zt_decl_def zconst_typ_ext)

text \<open>The two translations of a tight proof whose hypotheses and proof constants have
  propositions over the constants of the smaller signature:\<close>

lemma zprf_tr_teq:
  assumes "\<And>t n. t \<in> prf_hyps (S.zprf_trT ta z) \<Longrightarrow> n \<in> term_consts t \<Longrightarrow> const_decl ctab n"
    and "\<And>A n. A \<in> prf_atoms (S.zprf_trT ta z) \<Longrightarrow> n \<in> term_consts A \<Longrightarrow> const_decl ctab n"
  shows "prf_teq (S.zprf_trT ta z) (S'.zprf_trT ta z)"
  using assms
proof (induction z)
  case (ZConstp c)
  obtain nm A instT tab where c: "c = ((nm, A), (instT, tab))" by (metis prod.collapse)
  have look: "rel_option (\<lambda>t t'. erase t = erase t')
      (map_option S.zdec (zv_lookup_name tab xi)) (map_option S'.zdec (zv_lookup_name tab xi))" for xi
    by (cases "zv_lookup_name tab xi") (simp_all add: erase_zdec_ext)
  show ?case
  proof (cases nm)
    case (ZAxiom n)
    show ?thesis
    proof (cases "zeq_const n A")
      case True
      have "prf_teq (zeq_tr n (zinst_typs instT zeq_tvars) (\<lambda>x. map_option S.zdec (zv_lookup_name tab (x, -1))))
          (zeq_tr n (zinst_typs instT zeq_tvars) (\<lambda>x. map_option S'.zdec (zv_lookup_name tab (x, -1))))"
      proof (cases "find (\<lambda>(a, xs). n = STR ''Pure.'' + a) zeq_vars")
        case None
        then show ?thesis by (simp add: zeq_tr_def prf_teq.refl)
      next
        case (Some axs)
        obtain a xs where axs: "axs = (a, xs)" by (cases axs)
        have "rel_option (list_all2 (\<lambda>t t'. erase t = erase t'))
            (those (map (\<lambda>x. map_option S.zdec (zv_lookup_name tab (x, -1))) xs))
            (those (map (\<lambda>x. map_option S'.zdec (zv_lookup_name tab (x, -1))) xs))"
        proof (induction xs)
          case (Cons x xs)
          then show ?case
            by (cases "zv_lookup_name tab (x, -1)") (auto simp: erase_zdec_ext split: option.splits elim: option.rel_cases)
        qed simp
        then show ?thesis
          unfolding zeq_tr_def Some axs
          by (auto elim!: option.rel_cases intro: prf_teq_foldl_PAppt_Some[OF _ prf_teq.refl] prf_teq.refl)
      qed
      with True ZAxiom show ?thesis by (simp add: c S.zconst_trT_def S'.zconst_trT_def)
    next
      case False
      have "S.zdec A \<in> prf_atoms (S.zprf_trT ta (ZConstp c))"
        using False ZAxiom by (simp add: c S.zconst_trT_def zax_tr_def)
      then have "zt_decl ctab A" using ZConstp.prems(2) by (intro S.zt_decl_zdec) blast
      then have A: "S'.zdec A = S.zdec A" by (rule zdec_ext)
      have "prf_teq (zax_tr n (S.zdec A) Us (\<lambda>xi. map_option S.zdec (zv_lookup_name tab xi)))
          (zax_tr n (S.zdec A) Us (\<lambda>xi. map_option S'.zdec (zv_lookup_name tab xi)))" for Us
        unfolding zax_tr_def
        by (rule prf_teq_foldl_PAppt[OF _ prf_teq.refl])
          (auto simp: list_all2_map1 list_all2_map2 intro!: list_all2_refl look split: pterm.splits)
      with False ZAxiom A show ?thesis by (simp add: c S.zconst_trT_def S'.zconst_trT_def)
    qed
  next
    case (ZThm x)
    have "S.zdec A \<in> prf_atoms (S.zprf_trT ta (ZConstp c))"
      using ZThm by (simp add: c S.zconst_trT_def zthm_tr_def zthm_head_def)
    then have "zt_decl ctab A" using ZConstp.prems(2) by (intro S.zt_decl_zdec) blast
    then have A: "S'.zdec A = S.zdec A" by (rule zdec_ext)
    have "prf_teq (zthm_tr (S.zdec A) Us (\<lambda>xi. map_option S.zdec (zv_lookup_name tab xi)))
        (zthm_tr (S.zdec A) Us (\<lambda>xi. map_option S'.zdec (zv_lookup_name tab xi)))" for Us
      unfolding zthm_tr_def
      by (rule prf_teq_foldl_PAppt[OF _ prf_teq.refl])
        (auto simp: list_all2_map1 list_all2_map2 intro!: list_all2_refl look split: pterm.splits)
    with ZThm A show ?thesis by (simp add: c S.zconst_trT_def S'.zconst_trT_def)
  qed (simp_all add: c S.zconst_trT_def S'.zconst_trT_def prf_teq.refl)
next
  case (ZHyp t)
  then have "zt_decl ctab t" by (intro S.zt_decl_zdec) simp
  then show ?case by (simp add: zdec_ext prf_teq.refl)
qed (auto intro: prf_teq.intros simp: erase_zdec_ext)

lemma zhyps_ok_ext: "\<forall>h\<in>zhyps z. zt_decl ctab h \<Longrightarrow> S.zhyps_ok z \<Longrightarrow> S'.zhyps_ok z"
  unfolding S.zhyps_ok_def S'.zhyps_ok_def return_def
  using zdec_ext zterm_of_ext by metis

end

locale prf_ext = sig_ext alg alg' ar ctab ctab' +
  P: prf_sig alg ar ctab close tyargs + P': prf_sig alg' ar ctab' close tyargs
  for alg alg' ar ctab ctab' close tyargs
begin

lemma atom_ok_ext: "P.atom_ok A Us' Us \<Longrightarrow> P'.atom_ok A Us' Us"
  unfolding P.atom_ok_def P'.atom_ok_def by (auto elim!: list_all2_mono intro: has_sort_ext cert_typ_ext)

lemma prf_ok_ext:
  assumes ax: "\<And>A. ax A \<Longrightarrow> ax' A"
  shows "P.prf_ok ax H E e Hs p \<phi> \<Longrightarrow> P'.prf_ok ax' H E e Hs p \<phi>"
  by (induction rule: P.prf_ok.induct)
    (auto intro: P'.prf_ok.intros typing_ext conv_ext eqv_ext cert_typ_ext has_sort_ext atom_ok_ext ax)

lemma prf_valid_ext:
  assumes H: "\<And>h. h \<in> H \<Longrightarrow> vars h = {} \<and> ttvars h = {}" and ax: "\<And>A. ax A \<Longrightarrow> ax' A"
    and v: "P.prf_valid ax H tps p \<phi>"
  shows "P'.prf_valid ax' H tps p \<phi>"
proof -
  have "P.prf_ok ax H ((\<lambda>(l, r). (S.ap TVar Var l, S.ap TVar Var r)) ` set tps) e []
      (P.prf_ap TVar Var p) (S.ap TVar Var \<phi>)" for e
    using v P.cinst_TVar' P.gsubst_Var unfolding P.prf_valid_def by blast
  moreover have "S.ap TVar Var = (\<lambda>t. t)" using S.ap_Var_fun[of TVar] by (simp add: fun_eq_iff)
  ultimately have b: "P.prf_ok ax H (set tps) e [] p \<phi>" for e by (simp add: case_prod_Pair)
  have g: "P'.prf_ok ax' H (set tps) e [] p \<phi>" for e
    using prf_ok_ext[of ax ax' H "set tps" e "[]" p \<phi>] ax b by blast
  show ?thesis by (rule P'.prf_validI) (rule P'.prf_ok_ap_any[OF H g])
qed

text \<open>
  A valid tight proof stays valid in the extension: its hypotheses are hypotheses of the theorem
  and the propositions of its proof constants are axioms, so both mention only constants of the
  smaller signature; elsewhere the two translations differ in the types of constants in
  annotations, which the proof judgment erases.
\<close>

lemma zvalid_ext:
  assumes H: "\<And>h. h \<in> H \<Longrightarrow> vars h = {} \<and> ttvars h = {}" and ax: "\<And>A. ax A \<Longrightarrow> ax' A"
    and Hd: "\<And>h n. h \<in> H \<Longrightarrow> n \<in> term_consts h \<Longrightarrow> const_decl ctab n"
    and axd: "\<And>A n. ax A \<Longrightarrow> n \<in> term_consts A \<Longrightarrow> const_decl ctab n"
    and v: "P.zvalid ax H tps z \<phi>"
  shows "P'.zvalid ax' H tps z \<phi>" and "\<forall>h\<in>zhyps z. zt_decl ctab h"
proof -
  obtain w where w: "pcerase w = pcerase (P.zprf_tr z)" "P.prf_valid ax H tps w \<phi>" using v by (rule P.zvalidE)
  have hy: "prf_hyps (P.zprf_tr z) = prf_hyps w" using arg_cong[OF w(1), of prf_hyps] by simp
  have at: "prf_atoms (P.zprf_tr z) = prf_atoms w" using arg_cong[OF w(1), of prf_atoms] by simp
  have hd: "const_decl ctab n" if "t \<in> prf_hyps (P.zprf_tr z)" "n \<in> term_consts t" for t n
    using that P.prf_valid_hyps[OF w(2)] Hd unfolding hy by blast
  have ad: "const_decl ctab n" if "A \<in> prf_atoms (P.zprf_tr z)" "n \<in> term_consts A" for A n
    using that P.prf_valid_atoms[OF w(2)] axd unfolding at by blast
  show "\<forall>h\<in>zhyps z. zt_decl ctab h"
  proof
    fix h assume "h \<in> zhyps z"
    then have "S.zdec h \<in> prf_hyps (P.zprf_tr z)" using P.zhyps_prf_hyps[of z] by blast
    then show "zt_decl ctab h" using hd by (intro S.zt_decl_zdec) blast
  qed
  let ?w' = "prf_reclass (P'.zprf_tr z) w"
  have teq: "prf_teq w ?w'" by (rule prf_teq_reclass[OF zprf_tr_teq[OF hd ad] w(1)])
  have "P'.prf_valid ax' H tps w \<phi>" by (rule prf_valid_ext[OF H ax w(2)])
  then have "P'.prf_valid ax' H tps ?w' \<phi>" by (rule P'.prf_valid_aeq) (rule P'.prf_teq_aeq[OF teq])
  then show "P'.zvalid ax' H tps z \<phi>" by (rule P'.zvalidI[rotated]) simp
qed

end


text \<open>The proofs of a theorem of a signature are valid in its extensions:\<close>

theorem proofs_ok_transfer:
  assumes sem: "thm_sem TYPE('u) th" and prfs: "is_prf_sig (th_sign th) \<Longrightarrow> proofs_ok th"
    and sl: "sign_le (th_sign th) c'"
  shows "is_prf_sig (th_sign (th\<lparr>th_sign := c'\<rparr>)) \<Longrightarrow> proofs_ok (th\<lparr>th_sign := c'\<rparr>)"
proof -
  let ?c = "th_sign th"
  have ps: "pure_sig (sg_alg ?c) (sg_ar ?c)" and ar: "sg_ar c' = sg_ar ?c"
    and ax: "\<And>A. sg_ax ?c A \<Longrightarrow> sg_ax c' A" and cl: "sg_close c' = sg_close ?c" and ty: "sg_tyargs c' = sg_tyargs ?c"
    and axs: "\<And>a A. sg_axioms ?c a = Some A \<Longrightarrow> sg_axioms c' a = Some A \<and> pure_sig_gen.wtp (sg_alg ?c) (sg_ar ?c) (sg_consts ?c) A"
    using sl by (auto simp: sign_le_def)
  have axd: "\<And>A n. sg_ax ?c A \<Longrightarrow> n \<in> term_consts A \<Longrightarrow> const_decl (sg_consts ?c) n"
    using sl by (auto simp: sign_le_def)
  from sem ps have wf: "pure_sig.thm_wf (sg_alg ?c) (sg_ar ?c) (sg_consts ?c) (th_maxidx th) (th_hyps th) (th_tpairs th) (th_prop th)"
    and val: "\<And>M :: 'u model. is_model ?c M \<Longrightarrow> valid_in ?c M (th_shyps th) (th_hyps th) (th_tpairs th) (th_prop th)"
    by (auto simp: thm_sem_def)
  assume ip: "is_prf_sig (th_sign (th\<lparr>th_sign := c'\<rparr>))"
  then have ip': "prf_sig (sg_alg c') (sg_ar c') (sg_close c') (sg_tyargs c')" by (simp add: is_prf_sig_def)
  then have ps'': "pure_sig (sg_alg c') (sg_ar c')" by (simp add: prf_sig_def)
  have ipc: "prf_sig (sg_alg ?c) (sg_ar ?c) (sg_close ?c) (sg_tyargs ?c)"
    using ip' ps ar cl ty by (simp add: prf_sig_def)
  interpret PE: prf_ext "sg_alg ?c" "sg_alg c'" "sg_ar ?c" "sg_consts ?c" "sg_consts c'" "sg_close ?c" "sg_tyargs ?c"
    using sig_ext_sign_le[OF sl ps''] ipc ip' ar cl ty by (simp add: prf_ext_def)
  have po: "proofs_ok th" using prfs ipc by (simp add: is_prf_sig_def)
  have H: "h \<in> set (th_hyps th) \<Longrightarrow> vars h = {} \<and> ttvars h = {}" for h
    using wf by (simp add: PE.S.thm_wf_def PE.S.wt_thm_def)
  have Hd: "const_decl (sg_consts ?c) n" if "h \<in> set (th_hyps th)" "n \<in> term_consts h" for h n
  proof -
    from wf that(1) have "PE.S.wtp h" by (simp add: PE.S.thm_wf_def PE.S.wt_thm_def)
    from PE.S.typing_consts_decl[OF PE.S.wtpD(2)[OF this] that(2)] show ?thesis .
  qed
  have A: "PE.P'.prf_valid (sg_ax c') (set (th_hyps th)) (th_tpairs th) p (th_prop th) \<and>
      prf_idx (\<lambda>i. 0 \<le> i) p \<and> prf_nolb 0 p" if "th_proof th = returnW p" for p
    using po that PE.prf_valid_ext[OF H ax] by (simp add: proofs_ok_def Let_def)
  have B: "PE.P'.zvalid (sg_ax c') (set (th_hyps th)) (th_tpairs th) z (th_prop th) \<and> zinv z \<and> znolb 0 z \<and>
      PE.S'.zhyps_ok z" if "th_zproof th = return z" for z
  proof -
    from po that have v: "PE.P.zvalid (sg_ax ?c) (set (th_hyps th)) (th_tpairs th) z (th_prop th)"
      and i: "zinv z" "znolb 0 z" "PE.S.zhyps_ok z"
      by (simp_all add: proofs_ok_def Let_def)
    have zv1: "PE.P'.zvalid (sg_ax c') (set (th_hyps th)) (th_tpairs th) z (th_prop th)"
      by (rule PE.zvalid_ext(1)[OF _ _ _ _ v]) (use H ax Hd axd in blast)+
    have zv2: "\<forall>h\<in>zhyps z. zt_decl (sg_consts ?c) h"
      by (rule PE.zvalid_ext(2)[where ax' = "sg_ax c'", OF _ _ _ _ v]) (use H ax Hd axd in blast)+
    from zv1 PE.zhyps_ok_ext[OF zv2 i(3)] i(1,2) show ?thesis by simp
  qed
  show "proofs_ok (th\<lparr>th_sign := c'\<rparr>)"
    unfolding proofs_ok_def Let_def using A B by (simp add: ar cl ty)
qed

theorem thm_ok_transfer:
  assumes ok: "thm_ok TYPE('u) th" and sl: "sign_le (th_sign th) c'"
  shows "thm_ok TYPE('u) (th\<lparr>th_sign := c'\<rparr>)"
proof -
  from ok have s: "thm_sem TYPE('u) th" and p: "is_prf_sig (th_sign th) \<Longrightarrow> proofs_ok th"
    by (simp_all add: thm_ok_def)
  show ?thesis using thm_sem_transfer[OF s sl] proofs_ok_transfer[OF s p sl] by (simp add: thm_ok_def)
qed

end

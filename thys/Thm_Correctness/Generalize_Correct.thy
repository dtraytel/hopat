section \<open>Soundness of the generalization over a variable\<close>

theory Generalize_Correct
  imports Rules_Correct
begin

text \<open>
  \<open>Thm.forall_intr\<close> generalizes a theorem over a free or schematic variable that does not occur
  in the hypotheses and the flex-flex pairs. Variables are interpreted by name and type, so the
  other variables of the same name are not affected.
\<close>


subsection \<open>Free variables with their types\<close>

lemma occs_Free: "occs (Free a T) t \<longleftrightarrow> (a, T) \<in> pfrees t"
  by (induction t) (auto simp: occs_def)

lemma occs_Var: "occs (Var z T) t \<longleftrightarrow> (z, T) \<in> vars t"
  by (induction t) (auto simp: occs_def)

text \<open>Renaming of free variables:\<close>

fun frename :: "(name \<Rightarrow> ptyp \<Rightarrow> name) \<Rightarrow> pterm \<Rightarrow> pterm" where
  "frename f (Free x T) = Free (f x T) T"
| "frename f (Abs a T t) = Abs a T (frename f t)"
| "frename f (s $ t) = frename f s $ frename f t"
| "frename f t = t"

lemma frename_fsubst: "frename f t = fsubst (\<lambda>x T. Free (f x T) T) t"
  by (induction t) simp_all

lemma loose_bvar_frename [simp]: "loose_bvar (frename f t) k \<longleftrightarrow> loose_bvar t k"
  by (induction t arbitrary: k) simp_all

subsection \<open>Abstraction over a variable\<close>

lemma aconv_term_atom: "x = Free a T \<or> x = Var z T \<Longrightarrow> aconv_term x t \<longleftrightarrow> t = x"
  by (cases t) auto

lemma loose_bvar_abstract_over_aux:
  "\<not> loose_bvar t k \<Longrightarrow> lev < k \<Longrightarrow> \<not> loose_bvar (abstract_over_aux x lev t) k"
  by (induction x lev t arbitrary: k rule: abstract_over_aux.induct) auto

text \<open>The valuation that maps a free or schematic variable to a value:\<close>

definition vupd :: "pterm \<Rightarrow> 'u \<Rightarrow> 'u vval \<Rightarrow> 'u vval" where
  "vupd x u \<xi> = (case x of
      Free a T \<Rightarrow> (fst \<xi>, (snd \<xi>)(a := (snd \<xi> a)(T := u)))
    | Var z T \<Rightarrow> ((fst \<xi>)(z := (fst \<xi> z)(T := u)), snd \<xi>)
    | _ \<Rightarrow> \<xi>)"

context pure_sig
begin

lemma ap_cong_vars:
  "(\<And>v U. (v, U) \<in> vars t \<Longrightarrow> \<sigma> v (tsubst \<rho> U) = \<sigma>' v (tsubst \<rho> U)) \<Longrightarrow> ap \<rho> \<sigma> t = ap \<rho> \<sigma>' t"
  unfolding ap_def by (induction t) auto

lemma typing_frename: "e \<turnstile> t : T \<Longrightarrow> e \<turnstile> frename f t : T"
  by (induction rule: typing.induct) auto

lemma ap_frename:
  "(\<And>x U. (x, U) \<in> pfrees t \<Longrightarrow> f x (tsubst \<rho> U) = x) \<Longrightarrow>
    frename f (ap \<rho> \<sigma> t) = ap \<rho> (\<lambda>v U. frename f (\<sigma> v U)) t"
  unfolding ap_def by (induction t) auto

lemma conv_frename:
  assumes w: "wt s" and c: "s \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> t"
  shows "frename f s \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> frename f t"
proof -
  have wt: "wt t" using wt_conv[OF c] w by simp
  have ws: "wt (frename f s)" "wt (frename f t)"
    using w wt by (auto simp: wt_def intro: typing_frename)
  obtain u v where uv: "(sup beta eta)\<^sup>*\<^sup>* s u" "(sup beta eta)\<^sup>*\<^sup>* t v" "aconv_term u v"
    using conv_iff[OF w] c by blast
  have "aconv_term (frename f u) (frename f v)"
    using uv(3) by (simp add: aconv_term_unname unname_fsubst frename_fsubst)
  then show ?thesis
    using conv_iff[OF ws(1)] ws(2) beta_eta_fsubst[OF uv(1)] beta_eta_fsubst[OF uv(2)]
    unfolding frename_fsubst by blast
qed

lemma typing_abstract_over_aux:
  assumes x: "x = Free a T \<or> x = Var z T"
  shows "e \<turnstile> t : U \<Longrightarrow> 0 \<le> lev \<Longrightarrow> \<not> loose_bvar t lev \<Longrightarrow> (\<And>i. 0 \<le> i \<Longrightarrow> i < lev \<Longrightarrow> e' i = e i) \<Longrightarrow>
    e' lev = T \<Longrightarrow> e' \<turnstile> abstract_over_aux x lev t : U"
proof (induction t arbitrary: e e' lev U)
  case (Abs b V t)
  from Abs.prems(1) have V: "cert_typ alg ar V" and "\<exists>W. U = V \<rightarrow>\<^sub>T W \<and> e\<langle>0:V\<rangle> \<turnstile> t : W" by auto
  then obtain W where U: "U = V \<rightarrow>\<^sub>T W" and t: "e\<langle>0:V\<rangle> \<turnstile> t : W" by blast
  have "e'\<langle>0:V\<rangle> \<turnstile> abstract_over_aux x (lev + 1) t : W"
  proof (rule Abs.IH[OF t])
    show "(e'\<langle>0:V\<rangle>) i = (e\<langle>0:V\<rangle>) i" if "0 \<le> i" "i < lev + 1" for i
    proof (cases "i = 0")
      case False
      with that have "0 \<le> i - 1" "i - 1 < lev" by (simp_all add: integer_arith)
      with False show ?thesis using Abs.prems(4)[of "i - 1"] by (simp add: shift_def)
    qed (simp add: shift_def)
    show "(e'\<langle>0:V\<rangle>) (lev + 1) = T" using Abs.prems(2,5) by (simp add: shift_def)
  qed (use Abs.prems in simp_all)
  with x U V show ?case by (auto simp: aconv_term_atom)
next
  case (App s t)
  then show ?case using x by (auto simp: aconv_term_atom)
qed (use x in \<open>auto simp: aconv_term_atom\<close>)

end

context pure_model
begin

lemma sem_agree:
  "(\<And>x T. (x, T) \<in> vars t \<Longrightarrow> fst \<xi>1 x T = fst \<xi>2 x T) \<Longrightarrow>
    (\<And>a T. (a, T) \<in> pfrees t \<Longrightarrow> snd \<xi>1 a T = snd \<xi>2 a T) \<Longrightarrow> sem \<eta> \<xi>1 bv t = sem \<eta> \<xi>2 bv t"
  by (induction t arbitrary: bv) auto

lemma sem_frename:
  assumes "fst \<xi>' = fst \<xi>" "\<And>a T. (a, T) \<in> pfrees t \<Longrightarrow> snd \<xi>' (f a T) T = snd \<xi> a T"
  shows "sem \<eta> \<xi>' bv (frename f t) = sem \<eta> \<xi> bv t"
  using assms(2) by (induction t arbitrary: bv) (auto simp: assms(1))

lemma sem_abstract_over_aux:
  assumes x: "x = Free a T \<or> x = Var z T"
  shows "0 \<le> lev \<Longrightarrow> sem \<eta> \<xi> bv (abstract_over_aux x lev t) = sem \<eta> (vupd x (bv lev) \<xi>) bv t"
proof (induction t arbitrary: bv lev)
  case (Abs b V t)
  have "sem \<eta> \<xi> (push v bv) (abstract_over_aux x (lev + 1) t) = sem \<eta> (vupd x (bv lev) \<xi>) (push v bv) t" for v
    using Abs.IH[of "lev + 1" "push v bv"] Abs.prems by (simp add: push_def)
  with x show ?case by (auto simp: aconv_term_atom)
qed (use x in \<open>auto simp: aconv_term_atom vupd_def split: if_splits\<close>)

lemma sem_vupd_other:
  assumes x: "x = Free a T \<or> x = Var z T" and n: "\<not> occs x t"
  shows "sem \<eta> (vupd x u \<xi>) bv t = sem \<eta> \<xi> bv t"
  using x n by (intro sem_agree) (auto simp: vupd_def occs_Free occs_Var)

lemma good_vupd:
  assumes g: "good \<eta> \<xi>" and x: "x = Free a T \<or> x = Var z T" and u: "u \<in>\<^sub>u tsem \<eta> T"
  shows "good \<eta> (vupd x u \<xi>)"
  using g x u by (auto simp: good_def good_v_def vupd_def)

end

context pure_sig
begin

text \<open>The terms of a theorem:\<close>

definition thm_terms :: "pterm list \<Rightarrow> (pterm \<times> pterm) list \<Rightarrow> pterm \<Rightarrow> pterm set" where
  "thm_terms hs tps P = insert P (set hs \<union> fst ` set tps \<union> snd ` set tps)"

lemma finite_thm_terms [simp]: "finite (thm_terms hs tps P)"
  by (simp add: thm_terms_def)

end

context pure_model
begin

lemma wt_thm_wf_terms: "wt_thm m hs tps P \<Longrightarrow> wf_terms hs tps P"
  unfolding wt_thm_def wf_terms_def wtp_def gterm_def by (auto 0 3 simp: split_beta)

text \<open>
  The semantic argument: a valuation of the generalized variable by \<open>u\<close> keeps the flex-flex
  pairs and the hypotheses, which do not contain the variable.
\<close>

lemma forall_sem:
  assumes v: "valid Sh hs tps P" and wt: "wt_thm m hs tps P"
    and x: "x = Free a T \<or> x = Var z T"
    and nh: "\<forall>h\<in>set hs. \<not> occs x h" and nt: "\<forall>(t, u)\<in>set tps. \<not> occs x t \<and> \<not> occs x u"
    and sh: "\<And>S. S \<in> Sh \<Longrightarrow> sinh S" and g: "good \<eta> \<xi>"
    and tp: "\<And>t u. (t, u) \<in> set tps \<Longrightarrow> eq_at \<eta> \<xi> t u"
    and hh: "\<And>h. h \<in> set hs \<Longrightarrow> holds_at \<eta> \<xi> h"
    and u: "u \<in>\<^sub>u tsem \<eta> T"
  shows "holds_at \<eta> (vupd x u \<xi>) P"
proof (rule svalidD[OF v[unfolded valid_svalid[OF wt_thm_wf_terms[OF wt]]] sh good_vupd[OF g x u]])
  fix t t' assume tt: "(t, t') \<in> set tps"
  with nt have "\<not> occs x t" "\<not> occs x t'" by auto
  with tp[OF tt] show "eq_at \<eta> (vupd x u \<xi>) t t'" by (simp add: eq_at_def sem_vupd_other[OF x])
next
  fix h assume "h \<in> set hs"
  with nh hh show "holds_at \<eta> (vupd x u \<xi>) h" by (simp add: holds_at_def sem_vupd_other[OF x])
qed

lemma valid_forall:
  assumes v: "valid Sh hs tps P" and wt: "wt_thm m hs tps P"
    and x: "x = Free a T \<or> x = Var z T"
    and nh: "\<forall>h\<in>set hs. \<not> occs x h" and nt: "\<forall>(t, u)\<in>set tps. \<not> occs x t \<and> \<not> occs x u"
  shows "valid Sh hs tps (all_const T $ Abs b T (abstract_over x P))"
proof (rule validI)
  fix \<eta> \<xi> \<rho> \<sigma> assume sh: "\<And>S. S \<in> Sh \<Longrightarrow> sinh S" and g: "good \<eta> \<xi>" and \<rho>: "cinst \<rho>"
    and \<rho>i: "inh_inst \<rho>" and \<sigma>: "gsubst \<sigma>"
    and sol: "\<And>t u. (t, u) \<in> set tps \<Longrightarrow> eq_at \<eta> \<xi> (ap \<rho> \<sigma> t) (ap \<rho> \<sigma> u)"
    and hh: "\<And>h. h \<in> set hs \<Longrightarrow> holds_at \<eta> \<xi> (ap \<rho> \<sigma> h)"
  interpret pure_valuation alg ar ctab umem ufun uapp ulam ubool utrue ufalse tcon cls cval \<eta> \<xi>
    by unfold_locales (rule g)
  have wP: "wtp P" using wt by (simp add: wt_thm_def)
  note ws = gsubstD(1)[OF \<sigma>]
  define Q where "Q = abstract_over x P"
  have tQ: "(\<lambda>_. propT)\<langle>0:T\<rangle> \<turnstile> Q : propT"
    unfolding Q_def abstract_over_def
    by (rule typing_abstract_over_aux[OF x wtpD(2)[OF wP]]) (use wtpD(1)[OF wP] in \<open>simp_all add: closed_def\<close>)
  have "hb (push u bv0) (ap \<rho> \<sigma> Q)" if u: "u \<in>\<^sub>u tsem \<eta> (tsubst \<rho> T)" for u
  proof -
    let ?\<eta> = "apv_t \<eta> \<rho>" and ?\<xi> = "apv_v \<eta> \<xi> \<rho> \<sigma>"
    have "sem \<eta> \<xi> (push u bv0) (ap \<rho> \<sigma> Q) = sem ?\<eta> ?\<xi> (push u bv0) Q"
      by (rule sem_ap[OF ws tQ])
    also have "\<dots> = sem ?\<eta> (vupd x u ?\<xi>) (push u bv0) P"
      using sem_abstract_over_aux[OF x, of 0 ?\<eta> ?\<xi> "push u bv0" P] by (simp add: Q_def abstract_over_def push_def)
    also have "\<dots> = sem ?\<eta> (vupd x u ?\<xi>) bv0 P" by (rule sem_closed[OF wtpD(1)[OF wP]])
    moreover have "holds_at ?\<eta> (vupd x u ?\<xi>) P"
    proof (rule forall_sem[OF v wt x nh nt sh good_ap[OF g \<rho> \<rho>i ws]])
      fix t t' assume tt: "(t, t') \<in> set tps"
      from wt tt obtain U where ty: "\<And>e. e \<turnstile> t : U" "\<And>e. e \<turnstile> t' : U" by (fastforce simp: wt_thm_def)
      from sol[OF tt] show "eq_at ?\<eta> ?\<xi> t t'" by (simp add: eq_at_ap[OF ws ty])
    next
      fix h assume h: "h \<in> set hs"
      have th: "e \<turnstile> h : propT" for e using wt h by (auto simp: wt_thm_def wtp_def)
      from hh[OF h] show "holds_at ?\<eta> ?\<xi> h" by (simp add: holds_at_ap[OF ws th])
    next
      show "u \<in>\<^sub>u tsem ?\<eta> T" using u by (simp add: apv_t_def tsem_tsubst)
    qed
    ultimately show ?thesis by (simp add: holds_at_def)
  qed
  then show "holds_at \<eta> \<xi> (ap \<rho> \<sigma> (all_const T $ Abs b T Q))"
    using hb_all[OF cinstD(2)[OF \<rho>] \<sigma> tQ bvals0] by (simp add: holds_at_def)
qed

theorem forall_intr_valid:
  assumes ok: "okT (forall_intr hs (CTerm x T m) th0) th"
    and v: "valid Sh hs (th_tpairs th0) (th_prop th0)"
    and wt: "wt_thm (th_maxidx th0) hs (th_tpairs th0) (th_prop th0)" and tx: "\<And>e. e \<turnstile> x : T"
  shows "valid Sh hs (th_tpairs th) (th_prop th)"
proof -
  have hv: "\<And>h. h \<in> set hs \<Longrightarrow> vars h = {}" using wt by (simp add: wt_thm_def)
  obtain b where th: "th = mk_rep (max m (th_maxidx th0)) (th_tpairs th0)
      (all_const T $ Abs b T (abstract_over x (th_prop th0)))"
    and cases: "(x = Free b T \<and> \<not> occs_hyps x hs (th_tpairs th0)) \<or>
      (\<exists>j. x = Var (b, j) T \<and> \<not> occs_hyps x [] (th_tpairs th0))"
  proof (cases x)
    case (Free a U)
    with tx[of "\<lambda>_. propT"] have "U = T" by auto
    with ok Free that[of a] show ?thesis
      by (auto simp: forall_intr_def returnW_def raiseW_def Let_def split: if_splits)
  next
    case (Var zi U)
    obtain a j where zi: "zi = (a, j)" by (cases zi)
    with Var tx[of "\<lambda>_. propT"] have "U = T" by auto
    with ok Var zi that[of a] show ?thesis
      by (auto simp: forall_intr_def returnW_def raiseW_def Let_def split: if_splits)
  qed (use ok in \<open>auto simp: forall_intr_def raiseW_def Let_def\<close>)
  from cases obtain z where x: "x = Free b T \<or> x = Var z T"
    and nh: "\<forall>h\<in>set hs. \<not> occs x h" and nt: "\<forall>(t, u)\<in>set (th_tpairs th0). \<not> occs x t \<and> \<not> occs x u"
    using hv by (fastforce simp: occs_hyps_def occs_Var)
  have "valid Sh hs (th_tpairs th0) (all_const T $ Abs b T (abstract_over x (th_prop th0)))"
    by (rule valid_forall[OF v wt x nh nt])
  then show ?thesis by (simp add: th mk_rep_def)
qed

end

end

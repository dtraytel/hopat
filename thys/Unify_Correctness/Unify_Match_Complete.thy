section \<open>Completeness of \<open>MATCH\<close>\<close>

theory Unify_Match_Complete
  imports Unify_Simpl_Complete Unify_Mc_Fin Unify_Shape_Sound
begin

text \<open>
  The measure of the completeness proof of the search: the size of the \<open>\<eta>\<close>-long \<open>\<beta>\<close>-normal
  forms of the values of the solution. We measure the size with \<open>lsz\<close> of
  \<^theory>\<open>Unify_Correctness.Unify_Simpl_Term\<close>, without the outer abstractions of a value: a value
  \<open>\<lambda>x\<^sub>1 \<dots> x\<^sub>n. b\<close> of type \<open>T\<^sub>1 \<Rightarrow> \<dots> \<Rightarrow> T\<^sub>n \<Rightarrow> B\<close> counts as \<open>b\<close>. Then the values \<open>\<lambda>x\<^sub>1 \<dots> x\<^sub>n. b\<^sub>i\<close> of
  the new variables of a projection or an imitation \<open>\<lambda>x\<^sub>1 \<dots> x\<^sub>n. h b\<^sub>1 \<dots> b\<^sub>m\<close> are smaller than
  the value.
\<close>

context pure_sig
begin

subsection \<open>Invariance of the size of \<open>\<eta>\<close>-long forms\<close>

lemma mcp_lsz_unname [simp]:
  "lsz e (unname t) = lsz e t \<and> asz e (unname t) = asz e t"
proof (induction t arbitrary: e)
  case (App s t)
  have d: "dhd (unname s) = unname (dhd s)" "dnargs (unname s) = dnargs s"
    by (induction s) auto
  have dv: "(\<exists>x T. dhd s = Var x T) \<longleftrightarrow> (\<exists>x T. unname (dhd s) = Var x T)"
    by (cases "dhd s") auto
  show ?case
  proof (cases "\<exists>x T. dhd s = Var x T")
    case True
    then obtain x T where "dhd s = Var x T" by blast
    then show ?thesis using App d by simp
  next
    case False
    then have "\<not> (\<exists>x T. unname (dhd s) = Var x T)" using dv by blast
    then have l: "lsz e (unname s $ unname t) = tsz (spine_type e (unname s $ unname t)) + asz e (unname s $ unname t)"
      using d(1) by (cases "unname (dhd s)") simp_all
    have r: "lsz e (s $ t) = tsz (spine_type e (s $ t)) + asz e (s $ t)"
      using False by (cases "dhd s") simp_all
    show ?thesis using l r App by simp
  qed
qed auto

lemma mcp_lsz_aconv: "aconv_term s t \<Longrightarrow> lsz e s = lsz e t"
  by (metis aconv_term_unname mcp_lsz_unname)

text \<open>A term whose head is not a variable:\<close>

lemma mcp_lsz_rigid:
  "\<not> is_Abs s \<Longrightarrow> \<not> is_Var (dhd s) \<Longrightarrow> lsz e s = tsz (spine_type e s) + asz e s"
  by (cases s) (auto split: pterm.splits)

lemma mcp_lsz_flex:
  "dhd s = Var x T \<Longrightarrow> lsz e s = 2 * (arity T - dnargs s) + 1"
  by (cases s) auto

lemma mcp_arity_flex:
  "e \<turnstile> s : S \<Longrightarrow> dhd s = Var x T \<Longrightarrow> arity T = dnargs s + arity S"
proof (induction s arbitrary: S)
  case (App s t)
  then obtain A where "e \<turnstile> s : A \<rightarrow>\<^sub>T S" by auto
  with App show ?case by force
qed auto

lemma mcp_lsz_app_bound:
  assumes ty: "e \<turnstile> s : A \<rightarrow>\<^sub>T U" and nr: "no_redex s" "\<not> is_Abs s" and l: "lsz e t = tsz A"
  shows "lsz e (s $ t) + 2 = lsz e s"
proof (cases "is_Var (dhd s)")
  case True
  then obtain x T where h: "dhd s = Var x T" by (cases "dhd s") auto
  have "arity T = dnargs s + Suc (arity U)" using mcp_arity_flex[OF ty h] by simp
  then show ?thesis using h mcp_lsz_flex[OF h] by simp
next
  case False
  have st: "spine_type e s = A \<rightarrow>\<^sub>T U" by (rule spine_type_typing[OF ty nr])
  have "lsz e (s $ t) = tsz (spine_type e (s $ t)) + asz e (s $ t)"
    by (rule mcp_lsz_rigid) (use False in simp_all)
  then have "lsz e (s $ t) = tsz U + asz e s + tsz A" using st l by simp
  moreover have "lsz e s = tsz A + tsz U + 2 + asz e s" using mcp_lsz_rigid[OF nr(2) False, of e] st by simp
  ultimately show ?thesis by simp
qed

lemma mcp_lsz_subst_dummy:
  "\<not> loose_bvar1 s k \<Longrightarrow> 0 \<le> k \<Longrightarrow>
    spine_type e (s[u/k]) = spine_type (e\<langle>k:A\<rangle>) s \<and> lsz e (s[u/k]) = lsz (e\<langle>k:A\<rangle>) s \<and>
    asz e (s[u/k]) = asz (e\<langle>k:A\<rangle>) s \<and> (is_Var (dhd (s[u/k])) \<longleftrightarrow> is_Var (dhd s)) \<and>
    (is_Var (dhd s) \<longrightarrow> dhd (s[u/k]) = dhd s) \<and> dnargs (s[u/k]) = dnargs s"
proof (induction s arbitrary: e k u)
  case (Bound i)
  then show ?case by (auto simp: subst_Bound)
next
  case (Abs a B s)
  have IH: "lsz e' (s[u'/k']) = lsz (e'\<langle>k':A\<rangle>) s" if "\<not> loose_bvar1 s k'" "0 \<le> k'" for e' k' u'
    using Abs.IH that by blast
  show ?case using IH[of "k + 1" "e\<langle>0:B\<rangle>" "lift u 0"] Abs.prems by (simp add: integer_arith)
next
  case (App s t)
  have IHs: "spine_type e (s[u/k]) = spine_type (e\<langle>k:A\<rangle>) s" "lsz e (s[u/k]) = lsz (e\<langle>k:A\<rangle>) s"
    "asz e (s[u/k]) = asz (e\<langle>k:A\<rangle>) s" "is_Var (dhd (s[u/k])) \<longleftrightarrow> is_Var (dhd s)"
    "is_Var (dhd s) \<Longrightarrow> dhd (s[u/k]) = dhd s" "dnargs (s[u/k]) = dnargs s"
    using App.IH(1)[of k e u] App.prems by auto
  have IHt: "lsz e (t[u/k]) = lsz (e\<langle>k:A\<rangle>) t" using App.IH(2)[of k e u] App.prems by auto
  show ?case
  proof (cases "is_Var (dhd s)")
    case True
    then obtain x T where h: "dhd s = Var x T" by (cases "dhd s") auto
    with IHs(5) have h': "dhd (s[u/k]) = Var x T" by simp
    show ?thesis using h h' IHs IHt by simp
  next
    case False
    then have F': "\<not> is_Var (dhd (s[u/k]))" using IHs(4) by simp
    have l1: "lsz e (s[u/k] $ t[u/k]) = tsz (spine_type e (s[u/k] $ t[u/k])) + asz e (s[u/k] $ t[u/k])"
      by (rule mcp_lsz_rigid) (use F' in simp_all)
    have l2: "lsz (e\<langle>k:A\<rangle>) (s $ t) = tsz (spine_type (e\<langle>k:A\<rangle>) (s $ t)) + asz (e\<langle>k:A\<rangle>) (s $ t)"
      by (rule mcp_lsz_rigid) (use False in simp_all)
    show ?thesis using l1 l2 IHs IHt False F' by simp
  qed
qed auto

lemma mcp_eta_dhd:
  "s \<rightarrow>\<^sub>\<eta> t \<Longrightarrow> no_redex s \<Longrightarrow> \<not> is_Abs s \<Longrightarrow> dhd t = dhd s \<and> dnargs t = dnargs s"
proof (induction rule: eta.induct)
  case (appL s t u)
  then show ?case by (cases s) auto
qed auto

lemma mcp_lsz_eta:
  assumes "s \<rightarrow>\<^sub>\<eta> t" "e \<turnstile> s : T" "no_redex s"
  shows "lsz e t = lsz e s \<and> (\<not> is_Abs s \<longrightarrow> asz e t = asz e s)"
  using assms
proof (induction arbitrary: e T rule: eta.induct)
  case (eta s a A dummy)
  from eta.prems(1) obtain U where T: "T = A \<rightarrow>\<^sub>T U" and ty: "e\<langle>0:A\<rangle> \<turnstile> s : A \<rightarrow>\<^sub>T U"
    by auto
  have nr: "no_redex s" "\<not> is_Abs s" using eta.prems(2) by auto
  have "lsz (e\<langle>0:A\<rangle>) (s $ Bound 0) + 2 = lsz (e\<langle>0:A\<rangle>) s"
    by (rule mcp_lsz_app_bound[OF ty nr]) simp
  moreover have "lsz e (s[dummy/0]) = lsz (e\<langle>0:A\<rangle>) s"
    using mcp_lsz_subst_dummy[OF eta.hyps] by simp
  ultimately show ?case by simp
next
  case (appL s t u)
  from appL.prems obtain A where tys: "e \<turnstile> s : A \<rightarrow>\<^sub>T T" and tyu: "e \<turnstile> u : A" by auto
  have nr: "no_redex s" "\<not> is_Abs s" "no_redex u" using appL.prems(2) by auto
  from appL.IH[OF tys nr(1)] nr(2) have IH: "lsz e t = lsz e s" "asz e t = asz e s" by auto
  have d: "dhd t = dhd s" "dnargs t = dnargs s" using mcp_eta_dhd[OF appL.hyps nr(1,2)] by auto
  have nAt: "\<not> is_Abs t" using eta_not_Abs[OF appL.hyps nr(2)] .
  have "no_redex t" using no_redex_eta[OF appL.hyps nr(1)] .
  moreover have "e \<turnstile> t : A \<rightarrow>\<^sub>T T" using subject_reduction_eta[OF appL.hyps tys] .
  ultimately have "spine_type e t = A \<rightarrow>\<^sub>T T" using spine_type_typing nAt by blast
  moreover have "spine_type e s = A \<rightarrow>\<^sub>T T" using spine_type_typing[OF tys nr(1,2)] .
  ultimately have sp: "spine_type e t = spine_type e s" by simp
  show ?case
  proof (cases "is_Var (dhd s)")
    case True
    then obtain x V where h: "dhd s = Var x V" by (cases "dhd s") auto
    then show ?thesis using d IH by simp
  next
    case False
    have l1: "lsz e (t $ u) = tsz (spine_type e (t $ u)) + asz e (t $ u)"
      by (rule mcp_lsz_rigid) (use False d in simp_all)
    have l2: "lsz e (s $ u) = tsz (spine_type e (s $ u)) + asz e (s $ u)"
      by (rule mcp_lsz_rigid) (use False in simp_all)
    show ?thesis using l1 l2 sp IH by simp
  qed
next
  case (appR s t u)
  from appR.prems obtain A where tyu: "e \<turnstile> u : A \<rightarrow>\<^sub>T T" and tys: "e \<turnstile> s : A" by auto
  have nr: "no_redex u" "\<not> is_Abs u" "no_redex s" using appR.prems(2) by auto
  from appR.IH[OF tys nr(3)] have IH: "lsz e t = lsz e s" by auto
  show ?case
  proof (cases "is_Var (dhd u)")
    case True
    then obtain x V where h: "dhd u = Var x V" by (cases "dhd u") auto
    then show ?thesis using IH by simp
  next
    case False
    have l1: "lsz e (u $ t) = tsz (spine_type e (u $ t)) + asz e (u $ t)"
      by (rule mcp_lsz_rigid) (use False in simp_all)
    have l2: "lsz e (u $ s) = tsz (spine_type e (u $ s)) + asz e (u $ s)"
      by (rule mcp_lsz_rigid) (use False in simp_all)
    show ?thesis using l1 l2 IH by simp
  qed
next
  case (abs s t a A)
  from abs.prems obtain U where T: "T = A \<rightarrow>\<^sub>T U" and ty: "e\<langle>0:A\<rangle> \<turnstile> s : U" by auto
  from abs.IH[OF ty] abs.prems(2) show ?case by simp
qed

lemma mcp_lsz_reds:
  assumes "s \<rightarrow>\<^sub>\<beta>\<^sub>\<eta>\<^sup>* t" "e \<turnstile> s : T" "no_redex s"
  shows "lsz e t = lsz e s \<and> no_redex t"
  using assms(1)
proof (induction rule: rtranclp_induct)
  case (step t u)
  have ty: "e \<turnstile> t : T" using subject_reduction_reds[OF step.hyps(1) assms(2)] .
  from step.IH have nt: "no_redex t" by simp
  from nt step.hyps(2) have tu: "t \<rightarrow>\<^sub>\<eta> u" by (auto simp: no_redex_iff)
  show ?case using mcp_lsz_eta[OF tu ty nt] no_redex_eta[OF tu nt] step.IH by simp
qed (simp add: assms(3))

text \<open>The size is invariant under \<open>\<alpha>\<beta>\<eta>\<close>-equivalence of well-typed \<open>\<beta>\<close>-normal terms:\<close>

theorem mcp_lsz_conv:
  assumes "s \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> t" "e \<turnstile> s : T" "e \<turnstile> t : T" "no_redex s" "no_redex t"
  shows "lsz e s = lsz e t"
proof -
  obtain u v where uv: "s \<rightarrow>\<^sub>\<beta>\<^sub>\<eta>\<^sup>* u" "t \<rightarrow>\<^sub>\<beta>\<^sub>\<eta>\<^sup>* v" "aconv_term u v"
    using church_rosser[OF _ assms(1)] assms(2) by (auto simp: wt_def)
  have "lsz e u = lsz e s" using mcp_lsz_reds[OF uv(1) assms(2,4)] by simp
  moreover have "lsz e v = lsz e t" using mcp_lsz_reds[OF uv(2) assms(3,5)] by simp
  ultimately show ?thesis using mcp_lsz_aconv[OF uv(3)] by simp
qed

subsection \<open>Abstractions over types\<close>

lemma mcp_no_redex_types_abs [simp]: "no_redex (types_abs Ts u) \<longleftrightarrow> no_redex u"
  by (induction Ts) simp_all

lemma mcp_lsz_types_abs: "lsz e (types_abs Ts u) = lsz (pushes e Ts) u + 2 * length Ts"
  by (induction Ts arbitrary: e) simp_all

lemma mcp_bvs_downs: "bvs n = map Bound (downs n)"
  by (induction n) simp_all

lemma mcp_eta_types_abs: "closed w \<Longrightarrow> types_abs Ts (w \<degree>\<degree> bvs (length Ts)) \<rightarrow>\<^sub>\<eta>\<^sup>* w"
  using eta_abs_list_downs[of w "map (\<lambda>T. (STR '''', T)) Ts"]
  by (simp add: types_abs_abs_list mcp_bvs_downs)

lemma mcp_conv_eta_types_abs:
  "closed w \<Longrightarrow> wt (types_abs Ts (w \<degree>\<degree> bvs (length Ts))) \<Longrightarrow> types_abs Ts (w \<degree>\<degree> bvs (length Ts)) \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> w"
  by (rule beta_eta_conv) (use mcp_eta_types_abs[of w Ts] in \<open>auto intro: rtranclp_mono[THEN predicate2D, rotated]\<close>)


subsection \<open>The measure\<close>

abbreviation mcp_e0 :: "integer \<Rightarrow> ptyp" where
  "mcp_e0 \<equiv> \<lambda>_. TFree STR '''' []"

text \<open>The size of the value of a variable, without its outer abstractions:\<close>

definition mcp_vsz :: "tinst \<Rightarrow> vsubst \<Rightarrow> indexname \<times> ptyp \<Rightarrow> nat" where
  "mcp_vsz \<rho> \<sigma> y = lsz mcp_e0 (bnorm (\<sigma> (fst y) (tsubst \<rho> (snd y)))) - 2 * arity (tsubst \<rho> (snd y))"

lemma mcp_vsz_val:
  assumes \<sigma>: "wt_subst \<sigma>" "cert_typ alg ar (tsubst \<rho> T)"
    and eq: "\<sigma> x (tsubst \<rho> T) \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> types_abs Ss s" and T: "tsubst \<rho> T = Ss \<Rrightarrow> U"
    and ty: "pushes mcp_e0 Ss \<turnstile> s : U" "no_redex s" and c: "\<forall>S\<in>set Ss. cert_typ alg ar S"
  shows "mcp_vsz \<rho> \<sigma> (x, T) = lsz (pushes mcp_e0 Ss) s - 2 * arity U"
proof -
  let ?w = "\<sigma> x (tsubst \<rho> T)"
  have tw: "mcp_e0 \<turnstile> ?w : tsubst \<rho> T" by (rule wt_subst_typing[OF \<sigma>])
  from bnorm_typed[OF tw] have b: "?w \<rightarrow>\<^sub>\<beta>\<^sup>* bnorm ?w" "no_redex (bnorm ?w)" by blast+
  have tb: "mcp_e0 \<turnstile> bnorm ?w : tsubst \<rho> T" by (rule subject_reduction_beta'[OF b(1) tw])
  have ta: "mcp_e0 \<turnstile> types_abs Ss s : tsubst \<rho> T" using typing_types_abs[OF ty(1) c] T by simp
  have "?w \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> bnorm ?w" by (rule conv_beta_eta[OF _ b(1)]) (use tw in \<open>auto simp: wt_def\<close>)
  then have c1: "bnorm ?w \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> types_abs Ss s" using eq by (blast intro: conv_sym conv_trans)
  have "lsz mcp_e0 (bnorm ?w) = lsz mcp_e0 (types_abs Ss s)"
    by (rule mcp_lsz_conv[OF c1 tb ta b(2)]) (simp add: ty(2))
  then show ?thesis using T by (simp add: mcp_vsz_def mcp_lsz_types_abs arity_funs)
qed

lemma mcp_vsz_agree:
  "tagree n \<rho> \<rho>' \<Longrightarrow> sagree n \<sigma> \<sigma>' \<Longrightarrow> snd x \<le> n \<Longrightarrow> tbelow n (tvars T) \<Longrightarrow>
    mcp_vsz \<rho>' \<sigma>' (x, T) = mcp_vsz \<rho> \<sigma> (x, T)"
  by (cases x) (simp add: mcp_vsz_def tsubst_agree sagree_def)


subsection \<open>The arity bound\<close>

text \<open>
  The arity condition on a solution, for an arity bound \<open>k\<close> (the analogue of \<open>kokA\<close> of the old
  development): the unbound type variables of the normal forms of the type variables of the
  problem are instantiated by types in which every chain of arrows has at most \<open>k\<close> argument
  types.
\<close>

fun mcp_aok :: "nat \<Rightarrow> ptyp \<Rightarrow> bool" where
  "mcp_aok k (Type a Ts) \<longleftrightarrow> arity (Type a Ts) \<le> k \<and> (\<forall>T\<in>set Ts. mcp_aok k T)"
| "mcp_aok k _ \<longleftrightarrow> True"

definition mcp_kok :: "nat \<Rightarrow> tinst \<Rightarrow> tyenv \<Rightarrow> (indexname \<times> psort) set \<Rightarrow> bool" where
  "mcp_kok k \<rho> \<theta> P \<longleftrightarrow> (\<forall>(v, S)\<in>P. \<forall>(w, S')\<in>tvars (tnorm \<theta> (TVar v S)). mcp_aok k (\<rho> w S'))"

lemma mcp_aok_arity: "mcp_aok k T \<Longrightarrow> arity T \<le> k"
  by (cases T) auto

lemma mcp_kok_unbound:
  assumes "mcp_kok k \<rho> \<theta> P" "(v, S) \<in> P" "vt_lookup \<theta> v = None" "tacyc \<theta>"
  shows "mcp_aok k (\<rho> v S)"
proof -
  from assms(1,2) have "\<forall>(w, S')\<in>tvars (tnorm \<theta> (TVar v S)). mcp_aok k (\<rho> w S')"
    unfolding mcp_kok_def by blast
  moreover have "tnorm \<theta> (TVar v S) = TVar v S" using assms(3) tnorm_TVar[OF assms(4)] by simp
  ultimately show ?thesis by simp
qed

lemma mcp_body_type_TVar:
  assumes "body_type env T = Some r"
  shows "r = Ok B \<Longrightarrow> is_TVar B \<Longrightarrow> \<exists>v S. B = TVar v S \<and> vt_lookup (tyenv env) v = None"
  using body_type_TVar[OF assms] by (cases B) auto

text \<open>The arity of the instance of the result type of a projection, if it is not a type variable:\<close>

lemma mcp_body_type_nonTVar_arity:
  assumes "ok (body_type env T) B" "\<not> is_TVar B" "tacyc (tyenv env)"
  shows "arity (tsubst \<rho> B) = 0"
proof -
  have nb: "\<forall>C D. tnorm (tyenv env) B \<noteq> C \<rightarrow>\<^sub>T D"
    using mf_body_type_sound[of env T "Ok B" B] assms(1,3) by auto
  show ?thesis
  proof (cases B)
    case (Type a Ts)
    then have "\<not> (a = STR ''fun'' \<and> (\<exists>T1 U. Ts = [T1, U]))" using nb by auto
    then show ?thesis using arity_other[of a Ts "tsubst \<rho>"] Type by simp
  qed (use assms(2) in auto)
qed


lemma mcp_aok_tsubst: "mcp_aok k (tsubst \<rho> T) \<Longrightarrow> (w, S) \<in> tvars T \<Longrightarrow> mcp_aok k (\<rho> w S)"
  by (induction T) auto

lemma mcp_aok_funs: "mcp_aok k (Ds \<Rrightarrow> U) \<Longrightarrow> \<forall>D\<in>set Ds. mcp_aok k D"
  by (induction Ds) auto

text \<open>
  The arity condition is kept for the type variables \<open>K\<close> of the invariant of the termination
  proof, which cover the type variables of the problem:
\<close>

definition mcp_kokK :: "nat \<Rightarrow> tinst \<Rightarrow> tyenv \<Rightarrow> (indexname \<times> psort) set \<Rightarrow> (indexname \<times> psort) set \<Rightarrow> bool" where
  "mcp_kokK k \<rho> \<theta> A K \<longleftrightarrow> K \<subseteq> tvars_env \<theta> \<union> A \<and> mcp_kok k \<rho> \<theta> K"

lemma mcp_kokK_kok:
  assumes kk: "mcp_kokK k \<rho> (tyenv env) A K" and ei: "einv A K env"
  shows "mcp_kok k \<rho> (tyenv env) (tvars_env (tyenv env) \<union> A)"
  unfolding mcp_kok_def
proof (intro ballI, clarify)
  let ?\<theta> = "tyenv env" and ?P = "tvars_env (tyenv env) \<union> A"
  fix v S w Sw assume vS: "(v, S) \<in> ?P" and w: "(w, Sw) \<in> tvars (tnorm ?\<theta> (TVar v S))"
  note x = einvD[OF ei]
  have KP: "K \<subseteq> ?P" and kok: "mcp_kok k \<rho> ?\<theta> K" using kk by (simp_all add: mcp_kokK_def)
  have sc: "scons ?P" using x(2) by (simp add: tinv_def)
  have "w \<in> uvars ?\<theta> (TVar v S)" using w by (force simp: uvars_def)
  with tcoveredD[OF x(11) vS] obtain k0 Sk where k0: "(k0, Sk) \<in> K" "w \<in> uvars ?\<theta> (TVar k0 Sk)"
    by (auto simp: uvarsA_def)
  then obtain Sw' where w': "(w, Sw') \<in> tvars (tnorm ?\<theta> (TVar k0 Sk))" by (auto simp: uvars_def)
  have "mcp_aok k (\<rho> w Sw')" using kok k0(1) w' by (auto simp: mcp_kok_def)
  moreover have "(w, Sw) \<in> ?P" using tvars_tnorm[OF x(6), of "TVar v S"] w vS by auto
  moreover have "(w, Sw') \<in> ?P" using tvars_tnorm[OF x(6), of "TVar k0 Sk"] w' k0(1) KP by auto
  ultimately have "Sw = Sw'" using sc unfolding scons_def by blast
  with \<open>mcp_aok k (\<rho> w Sw')\<close> show "mcp_aok k (\<rho> w Sw)" by simp
qed

lemma mcp_kokK_ext:
  assumes kk: "mcp_kokK k \<rho> \<theta> A K" and ext: "textends \<theta> \<theta>'" and ac': "tacyc \<theta>'" and tc': "tcons_env \<theta>'"
    and sol: "tsol \<theta>' \<rho>'" and ag: "tagree n \<rho> \<rho>'" and bl: "tbelow n (tvars_env \<theta> \<union> A)" and ac: "tacyc \<theta>"
    and cons: "\<And>T. tvars T \<subseteq> tvars_env \<theta>' \<union> A' \<Longrightarrow> tcons \<theta>' T"
    and sub: "tvars_env \<theta> \<subseteq> tvars_env \<theta>'" "A \<subseteq> A'"
    and N: "\<forall>(v, S)\<in>N. (v, S) \<in> tvars_env \<theta>' \<union> A' \<and> mcp_aok k (\<rho>' v S)"
  shows "mcp_kokK k \<rho>' \<theta>' A' (K \<union> N)"
  unfolding mcp_kokK_def
proof (intro conjI)
  have KP: "K \<subseteq> tvars_env \<theta> \<union> A" and kok: "mcp_kok k \<rho> \<theta> K" using kk by (simp_all add: mcp_kokK_def)
  show "K \<union> N \<subseteq> tvars_env \<theta>' \<union> A'" using KP sub N by auto
  have inv: "tsubst \<rho>' (tnorm \<theta>' (TVar v S)) = \<rho>' v S" if "(v, S) \<in> tvars_env \<theta>' \<union> A'" for v S
    using tsubst_tnorm[OF ac' tc' sol cons[of "TVar v S"]] that by simp
  show "mcp_kok k \<rho>' \<theta>' (K \<union> N)"
    unfolding mcp_kok_def
  proof (intro ballI, clarify)
    fix v S w Sw assume vS: "(v, S) \<in> K \<union> N" and w: "(w, Sw) \<in> tvars (tnorm \<theta>' (TVar v S))"
    show "mcp_aok k (\<rho>' w Sw)"
    proof (cases "(v, S) \<in> K")
      case True
      have e1: "tnorm \<theta>' (tnorm \<theta> (TVar v S)) = tnorm \<theta>' (TVar v S)" by (rule tnorm_textends[OF ac' ext])
      have e2: "tnorm \<theta>' (tnorm \<theta> (TVar v S)) = tsubst (\<lambda>w S. tnorm \<theta>' (TVar w S)) (tnorm \<theta> (TVar v S))"
        by (rule tnorm_tsubst)
      from w have "(w, Sw) \<in> tvars (tsubst (\<lambda>w S. tnorm \<theta>' (TVar w S)) (tnorm \<theta> (TVar v S)))"
        by (simp only: e2[symmetric] e1)
      then obtain w0 S0 where w0: "(w0, S0) \<in> tvars (tnorm \<theta> (TVar v S))"
        and ww: "(w, Sw) \<in> tvars (tnorm \<theta>' (TVar w0 S0))" unfolding tvars_tsubst by blast
      have aok0: "mcp_aok k (\<rho> w0 S0)" using kok True w0 by (auto simp: mcp_kok_def)
      have P0: "(w0, S0) \<in> tvars_env \<theta> \<union> A" using tvars_tnorm[OF ac, of "TVar v S"] w0 True KP by auto
      have "snd w0 \<le> n" using bspec[OF bl[unfolded tbelow_def] P0] by simp
      then have "\<rho>' w0 S0 = \<rho> w0 S0" using ag by (cases w0) (simp add: tagree_def)
      moreover have "tsubst \<rho>' (tnorm \<theta>' (TVar w0 S0)) = \<rho>' w0 S0" by (rule inv) (use P0 sub in auto)
      ultimately have "mcp_aok k (tsubst \<rho>' (tnorm \<theta>' (TVar w0 S0)))" using aok0 by simp
      from mcp_aok_tsubst[OF this ww] show ?thesis .
    next
      case False
      with vS N have "(v, S) \<in> tvars_env \<theta>' \<union> A'" "mcp_aok k (\<rho>' v S)" by auto
      with inv have "mcp_aok k (tsubst \<rho>' (tnorm \<theta>' (TVar v S)))" by simp
      from mcp_aok_tsubst[OF this w] show ?thesis .
    qed
  qed
qed

lemma mcp_solution_supd:
  assumes sol: "solution \<rho> \<sigma> env" and vi: "vinv \<rho> env X" and n: "maxidx env < snd x"
    and w: "closed w" "\<And>e. e \<turnstile> w : T"
  shows "solution \<rho> (supd \<sigma> x T w) env" "sagree (maxidx env) \<sigma> (supd \<sigma> x T w)" "wt_subst (supd \<sigma> x T w)"
proof -
  show sa: "sagree (maxidx env) \<sigma> (supd \<sigma> x T w)" by (rule sagree_supd[OF n])
  show wt: "wt_subst (supd \<sigma> x T w)" by (rule wt_subst_supd[OF solutionD(3)[OF sol] w])
  show "solution \<rho> (supd \<sigma> x T w) env" by (rule solution_extend[OF sol vi sa wt refl]) auto
qed

lemma mcp_typing_val:
  assumes "pushes mcp_e0 Ss \<turnstile> s : UU" "\<not> loose_bvar s (ilength Ss)" "\<forall>S\<in>set Ss. cert_typ alg ar S"
  shows "e \<turnstile> types_abs Ss s : Ss \<Rrightarrow> UU"
  by (rule typing_closed[OF typing_types_abs[OF assms(1,3)] closed_types_abs[OF assms(2)]])

lemma mcp_loose_combound: "\<not> loose_bvar G 0 \<Longrightarrow> \<not> loose_bvar (G \<degree>\<degree> bvs n) (integer_of_nat n)"
  by (auto simp: loose_bvar_apps integer_less_iff integer_less_eq_iff integer_of_nat.rep_eq loose_bvar_mono)


subsection \<open>Typings of arguments and bodies\<close>

lemma mcp_typings_append: "e \<tturnstile> ts : Ts \<Longrightarrow> e \<tturnstile> us : Us \<Longrightarrow> e \<tturnstile> ts @ us : Ts @ Us"
  by (induction ts arbitrary: Ts) (auto split: list.splits)

lemma mcp_typings_lift0:
  "e \<tturnstile> ts : Us \<Longrightarrow> e\<langle>0:A\<rangle> \<tturnstile> map (\<lambda>t. lift t 0) ts @ [Bound 0] : Us @ [A]"
proof -
  assume t: "e \<tturnstile> ts : Us"
  have "e\<langle>0:A\<rangle> \<tturnstile> map (\<lambda>t. lift t 0) ts : Us"
    using t by (induction ts arbitrary: Us) (auto split: list.splits)
  moreover have "e\<langle>0:A\<rangle> \<tturnstile> [Bound 0] : [A]" by auto
  ultimately show ?thesis by (rule mcp_typings_append)
qed

lemma mcp_typings_lift:
  "e \<tturnstile> map (inst \<rho>) ts : Us \<Longrightarrow>
    e\<langle>0:A\<rangle> \<tturnstile> map (inst \<rho>) (map (incr_boundvars 1) ts @ [Bound 0]) : Us @ [A]"
  using mcp_typings_lift0[of e "map (inst \<rho>) ts" Us A] by (simp add: incr_boundvars_1 comp_def)

lemma mcp_ilength_snoc: "ilength (xs @ [x]) = ilength xs + 1"
  by (simp add: ilength_eq integer_of_nat_eq_of_nat)

text \<open>The body of an abstraction, applied to the lifted arguments and the new bound variable:\<close>

lemma mcp_conv_abs_body:
  assumes W: "closed W" "e \<turnstile> W : Ss \<Rrightarrow> (A \<rightarrow>\<^sub>T U1)" and ts: "e \<tturnstile> ts : Ss"
    and eq: "W \<degree>\<degree> ts \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> Abs a A b" and tb: "e\<langle>0:A\<rangle> \<turnstile> b : U1" and cA: "cert_typ alg ar A"
  shows "(W \<degree>\<degree> map (\<lambda>t. lift t 0) ts) $ Bound 0 \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> b"
proof -
  have l: "W \<degree>\<degree> map (\<lambda>t. lift t 0) ts = lift (W \<degree>\<degree> ts) 0" by (simp add: incr_bv_apps incr_bv_closed W(1))
  have ty1: "e \<turnstile> W \<degree>\<degree> ts : A \<rightarrow>\<^sub>T U1" by (rule list_app_typeI[OF W(2) ts])
  have tyA: "e \<turnstile> Abs a A b : A \<rightarrow>\<^sub>T U1" using tb cA by auto
  have c1: "lift (W \<degree>\<degree> ts) 0 \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> lift (Abs a A b) 0" by (rule conv_lift[OF eq]) simp
  have "e\<langle>0:A\<rangle> \<turnstile> lift (W \<degree>\<degree> ts) 0 : A \<rightarrow>\<^sub>T U1" by (rule lift_type[OF ty1]) simp
  then have w1: "e\<langle>0:A\<rangle> \<turnstile> lift (W \<degree>\<degree> ts) 0 $ Bound 0 : U1" by auto
  have "e\<langle>0:A\<rangle> \<turnstile> lift (Abs a A b) 0 : A \<rightarrow>\<^sub>T U1" by (rule lift_type[OF tyA]) simp
  then have w2: "e\<langle>0:A\<rangle> \<turnstile> lift (Abs a A b) 0 $ Bound 0 : U1" by auto
  have c2: "lift (W \<degree>\<degree> ts) 0 $ Bound 0 \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> lift (Abs a A b) 0 $ Bound 0"
    by (rule conv_App[OF _ _ c1 conv_refl]) (use w1 w2 in \<open>auto simp: wt_def\<close>)
  have "lift (Abs a A b) 0 $ Bound 0 \<rightarrow>\<^sub>\<beta> b"
    using beta.beta[of a A "lift b 1" "Bound 0"] subst_lift_Bound[of 0 b] by simp
  then have c3: "lift (Abs a A b) 0 $ Bound 0 \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> b"
    by (rule conv_beta[rotated]) (use w2 in \<open>auto simp: wt_def\<close>)
  show ?thesis unfolding l using conv_trans[OF c2 c3] .
qed

lemma mcp_conv_eta_body:
  assumes ty: "e \<turnstile> s : A \<rightarrow>\<^sub>T U1" and cA: "cert_typ alg ar A"
  obtains s' where "e\<langle>0:A\<rangle> \<turnstile> s' : U1" "no_redex s'" "lift s 0 $ Bound 0 \<rightarrow>\<^sub>\<beta>\<^sup>* s'"
    "Abs a A s' \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> s" "e \<turnstile> Abs a A s' : A \<rightarrow>\<^sub>T U1"
proof -
  have "e\<langle>0:A\<rangle> \<turnstile> lift s 0 : A \<rightarrow>\<^sub>T U1" by (rule lift_type[OF ty]) simp
  then have t1: "e\<langle>0:A\<rangle> \<turnstile> lift s 0 $ Bound 0 : U1" by (rule typing.App) auto
  define s' where "s' = bnorm (lift s 0 $ Bound 0)"
  from bnorm_typed[OF t1] have b: "lift s 0 $ Bound 0 \<rightarrow>\<^sub>\<beta>\<^sup>* s'" "no_redex s'" by (simp_all add: s'_def)
  have t2: "e\<langle>0:A\<rangle> \<turnstile> s' : U1" by (rule subject_reduction_beta'[OF b(1) t1])
  have tA: "e \<turnstile> Abs a A s' : A \<rightarrow>\<^sub>T U1" using t2 cA by auto
  have tA0: "e \<turnstile> Abs a A (lift s 0 $ Bound 0) : A \<rightarrow>\<^sub>T U1" by (rule typing.Abs[OF cA t1])
  have "Abs a A (lift s 0 $ Bound 0) \<rightarrow>\<^sub>\<beta>\<^sup>* Abs a A s'" by (rule rtrancl_beta_Abs[OF b(1)])
  then have "Abs a A (lift s 0 $ Bound 0) \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> Abs a A s'" using tA0 by (intro conv_beta_eta) (auto simp: wt_def)
  moreover have "Abs a A (lift s 0 $ Bound 0) \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> s"
    by (rule beta_eta_conv) (use tA0 eta_lift_Bound0[of a A s] in \<open>auto simp: wt_def\<close>)
  ultimately have "Abs a A s' \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> s" by (blast intro: conv_sym conv_trans)
  with that t2 b tA show ?thesis by blast
qed


subsection \<open>Simultaneous substitution of the arguments\<close>

text \<open>As \<open>cpy\<close> of theory \<open>Unify_Match_Sound\<close>: the \<open>\<beta>\<close>-normal form of an abstraction over
  \<open>length ts\<close> variables applied to \<open>ts\<close>.\<close>

fun mcp_cpy :: "pterm list \<Rightarrow> pterm \<Rightarrow> pterm" where
  "mcp_cpy [] u = u"
| "mcp_cpy (t # ts) u = mcp_cpy ts (u[incr_bv (ilength ts) 0 t / ilength ts])"

lemma mcp_beta_cpy_abs_list: "length bs = length ts \<Longrightarrow> abs_list bs u \<degree>\<degree> ts \<rightarrow>\<^sub>\<beta>\<^sup>* mcp_cpy ts u"
proof (induction ts arbitrary: bs u)
  case (Cons t ts)
  then obtain x T bs' where bs: "bs = (x, T) # bs'" and l: "length bs' = length ts" by (cases bs) auto
  have il: "ilength bs' = ilength ts" using l by (simp add: ilength_eq)
  have "Abs x T (abs_list bs' u) $ t \<rightarrow>\<^sub>\<beta> (abs_list bs' u)[t/0]" by (rule beta.beta)
  also have "(abs_list bs' u)[t/0] = abs_list bs' (u[incr_bv (ilength ts) 0 t / ilength ts])"
    by (simp add: subst_abs_list il)
  finally have "abs_list bs u \<degree>\<degree> (t # ts) \<rightarrow>\<^sub>\<beta>\<^sup>* abs_list bs' (u[incr_bv (ilength ts) 0 t / ilength ts]) \<degree>\<degree> ts"
    unfolding bs by (simp add: r_into_rtranclp)
  also have "\<dots> \<rightarrow>\<^sub>\<beta>\<^sup>* mcp_cpy (t # ts) u" using Cons.IH[OF l] by simp
  finally show ?case .
qed simp

lemma mcp_beta_cpy: "length Ts = length ts \<Longrightarrow> types_abs Ts u \<degree>\<degree> ts \<rightarrow>\<^sub>\<beta>\<^sup>* mcp_cpy ts u"
  unfolding types_abs_abs_list by (rule mcp_beta_cpy_abs_list) simp

lemma mcp_cpy_App: "mcp_cpy ts (s $ t) = mcp_cpy ts s $ mcp_cpy ts t"
  by (induction ts arbitrary: s t) simp_all

lemma mcp_cpy_apps: "mcp_cpy ts (s \<degree>\<degree> us) = mcp_cpy ts s \<degree>\<degree> map (mcp_cpy ts) us"
  by (induction us arbitrary: s) (simp_all add: mcp_cpy_App)

lemma mcp_cpy_closed: "closed h \<Longrightarrow> mcp_cpy ts h = h"
  by (induction ts) (simp_all add: subst_no_loose closed_loose_bvar)

lemma mcp_cpy_incr: "mcp_cpy ts (incr_bv (ilength ts) 0 t) = t"
proof (induction ts arbitrary: t)
  case (Cons s ts)
  have "(incr_bv (ilength ts + 1) 0 t)[incr_bv (ilength ts) 0 s/ilength ts] = incr_bv (ilength ts) 0 t"
    using subst_incr_bv_Suc[of 0 "ilength ts" t] by (simp add: ilength_nonneg)
  with Cons.IH show ?case by (simp add: algebra_simps)
qed simp

lemma mcp_cpy_Bound:
  "0 \<le> j \<Longrightarrow> j < ilength ts \<Longrightarrow> mcp_cpy ts (Bound j) = ts ! (length ts - 1 - nat_of_integer j)"
proof (induction ts)
  case (Cons t ts)
  show ?case
  proof (cases "j = ilength ts")
    case True
    then have "nat_of_integer j = length ts" by (simp add: ilength_eq)
    with True show ?thesis by (simp add: mcp_cpy_incr)
  next
    case False
    with Cons.prems have j: "j < ilength ts" by (simp add: integer_arith)
    then have "nat_of_integer j < length ts" using Cons.prems(1) nat_of_integer_less_ilength by blast
    then have "(t # ts) ! (length (t # ts) - 1 - nat_of_integer j) = ts ! (length ts - 1 - nat_of_integer j)"
      by (simp add: nth_Cons' Suc_diff_Suc)
    with j Cons.IH Cons.prems False show ?thesis by (simp add: subst_Bound)
  qed
qed simp

lemma mcp_conv_cpy:
  assumes "e \<turnstile> types_abs Ts u \<degree>\<degree> ts : U" "length Ts = length ts"
  shows "types_abs Ts u \<degree>\<degree> ts \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> mcp_cpy ts u" "e \<turnstile> mcp_cpy ts u : U"
proof -
  have b: "types_abs Ts u \<degree>\<degree> ts \<rightarrow>\<^sub>\<beta>\<^sup>* mcp_cpy ts u" by (rule mcp_beta_cpy[OF assms(2)])
  show "types_abs Ts u \<degree>\<degree> ts \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> mcp_cpy ts u"
    by (rule conv_beta_eta[OF _ b]) (use assms(1) in \<open>auto simp: wt_def\<close>)
  show "e \<turnstile> mcp_cpy ts u : U" by (rule subject_reduction_beta'[OF b assms(1)])
qed


subsection \<open>The shape of the target\<close>

text \<open>A \<open>\<beta>\<close>-normal target of a type that is not a function type is an atom applied to arguments:\<close>

lemma mcp_target_shape:
  assumes ty: "e \<turnstile> s : UU" and nr: "no_redex s" and ar: "arity UU = 0"
  shows "s = fst (strip_comb s) \<degree>\<degree> snd (strip_comb s)" "atom (fst (strip_comb s))"
proof -
  show s: "s = fst (strip_comb s) \<degree>\<degree> snd (strip_comb s)" by (rule strip_comb_apps) simp
  have nA: "\<not> is_Abs s"
  proof
    assume "is_Abs s"
    then obtain a A b where "s = Abs a A b" by (cases s) auto
    with ty have "\<exists>B. UU = A \<rightarrow>\<^sub>T B" by auto
    with ar show False by auto
  qed
  have "\<not> (\<exists>f u. fst (strip_comb s) = f $ u)" by (simp add: head_of_not_App flip: head_of_strip_comb)
  moreover have "\<not> is_Abs (fst (strip_comb s))"
  proof
    assume h: "is_Abs (fst (strip_comb s))"
    show False
    proof (cases "snd (strip_comb s)" rule: rev_exhaust)
      case Nil
      with s h nA show False by simp
    next
      case (snoc ts t)
      then have "s = (fst (strip_comb s) \<degree>\<degree> ts) $ t" using s by simp
      moreover have "is_Abs (fst (strip_comb s) \<degree>\<degree> ts) \<longrightarrow> \<not> no_redex ((fst (strip_comb s) \<degree>\<degree> ts) $ t)"
        by (cases "fst (strip_comb s) \<degree>\<degree> ts") auto
      moreover have "\<not> no_redex (fst (strip_comb s) \<degree>\<degree> ts) \<longrightarrow> \<not> no_redex ((fst (strip_comb s) \<degree>\<degree> ts) $ t)"
        by (cases "fst (strip_comb s) \<degree>\<degree> ts") auto
      moreover have "is_Abs (fst (strip_comb s)) \<Longrightarrow> ts \<noteq> [] \<Longrightarrow> \<not> no_redex (fst (strip_comb s) \<degree>\<degree> ts)"
      proof -
        assume "is_Abs (fst (strip_comb s))" "ts \<noteq> []"
        then obtain ts' t' where "ts = t' # ts'" by (cases ts) auto
        have "\<not> no_redex (fst (strip_comb s) $ t')" using h by (cases "fst (strip_comb s)") auto
        moreover have "\<not> no_redex r \<Longrightarrow> \<not> no_redex (r \<degree>\<degree> us)" for r us
        proof (induction us arbitrary: r)
          case (Cons a us)
          have "\<not> no_redex (r $ a)" using Cons.prems by (cases r) auto
          then show ?case using Cons.IH by simp
        qed simp
        ultimately show ?thesis using \<open>ts = t' # ts'\<close> by simp
      qed
      ultimately show False using nr h by (cases "ts = []") auto
    qed
  qed
  ultimately show "atom (fst (strip_comb s))" by (cases "fst (strip_comb s)") auto
qed


subsection \<open>Reachability\<close>

abbreviation vns :: "pterm \<Rightarrow> indexname set" where
  "vns t \<equiv> fst ` vars t"

definition vreach :: "env \<Rightarrow> indexname set \<Rightarrow> indexname set" where
  "vreach env X = {y. \<exists>x\<in>X. (y, x) \<in> (dep env)\<^sup>*}"

lemma vreach_incl: "X \<subseteq> vreach env X"
  by (auto simp: vreach_def)

lemma vreach_subset: "X \<subseteq> Y \<Longrightarrow> vreach env X \<subseteq> vreach env Y"
  by (auto simp: vreach_def)

lemma vreach_Un: "vreach env (X \<union> Y) = vreach env X \<union> vreach env Y"
  by (auto simp: vreach_def)

lemma vreach_mono: "X \<subseteq> vreach env Y \<Longrightarrow> vreach env X \<subseteq> vreach env Y"
  by (auto simp: vreach_def intro: rtrancl_trans)

lemma vreach_absorb: "Y \<subseteq> vreach env Z \<Longrightarrow> vreach env (X \<union> Y) \<subseteq> vreach env (X \<union> Z)"
  using vreach_mono[of Y env Z] vreach_subset[of Z "X \<union> Z" env] by (auto simp: vreach_Un)

lemma vreach_tenv: "tenv env' = tenv env \<Longrightarrow> vreach env' = vreach env"
  by (simp add: vreach_def dep_def fun_eq_iff)

lemma vreach_step:
  assumes b: "vt_lookup (tenv env) x = Some (U, w)" and x: "x \<in> vreach env X"
  shows "vns w \<subseteq> vreach env X"
proof
  fix y assume y: "y \<in> vns w"
  from x obtain x' where "x' \<in> X" "(x, x') \<in> (dep env)\<^sup>*" by (auto simp: vreach_def)
  moreover have "(y, x) \<in> dep env" using y b by (auto simp: dep_def)
  ultimately show "y \<in> vreach env X" by (auto simp: vreach_def intro: converse_rtrancl_into_rtrancl)
qed

lemma vreach_update:
  assumes "tenv env' = vt_update (v, (T, w)) (tenv env)"
  shows "vreach env' X \<subseteq> vreach env (X \<union> vns w)"
proof
  fix y assume "y \<in> vreach env' X"
  then obtain x where x: "x \<in> X" "(y, x) \<in> (dep env')\<^sup>*" by (auto simp: vreach_def)
  from x(2) show "y \<in> vreach env (X \<union> vns w)"
  proof (induction rule: converse_rtrancl_induct)
    case base
    then show ?case using x(1) vreach_incl by blast
  next
    case (step y z)
    from step.hyps(1) obtain U u where b: "vt_lookup (tenv env') z = Some (U, u)" and yu: "y \<in> vns u"
      by (auto simp: dep_def)
    show ?case
    proof (cases "z = v")
      case True
      with b assms have "u = w" by simp
      with yu show ?thesis using vreach_incl[of "X \<union> vns w" env] by blast
    next
      case False
      with b assms have "vt_lookup (tenv env) z = Some (U, u)" by simp
      from vreach_step[OF this step.IH] yu show ?thesis by blast
    qed
  qed
qed


subsection \<open>Normalization\<close>

lemma head_norm_vreach_aux:
  assumes "head_norm env t = Some r"
  shows "r = Ok t' \<Longrightarrow> vns t' \<subseteq> vreach env (vns t)"
  using assms
proof (induction env t r arbitrary: t' rule: head_norm.raw_induct[rotated, consumes 1])
  case (1 hn env t r)
  note h = "1.hyps"[unfolded "1.prems"(1)]
  have IH: "vns s' \<subseteq> vreach env (vns s)" if "ok (hn env s) s'" for s s'
    using "1.IH"[OF that(1) refl] .
  show ?case
  proof (cases t)
    case (Var x T)
    with h obtain lr where lr: "ok (lookup env x T) lr"
      and rest: "ok (case lr of Some u \<Rightarrow> hn env u | None \<Rightarrow> return t) t'"
      by auto
    show ?thesis
    proof (cases lr)
      case None
      with rest have "t' = t" by simp
      then show ?thesis using vreach_incl by blast
    next
      case (Some w)
      from ok_lookup_Some[OF lr[unfolded Some]] obtain U where b: "vt_lookup (tenv env) x = Some (U, w)" .
      from Some rest have "ok (hn env w) t'" by simp
      from IH[OF this] have a: "vns t' \<subseteq> vreach env (vns w)" .
      have "x \<in> vreach env (vns t)" using Var vreach_incl[of "vns t" env] by auto
      from vreach_step[OF b this] have "vns w \<subseteq> vreach env (vns t)" .
      with a show ?thesis using vreach_mono by blast
    qed
  next
    case (Abs a T body)
    with h obtain b' where hb: "ok (hn env body) b'" and e: "t' = Abs a T b'" by auto
    from IH[OF hb] e Abs show ?thesis by simp
  next
    case (App f u)
    have sb: "vns (subst_bound u body) \<subseteq> vreach env (vns t)" if "vns body \<subseteq> vreach env (vns f)" for body
    proof -
      have "vars (subst_bound u body) \<subseteq> vars body \<union> vars u" by (simp add: subst_bound_subst vars_subst)
      then have "vns (subst_bound u body) \<subseteq> vns body \<union> vns u" by blast
      moreover have "vns f \<subseteq> vns t" "vns u \<subseteq> vns t" using App by auto
      moreover have "vreach env (vns f) \<subseteq> vreach env (vns t)" by (rule vreach_subset) fact
      moreover note vreach_incl[of "vns t" env]
      ultimately show ?thesis using that by (meson Un_least order_trans)
    qed
    show ?thesis
    proof (cases "is_Abs f")
      case True
      then obtain a T body where f: "f = Abs a T body" by (cases f) auto
      with h App have hs: "ok (hn env (subst_bound u body)) t'" by simp
      have "vns (subst_bound u body) \<subseteq> vreach env (vns t)" by (rule sb) (use f vreach_incl in auto)
      with IH[OF hs] vreach_mono show ?thesis by blast
    next
      case False
      with h App obtain nf where nf: "ok (hn env f) nf"
        and rest: "ok (case nf of Abs _ _ body \<Rightarrow> hn env (subst_bound u body) | _ \<Rightarrow> return (nf $ u)) t'"
        by (cases f) auto
      note IHf = IH[OF nf]
      show ?thesis
      proof (cases "is_Abs nf")
        case True
        then obtain a T body where nfa: "nf = Abs a T body" by (cases nf) auto
        with rest have hs: "ok (hn env (subst_bound u body)) t'" by simp
        have "vns (subst_bound u body) \<subseteq> vreach env (vns t)" by (rule sb) (use IHf nfa in simp)
        with IH[OF hs] vreach_mono show ?thesis by blast
      next
        case nA: False
        with rest have "t' = nf $ u" by (cases nf) auto
        with IHf App vreach_incl[of "vns t" env] vreach_subset[of "vns f" "vns t" env] show ?thesis by auto
      qed
    qed
  qed (use h in auto)
qed

lemma head_norm_vreach: "ok (head_norm env t) t' \<Longrightarrow> vns t' \<subseteq> vreach env (vns t)"
  using head_norm_vreach_aux[of env t _ t'] by auto

subsection \<open>Simplification\<close>

definition vdp :: "dpair \<Rightarrow> indexname set" where
  "vdp dp = (case dp of (rb, t, u) \<Rightarrow> vns t \<union> vns u)"

lemma vdp_simp [simp]: "vdp (rb, t, u) = vns t \<union> vns u"
  by (simp add: vdp_def)

abbreviation vdps :: "dpair list \<Rightarrow> indexname set" where
  "vdps dps \<equiv> \<Union> (vdp ` set dps)"

definition vsp :: "sstate \<Rightarrow> indexname set" where
  "vsp st = (case st of (env, ffs, frs) \<Rightarrow> vdps (ffs @ frs))"

lemma vsp_simp [simp]: "vsp (env, ffs, frs) = vdps ffs \<union> vdps frs"
  by (simp add: vsp_def)

text \<open>
  A step from \<open>st\<close> to \<open>st'\<close> on pairs with variables \<open>D\<close>: only variables reachable from \<open>D\<close>
  become reachable or bound, and the variables of the new pairs are reachable from those of the
  old pairs and \<open>D\<close>.
\<close>

definition vsr :: "indexname set \<Rightarrow> sstate \<Rightarrow> sstate \<Rightarrow> bool" where
  "vsr D st st' \<longleftrightarrow> (\<forall>X. vreach (fst st') X \<subseteq> vreach (fst st) (X \<union> D)) \<and>
    vsp st' \<subseteq> vreach (fst st) (vsp st \<union> D) \<and>
    (\<forall>x. vt_lookup (tenv (fst st')) x \<noteq> None \<longrightarrow> vt_lookup (tenv (fst st)) x = None \<longrightarrow> x \<in> vreach (fst st) D)"

lemma vsrD:
  assumes "vsr D st st'"
  shows "vreach (fst st') X \<subseteq> vreach (fst st) (X \<union> D)" "vsp st' \<subseteq> vreach (fst st) (vsp st \<union> D)"
    "vt_lookup (tenv (fst st')) x \<noteq> None \<Longrightarrow> vt_lookup (tenv (fst st)) x = None \<Longrightarrow> x \<in> vreach (fst st) D"
  using assms unfolding vsr_def by blast+

lemma vsr_refl: "vsr D st st"
  unfolding vsr_def using vreach_subset[of _ _ "fst st"] vreach_incl[of _ "fst st"] by blast

lemma vsr_tenv:
  "tenv e1 = tenv e \<Longrightarrow> vsr D (e1, ffs, frs) st' \<longleftrightarrow> vsr D (e, ffs, frs) st'"
  using vreach_tenv[of e1 e] by (simp add: vsr_def)

lemma vsr_trans:
  assumes "vsr D1 st st1" "vsr D2 st1 st2"
  shows "vsr (D1 \<union> D2) st st2"
  unfolding vsr_def
proof (intro conjI allI impI)
  let ?e = "fst st" and ?e1 = "fst st1" and ?e2 = "fst st2"
  fix X
  have "vreach ?e2 X \<subseteq> vreach ?e1 (X \<union> D2)" using assms(2) by (simp add: vsr_def)
  also have "\<dots> \<subseteq> vreach ?e (X \<union> D2 \<union> D1)" using assms(1) by (simp add: vsr_def)
  finally show "vreach ?e2 X \<subseteq> vreach ?e (X \<union> (D1 \<union> D2))" by (simp add: Un_ac)
next
  let ?e = "fst st" and ?e1 = "fst st1" and ?e2 = "fst st2"
  have "vsp st2 \<subseteq> vreach ?e1 (vsp st1 \<union> D2)" using assms(2) by (simp add: vsr_def)
  also have "\<dots> \<subseteq> vreach ?e (vsp st1 \<union> D2 \<union> D1)" using assms(1) by (simp add: vsr_def)
  also have "\<dots> \<subseteq> vreach ?e ((D2 \<union> D1) \<union> (vsp st \<union> D1))"
    using vreach_absorb[of "vsp st1" ?e "vsp st \<union> D1" "D2 \<union> D1"] assms(1) by (simp add: vsr_def Un_ac)
  finally show "vsp st2 \<subseteq> vreach ?e (vsp st \<union> (D1 \<union> D2))" by (simp add: Un_ac)
next
  let ?e = "fst st" and ?e1 = "fst st1" and ?e2 = "fst st2"
  fix x assume b: "vt_lookup (tenv ?e2) x \<noteq> None" and n: "vt_lookup (tenv ?e) x = None"
  show "x \<in> vreach ?e (D1 \<union> D2)"
  proof (cases "vt_lookup (tenv ?e1) x = None")
    case True
    with b assms(2) have "x \<in> vreach ?e1 D2" unfolding vsr_def by blast
    also have "\<dots> \<subseteq> vreach ?e (D2 \<union> D1)" using assms(1) by (simp add: vsr_def)
    finally show ?thesis by (simp add: Un_ac)
  next
    case False
    with n assms(1) have "x \<in> vreach ?e D1" unfolding vsr_def by blast
    then show ?thesis using vreach_subset[of D1 "D1 \<union> D2" ?e] by blast
  qed
qed

lemma vsr_mono:
  assumes "vsr D st st'" "D \<subseteq> vreach (fst st) D'"
  shows "vsr D' st st'"
  unfolding vsr_def
proof (intro conjI allI impI)
  fix X
  show "vreach (fst st') X \<subseteq> vreach (fst st) (X \<union> D')"
    using assms(1) vreach_absorb[OF assms(2), of X] by (auto simp: vsr_def)
  show "vsp st' \<subseteq> vreach (fst st) (vsp st \<union> D')"
    using assms(1) vreach_absorb[OF assms(2), of "vsp st"] by (auto simp: vsr_def)
next
  fix x assume "vt_lookup (tenv (fst st')) x \<noteq> None" "vt_lookup (tenv (fst st)) x = None"
  with assms(1) have "x \<in> vreach (fst st) D" unfolding vsr_def by blast
  then show "x \<in> vreach (fst st) D'" using vreach_mono[OF assms(2)] by blast
qed

lemma new_dpair_strip:
  "okW (new_dpair al rb t u env) ((rb', t', u'), env') \<Longrightarrow>
    t' = strip_abs_body t \<and> u' = strip_abs_body u \<and> tenv env' = tenv env"
proof (induction al rb t u env rule: new_dpair.induct)
  case (1 al rb a T body1 b U body2 env)
  define c where "c = (if a = STR '''' then b else a)"
  from "1.prems"(1) obtain env1 where cu: "okW (cunify_types al T U env) env1"
    and rec: "okW (new_dpair al ((c, T) # rb) body1 body2 env1) ((rb', t', u'), env')"
    by (auto simp: c_def Let_def)
  from "1.IH"[OF cu c_def rec] cunify_types_sound(1)[OF cu] show ?case by simp
qed auto

lemma vars_strip_abs_body [simp]: "vars (strip_abs_body t) = vars t"
  by (induction t) auto

lemma head_norm_dpair_vreach:
  assumes "okW (head_norm_dpair al env dp) (dp', env')"
  shows "vdp dp' \<subseteq> vreach env (vdp dp) \<and> tenv env' = tenv env"
proof -
  obtain rb t u where dp: "dp = (rb, t, u)" by (cases dp)
  obtain rb' t' u' where dp': "dp' = (rb', t', u')" by (cases dp')
  from assms obtain t1 t2 u1 u2 where h1: "ok (head_norm env t) t1" and e1: "ok (eta_norm env rb t1) t2"
    and h2: "ok (head_norm env u) u1" and e2: "ok (eta_norm env rb u1) u2"
    and nd: "okW (new_dpair al rb t2 u2 env) ((rb', t', u'), env')"
    by (auto simp: head_norm_dpair_def dp dp')
  note s = new_dpair_strip[OF nd]
  have "vns t' \<subseteq> vreach env (vns t)" using head_norm_vreach[OF h1] eta_norm_vars[OF e1] s by simp
  moreover have "vns u' \<subseteq> vreach env (vns u)" using head_norm_vreach[OF h2] eta_norm_vars[OF e2] s by simp
  ultimately show ?thesis
    using vreach_subset[of "vns t" "vns t \<union> vns u" env] vreach_subset[of "vns u" "vns t \<union> vns u" env] s
    by (auto simp: dp dp')
qed

lemma vars_head_of: "vars (head_of t) \<subseteq> vars t"
  by (induction t) auto

lemma assignment_vreach:
  assumes "okW (assignment al rb t u env) env'"
  shows "vreach env' X \<subseteq> vreach env (X \<union> vns u)"
    "vt_lookup (tenv env') x \<noteq> None \<Longrightarrow> vt_lookup (tenv env) x = None \<Longrightarrow> x \<in> vns t"
proof -
  from assms obtain v T oc where gev: "okW (get_eta_var rb 0 t) (v, T)"
    and oc: "ok (rigid_occurs_term env v u) oc"
    and rest: "okW (case oc of
        NoOcc \<Rightarrow> do {T1 \<leftarrow> liftM (body_type env T); T2 \<leftarrow> liftM (fastype env rb u);
          env' \<leftarrow> cunify_types al T1 T2 env; liftM (update (v, T) (rlist_abs rb u) env')}
      | Nonrigid \<Rightarrow> raiseW ASSIGN | Rigid \<Rightarrow> raiseW CANTUNIFY) env'"
    by (auto simp: assignment_def)
  from rest have "oc = NoOcc" by (cases oc) auto
  with rest obtain T1 T2 env1 where cu: "okW (cunify_types al T1 T2 env) env1"
    and upd: "ok (update (v, T) (rlist_abs rb u) env1) env'"
    by auto
  have te: "tenv env' = vt_update (v, (T, rlist_abs rb u)) (tenv env)"
    using ok_update(2)[OF upd] cunify_types_sound(1)[OF cu] by simp
  from vreach_update[OF te] show "vreach env' X \<subseteq> vreach env (X \<union> vns u)" by simp
  assume "vt_lookup (tenv env') x \<noteq> None" "vt_lookup (tenv env) x = None"
  with te have "x = v" by (auto split: if_splits)
  moreover have "(v, T) \<in> vars t"
    using get_eta_var_head[OF gev] vars_head_of[of t] by auto
  ultimately show "x \<in> vns t" by force
qed

lemma okW_assign_handle:
  assumes "okW (handleW (do {env' \<leftarrow> assignment al rb t u env; returnW (env', ffs, frs)})
    (\<lambda>e. case e of ASSIGN \<Rightarrow> returnW x | _ \<Rightarrow> raiseW e)) st'"
  shows "(\<exists>env'. okW (assignment al rb t u env) env' \<and> st' = (env', ffs, frs)) \<or> st' = x"
proof -
  from assms[unfolded okW_handleW] consider
    (a) "okW (do {env' \<leftarrow> assignment al rb t u env; returnW (env', ffs, frs)}) st'"
  | (b) e where "okW (case e of ASSIGN \<Rightarrow> returnW x | _ \<Rightarrow> raiseW e) st'"
    by blast
  then show ?thesis
  proof cases
    case a
    then show ?thesis by auto
  next
    case b
    from okW_ASSIGN_return[OF b] show ?thesis by simp
  qed
qed

lemma simrands_vreach:
  "(\<And>dp st st'. okW (F dp st) st' \<Longrightarrow> vsr (vdp dp) st st') \<Longrightarrow>
    okW (simrands F rb u0 t u st) st' \<Longrightarrow> vsr (vns t \<union> vns u) st st'"
proof (induction F rb u0 t u st arbitrary: st' rule: simrands.induct)
  case (1 F rb u0 f1 t g1 u st)
  from "1.prems"(2) obtain st1 where r: "okW (simrands F rb u0 f1 g1 st) st1"
    and s: "okW (F (rb, t, u) st1) st'" by auto
  have v1: "vsr (vns f1 \<union> vns g1) st st1" by (rule "1.IH"[OF "1.prems"(1) r])
  have v2: "vsr (vns t \<union> vns u) st1 st'" using "1.prems"(1)[OF s] by simp
  from vsr_trans[OF v1 v2] show ?case by (simp add: Un_ac image_Un)
qed (auto intro: vsr_refl)

lemma SIMPL0_rest_vreach:
  assumes F: "\<And>dp st st'. okW (S al dp st) st' \<Longrightarrow> vsr (vdp dp) st st'"
    and ok: "okW (SIMPL0_rest S al rb t u env ffs frs) st'"
  shows "vsr (vns t \<union> vns u) (env, ffs, frs) st'"
proof -
  let ?D = "vns t \<union> vns u"
  have keep: "vsr ?D (env, ffs, frs) (env', ffs', frs')"
    if "tenv env' = tenv env" "vsp (env', ffs', frs') \<subseteq> vsp (env, ffs, frs) \<union> ?D" for env' ffs' frs'
    unfolding vsr_def fst_conv
  proof (intro conjI allI impI)
    fix X
    show "vreach env' X \<subseteq> vreach env (X \<union> ?D)"
      unfolding vreach_tenv[OF that(1)] by (rule vreach_subset) blast
    show "vsp (env', ffs', frs') \<subseteq> vreach env (vsp (env, ffs, frs) \<union> ?D)"
      using that(2) vreach_incl[of "vsp (env, ffs, frs) \<union> ?D" env] by blast
  next
    fix x assume "vt_lookup (tenv env') x \<noteq> None" "vt_lookup (tenv env) x = None"
    with that(1) show "x \<in> vreach env ?D" by simp
  qed
  have asg: "vsr ?D (env, ffs, frs) (env', ffs, frs)" if "okW (assignment al rb s s' env) env'"
    "s = t \<and> s' = u \<or> s = u \<and> s' = t" for env' s s'
    unfolding vsr_def
  proof (intro conjI allI impI)
    note a = assignment_vreach[OF that(1)]
    fix X
    show "vreach (fst (env', ffs, frs)) X \<subseteq> vreach (fst (env, ffs, frs)) (X \<union> ?D)"
      using a(1)[of X] that(2) vreach_subset[of "X \<union> vns s'" "X \<union> ?D" env] by auto
    show "vsp (env', ffs, frs) \<subseteq> vreach (fst (env, ffs, frs)) (vsp (env, ffs, frs) \<union> ?D)"
      using vreach_incl[of "vsp (env, ffs, frs) \<union> ?D" env] by auto
  next
    fix x assume "vt_lookup (tenv (fst (env', ffs, frs))) x \<noteq> None" "vt_lookup (tenv (fst (env, ffs, frs))) x = None"
    with assignment_vreach(2)[OF that(1)] have "x \<in> vns s" by simp
    with that(2) show "x \<in> vreach (fst (env, ffs, frs)) ?D" using vreach_incl[of ?D env] by auto
  qed
  consider (VV) x T y U where "head_of t = Var x T" "head_of u = Var y U"
    | (VR) x T where "head_of t = Var x T" "\<not> is_Var (head_of u)"
    | (RV) y U where "\<not> is_Var (head_of t)" "head_of u = Var y U"
    | (RR) "\<not> is_Var (head_of t)" "\<not> is_Var (head_of u)"
    by (cases "head_of t"; cases "head_of u") auto
  then show ?thesis
  proof cases
    case VV
    with ok obtain T' U' env' where cu: "okW (cunify_types al T' U' env) env'"
      and st': "st' = (env', (rb, t, u) # ffs, frs)"
      by (auto simp: SIMPL0_rest_def)
    show ?thesis unfolding st' by (rule keep[OF cunify_types_sound(1)[OF cu]]) auto
  next
    case VR
    with ok have h: "okW (handleW (do {env' \<leftarrow> assignment al rb t u env; returnW (env', ffs, frs)})
      (\<lambda>e. case e of ASSIGN \<Rightarrow> returnW (env, ffs, (rb, t, u) # frs) | _ \<Rightarrow> raiseW e)) st'"
      by (cases "head_of u") (simp_all add: SIMPL0_rest_def)
    from okW_assign_handle[OF h] show ?thesis
    proof
      assume "\<exists>env'. okW (assignment al rb t u env) env' \<and> st' = (env', ffs, frs)"
      then obtain env' where "okW (assignment al rb t u env) env'" "st' = (env', ffs, frs)" by blast
      with asg show ?thesis by blast
    next
      assume "st' = (env, ffs, (rb, t, u) # frs)"
      then show ?thesis by (simp only:) (rule keep, auto)
    qed
  next
    case RV
    with ok have h: "okW (handleW (do {env' \<leftarrow> assignment al rb u t env; returnW (env', ffs, frs)})
      (\<lambda>e. case e of ASSIGN \<Rightarrow> returnW (env, ffs, (rb, u, t) # frs) | _ \<Rightarrow> raiseW e)) st'"
      by (cases "head_of t") (simp_all add: SIMPL0_rest_def)
    from okW_assign_handle[OF h] show ?thesis
    proof
      assume "\<exists>env'. okW (assignment al rb u t env) env' \<and> st' = (env', ffs, frs)"
      then obtain env' where "okW (assignment al rb u t env) env'" "st' = (env', ffs, frs)" by blast
      with asg show ?thesis by blast
    next
      assume "st' = (env, ffs, (rb, u, t) # frs)"
      then show ?thesis by (simp only:) (rule keep, auto)
    qed
  next
    case RR
    have ct: "tenv env' = tenv env" if "cunify_types al T U env = Some (evs, UOk env')" for T U evs env'
      using that by (intro cunify_types_sound(1)) blast
    from ok RR obtain env1 where e1: "tenv env1 = tenv env"
      and sr: "okW (simrands (S al) rb u t u (env1, ffs, frs)) st'"
      by (cases "head_of t"; cases "head_of u") (auto simp: SIMPL0_rest_def split: if_splits dest: ct)
    from simrands_vreach[OF F sr] show ?thesis by (simp add: vsr_tenv[OF e1])
  qed
qed

theorem SIMPL0_vreach:
  assumes "SIMPL0 al dp0 st = Some r"
  shows "snd r = UOk st' \<Longrightarrow> vsr (vdp dp0) st st'"
  using assms
proof (induction al dp0 st r arbitrary: st' rule: SIMPL0.raw_induct[rotated, consumes 1])
  case (1 S al dp0 st r)
  have IH: "vsr (vdp dp) st1 st2" if "okW (S al dp st1) st2" for dp st1 st2
  proof -
    from that obtain evs where "S al dp st1 = Some (evs, UOk st2)" by blast
    from "1.IH"[OF this] show ?thesis by simp
  qed
  obtain env ffs frs where st: "st = (env, ffs, frs)" by (cases st)
  have "\<exists>rb t u env1. okW (head_norm_dpair al env dp0) ((rb, t, u), env1) \<and>
      okW (SIMPL0_rest S al rb t u env1 ffs frs) st'"
    using okW_of_Some[OF "1.hyps" "1.prems"(1)] st by (auto simp: SIMPL0_rest_def split: prod.splits)
  then obtain rb t u env1 where hnd: "okW (head_norm_dpair al env dp0) ((rb, t, u), env1)"
    and step: "okW (SIMPL0_rest S al rb t u env1 ffs frs) st'"
    by blast
  note hd = head_norm_dpair_vreach[OF hnd]
  have e1: "tenv env1 = tenv env" using hd by simp
  from SIMPL0_rest_vreach[OF IH step] have "vsr (vns t \<union> vns u) (env1, ffs, frs) st'" .
  then have "vsr (vdp (rb, t, u)) (env, ffs, frs) st'" unfolding vsr_tenv[OF e1] by simp
  from vsr_mono[OF this] hd st show ?case by simp
qed

corollary SIMPL0_vreach': "okW (SIMPL0 al dp st) st' \<Longrightarrow> vsr (vdp dp) st st'"
  using SIMPL0_vreach by fastforce

lemma foldrW_SIMPL0_vreach: "okW (foldrW (SIMPL0 al) dps st) st' \<Longrightarrow> vsr (vdps dps) st st'"
proof (induction dps arbitrary: st')
  case (Cons dp dps)
  from Cons.prems(1) obtain st1 where f: "okW (foldrW (SIMPL0 al) dps st) st1"
    and s: "okW (SIMPL0 al dp st1) st'" by auto
  from vsr_trans[OF Cons.IH[OF f] SIMPL0_vreach'[OF s]] show ?case by (simp add: Un_ac)
qed (simp add: vsr_refl)

theorem SIMPL_vreach:
  assumes "SIMPL al env dpairs = Some r"
  shows "snd r = UOk st' \<Longrightarrow> vsr (vdps dpairs) (env, [], []) st'"
  using assms
proof (induction al env dpairs r arbitrary: st' rule: SIMPL.raw_induct[rotated, consumes 1])
  case (1 S al env dpairs r)
  have "\<exists>env1 ffs frs. okW (foldrW (SIMPL0 al) dpairs (env, [], [])) (env1, ffs, frs) \<and>
      (okW (S al env1 (frs @ ffs)) st' \<or> st' = (env1, ffs, frs))"
    using okW_of_Some[OF "1.hyps" "1.prems"(1)] by (auto simp: Let_def split: prod.splits if_splits)
  then obtain env1 ffs frs where f: "okW (foldrW (SIMPL0 al) dpairs (env, [], [])) (env1, ffs, frs)"
    and r: "okW (S al env1 (frs @ ffs)) st' \<or> st' = (env1, ffs, frs)"
    by blast
  have v1: "vsr (vdps dpairs) (env, [], []) (env1, ffs, frs)" by (rule foldrW_SIMPL0_vreach[OF f])
  show ?case
  proof (cases "okW (S al env1 (frs @ ffs)) st'")
    case True
    then obtain evs where "S al env1 (frs @ ffs) = Some (evs, UOk st')" by blast
    from "1.IH"[OF this] have v2: "vsr (vdps (frs @ ffs)) (env1, [], []) st'" by simp
    have sub: "vdps (frs @ ffs) \<subseteq> vreach env (vdps dpairs)" using v1 by (auto simp: vsr_def)
    show ?thesis
      unfolding vsr_def
    proof (intro conjI allI impI)
      fix X
      have "vreach (fst st') X \<subseteq> vreach env1 (X \<union> vdps (frs @ ffs))" using v2 by (simp add: vsr_def)
      also have "\<dots> \<subseteq> vreach env (X \<union> vdps (frs @ ffs) \<union> vdps dpairs)" using v1 by (simp add: vsr_def)
      also have "\<dots> \<subseteq> vreach env ((X \<union> vdps dpairs) \<union> vdps dpairs)"
        using vreach_absorb[OF sub, of "X \<union> vdps dpairs"] by (simp add: Un_ac)
      finally show "vreach (fst st') X \<subseteq> vreach (fst (env, [], [])) (X \<union> vdps dpairs)" by simp
      have "vsp st' \<subseteq> vreach env1 (vdps (frs @ ffs))" using v2 by (simp add: vsr_def)
      also have "\<dots> \<subseteq> vreach env (vdps (frs @ ffs) \<union> vdps dpairs)" using v1 by (simp add: vsr_def)
      also have "\<dots> \<subseteq> vreach env (vdps dpairs \<union> vdps dpairs)"
        using vreach_absorb[OF sub, of "vdps dpairs"] by (simp add: Un_ac)
      finally show "vsp st' \<subseteq> vreach (fst (env, [], [])) (vsp (env, [], []) \<union> vdps dpairs)" by simp
    next
      fix x assume b: "vt_lookup (tenv (fst st')) x \<noteq> None" and n: "vt_lookup (tenv (fst (env, [], []))) x = None"
      show "x \<in> vreach (fst (env, [], [])) (vdps dpairs)"
      proof (cases "vt_lookup (tenv env1) x = None")
        case True
        with b v2 have "x \<in> vreach env1 (vdps (frs @ ffs))" unfolding vsr_def fst_conv by blast
        also have "\<dots> \<subseteq> vreach env (vdps (frs @ ffs) \<union> vdps dpairs)" using v1 by (simp add: vsr_def)
        also have "\<dots> \<subseteq> vreach env (vdps dpairs \<union> vdps dpairs)"
          using vreach_absorb[OF sub, of "vdps dpairs"] by (simp add: Un_ac)
        finally show ?thesis by simp
      next
        case False
        with n v1 show ?thesis unfolding vsr_def fst_conv by blast
      qed
    qed
  next
    case False
    with r v1 show ?thesis by simp
  qed
qed

subsection \<open>Auxiliary lemmas for projections\<close>

lemma mcp_make_projs_mem:
  "okW (make_projs u targs0 Ts targs) ps \<Longrightarrow> k < length targs \<Longrightarrow>
    (Bound (integer_of_nat (length targs - 1 - k)), Ts ! k, targs ! k) \<in> set ps"
proof (induction u targs0 Ts targs arbitrary: ps k rule: make_projs.induct)
  case (1 u targs0 T Ts targ targs)
  from "1.prems"(1) obtain ps' where ps': "okW (make_projs u targs0 Ts targs) ps'"
    and ps: "ps = (Bound (ilength Ts), T, targ) # ps'" by auto
  have l: "length Ts = length targs" using make_projs_props[OF ps'] by simp
  show ?case
  proof (cases k)
    case 0
    then show ?thesis using ps l by (simp add: ilength_eq)
  next
    case (Suc k')
    with "1.prems"(2) have "k' < length targs" by simp
    from "1.IH"[OF ps' this] Suc ps show ?thesis by simp
  qed
qed auto

lemma mcp_funs_split:
  "Xs \<Rrightarrow> P = Ys \<Rrightarrow> U \<Longrightarrow> arity U = 0 \<Longrightarrow>
    length Xs \<le> length Ys \<and> Ys = Xs @ drop (length Xs) Ys \<and> P = drop (length Xs) Ys \<Rrightarrow> U"
proof (induction Xs arbitrary: Ys)
  case Nil
  then show ?case by simp
next
  case (Cons X Xs)
  show ?case
  proof (cases Ys)
    case Nil
    with Cons.prems show ?thesis by auto
  next
    case (Cons Y Ys')
    with Cons.prems have "X = Y" "Xs \<Rrightarrow> P = Ys' \<Rrightarrow> U" by auto
    with Cons.IH[OF this(2) Cons.prems(2)] Cons show ?thesis by simp
  qed
qed

lemma mcp_ncu_cuok: "ncu m P \<Longrightarrow> cuok m Q \<Longrightarrow> \<exists>x. okW m x \<and> P x \<and> Q x"
  unfolding ncu_def xokW_def by blast

lemma mcp_sum_set_le_list: "sum f (set xs) \<le> sum_list (map f xs)" for f :: "'a \<Rightarrow> nat"
proof (induction xs)
  case (Cons x xs)
  have "sum f (set (x # xs)) \<le> f x + sum f (set xs)" by (simp add: sum.insert_if)
  with Cons show ?case by simp
qed simp

lemma mcp_conv_types_abs_inv:
  "e \<turnstile> types_abs Ss x : V \<Longrightarrow> e \<turnstile> types_abs Ss y : V \<Longrightarrow> types_abs Ss x \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> types_abs Ss y \<Longrightarrow>
    x \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> y"
proof (induction Ss arbitrary: e V)
  case (Cons S Ss)
  from Cons.prems(1) obtain V1 where V: "V = S \<rightarrow>\<^sub>T V1" and t1: "e\<langle>0:S\<rangle> \<turnstile> types_abs Ss x : V1" by auto
  from Cons.prems(2) V have t2: "e\<langle>0:S\<rangle> \<turnstile> types_abs Ss y : V1" by auto
  have "types_abs Ss x \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> types_abs Ss y"
    using conv_Abs_inv(2)[of e "STR ''''" S "types_abs Ss x" V "STR ''''" S "types_abs Ss y"] Cons.prems by simp
  from Cons.IH[OF t1 t2 this] show ?case .
qed simp

text \<open>The arguments applied to the bound variables of the binders are the arguments:\<close>

lemma mcp_conv_bvs:
  assumes ty: "pushes mcp_e0 Ss \<turnstile> b : B" and lb: "\<not> loose_bvar b (ilength Ss)"
    and c: "\<forall>S\<in>set Ss. cert_typ alg ar S"
  shows "types_abs Ss b \<degree>\<degree> bvs (length Ss) \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> b"
    "pushes e Ss \<turnstile> types_abs Ss b \<degree>\<degree> bvs (length Ss) : B"
proof -
  have tv: "e' \<turnstile> types_abs Ss b : Ss \<Rrightarrow> B" for e' by (rule mcp_typing_val[OF ty lb c])
  show t: "pushes e Ss \<turnstile> types_abs Ss b \<degree>\<degree> bvs (length Ss) : B"
    by (rule list_app_typeI[OF tv typings_bvs])
  have t0: "pushes mcp_e0 Ss \<turnstile> types_abs Ss b \<degree>\<degree> bvs (length Ss) : B"
    by (rule list_app_typeI[OF tv typings_bvs])
  have t1: "mcp_e0 \<turnstile> types_abs Ss (types_abs Ss b \<degree>\<degree> bvs (length Ss)) : Ss \<Rrightarrow> B"
    by (rule typing_types_abs[OF t0 c])
  have "types_abs Ss (types_abs Ss b \<degree>\<degree> bvs (length Ss)) \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> types_abs Ss b"
    by (rule mcp_conv_eta_types_abs[OF closed_types_abs[OF lb]]) (use t1 in \<open>auto simp: wt_def\<close>)
  from mcp_conv_types_abs_inv[OF t1 typing_types_abs[OF ty c] this] show "types_abs Ss b \<degree>\<degree> bvs (length Ss) \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> b" .
qed

text \<open>The new type variables of a guess can be instantiated by arbitrary types:\<close>

lemma mcp_gentvars_inst:
  assumes g: "gentvars p env = (env0, Cs)" and l: "length Ds = p" and ws: "wsinst alg \<rho>"
  obtains \<rho>1 where "tagree (maxidx env) \<rho> \<rho>1" "map (tsubst \<rho>1) Cs = Ds" "wsinst alg \<rho>1"
    "\<And>v S. snd v \<noteq> maxidx env + 1 \<Longrightarrow> \<rho>1 v S = \<rho> v S"
proof (cases "p = 0")
  case True
  then have "Cs = []" using g by (simp add: gentvars_def)
  with True l that[of \<rho>] ws show ?thesis by (simp add: tagree_def)
next
  case False
  obtain i te tye where env: "env = Envir i te tye" by (cases env)
  let ?nm = "\<lambda>n::nat. aT + radixstring (integer_of_nat n)"
  have Cs: "Cs = map (\<lambda>n. TVar (?nm n, i + 1) []) [0..<p]" using g False by (simp add: gentvars_def env)
  have inj: "?nm n = ?nm n' \<Longrightarrow> n = n'" for n n'
    using radixstring_inj[of "integer_of_nat n" "integer_of_nat n'"]
    by (simp add: plus_literal_cancel integer_of_nat_eq_of_nat)
  define \<rho>1 where "\<rho>1 = (\<lambda>v S. if snd v = i + 1 \<and> S = [] \<and> (\<exists>n<p. fst v = ?nm n)
    then Ds ! (THE n. n < p \<and> fst v = ?nm n) else \<rho> v S)"
  show ?thesis
  proof (rule that[of \<rho>1])
    show "tagree (maxidx env) \<rho> \<rho>1" by (auto simp: tagree_def \<rho>1_def env)
    show "\<rho>1 v S = \<rho> v S" if "snd v \<noteq> maxidx env + 1" for v S using that by (simp add: \<rho>1_def env)
    show "wsinst alg \<rho>1" using ws by (auto simp: wsinst_def \<rho>1_def)
    have "\<rho>1 (?nm n, i + 1) [] = Ds ! n" if "n < p" for n
    proof -
      have "(THE n'. n' < p \<and> ?nm n = ?nm n') = n" using that inj by blast
      then show ?thesis using that by (auto simp: \<rho>1_def)
    qed
    then show "map (tsubst \<rho>1) Cs = Ds" using l by (auto simp: Cs intro!: nth_equalityI)
  qed
qed

subsection \<open>Auxiliary lemmas for the new variables\<close>

lemma mcp_apps_inj: "G \<degree>\<degree> bs = G' \<degree>\<degree> bs \<Longrightarrow> G = G'"
  by (induction bs arbitrary: G G') auto

lemma mcp_make_args_distinct:
  assumes ma: "make_args name Ts env Us = (env', args)" and a: "args = map (\<lambda>G. G \<degree>\<degree> bvs (length Ts)) Gs"
  shows "distinct (map var_of Gs)"
proof (cases "Us = []")
  case True
  with ma a show ?thesis by (simp add: make_args_def)
next
  case False
  obtain env1 vs where g: "genvars name env (map (\<lambda>T. Ts \<Rrightarrow> T) Us) = (env1, vs)" by fastforce
  with ma False have "args = map (\<lambda>var. combound var 0 (length Ts)) vs"
    by (auto simp: make_args_def List.null_iff)
  with a have "map (\<lambda>G. G \<degree>\<degree> bvs (length Ts)) Gs = map (\<lambda>G. G \<degree>\<degree> bvs (length Ts)) vs"
    by (simp add: combound_bvs)
  then have "Gs = vs" by (simp add: inj_map_eq_map inj_on_def mcp_apps_inj)
  with genvars_props(5)[OF g] show ?thesis by simp
qed

text \<open>A substitution updated at new variables:\<close>

definition mcp_supds :: "vsubst \<Rightarrow> (indexname \<times> ptyp) list \<Rightarrow> pterm list \<Rightarrow> vsubst" where
  "mcp_supds \<sigma> ys ws = (\<lambda>x T. case map_of (zip ys ws) (x, T) of Some w \<Rightarrow> w | None \<Rightarrow> \<sigma> x T)"

lemma mcp_supds_nth:
  "distinct ys \<Longrightarrow> length ys = length ws \<Longrightarrow> l < length ys \<Longrightarrow> mcp_supds \<sigma> ys ws (fst (ys ! l)) (snd (ys ! l)) = ws ! l"
  by (simp add: mcp_supds_def map_of_zip_nth)

lemma mcp_supds_other: "(x, T) \<notin> set ys \<Longrightarrow> mcp_supds \<sigma> ys ws x T = \<sigma> x T"
proof -
  assume "(x, T) \<notin> set ys"
  then have "map_of (zip ys ws) (x, T) = None"
    by (force simp: map_of_eq_None_iff dest: set_zip_leftD)
  then show ?thesis by (simp add: mcp_supds_def)
qed

lemma mcp_supds_ran: "mcp_supds \<sigma> ys ws x T = \<sigma> x T \<or> (\<exists>l < length ys. l < length ws \<and> mcp_supds \<sigma> ys ws x T = ws ! l)"
proof (cases "map_of (zip ys ws) (x, T)")
  case (Some w)
  then have "((x, T), w) \<in> set (zip ys ws)" by (rule map_of_SomeD)
  then obtain l where "l < length ys" "l < length ws" "w = ws ! l" by (auto simp: set_zip)
  with Some show ?thesis by (auto simp: mcp_supds_def)
qed (simp add: mcp_supds_def)

lemma mcp_solution_supds:
  assumes sol: "solution \<rho> \<sigma> env" and vi: "vinv \<rho> env X" and n: "\<forall>y\<in>set ys. maxidx env < snd (fst y)"
    and w: "\<forall>w\<in>set ws. closed w" "\<And>l e. l < length ys \<Longrightarrow> l < length ws \<Longrightarrow> e \<turnstile> ws ! l : snd (ys ! l)"
  shows "solution \<rho> (mcp_supds \<sigma> ys ws) env" "sagree (maxidx env) \<sigma> (mcp_supds \<sigma> ys ws)"
    "wt_subst (mcp_supds \<sigma> ys ws)"
proof -
  show sa: "sagree (maxidx env) \<sigma> (mcp_supds \<sigma> ys ws)"
    unfolding sagree_def
  proof (intro allI impI)
    fix x :: indexname and T :: ptyp assume "snd x \<le> maxidx env"
    then have "(x, T) \<notin> set ys" using n by force
    then show "mcp_supds \<sigma> ys ws x T = \<sigma> x T" by (rule mcp_supds_other)
  qed
  have \<sigma>: "wt_subst \<sigma>" by (rule solutionD(3)[OF sol])
  show wt: "wt_subst (mcp_supds \<sigma> ys ws)"
    unfolding wt_subst_def closed_subst_def
  proof (intro conjI allI impI)
    fix x :: indexname and T :: ptyp
    have "closed (\<sigma> x T)" using \<sigma> unfolding wt_subst_def closed_subst_def by blast
    with mcp_supds_ran[of \<sigma> ys ws x T] show "closed (mcp_supds \<sigma> ys ws x T)"
      using w(1) by auto
  next
    fix x :: indexname and T :: ptyp
    assume T: "cert_typ alg ar T"
    show "\<exists>e. e \<turnstile> mcp_supds \<sigma> ys ws x T : T"
    proof (cases "map_of (zip ys ws) (x, T)")
      case None
      then show ?thesis using wt_subst_typing[OF \<sigma> T] by (simp add: mcp_supds_def)
    next
      case (Some w')
      then have "((x, T), w') \<in> set (zip ys ws)" by (rule map_of_SomeD)
      then obtain l where "l < length ys" "l < length ws" "ys ! l = (x, T)" "w' = ws ! l" by (auto simp: set_zip)
      with Some w(2)[of l] show ?thesis by (auto simp: mcp_supds_def)
    qed
  qed
  show "solution \<rho> (mcp_supds \<sigma> ys ws) env" by (rule solution_extend[OF sol vi sa wt refl]) auto
qed


subsection \<open>Simplification and type unification\<close>

lemma mcp_SIMPL:
  assumes cfg: "cfg_alg cfg = alg" and fin: "finite X" "finite K"
    and si: "sinv A K X env dps" and inv: "scinv \<rho> \<sigma> env dps X A"
  obtains env2 ffs frs \<rho>' \<sigma>' where "okW (SIMPL (cfg_alg cfg) env dps) (env2, ffs, frs)"
    "simpl_post A K X env (env2, ffs, frs)" "scinv \<rho>' \<sigma>' env2 (frs @ ffs) X A"
    "tagree (maxidx env) \<rho> \<rho>'" "sagree (maxidx env) \<sigma> \<sigma>'"
proof -
  note t = SIMPL_term[OF fin si]
  from t obtain r where r: "SIMPL alg env dps = Some r" unfolding xokW_def by auto
  note c = SIMPL_complete[OF r fin si inv]
  from t c(1) r obtain st where ok: "okW (SIMPL alg env dps) st" "simpl_post A K X env st"
    unfolding xokW_def by auto
  obtain env2 ffs frs where st: "st = (env2, ffs, frs)" by (cases st)
  from ok(1) r st have "snd r = UOk (env2, ffs, frs)" by auto
  with c obtain \<rho>' \<sigma>' where "scinv \<rho>' \<sigma>' env2 (frs @ ffs) X A" "tagree (maxidx env) \<rho> \<rho>'" "sagree (maxidx env) \<sigma> \<sigma>'"
    by blast
  with ok st cfg that show ?thesis by simp
qed

lemma mcp_ncu_test_unify:
  "ncu (cunify_types alg' T U env) P \<Longrightarrow> ncu (test_unify_types alg' T U env) P"
  unfolding test_unify_types_def
  by (rule ncu_bindW) (auto simp: ncu_def whenW_def emit_def bindW_def returnW_def split: option.splits ures.splits)

lemma mcp_tsol_agree:
  assumes "tsol \<theta> \<rho>" "tagree n \<rho> \<rho>'" "tbelow n (tvars_env \<theta>)"
  shows "tsol \<theta> \<rho>'"
  unfolding tsol_def
proof (intro allI impI)
  fix v S U assume b: "vt_lookup \<theta> v = Some (S, U)"
  have "(v, S) \<in> tvars_env \<theta>" "tvars U \<subseteq> tvars_env \<theta>" using b unfolding tvars_env_def by blast+
  then have sv: "snd v \<le> n" and tU: "tbelow n (tvars U)" using assms(3) by (auto simp: tbelow_def)
  have "\<rho>' v S = \<rho> v S" using assms(2) sv unfolding tagree_def by (cases v) auto
  moreover have "tsubst \<rho>' U = tsubst \<rho> U" by (rule tsubst_agree[OF assms(2) tU])
  ultimately have "\<rho>' v S = \<rho> v S" "tsubst \<rho>' U = tsubst \<rho> U" by blast+
  with tsolD[OF assms(1) b] show "\<rho>' v S = tsubst \<rho>' U" by simp
qed

lemma mcp_wft_inst: "cert_typ alg ar (tsubst \<rho> T) \<Longrightarrow> wft ar T"
  by (rule wft_tsubstD[where \<rho> = \<rho>]) (simp add: cert_typ_def)

lemma mcp_solution_tenv:
  "solution \<rho> \<sigma> env \<Longrightarrow> tenv env' = tenv env \<Longrightarrow> tyenv env' = tyenv env \<Longrightarrow> solution \<rho> \<sigma> env'"
  by (simp add: solution_def)

subsection \<open>Simplification and the unbound variables\<close>

text \<open>
  \<^const>\<open>SIMPL\<close> binds only variables of the problem and adds no new unbound ones (by the
  reachability lemma @{thm [source] SIMPL_vreach} above):
\<close>

lemma mcp_sstepD:
  assumes "sstep A K X env env'"
  shows "extends env env'" "tvars_env (tyenv env) \<subseteq> tvars_env (tyenv env')"
  using assms by (simp_all add: sstep_def)

lemma mcp_dep_evars:
  assumes "(x, z) \<in> (dep env)\<^sup>*" "x \<noteq> z"
  shows "x \<in> fst ` evars env"
  using assms(1)
proof (cases rule: converse_rtranclE)
  case base
  with assms(2) show ?thesis by simp
next
  case (step w)
  from step(1) obtain U u where "vt_lookup (tenv env) w = Some (U, u)" "x \<in> fst ` vars u"
    by (auto simp: dep_def)
  then show ?thesis unfolding evars_def bnds_def by force
qed

lemma mcp_SIMPL_ubv:
  assumes ok: "okW (SIMPL alg env dps) (env', ffs, frs)" and fin: "finite X" "finite K"
    and si: "sinv A K X env dps"
  shows "ubv env' X \<subseteq> ubv env X"
proof
  have post: "simpl_post A K X env (env', ffs, frs)"
    using SIMPL_term[OF fin si] ok unfolding xokW_def by auto
  then have ext: "extends env env'" by (simp add: simpl_post_def sstep_def)
  from ok obtain r where r: "SIMPL alg env dps = Some r" "snd r = UOk (env', ffs, frs)" by auto
  have vs: "vsr (vdps dps) (env, [], []) (env', ffs, frs)" by (rule SIMPL_vreach[OF r])
  have D: "vdps dps \<subseteq> fst ` (X \<union> evars env)"
  proof
    fix y assume "y \<in> vdps dps"
    then obtain rb t u where "(rb, t, u) \<in> set dps" "y \<in> vns t \<union> vns u" by auto
    moreover have "upok A env rb X t u" if "(rb, t, u) \<in> set dps" using si that by (auto simp: sinv_def)
    ultimately show "y \<in> fst ` (X \<union> evars env)" using upokD(1,2) by blast
  qed
  fix x assume x: "x \<in> ubv env' X"
  then have ub': "vt_lookup (tenv env') x = None" and xX: "x \<in> fst ` (X \<union> evars env')" by (simp_all add: ubv_def)
  have ub: "vt_lookup (tenv env) x = None"
    using ub' ext unfolding extends_def by (metis option.distinct(1) not_None_eq)
  have "x \<in> fst ` (X \<union> evars env)"
  proof (cases "x \<in> fst ` X")
    case True
    then show ?thesis by blast
  next
    case False
    with xX have "x \<in> fst ` evars env'" by blast
    then obtain y U u where b: "vt_lookup (tenv env') y = Some (U, u)" and xy: "x = y \<or> x \<in> vns u"
      unfolding evars_def bnds_def by force
    with ub' have xu: "x \<in> vns u" by auto
    have "y \<in> vreach env' {y}" by (rule set_mp[OF vreach_incl]) simp
    from vreach_step[OF b this] xu have "x \<in> vreach env' {y}" by blast
    with vsrD(1)[OF vs, of "{y}"] have "x \<in> vreach env ({y} \<union> vdps dps)" by auto
    then obtain z where z: "z \<in> {y} \<union> vdps dps" "(x, z) \<in> (dep env)\<^sup>*" unfolding vreach_def by blast
    show ?thesis
    proof (cases "x = z")
      case True
      have "x \<noteq> y" using b ub' by auto
      with True z(1) D show ?thesis by blast
    next
      case False
      from mcp_dep_evars[OF z(2) False] show ?thesis by blast
    qed
  qed
  with ub show "x \<in> ubv env X" by (simp add: ubv_def)
qed

lemma mcp_arity_nonarrow: "(\<forall>C D. U \<noteq> C \<rightarrow>\<^sub>T D) \<Longrightarrow> arity U = 0"
proof (cases U)
  case (Type a Ts)
  assume n: "\<forall>C D. U \<noteq> C \<rightarrow>\<^sub>T D"
  show ?thesis
  proof (cases "a = STR ''fun'' \<and> (\<exists>T1 U1. Ts = [T1, U1])")
    case True
    with n Type show ?thesis by auto
  next
    case False
    then show ?thesis using arity_other[of a Ts "\<lambda>T. T"] Type by simp
  qed
qed simp_all

subsection \<open>The measure of a problem\<close>

text \<open>
  The measure of a problem with the variables \<open>X\<close> for a solution \<open>(\<rho>, \<sigma>)\<close>: the sum of the sizes
  of the values of its unbound variables. A variable is counted once, with any of its types in
  the problem; by @{const vcons} of the invariant, the size does not depend on the choice.
\<close>

definition mcp_rep :: "env \<Rightarrow> (indexname \<times> ptyp) set \<Rightarrow> indexname \<Rightarrow> ptyp" where
  "mcp_rep env X x = (SOME T. (x, T) \<in> X \<union> evars env)"

definition mcp_meas :: "tinst \<Rightarrow> vsubst \<Rightarrow> env \<Rightarrow> (indexname \<times> ptyp) set \<Rightarrow> nat" where
  "mcp_meas \<rho> \<sigma> env X = (\<Sum>x\<in>ubv env X. mcp_vsz \<rho> \<sigma> (x, mcp_rep env X x))"

lemma mcp_rep_mem: "x \<in> ubv env X \<Longrightarrow> (x, mcp_rep env X x) \<in> X \<union> evars env"
  unfolding ubv_def mcp_rep_def by (rule someI_ex) force

lemma mcp_vsz_vcons:
  "vcons \<rho> Y \<Longrightarrow> (x, T) \<in> Y \<Longrightarrow> (x, T') \<in> Y \<Longrightarrow> mcp_vsz \<rho> \<sigma> (x, T) = mcp_vsz \<rho> \<sigma> (x, T')"
  unfolding vcons_def mcp_vsz_def by (metis fst_conv snd_conv)

lemma mcp_vsz_rep:
  "vinv \<rho> env X \<Longrightarrow> x \<in> ubv env X \<Longrightarrow> (x, T) \<in> X \<union> evars env \<Longrightarrow>
    mcp_vsz \<rho> \<sigma> (x, mcp_rep env X x) = mcp_vsz \<rho> \<sigma> (x, T)"
  by (rule mcp_vsz_vcons[of \<rho> "X \<union> evars env"]) (simp_all add: vinv_def mcp_rep_mem[simplified])

text \<open>The value of an old variable in an agreeing solution:\<close>

lemma mcp_vsz_old:
  assumes inv: "scinv \<rho> \<sigma> env dps X A" and ag: "tagree (maxidx env) \<rho> \<rho>'" "sagree (maxidx env) \<sigma> \<sigma>'"
    and y: "y \<in> X \<union> evars env"
  shows "mcp_vsz \<rho>' \<sigma>' y = mcp_vsz \<rho> \<sigma> y"
proof -
  note i = scinvD[OF inv]
  obtain x T where yx: "y = (x, T)" by (cases y)
  have "snd x \<le> maxidx env" using i(3) y yx unfolding vinv_def below_def by force
  moreover have tT: "tvars T \<subseteq> vtvars (X \<union> evars env)" using y yx unfolding vtvars_def by force
  have "tbelow (maxidx env) (tvars T)"
    by (rule tvinv_tbelow[OF i(4)]) (use tT i(5) vtvars_evars[OF i(4)] in auto)
  ultimately show ?thesis using mcp_vsz_agree[OF ag] yx by simp
qed

lemma mcp_vsz_rep_old:
  assumes inv: "scinv \<rho> \<sigma> env dps X A" and ag: "tagree (maxidx env) \<rho> \<rho>'" "sagree (maxidx env) \<sigma> \<sigma>'"
    and vi': "vinv \<rho>' env' X'" and sub: "X \<union> evars env \<subseteq> X' \<union> evars env'"
    and x: "x \<in> ubv env X" "x \<in> ubv env' X'"
  shows "mcp_vsz \<rho>' \<sigma>' (x, mcp_rep env' X' x) = mcp_vsz \<rho> \<sigma> (x, mcp_rep env X x)"
proof -
  have m: "(x, mcp_rep env X x) \<in> X \<union> evars env" by (rule mcp_rep_mem[OF x(1)])
  have "mcp_vsz \<rho>' \<sigma>' (x, mcp_rep env' X' x) = mcp_vsz \<rho>' \<sigma>' (x, mcp_rep env X x)"
    by (rule mcp_vsz_rep[OF vi' x(2)]) (use m sub in blast)
  also have "\<dots> = mcp_vsz \<rho> \<sigma> (x, mcp_rep env X x)" by (rule mcp_vsz_old[OF inv ag m])
  finally show ?thesis .
qed

text \<open>\<^const>\<open>SIMPL\<close> does not increase the measure:\<close>

theorem SIMPL_meas:
  assumes ok: "okW (SIMPL alg env dps) (env', ffs, frs)" and fin: "finite X" "finite K"
    and si: "sinv A K X env dps" and inv: "scinv \<rho> \<sigma> env dps X A"
    and inv': "scinv \<rho>' \<sigma>' env' (frs @ ffs) X A"
    and ag: "tagree (maxidx env) \<rho> \<rho>'" "sagree (maxidx env) \<sigma> \<sigma>'"
  shows "mcp_meas \<rho>' \<sigma>' env' X \<le> mcp_meas \<rho> \<sigma> env X"
proof -
  have ub: "ubv env' X \<subseteq> ubv env X" by (rule mcp_SIMPL_ubv[OF ok fin si])
  have post: "simpl_post A K X env (env', ffs, frs)"
    using SIMPL_term[OF fin si] ok unfolding xokW_def by auto
  then have ext: "extends env env'" by (simp add: simpl_post_def sstep_def)
  have sub: "X \<union> evars env \<subseteq> X \<union> evars env'" using evars_extends[OF ext] by blast
  have "mcp_meas \<rho>' \<sigma>' env' X = (\<Sum>x\<in>ubv env' X. mcp_vsz \<rho> \<sigma> (x, mcp_rep env X x))"
    unfolding mcp_meas_def
    by (rule sum.cong[OF refl mcp_vsz_rep_old[OF inv ag scinvD(3)[OF inv'] sub]]) (use ub in blast)+
  also have "\<dots> \<le> mcp_meas \<rho> \<sigma> env X"
    unfolding mcp_meas_def by (rule sum_mono2[OF finite_ubv[OF fin(1)] ub]) simp
  finally show ?thesis .
qed


subsection \<open>Binding the variable of the pair\<close>

text \<open>The target of the copy: the body of the \<open>\<eta>\<close>-long \<open>\<beta>\<close>-normal form of the value of the variable.\<close>

lemma mcp_loose_reds: "s \<rightarrow>\<^sub>\<beta>\<^sup>* t \<Longrightarrow> 0 \<le> k \<Longrightarrow> \<not> loose_bvar s k \<Longrightarrow> \<not> loose_bvar t k"
  by (induction rule: rtranclp_induct) (auto dest: loose_bvar_beta)

lemma mcp_value_target:
  assumes wt: "wt_subst \<sigma>" and c: "cert_typ alg ar (Ss \<Rrightarrow> UU)"
  obtains s where "pushes mcp_e0 Ss \<turnstile> s : UU" "no_redex s" "\<not> loose_bvar s (ilength Ss)"
    "types_abs Ss s \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> \<sigma> x (Ss \<Rrightarrow> UU)"
proof -
  let ?w = "\<sigma> x (Ss \<Rrightarrow> UU)"
  have cw: "closed ?w" using wt by (simp add: wt_subst_def closed_substD)
  have tw: "pushes mcp_e0 Ss \<turnstile> ?w : Ss \<Rrightarrow> UU" by (rule wt_subst_typing[OF wt c])
  have cSs: "\<forall>S\<in>set Ss. cert_typ alg ar S" using c by (simp add: cert_typ_funs)
  define s0 where "s0 = ?w \<degree>\<degree> bvs (length Ss)"
  have t0: "pushes mcp_e0 Ss \<turnstile> s0 : UU" unfolding s0_def by (rule list_app_typeI[OF tw typings_bvs])
  define s where "s = bnorm s0"
  from bnorm_typed[OF t0] have b: "s0 \<rightarrow>\<^sub>\<beta>\<^sup>* s" "no_redex s" by (simp_all add: s_def)
  have ts: "pushes mcp_e0 Ss \<turnstile> s : UU" by (rule subject_reduction_beta'[OF b(1) t0])
  have "\<not> loose_bvar s0 (ilength Ss)"
    using mcp_loose_combound[of ?w "length Ss"] cw by (simp add: s0_def closed_def ilength_eq)
  then have ls: "\<not> loose_bvar s (ilength Ss)" by (rule mcp_loose_reds[OF b(1) ilength_nonneg])
  have ta0: "mcp_e0 \<turnstile> types_abs Ss s0 : Ss \<Rrightarrow> UU" by (rule typing_types_abs[OF t0 cSs])
  have ta: "mcp_e0 \<turnstile> types_abs Ss s : Ss \<Rrightarrow> UU" by (rule typing_types_abs[OF ts cSs])
  have c1: "types_abs Ss s0 \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ?w" unfolding s0_def
    by (rule mcp_conv_eta_types_abs[OF cw]) (use ta0 in \<open>auto simp: wt_def s0_def\<close>)
  have "s0 \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> s" by (rule conv_beta_eta[OF _ b(1)]) (use t0 in \<open>auto simp: wt_def\<close>)
  then have c2: "types_abs Ss s0 \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> types_abs Ss s"
    by (rule conv_types_abs[rotated 2]) (use ta0 ta in \<open>auto simp: wt_def\<close>)
  have "types_abs Ss s \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ?w" using c1 c2 by (blast intro: conv_sym conv_trans)
  with that ts b(2) ls show ?thesis by blast
qed

lemma mcp_solution_update:
  "ok (update (F, T) t env) env' \<Longrightarrow> solution \<rho> \<sigma> env \<Longrightarrow> \<sigma> F (tsubst \<rho> T) \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma> t \<Longrightarrow>
    solution \<rho> \<sigma> env'"
  using ok_update(2,3)[of F T t env env'] unfolding solution_def by auto

text \<open>The measure decreases if a variable is bound and the new variables are smaller:\<close>

lemma mcp_meas_bind:
  assumes inv: "scinv \<rho> \<sigma> env dps X A" and ag: "tagree (maxidx env) \<rho> \<rho>'" "sagree (maxidx env) \<sigma> \<sigma>'"
    and vi'': "vinv \<rho>' env'' X''" and sub: "X \<union> evars env \<subseteq> X'' \<union> evars env''"
    and finX: "finite X" and finX'': "finite X''" and finNV: "finite NV" and NVX: "NV \<subseteq> X''"
    and ub: "ubv env'' X'' \<subseteq> (ubv env X - {v}) \<union> fst ` NV" and vU: "v \<in> ubv env X"
    and lt: "(\<Sum>y\<in>NV. mcp_vsz \<rho>' \<sigma>' y) < mcp_vsz \<rho> \<sigma> (v, mcp_rep env X v)"
  shows "mcp_meas \<rho>' \<sigma>' env'' X'' < mcp_meas \<rho> \<sigma> env X"
proof -
  let ?S = "ubv env'' X''" and ?U = "ubv env X"
  let ?f = "\<lambda>x. mcp_vsz \<rho> \<sigma> (x, mcp_rep env X x)" and ?g = "\<lambda>x. mcp_vsz \<rho>' \<sigma>' (x, mcp_rep env'' X'' x)"
  have fS: "finite ?S" and fU: "finite ?U" using finite_ubv finX finX'' by blast+
  define NV' where "NV' = {y \<in> NV. fst y \<in> ?S}"
  have fNV': "finite NV'" using finNV by (simp add: NV'_def)
  have S: "?S = (?S \<inter> (?U - {v})) \<union> fst ` NV'"
  proof (rule equalityI; rule subsetI)
    fix x assume x: "x \<in> ?S"
    with ub have "x \<in> ?U - {v} \<or> x \<in> fst ` NV" by blast
    then show "x \<in> (?S \<inter> (?U - {v})) \<union> fst ` NV'"
    proof
      assume "x \<in> fst ` NV"
      then obtain y where y: "y \<in> NV" "x = fst y" by blast
      with x have "y \<in> NV'" unfolding NV'_def by blast
      with y(2) show ?thesis by blast
    qed (use x in blast)
  next
    fix x assume "x \<in> (?S \<inter> (?U - {v})) \<union> fst ` NV'"
    then show "x \<in> ?S" unfolding NV'_def by blast
  qed
  have "sum ?g ?S \<le> sum ?g (?S \<inter> (?U - {v})) + sum ?g (fst ` NV')"
    using sum_Un_nat[of "?S \<inter> (?U - {v})" "fst ` NV'" ?g] fS fNV' S by simp
  moreover have "sum ?g (?S \<inter> (?U - {v})) = sum ?f (?S \<inter> (?U - {v}))"
    by (rule sum.cong[OF refl mcp_vsz_rep_old[OF inv ag vi'' sub]]) auto
  moreover have "sum ?f (?S \<inter> (?U - {v})) \<le> sum ?f (?U - {v})"
    by (rule sum_mono2) (use fU in auto)
  moreover have "sum ?g (fst ` NV') \<le> sum (?g \<circ> fst) NV'" by (rule sum_image_le[OF fNV']) simp
  moreover have "sum (?g \<circ> fst) NV' = sum (mcp_vsz \<rho>' \<sigma>') NV'"
  proof (rule sum.cong[OF refl])
    fix y assume "y \<in> NV'"
    then have y: "y \<in> X''" "fst y \<in> ?S" using NVX by (auto simp: NV'_def)
    show "(?g \<circ> fst) y = mcp_vsz \<rho>' \<sigma>' y"
      using mcp_vsz_rep[OF vi'' y(2), of "snd y" \<sigma>'] y(1) by simp
  qed
  moreover have "sum (mcp_vsz \<rho>' \<sigma>') NV' \<le> sum (mcp_vsz \<rho>' \<sigma>') NV" by (rule sum_mono2[OF finNV]) (auto simp: NV'_def)
  moreover have "sum ?f ?U = ?f v + sum ?f (?U - {v})" by (rule sum.remove[OF fU vU])
  ultimately show ?thesis using lt unfolding mcp_meas_def by linarith
qed

text \<open>The result of \<^const>\<open>MATCH\<close>: a new problem in the invariants, for a solution that agrees on the
  old variables, keeps the arity condition and has a smaller measure.\<close>

definition mcp_mres :: "(indexname \<times> psort) set \<Rightarrow> (indexname \<times> psort) set \<Rightarrow> (indexname \<times> ptyp) set \<Rightarrow>
    env \<Rightarrow> tinst \<Rightarrow> vsubst \<Rightarrow> nat \<Rightarrow> elem \<Rightarrow> bool" where
  "mcp_mres A K X env \<rho> \<sigma> k x \<longleftrightarrow> (\<exists>env' dps' A' K' X' \<rho>' \<sigma>'. x = El_E env' dps' \<and>
    finite X' \<and> finite K' \<and> A \<subseteq> A' \<and> K \<subseteq> K' \<and> X \<subseteq> X' \<and> sinv A' K' X' env' dps' \<and>
    scinv \<rho>' \<sigma>' env' dps' X' A' \<and> extends env env' \<and> tagree (maxidx env) \<rho> \<rho>' \<and> sagree (maxidx env) \<sigma> \<sigma>' \<and>
    mcp_kokK k \<rho>' (tyenv env') A' K' \<and> mcp_meas \<rho>' \<sigma>' env' X' < mcp_meas \<rho> \<sigma> env X)"

lemma mcp_mresI:
  assumes "x = El_E env' dps'" "finite X'" "finite K'" "A \<subseteq> A'" "K \<subseteq> K'" "X \<subseteq> X'"
    "sinv A' K' X' env' dps'" "scinv \<rho>' \<sigma>' env' dps' X' A'" "extends env env'"
    "tagree (maxidx env) \<rho> \<rho>'" "sagree (maxidx env) \<sigma> \<sigma>'" "mcp_kokK k \<rho>' (tyenv env') A' K'"
    "mcp_meas \<rho>' \<sigma>' env' X' < mcp_meas \<rho> \<sigma> env X"
  shows "mcp_mres A K X env \<rho> \<sigma> k x"
  unfolding mcp_mres_def
  by (rule exI[of _ env'], rule exI[of _ dps'], rule exI[of _ A'], rule exI[of _ K'], rule exI[of _ X'],
      rule exI[of _ \<rho>'], rule exI[of _ \<sigma>']) (intro conjI; fact)


subsection \<open>The hypotheses of the copies\<close>

text \<open>
  The semantic hypotheses of a copy into the unassigned variable \<open>X0\<close>: \<open>(\<rho>, \<sigma>)\<close> solves the problem
  \<open>dps\<close>, which contains the pair of the copy, and the target \<open>s\<close>, a \<open>\<beta>\<close>-normal term under binders of the
  types \<open>Ss\<close> of the arguments, is the value of \<open>X0\<close> without its outer abstractions. The type \<open>UU\<close> of \<open>u\<close>
  has no more argument types than \<open>u\<close> has abstractions.
\<close>

definition mcc_spre :: "tinst \<Rightarrow> vsubst \<Rightarrow> env \<Rightarrow> dpair list \<Rightarrow> (indexname \<times> ptyp) set \<Rightarrow>
    (indexname \<times> psort) set \<Rightarrow> (integer \<Rightarrow> ptyp) \<Rightarrow> binders \<Rightarrow> indexname \<times> ptyp \<Rightarrow> pterm list \<Rightarrow>
    ptyp list \<Rightarrow> pterm \<Rightarrow> ptyp \<Rightarrow> pterm \<Rightarrow> bool" where
  "mcc_spre \<rho> \<sigma> env dps X A e rb X0 targs Ss u UU s \<longleftrightarrow> scinv \<rho> \<sigma> env dps X A \<and> bs_env \<rho> e rb \<and>
    e \<tturnstile> map (inst \<rho>) targs : Ss \<and> e \<turnstile> inst \<rho> u : UU \<and> arity UU = nabs u \<and>
    tsubst \<rho> (snd X0) = Ss \<Rrightarrow> UU \<and> cert_typ alg ar (Ss \<Rrightarrow> UU) \<and>
    pushes mcp_e0 Ss \<turnstile> s : UU \<and> no_redex s \<and> \<not> loose_bvar s (ilength Ss) \<and>
    \<sigma> (fst X0) (Ss \<Rrightarrow> UU) \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> types_abs Ss s"

lemma mcc_spreD:
  assumes "mcc_spre \<rho> \<sigma> env dps X A e rb X0 targs Ss u UU s"
  shows "scinv \<rho> \<sigma> env dps X A" "bs_env \<rho> e rb" "e \<tturnstile> map (inst \<rho>) targs : Ss" "e \<turnstile> inst \<rho> u : UU"
    "arity UU = nabs u" "tsubst \<rho> (snd X0) = Ss \<Rrightarrow> UU" "cert_typ alg ar (Ss \<Rrightarrow> UU)"
    "pushes mcp_e0 Ss \<turnstile> s : UU" "no_redex s" "\<not> loose_bvar s (ilength Ss)"
    "\<sigma> (fst X0) (Ss \<Rrightarrow> UU) \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> types_abs Ss s"
  using assms unfolding mcc_spre_def by blast+

text \<open>
  A result of a copy into \<open>X0\<close>: a new problem in the invariant of the copies, with a solution that
  agrees with \<open>(\<rho>, \<sigma>)\<close> on the old variables; \<open>X0\<close> is bound, and the values of the new unbound
  variables \<open>NV\<close> are smaller than the value of \<open>X0\<close>, by \<open>m\<close>.
\<close>

definition mcc_res :: "(indexname \<times> psort) set \<Rightarrow> env \<Rightarrow> (indexname \<times> ptyp) set \<Rightarrow> dpair list \<Rightarrow>
    (indexname \<times> psort) set \<Rightarrow> (indexname \<times> psort) set \<Rightarrow> (indexname \<times> ptyp) set \<Rightarrow> env \<Rightarrow>
    indexname \<times> ptyp \<Rightarrow> tinst \<Rightarrow> vsubst \<Rightarrow> nat \<Rightarrow> elem \<Rightarrow> bool" where
  "mcc_res A0 envM VM F A K X env X0 \<rho> \<sigma> m x \<longleftrightarrow>
    (\<exists>env' dps' A' K' X' \<rho>' \<sigma>' NV. x = El_E env' dps' \<and> cpinvX A0 envM VM F A' K' X' env' dps' \<and>
      A \<subseteq> A' \<and> K \<subseteq> K' \<and> X \<subseteq> X' \<and> scinv \<rho>' \<sigma>' env' (F @ dps') X' A' \<and> extends env env' \<and>
      tagree (maxidx env) \<rho> \<rho>' \<and> sagree (maxidx env) \<sigma> \<sigma>' \<and>
      finite NV \<and> NV \<subseteq> X' \<and> (\<forall>y\<in>NV. maxidx env < snd (fst y) \<or> y = X0) \<and>
      ubv env' X' \<subseteq> (ubv env X - {fst X0}) \<union> fst ` NV \<and>
      (\<Sum>y\<in>NV. mcp_vsz \<rho>' \<sigma>' y) + m \<le> mcp_vsz \<rho> \<sigma> X0 \<and>
      (\<forall>k. mcp_kokK k \<rho> (tyenv env) A K \<longrightarrow> mcp_kokK k \<rho>' (tyenv env') A' K'))"

lemma mcc_resI:
  assumes "x = El_E env' dps'" "cpinvX A0 envM VM F A' K' X' env' dps'"
    "A \<subseteq> A'" "K \<subseteq> K'" "X \<subseteq> X'" "scinv \<rho>' \<sigma>' env' (F @ dps') X' A'" "extends env env'"
    "tagree (maxidx env) \<rho> \<rho>'" "sagree (maxidx env) \<sigma> \<sigma>'"
    "finite NV" "NV \<subseteq> X'" "\<forall>y\<in>NV. maxidx env < snd (fst y) \<or> y = X0"
    "ubv env' X' \<subseteq> (ubv env X - {fst X0}) \<union> fst ` NV"
    "(\<Sum>y\<in>NV. mcp_vsz \<rho>' \<sigma>' y) + m \<le> mcp_vsz \<rho> \<sigma> X0"
    "\<forall>k. mcp_kokK k \<rho> (tyenv env) A K \<longrightarrow> mcp_kokK k \<rho>' (tyenv env') A' K'"
  shows "mcc_res A0 envM VM F A K X env X0 \<rho> \<sigma> m x"
  unfolding mcc_res_def
  by (rule exI[of _ env'], rule exI[of _ dps'], rule exI[of _ A'], rule exI[of _ K'], rule exI[of _ X'],
      rule exI[of _ \<rho>'], rule exI[of _ \<sigma>'], rule exI[of _ NV]) (intro conjI; fact)

lemma mcc_resE:
  assumes "mcc_res A0 envM VM F A K X env X0 \<rho> \<sigma> m x"
  obtains env' dps' A' K' X' \<rho>' \<sigma>' NV where "x = El_E env' dps'" "cpinvX A0 envM VM F A' K' X' env' dps'"
    "A \<subseteq> A'" "K \<subseteq> K'" "X \<subseteq> X'" "scinv \<rho>' \<sigma>' env' (F @ dps') X' A'" "extends env env'"
    "tagree (maxidx env) \<rho> \<rho>'" "sagree (maxidx env) \<sigma> \<sigma>'"
    "finite NV" "NV \<subseteq> X'" "\<forall>y\<in>NV. maxidx env < snd (fst y) \<or> y = X0"
    "ubv env' X' \<subseteq> (ubv env X - {fst X0}) \<union> fst ` NV"
    "(\<Sum>y\<in>NV. mcp_vsz \<rho>' \<sigma>' y) + m \<le> mcp_vsz \<rho> \<sigma> X0"
    "\<forall>k. mcp_kokK k \<rho> (tyenv env) A K \<longrightarrow> mcp_kokK k \<rho>' (tyenv env') A' K'"
  using assms unfolding mcc_res_def by (elim exE conjE) (rule that; assumption)

lemma mcc_res_m:
  assumes "mcc_res A0 envM VM F A K X env X0 \<rho> \<sigma> m x" "m' \<le> m"
  shows "mcc_res A0 envM VM F A K X env X0 \<rho> \<sigma> m' x"
  using assms(1)
proof (rule mcc_resE)
  fix env' dps' A' K' X' \<rho>' \<sigma>' NV
  assume a: "x = El_E env' dps'" "cpinvX A0 envM VM F A' K' X' env' dps'"
    "A \<subseteq> A'" "K \<subseteq> K'" "X \<subseteq> X'" "scinv \<rho>' \<sigma>' env' (F @ dps') X' A'" "extends env env'"
    "tagree (maxidx env) \<rho> \<rho>'" "sagree (maxidx env) \<sigma> \<sigma>'"
    "finite NV" "NV \<subseteq> X'" "\<forall>y\<in>NV. maxidx env < snd (fst y) \<or> y = X0"
    "ubv env' X' \<subseteq> (ubv env X - {fst X0}) \<union> fst ` NV"
    "(\<Sum>y\<in>NV. mcp_vsz \<rho>' \<sigma>' y) + m \<le> mcp_vsz \<rho> \<sigma> X0"
    "\<forall>k. mcp_kokK k \<rho> (tyenv env) A K \<longrightarrow> mcp_kokK k \<rho>' (tyenv env') A' K'"
  show ?thesis by (rule mcc_resI[OF a(1-13) _ a(15)]) (use a(14) assms(2) in simp)
qed

text \<open>The completeness invariant after a sound step, for the variables of the new pairs:\<close>

lemma mcc_scinv_step:
  assumes inv: "scinv \<rho> \<sigma> env dps X A" and p: "\<forall>(rb, t, u)\<in>set dps. upok A env rb X t u"
    and st: "dstep env dps env' dps'"
    and sol: "solution \<rho>' \<sigma>' env'" and ag: "tagree (maxidx env) \<rho> \<rho>'" "sagree (maxidx env) \<sigma> \<sigma>'"
    and ds: "dsolved \<rho>' \<sigma>' dps'" and tv: "tvinv A' env'"
    and vt: "vtvars (X \<union> dvars dps') \<subseteq> tvars_env (tyenv env') \<union> A'"
  shows "scinv \<rho>' \<sigma>' env' dps' (X \<union> dvars dps') A'"
  using scinv_step_core[OF inv p st sol ag] sol ds tv vt unfolding scinv_def by auto

lemma mcc_scinv_cpinvX:
  assumes inv: "scinv \<rho> \<sigma> env (F @ dps) X A" and c0: "cpinvX A0 envM VM F A K X env dps"
    and st: "dstep env dps env' dps'"
    and sol: "solution \<rho>' \<sigma>' env'" and ag: "tagree (maxidx env) \<rho> \<rho>'" "sagree (maxidx env) \<sigma> \<sigma>'"
    and ds: "dsolved \<rho>' \<sigma>' (F @ dps')" and c: "cpinvX A0 envM VM F A' K' (X \<union> dvars (F @ dps')) env' dps'"
  shows "scinv \<rho>' \<sigma>' env' (F @ dps') (X \<union> dvars (F @ dps')) A'"
proof (rule mcc_scinv_step[OF inv _ _ sol ag ds])
  show "\<forall>(rb, t, u)\<in>set (F @ dps). upok A env rb X t u" using c0 by (auto simp: cpinvX_def sinv_def)
  show "dstep env (F @ dps) env' (F @ dps')" by (rule dstep_set[OF dstep_frame[OF st, where fs = F]]) auto
  show "tvinv A' env'" using c by (auto simp: cpinvX_def sinv_def dest: einvD(1))
  show "vtvars (X \<union> dvars (F @ dps')) \<subseteq> tvars_env (tyenv env') \<union> A'" using c by (simp add: cpinvX_def)
qed

text \<open>The solution after binding an unassigned variable, with new variables for the binding:\<close>

lemma mcc_solution_bind:
  assumes sol: "solution \<rho> \<sigma> env" and vi: "vinv \<rho> env X"
    and \<sigma>': "sagree (maxidx env) \<sigma> \<sigma>'" "wt_subst \<sigma>'"
    and te: "tenv env1 = tenv env" "tyenv env1 = tyenv env"
    and up: "ok (update (v, TX) t env1) env2" and eq: "\<sigma>' v (tsubst \<rho> TX) \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma>' t"
  shows "solution \<rho> \<sigma>' env2"
proof -
  have "solution \<rho> \<sigma>' env" by (rule solution_extend[OF sol vi \<sigma>' refl]) auto
  then have "solution \<rho> \<sigma>' env1" by (rule mcp_solution_tenv[OF _ te])
  then show ?thesis by (rule mcp_solution_update[OF up _ eq])
qed

lemma mcc_ubv_bind:
  assumes up: "ok (update (v, TX) t env1) env2" and te: "tenv env1 = tenv env"
    and vX: "v \<in> fst ` (X' \<union> evars env)"
    and sub: "fst ` (X' \<union> evars env) \<subseteq> fst ` (X \<union> evars env) \<union> fst ` NV"
    and vt: "fst ` vars t \<subseteq> fst ` NV"
  shows "ubv env2 X' \<subseteq> (ubv env X - {v}) \<union> fst ` NV"
proof -
  have ev: "evars env1 = evars env" using te by (rule evars_tenv)
  have "ubv env2 X' \<subseteq> (ubv env1 X' - {v}) \<union> {y \<in> fst ` vars t. vt_lookup (tenv env2) y = None}"
    by (rule ubv_update[OF up]) (use vX ev in simp)
  moreover have "ubv env1 X' \<subseteq> ubv env X \<union> fst ` NV" using sub te ev unfolding ubv_def by auto
  ultimately show ?thesis using vt by blast
qed

subsection \<open>The pair of the copy\<close>

lemma mcc_cS:
  assumes "mcc_spre \<rho> \<sigma> env dps X A e rb X0 targs Ss u UU s"
  shows "\<forall>S\<in>set Ss. cert_typ alg ar S" "cert_typ alg ar UU"
  using mcc_spreD(7)[OF assms] by (simp_all add: cert_typ_funs)

lemma mcc_spre_cv:
  assumes sp: "mcc_spre \<rho> \<sigma> env dps X A e rb (v, TX) targs Ss u UU s"
    and P: "(rb, Var v TX \<degree>\<degree> targs, u) \<in> set dps"
  shows "types_abs Ss s \<degree>\<degree> map (ap \<rho> \<sigma>) targs \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma> u"
proof -
  note sp' = mcc_spreD[OF sp] and cS = mcc_cS[OF sp]
  note i = scinvD[OF sp'(1)] and sd = solutionD[OF scinvD(1)[OF sp'(1)]]
  have "ap \<rho> \<sigma> (Var v TX \<degree>\<degree> targs) \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma> u" using i(7) P by (auto simp: dsolved_def)
  moreover have "ap \<rho> \<sigma> (Var v TX \<degree>\<degree> targs) = \<sigma> v (Ss \<Rrightarrow> UU) \<degree>\<degree> map (ap \<rho> \<sigma>) targs"
    unfolding ap_apps using sp'(6) by (simp add: ap_def)
  moreover have "types_abs Ss s \<degree>\<degree> map (ap \<rho> \<sigma>) targs \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> \<sigma> v (Ss \<Rrightarrow> UU) \<degree>\<degree> map (ap \<rho> \<sigma>) targs"
  proof (rule conv_apps[OF _ _ _ conv_sym[OF sp'(11)[simplified]]])
    show "list_all2 (\<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta>) (map (ap \<rho> \<sigma>) targs) (map (ap \<rho> \<sigma>) targs)"
      by (simp add: list_all2_refl)
    have ta: "e \<tturnstile> map (ap \<rho> \<sigma>) targs : Ss"
      using sp'(3) by (induction targs arbitrary: Ss) (auto split: list.splits intro: typing_ap[OF _ sd(3)])
    have "e \<turnstile> types_abs Ss s : Ss \<Rrightarrow> UU" by (rule mcp_typing_val[OF sp'(8,10) cS(1)])
    from list_app_typeI[OF this ta] show "wt (types_abs Ss s \<degree>\<degree> map (ap \<rho> \<sigma>) targs)" by (auto simp: wt_def)
    have "e \<turnstile> \<sigma> v (Ss \<Rrightarrow> UU) : Ss \<Rrightarrow> UU" by (rule wt_subst_typing[OF sd(3) sp'(7)])
    from list_app_typeI[OF this ta] show "wt (\<sigma> v (Ss \<Rrightarrow> UU) \<degree>\<degree> map (ap \<rho> \<sigma>) targs)" by (auto simp: wt_def)
  qed
  ultimately show ?thesis by (metis conv_trans)
qed

text \<open>The size of the value of the variable of the copy:\<close>

lemma mcc_vsz:
  assumes sp: "mcc_spre \<rho> \<sigma> env dps X A e rb X0 targs Ss u UU s"
  shows "mcp_vsz \<rho> \<sigma> X0 = lsz (pushes mcp_e0 Ss) s - 2 * arity UU"
proof -
  note sp' = mcc_spreD[OF sp] and cS = mcc_cS[OF sp]
  note sd = solutionD[OF scinvD(1)[OF sp'(1)]]
  obtain x T where X0: "X0 = (x, T)" by (cases X0)
  show ?thesis using mcp_vsz_val[OF sd(3) _ _ _ sp'(8,9) cS(1), of \<rho> T x] sp'(6,7,11) X0 by simp
qed

subsection \<open>Copies: flexible heads\<close>

text \<open>A flexible head: the new variable gets the value of the variable of the copy.\<close>

lemma mcc_var:
  assumes pre: "mcpre A0 envM VM F A K X env rb (v, TX) targs u dps ot" and vN: "vt_lookup (tenv env) v = None"
    and ty0: "fastype env rb (fst (strip_comb u)) = return T0" "body_type env T0 = return base"
      "mapM (fastype env rb) targs = return Ts"
    and sp: "mcc_spre \<rho> \<sigma> env (F @ (rb, Var v TX \<degree>\<degree> targs, u) # dps) X A e rb (v, TX) targs Ss u UU s"
    and Var: "fst (strip_comb u) = Var w W" and g: "genvar (fst w) env (foldr fun_type Ts base) = (env', newhd)"
    and up: "ok (update (v, TX) (types_abs Ts (combound newhd 0 (length Ts))) env') env''"
  shows "mcc_res A0 envM VM F A K X env (v, TX) \<rho> \<sigma> 0 (El_E env'' ((rb, newhd \<degree>\<degree> targs, u) # dps))"
proof -
  let ?P = "(rb, Var v TX \<degree>\<degree> targs, u)" and ?P' = "(rb, newhd \<degree>\<degree> targs, u)"
  note st = mcs_var[OF pre vN ty0 Var g up]
  note sp' = mcc_spreD[OF sp] and cS = mcc_cS[OF sp]
  note inv = sp'(1)
  note i = scinvD[OF inv] and sd = solutionD[OF scinvD(1)[OF inv]]
  note gs = genvar_simps[OF g]
  have c0: "cpinvX A0 envM VM F A K X env (?P # dps)" by (rule mcpre_cpinvX[OF pre, simplified])
  have na: "\<not> is_Abs (fst (strip_comb u))" using Var by simp
  have Tsok: "ok (mapM (fastype env rb) targs) Ts" using ty0(3) by (simp add: return_def)
  have SsT: "map (tsubst \<rho>) Ts = Ss" by (rule mapM_fastype_sound(2)[OF Tsok sd(2) sp'(2,3)])
  have tyV: "e \<turnstile> inst \<rho> (Var v TX) : Ss \<Rrightarrow> UU" using sp'(6,7) by auto
  have tyt: "e \<turnstile> inst \<rho> (Var v TX \<degree>\<degree> targs) : UU"
    using list_app_typeI[OF tyV sp'(3)] by (simp add: inst_apps)
  have UUb: "UU = tsubst \<rho> base" by (rule mcs_bse[OF pre vN ty0 na sd(2) sp'(2) tyt sp'(4)])
  define y where "y = ((fst w, maxidx env + 1), foldr fun_type Ts base)"
  have nh: "newhd = Var (fst y) (snd y)" using gs(4) by (simp add: y_def)
  have Ty: "tsubst \<rho> (snd y) = Ss \<Rrightarrow> UU" using SsT UUb by (simp add: y_def tsubst_funs)
  have tyv: "\<And>e'. e' \<turnstile> types_abs Ss s : Ss \<Rrightarrow> UU" by (rule mcp_typing_val[OF sp'(8,10) cS(1)])
  have clv: "closed (types_abs Ss s)" by (rule closed_types_abs[OF sp'(10)])
  define \<sigma>' where "\<sigma>' = supd \<sigma> (fst y) (Ss \<Rrightarrow> UU) (types_abs Ss s)"
  have ny: "maxidx env < snd (fst y)" by (simp add: y_def)
  note su = mcp_solution_supd[OF i(1) i(3) ny clv tyv, folded \<sigma>'_def]
  have \<sigma>'y: "\<sigma>' (fst y) (tsubst \<rho> (snd y)) = types_abs Ss s" by (simp add: \<sigma>'_def Ty)
  have vb: "snd v \<le> maxidx env" by (rule mcs_facts(2)[OF pre vN ty0])
  have \<sigma>'v: "\<sigma>' v (tsubst \<rho> TX) = \<sigma> v (Ss \<Rrightarrow> UU)" using vb ny sp'(6) by (auto simp: \<sigma>'_def supd_def)
  have lenS: "length Ss = length Ts" using SsT by auto
  have apc: "ap \<rho> \<sigma>' (combound newhd 0 (length Ts)) = types_abs Ss s \<degree>\<degree> bvs (length Ss)"
    by (simp add: combound_bvs ap_apps nh \<sigma>'y comp_def lenS)
  have cc: "types_abs Ss (types_abs Ss s \<degree>\<degree> bvs (length Ss)) \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> types_abs Ss s"
  proof -
    have "pushes mcp_e0 Ss \<turnstile> types_abs Ss s \<degree>\<degree> bvs (length Ss) : UU"
      by (rule list_app_typeI[OF tyv typings_bvs])
    then have "mcp_e0 \<turnstile> types_abs Ss (types_abs Ss s \<degree>\<degree> bvs (length Ss)) : Ss \<Rrightarrow> UU"
      by (rule typing_types_abs[OF _ cS(1)])
    then show ?thesis by (intro mcp_conv_eta_types_abs[OF clv]) (auto simp: wt_def)
  qed
  have eqv: "\<sigma>' v (tsubst \<rho> TX) \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma>' (types_abs Ts (combound newhd 0 (length Ts)))"
    unfolding \<sigma>'v ap_types_abs SsT apc using sp'(11)[simplified] conv_sym[OF cc] by (blast intro: conv_trans)
  have sol: "solution \<rho> \<sigma>' env''" by (rule mcc_solution_bind[OF i(1) i(3) su(2,3) gs(1,2) up eqv])
  \<comment> \<open>The pairs are solved:\<close>
  have below_old: "below (maxidx env) (vars t)" if "vars t \<subseteq> X \<union> evars env" for t
    using i(3) that unfolding vinv_def by (meson below_mono order_refl)
  have ps: "\<forall>(rb', t', u')\<in>set (F @ ?P # dps). upok A env rb' X t' u'"
    using c0 by (auto simp: cpinvX_def sinv_def)
  have vu: "vars u \<subseteq> X \<union> evars env" and vt: "lvars targs \<subseteq> X \<union> evars env"
    using mcs_facts(3,4)[OF pre vN ty0] .
  have apu: "ap \<rho> \<sigma>' u = ap \<rho> \<sigma> u" by (rule ap_sagree[OF su(2) below_old[OF vu]])
  have apt: "map (ap \<rho> \<sigma>') targs = map (ap \<rho> \<sigma>) targs"
    using ap_sagree[OF su(2) below_old] vt by auto
  have ds: "dsolved \<rho> \<sigma>' (F @ ?P' # dps)"
  proof -
    have "ap \<rho> \<sigma>' (newhd \<degree>\<degree> targs) = types_abs Ss s \<degree>\<degree> map (ap \<rho> \<sigma>) targs"
      by (simp add: ap_apps nh \<sigma>'y apt)
    then have "ap \<rho> \<sigma>' (newhd \<degree>\<degree> targs) \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma>' u" using mcc_spre_cv[OF sp] apu by simp
    moreover have "dsolved \<rho> \<sigma>' (F @ ?P # dps)" by (rule sc_dps_agree(2)[OF ps i(4) i(3) tagree_refl su(2) i(7)])
    ultimately show ?thesis by (auto simp: dsolved_def)
  qed
  let ?X' = "X \<union> dvars (F @ ?P' # dps)"
  have inv': "scinv \<rho> \<sigma>' env'' (F @ ?P' # dps) ?X' A"
    by (rule mcc_scinv_cpinvX[OF inv c0 st(2) sol tagree_refl su(2) ds st(5)])
  \<comment> \<open>The measure:\<close>
  have vszy: "mcp_vsz \<rho> \<sigma>' y = lsz (pushes mcp_e0 Ss) s - 2 * arity UU"
    using mcp_vsz_val[OF su(3) _ _ Ty sp'(8,9) cS(1), of "fst y"] \<sigma>'y sp'(7) Ty by (cases y) simp
  have yX: "y \<in> ?X'" by (simp add: nh vars_apps)
  have vT: "(v, TX) \<in> X \<union> evars env"
    using upokD(1)[OF mcs_inv(3)[OF pre vN ty0]] by (auto simp: vars_apps)
  have ub: "ubv env'' ?X' \<subseteq> (ubv env X - {fst (v, TX)}) \<union> fst ` {y}"
    unfolding fst_conv
  proof (rule mcc_ubv_bind[OF up gs(1)])
    show "v \<in> fst ` (?X' \<union> evars env)" using vT by force
    have "dvars (F @ ?P' # dps) \<subseteq> {y} \<union> (X \<union> evars env)"
      using vu vt mcs_facts(7)[OF pre vN ty0] by (auto simp: nh vars_apps)
    then show "fst ` (?X' \<union> evars env) \<subseteq> fst ` (X \<union> evars env) \<union> fst ` {y}" by blast
    show "fst ` vars (types_abs Ts (combound newhd 0 (length Ts))) \<subseteq> fst ` {y}"
      by (auto simp: combound_bvs vars_apps nh)
  qed
  show ?thesis
  proof (rule mcc_resI[OF refl st(5) order_refl order_refl _ inv' st(4) tagree_refl su(2) _ _ _ ub])
    show "X \<subseteq> ?X'" by blast
    show "finite {y}" "{y} \<subseteq> ?X'" "\<forall>y'\<in>{y}. maxidx env < snd (fst y') \<or> y' = (v, TX)" using yX ny by auto
    show "(\<Sum>y\<in>{y}. mcp_vsz \<rho> \<sigma>' y) + 0 \<le> mcp_vsz \<rho> \<sigma> (v, TX)" using vszy mcc_vsz[OF sp] by simp
    show "\<forall>k. mcp_kokK k \<rho> (tyenv env) A K \<longrightarrow> mcp_kokK k \<rho> (tyenv env'') A K" using st(3) by simp
  qed
qed

text \<open>A result of a copy into a new variable \<open>Y\<close> that replaces the variable of the copy:\<close>

lemma mcc_res_step:
  assumes r: "mcc_res A0 envM VM F A K X1 env1 Y \<rho> \<sigma>1 m x"
    and ext: "extends env env1" and ag: "sagree (maxidx env) \<sigma> \<sigma>1" and XX: "X \<subseteq> X1"
    and ub1: "ubv env1 X1 \<subseteq> (ubv env X - {v}) \<union> {fst Y}"
    and sz: "mcp_vsz \<rho> \<sigma>1 Y \<le> mcp_vsz \<rho> \<sigma> (v, TX)" and ty: "tyenv env1 = tyenv env"
    and Ynew: "maxidx env < snd (fst Y)"
  shows "mcc_res A0 envM VM F A K X env (v, TX) \<rho> \<sigma> m x"
proof -
  have mx: "maxidx env \<le> maxidx env1" by (rule extends_maxidx[OF ext])
  from r show ?thesis
  proof (rule mcc_resE)
    fix env' dps' A' K' X' \<rho>' \<sigma>' NV
    assume a: "x = El_E env' dps'" "cpinvX A0 envM VM F A' K' X' env' dps'"
      "A \<subseteq> A'" "K \<subseteq> K'" "X1 \<subseteq> X'" "scinv \<rho>' \<sigma>' env' (F @ dps') X' A'" "extends env1 env'"
      "tagree (maxidx env1) \<rho> \<rho>'" "sagree (maxidx env1) \<sigma>1 \<sigma>'"
      "finite NV" "NV \<subseteq> X'" "\<forall>y\<in>NV. maxidx env1 < snd (fst y) \<or> y = Y"
      "ubv env' X' \<subseteq> (ubv env1 X1 - {fst Y}) \<union> fst ` NV"
      "(\<Sum>y\<in>NV. mcp_vsz \<rho>' \<sigma>' y) + m \<le> mcp_vsz \<rho> \<sigma>1 Y"
      "\<forall>k. mcp_kokK k \<rho> (tyenv env1) A K \<longrightarrow> mcp_kokK k \<rho>' (tyenv env') A' K'"
    show ?thesis
    proof (rule mcc_resI[OF a(1,2,3,4) _ a(6) extends_trans[OF ext a(7)] _ _ a(10,11)])
      show "X \<subseteq> X'" using XX a(5) by blast
      show "tagree (maxidx env) \<rho> \<rho>'" by (rule tagree_trans[OF tagree_refl a(8) mx])
      show "sagree (maxidx env) \<sigma> \<sigma>'" by (rule sagree_trans[OF ag a(9) mx])
      show "\<forall>y\<in>NV. maxidx env < snd (fst y) \<or> y = (v, TX)" using a(12) mx Ynew by fastforce
      show "ubv env' X' \<subseteq> (ubv env X - {fst (v, TX)}) \<union> fst ` NV" using a(13) ub1 by auto
      show "(\<Sum>y\<in>NV. mcp_vsz \<rho>' \<sigma>' y) + m \<le> mcp_vsz \<rho> \<sigma> (v, TX)" using a(14) sz by simp
      show "\<forall>k. mcp_kokK k \<rho> (tyenv env) A K \<longrightarrow> mcp_kokK k \<rho>' (tyenv env') A' K'" using a(15) ty by simp
    qed
  qed
qed

subsection \<open>Copies: abstractions\<close>

text \<open>An abstraction: the body is copied into a new variable, whose value is the body of the value.\<close>

lemma mcc_abs:
  assumes pre: "mcpre A0 envM VM F A K X env rb (v, TX) targs u dps ot" and vN: "vt_lookup (tenv env) v = None"
    and ty0: "fastype env rb (fst (strip_comb u)) = return T0" "body_type env T0 = return base"
      "mapM (fastype env rb) targs = return Ts"
    and sp: "mcc_spre \<rho> \<sigma> env (F @ (rb, Var v TX \<degree>\<degree> targs, u) # dps) X A e rb (v, TX) targs Ss u UU s"
    and Abs: "fst (strip_comb u) = Abs a Ta body" and fB: "fastype env ((a, Ta) # rb) body = return B"
    and tvB: "tvars B \<subseteq> tvars_env (tyenv env) \<union> A"
    and g: "genvar vname env (foldr fun_type (Ts @ [Ta]) B) = (env', Y)"
    and up: "ok (update (v, TX) (types_abs Ts (Abs a Ta (combound Y 0 (Suc (length Ts))))) env') env''"
    and IH: "\<And>X'' \<sigma>'' e'' Ss'' UU'' s''. lsz (pushes mcp_e0 Ss'') s'' < lsz (pushes mcp_e0 Ss) s \<Longrightarrow>
      mcpre A0 envM VM F A K X'' env'' ((a, Ta) # rb) ((vname, maxidx env + 1), foldr fun_type (Ts @ [Ta]) B)
        (map (incr_boundvars 1) targs @ [Bound 0]) body dps None \<Longrightarrow>
      mcc_spre \<rho> \<sigma>'' env'' (F @ ((a, Ta) # rb, Var (vname, maxidx env + 1) (foldr fun_type (Ts @ [Ta]) B) \<degree>\<degree>
          (map (incr_boundvars 1) targs @ [Bound 0]), body) # dps) X'' A e'' ((a, Ta) # rb)
        ((vname, maxidx env + 1), foldr fun_type (Ts @ [Ta]) B) (map (incr_boundvars 1) targs @ [Bound 0])
        Ss'' body UU'' s'' \<Longrightarrow>
      \<exists>x. P x \<and> mcc_res A0 envM VM F A K X'' env'' ((vname, maxidx env + 1), foldr fun_type (Ts @ [Ta]) B)
        \<rho> \<sigma>'' m x"
  shows "\<exists>x. P x \<and> mcc_res A0 envM VM F A K X env (v, TX) \<rho> \<sigma> m x"
proof -
  let ?P = "(rb, Var v TX \<degree>\<degree> targs, u)" and ?rb = "(a, Ta) # rb"
  let ?ts = "map (incr_boundvars 1) targs @ [Bound 0]"
  define y where "y = ((vname, maxidx env + 1), foldr fun_type (Ts @ [Ta]) B)"
  note st = mcs_abs[OF pre vN ty0 Abs fB tvB g up]
  note sp' = mcc_spreD[OF sp] and cS = mcc_cS[OF sp]
  note inv = sp'(1)
  note i = scinvD[OF inv] and sd = solutionD[OF scinvD(1)[OF inv]]
  note gs = genvar_simps[OF g]
  have c0: "cpinvX A0 envM VM F A K X env (?P # dps)" by (rule mcpre_cpinvX[OF pre, simplified])
  have u: "u = Abs a Ta body" by (rule st(1))
  have Yy: "Y = Var (fst y) (snd y)" using gs(4) by (simp add: y_def)
  have t1: "map (\<lambda>t. lift t 0) targs @ [Bound 0] = ?ts" by (simp add: map_incr_boundvars_lift)
  let ?pb = "(?rb, Var (fst y) (snd y) \<degree>\<degree> ?ts, body)"
  have d: "dstep env (?P # dps) env'' (?pb # dps)" using st(3) by (simp add: Yy t1)
  let ?X'' = "X \<union> dvars (F @ ?pb # dps)"
  have pre'': "mcpre A0 envM VM F A K ?X'' env'' ?rb y ?ts body dps None"
    using st(6) by (simp add: Yy t1 y_def)
  have c'': "cpinvX A0 envM VM F A K ?X'' env'' (?pb # dps)" using mcpre_cpinvX[OF pre''] by simp
  have Tsok: "ok (mapM (fastype env rb) targs) Ts" using ty0(3) by (simp add: return_def)
  have SsT: "map (tsubst \<rho>) Ts = Ss" by (rule mapM_fastype_sound(2)[OF Tsok sd(2) sp'(2,3)])
  \<comment> \<open>The target of the body:\<close>
  let ?A = "tsubst \<rho> Ta"
  from sp'(4)[unfolded u] obtain UU1 where cT: "cert_typ alg ar ?A"
    and tyb: "e\<langle>0:?A\<rangle> \<turnstile> inst \<rho> body : UU1" and UU: "UU = ?A \<rightarrow>\<^sub>T UU1" by auto
  obtain s' where s': "(pushes mcp_e0 Ss)\<langle>0:?A\<rangle> \<turnstile> s' : UU1" "no_redex s'" "lift s 0 $ Bound 0 \<rightarrow>\<^sub>\<beta>\<^sup>* s'"
      "Abs STR '''' ?A s' \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> s" "pushes mcp_e0 Ss \<turnstile> Abs STR '''' ?A s' : UU"
    using mcp_conv_eta_body[OF sp'(8)[unfolded UU] cT] UU by blast
  have lbs': "\<not> loose_bvar s' (ilength (Ss @ [?A]))"
  proof
    assume "loose_bvar s' (ilength (Ss @ [?A]))"
    moreover have "(sup beta eta)\<^sup>*\<^sup>* (lift s 0 $ Bound 0) s'"
      using s'(3) by (rule rtranclp_mono[THEN predicate2D, rotated]) auto
    ultimately have "loose_bvar (lift s 0 $ Bound 0) (ilength Ss + 1)"
      using loose_bvar_reds[of "lift s 0 $ Bound 0" s' "ilength Ss + 1"] ilength_nonneg[of Ss]
      by (simp add: mcp_ilength_snoc integer_arith)
    then show False using sp'(10) loose_bvar_lift[of 0 "ilength Ss" s] ilength_nonneg[of Ss]
      by (simp add: integer_arith)
  qed
  have W: "closed (types_abs Ss s)" "\<And>e'. e' \<turnstile> types_abs Ss s : Ss \<Rrightarrow> UU"
    using closed_types_abs[OF sp'(10)] mcp_typing_val[OF sp'(8,10) cS(1)] by blast+
  have W': "closed (types_abs (Ss @ [?A]) s')" by (rule closed_types_abs[OF lbs'])
  have cS': "\<forall>S\<in>set (Ss @ [?A]). cert_typ alg ar S" using cS(1) cT by simp
  have tW': "\<And>e'. e' \<turnstile> types_abs (Ss @ [?A]) s' : (Ss @ [?A]) \<Rrightarrow> UU1"
    by (rule mcp_typing_val) (use s'(1) lbs' cS' in \<open>simp_all add: pushes_append\<close>)
  have tae: "types_abs (Ss @ [?A]) s' = types_abs Ss (Abs STR '''' ?A s')" by (simp add: types_abs_append)
  have WW: "types_abs (Ss @ [?A]) s' \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> types_abs Ss s"
    unfolding tae
    by (rule conv_types_abs[OF _ _ s'(4)]) (use tW' W(2) tae in \<open>auto simp: wt_def\<close>)
  \<comment> \<open>The value of the new variable:\<close>
  have fBo: "ok (fastype env ?rb body) B" using fB by (simp add: return_def)
  have bs1: "bs_env \<rho> (e\<langle>0:?A\<rangle>) ?rb" by (rule bs_env_Cons[OF sp'(2) cT])
  have B1: "tsubst \<rho> B = UU1" by (rule fastype_sound[OF fBo sd(2) bs1 tyb])
  have Ty: "tsubst \<rho> (snd y) = (Ss @ [?A]) \<Rrightarrow> UU1" using SsT B1 by (simp add: y_def tsubst_funs)
  define \<sigma>' where "\<sigma>' = supd \<sigma> (fst y) ((Ss @ [?A]) \<Rrightarrow> UU1) (types_abs (Ss @ [?A]) s')"
  have ny: "maxidx env < snd (fst y)" by (simp add: y_def)
  note su = mcp_solution_supd[OF i(1) i(3) ny W' tW', folded \<sigma>'_def]
  have \<sigma>'y: "\<sigma>' (fst y) (tsubst \<rho> (snd y)) = types_abs (Ss @ [?A]) s'" by (simp add: \<sigma>'_def Ty)
  have vb: "snd v \<le> maxidx env" by (rule mcs_facts(2)[OF pre vN ty0])
  have \<sigma>'v: "\<sigma>' v (tsubst \<rho> TX) = \<sigma> v (Ss \<Rrightarrow> UU)" using vb ny sp'(6) by (auto simp: \<sigma>'_def supd_def)
  have lenS: "length Ss = length Ts" using SsT by auto
  have un: "unname (types_abs Ss t) = types_abs Ss (unname t)" for t by (induction Ss) simp_all
  let ?w = "types_abs (Ss @ [?A]) s' \<degree>\<degree> bvs (length (Ss @ [?A]))"
  have apc: "ap \<rho> \<sigma>' (types_abs Ts (Abs a Ta (combound Y 0 (Suc (length Ts))))) \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> types_abs (Ss @ [?A]) ?w"
  proof -
    have "ap \<rho> \<sigma>' (types_abs Ts (Abs a Ta (combound Y 0 (Suc (length Ts))))) = types_abs Ss (Abs a ?A ?w)"
      unfolding combound_bvs by (simp add: ap_types_abs SsT ap_apps Yy \<sigma>'y comp_def lenS)
    moreover have "aconv_term (types_abs Ss (Abs a ?A ?w)) (types_abs (Ss @ [?A]) ?w)"
      by (simp add: aconv_term_unname un types_abs_append)
    ultimately show ?thesis by (simp add: aconv_term_conv)
  qed
  have cc: "types_abs (Ss @ [?A]) ?w \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> types_abs (Ss @ [?A]) s'"
  proof -
    have "pushes mcp_e0 (Ss @ [?A]) \<turnstile> ?w : UU1" by (rule list_app_typeI[OF tW' typings_bvs])
    then have "mcp_e0 \<turnstile> types_abs (Ss @ [?A]) ?w : (Ss @ [?A]) \<Rrightarrow> UU1"
      by (rule typing_types_abs[OF _ cS'])
    then show ?thesis by (intro mcp_conv_eta_types_abs[OF W']) (auto simp: wt_def)
  qed
  have eqv: "\<sigma>' v (tsubst \<rho> TX) \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma>' (types_abs Ts (Abs a Ta (combound Y 0 (Suc (length Ts)))))"
    unfolding \<sigma>'v using sp'(11)[simplified] WW cc apc by (blast intro: conv_sym conv_trans)
  have sol: "solution \<rho> \<sigma>' env''" by (rule mcc_solution_bind[OF i(1) i(3) su(2,3) gs(1,2) up eqv])
  \<comment> \<open>The pairs are solved:\<close>
  have below_old: "below (maxidx env) (vars t)" if "vars t \<subseteq> X \<union> evars env" for t
    using i(3) that unfolding vinv_def by (meson below_mono order_refl)
  have ps: "\<forall>(rb', t', u')\<in>set (F @ ?P # dps). upok A env rb' X t' u'"
    using c0 by (auto simp: cpinvX_def sinv_def)
  have vu: "vars u \<subseteq> X \<union> evars env" and vt: "lvars targs \<subseteq> X \<union> evars env"
    using mcs_facts(3,4)[OF pre vN ty0] .
  have apu: "ap \<rho> \<sigma>' u = ap \<rho> \<sigma> u" by (rule ap_sagree[OF su(2) below_old[OF vu]])
  have apt: "map (ap \<rho> \<sigma>') targs = map (ap \<rho> \<sigma>) targs"
    using ap_sagree[OF su(2) below_old] vt by auto
  have tapt: "e \<tturnstile> map (ap \<rho> \<sigma>) targs : Ss"
    using sp'(3) by (induction targs arbitrary: Ss) (auto split: list.splits intro: typing_ap[OF _ sd(3)])
  have cvb: "types_abs (Ss @ [?A]) s' \<degree>\<degree> map (ap \<rho> \<sigma>) ?ts \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma> body"
  proof -
    have m: "map (ap \<rho> \<sigma>) ?ts = map (\<lambda>t. lift t 0) (map (ap \<rho> \<sigma>) targs) @ [Bound 0]"
      by (simp add: incr_boundvars_1 ap_lift[OF sd(3)])
    have c0: "types_abs Ss s \<degree>\<degree> map (ap \<rho> \<sigma>) targs \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> Abs a ?A (ap \<rho> \<sigma> body)"
      using mcc_spre_cv[OF sp] u by simp
    have c1: "(types_abs Ss s \<degree>\<degree> map (\<lambda>t. lift t 0) (map (ap \<rho> \<sigma>) targs)) $ Bound 0 \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma> body"
      by (rule mcp_conv_abs_body[OF W(1) W(2)[unfolded UU] tapt c0 typing_ap[OF tyb sd(3)] cT])
    have tl: "e\<langle>0:?A\<rangle> \<tturnstile> map (\<lambda>t. lift t 0) (map (ap \<rho> \<sigma>) targs) @ [Bound 0] : Ss @ [?A]"
      by (rule mcp_typings_lift0[OF tapt])
    have tW: "e' \<turnstile> types_abs Ss s : (Ss @ [?A]) \<Rrightarrow> UU1" for e' using W(2)[of e'] UU by simp
    have t1: "e\<langle>0:?A\<rangle> \<turnstile> types_abs (Ss @ [?A]) s' \<degree>\<degree> (map (\<lambda>t. lift t 0) (map (ap \<rho> \<sigma>) targs) @ [Bound 0]) : UU1"
      by (rule list_app_typeI[OF tW' tl])
    have t2: "e\<langle>0:?A\<rangle> \<turnstile> types_abs Ss s \<degree>\<degree> (map (\<lambda>t. lift t 0) (map (ap \<rho> \<sigma>) targs) @ [Bound 0]) : UU1"
      by (rule list_app_typeI[OF tW tl])
    have "types_abs (Ss @ [?A]) s' \<degree>\<degree> (map (\<lambda>t. lift t 0) (map (ap \<rho> \<sigma>) targs) @ [Bound 0]) \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta>
        types_abs Ss s \<degree>\<degree> (map (\<lambda>t. lift t 0) (map (ap \<rho> \<sigma>) targs) @ [Bound 0])"
      by (rule conv_apps[OF _ _ _ WW]) (use t1 t2 in \<open>auto simp: wt_def list.rel_refl\<close>)
    also have "\<dots> = (types_abs Ss s \<degree>\<degree> map (\<lambda>t. lift t 0) (map (ap \<rho> \<sigma>) targs)) $ Bound 0" by simp
    also have "\<dots> \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma> body" by (rule c1)
    finally show ?thesis unfolding m .
  qed
  have apts: "map (ap \<rho> \<sigma>') ?ts = map (ap \<rho> \<sigma>) ?ts"
  proof -
    have "ap \<rho> \<sigma>' t = ap \<rho> \<sigma> t" if "t \<in> set ?ts" for t
    proof -
      from that consider t0 where "t0 \<in> set targs" "t = incr_boundvars 1 t0" | "t = Bound 0" by auto
      then show ?thesis
      proof cases
        case 1
        have "vars t \<subseteq> X \<union> evars env" using 1 vt by (auto simp: incr_boundvars_def)
        then show ?thesis by (rule ap_sagree[OF su(2) below_old])
      qed (simp add: ap_def)
    qed
    then show ?thesis by (simp del: map_append)
  qed
  have apb: "ap \<rho> \<sigma>' body = ap \<rho> \<sigma> body" using apu by (simp add: u)
  have ds: "dsolved \<rho> \<sigma>' (F @ ?pb # dps)"
  proof -
    have "ap \<rho> \<sigma>' (Var (fst y) (snd y) \<degree>\<degree> ?ts) = types_abs (Ss @ [?A]) s' \<degree>\<degree> map (ap \<rho> \<sigma>) ?ts"
      unfolding ap_apps apts by (simp add: \<sigma>'y)
    then have "ap \<rho> \<sigma>' (Var (fst y) (snd y) \<degree>\<degree> ?ts) \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma>' body" using cvb apb by simp
    moreover have "dsolved \<rho> \<sigma>' (F @ ?P # dps)" by (rule sc_dps_agree(2)[OF ps i(4) i(3) tagree_refl su(2) i(7)])
    ultimately show ?thesis by (auto simp: dsolved_def)
  qed
  have inv'': "scinv \<rho> \<sigma>' env'' (F @ ?pb # dps) ?X'' A"
    by (rule mcc_scinv_cpinvX[OF inv c0 d sol tagree_refl su(2) ds c''])
  \<comment> \<open>The hypotheses for the body:\<close>
  have pe: "pushes mcp_e0 (Ss @ [?A]) = (pushes mcp_e0 Ss)\<langle>0:?A\<rangle>" by (simp add: pushes_append)
  have sp'': "mcc_spre \<rho> \<sigma>' env'' (F @ ?pb # dps) ?X'' A (e\<langle>0:?A\<rangle>) ?rb y ?ts (Ss @ [?A]) body UU1 s'"
    unfolding mcc_spre_def
  proof (intro conjI)
    show "bs_env \<rho> (e\<langle>0:?A\<rangle>) ?rb" by (fact bs1)
    show "e\<langle>0:?A\<rangle> \<tturnstile> map (inst \<rho>) ?ts : Ss @ [?A]" by (rule mcp_typings_lift[OF sp'(3)])
    show "arity UU1 = nabs body" using sp'(5) UU u by simp
    show "tsubst \<rho> (snd y) = (Ss @ [?A]) \<Rrightarrow> UU1" by (fact Ty)
    show "cert_typ alg ar ((Ss @ [?A]) \<Rrightarrow> UU1)" using cS' sp'(7) UU by (simp add: cert_typ_funs)
    show "pushes mcp_e0 (Ss @ [?A]) \<turnstile> s' : UU1" using s'(1) pe by simp
    show "\<sigma>' (fst y) ((Ss @ [?A]) \<Rrightarrow> UU1) \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> types_abs (Ss @ [?A]) s'"
      using \<sigma>'y Ty by (simp add: conv_refl)
  qed (use inv'' tyb s'(2) lbs' in simp_all)
  have sz: "lsz (pushes mcp_e0 (Ss @ [?A])) s' < lsz (pushes mcp_e0 Ss) s"
  proof -
    have "lsz (pushes mcp_e0 Ss) (Abs STR '''' ?A s') = lsz (pushes mcp_e0 Ss) s"
      by (rule mcp_lsz_conv[OF s'(4) s'(5) sp'(8)[unfolded UU[symmetric]]]) (simp_all add: s'(2) sp'(9))
    then show ?thesis using pe by simp
  qed
  from IH[OF sz pre''[unfolded y_def fst_conv snd_conv] sp''[unfolded y_def fst_conv snd_conv]]
  obtain x where Px: "P x" and r: "mcc_res A0 envM VM F A K ?X'' env'' y \<rho> \<sigma>' m x"
    unfolding y_def fst_conv snd_conv by blast
  have vszy: "mcp_vsz \<rho> \<sigma>' y = mcp_vsz \<rho> \<sigma> (v, TX)"
  proof -
    have "lsz (pushes mcp_e0 Ss) (Abs STR '''' ?A s') = lsz (pushes mcp_e0 Ss) s"
      by (rule mcp_lsz_conv[OF s'(4) s'(5) sp'(8)[unfolded UU[symmetric]]]) (simp_all add: s'(2) sp'(9))
    then have "lsz (pushes mcp_e0 (Ss @ [?A])) s' - 2 * arity UU1 = lsz (pushes mcp_e0 Ss) s - 2 * arity UU"
      using pe UU by simp
    then show ?thesis using mcc_vsz[OF sp] mcc_vsz[OF sp''] by simp
  qed
  have vT: "(v, TX) \<in> X \<union> evars env"
    using upokD(1)[OF mcs_inv(3)[OF pre vN ty0]] by (auto simp: vars_apps)
  have ub: "ubv env'' ?X'' \<subseteq> (ubv env X - {v}) \<union> {fst y}"
  proof -
    have "ubv env'' ?X'' \<subseteq> (ubv env X - {v}) \<union> fst ` {y}"
    proof (rule mcc_ubv_bind[OF up gs(1)])
      show "v \<in> fst ` (?X'' \<union> evars env)" using vT by force
      have "dvars (F @ ?pb # dps) \<subseteq> {y} \<union> (X \<union> evars env)"
        using vu vt mcs_facts(7)[OF pre vN ty0] by (auto simp: vars_apps u incr_boundvars_def)
      then show "fst ` (?X'' \<union> evars env) \<subseteq> fst ` (X \<union> evars env) \<union> fst ` {y}" by blast
      show "fst ` vars (types_abs Ts (Abs a Ta (combound Y 0 (Suc (length Ts))))) \<subseteq> fst ` {y}"
        unfolding combound_bvs by (auto simp: vars_apps Yy)
    qed
    then show ?thesis by simp
  qed
  have "mcc_res A0 envM VM F A K X env (v, TX) \<rho> \<sigma> m x"
    by (rule mcc_res_step[OF r st(5) su(2) _ ub _ st(4) ny]) (use vszy in auto)
  with Px show ?thesis by blast
qed

subsection \<open>Bindings to rigid heads\<close>

text \<open>
  A binding of the variable of the copy to a rigid head applied to new variables, for a target
  \<open>h bs\<close>: the new variables get the arguments \<open>bs\<close> of the target as values, which are smaller than
  the target.
\<close>

lemma mcc_args:
  assumes sol: "solution \<rho> \<sigma> env" and vi: "vinv \<rho> env X"
    and ma: "make_args vname Ts env UC = (env1, args)"
    and up: "ok (update (v, TX) (types_abs Ts (list_comb h args)) env1) env2"
    and vb: "snd v \<le> maxidx env"
    and \<rho>Ts: "map (tsubst \<rho>) Ts = Ss" and \<rho>UC: "map (tsubst \<rho>) UC = Bts"
    and cS: "\<forall>S\<in>set Ss. cert_typ alg ar S" and cB: "\<forall>B\<in>set Bts. cert_typ alg ar B"
    and sh: "s = inst \<rho> h \<degree>\<degree> bs" "pushes mcp_e0 Ss \<turnstile> inst \<rho> h : Bts \<Rrightarrow> UU" "pushes mcp_e0 Ss \<tturnstile> bs : Bts"
    and hr: "rigid h" and tys: "pushes mcp_e0 Ss \<turnstile> s : UU" and nrs: "no_redex s"
    and lbs: "\<not> loose_bvar s (ilength Ss)"
    and \<sigma>v: "\<sigma> v (tsubst \<rho> TX) \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> types_abs Ss s"
  obtains Gs \<sigma>3 where "args = map (\<lambda>G. G \<degree>\<degree> bvs (length Ts)) Gs"
    "list_all2 (\<lambda>G U. \<exists>x. G = Var x (Ts \<Rrightarrow> U)) Gs UC"
    "\<forall>G\<in>set Gs. \<exists>a U. G = Var (a, maxidx env + 1) U" "length Gs = length bs"
    "sagree (maxidx env) \<sigma> \<sigma>3" "wt_subst \<sigma>3" "solution \<rho> \<sigma>3 env2"
    "\<And>l. l < length Gs \<Longrightarrow> ap \<rho> \<sigma>3 (Gs ! l) = types_abs Ss (bs ! l)"
    "\<And>l. l < length Gs \<Longrightarrow> mcp_vsz \<rho> \<sigma>3 (var_of (Gs ! l), Ts \<Rrightarrow> (UC ! l)) \<le> lsz (pushes mcp_e0 Ss) (bs ! l)"
    "(\<Sum>y\<in>lvars Gs. mcp_vsz \<rho> \<sigma>3 y) + 1 \<le> lsz (pushes mcp_e0 Ss) s"
proof -
  have rh': "rigid (inst \<rho> h)" using hr by (cases h) auto
  have lbs_arg: "\<forall>b\<in>set bs. \<not> loose_bvar b (ilength Ss)" using lbs sh(1) by (simp add: loose_bvar_apps)
  have nr_arg: "\<forall>b\<in>set bs. no_redex b"
    using nrs sh(1) no_redex_apps[of "inst \<rho> h" bs] rh' by (cases "inst \<rho> h") auto
  have lbs': "length bs = length Bts" using typings_nth[OF sh(3)] by simp
  obtain Gs where args: "args = map (\<lambda>G. G \<degree>\<degree> bvs (length Ts)) Gs"
    and GU: "list_all2 (\<lambda>G U. \<exists>x. G = Var x (Ts \<Rrightarrow> U)) Gs UC"
    and ma': "tenv env1 = tenv env" "tyenv env1 = tyenv env" "maxidx env \<le> maxidx env1"
    and Gi: "\<forall>G\<in>set Gs. \<exists>a U. G = Var (a, maxidx env + 1) U"
    by (rule make_args_props_idx[OF ma]) blast
  have dist: "distinct (map var_of Gs)" by (rule mcp_make_args_distinct[OF ma args])
  let ?q = "length Gs"
  have lq: "?q = length UC" by (rule list_all2_lengthD[OF GU])
  have lqb: "?q = length bs" using lq \<rho>UC lbs' by (metis length_map)
  define xs where "xs = map var_of Gs"
  have Gl: "Gs ! l = Var (xs ! l) (Ts \<Rrightarrow> (UC ! l))" if "l < ?q" for l
  proof -
    from list_all2_nthD[OF GU that] obtain x where "Gs ! l = Var x (Ts \<Rrightarrow> (UC ! l))" by blast
    then show ?thesis using that by (simp add: xs_def)
  qed
  have xidx: "snd (xs ! l) = maxidx env + 1" if "l < ?q" for l
    using Gi Gl[OF that] nth_mem[OF that] by fastforce
  define ysi where "ysi = map (\<lambda>l. (xs ! l, Ss \<Rrightarrow> (Bts ! l))) [0..<?q]"
  define ws where "ws = map (types_abs Ss) bs"
  define \<sigma>3 where "\<sigma>3 = mcp_supds \<sigma> ysi ws"
  have dys: "distinct ysi"
  proof -
    have "distinct xs" using dist by (simp add: xs_def)
    moreover have "length xs = ?q" by (simp add: xs_def)
    ultimately show ?thesis by (simp add: ysi_def distinct_conv_nth)
  qed
  have lys: "length ysi = ?q" "length ws = ?q" by (simp_all add: ysi_def ws_def lqb)
  have tyw: "e' \<turnstile> ws ! l : snd (ysi ! l)" if "l < length ysi" "l < length ws" for l e'
  proof -
    have l: "l < length bs" using that lys lqb by simp
    have "pushes mcp_e0 Ss \<turnstile> bs ! l : Bts ! l" using typings_nth[OF sh(3)] l by simp
    from mcp_typing_val[OF this] lbs_arg cS l show ?thesis using that by (simp add: ws_def ysi_def)
  qed
  have cw: "\<forall>w\<in>set ws. closed w" using lbs_arg by (auto simp: ws_def closed_types_abs)
  have nys: "\<forall>y\<in>set ysi. maxidx env < snd (fst y)" using xidx by (auto simp: ysi_def)
  have su: "solution \<rho> \<sigma>3 env" "sagree (maxidx env) \<sigma> \<sigma>3" "wt_subst \<sigma>3"
    unfolding \<sigma>3_def by (rule mcp_solution_supds[OF sol vi nys cw]; blast intro: tyw)+
  have \<sigma>3l: "\<sigma>3 (xs ! l) (Ss \<Rrightarrow> (Bts ! l)) = types_abs Ss (bs ! l)" if "l < ?q" for l
    using mcp_supds_nth[OF dys, of ws l \<sigma>] lys that lqb by (simp add: \<sigma>3_def ysi_def ws_def)
  have \<rho>Gl: "tsubst \<rho> (Ts \<Rrightarrow> (UC ! l)) = Ss \<Rrightarrow> (Bts ! l)" if "l < ?q" for l
    using \<rho>Ts \<rho>UC that lq by (simp add: tsubst_funs flip: nth_map[of l UC "tsubst \<rho>"])
  have apGl: "ap \<rho> \<sigma>3 (Gs ! l) = types_abs Ss (bs ! l)" if "l < ?q" for l
    using \<sigma>3l[OF that] \<rho>Gl[OF that] by (simp add: Gl[OF that])
  have lTsS: "length Ts = length Ss" using \<rho>Ts by auto
  have u'e: "list_comb h args = h \<degree>\<degree> map (\<lambda>G. G \<degree>\<degree> bvs (length Ts)) Gs"
    by (simp add: args list_comb_apps)
  have apc: "ap \<rho> \<sigma>3 (list_comb h args) = inst \<rho> h \<degree>\<degree> map (\<lambda>b. types_abs Ss b \<degree>\<degree> bvs (length Ss)) bs"
  proof -
    have "map (ap \<rho> \<sigma>3) (map (\<lambda>G. G \<degree>\<degree> bvs (length Ts)) Gs) = map (\<lambda>b. types_abs Ss b \<degree>\<degree> bvs (length Ss)) bs"
      by (rule nth_equalityI) (simp_all add: lqb ap_apps apGl lTsS comp_def)
    then show ?thesis by (simp add: u'e ap_apps rigid_ap[OF hr])
  qed
  have tbs: "pushes mcp_e0 Ss \<turnstile> bs ! l : Bts ! l" if "l < length bs" for l
    using typings_nth[OF sh(3)] that by simp
  have tm: "pushes mcp_e0 Ss \<tturnstile> map (\<lambda>b. types_abs Ss b \<degree>\<degree> bvs (length Ss)) bs : Bts"
    by (rule typings_nthI) (use mcp_conv_bvs(2)[OF tbs] lbs_arg cS lbs' in auto)
  have cvb: "inst \<rho> h \<degree>\<degree> map (\<lambda>b. types_abs Ss b \<degree>\<degree> bvs (length Ss)) bs \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> s"
    unfolding sh(1)
  proof (rule conv_apps[OF _ _ _ conv_refl])
    show "list_all2 (\<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta>) (map (\<lambda>b. types_abs Ss b \<degree>\<degree> bvs (length Ss)) bs) bs"
      by (rule list_all2_all_nthI) (use mcp_conv_bvs(1)[OF tbs] lbs_arg cS in auto)
    show "wt (inst \<rho> h \<degree>\<degree> map (\<lambda>b. types_abs Ss b \<degree>\<degree> bvs (length Ss)) bs)"
      using list_app_typeI[OF sh(2) tm] by (auto simp: wt_def)
    show "wt (inst \<rho> h \<degree>\<degree> bs)" using tys sh(1) by (auto simp: wt_def)
  qed
  have cvt: "types_abs Ss (ap \<rho> \<sigma>3 (list_comb h args)) \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> types_abs Ss s"
  proof (rule conv_types_abs[OF _ _ cvb[folded apc]])
    have "pushes mcp_e0 Ss \<turnstile> ap \<rho> \<sigma>3 (list_comb h args) : UU"
      unfolding apc by (rule list_app_typeI[OF sh(2) tm])
    from typing_types_abs[OF this cS]
    show "wt (types_abs Ss (ap \<rho> \<sigma>3 (list_comb h args)))" by (auto simp: wt_def)
    show "wt (types_abs Ss s)" using mcp_typing_val[OF tys lbs cS] by (auto simp: wt_def)
  qed
  have ny: "maxidx env < snd (fst y)" if "y \<in> set ysi" for y using nys that by blast
  have \<sigma>3v: "\<sigma>3 v (tsubst \<rho> TX) = \<sigma> v (tsubst \<rho> TX)"
    using su(2) vb unfolding sagree_def by blast
  have eqv: "\<sigma>3 v (tsubst \<rho> TX) \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma>3 (types_abs Ts (list_comb h args))"
    unfolding \<sigma>3v ap_types_abs \<rho>Ts using \<sigma>v cvt by (blast intro: conv_sym conv_trans)
  have sol2: "solution \<rho> \<sigma>3 env2" by (rule mcc_solution_bind[OF sol vi su(2,3) ma'(1,2) up eqv])
  have vszl: "mcp_vsz \<rho> \<sigma>3 (xs ! l, Ts \<Rrightarrow> (UC ! l)) \<le> lsz (pushes mcp_e0 Ss) (bs ! l)" if "l < ?q" for l
  proof -
    have "mcp_vsz \<rho> \<sigma>3 (xs ! l, Ts \<Rrightarrow> (UC ! l)) = lsz (pushes mcp_e0 Ss) (bs ! l) - 2 * arity (Bts ! l)"
    proof (rule mcp_vsz_val[OF su(3)])
      show "cert_typ alg ar (tsubst \<rho> (Ts \<Rrightarrow> (UC ! l)))"
        using \<rho>Gl[OF that] cS cB that lq lbs' lqb by (simp add: cert_typ_funs)
      show "\<sigma>3 (xs ! l) (tsubst \<rho> (Ts \<Rrightarrow> (UC ! l))) \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> types_abs Ss (bs ! l)"
        using \<sigma>3l[OF that] \<rho>Gl[OF that] by simp
      show "tsubst \<rho> (Ts \<Rrightarrow> (UC ! l)) = Ss \<Rrightarrow> (Bts ! l)" by (rule \<rho>Gl[OF that])
      show "pushes mcp_e0 Ss \<turnstile> bs ! l : Bts ! l" by (rule tbs) (use that lqb in simp)
      show "no_redex (bs ! l)" using nr_arg that lqb by simp
    qed (fact cS)
    then show ?thesis by simp
  qed
  have Gs_eq: "Gs = map (\<lambda>l. Var (xs ! l) (Ts \<Rrightarrow> (UC ! l))) [0..<?q]"
    by (rule nth_equalityI) (simp_all add: Gl)
  have mlG: "lvars Gs = set (map (\<lambda>l. (xs ! l, Ts \<Rrightarrow> (UC ! l))) [0..<?q])"
    by (subst Gs_eq) auto
  have msum: "(\<Sum>y\<in>lvars Gs. mcp_vsz \<rho> \<sigma>3 y) + 1 \<le> lsz (pushes mcp_e0 Ss) s"
  proof -
    let ?f = "\<lambda>l. (xs ! l, Ts \<Rrightarrow> (UC ! l))"
    have "(\<Sum>y\<in>lvars Gs. mcp_vsz \<rho> \<sigma>3 y) \<le> sum_list (map (mcp_vsz \<rho> \<sigma>3) (map ?f [0..<?q]))"
      unfolding mlG by (rule mcp_sum_set_le_list)
    also have "\<dots> \<le> sum_list (map (\<lambda>l. lsz (pushes mcp_e0 Ss) (bs ! l)) [0..<?q])"
      by (simp only: map_map comp_def) (rule sum_list_mono, use vszl in simp)
    also have "\<dots> = sum_list (map (lsz (pushes mcp_e0 Ss)) bs)"
      unfolding lqb by (rule arg_cong[where f = sum_list], rule nth_equalityI) simp_all
    finally have "(\<Sum>y\<in>lvars Gs. mcp_vsz \<rho> \<sigma>3 y) \<le> sum_list (map (lsz (pushes mcp_e0 Ss)) bs)" .
    moreover have "lsz (pushes mcp_e0 Ss) s = tsz (spine_type (pushes mcp_e0 Ss) s) + sum_list (map (lsz (pushes mcp_e0 Ss)) bs)"
      unfolding sh(1) by (rule lsz_rigid_apps[OF rh'])
    moreover have "0 < tsz (spine_type (pushes mcp_e0 Ss) s)" by (rule tsz_pos)
    ultimately show ?thesis by simp
  qed
  show ?thesis
  proof (rule that[OF args GU Gi _ su(2,3) sol2 apGl])
    show "length Gs = length bs" by (fact lqb)
    show "mcp_vsz \<rho> \<sigma>3 (var_of (Gs ! l), Ts \<Rrightarrow> (UC ! l)) \<le> lsz (pushes mcp_e0 Ss) (bs ! l)"
      if "l < length Gs" for l using vszl[OF that] by (simp add: xs_def that)
  qed (use msum in simp_all)
qed

subsection \<open>Copies: projections\<close>

lemma tvars_vtvars: "(x, T) \<in> S \<Longrightarrow> tvars T \<subseteq> vtvars S"
  by (auto simp: vtvars_def)

text \<open>The pending pairs stay solved by an agreeing solution:\<close>

lemma mcc_scinv_frame:
  assumes inv: "scinv \<rho> \<sigma> env (F @ dps) X A" and pF: "\<forall>(rb, t, u)\<in>set F. upok A env rb X t u"
    and inv': "scinv \<rho>' \<sigma>' env' dps' X A'"
    and ag: "tagree (maxidx env) \<rho> \<rho>'" "sagree (maxidx env) \<sigma> \<sigma>'"
  shows "scinv \<rho>' \<sigma>' env' (F @ dps') X A'"
proof -
  note i = scinvD[OF inv] and i' = scinvD[OF inv']
  have "dtyped \<rho> F" "dsolved \<rho> \<sigma> F" using i(6,7) by (auto simp: dtyped_def dsolved_def)
  then have "dtyped \<rho>' F" "dsolved \<rho>' \<sigma>' F"
    using sc_dps_agree[OF pF i(4) i(3) ag] by blast+
  then show ?thesis using inv' unfolding scinv_def by (auto simp: dtyped_def dsolved_def)
qed

text \<open>
  A projection for a target with a bound head: the right guess of the number of arguments, with the
  type unification, the binding and the simplification, gives a result.
\<close>

lemma mcc_proj_elem:
  assumes cfg: "cfg_alg cfg = alg"
    and pre: "mcpre A0 envM VM F A K X env rb (v, TX) targs u dps ot" and vN: "vt_lookup (tenv env) v = None"
    and ty0: "fastype env rb (fst (strip_comb u)) = return T0" "body_type env T0 = return base"
      "mapM (fastype env rb) targs = return Ts"
    and sp: "mcc_spre \<rho> \<sigma> env (F @ (rb, Var v TX \<degree>\<degree> targs, u) # dps) X A e rb (v, TX) targs Ss u UU s"
    and kk: "mcp_kokK (nat_of_integer (cfg_arity_bound cfg)) \<rho> (tyenv env) A K"
    and na: "\<not> is_Abs (fst (strip_comb u))"
    and sB: "s = Bound j \<degree>\<degree> bs" "0 \<le> j" "j < ilength Ss"
    and kdef: "k = length targs - 1 - nat_of_integer j"
    and st: "ok (strip_type env (Ts ! k)) (Us, bary)"
  shows "\<exists>p env0 Cs env'. p \<in> set (arity_guesses cfg bary) \<and> gentvars p env = (env0, Cs) \<and>
    okW (proj_unify cfg base bary Cs env0) env' \<and>
    (\<forall>env1 args. make_args vname Ts env' (Us @ Cs) = (env1, args) \<longrightarrow>
      (\<exists>env2 env3 fr ff. ok (update (v, TX) (types_abs Ts (list_comb (Bound j) args)) env1) env2 \<and>
        okW (SIMPL (cfg_alg cfg) env2
          ((rb, list_comb (targs ! k) (map (\<lambda>arg. list_comb (head_of arg) targs) args), u) # dps)) (env3, fr, ff) \<and>
        mcc_res A0 envM VM F A K X env (v, TX) \<rho> \<sigma> 1 (El_E env3 (fr @ ff))))"
proof -
  let ?P = "(rb, Var v TX \<degree>\<degree> targs, u)"
  note sp' = mcc_spreD[OF sp] and cS = mcc_cS[OF sp]
  note inv = sp'(1) and bs = sp'(2) and tyt = sp'(3) and tyu = sp'(4) and tys = sp'(8)
    and nrs = sp'(9) and lbs = sp'(10)
  note i = scinvD[OF inv] and sd = solutionD[OF scinvD(1)[OF inv]]
  note mp = mcs_pre[OF pre vN ty0] and mf = mcs_facts[OF pre vN ty0]
  have finX: "finite X" and finK: "finite K" by (fact mp(1), fact mp(2))
  have c0: "cpinvX A0 envM VM F A K X env (?P # dps)" by (rule mcpre_cpinvX[OF pre, simplified])
  have si: "sinv A K X env (F @ ?P # dps)" by (fact mp(9))
  have ei: "einv A K env" and ps: "\<forall>(rb', t', u')\<in>set (F @ ?P # dps). upok A env rb' X t' u'"
    using si by (auto simp: sinv_def)
  have pF: "\<forall>(rb', t', u')\<in>set F. upok A env rb' X t' u'" using ps by auto
  note x = einvD[OF ei]
  let ?\<theta> = "tyenv env" and ?KN = "tvars_env (tyenv env) \<union> A"
  have below_KN: "tbelow (maxidx env) S" if "S \<subseteq> ?KN" for S using tvinv_tbelow[OF i(4) that] .
  have Tsok: "ok (mapM (fastype env rb) targs) Ts" by (fact mf(9))
  have SsT: "map (tsubst \<rho>) Ts = Ss" by (rule mapM_fastype_sound(2)[OF Tsok sd(2) bs tyt])
  have tyV: "e \<turnstile> inst \<rho> (Var v TX) : Ss \<Rrightarrow> UU" using sp'(6,7) by auto
  have tyt': "e \<turnstile> inst \<rho> (Var v TX \<degree>\<degree> targs) : UU"
    using list_app_typeI[OF tyV tyt] by (simp add: inst_apps)
  have UUb: "UU = tsubst \<rho> base" by (rule mcs_bse[OF pre vN ty0 na sd(2) bs tyt' tyu])
  have kok: "mcp_kok (nat_of_integer (cfg_arity_bound cfg)) \<rho> ?\<theta> ?KN" by (rule mcp_kokK_kok[OF kk ei])
  let ?n = "length targs"
  have lSs: "length Ss = ?n" using SsT mf(10) by auto
  have jn: "nat_of_integer j < ?n" using sB(2,3) lSs nat_of_integer_less_ilength by fastforce
  have kn: "k < ?n" using kdef jn by simp
  have u: "u = fst (strip_comb u) \<degree>\<degree> snd (strip_comb u)" by (rule strip_comb_apps) simp
  have ar0: "arity UU = 0"
  proof -
    have "\<not> is_Abs u" using na u is_Abs_apps by metis
    then show ?thesis using sp'(5) by simp
  qed
  \<comment> \<open>The type of the projected argument:\<close>
  from tys[unfolded sB(1)] obtain Bts where tyB: "pushes mcp_e0 Ss \<turnstile> Bound j : Bts \<Rrightarrow> UU"
    and tybs: "pushes mcp_e0 Ss \<tturnstile> bs : Bts" by (rule list_app_typeE)
  have "pushes mcp_e0 Ss j = Bts \<Rrightarrow> UU" using tyB by auto
  moreover have "pushes mcp_e0 Ss j = Ss ! k"
    using pushes_nth[OF sB(2), of mcp_e0 Ss] sB(3) lSs kdef jn by (simp add: rev_nth)
  ultimately have SsK: "Ss ! k = Bts \<Rrightarrow> UU" by simp
  have \<rho>Tk: "tsubst \<rho> (Ts ! k) = Ss ! k" using SsT kn mf(10) by auto
  from st have bU: "ok (binder_types env (Ts ! k)) Us" and bB: "ok (body_type env (Ts ! k)) bary"
    by (auto simp: strip_type_def)
  have stk: "tsubst \<rho> (Ts ! k) = map (tsubst \<rho>) Us \<Rrightarrow> tsubst \<rho> bary" by (rule strip_type_sound[OF st sd(2)])
  from mcp_funs_split[OF _ ar0, of "map (tsubst \<rho>) Us" "tsubst \<rho> bary" Bts] stk \<rho>Tk SsK
  have spl: "length Us \<le> length Bts" "Bts = map (tsubst \<rho>) Us @ drop (length Us) Bts"
    "tsubst \<rho> bary = drop (length Us) Bts \<Rrightarrow> UU" by simp_all
  define Ds where "Ds = drop (length Us) Bts"
  define p where "p = length Ds"
  have tvTk: "tvars (Ts ! k) \<subseteq> ?KN" using mf(12) kn mf(10) by simp
  have "\<forall>U\<in>set Us. tvars U \<subseteq> tvars (Ts ! k) \<union> tvars_env ?\<theta>"
    using mf_binder_types_sound[of env "Ts ! k" "Ok Us" Us] bU x(6) by auto
  then have tvUs: "\<forall>U\<in>set Us. tvars U \<subseteq> ?KN" using tvTk by blast
  from body_type_term[OF x(2) refl tvTk] bB have tvbary: "tvars bary \<subseteq> ?KN" by (auto simp: return_def)
  have arb: "arity (tsubst \<rho> bary) = p" using spl(3) ar0 by (simp add: arity_funs p_def Ds_def)
  have pg: "p \<in> set (arity_guesses cfg bary)"
  proof (cases "is_TVar bary")
    case True
    from mcp_body_type_TVar[of env "Ts ! k" "Ok bary" bary] bB True obtain w S
      where bv: "bary = TVar w S" "vt_lookup ?\<theta> w = None" by auto
    have "(w, S) \<in> ?KN" using tvbary bv by simp
    from mcp_aok_arity[OF mcp_kok_unbound[OF kok this bv(2) x(6)]] arb bv
    have "p \<le> nat_of_integer (cfg_arity_bound cfg)" by simp
    with True show ?thesis by (auto simp: arity_guesses_def)
  next
    case False
    have "arity (tsubst \<rho> bary) = 0" by (rule mcp_body_type_nonTVar_arity[OF bB False x(6)])
    with False arb show ?thesis by (simp add: arity_guesses_def)
  qed
  \<comment> \<open>The new type variables of the guess:\<close>
  obtain env0 Cs where g: "gentvars p env = (env0, Cs)" by (cases "gentvars p env")
  note gs = gentvars_simps[OF g]
  let ?A1 = "A \<union> ntv Cs" and ?K1 = "K \<union> ntv Cs"
  have lD: "length Ds = p" by (simp add: p_def)
  obtain \<rho>1 where \<rho>1: "tagree (maxidx env) \<rho> \<rho>1" "map (tsubst \<rho>1) Cs = Ds" "wsinst alg \<rho>1"
    by (rule mcp_gentvars_inst[OF g lD sd(1)])
  have si0: "sinv ?A1 ?K1 X env0 (F @ ?P # dps)" by (rule sinv_gentvars[OF si g])
  have ei0: "einv ?A1 ?K1 env0" using si0 by (simp add: sinv_def)
  have ps0: "\<forall>(rb', t', u')\<in>set (F @ ?P # dps). upok ?A1 env0 rb' X t' u'" using si0 by (simp add: sinv_def)
  have ext0: "extends env env0" by (rule extends_tenv_eq[OF gs(1,2,3)])
  have tbe: "tbelow (maxidx env) (tvars_env ?\<theta>)" by (rule below_KN) simp
  have inv1: "scinv \<rho>1 \<sigma> env0 (F @ ?P # dps) X ?A1"
    unfolding scinv_def
  proof (intro conjI)
    have "tsol ?\<theta> \<rho>1" by (rule mcp_tsol_agree[OF sd(2) \<rho>1(1) tbe])
    then show "solution \<rho>1 \<sigma> env0"
      by (rule solution_tyenv[OF i(1) i(4) i(3) \<rho>1(3) _ \<rho>1(1) gs(1), unfolded gs(2)])
    show "wt_env \<rho>1 env0" using wt_env_agree[OF i(2) \<rho>1(1) i(4)] wt_env_tenv[OF gs(1)] by simp
    show "vinv \<rho>1 env0 X" using vinv_tenv[OF gs(1) ext0 vinv_agree[OF i(3) \<rho>1(1) i(4) i(5)]] .
    show "tvinv ?A1 env0" by (rule einvD(1)[OF ei0])
    show "vtvars X \<subseteq> tvars_env (tyenv env0) \<union> ?A1" using i(5) gs(2) by auto
    show "dtyped \<rho>1 (F @ ?P # dps)" by (rule sc_dps_agree(1)[OF ps i(4) i(3) \<rho>1(1) sagree_refl i(6)])
    show "dsolved \<rho>1 \<sigma> (F @ ?P # dps)" by (rule sc_dps_agree(2)[OF ps i(4) i(3) \<rho>1(1) sagree_refl i(7)])
  qed
  \<comment> \<open>The type unification of the projection:\<close>
  have \<rho>1b: "tsubst \<rho>1 base = UU" using tsubst_agree[OF \<rho>1(1) below_KN[OF mf(11)]] UUb by simp
  have \<rho>1bary: "tsubst \<rho>1 bary = Ds \<Rrightarrow> UU"
    using tsubst_agree[OF \<rho>1(1) below_KN[OF tvbary]] spl(3) by (simp add: Ds_def)
  have "cert_typ alg ar (Ss ! k)" using cS(1) kn lSs by simp
  then have cBts: "\<forall>B\<in>set Bts. cert_typ alg ar B" "cert_typ alg ar UU"
    using SsK by (simp_all add: cert_typ_funs)
  have cDs: "\<forall>D\<in>set Ds. cert_typ alg ar D" using cBts(1) by (auto simp: Ds_def dest: in_set_dropD)
  have tvC: "\<forall>C\<in>set Cs. tvars C \<subseteq> ntv Cs" by (auto simp: ntv_def)
  have tvb0: "tvars base \<subseteq> tvars_env (tyenv env0) \<union> ?A1" "tvars bary \<subseteq> tvars_env (tyenv env0) \<union> ?A1"
    using mf(11) tvbary gs(2) by auto
  have tvCb: "tvars (Cs \<Rrightarrow> base) \<subseteq> tvars_env (tyenv env0) \<union> ?A1"
    using tvb0(1) tvC by (auto simp: tvars_funs)
  have wb: "wft ar base" by (rule mcp_wft_inst[of \<rho>1]) (simp add: \<rho>1b cBts(2))
  have wbary: "wft ar bary" by (rule mcp_wft_inst[of \<rho>1]) (simp add: \<rho>1bary cDs cBts(2) cert_typ_funs)
  have wCb: "wft ar (Cs \<Rrightarrow> base)"
    by (rule mcp_wft_inst[of \<rho>1]) (simp add: tsubst_funs \<rho>1(2) \<rho>1b cDs cBts(2) cert_typ_funs)
  define Q where "Q = (\<lambda>env'. \<exists>\<rho>'. scinv \<rho>' \<sigma> env' (F @ ?P # dps) X ?A1 \<and> tagree (maxidx env0) \<rho>1 \<rho>' \<and>
    tvars_env (tyenv env0) \<subseteq> tvars_env (tyenv env') \<and> maxidx env0 \<le> maxidx env' \<and> tenv env' = tenv env0 \<and>
    textends (tyenv env0) (tyenv env'))"
  have ncu_pu: "ncu (proj_unify cfg base bary Cs env0) Q"
  proof (cases "Cs = []")
    case True
    then have Ds0: "Ds = []" using \<rho>1(2) by simp
    have eq: "tsubst \<rho>1 base = tsubst \<rho>1 bary" using \<rho>1b \<rho>1bary Ds0 by simp
    note c = sc_cunify_complete[OF inv1 ps0 tvb0(1) wb tvb0(2) wbary eq, folded Q_def]
    show ?thesis unfolding proj_unify_def using True cfg c mcp_ncu_test_unify[OF c]
      by (simp add: List.null_iff)
  next
    case False
    have eq: "tsubst \<rho>1 bary = tsubst \<rho>1 (Cs \<Rrightarrow> base)" using \<rho>1b \<rho>1bary \<rho>1(2) by (simp add: tsubst_funs)
    note c = sc_cunify_complete[OF inv1 ps0 tvb0(2) wbary tvCb wCb eq, folded Q_def]
    show ?thesis unfolding proj_unify_def using False cfg c by (simp add: List.null_iff)
  qed
  \<comment> \<open>Termination of the type unification, with the invariant of the termination proof:\<close>
  have r0: "tsol ?\<theta> (rho0 env)" "cert_inst (rho0 env)" by (rule einv_rho0[OF ei])+
  from upokD(9)[OF mcs_inv(3)[OF pre vN ty0] r0] obtain e0 U0 where t0: "bs_env (rho0 env) e0 rb"
    "e0 \<turnstile> inst (rho0 env) (Var v TX \<degree>\<degree> targs) : U0" "e0 \<turnstile> inst (rho0 env) u : U0" by blast
  from t0(2)[unfolded inst_apps] obtain Us0 where t0a: "e0 \<tturnstile> map (inst (rho0 env)) targs : Us0"
    by (rule list_app_typeE)
  have Us0: "map (tsubst (rho0 env)) Ts = Us0" by (rule mapM_fastype_sound(2)[OF Tsok r0(1) t0(1) t0a])
  have U0b: "U0 = tsubst (rho0 env) base" by (rule mcs_bse[OF pre vN ty0 na r0(1) t0])
  have cTk0: "cert_typ alg ar (tnorm ?\<theta> (Ts ! k))"
  proof -
    have "e0 \<turnstile> inst (rho0 env) (targs ! k) : Us0 ! k" using typings_nth[OF t0a] kn by auto
    then have "cert_typ alg ar (Us0 ! k)"
      by (rule bs_env_cert[OF t0(1)]) (use upokD(7)[OF mcs_inv(3)[OF pre vN ty0]] kn in \<open>auto simp: loose_bvar_apps\<close>)
    then show ?thesis using Us0 kn mf(10) by auto
  qed
  have cb0: "cert_typ alg ar (tnorm ?\<theta> base)"
    using bs_env_cert[OF t0(1) t0(3) upokD(8)[OF mcs_inv(3)[OF pre vN ty0]]] U0b by simp
  have cbary0: "cert_typ alg ar (tnorm ?\<theta> bary)"
    using cTk0 strip_type_sound[OF st r0(1)] by (simp add: cert_typ_funs)
  have cC: "\<forall>C\<in>set Cs. cert_typ alg ar (tnorm (tyenv env0) C)"
    using gs(6) cert_tnorm[OF ei0] by (fastforce simp: cert_typ_def sort_ok_def)
  have cu_pu: "cuok (proj_unify cfg base bary Cs env0) (\<lambda>env'. sinv ?A1 ?K1 X env' (F @ ?P # dps) \<and>
    tenv env' = tenv env0 \<and> extends env0 env' \<and> tvars_env (tyenv env0) \<subseteq> tvars_env (tyenv env') \<and>
    tnew ?A1 env0 ?A1 env' \<and> (\<forall>\<rho>. tsol (tyenv env') \<rho> \<longrightarrow> tsubst \<rho> bary = tsubst \<rho> (Cs \<Rrightarrow> base)))"
    by (rule proj_unify_sinv[OF cfg finite_UnI[OF finK finite_ntv] si0 tvb0 _ _ _ cC])
      (use tvC cb0 cbary0 gs(2) in auto)
  from mcp_ncu_cuok[OF ncu_pu cu_pu] obtain env' where pu: "okW (proj_unify cfg base bary Cs env0) env'"
    and Q: "Q env'" and post: "sinv ?A1 ?K1 X env' (F @ ?P # dps)" "tenv env' = tenv env0"
      "extends env0 env'" "tvars_env (tyenv env0) \<subseteq> tvars_env (tyenv env')" "tnew ?A1 env0 ?A1 env'"
    by blast
  from Q obtain \<rho>2 where inv2: "scinv \<rho>2 \<sigma> env' (F @ ?P # dps) X ?A1" and ag2: "tagree (maxidx env0) \<rho>1 \<rho>2"
    unfolding Q_def by blast
  note i2 = scinvD[OF inv2]
  have ag02: "tagree (maxidx env) \<rho> \<rho>2" by (rule tagree_trans[OF \<rho>1(1) ag2 gs(3)])
  have ext0': "extends env env'" by (rule extends_trans[OF ext0 post(3)])
  have mx: "maxidx env \<le> maxidx env'" using ext0' by (simp add: extends_def)
  have tve0: "tvars_env ?\<theta> \<subseteq> tvars_env (tyenv env')" using post(4) gs(2) by simp
  have \<rho>2Ts: "map (tsubst \<rho>2) Ts = Ss"
  proof -
    have "map (tsubst \<rho>2) Ts = map (tsubst \<rho>) Ts"
      by (rule map_cong[OF refl]) (use tsubst_agree[OF ag02 below_KN] mf(12) in blast)
    then show ?thesis using SsT by simp
  qed
  have \<rho>2Us: "map (tsubst \<rho>2) Us = map (tsubst \<rho>) Us"
    using tsubst_agree[OF ag02 below_KN] tvUs by simp
  have \<rho>2Cs: "map (tsubst \<rho>2) Cs = Ds"
  proof -
    have "tsubst \<rho>2 C = tsubst \<rho>1 C" if "C \<in> set Cs" for C
      using gs(6)[OF that] by (auto intro!: tsubst_agree[OF ag2] simp: tbelow_def)
    then show ?thesis using \<rho>1(2) by (metis map_eq_conv)
  qed
  have \<rho>2UC: "map (tsubst \<rho>2) (Us @ Cs) = Bts"
    unfolding map_append \<rho>2Us \<rho>2Cs using spl(2) by (simp add: Ds_def)
  have \<rho>2TX: "tsubst \<rho>2 TX = Ss \<Rrightarrow> UU"
    using tsubst_agree[OF ag02 below_KN[OF mf(1)]] sp'(6) by simp
  have ei': "einv ?A1 ?K1 env'" using post(1) by (simp add: sinv_def)
  note x' = einvD[OF ei']
  \<comment> \<open>The arity condition for the new type variables:\<close>
  have kk2: "\<forall>k'. mcp_kokK k' \<rho> (tyenv env) A K \<longrightarrow> mcp_kokK k' \<rho>2 (tyenv env') ?A1 ?K1"
  proof (intro allI impI)
    fix k' assume kk: "mcp_kokK k' \<rho> (tyenv env) A K"
    have N: "\<forall>(w, S)\<in>ntv Cs. (w, S) \<in> tvars_env (tyenv env') \<union> ?A1 \<and> mcp_aok k' (\<rho>2 w S)"
    proof (intro ballI, clarify)
      fix w S assume wS: "(w, S) \<in> ntv Cs"
      then obtain C where C: "C \<in> set Cs" "(w, S) \<in> tvars C" by (auto simp: ntv_def)
      from gs(6)[OF C(1)] obtain a where Ca: "C = TVar (a, maxidx env0) []" by blast
      have "tsubst \<rho>2 C \<in> set Ds" using \<rho>2Cs C(1) by (metis image_eqI list.set_map)
      then have D: "\<rho>2 w S \<in> set Ds" using C(2) Ca by simp
      have "Cs \<noteq> []" using C(1) by auto
      then have p0: "p \<noteq> 0" using gs(4) by auto
      then have "is_TVar bary" using pg by (auto simp: arity_guesses_def split: if_splits)
      from mcp_body_type_TVar[of env "Ts ! k" "Ok bary" bary] bB this obtain w' S'
        where bv: "bary = TVar w' S'" "vt_lookup ?\<theta> w' = None" by auto
      have "(w', S') \<in> ?KN" using tvbary bv by simp
      from mcp_kok_unbound[OF mcp_kokK_kok[OF kk ei] this bv(2) x(6)]
      have "mcp_aok k' (tsubst \<rho> bary)" using bv by simp
      then have "\<forall>D\<in>set Ds. mcp_aok k' D" using spl(3) by (simp add: mcp_aok_funs Ds_def)
      with D show "(w, S) \<in> tvars_env (tyenv env') \<union> ?A1 \<and> mcp_aok k' (\<rho>2 w S)" using wS by auto
    qed
    have tx: "textends ?\<theta> (tyenv env')" using ext0' by (simp add: extends_def)
    show "mcp_kokK k' \<rho>2 (tyenv env') ?A1 ?K1"
      by (rule mcp_kokK_ext[OF kk tx x'(6) x'(7) solutionD(2)[OF i2(1)] ag02 below_KN[OF order_refl] x(6)
            tinv_tcons[OF x'(2)] tve0 _ N]) auto
  qed
  let ?j = "integer_of_nat (length targs - 1 - k)"
  have jk: "j = ?j"
    using kdef jn sB(2) by (simp add: integer_eq_iff integer_of_nat.rep_eq nat_of_integer.rep_eq less_eq_integer.rep_eq)
  have hk: "k < length targs" "Bound j = Bound ?j" "targs ! k = targs ! k" "Ts ! k = Ts ! k"
    using kn jk by simp_all
  show ?thesis
  proof (rule exI[of _ p], rule exI[of _ env0], rule exI[of _ Cs], rule exI[of _ env'], intro conjI allI impI)
    show "p \<in> set (arity_guesses cfg bary)" by (rule pg)
    show "gentvars p env = (env0, Cs)" by (rule g)
    show "okW (proj_unify cfg base bary Cs env0) env'" by (rule pu)
    fix env1 args assume ma: "make_args vname Ts env' (Us @ Cs) = (env1, args)"
    have te1: "tenv env1 = tenv env'" by (rule make_args_props_idx[OF ma]) blast
    have vN1: "vt_lookup (tenv env1) v = None" using vN te1 post(2) gs(1) by simp
    obtain env2 where up: "ok (update (v, TX) (types_abs Ts (list_comb (Bound j) args)) env1) env2"
      using update_unbound[OF vN1] by blast
    let ?P' = "(rb, list_comb (targs ! k) (map (\<lambda>arg. list_comb (head_of arg) targs) args), u)"
    note ms = mcs_proj[OF pre vN ty0 na g pu post st pg hk tvUs ma up]
    let ?X2 = "X \<union> dvars (F @ ?P' # dps)"
    \<comment> \<open>The new variables for the arguments:\<close>
    have shB: "s = inst \<rho>2 (Bound j) \<degree>\<degree> bs" "pushes mcp_e0 Ss \<turnstile> inst \<rho>2 (Bound j) : Bts \<Rrightarrow> UU"
      using sB(1) tyB by simp_all
    have vb': "snd v \<le> maxidx env'" using mf(2) mx by simp
    obtain Gs \<sigma>3 where args: "args = map (\<lambda>G. G \<degree>\<degree> bvs (length Ts)) Gs"
      and GU: "list_all2 (\<lambda>G U. \<exists>x. G = Var x (Ts \<Rrightarrow> U)) Gs (Us @ Cs)"
      and Gi: "\<forall>G\<in>set Gs. \<exists>a U. G = Var (a, maxidx env' + 1) U" and lqb: "length Gs = length bs"
      and sa3': "sagree (maxidx env') \<sigma> \<sigma>3" and wt3: "wt_subst \<sigma>3" and sol3: "solution \<rho>2 \<sigma>3 env2"
      and apGl: "\<And>l. l < length Gs \<Longrightarrow> ap \<rho>2 \<sigma>3 (Gs ! l) = types_abs Ss (bs ! l)"
      and msum3: "(\<Sum>y\<in>lvars Gs. mcp_vsz \<rho>2 \<sigma>3 y) + 1 \<le> lsz (pushes mcp_e0 Ss) s"
      by (rule mcc_args[OF i2(1) i2(3) ma up vb' \<rho>2Ts \<rho>2UC cS(1) cBts(1) shB tybs _ tys nrs lbs])
        (use sp'(11) \<rho>2TX in simp_all)
    let ?q = "length Gs"
    have dpe: "list_comb (targs ! k) (map (\<lambda>arg. list_comb (head_of arg) targs) args) =
        (targs ! k) \<degree>\<degree> map (\<lambda>G. G \<degree>\<degree> targs) Gs"
    proof -
      have "head_of (G \<degree>\<degree> bvs (length Ts)) = G" if "G \<in> set Gs" for G
        using Gi that by (auto simp: head_of_apps)
      then show ?thesis by (simp add: args list_comb_apps comp_def cong: map_cong)
    qed
    \<comment> \<open>The new pair is solved:\<close>
    have sa3: "sagree (maxidx env) \<sigma> \<sigma>3" by (rule sagree_trans[OF sagree_refl sa3' mx])
    have ds2: "dsolved \<rho>2 \<sigma>3 (F @ ?P' # dps)"
    proof -
      let ?ts = "map (ap \<rho> \<sigma>) targs"
      have vb: "below (maxidx env) (vars t)" if "vars t \<subseteq> X \<union> evars env" for t
        using i(3) that unfolding vinv_def by (meson below_mono order_refl)
      have tvt: "(\<Union>t\<in>set targs. ttvars t) \<subseteq> ?KN" "ttvars u \<subseteq> ?KN"
        using upokD(3,4)[OF mcs_inv(3)[OF pre vN ty0]] by (auto simp: ttvars_apps)
      have apt: "ap \<rho>2 \<sigma>3 t = ap \<rho> \<sigma> t" if "t \<in> set targs" for t
        by (rule ap_agree[OF ag02 sa3 below_KN vb]) (use tvt mf(4) that in blast)+
      have apu: "ap \<rho>2 \<sigma>3 u = ap \<rho> \<sigma> u" by (rule ap_agree[OF ag02 sa3 below_KN vb]) (use tvt mf(3) in blast)+
      have apG: "ap \<rho>2 \<sigma>3 ((Gs ! l) \<degree>\<degree> targs) = types_abs Ss (bs ! l) \<degree>\<degree> ?ts" if "l < ?q" for l
        using apGl[OF that] apt by (simp add: ap_apps cong: map_cong)
      have tapt: "e \<tturnstile> ?ts : Ss"
        using tyt by (induction targs arbitrary: Ss) (auto split: list.splits intro: typing_ap[OF _ sd(3)])
      have tcs: "e \<turnstile> types_abs Ss s \<degree>\<degree> ?ts : UU" by (rule list_app_typeI[OF mcp_typing_val[OF tys lbs cS(1)] tapt])
      have lSs': "length Ss = length ?ts" using lSs by simp
      note cc = mcp_conv_cpy[OF tcs lSs']
      have cps: "mcp_cpy ?ts s = ap \<rho> \<sigma> (targs ! k) \<degree>\<degree> map (mcp_cpy ?ts) bs"
        using mcp_cpy_Bound[of j ?ts] sB lSs kdef kn by (simp add: mcp_cpy_apps ilength_eq)
      have lbs_arg: "\<forall>b\<in>set bs. \<not> loose_bvar b (ilength Ss)" using lbs sB(1) by (simp add: loose_bvar_apps)
      have lbs': "length bs = length Bts" using typings_nth[OF tybs] by simp
      have cb: "types_abs Ss (bs ! l) \<degree>\<degree> ?ts \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> mcp_cpy ?ts (bs ! l)"
        "e \<turnstile> types_abs Ss (bs ! l) \<degree>\<degree> ?ts : Bts ! l" if "l < length bs" for l
      proof -
        have "pushes mcp_e0 Ss \<turnstile> bs ! l : Bts ! l" using typings_nth[OF tybs] that by simp
        from list_app_typeI[OF mcp_typing_val[OF this] tapt] lbs_arg cS(1) that
        show t: "e \<turnstile> types_abs Ss (bs ! l) \<degree>\<degree> ?ts : Bts ! l" by simp
        show "types_abs Ss (bs ! l) \<degree>\<degree> ?ts \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> mcp_cpy ?ts (bs ! l)" using mcp_conv_cpy(1)[OF t] lSs' by simp
      qed
      have tk: "e \<turnstile> ap \<rho> \<sigma> (targs ! k) : Bts \<Rrightarrow> UU"
        using typing_ap[OF _ sd(3)] typings_nth[OF tyt] kn SsK lSs by auto
      have "ap \<rho>2 \<sigma>3 ((targs ! k) \<degree>\<degree> map (\<lambda>G. G \<degree>\<degree> targs) Gs) =
          ap \<rho> \<sigma> (targs ! k) \<degree>\<degree> map (\<lambda>b. types_abs Ss b \<degree>\<degree> ?ts) bs"
      proof -
        have "map (ap \<rho>2 \<sigma>3) (map (\<lambda>G. G \<degree>\<degree> targs) Gs) = map (\<lambda>b. types_abs Ss b \<degree>\<degree> ?ts) bs"
          by (rule nth_equalityI) (simp_all add: lqb apG)
        then show ?thesis using apt kn by (simp add: ap_apps)
      qed
      also have "\<dots> \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma> (targs ! k) \<degree>\<degree> map (mcp_cpy ?ts) bs"
      proof (rule conv_apps[OF _ _ _ conv_refl])
        show "list_all2 (\<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta>) (map (\<lambda>b. types_abs Ss b \<degree>\<degree> ?ts) bs) (map (mcp_cpy ?ts) bs)"
          by (rule list_all2_all_nthI) (simp_all add: cb(1))
        have "e \<tturnstile> map (\<lambda>b. types_abs Ss b \<degree>\<degree> ?ts) bs : Bts"
          by (rule typings_nthI) (simp_all add: lbs' cb(2))
        then show "wt (ap \<rho> \<sigma> (targs ! k) \<degree>\<degree> map (\<lambda>b. types_abs Ss b \<degree>\<degree> ?ts) bs)"
          using list_app_typeI[OF tk] by (auto simp: wt_def)
        have "e \<turnstile> mcp_cpy ?ts s : UU" by (rule cc(2))
        then show "wt (ap \<rho> \<sigma> (targs ! k) \<degree>\<degree> map (mcp_cpy ?ts) bs)" using cps by (auto simp: wt_def)
      qed
      also have "\<dots> = mcp_cpy ?ts s" by (rule cps[symmetric])
      also have "\<dots> \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> types_abs Ss s \<degree>\<degree> ?ts" by (rule conv_sym[OF cc(1)])
      also have "\<dots> \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho>2 \<sigma>3 u" using mcc_spre_cv[OF sp] apu by simp
      finally have "ap \<rho>2 \<sigma>3 ((targs ! k) \<degree>\<degree> map (\<lambda>G. G \<degree>\<degree> targs) Gs) \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho>2 \<sigma>3 u" .
      moreover have "dsolved \<rho>2 \<sigma>3 (F @ ?P # dps)" by (rule sc_dps_agree(2)[OF ps i(4) i(3) ag02 sa3 i(7)])
      ultimately show ?thesis by (auto simp: dsolved_def dpe)
    qed
    have inv3: "scinv \<rho>2 \<sigma>3 env2 (F @ ?P' # dps) ?X2 ?A1"
      by (rule mcc_scinv_cpinvX[OF inv c0 ms(1) sol3 ag02 sa3 ds2 ms(4)])
    \<comment> \<open>Simplification:\<close>
    have c3: "cpinvX A0 envM VM F ?A1 ?K1 ?X2 env2 (?P' # dps)" by (rule ms(4))
    have si3: "sinv ?A1 ?K1 ?X2 env2 (?P' # dps)" using c3 by (auto simp: cpinvX_def intro: sinv_mono)
    have finX2: "finite ?X2" and finK1: "finite ?K1" using c3 by (simp_all add: cpinvX_def)
    have inv3': "scinv \<rho>2 \<sigma>3 env2 (?P' # dps) ?X2 ?A1" by (rule scinv_mono[OF inv3]) auto
    obtain env3 ffs frs \<rho>4 \<sigma>4 where sm: "okW (SIMPL (cfg_alg cfg) env2 (?P' # dps)) (env3, ffs, frs)"
      and spost: "simpl_post ?A1 ?K1 ?X2 env2 (env3, ffs, frs)" and inv4: "scinv \<rho>4 \<sigma>4 env3 (frs @ ffs) ?X2 ?A1"
      and ag4: "tagree (maxidx env2) \<rho>2 \<rho>4" and sa4: "sagree (maxidx env2) \<sigma>3 \<sigma>4"
      by (rule mcp_SIMPL[OF cfg finX2 finK1 si3 inv3'])
    have c4: "cpinvX A0 envM VM F ?A1 ?K1 ?X2 env3 (ffs @ frs)" by (rule simpl_post_cpinvX[OF c3 spost])
    note ss = mcp_sstepD[OF conjunct2[OF conjunct2[OF conjunct2[OF spost[unfolded simpl_post_def prod.case]]]]]
    have ub4: "ubv env3 ?X2 \<subseteq> ubv env2 ?X2" by (rule mcp_SIMPL_ubv[OF sm[unfolded cfg] finX2 finK1 si3])
    have pF2: "\<forall>(rb', t', u')\<in>set F. upok ?A1 env2 rb' ?X2 t' u'" using c3 by (auto simp: cpinvX_def sinv_def)
    have inv4': "scinv \<rho>4 \<sigma>4 env3 (F @ ffs @ frs) ?X2 ?A1"
    proof (rule mcc_scinv_frame[OF inv3 pF2 _ ag4 sa4])
      show "scinv \<rho>4 \<sigma>4 env3 (ffs @ frs) ?X2 ?A1" by (rule scinv_mono[OF inv4]) auto
    qed
    \<comment> \<open>The result:\<close>
    have mx2: "maxidx env \<le> maxidx env2" using extends_maxidx[OF ms(3)] .
    have ext3: "extends env env3" by (rule extends_trans[OF ms(3) ss(1)])
    have Gidx: "\<forall>y\<in>lvars Gs. snd (fst y) = maxidx env' + 1" using Gi by auto
    have GX2: "lvars Gs \<subseteq> ?X2"
      using Gi dpe by (auto simp: vars_apps)
    have vbG: "snd (fst y) \<le> maxidx env2" if "y \<in> lvars Gs" for y
      using scinvD(3)[OF inv3] GX2 that unfolding vinv_def below_def by blast
    have tvG: "tbelow (maxidx env2) (tvars (snd y))" if "y \<in> lvars Gs" for y
    proof -
      have "y \<in> ?X2" using GX2 that by blast
      then have "tvars (snd y) \<subseteq> vtvars ?X2" by (cases y) (rule tvars_vtvars, simp)
      then show ?thesis
        using tvinv_tbelow[OF scinvD(4)[OF inv3]] scinvD(5)[OF inv3] by blast
    qed
    have vsz4: "mcp_vsz \<rho>4 \<sigma>4 y = mcp_vsz \<rho>2 \<sigma>3 y" if "y \<in> lvars Gs" for y
    proof -
      obtain x T where y: "y = (x, T)" by (cases y)
      show ?thesis unfolding y
        by (rule mcp_vsz_agree[OF ag4 sa4]) (use vbG[OF that] tvG[OF that] y in simp_all)
    qed
    have vT: "(v, TX) \<in> X \<union> evars env"
      using upokD(1)[OF mcs_inv(3)[OF pre vN ty0]] by (auto simp: vars_apps)
    have ub2: "ubv env2 ?X2 \<subseteq> (ubv env X - {v}) \<union> fst ` lvars Gs"
    proof (rule mcc_ubv_bind[OF up])
      show "tenv env1 = tenv env" using te1 post(2) gs(1) by simp
      show "v \<in> fst ` (?X2 \<union> evars env)" using vT by force
      have "dvars (F @ ?P' # dps) \<subseteq> lvars Gs \<union> (X \<union> evars env)"
        using mf(3,4,7) nth_mem[OF kn] Gi by (auto simp: dpe vars_apps)
      then show "fst ` (?X2 \<union> evars env) \<subseteq> fst ` (X \<union> evars env) \<union> fst ` lvars Gs" by blast
      show "fst ` vars (types_abs Ts (list_comb (Bound j) args)) \<subseteq> fst ` lvars Gs"
        by (auto simp: args list_comb_apps vars_apps)
    qed
    have r: "mcc_res A0 envM VM F A K X env (v, TX) \<rho> \<sigma> 1 (El_E env3 (ffs @ frs))"
    proof (rule mcc_resI[OF refl c4 _ _ _ inv4' ext3 _ _ _ GX2])
      show "A \<subseteq> ?A1" "K \<subseteq> ?K1" "X \<subseteq> ?X2" by auto
      show "tagree (maxidx env) \<rho> \<rho>4" by (rule tagree_trans[OF ag02 ag4 mx2])
      show "sagree (maxidx env) \<sigma> \<sigma>4" by (rule sagree_trans[OF sa3 sa4 mx2])
      show "finite (lvars Gs)" by simp
      show "\<forall>y\<in>lvars Gs. maxidx env < snd (fst y) \<or> y = (v, TX)" using Gidx mx by simp
      show "ubv env3 ?X2 \<subseteq> (ubv env X - {fst (v, TX)}) \<union> fst ` lvars Gs" using ub4 ub2 by auto
      have "(\<Sum>y\<in>lvars Gs. mcp_vsz \<rho>4 \<sigma>4 y) = (\<Sum>y\<in>lvars Gs. mcp_vsz \<rho>2 \<sigma>3 y)"
        by (rule sum.cong) (simp_all add: vsz4)
      moreover have "mcp_vsz \<rho> \<sigma> (v, TX) = lsz (pushes mcp_e0 Ss) s" using mcc_vsz[OF sp] ar0 by simp
      ultimately show "(\<Sum>y\<in>lvars Gs. mcp_vsz \<rho>4 \<sigma>4 y) + 1 \<le> mcp_vsz \<rho> \<sigma> (v, TX)" using msum3 by simp
      show "\<forall>k'. mcp_kokK k' \<rho> (tyenv env) A K \<longrightarrow> mcp_kokK k' \<rho>4 (tyenv env3) ?A1 ?K1"
      proof (intro allI impI)
        fix k' assume k0: "mcp_kokK k' \<rho> (tyenv env) A K"
        have k2: "mcp_kokK k' \<rho>2 (tyenv env2) ?A1 ?K1" using kk2 k0 ms(2) by simp
        have ei4: "einv ?A1 ?K1 env3" using c4 by (auto simp: cpinvX_def sinv_def)
        note x4 = einvD[OF ei4]
        have tx4: "textends (tyenv env2) (tyenv env3)" using ss(1) by (simp add: extends_def)
        have below2: "tbelow (maxidx env2) (tvars_env (tyenv env2) \<union> ?A1)"
          using tvinv_tbelow[OF scinvD(4)[OF inv3]] by blast
        have ei2: "einv ?A1 ?K1 env2" using c3 by (auto simp: cpinvX_def sinv_def)
        have "mcp_kokK k' \<rho>4 (tyenv env3) ?A1 (?K1 \<union> {})"
          by (rule mcp_kokK_ext[OF k2 tx4 x4(6) x4(7) solutionD(2)[OF scinvD(1)[OF inv4]] ag4 below2
                einvD(6)[OF ei2] tinv_tcons[OF x4(2)]]) (use ss(2) in auto)
        then show "mcp_kokK k' \<rho>4 (tyenv env3) ?A1 ?K1" by simp
      qed
    qed
    show "\<exists>env2 env3 fr ff. ok (update (v, TX) (types_abs Ts (list_comb (Bound j) args)) env1) env2 \<and>
        okW (SIMPL (cfg_alg cfg) env2 (?P' # dps)) (env3, fr, ff) \<and>
        mcc_res A0 envM VM F A K X env (v, TX) \<rho> \<sigma> 1 (El_E env3 (fr @ ff))"
      using up sm r by blast
  qed
qed

subsection \<open>Copies: arguments of an imitation\<close>

text \<open>A result for more variables of the problem is a result for fewer, if they add no unbound ones:\<close>

lemma mcc_res_X:
  assumes r: "mcc_res A0 envM VM F A K X1 env X0 \<rho> \<sigma> m x" and XX: "X \<subseteq> X1"
    and ub: "ubv env X1 \<subseteq> ubv env X"
  shows "mcc_res A0 envM VM F A K X env X0 \<rho> \<sigma> m x"
  using r
proof (rule mcc_resE)
  fix env' dps' A' K' X' \<rho>' \<sigma>' NV
  assume a: "x = El_E env' dps'" "cpinvX A0 envM VM F A' K' X' env' dps'"
    "A \<subseteq> A'" "K \<subseteq> K'" "X1 \<subseteq> X'" "scinv \<rho>' \<sigma>' env' (F @ dps') X' A'" "extends env env'"
    "tagree (maxidx env) \<rho> \<rho>'" "sagree (maxidx env) \<sigma> \<sigma>'"
    "finite NV" "NV \<subseteq> X'" "\<forall>y\<in>NV. maxidx env < snd (fst y) \<or> y = X0"
    "ubv env' X' \<subseteq> (ubv env X1 - {fst X0}) \<union> fst ` NV"
    "(\<Sum>y\<in>NV. mcp_vsz \<rho>' \<sigma>' y) + m \<le> mcp_vsz \<rho> \<sigma> X0"
    "\<forall>k. mcp_kokK k \<rho> (tyenv env) A K \<longrightarrow> mcp_kokK k \<rho>' (tyenv env') A' K'"
  show ?thesis
  proof (rule mcc_resI[OF a(1-4) _ a(6-12) _ a(14,15)])
    show "X \<subseteq> X'" using XX a(5) by blast
    show "ubv env' X' \<subseteq> (ubv env X - {fst X0}) \<union> fst ` NV" using a(13) ub by blast
  qed
qed

lemma mcc_okW_copycons:
  assumes G: "G = Var x U" and h: "head_norm envM uarg = return u1" and et: "eta_norm en rb u1 = return u2"
    and dW: "okW (if 0 < cfg_arity_bound cfg then liftM (defer_arg en rb u2) else returnW False) d0"
    and s: "okW (if d0 then returnW (S_Single (El_E en ((rb, list_comb G targs, u2) # d)))
      else mc cfg vname envM (x, U) rb targs u2 en d) cs"
  shows "okW (copycons cfg vname envM rb targs G uarg en d) cs"
proof -
  have h1: "ok (head_norm envM uarg) u1" and e2: "ok (eta_norm en rb u1) u2"
    using h et by (simp_all add: return_def)
  show ?thesis
    unfolding copycons_def okW_bindW okW_liftM
    by (rule exI[of _ "(x, U)"], rule conjI, simp add: G,
        rule exI[of _ u1], rule conjI[OF h1], rule exI[of _ u2], rule conjI[OF e2],
        rule exI[of _ d0], rule conjI[OF dW], rule s)
qed

text \<open>
  The copy of an argument with target \<open>b\<close>: the argument is normalized, and deferred or copied.
  The completeness of the copies of \<^const>\<open>mc\<close> for the target is a hypothesis.
\<close>

lemma mcc_copycons:
  assumes cfg: "cfg_alg cfg = alg" and M: "menv envM VM"
    and c: "cpinvX A0 envM VM F A K X en ((rb, G \<degree>\<degree> targs, uarg) # d)" and vu: "vars uarg \<subseteq> VM"
    and G: "G = Var x U"
    and inv: "scinv \<rho> \<sigma> en (F @ (rb, G \<degree>\<degree> targs, uarg) # d) X A"
    and kk: "mcp_kokK (nat_of_integer (cfg_arity_bound cfg)) \<rho> (tyenv en) A K"
    and bs: "bs_env \<rho> e rb" and tyt: "e \<tturnstile> map (inst \<rho>) targs : Ss" and tya: "e \<turnstile> inst \<rho> uarg : B"
    and TU: "tsubst \<rho> U = Ss \<Rrightarrow> B" and cSB: "cert_typ alg ar (Ss \<Rrightarrow> B)"
    and tyb: "pushes mcp_e0 Ss \<turnstile> b : B" and nrb: "no_redex b" and lbb: "\<not> loose_bvar b (ilength Ss)"
    and \<sigma>x: "\<sigma> x (Ss \<Rrightarrow> B) \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> types_abs Ss b"
    and IH: "\<And>A' K' X' u' \<sigma>'. mcpre A0 envM VM F A' K' X' en rb (x, U) targs u' d None \<Longrightarrow>
      mcc_spre \<rho> \<sigma>' en (F @ (rb, Var x U \<degree>\<degree> targs, u') # d) X' A' e rb (x, U) targs Ss u' B b \<Longrightarrow>
      mcp_kokK (nat_of_integer (cfg_arity_bound cfg)) \<rho> (tyenv en) A' K' \<Longrightarrow>
      \<exists>sq. okW (mc cfg vname envM (x, U) rb targs u' en d) sq \<and>
        (\<exists>y. ev cfg sq y \<and> (\<exists>m. mcc_res A0 envM VM F A' K' X' en (x, U) \<rho> \<sigma>' m y))"
  shows "\<exists>cs. okW (copycons cfg vname envM rb targs G uarg en d) cs \<and>
    (\<exists>y. ev cfg cs y \<and> mcc_res A0 envM VM F A K X en (x, U) \<rho> \<sigma> 0 y)"
proof -
  obtain u1 u2 A2 B2 where h: "head_norm envM uarg = return u1" and et: "eta_norm en rb u1 = return u2"
    and tc: "tconv en rb uarg u2" and vu2: "vars u2 \<subseteq> VM" and sat: "satd en rb u2"
    and da: "defer_arg en rb u2 = return (is_TVar B2)"
    and fA: "fastype en rb u2 = return A2" and bB: "body_type en A2 = return B2"
    and tvB2: "tvars B2 \<subseteq> tvars_env (tyenv en) \<union> A" and na2: "nabs u2 = arity (tsubst (rho0 en) A2)"
    and dc: "dstep en ((rb, G \<degree>\<degree> targs, uarg) # d) en ((rb, G \<degree>\<degree> targs, u2) # d)"
    and c2: "cpinvX A0 envM VM F A K (X \<union> dvars (F @ (rb, G \<degree>\<degree> targs, u2) # d)) en ((rb, G \<degree>\<degree> targs, u2) # d)"
    by (rule cc_inv[OF M c vu])
  let ?P2 = "(rb, G \<degree>\<degree> targs, u2)" and ?X2 = "X \<union> dvars (F @ (rb, G \<degree>\<degree> targs, u2) # d)"
  note i = scinvD[OF inv] and sd = solutionD[OF scinvD(1)[OF inv]]
  have ei: "einv A K en" using c by (auto simp: cpinvX_def sinv_def)
  note E = einvD[OF ei]
  have p: "upok A en rb X (G \<degree>\<degree> targs) uarg" using c by (auto simp: cpinvX_def sinv_def)
  note pd = upokD[OF p]
  have VX: "VM \<subseteq> X \<union> evars en" using c by (simp add: cpinvX_def)
  have tc': "e \<turnstile> inst \<rho> u2 : B \<and> \<not> loose_bvar u2 (ilength rb) \<and> (\<forall>\<sigma>'. solution \<rho> \<sigma>' en \<longrightarrow> ap \<rho> \<sigma>' uarg \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma>' u2)"
    using tc sd(2) i(2) bs tya pd(8) unfolding tconv_def by blast
  have tyu2: "e \<turnstile> inst \<rho> u2 : B" and apc: "ap \<rho> \<sigma> uarg \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma> u2" using tc' i(1) by blast+
  have ds: "dsolved \<rho> \<sigma> (F @ ?P2 # d)"
  proof -
    have "ap \<rho> \<sigma> (G \<degree>\<degree> targs) \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma> uarg" using i(7) by (auto simp: dsolved_def)
    then have "ap \<rho> \<sigma> (G \<degree>\<degree> targs) \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma> u2" using apc by (rule conv_trans)
    then show ?thesis using i(7) by (auto simp: dsolved_def)
  qed
  have inv2: "scinv \<rho> \<sigma> en (F @ ?P2 # d) ?X2 A"
    by (rule mcc_scinv_cpinvX[OF inv c dc i(1) tagree_refl sagree_refl ds c2])
  have ubX2: "ubv en ?X2 \<subseteq> ubv en X"
  proof -
    have "dvars (F @ ?P2 # d) \<subseteq> X \<union> evars en"
      using sinv_dvars[OF conjunct2[OF conjunct2[OF conjunct2[OF conjunct2[OF conjunct2[OF conjunct2[OF
          conjunct2[OF conjunct2[OF c[unfolded cpinvX_def]]]]]]]]]] vu2 VX pd(1) by (auto simp: vars_apps)
    then show ?thesis unfolding ubv_def by blast
  qed
  have xX: "(x, U) \<in> ?X2" by (simp add: G vars_apps)
  let ?d = "0 < cfg_arity_bound cfg \<and> is_TVar B2"
  have dW: "okW (if 0 < cfg_arity_bound cfg then liftM (defer_arg en rb u2) else returnW False) ?d"
    using da by (auto simp: return_def)
  show ?thesis
  proof (cases ?d)
    case True
    let ?cs = "S_Single (El_E en ((rb, list_comb G targs, u2) # d))"
    have ok: "okW (copycons cfg vname envM rb targs G uarg en d) ?cs"
      by (rule mcc_okW_copycons[OF G h et dW]) (use True in simp)
    have "mcc_res A0 envM VM F A K X en (x, U) \<rho> \<sigma> 0 (El_E en (?P2 # d))"
    proof (rule mcc_resI[OF refl c2 order_refl order_refl _ inv2 extends_refl tagree_refl sagree_refl])
      show "X \<subseteq> ?X2" by blast
      show "finite {(x, U)}" "{(x, U)} \<subseteq> ?X2" "\<forall>y\<in>{(x, U)}. maxidx en < snd (fst y) \<or> y = (x, U)"
        using xX by auto
      show "ubv en ?X2 \<subseteq> (ubv en X - {fst (x, U)}) \<union> fst ` {(x, U)}" using ubX2 by auto
    qed simp_all
    then have "ev cfg ?cs (El_E en ((rb, list_comb G targs, u2) # d)) \<and>
        mcc_res A0 envM VM F A K X en (x, U) \<rho> \<sigma> 0 (El_E en ((rb, list_comb G targs, u2) # d))"
      by (simp add: list_comb_apps ev.single)
    with ok show ?thesis by blast
  next
    case False
    have arB: "arity B = nabs u2"
    proof -
      from mf_body_type_sound[of en A2 "Ok B2" B2] bB E(6) obtain Zs where
        nb: "\<forall>C D. tnorm (tyenv en) B2 \<noteq> C \<rightarrow>\<^sub>T D"
        and Zs: "\<And>\<rho>'. tsol (tyenv en) \<rho>' \<Longrightarrow> tsubst \<rho>' A2 = map (tsubst \<rho>') Zs \<Rrightarrow> tsubst \<rho>' B2"
        by (auto simp: return_def)
      have "tsubst (rho0 en) A2 = map (tsubst (rho0 en)) Zs \<Rrightarrow> tnorm (tyenv en) B2"
        using Zs[OF einv_rho0(1)[OF ei]] by (simp add: tnorm_tsubst[symmetric])
      then have aT: "nabs u2 = length Zs" using na2 mcp_arity_nonarrow[OF nb] by (simp add: arity_funs)
      have "B = tsubst \<rho> A2" by (rule fastype_sound[OF _ sd(2) bs tyu2, symmetric]) (use fA in \<open>simp add: return_def\<close>)
      also have "\<dots> = map (tsubst \<rho>) Zs \<Rrightarrow> tsubst \<rho> B2" by (rule Zs[OF sd(2)])
      finally have aB: "arity B = length Zs + arity (tsubst \<rho> B2)" by (simp add: arity_funs)
      have "arity (tsubst \<rho> B2) = 0"
      proof (cases "is_TVar B2")
        case True
        with False have b0: "\<not> 0 < cfg_arity_bound cfg" by simp
        from mcp_body_type_TVar[of en A2 "Ok B2" B2] bB True obtain w S where
          bv: "B2 = TVar w S" "vt_lookup (tyenv en) w = None" by (auto simp: return_def)
        have "(w, S) \<in> tvars_env (tyenv en) \<union> A" using tvB2 bv by simp
        from mcp_aok_arity[OF mcp_kok_unbound[OF mcp_kokK_kok[OF kk ei] this bv(2) E(6)]]
        have "arity (\<rho> w S) \<le> nat_of_integer (cfg_arity_bound cfg)" .
        moreover have "nat_of_integer (cfg_arity_bound cfg) = 0"
          using b0 by (simp add: nat_of_integer.rep_eq less_integer.rep_eq)
        ultimately show ?thesis using bv by simp
      next
        case False
        then show ?thesis by (rule mcp_body_type_nonTVar_arity[OF bB[unfolded return_def] _ E(6)])
      qed
      with aB aT show ?thesis by simp
    qed
    have pre2: "mcpre A0 envM VM F A K ?X2 en rb (x, U) targs u2 d None"
      by (rule mcpreI) (use c2 vu2 sat in \<open>simp_all add: G msat_def\<close>)
    have sp2: "mcc_spre \<rho> \<sigma> en (F @ (rb, Var x U \<degree>\<degree> targs, u2) # d) ?X2 A e rb (x, U) targs Ss u2 B b"
      unfolding mcc_spre_def using inv2 bs tyt tyu2 arB TU cSB tyb nrb lbb \<sigma>x by (simp add: G)
    from IH[OF pre2 sp2 kk] obtain sq y m where sq: "okW (mc cfg vname envM (x, U) rb targs u2 en d) sq"
      and evy: "ev cfg sq y" and r: "mcc_res A0 envM VM F A K ?X2 en (x, U) \<rho> \<sigma> m y" by blast
    have ok: "okW (copycons cfg vname envM rb targs G uarg en d) sq"
      by (rule mcc_okW_copycons[OF G h et dW]) (simp only: if_not_P[OF False] sq)
    have "mcc_res A0 envM VM F A K X en (x, U) \<rho> \<sigma> 0 y"
      by (rule mcc_res_m[OF mcc_res_X[OF r _ ubX2]]) auto
    with ok evy show ?thesis by blast
  qed
qed

text \<open>The variable of a new argument variable:\<close>

fun mcc_vt :: "pterm \<Rightarrow> indexname \<times> ptyp" where
  "mcc_vt (Var x T) = (x, T)"
| "mcc_vt _ = undefined"

text \<open>
  A result of the copies of the arguments into their variables \<open>GV\<close>: the variables are bound unless
  they are among the unbound variables \<open>NV\<close>, which are new otherwise, and whose values are not
  larger in total.
\<close>

definition mcc_dres :: "(indexname \<times> psort) set \<Rightarrow> env \<Rightarrow> (indexname \<times> ptyp) set \<Rightarrow> dpair list \<Rightarrow>
    (indexname \<times> psort) set \<Rightarrow> (indexname \<times> psort) set \<Rightarrow> (indexname \<times> ptyp) set \<Rightarrow> env \<Rightarrow>
    (indexname \<times> ptyp) set \<Rightarrow> tinst \<Rightarrow> vsubst \<Rightarrow> elem \<Rightarrow> bool" where
  "mcc_dres A0 envM VM F A K X env GV \<rho> \<sigma> x \<longleftrightarrow>
    (\<exists>env' dps' A' K' X' \<rho>' \<sigma>' NV. x = El_E env' dps' \<and> cpinvX A0 envM VM F A' K' X' env' dps' \<and>
      A \<subseteq> A' \<and> K \<subseteq> K' \<and> X \<subseteq> X' \<and> scinv \<rho>' \<sigma>' env' (F @ dps') X' A' \<and> extends env env' \<and>
      tagree (maxidx env) \<rho> \<rho>' \<and> sagree (maxidx env) \<sigma> \<sigma>' \<and>
      finite NV \<and> NV \<subseteq> X' \<and> (\<forall>y\<in>NV. maxidx env < snd (fst y) \<or> y \<in> GV) \<and>
      ubv env' X' \<subseteq> (ubv env X - fst ` GV) \<union> fst ` NV \<and>
      (\<Sum>y\<in>NV. mcp_vsz \<rho>' \<sigma>' y) \<le> (\<Sum>y\<in>GV. mcp_vsz \<rho> \<sigma> y) \<and>
      (\<forall>k. mcp_kokK k \<rho> (tyenv env) A K \<longrightarrow> mcp_kokK k \<rho>' (tyenv env') A' K'))"

lemma mcc_dresI:
  assumes "x = El_E env' dps'" "cpinvX A0 envM VM F A' K' X' env' dps'"
    "A \<subseteq> A'" "K \<subseteq> K'" "X \<subseteq> X'" "scinv \<rho>' \<sigma>' env' (F @ dps') X' A'" "extends env env'"
    "tagree (maxidx env) \<rho> \<rho>'" "sagree (maxidx env) \<sigma> \<sigma>'"
    "finite NV" "NV \<subseteq> X'" "\<forall>y\<in>NV. maxidx env < snd (fst y) \<or> y \<in> GV"
    "ubv env' X' \<subseteq> (ubv env X - fst ` GV) \<union> fst ` NV"
    "(\<Sum>y\<in>NV. mcp_vsz \<rho>' \<sigma>' y) \<le> (\<Sum>y\<in>GV. mcp_vsz \<rho> \<sigma> y)"
    "\<forall>k. mcp_kokK k \<rho> (tyenv env) A K \<longrightarrow> mcp_kokK k \<rho>' (tyenv env') A' K'"
  shows "mcc_dres A0 envM VM F A K X env GV \<rho> \<sigma> x"
  unfolding mcc_dres_def
  by (rule exI[of _ env'], rule exI[of _ dps'], rule exI[of _ A'], rule exI[of _ K'], rule exI[of _ X'],
      rule exI[of _ \<rho>'], rule exI[of _ \<sigma>'], rule exI[of _ NV]) (intro conjI; fact)

lemma mcc_dresE:
  assumes "mcc_dres A0 envM VM F A K X env GV \<rho> \<sigma> x"
  obtains env' dps' A' K' X' \<rho>' \<sigma>' NV where "x = El_E env' dps'" "cpinvX A0 envM VM F A' K' X' env' dps'"
    "A \<subseteq> A'" "K \<subseteq> K'" "X \<subseteq> X'" "scinv \<rho>' \<sigma>' env' (F @ dps') X' A'" "extends env env'"
    "tagree (maxidx env) \<rho> \<rho>'" "sagree (maxidx env) \<sigma> \<sigma>'"
    "finite NV" "NV \<subseteq> X'" "\<forall>y\<in>NV. maxidx env < snd (fst y) \<or> y \<in> GV"
    "ubv env' X' \<subseteq> (ubv env X - fst ` GV) \<union> fst ` NV"
    "(\<Sum>y\<in>NV. mcp_vsz \<rho>' \<sigma>' y) \<le> (\<Sum>y\<in>GV. mcp_vsz \<rho> \<sigma> y)"
    "\<forall>k. mcp_kokK k \<rho> (tyenv env) A K \<longrightarrow> mcp_kokK k \<rho>' (tyenv env') A' K'"
  using assms unfolding mcc_dres_def by (elim exE conjE) (rule that; assumption)

text \<open>
  The copies of the arguments, each with the frame of the others. The variables of the arguments
  have distinct names, of index at most \<open>n\<close>; the completeness of the copy of each argument is a
  hypothesis, for every state whose solution agrees with \<open>(\<rho>, \<sigma>)\<close> up to \<open>n\<close>.
\<close>

lemma mcc_copyargs:
  assumes CC: "\<And>F' A' K' X' en d' G uarg \<rho>' \<sigma>'. (G, uarg) \<in> set gus \<Longrightarrow>
      cpinvX A0 envM VM F' A' K' X' en ((rb, G \<degree>\<degree> targs, uarg) # d') \<Longrightarrow>
      scinv \<rho>' \<sigma>' en (F' @ (rb, G \<degree>\<degree> targs, uarg) # d') X' A' \<Longrightarrow>
      tagree n \<rho> \<rho>' \<Longrightarrow> sagree n \<sigma> \<sigma>' \<Longrightarrow> n \<le> maxidx en \<Longrightarrow>
      mcp_kokK k \<rho>' (tyenv en) A' K' \<Longrightarrow>
      \<exists>cs. okW (copycons cfg vname envM rb targs G uarg en d') cs \<and>
        (\<exists>y. ev cfg cs y \<and> mcc_res A0 envM VM F' A' K' X' en (mcc_vt G) \<rho>' \<sigma>' 0 y)"
    and Gv: "\<forall>(G, uarg)\<in>set gus. \<exists>x U. G = Var x U \<and> snd x \<le> n"
    and dist: "distinct (map (fst \<circ> mcc_vt \<circ> fst) gus)"
  shows "cpinvX A0 envM VM F A K X en (map (\<lambda>(G, uarg). (rb, G \<degree>\<degree> targs, uarg)) gus @ d) \<Longrightarrow>
    scinv \<rho>' \<sigma>' en (F @ map (\<lambda>(G, uarg). (rb, G \<degree>\<degree> targs, uarg)) gus @ d) X A \<Longrightarrow>
    tagree n \<rho> \<rho>' \<Longrightarrow> sagree n \<sigma> \<sigma>' \<Longrightarrow> n \<le> maxidx en \<Longrightarrow> mcp_kokK k \<rho>' (tyenv en) A K \<Longrightarrow>
    \<exists>y. ev cfg (copyargs vname envM rb targs gus en d) y \<and>
      mcc_dres A0 envM VM F A K X en (set (map (mcc_vt \<circ> fst) gus)) \<rho>' \<sigma>' y"
  using CC Gv dist
proof (induction gus arbitrary: F)
  case Nil
  have "mcc_dres A0 envM VM F A K X en {} \<rho>' \<sigma>' (El_E en d)"
    by (rule mcc_dresI[where NV = "{}", OF refl _ order_refl order_refl order_refl _ extends_refl tagree_refl sagree_refl])
      (use Nil.prems(1,2) in simp_all)
  then show ?case by (auto intro: ev.single)
next
  case (Cons gu gus)
  obtain G uarg where gu: "gu = (G, uarg)" by (cases gu)
  let ?p = "(rb, G \<degree>\<degree> targs, uarg)" and ?ps = "map (\<lambda>(G, uarg). (rb, G \<degree>\<degree> targs, uarg)) gus"
  from Cons.prems(8) gu obtain x U where G: "G = Var x U" and xn: "snd x \<le> n" by auto
  have c1: "cpinvX A0 envM VM (F @ [?p]) A K X en (?ps @ d)"
    by (rule cpinvX_set[OF Cons.prems(1)]) (auto simp: gu)
  have inv1: "scinv \<rho>' \<sigma>' en ((F @ [?p]) @ ?ps @ d) X A"
    by (rule scinv_mono[OF Cons.prems(2)]) (auto simp: gu)
  have dist': "distinct (map (fst \<circ> mcc_vt \<circ> fst) gus)" using Cons.prems(9) by (simp add: comp_def)
  have xGs: "x \<notin> fst ` set (map (mcc_vt \<circ> fst) gus)"
    using Cons.prems(9) gu G by (simp add: image_image comp_def)
  from Cons.IH[OF c1 inv1 Cons.prems(3-6) _ _ dist'] Cons.prems(7,8)
  obtain y1 where ev1: "ev cfg (copyargs vname envM rb targs gus en d) y1"
    and r1: "mcc_dres A0 envM VM (F @ [?p]) A K X en (set (map (mcc_vt \<circ> fst) gus)) \<rho>' \<sigma>' y1" by auto
  let ?GV = "set (map (mcc_vt \<circ> fst) gus)"
  from r1 obtain e1 d1 A1 K1 X1 \<rho>1 \<sigma>1 NV1 where y1: "y1 = El_E e1 d1"
    and c1': "cpinvX A0 envM VM (F @ [?p]) A1 K1 X1 e1 d1" and AK1: "A \<subseteq> A1" "K \<subseteq> K1" "X \<subseteq> X1"
    and inv1': "scinv \<rho>1 \<sigma>1 e1 ((F @ [?p]) @ d1) X1 A1" and ext1: "extends en e1"
    and ag1: "tagree (maxidx en) \<rho>' \<rho>1" "sagree (maxidx en) \<sigma>' \<sigma>1"
    and NV1: "finite NV1" "NV1 \<subseteq> X1" "\<forall>y\<in>NV1. maxidx en < snd (fst y) \<or> y \<in> ?GV"
    and ub1: "ubv e1 X1 \<subseteq> (ubv en X - fst ` ?GV) \<union> fst ` NV1"
    and sz1: "(\<Sum>y\<in>NV1. mcp_vsz \<rho>1 \<sigma>1 y) \<le> (\<Sum>y\<in>?GV. mcp_vsz \<rho>' \<sigma>' y)"
    and kk1: "\<forall>k. mcp_kokK k \<rho>' (tyenv en) A K \<longrightarrow> mcp_kokK k \<rho>1 (tyenv e1) A1 K1"
    by (rule mcc_dresE)
  have mx1: "maxidx en \<le> maxidx e1" by (rule extends_maxidx[OF ext1])
  have c2: "cpinvX A0 envM VM F A1 K1 X1 e1 (?p # d1)" by (rule cpinvX_set[OF c1']) auto
  have inv2: "scinv \<rho>1 \<sigma>1 e1 (F @ ?p # d1) X1 A1" by (rule scinv_mono[OF inv1']) auto
  have ag2: "tagree n \<rho> \<rho>1" "sagree n \<sigma> \<sigma>1"
    using tagree_trans[OF Cons.prems(3) ag1(1)] sagree_trans[OF Cons.prems(4) ag1(2)] Cons.prems(5) by auto
  from Cons.prems(7)[OF _ c2 inv2 ag2 order_trans[OF Cons.prems(5) mx1]] kk1 Cons.prems(6) gu
  obtain cs y where cs: "okW (copycons cfg vname envM rb targs G uarg e1 d1) cs" and evy: "ev cfg cs y"
    and r2: "mcc_res A0 envM VM F A1 K1 X1 e1 (x, U) \<rho>1 \<sigma>1 0 y" by (auto simp: G)
  have ev: "ev cfg (copyargs vname envM rb targs (gu # gus) en d) y"
    using ev.maps[OF ev1[unfolded y1] cs evy] by (simp add: gu)
  from r2 obtain ef df Af Kf Xf \<rho>f \<sigma>f NV2 where y: "y = El_E ef df"
    and cf: "cpinvX A0 envM VM F Af Kf Xf ef df" and AK2: "A1 \<subseteq> Af" "K1 \<subseteq> Kf" "X1 \<subseteq> Xf"
    and invf: "scinv \<rho>f \<sigma>f ef (F @ df) Xf Af" and ext2: "extends e1 ef"
    and ag3: "tagree (maxidx e1) \<rho>1 \<rho>f" "sagree (maxidx e1) \<sigma>1 \<sigma>f"
    and NV2: "finite NV2" "NV2 \<subseteq> Xf" "\<forall>y\<in>NV2. maxidx e1 < snd (fst y) \<or> y = (x, U)"
    and ub2: "ubv ef Xf \<subseteq> (ubv e1 X1 - {fst (x, U)}) \<union> fst ` NV2"
    and sz2: "(\<Sum>y\<in>NV2. mcp_vsz \<rho>f \<sigma>f y) + 0 \<le> mcp_vsz \<rho>1 \<sigma>1 (x, U)"
    and kk2: "\<forall>k. mcp_kokK k \<rho>1 (tyenv e1) A1 K1 \<longrightarrow> mcp_kokK k \<rho>f (tyenv ef) Af Kf"
    by (rule mcc_resE)
  let ?GV' = "set (map (mcc_vt \<circ> fst) (gu # gus))"
  have GV': "?GV' = insert (x, U) ?GV" by (simp add: gu G)
  have xU: "(x, U) \<notin> ?GV" using xGs image_eqI[of x fst "(x, U)"] by auto
  \<comment> \<open>The values of the old variables are kept:\<close>
  have below1: "snd (fst y) \<le> maxidx e1" "tbelow (maxidx e1) (tvars (snd y))" if "y \<in> X1" for y
  proof -
    note i1 = scinvD[OF inv1']
    show "snd (fst y) \<le> maxidx e1" using i1(3) that unfolding vinv_def below_def by blast
    have "tvars (snd y) \<subseteq> vtvars X1" using that by (cases y) (rule tvars_vtvars, simp)
    then show "tbelow (maxidx e1) (tvars (snd y))" using tvinv_tbelow[OF i1(4)] i1(5) by blast
  qed
  have vsz1: "mcp_vsz \<rho>f \<sigma>f y = mcp_vsz \<rho>1 \<sigma>1 y" if "y \<in> X1" for y
  proof -
    obtain z T where yz: "y = (z, T)" by (cases y)
    show ?thesis unfolding yz by (rule mcp_vsz_agree[OF ag3]) (use below1[OF that] yz in simp_all)
  qed
  have below0: "tbelow (maxidx en) (tvars U)"
  proof -
    note i0 = scinvD[OF Cons.prems(2)]
    have "?p \<in> set (F @ map (\<lambda>(G, uarg). (rb, G \<degree>\<degree> targs, uarg)) (gu # gus) @ d)" by (simp add: gu)
    then have "upok A en rb X (G \<degree>\<degree> targs) uarg" using Cons.prems(1) unfolding cpinvX_def sinv_def by blast
    then have "(x, U) \<in> X \<union> evars en" using upokD(1) by (fastforce simp: G vars_apps)
    then have "tvars U \<subseteq> vtvars (X \<union> evars en)" by (rule tvars_vtvars)
    moreover have "vtvars (X \<union> evars en) \<subseteq> tvars_env (tyenv en) \<union> A"
      using i0(5) vtvars_evars[OF i0(4)] by simp
    ultimately show ?thesis using tvinv_tbelow[OF i0(4)] by blast
  qed
  have "mcc_dres A0 envM VM F A K X en ?GV' \<rho>' \<sigma>' y"
  proof (rule mcc_dresI[OF y cf])
    show "A \<subseteq> Af" "K \<subseteq> Kf" "X \<subseteq> Xf" using AK1 AK2 by auto
    show "scinv \<rho>f \<sigma>f ef (F @ df) Xf Af" by (fact invf)
    show "extends en ef" by (rule extends_trans[OF ext1 ext2])
    show "tagree (maxidx en) \<rho>' \<rho>f" by (rule tagree_trans[OF ag1(1) ag3(1) mx1])
    show "sagree (maxidx en) \<sigma>' \<sigma>f" by (rule sagree_trans[OF ag1(2) ag3(2) mx1])
    show "finite (NV1 \<union> NV2)" using NV1(1) NV2(1) by simp
    show "NV1 \<union> NV2 \<subseteq> Xf" using NV1(2) NV2(2) AK2(3) by auto
    show "\<forall>y\<in>NV1 \<union> NV2. maxidx en < snd (fst y) \<or> y \<in> ?GV'" using NV1(3) NV2(3) mx1 GV' by fastforce
    have "fst (x, U) \<notin> fst ` NV1"
    proof
      assume "fst (x, U) \<in> fst ` NV1"
      then obtain y where y: "y \<in> NV1" "fst y = x" by auto
      with NV1(3) have "maxidx en < snd x \<or> y \<in> ?GV" by auto
      then show False
      proof
        assume "maxidx en < snd x"
        then show False using xn Cons.prems(5) by simp
      next
        assume "y \<in> ?GV"
        then show False using y(2) xGs by force
      qed
    qed
    moreover have fGV': "fst ` ?GV' = insert x (fst ` ?GV)" using GV' by simp
    moreover have ub2': "ubv ef Xf \<subseteq> (ubv e1 X1 - {x}) \<union> fst ` NV2" using ub2 by simp
    ultimately show "ubv ef Xf \<subseteq> (ubv en X - fst ` ?GV') \<union> fst ` (NV1 \<union> NV2)"
      unfolding image_Un using ub1 by blast
    show "(\<Sum>y\<in>NV1 \<union> NV2. mcp_vsz \<rho>f \<sigma>f y) \<le> (\<Sum>y\<in>?GV'. mcp_vsz \<rho>' \<sigma>' y)"
    proof -
      have "(\<Sum>y\<in>NV1 \<union> NV2. mcp_vsz \<rho>f \<sigma>f y) + (\<Sum>y\<in>NV1 \<inter> NV2. mcp_vsz \<rho>f \<sigma>f y) =
          (\<Sum>y\<in>NV1. mcp_vsz \<rho>f \<sigma>f y) + (\<Sum>y\<in>NV2. mcp_vsz \<rho>f \<sigma>f y)"
        by (rule sum.union_inter) (use NV1(1) NV2(1) in auto)
      then have "(\<Sum>y\<in>NV1 \<union> NV2. mcp_vsz \<rho>f \<sigma>f y) \<le> (\<Sum>y\<in>NV1. mcp_vsz \<rho>f \<sigma>f y) + (\<Sum>y\<in>NV2. mcp_vsz \<rho>f \<sigma>f y)"
        by linarith
      also have "(\<Sum>y\<in>NV1. mcp_vsz \<rho>f \<sigma>f y) = (\<Sum>y\<in>NV1. mcp_vsz \<rho>1 \<sigma>1 y)"
        by (rule sum.cong[OF refl vsz1]) (use NV1(2) in blast)
      also have "mcp_vsz \<rho>1 \<sigma>1 (x, U) = mcp_vsz \<rho>' \<sigma>' (x, U)"
        by (rule mcp_vsz_agree[OF ag1]) (use xn Cons.prems(5) below0 in simp_all)
      ultimately show ?thesis using sz1 sz2 GV' xU by (simp add: sum.insert[OF finite_set])
    qed
    show "\<forall>k. mcp_kokK k \<rho>' (tyenv en) A K \<longrightarrow> mcp_kokK k \<rho>f (tyenv ef) Af Kf" using kk1 kk2 by blast
  qed
  with ev show ?case by blast
qed

subsection \<open>Copies: imitations\<close>

text \<open>The head of a target of a rigid term that is not a projection is the head of the term:\<close>

lemma mcc_target_rigid:
  assumes sp: "mcc_spre \<rho> \<sigma> env dps X A e rb (v, TX) targs Ss u UU s"
    and P: "(rb, Var v TX \<degree>\<degree> targs, u) \<in> set dps"
    and r: "rigid (fst (strip_comb u))" and sh: "s = h' \<degree>\<degree> bs" "atom h'" "closed h'"
  shows "h' = inst \<rho> (fst (strip_comb u))"
    "list_all2 (\<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta>) (map (mcp_cpy (map (ap \<rho> \<sigma>) targs)) bs) (map (ap \<rho> \<sigma>) (snd (strip_comb u)))"
proof -
  note sp' = mcc_spreD[OF sp] and cS = mcc_cS[OF sp]
  note sd = solutionD[OF scinvD(1)[OF sp'(1)]]
  let ?ts = "map (ap \<rho> \<sigma>) targs"
  have tapt: "e \<tturnstile> ?ts : Ss"
    using sp'(3) by (induction targs arbitrary: Ss) (auto split: list.splits intro: typing_ap[OF _ sd(3)])
  have tcs: "e \<turnstile> types_abs Ss s \<degree>\<degree> ?ts : UU" by (rule list_app_typeI[OF mcp_typing_val[OF sp'(8,10) cS(1)] tapt])
  have lSs: "length Ss = length ?ts" using typings_nth[OF tapt] by simp
  note cc = mcp_conv_cpy[OF tcs lSs]
  have cps: "mcp_cpy ?ts s = h' \<degree>\<degree> map (mcp_cpy ?ts) bs" by (simp add: sh(1) mcp_cpy_apps mcp_cpy_closed[OF sh(3)])
  have u: "u = fst (strip_comb u) \<degree>\<degree> snd (strip_comb u)" by (rule strip_comb_apps) simp
  have apu: "ap \<rho> \<sigma> u = inst \<rho> (fst (strip_comb u)) \<degree>\<degree> map (ap \<rho> \<sigma>) (snd (strip_comb u))"
    by (subst u) (simp add: ap_apps rigid_ap[OF r])
  have "h' \<degree>\<degree> map (mcp_cpy ?ts) bs \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> inst \<rho> (fst (strip_comb u)) \<degree>\<degree> map (ap \<rho> \<sigma>) (snd (strip_comb u))"
    using conv_trans[OF conv_sym[OF cc(1)] mcc_spre_cv[OF sp P]] cps apu by simp
  moreover have "wt (h' \<degree>\<degree> map (mcp_cpy ?ts) bs)" using cc(2) cps by (auto simp: wt_def)
  ultimately show "h' = inst \<rho> (fst (strip_comb u))"
    "list_all2 (\<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta>) (map (mcp_cpy ?ts) bs) (map (ap \<rho> \<sigma>) (snd (strip_comb u)))"
    using conv_atom_apps_inv[OF sh(2) rigid_inst[OF r]] by blast+
qed

text \<open>
  An imitation for a target with the head of the rigid side: the variable is bound to the head
  applied to new variables, whose values are the arguments of the target, and the arguments are
  copied into them. The completeness of the copies of \<^const>\<open>mc\<close> for the arguments of the target
  is a hypothesis.
\<close>

lemma mcc_imit:
  assumes cfg: "cfg_alg cfg = alg" and M: "menv envM VM"
    and pre: "mcpre A0 envM VM F A K X env rb (v, TX) targs u dps ot" and vN: "vt_lookup (tenv env) v = None"
    and ty0: "fastype env rb (fst (strip_comb u)) = return T0" "body_type env T0 = return base"
      "mapM (fastype env rb) targs = return Ts"
    and sp: "mcc_spre \<rho> \<sigma> env (F @ (rb, Var v TX \<degree>\<degree> targs, u) # dps) X A e rb (v, TX) targs Ss u UU s"
    and kk: "mcp_kokK (nat_of_integer (cfg_arity_bound cfg)) \<rho> (tyenv env) A K"
    and h: "fst (strip_comb u) = Const c C \<or> fst (strip_comb u) = Free c C"
    and sh: "s = inst \<rho> (fst (strip_comb u)) \<degree>\<degree> bs"
    and IH: "\<And>i F' A' K' X' en d' x0 U0 u' \<rho>' \<sigma>' B. i < length bs \<Longrightarrow>
      mcpre A0 envM VM F' A' K' X' en rb (x0, U0) targs u' d' None \<Longrightarrow>
      mcc_spre \<rho>' \<sigma>' en (F' @ (rb, Var x0 U0 \<degree>\<degree> targs, u') # d') X' A' e rb (x0, U0) targs Ss u' B (bs ! i) \<Longrightarrow>
      mcp_kokK (nat_of_integer (cfg_arity_bound cfg)) \<rho>' (tyenv en) A' K' \<Longrightarrow>
      \<exists>sq. okW (mc cfg vname envM (x0, U0) rb targs u' en d') sq \<and>
        (\<exists>y. ev cfg sq y \<and> (\<exists>m. mcc_res A0 envM VM F' A' K' X' en (x0, U0) \<rho>' \<sigma>' m y))"
  shows "\<exists>sq. okW (imitate vname envM rb targs env dps (v, TX) Ts (fst (strip_comb u)) (snd (strip_comb u))) sq \<and>
    (\<exists>y. ev cfg sq y \<and> mcc_res A0 envM VM F A K X env (v, TX) \<rho> \<sigma> 1 y)"
proof -
  let ?P = "(rb, Var v TX \<degree>\<degree> targs, u)"
  obtain uh uas where suh: "strip_comb u = (uh, uas)" by fastforce
  have fuh: "fst (strip_comb u) = uh" and suas: "snd (strip_comb u) = uas" using suh by simp_all
  have u2: "u = uh \<degree>\<degree> uas" by (rule strip_comb_apps[OF suh])
  note h = h[unfolded fuh] and sh = sh[unfolded fuh]
  note sp' = mcc_spreD[OF sp] and cS = mcc_cS[OF sp]
  note inv = sp'(1) and bs = sp'(2) and tyt = sp'(3) and tyu = sp'(4) and tys = sp'(8)
    and nrs = sp'(9) and lbs = sp'(10)
  note i = scinvD[OF inv] and sd = solutionD[OF scinvD(1)[OF inv]]
  note mp = mcs_pre[OF pre vN ty0] and mf = mcs_facts[OF pre vN ty0]
  have c0: "cpinvX A0 envM VM F A K X env (?P # dps)" by (rule mcpre_cpinvX[OF pre, simplified])
  have ps: "\<forall>(rb', t', u')\<in>set (F @ ?P # dps). upok A env rb' X t' u'" using mp(9) by (simp add: sinv_def)
  have ei: "einv A K env" using mp(9) by (simp add: sinv_def)
  let ?KN = "tvars_env (tyenv env) \<union> A"
  have below_KN: "tbelow (maxidx env) S" if "S \<subseteq> ?KN" for S using tvinv_tbelow[OF i(4) that] .
  have hr: "rigid uh" using h by auto
  have Tsok: "ok (mapM (fastype env rb) targs) Ts" by (fact mf(9))
  have SsT: "map (tsubst \<rho>) Ts = Ss" by (rule mapM_fastype_sound(2)[OF Tsok sd(2) bs tyt])
  have P: "?P \<in> set (F @ ?P # dps)" by simp
  have ch: "closed (inst \<rho> uh)" "atom (inst \<rho> uh)" using h by (auto simp: closed_def)
  note tr = mcc_target_rigid[OF sp P hr[folded fuh] sh[folded fuh] ch(2,1)[folded fuh], unfolded fuh suas]
  \<comment> \<open>The types of the arguments:\<close>
  from tys[unfolded sh] obtain Bts where tyh: "pushes mcp_e0 Ss \<turnstile> inst \<rho> uh : Bts \<Rrightarrow> UU"
    and tybs: "pushes mcp_e0 Ss \<tturnstile> bs : Bts" by (rule list_app_typeE)
  from tyu[unfolded u2[THEN arg_cong[of _ _ "inst \<rho>"]] inst_apps] obtain Vs where tyh': "e \<turnstile> inst \<rho> uh : Vs \<Rrightarrow> UU"
    and tyas: "e \<tturnstile> map (inst \<rho>) uas : Vs" by (rule list_app_typeE)
  have lbB: "length bs = length Bts" using typings_nth[OF tybs] by simp
  have lbu: "length bs = length uas" using list_all2_lengthD[OF tr(2)] by simp
  have luV: "length uas = length Vs" using typings_nth[OF tyas] by simp
  have "Bts \<Rrightarrow> UU = Vs \<Rrightarrow> UU" using tyh tyh' h by auto
  then have BV: "Bts = Vs" using funs_eq[of Bts Vs UU UU] lbB lbu luV by simp
  obtain Us where Usr: "mapM (fastype env rb) uas = return Us"
    and tvUs: "\<forall>U\<in>set Us. tvars U \<subseteq> ?KN" by (rule mcs_Us[OF pre vN ty0 u2])
  have Usok: "ok (mapM (fastype env rb) uas) Us" using Usr by (simp add: return_def)
  have UsB: "map (tsubst \<rho>) Us = Bts" using mapM_fastype_sound(2)[OF Usok sd(2) bs tyas] BV by simp
  have lba: "\<forall>a\<in>set uas. \<not> loose_bvar a (ilength rb)"
    using upokD(8)[OF mcs_inv(3)[OF pre vN ty0]] u2 by (metis loose_bvar_apps)
  have cB: "\<forall>B\<in>set Bts. cert_typ alg ar B"
  proof
    fix B assume "B \<in> set Bts"
    then obtain l where l: "l < length Bts" "B = Bts ! l" by (auto simp: in_set_conv_nth)
    have "e \<turnstile> inst \<rho> (uas ! l) : B" using typings_nth[OF tyas] l BV by auto
    then show "cert_typ alg ar B" by (rule bs_env_cert[OF bs]) (use lba l lbB lbu in auto)
  qed
  \<comment> \<open>The binding:\<close>
  obtain env' args where ma: "make_args vname Ts env Us = (env', args)" by fastforce
  have te': "tenv env' = tenv env" by (rule make_args_props_idx[OF ma]) blast
  have vN1: "vt_lookup (tenv env') v = None" using vN te' by simp
  obtain env'' where up: "ok (update (v, TX) (types_abs Ts (list_comb uh args)) env') env''"
    using update_unbound[OF vN1] by blast
  note ms = mcs_imit[OF pre vN ty0 u2 h Usok tvUs ma up]
  let ?gus = "zip (map head_of args) uas"
  let ?ps = "map (\<lambda>(G, uarg). (rb, G \<degree>\<degree> targs, uarg)) ?gus"
  let ?X2 = "X \<union> dvars (F @ ?ps @ dps)"
  have \<sigma>v: "\<sigma> v (tsubst \<rho> TX) \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> types_abs Ss s" using sp'(6,11) by simp
  obtain Gs \<sigma>3 where args: "args = map (\<lambda>G. G \<degree>\<degree> bvs (length Ts)) Gs"
    and GU: "list_all2 (\<lambda>G U. \<exists>x. G = Var x (Ts \<Rrightarrow> U)) Gs Us"
    and Gi: "\<forall>G\<in>set Gs. \<exists>a U. G = Var (a, maxidx env + 1) U" and lqb: "length Gs = length bs"
    and sa3: "sagree (maxidx env) \<sigma> \<sigma>3" and wt3: "wt_subst \<sigma>3" and sol3: "solution \<rho> \<sigma>3 env''"
    and apGl: "\<And>l. l < length Gs \<Longrightarrow> ap \<rho> \<sigma>3 (Gs ! l) = types_abs Ss (bs ! l)"
    and vszl: "\<And>l. l < length Gs \<Longrightarrow> mcp_vsz \<rho> \<sigma>3 (var_of (Gs ! l), Ts \<Rrightarrow> (Us ! l)) \<le> lsz (pushes mcp_e0 Ss) (bs ! l)"
    and msum3: "(\<Sum>y\<in>lvars Gs. mcp_vsz \<rho> \<sigma>3 y) + 1 \<le> lsz (pushes mcp_e0 Ss) s"
    by (rule mcc_args[OF i(1) i(3) ma up mf(2) SsT UsB cS(1) cB sh tyh tybs hr tys nrs lbs \<sigma>v]) blast
  have hd: "map head_of args = Gs" using Gi by (auto simp: args head_of_apps intro!: map_idI)
  have lGs: "length Gs = length uas" using lqb lbu by simp
  \<comment> \<open>The pairs of the arguments are solved:\<close>
  let ?ts = "map (ap \<rho> \<sigma>) targs"
  have vb: "below (maxidx env) (vars t)" if "vars t \<subseteq> X \<union> evars env" for t
    using i(3) that unfolding vinv_def by (meson below_mono order_refl)
  have tvt: "(\<Union>t\<in>set targs. ttvars t) \<subseteq> ?KN" "ttvars u \<subseteq> ?KN"
    using upokD(3,4)[OF mcs_inv(3)[OF pre vN ty0]] by (auto simp: ttvars_apps)
  have apt: "ap \<rho> \<sigma>3 t = ap \<rho> \<sigma> t" if "t \<in> set targs" for t
    by (rule ap_sagree[OF sa3 vb]) (use mf(4) that in blast)
  have apa: "ap \<rho> \<sigma>3 a = ap \<rho> \<sigma> a" if "a \<in> set uas" for a
  proof (rule ap_sagree[OF sa3 vb])
    show "vars a \<subseteq> X \<union> evars env" using mf(3) that u2 by (auto simp: vars_apps)
  qed
  have tapt: "e \<tturnstile> ?ts : Ss"
    using tyt by (induction targs arbitrary: Ss) (auto split: list.splits intro: typing_ap[OF _ sd(3)])
  have lSs': "length Ss = length ?ts" using typings_nth[OF tapt] by simp
  have lbs_arg: "\<forall>b\<in>set bs. \<not> loose_bvar b (ilength Ss)" using lbs sh by (simp add: loose_bvar_apps)
  have dsl: "ap \<rho> \<sigma>3 ((Gs ! l) \<degree>\<degree> targs) \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma>3 (uas ! l)" if l: "l < length Gs" for l
  proof -
    have "ap \<rho> \<sigma>3 ((Gs ! l) \<degree>\<degree> targs) = types_abs Ss (bs ! l) \<degree>\<degree> ?ts"
      using apGl[OF l] apt by (simp add: ap_apps cong: map_cong)
    also have "\<dots> \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> mcp_cpy ?ts (bs ! l)"
    proof -
      have "pushes mcp_e0 Ss \<turnstile> bs ! l : Bts ! l" using typings_nth[OF tybs] l lqb by simp
      from list_app_typeI[OF mcp_typing_val[OF this] tapt] lbs_arg cS(1) l lqb
      have "e \<turnstile> types_abs Ss (bs ! l) \<degree>\<degree> ?ts : Bts ! l" by simp
      then show ?thesis using mcp_conv_cpy(1) lSs' by blast
    qed
    also have "\<dots> \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma> (uas ! l)" using list_all2_nthD[OF tr(2), of l] l lqb lbu by simp
    also have "\<dots> = ap \<rho> \<sigma>3 (uas ! l)" using apa[of "uas ! l"] l lGs by simp
    finally show ?thesis .
  qed
  have ds: "dsolved \<rho> \<sigma>3 (F @ ?ps @ dps)"
  proof -
    have "dsolved \<rho> \<sigma>3 (F @ ?P # dps)" by (rule sc_dps_agree(2)[OF ps i(4) i(3) tagree_refl sa3 i(7)])
    moreover have "dsolved \<rho> \<sigma>3 ?ps"
      unfolding dsolved_def hd
    proof (clarsimp)
      fix G a assume "(G, a) \<in> set (zip Gs uas)"
      then obtain l where "l < length Gs" "G = Gs ! l" "a = uas ! l" using lGs by (auto simp: set_zip)
      with dsl show "ap \<rho> \<sigma>3 (G \<degree>\<degree> targs) \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma>3 a" by simp
    qed
    ultimately show ?thesis unfolding dsolved_def set_append ball_Un by simp
  qed
  have inv3: "scinv \<rho> \<sigma>3 env'' (F @ ?ps @ dps) ?X2 A"
    by (rule mcc_scinv_cpinvX[OF inv c0 ms(1) sol3 tagree_refl sa3 ds ms(4)])
  \<comment> \<open>The copies of the arguments:\<close>
  note i3 = scinvD[OF inv3]
  have c3: "cpinvX A0 envM VM F A K ?X2 env'' (?ps @ dps)" by (rule ms(4))
  have ext'': "extends env env''" by (rule ms(3))
  have mx: "maxidx env \<le> maxidx env''" by (rule extends_maxidx[OF ext''])
  have GsX: "lvars Gs \<subseteq> ?X2"
  proof
    fix y assume "y \<in> lvars Gs"
    then obtain l where l: "l < length Gs" "y \<in> vars (Gs ! l)" by (auto simp: in_set_conv_nth)
    have "(rb, (Gs ! l) \<degree>\<degree> targs, uas ! l) \<in> set ?ps"
      using l(1) lGs by (auto simp: hd set_zip intro!: image_eqI[where x = "(Gs ! l, uas ! l)"])
    then show "y \<in> ?X2" using l(2) by (force simp: vars_apps dvars_def)
  qed
  have Gb: "snd (fst y) \<le> maxidx env''" if "y \<in> lvars Gs" for y
  proof -
    have "y \<in> ?X2" using GsX that by (rule subsetD)
    moreover have "below (maxidx env'') (?X2 \<union> evars env'')" using i3(3) by (simp add: vinv_def)
    ultimately show ?thesis unfolding below_def by blast
  qed
  have GVar: "\<exists>x. Gs ! l = Var x (Ts \<Rrightarrow> (Us ! l))" if "l < length Gs" for l
    using list_all2_nthD[OF GU that] by simp
  have Gv: "\<forall>(G, uarg)\<in>set ?gus. \<exists>x U. G = Var x U \<and> snd x \<le> maxidx env''"
  proof (clarify)
    fix G a assume "(G, a) \<in> set ?gus"
    then obtain l where l: "l < length Gs" "G = Gs ! l" using lGs by (auto simp: hd set_zip)
    from GVar[OF l(1)] obtain x where "Gs ! l = Var x (Ts \<Rrightarrow> (Us ! l))" ..
    with l(2) have G: "G = Var x (Ts \<Rrightarrow> (Us ! l))" by simp
    have "G \<in> set Gs" using nth_mem[OF l(1)] l(2) by simp
    then have "(x, Ts \<Rrightarrow> (Us ! l)) \<in> lvars Gs" by (rule UN_I) (simp add: G)
    from Gb[OF this] show "\<exists>x U. G = Var x U \<and> snd x \<le> maxidx env''" using G by auto
  qed
  have dist: "distinct (map (fst \<circ> mcc_vt \<circ> fst) ?gus)"
  proof -
    have d0: "distinct (map var_of Gs)" by (rule mcp_make_args_distinct[OF ma args])
    have "map (fst \<circ> mcc_vt \<circ> fst) ?gus = map var_of Gs"
    proof (rule nth_equalityI)
      show "length (map (fst \<circ> mcc_vt \<circ> fst) ?gus) = length (map var_of Gs)" using lGs by (simp add: hd)
      fix l assume "l < length (map (fst \<circ> mcc_vt \<circ> fst) ?gus)"
      then have l: "l < length Gs" using lGs by (simp add: hd)
      from GVar[OF l] obtain x where "Gs ! l = Var x (Ts \<Rrightarrow> (Us ! l))" ..
      then show "map (fst \<circ> mcc_vt \<circ> fst) ?gus ! l = map var_of Gs ! l" using l lGs by (simp add: hd)
    qed
    with d0 show ?thesis by simp
  qed
  have GV: "set (map (mcc_vt \<circ> fst) ?gus) = lvars Gs"
  proof -
    have mfst: "map fst ?gus = Gs" using lGs by (simp add: hd)
    have "set (map (mcc_vt \<circ> fst) ?gus) = mcc_vt ` set Gs" by (metis mfst set_map map_map)
    moreover have vG: "vars G = {mcc_vt G}" if "G \<in> set Gs" for G using that Gi by auto
    then have "lvars Gs = mcc_vt ` set Gs" by (auto simp: vG)
    ultimately show ?thesis by simp
  qed
  have tvU: "tbelow (maxidx env) (tvars (Ts \<Rrightarrow> (Us ! l)))" if "l < length Us" for l
    by (rule below_KN) (use mf(12) tvUs that in \<open>auto simp: tvars_funs\<close>)
  have CC: "\<exists>cs. okW (copycons cfg vname envM rb targs G uarg en d') cs \<and>
        (\<exists>y. ev cfg cs y \<and> mcc_res A0 envM VM F' A' K' X' en (mcc_vt G) \<rho>' \<sigma>' 0 y)"
    if gu: "(G, uarg) \<in> set ?gus" and c': "cpinvX A0 envM VM F' A' K' X' en ((rb, G \<degree>\<degree> targs, uarg) # d')"
      and inv': "scinv \<rho>' \<sigma>' en (F' @ (rb, G \<degree>\<degree> targs, uarg) # d') X' A'"
      and ag': "tagree (maxidx env'') \<rho> \<rho>'" "sagree (maxidx env'') \<sigma>3 \<sigma>'"
      and mxe: "maxidx env'' \<le> maxidx en"
      and kk': "mcp_kokK (nat_of_integer (cfg_arity_bound cfg)) \<rho>' (tyenv en) A' K'"
    for F' A' K' X' en d' G uarg \<rho>' \<sigma>'
  proof -
    from gu obtain l where l: "l < length Gs" "G = Gs ! l" "uarg = uas ! l" using lGs by (auto simp: hd set_zip)
    from GVar[OF l(1)] obtain x where "Gs ! l = Var x (Ts \<Rrightarrow> (Us ! l))" ..
    with l(2) have G: "G = Var x (Ts \<Rrightarrow> (Us ! l))" by simp
    let ?U = "Ts \<Rrightarrow> (Us ! l)"
    have lUs: "l < length Us" using l(1) list_all2_lengthD[OF GU] by simp
    have lb: "l < length bs" using l(1) lqb by simp
    have ag0: "tagree (maxidx env) \<rho> \<rho>'" by (rule tagree_trans[OF tagree_refl ag'(1) mx])
    have ua: "uarg \<in> set uas" using l(1,3) lGs by simp
    have vu: "vars uarg \<subseteq> VM" using mp(10) ua u2 by (auto simp: vars_apps)
    have bs': "bs_env \<rho>' e rb" by (rule bs_env_agree[OF bs ag0 below_KN]) (use upokD(5)[OF mcs_inv(3)[OF pre vN ty0]] in blast)
    have it: "inst \<rho>' t = inst \<rho> t" if "ttvars t \<subseteq> ?KN" for t by (rule inst_agree[OF ag0 below_KN[OF that]])
    have tyt': "e \<tturnstile> map (inst \<rho>') targs : Ss"
    proof -
      have meq: "map (inst \<rho>') targs = map (inst \<rho>) targs"
      proof (rule map_cong[OF refl])
        fix t assume "t \<in> set targs"
        then have "ttvars t \<subseteq> ?KN" using tvt(1) by blast
        then show "inst \<rho>' t = inst \<rho> t" by (rule it)
      qed
      show ?thesis unfolding meq by (rule tyt)
    qed
    have tya': "e \<turnstile> inst \<rho>' uarg : Bts ! l"
    proof -
      have "ttvars uarg \<subseteq> ?KN" using tvt(2) ua u2 by (auto simp: ttvars_apps)
      then have "inst \<rho>' uarg = inst \<rho> uarg" by (rule it)
      moreover have "e \<turnstile> inst \<rho> uarg : Bts ! l" using typings_nth[OF tyas] l(1,3) lGs BV by auto
      ultimately show ?thesis by simp
    qed
    have TU': "tsubst \<rho>' ?U = Ss \<Rrightarrow> (Bts ! l)"
    proof -
      have "tsubst \<rho>' ?U = tsubst \<rho> ?U" by (rule tsubst_agree[OF ag0 tvU[OF lUs]])
      then show ?thesis using SsT UsB lUs by (simp add: tsubst_funs flip: nth_map[of l Us "tsubst \<rho>"])
    qed
    have cSB: "cert_typ alg ar (Ss \<Rrightarrow> (Bts ! l))" using cS(1) cB lb lbB by (simp add: cert_typ_funs)
    have tyb: "pushes mcp_e0 Ss \<turnstile> bs ! l : Bts ! l" using typings_nth[OF tybs] lb by simp
    have nrb: "no_redex (bs ! l)"
      using nrs sh no_redex_apps[of "inst \<rho> uh" bs] h lb by (cases "inst \<rho> uh") auto
    have lbb: "\<not> loose_bvar (bs ! l) (ilength Ss)" using lbs_arg lb by simp
    have \<sigma>x: "\<sigma>' x (Ss \<Rrightarrow> (Bts ! l)) \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> types_abs Ss (bs ! l)"
    proof -
      have "G \<in> set Gs" using nth_mem[OF l(1)] l(2) by simp
      then have "(x, ?U) \<in> lvars Gs" by (rule UN_I) (simp add: G)
      from Gb[OF this] have "snd x \<le> maxidx env''" by simp
      then have "\<sigma>' x (Ss \<Rrightarrow> (Bts ! l)) = \<sigma>3 x (Ss \<Rrightarrow> (Bts ! l))" using ag'(2) unfolding sagree_def by blast
      also have "\<dots> = types_abs Ss (bs ! l)"
        using apGl[OF l(1)] G l(2) TU' tsubst_agree[OF ag0 tvU[OF lUs]] by simp
      finally show ?thesis by (simp add: conv_refl)
    qed
    have "\<exists>cs. okW (copycons cfg vname envM rb targs G uarg en d') cs \<and>
        (\<exists>y. ev cfg cs y \<and> mcc_res A0 envM VM F' A' K' X' en (x, ?U) \<rho>' \<sigma>' 0 y)"
    proof (rule mcc_copycons[OF cfg M c' vu G inv' kk' bs' tyt' tya' TU' cSB tyb nrb lbb \<sigma>x])
      fix A'' K'' X'' u' \<sigma>''
      assume "mcpre A0 envM VM F' A'' K'' X'' en rb (x, ?U) targs u' d' None"
        "mcc_spre \<rho>' \<sigma>'' en (F' @ (rb, Var x ?U \<degree>\<degree> targs, u') # d') X'' A'' e rb (x, ?U) targs Ss u' (Bts ! l) (bs ! l)"
        "mcp_kokK (nat_of_integer (cfg_arity_bound cfg)) \<rho>' (tyenv en) A'' K''"
      from IH[OF lb this] show "\<exists>sq. okW (mc cfg vname envM (x, ?U) rb targs u' en d') sq \<and>
          (\<exists>y. ev cfg sq y \<and> (\<exists>m. mcc_res A0 envM VM F' A'' K'' X'' en (x, ?U) \<rho>' \<sigma>'' m y))" by simp
    qed
    then show ?thesis using G by simp
  qed
  have kk3: "mcp_kokK (nat_of_integer (cfg_arity_bound cfg)) \<rho> (tyenv env'') A K" using kk ms(2) by simp
  from mcc_copyargs[where \<rho> = \<rho> and \<sigma> = \<sigma>3 and n = "maxidx env''", OF CC Gv dist c3 inv3 tagree_refl sagree_refl
      order_refl kk3]
  obtain y where evy: "ev cfg (copyargs vname envM rb targs ?gus env'' dps) y"
    and r: "mcc_dres A0 envM VM F A K ?X2 env'' (lvars Gs) \<rho> \<sigma>3 y"
    unfolding GV by blast
  have vT: "(v, TX) \<in> X \<union> evars env"
    using upokD(1)[OF mcs_inv(3)[OF pre vN ty0]] by (auto simp: vars_apps)
  have ub2: "ubv env'' ?X2 \<subseteq> (ubv env X - {v}) \<union> fst ` lvars Gs"
  proof (rule mcc_ubv_bind[OF up te'])
    show "v \<in> fst ` (?X2 \<union> evars env)" using vT by force
    have "dvars (F @ ?ps @ dps) \<subseteq> lvars Gs \<union> (X \<union> evars env)"
    proof -
      have "dvars ?ps \<subseteq> lvars Gs \<union> (X \<union> evars env)"
      proof
        fix y assume "y \<in> dvars ?ps"
        then obtain G a where "(G, a) \<in> set ?gus" "y \<in> vars (G \<degree>\<degree> targs) \<union> vars a" by (auto simp: dvars_def)
        moreover from this(1) have "G \<in> set Gs" "a \<in> set uas" by (auto simp: hd dest: set_zip_leftD set_zip_rightD)
        ultimately show "y \<in> lvars Gs \<union> (X \<union> evars env)" using mf(3,4) u2 by (auto simp: vars_apps)
      qed
      then show ?thesis using mf(7) by auto
    qed
    then show "fst ` (?X2 \<union> evars env) \<subseteq> fst ` (X \<union> evars env) \<union> fst ` lvars Gs" by blast
    show "fst ` vars (types_abs Ts (list_comb uh args)) \<subseteq> fst ` lvars Gs"
      using h by (auto simp: args list_comb_apps vars_apps)
  qed
  have ar0: "arity UU = 0"
  proof -
    have "\<not> is_Abs u" using h unfolding u2 is_Abs_apps by auto
    then show ?thesis using sp'(5) by simp
  qed
  have "mcc_res A0 envM VM F A K X env (v, TX) \<rho> \<sigma> 1 y"
    using r
  proof (rule mcc_dresE)
    fix ef df Af Kf Xf \<rho>f \<sigma>f NV
    assume a: "y = El_E ef df" "cpinvX A0 envM VM F Af Kf Xf ef df"
      "A \<subseteq> Af" "K \<subseteq> Kf" "?X2 \<subseteq> Xf" "scinv \<rho>f \<sigma>f ef (F @ df) Xf Af" "extends env'' ef"
      "tagree (maxidx env'') \<rho> \<rho>f" "sagree (maxidx env'') \<sigma>3 \<sigma>f"
      "finite NV" "NV \<subseteq> Xf" "\<forall>y\<in>NV. maxidx env'' < snd (fst y) \<or> y \<in> lvars Gs"
      "ubv ef Xf \<subseteq> (ubv env'' ?X2 - fst ` lvars Gs) \<union> fst ` NV"
      "(\<Sum>y\<in>NV. mcp_vsz \<rho>f \<sigma>f y) \<le> (\<Sum>y\<in>lvars Gs. mcp_vsz \<rho> \<sigma>3 y)"
      "\<forall>k. mcp_kokK k \<rho> (tyenv env'') A K \<longrightarrow> mcp_kokK k \<rho>f (tyenv ef) Af Kf"
    show ?thesis
    proof (rule mcc_resI[OF a(1,2,3,4) _ a(6) extends_trans[OF ext'' a(7)] _ _ a(10,11)])
      show "X \<subseteq> Xf" using a(5) by blast
      show "tagree (maxidx env) \<rho> \<rho>f" by (rule tagree_trans[OF tagree_refl a(8) mx])
      show "sagree (maxidx env) \<sigma> \<sigma>f" by (rule sagree_trans[OF sa3 a(9) mx])
      show "\<forall>y\<in>NV. maxidx env < snd (fst y) \<or> y = (v, TX)" using a(12) mx Gi by fastforce
      show "ubv ef Xf \<subseteq> (ubv env X - {fst (v, TX)}) \<union> fst ` NV" using a(13) ub2 by auto
      have "mcp_vsz \<rho> \<sigma> (v, TX) = lsz (pushes mcp_e0 Ss) s" using mcc_vsz[OF sp] ar0 by simp
      then show "(\<Sum>y\<in>NV. mcp_vsz \<rho>f \<sigma>f y) + 1 \<le> mcp_vsz \<rho> \<sigma> (v, TX)" using a(14) msum3 by simp
      show "\<forall>k. mcp_kokK k \<rho> (tyenv env) A K \<longrightarrow> mcp_kokK k \<rho>f (tyenv ef) Af Kf" using a(15) ms(2) by simp
    qed
  qed
  moreover have "okW (imitate vname envM rb targs env dps (v, TX) Ts uh uas)
      (copyargs vname envM rb targs ?gus env'' dps)"
  proof -
    have up': "update (v, TX) (types_abs Ts (list_comb uh args)) env' = return env''"
      using up by (simp add: return_def)
    show ?thesis by (simp add: imitate_def Usr ma up' liftM_def return_def bindW_def returnW_def)
  qed
  ultimately show ?thesis unfolding fuh suas using evy by blast
qed

subsection \<open>The sequence of \<^const>\<open>matchfun\<close>\<close>

text \<open>The result of a projection on \<open>targ\<close> with the guess \<open>p\<close> is an element of the sequence \<open>s\<close>:\<close>

definition mcc_projel where
  "mcc_projel cfg vname env Ts Us bary base targs rb u dps X bvar targ p s \<longleftrightarrow>
    (\<forall>env0 Cs env' env1 args env2 env3 fr ff. gentvars p env = (env0, Cs) \<longrightarrow>
      okW (proj_unify cfg base bary Cs env0) env' \<longrightarrow> make_args vname Ts env' (Us @ Cs) = (env1, args) \<longrightarrow>
      ok (update X (types_abs Ts (list_comb bvar args)) env1) env2 \<longrightarrow>
      okW (SIMPL (cfg_alg cfg) env2 ((rb, list_comb targ (map (\<lambda>arg. list_comb (head_of arg) targs) args), u) # dps))
        (env3, fr, ff) \<longrightarrow>
      ev cfg s (El_E env3 (fr @ ff)))"

lemma mcc_projel_mono:
  "mcc_projel cfg vname env Ts Us bary base targs rb u dps X bvar targ p s \<Longrightarrow> (\<And>x. ev cfg s x \<Longrightarrow> ev cfg s' x) \<Longrightarrow>
    mcc_projel cfg vname env Ts Us bary base targs rb u dps X bvar targ p s'"
  unfolding mcc_projel_def by blast

lemma projenv_ev:
  assumes s: "okW (projenv cfg vname rb targs u env dps X base Ts bvar (Us, bary) targ p tail) s"
  shows "ev cfg tail x \<Longrightarrow> ev cfg s x" "mcc_projel cfg vname env Ts Us bary base targs rb u dps X bvar targ p s"
proof -
  obtain e0 C0 where g: "gentvars p env = (e0, C0)" by fastforce
  let ?f = "\<lambda>env'. returnW (S_Proj vname env' Ts (Us @ C0) targs rb u dps bvar targ X tail)"
  let ?m = "bindW (proj_unify cfg base bary C0 e0) ?f"
  have c: "(\<exists>env'. okW (proj_unify cfg base bary C0 e0) env' \<and>
      s = S_Proj vname env' Ts (Us @ C0) targs rb u dps bvar targ X tail) \<or>
      ((\<exists>evs e. ?m = Some (evs, UErr e)) \<and> s = tail)"
    using s unfolding projenv_def g prod.case okW_handleW
    by (auto split: uexn.splits) (metis uexn.exhaust)+
  show "ev cfg tail x \<Longrightarrow> ev cfg s x" using c by (auto intro: ev.proj_tail)
  show "mcc_projel cfg vname env Ts Us bary base targs rb u dps X bvar targ p s"
    unfolding mcc_projel_def
  proof (intro allI impI)
    fix env0 Cs env' env1 args env2 env3 fr ff
    assume g': "gentvars p env = (env0, Cs)" and pu: "okW (proj_unify cfg base bary Cs env0) env'"
      and ma: "make_args vname Ts env' (Us @ Cs) = (env1, args)"
      and up: "ok (update X (types_abs Ts (list_comb bvar args)) env1) env2"
      and sm: "okW (SIMPL (cfg_alg cfg) env2
        ((rb, list_comb targ (map (\<lambda>arg. list_comb (head_of arg) targs) args), u) # dps)) (env3, fr, ff)"
    have e: "env0 = e0" "Cs = C0" using g g' by simp_all
    have "\<not> (\<exists>evs e. ?m = Some (evs, UErr e))" using pu e by (auto simp: bindW_def returnW_def)
    with c obtain env'' where "okW (proj_unify cfg base bary C0 e0) env''"
      and s': "s = S_Proj vname env'' Ts (Us @ C0) targs rb u dps bvar targ X tail" by blast
    with pu e have "s = S_Proj vname env' Ts (Us @ Cs) targs rb u dps bvar targ X tail" by auto
    then show "ev cfg s (El_E env3 (fr @ ff))" using ev.proj[OF ma up sm] by simp
  qed
qed

lemma foldrW_projenv_ev:
  assumes "okW (foldrW (projenv cfg vname rb targs u env dps X base Ts bvar (Us, bary) targ) ps tail) s"
  shows "(\<forall>x. ev cfg tail x \<longrightarrow> ev cfg s x) \<and>
    (\<forall>p\<in>set ps. mcc_projel cfg vname env Ts Us bary base targs rb u dps X bvar targ p s)"
  using assms
proof (induction rule: okW_foldrW_induct)
  case (Cons p ps b b1 b')
  note pe = projenv_ev[OF Cons.hyps(2)]
  show ?case
  proof (intro conjI ballI allI impI)
    fix x assume "ev cfg b x"
    then show "ev cfg b' x" using Cons.IH pe(1) by blast
  next
    fix q assume "q \<in> set (p # ps)"
    then consider "q = p" | "q \<in> set ps" by auto
    then show "mcc_projel cfg vname env Ts Us bary base targs rb u dps X bvar targ q b'"
    proof cases
      case 1
      then show ?thesis using pe(2) by simp
    next
      case 2
      with Cons.IH have "mcc_projel cfg vname env Ts Us bary base targs rb u dps X bvar targ q b1" by blast
      then show ?thesis by (rule mcc_projel_mono) (rule pe(1))
    qed
  qed
qed simp

text \<open>The sequence of \<^const>\<open>matchfun\<close> contains the imitation and the projections with all guesses:\<close>

lemma matchfun_ev:
  assumes "okW (matchfun cfg vname envM rb targs u env dps X uhead uargs base Ts projs) sq"
  shows "(\<forall>si y. (\<exists>c C. uhead = Const c C \<or> uhead = Free c C) \<longrightarrow>
      okW (imitate vname envM rb targs env dps X Ts uhead uargs) si \<longrightarrow> ev cfg si y \<longrightarrow> ev cfg sq y) \<and>
    (\<forall>(bvar, T, targ)\<in>set projs. \<forall>Us bary. ok (strip_type env T) (Us, bary) \<longrightarrow>
      (\<forall>p\<in>set (arity_guesses cfg bary). mcc_projel cfg vname env Ts Us bary base targs rb u dps X bvar targ p sq))"
  using assms
proof (induction projs arbitrary: sq)
  case Nil
  show ?case
  proof (intro conjI allI impI)
    fix si y
    assume h: "\<exists>c C. uhead = Const c C \<or> uhead = Free c C"
      and si: "okW (imitate vname envM rb targs env dps X Ts uhead uargs) si" and ev: "ev cfg si y"
    from h Nil have "okW (imitate vname envM rb targs env dps X Ts uhead uargs) sq" by auto
    with si ev show "ev cfg sq y" by auto
  qed simp
next
  case (Cons q projs)
  obtain bvar T targ where q: "q = (bvar, T, targ)" by (cases q)
  from Cons.prems[unfolded q matchfun.simps] obtain Usb tail where st: "ok (strip_type env T) Usb"
    and mt: "okW (matchfun cfg vname envM rb targs u env dps X uhead uargs base Ts projs) tail"
    and fo: "okW (foldrW (projenv cfg vname rb targs u env dps X base Ts bvar Usb targ)
      (arity_guesses cfg (snd Usb)) tail) sq"
    by auto
  obtain Us0 bary0 where Usb: "Usb = (Us0, bary0)" by fastforce
  note IH = Cons.IH[OF mt]
  note fe = foldrW_projenv_ev[OF fo[unfolded Usb]]
  have pj: "mcc_projel cfg vname env Ts Us bary base targs rb u dps X bvar' targ' p sq"
    if m: "(bvar', T', targ') \<in> set (q # projs)" and st': "ok (strip_type env T') (Us, bary)"
      and p: "p \<in> set (arity_guesses cfg bary)" for bvar' T' targ' Us bary p
  proof -
    from m consider "(bvar', T', targ') = (bvar, T, targ)" | "(bvar', T', targ') \<in> set projs" using q by auto
    then show ?thesis
    proof cases
      case 1
      then have e: "bvar' = bvar" "T' = T" "targ' = targ" by simp_all
      with st st' Usb have "Us = Us0" "bary = bary0" by simp_all
      with fe p e show ?thesis by simp
    next
      case 2
      with IH st' p have "mcc_projel cfg vname env Ts Us bary base targs rb u dps X bvar' targ' p tail" by fastforce
      then show ?thesis by (rule mcc_projel_mono) (use fe in blast)
    qed
  qed
  show ?case
  proof (intro conjI)
    show "\<forall>si y. (\<exists>c C. uhead = Const c C \<or> uhead = Free c C) \<longrightarrow>
      okW (imitate vname envM rb targs env dps X Ts uhead uargs) si \<longrightarrow> ev cfg si y \<longrightarrow> ev cfg sq y"
      using IH fe by blast
    show "\<forall>(bvar, T, targ)\<in>set (q # projs). \<forall>Us bary. ok (strip_type env T) (Us, bary) \<longrightarrow>
      (\<forall>p\<in>set (arity_guesses cfg bary). mcc_projel cfg vname env Ts Us bary base targs rb u dps X bvar targ p sq)"
      using pj by blast
  qed
qed

subsection \<open>Completeness of the copies\<close>

lemma mcc_lsz_arg: "rigid h \<Longrightarrow> b \<in> set bs \<Longrightarrow> lsz E b < lsz E (h \<degree>\<degree> bs)"
proof -
  assume r: "rigid h" and b: "b \<in> set bs"
  have "lsz E b \<le> sum_list (map (lsz E) bs)" using b by (intro member_le_sum_list) auto
  then show ?thesis using lsz_rigid_apps[OF r] tsz_pos[of "spine_type E (h \<degree>\<degree> bs)"] by simp
qed

theorem mcc_mc_complete:
  assumes cfg: "cfg_alg cfg = alg" and M: "menv envM VM"
  shows "mcpre A0 envM VM F A K X env rb (x0, U0) targs u dps ot \<Longrightarrow>
    mcc_spre \<rho> \<sigma> env (F @ (rb, Var x0 U0 \<degree>\<degree> targs, u) # dps) X A e rb (x0, U0) targs Ss u UU s \<Longrightarrow>
    mcp_kokK (nat_of_integer (cfg_arity_bound cfg)) \<rho> (tyenv env) A K \<Longrightarrow>
    \<exists>sq. okW (mc cfg vname envM (x0, U0) rb targs u env dps) sq \<and>
      (\<exists>y. ev cfg sq y \<and> (\<exists>m. (rigid (fst (strip_comb u)) \<longrightarrow> vt_lookup (tenv env) x0 = None \<longrightarrow> m = 1) \<and>
        mcc_res A0 envM VM F A K X env (x0, U0) \<rho> \<sigma> m y))"
proof (induction "lsz (pushes mcp_e0 Ss) s" arbitrary: F A K X env rb x0 U0 targs u dps ot \<rho> \<sigma> e Ss UU s
    rule: less_induct)
  case less
  note pre = less.prems(1) and sp = less.prems(2) and kk = less.prems(3)
  let ?P = "(rb, Var x0 U0 \<degree>\<degree> targs, u)"
  note sp' = mcc_spreD[OF sp]
  have si: "sinv A K X env (F @ ?P # dps)" and vX: "vtvars X \<subseteq> tvars_env (tyenv env) \<union> A"
    using pre by (simp_all add: mcpre_def)
  have ei: "einv A K env" and wi: "winv env X" and p: "upok A env rb X (Var x0 U0 \<degree>\<degree> targs) u"
    using si by (auto simp: sinv_def)
  note E = einvD[OF ei] and pd = upokD[OF p]
  have vk: "vok env (X \<union> evars env)" by (rule vok_winv[OF ei wi vX])
  have vT: "(x0, U0) \<in> X \<union> evars env" using pd(1) by (auto simp: vars_apps)
  have lk: "lookup env x0 U0 = return (map_option snd (vt_lookup (tenv env) x0))"
    by (rule lookup_ok[OF E(6) E(7)]) (rule vok_mono[OF vk], use vT in blast)
  have c0: "cpinvX A0 envM VM F A K X env (?P # dps)" by (rule mcpre_cpinvX[OF pre, simplified])
  from mc_fin[OF cfg M pre] obtain sq where sq: "okW (mc cfg vname envM (x0, U0) rb targs u env dps) sq" by blast
  have "\<exists>y. ev cfg sq y \<and> (\<exists>m. (rigid (fst (strip_comb u)) \<longrightarrow> vt_lookup (tenv env) x0 = None \<longrightarrow> m = 1) \<and>
      mcc_res A0 envM VM F A K X env (x0, U0) \<rho> \<sigma> m y)"
    using sq
  proof (cases rule: mc_okW_cases)
    case (asg r)
    have vS: "vt_lookup (tenv env) x0 \<noteq> None"
      using lk asg(1) by (cases "vt_lookup (tenv env) x0") (auto simp: return_def)
    let ?y = "El_E env (?P # dps)"
    have "ev cfg sq ?y" using asg(2) by (simp add: list_comb_apps ev.single)
    moreover have "rigid (fst (strip_comb u)) \<longrightarrow> vt_lookup (tenv env) x0 = None \<longrightarrow> (0::nat) = 1"
      using vS by simp
    moreover have "mcc_res A0 envM VM F A K X env (x0, U0) \<rho> \<sigma> 0 ?y"
    proof (rule mcc_resI[where NV = "{}", OF refl c0 subset_refl subset_refl subset_refl sp'(1) extends_refl
          tagree_refl sagree_refl finite.emptyI empty_subsetI])
      show "ubv env X \<subseteq> (ubv env X - {fst (x0, U0)}) \<union> fst ` {}" using vS unfolding ubv_def by auto
    qed simp_all
    ultimately show ?thesis by (intro exI conjI)
  next
    case (abs a Ta body Ts B env' Y Y' env'')
    have vN: "vt_lookup (tenv env) x0 = None" using lk abs(1) by (auto simp: return_def)
    from pair_types[OF ei p] obtain T0 base Ts' where ty: "fastype env rb (fst (strip_comb u)) = return T0"
      "body_type env T0 = return base" "mapM (fastype env rb) targs = return Ts'" by blast
    have Ts: "Ts' = Ts" using ty(3) abs(3) by (simp add: return_def)
    note ty0 = ty(1,2) ty(3)[unfolded Ts]
    obtain B' where fB: "fastype env ((a, Ta) # rb) body = return B'"
      and tvB: "tvars B' \<subseteq> tvars_env (tyenv env) \<union> A" by (rule mcs_abs_type[OF pre vN ty0 abs(2)])
    have BB: "B' = B" using fB abs(4) by (simp add: return_def)
    note fB = fB[unfolded BB] and tvB = tvB[unfolded BB]
    note st = mcs_abs[OF pre vN ty0 abs(2) fB tvB abs(5) abs(7)]
    have Y': "Y' = ((vname, maxidx env + 1), foldr fun_type (Ts @ [Ta]) B)" using abs(6) st(2) by simp
    have "\<exists>x. ev cfg sq x \<and> mcc_res A0 envM VM F A K X env (x0, U0) \<rho> \<sigma> 0 x"
    proof (rule mcc_abs[OF pre vN ty0 sp abs(2) fB tvB abs(5) abs(7)])
      fix X'' \<sigma>'' e'' Ss'' UU'' s''
      assume lt: "lsz (pushes mcp_e0 Ss'') s'' < lsz (pushes mcp_e0 Ss) s"
        and pre'': "mcpre A0 envM VM F A K X'' env'' ((a, Ta) # rb) ((vname, maxidx env + 1), foldr fun_type (Ts @ [Ta]) B)
          (map (incr_boundvars 1) targs @ [Bound 0]) body dps None"
        and sp'': "mcc_spre \<rho> \<sigma>'' env'' (F @ ((a, Ta) # rb, Var (vname, maxidx env + 1) (foldr fun_type (Ts @ [Ta]) B) \<degree>\<degree>
          (map (incr_boundvars 1) targs @ [Bound 0]), body) # dps) X'' A e'' ((a, Ta) # rb)
          ((vname, maxidx env + 1), foldr fun_type (Ts @ [Ta]) B) (map (incr_boundvars 1) targs @ [Bound 0])
          Ss'' body UU'' s''"
      have kk'': "mcp_kokK (nat_of_integer (cfg_arity_bound cfg)) \<rho> (tyenv env'') A K" using kk st(4) by simp
      from less.hyps[OF lt pre'' sp'' kk''] obtain sq' y m where
        sq': "okW (mc cfg vname envM ((vname, maxidx env + 1), foldr fun_type (Ts @ [Ta]) B) ((a, Ta) # rb)
          (map (incr_boundvars 1) targs @ [Bound 0]) body env'' dps) sq'"
        and ev: "ev cfg sq' y"
        and r: "mcc_res A0 envM VM F A K X'' env'' ((vname, maxidx env + 1), foldr fun_type (Ts @ [Ta]) B) \<rho> \<sigma>'' m y"
        by blast
      have "sq' = sq" using sq' abs(8) Y' by auto
      with ev mcc_res_m[OF r] show "\<exists>x. ev cfg sq x \<and>
          mcc_res A0 envM VM F A K X'' env'' ((vname, maxidx env + 1), foldr fun_type (Ts @ [Ta]) B) \<rho> \<sigma>'' 0 x"
        by blast
    qed
    moreover have "\<not> rigid (fst (strip_comb u))" using abs(2) by (simp add: rigid_def)
    ultimately show ?thesis by blast
  next
    case (var w W T0 base Ts env' newhd env'')
    have vN: "vt_lookup (tenv env) x0 = None" using lk var(1) by (auto simp: return_def)
    have ty0: "fastype env rb (fst (strip_comb u)) = return T0" "body_type env T0 = return base"
      "mapM (fastype env rb) targs = return Ts" using var(2-5) by (simp_all add: return_def)
    have "mcc_res A0 envM VM F A K X env (x0, U0) \<rho> \<sigma> 0 (El_E env'' ((rb, newhd \<degree>\<degree> targs, u) # dps))"
      by (rule mcc_var[OF pre vN ty0 sp var(2,6,7)])
    moreover have "ev cfg sq (El_E env'' ((rb, newhd \<degree>\<degree> targs, u) # dps))"
      using var(8) by (simp add: list_comb_apps ev.single)
    moreover have "\<not> rigid (fst (strip_comb u))" using var(2) by (simp add: rigid_def)
    ultimately show ?thesis by blast
  next
    case (rigid T0 base Ts projs)
    let ?uh = "fst (strip_comb u)" and ?ua = "snd (strip_comb u)"
    have vN: "vt_lookup (tenv env) x0 = None" using lk rigid(1) by (auto simp: return_def)
    have ty0: "fastype env rb ?uh = return T0" "body_type env T0 = return base"
      "mapM (fastype env rb) targs = return Ts" using rigid(4-6) by (simp_all add: return_def)
    note mf = mcs_facts[OF pre vN ty0] and mev = matchfun_ev[OF rigid(8)]
    have lT: "length Ts = length targs" by (rule mf(10))
    have u2: "u = ?uh \<degree>\<degree> ?ua" by (rule strip_comb_apps) simp
    have r: "rigid ?uh"
    proof (cases ?uh)
      case (App f x)
      then have "strip_comb u = (f $ x, ?ua)" by (metis prod.collapse)
      from strip_comb_head[OF this] show ?thesis by blast
    qed (use rigid(2,3) in \<open>auto simp: rigid_def\<close>)
    have "\<not> is_Abs u" using rigid(2) unfolding u2[THEN arg_cong[of _ _ is_Abs]] is_Abs_apps by simp
    then have ar0: "arity UU = 0" using sp'(5) by simp
    note shp = mcp_target_shape[OF sp'(8) sp'(9) ar0]
    define h' where "h' = fst (strip_comb s)"
    define bs where "bs = snd (strip_comb s)"
    have s: "s = h' \<degree>\<degree> bs" and at: "atom h'" using shp by (simp_all add: h'_def bs_def)
    have P: "?P \<in> set (F @ ?P # dps)" by simp
    have imc: ?thesis if hc: "h' = Const c C \<or> h' = Free c C" for c C
    proof -
      have cc: "closed h'" "atom h'" using hc by (auto simp: closed_def)
      note tr = mcc_target_rigid[OF sp P r s cc(2,1)]
      obtain C0 where h: "?uh = Const c C0 \<or> ?uh = Free c C0" using tr(1) hc r by (cases ?uh) auto
      have rI: "rigid (inst \<rho> ?uh)" using h by (auto simp: rigid_def)
      have sh: "s = inst \<rho> ?uh \<degree>\<degree> bs" using s tr(1) by simp
      have IH: "\<exists>sq. okW (mc cfg vname envM (x0', U0') rb targs u' en d') sq \<and>
          (\<exists>y. ev cfg sq y \<and> (\<exists>m. mcc_res A0 envM VM F' A' K' X' en (x0', U0') \<rho>' \<sigma>' m y))"
        if "i < length bs" "mcpre A0 envM VM F' A' K' X' en rb (x0', U0') targs u' d' None"
          "mcc_spre \<rho>' \<sigma>' en (F' @ (rb, Var x0' U0' \<degree>\<degree> targs, u') # d') X' A' e rb (x0', U0') targs Ss u' B (bs ! i)"
          "mcp_kokK (nat_of_integer (cfg_arity_bound cfg)) \<rho>' (tyenv en) A' K'"
        for i F' A' K' X' en d' x0' U0' u' \<rho>' \<sigma>' B
      proof -
        have "lsz (pushes mcp_e0 Ss) (bs ! i) < lsz (pushes mcp_e0 Ss) s"
          unfolding sh by (rule mcc_lsz_arg[OF rI nth_mem[OF that(1)]])
        from less.hyps[OF this that(2-4)] show ?thesis by blast
      qed
      have "\<exists>si. okW (imitate vname envM rb targs env dps (x0, U0) Ts ?uh ?ua) si \<and>
          (\<exists>y. ev cfg si y \<and> mcc_res A0 envM VM F A K X env (x0, U0) \<rho> \<sigma> 1 y)"
        by (rule mcc_imit[OF cfg M pre vN ty0 sp kk h sh]) (rule IH; assumption)
      then obtain si y where
        si: "okW (imitate vname envM rb targs env dps (x0, U0) Ts ?uh ?ua) si" and ev: "ev cfg si y"
        and res: "mcc_res A0 envM VM F A K X env (x0, U0) \<rho> \<sigma> 1 y" by blast
      have "ev cfg sq y" using mev si ev h by blast
      with res show ?thesis by blast
    qed
    show ?thesis
    proof (cases h')
      case (Bound j)
      have "\<exists>B. pushes mcp_e0 Ss \<turnstile> Bound j : B" using sp'(8)[unfolded s Bound] by (blast elim: list_app_typeE)
      then have j0: "0 \<le> j" by auto
      have jS: "j < ilength Ss"
      proof (rule ccontr)
        assume "\<not> j < ilength Ss"
        then have "loose_bvar (Bound j) (ilength Ss)" by simp
        then show False using sp'(10) s Bound by (simp add: loose_bvar_apps)
      qed
      note sB = s[unfolded Bound] j0 jS
      have lSs: "length Ss = length targs" using typings_nth[OF sp'(3)] by simp
      define k where "k = length targs - 1 - nat_of_integer j"
      have jn: "nat_of_integer j < length targs" using sB(2,3) lSs nat_of_integer_less_ilength by fastforce
      have kn: "k < length targs" using jn by (simp add: k_def)
      have jk: "Bound (integer_of_nat (length targs - 1 - k)) = Bound j"
        using jn sB(2)
        by (simp add: k_def integer_eq_iff integer_of_nat.rep_eq nat_of_integer.rep_eq less_eq_integer.rep_eq)
      have tvTk: "tvars (Ts ! k) \<subseteq> tvars_env (tyenv env) \<union> A" using mf(12) kn lT by simp
      from binder_types_term[OF E(2) refl tvTk] obtain Us where bU: "binder_types env (Ts ! k) = return Us" by blast
      from body_type_term[OF E(2) refl tvTk] obtain bary where bB: "body_type env (Ts ! k) = return bary" by blast
      have st: "ok (strip_type env (Ts ! k)) (Us, bary)" using bU bB by (simp add: strip_type_def return_def)
      from mcc_proj_elem[OF cfg pre vN ty0 sp kk rigid(2) sB k_def st]
      obtain p env0 Cs env' where pg: "p \<in> set (arity_guesses cfg bary)" and g: "gentvars p env = (env0, Cs)"
        and pu: "okW (proj_unify cfg base bary Cs env0) env'"
        and el: "\<forall>env1 args. make_args vname Ts env' (Us @ Cs) = (env1, args) \<longrightarrow>
          (\<exists>env2 env3 fr ff. ok (update (x0, U0) (types_abs Ts (list_comb (Bound j) args)) env1) env2 \<and>
            okW (SIMPL (cfg_alg cfg) env2
              ((rb, list_comb (targs ! k) (map (\<lambda>arg. list_comb (head_of arg) targs) args), u) # dps)) (env3, fr, ff) \<and>
            mcc_res A0 envM VM F A K X env (x0, U0) \<rho> \<sigma> 1 (El_E env3 (fr @ ff)))"
        by blast
      obtain env1 args where ma: "make_args vname Ts env' (Us @ Cs) = (env1, args)" by fastforce
      from el ma obtain env2 env3 fr ff where up: "ok (update (x0, U0) (types_abs Ts (list_comb (Bound j) args)) env1) env2"
        and sm: "okW (SIMPL (cfg_alg cfg) env2
          ((rb, list_comb (targs ! k) (map (\<lambda>arg. list_comb (head_of arg) targs) args), u) # dps)) (env3, fr, ff)"
        and res: "mcc_res A0 envM VM F A K X env (x0, U0) \<rho> \<sigma> 1 (El_E env3 (fr @ ff))" by blast
      have "(Bound j, Ts ! k, targs ! k) \<in> set (rev projs)"
        using mcp_make_projs_mem[OF rigid(7) kn] jk by simp
      with mev st pg have "mcc_projel cfg vname env Ts Us bary base targs rb u dps (x0, U0) (Bound j) (targs ! k) p sq"
        by fastforce
      then have "ev cfg sq (El_E env3 (fr @ ff))" using g pu ma up sm unfolding mcc_projel_def by blast
      with res show ?thesis by blast
    next
      case (Var x T)
      have "Var x T = inst \<rho> ?uh" by (rule mcc_target_rigid(1)[OF sp P r s at, unfolded Var]) (simp add: closed_def)
      with r show ?thesis by (cases ?uh) (auto simp: rigid_def)
    qed (use imc at in auto)
  qed
  note conjI[OF sq this]
  then show ?case by (rule exI)
qed

subsection \<open>Completeness of \<^const>\<open>match_pair\<close>\<close>

lemma mcp_match_pair_complete:
  assumes cfg: "cfg_alg cfg = alg" and k: "k = nat_of_integer (cfg_arity_bound cfg)"
    and finX: "finite X" and finK: "finite K" and si: "sinv A K X env ((rb, t, u) # dps)"
    and fr: "fr_shape env (rb, t, u)" and inv: "scinv \<rho> \<sigma> env ((rb, t, u) # dps) X A"
    and kk: "mcp_kokK k \<rho> (tyenv env) A K"
    and st: "strip_comb t = (Var v T, targs)" and bt: "binder_types env T = return Ts"
    and len: "length Ts = length targs" and bT: "body_type env T = return B" and ar0: "arity (tsubst \<rho> B) = 0"
    and sat: "rsat env rb t u"
  shows "\<exists>s. okW (match_pair cfg env (rb, t, u) dps) s \<and> (\<exists>x. ev cfg s x \<and> mcp_mres A K X env \<rho> \<sigma> k x)"
proof -
  let ?\<theta> = "tyenv env" and ?KN = "tvars_env (tyenv env) \<union> A" and ?VM = "X \<union> evars env"
  have ei: "einv A K env" and wi: "winv env X" and p: "upok A env rb X t u"
    using si by (auto simp: sinv_def)
  note i = scinvD[OF inv] and sd = solutionD[OF scinvD(1)[OF inv]] and pd = upokD[OF p] and x = einvD[OF ei]
  have tt: "t = Var v T \<degree>\<degree> targs" by (rule strip_comb_apps[OF st])
  have hb: "hunb env (rb, t, u)" and f0: "frs0 (rb, t, u)" using fr by (simp_all add: fr_shape_def)
  have hv: "head_of t = Var v T" using st by (simp add: head_of_strip_comb)
  from hb hv have vn: "vt_lookup (tenv env) v = None" unfolding hunb_def by blast
  from f0 have nAu: "\<not> is_Abs u" and ru: "rigid (head_of u)" unfolding frs0_def by simp_all
  have ru': "rigid (fst (strip_comb u))" using ru by (simp add: head_of_strip_comb)
  have nab: "\<not> is_Abs (fst (strip_comb u))" using ru' by (cases "fst (strip_comb u)") (simp_all add: rigid_def)
  have vT: "(v, T) \<in> X \<union> evars env" using pd(1) tt by (simp add: vars_apps)
  have vU: "v \<in> ubv env X" using vT vn unfolding ubv_def by force
  \<comment> \<open>The type of the variable in the solution\<close>
  from i(6) obtain e TT where bs: "bs_env \<rho> e rb" and tyt0: "e \<turnstile> inst \<rho> t : TT"
    and tyu: "e \<turnstile> inst \<rho> u : TT" by (auto simp: dtyped_def)
  from tyt0[unfolded tt inst_apps] obtain Ss where tyv: "e \<turnstile> inst \<rho> (Var v T) : Ss \<Rrightarrow> TT"
    and tyas: "e \<tturnstile> map (inst \<rho>) targs : Ss" by (rule list_app_typeE)
  have Tv: "tsubst \<rho> T = Ss \<Rrightarrow> TT" and cT: "cert_typ alg ar (tsubst \<rho> T)" using tyv by auto
  have bT': "ok (body_type env T) B" using bT by (simp add: return_def)
  have TB: "tsubst \<rho> T = map (tsubst \<rho>) Ts \<Rrightarrow> tsubst \<rho> B"
    by (rule binder_body_type_sound[OF bt[unfolded return_def] refl bT' sd(2)])
  have lSs: "length Ss = length targs" using typings_nth[OF tyas] by simp
  have lSs': "length Ss = length (map (tsubst \<rho>) Ts)" using lSs len by simp
  from Tv TB have "Ss \<Rrightarrow> TT = map (tsubst \<rho>) Ts \<Rrightarrow> tsubst \<rho> B" by simp
  with funs_eq[OF lSs'] have TT: "TT = tsubst \<rho> B" by blast
  have arTT: "arity TT = 0" using ar0 TT by simp
  have cSs: "\<forall>S\<in>set Ss. cert_typ alg ar S" using cT Tv by (simp add: cert_typ_funs)
  \<comment> \<open>The target\<close>
  obtain s where tys: "pushes mcp_e0 Ss \<turnstile> s : TT" and nrs: "no_redex s" and lbs: "\<not> loose_bvar s (ilength Ss)"
    and cvs: "types_abs Ss s \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> \<sigma> v (Ss \<Rrightarrow> TT)"
    by (rule mcp_value_target[OF sd(3), of Ss TT v]) (use cT Tv in simp)
  \<comment> \<open>The copy\<close>
  have M: "menv env ?VM" unfolding menv_def using x(3,4,6,7) vok_winv[OF ei wi pd(6)] by blast
  have pre: "mcpre A env ?VM [] A K X env rb (v, T) targs u dps (Some t)"
    unfolding mcpre_def msat_def using finX finK pd(2,6) si sat nab by (simp add: tt)
  have sp: "mcc_spre \<rho> \<sigma> env ([] @ (rb, Var v T \<degree>\<degree> targs, u) # dps) X A e rb (v, T) targs Ss u TT s"
    unfolding mcc_spre_def
  proof (intro conjI)
    show "scinv \<rho> \<sigma> env ([] @ (rb, Var v T \<degree>\<degree> targs, u) # dps) X A" using inv tt by simp
    show "arity TT = nabs u" using arTT nAu by simp
    show "\<sigma> (fst (v, T)) (Ss \<Rrightarrow> TT) \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> types_abs Ss s" using cvs by (simp add: conv_sym)
  qed (use bs tyas tyu Tv cT tys nrs lbs in simp_all)
  have kk': "mcp_kokK (nat_of_integer (cfg_arity_bound cfg)) \<rho> (tyenv env) A K" using kk k by simp
  let ?R = "\<lambda>m y. (rigid (fst (strip_comb u)) \<longrightarrow> vt_lookup (tenv env) v = None \<longrightarrow> m = 1) \<and>
    mcc_res A env ?VM [] A K X env (v, T) \<rho> \<sigma> m y"
  have "\<exists>sq. okW (mc cfg (fst v) env (v, T) rb targs u env dps) sq \<and> (\<exists>y. ev cfg sq y \<and> (\<exists>m. ?R m y))"
    by (rule mcc_mc_complete[OF cfg M pre sp kk'])
  then obtain sq where sq0: "okW (mc cfg (fst v) env (v, T) rb targs u env dps) sq \<and> (\<exists>y. ev cfg sq y \<and> (\<exists>m. ?R m y))" ..
  note mc = conjunct1[OF sq0]
  from conjunct2[OF sq0] obtain y where y0: "ev cfg sq y \<and> (\<exists>m. ?R m y)" ..
  note evy = conjunct1[OF y0]
  from conjunct2[OF y0] obtain m where m0: "?R m y" ..
  have m1: "rigid (fst (strip_comb u)) \<longrightarrow> vt_lookup (tenv env) v = None \<longrightarrow> m = 1" using m0 by (rule conjunct1)
  have r: "mcc_res A env ?VM [] A K X env (v, T) \<rho> \<sigma> m y" using m0 by (rule conjunct2)
  have m: "m = 1" using m1 ru' vn by simp
  have "mcp_mres A K X env \<rho> \<sigma> k y"
    using r
  proof (rule mcc_resE)
    fix env' dps' A' K' X' \<rho>' \<sigma>' NV
    assume a: "y = El_E env' dps'" "cpinvX A env ?VM [] A' K' X' env' dps'"
      "A \<subseteq> A'" "K \<subseteq> K'" "X \<subseteq> X'" "scinv \<rho>' \<sigma>' env' ([] @ dps') X' A'" "extends env env'"
      "tagree (maxidx env) \<rho> \<rho>'" "sagree (maxidx env) \<sigma> \<sigma>'"
      "finite NV" "NV \<subseteq> X'" "\<forall>y\<in>NV. maxidx env < snd (fst y) \<or> y = (v, T)"
      "ubv env' X' \<subseteq> (ubv env X - {fst (v, T)}) \<union> fst ` NV"
      "(\<Sum>y\<in>NV. mcp_vsz \<rho>' \<sigma>' y) + m \<le> mcp_vsz \<rho> \<sigma> (v, T)"
      "\<forall>k. mcp_kokK k \<rho> (tyenv env) A K \<longrightarrow> mcp_kokK k \<rho>' (tyenv env') A' K'"
    have c: "finite X'" "finite K'" "sinv A' K' X' env' dps'" using a(2) by (simp_all add: cpinvX_def)
    have inv': "scinv \<rho>' \<sigma>' env' dps' X' A'" using a(6) by simp
    have sub: "X \<union> evars env \<subseteq> X' \<union> evars env'" using a(5) evars_extends[OF a(7)] by blast
    have lt: "(\<Sum>y\<in>NV. mcp_vsz \<rho>' \<sigma>' y) < mcp_vsz \<rho> \<sigma> (v, mcp_rep env X v)"
      using a(14) m mcp_vsz_rep[OF i(3) vU vT, of \<sigma>] by simp
    have meas: "mcp_meas \<rho>' \<sigma>' env' X' < mcp_meas \<rho> \<sigma> env X"
      by (rule mcp_meas_bind[OF inv a(8,9) scinvD(3)[OF inv'] sub finX c(1) a(10,11) _ vU lt]) (use a(13) in simp)
    show ?thesis
      by (rule mcp_mresI[OF a(1) c(1,2) a(3,4,5) c(3) inv' a(7,8,9) _ meas]) (use a(15) kk in blast)
  qed
  moreover have "okW (match_pair cfg env (rb, t, u) dps) sq" using mc st by (simp add: match_pair_def)
  ultimately show ?thesis using evy by blast
qed

lemma mcp_conv_incr: "s \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> t \<Longrightarrow> 0 \<le> k \<Longrightarrow> incr_bv (integer_of_nat n) k s \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> incr_bv (integer_of_nat n) k t"
proof (induction n)
  case (Suc n)
  have i: "integer_of_nat (Suc n) = integer_of_nat n + 1" by (simp add: integer_of_nat_eq_of_nat)
  show ?case unfolding i incr_bv_Suc[OF integer_of_nat_nonneg]
    by (rule conv_lift[OF Suc.IH[OF Suc.prems] Suc.prems(2)])
qed (simp add: integer_of_nat_eq_of_nat)

text \<open>The \<open>\<eta>\<close>-expansion of a solved pair is solved:\<close>

lemma mcp_scinv_eta_expand:
  assumes si: "sinv A K X env ((rb, t, u) # dps)" and inv: "scinv \<rho> \<sigma> env ((rb, t, u) # dps) X A"
    and st: "strip_comb t = (Var v T, targs)" and bt: "binder_types env T = return Ts"
  shows "scinv \<rho> \<sigma> env (eta_expand_dpair (drop (length targs) Ts) (rb, t, u) # dps) X A"
proof -
  note i = scinvD[OF inv] and sd = solutionD[OF scinvD(1)[OF inv]]
  have len: "length targs \<le> length Ts" by (rule sinv_eta_expand(1)[OF si st bt])
  have p: "upok A env rb X t u" using si by (simp add: sinv_def)
  define Es where "Es = drop (length targs) Ts"
  obtain rb' t' u' where ed: "eta_expand_dpair Es (rb, t, u) = (rb', t', u')" by (cases "eta_expand_dpair Es (rb, t, u)")
  have t': "t' = incr_bv (ilength Es) 0 t \<degree>\<degree> bvs (length Es)" and u': "u' = incr_bv (ilength Es) 0 u \<degree>\<degree> bvs (length Es)"
    using ed by (auto simp: eta_expand_dpair_def Let_def incr_boundvars_def list_comb_apps ilength_eq split: if_splits)
  have ds: "dstep env [(rb, t, u)] env [(rb', t', u')]"
    using dstep_eta_expand[OF st _ len, of env rb u] bt ed by (simp add: return_def Es_def)
  have "X \<union> dvars [(rb, t, u)] \<union> evars env = X \<union> evars env" using upokD(1,2)[OF p] by auto
  then have vi: "vinv \<rho> env (X \<union> dvars [(rb, t, u)])" using i(3) unfolding vinv_def by simp
  have dt1: "dtyped \<rho> [(rb, t, u)]" by (rule dtyped_mono[OF i(6)]) simp
  from dstepD(2)[OF ds sd(2) extends_refl i(2) dt1 vi] have dt': "dtyped \<rho> [(rb', t', u')]" by blast
  then obtain e' U where tyt: "e' \<turnstile> inst \<rho> t' : U" and tyu: "e' \<turnstile> inst \<rho> u' : U" by (auto simp: dtyped_def)
  have "ap \<rho> \<sigma> t \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma> u" using i(7) by (auto simp: dsolved_def)
  then have c: "incr_bv (ilength Es) 0 (ap \<rho> \<sigma> t) \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> incr_bv (ilength Es) 0 (ap \<rho> \<sigma> u)"
    unfolding ilength_eq by (rule mcp_conv_incr) simp
  have "ap \<rho> \<sigma> t' \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma> u'"
  proof -
    have e1: "ap \<rho> \<sigma> t' = incr_bv (ilength Es) 0 (ap \<rho> \<sigma> t) \<degree>\<degree> map (ap \<rho> \<sigma>) (bvs (length Es))"
      unfolding t' ap_apps by (simp add: ap_lift[OF sd(3)])
    have e2: "ap \<rho> \<sigma> u' = incr_bv (ilength Es) 0 (ap \<rho> \<sigma> u) \<degree>\<degree> map (ap \<rho> \<sigma>) (bvs (length Es))"
      unfolding u' ap_apps by (simp add: ap_lift[OF sd(3)])
    have w1: "wt (ap \<rho> \<sigma> t')" and w2: "wt (ap \<rho> \<sigma> u')" using wt_ap[OF tyt sd(3)] wt_ap[OF tyu sd(3)] .
    show ?thesis unfolding e1 e2
      by (rule conv_apps[OF _ _ _ c]) (use w1 w2 e1 e2 in \<open>simp_all add: list_all2_refl\<close>)
  qed
  then have "dsolved \<rho> \<sigma> [(rb', t', u')]" by (simp add: dsolved_def)
  then have "dsolved \<rho> \<sigma> ((rb', t', u') # dps)" and "dtyped \<rho> ((rb', t', u') # dps)"
    using i(6,7) dt' by (auto simp: dsolved_def dtyped_def)
  then show ?thesis using inv ed unfolding Es_def[symmetric] by (simp add: scinv_def)
qed


subsection \<open>Completeness of \<^const>\<open>match_sat\<close>\<close>

lemma mcp_match_sat_complete:
  assumes cfg: "cfg_alg cfg = alg" and k: "k = nat_of_integer (cfg_arity_bound cfg)"
    and finX: "finite X" and finK: "finite K" and si: "sinv A K X env ((rb, t, u) # dps)"
    and fr: "fr_shape env (rb, t, u)" and inv: "scinv \<rho> \<sigma> env ((rb, t, u) # dps) X A"
    and kk: "mcp_kokK k \<rho> (tyenv env) A K"
    and st: "strip_comb t = (Var v T, targs)" and bT: "body_type env T = return B" and ar0: "arity (tsubst \<rho> B) = 0"
    and ms: "msat_ok env (rb, t, u)"
  shows "\<exists>s. okW (match_sat cfg env (rb, t, u) dps) s \<and> (\<exists>x. ev cfg s x \<and> mcp_mres A K X env \<rho> \<sigma> k x)"
proof -
  have ei: "einv A K env" and p: "upok A env rb X t u" using si by (auto simp: sinv_def)
  have tv: "tvars T \<subseteq> tvars_env (tyenv env) \<union> A" using head_tvars_strip_comb[OF st] upokD(3)[OF p] by blast
  from binder_types_term[OF einvD(2)[OF ei] refl tv] obtain Ts where bt: "binder_types env T = return Ts" by blast
  define Es where "Es = drop (length targs) Ts"
  obtain rb' t' u' where ed: "eta_expand_dpair Es (rb, t, u) = (rb', t', u')"
    by (cases "eta_expand_dpair Es (rb, t, u)")
  have len: "length targs \<le> length Ts" by (rule sinv_eta_expand(1)[OF si st bt])
  have si': "sinv A K X env ((rb', t', u') # dps)" using sinv_eta_expand(2)[OF si st bt] ed by (simp add: Es_def)
  have inv': "scinv \<rho> \<sigma> env ((rb', t', u') # dps) X A" using mcp_scinv_eta_expand[OF si inv st bt] ed by (simp add: Es_def)
  have fr': "fr_shape env (rb', t', u')" using fr_shape_eta_expand[OF fr, of Es] ed by simp
  have t': "t' = incr_bv (ilength Es) 0 t \<degree>\<degree> bvs (length Es)"
    using ed by (auto simp: eta_expand_dpair_def Let_def incr_boundvars_def list_comb_apps ilength_eq split: if_splits)
  have st': "strip_comb t' = (Var v T, map (incr_bv (ilength Es) 0) targs @ bvs (length Es))"
    unfolding t' by (rule strip_comb_expand[OF st])
  have len': "length Ts = length (map (incr_bv (ilength Es) 0) targs @ bvs (length Es))"
    using len by (simp add: Es_def)
  have bto: "ok (binder_types env T) Ts" using bt by (simp add: return_def)
  from ms[unfolded msat_ok_def prod.case, rule_format, OF st bto] ed
  have sat': "rsat env rb' t' u'" by (simp add: Es_def)
  from mcp_match_pair_complete[OF cfg k finX finK si' fr' inv' kk st' bt len' bT ar0 sat']
  obtain s x where "okW (match_pair cfg env (rb', t', u') dps) s" "ev cfg s x" "mcp_mres A K X env \<rho> \<sigma> k x"
    by blast
  moreover have "okW (match_sat cfg env (rb, t, u) dps) s"
    using calculation(1) ed by (simp add: match_sat_def st bt Es_def return_def)
  ultimately show ?thesis by blast
qed


subsection \<open>Completeness of \<^const>\<open>MATCH\<close>\<close>

text \<open>A result for an extension of the type environment is a result for the original problem:\<close>

lemma mcp_mres_back:
  assumes r: "mcp_mres A' K' X env' \<rho>' \<sigma> k x" and sub: "A \<subseteq> A'" "K \<subseteq> K'"
    and ext: "extends env env'" and ag: "tagree (maxidx env) \<rho> \<rho>'" and te: "tenv env' = tenv env"
    and inv: "scinv \<rho> \<sigma> env dps X A" and vi': "vinv \<rho>' env' X"
  shows "mcp_mres A K X env \<rho> \<sigma> k x"
proof -
  have mx: "maxidx env \<le> maxidx env'" using ext by (simp add: extends_def)
  have ev: "evars env' = evars env" by (rule evars_tenv[OF te])
  have ub: "ubv env' X = ubv env X" by (simp add: ubv_def ev te)
  have rep: "mcp_rep env' X = mcp_rep env X" by (simp add: mcp_rep_def fun_eq_iff ev)
  have meq: "mcp_meas \<rho>' \<sigma> env' X = mcp_meas \<rho> \<sigma> env X"
    unfolding mcp_meas_def ub
    by (rule sum.cong[OF refl mcp_vsz_rep_old[OF inv ag sagree_refl vi']]) (use ub ev in auto)
  from r obtain env'' dps'' A'' K'' X'' \<rho>'' \<sigma>'' where x: "x = El_E env'' dps''" "finite X''" "finite K''"
    "A' \<subseteq> A''" "K' \<subseteq> K''" "X \<subseteq> X''" "sinv A'' K'' X'' env'' dps''" "scinv \<rho>'' \<sigma>'' env'' dps'' X'' A''"
    "extends env' env''" "tagree (maxidx env') \<rho>' \<rho>''" "sagree (maxidx env') \<sigma> \<sigma>''"
    "mcp_kokK k \<rho>'' (tyenv env'') A'' K''" "mcp_meas \<rho>'' \<sigma>'' env'' X'' < mcp_meas \<rho>' \<sigma> env' X"
    unfolding mcp_mres_def by blast
  show ?thesis
    by (rule mcp_mresI[OF x(1-3) _ _ x(6-8) extends_trans[OF ext x(9)] tagree_trans[OF ag x(10) mx]
          sagree_trans[OF sagree_refl x(11) mx] x(12)]) (use sub x(4,5,13) meq in auto)
qed

text \<open>The new type variables of a guess:\<close>

lemma mcp_gentvars_scinv:
  assumes si: "sinv A K X env dps" and inv: "scinv \<rho> \<sigma> env dps X A"
    and g: "gentvars p env = (env0, Cs)" and lD: "length Ds = p"
  obtains \<rho>1 where "tagree (maxidx env) \<rho> \<rho>1" "map (tsubst \<rho>1) Cs = Ds"
    "scinv \<rho>1 \<sigma> env0 dps X (A \<union> ntv Cs)" "sinv (A \<union> ntv Cs) (K \<union> ntv Cs) X env0 dps" "extends env env0"
proof -
  note gs = gentvars_simps[OF g] and i = scinvD[OF inv] and sd = solutionD[OF scinvD(1)[OF inv]]
  let ?\<theta> = "tyenv env" and ?A0 = "A \<union> ntv Cs" and ?K0 = "K \<union> ntv Cs"
  have ps: "\<forall>(rb', t', u')\<in>set dps. upok A env rb' X t' u'" using si by (simp add: sinv_def)
  obtain \<rho>1 where \<rho>1: "tagree (maxidx env) \<rho> \<rho>1" "map (tsubst \<rho>1) Cs = Ds" "wsinst alg \<rho>1"
    by (rule mcp_gentvars_inst[OF g lD sd(1)])
  have si0: "sinv ?A0 ?K0 X env0 dps" by (rule sinv_gentvars[OF si g])
  have ei0: "einv ?A0 ?K0 env0" using si0 by (simp add: sinv_def)
  have ext0: "extends env env0" by (rule extends_tenv_eq[OF gs(1,2,3)])
  have tbe: "tbelow (maxidx env) (tvars_env ?\<theta>)" by (rule tvinv_tbelow[OF i(4)]) simp
  have inv1: "scinv \<rho>1 \<sigma> env0 dps X ?A0"
    unfolding scinv_def
  proof (intro conjI)
    have "tsol ?\<theta> \<rho>1" by (rule mcp_tsol_agree[OF sd(2) \<rho>1(1) tbe])
    then show "solution \<rho>1 \<sigma> env0"
      by (rule solution_tyenv[OF i(1) i(4) i(3) \<rho>1(3) _ \<rho>1(1) gs(1), unfolded gs(2)])
    show "wt_env \<rho>1 env0" using wt_env_agree[OF i(2) \<rho>1(1) i(4)] wt_env_tenv[OF gs(1)] by simp
    show "vinv \<rho>1 env0 X" using vinv_tenv[OF gs(1) ext0 vinv_agree[OF i(3) \<rho>1(1) i(4) i(5)]] .
    show "tvinv ?A0 env0" by (rule einvD(1)[OF ei0])
    show "vtvars X \<subseteq> tvars_env (tyenv env0) \<union> ?A0" using i(5) gs(2) by auto
    show "dtyped \<rho>1 dps" by (rule sc_dps_agree(1)[OF ps i(4) i(3) \<rho>1(1) sagree_refl i(6)])
    show "dsolved \<rho>1 \<sigma> dps" by (rule sc_dps_agree(2)[OF ps i(4) i(3) \<rho>1(1) sagree_refl i(7)])
  qed
  from that[OF \<rho>1(1,2) inv1 si0 ext0] show ?thesis .
qed

lemma mcp_arity_split: obtains Ds R where "T = Ds \<Rrightarrow> R" "arity R = 0" "length Ds = arity T"
proof (induction "arity T" arbitrary: T thesis)
  case 0
  show ?case by (rule "0.prems"[of "[]" T]) (use "0.hyps" in simp_all)
next
  case (Suc n)
  then obtain T1 U where T: "T = T1 \<rightarrow>\<^sub>T U" by (cases T rule: arity.cases) (auto split: if_splits)
  from Suc.hyps(2) T have "n = arity U" by simp
  from Suc.hyps(1)[OF this] obtain Ds R where "U = Ds \<Rrightarrow> R" "arity R = 0" "length Ds = arity U" by blast
  with T show ?case by (intro Suc.prems[of "T1 # Ds" R]) simp_all
qed

lemma mcp_aok_res: "mcp_aok k (Ds \<Rrightarrow> U) \<Longrightarrow> mcp_aok k U"
  by (induction Ds) auto

text \<open>The arity of the instance of the type of a variable, from its body type:\<close>

lemma mcp_arity_body:
  assumes bT: "ok (body_type env T) B" and ac: "tacyc (tyenv env)" and sol: "tsol (tyenv env) \<rho>"
    and sol0: "tsol (tyenv env) (tnorm_inst (tyenv env))"
  shows "arity (tsubst \<rho> T) = arity (tnorm (tyenv env) T) + arity (tsubst \<rho> B)"
proof -
  from mf_body_type_sound[of env T "Ok B" B] bT ac obtain Zs where
    nf: "\<forall>C D. tnorm (tyenv env) B \<noteq> C \<rightarrow>\<^sub>T D" and
    Z: "\<And>\<rho>. tsol (tyenv env) \<rho> \<Longrightarrow> tsubst \<rho> T = map (tsubst \<rho>) Zs \<Rrightarrow> tsubst \<rho> B" by auto
  have a0: "arity (tnorm (tyenv env) B) = 0" using nf by (cases "tnorm (tyenv env) B" rule: arity.cases) auto
  have mz: "map (tsubst (tnorm_inst (tyenv env))) Zs = map (tnorm (tyenv env)) Zs"
    by (induction Zs) (simp_all only: list.map tsubst_tnorm_inst)
  have "tnorm (tyenv env) T = map (tnorm (tyenv env)) Zs \<Rrightarrow> tnorm (tyenv env) B"
    using Z[OF sol0] by (simp only: mz tsubst_tnorm_inst)
  then have "arity (tnorm (tyenv env) T) = length Zs" using a0 by (simp add: arity_funs)
  then show ?thesis using Z[OF sol] by (simp add: arity_funs)
qed

text \<open>Every guess of \<^const>\<open>match_eta\<close> keeps the elements of the tail:\<close>

lemma mcp_match_eta_tail:
  assumes "okW (match_eta cfg env dp dps B j tail) s" "ev cfg tail x"
  shows "ev cfg s x"
proof (cases "j = 0")
  case True
  with assms show ?thesis by (auto simp: match_eta_def intro: ev.append_r)
next
  case False
  obtain env1 Rs where g: "gentvars (Suc j) env = (env1, Rs)" by (cases "gentvars (Suc j) env")
  have h: "okW (handleW (do {
      env2 \<leftarrow> cunify_types (cfg_alg cfg) B (foldr (\<rightarrow>\<^sub>T) (tl Rs) (hd Rs)) env1;
      s' \<leftarrow> match_sat cfg env2 dp dps; returnW (S_Append s' tail)})
      (\<lambda>e. case e of CANTUNIFY \<Rightarrow> returnW tail | _ \<Rightarrow> raiseW e)) s"
    using assms(1) False g by (simp add: match_eta_def)
  from okW_handle_CANTUNIFY[OF h] show ?thesis using assms(2) by (auto intro: ev.append_r)
qed

lemma mcp_foldrW_mem:
  assumes "okW (foldrW f js b0) r" "j0 \<in> set js" "\<And>b s. okW (f j0 b) s \<Longrightarrow> ev cfg s x0"
    "\<And>j b s x. okW (f j b) s \<Longrightarrow> ev cfg b x \<Longrightarrow> ev cfg s x"
  shows "ev cfg r x0"
  using assms(1,2)
proof (induction js arbitrary: r)
  case (Cons j js)
  from Cons.prems(1) obtain r1 where r1: "okW (foldrW f js b0) r1" and r: "okW (f j r1) r" by auto
  show ?case
  proof (cases "j = j0")
    case True
    with r assms(3) show ?thesis by blast
  next
    case False
    with Cons.prems(2) have "j0 \<in> set js" by simp
    from assms(4)[OF r Cons.IH[OF r1 this]] show ?thesis .
  qed
qed simp


lemma mcp_noCU_match_eta: "noCU (match_eta cfg env dp dps B j tail)"
  unfolding match_eta_def match_sat_def
  by (auto intro!: noCU_bindW noCU_handleW noCU_CANTUNIFY_handler noCU_match_pair split: prod.splits pterm.splits)

lemma mcp_okW_bind_ok: "okW m x \<Longrightarrow> okW (bindW m f) y \<longleftrightarrow> okW (f x) y"
  by (auto simp only: okW_bindW dest: okW_det)

lemma mcp_okW_handle_ok: "okW m0 z \<Longrightarrow> okW (handleW m0 h) y \<Longrightarrow> y = z"
  by (auto simp: okW_handleW)

text \<open>
  Completeness of \<^const>\<open>MATCH\<close> on a flex-rigid pair of \<^const>\<open>SIMPL\<close>, for a solution that
  satisfies the arity condition: some element of an evaluation of the sequence is a new problem in
  the invariants, with an agreeing solution that satisfies the arity condition, and a smaller
  measure. If the body type of the variable is an unbound type variable, the right guess is the
  number of arguments of its instance, which is at most the arity bound; the other guesses do not
  raise exceptions (theorem @{thm [source] foldrW_match_eta_fin}).
\<close>

theorem MATCH_complete:
  assumes cfg: "cfg_alg cfg = alg" and k: "k = nat_of_integer (cfg_arity_bound cfg)"
    and finX: "finite X" and finK: "finite K" and si: "sinv A K X env (dp # dps)"
    and fr: "fr_shape env dp" and mo: "MATCH_ok env dp" and inv: "scinv \<rho> \<sigma> env (dp # dps) X A"
    and kk: "mcp_kokK k \<rho> (tyenv env) A K"
  shows "\<exists>ms. okW (MATCH cfg env dp dps) ms \<and> (\<exists>x. ev cfg ms x \<and> mcp_mres A K X env \<rho> \<sigma> k x)"
proof -
  obtain rb t u where dp: "dp = (rb, t, u)" by (cases dp)
  from fr dp obtain v T targs where st: "strip_comb t = (Var v T, targs)" by (auto elim: fr_shape_strip_comb)
  let ?\<theta> = "tyenv env" and ?KN = "tvars_env (tyenv env) \<union> A"
  have ei: "einv A K env" and p: "upok A env rb X t u" and ps: "\<forall>(rb', t', u')\<in>set (dp # dps). upok A env rb' X t' u'"
    using si dp by (auto simp: sinv_def)
  note x = einvD[OF ei] and i = scinvD[OF inv] and sd = solutionD[OF scinvD(1)[OF inv]]
  have below_KN: "tbelow (maxidx env) S" if "S \<subseteq> ?KN" for S using tvinv_tbelow[OF i(4) that] .
  have tvT: "tvars T \<subseteq> ?KN" using head_tvars_strip_comb[OF st] upokD(3)[OF p] by blast
  from body_type_term[OF x(2) refl tvT] obtain B where bT: "body_type env T = return B"
    and tvB: "tvars B \<subseteq> ?KN" by blast
  have bT': "ok (body_type env T) B" using bT by (simp add: return_def)
  \<comment> \<open>\<^const>\<open>match_sat\<close> in an extension of the type environment\<close>
  have good: "\<exists>s. okW (match_sat cfg envX dp dps) s \<and> (\<exists>x. ev cfg s x \<and> mcp_mres A K X env \<rho> \<sigma> k x)"
    if siX: "sinv AX KX X envX (dp # dps)" and invX: "scinv \<rho>X \<sigma> envX (dp # dps) X AX" and finKX: "finite KX"
      and kkX: "mcp_kokK k \<rho>X (tyenv envX) AX KX" and extX: "extends env envX" and teX: "tenv envX = tenv env"
      and bX: "body_type envX T = return BX" and arX: "arity (tsubst \<rho>X BX) = 0"
      and subX: "A \<subseteq> AX" "K \<subseteq> KX" and agX: "tagree (maxidx env) \<rho> \<rho>X"
    for envX \<rho>X AX KX BX
  proof -
    have frX: "fr_shape envX dp" using fr fr_shape_tenv[OF teX] by simp
    have msX: "msat_ok envX dp" using mo extX teX unfolding MATCH_ok_def by blast
    have "\<exists>s. okW (match_sat cfg envX (rb, t, u) dps) s \<and> (\<exists>x. ev cfg s x \<and> mcp_mres AX KX X envX \<rho>X \<sigma> k x)"
      by (rule mcp_match_sat_complete[OF cfg k finX finKX siX[unfolded dp] frX[unfolded dp] invX[unfolded dp]
            kkX st bX arX msX[unfolded dp]])
    then obtain s x where s: "okW (match_sat cfg envX (rb, t, u) dps) s" "ev cfg s x" "mcp_mres AX KX X envX \<rho>X \<sigma> k x"
      by blast
    have "mcp_mres A K X env \<rho> \<sigma> k x"
      by (rule mcp_mres_back[OF s(3) subX extX agX teX inv scinvD(3)[OF invX]])
    with s(1,2) dp show ?thesis by blast
  qed
  have M: "okW (MATCH cfg env dp dps) ms \<longleftrightarrow> okW (if is_TVar B then foldrW (match_eta cfg env dp dps B)
      (arity_guesses cfg B) S_Empty else match_sat cfg env dp dps) ms" for ms
  proof -
    have l3: "okW (liftM (body_type env T)) B" using bT' by simp
    show ?thesis
      by (simp only: MATCH_def dp st prod.case pterm.case mcp_okW_bind_ok[OF l3])
  qed
  show ?thesis
  proof (cases "is_TVar B")
    case False
    have ar0: "arity (tsubst \<rho> B) = 0" by (rule mcp_body_type_nonTVar_arity[OF bT' False x(6)])
    from good[OF si inv finK kk extends_refl refl bT ar0 order_refl order_refl tagree_refl] False M show ?thesis
      by (simp add: dp)
  next
    case TV: True
    from mcp_body_type_TVar[of env T "Ok B" B] bT TV obtain b S where Bb: "B = TVar b S"
      and bn: "vt_lookup (tyenv env) b = None" by (auto simp: return_def)
    have bS: "(b, S) \<in> tvars_env (tyenv env) \<union> A" using tvB Bb by simp
    have aokB: "mcp_aok k (tsubst \<rho> B)"
      using mcp_kok_unbound[OF mcp_kokK_kok[OF kk ei] bS bn x(6)] Bb by simp
    define j0 where "j0 = arity (tsubst \<rho> B)"
    have j0k: "j0 \<le> k" using mcp_aok_arity[OF aokB] by (simp add: j0_def)
    have j0g: "j0 \<in> set (arity_guesses cfg B)" using TV j0k k by (auto simp: arity_guesses_def)
    \<comment> \<open>The element for the guess \<open>j0\<close>\<close>
    obtain x0 where eta: "\<And>b s. okW (match_eta cfg env dp dps B j0 b) s \<Longrightarrow> ev cfg s x0"
      and gd: "mcp_mres A K X env \<rho> \<sigma> k x0"
    proof (cases "j0 = 0")
      case True
      from good[OF si inv finK kk extends_refl refl bT _ order_refl order_refl tagree_refl] True
      obtain s x where s: "okW (match_sat cfg env dp dps) s" "ev cfg s x" "mcp_mres A K X env \<rho> \<sigma> k x"
        by (auto simp: j0_def)
      show ?thesis
      proof (rule that[OF _ s(3)])
        fix b s' assume "okW (match_eta cfg env dp dps B j0 b) s'"
        then obtain s1 where o1: "okW (match_sat cfg env dp dps) s1" and e1: "s' = S_Append s1 b"
          using True by (auto simp: match_eta_def)
        have "s1 = s" by (rule okW_det[OF o1 s(1)])
        then show "ev cfg s' x" using e1 s(2) by (simp add: ev.append_l)
      qed
    next
      case False
      obtain Ds R where DR: "tsubst \<rho> B = Ds \<Rrightarrow> R" "arity R = 0" "length Ds = j0"
        using mcp_arity_split[of "tsubst \<rho> B"] by (auto simp: j0_def)
      obtain env1' Rs where g: "gentvars (Suc j0) env = (env1', Rs)" by (cases "gentvars (Suc j0) env")
      note gs = gentvars_simps[OF g]
      let ?A' = "A \<union> ntv Rs" and ?K' = "K \<union> ntv Rs"
      have lRD: "length (R # Ds) = Suc j0" using DR(3) by simp
      obtain \<rho>1' where r1: "tagree (maxidx env) \<rho> \<rho>1'" "map (tsubst \<rho>1') Rs = R # Ds"
        and inv1': "scinv \<rho>1' \<sigma> env1' (dp # dps) X ?A'" and si1': "sinv ?A' ?K' X env1' (dp # dps)"
        and ext1': "extends env env1'"
        by (rule mcp_gentvars_scinv[OF si inv g lRD])
      obtain R0 Rs' where Rs: "Rs = R0 # Rs'" using gs(4) by (cases Rs) auto
      have \<rho>R0: "tsubst \<rho>1' R0 = R" and \<rho>Rs': "map (tsubst \<rho>1') Rs' = Ds" using r1(2) Rs by simp_all
      have finK': "finite ?K'" using finK by (simp add: ntv_def)
      have ei1': "einv ?A' ?K' env1'" using si1' by (simp add: sinv_def)
      note x1' = einvD[OF ei1'] and i1' = scinvD[OF inv1'] and sd1' = solutionD[OF scinvD(1)[OF inv1']]
      have ps1': "\<forall>(rb', t', u')\<in>set (dp # dps). upok ?A' env1' rb' X t' u'" using si1' by (simp add: sinv_def)
      have tvB': "tvars B \<subseteq> tvars_env (tyenv env1') \<union> ?A'" using tvB gs(2) by auto
      have tvR: "tvars (Rs' \<Rrightarrow> R0) \<subseteq> tvars_env (tyenv env1') \<union> ?A'" using Rs by (auto simp: ntv_def tvars_funs)
      have \<rho>1'B: "tsubst \<rho>1' B = tsubst \<rho> B" by (rule tsubst_agree[OF r1(1) below_KN[OF tvB]])
      have eqB: "tsubst \<rho>1' B = tsubst \<rho>1' (Rs' \<Rrightarrow> R0)" using \<rho>1'B DR(1) \<rho>R0 \<rho>Rs' by (simp add: tsubst_funs)
      have cB0: "cert_typ alg ar B"
      proof -
        have "(b, S) \<in> tvars_env (tyenv env1') \<union> ?A'" using bS gs(2) by auto
        then have "sort_ok alg S" by (rule tcertD[OF x1'(10)])
        then show ?thesis by (simp add: Bb cert_typ_def)
      qed
      have cR0: "cert_typ alg ar (Rs' \<Rrightarrow> R0)"
      proof -
        have "cert_typ alg ar C" if "C \<in> set Rs" for C using gs(6)[OF that] by (auto simp: cert_typ_def sort_ok_def)
        then show ?thesis using Rs by (simp add: cert_typ_funs)
      qed
      from mcp_ncu_cuok[OF sc_cunify_complete[OF inv1' ps1' tvB' cert_wft[OF cB0] tvR cert_wft[OF cR0] eqB]
          cunify_types_sinv[OF finK' si1' tvB' cert_tnorm[OF ei1' cB0] tvR cert_tnorm[OF ei1' cR0]]]
      obtain env2 where cu2: "okW (cunify_types alg B (Rs' \<Rrightarrow> R0) env1') env2"
        and c2: "\<exists>\<rho>2. scinv \<rho>2 \<sigma> env2 (dp # dps) X ?A' \<and> tagree (maxidx env1') \<rho>1' \<rho>2 \<and>
          tvars_env (tyenv env1') \<subseteq> tvars_env (tyenv env2) \<and> maxidx env1' \<le> maxidx env2 \<and>
          tenv env2 = tenv env1' \<and> textends (tyenv env1') (tyenv env2)"
        and s2: "sinv ?A' ?K' X env2 (dp # dps) \<and> tenv env2 = tenv env1' \<and> extends env1' env2 \<and>
          tvars_env (tyenv env1') \<subseteq> tvars_env (tyenv env2) \<and>
          (\<forall>\<rho>. tsol (tyenv env2) \<rho> \<longrightarrow> tsubst \<rho> B = tsubst \<rho> (Rs' \<Rrightarrow> R0))"
        by blast
      from c2 obtain \<rho>2 where inv2: "scinv \<rho>2 \<sigma> env2 (dp # dps) X ?A'" and ag2: "tagree (maxidx env1') \<rho>1' \<rho>2"
        and tve2: "tvars_env (tyenv env1') \<subseteq> tvars_env (tyenv env2)" and te2: "tenv env2 = tenv env1'"
        and tx2: "textends (tyenv env1') (tyenv env2)" by blast
      have si2: "sinv ?A' ?K' X env2 (dp # dps)" and ext2: "extends env1' env2"
        and Beq: "\<And>\<rho>. tsol (tyenv env2) \<rho> \<Longrightarrow> tsubst \<rho> B = tsubst \<rho> (Rs' \<Rrightarrow> R0)" using s2 by blast+
      have ei2: "einv ?A' ?K' env2" using si2 by (simp add: sinv_def)
      note x2 = einvD[OF ei2] and i2 = scinvD[OF inv2] and sd2 = solutionD[OF scinvD(1)[OF inv2]]
      have mx1': "maxidx env \<le> maxidx env1'" by (rule gs(3))
      have ag12: "tagree (maxidx env) \<rho> \<rho>2" by (rule tagree_trans[OF r1(1) ag2 mx1'])
      have ext12: "extends env env2" by (rule extends_trans[OF ext1' ext2])
      have te02: "tenv env2 = tenv env" using te2 gs(1) by simp
      \<comment> \<open>The arity condition\<close>
      have N: "\<forall>(w, S')\<in>ntv Rs. (w, S') \<in> tvars_env (tyenv env1') \<union> ?A' \<and> mcp_aok k (\<rho>1' w S')"
      proof (intro ballI, clarify)
        fix w S' assume wS: "(w, S') \<in> ntv Rs"
        then obtain C where C: "C \<in> set Rs" "(w, S') \<in> tvars C" by (auto simp: ntv_def)
        from gs(6)[OF C(1)] obtain a where Ca: "C = TVar (a, maxidx env1') []" by blast
        have "tsubst \<rho>1' C \<in> set (R # Ds)" using r1(2) C(1) by (metis image_eqI list.set_map)
        moreover have "\<forall>D\<in>set (R # Ds). mcp_aok k D"
          using aokB DR(1) mcp_aok_funs[of k Ds R] mcp_aok_res[of k Ds R] by simp
        ultimately have "mcp_aok k (\<rho>1' w S')" using C(2) Ca by auto
        with wS show "(w, S') \<in> tvars_env (tyenv env1') \<union> ?A' \<and> mcp_aok k (\<rho>1' w S')" by auto
      qed
      have k1': "mcp_kokK k \<rho>1' (tyenv env1') ?A' ?K'"
        by (rule mcp_kokK_ext[OF kk _ x1'(6) x1'(7) sd1'(2) r1(1) below_KN[OF order_refl] x(6)
              tinv_tcons[OF x1'(2)] _ _ N]) (use gs(2) in auto)
      have "mcp_kokK k \<rho>2 (tyenv env2) ?A' (?K' \<union> {})"
        by (rule mcp_kokK_ext[OF k1' tx2 x2(6) x2(7) sd2(2) ag2 _ x1'(6) tinv_tcons[OF x2(2)] tve2])
          (use tvinv_tbelow[OF i1'(4)] in auto)
      then have kk2: "mcp_kokK k \<rho>2 (tyenv env2) ?A' ?K'" by simp
      \<comment> \<open>The body type in the extended type environment is not instantiated by a function type\<close>
      have tvT2: "tvars T \<subseteq> tvars_env (tyenv env2) \<union> ?A'" using tvT gs(2) tve2 by auto
      from body_type_term[OF x2(2) refl tvT2] obtain B2 where bT2: "body_type env2 T = return B2" by blast
      have bT2': "ok (body_type env2 T) B2" using bT2 by (simp add: return_def)
      have ar2: "arity (tsubst \<rho>2 B2) = 0"
      proof -
        let ?\<theta>2 = "tyenv env2"
        have tx12: "textends ?\<theta> ?\<theta>2" using tx2 gs(2) by simp
        note r02 = einv_rho0[OF ei2] and r01 = einv_rho0[OF ei]
        have a2: "arity (tsubst \<rho>2 T) = arity (tnorm ?\<theta>2 T) + arity (tsubst \<rho>2 B2)"
          by (rule mcp_arity_body[OF bT2' x2(6) sd2(2) r02(1)])
        have a1: "arity (tsubst \<rho> T) = arity (tnorm ?\<theta> T) + j0"
          using mcp_arity_body[OF bT' x(6) sd(2) r01(1)] by (simp add: j0_def)
        have \<rho>T: "tsubst \<rho>2 T = tsubst \<rho> T" by (rule tsubst_agree[OF ag12 below_KN[OF tvT]])
        from mf_body_type_sound[of env T "Ok B" B] bT' x(6) obtain Zs where
          nf: "\<forall>C D. tnorm ?\<theta> B \<noteq> C \<rightarrow>\<^sub>T D" and
          Z: "\<And>\<rho>. tsol ?\<theta> \<rho> \<Longrightarrow> tsubst \<rho> T = map (tsubst \<rho>) Zs \<Rrightarrow> tsubst \<rho> B" by auto
        have mz: "map (tsubst (tnorm_inst \<theta>)) Zs = map (tnorm \<theta>) Zs" for \<theta>
          by (induction Zs) (simp_all only: list.map tsubst_tnorm_inst)
        have "tnorm ?\<theta> T = map (tnorm ?\<theta>) Zs \<Rrightarrow> tnorm ?\<theta> B"
          using Z[OF r01(1)] by (simp only: mz tsubst_tnorm_inst)
        moreover have "arity (tnorm ?\<theta> B) = 0" using nf by (cases "tnorm ?\<theta> B" rule: arity.cases) auto
        ultimately have n1: "arity (tnorm ?\<theta> T) = length Zs" by (simp add: arity_funs)
        have s02: "tsol ?\<theta> (tnorm_inst ?\<theta>2)" by (rule tsol_textends[OF tx12 r02(1)])
        have "tnorm ?\<theta>2 T = map (tnorm ?\<theta>2) Zs \<Rrightarrow> tnorm ?\<theta>2 B"
          using Z[OF s02] by (simp only: mz tsubst_tnorm_inst)
        moreover have "tnorm ?\<theta>2 B = map (tnorm ?\<theta>2) Rs' \<Rrightarrow> tnorm ?\<theta>2 R0"
          using Beq[OF r02(1)] by (simp only: tsubst_tnorm_inst tnorm_funs_mf)
        moreover have lRs': "length Rs' = j0" using \<rho>Rs' DR(3) by (metis length_map)
        ultimately have "length Zs + j0 \<le> arity (tnorm ?\<theta>2 T)" by (simp add: arity_funs)
        then show ?thesis using a1 a2[unfolded \<rho>T] n1 by linarith
      qed
      from good[OF si2 inv2 finK' kk2 ext12 te02 bT2 ar2 _ _ ag12]
      obtain s x where s: "okW (match_sat cfg env2 dp dps) s" "ev cfg s x" "mcp_mres A K X env \<rho> \<sigma> k x"
        by auto
      show ?thesis
      proof (rule that[OF _ s(3)])
        fix b s' assume m: "okW (match_eta cfg env dp dps B j0 b) s'"
        let ?M = "do {env2' \<leftarrow> cunify_types (cfg_alg cfg) B (foldr (\<rightarrow>\<^sub>T) (tl Rs) (hd Rs)) env1';
          s'' \<leftarrow> match_sat cfg env2' dp dps; returnW (S_Append s'' b)}"
        have okM: "okW ?M (S_Append s b)" using cu2 s(1) Rs cfg by auto
        have "okW (handleW ?M (\<lambda>e. case e of CANTUNIFY \<Rightarrow> returnW b | _ \<Rightarrow> raiseW e)) s'"
          using m False g by (simp add: match_eta_def)
        then have "s' = S_Append s b" by (rule mcp_okW_handle_ok[OF okM])
        with s(2) show "ev cfg s' x" by (simp add: ev.append_l)
      qed
    qed
    \<comment> \<open>All guesses\<close>
    have "cuok (foldrW (match_eta cfg env dp dps B) (arity_guesses cfg B) S_Empty) (\<lambda>s. fin cfg s (mres A env))"
    proof (rule foldrW_match_eta_fin[OF cfg finX finK si fr _ tvB TV])
      show "msat_ok env' dp" if "extends env env'" "tenv env' = tenv env" for env'
        using mo that unfolding MATCH_ok_def by blast
    qed
    moreover have "noCU (foldrW (match_eta cfg env dp dps B) (arity_guesses cfg B) S_Empty)"
      by (rule noCU_foldrW[OF mcp_noCU_match_eta])
    ultimately obtain r where r: "okW (foldrW (match_eta cfg env dp dps B) (arity_guesses cfg B) S_Empty) r"
      unfolding xokW_def noCU_def by blast
    have "ev cfg r x0" by (rule mcp_foldrW_mem[OF r j0g eta mcp_match_eta_tail])
    with r M TV gd show ?thesis by auto
  qed
qed

end

end

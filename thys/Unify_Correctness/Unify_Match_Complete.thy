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

lemma mcp_vsubst_types_abs: "vsubst \<sigma> (types_abs Ts u) = types_abs Ts (vsubst \<sigma> u)"
  by (induction Ts) simp_all

lemma mcp_ap_types_abs: "ap \<rho> \<sigma> (types_abs Ts u) = types_abs (map (tsubst \<rho>) Ts) (ap \<rho> \<sigma> u)"
  by (simp add: ap_def mf_inst_types_abs mcp_vsubst_types_abs)

lemma mcp_types_abs_append: "types_abs (Ts @ Us) u = types_abs Ts (types_abs Us u)"
  by (induction Ts) simp_all

lemma mcp_no_redex_types_abs [simp]: "no_redex (types_abs Ts u) \<longleftrightarrow> no_redex u"
  by (induction Ts) simp_all

lemma mcp_lsz_types_abs: "lsz e (types_abs Ts u) = lsz (pushes e Ts) u + 2 * length Ts"
  by (induction Ts arbitrary: e) simp_all

lemma mcp_wt_types_abs: "wt (types_abs Vs s) \<Longrightarrow> wt s"
  by (induction Vs) (auto dest: wt_AbsD)

lemma mcp_conv_types_abs:
  "wt (types_abs Vs s) \<Longrightarrow> wt (types_abs Vs s') \<Longrightarrow> s \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> s' \<Longrightarrow> types_abs Vs s \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> types_abs Vs s'"
proof (induction Vs)
  case (Cons V Vs)
  from Cons.prems(1,2) have "wt (types_abs Vs s)" "wt (types_abs Vs s')" by (auto dest: wt_AbsD)
  from Cons.IH[OF this Cons.prems(3)] Cons.prems(1,2) show ?case by (simp add: conv_Abs)
qed simp

lemma mcp_bvs_downs: "mbvs n = map Bound (downs n)"
  by (induction n) simp_all

lemma mcp_eta_types_abs: "closed w \<Longrightarrow> types_abs Ts (w \<degree>\<degree> mbvs (length Ts)) \<rightarrow>\<^sub>\<eta>\<^sup>* w"
  using eta_abs_list_downs[of w "map (\<lambda>T. (STR '''', T)) Ts"]
  by (simp add: mf_types_abs_abs_list mcp_bvs_downs)

lemma mcp_conv_eta_types_abs:
  "closed w \<Longrightarrow> wt (types_abs Ts (w \<degree>\<degree> mbvs (length Ts))) \<Longrightarrow> types_abs Ts (w \<degree>\<degree> mbvs (length Ts)) \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> w"
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
  have ta: "mcp_e0 \<turnstile> types_abs Ss s : tsubst \<rho> T" using mf_typing_types_abs[OF ty(1) c] T by simp
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
  using assms
proof (induction env T r arbitrary: B rule: body_type.raw_induct[rotated, consumes 1])
  case (1 bt env T r)
  note h = "1.hyps"[unfolded "1.prems"(1)]
  show ?case
  proof (cases T)
    case (Type a Ts)
    show ?thesis
    proof (cases "a = STR ''fun'' \<and> (\<exists>T1 U. Ts = [T1, U])")
      case True
      then obtain T1 U where "T = T1 \<rightarrow>\<^sub>T U" using Type by auto
      with h have "ok (bt env U) B" by simp
      from "1.IH"[OF this refl "1.prems"(2)] show ?thesis .
    next
      case False
      with h Type have "B = T" by (auto split: list.splits if_splits)
      with Type "1.prems"(2) show ?thesis by simp
    qed
  next
    case (TVar v' S')
    from h TVar obtain lr where lr: "ok (type_lookup (tyenv env) v' S') lr"
      and rest: "ok (case lr of None \<Rightarrow> return T | Some T' \<Rightarrow> bt env T') B" by auto
    show ?thesis
    proof (cases lr)
      case None
      with lr have "vt_lookup (tyenv env) v' = None" by (auto simp: ok_type_lookup split: option.splits)
      with None rest TVar show ?thesis by (cases v') auto
    next
      case (Some T')
      with rest have "ok (bt env T') B" by simp
      from "1.IH"[OF this refl "1.prems"(2)] show ?thesis .
    qed
  next
    case (TFree a S)
    with h "1.prems"(2) show ?thesis by auto
  qed
qed

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


subsection \<open>The hypotheses of the copies\<close>

text \<open>The rigid side and the arguments are typable in every certified solution of the type environment:\<close>

definition mcp_tok :: "env \<Rightarrow> binders \<Rightarrow> pterm list \<Rightarrow> pterm \<Rightarrow> bool" where
  "mcp_tok env rb targs u \<longleftrightarrow> (\<forall>\<rho>0. tsol (tyenv env) \<rho>0 \<longrightarrow> cert_inst \<rho>0 \<longrightarrow>
    (\<exists>e Us U. bs_env \<rho>0 e rb \<and> e \<tturnstile> map (inst \<rho>0) targs : Us \<and> e \<turnstile> inst \<rho>0 u : U))"

text \<open>
  The hypotheses of a call \<open>mc cfg vname rb targs u env dps\<close>: the invariant of the termination
  proof for the other pairs \<open>dps\<close>, and the copied term \<open>u\<close> and the arguments \<open>targs\<close> of the
  variable are well-formed for the problem.
\<close>

definition mcp_pre :: "(indexname \<times> psort) set \<Rightarrow> (indexname \<times> psort) set \<Rightarrow> (indexname \<times> ptyp) set \<Rightarrow>
    env \<Rightarrow> dpair list \<Rightarrow> binders \<Rightarrow> pterm list \<Rightarrow> pterm \<Rightarrow> bool" where
  "mcp_pre A K X env dps rb targs u \<longleftrightarrow> finite X \<and> finite K \<and> sinv A K X env dps \<and>
    vars u \<subseteq> X \<union> evars env \<and> mlvars targs \<subseteq> X \<union> evars env \<and>
    ttvars u \<union> (\<Union>t\<in>set targs. ttvars t) \<union> btvars rb \<subseteq> tvars_env (tyenv env) \<union> A \<and>
    \<not> loose_bvar u (ilength rb) \<and> (\<forall>t\<in>set targs. \<not> loose_bvar t (ilength rb)) \<and>
    mcp_tok env rb targs u \<and> satd env rb u"

text \<open>
  The semantic hypotheses: \<open>(\<rho>, \<sigma>)\<close> solves the problem, and the target \<open>s\<close>, a \<open>\<beta>\<close>-normal term
  under binders of the types \<open>Ss\<close> of the arguments, is a copy of \<open>u\<close>: its abstraction applied to
  the arguments is equivalent to \<open>u\<close>. The type \<open>UU\<close> of \<open>u\<close> has no more argument types than \<open>u\<close>
  has abstractions.
\<close>

definition mcp_spre :: "tinst \<Rightarrow> vsubst \<Rightarrow> env \<Rightarrow> dpair list \<Rightarrow> (indexname \<times> ptyp) set \<Rightarrow>
    (indexname \<times> psort) set \<Rightarrow> (integer \<Rightarrow> ptyp) \<Rightarrow> binders \<Rightarrow> pterm list \<Rightarrow> ptyp list \<Rightarrow> pterm \<Rightarrow>
    ptyp \<Rightarrow> pterm \<Rightarrow> bool" where
  "mcp_spre \<rho> \<sigma> env dps X A e rb targs Ss u UU s \<longleftrightarrow> scinv \<rho> \<sigma> env dps X A \<and> bs_env \<rho> e rb \<and>
    e \<tturnstile> map (inst \<rho>) targs : Ss \<and> e \<turnstile> inst \<rho> u : UU \<and> arity UU = nabs u \<and>
    pushes mcp_e0 Ss \<turnstile> s : UU \<and> no_redex s \<and> \<not> loose_bvar s (ilength Ss) \<and>
    types_abs Ss s \<degree>\<degree> map (ap \<rho> \<sigma>) targs \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma> u"

text \<open>
  A copy \<open>u'\<close> of \<open>u\<close> for the target \<open>s\<close>: a new problem in the invariants, with a solution that
  agrees with \<open>(\<rho>, \<sigma>)\<close> on the old variables and maps the copy to the target; the new unbound
  variables \<open>NV\<close> have values whose sizes sum up to at most the size of the target, minus \<open>m\<close>.
\<close>

definition mcp_cres :: "(indexname \<times> psort) set \<Rightarrow> (indexname \<times> psort) set \<Rightarrow> (indexname \<times> ptyp) set \<Rightarrow>
    env \<Rightarrow> binders \<Rightarrow> pterm list \<Rightarrow> pterm \<Rightarrow> tinst \<Rightarrow> vsubst \<Rightarrow> ptyp list \<Rightarrow> ptyp \<Rightarrow> pterm \<Rightarrow> nat \<Rightarrow>
    elem \<Rightarrow> bool" where
  "mcp_cres A K X env rb targs u \<rho> \<sigma> Ss UU s m x \<longleftrightarrow>
    (\<exists>u' env' dps' A' K' X' \<rho>' \<sigma>' NV. x = El_C u' env' dps' \<and>
      finite X' \<and> finite K' \<and> A \<subseteq> A' \<and> K \<subseteq> K' \<and> X \<subseteq> X' \<and> sinv A' K' X' env' dps' \<and>
      scinv \<rho>' \<sigma>' env' dps' X' A' \<and> extends env env' \<and> tvars_env (tyenv env) \<subseteq> tvars_env (tyenv env') \<and>
      tagree (maxidx env) \<rho> \<rho>' \<and> sagree (maxidx env) \<sigma> \<sigma>' \<and>
      vars u' \<subseteq> X' \<union> evars env' \<and> ttvars u' \<subseteq> tvars_env (tyenv env') \<union> A' \<and> \<not> loose_bvar u' (ilength Ss) \<and>
      (\<forall>\<rho>0 e Us U. tsol (tyenv env') \<rho>0 \<longrightarrow> cert_inst \<rho>0 \<longrightarrow> bs_env \<rho>0 e rb \<longrightarrow>
        e \<tturnstile> map (inst \<rho>0) targs : Us \<longrightarrow> e \<turnstile> inst \<rho>0 u : U \<longrightarrow> (\<forall>e'. pushes e' Us \<turnstile> inst \<rho>0 u' : U)) \<and>
      pushes mcp_e0 Ss \<turnstile> inst \<rho>' u' : UU \<and> types_abs Ss (ap \<rho>' \<sigma>' u') \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> types_abs Ss s \<and>
      finite NV \<and> NV \<subseteq> X' \<and> (\<forall>y\<in>NV. maxidx env < snd (fst y)) \<and> ubv env' X' \<subseteq> ubv env X \<union> fst ` NV \<and>
      (\<Sum>y\<in>NV. mcp_vsz \<rho>' \<sigma>' y) + m \<le> lsz (pushes mcp_e0 Ss) s - 2 * arity UU \<and>
      (\<forall>k. mcp_kokK k \<rho> (tyenv env) A K \<longrightarrow> mcp_kokK k \<rho>' (tyenv env') A' K'))"

lemma mcp_typings_mem: "e \<tturnstile> map f ts : Us \<Longrightarrow> t \<in> set ts \<Longrightarrow> \<exists>U. e \<turnstile> f t : U"
  by (induction ts arbitrary: Us) (auto split: list.splits)

text \<open>The computations of the types at the beginning of \<^const>\<open>mc\<close> terminate:\<close>

lemma mcp_mc_types:
  assumes pre: "mcp_pre A K X env dps rb targs u"
  shows "\<exists>T0 base Ts. fastype env rb (fst (strip_comb u)) = return T0 \<and> body_type env T0 = return base \<and>
    mapM (fastype env rb) targs = return Ts \<and> tvars T0 \<subseteq> tvars_env (tyenv env) \<union> A \<and>
    tvars base \<subseteq> tvars_env (tyenv env) \<union> A \<and> (\<forall>T\<in>set Ts. tvars T \<subseteq> tvars_env (tyenv env) \<union> A)"
proof -
  have si: "sinv A K X env dps" and lu: "\<not> loose_bvar u (ilength rb)"
    and lt: "\<forall>t\<in>set targs. \<not> loose_bvar t (ilength rb)" and tok: "mcp_tok env rb targs u"
    and tv: "ttvars u \<union> (\<Union>t\<in>set targs. ttvars t) \<union> btvars rb \<subseteq> tvars_env (tyenv env) \<union> A"
    using pre by (simp_all add: mcp_pre_def)
  have ei: "einv A K env" using si by (simp add: sinv_def)
  note r0 = einv_rho0[OF ei] and ti = einvD(2)[OF ei]
  from tok r0 obtain e0 Us0 U0 where e0: "bs_env (rho0 env) e0 rb" "e0 \<tturnstile> map (inst (rho0 env)) targs : Us0"
    "e0 \<turnstile> inst (rho0 env) u : U0" unfolding mcp_tok_def by blast
  let ?uh = "fst (strip_comb u)"
  have hu: "head_of u = ?uh" by (simp add: head_of_strip_comb)
  from head_typing[OF e0(3)] hu obtain V where tyh: "e0 \<turnstile> inst (rho0 env) ?uh : V" by auto
  have u: "u = ?uh \<degree>\<degree> snd (strip_comb u)" by (rule strip_comb_apps) simp
  have luh: "\<not> loose_bvar ?uh (ilength rb)" using lu u by (metis loose_bvar_apps)
  have tvh: "ttvars ?uh \<union> btvars rb \<subseteq> tvars_env (tyenv env) \<union> A" using tv ttvars_head[of u] hu by auto
  from env_fastype_term[OF ti refl tyh e0(1) luh tvh] obtain T0 where
    T0: "env_fastype env (map snd rb) ?uh = return T0" "tvars T0 \<subseteq> tvars_env (tyenv env) \<union> A" by blast
  from body_type_term[OF ti refl T0(2)] obtain base where
    bt: "body_type env T0 = return base" "tvars base \<subseteq> tvars_env (tyenv env) \<union> A" by blast
  have "\<forall>s\<in>set targs. \<exists>e U. bs_env (rho0 env) e rb \<and> e \<turnstile> inst (rho0 env) s : U \<and> \<not> loose_bvar s (ilength rb) \<and>
      ttvars s \<union> btvars rb \<subseteq> tvars_env (tyenv env) \<union> A"
  proof
    fix s assume s: "s \<in> set targs"
    from mcp_typings_mem[OF e0(2) s] obtain U where "e0 \<turnstile> inst (rho0 env) s : U" by blast
    moreover have "ttvars s \<union> btvars rb \<subseteq> tvars_env (tyenv env) \<union> A" using tv s by blast
    ultimately show "\<exists>e U. bs_env (rho0 env) e rb \<and> e \<turnstile> inst (rho0 env) s : U \<and> \<not> loose_bvar s (ilength rb) \<and>
      ttvars s \<union> btvars rb \<subseteq> tvars_env (tyenv env) \<union> A" using e0(1) lt s by blast
  qed
  from mapM_fastype_term[OF ei this] obtain Ts where
    "mapM (fastype env rb) targs = return Ts" "\<forall>S\<in>set Ts. tvars S \<subseteq> tvars_env (tyenv env) \<union> A" by blast
  with T0 bt show ?thesis by (auto simp: fastype_def)
qed

text \<open>The types of the copy, for every typing of the arguments and the rigid side:\<close>

lemma mcp_types_sound:
  assumes pre: "mcp_pre A K X env dps rb targs u"
    and T0: "ok (fastype env rb (fst (strip_comb u))) T0" and bt: "ok (body_type env T0) base"
    and mt: "ok (mapM (fastype env rb) targs) Ts" and na: "\<not> is_Abs (fst (strip_comb u))"
    and \<rho>: "tsol (tyenv env) \<rho>" "bs_env \<rho> e rb" and tyt: "e \<tturnstile> map (inst \<rho>) targs : Us"
    and tyu: "e \<turnstile> inst \<rho> u : U"
  shows "Us = map (tsubst \<rho>) Ts" "U = tsubst \<rho> base" "\<forall>S\<in>set Us. cert_typ alg ar S" "cert_typ alg ar U"
    "length Ts = length targs"
proof -
  have lu: "\<not> loose_bvar u (ilength rb)" and lt: "\<forall>t\<in>set targs. \<not> loose_bvar t (ilength rb)"
    and sat: "satd env rb u" using pre by (simp_all add: mcp_pre_def)
  show us: "Us = map (tsubst \<rho>) Ts" using mapM_fastype_types[OF mt \<rho> tyt] by simp
  show "U = tsubst \<rho> base" by (rule satd_base[OF na sat T0 bt \<rho> tyu])
  show "\<forall>S\<in>set Us. cert_typ alg ar S" using mf_cert_targs[OF \<rho>(2) tyt[unfolded us] lt] us by simp
  show "cert_typ alg ar U" by (rule bs_env_cert[OF \<rho>(2) tyu lu])
  show "length Ts = length targs" using typings_nth[OF tyt] us by simp
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

lemma mcp_closed_types_abs: "\<not> loose_bvar s (ilength Ss) \<Longrightarrow> closed (types_abs Ss s)"
  by (simp add: closed_def mf_loose_bvar_types_abs)

lemma mcp_typing_val:
  assumes "pushes mcp_e0 Ss \<turnstile> s : UU" "\<not> loose_bvar s (ilength Ss)" "\<forall>S\<in>set Ss. cert_typ alg ar S"
  shows "e \<turnstile> types_abs Ss s : Ss \<Rrightarrow> UU"
  by (rule typing_closed[OF mf_typing_types_abs[OF assms(1,3)] mcp_closed_types_abs[OF assms(2)]])

lemma mcp_loose_combound: "\<not> loose_bvar G 0 \<Longrightarrow> \<not> loose_bvar (G \<degree>\<degree> mbvs n) (integer_of_nat n)"
  by (auto simp: loose_bvar_apps integer_less_iff integer_less_eq_iff integer_of_nat.rep_eq loose_bvar_mono)

subsection \<open>Copies: flexible heads\<close>

text \<open>A flexible head: a new variable for the copy, with a new pair.\<close>

lemma mcp_newvar:
  assumes pre: "mcp_pre A K X env dps rb targs u"
    and sp: "scinv \<rho> \<sigma> env dps X A \<and> bs_env \<rho> e rb \<and> e \<tturnstile> map (inst \<rho>) targs : Ss \<and> e \<turnstile> inst \<rho> u : UU \<and>
      pushes mcp_e0 Ss \<turnstile> s : UU \<and> no_redex s \<and> \<not> loose_bvar s (ilength Ss) \<and>
      types_abs Ss s \<degree>\<degree> map (ap \<rho> \<sigma>) targs \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma> u"
    and mt: "ok (mapM (fastype env rb) targs) Ts" and tvTs: "\<forall>T\<in>set Ts. tvars T \<subseteq> tvars_env (tyenv env) \<union> A"
    and tvW: "tvars W \<subseteq> tvars_env (tyenv env) \<union> A"
    and tyW: "\<And>\<rho>' e' U. tsol (tyenv env) \<rho>' \<Longrightarrow> bs_env \<rho>' e' rb \<Longrightarrow> e' \<turnstile> inst \<rho>' u : U \<Longrightarrow> U = tsubst \<rho>' W"
    and g: "genvar name env (Ts \<Rrightarrow> W) = (env', newhd)"
  shows "mcp_cres A K X env rb targs u \<rho> \<sigma> Ss UU s 0
    (El_C (combound newhd 0 (length Ts)) env' ((rb, newhd \<degree>\<degree> targs, u) # dps))"
proof -
  from pre have finX: "finite X" and finK: "finite K" and si: "sinv A K X env dps"
    and vu: "vars u \<subseteq> X \<union> evars env" and vt: "mlvars targs \<subseteq> X \<union> evars env"
    and tv: "ttvars u \<union> (\<Union>t\<in>set targs. ttvars t) \<union> btvars rb \<subseteq> tvars_env (tyenv env) \<union> A"
    and lu: "\<not> loose_bvar u (ilength rb)" and lt: "\<forall>t\<in>set targs. \<not> loose_bvar t (ilength rb)"
    and tok: "mcp_tok env rb targs u"
    unfolding mcp_pre_def by blast+
  from sp have inv: "scinv \<rho> \<sigma> env dps X A" and bs: "bs_env \<rho> e rb"
    and tyt: "e \<tturnstile> map (inst \<rho>) targs : Ss" and tyu: "e \<turnstile> inst \<rho> u : UU"
    and tys: "pushes mcp_e0 Ss \<turnstile> s : UU" and nrs: "no_redex s" and lbs: "\<not> loose_bvar s (ilength Ss)"
    and cv: "types_abs Ss s \<degree>\<degree> map (ap \<rho> \<sigma>) targs \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma> u"
    by blast+
  note i = scinvD[OF inv] and sd = solutionD[OF scinvD(1)[OF inv]]
  have ei: "einv A K env" and wi: "winv env X" and ps: "\<forall>(rb', t', u')\<in>set dps. pok A env rb' X t' u'"
    using si by (auto simp: sinv_def)
  let ?KN = "tvars_env (tyenv env) \<union> A"
  have ts: "Us = map (tsubst \<rho>') Ts" "U = tsubst \<rho>' W" "\<forall>S\<in>set Us. cert_typ alg ar S" "cert_typ alg ar U"
    "length Ts = length targs"
    if "tsol (tyenv env) \<rho>'" "bs_env \<rho>' e' rb" "e' \<tturnstile> map (inst \<rho>') targs : Us" "e' \<turnstile> inst \<rho>' u : U"
    for \<rho>' e' Us U
  proof -
    show us: "Us = map (tsubst \<rho>') Ts" using mapM_fastype_types[OF mt that(1-3)] by simp
    show "U = tsubst \<rho>' W" by (rule tyW[OF that(1,2,4)])
    show "\<forall>S\<in>set Us. cert_typ alg ar S" using mf_cert_targs[OF that(2) that(3)[unfolded us] lt] us by simp
    show "cert_typ alg ar U" by (rule bs_env_cert[OF that(2,4) lu])
    show "length Ts = length targs" using typings_nth[OF that(3)] us by simp
  qed
  note ts\<rho> = ts[OF sd(2) bs tyt tyu]
  note gs = genvar_simps[OF g]
  define y where "y = ((name, maxidx env + 1), Ts \<Rrightarrow> W)"
  have nh: "newhd = Var (fst y) (snd y)" using gs(4) by (simp add: y_def)
  define u' where "u' = combound newhd 0 (length Ts)"
  define dp where "dp = (rb, newhd \<degree>\<degree> targs, u)"
  have lenS: "length Ss = length Ts" using ts\<rho>(1) by simp
  have u'b: "u' = newhd \<degree>\<degree> mbvs (length Ss)" by (simp add: u'_def mf_combound_bvs lenS)
  have Ty: "tsubst \<rho> (snd y) = Ss \<Rrightarrow> UU" using ts\<rho>(1,2) by (simp add: y_def tsubst_funs)
  have cy: "cert_typ alg ar (tsubst \<rho> (snd y))" using Ty ts\<rho>(3,4) by (simp add: cert_typ_funs)
  have tyv: "\<And>e'. e' \<turnstile> types_abs Ss s : Ss \<Rrightarrow> UU" by (rule mcp_typing_val[OF tys lbs ts\<rho>(3)])
  have clv: "closed (types_abs Ss s)" by (rule mcp_closed_types_abs[OF lbs])
  define \<sigma>' where "\<sigma>' = supd \<sigma> (fst y) (tsubst \<rho> (snd y)) (types_abs Ss s)"
  have ny: "maxidx env < snd (fst y)" by (simp add: y_def)
  note su = mcp_solution_supd[OF i(1) i(3) ny clv tyv[folded Ty], folded \<sigma>'_def]
  have \<sigma>'y: "\<sigma>' (fst y) (tsubst \<rho> (snd y)) = types_abs Ss s" by (simp add: \<sigma>'_def)
  define X' where "X' = insert y X"
  have vX': "vars newhd \<union> X = X'" by (simp add: nh X'_def)
  have ev: "evars env' = evars env" by (rule evars_genvar[OF g])
  have ext: "extends env env'" by (rule extends_genvar[OF g])
  have tvy: "vtvars {y} \<subseteq> ?KN" using tvW tvTs by (auto simp: vtvars_def y_def tvars_funs)
  have vtX: "vtvars X' \<subseteq> ?KN" using tvy i(5) by (auto simp: X'_def vtvars_def)
  \<comment> \<open>The variables of the old terms are below the index of the new variable:\<close>
  have below_old: "below (maxidx env) (vars t)" if "vars t \<subseteq> X \<union> evars env" for t
    using i(3) that unfolding vinv_def by (meson below_mono order_refl)
  have apu: "ap \<rho> \<sigma>' u = ap \<rho> \<sigma> u" by (rule ap_sagree[OF su(2) below_old[OF vu]])
  have apt: "map (ap \<rho> \<sigma>') targs = map (ap \<rho> \<sigma>) targs"
    using ap_sagree[OF su(2) below_old] vt by auto
  \<comment> \<open>The typings of the new pair:\<close>
  have tyn: "e0 \<turnstile> inst \<rho>0 (newhd \<degree>\<degree> targs) : tsubst \<rho>0 W"
    if "bs_env \<rho>0 e0 rb" "e0 \<tturnstile> map (inst \<rho>0) targs : map (tsubst \<rho>0) Ts" "\<forall>S\<in>set (map (tsubst \<rho>0) Ts). cert_typ alg ar S"
      "cert_typ alg ar (tsubst \<rho>0 W)" for \<rho>0 e0
  proof -
    have "e0 \<turnstile> inst \<rho>0 newhd : map (tsubst \<rho>0) Ts \<Rrightarrow> tsubst \<rho>0 W"
      using that(3,4) by (auto simp: nh y_def tsubst_funs cert_typ_funs)
    from list_app_typeI[OF this that(2)] show ?thesis by (simp add: inst_apps)
  qed
  have tyu'0: "pushes e' Us \<turnstile> inst \<rho>0 u' : U"
    if "tsol (tyenv env) \<rho>0" "bs_env \<rho>0 e0 rb" "e0 \<tturnstile> map (inst \<rho>0) targs : Us" "e0 \<turnstile> inst \<rho>0 u : U" for \<rho>0 e0 Us U e'
  proof -
    note t0 = ts[OF that]
    have "pushes e' Us \<turnstile> inst \<rho>0 newhd : Us \<Rrightarrow> U"
      using t0 by (auto simp: nh y_def tsubst_funs cert_typ_funs)
    from list_app_typeI[OF this mf_typings_bvs] show ?thesis
      using t0(1) by (simp add: u'_def mf_combound_bvs inst_apps comp_def)
  qed
  \<comment> \<open>The invariant of the termination proof:\<close>
  have ei': "einv A K env'" by (rule einv_genvar[OF g ei])
  have wi': "winv env' X'"
    unfolding winv_def
  proof (intro allI impI)
    fix \<rho>0 assume "tsol (tyenv env') \<rho>0" "cert_inst \<rho>0"
    then have "wt_env \<rho>0 env \<and> vinv \<rho>0 env X" using winvD[OF wi] gs(2) by simp
    then show "wt_env \<rho>0 env' \<and> vinv \<rho>0 env' X'" using wt_env_genvar[OF g] vinv_genvar[OF g] vX' by blast
  qed
  have pdp: "pok A env' rb X' (newhd \<degree>\<degree> targs) u"
    unfolding pok_def
  proof (intro conjI allI impI)
    show "vars (newhd \<degree>\<degree> targs) \<union> vars u \<subseteq> X' \<union> evars env'"
      using vu vt by (auto simp: vars_apps nh X'_def ev)
    show "ttvars (newhd \<degree>\<degree> targs) \<union> ttvars u \<union> btvars rb \<union> vtvars X' \<subseteq> tvars_env (tyenv env') \<union> A"
      using tv vtX tvy by (auto simp: ttvars_apps gs(2) nh vtvars_def)
    show "\<not> loose_bvar (newhd \<degree>\<degree> targs) (ilength rb)" using lt by (simp add: loose_bvar_apps nh)
    show "\<not> loose_bvar u (ilength rb)" by (rule lu)
    fix \<rho>0 assume \<rho>0: "tsol (tyenv env') \<rho>0" "cert_inst \<rho>0"
    with tok gs(2) obtain e0 Us U where t0: "bs_env \<rho>0 e0 rb" "e0 \<tturnstile> map (inst \<rho>0) targs : Us"
      "e0 \<turnstile> inst \<rho>0 u : U" unfolding mcp_tok_def by auto
    note tt = ts[OF \<rho>0(1)[unfolded gs(2)] t0]
    show "\<exists>e T. bs_env \<rho>0 e rb \<and> e \<turnstile> inst \<rho>0 (newhd \<degree>\<degree> targs) : T \<and> e \<turnstile> inst \<rho>0 u : T"
      using tyn[OF t0(1) t0(2)[unfolded tt(1)]] tt t0 by blast
  qed
  have pds: "pok A env' rb' X' t' u''" if "(rb', t', u'') \<in> set dps" for rb' t' u''
  proof -
    from ps that have "pok A env rb' X t' u''" by auto
    then have "pok A env rb' X' t' u''" by (rule pok_Xmono) (use vtX in \<open>auto simp: X'_def\<close>)
    then show ?thesis by (rule pok_mono[OF _ ext]) (simp add: gs(2))
  qed
  have si': "sinv A K X' env' (dp # dps)"
    using ei' wi' pdp pds by (auto simp: sinv_def dp_def)
  \<comment> \<open>The completeness invariant:\<close>
  have dt: "dtyped \<rho> (dp # dps)"
  proof -
    have "e \<turnstile> inst \<rho> (newhd \<degree>\<degree> targs) : UU"
      using tyn[OF bs tyt[unfolded ts\<rho>(1)]] ts\<rho> by simp
    then show ?thesis using tyu bs i(6) lu lt by (auto simp: dp_def loose_bvar_apps nh)
  qed
  have ds: "dsolved \<rho> \<sigma>' (dp # dps)"
  proof -
    have "ap \<rho> \<sigma>' (newhd \<degree>\<degree> targs) = types_abs Ss s \<degree>\<degree> map (ap \<rho> \<sigma>) targs"
      by (simp add: ap_apps nh \<sigma>'y apt)
    then have "ap \<rho> \<sigma>' (newhd \<degree>\<degree> targs) \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma>' u" using cv apu by simp
    moreover have "dsolved \<rho> \<sigma>' dps" by (rule sc_dps_agree(2)[OF ps i(4) i(3) tagree_refl su(2) i(7)])
    ultimately show ?thesis by (simp add: dp_def)
  qed
  have inv': "scinv \<rho> \<sigma>' env' (dp # dps) X' A"
    unfolding scinv_def
  proof (intro conjI)
    show "solution \<rho> \<sigma>' env'" using su(1) solution_genvar[OF g] by simp
    show "wt_env \<rho> env'" using i(2) wt_env_genvar[OF g] by simp
    show "vinv \<rho> env' X'" using vinv_genvar[OF g i(3)] vX' by simp
    show "tvinv A env'" by (rule tvinv_genvar[OF g i(4)])
    show "vtvars X' \<subseteq> tvars_env (tyenv env') \<union> A" using vtX gs(2) by simp
  qed (use dt ds in simp_all)
  \<comment> \<open>The copy and its value:\<close>
  have tyc: "pushes mcp_e0 Ss \<turnstile> inst \<rho> u' : UU"
  proof -
    have "pushes mcp_e0 Ss \<turnstile> inst \<rho> newhd : Ss \<Rrightarrow> UU" using Ty cy by (auto simp: nh)
    from list_app_typeI[OF this mf_typings_bvs] show ?thesis by (simp add: u'b inst_apps comp_def)
  qed
  have apc: "ap \<rho> \<sigma>' u' = types_abs Ss s \<degree>\<degree> mbvs (length Ss)"
    by (simp add: u'b ap_apps nh \<sigma>'y comp_def)
  have cc: "types_abs Ss (ap \<rho> \<sigma>' u') \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> types_abs Ss s"
  proof -
    have "pushes mcp_e0 Ss \<turnstile> types_abs Ss s \<degree>\<degree> mbvs (length Ss) : UU"
      by (rule list_app_typeI[OF tyv mf_typings_bvs])
    then have "mcp_e0 \<turnstile> types_abs Ss (types_abs Ss s \<degree>\<degree> mbvs (length Ss)) : Ss \<Rrightarrow> UU"
      by (rule mf_typing_types_abs[OF _ ts\<rho>(3)])
    then show ?thesis unfolding apc by (intro mcp_conv_eta_types_abs[OF clv]) (auto simp: wt_def)
  qed
  \<comment> \<open>The measure:\<close>
  have vsz: "mcp_vsz \<rho> \<sigma>' y = lsz (pushes mcp_e0 Ss) s - 2 * arity UU"
    using mcp_vsz_val[OF su(3) cy _ Ty tys nrs ts\<rho>(3), of "fst y"] \<sigma>'y by (cases y) simp
  have ub: "ubv env' X' \<subseteq> ubv env X \<union> fst ` {y}"
    by (auto simp: ubv_def X'_def ev gs(1))
  have "mcp_cres A K X env rb targs u \<rho> \<sigma> Ss UU s 0 (El_C u' env' (dp # dps))"
    unfolding mcp_cres_def
  proof (intro exI conjI)
    show "finite X'" using finX by (simp add: X'_def)
    show "vars u' \<subseteq> X' \<union> evars env'" by (simp add: u'b vars_apps nh X'_def)
    show "ttvars u' \<subseteq> tvars_env (tyenv env') \<union> A" using tvy by (auto simp: u'b ttvars_apps nh vtvars_def gs(2))
    show "\<not> loose_bvar u' (ilength Ss)" unfolding u'b ilength_eq by (rule mcp_loose_combound) (simp add: nh)
    show "\<forall>\<rho>0 e Us U. tsol (tyenv env') \<rho>0 \<longrightarrow> cert_inst \<rho>0 \<longrightarrow> bs_env \<rho>0 e rb \<longrightarrow>
        e \<tturnstile> map (inst \<rho>0) targs : Us \<longrightarrow> e \<turnstile> inst \<rho>0 u : U \<longrightarrow> (\<forall>e'. pushes e' Us \<turnstile> inst \<rho>0 u' : U)"
      using tyu'0 gs(2) by simp
    show "(\<Sum>y\<in>{y}. mcp_vsz \<rho> \<sigma>' y) + 0 \<le> lsz (pushes mcp_e0 Ss) s - 2 * arity UU" using vsz by simp
  qed (use finK si' inv' ext gs su(2) tyc cc ny ub in \<open>auto simp: X'_def\<close>)
  then show ?thesis by (simp add: u'_def dp_def)
qed

lemma mcp_mc_var:
  assumes pre: "mcp_pre A K X env dps rb targs u"
    and sp: "mcp_spre \<rho> \<sigma> env dps X A e rb targs Ss u UU s"
    and hd: "fst (strip_comb u) = Var w W"
  shows "\<exists>sq. okW (mc cfg vname rb targs u env dps) sq \<and>
    (\<exists>x. ev cfg sq x \<and> mcp_cres A K X env rb targs u \<rho> \<sigma> Ss UU s 0 x)"
proof -
  let ?KN = "tvars_env (tyenv env) \<union> A"
  from mcp_mc_types[OF pre] obtain T0 base Ts where
    ty0: "fastype env rb (fst (strip_comb u)) = return T0" "body_type env T0 = return base"
      "mapM (fastype env rb) targs = return Ts" "tvars T0 \<subseteq> ?KN" "tvars base \<subseteq> ?KN" "\<forall>T\<in>set Ts. tvars T \<subseteq> ?KN"
    by blast
  have na: "\<not> is_Abs (fst (strip_comb u))" using hd by simp
  have sat: "satd env rb u" using pre by (simp add: mcp_pre_def)
  obtain env' newhd where g: "genvar (fst w) env (Ts \<Rrightarrow> base) = (env', newhd)" by fastforce
  have mc: "mc cfg vname rb targs u env dps =
      returnW (S_Single (El_C (combound newhd 0 (length Ts)) env' ((rb, newhd \<degree>\<degree> targs, u) # dps)))"
    by (subst mc.simps) (simp add: Let_def ty0(1-3) ty0(1)[unfolded hd] hd g list_comb_apps)
  have "mcp_cres A K X env rb targs u \<rho> \<sigma> Ss UU s 0
      (El_C (combound newhd 0 (length Ts)) env' ((rb, newhd \<degree>\<degree> targs, u) # dps))"
    by (rule mcp_newvar[where e = e, OF pre _ ty0(3)[unfolded return_def] ty0(6,5) satd_base[OF na sat ty0(1,2)[unfolded return_def]] g])
      (use sp in \<open>simp add: mcp_spre_def\<close>)
  then show ?thesis using mc by (auto intro: ev.single)
qed

subsection \<open>Copies: abstractions\<close>

lemma mcp_pushes_append: "pushes e (Ts @ Us) = pushes (pushes e Ts) Us"
  by (induction Ts arbitrary: e) simp_all

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

lemma mcp_ilength_nonneg: "0 \<le> ilength xs"
  by (simp add: ilength_eq integer_of_nat_eq_of_nat)

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
    by (rule beta_eta_conv) (use tA0 eta_lift[of a A s] in \<open>auto simp: wt_def\<close>)
  ultimately have "Abs a A s' \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> s" by (blast intro: conv_sym conv_trans)
  with that t2 b tA show ?thesis by blast
qed

lemma mcp_mc_abs:
  assumes pre: "mcp_pre A K X env dps rb targs u"
    and sp: "mcp_spre \<rho> \<sigma> env dps X A e rb targs Ss u UU s"
    and hd: "fst (strip_comb u) = Abs a T body"
    and IH: "\<And>e' Ss' UU' s'. lsz (pushes mcp_e0 Ss') s' < lsz (pushes mcp_e0 Ss) s \<Longrightarrow>
      mcp_pre A K X env dps ((a, T) # rb) (map (incr_boundvars 1) targs @ [Bound 0]) body \<Longrightarrow>
      mcp_spre \<rho> \<sigma> env dps X A e' ((a, T) # rb) (map (incr_boundvars 1) targs @ [Bound 0]) Ss' body UU' s' \<Longrightarrow>
      \<exists>sq. okW (mc cfg vname ((a, T) # rb) (map (incr_boundvars 1) targs @ [Bound 0]) body env dps) sq \<and>
        (\<exists>x. ev cfg sq x \<and> mcp_cres A K X env ((a, T) # rb) (map (incr_boundvars 1) targs @ [Bound 0]) body
          \<rho> \<sigma> Ss' UU' s' m x)"
  shows "\<exists>sq. okW (mc cfg vname rb targs u env dps) sq \<and>
    (\<exists>x. ev cfg sq x \<and> mcp_cres A K X env rb targs u \<rho> \<sigma> Ss UU s m x)"
proof -
  let ?rb = "(a, T) # rb" and ?ts = "map (incr_boundvars 1) targs @ [Bound 0]"
  from pre have finX: "finite X" and finK: "finite K" and si: "sinv A K X env dps"
    and vu: "vars u \<subseteq> X \<union> evars env" and vt: "mlvars targs \<subseteq> X \<union> evars env"
    and tv: "ttvars u \<union> (\<Union>t\<in>set targs. ttvars t) \<union> btvars rb \<subseteq> tvars_env (tyenv env) \<union> A"
    and lu: "\<not> loose_bvar u (ilength rb)" and lt: "\<forall>t\<in>set targs. \<not> loose_bvar t (ilength rb)"
    and tok: "mcp_tok env rb targs u" and sat: "satd env rb u"
    unfolding mcp_pre_def by blast+
  from sp have inv: "scinv \<rho> \<sigma> env dps X A" and bs: "bs_env \<rho> e rb"
    and tyt: "e \<tturnstile> map (inst \<rho>) targs : Ss" and tyu: "e \<turnstile> inst \<rho> u : UU" and ar: "arity UU = nabs u"
    and tys: "pushes mcp_e0 Ss \<turnstile> s : UU" and nrs: "no_redex s" and lbs: "\<not> loose_bvar s (ilength Ss)"
    and cv: "types_abs Ss s \<degree>\<degree> map (ap \<rho> \<sigma>) targs \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma> u"
    unfolding mcp_spre_def by blast+
  note i = scinvD[OF inv] and sd = solutionD[OF scinvD(1)[OF inv]]
  from satd_Abs[OF hd sat] have na: "snd (strip_comb u) = []" and sb: "satd env ?rb body" by blast+
  have "u = fst (strip_comb u) \<degree>\<degree> snd (strip_comb u)" by (rule strip_comb_apps) simp
  then have u: "u = Abs a T body" using hd na by simp
  from mcp_mc_types[OF pre] obtain T0 base Ts where
    ty0: "fastype env rb (fst (strip_comb u)) = return T0" "body_type env T0 = return base"
      "mapM (fastype env rb) targs = return Ts"
    by blast
  \<comment> \<open>The hypotheses for the body:\<close>
  have lts: "\<forall>t\<in>set ?ts. \<not> loose_bvar t (ilength ?rb)"
  proof
    fix t assume "t \<in> set ?ts"
    then consider t0 where "t0 \<in> set targs" "t = incr_boundvars 1 t0" | "t = Bound 0" by auto
    then show "\<not> loose_bvar t (ilength ?rb)"
    proof cases
      case 1
      then show ?thesis using lt loose_bvar_lift[of 0 "ilength rb" t0] mcp_ilength_nonneg[of rb]
        by (simp add: incr_boundvars_1 add.commute)
    next
      case 2
      then show ?thesis using mcp_ilength_nonneg[of rb] by (simp add: integer_arith)
    qed
  qed
  have tok': "mcp_tok env ?rb ?ts body"
    unfolding mcp_tok_def
  proof (intro allI impI)
    fix \<rho>0 assume \<rho>0: "tsol (tyenv env) \<rho>0" "cert_inst \<rho>0"
    with tok obtain e0 Us U where t0: "bs_env \<rho>0 e0 rb" "e0 \<tturnstile> map (inst \<rho>0) targs : Us"
      "e0 \<turnstile> inst \<rho>0 u : U" unfolding mcp_tok_def by blast
    from t0(3) u obtain U1 where c: "cert_typ alg ar (tsubst \<rho>0 T)"
      and tb: "e0\<langle>0:tsubst \<rho>0 T\<rangle> \<turnstile> inst \<rho>0 body : U1" by auto
    show "\<exists>e Us U. bs_env \<rho>0 e ?rb \<and> e \<tturnstile> map (inst \<rho>0) ?ts : Us \<and> e \<turnstile> inst \<rho>0 body : U"
      using bs_env_Cons[OF t0(1) c, of a] mcp_typings_lift[OF t0(2)] tb by blast
  qed
  have pre': "mcp_pre A K X env dps ?rb ?ts body"
    unfolding mcp_pre_def
  proof (intro conjI)
    show "vars body \<subseteq> X \<union> evars env" using vu u by simp
    show "mlvars ?ts \<subseteq> X \<union> evars env" using vt by (auto simp: incr_boundvars_def)
    show "ttvars body \<union> (\<Union>t\<in>set ?ts. ttvars t) \<union> btvars ?rb \<subseteq> tvars_env (tyenv env) \<union> A"
      using tv u by (auto simp: incr_boundvars_def btvars_def)
    show "\<not> loose_bvar body (ilength ?rb)" using lu u by (simp add: algebra_simps)
  qed (use finX finK si lts tok' sb in auto)
  \<comment> \<open>The target for the body:\<close>
  from tyu u obtain UU1 where cT: "cert_typ alg ar (tsubst \<rho> T)"
    and tyb: "e\<langle>0:tsubst \<rho> T\<rangle> \<turnstile> inst \<rho> body : UU1" and UU: "UU = tsubst \<rho> T \<rightarrow>\<^sub>T UU1" by auto
  let ?A = "tsubst \<rho> T"
  obtain s' where s': "(pushes mcp_e0 Ss)\<langle>0:?A\<rangle> \<turnstile> s' : UU1" "no_redex s'" "lift s 0 $ Bound 0 \<rightarrow>\<^sub>\<beta>\<^sup>* s'"
      "Abs STR '''' ?A s' \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> s" "pushes mcp_e0 Ss \<turnstile> Abs STR '''' ?A s' : UU"
    using mcp_conv_eta_body[OF tys[unfolded UU] cT] UU by blast
  have SsT: "map (tsubst \<rho>) Ts = Ss" by (rule mapM_fastype_types[OF ty0(3)[unfolded return_def] sd(2) bs tyt])
  have cS: "\<forall>S\<in>set Ss. cert_typ alg ar S" using mf_cert_targs[OF bs tyt[folded SsT] lt] SsT by auto
  have lbs': "\<not> loose_bvar s' (ilength (Ss @ [?A]))"
  proof
    assume "loose_bvar s' (ilength (Ss @ [?A]))"
    moreover have "(sup beta eta)\<^sup>*\<^sup>* (lift s 0 $ Bound 0) s'"
      using s'(3) by (rule rtranclp_mono[THEN predicate2D, rotated]) auto
    ultimately have "loose_bvar (lift s 0 $ Bound 0) (ilength Ss + 1)"
      using loose_bvar_reds[of "lift s 0 $ Bound 0" s' "ilength Ss + 1"] mcp_ilength_nonneg[of Ss]
      by (simp add: mcp_ilength_snoc integer_arith)
    then show False using lbs loose_bvar_lift[of 0 "ilength Ss" s] mcp_ilength_nonneg[of Ss]
      by (simp add: integer_arith)
  qed
  have W: "closed (types_abs Ss s)" "\<And>e'. e' \<turnstile> types_abs Ss s : Ss \<Rrightarrow> UU"
    using mcp_closed_types_abs[OF lbs] mcp_typing_val[OF tys lbs cS] by blast+
  have W': "closed (types_abs (Ss @ [?A]) s')" by (rule mcp_closed_types_abs[OF lbs'])
  have tW': "\<And>e'. e' \<turnstile> types_abs (Ss @ [?A]) s' : (Ss @ [?A]) \<Rrightarrow> UU1"
    by (rule mcp_typing_val) (use s'(1) lbs' cS cT in \<open>simp_all add: mcp_pushes_append\<close>)
  have tae: "types_abs (Ss @ [?A]) s' = types_abs Ss (Abs STR '''' ?A s')" by (simp add: mcp_types_abs_append)
  have WW: "types_abs (Ss @ [?A]) s' \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> types_abs Ss s"
    unfolding tae
    by (rule mcp_conv_types_abs[OF _ _ s'(4)]) (use tW' W(2) tae in \<open>auto simp: wt_def\<close>)
  have tapt: "e \<tturnstile> map (ap \<rho> \<sigma>) targs : Ss"
    using tyt by (induction targs arbitrary: Ss) (auto split: list.splits intro: typing_ap[OF _ sd(3)])
  have cvb: "types_abs (Ss @ [?A]) s' \<degree>\<degree> map (ap \<rho> \<sigma>) ?ts \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma> body"
  proof -
    have m: "map (ap \<rho> \<sigma>) ?ts = map (\<lambda>t. lift t 0) (map (ap \<rho> \<sigma>) targs) @ [Bound 0]"
      by (simp add: incr_boundvars_1 ap_lift[OF sd(3)])
    have c0: "types_abs Ss s \<degree>\<degree> map (ap \<rho> \<sigma>) targs \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> Abs a ?A (ap \<rho> \<sigma> body)" using cv u by simp
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
  have pe: "pushes mcp_e0 (Ss @ [?A]) = (pushes mcp_e0 Ss)\<langle>0:?A\<rangle>" by (simp add: mcp_pushes_append)
  have sp': "mcp_spre \<rho> \<sigma> env dps X A (e\<langle>0:?A\<rangle>) ?rb ?ts (Ss @ [?A]) body UU1 s'"
    unfolding mcp_spre_def
  proof (intro conjI)
    show "bs_env \<rho> (e\<langle>0:?A\<rangle>) ?rb" by (rule bs_env_Cons[OF bs cT])
    show "e\<langle>0:?A\<rangle> \<tturnstile> map (inst \<rho>) ?ts : Ss @ [?A]" by (rule mcp_typings_lift[OF tyt])
    show "arity UU1 = nabs body" using ar UU u by simp
    show "pushes mcp_e0 (Ss @ [?A]) \<turnstile> s' : UU1" using s'(1) pe by simp
  qed (use inv tyb s'(2) lbs' cvb in simp_all)
  have sz: "lsz (pushes mcp_e0 (Ss @ [?A])) s' < lsz (pushes mcp_e0 Ss) s"
  proof -
    have "lsz (pushes mcp_e0 Ss) (Abs STR '''' ?A s') = lsz (pushes mcp_e0 Ss) s"
      by (rule mcp_lsz_conv[OF s'(4) s'(5) tys[unfolded UU[symmetric]]]) (simp_all add: s'(2) nrs)
    then show ?thesis using pe by simp
  qed
  from IH[OF sz pre' sp'] obtain sq' x where sq': "okW (mc cfg vname ?rb ?ts body env dps) sq'"
    and evx: "ev cfg sq' x" and cr: "mcp_cres A K X env ?rb ?ts body \<rho> \<sigma> (Ss @ [?A]) UU1 s' m x" by blast
  from cr obtain body' env' dps' A' K' X' \<rho>' \<sigma>' NV where x: "x = El_C body' env' dps'"
    and c: "finite X'" "finite K'" "A \<subseteq> A'" "K \<subseteq> K'" "X \<subseteq> X'" "sinv A' K' X' env' dps'"
      "scinv \<rho>' \<sigma>' env' dps' X' A'" "extends env env'" "tvars_env (tyenv env) \<subseteq> tvars_env (tyenv env')"
      "tagree (maxidx env) \<rho> \<rho>'" "sagree (maxidx env) \<sigma> \<sigma>'"
      "vars body' \<subseteq> X' \<union> evars env'" "ttvars body' \<subseteq> tvars_env (tyenv env') \<union> A'"
      "\<not> loose_bvar body' (ilength (Ss @ [?A]))"
    and cty: "\<forall>\<rho>0 e Us U. tsol (tyenv env') \<rho>0 \<longrightarrow> cert_inst \<rho>0 \<longrightarrow> bs_env \<rho>0 e ?rb \<longrightarrow>
        e \<tturnstile> map (inst \<rho>0) ?ts : Us \<longrightarrow> e \<turnstile> inst \<rho>0 body : U \<longrightarrow> (\<forall>e'. pushes e' Us \<turnstile> inst \<rho>0 body' : U)"
    and c2: "pushes mcp_e0 (Ss @ [?A]) \<turnstile> inst \<rho>' body' : UU1"
      "types_abs (Ss @ [?A]) (ap \<rho>' \<sigma>' body') \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> types_abs (Ss @ [?A]) s'"
      "finite NV" "NV \<subseteq> X'" "\<forall>y\<in>NV. maxidx env < snd (fst y)" "ubv env' X' \<subseteq> ubv env X \<union> fst ` NV"
      "(\<Sum>y\<in>NV. mcp_vsz \<rho>' \<sigma>' y) + m \<le> lsz (pushes mcp_e0 (Ss @ [?A])) s' - 2 * arity UU1"
      "\<forall>k. mcp_kokK k \<rho> (tyenv env) A K \<longrightarrow> mcp_kokK k \<rho>' (tyenv env') A' K'"
    using cr unfolding mcp_cres_def by (elim exE conjE) (rule that; assumption)
  have mc: "mc cfg vname rb targs u env dps = bindW (mc cfg vname ?rb ?ts body env dps) (\<lambda>s. returnW (S_MapAbs a T s))"
    by (subst mc.simps) (simp add: Let_def ty0 ty0(1)[unfolded hd] hd)
  have ev': "ev cfg (S_MapAbs a T sq') (El_C (Abs a T body') env' dps')" using evx x by (simp add: ev.map_abs)
  have tT: "tvars T \<subseteq> tvars_env (tyenv env) \<union> A" using tv u by auto
  have \<rho>'T: "tsubst \<rho>' T = ?A" by (rule tsubst_agree[OF c(10) tvinv_tbelow[OF i(4) tT]])
  have ub: "lsz (pushes mcp_e0 Ss) s - 2 * arity UU = lsz (pushes mcp_e0 (Ss @ [?A])) s' - 2 * arity UU1"
  proof -
    have "lsz (pushes mcp_e0 Ss) (Abs STR '''' ?A s') = lsz (pushes mcp_e0 Ss) s"
      by (rule mcp_lsz_conv[OF s'(4) s'(5) tys[unfolded UU[symmetric]]]) (simp_all add: s'(2) nrs)
    then show ?thesis using pe UU by simp
  qed
  have un: "unname (types_abs Ss t) = types_abs Ss (unname t)" for t by (induction Ss) simp_all
  have cc: "types_abs Ss (ap \<rho>' \<sigma>' (Abs a T body')) \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> types_abs Ss s"
  proof -
    have "aconv_term (types_abs Ss (ap \<rho>' \<sigma>' (Abs a T body'))) (types_abs (Ss @ [?A]) (ap \<rho>' \<sigma>' body'))"
      by (simp add: aconv_term_unname un mcp_types_abs_append \<rho>'T)
    then have "types_abs Ss (ap \<rho>' \<sigma>' (Abs a T body')) \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> types_abs (Ss @ [?A]) (ap \<rho>' \<sigma>' body')"
      by (rule aconv_term_conv)
    then show ?thesis using c2(2) WW by (blast intro: conv_trans)
  qed
  have cr': "mcp_cres A K X env rb targs u \<rho> \<sigma> Ss UU s m (El_C (Abs a T body') env' dps')"
    unfolding mcp_cres_def
  proof (intro exI conjI)
    show "vars (Abs a T body') \<subseteq> X' \<union> evars env'" using c(12) by simp
    show "ttvars (Abs a T body') \<subseteq> tvars_env (tyenv env') \<union> A'" using c(3,9,13) tT by auto
    show "\<not> loose_bvar (Abs a T body') (ilength Ss)" using c(14) by (simp add: mcp_ilength_snoc add.commute)
    show "\<forall>\<rho>0 e Us U. tsol (tyenv env') \<rho>0 \<longrightarrow> cert_inst \<rho>0 \<longrightarrow> bs_env \<rho>0 e rb \<longrightarrow>
        e \<tturnstile> map (inst \<rho>0) targs : Us \<longrightarrow> e \<turnstile> inst \<rho>0 u : U \<longrightarrow> (\<forall>e'. pushes e' Us \<turnstile> inst \<rho>0 (Abs a T body') : U)"
    proof (intro allI impI)
      fix \<rho>0 e0 Us U e' assume a: "tsol (tyenv env') \<rho>0" "cert_inst \<rho>0" "bs_env \<rho>0 e0 rb"
        "e0 \<tturnstile> map (inst \<rho>0) targs : Us" "e0 \<turnstile> inst \<rho>0 u : U"
      from a(5) u obtain U1 where c0: "cert_typ alg ar (tsubst \<rho>0 T)"
        and tb: "e0\<langle>0:tsubst \<rho>0 T\<rangle> \<turnstile> inst \<rho>0 body : U1" and U: "U = tsubst \<rho>0 T \<rightarrow>\<^sub>T U1" by auto
      have "pushes e' (Us @ [tsubst \<rho>0 T]) \<turnstile> inst \<rho>0 body' : U1"
        using cty a(1,2) bs_env_Cons[OF a(3) c0, of a] mcp_typings_lift[OF a(4)] tb by blast
      then show "pushes e' Us \<turnstile> inst \<rho>0 (Abs a T body') : U" using c0 U by (auto simp: mcp_pushes_append)
    qed
    show "pushes mcp_e0 Ss \<turnstile> inst \<rho>' (Abs a T body') : UU" using c2(1) pe cT UU \<rho>'T by auto
    show "(\<Sum>y\<in>NV. mcp_vsz \<rho>' \<sigma>' y) + m \<le> lsz (pushes mcp_e0 Ss) s - 2 * arity UU" using c2(7) ub by simp
  qed (use c c2 cc in simp_all)
  show ?thesis using mc sq' ev' cr' by (intro exI[of _ "S_MapAbs a T sq'"]) auto
qed

subsection \<open>Simultaneous substitution of the arguments\<close>

text \<open>As \<open>cpy\<close> of theory \<open>Unify_Match_Sound\<close>: the \<open>\<beta>\<close>-normal form of an abstraction over
  \<open>length ts\<close> variables applied to \<open>ts\<close>.\<close>

lemma mcp_subst_abs_list:
  "0 \<le> k \<Longrightarrow> (abs_list bs u)[s/k] = abs_list bs (u[incr_bv (ilength bs) 0 s / k + ilength bs])"
proof (induction bs arbitrary: s k)
  case (Cons b bs)
  obtain x T where b: "b = (x, T)" by (cases b)
  have "incr_bv (ilength bs) 0 (lift s 0) = incr_bv (ilength (b # bs)) 0 s"
    by (simp add: mf_incr_bv_incr_bv)
  with Cons.IH[of "k + 1" "lift s 0"] Cons.prems show ?case by (simp add: b algebra_simps)
qed simp

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
    by (simp add: mcp_subst_abs_list il)
  finally have "abs_list bs u \<degree>\<degree> (t # ts) \<rightarrow>\<^sub>\<beta>\<^sup>* abs_list bs' (u[incr_bv (ilength ts) 0 t / ilength ts]) \<degree>\<degree> ts"
    unfolding bs by (simp add: r_into_rtranclp)
  also have "\<dots> \<rightarrow>\<^sub>\<beta>\<^sup>* mcp_cpy (t # ts) u" using Cons.IH[OF l] by simp
  finally show ?case .
qed simp

lemma mcp_beta_cpy: "length Ts = length ts \<Longrightarrow> types_abs Ts u \<degree>\<degree> ts \<rightarrow>\<^sub>\<beta>\<^sup>* mcp_cpy ts u"
  unfolding mf_types_abs_abs_list by (rule mcp_beta_cpy_abs_list) simp

lemma mcp_cpy_App: "mcp_cpy ts (s $ t) = mcp_cpy ts s $ mcp_cpy ts t"
  by (induction ts arbitrary: s t) simp_all

lemma mcp_cpy_apps: "mcp_cpy ts (s \<degree>\<degree> us) = mcp_cpy ts s \<degree>\<degree> map (mcp_cpy ts) us"
  by (induction us arbitrary: s) (simp_all add: mcp_cpy_App)

lemma mcp_cpy_closed: "closed h \<Longrightarrow> mcp_cpy ts h = h"
  by (induction ts) (simp_all add: subst_no_loose closed_loose_bvar)

lemma mcp_subst_incr_bv_Suc:
  "0 \<le> k \<Longrightarrow> 0 \<le> n \<Longrightarrow> (incr_bv (n + 1) k t)[s/k + n] = incr_bv n k t"
proof (induction t arbitrary: k s)
  case (Bound i)
  then show ?case by (auto simp: subst_Bound integer_arith)
next
  case (Abs a T t)
  from Abs.IH[of "k + 1" "lift s 0"] Abs.prems show ?case by (simp add: algebra_simps)
qed auto

lemma mcp_cpy_incr: "mcp_cpy ts (incr_bv (ilength ts) 0 t) = t"
proof (induction ts arbitrary: t)
  case (Cons s ts)
  have "(incr_bv (ilength ts + 1) 0 t)[incr_bv (ilength ts) 0 s/ilength ts] = incr_bv (ilength ts) 0 t"
    using mcp_subst_incr_bv_Suc[of 0 "ilength ts" t] by (simp add: mcp_ilength_nonneg)
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

subsection \<open>The sequence of \<^const>\<open>matchfun\<close>\<close>

text \<open>The copy of a projection on \<open>targ\<close>, after the type unification with the environment \<open>env'\<close>, is an
  element of the sequence \<open>s\<close>:\<close>

definition mcp_projel :: "cfg \<Rightarrow> name \<Rightarrow> env \<Rightarrow> ptyp list \<Rightarrow> ptyp list \<Rightarrow> pterm list \<Rightarrow> binders \<Rightarrow> pterm \<Rightarrow>
    dpair list \<Rightarrow> pterm \<Rightarrow> pterm \<Rightarrow> seq \<Rightarrow> bool" where
  "mcp_projel cfg vname env' Ts Us targs rb u dps bvar targ s \<longleftrightarrow>
    (\<forall>env'' args env2 fr ff. make_args vname Ts env' Us = (env'', args) \<longrightarrow>
      okW (SIMPL (cfg_alg cfg) env'' ((rb, list_comb targ (map (\<lambda>arg. list_comb (head_of arg) targs) args), u) # dps))
        (env2, fr, ff) \<longrightarrow>
      ev cfg s (El_C (list_comb bvar args) env2 (fr @ ff)))"

lemma mcp_projel_Proj: "mcp_projel cfg vname env' Ts Us targs rb u dps bvar targ (S_Proj vname env' Ts Us targs rb u dps bvar targ tail)"
  unfolding mcp_projel_def by (auto intro: ev.proj)

lemma mcp_projel_mono: "mcp_projel cfg vname env' Ts Us targs rb u dps bvar targ s \<Longrightarrow> (\<And>x. ev cfg s x \<Longrightarrow> ev cfg s' x) \<Longrightarrow>
    mcp_projel cfg vname env' Ts Us targs rb u dps bvar targ s'"
  unfolding mcp_projel_def by blast

lemma mcp_okW_cuok: "okW m x \<Longrightarrow> cuok m P \<Longrightarrow> P x"
  unfolding cuok_def by auto

lemma mcp_projenv:
  assumes cfg: "cfg_alg cfg = alg" and finK: "finite K" and si: "sinv A K X env dps"
    and tv: "tvars base \<subseteq> tvars_env (tyenv env) \<union> A" "tvars bary \<subseteq> tvars_env (tyenv env) \<union> A"
    and c: "cert_typ alg ar (tnorm (tyenv env) base)" "cert_typ alg ar (tnorm (tyenv env) bary)"
  shows "\<exists>s. okW (projenv cfg vname rb targs u env dps base Ts bvar (Us, bary) targ p tail) s \<and>
    (\<forall>x. ev cfg tail x \<longrightarrow> ev cfg s x) \<and>
    (\<forall>env0 Cs env'. gentvars p env = (env0, Cs) \<longrightarrow> okW (proj_unify cfg base bary Cs env0) env' \<longrightarrow>
      mcp_projel cfg vname env' Ts (Us @ Cs) targs rb u dps bvar targ s)"
proof -
  obtain env0 Cs where g: "gentvars p env = (env0, Cs)" by (cases "gentvars p env")
  note gs = gentvars_simps[OF g]
  have si0: "sinv (A \<union> ntv Cs) (K \<union> ntv Cs) X env0 dps" by (rule sinv_gentvars[OF si g])
  have ei0: "einv (A \<union> ntv Cs) (K \<union> ntv Cs) env0" using si0 by (simp add: sinv_def)
  have cC: "\<forall>C\<in>set Cs. cert_typ alg ar (tnorm (tyenv env0) C)"
    using gs(6) cert_tnorm[OF ei0] by (fastforce simp: cert_typ_def sort_ok_def)
  have pu: "cuok (proj_unify cfg base bary Cs env0) (\<lambda>_. True)"
    by (rule cuok_mono[OF proj_unify_sinv[OF cfg finite_UnI[OF finK finite_ntv] si0]])
      (use tv c cC gs(2) in \<open>auto simp: ntv_def\<close>)
  then consider (cu) evs where "proj_unify cfg base bary Cs env0 = Some (evs, UErr CANTUNIFY)"
    | (ok) env' where "okW (proj_unify cfg base bary Cs env0) env'"
    unfolding cuok_def by blast
  then show ?thesis
  proof cases
    case cu
    have "okW (projenv cfg vname rb targs u env dps base Ts bvar (Us, bary) targ p tail) tail"
      using cu by (simp add: projenv_def g bindW_def handleW_def returnW_def)
    moreover have "\<not> okW (proj_unify cfg base bary Cs env0) env'" for env' using cu by simp
    ultimately show ?thesis using g by (intro exI[of _ tail]) auto
  next
    case ok
    let ?s = "S_Proj vname env' Ts (Us @ Cs) targs rb u dps bvar targ tail"
    have "okW (projenv cfg vname rb targs u env dps base Ts bvar (Us, bary) targ p tail) ?s"
      using ok by (auto simp: projenv_def g okW_handleW)
    moreover have "ev cfg tail x \<Longrightarrow> ev cfg ?s x" for x by (rule ev.proj_tail)
    moreover have "mcp_projel cfg vname env'' Ts (Us @ Cs) targs rb u dps bvar targ ?s"
      if "okW (proj_unify cfg base bary Cs env0) env''" for env''
      using okW_det[OF ok that] mcp_projel_Proj by blast
    ultimately show ?thesis using g by (intro exI[of _ ?s]) auto
  qed
qed

lemma mcp_foldr_projenv:
  assumes cfg: "cfg_alg cfg = alg" and finK: "finite K" and si: "sinv A K X env dps"
    and tv: "tvars base \<subseteq> tvars_env (tyenv env) \<union> A" "tvars bary \<subseteq> tvars_env (tyenv env) \<union> A"
    and c: "cert_typ alg ar (tnorm (tyenv env) base)" "cert_typ alg ar (tnorm (tyenv env) bary)"
  shows "\<exists>s. okW (foldrW (projenv cfg vname rb targs u env dps base Ts bvar (Us, bary) targ) ps tail) s \<and>
    (\<forall>x. ev cfg tail x \<longrightarrow> ev cfg s x) \<and>
    (\<forall>p\<in>set ps. \<forall>env0 Cs env'. gentvars p env = (env0, Cs) \<longrightarrow> okW (proj_unify cfg base bary Cs env0) env' \<longrightarrow>
      mcp_projel cfg vname env' Ts (Us @ Cs) targs rb u dps bvar targ s)"
proof (induction ps)
  case Nil
  show ?case by (intro exI[of _ tail]) (simp add: returnW_def)
next
  case (Cons p ps)
  from Cons.IH obtain s0 where s0: "okW (foldrW (projenv cfg vname rb targs u env dps base Ts bvar (Us, bary) targ) ps tail) s0"
    "\<forall>x. ev cfg tail x \<longrightarrow> ev cfg s0 x"
    "\<forall>p\<in>set ps. \<forall>env0 Cs env'. gentvars p env = (env0, Cs) \<longrightarrow> okW (proj_unify cfg base bary Cs env0) env' \<longrightarrow>
      mcp_projel cfg vname env' Ts (Us @ Cs) targs rb u dps bvar targ s0" by blast
  from mcp_projenv[OF cfg finK si tv c, of vname rb targs u Ts bvar Us targ p s0] obtain s where
    s: "okW (projenv cfg vname rb targs u env dps base Ts bvar (Us, bary) targ p s0) s"
    "\<forall>x. ev cfg s0 x \<longrightarrow> ev cfg s x"
    "\<forall>env0 Cs env'. gentvars p env = (env0, Cs) \<longrightarrow> okW (proj_unify cfg base bary Cs env0) env' \<longrightarrow>
      mcp_projel cfg vname env' Ts (Us @ Cs) targs rb u dps bvar targ s" by blast
  show ?case
  proof (rule exI[of _ s], intro conjI)
    show "okW (foldrW (projenv cfg vname rb targs u env dps base Ts bvar (Us, bary) targ) (p # ps) tail) s"
      using s0(1) s(1) by auto
    show "\<forall>x. ev cfg tail x \<longrightarrow> ev cfg s x" using s0(2) s(2) by blast
    show "\<forall>q\<in>set (p # ps). \<forall>env0 Cs env'. gentvars q env = (env0, Cs) \<longrightarrow> okW (proj_unify cfg base bary Cs env0) env' \<longrightarrow>
      mcp_projel cfg vname env' Ts (Us @ Cs) targs rb u dps bvar targ s"
      using s0(3) s(2,3) mcp_projel_mono by (metis set_ConsD)
  qed
qed

text \<open>The sequence of \<^const>\<open>matchfun\<close> contains the imitation and the projections with all guesses:\<close>

lemma mcp_matchfun:
  assumes cfg: "cfg_alg cfg = alg" and finK: "finite K" and si: "sinv A K X env dps"
    and tvb: "tvars base \<subseteq> tvars_env (tyenv env) \<union> A" and cb: "cert_typ alg ar (tnorm (tyenv env) base)"
    and tvT: "\<forall>(bvar, T, targ)\<in>set projs. tvars T \<subseteq> tvars_env (tyenv env) \<union> A \<and> cert_typ alg ar (tnorm (tyenv env) T)"
  shows "\<exists>sq. okW (matchfun cfg vname rb targs u env dps uhead uargs base Ts projs) sq \<and>
    (\<forall>x. ev cfg (case uhead of
        Const _ _ \<Rightarrow> S_MapJoin uhead (copyargs vname rb targs env dps uargs)
      | Free _ _ \<Rightarrow> S_MapJoin uhead (copyargs vname rb targs env dps uargs)
      | _ \<Rightarrow> S_Empty) x \<longrightarrow> ev cfg sq x) \<and>
    (\<forall>(bvar, T, targ)\<in>set projs. \<forall>Us bary. ok (strip_type env T) (Us, bary) \<longrightarrow>
      (\<forall>p\<in>set (arity_guesses cfg bary). \<forall>env0 Cs env'. gentvars p env = (env0, Cs) \<longrightarrow>
        okW (proj_unify cfg base bary Cs env0) env' \<longrightarrow>
        mcp_projel cfg vname env' Ts (Us @ Cs) targs rb u dps bvar targ sq))"
  using tvT
proof (induction projs)
  case Nil
  show ?case by (intro exI conjI) (auto simp: returnW_def)
next
  case (Cons q projs)
  obtain bvar T targ where q: "q = (bvar, T, targ)" by (cases q)
  have ei: "einv A K env" using si by (simp add: sinv_def)
  from Cons.prems q have tT: "tvars T \<subseteq> tvars_env (tyenv env) \<union> A" and cT: "cert_typ alg ar (tnorm (tyenv env) T)"
    by auto
  from Cons.IH Cons.prems obtain s0 where s0: "okW (matchfun cfg vname rb targs u env dps uhead uargs base Ts projs) s0"
    "\<forall>x. ev cfg (case uhead of
        Const _ _ \<Rightarrow> S_MapJoin uhead (copyargs vname rb targs env dps uargs)
      | Free _ _ \<Rightarrow> S_MapJoin uhead (copyargs vname rb targs env dps uargs)
      | _ \<Rightarrow> S_Empty) x \<longrightarrow> ev cfg s0 x"
    "\<forall>(bvar, T, targ)\<in>set projs. \<forall>Us bary. ok (strip_type env T) (Us, bary) \<longrightarrow>
      (\<forall>p\<in>set (arity_guesses cfg bary). \<forall>env0 Cs env'. gentvars p env = (env0, Cs) \<longrightarrow>
        okW (proj_unify cfg base bary Cs env0) env' \<longrightarrow>
        mcp_projel cfg vname env' Ts (Us @ Cs) targs rb u dps bvar targ s0)" by auto
  from binder_types_term[OF einvD(2)[OF ei] refl tT] obtain Us where bU: "binder_types env T = return Us" by blast
  from body_type_term[OF einvD(2)[OF ei] refl tT] obtain bary where
    bB: "body_type env T = return bary" "tvars bary \<subseteq> tvars_env (tyenv env) \<union> A" by blast
  have sT: "strip_type env T = return (Us, bary)" using bU bB by (simp add: strip_type_def)
  have cbary: "cert_typ alg ar (tnorm (tyenv env) bary)"
  proof -
    have "tsubst (rho0 env) T = map (tsubst (rho0 env)) Us \<Rrightarrow> tsubst (rho0 env) bary"
      by (rule strip_type_sound[OF sT[unfolded return_def] einv_rho0(1)[OF ei]])
    with cT show ?thesis by (simp add: cert_typ_funs)
  qed
  from mcp_foldr_projenv[OF cfg finK si tvb bB(2) cb cbary, of vname rb targs u Ts bvar Us targ
      "arity_guesses cfg bary" s0]
  obtain s where s: "okW (foldrW (projenv cfg vname rb targs u env dps base Ts bvar (Us, bary) targ)
      (arity_guesses cfg bary) s0) s" "\<forall>x. ev cfg s0 x \<longrightarrow> ev cfg s x"
    "\<forall>p\<in>set (arity_guesses cfg bary). \<forall>env0 Cs env'. gentvars p env = (env0, Cs) \<longrightarrow>
      okW (proj_unify cfg base bary Cs env0) env' \<longrightarrow> mcp_projel cfg vname env' Ts (Us @ Cs) targs rb u dps bvar targ s"
    by blast
  show ?case
  proof (rule exI[of _ s], intro conjI)
    show "okW (matchfun cfg vname rb targs u env dps uhead uargs base Ts (q # projs)) s"
      using s0(1) s(1) sT by (auto simp: q return_def)
    show "\<forall>x. ev cfg (case uhead of
        Const _ _ \<Rightarrow> S_MapJoin uhead (copyargs vname rb targs env dps uargs)
      | Free _ _ \<Rightarrow> S_MapJoin uhead (copyargs vname rb targs env dps uargs)
      | _ \<Rightarrow> S_Empty) x \<longrightarrow> ev cfg s x" using s0(2) s(2) by blast
    show "\<forall>(bvar, T, targ)\<in>set (q # projs). \<forall>Us bary. ok (strip_type env T) (Us, bary) \<longrightarrow>
      (\<forall>p\<in>set (arity_guesses cfg bary). \<forall>env0 Cs env'. gentvars p env = (env0, Cs) \<longrightarrow>
        okW (proj_unify cfg base bary Cs env0) env' \<longrightarrow>
        mcp_projel cfg vname env' Ts (Us @ Cs) targs rb u dps bvar targ s)"
    proof (intro ballI)
      fix q' assume "q' \<in> set (q # projs)"
      then consider "q' = q" | "q' \<in> set projs" by auto
      note c = this
      obtain bvar' T' targ' where q': "q' = (bvar', T', targ')" by (cases q')
      show "case q' of (bvar, T, targ) \<Rightarrow> \<forall>Us bary. ok (strip_type env T) (Us, bary) \<longrightarrow>
        (\<forall>p\<in>set (arity_guesses cfg bary). \<forall>env0 Cs env'. gentvars p env = (env0, Cs) \<longrightarrow>
          okW (proj_unify cfg base bary Cs env0) env' \<longrightarrow>
          mcp_projel cfg vname env' Ts (Us @ Cs) targs rb u dps bvar targ s)"
        unfolding q' prod.case
      proof (intro allI impI ballI)
      fix Us' bary' p env0 Cs env'
      assume st: "ok (strip_type env T') (Us', bary')" and p: "p \<in> set (arity_guesses cfg bary')"
        and g: "gentvars p env = (env0, Cs)" and pu: "okW (proj_unify cfg base bary' Cs env0) env'"
      from c show "mcp_projel cfg vname env' Ts (Us' @ Cs) targs rb u dps bvar' targ' s"
      proof cases
        case 1
        with q q' have e: "bvar' = bvar" "T' = T" "targ' = targ" by auto
        with st sT have "Us' = Us" "bary' = bary" by (simp_all add: return_def)
        with s(3) p g pu e show ?thesis by blast
      next
        case 2
        with s0(3) q' st p g pu have "mcp_projel cfg vname env' Ts (Us' @ Cs) targs rb u dps bvar' targ' s0" by fastforce
        then show ?thesis by (rule mcp_projel_mono) (use s(2) in blast)
      qed
      qed
    qed
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
  have l: "length Ts = length targs" using mf_make_projs_props[OF ps'] by simp
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
  unfolding ncu_def cuok_def by blast

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
  shows "types_abs Ss b \<degree>\<degree> mbvs (length Ss) \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> b"
    "pushes e Ss \<turnstile> types_abs Ss b \<degree>\<degree> mbvs (length Ss) : B"
proof -
  have tv: "e' \<turnstile> types_abs Ss b : Ss \<Rrightarrow> B" for e' by (rule mcp_typing_val[OF ty lb c])
  show t: "pushes e Ss \<turnstile> types_abs Ss b \<degree>\<degree> mbvs (length Ss) : B"
    by (rule list_app_typeI[OF tv mf_typings_bvs])
  have t0: "pushes mcp_e0 Ss \<turnstile> types_abs Ss b \<degree>\<degree> mbvs (length Ss) : B"
    by (rule list_app_typeI[OF tv mf_typings_bvs])
  have t1: "mcp_e0 \<turnstile> types_abs Ss (types_abs Ss b \<degree>\<degree> mbvs (length Ss)) : Ss \<Rrightarrow> B"
    by (rule mf_typing_types_abs[OF t0 c])
  have "types_abs Ss (types_abs Ss b \<degree>\<degree> mbvs (length Ss)) \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> types_abs Ss b"
    by (rule mcp_conv_eta_types_abs[OF mcp_closed_types_abs[OF lb]]) (use t1 in \<open>auto simp: wt_def\<close>)
  from mcp_conv_types_abs_inv[OF t1 mf_typing_types_abs[OF ty c] this] show "types_abs Ss b \<degree>\<degree> mbvs (length Ss) \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> b" .
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
    using mf_radixstring_inj[of "integer_of_nat n" "integer_of_nat n'"]
    by (simp add: mf_plus_literal_cancel integer_of_nat_eq_of_nat)
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
  assumes ma: "make_args name Ts env Us = (env', args)" and a: "args = map (\<lambda>G. G \<degree>\<degree> mbvs (length Ts)) Gs"
  shows "distinct (map mf_var_of Gs)"
proof (cases "Us = []")
  case True
  with ma a show ?thesis by (simp add: make_args_def)
next
  case False
  obtain env1 vs where g: "genvars name env (map (\<lambda>T. Ts \<Rrightarrow> T) Us) = (env1, vs)" by fastforce
  with ma False have "args = map (\<lambda>var. combound var 0 (length Ts)) vs"
    by (auto simp: make_args_def List.null_iff)
  with a have "map (\<lambda>G. G \<degree>\<degree> mbvs (length Ts)) Gs = map (\<lambda>G. G \<degree>\<degree> mbvs (length Ts)) vs"
    by (simp add: mf_combound_bvs)
  then have "Gs = vs" by (simp add: inj_map_eq_map inj_on_def mcp_apps_inj)
  with mf_genvars_props(5)[OF g] show ?thesis by simp
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
  from t obtain r where r: "SIMPL alg env dps = Some r" unfolding cuok_def by auto
  note c = SIMPL_complete[OF r fin si inv]
  from t c(1) r obtain st where ok: "okW (SIMPL alg env dps) st" "simpl_post A K X env st"
    unfolding cuok_def by auto
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

lemma mcp_dstep_same:
  assumes "tenv env' = tenv env" "tyenv env' = tyenv env" "maxidx env \<le> maxidx env'"
  shows "dstep env dps env' dps"
proof (rule dstepI)
  show ext: "extends env env'" using assms by (simp add: extends_def)
  fix \<rho> env'' X assume "wt_env \<rho> env" "dtyped \<rho> dps" "vinv \<rho> env (X \<union> dvars dps)"
  then show "wt_env \<rho> env' \<and> dtyped \<rho> dps \<and> vinv \<rho> env' (X \<union> dvars dps) \<and>
      (\<forall>\<sigma>. solution \<rho> \<sigma> env'' \<longrightarrow> dsolved \<rho> \<sigma> dps \<longrightarrow> dsolved \<rho> \<sigma> dps)"
    using wt_env_tenv[OF assms(1)] vinv_tenv[OF assms(1) ext] by blast
qed

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

lemma mcp_Gs_unique: "map (\<lambda>G. G \<degree>\<degree> bs) Gs = map (\<lambda>G. G \<degree>\<degree> bs) Gs' \<Longrightarrow> Gs = Gs'"
  by (simp add: inj_map_eq_map inj_on_def mcp_apps_inj)

lemma mcp_wft_inst: "cert_typ alg ar (tsubst \<rho> T) \<Longrightarrow> wft ar T"
  by (rule wft_tsubstD[where \<rho> = \<rho>]) (simp add: cert_typ_def)

lemma mcp_solution_tenv:
  "solution \<rho> \<sigma> env \<Longrightarrow> tenv env' = tenv env \<Longrightarrow> tyenv env' = tyenv env \<Longrightarrow> solution \<rho> \<sigma> env'"
  by (simp add: solution_def)

lemma mcp_extends_same:
  "tenv env' = tenv env \<Longrightarrow> tyenv env' = tyenv env \<Longrightarrow> maxidx env \<le> maxidx env' \<Longrightarrow> extends env env'"
  by (simp add: extends_def)

lemma mcp_typings_nthI:
  "length ts = length Us \<Longrightarrow> (\<And>l. l < length ts \<Longrightarrow> e \<turnstile> ts ! l : Us ! l) \<Longrightarrow> e \<tturnstile> ts : Us"
  unfolding mf_typings_iff by (rule list_all2_all_nthI) auto



subsection \<open>Copies: projections\<close>

text \<open>
  \<^const>\<open>SIMPL\<close> binds only variables of the problem and adds no new unbound ones (by the
  reachability lemma @{thm [source] SIMPL_vreach} of \<open>Unify_Mc_Fin\<close>):
\<close>

lemma mcp_sstepD:
  assumes "sstep K X env env'"
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
    using SIMPL_term[OF fin si] ok unfolding cuok_def by auto
  then have ext: "extends env env'" by (simp add: simpl_post_def sstep_def)
  from ok obtain r where r: "SIMPL alg env dps = Some r" "snd r = UOk (env', ffs, frs)" by auto
  have vs: "vsr (vdps dps) (env, [], []) (env', ffs, frs)" by (rule SIMPL_vreach[OF r])
  have D: "vdps dps \<subseteq> fst ` (X \<union> evars env)"
  proof
    fix y assume "y \<in> vdps dps"
    then obtain rb t u where "(rb, t, u) \<in> set dps" "y \<in> vns t \<union> vns u" by auto
    moreover have "pok A env rb X t u" if "(rb, t, u) \<in> set dps" using si that by (auto simp: sinv_def)
    ultimately show "y \<in> fst ` (X \<union> evars env)" using pokD(1,2) by blast
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

lemma mcp_norm_satd: "ok (head_norm env t) u1 \<Longrightarrow> ok (eta_norm env rb u1) u2 \<Longrightarrow> satd env rb u2"
  by (rule head_norm_eta_norm_satd)


lemma mcp_cresI:
  assumes "x = El_C u' env' dps'" "finite X'" "finite K'" "A \<subseteq> A'" "K \<subseteq> K'" "X \<subseteq> X'"
    "sinv A' K' X' env' dps'" "scinv \<rho>' \<sigma>' env' dps' X' A'" "extends env env'"
    "tvars_env (tyenv env) \<subseteq> tvars_env (tyenv env')" "tagree (maxidx env) \<rho> \<rho>'" "sagree (maxidx env) \<sigma> \<sigma>'"
    "vars u' \<subseteq> X' \<union> evars env'" "ttvars u' \<subseteq> tvars_env (tyenv env') \<union> A'" "\<not> loose_bvar u' (ilength Ss)"
    "\<forall>\<rho>0 e Us U. tsol (tyenv env') \<rho>0 \<longrightarrow> cert_inst \<rho>0 \<longrightarrow> bs_env \<rho>0 e rb \<longrightarrow>
      e \<tturnstile> map (inst \<rho>0) targs : Us \<longrightarrow> e \<turnstile> inst \<rho>0 u : U \<longrightarrow> (\<forall>e'. pushes e' Us \<turnstile> inst \<rho>0 u' : U)"
    "pushes mcp_e0 Ss \<turnstile> inst \<rho>' u' : UU" "types_abs Ss (ap \<rho>' \<sigma>' u') \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> types_abs Ss s"
    "finite NV" "NV \<subseteq> X'" "\<forall>y\<in>NV. maxidx env < snd (fst y)" "ubv env' X' \<subseteq> ubv env X \<union> fst ` NV"
    "(\<Sum>y\<in>NV. mcp_vsz \<rho>' \<sigma>' y) + m \<le> lsz (pushes mcp_e0 Ss) s - 2 * arity UU"
    "\<forall>k. mcp_kokK k \<rho> (tyenv env) A K \<longrightarrow> mcp_kokK k \<rho>' (tyenv env') A' K'"
  shows "mcp_cres A K X env rb targs u \<rho> \<sigma> Ss UU s m x"
  unfolding mcp_cres_def
  by (rule exI[of _ u'], rule exI[of _ env'], rule exI[of _ dps'], rule exI[of _ A'], rule exI[of _ K'],
      rule exI[of _ X'], rule exI[of _ \<rho>'], rule exI[of _ \<sigma>'], rule exI[of _ NV]) (intro conjI; fact)

lemma mcp_cresE:
  assumes "mcp_cres A K X env rb targs u \<rho> \<sigma> Ss UU s m x"
  obtains u' env' dps' A' K' X' \<rho>' \<sigma>' NV where "x = El_C u' env' dps'" "finite X'" "finite K'" "A \<subseteq> A'" "K \<subseteq> K'" "X \<subseteq> X'"
    "sinv A' K' X' env' dps'" "scinv \<rho>' \<sigma>' env' dps' X' A'" "extends env env'"
    "tvars_env (tyenv env) \<subseteq> tvars_env (tyenv env')" "tagree (maxidx env) \<rho> \<rho>'" "sagree (maxidx env) \<sigma> \<sigma>'"
    "vars u' \<subseteq> X' \<union> evars env'" "ttvars u' \<subseteq> tvars_env (tyenv env') \<union> A'" "\<not> loose_bvar u' (ilength Ss)"
    "\<forall>\<rho>0 e Us U. tsol (tyenv env') \<rho>0 \<longrightarrow> cert_inst \<rho>0 \<longrightarrow> bs_env \<rho>0 e rb \<longrightarrow>
      e \<tturnstile> map (inst \<rho>0) targs : Us \<longrightarrow> e \<turnstile> inst \<rho>0 u : U \<longrightarrow> (\<forall>e'. pushes e' Us \<turnstile> inst \<rho>0 u' : U)"
    "pushes mcp_e0 Ss \<turnstile> inst \<rho>' u' : UU" "types_abs Ss (ap \<rho>' \<sigma>' u') \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> types_abs Ss s"
    "finite NV" "NV \<subseteq> X'" "\<forall>y\<in>NV. maxidx env < snd (fst y)" "ubv env' X' \<subseteq> ubv env X \<union> fst ` NV"
    "(\<Sum>y\<in>NV. mcp_vsz \<rho>' \<sigma>' y) + m \<le> lsz (pushes mcp_e0 Ss) s - 2 * arity UU"
    "\<forall>k. mcp_kokK k \<rho> (tyenv env) A K \<longrightarrow> mcp_kokK k \<rho>' (tyenv env') A' K'"
  using assms unfolding mcp_cres_def by (elim exE conjE) (rule that; assumption)

lemma mcp_cres_m0: "mcp_cres A K X env rb targs u \<rho> \<sigma> Ss UU s m x \<Longrightarrow> mcp_cres A K X env rb targs u \<rho> \<sigma> Ss UU s 0 x"
  by (elim mcp_cresE, rule mcp_cresI; assumption?) linarith

lemma mcp_cres_u:
  assumes c: "mcp_cres A K X env rb targs u2 \<rho> \<sigma> Ss UU s m x"
    and ty: "\<And>\<rho>0 e0 U. tsol (tyenv env) \<rho>0 \<Longrightarrow> cert_inst \<rho>0 \<Longrightarrow> bs_env \<rho>0 e0 rb \<Longrightarrow> e0 \<turnstile> inst \<rho>0 a : U \<Longrightarrow>
      e0 \<turnstile> inst \<rho>0 u2 : U"
  shows "mcp_cres A K X env rb targs a \<rho> \<sigma> Ss UU s m x"
  using c
proof (rule mcp_cresE)
  fix u' env' dps' A' K' X' \<rho>' \<sigma>' NV
  assume P: "x = El_C u' env' dps'" "finite X'" "finite K'" "A \<subseteq> A'" "K \<subseteq> K'" "X \<subseteq> X'"
    "sinv A' K' X' env' dps'" "scinv \<rho>' \<sigma>' env' dps' X' A'" "extends env env'"
    "tvars_env (tyenv env) \<subseteq> tvars_env (tyenv env')" "tagree (maxidx env) \<rho> \<rho>'" "sagree (maxidx env) \<sigma> \<sigma>'"
    "vars u' \<subseteq> X' \<union> evars env'" "ttvars u' \<subseteq> tvars_env (tyenv env') \<union> A'" "\<not> loose_bvar u' (ilength Ss)"
    and T: "\<forall>\<rho>0 e Us U. tsol (tyenv env') \<rho>0 \<longrightarrow> cert_inst \<rho>0 \<longrightarrow> bs_env \<rho>0 e rb \<longrightarrow>
      e \<tturnstile> map (inst \<rho>0) targs : Us \<longrightarrow> e \<turnstile> inst \<rho>0 u2 : U \<longrightarrow> (\<forall>e'. pushes e' Us \<turnstile> inst \<rho>0 u' : U)"
    and Q: "pushes mcp_e0 Ss \<turnstile> inst \<rho>' u' : UU" "types_abs Ss (ap \<rho>' \<sigma>' u') \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> types_abs Ss s"
    "finite NV" "NV \<subseteq> X'" "\<forall>y\<in>NV. maxidx env < snd (fst y)" "ubv env' X' \<subseteq> ubv env X \<union> fst ` NV"
    "(\<Sum>y\<in>NV. mcp_vsz \<rho>' \<sigma>' y) + m \<le> lsz (pushes mcp_e0 Ss) s - 2 * arity UU"
    "\<forall>k. mcp_kokK k \<rho> (tyenv env) A K \<longrightarrow> mcp_kokK k \<rho>' (tyenv env') A' K'"
  have T': "\<forall>\<rho>0 e Us U. tsol (tyenv env') \<rho>0 \<longrightarrow> cert_inst \<rho>0 \<longrightarrow> bs_env \<rho>0 e rb \<longrightarrow>
        e \<tturnstile> map (inst \<rho>0) targs : Us \<longrightarrow> e \<turnstile> inst \<rho>0 a : U \<longrightarrow> (\<forall>e'. pushes e' Us \<turnstile> inst \<rho>0 u' : U)"
  proof (intro allI impI)
    fix \<rho>0 e0 Us U e' assume a: "tsol (tyenv env') \<rho>0" "cert_inst \<rho>0" "bs_env \<rho>0 e0 rb"
      "e0 \<tturnstile> map (inst \<rho>0) targs : Us" "e0 \<turnstile> inst \<rho>0 a : U"
    have "tsol (tyenv env) \<rho>0" by (rule extends_tsol[OF a(1) P(9)])
    from ty[OF this a(2,3,5)] T a show "pushes e' Us \<turnstile> inst \<rho>0 u' : U" by blast
  qed
  show ?thesis by (rule mcp_cresI[OF P T' Q])
qed

text \<open>
  The element of a projection or an imitation with new variables for the arguments, after the type
  unification of a projection: the new variables get the arguments \<open>bs\<close> of the target as values.
  The element is in the invariants for every later state (of \<^const>\<open>SIMPL\<close> in \<^const>\<open>mc\<close>, or none
  in \<^const>\<open>match1\<close>) that keeps the solution of the new variables.
\<close>

lemma mcp_args_elem:
  assumes pre: "mcp_pre A K X env dps rb targs u" and sp: "mcp_spre \<rho> \<sigma> env dps X A e rb targs Ss u UU s"
    and ty0: "ok (fastype env rb (fst (strip_comb u))) T0" "ok (body_type env T0) base"
      "ok (mapM (fastype env rb) targs) Ts"
    and na: "\<not> is_Abs (fst (strip_comb u))"
    and si': "sinv A' K' X env' dps" and inv2: "scinv \<rho>2 \<sigma> env' dps X A'" and finK': "finite K'"
    and AK: "A \<subseteq> A'" "K \<subseteq> K'"
    and ext: "extends env env'" "tenv env' = tenv env" "tvars_env (tyenv env) \<subseteq> tvars_env (tyenv env')"
    and ag: "tagree (maxidx env) \<rho> \<rho>2"
    and kk: "\<forall>k. mcp_kokK k \<rho> (tyenv env) A K \<longrightarrow> mcp_kokK k \<rho>2 (tyenv env') A' K'"
    and \<rho>2Ts: "map (tsubst \<rho>2) Ts = Ss" and tvTs: "\<forall>T\<in>set Ts. tvars T \<subseteq> tvars_env (tyenv env') \<union> A'"
    and UC: "map (tsubst \<rho>2) UC = Bts" "\<forall>U\<in>set UC. tvars U \<subseteq> tvars_env (tyenv env') \<union> A'"
    and cB: "\<forall>B\<in>set Bts. cert_typ alg ar B"
    and sh: "s = inst \<rho>2 h \<degree>\<degree> bs" "pushes mcp_e0 Ss \<turnstile> inst \<rho>2 h : Bts \<Rrightarrow> UU" "pushes mcp_e0 Ss \<tturnstile> bs : Bts"
    and h: "rigid h" "vars h = {}" "ttvars h \<subseteq> tvars_env (tyenv env') \<union> A'" "\<not> loose_bvar h (ilength Ss)"
    and hty: "\<And>\<rho>0 e0 Us0 U0. tsol (tyenv env') \<rho>0 \<Longrightarrow> cert_inst \<rho>0 \<Longrightarrow> bs_env \<rho>0 e0 rb \<Longrightarrow>
      e0 \<tturnstile> map (inst \<rho>0) targs : Us0 \<Longrightarrow> e0 \<turnstile> inst \<rho>0 u : U0 \<Longrightarrow>
      (\<forall>e'. pushes e' Us0 \<turnstile> inst \<rho>0 h : map (tsubst \<rho>0) UC \<Rrightarrow> U0) \<and> (\<forall>U\<in>set UC. cert_typ alg ar (tsubst \<rho>0 U))"
    and ma: "make_args vname Ts env' UC = (env'', args)"
  obtains Gs \<sigma>3 where "args = map (\<lambda>G. G \<degree>\<degree> mbvs (length Ts)) Gs"
    "list_all2 (\<lambda>G U. \<exists>x. G = Var x (Ts \<Rrightarrow> U)) Gs UC"
    "tenv env'' = tenv env'" "tyenv env'' = tyenv env'" "maxidx env' \<le> maxidx env''"
    "\<forall>G\<in>set Gs. \<exists>a U. G = Var (a, maxidx env' + 1) U"
    "sinv A' K' (mlvars Gs \<union> X) env'' dps" "vtvars (mlvars Gs) \<subseteq> tvars_env (tyenv env') \<union> A'"
    "scinv \<rho>2 \<sigma>3 env'' dps (mlvars Gs \<union> X) A'" "sagree (maxidx env') \<sigma> \<sigma>3"
    "length Gs = length bs" "\<And>l. l < length Gs \<Longrightarrow> ap \<rho>2 \<sigma>3 (Gs ! l) = types_abs Ss (bs ! l)"
    "\<And>env2 dps2 \<rho>4 \<sigma>4. sinv A' K' (mlvars Gs \<union> X) env2 dps2 \<Longrightarrow> scinv \<rho>4 \<sigma>4 env2 dps2 (mlvars Gs \<union> X) A' \<Longrightarrow>
      tagree (maxidx env'') \<rho>2 \<rho>4 \<Longrightarrow> sagree (maxidx env'') \<sigma>3 \<sigma>4 \<Longrightarrow> extends env'' env2 \<Longrightarrow>
      tvars_env (tyenv env'') \<subseteq> tvars_env (tyenv env2) \<Longrightarrow> ubv env2 (mlvars Gs \<union> X) \<subseteq> ubv env'' (mlvars Gs \<union> X) \<Longrightarrow>
      (\<forall>k. mcp_kokK k \<rho>2 (tyenv env'') A' K' \<longrightarrow> mcp_kokK k \<rho>4 (tyenv env2) A' K') \<Longrightarrow>
      mcp_cres A K X env rb targs u \<rho> \<sigma> Ss UU s 1 (El_C (list_comb h args) env2 dps2)"
proof -
  from pre have finX: "finite X" unfolding mcp_pre_def by blast
  from sp have inv: "scinv \<rho> \<sigma> env dps X A" and bs: "bs_env \<rho> e rb"
    and tyt: "e \<tturnstile> map (inst \<rho>) targs : Ss" and tyu: "e \<turnstile> inst \<rho> u : UU" and ar: "arity UU = nabs u"
    and tys: "pushes mcp_e0 Ss \<turnstile> s : UU" and nrs: "no_redex s" and lbs: "\<not> loose_bvar s (ilength Ss)"
    unfolding mcp_spre_def by blast+
  note sd = solutionD[OF scinvD(1)[OF inv]] and i2 = scinvD[OF inv2]
  note ts = mcp_types_sound[OF pre ty0 na]
  note ts\<rho> = ts[OF sd(2) bs tyt tyu]
  have u: "u = fst (strip_comb u) \<degree>\<degree> snd (strip_comb u)" by (rule strip_comb_apps) simp
  have ar0: "arity UU = 0"
  proof -
    have "\<not> is_Abs u" using na u is_Abs_apps by metis
    then show ?thesis using ar by simp
  qed
  have mx: "maxidx env \<le> maxidx env'" using ext(1) by (simp add: extends_def)
  have tsol\<theta>: "tsol (tyenv env) \<rho>'" if "tsol (tyenv env') \<rho>'" for \<rho>' by (rule extends_tsol[OF that ext(1)])
  have rh': "rigid (inst \<rho>2 h)" using h(1) by (cases h) auto
  have lbs_arg: "\<forall>b\<in>set bs. \<not> loose_bvar b (ilength Ss)" using lbs sh(1) by (simp add: loose_bvar_apps)
  have nr_arg: "\<forall>b\<in>set bs. no_redex b"
    using nrs sh(1) no_redex_apps[of "inst \<rho>2 h" bs] rh' by (cases "inst \<rho>2 h") auto
  have lbs': "length bs = length Bts" using typings_nth[OF sh(3)] by simp
  obtain Gs where args: "args = map (\<lambda>G. G \<degree>\<degree> mbvs (length Ts)) Gs"
    and GU: "list_all2 (\<lambda>G U. \<exists>x. G = Var x (Ts \<Rrightarrow> U)) Gs UC"
    and ma': "tenv env'' = tenv env'" "tyenv env'' = tyenv env'" "maxidx env' \<le> maxidx env''"
    and Gi: "\<forall>G\<in>set Gs. \<exists>a U. G = Var (a, maxidx env' + 1) U"
    and si'': "sinv A' K' (mlvars Gs \<union> X) env'' dps"
    and vG: "vtvars (mlvars Gs) \<subseteq> tvars_env (tyenv env') \<union> A'"
    by (rule sinv_make_args[OF si' ma tvTs UC(2)])
  obtain Gs' where args': "args = map (\<lambda>G. G \<degree>\<degree> mbvs (length Ts)) Gs'"
    and vtr: "\<And>\<rho> X. vinv \<rho> env' X \<Longrightarrow> vinv \<rho> env'' (mlvars Gs' \<union> X)"
    by (rule mf_make_args_props[OF ma]) blast
  have "Gs' = Gs" using args args' by (metis mcp_Gs_unique)
  with vtr have vtr: "\<And>\<rho> X. vinv \<rho> env' X \<Longrightarrow> vinv \<rho> env'' (mlvars Gs \<union> X)" by simp
  have dist: "distinct (map mf_var_of Gs)" by (rule mcp_make_args_distinct[OF ma args])
  let ?q = "length Gs"
  have lq: "?q = length UC" by (rule list_all2_lengthD[OF GU])
  have lqb: "?q = length bs" using lq UC(1) lbs' by (metis length_map)
  define xs where "xs = map mf_var_of Gs"
  have Gl: "Gs ! l = Var (xs ! l) (Ts \<Rrightarrow> (UC ! l))" if "l < ?q" for l
  proof -
    from list_all2_nthD[OF GU that] obtain x where "Gs ! l = Var x (Ts \<Rrightarrow> (UC ! l))" by blast
    then show ?thesis using that by (simp add: xs_def)
  qed
  have xidx: "snd (xs ! l) = maxidx env' + 1" if "l < ?q" for l
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
    from mcp_typing_val[OF this] lbs_arg ts\<rho>(3) l show ?thesis using that by (simp add: ws_def ysi_def)
  qed
  have cw: "\<forall>w\<in>set ws. closed w" using lbs_arg by (auto simp: ws_def mcp_closed_types_abs)
  have nys: "\<forall>y\<in>set ysi. maxidx env' < snd (fst y)" using xidx by (auto simp: ysi_def)
  have su: "solution \<rho>2 \<sigma>3 env'" "sagree (maxidx env') \<sigma> \<sigma>3" "wt_subst \<sigma>3"
    unfolding \<sigma>3_def by (rule mcp_solution_supds[OF i2(1) i2(3) nys cw]; blast intro: tyw)+
  have \<sigma>3l: "\<sigma>3 (xs ! l) (Ss \<Rrightarrow> (Bts ! l)) = types_abs Ss (bs ! l)" if "l < ?q" for l
    using mcp_supds_nth[OF dys, of ws l \<sigma>] lys that lqb by (simp add: \<sigma>3_def ysi_def ws_def)
  have \<rho>2Gl: "tsubst \<rho>2 (Ts \<Rrightarrow> (UC ! l)) = Ss \<Rrightarrow> (Bts ! l)" if "l < ?q" for l
    using \<rho>2Ts UC(1) that lq by (simp add: tsubst_funs flip: nth_map[of l UC "tsubst \<rho>2"])
  define X'' where "X'' = mlvars Gs \<union> X"
  have ext'': "extends env' env''" by (rule mcp_extends_same[OF ma'])
  have ev'': "evars env'' = evars env" by (rule evars_tenv) (simp add: ma'(1) ext(2))
  have Gs_eq: "Gs = map (\<lambda>l. Var (xs ! l) (Ts \<Rrightarrow> (UC ! l))) [0..<?q]"
    by (rule nth_equalityI) (simp_all add: Gl)
  have mlG: "mlvars Gs = set (map (\<lambda>l. (xs ! l, Ts \<Rrightarrow> (UC ! l))) [0..<?q])"
    by (subst Gs_eq) auto
  have below'': "tbelow (maxidx env'') S" if "S \<subseteq> tvars_env (tyenv env') \<union> A'" for S
    using tvinv_tbelow[OF einvD(1)[OF conjunct1[OF si''[unfolded sinv_def]]]] that ma'(2) by simp
  have inv3: "scinv \<rho>2 \<sigma>3 env'' dps X'' A'"
    unfolding scinv_def
  proof (intro conjI)
    show "solution \<rho>2 \<sigma>3 env''" by (rule mcp_solution_tenv[OF su(1) ma'(1,2)])
    show "wt_env \<rho>2 env''" using i2(2) wt_env_tenv[OF ma'(1)] by simp
    show "vinv \<rho>2 env'' X''" unfolding X''_def by (rule vtr[OF i2(3)])
    show "tvinv A' env''" using si'' by (simp add: sinv_def einv_def)
    show "vtvars X'' \<subseteq> tvars_env (tyenv env'') \<union> A'" using vG i2(5) ma'(2) by (auto simp: X''_def)
    show "dtyped \<rho>2 dps" by (rule i2(6))
    show "dsolved \<rho>2 \<sigma>3 dps"
      by (rule sc_dps_agree(2)[OF _ i2(4) i2(3) tagree_refl su(2) i2(7)]) (use si' in \<open>simp add: sinv_def\<close>)
  qed
  have apGl: "ap \<rho>2 \<sigma>3 (Gs ! l) = types_abs Ss (bs ! l)" if "l < ?q" for l
    using \<sigma>3l[OF that] \<rho>2Gl[OF that] by (simp add: Gl[OF that])
  show ?thesis
  proof (rule that[OF args GU ma' Gi si'' vG inv3[unfolded X''_def] su(2) lqb apGl])
    fix env2 dps2 \<rho>4 \<sigma>4
    assume si4: "sinv A' K' (mlvars Gs \<union> X) env2 dps2" and inv4: "scinv \<rho>4 \<sigma>4 env2 dps2 (mlvars Gs \<union> X) A'"
      and ag4: "tagree (maxidx env'') \<rho>2 \<rho>4" and sa4: "sagree (maxidx env'') \<sigma>3 \<sigma>4"
      and ext4': "extends env'' env2" and tve4: "tvars_env (tyenv env'') \<subseteq> tvars_env (tyenv env2)"
      and ub4: "ubv env2 (mlvars Gs \<union> X) \<subseteq> ubv env'' (mlvars Gs \<union> X)"
      and kk4: "\<forall>k. mcp_kokK k \<rho>2 (tyenv env'') A' K' \<longrightarrow> mcp_kokK k \<rho>4 (tyenv env2) A' K'"
    note i4 = scinvD[OF inv4]
    have mx'': "maxidx env' \<le> maxidx env''" by (rule ma'(3))
    have ext4: "extends env env2" by (rule extends_trans[OF ext(1) extends_trans[OF ext'' ext4']])
    have ag04: "tagree (maxidx env) \<rho> \<rho>4" by (rule tagree_trans[OF ag ag4]) (use mx mx'' in simp)
    have sa04: "sagree (maxidx env) \<sigma> \<sigma>4"
    proof -
      have "sagree (maxidx env) \<sigma> \<sigma>3" by (rule sagree_trans[OF sagree_refl su(2) mx])
      then show ?thesis by (rule sagree_trans[OF _ sa4]) (use mx mx'' in simp)
    qed
    have tsol4: "tsol (tyenv env') \<rho>4"
      using extends_tsol[OF solutionD(2)[OF i4(1)] ext4'] ma'(2) by simp
    have \<rho>4Ts: "map (tsubst \<rho>4) Ts = Ss"
      using \<rho>2Ts tsubst_agree[OF ag4 below''] tvTs by (simp cong: map_cong)
    have "map (tsubst \<rho>4) UC = map (tsubst \<rho>2) UC"
      by (rule map_cong[OF refl]) (use tsubst_agree[OF ag4 below''] UC(2) in blast)
    then have \<rho>4UC: "map (tsubst \<rho>4) UC = Bts" by (simp add: UC(1))
    have cUC4: "\<forall>U\<in>set UC. cert_typ alg ar (tsubst \<rho>4 U)" using \<rho>4UC cB by (metis image_eqI list.set_map)
    have cTs4: "\<forall>T\<in>set Ts. cert_typ alg ar (tsubst \<rho>4 T)" using \<rho>4Ts ts\<rho>(3) by (metis image_eqI list.set_map)
    have ih4: "inst \<rho>4 h = inst \<rho>2 h" by (rule inst_agree[OF ag4 below''[OF h(3)]])
    define NV where "NV = mlvars Gs"
    have lTsS: "length Ts = length Ss" using ts\<rho>(1) by simp
    have u'e: "list_comb h args = h \<degree>\<degree> map (\<lambda>G. G \<degree>\<degree> mbvs (length Ts)) Gs"
      by (simp add: args list_comb_apps)
    have i3v: "below (maxidx env'') (X'' \<union> evars env'')" using scinvD(3)[OF inv3] by (simp add: vinv_def)
    have ix: "snd (xs ! l) \<le> maxidx env''" if "l < ?q" for l
    proof -
      have "(xs ! l, Ts \<Rrightarrow> (UC ! l)) \<in> X''" using mlG that by (auto simp: X''_def)
      then have "snd (fst (xs ! l, Ts \<Rrightarrow> (UC ! l))) \<le> maxidx env''"
        using i3v unfolding below_def by blast
      then show ?thesis by simp
    qed
    have tvl: "tbelow (maxidx env'') (tvars (Ts \<Rrightarrow> (UC ! l)))" if "l < ?q" for l
    proof (rule below'')
      have "UC ! l \<in> set UC" by (rule nth_mem) (use that lq in simp)
      then show "tvars (Ts \<Rrightarrow> (UC ! l)) \<subseteq> tvars_env (tyenv env') \<union> A'"
        using tvTs UC(2) by (auto simp: tvars_funs)
    qed
    have \<sigma>4l: "\<sigma>4 (xs ! l) (tsubst \<rho>4 (Ts \<Rrightarrow> (UC ! l))) = types_abs Ss (bs ! l)" if "l < ?q" for l
    proof -
      have "tsubst \<rho>4 (Ts \<Rrightarrow> (UC ! l)) = tsubst \<rho>2 (Ts \<Rrightarrow> (UC ! l))"
        by (rule tsubst_agree[OF ag4 tvl[OF that]])
      moreover have "\<sigma>4 (xs ! l) T = \<sigma>3 (xs ! l) T" for T using sa4 ix[OF that] unfolding sagree_def by blast
      ultimately show ?thesis using \<sigma>3l[OF that] \<rho>2Gl[OF that] by simp
    qed
    have apc: "ap \<rho>4 \<sigma>4 (list_comb h args) = inst \<rho>2 h \<degree>\<degree> map (\<lambda>b. types_abs Ss b \<degree>\<degree> mbvs (length Ss)) bs"
    proof -
      have "map (ap \<rho>4 \<sigma>4) (map (\<lambda>G. G \<degree>\<degree> mbvs (length Ts)) Gs) = map (\<lambda>b. types_abs Ss b \<degree>\<degree> mbvs (length Ss)) bs"
        by (rule nth_equalityI) (simp_all add: lqb ap_apps Gl \<sigma>4l lTsS comp_def)
      then show ?thesis by (simp add: u'e ap_apps rigid_ap[OF h(1)] ih4)
    qed
    have tbs: "pushes mcp_e0 Ss \<turnstile> bs ! l : Bts ! l" if "l < length bs" for l
      using typings_nth[OF sh(3)] that by simp
    have tm: "pushes mcp_e0 Ss \<tturnstile> map (\<lambda>b. types_abs Ss b \<degree>\<degree> mbvs (length Ss)) bs : Bts"
      by (rule mcp_typings_nthI) (use mcp_conv_bvs(2)[OF tbs] lbs_arg ts\<rho>(3) lbs' in auto)
    have cvb: "inst \<rho>2 h \<degree>\<degree> map (\<lambda>b. types_abs Ss b \<degree>\<degree> mbvs (length Ss)) bs \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> s"
      unfolding sh(1)
    proof (rule conv_apps[OF _ _ _ conv_refl])
      show "list_all2 (\<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta>) (map (\<lambda>b. types_abs Ss b \<degree>\<degree> mbvs (length Ss)) bs) bs"
        by (rule list_all2_all_nthI) (use mcp_conv_bvs(1)[OF tbs] lbs_arg ts\<rho>(3) in auto)
      show "wt (inst \<rho>2 h \<degree>\<degree> map (\<lambda>b. types_abs Ss b \<degree>\<degree> mbvs (length Ss)) bs)"
        using list_app_typeI[OF sh(2) tm] by (auto simp: wt_def)
      show "wt (inst \<rho>2 h \<degree>\<degree> bs)" using tys sh(1) by (auto simp: wt_def)
    qed
    have ub: "ubv env'' X'' \<subseteq> ubv env X \<union> fst ` NV"
      using ev'' ma'(1) ext(2) by (auto simp: ubv_def X''_def NV_def)
    have vszl: "mcp_vsz \<rho>4 \<sigma>4 (xs ! l, Ts \<Rrightarrow> (UC ! l)) \<le> lsz (pushes mcp_e0 Ss) (bs ! l)" if "l < ?q" for l
    proof -
      have "mcp_vsz \<rho>4 \<sigma>4 (xs ! l, Ts \<Rrightarrow> (UC ! l)) = mcp_vsz \<rho>2 \<sigma>3 (xs ! l, Ts \<Rrightarrow> (UC ! l))"
        by (rule mcp_vsz_agree[OF ag4 sa4 ix[OF that] tvl[OF that]])
      also have "\<dots> = lsz (pushes mcp_e0 Ss) (bs ! l) - 2 * arity (Bts ! l)"
      proof (rule mcp_vsz_val[OF su(3)])
        show "cert_typ alg ar (tsubst \<rho>2 (Ts \<Rrightarrow> (UC ! l)))"
          using \<rho>2Gl[OF that] ts\<rho>(3) cB that lq lbs' lqb by (simp add: cert_typ_funs)
        show "\<sigma>3 (xs ! l) (tsubst \<rho>2 (Ts \<Rrightarrow> (UC ! l))) \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> types_abs Ss (bs ! l)"
          using \<sigma>3l[OF that] \<rho>2Gl[OF that] by simp
        show "tsubst \<rho>2 (Ts \<Rrightarrow> (UC ! l)) = Ss \<Rrightarrow> (Bts ! l)" by (rule \<rho>2Gl[OF that])
        show "pushes mcp_e0 Ss \<turnstile> bs ! l : Bts ! l" by (rule tbs) (use that lqb in simp)
        show "no_redex (bs ! l)" using nr_arg that lqb by simp
        show "\<forall>S\<in>set Ss. cert_typ alg ar S" by (rule ts\<rho>(3))
      qed
      finally show ?thesis by simp
    qed
    have msum: "(\<Sum>y\<in>NV. mcp_vsz \<rho>4 \<sigma>4 y) + 1 \<le> lsz (pushes mcp_e0 Ss) s - 2 * arity UU"
    proof -
      let ?f = "\<lambda>l. (xs ! l, Ts \<Rrightarrow> (UC ! l))"
      have "(\<Sum>y\<in>NV. mcp_vsz \<rho>4 \<sigma>4 y) \<le> sum_list (map (mcp_vsz \<rho>4 \<sigma>4) (map ?f [0..<?q]))"
        unfolding NV_def mlG by (rule mcp_sum_set_le_list)
      also have "\<dots> \<le> sum_list (map (\<lambda>l. lsz (pushes mcp_e0 Ss) (bs ! l)) [0..<?q])"
        by (simp only: map_map comp_def) (rule sum_list_mono, use vszl in simp)
      also have "\<dots> = sum_list (map (lsz (pushes mcp_e0 Ss)) bs)"
        unfolding lqb by (rule arg_cong[where f = sum_list], rule nth_equalityI) simp_all
      finally have "(\<Sum>y\<in>NV. mcp_vsz \<rho>4 \<sigma>4 y) \<le> sum_list (map (lsz (pushes mcp_e0 Ss)) bs)" .
      moreover have "lsz (pushes mcp_e0 Ss) s = tsz (spine_type (pushes mcp_e0 Ss) s) + sum_list (map (lsz (pushes mcp_e0 Ss)) bs)"
        unfolding sh(1) by (rule lsz_rigid_apps[OF rh'])
      moreover have "0 < tsz (spine_type (pushes mcp_e0 Ss) s)" by (rule tsz_pos)
      ultimately show ?thesis using ar0 by simp
    qed
    show "mcp_cres A K X env rb targs u \<rho> \<sigma> Ss UU s 1 (El_C (list_comb h args) env2 dps2)"
      unfolding mcp_cres_def
    proof (rule exI[of _ "list_comb h args"], rule exI[of _ env2], rule exI[of _ dps2],
        rule exI[of _ A'], rule exI[of _ K'], rule exI[of _ X''], rule exI[of _ \<rho>4], rule exI[of _ \<sigma>4],
        rule exI[of _ NV], intro conjI)
      show "sinv A' K' X'' env2 dps2" using si4 by (simp add: X''_def)
      show "scinv \<rho>4 \<sigma>4 env2 dps2 X'' A'" using inv4 by (simp add: X''_def)
      show "tvars_env (tyenv env) \<subseteq> tvars_env (tyenv env2)" using ext(3) ma'(2) tve4 by auto
      show "vars (list_comb h args) \<subseteq> X'' \<union> evars env2" using h(2) by (auto simp: u'e vars_apps X''_def)
      have "ttvars (list_comb h args) \<subseteq> ttvars h \<union> vtvars (mlvars Gs)"
      proof -
        have "ttvars (G \<degree>\<degree> mbvs (length Ts)) \<subseteq> vtvars (mlvars Gs)" if "G \<in> set Gs" for G
        proof -
          from bspec[OF Gi that] obtain a U where G: "G = Var (a, maxidx env' + 1) U" by blast
          have "((a, maxidx env' + 1), U) \<in> mlvars Gs" using that G by force
          then show ?thesis by (auto simp: G ttvars_apps vtvars_def)
        qed
        then show ?thesis by (auto simp: u'e ttvars_apps)
      qed
      then show "ttvars (list_comb h args) \<subseteq> tvars_env (tyenv env2) \<union> A'"
        using h(3) vG ma'(2) tve4 by auto
      show "\<not> loose_bvar (list_comb h args) (ilength Ss)"
        using new_args_props(1)[OF GU _ args] h(4) lq lTsS by (auto simp: list_comb_apps loose_bvar_apps ilength_eq)
      show "\<forall>\<rho>0 e Us U. tsol (tyenv env2) \<rho>0 \<longrightarrow> cert_inst \<rho>0 \<longrightarrow> bs_env \<rho>0 e rb \<longrightarrow>
          e \<tturnstile> map (inst \<rho>0) targs : Us \<longrightarrow> e \<turnstile> inst \<rho>0 u : U \<longrightarrow>
          (\<forall>e'. pushes e' Us \<turnstile> inst \<rho>0 (list_comb h args) : U)"
      proof (intro allI impI)
        fix \<rho>0 e0 Us0 U0 e' assume a: "tsol (tyenv env2) \<rho>0" "cert_inst \<rho>0" "bs_env \<rho>0 e0 rb"
          "e0 \<tturnstile> map (inst \<rho>0) targs : Us0" "e0 \<turnstile> inst \<rho>0 u : U0"
        have \<rho>0': "tsol (tyenv env') \<rho>0" using extends_tsol[OF a(1) ext4'] ma'(2) by simp
        note tt = ts[OF tsol\<theta>[OF \<rho>0'] a(3-5)]
        from hty[OF \<rho>0' a(2-5)] have th: "pushes e' Us0 \<turnstile> inst \<rho>0 h : map (tsubst \<rho>0) UC \<Rrightarrow> U0"
          and cUC0: "\<forall>U\<in>set UC. cert_typ alg ar (tsubst \<rho>0 U)" by blast+
        have cTs0: "\<forall>T\<in>set Ts. cert_typ alg ar (tsubst \<rho>0 T)" using tt(1,3) by simp
        have "pushes e' (map (tsubst \<rho>0) Ts) \<tturnstile> map (inst \<rho>0) (map (\<lambda>G. G \<degree>\<degree> mbvs (length Ts)) Gs) :
            map (tsubst \<rho>0) UC"
          by (rule mf_typings_new_args[OF GU refl cTs0 cUC0 refl])
        from list_app_typeI[OF th this[folded tt(1)]]
        show "pushes e' Us0 \<turnstile> inst \<rho>0 (list_comb h args) : U0" by (simp add: u'e inst_apps)
      qed
      show "pushes mcp_e0 Ss \<turnstile> inst \<rho>4 (list_comb h args) : UU"
      proof -
        have "pushes mcp_e0 (map (tsubst \<rho>4) Ts) \<tturnstile> map (inst \<rho>4) (map (\<lambda>G. G \<degree>\<degree> mbvs (length Ts)) Gs) :
            map (tsubst \<rho>4) UC"
          by (rule mf_typings_new_args[OF GU refl cTs4 cUC4 refl])
        from list_app_typeI[OF sh(2) this[unfolded \<rho>4Ts \<rho>4UC]] show ?thesis by (simp add: u'e inst_apps ih4)
      qed
      show "types_abs Ss (ap \<rho>4 \<sigma>4 (list_comb h args)) \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> types_abs Ss s"
      proof (rule mcp_conv_types_abs[OF _ _ cvb[folded apc]])
        have "pushes mcp_e0 Ss \<turnstile> ap \<rho>4 \<sigma>4 (list_comb h args) : UU"
          unfolding apc by (rule list_app_typeI[OF sh(2) tm])
        from mf_typing_types_abs[OF this ts\<rho>(3)]
        show "wt (types_abs Ss (ap \<rho>4 \<sigma>4 (list_comb h args)))" by (auto simp: wt_def)
        show "wt (types_abs Ss s)" using mcp_typing_val[OF tys lbs ts\<rho>(3)] by (auto simp: wt_def)
      qed
      show "\<forall>k'. mcp_kokK k' \<rho> (tyenv env) A K \<longrightarrow> mcp_kokK k' \<rho>4 (tyenv env2) A' K'"
        using kk kk4 ma'(2) by simp
      show "finite NV" by (simp add: NV_def mlG)
      show "NV \<subseteq> X''" by (simp add: NV_def X''_def)
      show "\<forall>y\<in>NV. maxidx env < snd (fst y)" using mx Gi by (fastforce simp: NV_def)
      show "ubv env2 X'' \<subseteq> ubv env X \<union> fst ` NV" using ub4 ub by (auto simp: X''_def)
      show "(\<Sum>y\<in>NV. mcp_vsz \<rho>4 \<sigma>4 y) + 1 \<le> lsz (pushes mcp_e0 Ss) s - 2 * arity UU" by (rule msum)
    qed (use finX finK' AK ext4 ag04 sa04 in \<open>auto simp: X''_def\<close>)
  qed
qed

lemma mcp_proj_elem:
  assumes cfg: "cfg_alg cfg = alg"
    and pre: "mcp_pre A K X env dps rb targs u"
    and sp: "mcp_spre \<rho> \<sigma> env dps X A e rb targs Ss u UU s"
    and kok: "mcp_kok (nat_of_integer (cfg_arity_bound cfg)) \<rho> (tyenv env) (tvars_env (tyenv env) \<union> A)"
    and ty0: "ok (fastype env rb (fst (strip_comb u))) T0" "ok (body_type env T0) base"
      "ok (mapM (fastype env rb) targs) Ts" "tvars base \<subseteq> tvars_env (tyenv env) \<union> A"
      "\<forall>T\<in>set Ts. tvars T \<subseteq> tvars_env (tyenv env) \<union> A"
    and na: "\<not> is_Abs (fst (strip_comb u))"
    and sB: "s = Bound j \<degree>\<degree> bs" "0 \<le> j" "j < ilength Ss"
    and kdef: "k = length targs - 1 - nat_of_integer j"
    and st: "ok (strip_type env (Ts ! k)) (Us, bary)"
  shows "\<exists>p env0 Cs env'. p \<in> set (arity_guesses cfg bary) \<and> gentvars p env = (env0, Cs) \<and>
    okW (proj_unify cfg base bary Cs env0) env' \<and>
    (\<forall>env'' args. make_args vname Ts env' (Us @ Cs) = (env'', args) \<longrightarrow>
      (\<exists>env2 fr ff. okW (SIMPL (cfg_alg cfg) env''
          ((rb, list_comb (targs ! k) (map (\<lambda>arg. list_comb (head_of arg) targs) args), u) # dps)) (env2, fr, ff) \<and>
        mcp_cres A K X env rb targs u \<rho> \<sigma> Ss UU s 1 (El_C (list_comb (Bound j) args) env2 (fr @ ff))) \<and>
      mcp_cres A K X env rb targs u \<rho> \<sigma> Ss UU s 1 (El_C (list_comb (Bound j) args) env'' dps))"
proof -
  from pre have finX: "finite X" and finK: "finite K" and si: "sinv A K X env dps"
    and vu: "vars u \<subseteq> X \<union> evars env" and vt: "mlvars targs \<subseteq> X \<union> evars env"
    and tv: "ttvars u \<union> (\<Union>t\<in>set targs. ttvars t) \<union> btvars rb \<subseteq> tvars_env (tyenv env) \<union> A"
    and lu: "\<not> loose_bvar u (ilength rb)" and lt: "\<forall>t\<in>set targs. \<not> loose_bvar t (ilength rb)"
    and tok: "mcp_tok env rb targs u"
    unfolding mcp_pre_def by blast+
  from sp have inv: "scinv \<rho> \<sigma> env dps X A" and bs: "bs_env \<rho> e rb"
    and tyt: "e \<tturnstile> map (inst \<rho>) targs : Ss" and tyu: "e \<turnstile> inst \<rho> u : UU" and ar: "arity UU = nabs u"
    and tys: "pushes mcp_e0 Ss \<turnstile> s : UU" and nrs: "no_redex s" and lbs: "\<not> loose_bvar s (ilength Ss)"
    and cv: "types_abs Ss s \<degree>\<degree> map (ap \<rho> \<sigma>) targs \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma> u"
    unfolding mcp_spre_def by blast+
  note i = scinvD[OF inv] and sd = solutionD[OF scinvD(1)[OF inv]]
  have ei: "einv A K env" and wi: "winv env X" and ps: "\<forall>(rb', t', u')\<in>set dps. pok A env rb' X t' u'"
    using si by (auto simp: sinv_def)
  note x = einvD[OF ei] and r0 = einv_rho0[OF ei]
  let ?\<theta> = "tyenv env" and ?KN = "tvars_env (tyenv env) \<union> A"
  have below_KN: "tbelow (maxidx env) S" if "S \<subseteq> ?KN" for S using tvinv_tbelow[OF i(4) that] .
  note ts = mcp_types_sound[OF pre ty0(1-3) na]
  note ts\<rho> = ts[OF sd(2) bs tyt tyu]
  let ?n = "length targs"
  have lSs: "length Ss = ?n" using ts\<rho>(1,5) by simp
  have jn: "nat_of_integer j < ?n" using sB(2,3) lSs nat_of_integer_less_ilength by fastforce
  have kn: "k < ?n" using kdef jn by simp
  have jk: "j = integer_of_nat (?n - 1 - k)"
    using kdef jn sB(2) by (simp add: integer_eq_iff integer_of_nat.rep_eq nat_of_integer.rep_eq less_eq_integer.rep_eq)
  have u: "u = fst (strip_comb u) \<degree>\<degree> snd (strip_comb u)" by (rule strip_comb_apps) simp
  have ar0: "arity UU = 0"
  proof -
    have "\<not> is_Abs u" using na u is_Abs_apps by metis
    then show ?thesis using ar by simp
  qed
  \<comment> \<open>The type of the projected argument:\<close>
  from tys[unfolded sB(1)] obtain Bts where tyB: "pushes mcp_e0 Ss \<turnstile> Bound j : Bts \<Rrightarrow> UU"
    and tybs: "pushes mcp_e0 Ss \<tturnstile> bs : Bts" by (rule list_app_typeE)
  have "pushes mcp_e0 Ss j = Bts \<Rrightarrow> UU" using tyB by auto
  moreover have "pushes mcp_e0 Ss j = Ss ! k"
    using pushes_nth[OF sB(2), of mcp_e0 Ss] sB(3) lSs kdef jn by (simp add: rev_nth)
  ultimately have SsK: "Ss ! k = Bts \<Rrightarrow> UU" by simp
  have \<rho>Tk: "tsubst \<rho> (Ts ! k) = Ss ! k" using ts\<rho>(1,5) kn by simp
  from st have bU: "ok (binder_types env (Ts ! k)) Us" and bB: "ok (body_type env (Ts ! k)) bary"
    by (auto simp: strip_type_def)
  have stk: "tsubst \<rho> (Ts ! k) = map (tsubst \<rho>) Us \<Rrightarrow> tsubst \<rho> bary" by (rule strip_type_sound[OF st sd(2)])
  from mcp_funs_split[OF _ ar0, of "map (tsubst \<rho>) Us" "tsubst \<rho> bary" Bts] stk \<rho>Tk SsK
  have spl: "length Us \<le> length Bts" "Bts = map (tsubst \<rho>) Us @ drop (length Us) Bts"
    "tsubst \<rho> bary = drop (length Us) Bts \<Rrightarrow> UU" by simp_all
  define Ds where "Ds = drop (length Us) Bts"
  define p where "p = length Ds"
  have tvTk: "tvars (Ts ! k) \<subseteq> ?KN" using ty0(5) kn ts\<rho>(5) by simp
  have "\<forall>U\<in>set Us. tvars U \<subseteq> tvars (Ts ! k) \<union> tvars_env ?\<theta>"
    using mf_binder_types_sound[of env "Ts ! k" "Ok Us" Us] bU x(6) by auto
  then have tvUs: "\<forall>U\<in>set Us. tvars U \<subseteq> ?KN" using tvTk by blast
  from body_type_term[OF x(2) refl tvTk] bB have tvbary: "tvars bary \<subseteq> ?KN" by (auto simp: return_def)
  have arb: "arity (tsubst \<rho> bary) = p" using spl(3) ar0 by (simp add: arity_funs p_def Ds_def)
  have pg: "p \<in> set (arity_guesses cfg bary)"
  proof (cases "is_TVar bary")
    case True
    from mcp_body_type_TVar[of env "Ts ! k" "Ok bary" bary] bB True obtain v S
      where bv: "bary = TVar v S" "vt_lookup ?\<theta> v = None" by auto
    have "(v, S) \<in> ?KN" using tvbary bv by simp
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
  let ?A0 = "A \<union> ntv Cs" and ?K0 = "K \<union> ntv Cs"
  have lD: "length Ds = p" by (simp add: p_def)
  obtain \<rho>1 where \<rho>1: "tagree (maxidx env) \<rho> \<rho>1" "map (tsubst \<rho>1) Cs = Ds" "wsinst alg \<rho>1"
    by (rule mcp_gentvars_inst[OF g lD sd(1)])
  have si0: "sinv ?A0 ?K0 X env0 dps" by (rule sinv_gentvars[OF si g])
  have ei0: "einv ?A0 ?K0 env0" using si0 by (simp add: sinv_def)
  have ps0: "\<forall>(rb', t', u')\<in>set dps. pok ?A0 env0 rb' X t' u'" using si0 by (simp add: sinv_def)
  have ext0: "extends env env0" by (rule mcp_extends_same[OF gs(1,2,3)])
  have tbe: "tbelow (maxidx env) (tvars_env ?\<theta>)" by (rule below_KN) simp
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
  \<comment> \<open>The type unification of the projection:\<close>
  have \<rho>1b: "tsubst \<rho>1 base = UU" using tsubst_agree[OF \<rho>1(1) below_KN[OF ty0(4)]] ts\<rho>(2) by simp
  have \<rho>1bary: "tsubst \<rho>1 bary = Ds \<Rrightarrow> UU"
    using tsubst_agree[OF \<rho>1(1) below_KN[OF tvbary]] spl(3) by (simp add: Ds_def)
  have "cert_typ alg ar (Ss ! k)" using ts\<rho>(3) kn lSs by simp
  then have cBts: "\<forall>B\<in>set Bts. cert_typ alg ar B" "cert_typ alg ar UU"
    using SsK by (simp_all add: cert_typ_funs)
  have cDs: "\<forall>D\<in>set Ds. cert_typ alg ar D" using cBts(1) by (auto simp: Ds_def dest: in_set_dropD)
  have tvC: "\<forall>C\<in>set Cs. tvars C \<subseteq> ntv Cs" by (auto simp: ntv_def)
  have tvb0: "tvars base \<subseteq> tvars_env (tyenv env0) \<union> ?A0" "tvars bary \<subseteq> tvars_env (tyenv env0) \<union> ?A0"
    using ty0(4) tvbary gs(2) by auto
  have tvCb: "tvars (Cs \<Rrightarrow> base) \<subseteq> tvars_env (tyenv env0) \<union> ?A0"
    using tvb0(1) tvC by (auto simp: tvars_funs)
  have wb: "wft ar base" by (rule mcp_wft_inst[of \<rho>1]) (simp add: \<rho>1b cBts(2))
  have wbary: "wft ar bary" by (rule mcp_wft_inst[of \<rho>1]) (simp add: \<rho>1bary cDs cBts(2) cert_typ_funs)
  have wCb: "wft ar (Cs \<Rrightarrow> base)"
    by (rule mcp_wft_inst[of \<rho>1]) (simp add: tsubst_funs \<rho>1(2) \<rho>1b cDs cBts(2) cert_typ_funs)
  define Q where "Q = (\<lambda>env'. \<exists>\<rho>'. scinv \<rho>' \<sigma> env' dps X ?A0 \<and> tagree (maxidx env0) \<rho>1 \<rho>' \<and>
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
  from tok r0 obtain e0 Us0 U0 where t0: "bs_env (rho0 env) e0 rb" "e0 \<tturnstile> map (inst (rho0 env)) targs : Us0"
    "e0 \<turnstile> inst (rho0 env) u : U0" unfolding mcp_tok_def by blast
  note tr0 = ts[OF r0(1) t0]
  have cTk0: "cert_typ alg ar (tnorm ?\<theta> (Ts ! k))" using tr0(1,3) kn ts\<rho>(5) by simp
  have cb0: "cert_typ alg ar (tnorm ?\<theta> base)" using tr0(2,4) by simp
  have cbary0: "cert_typ alg ar (tnorm ?\<theta> bary)"
    using cTk0 strip_type_sound[OF st r0(1)] by (simp add: cert_typ_funs)
  have cC: "\<forall>C\<in>set Cs. cert_typ alg ar (tnorm (tyenv env0) C)"
    using gs(6) cert_tnorm[OF ei0] by (fastforce simp: cert_typ_def sort_ok_def)
  have cu_pu: "cuok (proj_unify cfg base bary Cs env0) (\<lambda>env'. sinv ?A0 ?K0 X env' dps \<and> tenv env' = tenv env0 \<and>
    extends env0 env' \<and> tvars_env (tyenv env0) \<subseteq> tvars_env (tyenv env') \<and>
    (\<forall>\<rho>. tsol (tyenv env') \<rho> \<longrightarrow> tsubst \<rho> bary = tsubst \<rho> (Cs \<Rrightarrow> base)))"
    by (rule proj_unify_sinv[OF cfg finite_UnI[OF finK finite_ntv] si0 tvb0 _ _ _ cC])
      (use tvC cb0 cbary0 gs(2) in auto)
  from mcp_ncu_cuok[OF ncu_pu cu_pu] obtain env' where pu: "okW (proj_unify cfg base bary Cs env0) env'"
    and Q: "Q env'" and si': "sinv ?A0 ?K0 X env' dps" and te': "tenv env' = tenv env0"
    and ext': "extends env0 env'" and tve': "tvars_env (tyenv env0) \<subseteq> tvars_env (tyenv env')"
    and beq: "\<forall>\<rho>. tsol (tyenv env') \<rho> \<longrightarrow> tsubst \<rho> bary = tsubst \<rho> (Cs \<Rrightarrow> base)" by blast
  from Q obtain \<rho>2 where inv2: "scinv \<rho>2 \<sigma> env' dps X ?A0" and ag2: "tagree (maxidx env0) \<rho>1 \<rho>2"
    unfolding Q_def by blast
  note i2 = scinvD[OF inv2]
  have ag02: "tagree (maxidx env) \<rho> \<rho>2" by (rule tagree_trans[OF \<rho>1(1) ag2 gs(3)])
  have ext0': "extends env env'" by (rule extends_trans[OF ext0 ext'])
  have mx: "maxidx env \<le> maxidx env'" using ext0' by (simp add: extends_def)
  have tve0: "tvars_env ?\<theta> \<subseteq> tvars_env (tyenv env')" using tve' gs(2) by simp
  have te0: "tenv env' = tenv env" using te' gs(1) by simp
  have tsol\<theta>: "tsol ?\<theta> \<rho>'" if "tsol (tyenv env') \<rho>'" for \<rho>' by (rule extends_tsol[OF that ext0'])
  have \<rho>2Ts: "map (tsubst \<rho>2) Ts = Ss"
    using ts\<rho>(1) tsubst_agree[OF ag02 below_KN] ty0(5) by simp
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
  have lbs_arg: "\<forall>b\<in>set bs. \<not> loose_bvar b (ilength Ss)" using lbs sB(1) by (simp add: loose_bvar_apps)
  have nr_arg: "\<forall>b\<in>set bs. no_redex b" using nrs sB(1) no_redex_apps[of "Bound j" bs] by simp
  have lbs': "length bs = length Bts" using typings_nth[OF tybs] by simp
  \<comment> \<open>The type of the projected argument, for a general type instantiation:\<close>
  have hty: "(\<forall>e'. pushes e' Us0 \<turnstile> inst \<rho>0 (Bound j) : map (tsubst \<rho>0) (Us @ Cs) \<Rrightarrow> U0) \<and>
      (\<forall>U\<in>set (Us @ Cs). cert_typ alg ar (tsubst \<rho>0 U))"
    if "tsol (tyenv env') \<rho>0" "cert_inst \<rho>0" "bs_env \<rho>0 e0 rb" "e0 \<tturnstile> map (inst \<rho>0) targs : Us0"
      "e0 \<turnstile> inst \<rho>0 u : U0" for \<rho>0 e0 Us0 U0
  proof -
    note tt = ts[OF tsol\<theta>[OF that(1)] that(3-5)]
    have Tk: "tsubst \<rho>0 (Ts ! k) = map (tsubst \<rho>0) (Us @ Cs) \<Rrightarrow> tsubst \<rho>0 base"
      using strip_type_sound[OF st tsol\<theta>[OF that(1)]] beq that(1) by (simp add: tsubst_funs)
    moreover have "cert_typ alg ar (tsubst \<rho>0 (Ts ! k))" using tt(1,3) kn ts\<rho>(5) by simp
    ultimately have cUC0: "\<forall>U\<in>set (Us @ Cs). cert_typ alg ar (tsubst \<rho>0 U)" by (auto simp: cert_typ_funs)
    have "pushes e' Us0 \<turnstile> Bound j : map (tsubst \<rho>0) (Us @ Cs) \<Rrightarrow> U0" for e'
    proof -
      have "pushes e' (map (tsubst \<rho>0) Ts) j = rev (map (tsubst \<rho>0) Ts) ! nat_of_integer j"
        using pushes_nth[OF sB(2)] sB(3) lSs ts\<rho>(5) by (simp add: ilength_eq)
      also have "\<dots> = tsubst \<rho>0 (Ts ! k)" using kdef jn ts\<rho>(5) by (simp add: rev_nth)
      finally show ?thesis using Tk tt(1,2) sB(2) by auto
    qed
    with cUC0 show ?thesis by simp
  qed
  show ?thesis
  proof (rule exI[of _ p], rule exI[of _ env0], rule exI[of _ Cs], rule exI[of _ env'], intro conjI allI impI)
    show "p \<in> set (arity_guesses cfg bary)" by (rule pg)
    show "gentvars p env = (env0, Cs)" by (rule g)
    show "okW (proj_unify cfg base bary Cs env0) env'" by (rule pu)
    fix env'' args assume ma: "make_args vname Ts env' (Us @ Cs) = (env'', args)"
    have tvTs': "\<forall>T\<in>set Ts. tvars T \<subseteq> tvars_env (tyenv env') \<union> ?A0" using ty0(5) tve0 by blast
    have tvUC: "\<forall>U\<in>set (Us @ Cs). tvars U \<subseteq> tvars_env (tyenv env') \<union> ?A0" using tvUs tvC tve0 by auto
    have finK0: "finite ?K0" using finK by simp
    have ei': "einv ?A0 ?K0 env'" using si' by (simp add: sinv_def)
    note x' = einvD[OF ei']
    \<comment> \<open>The arity condition for the new type variables:\<close>
    have kk2: "\<forall>k'. mcp_kokK k' \<rho> (tyenv env) A K \<longrightarrow> mcp_kokK k' \<rho>2 (tyenv env') ?A0 ?K0"
    proof (intro allI impI)
      fix k' assume kk: "mcp_kokK k' \<rho> (tyenv env) A K"
      have N: "\<forall>(v, S)\<in>ntv Cs. (v, S) \<in> tvars_env (tyenv env') \<union> ?A0 \<and> mcp_aok k' (\<rho>2 v S)"
      proof (intro ballI, clarify)
        fix v S assume vS: "(v, S) \<in> ntv Cs"
        then obtain C where C: "C \<in> set Cs" "(v, S) \<in> tvars C" by (auto simp: ntv_def)
        from gs(6)[OF C(1)] obtain a where Ca: "C = TVar (a, maxidx env0) []" by blast
        have "tsubst \<rho>2 C \<in> set Ds" using \<rho>2Cs C(1) by (metis image_eqI list.set_map)
        then have D: "\<rho>2 v S \<in> set Ds" using C(2) Ca by simp
        have "Cs \<noteq> []" using C(1) by auto
        then have p0: "p \<noteq> 0" using gs(4) by auto
        then have "is_TVar bary" using pg by (auto simp: arity_guesses_def split: if_splits)
        from mcp_body_type_TVar[of env "Ts ! k" "Ok bary" bary] bB this obtain v' S'
          where bv: "bary = TVar v' S'" "vt_lookup ?\<theta> v' = None" by auto
        have "(v', S') \<in> ?KN" using tvbary bv by simp
        from mcp_kok_unbound[OF mcp_kokK_kok[OF kk ei] this bv(2) x(6)]
        have "mcp_aok k' (tsubst \<rho> bary)" using bv by simp
        then have "\<forall>D\<in>set Ds. mcp_aok k' D" using spl(3) by (simp add: mcp_aok_funs Ds_def)
        with D show "(v, S) \<in> tvars_env (tyenv env') \<union> ?A0 \<and> mcp_aok k' (\<rho>2 v S)" using vS by auto
      qed
      have tx: "textends ?\<theta> (tyenv env')" using ext0' by (simp add: extends_def)
      show "mcp_kokK k' \<rho>2 (tyenv env') ?A0 ?K0"
        by (rule mcp_kokK_ext[OF kk tx x'(6) x'(7) solutionD(2)[OF i2(1)] ag02 below_KN[OF order_refl] x(6)
              tinv_tcons[OF x'(2)] tve0 _ N]) auto
    qed
    \<comment> \<open>The new variables for the arguments:\<close>
    have shB: "s = inst \<rho>2 (Bound j) \<degree>\<degree> bs" "pushes mcp_e0 Ss \<turnstile> inst \<rho>2 (Bound j) : Bts \<Rrightarrow> UU"
      using sB(1) tyB by simp_all
    have hB: "rigid (Bound j)" "vars (Bound j) = {}" "ttvars (Bound j) \<subseteq> tvars_env (tyenv env') \<union> ?A0"
      "\<not> loose_bvar (Bound j) (ilength Ss)" using sB(3) by simp_all
    have AK: "A \<subseteq> ?A0" "K \<subseteq> ?K0" by auto
    obtain Gs \<sigma>3 where args: "args = map (\<lambda>G. G \<degree>\<degree> mbvs (length Ts)) Gs"
      and GU: "list_all2 (\<lambda>G U. \<exists>x. G = Var x (Ts \<Rrightarrow> U)) Gs (Us @ Cs)"
      and ma': "tenv env'' = tenv env'" "tyenv env'' = tyenv env'" "maxidx env' \<le> maxidx env''"
      and Gi: "\<forall>G\<in>set Gs. \<exists>a U. G = Var (a, maxidx env' + 1) U"
      and si'': "sinv ?A0 ?K0 (mlvars Gs \<union> X) env'' dps"
      and vG: "vtvars (mlvars Gs) \<subseteq> tvars_env (tyenv env') \<union> ?A0"
      and inv3d: "scinv \<rho>2 \<sigma>3 env'' dps (mlvars Gs \<union> X) ?A0" and sa3': "sagree (maxidx env') \<sigma> \<sigma>3"
      and lqb: "length Gs = length bs" and apGl: "\<And>l. l < length Gs \<Longrightarrow> ap \<rho>2 \<sigma>3 (Gs ! l) = types_abs Ss (bs ! l)"
      and post: "\<And>env2 dps2 \<rho>4 \<sigma>4. sinv ?A0 ?K0 (mlvars Gs \<union> X) env2 dps2 \<Longrightarrow>
        scinv \<rho>4 \<sigma>4 env2 dps2 (mlvars Gs \<union> X) ?A0 \<Longrightarrow>
        tagree (maxidx env'') \<rho>2 \<rho>4 \<Longrightarrow> sagree (maxidx env'') \<sigma>3 \<sigma>4 \<Longrightarrow> extends env'' env2 \<Longrightarrow>
        tvars_env (tyenv env'') \<subseteq> tvars_env (tyenv env2) \<Longrightarrow> ubv env2 (mlvars Gs \<union> X) \<subseteq> ubv env'' (mlvars Gs \<union> X) \<Longrightarrow>
        (\<forall>k. mcp_kokK k \<rho>2 (tyenv env'') ?A0 ?K0 \<longrightarrow> mcp_kokK k \<rho>4 (tyenv env2) ?A0 ?K0) \<Longrightarrow>
        mcp_cres A K X env rb targs u \<rho> \<sigma> Ss UU s 1 (El_C (list_comb (Bound j) args) env2 dps2)"
      by (rule mcp_args_elem[OF pre sp ty0(1-3) na si' inv2 finK0 AK ext0' te0 tve0 ag02 kk2 \<rho>2Ts tvTs'
            \<rho>2UC tvUC cBts(1) shB tybs hB _ ma], rule hty, assumption+) blast
    let ?q = "length Gs"
    have lq: "?q = length (Us @ Cs)" by (rule list_all2_lengthD[OF GU])
    have Gl: "\<exists>x. Gs ! l = Var x (Ts \<Rrightarrow> ((Us @ Cs) ! l))" if "l < ?q" for l by (rule list_all2_nthD[OF GU that])
    define X'' where "X'' = mlvars Gs \<union> X"
    have finX'': "finite X''" using finX by (simp add: X''_def)
    define dp where "dp = (rb, (targs ! k) \<degree>\<degree> map (\<lambda>G. G \<degree>\<degree> targs) Gs, u)"
    have dpe: "list_comb (targs ! k) (map (\<lambda>arg. list_comb (head_of arg) targs) args) = (targs ! k) \<degree>\<degree> map (\<lambda>G. G \<degree>\<degree> targs) Gs"
    proof -
      have "head_of (G \<degree>\<degree> mbvs (length Ts)) = G" if "G \<in> set Gs" for G
        using Gi that by (auto simp: head_of_apps')
      then show ?thesis by (simp add: args list_comb_apps comp_def cong: map_cong)
    qed
    have ev'': "evars env'' = evars env" by (rule evars_tenv) (simp add: ma'(1) te0)
    \<comment> \<open>Typings of the new pair at a type instantiation:\<close>
    have tydp: "e' \<turnstile> inst \<rho>' ((targs ! k) \<degree>\<degree> map (\<lambda>G. G \<degree>\<degree> targs) Gs) : tsubst \<rho>' base"
      if "tsol (tyenv env') \<rho>'" "e' \<tturnstile> map (inst \<rho>') targs : map (tsubst \<rho>') Ts"
        "\<forall>U\<in>set (Us @ Cs). cert_typ alg ar (tsubst \<rho>' U)" "\<forall>T\<in>set Ts. cert_typ alg ar (tsubst \<rho>' T)" for \<rho>' e'
    proof -
      have "tsubst \<rho>' (Ts ! k) = map (tsubst \<rho>') Us \<Rrightarrow> tsubst \<rho>' bary"
        by (rule strip_type_sound[OF st tsol\<theta>[OF that(1)]])
      then have Tk: "tsubst \<rho>' (Ts ! k) = map (tsubst \<rho>') (Us @ Cs) \<Rrightarrow> tsubst \<rho>' base"
        using beq that(1) by (simp add: tsubst_funs)
      have "e' \<turnstile> inst \<rho>' (targs ! k) : tsubst \<rho>' (Ts ! k)"
        using typings_nth[OF that(2)] kn ts\<rho>(5) by auto
      then have tk: "e' \<turnstile> inst \<rho>' (targs ! k) : map (tsubst \<rho>') (Us @ Cs) \<Rrightarrow> tsubst \<rho>' base"
        using Tk by simp
      have tg: "e' \<tturnstile> map (inst \<rho>') (map (\<lambda>G. G \<degree>\<degree> targs) Gs) : map (tsubst \<rho>') (Us @ Cs)"
      proof (rule mcp_typings_nthI)
        show "length (map (inst \<rho>') (map (\<lambda>G. G \<degree>\<degree> targs) Gs)) = length (map (tsubst \<rho>') (Us @ Cs))"
          using lq by simp
        fix l assume "l < length (map (inst \<rho>') (map (\<lambda>G. G \<degree>\<degree> targs) Gs))"
        then have l: "l < ?q" by simp
        have "(Us @ Cs) ! l \<in> set (Us @ Cs)" by (rule nth_mem) (use l lq in simp)
        then have c: "cert_typ alg ar (tsubst \<rho>' (Ts \<Rrightarrow> ((Us @ Cs) ! l)))"
          using that(3,4) by (auto simp: tsubst_funs cert_typ_funs)
        have "e' \<turnstile> inst \<rho>' (Gs ! l) : map (tsubst \<rho>') Ts \<Rrightarrow> tsubst \<rho>' ((Us @ Cs) ! l)"
          using c Gl[OF l] by (auto simp: tsubst_funs)
        from list_app_typeI[OF this that(2)] show "e' \<turnstile> map (inst \<rho>') (map (\<lambda>G. G \<degree>\<degree> targs) Gs) ! l :
            map (tsubst \<rho>') (Us @ Cs) ! l" using l lq nth_map[of l "Us @ Cs" "tsubst \<rho>'"]
          by (simp add: inst_apps del: map_append)
      qed
      from list_app_typeI[OF tk tg] show ?thesis by (simp add: inst_apps)
    qed
    have cUC2: "\<forall>U\<in>set (Us @ Cs). cert_typ alg ar (tsubst \<rho>2 U)" using \<rho>2UC cBts(1) by (metis image_eqI list.set_map)
    have cTs2: "\<forall>T\<in>set Ts. cert_typ alg ar (tsubst \<rho>2 T)" using \<rho>2Ts ts\<rho>(3) by (metis image_eqI list.set_map)
    have below'': "tbelow (maxidx env'') S" if "S \<subseteq> tvars_env (tyenv env') \<union> ?A0" for S
      using tvinv_tbelow[OF einvD(1)[OF conjunct1[OF si''[unfolded sinv_def]]]] that ma'(2) by simp
    \<comment> \<open>The completeness invariant for the new pair:\<close>
    have inv3: "scinv \<rho>2 \<sigma>3 env'' (dp # dps) X'' ?A0"
    proof -
      note i3 = scinvD[OF inv3d[folded X''_def]]
      have bs2: "bs_env \<rho>2 e rb" by (rule bs_env_agree[OF bs ag02 below_KN]) (use tv in blast)
      have it: "inst \<rho>2 t = inst \<rho> t" if "t \<in> set targs" for t
        by (rule inst_agree[OF ag02 below_KN]) (use tv that in blast)
      have tyt2: "e \<tturnstile> map (inst \<rho>2) targs : map (tsubst \<rho>2) Ts" using tyt it \<rho>2Ts by (simp cong: map_cong)
      have iu: "inst \<rho>2 u = inst \<rho> u" by (rule inst_agree[OF ag02 below_KN]) (use tv in blast)
      have "e \<turnstile> inst \<rho>2 ((targs ! k) \<degree>\<degree> map (\<lambda>G. G \<degree>\<degree> targs) Gs) : tsubst \<rho>2 base"
        by (rule tydp[OF i2(1)[THEN solutionD(2)] tyt2 cUC2 cTs2])
      moreover have "tsubst \<rho>2 base = UU" using tsubst_agree[OF ag02 below_KN[OF ty0(4)]] ts\<rho>(2) by simp
      ultimately have dt: "dtyped \<rho>2 (dp # dps)"
        using bs2 tyu iu i2(6) lt lu Gi nth_mem[OF kn] by (auto simp: dp_def loose_bvar_apps)
      \<comment> \<open>The new pair is solved:\<close>
      let ?ts = "map (ap \<rho> \<sigma>) targs"
      have vb: "below (maxidx env) (vars t)" if "vars t \<subseteq> X \<union> evars env" for t
        using i(3) that unfolding vinv_def by (meson below_mono order_refl)
      have sa3: "sagree (maxidx env) \<sigma> \<sigma>3" by (rule sagree_trans[OF sagree_refl sa3' mx])
      have apt: "ap \<rho>2 \<sigma>3 t = ap \<rho> \<sigma> t" if "t \<in> set targs" for t
        by (rule ap_agree[OF ag02 sa3 below_KN vb]) (use tv vt that in blast)+
      have apu: "ap \<rho>2 \<sigma>3 u = ap \<rho> \<sigma> u" by (rule ap_agree[OF ag02 sa3 below_KN vb]) (use tv vu in blast)+
      have apG: "ap \<rho>2 \<sigma>3 ((Gs ! l) \<degree>\<degree> targs) = types_abs Ss (bs ! l) \<degree>\<degree> ?ts" if "l < ?q" for l
        using apGl[OF that] apt by (simp add: ap_apps cong: map_cong)
      have tapt: "e \<tturnstile> ?ts : Ss"
        using tyt by (induction targs arbitrary: Ss) (auto split: list.splits intro: typing_ap[OF _ sd(3)])
      have tcs: "e \<turnstile> types_abs Ss s \<degree>\<degree> ?ts : UU" by (rule list_app_typeI[OF mcp_typing_val[OF tys lbs ts\<rho>(3)] tapt])
      note cc = mcp_conv_cpy[OF tcs] lSs
      have cps: "mcp_cpy ?ts s = ap \<rho> \<sigma> (targs ! k) \<degree>\<degree> map (mcp_cpy ?ts) bs"
        using mcp_cpy_Bound[of j ?ts] sB lSs kdef kn by (simp add: mcp_cpy_apps ilength_eq)
      have cb: "types_abs Ss (bs ! l) \<degree>\<degree> ?ts \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> mcp_cpy ?ts (bs ! l)"
        "e \<turnstile> types_abs Ss (bs ! l) \<degree>\<degree> ?ts : Bts ! l" if "l < length bs" for l
      proof -
        have "pushes mcp_e0 Ss \<turnstile> bs ! l : Bts ! l" using typings_nth[OF tybs] that by simp
        from list_app_typeI[OF mcp_typing_val[OF this] tapt] lbs_arg ts\<rho>(3) that
        show t: "e \<turnstile> types_abs Ss (bs ! l) \<degree>\<degree> ?ts : Bts ! l" by simp
        show "types_abs Ss (bs ! l) \<degree>\<degree> ?ts \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> mcp_cpy ?ts (bs ! l)" using mcp_conv_cpy(1)[OF t] lSs by simp
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
          by (rule mcp_typings_nthI) (simp_all add: lbs' cb(2))
        then show "wt (ap \<rho> \<sigma> (targs ! k) \<degree>\<degree> map (\<lambda>b. types_abs Ss b \<degree>\<degree> ?ts) bs)"
          using list_app_typeI[OF tk] by (auto simp: wt_def)
        have "e \<turnstile> mcp_cpy ?ts s : UU" by (rule mcp_conv_cpy(2)[OF tcs]) (use lSs in simp)
        then show "wt (ap \<rho> \<sigma> (targs ! k) \<degree>\<degree> map (mcp_cpy ?ts) bs)" using cps by (auto simp: wt_def)
      qed
      also have "\<dots> = mcp_cpy ?ts s" by (rule cps[symmetric])
      also have "\<dots> \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> types_abs Ss s \<degree>\<degree> ?ts" by (rule conv_sym[OF cc(1)]) (use lSs in simp)
      also have "\<dots> \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho>2 \<sigma>3 u" using cv apu by simp
      finally have "ap \<rho>2 \<sigma>3 ((targs ! k) \<degree>\<degree> map (\<lambda>G. G \<degree>\<degree> targs) Gs) \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho>2 \<sigma>3 u" .
      then have "dsolved \<rho>2 \<sigma>3 (dp # dps)" using i3(7) by (simp add: dp_def)
      with dt i3 show ?thesis by (simp add: scinv_def)
    qed
    \<comment> \<open>The invariant of the termination proof for the new pair:\<close>
    have pdp: "pok ?A0 env'' rb X'' ((targs ! k) \<degree>\<degree> map (\<lambda>G. G \<degree>\<degree> targs) Gs) u"
      unfolding pok_def
    proof (intro conjI allI impI)
      show "vars ((targs ! k) \<degree>\<degree> map (\<lambda>G. G \<degree>\<degree> targs) Gs) \<union> vars u \<subseteq> X'' \<union> evars env''"
        using vu vt nth_mem[OF kn] by (auto simp: vars_apps X''_def ev'')
      have tG: "ttvars (G \<degree>\<degree> targs) \<subseteq> vtvars (mlvars Gs) \<union> (\<Union>t\<in>set targs. ttvars t)" if "G \<in> set Gs" for G
      proof -
        from bspec[OF Gi that] obtain a U where G: "G = Var (a, maxidx env' + 1) U" by blast
        have "((a, maxidx env' + 1), U) \<in> mlvars Gs" using that G by force
        then have "tvars U \<subseteq> vtvars (mlvars Gs)" by (auto simp: vtvars_def)
        then show ?thesis by (auto simp: G ttvars_apps)
      qed
      have "ttvars ((targs ! k) \<degree>\<degree> map (\<lambda>G. G \<degree>\<degree> targs) Gs) \<subseteq> vtvars (mlvars Gs) \<union> (\<Union>t\<in>set targs. ttvars t)"
        using tG nth_mem[OF kn] by (auto simp: ttvars_apps)
      moreover have "vtvars (mlvars Gs) \<union> (\<Union>t\<in>set targs. ttvars t) \<subseteq> tvars_env (tyenv env'') \<union> ?A0"
        using vG tv tve0 ma'(2) by auto
      moreover have "ttvars u \<union> btvars rb \<union> vtvars X'' \<subseteq> tvars_env (tyenv env'') \<union> ?A0"
        using tv vG i2(5) tve0 ma'(2) by (auto simp: X''_def)
      ultimately show "ttvars ((targs ! k) \<degree>\<degree> map (\<lambda>G. G \<degree>\<degree> targs) Gs) \<union> ttvars u \<union> btvars rb \<union> vtvars X'' \<subseteq>
          tvars_env (tyenv env'') \<union> ?A0" by blast
      show "\<not> loose_bvar ((targs ! k) \<degree>\<degree> map (\<lambda>G. G \<degree>\<degree> targs) Gs) (ilength rb)"
        using lt Gi nth_mem[OF kn] by (fastforce simp: loose_bvar_apps)
      show "\<not> loose_bvar u (ilength rb)" by (rule lu)
      fix \<rho>0 assume \<rho>0: "tsol (tyenv env'') \<rho>0" "cert_inst \<rho>0"
      have \<rho>0': "tsol (tyenv env') \<rho>0" using \<rho>0(1) ma'(2) by simp
      with tok tsol\<theta> \<rho>0(2) obtain e0 Us0 U0 where t0: "bs_env \<rho>0 e0 rb" "e0 \<tturnstile> map (inst \<rho>0) targs : Us0"
        "e0 \<turnstile> inst \<rho>0 u : U0" unfolding mcp_tok_def by blast
      note tt = ts[OF tsol\<theta>[OF \<rho>0'] t0]
      have cUC0: "\<forall>U\<in>set (Us @ Cs). cert_typ alg ar (tsubst \<rho>0 U)" using hty[OF \<rho>0' \<rho>0(2) t0] by blast
      have cTs0: "\<forall>T\<in>set Ts. cert_typ alg ar (tsubst \<rho>0 T)" using tt(1,3) by simp
      from tydp[OF \<rho>0' t0(2)[unfolded tt(1)] cUC0 cTs0] tt(2) t0
      show "\<exists>e T. bs_env \<rho>0 e rb \<and> e \<turnstile> inst \<rho>0 ((targs ! k) \<degree>\<degree> map (\<lambda>G. G \<degree>\<degree> targs) Gs) : T \<and> e \<turnstile> inst \<rho>0 u : T"
        by blast
    qed
    have si3: "sinv ?A0 ?K0 X'' env'' (dp # dps)"
      using si'' pdp by (simp add: sinv_def dp_def X''_def)
    \<comment> \<open>Simplification:\<close>
    obtain env2 ffs frs \<rho>4 \<sigma>4 where sm: "okW (SIMPL (cfg_alg cfg) env'' (dp # dps)) (env2, ffs, frs)"
      and spost: "simpl_post ?A0 ?K0 X'' env'' (env2, ffs, frs)" and inv4: "scinv \<rho>4 \<sigma>4 env2 (frs @ ffs) X'' ?A0"
      and ag4: "tagree (maxidx env'') \<rho>2 \<rho>4" and sa4: "sagree (maxidx env'') \<sigma>3 \<sigma>4"
      by (rule mcp_SIMPL[OF cfg finX'' finK0 si3 inv3])
    from spost have si4: "sinv ?A0 ?K0 X'' env2 (frs @ ffs)" and ss4: "sstep ?K0 X'' env'' env2"
      by (simp_all add: simpl_post_def)
    note ss = mcp_sstepD[OF ss4]
    have ub4: "ubv env2 X'' \<subseteq> ubv env'' X''" by (rule mcp_SIMPL_ubv[OF sm[unfolded cfg] finX'' finK0 si3])
    note i4 = scinvD[OF inv4]
    have kk4: "\<forall>k'. mcp_kokK k' \<rho>2 (tyenv env'') ?A0 ?K0 \<longrightarrow> mcp_kokK k' \<rho>4 (tyenv env2) ?A0 ?K0"
    proof (intro allI impI)
      fix k' assume k2: "mcp_kokK k' \<rho>2 (tyenv env'') ?A0 ?K0"
      have ei4: "einv ?A0 ?K0 env2" using si4 by (simp add: sinv_def)
      note x4 = einvD[OF ei4]
      have tx4: "textends (tyenv env') (tyenv env2)" using ss(1) ma'(2) by (simp add: extends_def)
      have "mcp_kokK k' \<rho>4 (tyenv env2) ?A0 (?K0 \<union> {})"
        by (rule mcp_kokK_ext[OF k2[unfolded ma'(2)] tx4 x4(6) x4(7) solutionD(2)[OF i4(1)] ag4 below''[OF order_refl]
              x'(6) tinv_tcons[OF x4(2)]]) (use ss(2) ma'(2) in auto)
      then show "mcp_kokK k' \<rho>4 (tyenv env2) ?A0 ?K0" by simp
    qed
    have si4': "sinv ?A0 ?K0 (mlvars Gs \<union> X) env2 (ffs @ frs)" by (rule sinv_mono[OF si4[unfolded X''_def]]) auto
    have inv4': "scinv \<rho>4 \<sigma>4 env2 (ffs @ frs) (mlvars Gs \<union> X) ?A0"
      by (rule scinv_mono[OF inv4[unfolded X''_def]]) auto
    show "\<exists>env2 fr ff. okW (SIMPL (cfg_alg cfg) env''
          ((rb, list_comb (targs ! k) (map (\<lambda>arg. list_comb (head_of arg) targs) args), u) # dps)) (env2, fr, ff) \<and>
        mcp_cres A K X env rb targs u \<rho> \<sigma> Ss UU s 1 (El_C (list_comb (Bound j) args) env2 (fr @ ff))"
    proof (rule exI[of _ env2], rule exI[of _ ffs], rule exI[of _ frs], rule conjI)
      show "okW (SIMPL (cfg_alg cfg) env''
          ((rb, list_comb (targs ! k) (map (\<lambda>arg. list_comb (head_of arg) targs) args), u) # dps)) (env2, ffs, frs)"
        using sm by (simp add: dpe dp_def)
      show "mcp_cres A K X env rb targs u \<rho> \<sigma> Ss UU s 1 (El_C (list_comb (Bound j) args) env2 (ffs @ frs))"
        by (rule post[OF si4' inv4' ag4 sa4 ss(1,2) ub4[unfolded X''_def] kk4])
    qed
    show "mcp_cres A K X env rb targs u \<rho> \<sigma> Ss UU s 1 (El_C (list_comb (Bound j) args) env'' dps)"
      by (rule post[OF si'' inv3d tagree_refl sagree_refl extends_refl subset_refl subset_refl]) simp
  qed
qed


subsection \<open>Copies: arguments of an imitation\<close>

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

lemma mcp_copycons:
  assumes cfg: "cfg_alg cfg = alg"
    and finX: "finite X" and finK: "finite K" and si: "sinv A K X env dps" and inv: "scinv \<rho> \<sigma> env dps X A"
    and kk: "mcp_kokK (nat_of_integer (cfg_arity_bound cfg)) \<rho> (tyenv env) A K"
    and vt: "mlvars targs \<subseteq> X \<union> evars env"
    and tvt: "(\<Union>t\<in>set targs. ttvars t) \<union> btvars rb \<subseteq> tvars_env (tyenv env) \<union> A"
    and lt: "\<forall>t\<in>set targs. \<not> loose_bvar t (ilength rb)"
    and va: "vars a \<subseteq> X \<union> evars env" and tva: "ttvars a \<subseteq> tvars_env (tyenv env) \<union> A"
    and la: "\<not> loose_bvar a (ilength rb)" and toka: "mcp_tok env rb targs a"
    and bs: "bs_env \<rho> e rb" and tyt: "e \<tturnstile> map (inst \<rho>) targs : Ss" and tya: "e \<turnstile> inst \<rho> a : B"
    and tyb: "pushes mcp_e0 Ss \<turnstile> b : B" and nrb: "no_redex b" and lbb: "\<not> loose_bvar b (ilength Ss)"
    and cvb: "types_abs Ss b \<degree>\<degree> map (ap \<rho> \<sigma>) targs \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma> a"
    and IH: "\<And>A K X env dps u \<rho> \<sigma> UU. mcp_pre A K X env dps rb targs u \<Longrightarrow>
      mcp_spre \<rho> \<sigma> env dps X A e rb targs Ss u UU b \<Longrightarrow>
      mcp_kokK (nat_of_integer (cfg_arity_bound cfg)) \<rho> (tyenv env) A K \<Longrightarrow>
      \<exists>sq. okW (mc cfg vname rb targs u env dps) sq \<and>
        (\<exists>x. ev cfg sq x \<and> (\<exists>m. mcp_cres A K X env rb targs u \<rho> \<sigma> Ss UU b m x))"
  shows "\<exists>cs. okW (copycons cfg vname rb targs a uas env dps) cs \<and>
    (\<exists>a' env' dps'. ev cfg cs (El_D (a' # uas) env' dps') \<and> mcp_cres A K X env rb targs a \<rho> \<sigma> Ss B b 0 (El_C a' env' dps'))"
proof -
  let ?\<theta> = "tyenv env" and ?KN = "tvars_env (tyenv env) \<union> A"
  have ei: "einv A K env" and wi: "winv env X" using si by (simp_all add: sinv_def)
  note x = einvD[OF ei] and r0 = einv_rho0[OF ei] and i = scinvD[OF inv] and sd = solutionD[OF scinvD(1)[OF inv]]
  have p: "pok A env rb X a a"
    unfolding pok_def
  proof (intro conjI allI impI)
    show "vars a \<union> vars a \<subseteq> X \<union> evars env" using va by simp
    show "ttvars a \<union> ttvars a \<union> btvars rb \<union> vtvars X \<subseteq> ?KN" using tva tvt i(5) by auto
    show "\<not> loose_bvar a (ilength rb)" "\<not> loose_bvar a (ilength rb)" by (rule la)+
    fix \<rho>0 assume "tsol ?\<theta> \<rho>0" "cert_inst \<rho>0"
    with toka obtain e0 Us U where "bs_env \<rho>0 e0 rb" "e0 \<turnstile> inst \<rho>0 a : U" unfolding mcp_tok_def by blast
    then show "\<exists>e T. bs_env \<rho>0 e rb \<and> e \<turnstile> inst \<rho>0 a : T \<and> e \<turnstile> inst \<rho>0 a : T" by blast
  qed
  from hn_term[OF ei wi p] obtain u1 u1' where h: "head_norm env a = return u1" "head_norm env a = return u1'"
    "pok A env rb X u1 u1'" by blast
  from h(1,2) have "u1' = u1" by (simp add: return_def)
  with h(3) have p1: "pok A env rb X u1 u1" by simp
  note pd1 = pokD[OF p1]
  from pd1(9)[OF r0] obtain e0 T where t0: "bs_env (rho0 env) e0 rb" "e0 \<turnstile> inst (rho0 env) u1 : T" by blast
  have tv1: "ttvars u1 \<union> btvars rb \<subseteq> ?KN" using pd1(3,5) by blast
  from eta_norm_term[OF x(2) refl t0(2,1) pd1(7) tv1] obtain u2 where
    et: "eta_norm env rb u1 = return u2" "ttvars u2 \<subseteq> ?KN" "nabs u2 = arity T" by blast
  have et': "ok (eta_norm env rb u1) u2" using et(1) by (simp add: return_def)
  have h': "ok (head_norm env a) u1" using h(1) by (simp add: return_def)
  have p2: "pok A env rb X u2 u2"
    using pok_sym[OF pok_eta_norm[OF pok_sym[OF pok_eta_norm[OF p1 et' et(2)]] et' et(2)]] .
  note pd2 = pokD[OF p2]
  note es = eta_norm_sound[OF et']
  have tyu2: "e' \<turnstile> inst \<rho>' u2 : U"
    if "tsol ?\<theta> \<rho>'" "wt_env \<rho>' env" "bs_env \<rho>' e' rb" "e' \<turnstile> inst \<rho>' a : U" for \<rho>' e' U
  proof -
    have "e' \<turnstile> inst \<rho>' u1 : U" using head_norm_sound[OF h(1)[unfolded return_def] refl that(1,2,4)] by blast
    then show ?thesis using es that(1,3) pd1(7) by blast
  qed
  have apu2: "ap \<rho> \<sigma> u2 \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma> a"
  proof -
    have h1: "ap \<rho> \<sigma> a \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma> u1"
      using head_norm_sound[OF h(1)[unfolded return_def] refl sd(2) i(2) tya] i(1) by blast
    have "e \<turnstile> inst \<rho> u1 : B" using head_norm_sound[OF h(1)[unfolded return_def] refl sd(2) i(2) tya] by blast
    then have "ap \<rho> \<sigma> u2 \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma> u1" using es sd(2,3) bs pd1(7) by blast
    then show ?thesis using h1 by (blast intro: conv_trans conv_sym)
  qed
  have tyu2\<rho>: "e \<turnstile> inst \<rho> u2 : B" by (rule tyu2[OF sd(2) i(2) bs tya])
  \<comment> \<open>The type of the normalized argument and the deferral:\<close>
  from pd2(9)[OF r0] obtain e1 T1 where t1: "bs_env (rho0 env) e1 rb" "e1 \<turnstile> inst (rho0 env) u2 : T1" by blast
  from env_fastype_term[OF x(2) refl t1(2,1) pd2(7)] pd2(3,5) obtain Wa where
    Wa: "env_fastype env (map snd rb) u2 = return Wa" "tvars Wa \<subseteq> ?KN" by blast
  have fW: "fastype env rb u2 = return Wa" using Wa(1) by (simp add: fastype_def)
  from body_type_term[OF x(2) refl Wa(2)] obtain Ba where
    bB: "body_type env Wa = return Ba" "tvars Ba \<subseteq> ?KN" by blast
  have da: "defer_arg env rb u2 = return (is_TVar Ba)" by (simp add: defer_arg_def fW bB(1))
  have "\<forall>s\<in>set targs. \<exists>e U. bs_env (rho0 env) e rb \<and> e \<turnstile> inst (rho0 env) s : U \<and> \<not> loose_bvar s (ilength rb) \<and>
      ttvars s \<union> btvars rb \<subseteq> ?KN"
  proof
    fix s assume s: "s \<in> set targs"
    from toka r0 obtain e2 Us U where "bs_env (rho0 env) e2 rb" "e2 \<tturnstile> map (inst (rho0 env)) targs : Us"
      unfolding mcp_tok_def by blast
    with mcp_typings_mem[OF _ s] obtain V where "bs_env (rho0 env) e2 rb" "e2 \<turnstile> inst (rho0 env) s : V" by blast
    then show "\<exists>e U. bs_env (rho0 env) e rb \<and> e \<turnstile> inst (rho0 env) s : U \<and> \<not> loose_bvar s (ilength rb) \<and>
      ttvars s \<union> btvars rb \<subseteq> ?KN" using lt s tvt by blast
  qed
  from mapM_fastype_term[OF ei this] obtain Ts where
    mt: "mapM (fastype env rb) targs = return Ts" "\<forall>T\<in>set Ts. tvars T \<subseteq> ?KN" by blast
  have tyWa: "U = tsubst \<rho>' Wa" if "tsol ?\<theta> \<rho>'" "bs_env \<rho>' e' rb" "e' \<turnstile> inst \<rho>' u2 : U" for \<rho>' e' U
    using fastype_sound[OF fW[unfolded return_def] that] by simp
  \<comment> \<open>The hypotheses for the normalized argument:\<close>
  have tok2: "mcp_tok env rb targs u2"
    unfolding mcp_tok_def
  proof (intro allI impI)
    fix \<rho>0 assume \<rho>0: "tsol ?\<theta> \<rho>0" "cert_inst \<rho>0"
    with toka obtain e2 Us U where t2: "bs_env \<rho>0 e2 rb" "e2 \<tturnstile> map (inst \<rho>0) targs : Us" "e2 \<turnstile> inst \<rho>0 a : U"
      unfolding mcp_tok_def by blast
    have "wt_env \<rho>0 env" using winvD[OF wi \<rho>0] by blast
    from tyu2[OF \<rho>0(1) this t2(1,3)] t2 show "\<exists>e Us U. bs_env \<rho>0 e rb \<and> e \<tturnstile> map (inst \<rho>0) targs : Us \<and> e \<turnstile> inst \<rho>0 u2 : U"
      by blast
  qed
  have pre2: "mcp_pre A K X env dps rb targs u2"
    unfolding mcp_pre_def
    using finX finK si pd2(1) vt pd2(3) tvt pd2(7) lt tok2 mcp_norm_satd[OF h' et'] by auto
  have sp0: "scinv \<rho> \<sigma> env dps X A \<and> bs_env \<rho> e rb \<and> e \<tturnstile> map (inst \<rho>) targs : Ss \<and> e \<turnstile> inst \<rho> u2 : B \<and>
      pushes mcp_e0 Ss \<turnstile> b : B \<and> no_redex b \<and> \<not> loose_bvar b (ilength Ss) \<and>
      types_abs Ss b \<degree>\<degree> map (ap \<rho> \<sigma>) targs \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma> u2"
    using inv bs tyt tyu2\<rho> tyb nrb lbb conv_trans[OF cvb conv_sym[OF apu2]] by blast
  have conv_a: "e0 \<turnstile> inst \<rho>0 u2 : U"
    if "tsol ?\<theta> \<rho>0" "cert_inst \<rho>0" "bs_env \<rho>0 e0 rb" "e0 \<turnstile> inst \<rho>0 a : U" for \<rho>0 e0 U
    using tyu2[OF that(1) _ that(3,4)] winvD[OF wi that(1,2)] by blast
  define d where "d = (0 < cfg_arity_bound cfg \<and> is_TVar Ba)"
  show ?thesis
  proof (cases d)
    case True
    obtain env' newhd where g: "genvar vname env (Ts \<Rrightarrow> Wa) = (env', newhd)" by fastforce
    have cr: "mcp_cres A K X env rb targs u2 \<rho> \<sigma> Ss B b 0
        (El_C (combound newhd 0 (length Ts)) env' ((rb, newhd \<degree>\<degree> targs, u2) # dps))"
      by (rule mcp_newvar[where e = e, OF pre2 sp0 mt(1)[unfolded return_def] mt(2) Wa(2) tyWa g])
    let ?cs = "S_MapCons uas (S_Single (El_C (combound newhd 0 (length Ts)) env' ((rb, list_comb newhd targs, u2) # dps)))"
    have "okW (copycons cfg vname rb targs a uas env dps) ?cs"
      using True by (simp add: copycons_def h(1) et(1) da fW mt(1) g d_def Let_def)
    moreover have "ev cfg ?cs (El_D (combound newhd 0 (length Ts) # uas) env' ((rb, newhd \<degree>\<degree> targs, u2) # dps))"
      by (simp add: list_comb_apps ev.map_cons ev.single)
    moreover have "mcp_cres A K X env rb targs a \<rho> \<sigma> Ss B b 0
        (El_C (combound newhd 0 (length Ts)) env' ((rb, newhd \<degree>\<degree> targs, u2) # dps))"
      by (rule mcp_cres_u[OF cr conv_a])
    ultimately show ?thesis by blast
  next
    case False
    have arB: "arity B = nabs u2"
    proof -
      from mf_body_type_sound[of env Wa "Ok Ba" Ba] bB(1) x(6) obtain Zs where
        nb: "\<forall>C D. tnorm ?\<theta> Ba \<noteq> C \<rightarrow>\<^sub>T D" and Zs: "\<And>\<rho>'. tsol ?\<theta> \<rho>' \<Longrightarrow> tsubst \<rho>' Wa = map (tsubst \<rho>') Zs \<Rrightarrow> tsubst \<rho>' Ba"
        by (auto simp: return_def)
      have "e0 \<turnstile> inst (rho0 env) u2 : T" using es r0(1) t0 pd1(7) by blast
      then have "T = tsubst (rho0 env) Wa" by (rule tyWa[OF r0(1) t0(1)])
      also have "\<dots> = map (tsubst (rho0 env)) Zs \<Rrightarrow> tnorm ?\<theta> Ba" using Zs[OF r0(1)] by (simp add: tnorm_tsubst[symmetric])
      finally have aT: "arity T = length Zs" using mcp_arity_nonarrow[OF nb] by (simp add: arity_funs)
      have "B = tsubst \<rho> Wa" by (rule tyWa[OF sd(2) bs tyu2\<rho>])
      also have "\<dots> = map (tsubst \<rho>) Zs \<Rrightarrow> tsubst \<rho> Ba" by (rule Zs[OF sd(2)])
      finally have aB: "arity B = length Zs + arity (tsubst \<rho> Ba)" by (simp add: arity_funs)
      have "arity (tsubst \<rho> Ba) = 0"
      proof (cases "is_TVar Ba")
        case True
        with False have b0: "\<not> 0 < cfg_arity_bound cfg" by (simp add: d_def)
        from mcp_body_type_TVar[of env Wa "Ok Ba" Ba] bB(1) True obtain v S where
          bv: "Ba = TVar v S" "vt_lookup ?\<theta> v = None" by (auto simp: return_def)
        have "(v, S) \<in> ?KN" using bB(2) bv by simp
        from mcp_aok_arity[OF mcp_kok_unbound[OF mcp_kokK_kok[OF kk ei] this bv(2) x(6)]]
        have "arity (\<rho> v S) \<le> nat_of_integer (cfg_arity_bound cfg)" .
        moreover have "nat_of_integer (cfg_arity_bound cfg) = 0"
          using b0 by (simp add: nat_of_integer.rep_eq less_integer.rep_eq)
        ultimately show ?thesis using bv by simp
      next
        case False
        then show ?thesis by (rule mcp_body_type_nonTVar_arity[OF bB(1)[unfolded return_def] _ x(6)])
      qed
      with aB aT et(3) show ?thesis by simp
    qed
    have sp2: "mcp_spre \<rho> \<sigma> env dps X A e rb targs Ss u2 B b"
      using sp0 arB by (simp add: mcp_spre_def)
    from IH[OF pre2 sp2 kk] obtain sq x m where sq: "okW (mc cfg vname rb targs u2 env dps) sq"
      and evx: "ev cfg sq x" and cr: "mcp_cres A K X env rb targs u2 \<rho> \<sigma> Ss B b m x" by blast
    from cr obtain a' env' dps' where x: "x = El_C a' env' dps'" by (rule mcp_cresE) blast
    have "okW (copycons cfg vname rb targs a uas env dps) (S_MapCons uas sq)"
      using False sq by (auto simp: copycons_def h(1) et(1) da d_def)
    moreover have "ev cfg (S_MapCons uas sq) (El_D (a' # uas) env' dps')"
      using evx x by (simp add: ev.map_cons)
    moreover have "mcp_cres A K X env rb targs a \<rho> \<sigma> Ss B b 0 (El_C a' env' dps')"
      using mcp_cres_m0[OF mcp_cres_u[OF cr conv_a]] x by simp
    ultimately show ?thesis by blast
  qed
qed


text \<open>The copies of a list of arguments, for the targets \<open>bs\<close> of types \<open>Bs\<close>:\<close>

definition mcp_dres :: "(indexname \<times> psort) set \<Rightarrow> (indexname \<times> psort) set \<Rightarrow> (indexname \<times> ptyp) set \<Rightarrow>
    env \<Rightarrow> binders \<Rightarrow> pterm list \<Rightarrow> pterm list \<Rightarrow> tinst \<Rightarrow> vsubst \<Rightarrow> ptyp list \<Rightarrow> ptyp list \<Rightarrow> pterm list \<Rightarrow>
    elem \<Rightarrow> bool" where
  "mcp_dres A K X env rb targs uas \<rho> \<sigma> Ss Bs bs x \<longleftrightarrow>
    (\<exists>uas' env' dps' A' K' X' \<rho>' \<sigma>' NV. x = El_D uas' env' dps' \<and>
      finite X' \<and> finite K' \<and> A \<subseteq> A' \<and> K \<subseteq> K' \<and> X \<subseteq> X' \<and> sinv A' K' X' env' dps' \<and>
      scinv \<rho>' \<sigma>' env' dps' X' A' \<and> extends env env' \<and> tvars_env (tyenv env) \<subseteq> tvars_env (tyenv env') \<and>
      tagree (maxidx env) \<rho> \<rho>' \<and> sagree (maxidx env) \<sigma> \<sigma>' \<and> length uas' = length uas \<and>
      mlvars uas' \<subseteq> X' \<union> evars env' \<and> (\<Union>t\<in>set uas'. ttvars t) \<subseteq> tvars_env (tyenv env') \<union> A' \<and>
      (\<forall>t\<in>set uas'. \<not> loose_bvar t (ilength Ss)) \<and>
      (\<forall>\<rho>0 e Us Vs. tsol (tyenv env') \<rho>0 \<longrightarrow> cert_inst \<rho>0 \<longrightarrow> bs_env \<rho>0 e rb \<longrightarrow>
        e \<tturnstile> map (inst \<rho>0) targs : Us \<longrightarrow> e \<tturnstile> map (inst \<rho>0) uas : Vs \<longrightarrow>
        (\<forall>e'. pushes e' Us \<tturnstile> map (inst \<rho>0) uas' : Vs)) \<and>
      pushes mcp_e0 Ss \<tturnstile> map (inst \<rho>') uas' : Bs \<and>
      (\<forall>i<length uas. types_abs Ss (ap \<rho>' \<sigma>' (uas' ! i)) \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> types_abs Ss (bs ! i)) \<and>
      finite NV \<and> NV \<subseteq> X' \<and> (\<forall>y\<in>NV. maxidx env < snd (fst y)) \<and> ubv env' X' \<subseteq> ubv env X \<union> fst ` NV \<and>
      (\<Sum>y\<in>NV. mcp_vsz \<rho>' \<sigma>' y) \<le> sum_list (map (\<lambda>(b, B). lsz (pushes mcp_e0 Ss) b - 2 * arity B) (zip bs Bs)) \<and>
      (\<forall>k. mcp_kokK k \<rho> (tyenv env) A K \<longrightarrow> mcp_kokK k \<rho>' (tyenv env') A' K'))"

lemma mcp_evars_extends: "extends env env' \<Longrightarrow> evars env \<subseteq> evars env'"
  unfolding extends_def evars_def bnds_def by blast

lemma mcp_tok_extends: "mcp_tok env rb targs u \<Longrightarrow> extends env env' \<Longrightarrow> mcp_tok env' rb targs u"
  unfolding mcp_tok_def by (meson extends_tsol)

lemma mcp_agree_old:
  assumes inv: "scinv \<rho> \<sigma> env dps X A" and ag: "tagree (maxidx env) \<rho> \<rho>'" "sagree (maxidx env) \<sigma> \<sigma>'"
    and v: "vars t \<subseteq> X \<union> evars env" and tv: "ttvars t \<subseteq> tvars_env (tyenv env) \<union> A"
  shows "ap \<rho>' \<sigma>' t = ap \<rho> \<sigma> t" "inst \<rho>' t = inst \<rho> t"
proof -
  note i = scinvD[OF inv]
  have b: "below (maxidx env) (vars t)" using i(3) v unfolding vinv_def by (meson below_mono order_refl)
  have tb: "tbelow (maxidx env) (ttvars t)" by (rule tvinv_tbelow[OF i(4) tv])
  show "ap \<rho>' \<sigma>' t = ap \<rho> \<sigma> t" by (rule ap_agree[OF ag tb b])
  show "inst \<rho>' t = inst \<rho> t" by (rule inst_agree[OF ag(1) tb])
qed

lemma mcp_vsz_agree_X:
  assumes inv: "scinv \<rho> \<sigma> env dps X A" and ag: "tagree (maxidx env) \<rho> \<rho>'" "sagree (maxidx env) \<sigma> \<sigma>'"
    and y: "y \<in> X"
  shows "mcp_vsz \<rho>' \<sigma>' y = mcp_vsz \<rho> \<sigma> y"
proof -
  note i = scinvD[OF inv]
  obtain x T where yx: "y = (x, T)" by (cases y)
  have "snd x \<le> maxidx env" using i(3) y yx unfolding vinv_def below_def by force
  moreover have "tbelow (maxidx env) (tvars T)"
    by (rule tvinv_tbelow[OF i(4)]) (use i(5) y yx in \<open>auto simp: vtvars_def\<close>)
  ultimately show ?thesis using mcp_vsz_agree[OF ag] yx by simp
qed

lemma mcp_dresE:
  assumes "mcp_dres A K X env rb targs uas \<rho> \<sigma> Ss Bs bs x"
  obtains uas' env' dps' A' K' X' \<rho>' \<sigma>' NV where "x = El_D uas' env' dps'"
    "finite X'" "finite K'" "A \<subseteq> A'" "K \<subseteq> K'" "X \<subseteq> X'" "sinv A' K' X' env' dps'"
    "scinv \<rho>' \<sigma>' env' dps' X' A'" "extends env env'" "tvars_env (tyenv env) \<subseteq> tvars_env (tyenv env')"
    "tagree (maxidx env) \<rho> \<rho>'" "sagree (maxidx env) \<sigma> \<sigma>'" "length uas' = length uas"
    "mlvars uas' \<subseteq> X' \<union> evars env'" "(\<Union>t\<in>set uas'. ttvars t) \<subseteq> tvars_env (tyenv env') \<union> A'"
    "\<forall>t\<in>set uas'. \<not> loose_bvar t (ilength Ss)"
    "\<forall>\<rho>0 e Us Vs. tsol (tyenv env') \<rho>0 \<longrightarrow> cert_inst \<rho>0 \<longrightarrow> bs_env \<rho>0 e rb \<longrightarrow>
        e \<tturnstile> map (inst \<rho>0) targs : Us \<longrightarrow> e \<tturnstile> map (inst \<rho>0) uas : Vs \<longrightarrow>
        (\<forall>e'. pushes e' Us \<tturnstile> map (inst \<rho>0) uas' : Vs)"
    "pushes mcp_e0 Ss \<tturnstile> map (inst \<rho>') uas' : Bs"
    "\<forall>i<length uas. types_abs Ss (ap \<rho>' \<sigma>' (uas' ! i)) \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> types_abs Ss (bs ! i)"
    "finite NV" "NV \<subseteq> X'" "\<forall>y\<in>NV. maxidx env < snd (fst y)" "ubv env' X' \<subseteq> ubv env X \<union> fst ` NV"
    "(\<Sum>y\<in>NV. mcp_vsz \<rho>' \<sigma>' y) \<le> sum_list (map (\<lambda>(b, B). lsz (pushes mcp_e0 Ss) b - 2 * arity B) (zip bs Bs))"
    "\<forall>k. mcp_kokK k \<rho> (tyenv env) A K \<longrightarrow> mcp_kokK k \<rho>' (tyenv env') A' K'"
  using assms unfolding mcp_dres_def by (elim exE conjE) (rule that; assumption)

lemma mcp_dresI:
  assumes "x = El_D uas' env' dps'"
    "finite X'" "finite K'" "A \<subseteq> A'" "K \<subseteq> K'" "X \<subseteq> X'" "sinv A' K' X' env' dps'"
    "scinv \<rho>' \<sigma>' env' dps' X' A'" "extends env env'" "tvars_env (tyenv env) \<subseteq> tvars_env (tyenv env')"
    "tagree (maxidx env) \<rho> \<rho>'" "sagree (maxidx env) \<sigma> \<sigma>'" "length uas' = length uas"
    "mlvars uas' \<subseteq> X' \<union> evars env'" "(\<Union>t\<in>set uas'. ttvars t) \<subseteq> tvars_env (tyenv env') \<union> A'"
    "\<forall>t\<in>set uas'. \<not> loose_bvar t (ilength Ss)"
    "\<forall>\<rho>0 e Us Vs. tsol (tyenv env') \<rho>0 \<longrightarrow> cert_inst \<rho>0 \<longrightarrow> bs_env \<rho>0 e rb \<longrightarrow>
        e \<tturnstile> map (inst \<rho>0) targs : Us \<longrightarrow> e \<tturnstile> map (inst \<rho>0) uas : Vs \<longrightarrow>
        (\<forall>e'. pushes e' Us \<tturnstile> map (inst \<rho>0) uas' : Vs)"
    "pushes mcp_e0 Ss \<tturnstile> map (inst \<rho>') uas' : Bs"
    "\<forall>i<length uas. types_abs Ss (ap \<rho>' \<sigma>' (uas' ! i)) \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> types_abs Ss (bs ! i)"
    "finite NV" "NV \<subseteq> X'" "\<forall>y\<in>NV. maxidx env < snd (fst y)" "ubv env' X' \<subseteq> ubv env X \<union> fst ` NV"
    "(\<Sum>y\<in>NV. mcp_vsz \<rho>' \<sigma>' y) \<le> sum_list (map (\<lambda>(b, B). lsz (pushes mcp_e0 Ss) b - 2 * arity B) (zip bs Bs))"
    "\<forall>k. mcp_kokK k \<rho> (tyenv env) A K \<longrightarrow> mcp_kokK k \<rho>' (tyenv env') A' K'"
  shows "mcp_dres A K X env rb targs uas \<rho> \<sigma> Ss Bs bs x"
  unfolding mcp_dres_def
  by (rule exI[of _ uas'], rule exI[of _ env'], rule exI[of _ dps'], rule exI[of _ A'], rule exI[of _ K'],
      rule exI[of _ X'], rule exI[of _ \<rho>'], rule exI[of _ \<sigma>'], rule exI[of _ NV]) (intro conjI; fact)

lemma mcp_copyargs:
  assumes cfg: "cfg_alg cfg = alg"
    and finX: "finite X" and finK: "finite K" and si: "sinv A K X env dps" and inv: "scinv \<rho> \<sigma> env dps X A"
    and kk: "mcp_kokK (nat_of_integer (cfg_arity_bound cfg)) \<rho> (tyenv env) A K"
    and vt: "mlvars targs \<subseteq> X \<union> evars env"
    and tvt: "(\<Union>t\<in>set targs. ttvars t) \<union> btvars rb \<subseteq> tvars_env (tyenv env) \<union> A"
    and lt: "\<forall>t\<in>set targs. \<not> loose_bvar t (ilength rb)"
    and va: "mlvars uargs \<subseteq> X \<union> evars env" and tva: "(\<Union>t\<in>set uargs. ttvars t) \<subseteq> tvars_env (tyenv env) \<union> A"
    and la: "\<forall>t\<in>set uargs. \<not> loose_bvar t (ilength rb)"
    and tok: "\<forall>\<rho>0. tsol (tyenv env) \<rho>0 \<longrightarrow> cert_inst \<rho>0 \<longrightarrow>
      (\<exists>e0 Us Vs. bs_env \<rho>0 e0 rb \<and> e0 \<tturnstile> map (inst \<rho>0) targs : Us \<and> e0 \<tturnstile> map (inst \<rho>0) uargs : Vs)"
    and bs: "bs_env \<rho> e rb" and tyt: "e \<tturnstile> map (inst \<rho>) targs : Ss" and tya: "e \<tturnstile> map (inst \<rho>) uargs : Bs"
    and lbs: "length bs = length uargs"
    and tyb: "\<forall>i<length bs. pushes mcp_e0 Ss \<turnstile> bs ! i : Bs ! i \<and> no_redex (bs ! i) \<and> \<not> loose_bvar (bs ! i) (ilength Ss) \<and>
      types_abs Ss (bs ! i) \<degree>\<degree> map (ap \<rho> \<sigma>) targs \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma> (uargs ! i)"
    and IH: "\<And>i A K X env dps u \<rho> \<sigma> UU. i < length bs \<Longrightarrow> mcp_pre A K X env dps rb targs u \<Longrightarrow>
      mcp_spre \<rho> \<sigma> env dps X A e rb targs Ss u UU (bs ! i) \<Longrightarrow>
      mcp_kokK (nat_of_integer (cfg_arity_bound cfg)) \<rho> (tyenv env) A K \<Longrightarrow>
      \<exists>sq. okW (mc cfg vname rb targs u env dps) sq \<and>
        (\<exists>x. ev cfg sq x \<and> (\<exists>m. mcp_cres A K X env rb targs u \<rho> \<sigma> Ss UU (bs ! i) m x))"
  shows "\<exists>x. ev cfg (copyargs vname rb targs env dps uargs) x \<and> mcp_dres A K X env rb targs uargs \<rho> \<sigma> Ss Bs bs x"
  using va tva la tok tya lbs tyb IH
proof (induction uargs arbitrary: bs Bs)
  case Nil
  then have bs0: "bs = []" and Bs0: "Bs = []" by simp_all
  have "mcp_dres A K X env rb targs [] \<rho> \<sigma> Ss Bs bs (El_D [] env dps)"
    by (rule mcp_dresI[where NV = "{}"]) (use finX finK si inv bs0 Bs0 extends_refl in auto)
  moreover have "ev cfg (copyargs vname rb targs env dps []) (El_D [] env dps)" by (simp add: ev.single)
  ultimately show ?case by blast
next
  case (Cons a as)
  note i = scinvD[OF inv]
  have below_KN: "tbelow (maxidx env) S" if "S \<subseteq> tvars_env (tyenv env) \<union> A" for S using tvinv_tbelow[OF i(4) that] .
  from Cons.prems(6) obtain b0 bs' where bsc: "bs = b0 # bs'" by (cases bs) auto
  from Cons.prems(5) obtain B0 Bs' where Bsc: "Bs = B0 # Bs'" and tya0: "e \<turnstile> inst \<rho> a : B0"
    and tyas: "e \<tturnstile> map (inst \<rho>) as : Bs'" by (cases Bs) auto
  have va': "mlvars as \<subseteq> X \<union> evars env" and va0: "vars a \<subseteq> X \<union> evars env" using Cons.prems(1) by auto
  have tva': "(\<Union>t\<in>set as. ttvars t) \<subseteq> tvars_env (tyenv env) \<union> A" and tva0: "ttvars a \<subseteq> tvars_env (tyenv env) \<union> A"
    using Cons.prems(2) by auto
  have la': "\<forall>t\<in>set as. \<not> loose_bvar t (ilength rb)" and la0: "\<not> loose_bvar a (ilength rb)" using Cons.prems(3) by auto
  have tok': "\<forall>\<rho>0. tsol (tyenv env) \<rho>0 \<longrightarrow> cert_inst \<rho>0 \<longrightarrow>
      (\<exists>e0 Us Vs. bs_env \<rho>0 e0 rb \<and> e0 \<tturnstile> map (inst \<rho>0) targs : Us \<and> e0 \<tturnstile> map (inst \<rho>0) as : Vs)"
    and toka: "mcp_tok env rb targs a"
  proof -
    have "\<exists>e0 Us Vs. bs_env \<rho>0 e0 rb \<and> e0 \<tturnstile> map (inst \<rho>0) targs : Us \<and> e0 \<tturnstile> map (inst \<rho>0) as : Vs \<and>
        (\<exists>U. e0 \<turnstile> inst \<rho>0 a : U)" if "tsol (tyenv env) \<rho>0" "cert_inst \<rho>0" for \<rho>0
    proof -
      from Cons.prems(4) that obtain e0 Us Vs where "bs_env \<rho>0 e0 rb" "e0 \<tturnstile> map (inst \<rho>0) targs : Us"
        "e0 \<tturnstile> map (inst \<rho>0) (a # as) : Vs" by blast
      then show ?thesis by (cases Vs) auto
    qed
    then show "\<forall>\<rho>0. tsol (tyenv env) \<rho>0 \<longrightarrow> cert_inst \<rho>0 \<longrightarrow>
      (\<exists>e0 Us Vs. bs_env \<rho>0 e0 rb \<and> e0 \<tturnstile> map (inst \<rho>0) targs : Us \<and> e0 \<tturnstile> map (inst \<rho>0) as : Vs)"
      "mcp_tok env rb targs a" unfolding mcp_tok_def by blast+
  qed
  have lbs': "length bs' = length as" using Cons.prems(6) bsc by simp
  have tyb': "\<forall>i<length bs'. pushes mcp_e0 Ss \<turnstile> bs' ! i : Bs' ! i \<and> no_redex (bs' ! i) \<and>
      \<not> loose_bvar (bs' ! i) (ilength Ss) \<and> types_abs Ss (bs' ! i) \<degree>\<degree> map (ap \<rho> \<sigma>) targs \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma> (as ! i)"
  proof (intro allI impI)
    fix i assume "i < length bs'"
    then show "pushes mcp_e0 Ss \<turnstile> bs' ! i : Bs' ! i \<and> no_redex (bs' ! i) \<and>
      \<not> loose_bvar (bs' ! i) (ilength Ss) \<and> types_abs Ss (bs' ! i) \<degree>\<degree> map (ap \<rho> \<sigma>) targs \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma> (as ! i)"
      using spec[OF Cons.prems(7), of "Suc i"] bsc Bsc by simp
  qed
  have tyb0: "pushes mcp_e0 Ss \<turnstile> b0 : B0" and nrb0: "no_redex b0" and lbb0: "\<not> loose_bvar b0 (ilength Ss)"
    and cvb0: "types_abs Ss b0 \<degree>\<degree> map (ap \<rho> \<sigma>) targs \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma> a"
    using spec[OF Cons.prems(7), of 0] bsc Bsc by simp_all
  have IH': "\<exists>sq. okW (mc cfg vname rb targs u1 env1 dps1) sq \<and>
      (\<exists>x. ev cfg sq x \<and> (\<exists>m. mcp_cres A1 K1 X1 env1 rb targs u1 \<rho>1 \<sigma>1 Ss UU1 (bs' ! j) m x))"
    if "j < length bs'" "mcp_pre A1 K1 X1 env1 dps1 rb targs u1"
      "mcp_spre \<rho>1 \<sigma>1 env1 dps1 X1 A1 e rb targs Ss u1 UU1 (bs' ! j)"
      "mcp_kokK (nat_of_integer (cfg_arity_bound cfg)) \<rho>1 (tyenv env1) A1 K1"
    for j A1 K1 X1 env1 dps1 u1 \<rho>1 \<sigma>1 UU1
    using Cons.prems(8)[of "Suc j" A1 K1 X1 env1 dps1 u1 \<rho>1 \<sigma>1 UU1] that bsc by simp
  have IH0: "\<exists>sq. okW (mc cfg vname rb targs u1 env1 dps1) sq \<and>
      (\<exists>x. ev cfg sq x \<and> (\<exists>m. mcp_cres A1 K1 X1 env1 rb targs u1 \<rho>1 \<sigma>1 Ss UU1 b0 m x))"
    if "mcp_pre A1 K1 X1 env1 dps1 rb targs u1"
      "mcp_spre \<rho>1 \<sigma>1 env1 dps1 X1 A1 e rb targs Ss u1 UU1 b0"
      "mcp_kokK (nat_of_integer (cfg_arity_bound cfg)) \<rho>1 (tyenv env1) A1 K1"
    for A1 K1 X1 env1 dps1 u1 \<rho>1 \<sigma>1 UU1
    using Cons.prems(8)[of 0 A1 K1 X1 env1 dps1 u1 \<rho>1 \<sigma>1 UU1] that bsc by simp
  from Cons.IH[OF va' tva' la' tok' tyas lbs' tyb' IH'] obtain x1 where
    ev1: "ev cfg (copyargs vname rb targs env dps as) x1" and dr1: "mcp_dres A K X env rb targs as \<rho> \<sigma> Ss Bs' bs' x1"
    by blast
  from dr1 obtain uas1 env1 dps1 A1 K1 X1 \<rho>1 \<sigma>1 NV1 where d: "x1 = El_D uas1 env1 dps1"
    "finite X1" "finite K1" "A \<subseteq> A1" "K \<subseteq> K1" "X \<subseteq> X1" "sinv A1 K1 X1 env1 dps1"
    "scinv \<rho>1 \<sigma>1 env1 dps1 X1 A1" "extends env env1" "tvars_env (tyenv env) \<subseteq> tvars_env (tyenv env1)"
    "tagree (maxidx env) \<rho> \<rho>1" "sagree (maxidx env) \<sigma> \<sigma>1" "length uas1 = length as"
    "mlvars uas1 \<subseteq> X1 \<union> evars env1" "(\<Union>t\<in>set uas1. ttvars t) \<subseteq> tvars_env (tyenv env1) \<union> A1"
    "\<forall>t\<in>set uas1. \<not> loose_bvar t (ilength Ss)"
    "\<forall>\<rho>0 e Us Vs. tsol (tyenv env1) \<rho>0 \<longrightarrow> cert_inst \<rho>0 \<longrightarrow> bs_env \<rho>0 e rb \<longrightarrow>
        e \<tturnstile> map (inst \<rho>0) targs : Us \<longrightarrow> e \<tturnstile> map (inst \<rho>0) as : Vs \<longrightarrow>
        (\<forall>e'. pushes e' Us \<tturnstile> map (inst \<rho>0) uas1 : Vs)"
    "pushes mcp_e0 Ss \<tturnstile> map (inst \<rho>1) uas1 : Bs'"
    "\<forall>i<length as. types_abs Ss (ap \<rho>1 \<sigma>1 (uas1 ! i)) \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> types_abs Ss (bs' ! i)"
    "finite NV1" "NV1 \<subseteq> X1" "\<forall>y\<in>NV1. maxidx env < snd (fst y)" "ubv env1 X1 \<subseteq> ubv env X \<union> fst ` NV1"
    "(\<Sum>y\<in>NV1. mcp_vsz \<rho>1 \<sigma>1 y) \<le> sum_list (map (\<lambda>(b, B). lsz (pushes mcp_e0 Ss) b - 2 * arity B) (zip bs' Bs'))"
    "\<forall>k. mcp_kokK k \<rho> (tyenv env) A K \<longrightarrow> mcp_kokK k \<rho>1 (tyenv env1) A1 K1"
    by (rule mcp_dresE)
  have mx: "maxidx env \<le> maxidx env1" using d(9) by (simp add: extends_def)
  have old: "ap \<rho>1 \<sigma>1 t = ap \<rho> \<sigma> t" "inst \<rho>1 t = inst \<rho> t"
    if "vars t \<subseteq> X \<union> evars env" "ttvars t \<subseteq> tvars_env (tyenv env) \<union> A" for t
    using mcp_agree_old[OF inv d(11) d(12) that] by simp_all
  have oldt: "ap \<rho>1 \<sigma>1 t = ap \<rho> \<sigma> t" "inst \<rho>1 t = inst \<rho> t" if "t \<in> set targs" for t
    using old[of t] vt tvt that by blast+
  \<comment> \<open>The head argument is copied in the new problem:\<close>
  have kk1: "mcp_kokK (nat_of_integer (cfg_arity_bound cfg)) \<rho>1 (tyenv env1) A1 K1" using d(25) kk by blast
  have vt1: "mlvars targs \<subseteq> X1 \<union> evars env1" using vt d(6) mcp_evars_extends[OF d(9)] by blast
  have tvt1: "(\<Union>t\<in>set targs. ttvars t) \<union> btvars rb \<subseteq> tvars_env (tyenv env1) \<union> A1" using tvt d(4) d(10) by blast
  have va1: "vars a \<subseteq> X1 \<union> evars env1" using va0 d(6) mcp_evars_extends[OF d(9)] by blast
  have tva1: "ttvars a \<subseteq> tvars_env (tyenv env1) \<union> A1" using tva0 d(4) d(10) by blast
  have toka1: "mcp_tok env1 rb targs a" by (rule mcp_tok_extends[OF toka d(9)])
  have bs1: "bs_env \<rho>1 e rb" by (rule bs_env_agree[OF bs d(11) below_KN]) (use tvt in blast)
  have tyt1: "e \<tturnstile> map (inst \<rho>1) targs : Ss" using tyt oldt(2) by (simp cong: map_cong)
  have tya1: "e \<turnstile> inst \<rho>1 a : B0" using tya0 old(2)[OF va0 tva0] by simp
  have cvb1: "types_abs Ss b0 \<degree>\<degree> map (ap \<rho>1 \<sigma>1) targs \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho>1 \<sigma>1 a"
    using cvb0 oldt(1) old(1)[OF va0 tva0] by (simp cong: map_cong)
  from mcp_copycons[OF cfg d(2) d(3) d(7) d(8) kk1 vt1 tvt1 lt va1 tva1 la0 toka1 bs1 tyt1 tya1 tyb0 nrb0 lbb0 cvb1 IH0]
  obtain cs a' env2 dps2 where cs: "okW (copycons cfg vname rb targs a uas1 env1 dps1) cs"
    and evcs: "ev cfg cs (El_D (a' # uas1) env2 dps2)"
    and cr: "mcp_cres A1 K1 X1 env1 rb targs a \<rho>1 \<sigma>1 Ss B0 b0 0 (El_C a' env2 dps2)" by blast
  from cr obtain u2 env3 dps3 A2 K2 X2 \<rho>2 \<sigma>2 NV2 where c: "El_C a' env2 dps2 = El_C u2 env3 dps3"
    "finite X2" "finite K2" "A1 \<subseteq> A2" "K1 \<subseteq> K2" "X1 \<subseteq> X2"
    "sinv A2 K2 X2 env3 dps3" "scinv \<rho>2 \<sigma>2 env3 dps3 X2 A2" "extends env1 env3"
    "tvars_env (tyenv env1) \<subseteq> tvars_env (tyenv env3)" "tagree (maxidx env1) \<rho>1 \<rho>2" "sagree (maxidx env1) \<sigma>1 \<sigma>2"
    "vars u2 \<subseteq> X2 \<union> evars env3" "ttvars u2 \<subseteq> tvars_env (tyenv env3) \<union> A2" "\<not> loose_bvar u2 (ilength Ss)"
    "\<forall>\<rho>0 e Us U. tsol (tyenv env3) \<rho>0 \<longrightarrow> cert_inst \<rho>0 \<longrightarrow> bs_env \<rho>0 e rb \<longrightarrow>
      e \<tturnstile> map (inst \<rho>0) targs : Us \<longrightarrow> e \<turnstile> inst \<rho>0 a : U \<longrightarrow> (\<forall>e'. pushes e' Us \<turnstile> inst \<rho>0 u2 : U)"
    "pushes mcp_e0 Ss \<turnstile> inst \<rho>2 u2 : B0" "types_abs Ss (ap \<rho>2 \<sigma>2 u2) \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> types_abs Ss b0"
    "finite NV2" "NV2 \<subseteq> X2" "\<forall>y\<in>NV2. maxidx env1 < snd (fst y)" "ubv env3 X2 \<subseteq> ubv env1 X1 \<union> fst ` NV2"
    "(\<Sum>y\<in>NV2. mcp_vsz \<rho>2 \<sigma>2 y) + 0 \<le> lsz (pushes mcp_e0 Ss) b0 - 2 * arity B0"
    "\<forall>k. mcp_kokK k \<rho>1 (tyenv env1) A1 K1 \<longrightarrow> mcp_kokK k \<rho>2 (tyenv env3) A2 K2"
    by (rule mcp_cresE)
  from c(1) have eqs: "a' = u2" "env2 = env3" "dps2 = dps3" by simp_all
  have ev2: "ev cfg (copyargs vname rb targs env dps (a # as)) (El_D (u2 # uas1) env3 dps3)"
    using ev.maps[OF ev1[unfolded d(1)] cs evcs] eqs by simp
  \<comment> \<open>The old copies keep their values:\<close>
  have old1: "ap \<rho>2 \<sigma>2 t = ap \<rho>1 \<sigma>1 t" "inst \<rho>2 t = inst \<rho>1 t" if "t \<in> set uas1" for t
  proof -
    have "vars t \<subseteq> X1 \<union> evars env1" "ttvars t \<subseteq> tvars_env (tyenv env1) \<union> A1" using d(14,15) that by blast+
    from mcp_agree_old[OF d(8) c(11) c(12) this] show "ap \<rho>2 \<sigma>2 t = ap \<rho>1 \<sigma>1 t" "inst \<rho>2 t = inst \<rho>1 t" by simp_all
  qed
  have sum: "(\<Sum>y\<in>NV1 \<union> NV2. mcp_vsz \<rho>2 \<sigma>2 y) \<le>
      sum_list (map (\<lambda>(b, B). lsz (pushes mcp_e0 Ss) b - 2 * arity B) (zip bs Bs))"
  proof -
    have "(\<Sum>y\<in>NV1 \<union> NV2. mcp_vsz \<rho>2 \<sigma>2 y) \<le> (\<Sum>y\<in>NV1. mcp_vsz \<rho>2 \<sigma>2 y) + (\<Sum>y\<in>NV2. mcp_vsz \<rho>2 \<sigma>2 y)"
      using sum_Un_nat[OF d(20) c(19), of "mcp_vsz \<rho>2 \<sigma>2"] by linarith
    moreover have "(\<Sum>y\<in>NV1. mcp_vsz \<rho>2 \<sigma>2 y) = (\<Sum>y\<in>NV1. mcp_vsz \<rho>1 \<sigma>1 y)"
      by (rule sum.cong[OF refl mcp_vsz_agree_X[OF d(8) c(11) c(12)]]) (use d(21) in blast)
    ultimately show ?thesis using d(24) c(23) bsc Bsc by simp
  qed
  have "mcp_dres A K X env rb targs (a # as) \<rho> \<sigma> Ss Bs bs (El_D (u2 # uas1) env3 dps3)"
  proof (rule mcp_dresI[OF refl c(2) c(3) _ _ _ c(7) c(8) extends_trans[OF d(9) c(9)] _
        tagree_trans[OF d(11) c(11) mx] sagree_trans[OF d(12) c(12) mx] _ _ _ _ _ _ _ _ _ _ _ sum])
    show "A \<subseteq> A2" "K \<subseteq> K2" "X \<subseteq> X2" using d(4-6) c(4-6) by blast+
    show "tvars_env (tyenv env) \<subseteq> tvars_env (tyenv env3)" using d(10) c(10) by blast
    show "length (u2 # uas1) = length (a # as)" using d(13) by simp
    show "mlvars (u2 # uas1) \<subseteq> X2 \<union> evars env3" using c(13) d(14) c(6) mcp_evars_extends[OF c(9)] by auto
    show "(\<Union>t\<in>set (u2 # uas1). ttvars t) \<subseteq> tvars_env (tyenv env3) \<union> A2" using c(14) d(15) c(4) c(10) by auto
    show "\<forall>t\<in>set (u2 # uas1). \<not> loose_bvar t (ilength Ss)" using c(15) d(16) by simp
    show "\<forall>\<rho>0 e Us Vs. tsol (tyenv env3) \<rho>0 \<longrightarrow> cert_inst \<rho>0 \<longrightarrow> bs_env \<rho>0 e rb \<longrightarrow>
        e \<tturnstile> map (inst \<rho>0) targs : Us \<longrightarrow> e \<tturnstile> map (inst \<rho>0) (a # as) : Vs \<longrightarrow>
        (\<forall>e'. pushes e' Us \<tturnstile> map (inst \<rho>0) (u2 # uas1) : Vs)"
    proof (intro allI impI)
      fix \<rho>0 e0 Us Vs e' assume a: "tsol (tyenv env3) \<rho>0" "cert_inst \<rho>0" "bs_env \<rho>0 e0 rb"
        "e0 \<tturnstile> map (inst \<rho>0) targs : Us" "e0 \<tturnstile> map (inst \<rho>0) (a # as) : Vs"
      from a(5) obtain V0 Vs' where Vs: "Vs = V0 # Vs'" "e0 \<turnstile> inst \<rho>0 a : V0" "e0 \<tturnstile> map (inst \<rho>0) as : Vs'"
        by (cases Vs) auto
      have "pushes e' Us \<turnstile> inst \<rho>0 u2 : V0" using c(16) a(1-4) Vs(2) by blast
      moreover have "pushes e' Us \<tturnstile> map (inst \<rho>0) uas1 : Vs'"
        using d(17) extends_tsol[OF a(1) c(9)] a(2-4) Vs(3) by blast
      ultimately show "pushes e' Us \<tturnstile> map (inst \<rho>0) (u2 # uas1) : Vs" using Vs(1) by simp
    qed
    show "pushes mcp_e0 Ss \<tturnstile> map (inst \<rho>2) (u2 # uas1) : Bs"
      using c(17) d(18) old1(2) Bsc by (simp cong: map_cong)
    show "\<forall>i<length (a # as). types_abs Ss (ap \<rho>2 \<sigma>2 ((u2 # uas1) ! i)) \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> types_abs Ss (bs ! i)"
    proof (intro allI impI)
      fix i assume "i < length (a # as)"
      then show "types_abs Ss (ap \<rho>2 \<sigma>2 ((u2 # uas1) ! i)) \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> types_abs Ss (bs ! i)"
      proof (cases i)
        case 0
        then show ?thesis using c(18) bsc by simp
      next
        case (Suc j)
        with \<open>i < length (a # as)\<close> have j: "j < length as" by simp
        then have "uas1 ! j \<in> set uas1" using d(13) by simp
        then show ?thesis using d(19) j old1(1) Suc bsc by simp
      qed
    qed
    show "finite (NV1 \<union> NV2)" using d(20) c(19) by simp
    show "NV1 \<union> NV2 \<subseteq> X2" using d(21) c(6) c(20) by blast
    show "\<forall>y\<in>NV1 \<union> NV2. maxidx env < snd (fst y)" using d(22) c(21) mx by fastforce
    show "ubv env3 X2 \<subseteq> ubv env X \<union> fst ` (NV1 \<union> NV2)" using c(22) d(23) by blast
    show "\<forall>k. mcp_kokK k \<rho> (tyenv env) A K \<longrightarrow> mcp_kokK k \<rho>2 (tyenv env3) A2 K2" using d(25) c(24) by blast
  qed
  with ev2 show ?case by blast
qed


subsection \<open>Copies: rigid heads\<close>

lemma mcp_cert_Ss:
  assumes "mcp_pre A K X env dps rb targs u" "mcp_spre \<rho> \<sigma> env dps X A e rb targs Ss u UU s"
  shows "\<forall>S\<in>set Ss. cert_typ alg ar S"
proof
  fix S assume S: "S \<in> set Ss"
  have bs: "bs_env \<rho> e rb" and tyt: "e \<tturnstile> map (inst \<rho>) targs : Ss" using assms(2) by (simp_all add: mcp_spre_def)
  have lt: "\<forall>t\<in>set targs. \<not> loose_bvar t (ilength rb)" using assms(1) by (simp add: mcp_pre_def)
  from S obtain i where i: "i < length Ss" "S = Ss ! i" by (auto simp: in_set_conv_nth)
  from typings_nth[OF tyt] i have "i < length targs" "e \<turnstile> inst \<rho> (targs ! i) : S" by auto
  then show "cert_typ alg ar S" using bs_env_cert[OF bs] lt by (meson nth_mem)
qed

text \<open>The head of a target of a rigid term that is not a projection is the head of the term:\<close>

lemma mcp_target_rigid:
  assumes pre: "mcp_pre A K X env dps rb targs u" and sp: "mcp_spre \<rho> \<sigma> env dps X A e rb targs Ss u UU s"
    and r: "rigid (fst (strip_comb u))" and sh: "s = h' \<degree>\<degree> bs" "atom h'" "closed h'"
  shows "h' = inst \<rho> (fst (strip_comb u))"
    "list_all2 (\<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta>) (map (mcp_cpy (map (ap \<rho> \<sigma>) targs)) bs) (map (ap \<rho> \<sigma>) (snd (strip_comb u)))"
proof -
  from sp have inv: "scinv \<rho> \<sigma> env dps X A" and tyt: "e \<tturnstile> map (inst \<rho>) targs : Ss"
    and tys: "pushes mcp_e0 Ss \<turnstile> s : UU" and lbs: "\<not> loose_bvar s (ilength Ss)"
    and cv: "types_abs Ss s \<degree>\<degree> map (ap \<rho> \<sigma>) targs \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma> u"
    unfolding mcp_spre_def by blast+
  note sd = solutionD[OF scinvD(1)[OF inv]]
  let ?ts = "map (ap \<rho> \<sigma>) targs"
  have cS: "\<forall>S\<in>set Ss. cert_typ alg ar S" by (rule mcp_cert_Ss[OF pre sp])
  have tapt: "e \<tturnstile> ?ts : Ss"
    using tyt by (induction targs arbitrary: Ss) (auto split: list.splits intro: typing_ap[OF _ sd(3)])
  have tcs: "e \<turnstile> types_abs Ss s \<degree>\<degree> ?ts : UU" by (rule list_app_typeI[OF mcp_typing_val[OF tys lbs cS] tapt])
  have lSs: "length Ss = length ?ts" using typings_nth[OF tapt] by simp
  note cc = mcp_conv_cpy[OF tcs lSs]
  have cps: "mcp_cpy ?ts s = h' \<degree>\<degree> map (mcp_cpy ?ts) bs" by (simp add: sh(1) mcp_cpy_apps mcp_cpy_closed[OF sh(3)])
  have u: "u = fst (strip_comb u) \<degree>\<degree> snd (strip_comb u)" by (rule strip_comb_apps) simp
  have apu: "ap \<rho> \<sigma> u = inst \<rho> (fst (strip_comb u)) \<degree>\<degree> map (ap \<rho> \<sigma>) (snd (strip_comb u))"
    by (subst u) (simp add: ap_apps rigid_ap[OF r])
  have "h' \<degree>\<degree> map (mcp_cpy ?ts) bs \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> inst \<rho> (fst (strip_comb u)) \<degree>\<degree> map (ap \<rho> \<sigma>) (snd (strip_comb u))"
    using conv_trans[OF conv_sym[OF cc(1)] cv] cps apu by simp
  moreover have "wt (h' \<degree>\<degree> map (mcp_cpy ?ts) bs)" using cc(2) cps by (auto simp: wt_def)
  ultimately show "h' = inst \<rho> (fst (strip_comb u))"
    "list_all2 (\<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta>) (map (mcp_cpy ?ts) bs) (map (ap \<rho> \<sigma>) (snd (strip_comb u)))"
    using conv_atom_apps_inv[OF sh(2) rigid_inst[OF r]] by blast+
qed

lemma mcp_mc_proj:
  assumes cfg: "cfg_alg cfg = alg"
    and pre: "mcp_pre A K X env dps rb targs u" and sp: "mcp_spre \<rho> \<sigma> env dps X A e rb targs Ss u UU s"
    and kk: "mcp_kokK (nat_of_integer (cfg_arity_bound cfg)) \<rho> (tyenv env) A K"
    and r: "rigid (fst (strip_comb u))"
    and sB: "s = Bound j \<degree>\<degree> bs" "0 \<le> j" "j < ilength Ss"
  shows "\<exists>sq. okW (mc cfg vname rb targs u env dps) sq \<and>
    (\<exists>x. ev cfg sq x \<and> mcp_cres A K X env rb targs u \<rho> \<sigma> Ss UU s 1 x)"
proof -
  let ?\<theta> = "tyenv env" and ?KN = "tvars_env (tyenv env) \<union> A" and ?uh = "fst (strip_comb u)"
  have si: "sinv A K X env dps" and finK: "finite K" and tok: "mcp_tok env rb targs u"
    using pre by (simp_all add: mcp_pre_def)
  have ei: "einv A K env" using si by (simp add: sinv_def)
  note x = einvD[OF ei] and r0 = einv_rho0[OF ei]
  have kok0: "mcp_kok (nat_of_integer (cfg_arity_bound cfg)) \<rho> ?\<theta> ?KN" by (rule mcp_kokK_kok[OF kk ei])
  from mcp_mc_types[OF pre] obtain T0 base Ts where
    ty0: "fastype env rb ?uh = return T0" "body_type env T0 = return base"
      "mapM (fastype env rb) targs = return Ts" "tvars T0 \<subseteq> ?KN" "tvars base \<subseteq> ?KN" "\<forall>T\<in>set Ts. tvars T \<subseteq> ?KN"
    by blast
  have na: "\<not> is_Abs ?uh" using r by (cases ?uh) auto
  have ty0': "ok (fastype env rb ?uh) T0" "ok (body_type env T0) base" "ok (mapM (fastype env rb) targs) Ts"
    using ty0 by (simp_all add: return_def)
  have lT: "length Ts = length targs" using ty0'(3) by (simp add: ok_mapM list_all2_lengthD)
  from make_projs_term[OF lT, of u targs] obtain projs where mp: "okW (make_projs u targs Ts targs) projs" by blast
  from tok r0 obtain e0 Us0 U0 where t0: "bs_env (rho0 env) e0 rb" "e0 \<tturnstile> map (inst (rho0 env)) targs : Us0"
    "e0 \<turnstile> inst (rho0 env) u : U0" unfolding mcp_tok_def by blast
  note tr0 = mcp_types_sound[OF pre ty0' na r0(1) t0]
  have cTs0: "\<forall>T\<in>set Ts. cert_typ alg ar (tnorm ?\<theta> T)" using tr0(1,3) by simp
  have cb0: "cert_typ alg ar (tnorm ?\<theta> base)" using tr0(2,4) by simp
  have tvT: "\<forall>(bvar, T, targ)\<in>set (rev projs). tvars T \<subseteq> ?KN \<and> cert_typ alg ar (tnorm ?\<theta> T)"
    using mf_make_projs_props[OF mp] ty0(6) cTs0 lT by (fastforce dest: nth_mem)
  from mcp_matchfun[OF cfg finK si ty0(5) cb0 tvT, of vname rb targs u ?uh "snd (strip_comb u)" Ts]
  obtain sq where mf: "okW (matchfun cfg vname rb targs u env dps ?uh (snd (strip_comb u)) base Ts (rev projs)) sq"
    and pj: "\<forall>(bvar, T, targ)\<in>set (rev projs). \<forall>Us bary. ok (strip_type env T) (Us, bary) \<longrightarrow>
      (\<forall>p\<in>set (arity_guesses cfg bary). \<forall>env0 Cs env'. gentvars p env = (env0, Cs) \<longrightarrow>
        okW (proj_unify cfg base bary Cs env0) env' \<longrightarrow>
        mcp_projel cfg vname env' Ts (Us @ Cs) targs rb u dps bvar targ sq)"
    by blast
  have mc: "okW (mc cfg vname rb targs u env dps) sq"
    using mf mp r ty0(1,2) by (subst mc.simps) (cases ?uh; auto simp: Let_def ty0(3) return_def)
  have lSs: "length Ss = length targs"
    using sp lT by (simp add: mcp_spre_def) (metis typings_nth length_map)
  define k where "k = length targs - 1 - nat_of_integer j"
  have jn: "nat_of_integer j < length targs" using sB(2,3) lSs nat_of_integer_less_ilength by fastforce
  have kn: "k < length targs" using jn by (simp add: k_def)
  have jk: "Bound (integer_of_nat (length targs - 1 - k)) = Bound j"
    using jn sB(2) by (simp add: k_def integer_eq_iff integer_of_nat.rep_eq nat_of_integer.rep_eq less_eq_integer.rep_eq)
  have tvTk: "tvars (Ts ! k) \<subseteq> ?KN" using ty0(6) kn lT by simp
  from binder_types_term[OF x(2) refl tvTk] obtain Us where bU: "binder_types env (Ts ! k) = return Us" by blast
  from body_type_term[OF x(2) refl tvTk] obtain bary where bB: "body_type env (Ts ! k) = return bary" by blast
  have st: "ok (strip_type env (Ts ! k)) (Us, bary)" using bU bB by (simp add: strip_type_def return_def)
  from mcp_proj_elem[OF cfg pre sp kok0 ty0' ty0(5,6) na sB k_def st, of vname]
  obtain p env0 Cs env' where pg: "p \<in> set (arity_guesses cfg bary)" and g: "gentvars p env = (env0, Cs)"
    and pu: "okW (proj_unify cfg base bary Cs env0) env'"
    and el: "\<forall>env'' args. make_args vname Ts env' (Us @ Cs) = (env'', args) \<longrightarrow>
      (\<exists>env2 fr ff. okW (SIMPL (cfg_alg cfg) env''
          ((rb, list_comb (targs ! k) (map (\<lambda>arg. list_comb (head_of arg) targs) args), u) # dps)) (env2, fr, ff) \<and>
        mcp_cres A K X env rb targs u \<rho> \<sigma> Ss UU s 1 (El_C (list_comb (Bound j) args) env2 (fr @ ff)))"
    by blast
  obtain env'' args where ma: "make_args vname Ts env' (Us @ Cs) = (env'', args)" by fastforce
  from el ma obtain env2 fr ff where sm: "okW (SIMPL (cfg_alg cfg) env''
      ((rb, list_comb (targs ! k) (map (\<lambda>arg. list_comb (head_of arg) targs) args), u) # dps)) (env2, fr, ff)"
    and cr: "mcp_cres A K X env rb targs u \<rho> \<sigma> Ss UU s 1 (El_C (list_comb (Bound j) args) env2 (fr @ ff))" by blast
  have "(Bound (integer_of_nat (length targs - 1 - k)), Ts ! k, targs ! k) \<in> set (rev projs)"
    using mcp_make_projs_mem[OF mp kn] by simp
  with pj st pg g pu have "mcp_projel cfg vname env' Ts (Us @ Cs) targs rb u dps (Bound j) (targs ! k) sq"
    unfolding jk by fastforce
  with ma sm have "ev cfg sq (El_C (list_comb (Bound j) args) env2 (fr @ ff))" unfolding mcp_projel_def by blast
  with mc cr show ?thesis by blast
qed


lemma mcp_sum_zip_le:
  "sum_list (map (\<lambda>(b, B). g b - (h B :: nat)) (zip bs Bs)) \<le> sum_list (map g bs)"
proof (induction bs arbitrary: Bs)
  case (Cons b bs)
  then show ?case by (cases Bs) (auto intro: add_mono)
qed simp

lemma mcp_closed_typed_atom:
  "e \<turnstile> c : T \<Longrightarrow> (\<exists>n S. c = Const n S) \<or> (\<exists>n S. c = Free n S) \<Longrightarrow> e' \<turnstile> c : T"
  by auto

lemma mcp_mc_imit:
  assumes cfg: "cfg_alg cfg = alg"
    and pre: "mcp_pre A K X env dps rb targs u" and sp: "mcp_spre \<rho> \<sigma> env dps X A e rb targs Ss u UU s"
    and kk: "mcp_kokK (nat_of_integer (cfg_arity_bound cfg)) \<rho> (tyenv env) A K"
    and r: "rigid (fst (strip_comb u))"
    and sC: "s = c \<degree>\<degree> bs" "(\<exists>n S. c = Const n S) \<or> (\<exists>n S. c = Free n S)"
    and IH: "\<And>i A K X env dps u \<rho> \<sigma> UU. i < length bs \<Longrightarrow> mcp_pre A K X env dps rb targs u \<Longrightarrow>
      mcp_spre \<rho> \<sigma> env dps X A e rb targs Ss u UU (bs ! i) \<Longrightarrow>
      mcp_kokK (nat_of_integer (cfg_arity_bound cfg)) \<rho> (tyenv env) A K \<Longrightarrow>
      \<exists>sq. okW (mc cfg vname rb targs u env dps) sq \<and>
        (\<exists>x. ev cfg sq x \<and> (\<exists>m. mcp_cres A K X env rb targs u \<rho> \<sigma> Ss UU (bs ! i) m x))"
  shows "\<exists>sq. okW (mc cfg vname rb targs u env dps) sq \<and>
    (\<exists>x. ev cfg sq x \<and> mcp_cres A K X env rb targs u \<rho> \<sigma> Ss UU s 1 x)"
proof -
  let ?\<theta> = "tyenv env" and ?KN = "tvars_env (tyenv env) \<union> A" and ?uh = "fst (strip_comb u)"
    and ?ua = "snd (strip_comb u)"
  from pre have finX: "finite X" and finK: "finite K" and si: "sinv A K X env dps"
    and vu: "vars u \<subseteq> X \<union> evars env" and vt: "mlvars targs \<subseteq> X \<union> evars env"
    and tv: "ttvars u \<union> (\<Union>t\<in>set targs. ttvars t) \<union> btvars rb \<subseteq> ?KN"
    and lu: "\<not> loose_bvar u (ilength rb)" and lt: "\<forall>t\<in>set targs. \<not> loose_bvar t (ilength rb)"
    and tok: "mcp_tok env rb targs u"
    unfolding mcp_pre_def by blast+
  from sp have inv: "scinv \<rho> \<sigma> env dps X A" and bs: "bs_env \<rho> e rb"
    and tyt: "e \<tturnstile> map (inst \<rho>) targs : Ss" and tyu: "e \<turnstile> inst \<rho> u : UU" and ar: "arity UU = nabs u"
    and tys: "pushes mcp_e0 Ss \<turnstile> s : UU" and nrs: "no_redex s" and lbs: "\<not> loose_bvar s (ilength Ss)"
    and cv: "types_abs Ss s \<degree>\<degree> map (ap \<rho> \<sigma>) targs \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma> u"
    unfolding mcp_spre_def by blast+
  have ei: "einv A K env" using si by (simp add: sinv_def)
  note x = einvD[OF ei] and r0 = einv_rho0[OF ei] and i = scinvD[OF inv] and sd = solutionD[OF scinvD(1)[OF inv]]
  have u: "u = ?uh \<degree>\<degree> ?ua" by (rule strip_comb_apps) simp
  have na: "\<not> is_Abs ?uh" using r by (cases ?uh) auto
  have ar0: "arity UU = 0" using ar na u is_Abs_apps by (metis nabs_nonAbs)
  have cc: "closed c" "atom c" using sC(2) by (auto simp: closed_def)
  note tr = mcp_target_rigid[OF pre sp r sC(1) cc(2,1)]
  have uhc: "(\<exists>n S. ?uh = Const n S) \<or> (\<exists>n S. ?uh = Free n S)" using tr(1) sC(2) r by (cases ?uh) auto
  have cS: "\<forall>S\<in>set Ss. cert_typ alg ar S" by (rule mcp_cert_Ss[OF pre sp])
  let ?ts = "map (ap \<rho> \<sigma>) targs"
  have tapt: "e \<tturnstile> ?ts : Ss"
    using tyt by (induction targs arbitrary: Ss) (auto split: list.splits intro: typing_ap[OF _ sd(3)])
  have lSs: "length Ss = length ?ts" using typings_nth[OF tapt] by simp
  \<comment> \<open>The types of the arguments:\<close>
  from tys[unfolded sC(1)] obtain Bs where tyc: "pushes mcp_e0 Ss \<turnstile> c : Bs \<Rrightarrow> UU"
    and tybs: "pushes mcp_e0 Ss \<tturnstile> bs : Bs" by (rule list_app_typeE)
  from tyu[unfolded u[THEN arg_cong[of _ _ "inst \<rho>"]] inst_apps] obtain Vs where tyh: "e \<turnstile> inst \<rho> ?uh : Vs \<Rrightarrow> UU"
    and tya: "e \<tturnstile> map (inst \<rho>) ?ua : Vs" by (rule list_app_typeE)
  have lba: "length bs = length ?ua" using list_all2_lengthD[OF tr(2)] by simp
  have "Vs \<Rrightarrow> UU = Bs \<Rrightarrow> UU"
    using tyh tyc tr(1) mcp_closed_typed_atom[OF tyc sC(2), of e] typing_unique by metis
  moreover have "length Vs = length Bs" using typings_nth[OF tya] typings_nth[OF tybs] lba by simp
  ultimately have VB: "Vs = Bs" using funs_eq by blast
  \<comment> \<open>The sequence of the imitation:\<close>
  from mcp_mc_types[OF pre] obtain T0 base Ts where
    ty0: "fastype env rb ?uh = return T0" "body_type env T0 = return base"
      "mapM (fastype env rb) targs = return Ts" "tvars T0 \<subseteq> ?KN" "tvars base \<subseteq> ?KN" "\<forall>T\<in>set Ts. tvars T \<subseteq> ?KN"
    by blast
  have ty0': "ok (fastype env rb ?uh) T0" "ok (body_type env T0) base" "ok (mapM (fastype env rb) targs) Ts"
    using ty0 by (simp_all add: return_def)
  have lT: "length Ts = length targs" using ty0'(3) by (simp add: ok_mapM list_all2_lengthD)
  from make_projs_term[OF lT, of u targs] obtain projs where mp: "okW (make_projs u targs Ts targs) projs" by blast
  from tok r0 obtain e0 Us0 U0 where t0: "bs_env (rho0 env) e0 rb" "e0 \<tturnstile> map (inst (rho0 env)) targs : Us0"
    "e0 \<turnstile> inst (rho0 env) u : U0" unfolding mcp_tok_def by blast
  note tr0 = mcp_types_sound[OF pre ty0' na r0(1) t0]
  have cTs0: "\<forall>T\<in>set Ts. cert_typ alg ar (tnorm ?\<theta> T)" using tr0(1,3) by simp
  have cb0: "cert_typ alg ar (tnorm ?\<theta> base)" using tr0(2,4) by simp
  have tvT: "\<forall>(bvar, T, targ)\<in>set (rev projs). tvars T \<subseteq> ?KN \<and> cert_typ alg ar (tnorm ?\<theta> T)"
    using mf_make_projs_props[OF mp] ty0(6) cTs0 lT by (fastforce dest: nth_mem)
  from mcp_matchfun[OF cfg finK si ty0(5) cb0 tvT, of vname rb targs u ?uh ?ua Ts]
  obtain sq where mf: "okW (matchfun cfg vname rb targs u env dps ?uh ?ua base Ts (rev projs)) sq"
    and im: "\<forall>x. ev cfg (case ?uh of
        Const _ _ \<Rightarrow> S_MapJoin ?uh (copyargs vname rb targs env dps ?ua)
      | Free _ _ \<Rightarrow> S_MapJoin ?uh (copyargs vname rb targs env dps ?ua)
      | _ \<Rightarrow> S_Empty) x \<longrightarrow> ev cfg sq x"
    by blast
  have mc: "okW (mc cfg vname rb targs u env dps) sq"
    using mf mp r ty0(1,2) by (subst mc.simps) (cases ?uh; auto simp: Let_def ty0(3) return_def)
  have im': "ev cfg (S_MapJoin ?uh (copyargs vname rb targs env dps ?ua)) x \<Longrightarrow> ev cfg sq x" for x
    using im uhc by auto
  \<comment> \<open>The copies of the arguments:\<close>
  have toka: "\<forall>\<rho>0. tsol ?\<theta> \<rho>0 \<longrightarrow> cert_inst \<rho>0 \<longrightarrow>
      (\<exists>e0 Us Vs. bs_env \<rho>0 e0 rb \<and> e0 \<tturnstile> map (inst \<rho>0) targs : Us \<and> e0 \<tturnstile> map (inst \<rho>0) ?ua : Vs)"
  proof (intro allI impI)
    fix \<rho>0 assume "tsol ?\<theta> \<rho>0" "cert_inst \<rho>0"
    with tok obtain e0 Us U where t: "bs_env \<rho>0 e0 rb" "e0 \<tturnstile> map (inst \<rho>0) targs : Us" "e0 \<turnstile> inst \<rho>0 u : U"
      unfolding mcp_tok_def by blast
    from t(3)[unfolded u[THEN arg_cong[of _ _ "inst \<rho>0"]] inst_apps] obtain Ws where "e0 \<tturnstile> map (inst \<rho>0) ?ua : Ws"
      by (rule list_app_typeE)
    with t show "\<exists>e0 Us Vs. bs_env \<rho>0 e0 rb \<and> e0 \<tturnstile> map (inst \<rho>0) targs : Us \<and> e0 \<tturnstile> map (inst \<rho>0) ?ua : Vs"
      by blast
  qed
  have nrbs: "\<forall>b\<in>set bs. no_redex b" using nrs sC(1) no_redex_apps[of c bs] sC(2) by auto
  have lbbs: "\<forall>b\<in>set bs. \<not> loose_bvar b (ilength Ss)" using lbs sC(1) by (simp add: loose_bvar_apps)
  have tyb: "\<forall>i<length bs. pushes mcp_e0 Ss \<turnstile> bs ! i : Bs ! i \<and> no_redex (bs ! i) \<and> \<not> loose_bvar (bs ! i) (ilength Ss) \<and>
      types_abs Ss (bs ! i) \<degree>\<degree> ?ts \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma> (?ua ! i)"
  proof (intro allI impI conjI)
    fix i assume il: "i < length bs"
    show tb: "pushes mcp_e0 Ss \<turnstile> bs ! i : Bs ! i" using typings_nth[OF tybs] il by simp
    show "no_redex (bs ! i)" "\<not> loose_bvar (bs ! i) (ilength Ss)" using nrbs lbbs il by simp_all
    have "e \<turnstile> types_abs Ss (bs ! i) \<degree>\<degree> ?ts : Bs ! i"
      by (rule list_app_typeI[OF mcp_typing_val[OF tb _ cS] tapt]) (use lbbs il in simp)
    from mcp_conv_cpy(1)[OF this lSs] list_all2_nthD[OF tr(2), of i] il lba
    show "types_abs Ss (bs ! i) \<degree>\<degree> ?ts \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma> (?ua ! i)" by (auto intro: conv_trans)
  qed
  have va: "mlvars ?ua \<subseteq> X \<union> evars env" using vu u by (metis vars_apps Un_subset_iff)
  have tva: "(\<Union>t\<in>set ?ua. ttvars t) \<subseteq> ?KN" using tv u by (metis ttvars_apps Un_subset_iff)
  have la: "\<forall>t\<in>set ?ua. \<not> loose_bvar t (ilength rb)" using lu u by (metis loose_bvar_apps)
  from mcp_copyargs[OF cfg finX finK si inv kk vt _ lt va tva la toka bs tyt tya[unfolded VB] lba tyb IH]
  obtain x0 where ev0: "ev cfg (copyargs vname rb targs env dps ?ua) x0"
    and dr: "mcp_dres A K X env rb targs ?ua \<rho> \<sigma> Ss Bs bs x0" using tv by blast
  from dr obtain uas' env' dps' A' K' X' \<rho>' \<sigma>' NV where x0: "x0 = El_D uas' env' dps'"
    and d: "finite X'" "finite K'" "A \<subseteq> A'" "K \<subseteq> K'" "X \<subseteq> X'" "sinv A' K' X' env' dps'"
    "scinv \<rho>' \<sigma>' env' dps' X' A'" "extends env env'" "tvars_env (tyenv env) \<subseteq> tvars_env (tyenv env')"
    "tagree (maxidx env) \<rho> \<rho>'" "sagree (maxidx env) \<sigma> \<sigma>'" "length uas' = length ?ua"
    "mlvars uas' \<subseteq> X' \<union> evars env'" "(\<Union>t\<in>set uas'. ttvars t) \<subseteq> tvars_env (tyenv env') \<union> A'"
    "\<forall>t\<in>set uas'. \<not> loose_bvar t (ilength Ss)"
    and dty: "\<forall>\<rho>0 e Us Vs. tsol (tyenv env') \<rho>0 \<longrightarrow> cert_inst \<rho>0 \<longrightarrow> bs_env \<rho>0 e rb \<longrightarrow>
        e \<tturnstile> map (inst \<rho>0) targs : Us \<longrightarrow> e \<tturnstile> map (inst \<rho>0) ?ua : Vs \<longrightarrow>
        (\<forall>e'. pushes e' Us \<tturnstile> map (inst \<rho>0) uas' : Vs)"
    and d2: "pushes mcp_e0 Ss \<tturnstile> map (inst \<rho>') uas' : Bs"
    "\<forall>i<length ?ua. types_abs Ss (ap \<rho>' \<sigma>' (uas' ! i)) \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> types_abs Ss (bs ! i)"
    "finite NV" "NV \<subseteq> X'" "\<forall>y\<in>NV. maxidx env < snd (fst y)" "ubv env' X' \<subseteq> ubv env X \<union> fst ` NV"
    "(\<Sum>y\<in>NV. mcp_vsz \<rho>' \<sigma>' y) \<le> sum_list (map (\<lambda>(b, B). lsz (pushes mcp_e0 Ss) b - 2 * arity B) (zip bs Bs))"
    "\<forall>k. mcp_kokK k \<rho> (tyenv env) A K \<longrightarrow> mcp_kokK k \<rho>' (tyenv env') A' K'"
    by (rule mcp_dresE)
  have ev1: "ev cfg sq (El_C (list_comb ?uh uas') env' dps')"
    by (rule im', rule ev.map_join) (use ev0 x0 in simp)
  have tvh: "ttvars ?uh \<subseteq> ?KN" using tv ttvars_head[of u] by (simp add: head_of_strip_comb) blast
  have ih: "inst \<rho>' ?uh = c" using inst_agree[OF d(10) tvinv_tbelow[OF i(4) tvh]] tr(1) by simp
  have tyc': "pushes e' Us \<turnstile> inst \<rho>0 ?uh : T" if "e0 \<turnstile> inst \<rho>0 ?uh : T" for e' Us \<rho>0 e0 T
    using that uhc by auto
  have cr: "mcp_cres A K X env rb targs u \<rho> \<sigma> Ss UU s 1 (El_C (list_comb ?uh uas') env' dps')"
  proof (rule mcp_cresI[OF refl d(1-11)])
    show "vars (list_comb ?uh uas') \<subseteq> X' \<union> evars env'" using d(13) uhc by (auto simp: list_comb_apps vars_apps)
    show "ttvars (list_comb ?uh uas') \<subseteq> tvars_env (tyenv env') \<union> A'"
    proof -
      have "ttvars ?uh \<subseteq> ?KN" using tv ttvars_head[of u] by (simp add: head_of_strip_comb) blast
      then show ?thesis using d(14,3,9) by (auto simp: list_comb_apps ttvars_apps)
    qed
    show "\<not> loose_bvar (list_comb ?uh uas') (ilength Ss)" using d(15) uhc by (auto simp: list_comb_apps loose_bvar_apps)
    show "\<forall>\<rho>0 e Us U. tsol (tyenv env') \<rho>0 \<longrightarrow> cert_inst \<rho>0 \<longrightarrow> bs_env \<rho>0 e rb \<longrightarrow>
        e \<tturnstile> map (inst \<rho>0) targs : Us \<longrightarrow> e \<turnstile> inst \<rho>0 u : U \<longrightarrow> (\<forall>e'. pushes e' Us \<turnstile> inst \<rho>0 (list_comb ?uh uas') : U)"
    proof (intro allI impI)
      fix \<rho>0 e0 Us U e' assume a: "tsol (tyenv env') \<rho>0" "cert_inst \<rho>0" "bs_env \<rho>0 e0 rb"
        "e0 \<tturnstile> map (inst \<rho>0) targs : Us" "e0 \<turnstile> inst \<rho>0 u : U"
      from a(5)[unfolded u[THEN arg_cong[of _ _ "inst \<rho>0"]] inst_apps] obtain Ws where
        th: "e0 \<turnstile> inst \<rho>0 ?uh : Ws \<Rrightarrow> U" and ta: "e0 \<tturnstile> map (inst \<rho>0) ?ua : Ws" by (rule list_app_typeE)
      from dty a(1-4) ta have "pushes e' Us \<tturnstile> map (inst \<rho>0) uas' : Ws" by blast
      from list_app_typeI[OF tyc'[OF th] this] show "pushes e' Us \<turnstile> inst \<rho>0 (list_comb ?uh uas') : U"
        by (simp add: list_comb_apps inst_apps)
    qed
    have tyu': "pushes mcp_e0 Ss \<turnstile> inst \<rho>' (list_comb ?uh uas') : UU"
      using list_app_typeI[OF tyc d2(1)] ih by (simp add: list_comb_apps inst_apps)
    then show "pushes mcp_e0 Ss \<turnstile> inst \<rho>' (list_comb ?uh uas') : UU" .
    show "types_abs Ss (ap \<rho>' \<sigma>' (list_comb ?uh uas')) \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> types_abs Ss s"
    proof -
      have apc: "ap \<rho>' \<sigma>' (list_comb ?uh uas') = c \<degree>\<degree> map (ap \<rho>' \<sigma>') uas'"
        using ih r by (simp add: list_comb_apps ap_apps rigid_ap)
      have tap: "pushes mcp_e0 Ss \<tturnstile> map (ap \<rho>' \<sigma>') uas' : Bs"
        using d2(1) solutionD(3)[OF scinvD(1)[OF d(7)]]
        by (induction uas' arbitrary: Bs) (auto split: list.splits intro: typing_ap)
      have cvi: "ap \<rho>' \<sigma>' (uas' ! i) \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> bs ! i" if "i < length bs" for i
      proof (rule mcp_conv_types_abs_inv)
        show "mcp_e0 \<turnstile> types_abs Ss (ap \<rho>' \<sigma>' (uas' ! i)) : Ss \<Rrightarrow> (Bs ! i)"
          by (rule mf_typing_types_abs[OF _ cS]) (use typings_nth[OF tap] that lba d(12) in simp)
        show "mcp_e0 \<turnstile> types_abs Ss (bs ! i) : Ss \<Rrightarrow> (Bs ! i)"
          by (rule mf_typing_types_abs[OF _ cS]) (use typings_nth[OF tybs] that in simp)
        show "types_abs Ss (ap \<rho>' \<sigma>' (uas' ! i)) \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> types_abs Ss (bs ! i)" using d2(2) that lba by simp
      qed
      have c1: "c \<degree>\<degree> map (ap \<rho>' \<sigma>') uas' \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> c \<degree>\<degree> bs"
      proof (rule conv_apps[OF _ _ _ conv_refl])
        show "list_all2 (\<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta>) (map (ap \<rho>' \<sigma>') uas') bs"
          by (rule list_all2_all_nthI) (use cvi d(12) lba in auto)
        show "wt (c \<degree>\<degree> map (ap \<rho>' \<sigma>') uas')" using list_app_typeI[OF tyc tap] by (auto simp: wt_def)
        show "wt (c \<degree>\<degree> bs)" using tys sC(1) by (auto simp: wt_def)
      qed
      show ?thesis unfolding apc sC(1)
      proof (rule mcp_conv_types_abs[OF _ _ c1])
        show "wt (types_abs Ss (c \<degree>\<degree> map (ap \<rho>' \<sigma>') uas'))"
          using mf_typing_types_abs[OF list_app_typeI[OF tyc tap] cS] by (auto simp: wt_def)
        show "wt (types_abs Ss (c \<degree>\<degree> bs))" using mf_typing_types_abs[OF tys[unfolded sC(1)] cS] by (auto simp: wt_def)
      qed
    qed
    show "(\<Sum>y\<in>NV. mcp_vsz \<rho>' \<sigma>' y) + 1 \<le> lsz (pushes mcp_e0 Ss) s - 2 * arity UU"
    proof -
      have "(\<Sum>y\<in>NV. mcp_vsz \<rho>' \<sigma>' y) \<le> sum_list (map (lsz (pushes mcp_e0 Ss)) bs)"
        using d2(7) mcp_sum_zip_le[of "lsz (pushes mcp_e0 Ss)" "\<lambda>B. 2 * arity B" bs Bs] by linarith
      moreover have "rigid c" using sC(2) by auto
      then have "lsz (pushes mcp_e0 Ss) s = tsz (spine_type (pushes mcp_e0 Ss) s) + sum_list (map (lsz (pushes mcp_e0 Ss)) bs)"
        unfolding sC(1) by (rule lsz_rigid_apps)
      moreover have "0 < tsz (spine_type (pushes mcp_e0 Ss) s)" by (rule tsz_pos)
      ultimately show ?thesis using ar0 by simp
    qed
  qed (use d2(3-6,8) in simp_all)
  with mc ev1 show ?thesis by blast
qed


subsection \<open>Completeness of copying\<close>

text \<open>
  Completeness of \<^const>\<open>mc\<close>: for every target \<open>s\<close> of a term \<open>u\<close> (the body of the value of the
  variable, applied to the arguments \<open>targs\<close>, is equivalent to \<open>u\<close>), the sequence of \<^const>\<open>mc\<close>
  contains a copy of \<open>u\<close> with a solution that maps it to the target. The values of the new
  variables of the copy are smaller than the target, strictly so if the head of \<open>u\<close> is rigid
  (@{term "m = 1"}). The proof is by induction on the size of the target.
\<close>

theorem mcp_mc_complete:
  assumes cfg: "cfg_alg cfg = alg"
  shows "mcp_pre A K X env dps rb targs u \<Longrightarrow> mcp_spre \<rho> \<sigma> env dps X A e rb targs Ss u UU s \<Longrightarrow>
    mcp_kokK (nat_of_integer (cfg_arity_bound cfg)) \<rho> (tyenv env) A K \<Longrightarrow>
    \<exists>sq. okW (mc cfg vname rb targs u env dps) sq \<and>
      (\<exists>x. ev cfg sq x \<and> (\<exists>m. (rigid (fst (strip_comb u)) \<longrightarrow> m = 1) \<and>
        mcp_cres A K X env rb targs u \<rho> \<sigma> Ss UU s m x))"
proof (induction "lsz (pushes mcp_e0 Ss) s" arbitrary: A K X env dps rb targs u \<rho> \<sigma> e Ss UU s rule: less_induct)
  case less
  note pre = less.prems(1) and sp = less.prems(2) and kk = less.prems(3)
  have IH: "\<exists>sq. okW (mc cfg vname rb' targs' u' env' dps') sq \<and>
      (\<exists>x. ev cfg sq x \<and> (\<exists>m. mcp_cres A' K' X' env' rb' targs' u' \<rho>' \<sigma>' Ss' UU' s' m x))"
    if "lsz (pushes mcp_e0 Ss') s' < lsz (pushes mcp_e0 Ss) s" "mcp_pre A' K' X' env' dps' rb' targs' u'"
      "mcp_spre \<rho>' \<sigma>' env' dps' X' A' e' rb' targs' Ss' u' UU' s'"
      "mcp_kokK (nat_of_integer (cfg_arity_bound cfg)) \<rho>' (tyenv env') A' K'"
    for A' K' X' env' dps' rb' targs' u' \<rho>' \<sigma>' e' Ss' UU' s'
    using less.hyps[OF that] by blast
  let ?uh = "fst (strip_comb u)"
  from sp have tys: "pushes mcp_e0 Ss \<turnstile> s : UU" and nrs: "no_redex s" and lbs: "\<not> loose_bvar s (ilength Ss)"
    and ar: "arity UU = nabs u"
    unfolding mcp_spre_def by blast+
  have u: "u = ?uh \<degree>\<degree> snd (strip_comb u)" by (rule strip_comb_apps) simp
  show ?case
  proof (cases "is_Abs ?uh")
    case True
    then obtain a T body where hd: "?uh = Abs a T body" by (cases ?uh) auto
    have "\<exists>sq. okW (mc cfg vname rb targs u env dps) sq \<and>
        (\<exists>x. ev cfg sq x \<and> mcp_cres A K X env rb targs u \<rho> \<sigma> Ss UU s 0 x)"
    proof (rule mcp_mc_abs[OF pre sp hd])
      fix e' Ss' UU' s'
      assume "lsz (pushes mcp_e0 Ss') s' < lsz (pushes mcp_e0 Ss) s"
        "mcp_pre A K X env dps ((a, T) # rb) (map (incr_boundvars 1) targs @ [Bound 0]) body"
        "mcp_spre \<rho> \<sigma> env dps X A e' ((a, T) # rb) (map (incr_boundvars 1) targs @ [Bound 0]) Ss' body UU' s'"
      from IH[OF this kk] show "\<exists>sq. okW (mc cfg vname ((a, T) # rb) (map (incr_boundvars 1) targs @ [Bound 0]) body env dps) sq \<and>
          (\<exists>x. ev cfg sq x \<and> mcp_cres A K X env ((a, T) # rb) (map (incr_boundvars 1) targs @ [Bound 0]) body
            \<rho> \<sigma> Ss' UU' s' 0 x)" by (blast intro: mcp_cres_m0)
    qed
    then show ?thesis using hd by auto
  next
    case nA: False
    show ?thesis
    proof (cases "is_Var ?uh")
      case True
      then obtain w W where hd: "?uh = Var w W" by (cases ?uh) auto
      from mcp_mc_var[OF pre sp hd, of cfg vname] obtain sq x where
        "okW (mc cfg vname rb targs u env dps) sq" "ev cfg sq x" "mcp_cres A K X env rb targs u \<rho> \<sigma> Ss UU s 0 x" by blast
      moreover have "\<not> rigid ?uh" using hd by simp
      ultimately show ?thesis by blast
    next
      case nV: False
      have r: "rigid ?uh" using nA nV head_of_not_App[of u] by (cases ?uh) (auto simp: head_of_strip_comb)
      have ar0: "arity UU = 0" using ar nA u is_Abs_apps by (metis nabs_nonAbs)
      note shp = mcp_target_shape[OF tys nrs ar0]
      define h' where "h' = fst (strip_comb s)"
      define bs where "bs = snd (strip_comb s)"
      have s: "s = h' \<degree>\<degree> bs" and at: "atom h'" using shp by (simp_all add: h'_def bs_def)
      show ?thesis
      proof (cases h')
        case (Bound j)
        have tyB: "\<exists>B. pushes mcp_e0 Ss \<turnstile> Bound j : B" using tys[unfolded s Bound] by (blast elim: list_app_typeE)
        then have j0: "0 \<le> j" by auto
        have jS: "j < ilength Ss"
        proof (rule ccontr)
          assume "\<not> j < ilength Ss"
          then have "loose_bvar (Bound j) (ilength Ss)" by simp
          then show False using lbs s Bound by (simp add: loose_bvar_apps)
        qed
        from mcp_mc_proj[OF cfg pre sp kk r s[unfolded Bound] j0 jS] show ?thesis by blast
      next
        case (Var x T)
        have "Var x T = inst \<rho> ?uh" by (rule mcp_target_rigid(1)[OF pre sp r s at, unfolded Var]) (simp add: closed_def)
        with r show ?thesis by (cases ?uh) auto
      next
        case (Const n T)
        have "\<exists>sq. okW (mc cfg vname rb targs u env dps) sq \<and> (\<exists>x. ev cfg sq x \<and> mcp_cres A K X env rb targs u \<rho> \<sigma> Ss UU s 1 x)"
        proof (rule mcp_mc_imit[OF cfg pre sp kk r s])
          show "(\<exists>n S. h' = Const n S) \<or> (\<exists>n S. h' = Free n S)" using Const by blast
          fix i A' K' X' env' dps' u' \<rho>' \<sigma>' UU'
          assume a: "i < length bs" "mcp_pre A' K' X' env' dps' rb targs u'"
            "mcp_spre \<rho>' \<sigma>' env' dps' X' A' e rb targs Ss u' UU' (bs ! i)"
            "mcp_kokK (nat_of_integer (cfg_arity_bound cfg)) \<rho>' (tyenv env') A' K'"
          have "lsz (pushes mcp_e0 Ss) (bs ! i) < lsz (pushes mcp_e0 Ss) s"
          proof -
            have "lsz (pushes mcp_e0 Ss) (bs ! i) \<le> sum_list (map (lsz (pushes mcp_e0 Ss)) bs)"
              using a(1) by (simp add: member_le_sum_list)
            moreover have "lsz (pushes mcp_e0 Ss) s = tsz (spine_type (pushes mcp_e0 Ss) s) + sum_list (map (lsz (pushes mcp_e0 Ss)) bs)"
              unfolding s Const by (rule lsz_rigid_apps) simp
            ultimately show ?thesis using tsz_pos[of "spine_type (pushes mcp_e0 Ss) s"] by linarith
          qed
          from IH[OF this a(2-4)] show "\<exists>sq. okW (mc cfg vname rb targs u' env' dps') sq \<and>
              (\<exists>x. ev cfg sq x \<and> (\<exists>m. mcp_cres A' K' X' env' rb targs u' \<rho>' \<sigma>' Ss UU' (bs ! i) m x))" .
        qed
        then show ?thesis by blast
      next
        case (Free n T)
        have "\<exists>sq. okW (mc cfg vname rb targs u env dps) sq \<and> (\<exists>x. ev cfg sq x \<and> mcp_cres A K X env rb targs u \<rho> \<sigma> Ss UU s 1 x)"
        proof (rule mcp_mc_imit[OF cfg pre sp kk r s])
          show "(\<exists>n S. h' = Const n S) \<or> (\<exists>n S. h' = Free n S)" using Free by blast
          fix i A' K' X' env' dps' u' \<rho>' \<sigma>' UU'
          assume a: "i < length bs" "mcp_pre A' K' X' env' dps' rb targs u'"
            "mcp_spre \<rho>' \<sigma>' env' dps' X' A' e rb targs Ss u' UU' (bs ! i)"
            "mcp_kokK (nat_of_integer (cfg_arity_bound cfg)) \<rho>' (tyenv env') A' K'"
          have "lsz (pushes mcp_e0 Ss) (bs ! i) < lsz (pushes mcp_e0 Ss) s"
          proof -
            have "lsz (pushes mcp_e0 Ss) (bs ! i) \<le> sum_list (map (lsz (pushes mcp_e0 Ss)) bs)"
              using a(1) by (simp add: member_le_sum_list)
            moreover have "lsz (pushes mcp_e0 Ss) s = tsz (spine_type (pushes mcp_e0 Ss) s) + sum_list (map (lsz (pushes mcp_e0 Ss)) bs)"
              unfolding s Free by (rule lsz_rigid_apps) simp
            ultimately show ?thesis using tsz_pos[of "spine_type (pushes mcp_e0 Ss) s"] by linarith
          qed
          from IH[OF this a(2-4)] show "\<exists>sq. okW (mc cfg vname rb targs u' env' dps') sq \<and>
              (\<exists>x. ev cfg sq x \<and> (\<exists>m. mcp_cres A' K' X' env' rb targs u' \<rho>' \<sigma>' Ss UU' (bs ! i) m x))" .
        qed
        then show ?thesis by blast
      qed (use at in auto)
    qed
  qed
qed


subsection \<open>Completeness of a single step of matching\<close>

text \<open>
  The sequence of \<^const>\<open>match1\<close> (for an occurring variable) contains the elements with new
  variables for the arguments of a projection or an imitation, and the pairs are kept:
\<close>

definition mcp_m1el :: "cfg \<Rightarrow> name \<Rightarrow> env \<Rightarrow> ptyp list \<Rightarrow> ptyp list \<Rightarrow> dpair list \<Rightarrow> pterm \<Rightarrow> seq \<Rightarrow> bool" where
  "mcp_m1el cfg vname env' Ts Us dps bvar s \<longleftrightarrow>
    (\<forall>env'' args. make_args vname Ts env' Us = (env'', args) \<longrightarrow> ev cfg s (El_C (list_comb bvar args) env'' dps))"

lemma mcp_m1el_mono: "mcp_m1el cfg vname env' Ts Us dps bvar s \<Longrightarrow> (\<And>x. ev cfg s x \<Longrightarrow> ev cfg s' x) \<Longrightarrow>
    mcp_m1el cfg vname env' Ts Us dps bvar s'"
  unfolding mcp_m1el_def by blast

lemma mcp_match1_proj:
  assumes cfg: "cfg_alg cfg = alg" and finK: "finite K" and si: "sinv A K X env dps"
    and tv: "tvars base \<subseteq> tvars_env (tyenv env) \<union> A" "tvars bary \<subseteq> tvars_env (tyenv env) \<union> A"
    and c: "cert_typ alg ar (tnorm (tyenv env) base)" "cert_typ alg ar (tnorm (tyenv env) bary)"
  shows "\<exists>s. okW (match1_proj cfg vname env dps base Ts bvar (Us, bary) p tail) s \<and>
    (\<forall>x. ev cfg tail x \<longrightarrow> ev cfg s x) \<and>
    (\<forall>env0 Cs env'. gentvars p env = (env0, Cs) \<longrightarrow> okW (proj_unify cfg base bary Cs env0) env' \<longrightarrow>
      mcp_m1el cfg vname env' Ts (Us @ Cs) dps bvar s)"
proof -
  obtain env0 Cs where g: "gentvars p env = (env0, Cs)" by (cases "gentvars p env")
  note gs = gentvars_simps[OF g]
  have si0: "sinv (A \<union> ntv Cs) (K \<union> ntv Cs) X env0 dps" by (rule sinv_gentvars[OF si g])
  have ei0: "einv (A \<union> ntv Cs) (K \<union> ntv Cs) env0" using si0 by (simp add: sinv_def)
  have cC: "\<forall>C\<in>set Cs. cert_typ alg ar (tnorm (tyenv env0) C)"
    using gs(6) cert_tnorm[OF ei0] by (fastforce simp: cert_typ_def sort_ok_def)
  have pu: "cuok (proj_unify cfg base bary Cs env0) (\<lambda>_. True)"
    by (rule cuok_mono[OF proj_unify_sinv[OF cfg finite_UnI[OF finK finite_ntv] si0]])
      (use tv c cC gs(2) in \<open>auto simp: ntv_def\<close>)
  then consider (cu) evs where "proj_unify cfg base bary Cs env0 = Some (evs, UErr CANTUNIFY)"
    | (ok) env' where "okW (proj_unify cfg base bary Cs env0) env'"
    unfolding cuok_def by blast
  then show ?thesis
  proof cases
    case cu
    have "okW (match1_proj cfg vname env dps base Ts bvar (Us, bary) p tail) tail"
      using cu by (simp add: match1_proj_def g bindW_def handleW_def returnW_def)
    moreover have "\<not> okW (proj_unify cfg base bary Cs env0) env'" for env' using cu by simp
    ultimately show ?thesis using g by (intro exI[of _ tail]) auto
  next
    case ok
    obtain env'' args where ma: "make_args vname Ts env' (Us @ Cs) = (env'', args)" by fastforce
    let ?s = "S_Append (S_Single (El_C (list_comb bvar args) env'' dps)) tail"
    have "okW (match1_proj cfg vname env dps base Ts bvar (Us, bary) p tail) ?s"
      using ok ma by (auto simp: match1_proj_def g okW_handleW)
    moreover have "ev cfg tail x \<Longrightarrow> ev cfg ?s x" for x by (rule ev.append_r)
    moreover have "mcp_m1el cfg vname env1 Ts (Us @ Cs) dps bvar ?s"
      if "okW (proj_unify cfg base bary Cs env0) env1" for env1
      using okW_det[OF ok that] ma by (auto simp: mcp_m1el_def intro: ev.append_l ev.single)
    ultimately show ?thesis using g by (intro exI[of _ ?s]) auto
  qed
qed

lemma mcp_foldr_match1_proj:
  assumes cfg: "cfg_alg cfg = alg" and finK: "finite K" and si: "sinv A K X env dps"
    and tv: "tvars base \<subseteq> tvars_env (tyenv env) \<union> A" "tvars bary \<subseteq> tvars_env (tyenv env) \<union> A"
    and c: "cert_typ alg ar (tnorm (tyenv env) base)" "cert_typ alg ar (tnorm (tyenv env) bary)"
  shows "\<exists>s. okW (foldrW (match1_proj cfg vname env dps base Ts bvar (Us, bary)) ps tail) s \<and>
    (\<forall>x. ev cfg tail x \<longrightarrow> ev cfg s x) \<and>
    (\<forall>p\<in>set ps. \<forall>env0 Cs env'. gentvars p env = (env0, Cs) \<longrightarrow> okW (proj_unify cfg base bary Cs env0) env' \<longrightarrow>
      mcp_m1el cfg vname env' Ts (Us @ Cs) dps bvar s)"
proof (induction ps)
  case Nil
  show ?case by (intro exI[of _ tail]) (simp add: returnW_def)
next
  case (Cons p ps)
  from Cons.IH obtain s0 where s0: "okW (foldrW (match1_proj cfg vname env dps base Ts bvar (Us, bary)) ps tail) s0"
    "\<forall>x. ev cfg tail x \<longrightarrow> ev cfg s0 x"
    "\<forall>p\<in>set ps. \<forall>env0 Cs env'. gentvars p env = (env0, Cs) \<longrightarrow> okW (proj_unify cfg base bary Cs env0) env' \<longrightarrow>
      mcp_m1el cfg vname env' Ts (Us @ Cs) dps bvar s0" by blast
  from mcp_match1_proj[OF cfg finK si tv c, of vname Ts bvar Us p s0] obtain s where
    s: "okW (match1_proj cfg vname env dps base Ts bvar (Us, bary) p s0) s"
    "\<forall>x. ev cfg s0 x \<longrightarrow> ev cfg s x"
    "\<forall>env0 Cs env'. gentvars p env = (env0, Cs) \<longrightarrow> okW (proj_unify cfg base bary Cs env0) env' \<longrightarrow>
      mcp_m1el cfg vname env' Ts (Us @ Cs) dps bvar s" by blast
  show ?case
  proof (rule exI[of _ s], intro conjI)
    show "okW (foldrW (match1_proj cfg vname env dps base Ts bvar (Us, bary)) (p # ps) tail) s"
      using s0(1) s(1) by auto
    show "\<forall>x. ev cfg tail x \<longrightarrow> ev cfg s x" using s0(2) s(2) by blast
    show "\<forall>q\<in>set (p # ps). \<forall>env0 Cs env'. gentvars q env = (env0, Cs) \<longrightarrow> okW (proj_unify cfg base bary Cs env0) env' \<longrightarrow>
      mcp_m1el cfg vname env' Ts (Us @ Cs) dps bvar s"
      using s0(3) s(2,3) mcp_m1el_mono by (metis set_ConsD)
  qed
qed

lemma mcp_match1_projs:
  assumes cfg: "cfg_alg cfg = alg" and finK: "finite K" and si: "sinv A K X env dps"
    and tvb: "tvars base \<subseteq> tvars_env (tyenv env) \<union> A" and cb: "cert_typ alg ar (tnorm (tyenv env) base)"
    and tvT: "\<forall>(bvar, T, targ)\<in>set projs. tvars T \<subseteq> tvars_env (tyenv env) \<union> A \<and> cert_typ alg ar (tnorm (tyenv env) T)"
  shows "\<exists>sq. okW (match1_projs cfg vname env dps base Ts projs tail) sq \<and> (\<forall>x. ev cfg tail x \<longrightarrow> ev cfg sq x) \<and>
    (\<forall>(bvar, T, targ)\<in>set projs. \<forall>Us bary. ok (strip_type env T) (Us, bary) \<longrightarrow>
      (\<forall>p\<in>set (arity_guesses cfg bary). \<forall>env0 Cs env'. gentvars p env = (env0, Cs) \<longrightarrow>
        okW (proj_unify cfg base bary Cs env0) env' \<longrightarrow> mcp_m1el cfg vname env' Ts (Us @ Cs) dps bvar sq))"
  using tvT
proof (induction projs)
  case Nil
  show ?case by (intro exI conjI) (auto simp: returnW_def)
next
  case (Cons q projs)
  obtain bvar T targ where q: "q = (bvar, T, targ)" by (cases q)
  have ei: "einv A K env" using si by (simp add: sinv_def)
  from Cons.prems q have tT: "tvars T \<subseteq> tvars_env (tyenv env) \<union> A" and cT: "cert_typ alg ar (tnorm (tyenv env) T)"
    by auto
  from Cons.IH Cons.prems obtain s0 where s0: "okW (match1_projs cfg vname env dps base Ts projs tail) s0"
    "\<forall>x. ev cfg tail x \<longrightarrow> ev cfg s0 x"
    "\<forall>(bvar, T, targ)\<in>set projs. \<forall>Us bary. ok (strip_type env T) (Us, bary) \<longrightarrow>
      (\<forall>p\<in>set (arity_guesses cfg bary). \<forall>env0 Cs env'. gentvars p env = (env0, Cs) \<longrightarrow>
        okW (proj_unify cfg base bary Cs env0) env' \<longrightarrow> mcp_m1el cfg vname env' Ts (Us @ Cs) dps bvar s0)" by auto
  from binder_types_term[OF einvD(2)[OF ei] refl tT] obtain Us where bU: "binder_types env T = return Us" by blast
  from body_type_term[OF einvD(2)[OF ei] refl tT] obtain bary where
    bB: "body_type env T = return bary" "tvars bary \<subseteq> tvars_env (tyenv env) \<union> A" by blast
  have sT: "strip_type env T = return (Us, bary)" using bU bB by (simp add: strip_type_def)
  have cbary: "cert_typ alg ar (tnorm (tyenv env) bary)"
  proof -
    have "tsubst (rho0 env) T = map (tsubst (rho0 env)) Us \<Rrightarrow> tsubst (rho0 env) bary"
      by (rule strip_type_sound[OF sT[unfolded return_def] einv_rho0(1)[OF ei]])
    with cT show ?thesis by (simp add: cert_typ_funs)
  qed
  from mcp_foldr_match1_proj[OF cfg finK si tvb bB(2) cb cbary, of vname Ts bvar Us "arity_guesses cfg bary" s0]
  obtain s where s: "okW (foldrW (match1_proj cfg vname env dps base Ts bvar (Us, bary)) (arity_guesses cfg bary) s0) s"
    "\<forall>x. ev cfg s0 x \<longrightarrow> ev cfg s x"
    "\<forall>p\<in>set (arity_guesses cfg bary). \<forall>env0 Cs env'. gentvars p env = (env0, Cs) \<longrightarrow>
      okW (proj_unify cfg base bary Cs env0) env' \<longrightarrow> mcp_m1el cfg vname env' Ts (Us @ Cs) dps bvar s"
    by blast
  show ?case
  proof (rule exI[of _ s], intro conjI)
    show "okW (match1_projs cfg vname env dps base Ts (q # projs) tail) s"
      using s0(1) s(1) sT by (auto simp: q return_def)
    show "\<forall>x. ev cfg tail x \<longrightarrow> ev cfg s x" using s0(2) s(2) by blast
    show "\<forall>(bvar, T, targ)\<in>set (q # projs). \<forall>Us bary. ok (strip_type env T) (Us, bary) \<longrightarrow>
      (\<forall>p\<in>set (arity_guesses cfg bary). \<forall>env0 Cs env'. gentvars p env = (env0, Cs) \<longrightarrow>
        okW (proj_unify cfg base bary Cs env0) env' \<longrightarrow> mcp_m1el cfg vname env' Ts (Us @ Cs) dps bvar s)"
    proof (intro ballI)
      fix q' assume "q' \<in> set (q # projs)"
      then consider "q' = q" | "q' \<in> set projs" by auto
      note c = this
      obtain bvar' T' targ' where q': "q' = (bvar', T', targ')" by (cases q')
      show "case q' of (bvar, T, targ) \<Rightarrow> \<forall>Us bary. ok (strip_type env T) (Us, bary) \<longrightarrow>
        (\<forall>p\<in>set (arity_guesses cfg bary). \<forall>env0 Cs env'. gentvars p env = (env0, Cs) \<longrightarrow>
          okW (proj_unify cfg base bary Cs env0) env' \<longrightarrow> mcp_m1el cfg vname env' Ts (Us @ Cs) dps bvar s)"
        unfolding q' prod.case
      proof (intro allI impI ballI)
        fix Us' bary' p env0 Cs env'
        assume st: "ok (strip_type env T') (Us', bary')" and p: "p \<in> set (arity_guesses cfg bary')"
          and g: "gentvars p env = (env0, Cs)" and pu: "okW (proj_unify cfg base bary' Cs env0) env'"
        from c show "mcp_m1el cfg vname env' Ts (Us' @ Cs) dps bvar' s"
        proof cases
          case 1
          with q q' have e: "bvar' = bvar" "T' = T" "targ' = targ" by auto
          with st sT have "Us' = Us" "bary' = bary" by (simp_all add: return_def)
          with s(3) p g pu e show ?thesis by blast
        next
          case 2
          with s0(3) q' st p g pu have "mcp_m1el cfg vname env' Ts (Us' @ Cs) dps bvar' s0" by fastforce
          then show ?thesis by (rule mcp_m1el_mono) (use s(2) in blast)
        qed
      qed
    qed
  qed
qed

text \<open>
  Completeness of \<^const>\<open>match1\<close>: for every target \<open>s\<close> of a term \<open>u\<close> with a rigid head, the sequence
  of \<^const>\<open>match1\<close> contains a projection or an imitation with new variables for the arguments,
  whose values are smaller than the target.
\<close>

lemma mcp_match1_complete:
  assumes cfg: "cfg_alg cfg = alg"
    and pre: "mcp_pre A K X env dps rb targs u" and sp: "mcp_spre \<rho> \<sigma> env dps X A e rb targs Ss u UU s"
    and kk: "mcp_kokK (nat_of_integer (cfg_arity_bound cfg)) \<rho> (tyenv env) A K"
    and r: "rigid (fst (strip_comb u))"
  shows "\<exists>sq. okW (match1 cfg vname rb targs u env dps) sq \<and>
    (\<exists>x. ev cfg sq x \<and> mcp_cres A K X env rb targs u \<rho> \<sigma> Ss UU s 1 x)"
proof -
  let ?\<theta> = "tyenv env" and ?KN = "tvars_env (tyenv env) \<union> A" and ?uh = "fst (strip_comb u)"
  have si: "sinv A K X env dps" and finK: "finite K" and tok: "mcp_tok env rb targs u"
    and tv: "ttvars u \<union> (\<Union>t\<in>set targs. ttvars t) \<union> btvars rb \<subseteq> ?KN"
    using pre by (simp_all add: mcp_pre_def)
  from sp have inv: "scinv \<rho> \<sigma> env dps X A" and bs: "bs_env \<rho> e rb"
    and tyt: "e \<tturnstile> map (inst \<rho>) targs : Ss" and tyu: "e \<turnstile> inst \<rho> u : UU" and ar: "arity UU = nabs u"
    and tys: "pushes mcp_e0 Ss \<turnstile> s : UU" and nrs: "no_redex s" and lbs: "\<not> loose_bvar s (ilength Ss)"
    unfolding mcp_spre_def by blast+
  have ei: "einv A K env" using si by (simp add: sinv_def)
  note x = einvD[OF ei] and r0 = einv_rho0[OF ei] and sd = solutionD[OF scinvD(1)[OF inv]]
  have kok0: "mcp_kok (nat_of_integer (cfg_arity_bound cfg)) \<rho> ?\<theta> ?KN" by (rule mcp_kokK_kok[OF kk ei])
  from mcp_mc_types[OF pre] obtain T0 base Ts where
    ty0: "fastype env rb ?uh = return T0" "body_type env T0 = return base"
      "mapM (fastype env rb) targs = return Ts" "tvars T0 \<subseteq> ?KN" "tvars base \<subseteq> ?KN" "\<forall>T\<in>set Ts. tvars T \<subseteq> ?KN"
    by blast
  have na: "\<not> is_Abs ?uh" using r by (cases ?uh) auto
  have ty0': "ok (fastype env rb ?uh) T0" "ok (body_type env T0) base" "ok (mapM (fastype env rb) targs) Ts"
    using ty0 by (simp_all add: return_def)
  note ts = mcp_types_sound[OF pre ty0' na]
  note ts\<rho> = ts[OF sd(2) bs tyt tyu]
  have lT: "length Ts = length targs" using ty0'(3) by (simp add: ok_mapM list_all2_lengthD)
  from make_projs_term[OF lT, of u targs] obtain projs where mp: "okW (make_projs u targs Ts targs) projs" by blast
  from tok r0 obtain e0 Us0 U0 where t0: "bs_env (rho0 env) e0 rb" "e0 \<tturnstile> map (inst (rho0 env)) targs : Us0"
    "e0 \<turnstile> inst (rho0 env) u : U0" unfolding mcp_tok_def by blast
  note tr0 = ts[OF r0(1) t0]
  have cTs0: "\<forall>T\<in>set Ts. cert_typ alg ar (tnorm ?\<theta> T)" using tr0(1,3) by simp
  have cb0: "cert_typ alg ar (tnorm ?\<theta> base)" using tr0(2,4) by simp
  have tvT: "\<forall>(bvar, T, targ)\<in>set (rev projs). tvars T \<subseteq> ?KN \<and> cert_typ alg ar (tnorm ?\<theta> T)"
    using mf_make_projs_props[OF mp] ty0(6) cTs0 lT by (fastforce dest: nth_mem)
  \<comment> \<open>The sequence of \<^const>\<open>match1\<close>:\<close>
  from binder_types_term[OF x(2) refl ty0(4)] obtain Vs where bV: "binder_types env T0 = return Vs" by blast
  obtain envI argsI where maI: "make_args vname Ts env Vs = (envI, argsI)" by fastforce
  define imit where "imit = (case ?uh of
      Const _ _ \<Rightarrow> S_Single (El_C (list_comb ?uh argsI) envI dps)
    | Free _ _ \<Rightarrow> S_Single (El_C (list_comb ?uh argsI) envI dps)
    | _ \<Rightarrow> S_Empty)"
  from mcp_match1_projs[OF cfg finK si ty0(5) cb0 tvT, of vname Ts imit]
  obtain sq where mf: "okW (match1_projs cfg vname env dps base Ts (rev projs) imit) sq"
    and im: "\<forall>x. ev cfg imit x \<longrightarrow> ev cfg sq x"
    and pj: "\<forall>(bvar, T, targ)\<in>set (rev projs). \<forall>Us bary. ok (strip_type env T) (Us, bary) \<longrightarrow>
      (\<forall>p\<in>set (arity_guesses cfg bary). \<forall>env0 Cs env'. gentvars p env = (env0, Cs) \<longrightarrow>
        okW (proj_unify cfg base bary Cs env0) env' \<longrightarrow> mcp_m1el cfg vname env' Ts (Us @ Cs) dps bvar sq)"
    by blast
  have m1: "okW (match1 cfg vname rb targs u env dps) sq"
    using mf mp ty0(1,2) bV maI unfolding match1_def
    by (cases ?uh) (auto simp: Let_def ty0(3) return_def imit_def)
  \<comment> \<open>The shape of the target:\<close>
  have u: "u = ?uh \<degree>\<degree> snd (strip_comb u)" by (rule strip_comb_apps) simp
  have ar0: "arity UU = 0" using ar na u is_Abs_apps by (metis nabs_nonAbs)
  note shp = mcp_target_shape[OF tys nrs ar0]
  define h' where "h' = fst (strip_comb s)"
  define bs where "bs = snd (strip_comb s)"
  have s: "s = h' \<degree>\<degree> bs" and at: "atom h'" using shp by (simp_all add: h'_def bs_def)
  \<comment> \<open>Imitation:\<close>
  have imc: ?thesis if hc: "(\<exists>n S. h' = Const n S) \<or> (\<exists>n S. h' = Free n S)"
  proof -
    have cc: "closed h'" "atom h'" using hc by (auto simp: closed_def)
    note tr = mcp_target_rigid[OF pre sp r s cc(2,1)]
    have uhc: "(\<exists>n S. ?uh = Const n S) \<or> (\<exists>n S. ?uh = Free n S)" using tr(1) hc r by (cases ?uh) auto
    have "ev cfg imit (El_C (list_comb ?uh argsI) envI dps)" using uhc by (auto simp: imit_def intro: ev.single)
    with im have evI: "ev cfg sq (El_C (list_comb ?uh argsI) envI dps)" by blast
    from tys[unfolded s] obtain Bs where tyc: "pushes mcp_e0 Ss \<turnstile> h' : Bs \<Rrightarrow> UU"
      and tybs: "pushes mcp_e0 Ss \<tturnstile> bs : Bs" by (rule list_app_typeE)
    have hu: "head_of u = ?uh" by (simp add: head_of_strip_comb)
    have luh: "\<not> loose_bvar ?uh (ilength rb)" "\<not> loose_bvar ?uh (ilength Ss)" using uhc by auto
    have stT0: "ok (strip_type env T0) (Vs, base)" using bV ty0(2) by (simp add: strip_type_def return_def)
    from head_typing[OF tyu] hu obtain V where tyh: "e \<turnstile> inst \<rho> ?uh : V" by auto
    have "tsubst \<rho> T0 = V" by (rule fastype_sound[OF ty0'(1) sd(2) bs tyh])
    moreover have "V = Bs \<Rrightarrow> UU" using tyh tyc tr(1) mcp_closed_typed_atom[OF tyc hc, of e] typing_unique by metis
    moreover have "tsubst \<rho> T0 = map (tsubst \<rho>) Vs \<Rrightarrow> tsubst \<rho> base" by (rule strip_type_sound[OF stT0 sd(2)])
    ultimately have VB0: "map (tsubst \<rho>) Vs \<Rrightarrow> UU = Bs \<Rrightarrow> UU" using ts\<rho>(2) by simp
    have VB: "map (tsubst \<rho>) Vs = Bs"
    proof -
      from mcp_funs_split[OF VB0 ar0] have "Bs = map (tsubst \<rho>) Vs @ drop (length Vs) Bs"
        "UU = drop (length Vs) Bs \<Rrightarrow> UU" by simp_all
      moreover from arg_cong[OF this(2), of arity] ar0 have "drop (length Vs) Bs = []" by (simp add: arity_funs)
      ultimately show ?thesis by simp
    qed
    have cB: "\<forall>B\<in>set Bs. cert_typ alg ar B"
      using bs_env_cert[OF bs tyh luh(1)] \<open>V = Bs \<Rrightarrow> UU\<close> by (simp add: cert_typ_funs)
    have "\<forall>U\<in>set Vs. tvars U \<subseteq> tvars T0 \<union> tvars_env ?\<theta>"
      using mf_binder_types_sound[of env T0 "Ok Vs" Vs] bV x(6) by (auto simp: return_def)
    then have tvVs: "\<forall>U\<in>set Vs. tvars U \<subseteq> ?KN" using ty0(4) by blast
    have tvh: "ttvars ?uh \<subseteq> ?KN" using tv ttvars_head[of u] by (simp add: head_of_strip_comb) blast
    have shI: "s = inst \<rho> ?uh \<degree>\<degree> bs" "pushes mcp_e0 Ss \<turnstile> inst \<rho> ?uh : Bs \<Rrightarrow> UU" using s tyc tr(1) by simp_all
    have hI: "rigid ?uh" "vars ?uh = {}" "ttvars ?uh \<subseteq> ?KN" "\<not> loose_bvar ?uh (ilength Ss)"
      using r uhc tvh luh(2) by auto
    have htyI: "(\<forall>e'. pushes e' Us1 \<turnstile> inst \<rho>0 ?uh : map (tsubst \<rho>0) Vs \<Rrightarrow> U1) \<and>
        (\<forall>U\<in>set Vs. cert_typ alg ar (tsubst \<rho>0 U))"
      if "tsol ?\<theta> \<rho>0" "cert_inst \<rho>0" "bs_env \<rho>0 e1 rb" "e1 \<tturnstile> map (inst \<rho>0) targs : Us1"
        "e1 \<turnstile> inst \<rho>0 u : U1" for \<rho>0 e1 Us1 U1
    proof -
      note tt = ts[OF that(1) that(3-5)]
      from head_typing[OF that(5)] hu obtain W where tW: "e1 \<turnstile> inst \<rho>0 ?uh : W" by auto
      have "tsubst \<rho>0 T0 = W" by (rule fastype_sound[OF ty0'(1) that(1,3) tW])
      moreover have "tsubst \<rho>0 T0 = map (tsubst \<rho>0) Vs \<Rrightarrow> tsubst \<rho>0 base" by (rule strip_type_sound[OF stT0 that(1)])
      ultimately have W: "W = map (tsubst \<rho>0) Vs \<Rrightarrow> U1" using tt(2) by simp
      have "(\<exists>n S. inst \<rho>0 ?uh = Const n S) \<or> (\<exists>n S. inst \<rho>0 ?uh = Free n S)" using uhc by auto
      from mcp_closed_typed_atom[OF tW this] W have "pushes e' Us1 \<turnstile> inst \<rho>0 ?uh : map (tsubst \<rho>0) Vs \<Rrightarrow> U1" for e'
        by simp
      moreover have "\<forall>U\<in>set Vs. cert_typ alg ar (tsubst \<rho>0 U)"
        using bs_env_cert[OF that(3) tW luh(1)] W by (simp add: cert_typ_funs)
      ultimately show ?thesis by blast
    qed
    have kkI: "\<forall>k. mcp_kokK k \<rho> ?\<theta> A K \<longrightarrow> mcp_kokK k \<rho> ?\<theta> A K" by simp
    obtain Gs \<sigma>3 where args: "argsI = map (\<lambda>G. G \<degree>\<degree> mbvs (length Ts)) Gs"
      and GU: "list_all2 (\<lambda>G U. \<exists>x. G = Var x (Ts \<Rrightarrow> U)) Gs Vs"
      and ma': "tenv envI = tenv env" "tyenv envI = tyenv env" "maxidx env \<le> maxidx envI"
      and Gi: "\<forall>G\<in>set Gs. \<exists>a U. G = Var (a, maxidx env + 1) U"
      and si'': "sinv A K (mlvars Gs \<union> X) envI dps"
      and vG: "vtvars (mlvars Gs) \<subseteq> tvars_env (tyenv env) \<union> A"
      and inv3d: "scinv \<rho> \<sigma>3 envI dps (mlvars Gs \<union> X) A" and sa3': "sagree (maxidx env) \<sigma> \<sigma>3"
      and lqb: "length Gs = length bs" and apGl: "\<And>l. l < length Gs \<Longrightarrow> ap \<rho> \<sigma>3 (Gs ! l) = types_abs Ss (bs ! l)"
      and post: "\<And>env2 dps2 \<rho>4 \<sigma>4. sinv A K (mlvars Gs \<union> X) env2 dps2 \<Longrightarrow>
        scinv \<rho>4 \<sigma>4 env2 dps2 (mlvars Gs \<union> X) A \<Longrightarrow>
        tagree (maxidx envI) \<rho> \<rho>4 \<Longrightarrow> sagree (maxidx envI) \<sigma>3 \<sigma>4 \<Longrightarrow> extends envI env2 \<Longrightarrow>
        tvars_env (tyenv envI) \<subseteq> tvars_env (tyenv env2) \<Longrightarrow> ubv env2 (mlvars Gs \<union> X) \<subseteq> ubv envI (mlvars Gs \<union> X) \<Longrightarrow>
        (\<forall>k. mcp_kokK k \<rho> (tyenv envI) A K \<longrightarrow> mcp_kokK k \<rho>4 (tyenv env2) A K) \<Longrightarrow>
        mcp_cres A K X env rb targs u \<rho> \<sigma> Ss UU s 1 (El_C (list_comb ?uh argsI) env2 dps2)"
      by (rule mcp_args_elem[OF pre sp ty0' na si inv finK subset_refl subset_refl extends_refl refl subset_refl
            tagree_refl kkI ts\<rho>(1)[symmetric] ty0(6) VB tvVs cB shI tybs hI _ maI], rule htyI, assumption+) blast
    have "mcp_cres A K X env rb targs u \<rho> \<sigma> Ss UU s 1 (El_C (list_comb ?uh argsI) envI dps)"
      by (rule post[OF si'' inv3d tagree_refl sagree_refl extends_refl subset_refl subset_refl]) simp
    with m1 evI show ?thesis by blast
  qed
  show ?thesis
  proof (cases h')
    case (Bound j)
    have tyB: "\<exists>B. pushes mcp_e0 Ss \<turnstile> Bound j : B" using tys[unfolded s Bound] by (blast elim: list_app_typeE)
    then have j0: "0 \<le> j" by auto
    have jS: "j < ilength Ss"
    proof (rule ccontr)
      assume "\<not> j < ilength Ss"
      then have "loose_bvar (Bound j) (ilength Ss)" by simp
      then show False using lbs s Bound by (simp add: loose_bvar_apps)
    qed
    note sB = s[unfolded Bound] j0 jS
    have lSs: "length Ss = length targs"
      using sp lT by (simp add: mcp_spre_def) (metis typings_nth length_map)
    define k where "k = length targs - 1 - nat_of_integer j"
    have jn: "nat_of_integer j < length targs" using sB(2,3) lSs nat_of_integer_less_ilength by fastforce
    have kn: "k < length targs" using jn by (simp add: k_def)
    have jk: "Bound (integer_of_nat (length targs - 1 - k)) = Bound j"
      using jn sB(2) by (simp add: k_def integer_eq_iff integer_of_nat.rep_eq nat_of_integer.rep_eq less_eq_integer.rep_eq)
    have tvTk: "tvars (Ts ! k) \<subseteq> ?KN" using ty0(6) kn lT by simp
    from binder_types_term[OF x(2) refl tvTk] obtain Us where bU: "binder_types env (Ts ! k) = return Us" by blast
    from body_type_term[OF x(2) refl tvTk] obtain bary where bB: "body_type env (Ts ! k) = return bary" by blast
    have st: "ok (strip_type env (Ts ! k)) (Us, bary)" using bU bB by (simp add: strip_type_def return_def)
    from mcp_proj_elem[OF cfg pre sp kok0 ty0' ty0(5,6) na sB k_def st, of vname]
    obtain p env0 Cs env' where pg: "p \<in> set (arity_guesses cfg bary)" and g: "gentvars p env = (env0, Cs)"
      and pu: "okW (proj_unify cfg base bary Cs env0) env'"
      and el: "\<forall>env'' args. make_args vname Ts env' (Us @ Cs) = (env'', args) \<longrightarrow>
        mcp_cres A K X env rb targs u \<rho> \<sigma> Ss UU s 1 (El_C (list_comb (Bound j) args) env'' dps)"
      by blast
    obtain env'' args where ma: "make_args vname Ts env' (Us @ Cs) = (env'', args)" by fastforce
    from el ma have cr: "mcp_cres A K X env rb targs u \<rho> \<sigma> Ss UU s 1 (El_C (list_comb (Bound j) args) env'' dps)"
      by blast
    have "(Bound (integer_of_nat (length targs - 1 - k)), Ts ! k, targs ! k) \<in> set (rev projs)"
      using mcp_make_projs_mem[OF mp kn] by simp
    with pj st pg g pu have "mcp_m1el cfg vname env' Ts (Us @ Cs) dps (Bound j) sq"
      unfolding jk by fastforce
    with ma have "ev cfg sq (El_C (list_comb (Bound j) args) env'' dps)" unfolding mcp_m1el_def by blast
    with m1 cr show ?thesis by blast
  next
    case (Var x T)
    have "Var x T = inst \<rho> ?uh" by (rule mcp_target_rigid(1)[OF pre sp r s at, unfolded Var]) (simp add: closed_def)
    with r show ?thesis by (cases ?uh) auto
  qed (use imc at in auto)
qed

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
    using SIMPL_term[OF fin si] ok unfolding cuok_def by auto
  then have ext: "extends env env'" by (simp add: simpl_post_def sstep_def)
  have sub: "X \<union> evars env \<subseteq> X \<union> evars env'" using mcp_evars_extends[OF ext] by blast
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
  define s0 where "s0 = ?w \<degree>\<degree> mbvs (length Ss)"
  have t0: "pushes mcp_e0 Ss \<turnstile> s0 : UU" unfolding s0_def by (rule list_app_typeI[OF tw mf_typings_bvs])
  define s where "s = bnorm s0"
  from bnorm_typed[OF t0] have b: "s0 \<rightarrow>\<^sub>\<beta>\<^sup>* s" "no_redex s" by (simp_all add: s_def)
  have ts: "pushes mcp_e0 Ss \<turnstile> s : UU" by (rule subject_reduction_beta'[OF b(1) t0])
  have "\<not> loose_bvar s0 (ilength Ss)"
    using mcp_loose_combound[of ?w "length Ss"] cw by (simp add: s0_def closed_def ilength_eq)
  then have ls: "\<not> loose_bvar s (ilength Ss)" by (rule mcp_loose_reds[OF b(1) mcp_ilength_nonneg])
  have ta0: "mcp_e0 \<turnstile> types_abs Ss s0 : Ss \<Rrightarrow> UU" by (rule mf_typing_types_abs[OF t0 cSs])
  have ta: "mcp_e0 \<turnstile> types_abs Ss s : Ss \<Rrightarrow> UU" by (rule mf_typing_types_abs[OF ts cSs])
  have c1: "types_abs Ss s0 \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ?w" unfolding s0_def
    by (rule mcp_conv_eta_types_abs[OF cw]) (use ta0 in \<open>auto simp: wt_def s0_def\<close>)
  have "s0 \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> s" by (rule conv_beta_eta[OF _ b(1)]) (use t0 in \<open>auto simp: wt_def\<close>)
  then have c2: "types_abs Ss s0 \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> types_abs Ss s"
    by (rule mcp_conv_types_abs[rotated 2]) (use ta0 ta in \<open>auto simp: wt_def\<close>)
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


text \<open>
  Completeness of \<^const>\<open>match_pair\<close> on a saturated flex-rigid pair whose variable does not occur
  (the copies of \<^const>\<open>mc\<close>), if the instance of its type is not a function type.
\<close>

lemma mcp_match_pair_mc:
  assumes cfg: "cfg_alg cfg = alg" and k: "k = nat_of_integer (cfg_arity_bound cfg)"
    and finX: "finite X" and finK: "finite K" and si: "sinv A K X env ((rb, t, u) # dps)"
    and fr: "fr_shape env (rb, t, u)" and inv: "scinv \<rho> \<sigma> env ((rb, t, u) # dps) X A"
    and kk: "mcp_kokK k \<rho> (tyenv env) A K"
    and st: "strip_comb t = (Var v T, targs)" and bt: "binder_types env T = return Ts"
    and len: "length Ts = length targs" and bT: "body_type env T = return B" and ar0: "arity (tsubst \<rho> B) = 0"
    and sat: "satd env rb u"
    and oc: "occurs_terms env v (u # targs @ concat (map (\<lambda>(_, t, u). [t, u]) dps)) = return False"
  shows "\<exists>s. okW (match_pair cfg env (rb, t, u) dps) s \<and> (\<exists>x. ev cfg s x \<and> mcp_mres A K X env \<rho> \<sigma> k x)"
proof -
  let ?\<theta> = "tyenv env" and ?KN = "tvars_env (tyenv env) \<union> A"
  have ei: "einv A K env" and wi: "winv env X" and p: "pok A env rb X t u"
    using si by (auto simp: sinv_def)
  have si0: "sinv A K X env dps" by (rule sinv_mono[OF si]) auto
  have inv0: "scinv \<rho> \<sigma> env dps X A" by (rule scinv_mono[OF inv]) auto
  note i = scinvD[OF inv] and sd = solutionD[OF scinvD(1)[OF inv]] and pd = pokD[OF p] and x = einvD[OF ei]
  have tt: "t = Var v T \<degree>\<degree> targs" by (rule strip_comb_apps[OF st])
  have hv: "head_of t = Var v T" using st by (simp add: head_of_strip_comb)
  have hb: "hunb env (rb, t, u)" and f0: "frs0 (rb, t, u)" using fr by (simp_all add: fr_shape_def)
  from hb hv have vn: "vt_lookup (tenv env) v = None" unfolding hunb_def by blast
  from f0 have nAu: "\<not> is_Abs u" and ru: "rigid (head_of u)" unfolding frs0_def by simp_all
  have ru': "rigid (fst (strip_comb u))" using ru by (simp add: head_of_strip_comb)
  have vT: "(v, T) \<in> X \<union> evars env" using pd(1) tt by (simp add: vars_apps)
  have vU: "v \<in> ubv env X" using vT vn unfolding ubv_def by force
  have mv: "snd v \<le> maxidx env" using i(3) vT unfolding vinv_def below_def by force
  have tvT: "tvars T \<subseteq> ?KN" using head_tvars_strip_comb[OF st] pd(3) by blast
  have below_KN: "tbelow (maxidx env) S" if "S \<subseteq> ?KN" for S using tvinv_tbelow[OF i(4) that] .
  from mf_binder_types_sound[OF bt[unfolded return_def] refl x(6)]
  have tvTs: "\<forall>U\<in>set Ts. tvars U \<subseteq> ?KN" using tvT x(9) by blast
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
  with funs_eq[OF lSs'] have Ss: "Ss = map (tsubst \<rho>) Ts" and TT: "TT = tsubst \<rho> B" by blast+
  have arTT: "arity TT = 0" using ar0 TT by simp
  have cSs: "\<forall>S\<in>set Ss. cert_typ alg ar S" using cT Tv by (simp add: cert_typ_funs)
  have \<rho>Ts: "map (tsubst \<rho>) Ts = Ss" using Ss by simp
  \<comment> \<open>The target\<close>
  obtain s where tys: "pushes mcp_e0 Ss \<turnstile> s : TT" and nrs: "no_redex s" and lbs: "\<not> loose_bvar s (ilength Ss)"
    and cvs: "types_abs Ss s \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> \<sigma> v (Ss \<Rrightarrow> TT)"
    by (rule mcp_value_target[OF sd(3), of Ss TT v]) (use cT Tv in simp)
  have vsz: "mcp_vsz \<rho> \<sigma> (v, T) = lsz (pushes mcp_e0 Ss) s"
    using mcp_vsz_val[OF sd(3) cT _ Tv tys nrs cSs] cvs arTT Tv by (simp add: conv_sym)
  have pre: "mcp_pre A K X env dps rb targs u"
    unfolding mcp_pre_def
  proof (intro conjI)
    show "vars u \<subseteq> X \<union> evars env" by (rule pd(2))
    show "mlvars targs \<subseteq> X \<union> evars env" using pd(1) tt by (auto simp: vars_apps)
    show "ttvars u \<union> (\<Union>t\<in>set targs. ttvars t) \<union> btvars rb \<subseteq> ?KN"
      using pd(3,4,5) tt by (auto simp: ttvars_apps)
    show "\<not> loose_bvar u (ilength rb)" by (rule pd(8))
    show "\<forall>t\<in>set targs. \<not> loose_bvar t (ilength rb)" using pd(7) tt by (simp add: loose_bvar_apps)
    show "mcp_tok env rb targs u"
      unfolding mcp_tok_def
    proof (intro allI impI)
      fix \<rho>0 assume "tsol ?\<theta> \<rho>0" "cert_inst \<rho>0"
      from pd(9)[OF this] obtain e0 T0 where "bs_env \<rho>0 e0 rb" "e0 \<turnstile> inst \<rho>0 t : T0" "e0 \<turnstile> inst \<rho>0 u : T0"
        by blast
      moreover from this(2)[unfolded tt inst_apps] obtain Us where "e0 \<tturnstile> map (inst \<rho>0) targs : Us"
        by (rule list_app_typeE)
      ultimately show "\<exists>e Us U. bs_env \<rho>0 e rb \<and> e \<tturnstile> map (inst \<rho>0) targs : Us \<and> e \<turnstile> inst \<rho>0 u : U" by blast
    qed
  qed (use finX finK si0 sat in simp_all)
  have spre: "mcp_spre \<rho> \<sigma> env dps X A e rb targs Ss u TT s"
    unfolding mcp_spre_def
  proof (intro conjI)
    show "arity TT = nabs u" using arTT nAu by simp
    have "ap \<rho> \<sigma> t = \<sigma> v (Ss \<Rrightarrow> TT) \<degree>\<degree> map (ap \<rho> \<sigma>) targs"
      unfolding tt ap_apps using Tv by (simp add: ap_def)
    moreover have "ap \<rho> \<sigma> t \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma> u" using i(7) by (auto simp: dsolved_def)
    moreover have "types_abs Ss s \<degree>\<degree> map (ap \<rho> \<sigma>) targs \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> \<sigma> v (Ss \<Rrightarrow> TT) \<degree>\<degree> map (ap \<rho> \<sigma>) targs"
    proof (rule conv_apps[OF _ _ _ cvs])
      show "list_all2 (\<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta>) (map (ap \<rho> \<sigma>) targs) (map (ap \<rho> \<sigma>) targs)"
        by (simp add: list_all2_refl)
      have ta: "e \<tturnstile> map (ap \<rho> \<sigma>) targs : Ss"
        using tyas by (induction targs arbitrary: Ss) (auto split: list.splits intro: typing_ap[OF _ sd(3)])
      have "e \<turnstile> types_abs Ss s : Ss \<Rrightarrow> TT" by (rule mcp_typing_val[OF tys lbs cSs])
      from list_app_typeI[OF this ta] show "wt (types_abs Ss s \<degree>\<degree> map (ap \<rho> \<sigma>) targs)" by (auto simp: wt_def)
      have "e \<turnstile> \<sigma> v (Ss \<Rrightarrow> TT) : Ss \<Rrightarrow> TT" by (rule wt_subst_typing[OF sd(3)]) (use cT Tv in simp)
      from list_app_typeI[OF this ta] show "wt (\<sigma> v (Ss \<Rrightarrow> TT) \<degree>\<degree> map (ap \<rho> \<sigma>) targs)" by (auto simp: wt_def)
    qed
    ultimately show "types_abs Ss s \<degree>\<degree> map (ap \<rho> \<sigma>) targs \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma> u"
      by (metis conv_trans)
  qed (use inv0 bs tyas tyu tys nrs lbs in simp_all)
  \<comment> \<open>The copy\<close>
  from mcp_mc_complete[OF cfg, of A K X env dps rb targs u \<rho> \<sigma> e Ss TT s "fst v"] pre spre kk k
  obtain sq x m where mc: "okW (mc cfg (fst v) rb targs u env dps) sq" and evx: "ev cfg sq x"
    and m: "rigid (fst (strip_comb u)) \<longrightarrow> m = 1" and cr: "mcp_cres A K X env rb targs u \<rho> \<sigma> Ss TT s m x"
    by blast
  have m1: "m = 1" using m ru' by simp
  have "fin cfg sq (copy_ok A (v, T) Ts)"
    using mc_fin[OF cfg finX finK si fr st bt len oc] mc unfolding cuok_def by auto
  then have cok: "copy_ok A (v, T) Ts x" using evals_ev evx unfolding fin_def by blast
  from cr obtain u' env' dps' A' K' X' \<rho>' \<sigma>' NV where c: "x = El_C u' env' dps'" "finite X'" "finite K'"
    "A \<subseteq> A'" "K \<subseteq> K'" "X \<subseteq> X'"
    "sinv A' K' X' env' dps'" "scinv \<rho>' \<sigma>' env' dps' X' A'" "extends env env'"
    "tvars_env (tyenv env) \<subseteq> tvars_env (tyenv env')" "tagree (maxidx env) \<rho> \<rho>'" "sagree (maxidx env) \<sigma> \<sigma>'"
    "vars u' \<subseteq> X' \<union> evars env'" "ttvars u' \<subseteq> tvars_env (tyenv env') \<union> A'" "\<not> loose_bvar u' (ilength Ss)"
    "\<forall>\<rho>0 e Us U. tsol (tyenv env') \<rho>0 \<longrightarrow> cert_inst \<rho>0 \<longrightarrow> bs_env \<rho>0 e rb \<longrightarrow>
      e \<tturnstile> map (inst \<rho>0) targs : Us \<longrightarrow> e \<turnstile> inst \<rho>0 u : U \<longrightarrow> (\<forall>e'. pushes e' Us \<turnstile> inst \<rho>0 u' : U)"
    "pushes mcp_e0 Ss \<turnstile> inst \<rho>' u' : TT" "types_abs Ss (ap \<rho>' \<sigma>' u') \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> types_abs Ss s"
    "finite NV" "NV \<subseteq> X'" "\<forall>y\<in>NV. maxidx env < snd (fst y)" "ubv env' X' \<subseteq> ubv env X \<union> fst ` NV"
    "(\<Sum>y\<in>NV. mcp_vsz \<rho>' \<sigma>' y) + m \<le> lsz (pushes mcp_e0 Ss) s - 2 * arity TT"
    "\<forall>k. mcp_kokK k \<rho> (tyenv env) A K \<longrightarrow> mcp_kokK k \<rho>' (tyenv env') A' K'"
    by (rule mcp_cresE)
  from cok c(1) have vn': "vt_lookup (tenv env') v = None"
    and acy: "\<forall>y U. (y, U) \<in> vars u' \<longrightarrow> (v, y) \<notin> (dep env')\<^sup>*"
    and tyw: "\<And>\<rho>0 e. tsol (tyenv env') \<rho>0 \<Longrightarrow> cert_inst \<rho>0 \<Longrightarrow> e \<turnstile> inst \<rho>0 (types_abs Ts u') : tsubst \<rho>0 T"
    unfolding copy_ok_def by auto
  \<comment> \<open>The binding of the variable\<close>
  let ?w = "types_abs Ts u'"
  from update_ok[OF vn'] obtain env'' where upd: "update (v, T) ?w env' = return env''" by blast
  then have upd': "ok (update (v, T) ?w env') env''" by (simp add: return_def)
  note ou = ok_update[OF upd']
  have ext': "extends env' env''" by (rule extends_update[OF upd'])
  have ext'': "extends env env''" by (rule extends_trans[OF c(9) ext'])
  have lTs: "ilength Ts = ilength Ss" using Ss by (simp add: ilength_eq)
  have cl: "closed ?w" using c(15) lTs by (simp add: closed_def mf_loose_bvar_types_abs)
  have mx': "maxidx env \<le> maxidx env'" using c(9) by (simp add: extends_def)
  have ei': "einv A' K' env'" and wi': "winv env' X'" using c(7) by (simp_all add: sinv_def)
  have tvw: "tvars T \<union> ttvars ?w \<subseteq> tvars_env (tyenv env') \<union> A'"
    using tvT tvTs c(14) c(4) c(10) unfolding mf_ttvars_types_abs by blast
  have ei'': "einv A' K' env''"
    by (rule einv_update[OF ei' upd' _ cl _ tvw]) (use acy mv mx' in auto)
  have vX': "(v, T) \<in> X' \<union> evars env'" using vT c(6) mcp_evars_extends[OF c(9)] by blast
  have vX'': "X' \<union> insert (v, T) (vars ?w) \<union> evars env' = X' \<union> evars env'" using vX' c(13) by auto
  have wi'': "winv env'' X'"
    unfolding winv_def
  proof (intro allI impI)
    fix \<rho>0 assume \<rho>0: "tsol (tyenv env'') \<rho>0" "cert_inst \<rho>0"
    then have \<rho>0': "tsol (tyenv env') \<rho>0" by (simp add: ou(3))
    have w: "wt_env \<rho>0 env'" "vinv \<rho>0 env' X'" using winvD[OF wi' \<rho>0' \<rho>0(2)] by blast+
    have "wt_env \<rho>0 env''" by (rule wt_env_update[OF upd' w(1) cl tyw[OF \<rho>0' \<rho>0(2)]])
    moreover have "vinv \<rho>0 env'' X'"
      by (rule vinv_update[OF upd']) (use w(2) vX'' in \<open>simp add: vinv_def\<close>)
    ultimately show "wt_env \<rho>0 env'' \<and> vinv \<rho>0 env'' X'" ..
  qed
  have si'': "sinv A' K' X' env'' dps'"
    using c(7) ei'' wi'' pok_mono[OF _ ext'] ou(3) unfolding sinv_def by auto
  \<comment> \<open>The solution\<close>
  note i' = scinvD[OF c(8)]
  have \<rho>'T: "tsubst \<rho>' T = tsubst \<rho> T" by (rule tsubst_agree[OF c(11) below_KN[OF tvT]])
  have \<rho>'Ts: "map (tsubst \<rho>') Ts = Ss" using tsubst_agree[OF c(11) below_KN] tvTs \<rho>Ts by (auto cong: map_cong)
  have \<sigma>'v: "\<sigma>' v (tsubst \<rho>' T) = \<sigma> v (tsubst \<rho> T)" using c(12) mv \<rho>'T by (cases v) (simp add: sagree_def)
  have apw: "ap \<rho>' \<sigma>' ?w = types_abs Ss (ap \<rho>' \<sigma>' u')" by (simp add: mcp_ap_types_abs \<rho>'Ts)
  have eqv: "\<sigma>' v (tsubst \<rho>' T) \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho>' \<sigma>' ?w"
    using cvs c(18) Tv \<sigma>'v apw by (metis conv_sym conv_trans)
  have tyw': "e0 \<turnstile> inst \<rho>' ?w : tsubst \<rho>' T" for e0
  proof -
    have "e0 \<turnstile> types_abs Ss (inst \<rho>' u') : Ss \<Rrightarrow> TT" by (rule mcp_typing_val[OF c(17)]) (use c(15) cSs in simp_all)
    then show ?thesis using \<rho>'T Tv by (simp add: mf_inst_types_abs \<rho>'Ts)
  qed
  have inv'': "scinv \<rho>' \<sigma>' env'' dps' X' A'"
    unfolding scinv_def
  proof (intro conjI)
    show "solution \<rho>' \<sigma>' env''" by (rule mcp_solution_update[OF upd' i'(1) eqv])
    show "wt_env \<rho>' env''" by (rule wt_env_update[OF upd' i'(2) cl tyw'])
    show "vinv \<rho>' env'' X'" by (rule vinv_update[OF upd']) (use i'(3) vX'' in \<open>simp add: vinv_def\<close>)
    show "tvinv A' env''" using ei'' by (simp add: einv_def)
    show "vtvars X' \<subseteq> tvars_env (tyenv env'') \<union> A'" using i'(5) ou(3) by simp
  qed (use i'(6,7) in simp_all)
  \<comment> \<open>The measure\<close>
  have ub'': "ubv env'' X' \<subseteq> (ubv env X - {v}) \<union> fst ` NV"
  proof
    fix y assume y: "y \<in> ubv env'' X'"
    have vin: "v \<in> fst ` (X' \<union> evars env')" using vX' by force
    from ubv_update[OF upd' vin] y have "y \<in> ubv env' X' - {v} \<or> (y \<in> vns ?w \<and> vt_lookup (tenv env'') y = None)"
      by blast
    then have "y \<in> ubv env' X' - {v}"
    proof
      assume a: "y \<in> vns ?w \<and> vt_lookup (tenv env'') y = None"
      then have "y \<noteq> v" using ou(2) by auto
      moreover have "vt_lookup (tenv env') y = None" using a ou(2) by (auto split: if_splits)
      moreover have "y \<in> fst ` (X' \<union> evars env')" using a c(13) by auto
      ultimately show ?thesis unfolding ubv_def by blast
    qed
    then show "y \<in> (ubv env X - {v}) \<union> fst ` NV" using c(22) by blast
  qed
  have vi'': "vinv \<rho>' env'' X'" using scinvD(3)[OF inv''] .
  have sub'': "X \<union> evars env \<subseteq> X' \<union> evars env''"
    using c(6) mcp_evars_extends[OF ext''] by blast
  have lt: "(\<Sum>y\<in>NV. mcp_vsz \<rho>' \<sigma>' y) < mcp_vsz \<rho> \<sigma> (v, mcp_rep env X v)"
    using c(23) m1 arTT vsz mcp_vsz_rep[OF i(3) vU vT, of \<sigma>] by simp
  have meas: "mcp_meas \<rho>' \<sigma>' env'' X' < mcp_meas \<rho> \<sigma> env X"
    by (rule mcp_meas_bind[OF inv c(11,12) vi'' sub'' finX c(2) c(19,20) ub'' vU lt])
  have kk'': "mcp_kokK k \<rho>' (tyenv env'') A' K'" using c(24) kk ou(3) by simp
  have res: "mcp_mres A K X env \<rho> \<sigma> k (El_E env'' dps')"
    by (rule mcp_mresI[OF refl c(2-6) si'' inv'' ext'' c(11,12) kk'' meas])
  \<comment> \<open>The sequence\<close>
  have nd: "okW (new_dset (v, T) Ts u' env' dps') (El_E env'' dps')"
    by (simp add: new_dset_def lookup_unbound[OF vn'] upd return_def)
  have evn: "ev cfg (S_MapNewDset (v, T) Ts sq) (El_E env'' dps')"
    by (rule ev.new_dset[OF evx[unfolded c(1)] nd])
  have "okW (match_pair cfg env (rb, t, u) dps) (S_MapNewDset (v, T) Ts sq)"
    using mc by (auto simp: match_pair_def st bt oc return_def)
  with evn res show ?thesis by blast
qed


text \<open>The same for an occurring variable, from the completeness of \<^const>\<open>match1\<close>:\<close>

lemma mcp_match_pair_m1:
  assumes cfg: "cfg_alg cfg = alg" and k: "k = nat_of_integer (cfg_arity_bound cfg)"
    and finX: "finite X" and finK: "finite K" and si: "sinv A K X env ((rb, t, u) # dps)"
    and fr: "fr_shape env (rb, t, u)" and inv: "scinv \<rho> \<sigma> env ((rb, t, u) # dps) X A"
    and kk: "mcp_kokK k \<rho> (tyenv env) A K"
    and st: "strip_comb t = (Var v T, targs)" and bt: "binder_types env T = return Ts"
    and len: "length Ts = length targs" and bT: "body_type env T = return B" and ar0: "arity (tsubst \<rho> B) = 0"
    and sat: "satd env rb u"
    and oc: "occurs_terms env v (u # targs @ concat (map (\<lambda>(_, t, u). [t, u]) dps)) = return True"
  shows "\<exists>s. okW (match_pair cfg env (rb, t, u) dps) s \<and> (\<exists>x. ev cfg s x \<and> mcp_mres A K X env \<rho> \<sigma> k x)"
proof -
  let ?\<theta> = "tyenv env" and ?KN = "tvars_env (tyenv env) \<union> A"
  have ei: "einv A K env" and wi: "winv env X" and p: "pok A env rb X t u"
    using si by (auto simp: sinv_def)
  have si0: "sinv A K X env ((rb, t, u) # dps)" by (rule si)
  have inv0: "scinv \<rho> \<sigma> env ((rb, t, u) # dps) X A" by (rule inv)
  note i = scinvD[OF inv] and sd = solutionD[OF scinvD(1)[OF inv]] and pd = pokD[OF p] and x = einvD[OF ei]
  have tt: "t = Var v T \<degree>\<degree> targs" by (rule strip_comb_apps[OF st])
  have hv: "head_of t = Var v T" using st by (simp add: head_of_strip_comb)
  have hb: "hunb env (rb, t, u)" and f0: "frs0 (rb, t, u)" using fr by (simp_all add: fr_shape_def)
  from hb hv have vn: "vt_lookup (tenv env) v = None" unfolding hunb_def by blast
  from f0 have nAu: "\<not> is_Abs u" and ru: "rigid (head_of u)" unfolding frs0_def by simp_all
  have ru': "rigid (fst (strip_comb u))" using ru by (simp add: head_of_strip_comb)
  have vT: "(v, T) \<in> X \<union> evars env" using pd(1) tt by (simp add: vars_apps)
  have vU: "v \<in> ubv env X" using vT vn unfolding ubv_def by force
  have mv: "snd v \<le> maxidx env" using i(3) vT unfolding vinv_def below_def by force
  have tvT: "tvars T \<subseteq> ?KN" using head_tvars_strip_comb[OF st] pd(3) by blast
  have below_KN: "tbelow (maxidx env) S" if "S \<subseteq> ?KN" for S using tvinv_tbelow[OF i(4) that] .
  from mf_binder_types_sound[OF bt[unfolded return_def] refl x(6)]
  have tvTs: "\<forall>U\<in>set Ts. tvars U \<subseteq> ?KN" using tvT x(9) by blast
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
  with funs_eq[OF lSs'] have Ss: "Ss = map (tsubst \<rho>) Ts" and TT: "TT = tsubst \<rho> B" by blast+
  have arTT: "arity TT = 0" using ar0 TT by simp
  have cSs: "\<forall>S\<in>set Ss. cert_typ alg ar S" using cT Tv by (simp add: cert_typ_funs)
  have \<rho>Ts: "map (tsubst \<rho>) Ts = Ss" using Ss by simp
  \<comment> \<open>The target\<close>
  obtain s where tys: "pushes mcp_e0 Ss \<turnstile> s : TT" and nrs: "no_redex s" and lbs: "\<not> loose_bvar s (ilength Ss)"
    and cvs: "types_abs Ss s \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> \<sigma> v (Ss \<Rrightarrow> TT)"
    by (rule mcp_value_target[OF sd(3), of Ss TT v]) (use cT Tv in simp)
  have vsz: "mcp_vsz \<rho> \<sigma> (v, T) = lsz (pushes mcp_e0 Ss) s"
    using mcp_vsz_val[OF sd(3) cT _ Tv tys nrs cSs] cvs arTT Tv by (simp add: conv_sym)
  have pre: "mcp_pre A K X env ((rb, t, u) # dps) rb targs u"
    unfolding mcp_pre_def
  proof (intro conjI)
    show "vars u \<subseteq> X \<union> evars env" by (rule pd(2))
    show "mlvars targs \<subseteq> X \<union> evars env" using pd(1) tt by (auto simp: vars_apps)
    show "ttvars u \<union> (\<Union>t\<in>set targs. ttvars t) \<union> btvars rb \<subseteq> ?KN"
      using pd(3,4,5) tt by (auto simp: ttvars_apps)
    show "\<not> loose_bvar u (ilength rb)" by (rule pd(8))
    show "\<forall>t\<in>set targs. \<not> loose_bvar t (ilength rb)" using pd(7) tt by (simp add: loose_bvar_apps)
    show "mcp_tok env rb targs u"
      unfolding mcp_tok_def
    proof (intro allI impI)
      fix \<rho>0 assume "tsol ?\<theta> \<rho>0" "cert_inst \<rho>0"
      from pd(9)[OF this] obtain e0 T0 where "bs_env \<rho>0 e0 rb" "e0 \<turnstile> inst \<rho>0 t : T0" "e0 \<turnstile> inst \<rho>0 u : T0"
        by blast
      moreover from this(2)[unfolded tt inst_apps] obtain Us where "e0 \<tturnstile> map (inst \<rho>0) targs : Us"
        by (rule list_app_typeE)
      ultimately show "\<exists>e Us U. bs_env \<rho>0 e rb \<and> e \<tturnstile> map (inst \<rho>0) targs : Us \<and> e \<turnstile> inst \<rho>0 u : U" by blast
    qed
  qed (use finX finK si0 sat in simp_all)
  have spre: "mcp_spre \<rho> \<sigma> env ((rb, t, u) # dps) X A e rb targs Ss u TT s"
    unfolding mcp_spre_def
  proof (intro conjI)
    show "arity TT = nabs u" using arTT nAu by simp
    have "ap \<rho> \<sigma> t = \<sigma> v (Ss \<Rrightarrow> TT) \<degree>\<degree> map (ap \<rho> \<sigma>) targs"
      unfolding tt ap_apps using Tv by (simp add: ap_def)
    moreover have "ap \<rho> \<sigma> t \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma> u" using i(7) by (auto simp: dsolved_def)
    moreover have "types_abs Ss s \<degree>\<degree> map (ap \<rho> \<sigma>) targs \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> \<sigma> v (Ss \<Rrightarrow> TT) \<degree>\<degree> map (ap \<rho> \<sigma>) targs"
    proof (rule conv_apps[OF _ _ _ cvs])
      show "list_all2 (\<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta>) (map (ap \<rho> \<sigma>) targs) (map (ap \<rho> \<sigma>) targs)"
        by (simp add: list_all2_refl)
      have ta: "e \<tturnstile> map (ap \<rho> \<sigma>) targs : Ss"
        using tyas by (induction targs arbitrary: Ss) (auto split: list.splits intro: typing_ap[OF _ sd(3)])
      have "e \<turnstile> types_abs Ss s : Ss \<Rrightarrow> TT" by (rule mcp_typing_val[OF tys lbs cSs])
      from list_app_typeI[OF this ta] show "wt (types_abs Ss s \<degree>\<degree> map (ap \<rho> \<sigma>) targs)" by (auto simp: wt_def)
      have "e \<turnstile> \<sigma> v (Ss \<Rrightarrow> TT) : Ss \<Rrightarrow> TT" by (rule wt_subst_typing[OF sd(3)]) (use cT Tv in simp)
      from list_app_typeI[OF this ta] show "wt (\<sigma> v (Ss \<Rrightarrow> TT) \<degree>\<degree> map (ap \<rho> \<sigma>) targs)" by (auto simp: wt_def)
    qed
    ultimately show "types_abs Ss s \<degree>\<degree> map (ap \<rho> \<sigma>) targs \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma> u"
      by (metis conv_trans)
  qed (use inv0 bs tyas tyu tys nrs lbs in simp_all)
  \<comment> \<open>The copy\<close>
  from mcp_match1_complete[OF cfg pre spre kk[unfolded k] ru', of "fst v"]
  obtain sq x where mc: "okW (match1 cfg (fst v) rb targs u env ((rb, t, u) # dps)) sq" and evx: "ev cfg sq x"
    and cr0: "mcp_cres A K X env rb targs u \<rho> \<sigma> Ss TT s 1 x" by blast
  obtain m :: nat where m1: "m = 1" and cr: "mcp_cres A K X env rb targs u \<rho> \<sigma> Ss TT s m x" using cr0 by blast
  have "fin cfg sq (copy_ok A (v, T) Ts)"
    using match1_fin[OF cfg finX finK si fr st bt len, of "fst v"] mc unfolding cuok_def by auto
  then have cok: "copy_ok A (v, T) Ts x" using evals_ev evx unfolding fin_def by blast
  from cr obtain u' env' dps' A' K' X' \<rho>' \<sigma>' NV where c: "x = El_C u' env' dps'" "finite X'" "finite K'"
    "A \<subseteq> A'" "K \<subseteq> K'" "X \<subseteq> X'"
    "sinv A' K' X' env' dps'" "scinv \<rho>' \<sigma>' env' dps' X' A'" "extends env env'"
    "tvars_env (tyenv env) \<subseteq> tvars_env (tyenv env')" "tagree (maxidx env) \<rho> \<rho>'" "sagree (maxidx env) \<sigma> \<sigma>'"
    "vars u' \<subseteq> X' \<union> evars env'" "ttvars u' \<subseteq> tvars_env (tyenv env') \<union> A'" "\<not> loose_bvar u' (ilength Ss)"
    "\<forall>\<rho>0 e Us U. tsol (tyenv env') \<rho>0 \<longrightarrow> cert_inst \<rho>0 \<longrightarrow> bs_env \<rho>0 e rb \<longrightarrow>
      e \<tturnstile> map (inst \<rho>0) targs : Us \<longrightarrow> e \<turnstile> inst \<rho>0 u : U \<longrightarrow> (\<forall>e'. pushes e' Us \<turnstile> inst \<rho>0 u' : U)"
    "pushes mcp_e0 Ss \<turnstile> inst \<rho>' u' : TT" "types_abs Ss (ap \<rho>' \<sigma>' u') \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> types_abs Ss s"
    "finite NV" "NV \<subseteq> X'" "\<forall>y\<in>NV. maxidx env < snd (fst y)" "ubv env' X' \<subseteq> ubv env X \<union> fst ` NV"
    "(\<Sum>y\<in>NV. mcp_vsz \<rho>' \<sigma>' y) + m \<le> lsz (pushes mcp_e0 Ss) s - 2 * arity TT"
    "\<forall>k. mcp_kokK k \<rho> (tyenv env) A K \<longrightarrow> mcp_kokK k \<rho>' (tyenv env') A' K'"
    by (rule mcp_cresE)
  from cok c(1) have vn': "vt_lookup (tenv env') v = None"
    and acy: "\<forall>y U. (y, U) \<in> vars u' \<longrightarrow> (v, y) \<notin> (dep env')\<^sup>*"
    and tyw: "\<And>\<rho>0 e. tsol (tyenv env') \<rho>0 \<Longrightarrow> cert_inst \<rho>0 \<Longrightarrow> e \<turnstile> inst \<rho>0 (types_abs Ts u') : tsubst \<rho>0 T"
    unfolding copy_ok_def by auto
  \<comment> \<open>The binding of the variable\<close>
  let ?w = "types_abs Ts u'"
  from update_ok[OF vn'] obtain env'' where upd: "update (v, T) ?w env' = return env''" by blast
  then have upd': "ok (update (v, T) ?w env') env''" by (simp add: return_def)
  note ou = ok_update[OF upd']
  have ext': "extends env' env''" by (rule extends_update[OF upd'])
  have ext'': "extends env env''" by (rule extends_trans[OF c(9) ext'])
  have lTs: "ilength Ts = ilength Ss" using Ss by (simp add: ilength_eq)
  have cl: "closed ?w" using c(15) lTs by (simp add: closed_def mf_loose_bvar_types_abs)
  have mx': "maxidx env \<le> maxidx env'" using c(9) by (simp add: extends_def)
  have ei': "einv A' K' env'" and wi': "winv env' X'" using c(7) by (simp_all add: sinv_def)
  have tvw: "tvars T \<union> ttvars ?w \<subseteq> tvars_env (tyenv env') \<union> A'"
    using tvT tvTs c(14) c(4) c(10) unfolding mf_ttvars_types_abs by blast
  have ei'': "einv A' K' env''"
    by (rule einv_update[OF ei' upd' _ cl _ tvw]) (use acy mv mx' in auto)
  have vX': "(v, T) \<in> X' \<union> evars env'" using vT c(6) mcp_evars_extends[OF c(9)] by blast
  have vX'': "X' \<union> insert (v, T) (vars ?w) \<union> evars env' = X' \<union> evars env'" using vX' c(13) by auto
  have wi'': "winv env'' X'"
    unfolding winv_def
  proof (intro allI impI)
    fix \<rho>0 assume \<rho>0: "tsol (tyenv env'') \<rho>0" "cert_inst \<rho>0"
    then have \<rho>0': "tsol (tyenv env') \<rho>0" by (simp add: ou(3))
    have w: "wt_env \<rho>0 env'" "vinv \<rho>0 env' X'" using winvD[OF wi' \<rho>0' \<rho>0(2)] by blast+
    have "wt_env \<rho>0 env''" by (rule wt_env_update[OF upd' w(1) cl tyw[OF \<rho>0' \<rho>0(2)]])
    moreover have "vinv \<rho>0 env'' X'"
      by (rule vinv_update[OF upd']) (use w(2) vX'' in \<open>simp add: vinv_def\<close>)
    ultimately show "wt_env \<rho>0 env'' \<and> vinv \<rho>0 env'' X'" ..
  qed
  have si'': "sinv A' K' X' env'' dps'"
    using c(7) ei'' wi'' pok_mono[OF _ ext'] ou(3) unfolding sinv_def by auto
  \<comment> \<open>The solution\<close>
  note i' = scinvD[OF c(8)]
  have \<rho>'T: "tsubst \<rho>' T = tsubst \<rho> T" by (rule tsubst_agree[OF c(11) below_KN[OF tvT]])
  have \<rho>'Ts: "map (tsubst \<rho>') Ts = Ss" using tsubst_agree[OF c(11) below_KN] tvTs \<rho>Ts by (auto cong: map_cong)
  have \<sigma>'v: "\<sigma>' v (tsubst \<rho>' T) = \<sigma> v (tsubst \<rho> T)" using c(12) mv \<rho>'T by (cases v) (simp add: sagree_def)
  have apw: "ap \<rho>' \<sigma>' ?w = types_abs Ss (ap \<rho>' \<sigma>' u')" by (simp add: mcp_ap_types_abs \<rho>'Ts)
  have eqv: "\<sigma>' v (tsubst \<rho>' T) \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho>' \<sigma>' ?w"
    using cvs c(18) Tv \<sigma>'v apw by (metis conv_sym conv_trans)
  have tyw': "e0 \<turnstile> inst \<rho>' ?w : tsubst \<rho>' T" for e0
  proof -
    have "e0 \<turnstile> types_abs Ss (inst \<rho>' u') : Ss \<Rrightarrow> TT" by (rule mcp_typing_val[OF c(17)]) (use c(15) cSs in simp_all)
    then show ?thesis using \<rho>'T Tv by (simp add: mf_inst_types_abs \<rho>'Ts)
  qed
  have inv'': "scinv \<rho>' \<sigma>' env'' dps' X' A'"
    unfolding scinv_def
  proof (intro conjI)
    show "solution \<rho>' \<sigma>' env''" by (rule mcp_solution_update[OF upd' i'(1) eqv])
    show "wt_env \<rho>' env''" by (rule wt_env_update[OF upd' i'(2) cl tyw'])
    show "vinv \<rho>' env'' X'" by (rule vinv_update[OF upd']) (use i'(3) vX'' in \<open>simp add: vinv_def\<close>)
    show "tvinv A' env''" using ei'' by (simp add: einv_def)
    show "vtvars X' \<subseteq> tvars_env (tyenv env'') \<union> A'" using i'(5) ou(3) by simp
  qed (use i'(6,7) in simp_all)
  \<comment> \<open>The measure\<close>
  have ub'': "ubv env'' X' \<subseteq> (ubv env X - {v}) \<union> fst ` NV"
  proof
    fix y assume y: "y \<in> ubv env'' X'"
    have vin: "v \<in> fst ` (X' \<union> evars env')" using vX' by force
    from ubv_update[OF upd' vin] y have "y \<in> ubv env' X' - {v} \<or> (y \<in> vns ?w \<and> vt_lookup (tenv env'') y = None)"
      by blast
    then have "y \<in> ubv env' X' - {v}"
    proof
      assume a: "y \<in> vns ?w \<and> vt_lookup (tenv env'') y = None"
      then have "y \<noteq> v" using ou(2) by auto
      moreover have "vt_lookup (tenv env') y = None" using a ou(2) by (auto split: if_splits)
      moreover have "y \<in> fst ` (X' \<union> evars env')" using a c(13) by auto
      ultimately show ?thesis unfolding ubv_def by blast
    qed
    then show "y \<in> (ubv env X - {v}) \<union> fst ` NV" using c(22) by blast
  qed
  have vi'': "vinv \<rho>' env'' X'" using scinvD(3)[OF inv''] .
  have sub'': "X \<union> evars env \<subseteq> X' \<union> evars env''"
    using c(6) mcp_evars_extends[OF ext''] by blast
  have lt: "(\<Sum>y\<in>NV. mcp_vsz \<rho>' \<sigma>' y) < mcp_vsz \<rho> \<sigma> (v, mcp_rep env X v)"
    using c(23) m1 arTT vsz mcp_vsz_rep[OF i(3) vU vT, of \<sigma>] by simp
  have meas: "mcp_meas \<rho>' \<sigma>' env'' X' < mcp_meas \<rho> \<sigma> env X"
    by (rule mcp_meas_bind[OF inv c(11,12) vi'' sub'' finX c(2) c(19,20) ub'' vU lt])
  have kk'': "mcp_kokK k \<rho>' (tyenv env'') A' K'" using c(24) kk ou(3) by simp
  have res: "mcp_mres A K X env \<rho> \<sigma> k (El_E env'' dps')"
    by (rule mcp_mresI[OF refl c(2-6) si'' inv'' ext'' c(11,12) kk'' meas])
  \<comment> \<open>The sequence\<close>
  have nd: "okW (new_dset (v, T) Ts u' env' dps') (El_E env'' dps')"
    by (simp add: new_dset_def lookup_unbound[OF vn'] upd return_def)
  have evn: "ev cfg (S_MapNewDset (v, T) Ts sq) (El_E env'' dps')"
    by (rule ev.new_dset[OF evx[unfolded c(1)] nd])
  have "okW (match_pair cfg env (rb, t, u) dps) (S_MapNewDset (v, T) Ts sq)"
    using mc by (auto simp: match_pair_def st bt oc return_def)
  with evn res show ?thesis by blast
qed


lemma mcp_match_pair_complete:
  assumes cfg: "cfg_alg cfg = alg" and k: "k = nat_of_integer (cfg_arity_bound cfg)"
    and finX: "finite X" and finK: "finite K" and si: "sinv A K X env ((rb, t, u) # dps)"
    and fr: "fr_shape env (rb, t, u)" and inv: "scinv \<rho> \<sigma> env ((rb, t, u) # dps) X A"
    and kk: "mcp_kokK k \<rho> (tyenv env) A K"
    and st: "strip_comb t = (Var v T, targs)" and bt: "binder_types env T = return Ts"
    and len: "length Ts = length targs" and bT: "body_type env T = return B" and ar0: "arity (tsubst \<rho> B) = 0"
    and sat: "satd env rb u"
  shows "\<exists>s. okW (match_pair cfg env (rb, t, u) dps) s \<and> (\<exists>x. ev cfg s x \<and> mcp_mres A K X env \<rho> \<sigma> k x)"
proof -
  let ?L = "u # targs @ concat (map (\<lambda>(_, t, u). [t, u]) dps)"
  have ei: "einv A K env" and wi: "winv env X" and p: "pok A env rb X t u"
    and ps: "\<forall>(rb', t', u')\<in>set dps. pok A env rb' X t' u'"
    using si by (auto simp: sinv_def)
  have t: "t = Var v T \<degree>\<degree> targs" by (rule strip_comb_apps[OF st])
  have "\<forall>s\<in>set ?L. vars s \<subseteq> X \<union> evars env"
  proof
    fix s assume "s \<in> set ?L"
    then consider "s = u" | "s \<in> set targs" | rb' t' u' where "(rb', t', u') \<in> set dps" "s = t' \<or> s = u'"
      by auto
    then show "vars s \<subseteq> X \<union> evars env"
    proof cases
      case 2
      then show ?thesis using pokD(1)[OF p] t by (auto simp: vars_apps)
    next
      case (3 rb' t' u')
      with ps have "pok A env rb' X t' u'" by auto
      with 3(2) show ?thesis using pokD(1,2) by blast
    qed (use pokD(2)[OF p] in simp)
  qed
  from occurs_terms_term[OF ei wi pokD(6)[OF p] this, of v] obtain b where oc: "occurs_terms env v ?L = return b"
    by blast
  show ?thesis
  proof (cases b)
    case True
    have oc1: "occurs_terms env v ?L = return True" using oc True by simp
    from mcp_match_pair_m1[OF cfg refl finX finK si fr inv kk[unfolded k] st bt len bT ar0 sat oc1] k
    show ?thesis by simp
  next
    case False
    from mcp_match_pair_mc[OF cfg k finX finK si fr inv kk st bt len bT ar0 sat] oc False show ?thesis by simp
  qed
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
  have p: "pok A env rb X t u" using si by (simp add: sinv_def)
  define Es where "Es = drop (length targs) Ts"
  obtain rb' t' u' where ed: "eta_expand_dpair Es (rb, t, u) = (rb', t', u')" by (cases "eta_expand_dpair Es (rb, t, u)")
  have t': "t' = incr_bv (ilength Es) 0 t \<degree>\<degree> mbvs (length Es)" and u': "u' = incr_bv (ilength Es) 0 u \<degree>\<degree> mbvs (length Es)"
    using ed by (auto simp: eta_expand_dpair_def Let_def incr_boundvars_def list_comb_apps ilength_eq split: if_splits)
  have ds: "dstep env [(rb, t, u)] env [(rb', t', u')]"
    using dstep_eta_expand[OF st _ len, of env rb u] bt ed by (simp add: return_def Es_def)
  have "X \<union> dvars [(rb, t, u)] \<union> evars env = X \<union> evars env" using pokD(1,2)[OF p] by auto
  then have vi: "vinv \<rho> env (X \<union> dvars [(rb, t, u)])" using i(3) unfolding vinv_def by simp
  have dt1: "dtyped \<rho> [(rb, t, u)]" by (rule dtyped_mono[OF i(6)]) simp
  from dstepD(2)[OF ds sd(2) extends_refl i(2) dt1 vi] have dt': "dtyped \<rho> [(rb', t', u')]" by blast
  then obtain e' U where tyt: "e' \<turnstile> inst \<rho> t' : U" and tyu: "e' \<turnstile> inst \<rho> u' : U" by (auto simp: dtyped_def)
  have "ap \<rho> \<sigma> t \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma> u" using i(7) by (auto simp: dsolved_def)
  then have c: "incr_bv (ilength Es) 0 (ap \<rho> \<sigma> t) \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> incr_bv (ilength Es) 0 (ap \<rho> \<sigma> u)"
    unfolding ilength_eq by (rule mcp_conv_incr) simp
  have "ap \<rho> \<sigma> t' \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma> u'"
  proof -
    have e1: "ap \<rho> \<sigma> t' = incr_bv (ilength Es) 0 (ap \<rho> \<sigma> t) \<degree>\<degree> map (ap \<rho> \<sigma>) (mbvs (length Es))"
      unfolding t' ap_apps by (simp add: ap_lift[OF sd(3)])
    have e2: "ap \<rho> \<sigma> u' = incr_bv (ilength Es) 0 (ap \<rho> \<sigma> u) \<degree>\<degree> map (ap \<rho> \<sigma>) (mbvs (length Es))"
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
    and sat: "\<And>Ts rb' t' u'. binder_types env T = return Ts \<Longrightarrow>
      eta_expand_dpair (drop (length targs) Ts) (rb, t, u) = (rb', t', u') \<Longrightarrow> satd env rb' u'"
  shows "\<exists>s. okW (match_sat cfg env (rb, t, u) dps) s \<and> (\<exists>x. ev cfg s x \<and> mcp_mres A K X env \<rho> \<sigma> k x)"
proof -
  have ei: "einv A K env" and p: "pok A env rb X t u" using si by (auto simp: sinv_def)
  have tv: "tvars T \<subseteq> tvars_env (tyenv env) \<union> A" using head_tvars_strip_comb[OF st] pokD(3)[OF p] by blast
  from binder_types_term[OF einvD(2)[OF ei] refl tv] obtain Ts where bt: "binder_types env T = return Ts" by blast
  define Es where "Es = drop (length targs) Ts"
  obtain rb' t' u' where ed: "eta_expand_dpair Es (rb, t, u) = (rb', t', u')"
    by (cases "eta_expand_dpair Es (rb, t, u)")
  have len: "length targs \<le> length Ts" by (rule sinv_eta_expand(1)[OF si st bt])
  have si': "sinv A K X env ((rb', t', u') # dps)" using sinv_eta_expand(2)[OF si st bt] ed by (simp add: Es_def)
  have inv': "scinv \<rho> \<sigma> env ((rb', t', u') # dps) X A" using mcp_scinv_eta_expand[OF si inv st bt] ed by (simp add: Es_def)
  have fr': "fr_shape env (rb', t', u')" using fr_shape_eta_expand[OF fr, of Es] ed by simp
  have t': "t' = incr_bv (ilength Es) 0 t \<degree>\<degree> mbvs (length Es)"
    using ed by (auto simp: eta_expand_dpair_def Let_def incr_boundvars_def list_comb_apps ilength_eq split: if_splits)
  have st': "strip_comb t' = (Var v T, map (incr_bv (ilength Es) 0) targs @ mbvs (length Es))"
    unfolding t' by (rule mf_strip_comb_expand[OF st])
  have len': "length Ts = length (map (incr_bv (ilength Es) 0) targs @ mbvs (length Es))"
    using len by (simp add: Es_def)
  have sat': "satd env rb' u'" by (rule sat[OF bt ed[unfolded Es_def]])
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
  have ps: "\<forall>(rb', t', u')\<in>set dps. pok A env rb' X t' u'" using si by (simp add: sinv_def)
  obtain \<rho>1 where \<rho>1: "tagree (maxidx env) \<rho> \<rho>1" "map (tsubst \<rho>1) Cs = Ds" "wsinst alg \<rho>1"
    by (rule mcp_gentvars_inst[OF g lD sd(1)])
  have si0: "sinv ?A0 ?K0 X env0 dps" by (rule sinv_gentvars[OF si g])
  have ei0: "einv ?A0 ?K0 env0" using si0 by (simp add: sinv_def)
  have ext0: "extends env env0" by (rule mcp_extends_same[OF gs(1,2,3)])
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

lemma mcp_arity_tsubst: "arity T \<le> arity (tsubst \<rho> T)"
  by (induction T rule: arity.induct) auto

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


text \<open>
  After the unification of the types of the sides, the rigid side of the \<open>\<eta>\<close>-expanded pair is
  saturated (as in the proof of @{thm [source] frs_shape_MATCH_ok}, for every type instantiation):
\<close>

lemma mcp_top_satd:
  assumes sh: "frs_shape (rb, t, u)" and T1: "ok (fastype env0 rb t) T1" and U1: "ok (fastype env0 rb u) U1"
    and cu: "okW (cunify_types alg' T1 U1 env0) env1" and ext: "extends env1 env2"
    and st: "strip_comb t = (Var v T, targs)" and bt: "ok (binder_types env2 T) Ts"
    and ed: "eta_expand_dpair (drop (length targs) Ts) (rb, t, u) = (rb', t', u')"
    and w0: "tsol (tyenv env2) \<rho>0" and bs0: "bs_env \<rho>0 e0 rb'"
    and tyt0: "e0 \<turnstile> inst \<rho>0 t' : U0" and tyu0: "e0 \<turnstile> inst \<rho>0 u' : U0"
  shows "satd env2 rb' u'"
proof -
  from sh have nAu: "\<not> is_Abs u" and hu: "head_nf u" by (simp_all add: frs_shape_def)
  have ext1: "extends env0 env1" by (rule cunify_types_sound(2)[OF cu])
  have ext02: "extends env0 env2" by (rule extends_trans[OF ext1 ext])
  have te02: "textends (tyenv env0) (tyenv env2)" and te12: "textends (tyenv env1) (tyenv env2)"
    using ext02 ext by (simp_all add: extends_def)
  have t: "t = Var v T \<degree>\<degree> targs" by (rule strip_comb_apps[OF st])
  have fv: "ok (env_fastype env0 (map snd rb) (Var v T)) T" by simp
  define Es where "Es = drop (length targs) Ts"
  from env_fastype_apps_binder_types[OF T1[unfolded fastype_def t] fv te02 bt]
  have bT1: "ok (binder_types env2 T1) Es" by (simp_all add: Es_def)
  define hu where "hu = fst (strip_comb u)"
  define uargs where "uargs = snd (strip_comb u)"
  have u: "u = hu \<degree>\<degree> uargs" by (rule strip_comb_apps) (simp add: hu_def uargs_def)
  have nAhu: "\<not> is_Abs hu" using nAu hu by (simp add: head_nf_nonAbs hu_def fst_strip_comb)
  have nApp: "\<not> (\<exists>f a. hu = f $ a)" using strip_comb_head[of u hu uargs] by (simp add: hu_def uargs_def)
  from env_fastype_apps_head[OF U1[unfolded fastype_def u]] obtain H
    where fH: "ok (env_fastype env0 (map snd rb) hu) H" by blast
  define k where "k = ilength Es"
  define h' where "h' = incr_bv k 0 hu"
  define args' where "args' = map (incr_bv k 0) uargs @ bvs (length Es)"
  have rb': "rb' = rev (map (\<lambda>T. (STR '''', T)) Es) @ rb"
    and t': "t' = incr_bv k 0 t \<degree>\<degree> bvs (length Es)" and u'0: "u' = incr_bv k 0 u \<degree>\<degree> bvs (length Es)"
    using ed by (auto simp: eta_expand_dpair_def Let_def incr_boundvars_def list_comb_apps ilength_eq k_def Es_def
        split: if_splits)
  have u': "u' = h' \<degree>\<degree> args'" by (simp add: u'0 h'_def args'_def u incr_bv_apps)
  have nApp': "\<not> (\<exists>f a. h' = f $ a)" and nAh': "\<not> is_Abs h'"
    using nApp nAhu by (cases hu; simp add: h'_def)+
  have sh': "fst (strip_comb u') = h'" by (simp add: u' strip_comb_atom_apps[OF nApp'])
  have mrb': "map snd rb' = rev Es @ map snd rb" by (simp add: rb' rev_map comp_def)
  have fh': "ok (fastype env2 rb' h') H"
    using env_fastype_incr_atom[OF nAhu nApp fH, of env2 "rev Es"]
    by (simp add: fastype_def mrb' h'_def k_def ilength_eq)
  have lh: "\<not> loose_bvar h' (ilength rb')"
  proof (cases h')
    case (Bound j)
    have nh: False if "ok (case e of Subscript \<Rightarrow> raise (Term_Error (STR ''fastype: Bound'') [Bound j])
        | _ \<Rightarrow> raise e) y" for e and y :: ptyp
      using that by (cases e) auto
    from fh' Bound have "ok (nth (map snd rb') j) H" by (auto simp: fastype_def ok_handle dest: nh)
    then show ?thesis by (simp add: Bound ok_nth ilength_eq)
  qed (use nAh' nApp' in simp_all)
  have tsol0: "tsol (tyenv env0) \<rho>0" by (rule extends_tsol[OF w0 ext02])
  have tsol1: "tsol (tyenv env1) \<rho>0" by (rule extends_tsol[OF w0 ext])
  \<comment> \<open>The arities agree, by the witness \<open>\<rho>0\<close>:\<close>
  from tyu0[unfolded u' inst_apps] obtain Ws0 where tyh0: "e0 \<turnstile> inst \<rho>0 h' : Ws0 \<Rrightarrow> U0"
    by (rule list_app_typeE)
  have H0: "tsubst \<rho>0 H = Ws0 \<Rrightarrow> U0" by (rule fastype_sound[OF fh' w0 bs0 tyh0])
  from bs_env_cert[OF bs0 tyh0 lh] H0 have wH: "wft ar (tsubst \<rho>0 H)" by (simp add: cert_wft)
  have wU1: "wft ar (tsubst \<rho>0 U1)" by (rule env_fastype_apps_wft[OF U1[unfolded fastype_def u] fH tsol0 wH])
  have st': "strip_comb t' = (Var v T, map (incr_bv k 0) targs @ bvs (length Es))"
    by (simp add: t' strip_comb_expand[OF st])
  from tyt0[unfolded strip_comb_apps[OF st'] inst_apps] obtain Ws' where "e0 \<turnstile> inst \<rho>0 (Var v T) : Ws' \<Rrightarrow> U0"
    by (rule list_app_typeE)
  then have "cert_typ alg ar (tsubst \<rho>0 T)" by auto
  then have wT: "wft ar (tsubst \<rho>0 T)" by (rule cert_wft)
  have wT1: "wft ar (tsubst \<rho>0 T1)" by (rule env_fastype_apps_wft[OF T1[unfolded fastype_def t] fv tsol0 wT])
  have sp: "tspine (tyenv env1) T1 U1" by (rule cunify_types_tspine[OF cu tsol1 wT1 wU1])
  have "U = tsubst \<rho> B"
    if f0: "ok (fastype env2 rb' h') T0" and bB: "ok (body_type env2 T0) B" and tsol: "tsol (tyenv env2) \<rho>"
      and bs: "bs_env \<rho> e rb'" and tyu: "e \<turnstile> inst \<rho> u' : U" for T0 B \<rho> e U
  proof -
    have T0: "T0 = H" using f0 fh' by simp
    from tyu[unfolded u' inst_apps] obtain Ws where tyh: "e \<turnstile> inst \<rho> h' : Ws \<Rrightarrow> U"
      and tyas: "e \<tturnstile> map (inst \<rho>) args' : Ws" by (rule list_app_typeE)
    have lWs: "length Ws = length uargs + length Es" using typings_nth[OF tyas] by (simp add: args'_def)
    have H: "tsubst \<rho> H = Ws \<Rrightarrow> U" by (rule fastype_sound[OF fh' tsol bs tyh])
    from body_type_binder_types[OF bB refl] obtain Hs where bH: "ok (binder_types env2 T0) Hs" by blast
    from env_fastype_apps_binder_types[OF U1[unfolded fastype_def u] fH te02 bH[unfolded T0]]
    have lH: "length uargs \<le> length Hs" and bU1: "ok (binder_types env2 U1) (drop (length uargs) Hs)"
      by simp_all
    from sp te12 bT1 bU1 have "length Es = length (drop (length uargs) Hs)" unfolding tspine_def by blast
    with lH lWs have lHs: "length (map (tsubst \<rho>) Hs) = length Ws" by simp
    from binder_body_type_sound[OF bH refl bB tsol] H T0
    have "Ws \<Rrightarrow> U = map (tsubst \<rho>) Hs \<Rrightarrow> tsubst \<rho> B" by simp
    with funs_eq[OF lHs[symmetric]] show "U = tsubst \<rho> B" by simp
  qed
  then show ?thesis using nAh' unfolding sh'[symmetric]
    by (subst satd.simps) (auto split: pterm.splits)
qed


lemma mcp_noCU_match_eta: "noCU (match_eta cfg env dp dps B j tail)"
  unfolding match_eta_def match_sat_def
  by (auto intro!: noCU_bindW noCU_handleW noCU_CANTUNIFY_handler noCU_match_pair split: prod.splits pterm.splits)

lemma mcp_okW_det: "okW m x \<Longrightarrow> okW m y \<Longrightarrow> x = y"
  by auto

lemma mcp_okW_bind_ok: "okW m x \<Longrightarrow> okW (bindW m f) y \<longleftrightarrow> okW (f x) y"
  by (auto simp only: okW_bindW dest: mcp_okW_det)

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
    and fr: "fr_shape env dp" and sh: "frs_shape dp" and inv: "scinv \<rho> \<sigma> env (dp # dps) X A"
    and kk: "mcp_kokK k \<rho> (tyenv env) A K"
  shows "\<exists>ms. okW (MATCH cfg env dp dps) ms \<and> (\<exists>x. ev cfg ms x \<and> mcp_mres A K X env \<rho> \<sigma> k x)"
proof -
  obtain rb t u where dp: "dp = (rb, t, u)" by (cases dp)
  from fr dp obtain v T targs where st: "strip_comb t = (Var v T, targs)" by (auto elim: fr_shape_strip_comb)
  let ?\<theta> = "tyenv env" and ?KN = "tvars_env (tyenv env) \<union> A"
  have ei: "einv A K env" and p: "pok A env rb X t u" and ps: "\<forall>(rb', t', u')\<in>set (dp # dps). pok A env rb' X t' u'"
    using si dp by (auto simp: sinv_def)
  note x = einvD[OF ei] and i = scinvD[OF inv] and sd = solutionD[OF scinvD(1)[OF inv]]
  have below_KN: "tbelow (maxidx env) S" if "S \<subseteq> ?KN" for S using tvinv_tbelow[OF i(4) that] .
  from fastype_pair_term[OF ei p] obtain T1 U1 where
    ty: "fastype env rb t = return T1" "fastype env rb u = return U1"
      "tvars T1 \<subseteq> ?KN" "tvars U1 \<subseteq> ?KN" "tnorm ?\<theta> T1 = tnorm ?\<theta> U1" "cert_typ alg ar (tnorm ?\<theta> T1)"
    by blast
  have T1': "ok (fastype env rb t) T1" and U1': "ok (fastype env rb u) U1" using ty(1,2) by (simp_all add: return_def)
  \<comment> \<open>The unification of the types of the sides\<close>
  from i(6) dp obtain e TT where bs: "bs_env \<rho> e rb" and tyt: "e \<turnstile> inst \<rho> t : TT" and tyu: "e \<turnstile> inst \<rho> u : TT"
    by (auto simp: dtyped_def)
  have eq: "tsubst \<rho> T1 = tsubst \<rho> U1"
    using fastype_sound[OF T1' sd(2) bs tyt] fastype_sound[OF U1' sd(2) bs tyu] by simp
  have cU: "cert_typ alg ar (tnorm ?\<theta> U1)" using ty(5,6) by simp
  have wT1: "wft ar T1" by (rule mcp_wft_inst[of "rho0 env"]) (use ty(6) in simp)
  have wU1: "wft ar U1" by (rule mcp_wft_inst[of "rho0 env"]) (use cU in simp)
  from mcp_ncu_cuok[OF sc_cunify_complete[OF inv ps ty(3) wT1 ty(4) wU1 eq] cunify_types_sinv[OF finK si ty(3,6,4) cU]]
  obtain env1 where cu: "okW (cunify_types alg T1 U1 env) env1"
    and c1: "\<exists>\<rho>1. scinv \<rho>1 \<sigma> env1 (dp # dps) X A \<and> tagree (maxidx env) \<rho> \<rho>1 \<and>
      tvars_env ?\<theta> \<subseteq> tvars_env (tyenv env1) \<and> maxidx env \<le> maxidx env1 \<and> tenv env1 = tenv env \<and>
      textends ?\<theta> (tyenv env1)"
    and s1: "sinv A K X env1 (dp # dps) \<and> tenv env1 = tenv env \<and> extends env env1 \<and>
      tvars_env ?\<theta> \<subseteq> tvars_env (tyenv env1) \<and> (\<forall>\<rho>. tsol (tyenv env1) \<rho> \<longrightarrow> tsubst \<rho> T1 = tsubst \<rho> U1)"
    by blast
  from c1 obtain \<rho>1 where inv1: "scinv \<rho>1 \<sigma> env1 (dp # dps) X A" and ag1: "tagree (maxidx env) \<rho> \<rho>1"
    and tve1: "tvars_env ?\<theta> \<subseteq> tvars_env (tyenv env1)" and te1: "tenv env1 = tenv env"
    and tx1: "textends ?\<theta> (tyenv env1)" by blast
  have si1: "sinv A K X env1 (dp # dps)" and ext1: "extends env env1" using s1 by blast+
  have ei1: "einv A K env1" using si1 by (simp add: sinv_def)
  note x1 = einvD[OF ei1] and i1 = scinvD[OF inv1] and sd1 = solutionD[OF scinvD(1)[OF inv1]]
  have mx1: "maxidx env \<le> maxidx env1" using ext1 by (simp add: extends_def)
  have fr1: "fr_shape env1 dp" using fr fr_shape_tenv[OF te1] by simp
  have "mcp_kokK k \<rho>1 (tyenv env1) A (K \<union> {})"
    by (rule mcp_kokK_ext[OF kk tx1 x1(6) x1(7) sd1(2) ag1 below_KN[OF order_refl] x(6) tinv_tcons[OF x1(2)] tve1])
      simp_all
  then have kk1: "mcp_kokK k \<rho>1 (tyenv env1) A K" by simp
  have tvT: "tvars T \<subseteq> ?KN" using head_tvars_strip_comb[OF st] pokD(3)[OF p] by blast
  have tvT1: "tvars T \<subseteq> tvars_env (tyenv env1) \<union> A" using tvT tve1 by blast
  have below1: "tbelow (maxidx env1) S" if "S \<subseteq> tvars_env (tyenv env1) \<union> A" for S
    using tvinv_tbelow[OF i1(4) that] .
  from body_type_term[OF x1(2) refl tvT1] obtain B where bT: "body_type env1 T = return B"
    and tvB: "tvars B \<subseteq> tvars_env (tyenv env1) \<union> A" by blast
  have bT': "ok (body_type env1 T) B" using bT by (simp add: return_def)
  \<comment> \<open>\<^const>\<open>match_sat\<close> in an extension of the type environment\<close>
  have good: "\<exists>s. okW (match_sat cfg envX dp dps) s \<and> (\<exists>x. ev cfg s x \<and> mcp_mres A K X env \<rho> \<sigma> k x)"
    if siX: "sinv AX KX X envX (dp # dps)" and invX: "scinv \<rho>X \<sigma> envX (dp # dps) X AX" and finKX: "finite KX"
      and kkX: "mcp_kokK k \<rho>X (tyenv envX) AX KX" and extX: "extends env1 envX" and teX: "tenv envX = tenv env"
      and bX: "body_type envX T = return BX" and arX: "arity (tsubst \<rho>X BX) = 0"
      and subX: "A \<subseteq> AX" "K \<subseteq> KX" and agX: "tagree (maxidx env) \<rho> \<rho>X"
    for envX \<rho>X AX KX BX
  proof -
    have frX: "fr_shape envX dp" using fr fr_shape_tenv[OF teX] by simp
    have eiX: "einv AX KX envX" using siX by (simp add: sinv_def)
    note r0 = einv_rho0[OF eiX]
    have sat: "satd envX rb' u'"
      if bt: "binder_types envX T = return Ts" and ed: "eta_expand_dpair (drop (length targs) Ts) (rb, t, u) = (rb', t', u')"
      for Ts rb' t' u'
    proof -
      have "sinv AX KX X envX (eta_expand_dpair (drop (length targs) Ts) (rb, t, u) # dps)"
        by (rule sinv_eta_expand(2)[OF siX[unfolded dp] st bt])
      then have p': "pok AX envX rb' X t' u'" using ed by (simp add: sinv_def)
      from pokD(9)[OF p' r0] obtain e0 U0 where e0: "bs_env (rho0 envX) e0 rb'"
        "e0 \<turnstile> inst (rho0 envX) t' : U0" "e0 \<turnstile> inst (rho0 envX) u' : U0" by blast
      have bt': "ok (binder_types envX T) Ts" using bt by (simp add: return_def)
      show ?thesis by (rule mcp_top_satd[OF sh[unfolded dp] T1' U1' cu extX st bt' ed r0(1) e0])
    qed
    have "\<exists>s. okW (match_sat cfg envX (rb, t, u) dps) s \<and> (\<exists>x. ev cfg s x \<and> mcp_mres AX KX X envX \<rho>X \<sigma> k x)"
      by (rule mcp_match_sat_complete[OF cfg k finX finKX siX[unfolded dp] frX[unfolded dp] invX[unfolded dp]
            kkX st bX arX]) (rule sat; assumption)
    then obtain s x where s: "okW (match_sat cfg envX (rb, t, u) dps) s" "ev cfg s x" "mcp_mres AX KX X envX \<rho>X \<sigma> k x"
      by blast
    have "mcp_mres A K X env \<rho> \<sigma> k x"
      by (rule mcp_mres_back[OF s(3) subX extends_trans[OF ext1 extX] agX teX inv scinvD(3)[OF invX]])
    with s(1,2) dp show ?thesis by blast
  qed
  have M: "okW (MATCH cfg env dp dps) ms \<longleftrightarrow> okW (if is_TVar B then foldrW (match_eta cfg env1 dp dps B)
      (arity_guesses cfg B) S_Empty else match_sat cfg env1 dp dps) ms" for ms
  proof -
    have cu': "okW (cunify_types (cfg_alg cfg) T1 U1 env) env1" using cu cfg by simp
    have l1: "okW (liftM (fastype env rb t)) T1" and l2: "okW (liftM (fastype env rb u)) U1"
      and l3: "okW (liftM (body_type env1 T)) B" using T1' U1' bT' by simp_all
    show ?thesis
      by (simp only: MATCH_def dp st prod.case pterm.case mcp_okW_bind_ok[OF l1] mcp_okW_bind_ok[OF l2]
          mcp_okW_bind_ok[OF cu'] mcp_okW_bind_ok[OF l3])
  qed
  show ?thesis
  proof (cases "is_TVar B")
    case False
    have ar0: "arity (tsubst \<rho>1 B) = 0" by (rule mcp_body_type_nonTVar_arity[OF bT' False x1(6)])
    from good[OF si1 inv1 finK kk1 extends_refl te1 bT ar0 order_refl order_refl ag1] False M show ?thesis
      by (simp add: dp)
  next
    case TV: True
    from mcp_body_type_TVar[of env1 T "Ok B" B] bT TV obtain b S where Bb: "B = TVar b S"
      and bn: "vt_lookup (tyenv env1) b = None" by (auto simp: return_def)
    have bS: "(b, S) \<in> tvars_env (tyenv env1) \<union> A" using tvB Bb by simp
    have aokB: "mcp_aok k (tsubst \<rho>1 B)"
      using mcp_kok_unbound[OF mcp_kokK_kok[OF kk1 ei1] bS bn x1(6)] Bb by simp
    define j0 where "j0 = arity (tsubst \<rho>1 B)"
    have j0k: "j0 \<le> k" using mcp_aok_arity[OF aokB] by (simp add: j0_def)
    have j0g: "j0 \<in> set (arity_guesses cfg B)" using TV j0k k by (auto simp: arity_guesses_def)
    \<comment> \<open>The element for the guess \<open>j0\<close>\<close>
    obtain x0 where eta: "\<And>b s. okW (match_eta cfg env1 dp dps B j0 b) s \<Longrightarrow> ev cfg s x0"
      and gd: "mcp_mres A K X env \<rho> \<sigma> k x0"
    proof (cases "j0 = 0")
      case True
      from good[OF si1 inv1 finK kk1 extends_refl te1 bT _ order_refl order_refl ag1] True
      obtain s x where s: "okW (match_sat cfg env1 dp dps) s" "ev cfg s x" "mcp_mres A K X env \<rho> \<sigma> k x"
        by (auto simp: j0_def)
      show ?thesis
      proof (rule that[OF _ s(3)])
        fix b s' assume "okW (match_eta cfg env1 dp dps B j0 b) s'"
        then obtain s1 where o1: "okW (match_sat cfg env1 dp dps) s1" and e1: "s' = S_Append s1 b"
          using True by (auto simp: match_eta_def)
        have "s1 = s" by (rule mcp_okW_det[OF o1 s(1)])
        then show "ev cfg s' x" using e1 s(2) by (simp add: ev.append_l)
      qed
    next
      case False
      obtain Ds R where DR: "tsubst \<rho>1 B = Ds \<Rrightarrow> R" "arity R = 0" "length Ds = j0"
        using mcp_arity_split[of "tsubst \<rho>1 B"] by (auto simp: j0_def)
      obtain env1' Rs where g: "gentvars (Suc j0) env1 = (env1', Rs)" by (cases "gentvars (Suc j0) env1")
      note gs = gentvars_simps[OF g]
      let ?A' = "A \<union> ntv Rs" and ?K' = "K \<union> ntv Rs"
      have lRD: "length (R # Ds) = Suc j0" using DR(3) by simp
      obtain \<rho>1' where r1: "tagree (maxidx env1) \<rho>1 \<rho>1'" "map (tsubst \<rho>1') Rs = R # Ds"
        and inv1': "scinv \<rho>1' \<sigma> env1' (dp # dps) X ?A'" and si1': "sinv ?A' ?K' X env1' (dp # dps)"
        and ext1': "extends env1 env1'"
        by (rule mcp_gentvars_scinv[OF si1 inv1 g lRD])
      obtain R0 Rs' where Rs: "Rs = R0 # Rs'" using gs(4) by (cases Rs) auto
      have \<rho>R0: "tsubst \<rho>1' R0 = R" and \<rho>Rs': "map (tsubst \<rho>1') Rs' = Ds" using r1(2) Rs by simp_all
      have finK': "finite ?K'" using finK by (simp add: ntv_def)
      have ei1': "einv ?A' ?K' env1'" using si1' by (simp add: sinv_def)
      note x1' = einvD[OF ei1'] and i1' = scinvD[OF inv1'] and sd1' = solutionD[OF scinvD(1)[OF inv1']]
      have ps1': "\<forall>(rb', t', u')\<in>set (dp # dps). pok ?A' env1' rb' X t' u'" using si1' by (simp add: sinv_def)
      have tvB': "tvars B \<subseteq> tvars_env (tyenv env1') \<union> ?A'" using tvB gs(2) by auto
      have tvR: "tvars (Rs' \<Rrightarrow> R0) \<subseteq> tvars_env (tyenv env1') \<union> ?A'" using Rs by (auto simp: ntv_def tvars_funs)
      have \<rho>1'B: "tsubst \<rho>1' B = tsubst \<rho>1 B" by (rule tsubst_agree[OF r1(1) below1[OF tvB]])
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
      have mx1': "maxidx env1 \<le> maxidx env1'" by (rule gs(3))
      have ag12: "tagree (maxidx env1) \<rho>1 \<rho>2" by (rule tagree_trans[OF r1(1) ag2 mx1'])
      have ag02: "tagree (maxidx env) \<rho> \<rho>2" by (rule tagree_trans[OF ag1 ag12 mx1])
      have ext12: "extends env1 env2" by (rule extends_trans[OF ext1' ext2])
      have te02: "tenv env2 = tenv env" using te2 gs(1) te1 by simp
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
        by (rule mcp_kokK_ext[OF kk1 _ x1'(6) x1'(7) sd1'(2) r1(1) below1[OF order_refl] x1(6)
              tinv_tcons[OF x1'(2)] _ _ N]) (use gs(2) in auto)
      have "mcp_kokK k \<rho>2 (tyenv env2) ?A' (?K' \<union> {})"
        by (rule mcp_kokK_ext[OF k1' tx2 x2(6) x2(7) sd2(2) ag2 _ x1'(6) tinv_tcons[OF x2(2)] tve2])
          (use tvinv_tbelow[OF i1'(4)] in auto)
      then have kk2: "mcp_kokK k \<rho>2 (tyenv env2) ?A' ?K'" by simp
      \<comment> \<open>The body type in the extended type environment is not instantiated by a function type\<close>
      have tvT2: "tvars T \<subseteq> tvars_env (tyenv env2) \<union> ?A'" using tvT1 gs(2) tve2 by auto
      from body_type_term[OF x2(2) refl tvT2] obtain B2 where bT2: "body_type env2 T = return B2" by blast
      have bT2': "ok (body_type env2 T) B2" using bT2 by (simp add: return_def)
      have ar2: "arity (tsubst \<rho>2 B2) = 0"
      proof -
        let ?\<theta>1 = "tyenv env1" and ?\<theta>2 = "tyenv env2"
        have tx12: "textends ?\<theta>1 ?\<theta>2" using tx2 gs(2) by simp
        note r02 = einv_rho0[OF ei2] and r01 = einv_rho0[OF ei1]
        have a2: "arity (tsubst \<rho>2 T) = arity (tnorm ?\<theta>2 T) + arity (tsubst \<rho>2 B2)"
          by (rule mcp_arity_body[OF bT2' x2(6) sd2(2) r02(1)])
        have a1: "arity (tsubst \<rho>1 T) = arity (tnorm ?\<theta>1 T) + j0"
          using mcp_arity_body[OF bT' x1(6) sd1(2) r01(1)] by (simp add: j0_def)
        have \<rho>T: "tsubst \<rho>2 T = tsubst \<rho>1 T" by (rule tsubst_agree[OF ag12 below1[OF tvT1]])
        from mf_body_type_sound[of env1 T "Ok B" B] bT' x1(6) obtain Zs where
          nf: "\<forall>C D. tnorm ?\<theta>1 B \<noteq> C \<rightarrow>\<^sub>T D" and
          Z: "\<And>\<rho>. tsol ?\<theta>1 \<rho> \<Longrightarrow> tsubst \<rho> T = map (tsubst \<rho>) Zs \<Rrightarrow> tsubst \<rho> B" by auto
        have mz: "map (tsubst (tnorm_inst \<theta>)) Zs = map (tnorm \<theta>) Zs" for \<theta>
          by (induction Zs) (simp_all only: list.map tsubst_tnorm_inst)
        have "tnorm ?\<theta>1 T = map (tnorm ?\<theta>1) Zs \<Rrightarrow> tnorm ?\<theta>1 B"
          using Z[OF r01(1)] by (simp only: mz tsubst_tnorm_inst)
        moreover have "arity (tnorm ?\<theta>1 B) = 0" using nf by (cases "tnorm ?\<theta>1 B" rule: arity.cases) auto
        ultimately have n1: "arity (tnorm ?\<theta>1 T) = length Zs" by (simp add: arity_funs)
        have s02: "tsol ?\<theta>1 (tnorm_inst ?\<theta>2)" by (rule tsol_textends[OF tx12 r02(1)])
        have "tnorm ?\<theta>2 T = map (tnorm ?\<theta>2) Zs \<Rrightarrow> tnorm ?\<theta>2 B"
          using Z[OF s02] by (simp only: mz tsubst_tnorm_inst)
        moreover have "tnorm ?\<theta>2 B = map (tnorm ?\<theta>2) Rs' \<Rrightarrow> tnorm ?\<theta>2 R0"
          using Beq[OF r02(1)] by (simp only: tsubst_tnorm_inst tnorm_funs_mf)
        moreover have lRs': "length Rs' = j0" using \<rho>Rs' DR(3) by (metis length_map)
        ultimately have "length Zs + j0 \<le> arity (tnorm ?\<theta>2 T)" by (simp add: arity_funs)
        then show ?thesis using a1 a2[unfolded \<rho>T] n1 by linarith
      qed
      from good[OF si2 inv2 finK' kk2 ext12 te02 bT2 ar2 _ _ ag02]
      obtain s x where s: "okW (match_sat cfg env2 dp dps) s" "ev cfg s x" "mcp_mres A K X env \<rho> \<sigma> k x"
        by auto
      show ?thesis
      proof (rule that[OF _ s(3)])
        fix b s' assume m: "okW (match_eta cfg env1 dp dps B j0 b) s'"
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
    have "cuok (foldrW (match_eta cfg env1 dp dps B) (arity_guesses cfg B) S_Empty) (\<lambda>s. fin cfg s (mres A))"
      by (rule foldrW_match_eta_fin[OF cfg finX finK si1 fr1 tvB TV])
    moreover have "noCU (foldrW (match_eta cfg env1 dp dps B) (arity_guesses cfg B) S_Empty)"
      by (rule noCU_foldrW[OF mcp_noCU_match_eta])
    ultimately obtain r where r: "okW (foldrW (match_eta cfg env1 dp dps B) (arity_guesses cfg B) S_Empty) r"
      unfolding cuok_def noCU_def by blast
    have "ev cfg r x0" by (rule mcp_foldrW_mem[OF r j0g eta mcp_match_eta_tail])
    with r M TV gd show ?thesis by auto
  qed
qed

end

end

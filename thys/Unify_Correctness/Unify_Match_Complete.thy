section \<open>Completeness of \<open>MATCH\<close>\<close>

theory Unify_Match_Complete
  imports Unify_Simpl_Complete Unify_Match_Fin
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

text \<open>
  The rigid side is saturated: its abstractions have no arguments, and otherwise its type is the
  body type of the type of its head, for every type instantiation (as \<open>satd\<close> of theory
  \<open>Unify_Match_Sound\<close>).
\<close>

function mcp_satd :: "env \<Rightarrow> binders \<Rightarrow> pterm \<Rightarrow> bool" where
  "mcp_satd env rb u =
    (case fst (strip_comb u) of
      Abs a T b \<Rightarrow> snd (strip_comb u) = [] \<and> mcp_satd env ((a, T) # rb) b
    | _ \<Rightarrow> (\<forall>T0 B \<rho> e U. ok (fastype env rb (fst (strip_comb u))) T0 \<longrightarrow> ok (body_type env T0) B \<longrightarrow>
        tsol (tyenv env) \<rho> \<longrightarrow> bs_env \<rho> e rb \<longrightarrow> e \<turnstile> inst \<rho> u : U \<longrightarrow> U = tsubst \<rho> B))"
  by auto
termination
  by (relation "measure (\<lambda>(env, rb, u). size u)") (auto dest: strip_comb_Abs_size)

declare mcp_satd.simps[simp del]

lemma mcp_satd_Abs:
  "fst (strip_comb u) = Abs a T b \<Longrightarrow> mcp_satd env rb u \<Longrightarrow> snd (strip_comb u) = [] \<and> mcp_satd env ((a, T) # rb) b"
  by (subst (asm) mcp_satd.simps) simp

lemma mcp_satd_base:
  "\<not> is_Abs (fst (strip_comb u)) \<Longrightarrow> mcp_satd env rb u \<Longrightarrow> ok (fastype env rb (fst (strip_comb u))) T0 \<Longrightarrow>
    ok (body_type env T0) B \<Longrightarrow> tsol (tyenv env) \<rho> \<Longrightarrow> bs_env \<rho> e rb \<Longrightarrow> e \<turnstile> inst \<rho> u : U \<Longrightarrow>
    U = tsubst \<rho> B"
  by (subst (asm) mcp_satd.simps) (auto split: pterm.splits)

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
    mcp_tok env rb targs u \<and> mcp_satd env rb u"

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
      finite NV \<and> (\<forall>y\<in>NV. maxidx env < snd (fst y)) \<and> ubv env' X' \<subseteq> ubv env X \<union> fst ` NV \<and>
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
    and sat: "mcp_satd env rb u" using pre by (simp_all add: mcp_pre_def)
  show us: "Us = map (tsubst \<rho>) Ts" using mapM_fastype_types[OF mt \<rho> tyt] by simp
  show "U = tsubst \<rho> base" by (rule mcp_satd_base[OF na sat T0 bt \<rho> tyu])
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
  have sat: "mcp_satd env rb u" using pre by (simp add: mcp_pre_def)
  obtain env' newhd where g: "genvar (fst w) env (Ts \<Rrightarrow> base) = (env', newhd)" by fastforce
  have mc: "mc cfg vname rb targs u env dps =
      returnW (S_Single (El_C (combound newhd 0 (length Ts)) env' ((rb, newhd \<degree>\<degree> targs, u) # dps)))"
    by (subst mc.simps) (simp add: Let_def ty0(1-3) ty0(1)[unfolded hd] hd g list_comb_apps)
  have "mcp_cres A K X env rb targs u \<rho> \<sigma> Ss UU s 0
      (El_C (combound newhd 0 (length Ts)) env' ((rb, newhd \<degree>\<degree> targs, u) # dps))"
    by (rule mcp_newvar[where e = e, OF pre _ ty0(3)[unfolded return_def] ty0(6,5) mcp_satd_base[OF na sat ty0(1,2)[unfolded return_def]] g])
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
    and tok: "mcp_tok env rb targs u" and sat: "mcp_satd env rb u"
    unfolding mcp_pre_def by blast+
  from sp have inv: "scinv \<rho> \<sigma> env dps X A" and bs: "bs_env \<rho> e rb"
    and tyt: "e \<tturnstile> map (inst \<rho>) targs : Ss" and tyu: "e \<turnstile> inst \<rho> u : UU" and ar: "arity UU = nabs u"
    and tys: "pushes mcp_e0 Ss \<turnstile> s : UU" and nrs: "no_redex s" and lbs: "\<not> loose_bvar s (ilength Ss)"
    and cv: "types_abs Ss s \<degree>\<degree> map (ap \<rho> \<sigma>) targs \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma> u"
    unfolding mcp_spre_def by blast+
  note i = scinvD[OF inv] and sd = solutionD[OF scinvD(1)[OF inv]]
  from mcp_satd_Abs[OF hd sat] have na: "snd (strip_comb u) = []" and sb: "mcp_satd env ?rb body" by blast+
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
      "finite NV" "\<forall>y\<in>NV. maxidx env < snd (fst y)" "ubv env' X' \<subseteq> ubv env X \<union> fst ` NV"
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
    show "(\<Sum>y\<in>NV. mcp_vsz \<rho>' \<sigma>' y) + m \<le> lsz (pushes mcp_e0 Ss) s - 2 * arity UU" using c2(6) ub by simp
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

end


subsection \<open>Copies: projections\<close>

text \<open>
  The completeness of the copies relies on a property of \<^const>\<open>SIMPL\<close> that is not part of
  its completeness theorem: it binds only variables of the problem and adds no new unbound ones
  (it follows from the reachability lemmas of \<open>Unify_Mc_Fin\<close>, @{text SIMPL_vreach}).
\<close>

locale mcp_hyp = pure_sig +
  assumes mcp_SIMPL_ubv: "\<And>env dps env' ffs frs A K X. okW (SIMPL alg env dps) (env', ffs, frs) \<Longrightarrow>
    finite X \<Longrightarrow> finite K \<Longrightarrow> sinv A K X env dps \<Longrightarrow> ubv env' X \<subseteq> ubv env X"
    and mcp_norm_satd: "\<And>env t u1 rb u2. ok (head_norm env t) u1 \<Longrightarrow> ok (eta_norm env rb u1) u2 \<Longrightarrow>
      mcp_satd env rb u2"
begin

lemma mcp_cresI:
  assumes "x = El_C u' env' dps'" "finite X'" "finite K'" "A \<subseteq> A'" "K \<subseteq> K'" "X \<subseteq> X'"
    "sinv A' K' X' env' dps'" "scinv \<rho>' \<sigma>' env' dps' X' A'" "extends env env'"
    "tvars_env (tyenv env) \<subseteq> tvars_env (tyenv env')" "tagree (maxidx env) \<rho> \<rho>'" "sagree (maxidx env) \<sigma> \<sigma>'"
    "vars u' \<subseteq> X' \<union> evars env'" "ttvars u' \<subseteq> tvars_env (tyenv env') \<union> A'" "\<not> loose_bvar u' (ilength Ss)"
    "\<forall>\<rho>0 e Us U. tsol (tyenv env') \<rho>0 \<longrightarrow> cert_inst \<rho>0 \<longrightarrow> bs_env \<rho>0 e rb \<longrightarrow>
      e \<tturnstile> map (inst \<rho>0) targs : Us \<longrightarrow> e \<turnstile> inst \<rho>0 u : U \<longrightarrow> (\<forall>e'. pushes e' Us \<turnstile> inst \<rho>0 u' : U)"
    "pushes mcp_e0 Ss \<turnstile> inst \<rho>' u' : UU" "types_abs Ss (ap \<rho>' \<sigma>' u') \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> types_abs Ss s"
    "finite NV" "\<forall>y\<in>NV. maxidx env < snd (fst y)" "ubv env' X' \<subseteq> ubv env X \<union> fst ` NV"
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
    "finite NV" "\<forall>y\<in>NV. maxidx env < snd (fst y)" "ubv env' X' \<subseteq> ubv env X \<union> fst ` NV"
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
    "finite NV" "\<forall>y\<in>NV. maxidx env < snd (fst y)" "ubv env' X' \<subseteq> ubv env X \<union> fst ` NV"
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
        mcp_cres A K X env rb targs u \<rho> \<sigma> Ss UU s 1 (El_C (list_comb (Bound j) args) env2 (fr @ ff))))"
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
  \<comment> \<open>The copy for a general type instantiation:\<close>
  have tycopy: "pushes e' (map (tsubst \<rho>') Ts) \<turnstile> inst \<rho>' (Bound j \<degree>\<degree> map (\<lambda>G. G \<degree>\<degree> mbvs (length Ts)) Gs) :
      tsubst \<rho>' base"
    if "tsol (tyenv env') \<rho>'" "\<forall>T\<in>set Ts. cert_typ alg ar (tsubst \<rho>' T)"
      "\<forall>U\<in>set (Us @ Cs). cert_typ alg ar (tsubst \<rho>' U)"
      "list_all2 (\<lambda>G U. \<exists>x. G = Var x (Ts \<Rrightarrow> U)) Gs (Us @ Cs)" for \<rho>' e' Gs
  proof -
    have "tsubst \<rho>' (Ts ! k) = map (tsubst \<rho>') Us \<Rrightarrow> tsubst \<rho>' bary"
      by (rule strip_type_sound[OF st tsol\<theta>[OF that(1)]])
    then have Tk: "tsubst \<rho>' (Ts ! k) = map (tsubst \<rho>') (Us @ Cs) \<Rrightarrow> tsubst \<rho>' base"
      using beq that(1) by (simp add: tsubst_funs)
    have "pushes e' (map (tsubst \<rho>') Ts) j = rev (map (tsubst \<rho>') Ts) ! nat_of_integer j"
      using pushes_nth[OF sB(2)] sB(3) lSs ts\<rho>(5) by (simp add: ilength_eq)
    also have "\<dots> = tsubst \<rho>' (Ts ! k)" using kdef jn ts\<rho>(5) by (simp add: rev_nth)
    finally have tB: "pushes e' (map (tsubst \<rho>') Ts) \<turnstile> Bound j : map (tsubst \<rho>') (Us @ Cs) \<Rrightarrow> tsubst \<rho>' base"
      using Tk sB(2) by auto
    have "pushes e' (map (tsubst \<rho>') Ts) \<tturnstile> map (inst \<rho>') (map (\<lambda>G. G \<degree>\<degree> mbvs (length Ts)) Gs) :
        map (tsubst \<rho>') (Us @ Cs)"
      by (rule mf_typings_new_args[OF that(4) refl that(2,3) refl])
    from list_app_typeI[OF tB this] show ?thesis by (simp add: inst_apps)
  qed
  show ?thesis
  proof (rule exI[of _ p], rule exI[of _ env0], rule exI[of _ Cs], rule exI[of _ env'], intro conjI allI impI)
    show "p \<in> set (arity_guesses cfg bary)" by (rule pg)
    show "gentvars p env = (env0, Cs)" by (rule g)
    show "okW (proj_unify cfg base bary Cs env0) env'" by (rule pu)
    fix env'' args assume ma: "make_args vname Ts env' (Us @ Cs) = (env'', args)"
    have tvTs': "\<forall>T\<in>set Ts. tvars T \<subseteq> tvars_env (tyenv env') \<union> ?A0" using ty0(5) tve0 by blast
    have tvUC: "\<forall>U\<in>set (Us @ Cs). tvars U \<subseteq> tvars_env (tyenv env') \<union> ?A0" using tvUs tvC tve0 by auto
    obtain Gs where args: "args = map (\<lambda>G. G \<degree>\<degree> mbvs (length Ts)) Gs"
      and GU: "list_all2 (\<lambda>G U. \<exists>x. G = Var x (Ts \<Rrightarrow> U)) Gs (Us @ Cs)"
      and ma': "tenv env'' = tenv env'" "tyenv env'' = tyenv env'" "maxidx env' \<le> maxidx env''"
      and Gi: "\<forall>G\<in>set Gs. \<exists>a U. G = Var (a, maxidx env' + 1) U"
      and si'': "sinv ?A0 ?K0 (mlvars Gs \<union> X) env'' dps"
      and vG: "vtvars (mlvars Gs) \<subseteq> tvars_env (tyenv env') \<union> ?A0"
      by (rule sinv_make_args[OF si' ma tvTs' tvUC])
    obtain Gs' where args': "args = map (\<lambda>G. G \<degree>\<degree> mbvs (length Ts)) Gs'"
      and vtr: "\<And>\<rho> X. vinv \<rho> env' X \<Longrightarrow> vinv \<rho> env'' (mlvars Gs' \<union> X)"
      by (rule mf_make_args_props[OF ma]) blast
    have "Gs' = Gs" using args args' by (metis mcp_Gs_unique)
    with vtr have vtr: "\<And>\<rho> X. vinv \<rho> env' X \<Longrightarrow> vinv \<rho> env'' (mlvars Gs \<union> X)" by simp
    have dist: "distinct (map mf_var_of Gs)" by (rule mcp_make_args_distinct[OF ma args])
    let ?q = "length Gs"
    have lq: "?q = length (Us @ Cs)" by (rule list_all2_lengthD[OF GU])
    have lqb: "?q = length bs" using lq gs(4) spl(1) lbs' by (simp add: p_def Ds_def)
    define xs where "xs = map mf_var_of Gs"
    have Gl: "Gs ! l = Var (xs ! l) (Ts \<Rrightarrow> ((Us @ Cs) ! l))" if "l < ?q" for l
    proof -
      from list_all2_nthD[OF GU that] obtain x where "Gs ! l = Var x (Ts \<Rrightarrow> ((Us @ Cs) ! l))" by blast
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
      have "pushes mcp_e0 Ss \<turnstile> bs ! l : Bts ! l" using typings_nth[OF tybs] l by simp
      from mcp_typing_val[OF this] lbs_arg ts\<rho>(3) l show ?thesis using that by (simp add: ws_def ysi_def)
    qed
    have cw: "\<forall>w\<in>set ws. closed w" using lbs_arg by (auto simp: ws_def mcp_closed_types_abs)
    have nys: "\<forall>y\<in>set ysi. maxidx env' < snd (fst y)" using xidx by (auto simp: ysi_def)
    have su: "solution \<rho>2 \<sigma>3 env'" "sagree (maxidx env') \<sigma> \<sigma>3" "wt_subst \<sigma>3"
      unfolding \<sigma>3_def by (rule mcp_solution_supds[OF i2(1) i2(3) nys cw]; blast intro: tyw)+
    have \<sigma>3l: "\<sigma>3 (xs ! l) (Ss \<Rrightarrow> (Bts ! l)) = types_abs Ss (bs ! l)" if "l < ?q" for l
      using mcp_supds_nth[OF dys, of ws l \<sigma>] lys that lqb by (simp add: \<sigma>3_def ysi_def ws_def)
    have \<rho>2Gl: "tsubst \<rho>2 (Ts \<Rrightarrow> ((Us @ Cs) ! l)) = Ss \<Rrightarrow> (Bts ! l)" if "l < ?q" for l
      using \<rho>2Ts \<rho>2UC that lq by (simp add: tsubst_funs flip: nth_map[of l "Us @ Cs" "tsubst \<rho>2"])
    define X'' where "X'' = mlvars Gs \<union> X"
    define dp where "dp = (rb, (targs ! k) \<degree>\<degree> map (\<lambda>G. G \<degree>\<degree> targs) Gs, u)"
    have dpe: "list_comb (targs ! k) (map (\<lambda>arg. list_comb (head_of arg) targs) args) = (targs ! k) \<degree>\<degree> map (\<lambda>G. G \<degree>\<degree> targs) Gs"
    proof -
      have "head_of (G \<degree>\<degree> mbvs (length Ts)) = G" if "G \<in> set Gs" for G
        using Gi that by (auto simp: head_of_apps')
      then show ?thesis by (simp add: args list_comb_apps comp_def cong: map_cong)
    qed
    have ext'': "extends env' env''" by (rule mcp_extends_same[OF ma'])
    have ev'': "evars env'' = evars env" by (rule evars_tenv) (simp add: ma'(1) te0)
    have Gs_eq: "Gs = map (\<lambda>l. Var (xs ! l) (Ts \<Rrightarrow> ((Us @ Cs) ! l))) [0..<?q]"
      by (rule nth_equalityI) (simp_all add: Gl)
    have mlG: "mlvars Gs = set (map (\<lambda>l. (xs ! l, Ts \<Rrightarrow> ((Us @ Cs) ! l))) [0..<?q])"
      by (subst Gs_eq) auto
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
          using c by (auto simp: Gl[OF l] tsubst_funs)
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
      unfolding scinv_def
    proof (intro conjI)
      show "solution \<rho>2 \<sigma>3 env''" by (rule mcp_solution_tenv[OF su(1) ma'(1,2)])
      show "wt_env \<rho>2 env''" using i2(2) wt_env_tenv[OF ma'(1)] by simp
      show "vinv \<rho>2 env'' X''" unfolding X''_def by (rule vtr[OF i2(3)])
      show "tvinv ?A0 env''" using si'' by (simp add: sinv_def einv_def)
      show "vtvars X'' \<subseteq> tvars_env (tyenv env'') \<union> ?A0" using vG i2(5) ma'(2) by (auto simp: X''_def)
      have bs2: "bs_env \<rho>2 e rb" by (rule bs_env_agree[OF bs ag02 below_KN]) (use tv in blast)
      have it: "inst \<rho>2 t = inst \<rho> t" if "t \<in> set targs" for t
        by (rule inst_agree[OF ag02 below_KN]) (use tv that in blast)
      have tyt2: "e \<tturnstile> map (inst \<rho>2) targs : map (tsubst \<rho>2) Ts" using tyt it \<rho>2Ts by (simp cong: map_cong)
      have iu: "inst \<rho>2 u = inst \<rho> u" by (rule inst_agree[OF ag02 below_KN]) (use tv in blast)
      have "e \<turnstile> inst \<rho>2 ((targs ! k) \<degree>\<degree> map (\<lambda>G. G \<degree>\<degree> targs) Gs) : tsubst \<rho>2 base"
        by (rule tydp[OF i2(1)[THEN solutionD(2)] tyt2 cUC2 cTs2])
      moreover have "tsubst \<rho>2 base = UU" using tsubst_agree[OF ag02 below_KN[OF ty0(4)]] ts\<rho>(2) by simp
      ultimately show "dtyped \<rho>2 (dp # dps)"
        using bs2 tyu iu i2(6) lt lu Gi nth_mem[OF kn] by (auto simp: dp_def loose_bvar_apps)
      \<comment> \<open>The new pair is solved:\<close>
      let ?ts = "map (ap \<rho> \<sigma>) targs"
      have vb: "below (maxidx env) (vars t)" if "vars t \<subseteq> X \<union> evars env" for t
        using i(3) that unfolding vinv_def by (meson below_mono order_refl)
      have sa3: "sagree (maxidx env) \<sigma> \<sigma>3" by (rule sagree_trans[OF sagree_refl su(2) mx])
      have apt: "ap \<rho>2 \<sigma>3 t = ap \<rho> \<sigma> t" if "t \<in> set targs" for t
        by (rule ap_agree[OF ag02 sa3 below_KN vb]) (use tv vt that in blast)+
      have apu: "ap \<rho>2 \<sigma>3 u = ap \<rho> \<sigma> u" by (rule ap_agree[OF ag02 sa3 below_KN vb]) (use tv vu in blast)+
      have apG: "ap \<rho>2 \<sigma>3 ((Gs ! l) \<degree>\<degree> targs) = types_abs Ss (bs ! l) \<degree>\<degree> ?ts" if "l < ?q" for l
        using \<sigma>3l[OF that] \<rho>2Gl[OF that] apt by (simp add: Gl[OF that] ap_apps cong: map_cong)
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
      moreover have "dsolved \<rho>2 \<sigma>3 dps"
        by (rule sc_dps_agree(2)[OF _ i2(4) i2(3) tagree_refl su(2) i2(7)]) (use si' in \<open>simp add: sinv_def\<close>)
      ultimately show "dsolved \<rho>2 \<sigma>3 (dp # dps)" by (simp add: dp_def)
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
      have "tsubst \<rho>0 (Ts ! k) = map (tsubst \<rho>0) (Us @ Cs) \<Rrightarrow> tsubst \<rho>0 base"
        using strip_type_sound[OF st tsol\<theta>[OF \<rho>0']] beq \<rho>0' by (simp add: tsubst_funs)
      moreover have "cert_typ alg ar (tsubst \<rho>0 (Ts ! k))" using tt(1,3) kn ts\<rho>(5) by simp
      ultimately have cUC0: "\<forall>U\<in>set (Us @ Cs). cert_typ alg ar (tsubst \<rho>0 U)" by (auto simp: cert_typ_funs)
      have cTs0: "\<forall>T\<in>set Ts. cert_typ alg ar (tsubst \<rho>0 T)" using tt(1,3) by simp
      from tydp[OF \<rho>0' t0(2)[unfolded tt(1)] cUC0 cTs0] tt(2) t0
      show "\<exists>e T. bs_env \<rho>0 e rb \<and> e \<turnstile> inst \<rho>0 ((targs ! k) \<degree>\<degree> map (\<lambda>G. G \<degree>\<degree> targs) Gs) : T \<and> e \<turnstile> inst \<rho>0 u : T"
        by blast
    qed
    have si3: "sinv ?A0 ?K0 X'' env'' (dp # dps)"
      using si'' pdp by (simp add: sinv_def dp_def X''_def)
    have finX'': "finite X''" using finX by (simp add: X''_def)
    have finK0: "finite ?K0" using finK by simp
    \<comment> \<open>Simplification:\<close>
    obtain env2 ffs frs \<rho>4 \<sigma>4 where sm: "okW (SIMPL (cfg_alg cfg) env'' (dp # dps)) (env2, ffs, frs)"
      and spost: "simpl_post ?A0 ?K0 X'' env'' (env2, ffs, frs)" and inv4: "scinv \<rho>4 \<sigma>4 env2 (frs @ ffs) X'' ?A0"
      and ag4: "tagree (maxidx env'') \<rho>2 \<rho>4" and sa4: "sagree (maxidx env'') \<sigma>3 \<sigma>4"
      by (rule mcp_SIMPL[OF cfg finX'' finK0 si3 inv3])
    from spost have si4: "sinv ?A0 ?K0 X'' env2 (frs @ ffs)" and ss4: "sstep ?K0 X'' env'' env2"
      by (simp_all add: simpl_post_def)
    note ss = sstepD[OF ss4]
    have ub4: "ubv env2 X'' \<subseteq> ubv env'' X''" by (rule mcp_SIMPL_ubv[OF sm[unfolded cfg] finX'' finK0 si3])
    note i4 = scinvD[OF inv4]
    have mx'': "maxidx env' \<le> maxidx env''" by (rule ma'(3))
    have ext4: "extends env env2"
      by (rule extends_trans[OF ext0' extends_trans[OF ext'' ss(1)]])
    have ag04: "tagree (maxidx env) \<rho> \<rho>4"
      by (rule tagree_trans[OF ag02 ag4]) (use mx mx'' in simp)
    have sa04: "sagree (maxidx env) \<sigma> \<sigma>4"
    proof -
      have "sagree (maxidx env) \<sigma> \<sigma>3" by (rule sagree_trans[OF sagree_refl su(2) mx])
      then show ?thesis by (rule sagree_trans[OF _ sa4]) (use mx mx'' in simp)
    qed
    have tsol4: "tsol (tyenv env') \<rho>4"
      using extends_tsol[OF solutionD(2)[OF i4(1)] ss(1)] ma'(2) by simp
    have \<rho>4Ts: "map (tsubst \<rho>4) Ts = Ss"
      using \<rho>2Ts tsubst_agree[OF ag4 below''] tvTs' by (simp cong: map_cong)
    have "map (tsubst \<rho>4) (Us @ Cs) = map (tsubst \<rho>2) (Us @ Cs)"
      by (rule map_cong[OF refl]) (use tsubst_agree[OF ag4 below''] tvUC in blast)
    then have \<rho>4UC: "map (tsubst \<rho>4) (Us @ Cs) = Bts" by (subst (asm) \<rho>2UC)
    have cUC4: "\<forall>U\<in>set (Us @ Cs). cert_typ alg ar (tsubst \<rho>4 U)" using \<rho>4UC cBts(1) by (metis image_eqI list.set_map)
    have cTs4: "\<forall>T\<in>set Ts. cert_typ alg ar (tsubst \<rho>4 T)" using \<rho>4Ts ts\<rho>(3) by (metis image_eqI list.set_map)
    have \<rho>4b: "tsubst \<rho>4 base = UU"
      using tsubst_agree[OF ag04 below_KN[OF ty0(4)]] ts\<rho>(2) by simp
    define NV where "NV = mlvars Gs"
    show "\<exists>env2 fr ff. okW (SIMPL (cfg_alg cfg) env''
          ((rb, list_comb (targs ! k) (map (\<lambda>arg. list_comb (head_of arg) targs) args), u) # dps)) (env2, fr, ff) \<and>
        mcp_cres A K X env rb targs u \<rho> \<sigma> Ss UU s 1 (El_C (list_comb (Bound j) args) env2 (fr @ ff))"
    proof (rule exI[of _ env2], rule exI[of _ ffs], rule exI[of _ frs], rule conjI)
      show "okW (SIMPL (cfg_alg cfg) env''
          ((rb, list_comb (targs ! k) (map (\<lambda>arg. list_comb (head_of arg) targs) args), u) # dps)) (env2, ffs, frs)"
        using sm by (simp add: dpe dp_def)
      have lTsS: "length Ts = length Ss" using ts\<rho>(1) by simp
      have u'e: "list_comb (Bound j) args = Bound j \<degree>\<degree> map (\<lambda>G. G \<degree>\<degree> mbvs (length Ts)) Gs"
        by (simp add: args list_comb_apps)
      have i3v: "below (maxidx env'') (X'' \<union> evars env'')" using scinvD(3)[OF inv3] by (simp add: vinv_def)
      have ix: "snd (xs ! l) \<le> maxidx env''" if "l < ?q" for l
      proof -
        have "(xs ! l, Ts \<Rrightarrow> ((Us @ Cs) ! l)) \<in> X''" using mlG that by (auto simp: X''_def)
        then have "snd (fst (xs ! l, Ts \<Rrightarrow> ((Us @ Cs) ! l))) \<le> maxidx env''"
          using i3v unfolding below_def by blast
        then show ?thesis by simp
      qed
      have tvl: "tbelow (maxidx env'') (tvars (Ts \<Rrightarrow> ((Us @ Cs) ! l)))" if "l < ?q" for l
      proof (rule below'')
        have "(Us @ Cs) ! l \<in> set (Us @ Cs)" by (rule nth_mem) (use that lq in simp)
        then show "tvars (Ts \<Rrightarrow> ((Us @ Cs) ! l)) \<subseteq> tvars_env (tyenv env') \<union> ?A0"
          using tvTs' tvUC by (auto simp: tvars_funs)
      qed
      have \<sigma>4l: "\<sigma>4 (xs ! l) (tsubst \<rho>4 (Ts \<Rrightarrow> ((Us @ Cs) ! l))) = types_abs Ss (bs ! l)" if "l < ?q" for l
      proof -
        have "tsubst \<rho>4 (Ts \<Rrightarrow> ((Us @ Cs) ! l)) = tsubst \<rho>2 (Ts \<Rrightarrow> ((Us @ Cs) ! l))"
          by (rule tsubst_agree[OF ag4 tvl[OF that]])
        moreover have "\<sigma>4 (xs ! l) T = \<sigma>3 (xs ! l) T" for T using sa4 ix[OF that] unfolding sagree_def by blast
        ultimately show ?thesis using \<sigma>3l[OF that] \<rho>2Gl[OF that] by simp
      qed
      have apc: "ap \<rho>4 \<sigma>4 (list_comb (Bound j) args) = Bound j \<degree>\<degree> map (\<lambda>b. types_abs Ss b \<degree>\<degree> mbvs (length Ss)) bs"
      proof -
        have "map (ap \<rho>4 \<sigma>4) (map (\<lambda>G. G \<degree>\<degree> mbvs (length Ts)) Gs) = map (\<lambda>b. types_abs Ss b \<degree>\<degree> mbvs (length Ss)) bs"
          by (rule nth_equalityI) (simp_all add: lqb ap_apps Gl \<sigma>4l lTsS comp_def)
        then show ?thesis by (simp add: u'e ap_apps)
      qed
      have tbs: "pushes mcp_e0 Ss \<turnstile> bs ! l : Bts ! l" if "l < length bs" for l
        using typings_nth[OF tybs] that by simp
      have tm: "pushes mcp_e0 Ss \<tturnstile> map (\<lambda>b. types_abs Ss b \<degree>\<degree> mbvs (length Ss)) bs : Bts"
        by (rule mcp_typings_nthI) (use mcp_conv_bvs(2)[OF tbs] lbs_arg ts\<rho>(3) lbs' in auto)
      have cvb: "Bound j \<degree>\<degree> map (\<lambda>b. types_abs Ss b \<degree>\<degree> mbvs (length Ss)) bs \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> s"
      proof -
        show ?thesis unfolding sB(1)
        proof (rule conv_apps[OF _ _ _ conv_refl])
          show "list_all2 (\<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta>) (map (\<lambda>b. types_abs Ss b \<degree>\<degree> mbvs (length Ss)) bs) bs"
            by (rule list_all2_all_nthI) (use mcp_conv_bvs(1)[OF tbs] lbs_arg ts\<rho>(3) in auto)
          show "wt (Bound j \<degree>\<degree> map (\<lambda>b. types_abs Ss b \<degree>\<degree> mbvs (length Ss)) bs)"
            using list_app_typeI[OF tyB tm] by (auto simp: wt_def)
          show "wt (Bound j \<degree>\<degree> bs)" using tys sB(1) by (auto simp: wt_def)
        qed
      qed
      have ub: "ubv env'' X'' \<subseteq> ubv env X \<union> fst ` NV"
        using ev'' ma'(1) te0 by (auto simp: ubv_def X''_def NV_def)
      have vszl: "mcp_vsz \<rho>4 \<sigma>4 (xs ! l, Ts \<Rrightarrow> ((Us @ Cs) ! l)) \<le> lsz (pushes mcp_e0 Ss) (bs ! l)" if "l < ?q" for l
      proof -
        have "mcp_vsz \<rho>4 \<sigma>4 (xs ! l, Ts \<Rrightarrow> ((Us @ Cs) ! l)) = mcp_vsz \<rho>2 \<sigma>3 (xs ! l, Ts \<Rrightarrow> ((Us @ Cs) ! l))"
          by (rule mcp_vsz_agree[OF ag4 sa4 ix[OF that] tvl[OF that]])
        also have "\<dots> = lsz (pushes mcp_e0 Ss) (bs ! l) - 2 * arity (Bts ! l)"
        proof (rule mcp_vsz_val[OF su(3)])
          show "cert_typ alg ar (tsubst \<rho>2 (Ts \<Rrightarrow> ((Us @ Cs) ! l)))"
            using \<rho>2Gl[OF that] ts\<rho>(3) cBts(1) that lq lbs' lqb by (simp add: cert_typ_funs)
          show "\<sigma>3 (xs ! l) (tsubst \<rho>2 (Ts \<Rrightarrow> ((Us @ Cs) ! l))) \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> types_abs Ss (bs ! l)"
            using \<sigma>3l[OF that] \<rho>2Gl[OF that] by simp
          show "tsubst \<rho>2 (Ts \<Rrightarrow> ((Us @ Cs) ! l)) = Ss \<Rrightarrow> (Bts ! l)" by (rule \<rho>2Gl[OF that])
          show "pushes mcp_e0 Ss \<turnstile> bs ! l : Bts ! l" by (rule tbs) (use that lqb in simp)
          show "no_redex (bs ! l)" using nr_arg that lqb by simp
          show "\<forall>S\<in>set Ss. cert_typ alg ar S" by (rule ts\<rho>(3))
        qed
        finally show ?thesis by simp
      qed
      have msum: "(\<Sum>y\<in>NV. mcp_vsz \<rho>4 \<sigma>4 y) + 1 \<le> lsz (pushes mcp_e0 Ss) s - 2 * arity UU"
      proof -
        let ?f = "\<lambda>l. (xs ! l, Ts \<Rrightarrow> ((Us @ Cs) ! l))"
        have "(\<Sum>y\<in>NV. mcp_vsz \<rho>4 \<sigma>4 y) \<le> sum_list (map (mcp_vsz \<rho>4 \<sigma>4) (map ?f [0..<?q]))"
          unfolding NV_def mlG by (rule mcp_sum_set_le_list)
        also have "\<dots> \<le> sum_list (map (\<lambda>l. lsz (pushes mcp_e0 Ss) (bs ! l)) [0..<?q])"
          by (simp only: map_map comp_def) (rule sum_list_mono, use vszl in simp)
        also have "\<dots> = sum_list (map (lsz (pushes mcp_e0 Ss)) bs)"
          unfolding lqb by (rule arg_cong[where f = sum_list], rule nth_equalityI) simp_all
        finally have "(\<Sum>y\<in>NV. mcp_vsz \<rho>4 \<sigma>4 y) \<le> sum_list (map (lsz (pushes mcp_e0 Ss)) bs)" .
        moreover have "lsz (pushes mcp_e0 Ss) s = tsz (spine_type (pushes mcp_e0 Ss) s) + sum_list (map (lsz (pushes mcp_e0 Ss)) bs)"
          unfolding sB(1) by (rule lsz_rigid_apps) simp
        moreover have "0 < tsz (spine_type (pushes mcp_e0 Ss) s)" by (rule tsz_pos)
        ultimately show ?thesis using ar0 by simp
      qed
      show "mcp_cres A K X env rb targs u \<rho> \<sigma> Ss UU s 1 (El_C (list_comb (Bound j) args) env2 (ffs @ frs))"
        unfolding mcp_cres_def
      proof (rule exI[of _ "list_comb (Bound j) args"], rule exI[of _ env2], rule exI[of _ "ffs @ frs"],
          rule exI[of _ ?A0], rule exI[of _ ?K0], rule exI[of _ X''], rule exI[of _ \<rho>4], rule exI[of _ \<sigma>4],
          rule exI[of _ NV], intro conjI)
        show "sinv ?A0 ?K0 X'' env2 (ffs @ frs)" by (rule sinv_mono[OF si4]) auto
        show "scinv \<rho>4 \<sigma>4 env2 (ffs @ frs) X'' ?A0" by (rule scinv_mono[OF inv4]) auto
        show "tvars_env (tyenv env) \<subseteq> tvars_env (tyenv env2)" using tve0 ma'(2) ss(2) by auto
        show "vars (list_comb (Bound j) args) \<subseteq> X'' \<union> evars env2" by (auto simp: u'e vars_apps X''_def)
        have "ttvars (list_comb (Bound j) args) \<subseteq> vtvars (mlvars Gs)"
        proof -
          have "ttvars (G \<degree>\<degree> mbvs (length Ts)) \<subseteq> vtvars (mlvars Gs)" if "G \<in> set Gs" for G
          proof -
            from bspec[OF Gi that] obtain a U where G: "G = Var (a, maxidx env' + 1) U" by blast
            have "((a, maxidx env' + 1), U) \<in> mlvars Gs" using that G by force
            then show ?thesis by (auto simp: G ttvars_apps vtvars_def)
          qed
          then show ?thesis by (auto simp: u'e ttvars_apps)
        qed
        then show "ttvars (list_comb (Bound j) args) \<subseteq> tvars_env (tyenv env2) \<union> ?A0"
          using vG ma'(2) ss(2) by auto
        show "\<not> loose_bvar (list_comb (Bound j) args) (ilength Ss)"
          using new_args_props(1)[OF GU _ args] sB(3) lq lTsS by (auto simp: list_comb_apps loose_bvar_apps ilength_eq)
        show "\<forall>\<rho>0 e Us U. tsol (tyenv env2) \<rho>0 \<longrightarrow> cert_inst \<rho>0 \<longrightarrow> bs_env \<rho>0 e rb \<longrightarrow>
            e \<tturnstile> map (inst \<rho>0) targs : Us \<longrightarrow> e \<turnstile> inst \<rho>0 u : U \<longrightarrow>
            (\<forall>e'. pushes e' Us \<turnstile> inst \<rho>0 (list_comb (Bound j) args) : U)"
        proof (intro allI impI)
          fix \<rho>0 e0 Us0 U0 e' assume a: "tsol (tyenv env2) \<rho>0" "cert_inst \<rho>0" "bs_env \<rho>0 e0 rb"
            "e0 \<tturnstile> map (inst \<rho>0) targs : Us0" "e0 \<turnstile> inst \<rho>0 u : U0"
          have \<rho>0': "tsol (tyenv env') \<rho>0" using extends_tsol[OF a(1) ss(1)] ma'(2) by simp
          note tt = ts[OF tsol\<theta>[OF \<rho>0'] a(3-5)]
          have "tsubst \<rho>0 (Ts ! k) = map (tsubst \<rho>0) (Us @ Cs) \<Rrightarrow> tsubst \<rho>0 base"
            using strip_type_sound[OF st tsol\<theta>[OF \<rho>0']] beq \<rho>0' by (simp add: tsubst_funs)
          moreover have "cert_typ alg ar (tsubst \<rho>0 (Ts ! k))" using tt(1,3) kn ts\<rho>(5) by simp
          ultimately have cUC0: "\<forall>U\<in>set (Us @ Cs). cert_typ alg ar (tsubst \<rho>0 U)" by (auto simp: cert_typ_funs)
          have cTs0: "\<forall>T\<in>set Ts. cert_typ alg ar (tsubst \<rho>0 T)" using tt(1,3) by simp
          from tycopy[OF \<rho>0' cTs0 cUC0 GU, of e'] tt(1,2)
          show "pushes e' Us0 \<turnstile> inst \<rho>0 (list_comb (Bound j) args) : U0" by (simp add: u'e)
        qed
        show "pushes mcp_e0 Ss \<turnstile> inst \<rho>4 (list_comb (Bound j) args) : UU"
          using tycopy[OF tsol4 cTs4 cUC4 GU, of mcp_e0] \<rho>4Ts \<rho>4b by (simp add: u'e)
        show "types_abs Ss (ap \<rho>4 \<sigma>4 (list_comb (Bound j) args)) \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> types_abs Ss s"
        proof (rule mcp_conv_types_abs[OF _ _ cvb[folded apc]])
          have "pushes mcp_e0 Ss \<turnstile> ap \<rho>4 \<sigma>4 (list_comb (Bound j) args) : UU"
            unfolding apc by (rule list_app_typeI[OF tyB tm])
          from mf_typing_types_abs[OF this ts\<rho>(3)]
          show "wt (types_abs Ss (ap \<rho>4 \<sigma>4 (list_comb (Bound j) args)))" by (auto simp: wt_def)
          show "wt (types_abs Ss s)" using mcp_typing_val[OF tys lbs ts\<rho>(3)] by (auto simp: wt_def)
        qed
        show "\<forall>k'. mcp_kokK k' \<rho> (tyenv env) A K \<longrightarrow> mcp_kokK k' \<rho>4 (tyenv env2) ?A0 ?K0"
        proof (intro allI impI)
          fix k' assume kk: "mcp_kokK k' \<rho> (tyenv env) A K"
          have ei': "einv ?A0 ?K0 env'" using si' by (simp add: sinv_def)
          note x' = einvD[OF ei']
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
          have k2: "mcp_kokK k' \<rho>2 (tyenv env') ?A0 (K \<union> ntv Cs)"
            by (rule mcp_kokK_ext[OF kk tx x'(6) x'(7) solutionD(2)[OF i2(1)] ag02 below_KN[OF order_refl] x(6)
                  tinv_tcons[OF x'(2)] tve0 _ N]) auto
          have ei4: "einv ?A0 ?K0 env2" using si4 by (simp add: sinv_def)
          note x4 = einvD[OF ei4]
          have tx4: "textends (tyenv env') (tyenv env2)" using ss(1) ma'(2) by (simp add: extends_def)
          have "mcp_kokK k' \<rho>4 (tyenv env2) ?A0 ((K \<union> ntv Cs) \<union> {})"
            by (rule mcp_kokK_ext[OF k2 tx4 x4(6) x4(7) solutionD(2)[OF i4(1)] ag4 below''[OF order_refl] x'(6)
                  tinv_tcons[OF x4(2)]]) (use ss(2) ma'(2) in auto)
          then show "mcp_kokK k' \<rho>4 (tyenv env2) ?A0 ?K0" by simp
        qed
        show "finite NV" by (simp add: NV_def mlG)
        show "\<forall>y\<in>NV. maxidx env < snd (fst y)" using mx Gi by (fastforce simp: NV_def)
        show "ubv env2 X'' \<subseteq> ubv env X \<union> fst ` NV" using ub4 ub by blast
        show "(\<Sum>y\<in>NV. mcp_vsz \<rho>4 \<sigma>4 y) + 1 \<le> lsz (pushes mcp_e0 Ss) s - 2 * arity UU" by (rule msum)
      qed (use finX'' finK ext4 ag04 sa04 in \<open>auto simp: X''_def\<close>)
    qed
  qed
qed

end

context pure_sig
begin

end

end

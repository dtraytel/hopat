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

text \<open>
  The measure of a problem with the variables \<open>X\<close>: the sum of the sizes of the values of the
  unbound variables of the problem and of the environment.
\<close>

definition mcp_ubv :: "env \<Rightarrow> (indexname \<times> ptyp) set \<Rightarrow> (indexname \<times> ptyp) set" where
  "mcp_ubv env X = {y \<in> X \<union> evars env. vt_lookup (tenv env) (fst y) = None}"

definition mcp_mu :: "tinst \<Rightarrow> vsubst \<Rightarrow> env \<Rightarrow> (indexname \<times> ptyp) set \<Rightarrow> nat" where
  "mcp_mu \<rho> \<sigma> env X = (\<Sum>y\<in>mcp_ubv env X. mcp_vsz \<rho> \<sigma> y)"

lemma finite_mcp_ubv: "finite X \<Longrightarrow> finite (mcp_ubv env X)"
  unfolding mcp_ubv_def using finite_evars by auto

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
      finite NV \<and> (\<forall>y\<in>NV. maxidx env < snd (fst y)) \<and> mcp_ubv env' X' \<subseteq> mcp_ubv env X \<union> NV \<and>
      (\<Sum>y\<in>NV. mcp_vsz \<rho>' \<sigma>' y) + m \<le> lsz (pushes mcp_e0 Ss) s - 2 * arity UU)"

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

lemma mcp_mc_var:
  assumes pre: "mcp_pre A K X env dps rb targs u"
    and sp: "mcp_spre \<rho> \<sigma> env dps X A e rb targs Ss u UU s"
    and hd: "fst (strip_comb u) = Var w W"
  shows "\<exists>sq. okW (mc cfg vname rb targs u env dps) sq \<and>
    (\<exists>x. ev cfg sq x \<and> mcp_cres A K X env rb targs u \<rho> \<sigma> Ss UU s 0 x)"
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
    unfolding mcp_spre_def by blast+
  note i = scinvD[OF inv] and sd = solutionD[OF scinvD(1)[OF inv]]
  have ei: "einv A K env" and wi: "winv env X" and ps: "\<forall>(rb', t', u')\<in>set dps. pok A env rb' X t' u'"
    using si by (auto simp: sinv_def)
  let ?KN = "tvars_env (tyenv env) \<union> A"
  from mcp_mc_types[OF pre] obtain T0 base Ts where
    ty0: "fastype env rb (fst (strip_comb u)) = return T0" "body_type env T0 = return base"
      "mapM (fastype env rb) targs = return Ts" "tvars T0 \<subseteq> ?KN" "tvars base \<subseteq> ?KN" "\<forall>T\<in>set Ts. tvars T \<subseteq> ?KN"
    by blast
  have na: "\<not> is_Abs (fst (strip_comb u))" using hd by simp
  note ts = mcp_types_sound[OF pre ty0(1-3)[unfolded return_def] na]
  note ts\<rho> = ts[OF sd(2) bs tyt tyu]
  obtain env' newhd where g: "genvar (fst w) env (Ts \<Rrightarrow> base) = (env', newhd)" by fastforce
  note gs = genvar_simps[OF g]
  define y where "y = ((fst w, maxidx env + 1), Ts \<Rrightarrow> base)"
  have nh: "newhd = Var (fst y) (snd y)" using gs(4) by (simp add: y_def)
  define u' where "u' = combound newhd 0 (length Ts)"
  define dp where "dp = (rb, newhd \<degree>\<degree> targs, u)"
  have mc: "mc cfg vname rb targs u env dps = returnW (S_Single (El_C u' env' (dp # dps)))"
    by (subst mc.simps) (simp add: Let_def ty0(1-3) ty0(1)[unfolded hd] hd g u'_def dp_def list_comb_apps)
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
  have tvy: "vtvars {y} \<subseteq> ?KN" using ty0(5,6) by (auto simp: vtvars_def y_def tvars_funs)
  have vtX: "vtvars X' \<subseteq> ?KN" using tvy i(5) by (auto simp: X'_def vtvars_def)
  \<comment> \<open>The variables of the old terms are below the index of the new variable:\<close>
  have below_old: "below (maxidx env) (vars t)" if "vars t \<subseteq> X \<union> evars env" for t
    using i(3) that unfolding vinv_def by (meson below_mono order_refl)
  have apu: "ap \<rho> \<sigma>' u = ap \<rho> \<sigma> u" by (rule ap_sagree[OF su(2) below_old[OF vu]])
  have apt: "map (ap \<rho> \<sigma>') targs = map (ap \<rho> \<sigma>) targs"
    using ap_sagree[OF su(2) below_old] vt by auto
  \<comment> \<open>The typings of the new pair:\<close>
  have tyn: "e0 \<turnstile> inst \<rho>0 (newhd \<degree>\<degree> targs) : tsubst \<rho>0 base"
    if "bs_env \<rho>0 e0 rb" "e0 \<tturnstile> map (inst \<rho>0) targs : map (tsubst \<rho>0) Ts" "\<forall>S\<in>set (map (tsubst \<rho>0) Ts). cert_typ alg ar S"
      "cert_typ alg ar (tsubst \<rho>0 base)" for \<rho>0 e0
  proof -
    have "e0 \<turnstile> inst \<rho>0 newhd : map (tsubst \<rho>0) Ts \<Rrightarrow> tsubst \<rho>0 base"
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
  have ub: "mcp_ubv env' X' \<subseteq> mcp_ubv env X \<union> {y}"
    by (auto simp: mcp_ubv_def X'_def ev gs(1))
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
  then show ?thesis using mc by (intro exI[of _ "S_Single (El_C u' env' (dp # dps))"]) (auto intro: ev.single)
qed

subsection \<open>Copies: abstractions\<close>

lemma mcp_pushes_append: "pushes e (Ts @ Us) = pushes (pushes e Ts) Us"
  by (induction Ts arbitrary: e) simp_all

lemma mcp_typings_append: "e \<tturnstile> ts : Ts \<Longrightarrow> e \<tturnstile> us : Us \<Longrightarrow> e \<tturnstile> ts @ us : Ts @ Us"
  by (induction ts arbitrary: Ts) (auto split: list.splits)

lemma mcp_typings_lift:
  "e \<tturnstile> map (inst \<rho>) ts : Us \<Longrightarrow>
    e\<langle>0:A\<rangle> \<tturnstile> map (inst \<rho>) (map (incr_boundvars 1) ts @ [Bound 0]) : Us @ [A]"
proof -
  assume t: "e \<tturnstile> map (inst \<rho>) ts : Us"
  have "e\<langle>0:A\<rangle> \<tturnstile> map (inst \<rho>) (map (incr_boundvars 1) ts) : Us"
    using t by (induction ts arbitrary: Us) (auto split: list.splits simp: incr_boundvars_1)
  then show ?thesis by (intro mcp_typings_append) auto
qed

text \<open>The body of an abstraction, applied to the lifted arguments and the new bound variable:\<close>

lemma mcp_conv_abs_body:
  assumes W: "closed W" "e \<turnstile> W : Ss \<Rrightarrow> (A \<rightarrow>\<^sub>T U1)" and ts: "e \<tturnstile> ts : Ss"
    and eq: "W \<degree>\<degree> ts \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> Abs a A b" and tb: "e\<langle>0:A\<rangle> \<turnstile> b : U1" and cA: "cert_typ alg ar A"
  shows "W \<degree>\<degree> map (\<lambda>t. lift t 0) ts $ Bound 0 \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> b"
proof -
  have l: "W \<degree>\<degree> map (\<lambda>t. lift t 0) ts = lift (W \<degree>\<degree> ts) 0" by (simp add: incr_bv_apps incr_bv_closed W(1))
  have ty1: "e \<turnstile> W \<degree>\<degree> ts : A \<rightarrow>\<^sub>T U1" by (rule list_app_typeI[OF W(2) ts])
  have tyA: "e \<turnstile> Abs a A b : A \<rightarrow>\<^sub>T U1" using tb cA by auto
  have c1: "lift (W \<degree>\<degree> ts) 0 \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> lift (Abs a A b) 0" by (rule conv_lift[OF eq]) simp
  have w1: "e\<langle>0:A\<rangle> \<turnstile> lift (W \<degree>\<degree> ts) 0 $ Bound 0 : U1" using lift_type[OF ty1, of 0 A] by auto
  have w2: "e\<langle>0:A\<rangle> \<turnstile> lift (Abs a A b) 0 $ Bound 0 : U1" using lift_type[OF tyA, of 0 A] by auto
  have c2: "lift (W \<degree>\<degree> ts) 0 $ Bound 0 \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> lift (Abs a A b) 0 $ Bound 0"
    by (rule conv_App[OF _ _ c1 conv_refl]) (use w1 w2 in \<open>auto simp: wt_def\<close>)
  have "lift (Abs a A b) 0 $ Bound 0 \<rightarrow>\<^sub>\<beta> (lift b 1)[Bound 0/0]" by (simp add: beta.beta)
  then have c3: "lift (Abs a A b) 0 $ Bound 0 \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> b"
    using conv_beta[of "lift (Abs a A b) 0 $ Bound 0"] subst_lift_Bound[of 0 b] w2 by (auto simp: wt_def)
  show ?thesis unfolding l using conv_trans[OF c2 c3] .
qed

lemma mcp_conv_eta_body:
  assumes ty: "e \<turnstile> s : A \<rightarrow>\<^sub>T U1" and cA: "cert_typ alg ar A"
  obtains s' where "e\<langle>0:A\<rangle> \<turnstile> s' : U1" "no_redex s'" "lift s 0 $ Bound 0 \<rightarrow>\<^sub>\<beta>\<^sup>* s'"
    "Abs a A s' \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> s" "e \<turnstile> Abs a A s' : A \<rightarrow>\<^sub>T U1"
proof -
  have t1: "e\<langle>0:A\<rangle> \<turnstile> lift s 0 $ Bound 0 : U1" using lift_type[OF ty, of 0 A] by auto
  define s' where "s' = bnorm (lift s 0 $ Bound 0)"
  from bnorm_typed[OF t1] have b: "lift s 0 $ Bound 0 \<rightarrow>\<^sub>\<beta>\<^sup>* s'" "no_redex s'" by (simp_all add: s'_def)
  have t2: "e\<langle>0:A\<rangle> \<turnstile> s' : U1" by (rule subject_reduction_beta'[OF b(1) t1])
  have tA: "e \<turnstile> Abs a A s' : A \<rightarrow>\<^sub>T U1" using t2 cA by auto
  have tA0: "e \<turnstile> Abs a A (lift s 0 $ Bound 0) : A \<rightarrow>\<^sub>T U1" using t1 cA by auto
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
    and IH: "\<And>e' Ss' UU' s'. mcp_pre A K X env dps ((a, T) # rb) (map (incr_boundvars 1) targs @ [Bound 0]) body \<Longrightarrow>
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
  have u: "u = Abs a T body" using strip_comb_apps[of u "fst (strip_comb u)" "snd (strip_comb u)"] hd na by simp
  from mcp_mc_types[OF pre] obtain T0 base Ts where
    ty0: "fastype env rb (fst (strip_comb u)) = return T0" "body_type env T0 = return base"
      "mapM (fastype env rb) targs = return Ts"
    by blast
  \<comment> \<open>The hypotheses for the body:\<close>
  have lts: "\<forall>t\<in>set ?ts. \<not> loose_bvar t (ilength ?rb)"
    using lt by (auto simp: incr_boundvars_1 loose_bvar_lift algebra_simps)
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
  have cS: "\<forall>S\<in>set Ss. cert_typ alg ar S"
  proof -
    from mcp_types_sound[OF pre] obtain Ts' where "map (tsubst \<rho>) Ts = Ss" "\<forall>S\<in>set Ss. cert_typ alg ar S"
      using mapM_fastype_types[OF ty0(3)[unfolded return_def] sd(2) bs tyt] mf_cert_targs[OF bs _ lt] tyt by metis
    then show ?thesis by blast
  qed
  have lbs': "\<not> loose_bvar s' (ilength (Ss @ [?A]))"
  proof
    assume "loose_bvar s' (ilength (Ss @ [?A]))"
    then have "loose_bvar (lift s 0 $ Bound 0) (ilength Ss + 1)"
      using loose_bvar_reds[OF rtranclp_mono[THEN predicate2D, OF _ s'(3)]] by (auto simp: ilength_eq)
    then show False using lbs loose_bvar_lift[of 0 "ilength Ss" s] by (auto simp: ilength_eq)
  qed
  have W: "closed (types_abs Ss s)" "\<And>e'. e' \<turnstile> types_abs Ss s : Ss \<Rrightarrow> UU"
    using mcp_closed_types_abs[OF lbs] mcp_typing_val[OF tys lbs cS] by blast+
  have W': "closed (types_abs (Ss @ [?A]) s')" by (rule mcp_closed_types_abs[OF lbs'])
  have tW': "\<And>e'. e' \<turnstile> types_abs (Ss @ [?A]) s' : (Ss @ [?A]) \<Rrightarrow> UU1"
    by (rule mcp_typing_val) (use s'(1) lbs' cS cT in \<open>simp_all add: mcp_pushes_append\<close>)
  have WW: "types_abs (Ss @ [?A]) s' \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> types_abs Ss s"
    unfolding mcp_types_abs_append
    by (rule mcp_conv_types_abs[OF _ _ s'(4)]) (use tW' W(2) in \<open>auto simp: wt_def mcp_types_abs_append\<close>)
  have tapt: "e \<tturnstile> map (ap \<rho> \<sigma>) targs : Ss"
    using tyt by (induction targs arbitrary: Ss) (auto split: list.splits intro: typing_ap[OF _ sd(3)])
  have cvb: "types_abs (Ss @ [?A]) s' \<degree>\<degree> map (ap \<rho> \<sigma>) ?ts \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma> body"
  proof -
    have m: "map (ap \<rho> \<sigma>) ?ts = map (\<lambda>t. lift t 0) (map (ap \<rho> \<sigma>) targs) @ [Bound 0]"
      by (simp add: incr_boundvars_1 ap_lift[OF sd(3)])
    have c0: "types_abs Ss s \<degree>\<degree> map (ap \<rho> \<sigma>) targs \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> Abs a ?A (ap \<rho> \<sigma> body)" using cv u by simp
    have c1: "types_abs Ss s \<degree>\<degree> map (\<lambda>t. lift t 0) (map (ap \<rho> \<sigma>) targs) $ Bound 0 \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma> body"
      by (rule mcp_conv_abs_body[OF W(1) W(2)[unfolded UU] tapt c0 typing_ap[OF tyb sd(3)] cT])
    have tl: "e\<langle>0:?A\<rangle> \<tturnstile> map (\<lambda>t. lift t 0) (map (ap \<rho> \<sigma>) targs) @ [Bound 0] : Ss @ [?A]"
      using mcp_typings_lift[OF tapt[folded map_ident[of "map (ap \<rho> \<sigma>) targs"]], of TVar ?A]
      by (simp add: incr_boundvars_1 comp_def)
    have w1: "wt (types_abs (Ss @ [?A]) s' \<degree>\<degree> (map (\<lambda>t. lift t 0) (map (ap \<rho> \<sigma>) targs) @ [Bound 0]))"
      using list_app_typeI[OF tW' tl] by (auto simp: wt_def)
    have w2: "wt (types_abs Ss s \<degree>\<degree> (map (\<lambda>t. lift t 0) (map (ap \<rho> \<sigma>) targs) @ [Bound 0]))"
      using list_app_typeI[OF W(2) mf_typings_iff[THEN iffD2, OF list_all2_appendI[OF
          mf_typings_iff[THEN iffD1, OF tl[THEN mf_typings_iff[THEN iffD1], THEN list_all2_appendD, simplified]]]]]
      sorry
    show ?thesis sorry
  qed
  show ?thesis sorry
qed

end

end

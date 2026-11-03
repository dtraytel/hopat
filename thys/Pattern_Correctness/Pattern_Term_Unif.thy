section \<open>Termination of Unification\<close>

theory Pattern_Term_Unif
  imports Pattern_Term_Proj
begin

context pure_sig
begin


subsection \<open>Problems\<close>

text \<open>
  A problem \<open>s =?= t\<close> under the binders \<open>bs\<close> is well-formed for the variables \<open>X\<close> if its
  variables are in \<open>X\<close> or the environment, its type variables are known, its loose bound variables
  are bound by \<open>bs\<close>, and it is well-typed for every certified solution of the type environment.
\<close>

definition pok :: "(indexname \<times> psort) set \<Rightarrow> env \<Rightarrow> binders \<Rightarrow> (indexname \<times> ptyp) set \<Rightarrow> pterm \<Rightarrow> pterm \<Rightarrow> bool" where
  "pok A env bs X s t \<longleftrightarrow> vars s \<union> vars t \<subseteq> X \<union> evars env \<and>
    ttvars s \<union> ttvars t \<union> btvars bs \<union> vtvars X \<subseteq> tvars_env (tyenv env) \<union> A \<and>
    \<not> loose_bvar s (ilength bs) \<and> \<not> loose_bvar t (ilength bs) \<and>
    (\<forall>\<rho>. tsol (tyenv env) \<rho> \<longrightarrow> cert_inst \<rho> \<longrightarrow> (\<exists>e T. bs_env \<rho> e bs \<and> e \<turnstile> inst \<rho> s : T \<and> e \<turnstile> inst \<rho> t : T))"

lemma pokD:
  assumes "pok A env bs X s t"
  shows "vars s \<subseteq> X \<union> evars env" "vars t \<subseteq> X \<union> evars env"
    "ttvars s \<subseteq> tvars_env (tyenv env) \<union> A" "ttvars t \<subseteq> tvars_env (tyenv env) \<union> A"
    "btvars bs \<subseteq> tvars_env (tyenv env) \<union> A" "vtvars X \<subseteq> tvars_env (tyenv env) \<union> A"
    "\<not> loose_bvar s (ilength bs)" "\<not> loose_bvar t (ilength bs)"
    "tsol (tyenv env) \<rho> \<Longrightarrow> cert_inst \<rho> \<Longrightarrow> \<exists>e T. bs_env \<rho> e bs \<and> e \<turnstile> inst \<rho> s : T \<and> e \<turnstile> inst \<rho> t : T"
  using assms unfolding pok_def by blast+

lemma pok_sym: "pok A env bs X s t \<Longrightarrow> pok A env bs X t s"
  unfolding pok_def by blast

lemma vinv_evars: "vars s \<union> vars t \<subseteq> X \<union> evars env \<Longrightarrow> vinv \<rho> env (X \<union> vars s \<union> vars t) \<longleftrightarrow> vinv \<rho> env X"
proof -
  assume "vars s \<union> vars t \<subseteq> X \<union> evars env"
  then have "X \<union> vars s \<union> vars t \<union> evars env = X \<union> evars env" by blast
  then show ?thesis by (simp add: vinv_def)
qed

text \<open>Soundness gives the typing invariant of the results:\<close>

lemma winv_step:
  assumes st: "step_ok env bs s t env'" and wi: "winv env X" and p: "pok A env bs X s t"
  shows "winv env' X"
  unfolding winv_def
proof (intro allI impI)
  fix \<rho> assume \<rho>: "tsol (tyenv env') \<rho>" "cert_inst \<rho>"
  have ext: "extends env env'" by (rule step_okD(1)[OF st])
  have \<rho>0: "tsol (tyenv env) \<rho>" by (rule extends_tsol[OF \<rho>(1) ext])
  obtain e T where ty: "bs_env \<rho> e bs" "e \<turnstile> inst \<rho> s : T" "e \<turnstile> inst \<rho> t : T"
    using pokD(9)[OF p \<rho>0 \<rho>(2)] by blast
  have w: "wt_env \<rho> env" "vinv \<rho> env X" using winvD[OF wi \<rho>0 \<rho>(2)] by blast+
  have "vinv \<rho> env (X \<union> vars s \<union> vars t)" using w(2) vinv_evars[of s t X env \<rho>] pokD(1,2)[OF p] by simp
  from step_okD(2)[OF st \<rho>(1) extends_refl w(1) ty this pokD(7,8)[OF p]]
  show "wt_env \<rho> env' \<and> vinv \<rho> env' X" by blast
qed

subsection \<open>Flex-rigid problems\<close>

lemma flexrigid_term:
  assumes ei: "einv A K env" and wi: "winv env X" and fin: "finite X"
    and vX: "vtvars X \<subseteq> tvars_env (tyenv env) \<union> A"
    and F: "vt_lookup (tenv env) F = None" "(F, Fty) \<in> X \<union> evars env"
    and xs: "\<forall>i\<in>set is. 0 \<le> i \<and> i < ilength bs"
    and vt: "vars t \<subseteq> X \<union> evars env"
    and tv: "ttvars t \<union> btvars bs \<union> tvars Fty \<subseteq> tvars_env (tyenv env) \<union> A"
    and lt: "\<not> loose_bvar t (ilength bs)"
    and ty: "\<And>\<rho>. tsol (tyenv env) \<rho> \<Longrightarrow> cert_inst \<rho> \<Longrightarrow> \<exists>e T. bs_env \<rho> e bs \<and> e \<turnstile> inst \<rho> t : T"
  shows "\<exists>r. flexrigid env bs F Fty is t = Some r \<and>
    (case r of Ok env' \<Rightarrow> einv A K env' \<and> tyenv env' = tyenv env \<and> extends env env' \<and>
        card (ubv env' X) < card (ubv env X)
      | Err e \<Rightarrow> (\<exists>v. e = Unif v) \<or> e = Pattern)"
proof -
  let ?\<theta> = "tyenv env" let ?\<rho> = "tnorm_inst ?\<theta>"
  note e = einvD[OF ei] and r0 = einv_rho0[OF ei]
  have w0: "wt_env ?\<rho> env" "vinv ?\<rho> env X" using winvD[OF wi r0] by blast+
  have vk: "vok env (vars t \<union> evars env)" using vok_winv[OF ei wi vX] vt by (auto intro: vok_mono)
  have occ: "occurs F t env = return (F \<in> fst ` vars (unf env t))" by (rule occurs_ok[OF e(3,6,7) vk])
  obtain e0 T0 where ty0: "bs_env ?\<rho> e0 bs" "e0 \<turnstile> inst ?\<rho> t : T0" using ty[OF r0] by blast
  have vc: "vcons ?\<rho> (vars t \<union> evars env)" using w0(2) vt unfolding vinv_def by (auto intro: vcons_mono)
  have Fb: "snd F \<le> maxidx env" using w0(2) F(2) unfolding vinv_def by (blast dest: belowD)
  show ?thesis
  proof (cases "F \<in> fst ` vars (unf env t)")
    case True
    obtain b' where "rigid_occurs F t env = return b'"
      using rigid_occurs_result[OF e(3,4,6,7) vk termip_unf[OF e(3) w0(1) vc ty0(2)]] by blast
    with occ True show ?thesis by (cases b') (auto simp: flexrigid_def raise_def)
  next
    case False
    have vs: "vars t \<subseteq> X \<union> evars env" by (rule vt)
    have tv': "ttvars t \<union> btvars bs \<subseteq> tvars_env (tyenv env) \<union> A" using tv by blast
    have is0: "\<forall>x\<in>set is. 0 \<le> x" using xs by blast
    obtain r where pj: "proj t env bs is = Some r" and post: "prpost A K env X t r"
      using proj_term[OF ei wi fin vX vt tv' lt ty is0] by blast
    show ?thesis
    proof (cases r)
      case (Err ex)
      with post have ex: "(\<exists>v. ex = Unif v) \<or> ex = Pattern" by (simp add: prpost_def)
      have pjr: "proj t env bs is = raise ex" using pj Err by (simp add: raise_def)
      from ex show ?thesis
      proof
        assume "\<exists>v. ex = Unif v"
        then obtain v where "ex = Unif v" by blast
        then have "flexrigid env bs F Fty is t = raise (Unif (Proj_Fail env bs F is t))"
          by (simp add: flexrigid_def occ False pjr)
        then show ?thesis by (simp add: raise_def)
      next
        assume "ex = Pattern"
        then have "flexrigid env bs F Fty is t = raise Pattern" by (simp add: flexrigid_def occ False pjr)
        then show ?thesis by (simp add: raise_def)
      qed
    next
      case (Ok p)
      obtain u env1 where p: "p = (u, env1)" by force
      have pp: "einv A K env1 \<and> winv env1 X \<and> tyenv env1 = tyenv env \<and> extends env env1 \<and>
        prunes env env1 X \<and> card (ubv env1 X) \<le> card (ubv env X) \<and> newb env env1 \<and>
        (\<forall>x b. vt_lookup (tenv env1) x = Some b \<longrightarrow> vt_lookup (tenv env) x = None \<longrightarrow>
           x \<in> fst ` vars (unf env t) \<union> {y. maxidx env < snd y}) \<and>
        fst ` vars (unf env1 u) \<subseteq> fst ` vars (unf env t) \<union> {y. maxidx env < snd y} \<and>
        ttvars u \<subseteq> tvars_env (tyenv env) \<union> A \<and> vars u \<subseteq> X \<union> evars env1"
        using post[unfolded Ok p] unfolding prpost_def res.case prod.case .
      then have p1: "einv A K env1" "tyenv env1 = tyenv env" "extends env env1"
        "card (ubv env1 X) \<le> card (ubv env X)"
        "\<And>x b. vt_lookup (tenv env1) x = Some b \<Longrightarrow> vt_lookup (tenv env) x = None \<Longrightarrow>
           x \<in> fst ` vars (unf env t) \<union> {y. maxidx env < snd y}"
        "fst ` vars (unf env1 u) \<subseteq> fst ` vars (unf env t) \<union> {y. maxidx env < snd y}"
        "ttvars u \<subseteq> tvars_env (tyenv env) \<union> A" "vars u \<subseteq> X \<union> evars env1"
        by blast+
      have pj': "ok (proj t env bs is) (u, env1)" using pj Ok p by simp
      have t1: "tsol (tyenv env1) ?\<rho>" using r0(1) p1(2) by simp
      have vi0: "vinv ?\<rho> env (X \<union> vars t)" using w0(2) vinv_evars[of t t X env ?\<rho>] vt by simp
      have lu: "\<not> loose_bvar u (ilength is)"
        using proj_sound(2)[OF pj' is0 t1 extends_refl w0(1) ty0 vi0 lt] by blast
      have F1: "vt_lookup (tenv env1) F = None"
      proof (rule ccontr)
        assume "vt_lookup (tenv env1) F \<noteq> None"
        then obtain b where "vt_lookup (tenv env1) F = Some b" by blast
        from p1(5)[OF this F(1)] False Fb show False by auto
      qed
      let ?u = "abs_list (map (\<lambda>i. bs ! nat_of_integer i) is) u"
      have mk: "mkabs bs is u = return ?u" by (rule mkabs_ok[OF xs])
      obtain env' where upd: "update (F, Fty) ?u env1 = return env'" using update_ok[OF F1] by blast
      note upd' = upd[unfolded return_def]
      have nr: "F \<notin> fst ` vars (unf env1 u)" using p1(6) False Fb by auto
      have ei': "einv A K env'"
      proof (rule einv_update[OF p1(1) upd'])
        fix y U assume yU: "(y, U) \<in> vars ?u"
        show "(F, y) \<notin> (dep env1)\<^sup>*"
        proof
          assume "(F, y) \<in> (dep env1)\<^sup>*"
          then have "F \<in> fst ` vars (unf env1 (Var y U))"
            using vars_unf_Var[OF einvD(3)[OF p1(1)], of y U] F1 by blast
          moreover have "vars (unf env1 (Var y U)) \<subseteq> vars (unf env1 u)"
            using yU vars_unf[of env1 u] by auto
          ultimately show False using nr by blast
        qed
      next
        show "closed ?u" by (rule closed_abs_list) (use lu in \<open>simp add: ilength_eq\<close>)
      next
        show "snd F \<le> maxidx env1" using Fb p1(3) by (auto simp: extends_def)
      next
        have "btvars (map (\<lambda>i. bs ! nat_of_integer i) is) \<subseteq> btvars bs" by (rule btvars_nths[OF xs])
        then show "tvars Fty \<union> ttvars ?u \<subseteq> tvars_env (tyenv env1) \<union> A"
          using tv p1(2,7) by (auto simp: ttvars_abs_list)
      qed
      have Fin: "F \<in> fst ` (X \<union> evars env1)" using F(2) evars_extends[OF p1(3)] by (metis fst_conv image_eqI subsetD Un_mono order_refl)
      have "card (ubv env' X) < card (ubv env1 X)"
        by (rule card_ubv_update(1)[OF fin upd' Fin]) (use p1(8) in simp)
      with p1(4) have card: "card (ubv env' X) < card (ubv env X)" by simp
      have pjr: "proj t env bs is = return (u, env1)" using pj' by (simp add: return_def)
      have "flexrigid env bs F Fty is t = return env'"
        by (simp add: flexrigid_def occ False pjr mk upd)
      with ei' card p1(2,3) ok_update(3)[OF upd'] extends_update[OF upd'] show ?thesis
        by (auto simp: return_def intro: extends_trans)
    qed
  qed
qed

subsection \<open>The measure and the result of unification\<close>

definition umeas :: "(indexname \<times> psort) set \<Rightarrow> env \<Rightarrow> (indexname \<times> ptyp) set \<Rightarrow> pterm list \<Rightarrow> nat \<times> nat \<times> nat" where
  "umeas K env X ts = (card (uvarsA (tyenv env) K), card (ubv env X), sum_list (map (M (tnorm_inst (tyenv env)) env) ts))"

abbreviation ulex :: "((nat \<times> nat \<times> nat) \<times> (nat \<times> nat \<times> nat)) set" where
  "ulex \<equiv> less_than <*lex*> less_than <*lex*> less_than"

definition upost :: "(indexname \<times> psort) set \<Rightarrow> (indexname \<times> psort) set \<Rightarrow> env \<Rightarrow> (indexname \<times> ptyp) set \<Rightarrow>
    env res \<Rightarrow> bool" where
  "upost A K env X r \<longleftrightarrow> (case r of
      Ok env' \<Rightarrow> einv A K env' \<and> winv env' X \<and> extends env env' \<and>
        tvars_env (tyenv env) \<subseteq> tvars_env (tyenv env') \<and>
        (tyenv env' = tyenv env \<longrightarrow> card (ubv env' X) < card (ubv env X) \<or>
           (card (ubv env' X) \<le> card (ubv env X) \<and> prunes env env' X)) \<and>
        (tyenv env' \<noteq> tyenv env \<longrightarrow> card (uvarsA (tyenv env') K) < card (uvarsA (tyenv env) K))
    | Err e \<Rightarrow> (\<exists>v. e = Unif v) \<or> e = Pattern)"

lemma vt_eqI: "(\<And>k. vt_lookup t k = vt_lookup t' k) \<Longrightarrow> t = t'"
  by transfer auto

lemma textends_antisym: "textends \<theta> \<theta>' \<Longrightarrow> textends \<theta>' \<theta> \<Longrightarrow> \<theta>' = \<theta>"
  unfolding textends_def by (rule vt_eqI) (metis not_None_eq)

lemma upost_Err [simp]: "upost A K env X (Err e) \<longleftrightarrow> (\<exists>v. e = Unif v) \<or> e = Pattern"
  by (simp add: upost_def)

lemma upost_OkD:
  assumes "upost A K env X (Ok env')"
  shows "einv A K env'" "winv env' X" "extends env env'" "tvars_env (tyenv env) \<subseteq> tvars_env (tyenv env')"
    "tyenv env' = tyenv env \<Longrightarrow> card (ubv env' X) < card (ubv env X) \<or>
       (card (ubv env' X) \<le> card (ubv env X) \<and> prunes env env' X)"
    "tyenv env' \<noteq> tyenv env \<Longrightarrow> card (uvarsA (tyenv env') K) < card (uvarsA (tyenv env) K)"
  using assms by (simp_all add: upost_def)

lemma upost_trans:
  assumes 1: "upost A K env X (Ok env1)" and 2: "upost A K env1 X r"
  shows "upost A K env X r"
proof (cases r)
  case (Err e)
  with 2 show ?thesis by simp
next
  case (Ok env2)
  note a = upost_OkD[OF 1] and b = upost_OkD[OF 2[unfolded Ok]]
  have ext: "extends env env2" by (rule extends_trans[OF a(3) b(3)])
  have te1: "textends (tyenv env) (tyenv env1)" and te2: "textends (tyenv env1) (tyenv env2)"
    using a(3) b(3) by (simp_all add: extends_def)
  have same: "tyenv env2 = tyenv env \<Longrightarrow> tyenv env1 = tyenv env"
    using te1 te2 textends_antisym by metis
  have c: "tyenv env2 = tyenv env \<longrightarrow> card (ubv env2 X) < card (ubv env X) \<or>
      (card (ubv env2 X) \<le> card (ubv env X) \<and> prunes env env2 X)"
  proof
    assume e2: "tyenv env2 = tyenv env"
    with same have e1: "tyenv env1 = tyenv env" by blast
    with e2 have e21: "tyenv env2 = tyenv env1" by simp
    from a(5)[OF e1] b(5)[OF e21] show "card (ubv env2 X) < card (ubv env X) \<or>
      (card (ubv env2 X) \<le> card (ubv env X) \<and> prunes env env2 X)"
      using prunes_trans[OF _ _ b(3) a(3)] by fastforce
  qed
  have d: "tyenv env2 \<noteq> tyenv env \<longrightarrow> card (uvarsA (tyenv env2) K) < card (uvarsA (tyenv env) K)"
  proof
    assume "tyenv env2 \<noteq> tyenv env"
    then consider "tyenv env1 \<noteq> tyenv env" | "tyenv env1 = tyenv env" "tyenv env2 \<noteq> tyenv env1"
      by (cases "tyenv env1 = tyenv env") auto
    then show "card (uvarsA (tyenv env2) K) < card (uvarsA (tyenv env) K)"
    proof cases
      case 1
      with a(6) b(6) show ?thesis by (cases "tyenv env2 = tyenv env1") auto
    next
      case 2
      with b(6) show ?thesis by simp
    qed
  qed
  show ?thesis using Ok b(1,2) ext a(4) b(4) c d by (auto simp: upost_def)
qed

lemma ulex_trans: "(a, b) \<in> ulex \<Longrightarrow> (b, c) \<in> ulex \<Longrightarrow> (a, c) \<in> ulex"
  by (rule transD[OF trans_lex_prod[OF trans_less_than trans_lex_prod[OF trans_less_than trans_less_than]]])

subsection \<open>Head normalization of problems\<close>

lemma etvars_known: "tvinv A env \<Longrightarrow> etvars env \<subseteq> tvars_env (tyenv env) \<union> A"
  unfolding etvars_def bnds_def using tvinvD(2) by fastforce

lemma typing_unf0:
  assumes "einv A K env" "winv env X" "vars t \<subseteq> X \<union> evars env"
    and "e \<turnstile> inst (tnorm_inst (tyenv env)) t : T"
  shows "e \<turnstile> inst (tnorm_inst (tyenv env)) (unf env t) : T"
proof -
  note r0 = einv_rho0[OF assms(1)]
  have w: "wt_env (tnorm_inst (tyenv env)) env" "vinv (tnorm_inst (tyenv env)) env X"
    using winvD[OF assms(2) r0] by blast+
  have "vcons (tnorm_inst (tyenv env)) (vars t \<union> evars env)"
    using w(2) assms(3) unfolding vinv_def by (auto intro: vcons_mono)
  then show ?thesis by (rule typing_unf[OF einvD(3)[OF assms(1)] w(1) _ assms(4)])
qed

lemma termip_unf0:
  assumes "einv A K env" "winv env X" "vars t \<subseteq> X \<union> evars env"
    and "e \<turnstile> inst (tnorm_inst (tyenv env)) t : T"
  shows "termip (sup beta subt) (unf env t)"
  using termip_inst[OF type_implies_termi[OF typing_unf0[OF assms]] refl] by (rule termip_beta_subt)

lemma hn_term:
  assumes ei: "einv A K env" and wi: "winv env X" and p: "pok A env bs X s t"
  shows "\<exists>s' t'. head_norm env s = return s' \<and> head_norm env t = return t' \<and> pok A env bs X s' t' \<and>
    umeas K env X [s', t'] = umeas K env X [s, t]"
proof -
  let ?\<rho> = "tnorm_inst (tyenv env)"
  note e = einvD[OF ei] and r0 = einv_rho0[OF ei] and pd = pokD[OF p]
  have vk: "vok env (X \<union> evars env)" by (rule vok_winv[OF ei wi pd(6)])
  obtain e0 T0 where ty0: "bs_env ?\<rho> e0 bs" "e0 \<turnstile> inst ?\<rho> s : T0" "e0 \<turnstile> inst ?\<rho> t : T0"
    using pd(9)[OF r0] by blast
  have hn: "\<exists>u'. head_norm env u = return u'" if "vars u \<subseteq> X \<union> evars env" "e0 \<turnstile> inst ?\<rho> u : T0" for u
  proof (rule head_norm_term[OF e(3,4,6,7)])
    show "vok env (vars u \<union> evars env)" using vk that(1) by (auto intro: vok_mono)
    show "termip (sup beta subt) (unf env u)" by (rule termip_unf0[OF ei wi that])
  qed
  obtain s' t' where s': "head_norm env s = return s'" and t': "head_norm env t = return t'"
    using hn[OF pd(1) ty0(2)] hn[OF pd(2) ty0(3)] by blast
  note s'' = s'[unfolded return_def] and t'' = t'[unfolded return_def]
  have w0: "wt_env ?\<rho> env" using winvD[OF wi r0] by blast
  have "pok A env bs X s' t'"
    unfolding pok_def
  proof (intro conjI allI impI)
    show "vars s' \<union> vars t' \<subseteq> X \<union> evars env"
      using head_norm_vars[OF s'' refl] head_norm_vars[OF t'' refl] pd(1,2) by blast
    show "ttvars s' \<union> ttvars t' \<union> btvars bs \<union> vtvars X \<subseteq> tvars_env (tyenv env) \<union> A"
      using head_norm_ttvars[OF s'' refl] head_norm_ttvars[OF t'' refl] pd(3-6) etvars_known[OF e(1)] by blast
    show "\<not> loose_bvar s' (ilength bs)" by (rule head_norm_loose[OF s'' refl w0 ilength_nonneg pd(7)])
    show "\<not> loose_bvar t' (ilength bs)" by (rule head_norm_loose[OF t'' refl w0 ilength_nonneg pd(8)])
    fix \<rho> assume \<rho>: "tsol (tyenv env) \<rho>" "cert_inst \<rho>"
    obtain e T where ty: "bs_env \<rho> e bs" "e \<turnstile> inst \<rho> s : T" "e \<turnstile> inst \<rho> t : T" using pd(9)[OF \<rho>] by blast
    have wr: "wt_env \<rho> env" using winvD[OF wi \<rho>] by blast
    show "\<exists>e T. bs_env \<rho> e bs \<and> e \<turnstile> inst \<rho> s' : T \<and> e \<turnstile> inst \<rho> t' : T"
      using ty head_norm_sound[OF s'' refl \<rho>(1) wr ty(2)] head_norm_sound[OF t'' refl \<rho>(1) wr ty(3)] by blast
  qed
  moreover have "M ?\<rho> env s' = M ?\<rho> env s"
    by (rule M_head_norm[OF s'' e(3,4) typing_unf0[OF ei wi pd(1) ty0(2)]])
  moreover have "M ?\<rho> env t' = M ?\<rho> env t"
    by (rule M_head_norm[OF t'' e(3,4) typing_unf0[OF ei wi pd(2) ty0(3)]])
  ultimately show ?thesis using s' t' by (auto simp: umeas_def)
qed

subsection \<open>Auxiliary facts for the cases of unification\<close>

lemma winv_tyext:
  assumes "winv env X" "tenv env1 = tenv env" "textends (tyenv env) (tyenv env1)" "maxidx env \<le> maxidx env1"
  shows "winv env1 X"
  unfolding winv_def
proof (intro allI impI)
  fix \<rho> assume \<rho>: "tsol (tyenv env1) \<rho>" "cert_inst \<rho>"
  have "tsol (tyenv env) \<rho>" by (rule tsol_textends[OF assms(3) \<rho>(1)])
  from winvD[OF assms(1) this \<rho>(2)] have "wt_env \<rho> env" "vinv \<rho> env X" by blast+
  moreover have "evars env1 = evars env" using assms(2) by (simp add: evars_def bnds_def)
  ultimately show "wt_env \<rho> env1 \<and> vinv \<rho> env1 X"
    using assms(2,4) unfolding wt_env_def vinv_def by (auto intro: below_mono)
qed

lemma pok_mono:
  assumes "pok A env bs X s t" "extends env env1" "tvars_env (tyenv env) \<subseteq> tvars_env (tyenv env1)"
  shows "pok A env1 bs X s t"
  unfolding pok_def
proof (intro conjI allI impI)
  note pd = pokD[OF assms(1)]
  show "vars s \<union> vars t \<subseteq> X \<union> evars env1" using pd(1,2) evars_extends[OF assms(2)] by blast
  show "ttvars s \<union> ttvars t \<union> btvars bs \<union> vtvars X \<subseteq> tvars_env (tyenv env1) \<union> A"
    using pd(3-6) assms(3) by blast
  show "\<not> loose_bvar s (ilength bs)" "\<not> loose_bvar t (ilength bs)" by (rule pd(7), rule pd(8))
  fix \<rho> assume "tsol (tyenv env1) \<rho>" "cert_inst \<rho>"
  then show "\<exists>e T. bs_env \<rho> e bs \<and> e \<turnstile> inst \<rho> s : T \<and> e \<turnstile> inst \<rho> t : T"
    using pd(9) extends_tsol[OF _ assms(2)] by blast
qed

lemma upost_refl: "einv A K env \<Longrightarrow> winv env X \<Longrightarrow> upost A K env X (Ok env)"
  by (simp add: upost_def prunes_same)

lemma upost_tyext:
  assumes "einv A K env1" "winv env X" "tenv env1 = tenv env" "textends (tyenv env) (tyenv env1)"
    "maxidx env \<le> maxidx env1" "tvars_env (tyenv env) \<subseteq> tvars_env (tyenv env1)"
    "tyenv env1 = tyenv env \<or> card (uvarsA (tyenv env1) K) < card (uvarsA (tyenv env) K)"
  shows "upost A K env X (Ok env1)"
proof -
  have "extends env env1" using assms(3-5) by (simp add: extends_def)
  moreover have "ubv env1 X = ubv env X" using assms(3) by (simp add: ubv_def evars_def bnds_def)
  ultimately show ?thesis using assms winv_tyext[OF assms(2-5)] prunes_same[OF assms(3)]
    by (auto simp: upost_def)
qed

lemma cert_typ_tsubst_rev:
  assumes "cert_typ alg ar (tsubst \<rho> T)" "tcert alg (tvars T)"
  shows "wft ar T" "sorts_ok alg T"
proof -
  have "wft ar (tsubst \<rho> T) \<Longrightarrow> wft ar T" by (induction T) auto
  then show "wft ar T" using assms(1) by (simp add: cert_typ_def)
  have "sorts_ok alg (tsubst \<rho> T) \<Longrightarrow> tcert alg (tvars T) \<Longrightarrow> sorts_ok alg T"
  proof (induction T)
    case (Type a Ts)
    then show ?case by (auto simp: tcert_def)
  qed (auto simp: tcert_def)
  then show "sorts_ok alg T" using assms by (simp add: cert_typ_def)
qed


subsection \<open>The cases of unification\<close>

text \<open>The cases assume the induction hypothesis for problems of smaller measure than \<open>B\<close>.\<close>

lemma M_tenv: "tenv env1 = tenv env \<Longrightarrow> M \<rho> env1 = M \<rho> env"
proof -
  assume "tenv env1 = tenv env"
  from unf_tenv[OF this] show ?thesis by (simp only: M_def[abs_def])
qed

lemma ubv_tenv: "tenv env1 = tenv env \<Longrightarrow> ubv env1 X = ubv env X"
  by (simp add: ubv_def evars_def bnds_def)

lemma ulex_iff: "((a, b, c), (a', b', c')) \<in> ulex \<longleftrightarrow> a < a' \<or> a = a' \<and> (b < b' \<or> b = b' \<and> c < c')"
  by simp

lemma lift_rigid: "rigid h \<Longrightarrow> rigid (lift h k)"
  by (cases h) simp_all

lemma M_eta:
  assumes ac: "acyc env" and cl: "closed_env env"
    and h: "rigid h \<or> (\<exists>F T. h = Var F T \<and> vt_lookup (tenv env) F = None)"
    and ty: "e \<turnstile> inst \<rho> (unf env (h \<degree>\<degree> us)) : V"
    and ty': "e' \<turnstile> inst \<rho> (unf env (incr (h \<degree>\<degree> us) $ Bound 0)) : V'"
  shows "M \<rho> env (incr (h \<degree>\<degree> us) $ Bound 0) \<le> M \<rho> env (h \<degree>\<degree> us) + 1"
proof -
  have i: "incr (h \<degree>\<degree> us) $ Bound 0 = lift h 0 \<degree>\<degree> (map (\<lambda>u. lift u 0) us @ [Bound 0])"
    by (simp add: incr_def incr_aux_lift)
  from h show ?thesis
  proof
    assume r: "rigid h"
    have targ: "\<exists>U. e \<turnstile> inst \<rho> (unf env u) : U" if "u \<in> set us" for u
    proof -
      have "inst \<rho> (unf env (h \<degree>\<degree> us)) = inst \<rho> (unf env h) \<degree>\<degree> map (\<lambda>u. inst \<rho> (unf env u)) us"
        by (simp add: unf_apps inst_apps comp_def)
      with typing_args[of e _ "map (\<lambda>u. inst \<rho> (unf env u)) us" V] ty that show ?thesis by auto
    qed
    have "M \<rho> env (lift u 0) = M \<rho> env u" if "u \<in> set us" for u
      using targ[OF that] M_lift[OF ac cl, of 0] by fastforce
    then have ml: "map (M \<rho> env) (map (\<lambda>u. lift u 0) us) = map (M \<rho> env) us" by simp
    have b0: "M \<rho> env (Bound 0) = 1"
      using M_rigid[of "Bound 0" e' \<rho> env "[]"] typing_args[OF ty'[unfolded i unf_apps inst_apps]] by auto
    have sl: "sum_list (map (M \<rho> env) (map (\<lambda>u. lift u 0) us @ [Bound 0])) = sum_list (map (M \<rho> env) us) + 1"
      by (simp only: map_append sum_list_append ml) (simp add: b0)
    have "M \<rho> env (incr (h \<degree>\<degree> us) $ Bound 0) =
        1 + sum_list (map (M \<rho> env) (map (\<lambda>u. lift u 0) us @ [Bound 0]))"
      unfolding i by (rule M_rigid[OF lift_rigid[OF r] ty'[unfolded i]])
    moreover have "M \<rho> env (h \<degree>\<degree> us) = 1 + sum_list (map (M \<rho> env) us)" by (rule M_rigid[OF r ty])
    ultimately show ?thesis by (simp only: sl)
  next
    assume "\<exists>F T. h = Var F T \<and> vt_lookup (tenv env) F = None"
    then obtain F T where hF: "h = Var F T" "vt_lookup (tenv env) F = None" by blast
    have i': "incr (h \<degree>\<degree> us) $ Bound 0 = Var F T \<degree>\<degree> (map (\<lambda>u. lift u 0) us @ [Bound 0])"
      using i hF by simp
    have "M \<rho> env (incr (h \<degree>\<degree> us) $ Bound 0) = 2 * (arity (tsubst \<rho> T) - Suc (length us)) + 1"
      unfolding i' using M_flex[OF ac hF(2) ty'[unfolded i']] by simp
    moreover have "M \<rho> env (h \<degree>\<degree> us) = 2 * (arity (tsubst \<rho> T) - length us) + 1"
      using M_flex[OF ac hF(2) ty[unfolded hF(1)]] hF(1) by simp
    ultimately show ?thesis by simp
  qed
qed

lemma strip_comb_head_cases:
  assumes "\<not> is_Abs h" "\<not> (\<exists>f u. h = f $ u)"
  shows "rigid h \<or> (\<exists>F T. h = Var F T)"
  using assms by (cases h) simp_all


context
  fixes A K X B
  assumes IH: "\<And>env1 bs1 s1 t1. (umeas K env1 X [s1, t1], B) \<in> ulex \<Longrightarrow> einv A K env1 \<Longrightarrow> winv env1 X \<Longrightarrow>
    pok A env1 bs1 X s1 t1 \<Longrightarrow> \<exists>r. unif alg bs1 s1 t1 env1 = Some r \<and> upost A K env1 X r"
    and finX: "finite X" and finK: "finite K"
begin

lemma case_abs_abs:
  assumes ei: "einv A K env" and wi: "winv env X" and p: "pok A env bs X (Abs ns Ts ts) (Abs nt Tt tt)"
    and B: "B = umeas K env X [Abs ns Ts ts, Abs nt Tt tt]"
  shows "\<exists>r. (unify_types alg Ts Tt env \<bind> (\<lambda>env'. unif alg ((nm, Ts) # bs) ts tt env')) = Some r \<and>
    upost A K env X r"
proof -
  let ?\<theta> = "tyenv env" let ?\<rho> = "tnorm_inst ?\<theta>"
  note e = einvD[OF ei] and r0 = einv_rho0[OF ei] and pd = pokD[OF p]
  obtain e0 T0 where ty0: "bs_env ?\<rho> e0 bs" "e0 \<turnstile> inst ?\<rho> (Abs ns Ts ts) : T0"
    "e0 \<turnstile> inst ?\<rho> (Abs nt Tt tt) : T0"
    using pd(9)[OF r0] by blast
  from ty0(2) have cTs: "cert_typ alg ar (tsubst ?\<rho> Ts)" by auto
  from ty0(3) have cTt: "cert_typ alg ar (tsubst ?\<rho> Tt)" by auto
  have kTs: "tvars Ts \<subseteq> tvars_env ?\<theta> \<union> A" and kTt: "tvars Tt \<subseteq> tvars_env ?\<theta> \<union> A"
    using pd(3,4) by (auto simp: ttvars_def)
  have tcs: "tcert alg (tvars Ts)" "tcert alg (tvars Tt)" using e(10) kTs kTt tcert_mono by blast+
  note wTs = cert_typ_tsubst_rev[OF cTs tcs(1)] and wTt = cert_typ_tsubst_rev[OF cTt tcs(2)]
  from unify_types_term[OF ei finK kTs wTs kTt wTt] show ?thesis
  proof
    assume "\<exists>u. unify_types alg Ts Tt env = raise (Unif u)"
    then obtain u where "unify_types alg Ts Tt env = raise (Unif u)" by blast
    then have "(unify_types alg Ts Tt env \<bind> (\<lambda>env'. unif alg ((nm, Ts) # bs) ts tt env')) = raise (Unif u)"
      by simp
    then show ?thesis by (simp add: raise_def)
  next
    assume "\<exists>env'. unify_types alg Ts Tt env = return env' \<and> einv A K env' \<and> tenv env' = tenv env \<and>
      textends (tyenv env) (tyenv env') \<and> maxidx env \<le> maxidx env' \<and>
      tvars_env (tyenv env) \<subseteq> tvars_env (tyenv env') \<and>
      (\<forall>\<rho>. tsol (tyenv env') \<rho> \<longrightarrow> tsubst \<rho> Ts = tsubst \<rho> Tt) \<and>
      (tyenv env' = tyenv env \<or> card (uvarsA (tyenv env') K) < card (uvarsA (tyenv env) K))"
    then obtain env1 where ut: "unify_types alg Ts Tt env = return env1" and ei1: "einv A K env1"
      and te: "tenv env1 = tenv env" and tx: "textends ?\<theta> (tyenv env1)" and mx: "maxidx env \<le> maxidx env1"
      and tv: "tvars_env ?\<theta> \<subseteq> tvars_env (tyenv env1)"
      and sol: "\<forall>\<rho>. tsol (tyenv env1) \<rho> \<longrightarrow> tsubst \<rho> Ts = tsubst \<rho> Tt"
      and card: "tyenv env1 = ?\<theta> \<or> card (uvarsA (tyenv env1) K) < card (uvarsA ?\<theta> K)"
      by blast
    have up1: "upost A K env X (Ok env1)" by (rule upost_tyext[OF ei1 wi te tx mx tv card])
    have wi1: "winv env1 X" using upost_OkD(2)[OF up1] .
    have ev: "evars env1 = evars env" using te by (simp add: evars_def bnds_def)
    have p1: "pok A env1 ((nm, Ts) # bs) X ts tt"
      unfolding pok_def
    proof (intro conjI allI impI)
      show "vars ts \<union> vars tt \<subseteq> X \<union> evars env1" using pd(1,2) ev by simp
      show "ttvars ts \<union> ttvars tt \<union> btvars ((nm, Ts) # bs) \<union> vtvars X \<subseteq> tvars_env (tyenv env1) \<union> A"
        using pd(3-6) tv kTs by (auto simp: ttvars_def btvars_def)
      show "\<not> loose_bvar ts (ilength ((nm, Ts) # bs))" using pd(7) by (simp add: algebra_simps)
      show "\<not> loose_bvar tt (ilength ((nm, Ts) # bs))" using pd(8) by (simp add: algebra_simps)
      fix \<rho> assume \<rho>: "tsol (tyenv env1) \<rho>" "cert_inst \<rho>"
      have \<rho>0: "tsol ?\<theta> \<rho>" by (rule tsol_textends[OF tx \<rho>(1)])
      obtain e T where ty: "bs_env \<rho> e bs" "e \<turnstile> inst \<rho> (Abs ns Ts ts) : T" "e \<turnstile> inst \<rho> (Abs nt Tt tt) : T"
        using pd(9)[OF \<rho>0 \<rho>(2)] by blast
      have eq: "tsubst \<rho> Ts = tsubst \<rho> Tt" using sol \<rho>(1) by blast
      from ty(2) obtain U where T: "T = tsubst \<rho> Ts \<rightarrow>\<^sub>T U" and c: "cert_typ alg ar (tsubst \<rho> Ts)"
        and t1: "e\<langle>0:tsubst \<rho> Ts\<rangle> \<turnstile> inst \<rho> ts : U" by auto
      from ty(3) obtain U' where T': "T = tsubst \<rho> Tt \<rightarrow>\<^sub>T U'"
        and t2: "e\<langle>0:tsubst \<rho> Tt\<rangle> \<turnstile> inst \<rho> tt : U'" by auto
      from T T' eq have "U' = U" by simp
      with t1 t2 eq bs_env_Cons[OF ty(1) c]
      show "\<exists>e T. bs_env \<rho> e ((nm, Ts) # bs) \<and> e \<turnstile> inst \<rho> ts : T \<and> e \<turnstile> inst \<rho> tt : T" by metis
    qed
    have lt: "(umeas K env1 X [ts, tt], B) \<in> ulex"
    proof (cases "tyenv env1 = ?\<theta>")
      case True
      have M1: "M (tnorm_inst (tyenv env1)) env1 = M ?\<rho> env" using True M_tenv[OF te] by simp
      have "M ?\<rho> env (Abs ns Ts ts) = M ?\<rho> env ts + 2"
        by (rule M_Abs[OF typing_unf0[OF ei wi _ ty0(2)]]) (use pd(1) in simp)
      moreover have "M ?\<rho> env (Abs nt Tt tt) = M ?\<rho> env tt + 2"
        by (rule M_Abs[OF typing_unf0[OF ei wi _ ty0(3)]]) (use pd(2) in simp)
      ultimately show ?thesis using True M1 ubv_tenv[OF te] B by (simp add: umeas_def)
    next
      case False
      with card B show ?thesis by (simp add: umeas_def)
    qed
    obtain r where r: "unif alg ((nm, Ts) # bs) ts tt env1 = Some r" "upost A K env1 X r"
      using IH[OF lt ei1 wi1 p1] by blast
    show ?thesis using ut r upost_trans[OF up1 r(2)] by simp
  qed
qed

lemma eta_facts:
  assumes ei: "einv A K env" and wi: "winv env X" and p: "pok A env bs X (Abs ns Ts ts) t'"
    and hd: "rigid (fst (strip_comb t')) \<or> (\<exists>F T. fst (strip_comb t') = Var F T \<and> vt_lookup (tenv env) F = None)"
  shows "pok A env ((ns, Ts) # bs) X ts (incr t' $ Bound 0)"
    and "M (tnorm_inst (tyenv env)) env ts + M (tnorm_inst (tyenv env)) env (incr t' $ Bound 0) <
      M (tnorm_inst (tyenv env)) env (Abs ns Ts ts) + M (tnorm_inst (tyenv env)) env t'"
proof -
  let ?\<rho> = "tnorm_inst (tyenv env)"
  note e = einvD[OF ei] and r0 = einv_rho0[OF ei] and pd = pokD[OF p]
  have ty_eta: "\<exists>U. e\<langle>0:tsubst \<rho> Ts\<rangle> \<turnstile> inst \<rho> ts : U \<and> e\<langle>0:tsubst \<rho> Ts\<rangle> \<turnstile> inst \<rho> (incr t' $ Bound 0) : U \<and>
      cert_typ alg ar (tsubst \<rho> Ts)"
    if "e \<turnstile> inst \<rho> (Abs ns Ts ts) : T" "e \<turnstile> inst \<rho> t' : T" for \<rho> e T
  proof -
    from that(1) obtain U where T: "T = tsubst \<rho> Ts \<rightarrow>\<^sub>T U" and c: "cert_typ alg ar (tsubst \<rho> Ts)"
      and t1: "e\<langle>0:tsubst \<rho> Ts\<rangle> \<turnstile> inst \<rho> ts : U" by auto
    have "e\<langle>0:tsubst \<rho> Ts\<rangle> \<turnstile> inst \<rho> (incr t' $ Bound 0) : U"
      using that(2) T by (auto simp: incr_def incr_aux_lift intro!: lift_type)
    with t1 c show ?thesis by blast
  qed
  show p': "pok A env ((ns, Ts) # bs) X ts (incr t' $ Bound 0)"
    unfolding pok_def
  proof (intro conjI allI impI)
    show "vars ts \<union> vars (incr t' $ Bound 0) \<subseteq> X \<union> evars env" using pd(1,2) by (simp add: incr_def)
    show "ttvars ts \<union> ttvars (incr t' $ Bound 0) \<union> btvars ((ns, Ts) # bs) \<union> vtvars X \<subseteq> tvars_env (tyenv env) \<union> A"
      using pd(3-6) by (auto simp: ttvars_def btvars_def incr_def incr_aux_lift)
    show "\<not> loose_bvar ts (ilength ((ns, Ts) # bs))" using pd(7) by (simp add: algebra_simps)
    show "\<not> loose_bvar (incr t' $ Bound 0) (ilength ((ns, Ts) # bs))"
      using pd(8) loose_bvar_lift[of 0 "ilength bs" t'] ilength_nonneg[of bs]
      by (simp add: incr_def incr_aux_lift integer_arith)
    fix \<rho> assume \<rho>: "tsol (tyenv env) \<rho>" "cert_inst \<rho>"
    obtain e T where ty: "bs_env \<rho> e bs" "e \<turnstile> inst \<rho> (Abs ns Ts ts) : T" "e \<turnstile> inst \<rho> t' : T"
      using pd(9)[OF \<rho>] by blast
    from ty_eta[OF ty(2,3)] obtain U where "e\<langle>0:tsubst \<rho> Ts\<rangle> \<turnstile> inst \<rho> ts : U"
      "e\<langle>0:tsubst \<rho> Ts\<rangle> \<turnstile> inst \<rho> (incr t' $ Bound 0) : U" "cert_typ alg ar (tsubst \<rho> Ts)" by blast
    with bs_env_Cons[OF ty(1)] show "\<exists>e T. bs_env \<rho> e ((ns, Ts) # bs) \<and> e \<turnstile> inst \<rho> ts : T \<and>
        e \<turnstile> inst \<rho> (incr t' $ Bound 0) : T" by blast
  qed
  obtain e0 T0 where ty0: "bs_env ?\<rho> e0 bs" "e0 \<turnstile> inst ?\<rho> (Abs ns Ts ts) : T0" "e0 \<turnstile> inst ?\<rho> t' : T0"
    using pd(9)[OF r0] by blast
  from ty_eta[OF ty0(2,3)] obtain U where tts: "e0\<langle>0:tsubst ?\<rho> Ts\<rangle> \<turnstile> inst ?\<rho> ts : U"
    and tet: "e0\<langle>0:tsubst ?\<rho> Ts\<rangle> \<turnstile> inst ?\<rho> (incr t' $ Bound 0) : U" by blast
  have pd' : "vars (incr t' $ Bound 0) \<subseteq> X \<union> evars env" using pokD(2)[OF p'] .
  obtain h us where st: "strip_comb t' = (h, us)" by force
  have t': "t' = h \<degree>\<degree> us" by (rule strip_comb_apps[OF st])
  have hd': "rigid h \<or> (\<exists>F T. h = Var F T \<and> vt_lookup (tenv env) F = None)" using hd st by simp
  have "M ?\<rho> env (incr t' $ Bound 0) \<le> M ?\<rho> env t' + 1"
    unfolding t' by (rule M_eta[OF e(3,4) hd' typing_unf0[OF ei wi pd(2) ty0(3), unfolded t']
        typing_unf0[OF ei wi pd' tet, unfolded t']])
  moreover have "M ?\<rho> env (Abs ns Ts ts) = M ?\<rho> env ts + 2"
    by (rule M_Abs[OF typing_unf0[OF ei wi pd(1) ty0(2)]])
  ultimately show "M ?\<rho> env ts + M ?\<rho> env (incr t' $ Bound 0) < M ?\<rho> env (Abs ns Ts ts) + M ?\<rho> env t'"
    by simp
qed

lemma case_eta_l:
  assumes ei: "einv A K env" and wi: "winv env X" and p: "pok A env bs X (Abs ns Ts ts) t'"
    and hd: "rigid (fst (strip_comb t')) \<or> (\<exists>F T. fst (strip_comb t') = Var F T \<and> vt_lookup (tenv env) F = None)"
    and B: "B = umeas K env X [Abs ns Ts ts, t']"
  shows "\<exists>r. unif alg ((ns, Ts) # bs) ts (incr t' $ Bound 0) env = Some r \<and> upost A K env X r"
proof (rule IH[OF _ ei wi eta_facts(1)[OF ei wi p hd]])
  show "(umeas K env X [ts, incr t' $ Bound 0], B) \<in> ulex"
    using eta_facts(2)[OF ei wi p hd] B by (simp add: umeas_def)
qed

lemma case_eta_r:
  assumes ei: "einv A K env" and wi: "winv env X" and p: "pok A env bs X s' (Abs nt Tt tt)"
    and hd: "rigid (fst (strip_comb s')) \<or> (\<exists>F T. fst (strip_comb s') = Var F T \<and> vt_lookup (tenv env) F = None)"
    and B: "B = umeas K env X [s', Abs nt Tt tt]"
  shows "\<exists>r. unif alg ((nt, Tt) # bs) (incr s' $ Bound 0) tt env = Some r \<and> upost A K env X r"
proof (rule IH[OF _ ei wi pok_sym[OF eta_facts(1)[OF ei wi pok_sym[OF p] hd]]])
  show "(umeas K env X [incr s' $ Bound 0, tt], B) \<in> ulex"
    using eta_facts(2)[OF ei wi pok_sym[OF p] hd] B by (simp add: umeas_def)
qed

end

end

end

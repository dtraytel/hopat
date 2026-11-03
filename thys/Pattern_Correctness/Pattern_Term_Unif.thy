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


lemma pok_app_flex:
  assumes ei: "einv A K env" and wi: "winv env X" and p: "pok A env bs X s' t'"
    and st: "strip_comb s' = (Var F Fty, ss)" and io: "ints_of' env ss = return is"
  shows "pok A env bs X (app (Var F Fty) is) t'"
  unfolding pok_def
proof (intro conjI allI impI)
  note pd = pokD[OF p] and r0 = einv_rho0[OF ei]
  have s': "s' = Var F Fty \<degree>\<degree> ss" by (rule strip_comb_apps[OF st])
  have io': "ok (ints_of' env ss) is" using io by (simp add: return_def)
  show "vars (app (Var F Fty) is) \<union> vars t' \<subseteq> X \<union> evars env" using pd(1,2) s' by (auto simp: vars_apps)
  show "ttvars (app (Var F Fty) is) \<union> ttvars t' \<union> btvars bs \<union> vtvars X \<subseteq> tvars_env (tyenv env) \<union> A"
    using pd(3-6) s' by (auto simp: ttvars_apps)
  have w0: "wt_env (tnorm_inst (tyenv env)) env" using winvD[OF wi r0] by blast
  have "\<forall>i\<in>set is. i < ilength bs"
    by (rule ints_of'_loose[OF io' w0 ilength_nonneg]) (use pd(7) s' in \<open>simp add: loose_bvar_apps\<close>)
  then show "\<not> loose_bvar (app (Var F Fty) is) (ilength bs)" by (simp add: loose_bvar_app_Var)
  show "\<not> loose_bvar t' (ilength bs)" by (rule pd(8))
  fix \<rho> assume \<rho>: "tsol (tyenv env) \<rho>" "cert_inst \<rho>"
  obtain e T where ty: "bs_env \<rho> e bs" "e \<turnstile> inst \<rho> s' : T" "e \<turnstile> inst \<rho> t' : T" using pd(9)[OF \<rho>] by blast
  have "wt_env \<rho> env" using winvD[OF wi \<rho>] by blast
  from flex_sound(1)[OF io' \<rho>(1) this ty(2)[unfolded s']] ty(1,3)
  show "\<exists>e T. bs_env \<rho> e bs \<and> e \<turnstile> inst \<rho> (app (Var F Fty) is) : T \<and> e \<turnstile> inst \<rho> t' : T" by blast
qed

lemma ints_of'_flex:
  assumes ei: "einv A K env" and wi: "winv env X" and p: "pok A env bs X s' t'"
    and st: "strip_comb s' = (Var F Fty, ss)"
  shows "(\<exists>is. ints_of' env ss = return is) \<or> ints_of' env ss = raise Pattern"
proof (rule ints_of'_result[OF einvD(3,4,6,7)[OF ei]])
  note pd = pokD[OF p] and r0 = einv_rho0[OF ei]
  have s': "s' = Var F Fty \<degree>\<degree> ss" by (rule strip_comb_apps[OF st])
  have vss: "vars t \<subseteq> X \<union> evars env" if "t \<in> set ss" for t using pd(1) s' that by (auto simp: vars_apps)
  show "vok env (\<Union> (vars ` set ss) \<union> evars env)"
    by (rule vok_mono[OF vok_winv[OF ei wi pd(6)]]) (use vss in blast)
  fix t assume tin: "t \<in> set ss"
  obtain e T where "e \<turnstile> inst (tnorm_inst (tyenv env)) s' : T" using pd(9)[OF r0] by blast
  then obtain U where "e \<turnstile> inst (tnorm_inst (tyenv env)) t : U"
    using typing_args[of e _ "map (inst (tnorm_inst (tyenv env))) ss" T] tin s' by (auto simp: inst_apps)
  then show "termip (sup beta subt) (unf env t)" by (rule termip_unf0[OF ei wi vss[OF tin]])
qed

lemma upost_flex:
  assumes "einv A K env'" "winv env' X" "extends env env'" "tyenv env' = tyenv env"
    "card (ubv env' X) < card (ubv env X) \<or> (card (ubv env' X) \<le> card (ubv env X) \<and> prunes env env' X)"
  shows "upost A K env X (Ok env')"
  using assms by (simp add: upost_def)


lemma ex_returnI: "m = return x \<Longrightarrow> P (Ok x) \<Longrightarrow> \<exists>r. m = Some r \<and> P r"
  and ex_raiseI: "m = raise e \<Longrightarrow> P (Err e) \<Longrightarrow> \<exists>r. m = Some r \<and> P r"
  by (simp_all add: return_def raise_def)

lemma case_flexflex:
  assumes ei: "einv A K env" and wi: "winv env X" and fin: "finite X" and p: "pok A env bs X s' t'"
    and st1: "strip_comb s' = (Var F Fty, ss)" and st2: "strip_comb t' = (Var G Gty, ts)"
    and F0: "vt_lookup (tenv env) F = None" and G0: "vt_lookup (tenv env) G = None"
  shows "\<exists>r. (ints_of' env ss \<bind> (\<lambda>is. ints_of' env ts \<bind> (\<lambda>js.
      if F = G then flexflex1 env bs F Fty is js else flexflex2 env bs F Fty is G Gty js))) = Some r \<and>
    upost A K env X r"
proof -
  let ?\<rho> = "tnorm_inst (tyenv env)"
  note r0 = einv_rho0[OF ei]
  from ints_of'_flex[OF ei wi p st1] show ?thesis
  proof
    assume "ints_of' env ss = raise Pattern"
    then show ?thesis by (intro ex_raiseI[of _ Pattern]) simp_all
  next
    assume "\<exists>is. ints_of' env ss = return is"
    then obtain "is" where io1: "ints_of' env ss = return is" by blast
    from ints_of'_flex[OF ei wi pok_sym[OF p] st2] show ?thesis
    proof
      assume "ints_of' env ts = raise Pattern"
      then show ?thesis using io1 by (intro ex_raiseI[of _ Pattern]) simp_all
    next
      assume "\<exists>js. ints_of' env ts = return js"
      then obtain js where io2: "ints_of' env ts = return js" by blast
      have p1: "pok A env bs X (app (Var F Fty) is) (app (Var G Gty) js)"
        using pok_sym[OF pok_app_flex[OF ei wi pok_sym[OF pok_app_flex[OF ei wi p st1 io1]] st2 io2]] .
      note pd = pokD[OF p1]
      obtain e0 T0 where ty0: "e0 \<turnstile> inst ?\<rho> (app (Var F Fty) is) : T0" "e0 \<turnstile> inst ?\<rho> (app (Var G Gty) js) : T0"
        using pd(9)[OF r0] by blast
      have FX: "(F, Fty) \<in> X \<union> evars env" and GX: "(G, Gty) \<in> X \<union> evars env" using pd(1,2) by auto
      have tvF: "tvars Fty \<subseteq> tvars_env (tyenv env) \<union> A" and tvG: "tvars Gty \<subseteq> tvars_env (tyenv env) \<union> A"
        using pd(3,4) by (simp_all add: ttvars_def app_apps typs_apps)
      show ?thesis
      proof (cases "F = G")
        case True
        from flexflex1_term[OF ei wi fin F0 FX GX[unfolded True[symmetric]] ty0(1) ty0(2)[unfolded True[symmetric]]
            pd(7) tvF pd(5)]
        obtain env' where r: "flexflex1 env bs F Fty is js = return env'" and post: "einv A K env'"
          "tyenv env' = tyenv env" "extends env env'" "prunes env env' X" "card (ubv env' X) \<le> card (ubv env X)"
          by blast
        have "winv env' X"
          by (rule winv_step[OF flexflex1_step[OF r[unfolded return_def]] wi p1[unfolded True[symmetric]]])
        then show ?thesis using io1 io2 True r post upost_flex by (intro ex_returnI[of _ env']) simp_all
      next
        case False
        from flexflex2_term[OF ei wi fin F0 FX G0 GX False[symmetric] ty0 pd(7,8) tvF tvG pd(5)]
        obtain env' where r: "flexflex2 env bs F Fty is G Gty js = return env'" and post: "einv A K env'"
          "tyenv env' = tyenv env" "extends env env'" "card (ubv env' X) < card (ubv env X)"
          by blast
        have "winv env' X" by (rule winv_step[OF flexflex2_step[OF r[unfolded return_def]] wi p1])
        then show ?thesis using io1 io2 False r post upost_flex by (intro ex_returnI[of _ env']) simp_all
      qed
    qed
  qed
qed

lemma case_flexrigid:
  assumes ei: "einv A K env" and wi: "winv env X" and fin: "finite X" and p: "pok A env bs X s' t'"
    and st1: "strip_comb s' = (Var F Fty, ss)" and F0: "vt_lookup (tenv env) F = None"
  shows "\<exists>r. (ints_of' env ss \<bind> (\<lambda>is. flexrigid env bs F Fty is t')) = Some r \<and> upost A K env X r"
proof -
  let ?\<rho> = "tnorm_inst (tyenv env)"
  note r0 = einv_rho0[OF ei]
  from ints_of'_flex[OF ei wi p st1] show ?thesis
  proof
    assume "ints_of' env ss = raise Pattern"
    then show ?thesis by (intro ex_raiseI[of _ Pattern]) simp_all
  next
    assume "\<exists>is. ints_of' env ss = return is"
    then obtain "is" where io1: "ints_of' env ss = return is" by blast
    have p1: "pok A env bs X (app (Var F Fty) is) t'" by (rule pok_app_flex[OF ei wi p st1 io1])
    note pd = pokD[OF p1]
    obtain e0 T0 where ty0: "e0 \<turnstile> inst ?\<rho> (app (Var F Fty) is) : T0" using pd(9)[OF r0] by blast
    from ty0 have is0: "\<forall>i\<in>set is. 0 \<le> i" by (rule typing_appE)
    have xs: "\<forall>i\<in>set is. 0 \<le> i \<and> i < ilength bs" using is0 pd(7) by (simp add: loose_bvar_app_Var)
    have FX: "(F, Fty) \<in> X \<union> evars env" using pd(1) by auto
    have tv: "ttvars t' \<union> btvars bs \<union> tvars Fty \<subseteq> tvars_env (tyenv env) \<union> A"
      using pd(3-5) by (auto simp: ttvars_def app_apps typs_apps)
    have ty: "\<exists>e T. bs_env \<rho> e bs \<and> e \<turnstile> inst \<rho> t' : T" if "tsol (tyenv env) \<rho>" "cert_inst \<rho>" for \<rho>
      using pd(9)[OF that] by blast
    from flexrigid_term[OF ei wi fin pd(6) F0 FX xs pd(2) tv pd(8) ty]
    obtain r where r: "flexrigid env bs F Fty is t' = Some r"
      and post: "case r of Ok env' \<Rightarrow> einv A K env' \<and> tyenv env' = tyenv env \<and> extends env env' \<and>
          card (ubv env' X) < card (ubv env X) | Err e \<Rightarrow> (\<exists>v. e = Unif v) \<or> e = Pattern"
      by blast
    show ?thesis
    proof (cases r)
      case (Ok env')
      with post have post': "einv A K env'" "tyenv env' = tyenv env" "extends env env'"
        "card (ubv env' X) < card (ubv env X)" by simp_all
      have "winv env' X" by (rule winv_step[OF flexrigid_step[OF r[unfolded Ok]] wi p1])
      then show ?thesis using io1 r Ok post' upost_flex by simp
    next
      case (Err e)
      with post io1 r show ?thesis by simp
    qed
  qed
qed


definition pairs :: "(pterm \<times> pterm) list \<Rightarrow> pterm list" where
  "pairs ps = concat (map (\<lambda>(a, b). [a, b]) ps)"

lemma pairs_simps [simp]: "pairs [] = []" "pairs ((a, b) # ps) = a # b # pairs ps"
  by (simp_all add: pairs_def)

lemma sum_pairs_zip:
  "length ss = length ts \<Longrightarrow> sum_list (map (f :: pterm \<Rightarrow> nat) (pairs (zip ss ts))) = sum_list (map f ss) + sum_list (map f ts)"
  by (induction ss ts rule: list_induct2) (simp_all add: algebra_simps)

lemma zip_eq_ok: "length ss = length ts \<Longrightarrow> zip_eq ss ts = return (zip ss ts)"
  by (induction ss ts rule: list_induct2) simp_all

lemma ulex_le:
  assumes "((x, y, z), B) \<in> ulex" "x1 \<le> x" "x1 = x \<longrightarrow> y1 \<le> y" "x1 = x \<and> y1 = y \<longrightarrow> z1 \<le> z"
  shows "((x1, y1, z1), B) \<in> ulex"
proof -
  obtain bx "by" bz where B: "B = (bx, by, bz)" by (cases B) auto
  from assms(1) B have "x < bx \<or> x = bx \<and> (y < by \<or> y = by \<and> z < bz)" by simp
  with assms(2-4) B show ?thesis by auto
qed

text \<open>Pruning extensions keep the measure of the remaining problems:\<close>

lemma sum_M_prunes:
  assumes pr: "prunes env env1 X" and wi1: "winv env1 X" and ei: "einv A K env"
    and th: "tyenv env1 = tyenv env"
    and ts: "\<And>t. t \<in> set ts \<Longrightarrow> vars t \<subseteq> X \<union> evars env \<and> (\<exists>e T. e \<turnstile> inst (tnorm_inst (tyenv env)) t : T)"
  shows "sum_list (map (M (tnorm_inst (tyenv env1)) env1) ts) = sum_list (map (M (tnorm_inst (tyenv env)) env) ts)"
proof -
  let ?\<rho> = "tnorm_inst (tyenv env)"
  note r0 = einv_rho0[OF ei]
  have w: "wt_env ?\<rho> env1" "vinv ?\<rho> env1 X" using winvD[OF wi1] r0 th by auto
  have vc: "vcons ?\<rho> (X \<union> evars env1)" using w(2) by (simp add: vinv_def)
  have "M ?\<rho> env1 t = M ?\<rho> env t" if "t \<in> set ts" for t
    using ts[OF that] pr w(1) vc unfolding prunes_def by blast
  then show ?thesis using th by (simp cong: map_cong)
qed

lemma rigid_inst: "rigid h \<Longrightarrow> inst \<rho> h = h' \<Longrightarrow> rigid h'"
  by (cases h) auto

text \<open>The arguments of rigid problems with the same head:\<close>

lemma rigid_args_pok:
  assumes p: "pok A env bs X (h \<degree>\<degree> ss) (h' \<degree>\<degree> ts)" and rh: "rigid h" "rigid h'"
    and hh: "\<And>\<rho>. tsol (tyenv env) \<rho> \<Longrightarrow> cert_inst \<rho> \<Longrightarrow> inst \<rho> h = inst \<rho> h'"
    and r0: "tsol (tyenv env) \<rho>0" "cert_inst \<rho>0"
  shows "length ss = length ts" "\<forall>(a, b)\<in>set (zip ss ts). pok A env bs X a b"
proof -
  note pd = pokD[OF p]
  have tys: "\<exists>e Us. bs_env \<rho> e bs \<and> e \<tturnstile> map (inst \<rho>) ss : Us \<and> e \<tturnstile> map (inst \<rho>) ts : Us \<and>
      length ss = length ts" if \<rho>: "tsol (tyenv env) \<rho>" "cert_inst \<rho>" for \<rho>
  proof -
    obtain e T where ty: "bs_env \<rho> e bs" "e \<turnstile> inst \<rho> (h \<degree>\<degree> ss) : T" "e \<turnstile> inst \<rho> (h' \<degree>\<degree> ts) : T"
      using pd(9)[OF \<rho>] by blast
    from list_app_typeD[OF ty(2)[unfolded inst_apps]] obtain Us where
      u1: "e \<turnstile> inst \<rho> h : Us \<Rrightarrow> T" "e \<tturnstile> map (inst \<rho>) ss : Us" by blast
    from list_app_typeD[OF ty(3)[unfolded inst_apps hh[OF \<rho>, symmetric]]] obtain Us' where
      u2: "e \<turnstile> inst \<rho> h : Us' \<Rrightarrow> T" "e \<tturnstile> map (inst \<rho>) ts : Us'" by blast
    have at: "atom (inst \<rho> h)" using rigid_inst[OF rh(1) refl] by (simp add: rigid_def)
    have "Us \<Rrightarrow> T = Us' \<Rrightarrow> T" using u1(1) u2(1) at by (cases "inst \<rho> h") (auto simp: rigid_def)
    moreover from this have "length Us = length Us'" by (rule funs_eq_length)
    ultimately have "Us' = Us" using funs_eq by blast
    moreover have "length ss = length ts"
      using typings_nth[OF u1(2)] typings_nth[OF u2(2)] \<open>length Us = length Us'\<close> by simp
    ultimately show ?thesis using ty(1) u1(2) u2(2) by auto
  qed
  show len: "length ss = length ts" using tys[OF r0] by blast
  show "\<forall>(a, b)\<in>set (zip ss ts). pok A env bs X a b"
  proof (clarify)
    fix a b assume ab: "(a, b) \<in> set (zip ss ts)"
    then obtain i where i: "i < length ss" "a = ss ! i" "b = ts ! i" using len by (auto simp: set_zip)
    have a: "a \<in> set ss" and b: "b \<in> set ts" using i len by auto
    show "pok A env bs X a b"
      unfolding pok_def
    proof (intro conjI allI impI)
      show "vars a \<union> vars b \<subseteq> X \<union> evars env" using pd(1,2) a b by (auto simp: vars_apps)
      show "ttvars a \<union> ttvars b \<union> btvars bs \<union> vtvars X \<subseteq> tvars_env (tyenv env) \<union> A"
        using pd(3-6) a b by (auto simp: ttvars_apps)
      show "\<not> loose_bvar a (ilength bs)" "\<not> loose_bvar b (ilength bs)"
        using pd(7,8) a b by (auto simp: loose_bvar_apps)
      fix \<rho> assume \<rho>: "tsol (tyenv env) \<rho>" "cert_inst \<rho>"
      from tys[OF \<rho>] obtain e Us where e: "bs_env \<rho> e bs" "e \<tturnstile> map (inst \<rho>) ss : Us"
        "e \<tturnstile> map (inst \<rho>) ts : Us" by blast
      from typings_nth[OF e(2)] typings_nth[OF e(3)] i len
      have "e \<turnstile> inst \<rho> a : Us ! i" "e \<turnstile> inst \<rho> b : Us ! i" by auto
      with e(1) show "\<exists>e T. bs_env \<rho> e bs \<and> e \<turnstile> inst \<rho> a : T \<and> e \<turnstile> inst \<rho> b : T" by blast
    qed
  qed
qed

lemma rigid_clash_Unif: "\<exists>u. rigid_clash bs h1 h2 = raise (Unif u)"
  by (auto simp: rigid_clash_def split: pterm.splits)


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

lemma foldM_unif:
  "\<forall>(a, b)\<in>set ps. pok A env bs X a b \<Longrightarrow> einv A K env \<Longrightarrow> winv env X \<Longrightarrow>
    (umeas K env X (pairs ps), B) \<in> ulex \<Longrightarrow>
    \<exists>r. foldM (\<lambda>(s, t) env. unif alg bs s t env) ps env = Some r \<and> upost A K env X r"
proof (induction ps arbitrary: env)
  case Nil
  then show ?case by (intro ex_returnI[of _ env]) (simp_all add: upost_refl)
next
  case (Cons p ps)
  obtain a b where p: "p = (a, b)" by force
  let ?\<rho> = "tnorm_inst (tyenv env)"
  note ei = Cons.prems(2) and wi = Cons.prems(3)
  have pab: "pok A env bs X a b" using Cons.prems(1) p by simp
  have lt0: "(umeas K env X (a # b # pairs ps), B) \<in> ulex" using Cons.prems(4) p by simp
  have lt1: "(umeas K env X [a, b], B) \<in> ulex"
    unfolding umeas_def by (rule ulex_le[OF lt0[unfolded umeas_def]]) simp_all
  obtain r1 where r1: "unif alg bs a b env = Some r1" "upost A K env X r1" using IH[OF lt1 ei wi pab] by blast
  show ?case
  proof (cases r1)
    case (Err e)
    then have "unif alg bs a b env = raise e" using r1(1) by (simp add: raise_def)
    then show ?thesis using r1(2) Err p by (intro ex_raiseI[of _ e]) simp_all
  next
    case (Ok env1)
    note u1 = upost_OkD[OF r1(2)[unfolded Ok]]
    have ps1: "\<forall>(a, b)\<in>set ps. pok A env1 bs X a b"
      using Cons.prems(1) pok_mono[OF _ u1(3,4)] by auto
    have ts: "vars t \<subseteq> X \<union> evars env \<and> (\<exists>e T. e \<turnstile> inst ?\<rho> t : T)" if "t \<in> set (pairs ps)" for t
    proof -
      from that obtain a' b' where ab': "(a', b') \<in> set ps" "t = a' \<or> t = b'" by (auto simp: pairs_def)
      with Cons.prems(1) have pab': "pok A env bs X a' b'" by auto
      from pokD(9)[OF pab' einv_rho0[OF ei]] pokD(1,2)[OF pab'] ab'(2) show ?thesis by blast
    qed
    have lt2: "(umeas K env1 X (pairs ps), B) \<in> ulex"
    proof (cases "tyenv env1 = tyenv env")
      case True
      from u1(5)[OF True] show ?thesis
      proof
        assume "card (ubv env1 X) < card (ubv env X)"
        then show ?thesis using ulex_le[OF lt0[unfolded umeas_def]] True by (simp add: umeas_def)
      next
        assume c: "card (ubv env1 X) \<le> card (ubv env X) \<and> prunes env env1 X"
        have "sum_list (map (M (tnorm_inst (tyenv env1)) env1) (pairs ps)) = sum_list (map (M ?\<rho> env) (pairs ps))"
          using sum_M_prunes[OF conjunct2[OF c] u1(2) ei True ts] by blast
        then show ?thesis using ulex_le[OF lt0[unfolded umeas_def]] True c by (simp add: umeas_def)
      qed
    next
      case False
      with u1(6) show ?thesis using ulex_le[OF lt0[unfolded umeas_def]] by (simp add: umeas_def)
    qed
    from Cons.IH[OF ps1 u1(1,2) lt2] obtain r2 where
      r2: "foldM (\<lambda>(s, t) env. unif alg bs s t env) ps env1 = Some r2" "upost A K env1 X r2" by blast
    have "foldM (\<lambda>(s, t) env. unif alg bs s t env) (p # ps) env = Some r2"
      using r1(1) Ok r2(1) p by (simp add: return_def[symmetric])
    with upost_trans[OF r1(2)[unfolded Ok] r2(2)] show ?thesis by blast
  qed
qed

lemma case_rigid_args:
  assumes ei: "einv A K env" and wi: "winv env X" and p: "pok A env1 bs X (h \<degree>\<degree> ss) (h' \<degree>\<degree> ts)"
    and rh: "rigid h" "rigid h'"
    and up1: "upost A K env X (Ok env1)"
    and hh: "\<And>\<rho>. tsol (tyenv env1) \<rho> \<Longrightarrow> cert_inst \<rho> \<Longrightarrow> inst \<rho> h = inst \<rho> h'"
    and tyM: "\<exists>e T. e \<turnstile> inst (tnorm_inst (tyenv env)) (unf env (h \<degree>\<degree> ss)) : T"
      "\<exists>e T. e \<turnstile> inst (tnorm_inst (tyenv env)) (unf env (h' \<degree>\<degree> ts)) : T"
    and same: "tyenv env1 = tyenv env \<Longrightarrow> tenv env1 = tenv env"
    and B: "B = umeas K env X [h \<degree>\<degree> ss, h' \<degree>\<degree> ts]"
  shows "\<exists>r. (zip_eq ss ts \<bind> (\<lambda>ps. foldM (\<lambda>(s, t) env. unif alg bs s t env) ps env1)) = Some r \<and>
    upost A K env X r"
proof -
  note u1 = upost_OkD[OF up1]
  note ra = rigid_args_pok[OF p rh hh einv_rho0[OF u1(1)]]
  have z: "zip_eq ss ts = return (zip ss ts)" by (rule zip_eq_ok[OF ra(1)])
  let ?\<rho> = "tnorm_inst (tyenv env)"
  have lt: "(umeas K env1 X (pairs (zip ss ts)), B) \<in> ulex"
  proof (cases "tyenv env1 = tyenv env")
    case True
    have te: "tenv env1 = tenv env" by (rule same[OF True])
    have "M ?\<rho> env (h \<degree>\<degree> ss) = 1 + sum_list (map (M ?\<rho> env) ss)" using M_rigid[OF rh(1)] tyM(1) by blast
    moreover have "M ?\<rho> env (h' \<degree>\<degree> ts) = 1 + sum_list (map (M ?\<rho> env) ts)" using M_rigid[OF rh(2)] tyM(2) by blast
    ultimately show ?thesis
      using True B M_tenv[OF te] ubv_tenv[OF te] sum_pairs_zip[OF ra(1)] by (simp add: umeas_def)
  next
    case False
    with u1(6) B show ?thesis by (simp add: umeas_def)
  qed
  from foldM_unif[OF ra(2) u1(1,2) lt] obtain r where
    r: "foldM (\<lambda>(s, t) env. unif alg bs s t env) (zip ss ts) env1 = Some r" "upost A K env1 X r" by blast
  show ?thesis using z r upost_trans[OF up1 r(2)] by simp
qed


lemma case_rigid_same:
  assumes ei: "einv A K env" and wi: "winv env X" and p: "pok A env bs X s' t'"
    and st1: "strip_comb s' = (c Ta, ss)" and st2: "strip_comb t' = (c Tb, ts)"
    and c: "c = Const a \<or> c = Free a" and B: "B = umeas K env X [s', t']"
  shows "\<exists>r. (unify_types alg Ta Tb env \<bind> (\<lambda>env'. zip_eq ss ts \<bind>
      (\<lambda>ps. foldM (\<lambda>(s, t) env. unif alg bs s t env) ps env'))) = Some r \<and> upost A K env X r"
proof -
  let ?\<theta> = "tyenv env" let ?\<rho> = "tnorm_inst ?\<theta>"
  note e = einvD[OF ei] and r0 = einv_rho0[OF ei] and pd = pokD[OF p]
  have s': "s' = c Ta \<degree>\<degree> ss" and t': "t' = c Tb \<degree>\<degree> ts"
    by (rule strip_comb_apps[OF st1], rule strip_comb_apps[OF st2])
  have rc: "rigid (c Ta)" "rigid (c Tb)" using c by auto
  have ic: "inst \<rho> (c T) = c (tsubst \<rho> T)" for \<rho> T using c by auto
  obtain e0 T0 where ty0: "e0 \<turnstile> inst ?\<rho> s' : T0" "e0 \<turnstile> inst ?\<rho> t' : T0" using pd(9)[OF r0] by blast
  have cert: "cert_typ alg ar (tsubst ?\<rho> T)" if "e0 \<turnstile> inst ?\<rho> (c T \<degree>\<degree> us) : T0" for T us
  proof -
    from list_app_typeD[OF that[unfolded inst_apps]] obtain Us where "e0 \<turnstile> inst ?\<rho> (c T) : Us \<Rrightarrow> T0" by blast
    then show ?thesis using c by auto
  qed
  have kTa: "tvars Ta \<subseteq> tvars_env ?\<theta> \<union> A" and kTb: "tvars Tb \<subseteq> tvars_env ?\<theta> \<union> A"
    using pd(3,4) s' t' c by (auto simp: ttvars_apps)
  have tcs: "tcert alg (tvars Ta)" "tcert alg (tvars Tb)" using e(10) kTa kTb tcert_mono by blast+
  note wTa = cert_typ_tsubst_rev[OF cert[OF ty0(1)[unfolded s']] tcs(1)]
    and wTb = cert_typ_tsubst_rev[OF cert[OF ty0(2)[unfolded t']] tcs(2)]
  have tyM: "\<exists>e T. e \<turnstile> inst ?\<rho> (unf env (c Ta \<degree>\<degree> ss)) : T" "\<exists>e T. e \<turnstile> inst ?\<rho> (unf env (c Tb \<degree>\<degree> ts)) : T"
    using typing_unf0[OF ei wi pd(1) ty0(1)] typing_unf0[OF ei wi pd(2) ty0(2)] s' t' by blast+
  from unify_types_term[OF ei finK kTa wTa kTb wTb] show ?thesis
  proof
    assume "\<exists>u. unify_types alg Ta Tb env = raise (Unif u)"
    then obtain u where "unify_types alg Ta Tb env = raise (Unif u)" by blast
    then show ?thesis by (intro ex_raiseI[of _ "Unif u"]) simp_all
  next
    assume "\<exists>env'. unify_types alg Ta Tb env = return env' \<and> einv A K env' \<and> tenv env' = tenv env \<and>
      textends (tyenv env) (tyenv env') \<and> maxidx env \<le> maxidx env' \<and>
      tvars_env (tyenv env) \<subseteq> tvars_env (tyenv env') \<and>
      (\<forall>\<rho>. tsol (tyenv env') \<rho> \<longrightarrow> tsubst \<rho> Ta = tsubst \<rho> Tb) \<and>
      (tyenv env' = tyenv env \<or> card (uvarsA (tyenv env') K) < card (uvarsA (tyenv env) K))"
    then obtain env1 where ut: "unify_types alg Ta Tb env = return env1" and ei1: "einv A K env1"
      and te: "tenv env1 = tenv env" and tx: "textends ?\<theta> (tyenv env1)" and mx: "maxidx env \<le> maxidx env1"
      and tv: "tvars_env ?\<theta> \<subseteq> tvars_env (tyenv env1)"
      and sol: "\<forall>\<rho>. tsol (tyenv env1) \<rho> \<longrightarrow> tsubst \<rho> Ta = tsubst \<rho> Tb"
      and card: "tyenv env1 = ?\<theta> \<or> card (uvarsA (tyenv env1) K) < card (uvarsA ?\<theta> K)"
      by blast
    have up1: "upost A K env X (Ok env1)" by (rule upost_tyext[OF ei1 wi te tx mx tv card])
    have p1: "pok A env1 bs X (c Ta \<degree>\<degree> ss) (c Tb \<degree>\<degree> ts)"
      using pok_mono[OF p upost_OkD(3,4)[OF up1]] s' t' by simp
    have hh: "inst \<rho> (c Ta) = inst \<rho> (c Tb)" if "tsol (tyenv env1) \<rho>" "cert_inst \<rho>" for \<rho>
      using sol that(1) ic by simp
    from case_rigid_args[OF ei wi p1 rc up1 hh tyM _ B[unfolded s' t']] te
    obtain r where "(zip_eq ss ts \<bind> (\<lambda>ps. foldM (\<lambda>(s, t) env. unif alg bs s t env) ps env1)) = Some r"
      "upost A K env X r" by blast
    then show ?thesis using ut by simp
  qed
qed

lemma case_bound_same:
  assumes ei: "einv A K env" and wi: "winv env X" and p: "pok A env bs X s' t'"
    and st1: "strip_comb s' = (Bound i, ss)" and st2: "strip_comb t' = (Bound i, ts)"
    and B: "B = umeas K env X [s', t']"
  shows "\<exists>r. (zip_eq ss ts \<bind> (\<lambda>ps. foldM (\<lambda>(s, t) env. unif alg bs s t env) ps env)) = Some r \<and>
    upost A K env X r"
proof -
  let ?\<rho> = "tnorm_inst (tyenv env)"
  note r0 = einv_rho0[OF ei] and pd = pokD[OF p]
  have s': "s' = Bound i \<degree>\<degree> ss" and t': "t' = Bound i \<degree>\<degree> ts"
    by (rule strip_comb_apps[OF st1], rule strip_comb_apps[OF st2])
  obtain e0 T0 where ty0: "e0 \<turnstile> inst ?\<rho> s' : T0" "e0 \<turnstile> inst ?\<rho> t' : T0" using pd(9)[OF r0] by blast
  have tyM: "\<exists>e T. e \<turnstile> inst ?\<rho> (unf env (Bound i \<degree>\<degree> ss)) : T" "\<exists>e T. e \<turnstile> inst ?\<rho> (unf env (Bound i \<degree>\<degree> ts)) : T"
    using typing_unf0[OF ei wi pd(1) ty0(1)] typing_unf0[OF ei wi pd(2) ty0(2)] s' t' by blast+
  show ?thesis
    by (rule case_rigid_args[OF ei wi p[unfolded s' t'] _ _ upost_refl[OF ei wi] _ tyM _ B[unfolded s' t']]) simp_all
qed


lemma unif_step:
  assumes ei: "einv A K env" and wi: "winv env X" and p: "pok A env bs X s t"
    and B: "B = umeas K env X [s, t]"
  shows "\<exists>r. unif alg bs s t env = Some r \<and> upost A K env X r"
proof -
  obtain s' t' where hs: "head_norm env s = return s'" and ht: "head_norm env t = return t'"
    and p': "pok A env bs X s' t'" and m: "umeas K env X [s', t'] = umeas K env X [s, t]"
    using hn_term[OF ei wi p] by blast
  have B': "B = umeas K env X [s', t']" using B m by simp
  have hd: "rigid (fst (strip_comb u)) \<or> (\<exists>F T. fst (strip_comb u) = Var F T \<and> vt_lookup (tenv env) F = None)"
    if "head_norm env w = return u" "\<not> is_Abs u" for w u
  proof -
    note u = that(1)[unfolded return_def]
    obtain h us where st: "strip_comb u = (h, us)" by force
    have "\<not> is_Abs h" using head_norm_head[OF u refl that(2)] st by simp
    moreover have "\<not> (\<exists>f a. h = f $ a)" by (rule strip_comb_head[OF st])
    ultimately have "rigid h \<or> (\<exists>F T. h = Var F T)" by (rule strip_comb_head_cases)
    then show ?thesis using head_norm_Var_head[OF u refl] st by auto
  qed
  note U = unif.simps[of alg bs s t env]
  show ?thesis
  proof (cases "is_Abs s'")
    case sA: True
    then obtain ns Ts ts where s'': "s' = Abs ns Ts ts" by (cases s') auto
    show ?thesis
    proof (cases "is_Abs t'")
      case True
      then obtain nt Tt tt where t'': "t' = Abs nt Tt tt" by (cases t') auto
      from case_abs_abs[OF ei wi p'[unfolded s'' t''] B'[unfolded s'' t''], of "if ns = STR '''' then nt else ns"]
      show ?thesis unfolding U by (simp add: hs ht s'' t'' Let_def)
    next
      case False
      from case_eta_l[OF ei wi p'[unfolded s''] hd[OF ht False] B'[unfolded s'']]
      show ?thesis unfolding U by (simp add: hs ht s'' False)
    qed
  next
    case sN: False
    show ?thesis
    proof (cases "is_Abs t'")
      case True
      then obtain nt Tt tt where t'': "t' = Abs nt Tt tt" by (cases t') auto
      from case_eta_r[OF ei wi p'[unfolded t''] hd[OF hs sN] B'[unfolded t'']]
      show ?thesis unfolding U by (simp add: hs ht t'' sN)
    next
      case tN: False
      obtain hs1 ss where st1: "strip_comb s' = (hs1, ss)" by force
      obtain ht1 ts where st2: "strip_comb t' = (ht1, ts)" by force
      have h1: "rigid hs1 \<or> (\<exists>F T. hs1 = Var F T \<and> vt_lookup (tenv env) F = None)" using hd[OF hs sN] st1 by simp
      have h2: "rigid ht1 \<or> (\<exists>F T. ht1 = Var F T \<and> vt_lookup (tenv env) F = None)" using hd[OF ht tN] st2 by simp
      note base = hs ht sN tN st1 st2 Let_def
      show ?thesis
      proof (cases "\<exists>F T. hs1 = Var F T \<and> vt_lookup (tenv env) F = None")
        case True
        then obtain F Fty where hF: "hs1 = Var F Fty" "vt_lookup (tenv env) F = None" by blast
        show ?thesis
        proof (cases "\<exists>G T. ht1 = Var G T \<and> vt_lookup (tenv env) G = None")
          case True
          then obtain G Gty where hG: "ht1 = Var G Gty" "vt_lookup (tenv env) G = None" by blast
          from case_flexflex[OF ei wi finX p' st1[unfolded hF(1)] st2[unfolded hG(1)] hF(2) hG(2)]
          show ?thesis unfolding U by (simp add: base hF(1) hG(1))
        next
          case False
          with h2 have r2: "rigid ht1" by blast
          then have "\<not> is_Var ht1" by (simp add: rigid_def)
          with case_flexrigid[OF ei wi finX p' st1[unfolded hF(1)] hF(2)]
          show ?thesis unfolding U by (simp add: base hF(1))
        qed
      next
        case False
        with h1 have r1: "rigid hs1" by blast
        then have nv1: "\<not> is_Var hs1" "\<not> is_Abs hs1" by (cases hs1; simp)+
        show ?thesis
        proof (cases "\<exists>G T. ht1 = Var G T \<and> vt_lookup (tenv env) G = None")
          case True
          then obtain G Gty where hG: "ht1 = Var G Gty" "vt_lookup (tenv env) G = None" by blast
          from case_flexrigid[OF ei wi finX pok_sym[OF p'] st2[unfolded hG(1)] hG(2)] nv1
          show ?thesis unfolding U by (simp add: base hG(1))
        next
          case False
          with h2 have r2: "rigid ht1" by blast
          then have nv2: "\<not> is_Var ht1" "\<not> is_Abs ht1" by (cases ht1; simp)+
          have clash: ?thesis if "unif alg bs s t env = rigid_clash bs hs1 ht1"
            using that rigid_clash_Unif[of bs hs1 ht1] by (auto intro: ex_raiseI)
          have cl: ?thesis if "\<not> (\<exists>a Ta b Tb. hs1 = Const a Ta \<and> ht1 = Const b Tb)"
            "\<not> (\<exists>a Ta b Tb. hs1 = Free a Ta \<and> ht1 = Free b Tb)" "\<not> (\<exists>i j. hs1 = Bound i \<and> ht1 = Bound j)"
          proof (rule clash)
            have "(case (hs1, ht1) of
                (Const a Ta, Const b Tb) \<Rightarrow> if a \<noteq> b then raise (Unif (Clash a b))
                  else unify_types alg Ta Tb env \<bind> (\<lambda>env'. zip_eq ss ts \<bind> (\<lambda>ps. foldM (\<lambda>(x, y). unif alg bs x y) ps env'))
              | (Const a Ta, _) \<Rightarrow> rigid_clash bs hs1 ht1
              | (Free a Ta, Free b Tb) \<Rightarrow> if a \<noteq> b then raise (Unif (Clash a b))
                  else unify_types alg Ta Tb env \<bind> (\<lambda>env'. zip_eq ss ts \<bind> (\<lambda>ps. foldM (\<lambda>(x, y). unif alg bs x y) ps env'))
              | (Free a Ta, _) \<Rightarrow> rigid_clash bs hs1 ht1
              | (Bound i, Bound j) \<Rightarrow> if i \<noteq> j then raise (Unif (Clash_BB bs i j))
                  else zip_eq ss ts \<bind> (\<lambda>ps. foldM (\<lambda>(x, y). unif alg bs x y) ps env)
              | (Bound i, _) \<Rightarrow> rigid_clash bs hs1 ht1
              | (_, _) \<Rightarrow> rigid_clash bs hs1 ht1) = rigid_clash bs hs1 ht1"
              using that by (cases hs1; cases ht1) auto
            then show "unif alg bs s t env = rigid_clash bs hs1 ht1" unfolding U by (simp add: base nv1 nv2)
          qed
          from r1 consider (C) a Ta where "hs1 = Const a Ta" | (Fr) a Ta where "hs1 = Free a Ta"
            | (Bd) i where "hs1 = Bound i" by (cases hs1) auto
          then show ?thesis
          proof cases
            case C
            show ?thesis
            proof (cases "\<exists>b Tb. ht1 = Const b Tb")
              case True
              then obtain b Tb where hb: "ht1 = Const b Tb" by blast
              show ?thesis
              proof (cases "a = b")
                case True
                from case_rigid_same[where c = "Const a", OF ei wi p' st1[unfolded C] st2[unfolded hb True[symmetric]]
                    disjI1[OF refl] B'] True
                show ?thesis unfolding U by (simp add: base C hb)
              next
                case False
                then show ?thesis unfolding U
                  by (intro ex_raiseI[of _ "Unif (Clash a b)"]) (simp_all add: base C hb)
              qed
            qed (rule cl, use C in auto)
          next
            case Fr
            show ?thesis
            proof (cases "\<exists>b Tb. ht1 = Free b Tb")
              case True
              then obtain b Tb where hb: "ht1 = Free b Tb" by blast
              show ?thesis
              proof (cases "a = b")
                case True
                from case_rigid_same[where c = "Free a", OF ei wi p' st1[unfolded Fr] st2[unfolded hb True[symmetric]]
                    disjI2[OF refl] B'] True
                show ?thesis unfolding U by (simp add: base Fr hb)
              next
                case False
                then show ?thesis unfolding U
                  by (intro ex_raiseI[of _ "Unif (Clash a b)"]) (simp_all add: base Fr hb)
              qed
            qed (rule cl, use Fr in auto)
          next
            case Bd
            show ?thesis
            proof (cases "\<exists>j. ht1 = Bound j")
              case True
              then obtain j where hb: "ht1 = Bound j" by blast
              show ?thesis
              proof (cases "i = j")
                case True
                from case_bound_same[OF ei wi p' st1[unfolded Bd] st2[unfolded hb True[symmetric]] B'] True
                show ?thesis unfolding U by (simp add: base Bd hb)
              next
                case False
                then show ?thesis unfolding U
                  by (intro ex_raiseI[of _ "Unif (Clash_BB bs i j)"]) (simp_all add: base Bd hb)
              qed
            qed (rule cl, use Bd in auto)
          qed
        qed
      qed
    qed
  qed
qed

end

subsection \<open>Termination\<close>

lemma wf_ulex: "wf ulex"
  by (intro wf_lex_prod wf_less_than)

text \<open>
  \<^const>\<open>unif\<close> terminates on well-formed problems: for a finite set \<open>X\<close> of the problem's
  variables and a finite set \<open>K\<close> of type variables covering the known ones, it returns an
  environment that keeps the invariants, or fails with \<open>Unif\<close> or \<open>Pattern\<close>.
\<close>

theorem unif_term:
  assumes fin: "finite X" "finite K"
    and "einv A K env" "winv env X" "pok A env bs X s t"
  shows "\<exists>r. unif alg bs s t env = Some r \<and> upost A K env X r"
proof -
  have "\<forall>env bs s t. umeas K env X [s, t] = m \<longrightarrow> einv A K env \<longrightarrow> winv env X \<longrightarrow> pok A env bs X s t \<longrightarrow>
      (\<exists>r. unif alg bs s t env = Some r \<and> upost A K env X r)" for m
  proof (induction m rule: wf_induct_rule[OF wf_ulex])
    case (1 m)
    show ?case
    proof (intro allI impI)
      fix env bs s t assume m: "umeas K env X [s, t] = m" and ei: "einv A K env" and wi: "winv env X"
        and p: "pok A env bs X s t"
      show "\<exists>r. unif alg bs s t env = Some r \<and> upost A K env X r"
      proof (rule unif_step[OF _ fin ei wi p m[symmetric]])
        fix env1 bs1 s1 t1 assume "(umeas K env1 X [s1, t1], m) \<in> ulex" "einv A K env1" "winv env1 X"
          "pok A env1 bs1 X s1 t1"
        then show "\<exists>r. unif alg bs1 s1 t1 env1 = Some r \<and> upost A K env1 X r" using "1.IH" by blast
      qed
    qed
  qed
  with assms(3-5) show ?thesis by blast
qed

lemma finite_tvars_env: "finite (tvars_env \<theta>)"
proof -
  have "tvars_env \<theta> \<subseteq> (\<Union>v\<in>{v. vt_lookup \<theta> v \<noteq> None}.
      insert (v, fst (the (vt_lookup \<theta> v))) (tvars (snd (the (vt_lookup \<theta> v)))))"
    by (force simp: tvars_env_def)
  moreover have "finite (\<Union>v\<in>{v. vt_lookup \<theta> v \<noteq> None}.
      insert (v, fst (the (vt_lookup \<theta> v))) (tvars (snd (the (vt_lookup \<theta> v)))))"
    using finite_vt_lookup[of \<theta>] by simp
  ultimately show ?thesis by (rule finite_subset)
qed

text \<open>
  Hence \<^const>\<open>unify\<close> terminates on closed problems that are well-typed for every certified
  solution of the type environment, if the environment is acyclic, well-typed and consistent with
  the problem (\<^const>\<open>winv\<close>), its type environment satisfies the invariant of type unification
  (\<^const>\<open>tvinv\<close>) and has certified sorts, and the type variables of the problem are known.
  It returns an environment that satisfies these invariants again, or fails with \<open>Unif\<close> or
  \<open>Pattern\<close>; no other exception is raised.
\<close>

theorem unify_terminates:
  assumes fin: "finite A" and tv: "tvinv A env" "scert alg (tyenv env)" "tcert alg (tvars_env (tyenv env) \<union> A)"
    and ac: "acyc env" and wi: "winv env (vars s \<union> vars t)"
    and tvs: "ttvars s \<union> ttvars t \<subseteq> tvars_env (tyenv env) \<union> A"
    and cl: "closed s" "closed t"
    and ty: "\<And>\<rho>. tsol (tyenv env) \<rho> \<Longrightarrow> cert_inst \<rho> \<Longrightarrow> \<exists>e T. e \<turnstile> inst \<rho> s : T \<and> e \<turnstile> inst \<rho> t : T"
  obtains r where "unify alg s t env = Some r"
    and "r = Err e \<Longrightarrow> (\<exists>u. e = Unif u) \<or> e = Pattern"
    and "r = Ok env' \<Longrightarrow> extends env env' \<and> tvinv A env' \<and> scert alg (tyenv env') \<and>
      tcert alg (tvars_env (tyenv env') \<union> A) \<and> acyc env' \<and> winv env' (vars s \<union> vars t)"
proof -
  let ?\<theta> = "tyenv env" let ?X = "vars s \<union> vars t" let ?K = "tvars_env ?\<theta> \<union> A"
  have inv: "tinv ar (maxidx env) ?\<theta> A" by (rule tvinvD(1)[OF tv(1)])
  have r0: "tsol ?\<theta> (tnorm_inst ?\<theta>)" "cert_inst (tnorm_inst ?\<theta>)"
    using tsol_tnorm[OF tinv_tacyc[OF inv]] cert_inst_tnorm[OF tinv_tacyc[OF inv]] tinv_wft[OF inv] tv(2)
    by (auto simp: scert_def)
  have w0: "wt_env (tnorm_inst ?\<theta>) env" "vinv (tnorm_inst ?\<theta>) env ?X" using winvD[OF wi r0] by blast+
  have bb: "bbelow env"
    unfolding bbelow_def
  proof (intro allI impI)
    fix x b assume "vt_lookup (tenv env) x = Some b"
    then obtain U u where "vt_lookup (tenv env) x = Some (U, u)" by (cases b) auto
    then have "(x, U) \<in> ?X \<union> evars env" using evarsI by blast
    with w0(2) show "snd x \<le> maxidx env" unfolding vinv_def by (blast dest: belowD)
  qed
  have cov: "tcovered ?\<theta> ?K ?K" by (auto simp: tcovered_def uvarsA_def)
  have ei: "einv A ?K env"
    using tv ac wt_env_closed_env[OF w0(1)] bb cov by (simp add: einv_def)
  have p: "pok A env [] ?X s t"
    unfolding pok_def
  proof (intro conjI allI impI)
    show "vars s \<union> vars t \<subseteq> ?X \<union> evars env" by blast
    show "ttvars s \<union> ttvars t \<union> btvars [] \<union> vtvars ?X \<subseteq> tvars_env ?\<theta> \<union> A"
      using tvs vtvars_vars[of s] vtvars_vars[of t] by (auto simp: btvars_def vtvars_def)
    show "\<not> loose_bvar s (ilength [])" "\<not> loose_bvar t (ilength [])" using cl by (simp_all add: closed_def)
    fix \<rho> assume "tsol ?\<theta> \<rho>" "cert_inst \<rho>"
    from ty[OF this] show "\<exists>e T. bs_env \<rho> e [] \<and> e \<turnstile> inst \<rho> s : T \<and> e \<turnstile> inst \<rho> t : T"
      by (auto simp: bs_env_def)
  qed
  have finK: "finite ?K" using fin finite_tvars_env by simp
  have finX: "finite ?X" by simp
  obtain r where r: "unif alg [] s t env = Some r" "upost A ?K env ?X r"
    using unif_term[OF finX finK ei wi p] by blast
  show ?thesis
  proof (rule that)
    show "unify alg s t env = Some r" using r(1) by (simp add: unify_def)
    show "(\<exists>u. e = Unif u) \<or> e = Pattern" if "r = Err e" using r(2) that by simp
    show "extends env env' \<and> tvinv A env' \<and> scert alg (tyenv env') \<and> tcert alg (tvars_env (tyenv env') \<union> A) \<and>
        acyc env' \<and> winv env' ?X" if "r = Ok env'"
      using upost_OkD[OF r(2)[unfolded that]] by (simp add: einv_def)
  qed
qed

end

end

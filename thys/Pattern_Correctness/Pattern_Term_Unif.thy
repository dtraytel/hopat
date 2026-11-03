section \<open>Termination of Unification\<close>

theory Pattern_Term_Unif
  imports Pattern_Term_Flex
begin

context pure_sig
begin

(* TEMPORARY STUB, to be replaced by Pattern_Term_Proj *)
definition prpost :: "(indexname \<times> psort) set \<Rightarrow> (indexname \<times> psort) set \<Rightarrow> env \<Rightarrow> (indexname \<times> ptyp) set \<Rightarrow>
    pterm \<Rightarrow> (pterm \<times> env) res \<Rightarrow> bool" where
  "prpost A K env X s r \<longleftrightarrow> (case r of
      Ok (u, env') \<Rightarrow> einv A K env' \<and> winv env' X \<and> tyenv env' = tyenv env \<and> extends env env' \<and>
        prunes env env' X \<and> card (ubv env' X) \<le> card (ubv env X) \<and> newb env env' \<and>
        (\<forall>x b. vt_lookup (tenv env') x = Some b \<longrightarrow> vt_lookup (tenv env) x = None \<longrightarrow>
           x \<in> fst ` vars (unf env s) \<union> {y. maxidx env < snd y}) \<and>
        fst ` vars (unf env' u) \<subseteq> fst ` vars (unf env s) \<union> {y. maxidx env < snd y} \<and>
        ttvars u \<subseteq> tvars_env (tyenv env) \<union> A \<and> vars u \<subseteq> X \<union> evars env'
    | Err e \<Rightarrow> (\<exists>v. e = Unif v) \<or> e = Pattern)"

lemma proj_term:
  assumes "einv A K env" "winv env X" "finite X" "vtvars X \<subseteq> tvars_env (tyenv env) \<union> A"
    and "vars s \<subseteq> X \<union> evars env" "ttvars s \<union> btvars bs \<subseteq> tvars_env (tyenv env) \<union> A"
    and "\<not> loose_bvar s (ilength bs)"
    and "\<And>\<rho>. tsol (tyenv env) \<rho> \<Longrightarrow> cert_inst \<rho> \<Longrightarrow> \<exists>e T. bs_env \<rho> e bs \<and> e \<turnstile> inst \<rho> s : T"
    and "\<forall>x\<in>set is. 0 \<le> x"
  shows "\<exists>r. proj s env bs is = Some r \<and> prpost A K env X s r"
  sorry
(* END STUB *)

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

text \<open>The head variable of a head normal form is unbound:\<close>

lemma head_norm_var_head:
  assumes "head_norm env t = Some r"
  shows "r = Ok t' \<Longrightarrow> fst (strip_comb t') = Var F T \<Longrightarrow> vt_lookup (tenv env) F = None"
  using assms
proof (induction env t r arbitrary: t' rule: head_norm.raw_induct[rotated, consumes 1])
  case (1 hn env t r)
  note h = "1.hyps"[unfolded "1.prems"(1)]
  have IH: "vt_lookup (tenv env) F = None" if "ok (hn env u) u'" "fst (strip_comb u') = Var F T" for u u'
    using "1.IH"[OF that(1) refl that(2)] .
  show ?case
  proof (cases t)
    case (Var x U)
    with h obtain lr where lr: "ok (lookup env x U) lr"
      and rest: "ok (case lr of Some u \<Rightarrow> hn env u | None \<Rightarrow> return t) t'"
      by auto
    show ?thesis
    proof (cases lr)
      case None
      with rest Var have "t' = Var x U" by simp
      with "1.prems"(2) have "x = F" by (simp add: strip_comb_def)
      with lr None show ?thesis using ok_lookup_None by blast
    next
      case (Some u)
      with rest IH "1.prems"(2) show ?thesis by simp
    qed
  next
    case (Abs a U body)
    with h "1.prems"(2) show ?thesis by (auto simp: strip_comb_def)
  next
    case (App f u)
    have redex: ?thesis if "ok (hn env (subst_bound u body)) t'" for body
      using IH[OF that "1.prems"(2)] .
    show ?thesis
    proof (cases "is_Abs f")
      case True
      then obtain b U0 body where f: "f = Abs b U0 body" by (cases f) auto
      with h App redex show ?thesis by simp
    next
      case False
      with h App obtain nf where hf: "ok (hn env f) nf"
        and rest: "ok (case nf of Abs _ _ body \<Rightarrow> hn env (subst_bound u body) | _ \<Rightarrow> return (nf $ u)) t'"
        by (cases f) auto
      show ?thesis
      proof (cases "is_Abs nf")
        case True
        then obtain b U0 body where "nf = Abs b U0 body" by (cases nf) auto
        with rest redex show ?thesis by simp
      next
        case False
        with rest have "t' = nf $ u" by (cases nf) auto
        with "1.prems"(2) have "fst (strip_comb nf) = Var F T"
          by (simp add: strip_comb_App)
        from IH[OF hf this] show ?thesis .
      qed
    qed
  qed (use h "1.prems"(2) in \<open>auto simp: strip_comb_def\<close>)
qed

end

end

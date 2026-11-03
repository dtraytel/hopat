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

end

end

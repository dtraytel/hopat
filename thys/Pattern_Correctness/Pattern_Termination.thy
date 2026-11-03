section \<open>Termination of Pattern Unification\<close>

theory Pattern_Termination
  imports Pattern_Size Pattern_Complete
begin

context pure_sig
begin

subsection \<open>Strong normalization with subterms\<close>

definition subt :: "pterm \<Rightarrow> pterm \<Rightarrow> bool" where
  "subt s t \<longleftrightarrow> (\<exists>a T. s = Abs a T t) \<or> (\<exists>u. s = t $ u) \<or> (\<exists>u. s = u $ t)"

lemma subt_beta: "subt x x1 \<Longrightarrow> x1 \<rightarrow>\<^sub>\<beta> w1 \<Longrightarrow> \<exists>w. x \<rightarrow>\<^sub>\<beta> w \<and> subt w w1"
  by (auto simp: subt_def)

lemma subts_beta: "subt\<^sup>*\<^sup>* x y \<Longrightarrow> y \<rightarrow>\<^sub>\<beta> z \<Longrightarrow> \<exists>w. x \<rightarrow>\<^sub>\<beta> w \<and> subt\<^sup>*\<^sup>* w z"
proof (induction rule: converse_rtranclp_induct)
  case (step x x1)
  from step.IH[OF step.prems] obtain w1 where "x1 \<rightarrow>\<^sub>\<beta> w1" "subt\<^sup>*\<^sup>* w1 z" by blast
  with subt_beta[OF step.hyps(1)] show ?case by (meson converse_rtranclp_into_rtranclp)
qed blast

lemma subt_size: "subt x y \<Longrightarrow> size y < size x"
  by (auto simp: subt_def)

text \<open>Strongly normalizing terms are strongly normalizing for reduction and subterms:\<close>

lemma termip_beta_subt:
  assumes "termip beta t"
  shows "termip (sup beta subt) t"
proof -
  have "\<forall>z. subt\<^sup>*\<^sup>* x z \<longrightarrow> termip (sup beta subt) z" if "termip beta x" for x
    using that
  proof (induction rule: accp_induct_rule)
    case (1 x)
    show ?case
    proof (intro allI impI)
      fix z assume "subt\<^sup>*\<^sup>* x z"
      then show "termip (sup beta subt) z"
      proof (induction z rule: measure_induct_rule[of size])
        case (less z)
        show ?case
        proof (rule accp.accI)
          fix z' assume "conversep (sup beta subt) z' z"
          then have "z \<rightarrow>\<^sub>\<beta> z' \<or> subt z z'" by auto
          then show "termip (sup beta subt) z'"
          proof
            assume "z \<rightarrow>\<^sub>\<beta> z'"
            from subts_beta[OF less.prems this] obtain w where "x \<rightarrow>\<^sub>\<beta> w" "subt\<^sup>*\<^sup>* w z'" by blast
            with "1.IH" show ?thesis by blast
          next
            assume "subt z z'"
            with less.prems have "subt\<^sup>*\<^sup>* x z'" by (rule rtranclp.rtrancl_into_rtrancl)
            with less.IH subt_size[OF \<open>subt z z'\<close>] show ?thesis by blast
          qed
        qed
      qed
    qed
  qed
  with assms show ?thesis by blast
qed

definition sn_less :: "(pterm \<times> pterm) set" where
  "sn_less = {(y, x). termip (sup beta subt) x \<and> (sup beta subt)\<^sup>+\<^sup>+ x y}"

lemma wf_sn_less: "wf sn_less"
proof (rule wfI_pf)
  fix A assume A: "A \<subseteq> sn_less `` A"
  show "A = {}"
  proof (rule ccontr)
    assume "A \<noteq> {}"
    then obtain x where "x \<in> A" by blast
    have "\<forall>y. (sup beta subt)\<^sup>*\<^sup>* x y \<longrightarrow> y \<notin> A" if "termip (sup beta subt) x" for x
      using that
    proof (induction rule: accp_induct_rule)
      case (1 x)
      show ?case
      proof (intro allI impI notI)
        fix y assume xy: "(sup beta subt)\<^sup>*\<^sup>* x y" and yA: "y \<in> A"
        from yA A obtain z where z: "z \<in> A" "(z, y) \<in> sn_less" by blast
        then have "(sup beta subt)\<^sup>+\<^sup>+ y z" by (simp add: sn_less_def)
        with xy have "(sup beta subt)\<^sup>+\<^sup>+ x z" by (rule rtranclp_tranclp_tranclp)
        then obtain x' where x': "sup beta subt x x'" "(sup beta subt)\<^sup>*\<^sup>* x' z"
          by (auto dest: tranclpD)
        have "conversep (sup beta subt) x' x" using x'(1) by (rule conversepI)
        from "1.IH"[OF this] x'(2) z(1) show False by blast
      qed
    qed
    moreover from \<open>x \<in> A\<close> A obtain z where "(z, x) \<in> sn_less" by blast
    then have "termip (sup beta subt) x" by (simp add: sn_less_def)
    ultimately show False using \<open>x \<in> A\<close> by blast
  qed
qed

lemma termip_sup_reds: "(sup beta subt)\<^sup>*\<^sup>* x y \<Longrightarrow> termip (sup beta subt) x \<Longrightarrow> termip (sup beta subt) y"
  by (induction rule: rtranclp_induct) (auto elim: accp_downward intro: conversepI)

lemma beta_reds_sup: "s \<rightarrow>\<^sub>\<beta>\<^sup>* t \<Longrightarrow> (sup beta subt)\<^sup>*\<^sup>* s t"
  by (induction rule: rtranclp_induct) (auto intro: rtranclp.rtrancl_into_rtrancl)


subsection \<open>Head normalization\<close>

definition hrk :: "env \<Rightarrow> pterm \<Rightarrow> nat" where
  "hrk env t = (case t of Var x T \<Rightarrow> Suc (rk env x) | _ \<Rightarrow> 0)"

text \<open>
  On an acyclic environment with closed bindings, head normalization of a consistent term whose
  unfolding is strongly normalizing returns a result.
\<close>

lemma head_norm_term:
  assumes ac: "acyc env" and cl: "closed_env env"
    and tac: "tacyc (tyenv env)" and tc: "tcons_env (tyenv env)"
  shows "vok env (vars t \<union> evars env) \<Longrightarrow> termip (sup beta subt) (unf env t) \<Longrightarrow>
    \<exists>t'. head_norm env t = return t'"
proof (induction t rule: wf_induct_rule[OF wf_inv_image[OF wf_lex_prod[OF wf_sn_less wf_less_than],
    of "\<lambda>t. (unf env t, hrk env t)"]])
  case (1 t)
  have sn: "termip (sup beta subt) u" if "(sup beta subt)\<^sup>*\<^sup>* (unf env t) u" for u
    by (rule termip_sup_reds[OF that "1.prems"(2)])
  have IH: "\<exists>t'. head_norm env u = return t'"
    if "vok env (vars u \<union> evars env)" "(sup beta subt)\<^sup>+\<^sup>+ (unf env t) (unf env u)" for u
  proof (rule "1.IH"[OF _ that(1)])
    have "(unf env u, unf env t) \<in> sn_less"
      by (simp only: sn_less_def mem_Collect_eq case_prod_conv) (use that(2) "1.prems"(2) in blast)
    then show "(u, t) \<in> inv_image (sn_less <*lex*> less_than) (\<lambda>t. (unf env t, hrk env t))"
      by simp
    show "termip (sup beta subt) (unf env u)" by (rule sn[OF tranclp_into_rtranclp[OF that(2)]])
  qed
  have IH': "\<exists>t'. head_norm env u = return t'"
    if "vok env (vars u \<union> evars env)" "unf env u = unf env t" "hrk env u < hrk env t" for u
  proof (rule "1.IH"[OF _ that(1)])
    show "(u, t) \<in> inv_image (sn_less <*lex*> less_than) (\<lambda>t. (unf env t, hrk env t))"
      using that(2,3) by simp
    show "termip (sup beta subt) (unf env u)" by (subst that(2)) (rule "1.prems"(2))
  qed
  have vk: "vok env (vars u \<union> evars env)" if "vars u \<subseteq> vars t \<union> evars env" for u
    using "1.prems"(1) that by (auto intro: vok_mono)
  have redex: "\<exists>t'. head_norm env (subst_bound u body) = return t'"
    if "(sup beta subt)\<^sup>*\<^sup>* (unf env t) (unf env (Abs b U body $ u))" "vars body \<union> vars u \<subseteq> vars t \<union> evars env"
    for b U body u
  proof (subst subst_bound_subst, rule IH)
    have r: "unf env (Abs b U body $ u) \<rightarrow>\<^sub>\<beta> unf env (body[u/0])"
      by (simp add: unf_subst[OF ac cl])
    then show "(sup beta subt)\<^sup>+\<^sup>+ (unf env t) (unf env (body[u/0]))"
      using that(1) by (meson rtranclp_into_tranclp1 sup2I1)
    show "vok env (vars (body[u/0]) \<union> evars env)"
      using vk vars_subst[of body u 0] that(2) by blast
  qed
  show ?case
  proof (cases t)
    case (Var x T)
    have lk: "lookup env x T = return (map_option snd (vt_lookup (tenv env) x))"
      by (rule lookup_ok[OF tac tc vok_mono[OF "1.prems"(1)]]) (auto simp: Var)
    show ?thesis
    proof (cases "vt_lookup (tenv env) x")
      case (Some p)
      obtain U u where p: "p = (U, u)" by force
      have u: "unf env u = unf env t" using Some p Var by (simp add: unf_Var[OF ac])
      have "hrk env u < hrk env t"
      proof (cases u)
        case (Var y U')
        have "(y, x) \<in> dep env" using depI[OF Some[unfolded p], of y U'] Var by simp
        then show ?thesis using rk_less[OF ac] Var \<open>t = Var x T\<close> by (simp add: hrk_def)
      qed (simp_all add: hrk_def \<open>t = Var x T\<close>)
      moreover have "vars u \<subseteq> vars t \<union> evars env" using evarsI2[OF Some[unfolded p]] by blast
      ultimately obtain t' where "head_norm env u = return t'"
        using IH'[of u] vk u by blast
      then show ?thesis using lk Var Some p by (subst head_norm.simps) simp
    qed (use lk Var in \<open>subst head_norm.simps, simp\<close>)
  next
    case (Abs a T body)
    have "subt (unf env t) (unf env body)" using Abs by (simp add: subt_def)
    then have "(sup beta subt)\<^sup>+\<^sup>+ (unf env t) (unf env body)" by blast
    moreover have "vok env (vars body \<union> evars env)" by (rule vk) (use Abs in simp)
    ultimately obtain b' where "head_norm env body = return b'" using IH[of body] by blast
    then show ?thesis using Abs by (subst head_norm.simps) simp
  next
    case (App f u)
    have vfu: "vars f \<union> vars u \<subseteq> vars t \<union> evars env" using App by auto
    show ?thesis
    proof (cases "is_Abs f")
      case True
      then obtain b U body where f: "f = Abs b U body" by (cases f) auto
      from redex[of b U body u] f App vfu show ?thesis by (subst head_norm.simps) simp
    next
      case False
      have "subt (unf env t) (unf env f)" using App by (simp add: subt_def)
      then have tf: "(sup beta subt)\<^sup>+\<^sup>+ (unf env t) (unf env f)" by blast
      moreover have "vok env (vars f \<union> evars env)" using vk vfu by blast
      ultimately obtain nf where nf: "head_norm env f = return nf" using IH[of f] by blast
      have fnf: "unf env f \<rightarrow>\<^sub>\<beta>\<^sup>* unf env nf"
        by (rule head_norm_unf[OF nf[unfolded return_def] refl ac cl])
      have hn: "head_norm env t =
          (case nf of Abs _ _ body \<Rightarrow> head_norm env (subst_bound u body) | _ \<Rightarrow> return (nf $ u))"
        using App False nf by (subst head_norm.simps) (cases f; simp)
      show ?thesis
      proof (cases nf)
        case (Abs b U body)
        have "(sup beta subt)\<^sup>*\<^sup>* (unf env t) (unf env (Abs b U body $ u))"
          using App Abs beta_reds_sup[OF rtrancl_beta_AppL[OF fnf, of "unf env u"]] by simp
        moreover have "vars nf \<subseteq> vars f \<union> evars env"
          by (rule head_norm_vars[OF nf[unfolded return_def] refl])
        then have "vars body \<union> vars u \<subseteq> vars t \<union> evars env" using vfu Abs by auto
        ultimately obtain t' where "head_norm env (subst_bound u body) = return t'" using redex[of b U body u] by blast
        then show ?thesis using hn Abs by simp
      qed (use hn in simp_all)
    qed
  qed (subst head_norm.simps, simp)+
qed

end

end

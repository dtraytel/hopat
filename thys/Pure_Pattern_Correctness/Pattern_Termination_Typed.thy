section \<open>Termination of Pattern Unification on Well-Typed Terms\<close>

theory Pattern_Termination_Typed
  imports Pattern_Size Pattern_Exceptions
begin

text \<open>
  On well-typed terms in an acyclic, well-typed environment, \<^const>\<open>unify\<close> terminates; the terms
  need not be patterns or \<open>\<beta>\<close>-normal. Head normalisation terminates because instances of
  well-typed terms are strongly normalising. The other recursions decrease the size
  \<^const>\<open>Ms\<close> of the \<open>\<beta>\<close>-normal form of the instance, or, when variables are bound, the number of
  unbound variables reachable from the problem.
\<close>

subsection \<open>Strong normalisation with subterms\<close>

definition subt :: "dB \<Rightarrow> dB \<Rightarrow> bool" where
  "subt s t \<longleftrightarrow> s = dB.Abs t \<or> (\<exists>u. s = t \<degree> u) \<or> (\<exists>u. s = u \<degree> t)"

lemma termip_subt: "termip subt t"
proof (induction t rule: measure_induct_rule[of size])
  case (less t)
  show ?case by (rule accp.accI) (use less in \<open>auto simp: subt_def\<close>)
qed

lemma subt_beta: "subt x x1 \<Longrightarrow> x1 \<rightarrow>\<^sub>\<beta> w1 \<Longrightarrow> \<exists>w. x \<rightarrow>\<^sub>\<beta> w \<and> subt w w1"
  by (auto simp: subt_def)

lemma subts_beta: "subt\<^sup>*\<^sup>* x y \<Longrightarrow> y \<rightarrow>\<^sub>\<beta> z \<Longrightarrow> \<exists>w. x \<rightarrow>\<^sub>\<beta> w \<and> subt\<^sup>*\<^sup>* w z"
proof (induction rule: converse_rtranclp_induct)
  case (step x x1)
  from step.IH[OF step.prems] obtain w1 where "x1 \<rightarrow>\<^sub>\<beta> w1" "subt\<^sup>*\<^sup>* w1 z" by blast
  with subt_beta[OF step.hyps(1)] show ?case by (meson converse_rtranclp_into_rtranclp)
qed blast

lemma termip_beta_subt:
  assumes "termip beta t"
  shows "termip (sup beta subt) t"
proof (rule termip_sup[OF _ termip_subt assms])
  show "subt\<^sup>*\<^sup>* OO beta \<le> beta\<^sup>+\<^sup>+ OO subt\<^sup>*\<^sup>*"
  proof (rule predicate2I)
    fix x y assume "(subt\<^sup>*\<^sup>* OO beta) x y"
    then obtain b where "subt\<^sup>*\<^sup>* x b" "b \<rightarrow>\<^sub>\<beta> y" by auto
    from subts_beta[OF this] obtain w where "x \<rightarrow>\<^sub>\<beta> w" "subt\<^sup>*\<^sup>* w y" by blast
    then show "(beta\<^sup>+\<^sup>+ OO subt\<^sup>*\<^sup>*) x y" by auto
  qed
qed

lemma beta_reds_sup: "s \<rightarrow>\<^sub>\<beta>\<^sup>* t \<Longrightarrow> (sup beta subt)\<^sup>*\<^sup>* s t"
  by (induction rule: rtranclp_induct) (auto intro: rtranclp.rtrancl_into_rtrancl)

definition sn_less :: "(dB \<times> dB) set" where
  "sn_less = {(y, x). termip (sup beta subt) x \<and> (sup beta subt)\<^sup>+\<^sup>+ x y}"

lemma wf_sn_less: "wf sn_less"
proof (rule wfI_pf)
  fix A assume A: "A \<subseteq> sn_less `` A"
  show "A = {}"
  proof (rule ccontr)
    assume "A \<noteq> {}"
    then obtain x where "x \<in> A" by blast
    have "\<forall>x. termip (sup beta subt) x \<longrightarrow> (\<forall>y. (sup beta subt)\<^sup>*\<^sup>* x y \<longrightarrow> y \<notin> A)"
    proof (rule allI, rule impI)
      fix x assume "termip (sup beta subt) x"
      then show "\<forall>y. (sup beta subt)\<^sup>*\<^sup>* x y \<longrightarrow> y \<notin> A"
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
          from "1.IH"[OF this] have "\<forall>ya. (sup beta subt)\<^sup>*\<^sup>* x' ya \<longrightarrow> ya \<notin> A" .
          with x'(2) z(1) show False by blast
        qed
      qed
    qed
    moreover from \<open>x \<in> A\<close> A obtain z where "(z, x) \<in> sn_less" by blast
    then have "termip (sup beta subt) x" by (simp add: sn_less_def)
    ultimately show False using \<open>x \<in> A\<close> by blast
  qed
qed

lemma typable_termip_subt: "typable t \<Longrightarrow> termip (sup beta subt) t"
  by (rule termip_beta_subt[OF typable_termip])

lemma sn_lessI: "typable x \<Longrightarrow> (sup beta subt)\<^sup>+\<^sup>+ x y \<Longrightarrow> (y, x) \<in> sn_less"
  by (simp add: sn_less_def typable_termip_subt)


subsection \<open>Termination of head normalisation\<close>

context
  fixes ar env W
  assumes ac: "acyc env" and wf: "wf_env ar env" and ety: "env_typed W env"
begin

abbreviation inst :: "pterm \<Rightarrow> dB" where
  "inst t \<equiv> mk_subst (env_inst env) (tr t)"

lemma head_norm_Ok_typed:
  assumes "hn env t = Some t'" "has_type W Ts t T"
  shows "head_norm env t = Some (Ok t')"
  using hn_head_norm[OF assms(1) wf_envD(1)[OF wf]] head_norm_no_exn[OF wf ety assms(2)]
  by (auto simp: no_exn_def)

lemma reach_card_less:
  assumes "lk env x U = Some u"
  shows "card (reach env (vps u)) < card (reach env (vps (pterm.Var x U)))"
proof (rule psubset_card_mono)
  show "finite (reach env (vps (pterm.Var x U)))" by (simp add: finite_reach[OF fin_env])
  have "reach env (vps u) \<subseteq> reach env {(x, U)}" by (rule reach_lk[OF assms])
  moreover have "(x, U) \<notin> reach env (vps u)"
  proof
    assume "(x, U) \<in> reach env (vps u)"
    from reach_lk_trancl[OF assms this] ac show False unfolding acyc_def acyclic_def by blast
  qed
  moreover have "(x, U) \<in> reach env {(x, U)}" by (rule set_mp[OF reach_incl]) simp
  ultimately show "reach env (vps u) \<subset> reach env (vps (pterm.Var x U))" by auto
qed

lemma hn_term_typed: "has_type W Ts t T \<Longrightarrow> \<exists>t'. hn env t = Some t'"
proof (induction t arbitrary: Ts T rule: wf_induct_rule[OF wf_inv_image[OF wf_lex_prod[OF wf_sn_less wf_less_than],
    of "\<lambda>t. (inst t, card (reach env (vps t)))"]])
  case (1 t)
  have red: "\<exists>t'. hn env u = Some t'"
    if "(sup beta subt)\<^sup>+\<^sup>+ (inst t) (inst u)" "has_type W Us u U" for u Us U
    using "1.IH"[OF _ that(2)] sn_lessI[OF inst_typable[OF ac wf ety "1.prems"] that(1)] by simp
  show ?case
  proof (cases t)
    case (Var x U)
    show ?thesis
    proof (cases "lk env x U")
      case (Some u)
      note lk = lkD[OF Some]
      from env_typedD[OF ety lk] have tyu: "has_type W [] u U" by simp
      have "\<exists>t'. hn env u = Some t'"
        using "1.IH"[OF _ tyu] reach_card_less[OF Some] inst_bound[OF ac wf ety lk] Var by simp
      with Some Var show ?thesis by (subst hn.simps) simp
    qed (use Var in \<open>subst hn.simps; simp\<close>)
  next
    case (Abs a U b)
    from "1.prems" Abs obtain V where tyb: "has_type W (U # Ts) b V" by (auto elim: has_type_elims)
    have "\<exists>t'. hn env b = Some t'"
      by (rule red[OF _ tyb]) (auto simp: Abs subt_def)
    with Abs show ?thesis by (subst hn.simps) auto
  next
    case (App f u)
    from "1.prems" App obtain U where tyf: "has_type W Ts f (U \<rightarrow>\<^sub>T T)" and tyu: "has_type W Ts u U"
      by (auto elim: has_type_elims)
    have pu: "proper u" by (rule has_type_proper[OF tyu])
    show ?thesis
    proof (cases "is_Abs f")
      case True
      then obtain a U' body where f: "f = pterm.Abs a U' body" by (cases f) auto
      from tyf f have tyb: "has_type W (U # Ts) body T" by (auto elim: has_type_elims)
      have pb: "proper body" by (rule has_type_proper[OF tyb])
      have "\<exists>t'. hn env (subst_bound u body) = Some t'"
      proof (rule red[OF _ has_type_subst_bound[OF tyb tyu]])
        have "inst t \<rightarrow>\<^sub>\<beta> inst (subst_bound u body)"
          using App f by (simp add: inst_subst_bound[OF ac wf ety pb pu])
        then show "(sup beta subt)\<^sup>+\<^sup>+ (inst t) (inst (subst_bound u body))" by auto
      qed
      with App f show ?thesis by (subst hn.simps) simp
    next
      case False
      have "\<exists>t'. hn env f = Some t'"
        by (rule red[OF _ tyf]) (auto simp: App subt_def)
      then obtain nf where nf: "hn env f = Some nf" by blast
      have hf: "head_norm env f = Some (Ok nf)" by (rule head_norm_Ok_typed[OF nf tyf])
      have tynf: "has_type W Ts nf (U \<rightarrow>\<^sub>T T)" by (rule head_norm_typed[OF hf refl wf ety tyf])
      have rf: "inst f \<rightarrow>\<^sub>\<beta>\<^sup>* inst nf"
        using head_norm_inst[OF ac wf ety hf has_type_proper[OF tyf]] by simp
      have rest: "\<exists>t'. (case nf of pterm.Abs _ _ body \<Rightarrow> hn env (subst_bound u body) | _ \<Rightarrow> Some (nf $ u)) = Some t'"
      proof (cases "is_Abs nf")
        case True
        then obtain a U' body where nfa: "nf = pterm.Abs a U' body" by (cases nf) auto
        from tynf nfa have tyb: "has_type W (U # Ts) body T" by (auto elim: has_type_elims)
        have pb: "proper body" by (rule has_type_proper[OF tyb])
        have "\<exists>t'. hn env (subst_bound u body) = Some t'"
        proof (rule red[OF _ has_type_subst_bound[OF tyb tyu]])
          have "inst t \<rightarrow>\<^sub>\<beta>\<^sup>* inst nf \<degree> inst u" using rf App by (simp add: rtrancl_beta_AppL)
          moreover have "inst nf \<degree> inst u \<rightarrow>\<^sub>\<beta> inst (subst_bound u body)"
            using nfa by (simp add: inst_subst_bound[OF ac wf ety pb pu])
          ultimately show "(sup beta subt)\<^sup>+\<^sup>+ (inst t) (inst (subst_bound u body))"
            by (auto intro: rtranclp_into_tranclp1 beta_reds_sup)
        qed
        with nfa show ?thesis by simp
      qed (cases nf; simp)
      with False App nf show ?thesis by (subst hn.simps) (cases f; auto)
    qed
  qed (subst hn.simps; simp)+
qed

lemma head_norm_term_typed: "has_type W Ts t T \<Longrightarrow> \<exists>t'. head_norm env t = Some (Ok t')"
  using hn_term_typed head_norm_Ok_typed by blast

lemma ints_of'_termT: "\<forall>t\<in>set ts. \<exists>U. has_type W Ts t U \<Longrightarrow> \<exists>r. ints_of' env ts = Some r"
  unfolding ints_of'_def
  by (rule bindM_term[OF mapM_term ints_of_term]) (use head_norm_term_typed in blast)

end


subsection \<open>Pruning steps\<close>

definition tinvT :: "(name \<Rightarrow> nat) \<Rightarrow> (indexname \<Rightarrow> ptyp) \<Rightarrow> env \<Rightarrow> bool" where
  "tinvT ar W env \<longleftrightarrow> acyc env \<and> wf_env ar env \<and> env_typed W env \<and> fresh_env env"

lemma tinvTD:
  assumes "tinvT ar W env"
  shows "acyc env" "wf_env ar env" "env_typed W env" "fresh_env env"
  using assms by (simp_all add: tinvT_def)

text \<open>
  \<open>prunesT ar W env W' env' S\<close>: \<open>env'\<close> extends \<open>env\<close> by bindings that prune the arguments of
  variables in \<open>S\<close> or of new variables; \<open>W'\<close> types \<open>env'\<close> and agrees with \<open>W\<close> on the old variables.
\<close>

definition prunesT :: "(name \<Rightarrow> nat) \<Rightarrow> (indexname \<Rightarrow> ptyp) \<Rightarrow> env \<Rightarrow> (indexname \<Rightarrow> ptyp) \<Rightarrow> env \<Rightarrow>
    (indexname \<times> ptyp) set \<Rightarrow> bool" where
  "prunesT ar W env W' env' S \<longleftrightarrow> extends env' env \<and> maxidx env \<le> maxidx env' \<and> tinvT ar W' env' \<and>
    agreeV (maxidx env) W W' \<and>
    (\<forall>X. reach env' X \<subseteq> reach env X \<union> fr env) \<and>
    (\<forall>X. finite X \<longrightarrow> (\<forall>y\<in>X. snd (fst y) \<le> maxidx env) \<longrightarrow> card (unb env' X) \<le> card (unb env X)) \<and>
    (\<forall>t Ts T. has_type W Ts t T \<longrightarrow> below (maxidx env) t \<longrightarrow> Ms env' W' t = Ms env W t) \<and>
    (\<forall>x X. lk env x X = None \<longrightarrow> lk env' x X \<noteq> None \<longrightarrow> (x, X) \<in> S \<union> fr env)"

lemma prunesT_refl: "tinvT ar W env \<Longrightarrow> prunesT ar W env W env S"
  by (auto simp: prunesT_def)

lemma prunesTD:
  assumes "prunesT ar W env W' env' S"
  shows "extends env' env" "maxidx env \<le> maxidx env'" "tinvT ar W' env'" "agreeV (maxidx env) W W'"
    "reach env' X \<subseteq> reach env X \<union> fr env"
    "finite X \<Longrightarrow> \<forall>y\<in>X. snd (fst y) \<le> maxidx env \<Longrightarrow> card (unb env' X) \<le> card (unb env X)"
    "has_type W Ts t T \<Longrightarrow> below (maxidx env) t \<Longrightarrow> Ms env' W' t = Ms env W t"
    "lk env x XT = None \<Longrightarrow> lk env' x XT \<noteq> None \<Longrightarrow> (x, XT) \<in> S \<union> fr env"
  using assms unfolding prunesT_def by blast+

lemma prunesT_mono: "prunesT ar W env W' env' S \<Longrightarrow> S \<subseteq> S' \<Longrightarrow> prunesT ar W env W' env' S'"
  unfolding prunesT_def by blast

lemma prunesT_trans:
  assumes p1: "prunesT ar W env W1 env1 S" and p2: "prunesT ar W1 env1 W2 env2 S'" and S': "S' \<subseteq> S \<union> fr env"
  shows "prunesT ar W env W2 env2 S"
proof -
  have m: "maxidx env \<le> maxidx env1" "maxidx env1 \<le> maxidx env2" using p1 p2 by (simp_all add: prunesT_def)
  note f = fr_mono[OF m(1)]
  have "reach env2 X \<subseteq> reach env X \<union> fr env" for X
    using prunesTD(5)[OF p1, of X] prunesTD(5)[OF p2, of X] f by blast
  moreover have "card (unb env2 X) \<le> card (unb env X)"
    if "finite X" "\<forall>y\<in>X. snd (fst y) \<le> maxidx env" for X
  proof -
    have "\<forall>y\<in>X. snd (fst y) \<le> maxidx env1" using that(2) m(1) by force
    with prunesTD(6)[OF p1 that] prunesTD(6)[OF p2 that(1)] show ?thesis by linarith
  qed
  moreover have "Ms env2 W2 t = Ms env W t" if "has_type W Ts t T" "below (maxidx env) t" for t Ts T
  proof -
    have "has_type W1 Ts t T" by (rule has_type_agreeV[OF that prunesTD(4)[OF p1]])
    moreover have "below (maxidx env1) t" using that(2) m(1) by (rule below_mono)
    ultimately show ?thesis using prunesTD(7)[OF p1 that] prunesTD(7)[OF p2] by simp
  qed
  moreover have "(x, X) \<in> S \<union> fr env" if "lk env x X = None" "lk env2 x X \<noteq> None" for x X
  proof (cases "lk env1 x X = None")
    case True
    with prunesTD(8)[OF p2 True that(2)] S' f show ?thesis by blast
  next
    case False
    with prunesTD(8)[OF p1 that(1)] show ?thesis by blast
  qed
  moreover have "agreeV (maxidx env) W W2"
    using agreeV_trans[OF prunesTD(4)[OF p1] prunesTD(4)[OF p2] m(1)] .
  ultimately show ?thesis using p1 p2 m unfolding prunesT_def by (auto intro: extends_trans)
qed

lemma has_type_vps: "has_type V Ts u U \<Longrightarrow> (y, T) \<in> vps u \<Longrightarrow> V y = T"
  by (induction rule: has_type.induct) auto

lemma prune_stepT:
  assumes ti: "tinvT ar W env"
    and gv: "genvar a env Hty = (env1, H)" and upd: "ok (update (G, Gty) u env1) env2"
    and u: "ok (mkabs binders js (app H ks)) u" and ks: "\<forall>k\<in>set ks. 0 \<le> k"
    and T: "Gty = foldr fun_type Us U" "length Us = length js"
      "Hty = foldr fun_type Vs U" "length Vs = length ks"
    and G: "snd G \<le> maxidx env"
    and wf2: "wf_env ar env2" and ety2: "env_typed W' env2" and ag: "agreeV (maxidx env) W W'"
  shows "prunesT ar W env W' env2 {(G, Gty)}"
proof -
  note t0 = tinvTD[OF ti]
  have fr: "fresh_env env" by (rule t0(4))
  define m where "m = maxidx env"
  define Hn where "Hn = (a, m + 1)"
  note g = genvar_simps[OF gv, folded m_def]
  note up = ok_update[OF upd]
  have H: "H = Var Hn Hty" using g(4) by (simp add: Hn_def)
  have G0: "vt_lookup (tenv env) G = None" using up(1) g(1) by simp
  have t2: "tenv env2 = vt_update (G, (Gty, u)) (tenv env)" using up(2) g(1) by simp
  have vu: "vps u = {(Hn, Hty)}" using vps_mkabs[OF u] H by simp
  have m1: "m < snd Hn" by (simp add: Hn_def)
  have lH: "lk env Hn Hty = None" using lk_fresh[OF fr] m1 by (simp add: m_def)
  have rH: "reach env (vps u) = {(Hn, Hty)}" using vu reach_unbound[OF lH] by simp
  have GH: "(G, Gty) \<notin> reach env (vps u)" using rH G m1 by (auto simp: m_def)
  have d2: "dep env2 = dep env \<union> (\<lambda>y. (y, (G, Gty))) ` vps u" by (rule dep_update[OF t2 G0])
  have ac2: "acyc env2" using acyclic_update[OF d2 GH] t0(1) by (simp add: acyc_def)
  have mx2: "maxidx env2 = m + 1" using up(4) g(3) by simp
  have fr2: "fresh_env env2"
    unfolding fresh_env_def
  proof (intro allI impI)
    fix x U' u' assume "vt_lookup (tenv env2) x = Some (U', u')"
    then consider "x = G" "u' = u" | "vt_lookup (tenv env) x = Some (U', u')"
      using t2 by (auto split: if_splits)
    then show "snd x \<le> maxidx env2 \<and> below (maxidx env2) u'"
    proof cases
      case 1
      have "vars u = {Hn}" using vars_mkabs[OF u] H by (simp add: vars_app)
      with 1 G show ?thesis by (simp add: mx2 below_def m_def Hn_def)
    next
      case 2
      from fresh_envD[OF fr 2] show ?thesis by (auto simp: mx2 m_def intro: below_mono)
    qed
  qed
  have ext: "extends env2 env"
    using ok_update_extends[OF upd] genvar_extends[OF gv] by (rule extends_trans)
  have lk2: "lk env2 x X = (if x = G then (if X = Gty then Some u else None) else lk env x X)" for x X
    by (simp add: lk_update[OF t2])
  have r2: "reach env2 X = reach env X \<union> (if (G, Gty) \<in> reach env X then {(Hn, Hty)} else {})" for X
    using reach_update[OF d2 GH] rH by simp
  have u2: "unb env2 X = (unb env X - {(G, Gty)}) \<union> (if (G, Gty) \<in> reach env X then {(Hn, Hty)} else {})"
    for X
  proof -
    have "unb env (vps u) = {(Hn, Hty)}" using rH lH by (auto simp: unb_def)
    then show ?thesis using unb_update[OF t2 G0 GH] by simp
  qed
  have "card (unb env2 X) \<le> card (unb env X)"
    if X: "finite X" "\<forall>y\<in>X. snd (fst y) \<le> maxidx env" for X
  proof -
    have fu: "finite (unb env X)" by (rule finite_unb[OF fin_env X(1)])
    have nH: "(Hn, Hty) \<notin> unb env X"
    proof
      assume "(Hn, Hty) \<in> unb env X"
      then have "(Hn, Hty) \<in> reach env X" by (simp add: unb_def)
      from reach_old[OF fr X(2) this] m1 show False by (simp add: m_def)
    qed
    show ?thesis
    proof (cases "(G, Gty) \<in> reach env X")
      case True
      then have G1: "(G, Gty) \<in> unb env X" using G0 by (simp add: unb_def lk_def)
      have "card (unb env2 X) = card (insert (Hn, Hty) (unb env X - {(G, Gty)}))" using True by (simp add: u2)
      also have "\<dots> = Suc (card (unb env X - {(G, Gty)}))" using fu nH by simp
      also have "\<dots> = card (unb env X)" by (rule card_Suc_Diff1[OF fu G1])
      finally show ?thesis by simp
    next
      case False
      then show ?thesis using fu by (simp add: u2 card_Diff1_le)
    qed
  qed
  moreover have "Ms env2 W' t = Ms env W t" if "has_type W Ts t T" "below (maxidx env) t" for t Ts T
  proof (rule Ms_prune[OF t0(1-4) ac2 wf2 ety2 ext ag _ that])
    show "prunes_inst W' env env2"
      unfolding prunes_inst_def
    proof (intro allI impI)
      fix y assume y: "vt_lookup (tenv env) y = None" "vt_lookup (tenv env2) y \<noteq> None"
      then have yG: "y = G" using t2 by (auto split: if_splits)
      have lkG: "vt_lookup (tenv env2) G = Some (Gty, u)" using t2 by simp
      have Hu: "vt_lookup (tenv env2) Hn = None"
        using t2 fresh_envD[OF fr, of Hn] m1 G by (cases "vt_lookup (tenv env) Hn") (auto simp: m_def)
      from env_typedD[OF ety2 lkG] have WG: "W' G = Gty" and tyu: "has_type W' [] u Gty" by auto
      have WH: "W' Hn = Hty" using has_type_vps[OF tyu] vu by simp
      have "tr u = Abs_m (length js) (dB.Var (code (AVar Hn)) \<degree>\<degree> map BVar (nats ks))"
        using ok_mkabs[OF u] H by (simp add: tr_app')
      then have "env_inst env2 (code (AVar G)) =
          Abs_m (length js) (dB.Var (code (AVar Hn)) \<degree>\<degree> map BVar (nats ks))"
        by (simp add: inst_bound[OF ac2 wf2 ety2 lkG] inst_unbound[OF ac2 wf2 ety2 Hu] comp_def)
      moreover have "ty_arity (trty (W' G)) = length js + ty_arity (trty U)"
        using WG T by (simp add: trty_foldr ty_arity_funs)
      moreover have "ty_arity (trty (W' Hn)) = length (nats ks) + ty_arity (trty U)"
        using WH T by (simp add: trty_foldr ty_arity_funs)
      ultimately show "\<exists>H ks m a. env_inst env2 (code (AVar y)) = Abs_m m (dB.Var (code (AVar H)) \<degree>\<degree> map BVar ks) \<and>
          vt_lookup (tenv env2) H = None \<and> ty_arity (trty (W' y)) = m + a \<and> ty_arity (trty (W' H)) = length ks + a"
        using yG Hu by blast
    qed
  qed
  moreover have "reach env2 X \<subseteq> reach env X \<union> fr env" for X
    using r2 m1 by (auto simp: fr_def m_def)
  moreover have "(x, X) \<in> {(G, Gty)} \<union> fr env" if "lk env x X = None" "lk env2 x X \<noteq> None" for x X
    using that lk2[of x X] by (auto split: if_splits)
  moreover have "tinvT ar W' env2" using ac2 wf2 ety2 fr2 by (simp add: tinvT_def)
  ultimately show ?thesis using ext mx2 ag by (simp add: prunesT_def m_def)
qed


subsection ‹Termination of projections›

lemma nat_of_integer_succ: "0 ≤ d ⟹ nat_of_integer (d + 1) = Suc (nat_of_integer d)"
  by (simp add: integer_eq_iff nat_of_integer_add)

lemma pr_termT:
  "Ms env W s = n ⟹ tinvT ar W env ⟹ has_type W (map snd binders) s T ⟹ typs_ok ar s ⟹
    below (maxidx env) s ⟹ binders_ok ar binders ⟹ 0 ≤ d ⟹ nat_of_integer d ≤ length binders ⟹
    ∀x∈set xs. 0 ≤ x ∧ nat_of_integer d + nat_of_integer x < length binders ⟹
    ∃r. pr xs s env d binders = Some r ∧
      (∀s' env'. r = Ok (s', env') ⟶ (∃W'. prunesT ar W env W' env' (reach env (vps s))) ∧
        vps s' ⊆ reach env' (vps s) ∧ below (maxidx env') s')"
proof (induction n arbitrary: s env W d binders T rule: less_induct)
  case (less n s env W d binders T)
  have pz: "Ms env W s = n" and ti: "tinvT ar W env" and tys: "has_type W (map snd binders) s T"
    and ts: "typs_ok ar s" and bs: "below (maxidx env) s" and bok: "binders_ok ar binders"
    and d0: "0 ≤ d" and dl: "nat_of_integer d ≤ length binders"
    and xs0: "∀x∈set xs. 0 ≤ x ∧ nat_of_integer d + nat_of_integer x < length binders"
    using less.prems by simp_all
  note t0 = tinvTD[OF ti]
  have e: "vt_is_empty (tyenv env)" by (rule wf_envD(1)[OF t0(2)])
  have ps: "proper s" by (rule has_type_proper[OF tys])
  from head_norm_term_typed[OF t0(1-3) tys] obtain s0 where ok: "head_norm env s = Some (Ok s0)" by blast
  define R where "R = (λs0. if is_Abs s0 then
        (case s0 of
          pterm.Abs a T t ⇒ do {(t', env') ← pr xs t env (d + 1) ((a, T) # binders);
            return (pterm.Abs a T t', env')}
        | _ ⇒ raise (Failure (STR ''pr'')))
      else
        (let (h, ts) = strip_comb s0 in
          if is_Var h then
            (case h of
              pterm.Var F Fty ⇒ do {
                js ← ints_of' env ts;
                js' ← mapM (try_trans xs d) js;
                let ks = mk_proj_list js';
                let ls = List.map_filter id js';
                Hty ← type_of_G env Fty (ilength js) ks;
                let (env', H) = genvar (fst F) env Hty;
                t ← mk_hnf binders js H ks;
                env'' ← update (F, Fty) t env';
                return (app H ls, env'')}
            | _ ⇒ raise (Failure (STR ''pr'')))
          else if is_Abs h then raise Pattern
          else do {
            h' ← (case h of Bound i ⇒ do {j ← trans xs d i; return (Bound j)} | _ ⇒ return h);
            (ts', env') ← mapAccM (λs env. pr xs s env d binders) ts env;
            return (list_comb h' ts', env')}))"
  define P where "P r ⟷ (∀s' env'. r = Ok (s', env') ⟶ (∃W'. prunesT ar W env W' env' (reach env (vps s))) ∧
    vps s' ⊆ reach env' (vps s) ∧ below (maxidx env') s')" for r
  have pr_hn: "pr xs s env d binders = head_norm env s ⤜ R"
    unfolding R_def by (subst pr.simps) (rule refl)
  have hh: "head_norm env s = return s0" using ok by (simp add: return_def)
  have pr_eq: "pr xs s env d binders = R s0" by (simp add: pr_hn hh)
  have vs0: "vps s0 ⊆ reach env (vps s)" by (rule hn_vps[OF head_norm_hn[OF ok e refl]])
  have tys0: "has_type W (map snd binders) s0 T" by (rule head_norm_typed[OF ok refl t0(2,3) tys])
  have pz0: "Ms env W s0 = n" using Ms_head_norm[OF t0(1-3) ok ps tys] pz by simp
  from head_norm_sound[OF ok refl t0(2) ps ts] have ts0: "typs_ok ar s0" by simp
  have bs0: "below (maxidx env) s0" by (rule below_head_norm[OF ok refl t0(2,4) bs])
  have vmono: "reach env' (vps s0) ⊆ reach env' (vps s)" if "extends env' env" for env'
    using vs0 reach_extends[OF that] by (intro reach_mono) blast
  have rmono: "reach env (vps x) ⊆ reach env (vps s)" if "vps x ⊆ vps s0" for x
    using that vs0 by (intro reach_mono) blast
  have "∃r. pr xs s env d binders = Some r ∧ P r"
  proof (cases "is_Abs s0")
    case True
    then obtain a U t where s0: "s0 = Abs a U t" by (cases s0) auto
    from tys0 s0 obtain V where tyt: "has_type W (U # map snd binders) t V" by (auto elim: has_type_elims)
    have m: "Ms env W t + 2 = n" using Ms_Abs[OF t0(1-3) tys0[unfolded s0]] pz0 s0 by simp
    have tt: "typs_ok ar t" "ground ar U" using ts0 s0 by simp_all
    have bt: "below (maxidx env) t" using bs0 s0 by simp
    have bok': "binders_ok ar ((a, U) # binders)" using bok tt(2) by (simp add: binders_ok_def)
    have d1: "0 ≤ d + 1" "nat_of_integer (d + 1) ≤ length ((a, U) # binders)"
      using d0 dl by (simp_all add: nat_of_integer_succ)
    have xs1: "∀x∈set xs. 0 ≤ x ∧ nat_of_integer (d + 1) + nat_of_integer x < length ((a, U) # binders)"
      using xs0 d0 by (simp add: nat_of_integer_succ)
    from less.IH[OF _ refl ti _ tt(1) bt bok' d1 xs1, of V] m tyt
    obtain r where r: "pr xs t env (d + 1) ((a, U) # binders) = Some r"
      and rP: "∀s' env'. r = Ok (s', env') ⟶ (∃W'. prunesT ar W env W' env' (reach env (vps t))) ∧
        vps s' ⊆ reach env' (vps t) ∧ below (maxidx env') s'"
      by auto
    show ?thesis
    proof (cases r)
      case (Ok p)
      obtain t' env' where p: "p = (t', env')" by force
      with rP Ok obtain W' where pr1: "prunesT ar W env W' env' (reach env (vps t))"
        and v1: "vps t' ⊆ reach env' (vps t)" and b1: "below (maxidx env') t'" by auto
      have "prunesT ar W env W' env' (reach env (vps s))" using pr1 rmono[of t] s0 by (auto intro: prunesT_mono)
      moreover have "vps (Abs a U t') ⊆ reach env' (vps s)"
        using v1 vmono[OF prunesTD(1)[OF pr1]] s0 by auto
      ultimately have "P (Ok (Abs a U t', env'))" using b1 by (auto simp: P_def)
      with pr_eq r Ok p s0 show ?thesis by (simp add: R_def return_def bindM_def)
    next
      case (Err e')
      with pr_eq r s0 show ?thesis by (simp add: R_def bindM_def P_def)
    qed
  next
    case nA: False
    obtain h ts where sc: "strip_comb s0 = (h, ts)" by force
    have s0e: "s0 = list_comb h ts" by (rule strip_comb_list_comb[OF sc])
    have nApp: "¬ (∃f u. h = f $ u)" by (rule strip_comb_head[OF sc])
    from tys0 s0e obtain Us where tyh: "has_type W (map snd binders) h (foldr fun_type Us T)"
      and tyts: "list_all2 (has_type W (map snd binders)) ts Us"
      by (auto simp: has_type_list_comb)
    have tts': "∀t∈set ts. ∃U. has_type W (map snd binders) t U"
      using tyts by (metis in_set_conv_nth list_all2_conv_all_nth)
    consider (flex) F Fty where "h = Var F Fty" | (abs) "is_Abs h" | (rigid) "is_rigid h"
      using nApp has_type_proper[OF tyh] by (cases h) (auto simp: is_rigid_def)
    then show ?thesis
    proof cases
      case abs
      with nA sc have "R s0 = raise Pattern" by (cases h) (simp_all add: R_def)
      with pr_eq show ?thesis by (simp add: raise_def P_def)
    next
      case flex
      have trm: "∃r. R s0 = Some r"
        using nA sc flex unfolding R_def
        by (auto simp: Let_def mk_hnf_def split: prod.splits
            intro!: bindM_term ints_of'_termT[OF t0(1-3) tts'] mapM_term try_trans_term type_of_G_term[OF e]
              mkabs_term update_term)
      then obtain r where r: "R s0 = Some r" by blast
      have "P r"
        unfolding P_def
      proof (intro allI impI)
        fix s' env'' assume rOk: "r = Ok (s', env'')"
        with r nA sc flex obtain js js' Hty where js: "ok (ints_of' env ts) js"
          and js': "ok (mapM (try_trans xs d) js) js'"
          and Hty: "ok (type_of_G env Fty (ilength js) (mk_proj_list js')) Hty"
          and rest2: "ok (case genvar (fst F) env Hty of (env1, H) ⇒
            mk_hnf binders js H (mk_proj_list js') ⤜ (λt. update (F, Fty) t env1 ⤜
              (λenv''. return (app H (List.map_filter id js'), env'')))) (s', env'')"
          unfolding R_def by (auto simp: Let_def)
        obtain env1 H where G: "genvar (fst F) env Hty = (env1, H)" by force
        with rest2 obtain t where t: "ok (mkabs binders js (app H (mk_proj_list js'))) t"
          and env'': "ok (update (F, Fty) t env1) env''" and s': "s' = app H (List.map_filter id js')"
          by (auto simp: mk_hnf_def)
        have prs: "pr xs s env d binders = Some (Ok (s', env''))" using pr_eq r rOk by simp
        from pr_exn[OF prs t0(2) bok t0(3,4) ps ts tys bs d0 dl xs0] obtain W'' where
          te: "ty_ext ar W env W'' env''" by auto
        note te' = te[unfolded ty_ext_def]
        from ok_type_of_G'[OF Hty e] obtain Us' U Vs where
          T: "Fty = foldr fun_type Us' U" "length Us' = length js"
            "Hty = foldr fun_type Vs U" "length Vs = length (mk_proj_list js')"
            and ks: "∀k∈set (mk_proj_list js'). 0 ≤ k"
          by auto
        have Fm: "snd F ≤ maxidx env" using bs0 s0e flex by (simp add: below_list_comb)
        have p1: "prunesT ar W env W'' env'' {(F, Fty)}"
          by (rule prune_stepT[OF ti G env'' t ks T Fm]) (use te' in simp_all)
        have Fr: "(F, Fty) ∈ reach env (vps s)" using vs0 s0e flex by (auto simp: vps_list_comb)
        have "prunesT ar W env W'' env'' (reach env (vps s))" using p1 Fr by (auto intro: prunesT_mono)
        moreover have "vps s' ⊆ reach env'' (vps s)"
        proof
          fix y assume "y ∈ vps s'"
          then have y: "y = ((fst F, maxidx env + 1), Hty)" using s' genvar_simps(4)[OF G] by simp
          have "lk env'' F Fty = Some t" using ok_update_lookup[OF env''] by (simp add: lk_def)
          moreover have "y ∈ vps t" using vps_mkabs[OF t] genvar_simps(4)[OF G] y by simp
          ultimately have "(y, (F, Fty)) ∈ dep env''" by (auto simp: dep_iff)
          moreover have "(F, Fty) ∈ reach env'' (vps s)"
            using Fr reach_extends[OF prunesTD(1)[OF p1]] by blast
          ultimately show "y ∈ reach env'' (vps s)" by (rule reach_pred)
        qed
        moreover have "below (maxidx env'') s'"
          using s' genvar_simps(3,4)[OF G] ok_update(4)[OF env''] by (simp add: below_app)
        ultimately show "(∃W'. prunesT ar W env W' env'' (reach env (vps s))) ∧ vps s' ⊆ reach env'' (vps s) ∧
          below (maxidx env'') s'" by blast
      qed
      with r pr_eq show ?thesis by simp
    next
      case rigid
      have nV: "¬ is_Var h" "¬ is_Abs h" using rigid by (auto simp: is_rigid_def)
      define hc where "hc = (case h of Bound i ⇒ do {j ← trans xs d i; return (Bound j)} | _ ⇒ return h)"
      have hc: "∃r. hc = Some r ∧ (∀h'. r = Ok h' ⟶ vps h' = {} ∧ vars h' = {})"
        using rigid trans_term[of xs d]
        by (auto simp: hc_def is_rigid_def return_def bindM_def split: option.splits res.splits)
      define R0 where "R0 e ⟷ (∃We. prunesT ar W env We e (reach env (vps s)))" for e
      define S0 where "S0 e e' ⟷ extends e' e ∧ maxidx e ≤ maxidx e'" for e e'
      define Q0 where "Q0 x y e' ⟷ vps y ⊆ reach e' (vps x) ∧ below (maxidx e') y" for x y e'
      have tts: "∀t∈set ts. typs_ok ar t" "∀t∈set ts. below (maxidx env) t"
        using ts0 bs0 s0e by (simp_all add: typs_ok_list_comb below_list_comb)
      have vts: "vps x ⊆ vps s0" if "x ∈ set ts" for x using that s0e by (auto simp: vps_list_comb)
      have Msum: "Ms env W s0 = 1 + sum_list (map (Ms env W) ts)"
        using Ms_rigid[OF t0(1-3) rigid tys0[unfolded s0e]] s0e by simp
      have mp: "∃r. mapAccM (λs env. pr xs s env d binders) ts env = Some r ∧
          (∀ys e'. r = Ok (ys, e') ⟶ R0 e' ∧ S0 env e' ∧ list_all2 (λx y. Q0 x y e') ts ys)"
      proof (rule Pattern_Termination.mapAccM_inv)
        fix x e assume x: "x ∈ set ts" and Re: "R0 e"
        from Re obtain We where pe: "prunesT ar W env We e (reach env (vps s))" by (auto simp: R0_def)
        from x tyts obtain Ux where tyx: "has_type W (map snd binders) x Ux"
          by (metis in_set_conv_nth list_all2_conv_all_nth)
        have bx0: "below (maxidx env) x" using tts(2) x by simp
        have "Ms env W x < n"
          using Msum pz0 x by (induction ts) (auto simp: sum_list_map_remove1[of x] dest: member_le_sum_list)
        then have m: "Ms e We x < n" using prunesTD(7)[OF pe tyx bx0] by simp
        have tyx': "has_type We (map snd binders) x Ux" by (rule has_type_agreeV[OF tyx bx0 prunesTD(4)[OF pe]])
        have bx: "below (maxidx e) x" using bx0 prunesTD(2)[OF pe] by (rule below_mono)
        from less.IH[OF m refl prunesTD(3)[OF pe] tyx' _ bx bok d0 dl xs0] tts(1) x
        obtain r where r: "pr xs x e d binders = Some r"
          and rP: "∀y e'. r = Ok (y, e') ⟶ (∃W'. prunesT ar We e W' e' (reach e (vps x))) ∧
            vps y ⊆ reach e' (vps x) ∧ below (maxidx e') y"
          by blast
        have "R0 e' ∧ S0 e e' ∧ Q0 x y e'" if "r = Ok (y, e')" for y e'
        proof -
          from rP that obtain W' where p2: "prunesT ar We e W' e' (reach e (vps x))"
            and q: "vps y ⊆ reach e' (vps x)" "below (maxidx e') y" by auto
          have "reach e (vps x) ⊆ reach env (vps s) ∪ fr env"
            using prunesTD(5)[OF pe, of "vps x"] rmono[OF vts[OF x]] by blast
          with prunesT_trans[OF pe p2] have "R0 e'" by (auto simp: R0_def)
          moreover have "S0 e e'" using prunesTD(1,2)[OF p2] by (simp add: S0_def)
          ultimately show ?thesis using q by (simp add: Q0_def)
        qed
        with r show "∃r. pr xs x e d binders = Some r ∧
          (∀y e'. r = Ok (y, e') ⟶ R0 e' ∧ S0 e e' ∧ Q0 x y e')" by blast
      next
        show "S0 e1 e3" if "S0 e1 e2" "S0 e2 e3" for e1 e2 e3
          using that by (auto simp: S0_def intro: extends_trans)
      next
        show "S0 e e" for e by (simp add: S0_def)
      next
        show "Q0 x y e2" if "Q0 x y e1" "S0 e1 e2" for x y e1 e2
          using that reach_extends[of e2 e1] by (auto simp: Q0_def S0_def intro: below_mono)
      next
        show "R0 env" using prunesT_refl[OF ti] by (auto simp: R0_def)
      qed
      from hc obtain rh where rh: "hc = Some rh" and rhP: "∀h'. rh = Ok h' ⟶ vps h' = {} ∧ vars h' = {}"
        by blast
      from mp obtain rm where rm: "mapAccM (λs env. pr xs s env d binders) ts env = Some rm"
        and rmP: "∀ys e'. rm = Ok (ys, e') ⟶ R0 e' ∧ S0 env e' ∧ list_all2 (λx y. Q0 x y e') ts ys"
        by blast
      have R_eq: "R s0 = hc ⤜ (λh'. mapAccM (λs env. pr xs s env d binders) ts env ⤜
          (λ(ts', env'). return (list_comb h' ts', env')))"
        using nA sc nV unfolding R_def hc_def by simp
      show ?thesis
      proof (cases rh)
        case (Err e')
        with R_eq rh pr_eq show ?thesis by (simp add: bindM_def P_def)
      next
        case (Ok h')
        note hv = rhP[rule_format, OF Ok]
        show ?thesis
        proof (cases rm)
          case (Err e')
          with R_eq rh rm Ok pr_eq show ?thesis by (simp add: bindM_def P_def)
        next
          case (Ok q)
          obtain ts' env' where q: "q = (ts', env')" by force
          with rmP Ok have R0': "R0 env'" and S0': "S0 env env'" and Q: "list_all2 (λx y. Q0 x y env') ts ts'"
            by auto
          have "vps (list_comb h' ts') ⊆ reach env' (vps s)"
          proof -
            have "vps y ⊆ reach env' (vps s)" if "y ∈ set ts'" for y
            proof -
              from list_all2_set2'[OF Q] that obtain x where x: "x ∈ set ts" "Q0 x y env'"
                by blast
              have e': "extends env' env" using S0' by (simp add: S0_def)
              have "reach env' (vps x) ⊆ reach env' (vps s)"
                using reach_subset[OF vts[OF x(1)], of env'] vmono[OF e'] by (rule order_trans)
              with x(2) show ?thesis by (auto simp: Q0_def)
            qed
            with hv show ?thesis by (auto simp: vps_list_comb)
          qed
          moreover have "below (maxidx env') (list_comb h' ts')"
          proof -
            have "below (maxidx env') y" if "y ∈ set ts'" for y
              using list_all2_set2'[OF Q] that by (auto simp: Q0_def)
            moreover have "below (maxidx env') h'" using hv by (simp add: below_def)
            ultimately show ?thesis by (simp add: below_list_comb)
          qed
          ultimately have "P (Ok (list_comb h' ts', env'))" using R0' by (auto simp: P_def R0_def)
          with R_eq rh rm ‹rh = Ok h'› Ok q pr_eq show ?thesis by (simp add: bindM_def return_def)
        qed
      qed
    qed
  qed
  then show ?case by (simp add: P_def)
qed

lemma proj_termT:
  assumes ti: "tinvT ar W env" and ty: "has_type W (map snd binders) t T" and ts: "typs_ok ar t"
    and bt: "below (maxidx env) t" and bok: "binders_ok ar binders"
    and is0: "∀i∈set is. 0 ≤ i ∧ nat_of_integer i < length binders"
  shows "∃r. proj t env binders is = Some r ∧
    (∀u env'. r = Ok (u, env') ⟶ (∃W'. prunesT ar W env W' env' (reach env (vps t))) ∧
      vps u ⊆ reach env' (vps t) ∧ below (maxidx env') u)"
proof (cases "downto0 is (ilength binders - 1)")
  case True
  then show ?thesis using prunesT_refl[OF ti] reach_incl[of "vps t" env] bt
    by (auto simp: proj_def return_def)
next
  case False
  have "∀x∈set is. 0 ≤ x ∧ nat_of_integer 0 + nat_of_integer x < length binders" using is0 by simp
  from pr_termT[OF refl ti ty ts bt bok _ _ this] False show ?thesis by (simp add: proj_def)
qed


subsection ‹Termination of the rigid occurs check›

lemma rigid_occurs_termT:
  assumes ti: "tinvT ar W env"
  shows "has_type W Ts t T ⟹ ∃r. rigid_occurs F t env = Some r"
proof (induction "Ms env W t" arbitrary: t Ts T rule: less_induct)
  case less
  note t0 = tinvTD[OF ti]
  from head_norm_term_typed[OF t0(1-3) less.prems] obtain t' where hn: "head_norm env t = Some (Ok t')"
    by blast
  have tyt': "has_type W Ts t' T" by (rule head_norm_typed[OF hn refl t0(2,3) less.prems])
  have pz: "Ms env W t' = Ms env W t" by (rule Ms_head_norm[OF t0(1-3) hn has_type_proper less.prems])
    (rule less.prems)
  have IH: "∃r. rigid_occurs F u env = Some r" if "has_type W Us u U" "Ms env W u < Ms env W t'" for u Us U
    using less.hyps[OF _ that(1)] that(2) pz by simp
  define B where "B = (λt'. case t' of
        pterm.Abs _ _ u ⇒ rigid_occurs F u env
      | _ ⇒
          (let (h, ts) = strip_comb t' in
            (case h of
              pterm.Var G _ ⇒
                if G = F then
                  handle (ints_of' env ts ⤜ (λ_. return True))
                    (λe. case e of Pattern ⇒ return False | _ ⇒ raise e)
                else return False
            | pterm.Abs _ _ _ ⇒ return False
            | _ ⇒ existsM (λu. rigid_occurs F u env) ts)))"
  have ro: "rigid_occurs F t env = head_norm env t ⤜ B"
    by (subst rigid_occurs.simps) (simp add: B_def)
  have "∃r. B t' = Some r"
  proof (cases "is_Abs t'")
    case True
    then obtain a U u where t'a: "t' = pterm.Abs a U u" by (cases t') auto
    from tyt' t'a obtain V where tyu: "has_type W (U # Ts) u V" by (auto elim: has_type_elims)
    have "Ms env W t' = Ms env W u + 2" using Ms_Abs[OF t0(1-3) tyt'[unfolded t'a]] t'a by simp
    with IH[OF tyu] t'a show ?thesis by (simp add: B_def)
  next
    case nA: False
    obtain h ts where sc: "strip_comb t' = (h, ts)" by force
    note t'e = strip_comb_list_comb[OF sc]
    have B: "B t' = (case h of
        pterm.Var G _ ⇒
          if G = F then
            handle (ints_of' env ts ⤜ (λ_. return True))
              (λe. case e of Pattern ⇒ return False | _ ⇒ raise e)
          else return False
      | pterm.Abs _ _ _ ⇒ return False
      | _ ⇒ existsM (λu. rigid_occurs F u env) ts)"
      using sc nA unfolding B_def by (cases t') simp_all
    from tyt' t'e obtain Us where tyh: "has_type W Ts h (foldr fun_type Us T)"
      and tyts: "list_all2 (has_type W Ts) ts Us"
      by (auto simp: has_type_list_comb)
    have tts: "∀u∈set ts. ∃U. has_type W Ts u U"
      using tyts by (metis in_set_conv_nth list_all2_conv_all_nth)
    have nApp: "¬ (∃f u. h = f $ u)" by (rule strip_comb_head[OF sc])
    consider (V) G U where "h = Var G U" | (A) "is_Abs h" | (R) "is_rigid h"
      using nApp has_type_proper[OF tyh] by (cases h) (auto simp: is_rigid_def)
    then show ?thesis
    proof cases
      case R
      have "Ms env W t' = 1 + sum_list (map (Ms env W) ts)"
        using Ms_rigid[OF t0(1-3) R tyt'[unfolded t'e]] t'e by simp
      then have "Ms env W u < Ms env W t'" if "u ∈ set ts" for u
        using member_le_sum_list[of "Ms env W u" "map (Ms env W) ts"] that by simp
      with IH tyts have "∃r. existsM (λu. rigid_occurs F u env) ts = Some r"
        by (intro existsM_term) (metis in_set_conv_nth list_all2_conv_all_nth)
      with B R show ?thesis by (cases h) (simp_all add: is_rigid_def)
    next
      case V
      from ints_of'_termT[OF t0(1-3) tts] have "∃r. handle (ints_of' env ts ⤜ (λ_. return True))
          (λe. case e of Pattern ⇒ return False | _ ⇒ raise e) = Some r"
        by (auto intro!: handle_term bindM_term split: exn.splits)
      with B V show ?thesis by simp
    next
      case A
      with B show ?thesis by (cases h) simp_all
    qed
  qed
  then show ?case using hn ro by (auto intro!: bindM_term)
qed


subsection ‹Termination of the flexible cases›

lemma flexrigid_termT:
  assumes ti: "tinvT ar W env" and tyF: "has_type W (map snd binders) (app (pterm.Var F Fty) is) T"
    and tyt: "has_type W (map snd binders) t T" and pt: "typs_ok ar t"
    and bt: "below (maxidx env) t" and Fm: "snd F ≤ maxidx env" and bok: "binders_ok ar binders"
    and gF: "ground ar Fty"
  shows "∃r. flexrigid env binders F Fty is t = Some r ∧ (∀env''. r = Ok env'' ⟶
    (∃W''. tinvT ar W'' env'' ∧ agreeV (maxidx env) W W'') ∧ extends env'' env ∧ maxidx env ≤ maxidx env'' ∧
    (∀Y. finite Y ⟶ (∀y∈Y. snd (fst y) ≤ maxidx env) ⟶ (F, Fty) ∈ unb env Y ⟶
      vps t ⊆ reach env Y ⟶ card (unb env'' Y) < card (unb env Y)))"
proof -
  note t0 = tinvTD[OF ti]
  have e: "vt_is_empty (tyenv env)" by (rule wf_envD(1)[OF t0(2)])
  have is0: "∀i∈set is. 0 ≤ i ∧ nat_of_integer i < length binders"
    using has_type_app_Var(1)[OF tyF] by simp
  have hnd: "¬ ok (case e of Unif _ ⇒ raise (Unif (Proj_Fail env binders F is t)) | _ ⇒ raise e) y"
    for e and y :: env by (cases e) simp_all
  from occurs_term[OF fin_env t0(1,2)] obtain ro where ro: "occurs F t env = Some ro" by blast
  from proj_termT[OF ti tyt pt bt bok is0] obtain rp where rp: "proj t env binders is = Some rp"
    and rpP: "∀u env'. rp = Ok (u, env') ⟶ (∃W'. prunesT ar W env W' env' (reach env (vps t))) ∧
      vps u ⊆ reach env' (vps t) ∧ below (maxidx env') u" by blast
  from rigid_occurs_termT[OF ti tyt] obtain rro where rro: "rigid_occurs F t env = Some rro" by blast
  have "∃r. flexrigid env binders F Fty is t = Some r"
    unfolding flexrigid_def using ro rp rro
    by (auto intro!: bindM_term handle_term mkabs_term update_term handler_term split: prod.splits res.splits)
  then obtain r where r: "flexrigid env binders F Fty is t = Some r" by blast
  have "(∃W''. tinvT ar W'' env'' ∧ agreeV (maxidx env) W W'') ∧ extends env'' env ∧ maxidx env ≤ maxidx env'' ∧
    (∀Y. finite Y ⟶ (∀y∈Y. snd (fst y) ≤ maxidx env) ⟶ (F, Fty) ∈ unb env Y ⟶
      vps t ⊆ reach env Y ⟶ card (unb env'' Y) < card (unb env Y))" if rOk: "r = Ok env''" for env''
  proof -
    have frg: "flexrigid env binders F Fty is t = Some (Ok env'')" using r rOk by simp
    from frg obtain u env1 u' where occ: "occurs F t env = Some (Ok False)"
      and pj: "ok (proj t env binders is) (u, env1)"
      and u': "ok (mkabs binders is u) u'" and env'': "ok (update (F, Fty) u' env1) env''"
      by (auto simp: flexrigid_def ok_handle hnd split: if_splits prod.splits)
    from rpP pj rp obtain W1 where p1: "prunesT ar W env W1 env1 (reach env (vps t))"
      and vu: "vps u ⊆ reach env1 (vps t)" and bu: "below (maxidx env1) u" by auto
    note pd = prunesTD[OF p1]
    note t1 = tinvTD[OF pd(3)]
    have F1: "vt_lookup (tenv env1) F = None" by (rule ok_update(1)[OF env''])
    have F0: "vt_lookup (tenv env) F = None"
    proof (rule ccontr)
      assume "vt_lookup (tenv env) F ≠ None"
      then obtain b where "vt_lookup (tenv env) F = Some b" by blast
      with pd(1) have "vt_lookup (tenv env1) F = Some b" unfolding extends_def by blast
      with F1 show False by simp
    qed
    have noF: "∀y∈reach env (vps t). fst y ≠ F" by (rule occurs_False[OF occ refl e F0])
    have vu': "vps u' = vps u" by (rule vps_mkabs[OF u'])
    have ru: "reach env1 (vps u') ⊆ reach env1 (vps t)" using vu vu' by (intro reach_mono) simp
    have nc: "(F, Fty) ∉ reach env1 (vps u')"
      using ru pd(5)[of "vps t"] noF Fm by (force simp: fr_def)
    have Fm1: "snd F ≤ maxidx env1" using Fm pd(2) by simp
    have bu': "below (maxidx env1) u'" using bu vars_mkabs[OF u'] by (simp add: below_def)
    note bs = bind_step[OF fin_env t1(1,4) env'' nc Fm1 bu']
    from flexrigid_exn[OF frg t0(2) bok t0(3,4) Fm gF tyF tyt has_type_proper[OF tyt] pt bt F0]
    obtain W'' where te: "ty_ext ar W env W'' env''" by blast
    note te' = te[unfolded ty_ext_def]
    have ti'': "tinvT ar W'' env''" using bs(2) te' by (simp add: tinvT_def)
    have ext: "extends env'' env" by (rule extends_trans[OF bs(4) pd(1)])
    have mx: "maxidx env ≤ maxidx env''" using bs(5) pd(2) by simp
    have "card (unb env'' Y) < card (unb env Y)"
      if Y: "finite Y" "∀y∈Y. snd (fst y) ≤ maxidx env" "(F, Fty) ∈ unb env Y" "vps t ⊆ reach env Y" for Y
    proof -
      have rY: "reach env Y ⊆ reach env1 Y" by (rule reach_extends[OF pd(1)])
      have "reach env1 (vps t) ⊆ reach env1 Y" using Y(4) rY by (intro reach_mono) blast
      with ru have uu: "unb env1 (vps u') ⊆ unb env1 Y" by (auto simp: unb_def)
      have e1: "unb env'' Y ⊆ (unb env1 Y - {(F, Fty)}) ∪ unb env1 (vps u')"
        using bs(7)[of Y] by (cases "(F, Fty) ∈ reach env1 Y") simp_all
      have e2: "(F, Fty) ∉ unb env1 (vps u')" using nc by (simp add: unb_def)
      from e1 e2 uu have sub: "unb env'' Y ⊆ unb env1 Y - {(F, Fty)}" by blast
      have F1Y: "(F, Fty) ∈ unb env1 Y" using Y(3) rY F1 by (auto simp: unb_def lk_def)
      have fin1: "finite (unb env1 Y)" by (rule finite_unb[OF fin_env Y(1)])
      have "card (unb env'' Y) ≤ card (unb env1 Y - {(F, Fty)})" using sub fin1 by (intro card_mono) auto
      also have "… < card (unb env1 Y)" by (rule card_Diff1_less[OF fin1 F1Y])
      also have "… ≤ card (unb env Y)" by (rule pd(6)[OF Y(1,2)])
      finally show ?thesis .
    qed
    with ti'' te' ext mx show ?thesis by blast
  qed
  with r show ?thesis by blast
qed

end

section \<open>Termination of \<open>SIMPL\<close>\<close>

theory Unify_Simpl_Term
  imports Unify_Simpl_Sound "Pattern_Correctness.Pattern_Term_Unif"
begin

text \<open>
  \<^const>\<open>SIMPL0\<close> and \<^const>\<open>SIMPL\<close> terminate on problems that satisfy the invariants of the
  termination proof of pattern unification (theory \<^theory>\<open>Pattern_Correctness.Pattern_Term_Unif\<close>),
  raising at most \<open>CANTUNIFY\<close>, and their results satisfy the invariants again and have the shapes
  that \<open>MATCH\<close> expects. The measure is lexicographic: the number of unbound type variables
  reachable from a finite set \<open>K\<close>, the number of unbound variables of the problem, and the size of
  the \<open>\<eta>\<close>-long \<open>\<beta>\<close>-normal form of the instances of the pairs under the most general solution of
  the type environment (the \<open>\<eta>\<close>-expansion of \<open>unify.ML\<close> keeps it, and decomposition reduces it).
\<close>

context pure_sig
begin

subsection \<open>The occurs check\<close>

text \<open>
  Every path in the dependency relation from a variable \<open>y\<close> down to \<open>v\<close> passes through a variable
  of \<open>seen\<close>:
\<close>

definition good :: "env \<Rightarrow> indexname \<Rightarrow> indexname list \<Rightarrow> indexname \<Rightarrow> bool" where
  "good env v seen y \<longleftrightarrow>
    ((v, y) \<in> (dep env)\<^sup>* \<longrightarrow> (\<exists>w\<in>set seen. (v, w) \<in> (dep env)\<^sup>* \<and> (w, y) \<in> (dep env)\<^sup>*))"

definition osafe :: "env \<Rightarrow> indexname \<Rightarrow> indexname list \<Rightarrow> pterm \<Rightarrow> indexname list \<Rightarrow> bool" where
  "osafe env v seen t s \<longleftrightarrow> (\<forall>y\<in>fst ` vars t. good env v seen y) \<and> (\<forall>w\<in>set s. good env v seen w)"

lemma good_refl: "w \<in> set seen \<Longrightarrow> good env v seen w"
  unfolding good_def by blast

lemma good_all: "\<forall>w\<in>set seen. good env v seen w"
  using good_refl by blast

lemma good_trans: "\<forall>w\<in>set s1. good env v seen w \<Longrightarrow> good env v s1 y \<Longrightarrow> good env v seen y"
  unfolding good_def by (meson rtrancl_trans)

lemma osafe_refl: "fst ` vars t = {} \<Longrightarrow> osafe env v seen t seen"
  unfolding osafe_def by (auto intro: good_refl)

lemma osafe_trans:
  assumes "osafe env v seen x s1" "osafe env v s1 f s2" "fst ` vars t \<subseteq> fst ` vars x \<union> fst ` vars f"
  shows "osafe env v seen t s2"
proof -
  have s1: "\<forall>w\<in>set s1. good env v seen w" using assms(1) by (simp add: osafe_def)
  have "good env v seen y" if "y \<in> fst ` vars t" for y
  proof -
    from that assms(3) consider "y \<in> fst ` vars x" | "y \<in> fst ` vars f" by blast
    then show ?thesis
    proof cases
      case 1
      with assms(1) show ?thesis unfolding osafe_def by blast
    next
      case 2
      with assms(2) have "good env v s1 y" unfolding osafe_def by blast
      with s1 show ?thesis by (rule good_trans)
    qed
  qed
  moreover have "good env v seen w" if "w \<in> set s2" for w
  proof -
    from that assms(2) have "good env v s1 w" by (simp add: osafe_def)
    with s1 show ?thesis by (rule good_trans)
  qed
  ultimately show ?thesis by (simp add: osafe_def)
qed

lemma good_bound:
  assumes ac: "acyc env" and b: "vt_lookup (tenv env) w = Some (U, u)" and vw: "v \<noteq> w"
    and g: "\<forall>y\<in>fst ` vars u. good env v (w # seen) y"
  shows "good env v seen w"
  unfolding good_def
proof
  assume "(v, w) \<in> (dep env)\<^sup>*"
  with vw have "(v, w) \<in> (dep env)\<^sup>+" by (meson rtranclD)
  then obtain y where vy: "(v, y) \<in> (dep env)\<^sup>*" and yw: "(y, w) \<in> dep env" by (meson tranclD2)
  from yw b have yu: "y \<in> fst ` vars u" by (auto elim!: depE) (metis fst_conv image_eqI)
  from g yu vy obtain w' where w': "w' \<in> set (w # seen)" "(v, w') \<in> (dep env)\<^sup>*" "(w', y) \<in> (dep env)\<^sup>*"
    unfolding good_def by blast
  show "\<exists>w'\<in>set seen. (v, w') \<in> (dep env)\<^sup>* \<and> (w', w) \<in> (dep env)\<^sup>*"
  proof (cases "w' = w")
    case True
    with w'(3) yw have "(w, w) \<in> (dep env)\<^sup>+" by (meson rtrancl_into_trancl1)
    with ac show ?thesis unfolding acyc_def acyclic_def by (cases w) blast
  next
    case False
    with w' yw show ?thesis by (meson rtrancl.rtrancl_into_rtrancl set_ConsD)
  qed
qed

abbreviation bset :: "env \<Rightarrow> indexname set" where
  "bset env \<equiv> {x. vt_lookup (tenv env) x \<noteq> None}"

lemma card_bset_less:
  "w \<notin> set seen \<Longrightarrow> vt_lookup (tenv env) w \<noteq> None \<Longrightarrow>
    card (bset env - set (w # seen)) < card (bset env - set seen)"
  by (rule psubset_card_mono) (use finite_vt_lookup[of "tenv env"] in auto)

lemma card_bset_mono: "set seen \<subseteq> set s \<Longrightarrow> card (bset env - set s) \<le> card (bset env - set seen)"
  by (rule card_mono) (use finite_vt_lookup[of "tenv env"] in auto)

context
  fixes env assumes ac: "acyc env" and tac: "tacyc (tyenv env)" and tc: "tcons_env (tyenv env)"
begin

lemma lookup_vok:
  "vok env (vars (Var x T) \<union> evars env) \<Longrightarrow> lookup env x T = return (map_option snd (vt_lookup (tenv env) x))"
  by (rule lookup_ok[OF tac tc]) (auto intro: vok_mono)

lemma occur_term:
  "card (bset env - set seen) \<le> k \<Longrightarrow> vok env (vars t \<union> evars env) \<Longrightarrow>
    \<exists>b s. occur t env v seen = return (b, s) \<and> set seen \<subseteq> set s \<and> (\<not> b \<longrightarrow> osafe env v seen t s)"
proof (induction k arbitrary: t seen rule: less_induct)
  case (less k)
  show ?case using less.prems
  proof (induction t arbitrary: seen)
    case (Var w T)
    have lk: "lookup env w T = return (map_option snd (vt_lookup (tenv env) w))" by (rule lookup_vok[OF Var.prems(2)])
    show ?case
    proof (cases "w \<in> set seen")
      case True
      then show ?thesis by (subst occur.simps) (auto simp: osafe_def intro: good_refl)
    next
      case nseen: False
      show ?thesis
      proof (cases "v = w")
        case True
        with nseen show ?thesis by (subst occur.simps) auto
      next
        case vw: False
        show ?thesis
        proof (cases "vt_lookup (tenv env) w")
          case None
          have "good env v seen w"
            unfolding good_def using vw None dep_bound by (metis rtranclD)
          then have "osafe env v seen (Var w T) (w # seen)" by (auto simp: osafe_def intro: good_refl)
          then show ?thesis using nseen vw None lk by (subst occur.simps) auto
        next
          case (Some b)
          obtain U u where b: "b = (U, u)" by force
          have lt: "card (bset env - set (w # seen)) < k"
            using card_bset_less[OF nseen, of env] Some Var.prems(1) by simp
          have vu: "vok env (vars u \<union> evars env)" by (rule vok_binding[OF Var.prems(2) Some[unfolded b]])
          from less.IH[OF lt order_refl vu] obtain b' s where
            r: "occur u env v (w # seen) = return (b', s)" "set (w # seen) \<subseteq> set s"
              "\<not> b' \<longrightarrow> osafe env v (w # seen) u s"
            by blast
          have "osafe env v seen (Var w T) s" if nb: "\<not> b'"
          proof -
            from r(3) nb have o: "\<forall>y\<in>fst ` vars u. good env v (w # seen) y" "\<forall>x\<in>set s. good env v (w # seen) x"
              by (simp_all add: osafe_def)
            have gw: "good env v seen w" by (rule good_bound[OF ac Some[unfolded b] vw o(1)])
            have gs: "\<forall>x\<in>set (w # seen). good env v seen x" using gw by (auto intro: good_refl)
            show ?thesis using gw o(2) good_trans[OF gs] by (simp add: osafe_def)
          qed
          then show ?thesis using nseen vw Some b lk r(1,2) by (subst occur.simps) auto
        qed
      qed
    qed
  next
    case (Abs a T body)
    from Abs.IH[of seen] Abs.prems show ?case by (subst occur.simps) (simp add: osafe_def)
  next
    case (App f u)
    from App.IH(2)[of seen] App.prems obtain b1 s1 where
      r1: "occur u env v seen = return (b1, s1)" "set seen \<subseteq> set s1" "\<not> b1 \<longrightarrow> osafe env v seen u s1"
      by (auto intro: vok_mono)
    show ?case
    proof (cases b1)
      case True
      with r1 show ?thesis by (subst occur.simps) auto
    next
      case False
      from App.IH(1)[of s1] App.prems card_bset_mono[OF r1(2), of env] obtain b2 s2 where
        r2: "occur f env v s1 = return (b2, s2)" "set s1 \<subseteq> set s2" "\<not> b2 \<longrightarrow> osafe env v s1 f s2"
        by (fastforce intro: vok_mono)
      have "\<not> b2 \<longrightarrow> osafe env v seen (f $ u) s2"
        using r1(3) r2(3) False osafe_trans[of env v seen u s1 f s2 "f $ u"] by auto
      with r1 r2 False show ?thesis by (subst occur.simps) auto
    qed
  qed (subst occur.simps; auto simp: osafe_def intro: good_refl)+
qed

lemma nonrigid_term:
  "vok env (vars t \<union> evars env) \<Longrightarrow>
    \<exists>r. nonrigid env v seen t = return r \<and> set seen \<subseteq> set (snd r) \<and> (fst r = NoOcc \<longrightarrow> osafe env v seen t (snd r))"
proof -
  assume vk: "vok env (vars t \<union> evars env)"
  from occur_term[where seen = seen and v = v, OF order_refl vk] obtain b s where
    "occur t env v seen = return (b, s)" "set seen \<subseteq> set s" "\<not> b \<longrightarrow> osafe env v seen t s" by blast
  then show ?thesis by (auto simp: nonrigid_def)
qed

lemma head_of_in_term: "vok env (vars t \<union> evars env) \<Longrightarrow> \<exists>h. head_of_in env t = return h"
proof (induction t rule: wf_induct_rule[OF wf_inv_image[OF wf_lex_prod[OF wf_less_than wf_less_than],
    of "\<lambda>t. (size (unf env t), case t of Var x T \<Rightarrow> Suc (rk env x) | _ \<Rightarrow> 0)"]])
  case (1 t)
  note IH = "1.IH"[simplified, rule_format]
  show ?case
  proof (cases t)
    case (Var G T)
    have lk: "lookup env G T = return (map_option snd (vt_lookup (tenv env) G))"
      by (rule lookup_vok) (use "1.prems" Var in simp)
    show ?thesis
    proof (cases "vt_lookup (tenv env) G")
      case None
      then show ?thesis using lk Var by (subst head_of_in.simps) simp
    next
      case (Some b)
      obtain U u where b: "b = (U, u)" by force
      have u: "unf env (Var G T) = unf env u" using Some b by (simp add: unf_Var[OF ac])
      have "rank": "(case u of Var x T \<Rightarrow> Suc (rk env x) | _ \<Rightarrow> 0) < Suc (rk env G)"
      proof (cases u)
        case (Var y U')
        have "(y, G) \<in> dep env" using depI[OF Some[unfolded b], of y U'] Var by simp
        then show ?thesis using rk_less[OF ac] Var by simp
      qed simp_all
      obtain h where "head_of_in env u = return h"
        using IH[of u] u "rank" Var vok_binding[OF "1.prems"[unfolded Var] Some[unfolded b]] by auto
      then show ?thesis using lk Var Some b by (subst head_of_in.simps) simp
    qed
  next
    case (App f u)
    obtain h where "head_of_in env f = return h"
      using IH[of f] "1.prems" App by (auto intro: vok_mono)
    then show ?thesis using App by (subst head_of_in.simps) simp
  qed (subst head_of_in.simps, simp)+
qed

lemma occomb_term:
  assumes H: "\<And>s seen'. size s < size t0 \<Longrightarrow> set seen0 \<subseteq> set seen' \<Longrightarrow> vok env (vars s \<union> evars env) \<Longrightarrow>
      \<exists>r. oc seen' s = return r \<and> set seen' \<subseteq> set (snd r) \<and> (fst r = NoOcc \<longrightarrow> osafe env v seen' s (snd r))"
  shows "size t \<le> size t0 \<Longrightarrow> (\<exists>f u. t = f $ u) \<or> size t < size t0 \<Longrightarrow> set seen0 \<subseteq> set seen \<Longrightarrow>
    vok env (vars t \<union> evars env) \<Longrightarrow>
    \<exists>r. occomb oc seen t = return r \<and> set seen \<subseteq> set (snd r) \<and> (fst r = NoOcc \<longrightarrow> osafe env v seen t (snd r))"
proof (induction t arbitrary: seen)
  case (App f x)
  have x: "size x < size t0" "vok env (vars x \<union> evars env)" using App.prems(1,4) by (auto intro: vok_mono)
  from H[OF x(1) App.prems(3) x(2)] obtain r1 where
    r1: "oc seen x = return r1" "set seen \<subseteq> set (snd r1)" "fst r1 = NoOcc \<longrightarrow> osafe env v seen x (snd r1)"
    by blast
  show ?case
  proof (cases "fst r1 = Rigid")
    case True
    then show ?thesis using r1 by simp
  next
    case False
    from App.IH(1)[of "snd r1"] App.prems r1(2) obtain r2 where
      r2: "occomb oc (snd r1) f = return r2" "set (snd r1) \<subseteq> set (snd r2)"
        "fst r2 = NoOcc \<longrightarrow> osafe env v (snd r1) f (snd r2)"
      by (fastforce intro: vok_mono)
    have "(if fst r2 = NoOcc then fst r1 else fst r2) = NoOcc \<longrightarrow> osafe env v seen (f $ x) (snd r2)"
      using r1(3) r2(3) osafe_trans[of env v seen x "snd r1" f "snd r2" "f $ x"] by (auto split: if_splits)
    then show ?thesis using r1 r2 False by auto
  qed
qed (use H in fastforce)+

lemma rocc_term:
  "card (bset env - set seen) \<le> k \<Longrightarrow> vok env (vars t \<union> evars env) \<Longrightarrow>
    \<exists>r. rocc t env v seen = return r \<and> set seen \<subseteq> set (snd r) \<and> (fst r = NoOcc \<longrightarrow> osafe env v seen t (snd r))"
proof (induction k arbitrary: t seen rule: less_induct)
  case (less k)
  show ?case using less.prems
  proof (induction "size t" arbitrary: t seen rule: less_induct)
    case less2: less
    show ?case
    proof (cases t)
      case (Var w T)
      have lk: "lookup env w T = return (map_option snd (vt_lookup (tenv env) w))"
        by (rule lookup_vok) (use less2.prems(2) Var in simp)
      show ?thesis
      proof (cases "w \<in> set seen")
        case True
        then show ?thesis using Var by (subst rocc.simps) (auto simp: osafe_def intro: good_refl)
      next
        case nseen: False
        show ?thesis
        proof (cases "v = w")
          case True
          with nseen Var show ?thesis by (subst rocc.simps) simp
        next
          case vw: False
          show ?thesis
          proof (cases "vt_lookup (tenv env) w")
            case None
            have "good env v seen w"
              unfolding good_def using vw None dep_bound by (metis rtranclD)
            then have "osafe env v seen (Var w T) (w # seen)" by (auto simp: osafe_def intro: good_refl)
            then show ?thesis using nseen vw None lk Var by (subst rocc.simps) auto
          next
            case (Some b)
            obtain U u where b: "b = (U, u)" by force
            have lt: "card (bset env - set (w # seen)) < k"
              using card_bset_less[OF nseen, of env] Some less2.prems(1) by simp
            have vu: "vok env (vars u \<union> evars env)"
              by (rule vok_binding[OF less2.prems(2)[unfolded Var] Some[unfolded b]])
            from less.IH[OF lt order_refl vu] obtain r where
              r: "rocc u env v (w # seen) = return r" "set (w # seen) \<subseteq> set (snd r)"
                "fst r = NoOcc \<longrightarrow> osafe env v (w # seen) u (snd r)"
              by blast
            have "osafe env v seen (Var w T) (snd r)" if nb: "fst r = NoOcc"
            proof -
              from r(3) nb have o: "\<forall>y\<in>fst ` vars u. good env v (w # seen) y"
                "\<forall>x\<in>set (snd r). good env v (w # seen) x"
                by (simp_all add: osafe_def)
              have gw: "good env v seen w" by (rule good_bound[OF ac Some[unfolded b] vw o(1)])
              have gs: "\<forall>x\<in>set (w # seen). good env v seen x" using gw by (auto intro: good_refl)
              show ?thesis using gw o(2) good_trans[OF gs] by (simp add: osafe_def)
            qed
            then show ?thesis using nseen vw Some b lk r(1,2) Var by (subst rocc.simps) auto
          qed
        qed
      qed
    next
      case (Abs a T body)
      from less2.hyps[of body seen] less2.prems Abs show ?thesis
        by (subst rocc.simps) (simp add: osafe_def)
    next
      case (App f u)
      have vf: "vok env (vars f \<union> evars env)" using less2.prems App by (auto intro: vok_mono)
      from head_of_in_term[OF vf] obtain h where hd: "head_of_in env f = return h" by blast
      have nr: "\<exists>r. nonrigid env v seen t = return r \<and> set seen \<subseteq> set (snd r) \<and>
          (fst r = NoOcc \<longrightarrow> osafe env v seen t (snd r))"
        by (rule nonrigid_term[OF less2.prems(2)])
      have oc: "\<exists>r. occomb (\<lambda>seen t. rocc t env v seen) seen t = return r \<and> set seen \<subseteq> set (snd r) \<and>
          (fst r = NoOcc \<longrightarrow> osafe env v seen t (snd r))"
      proof (rule occomb_term[where t0 = t and seen0 = seen])
        fix s seen' assume s: "size s < size t" "set seen \<subseteq> set seen'" "vok env (vars s \<union> evars env)"
        have "card (bset env - set seen') \<le> k" using card_bset_mono[OF s(2), of env] less2.prems by simp
        from less2.hyps[OF s(1) this s(3)]
        show "\<exists>r. rocc s env v seen' = return r \<and> set seen' \<subseteq> set (snd r) \<and>
            (fst r = NoOcc \<longrightarrow> osafe env v seen' s (snd r))" .
      qed (use App less2.prems in auto)
      show ?thesis
      proof (cases h)
        case (Var x U)
        then show ?thesis using hd nr oc App by (subst rocc.simps) auto
      next
        case (Abs a T b)
        then show ?thesis using hd nr App by (subst rocc.simps) auto
      qed (use hd oc App in \<open>subst rocc.simps, auto simp del: occomb.simps\<close>)+
    qed (subst rocc.simps; rule exI[of _ "(NoOcc, seen)"]; simp add: osafe_def good_refl)+
  qed
qed

text \<open>The occurs check terminates; if it finds no occurrence, the variable is not reachable:\<close>

theorem rigid_occurs_term_term:
  assumes "vok env (vars t \<union> evars env)"
  shows "\<exists>oc. rigid_occurs_term env v t = return oc \<and> (oc = NoOcc \<longrightarrow> (\<forall>y\<in>fst ` vars t. (v, y) \<notin> (dep env)\<^sup>*))"
proof -
  from rocc_term[where seen = "[]" and v = v, OF order_refl assms] obtain r where
    r: "rocc t env v [] = return r" "fst r = NoOcc \<longrightarrow> osafe env v [] t (snd r)" by blast
  then show ?thesis by (auto simp: rigid_occurs_term_def osafe_def good_def)
qed

end

subsection \<open>Operations on types\<close>

text \<open>The known type variables: those of the type environment and of \<open>A\<close>.\<close>

context
  fixes \<theta> A n assumes ti: "tinv ar n \<theta> A"
begin

lemma ti_ac: "tacyc \<theta>" and ti_tc: "tcons_env \<theta>"
  using tinv_tacyc[OF ti] tinv_tcons_env[OF ti] .

lemma devar_term:
  "tvars T \<subseteq> tvars_env \<theta> \<union> A \<Longrightarrow> \<exists>U. devar \<theta> T = return U \<and> tvars U \<subseteq> tvars_env \<theta> \<union> A \<and>
    tnorm \<theta> U = tnorm \<theta> T \<and> \<not> tbound \<theta> U"
proof -
  assume tv: "tvars T \<subseteq> tvars_env \<theta> \<union> A"
  have "tcons \<theta> T \<Longrightarrow> \<exists>U. devar \<theta> T = return U \<and> tvars U \<subseteq> tvars T \<union> tvars_env \<theta>"
  proof (induction rule: tnorm_induct[OF ti_ac ti_tc, consumes 1, case_names TFree Type Unbound Bound])
    case (TFree a S)
    then show ?case by (subst devar.simps) simp
  next
    case (Type a Ts)
    then show ?case by (subst devar.simps) simp
  next
    case (Unbound v S)
    then show ?case by (subst devar.simps) (simp add: type_lookup_ok)
  next
    case (Bound v S U)
    then show ?case using tvars_envI2[OF Bound(1)] by (subst devar.simps) (auto simp: type_lookup_ok)
  qed
  from this[OF tinv_tcons[OF ti tv]] obtain U where U: "devar \<theta> T = return U" "tvars U \<subseteq> tvars T \<union> tvars_env \<theta>"
    by blast
  from devar_ok[OF ti_ac ti_tc tinv_tcons[OF ti tv]] U(1) have "tnorm \<theta> U = tnorm \<theta> T \<and> \<not> tbound \<theta> U" by auto
  with U tv show ?thesis by blast
qed

lemma body_type_term:
  "tyenv env = \<theta> \<Longrightarrow> tvars T \<subseteq> tvars_env \<theta> \<union> A \<Longrightarrow>
    \<exists>B. body_type env T = return B \<and> tvars B \<subseteq> tvars_env \<theta> \<union> A"
proof -
  assume th: "tyenv env = \<theta>" and tv: "tvars T \<subseteq> tvars_env \<theta> \<union> A"
  have "tcons \<theta> T \<Longrightarrow> \<exists>B. body_type env T = return B \<and> tvars B \<subseteq> tvars T \<union> tvars_env \<theta>"
  proof (induction rule: tnorm_induct[OF ti_ac ti_tc, consumes 1, case_names TFree Type Unbound Bound])
    case (TFree a S)
    then show ?case by (subst body_type.simps) simp
  next
    case (Type a Ts)
    show ?case
    proof (cases "a = STR ''fun'' \<and> (\<exists>T1 U. Ts = [T1, U])")
      case True
      then obtain T1 U where Ts: "Ts = [T1, U]" and a: "a = STR ''fun''" by blast
      from Type(1)[of U] Ts obtain B where "body_type env U = return B" "tvars B \<subseteq> tvars U \<union> tvars_env \<theta>"
        by auto
      then show ?thesis using Ts a by (subst body_type.simps) auto
    next
      case False
      then show ?thesis by (subst body_type.simps) (auto split: list.splits)
    qed
  next
    case (Unbound v S)
    then show ?case by (subst body_type.simps) (simp add: type_lookup_ok th)
  next
    case (Bound v S U)
    then show ?case using tvars_envI2[OF Bound(1)] by (subst body_type.simps) (auto simp: type_lookup_ok th)
  qed
  then show ?thesis using tinv_tcons[OF ti tv] tv by blast
qed

lemma binder_types_term:
  "tyenv env = \<theta> \<Longrightarrow> tvars T \<subseteq> tvars_env \<theta> \<union> A \<Longrightarrow> \<exists>Ts. binder_types env T = return Ts"
proof -
  assume th: "tyenv env = \<theta>" and tv: "tvars T \<subseteq> tvars_env \<theta> \<union> A"
  have "tcons \<theta> T \<Longrightarrow> \<exists>Ts. binder_types env T = return Ts"
  proof (induction rule: tnorm_induct[OF ti_ac ti_tc, consumes 1, case_names TFree Type Unbound Bound])
    case (TFree a S)
    then show ?case by (subst binder_types.simps) simp
  next
    case (Type a Ts)
    show ?case
    proof (cases "a = STR ''fun'' \<and> (\<exists>T1 U. Ts = [T1, U])")
      case True
      then obtain T1 U where Ts: "Ts = [T1, U]" and a: "a = STR ''fun''" by blast
      from Type(1)[of U] Ts obtain Us where "binder_types env U = return Us" by auto
      then show ?thesis using Ts a by (subst binder_types.simps) auto
    next
      case False
      then show ?thesis by (subst binder_types.simps) (auto split: list.splits)
    qed
  next
    case (Unbound v S)
    then show ?case by (subst binder_types.simps) (simp add: type_lookup_ok th)
  next
    case (Bound v S U)
    then show ?case by (subst binder_types.simps) (auto simp: type_lookup_ok th)
  qed
  then show ?thesis using tinv_tcons[OF ti tv] by blast
qed

end

text \<open>The number of leading abstractions:\<close>

fun nabs :: "pterm \<Rightarrow> nat" where
  "nabs (Abs _ _ t) = Suc (nabs t)"
| "nabs _ = 0"

lemma nabs_nonAbs [simp]: "\<not> is_Abs t \<Longrightarrow> nabs t = 0"
  by (cases t) simp_all

lemma head_of_strip_comb: "head_of t = fst (strip_comb t)"
  by (induction t) (simp_all add: strip_comb_App, simp_all add: strip_comb_def)

lemma head_of_incr_bv: "head_of (incr_bv n k t) = incr_bv n k (head_of t)"
  by (induction n k t rule: incr_bv.induct) auto

text \<open>The head of a head normal form is rigid or an unbound variable:\<close>

definition ahd :: "env \<Rightarrow> pterm \<Rightarrow> bool" where
  "ahd env t \<longleftrightarrow> rigid (head_of t) \<or> (\<exists>F T. head_of t = Var F T \<and> vt_lookup (tenv env) F = None)"

fun hnf :: "env \<Rightarrow> pterm \<Rightarrow> bool" where
  "hnf env (Abs a T t) = hnf env t"
| "hnf env t = ahd env t"

lemma hnf_nonAbs: "\<not> is_Abs t \<Longrightarrow> hnf env t = ahd env t"
  by (cases t) simp_all

lemma ahd_tenv: "tenv env' = tenv env \<Longrightarrow> ahd env' t = ahd env t"
  by (simp add: ahd_def)

lemma hnf_tenv: "tenv env' = tenv env \<Longrightarrow> hnf env' t = hnf env t"
  by (induction t) (simp_all add: ahd_def)

lemma ahd_lift: "ahd env t \<Longrightarrow> ahd env (incr_bv 1 0 t $ Bound 0)"
proof -
  assume "ahd env t"
  moreover have "head_of (incr_bv 1 0 t $ Bound 0) = incr_bv 1 0 (head_of t)" by (simp add: head_of_incr_bv)
  ultimately show ?thesis unfolding ahd_def using lift_rigid[of "head_of t" 0] by auto
qed

lemma head_norm_hnf:
  assumes "head_norm env t = Some r"
  shows "r = Ok t' \<Longrightarrow> hnf env t'"
  using assms
proof (induction env t r arbitrary: t' rule: head_norm.raw_induct[rotated, consumes 1])
  case (1 hn env t r)
  note h = "1.hyps"[unfolded "1.prems"(1)]
  have IH: "hnf env u'" if "ok (hn env u) u'" for u u'
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
      with rest Var have "t' = Var x T" by simp
      with ok_lookup_None[of env x T] lr None show ?thesis by (simp add: ahd_def)
    next
      case (Some u)
      with rest IH show ?thesis by simp
    qed
  next
    case (Abs a T body)
    with h IH show ?thesis by auto
  next
    case (App f u)
    show ?thesis
    proof (cases "is_Abs f")
      case True
      then obtain a T body where "f = Abs a T body" by (cases f) auto
      with h App IH show ?thesis by simp
    next
      case False
      with h App obtain nf where nf: "ok (hn env f) nf"
        and rest: "ok (case nf of Abs _ _ body \<Rightarrow> hn env (subst_bound u body) | _ \<Rightarrow> return (nf $ u)) t'"
        by (cases f) auto
      show ?thesis
      proof (cases "is_Abs nf")
        case True
        then obtain a T body where "nf = Abs a T body" by (cases nf) auto
        with rest IH show ?thesis by simp
      next
        case nA: False
        with rest have "t' = nf $ u" by (cases nf) simp_all
        with IH[OF nf] nA show ?thesis by (simp add: hnf_nonAbs ahd_def)
      qed
    qed
  qed (use h in \<open>auto simp: ahd_def\<close>)
qed

lemma ahd_hnf: "ahd env t \<Longrightarrow> hnf env t"
  by (cases t) (simp_all add: ahd_def)

lemma arity_other: "\<not> (a = STR ''fun'' \<and> (\<exists>T1 U. Ts = [T1, U])) \<Longrightarrow> arity (Type a (map f Ts)) = 0"
proof (cases Ts)
  case (Cons T1 Us)
  assume a: "\<not> (a = STR ''fun'' \<and> (\<exists>T1 U. Ts = [T1, U]))"
  show ?thesis
  proof (cases Us)
    case (Cons U Vs)
    with \<open>Ts = T1 # Us\<close> a show ?thesis by (cases Vs) auto
  qed (use Cons in simp)
qed simp

context
  fixes \<theta> A n assumes ti: "tinv ar n \<theta> A"
begin

lemma etif_term:
  "tvars T \<subseteq> tvars_env \<theta> \<union> A \<Longrightarrow> \<exists>t'. etif \<theta> T t = return t' \<and> ttvars t' \<subseteq> ttvars t \<union> tvars_env \<theta> \<union> A \<and>
    (\<not> is_Abs t \<longrightarrow> nabs t' = arity (tnorm \<theta> T)) \<and> (ahd env t \<longrightarrow> hnf env t')"
proof -
  assume tv: "tvars T \<subseteq> tvars_env \<theta> \<union> A"
  have "tcons \<theta> T \<Longrightarrow> \<forall>t. \<exists>t'. etif \<theta> T t = return t' \<and> ttvars t' \<subseteq> ttvars t \<union> tvars T \<union> tvars_env \<theta> \<and>
    (\<not> is_Abs t \<longrightarrow> nabs t' = arity (tnorm \<theta> T)) \<and> (ahd env t \<longrightarrow> hnf env t')"
  proof (induction rule: tnorm_induct[OF ti_ac[OF ti] ti_tc[OF ti], consumes 1, case_names TFree Type Unbound Bound])
    case (TFree a S)
    then show ?case by (subst etif.simps) (simp add: ahd_hnf)
  next
    case (Type a Ts)
    show ?case
    proof
      fix t
      show "\<exists>t'. etif \<theta> (Type a Ts) t = return t' \<and> ttvars t' \<subseteq> ttvars t \<union> tvars (Type a Ts) \<union> tvars_env \<theta> \<and>
        (\<not> is_Abs t \<longrightarrow> nabs t' = arity (tnorm \<theta> (Type a Ts))) \<and> (ahd env t \<longrightarrow> hnf env t')"
      proof (cases "a = STR ''fun'' \<and> (\<exists>T1 U. Ts = [T1, U])")
        case True
        then obtain T1 U where Ts: "Ts = [T1, U]" and a: "a = STR ''fun''" by blast
        let ?t = "incr_boundvars 1 t $ Bound 0"
        from Type(1)[of U] Ts obtain u where u: "etif \<theta> U ?t = return u"
          "ttvars u \<subseteq> ttvars ?t \<union> tvars U \<union> tvars_env \<theta>" "nabs u = arity (tnorm \<theta> U)"
          "ahd env ?t \<longrightarrow> hnf env u"
          by fastforce
        have tt: "ttvars ?t = ttvars t" by (simp add: incr_boundvars_def ttvars_def)
        have "ahd env ?t" if "ahd env t" using ahd_lift[OF that] by (simp add: incr_boundvars_def)
        then show ?thesis using u tt Ts a by (subst etif.simps) auto
      next
        case False
        then have "arity (tnorm \<theta> (Type a Ts)) = 0" by (simp add: arity_other)
        with False show ?thesis by (subst etif.simps) (auto simp: ahd_hnf split: list.splits)
      qed
    qed
  next
    case (Unbound v S)
    then show ?case by (subst etif.simps) (auto simp: type_lookup_ok tnorm_TVar[OF ti_ac[OF ti]] ahd_hnf)
  next
    case (Bound v S U)
    then show ?case using tvars_envI2[OF Bound(1)]
      by (subst etif.simps) (fastforce simp: type_lookup_ok tnorm_TVar[OF ti_ac[OF ti]])
  qed
  from this[OF tinv_tcons[OF ti tv]] tv show ?thesis by blast
qed

abbreviation (input) KN :: "(indexname \<times> psort) set" where
  "KN \<equiv> tvars_env \<theta> \<union> A"

lemma btvars_nth: "0 \<le> i \<Longrightarrow> i < ilength bs \<Longrightarrow> tvars (snd (bs ! nat_of_integer i)) \<subseteq> btvars bs"
proof -
  assume "0 \<le> i" "i < ilength bs"
  then have "bs ! nat_of_integer i \<in> set bs" using nat_of_integer_less_ilength[of i bs] by simp
  moreover obtain x U where "bs ! nat_of_integer i = (x, U)" by force
  ultimately show ?thesis unfolding btvars_def by force
qed

lemma env_fastype_term:
  "tyenv env = \<theta> \<Longrightarrow> e \<turnstile> inst (tnorm_inst \<theta>) t : T \<Longrightarrow> bs_env (tnorm_inst \<theta>) e bs \<Longrightarrow>
    \<not> loose_bvar t (ilength bs) \<Longrightarrow> ttvars t \<union> btvars bs \<subseteq> KN \<Longrightarrow>
    \<exists>U. env_fastype env (map snd bs) t = return U \<and> tvars U \<subseteq> KN \<and> tnorm \<theta> U = T"
proof (induction t arbitrary: e T bs)
  case (App f u)
  from App.prems(2) obtain B where tf: "e \<turnstile> inst (tnorm_inst \<theta>) f : B \<rightarrow>\<^sub>T T" by auto
  from App.IH(1)[OF App.prems(1) tf App.prems(3)] App.prems(4,5) obtain Uf where
    uf: "env_fastype env (map snd bs) f = return Uf" "tvars Uf \<subseteq> KN" "tnorm \<theta> Uf = B \<rightarrow>\<^sub>T T"
    by auto
  from devar_term[OF ti uf(2)] obtain U' where
    dv: "devar \<theta> Uf = return U'" "tvars U' \<subseteq> KN" "tnorm \<theta> U' = tnorm \<theta> Uf" "\<not> tbound \<theta> U'"
    by blast
  have "\<exists>U1 U2. U' = U1 \<rightarrow>\<^sub>T U2 \<and> tnorm \<theta> U2 = T"
  proof (cases U')
    case (TVar v S)
    with dv(4) have "vt_lookup \<theta> v = None" by (cases "vt_lookup \<theta> v") auto
    with TVar dv(3) uf(3) show ?thesis by (simp add: tnorm_TVar[OF ti_ac[OF ti]])
  next
    case (Type a Us)
    with dv(3) uf(3) show ?thesis by (auto simp: Cons_eq_map_conv)
  qed (use dv uf in auto)
  then obtain U1 U2 where U': "U' = U1 \<rightarrow>\<^sub>T U2" "tnorm \<theta> U2 = T" by blast
  have "env_fastype env (map snd bs) (f $ u) = return U2" using uf(1) dv(1) U' App.prems(1) by simp
  with dv(2) U' show ?case by auto
next
  case (Bound i)
  from Bound.prems(2) have i: "0 \<le> i" "e i = T" by auto
  from Bound.prems(4) have il: "i < ilength bs" by simp
  have "ilength (map snd bs) = ilength bs" by (simp add: ilength_eq)
  then have "nth (map snd bs) i = return (snd (bs ! nat_of_integer i))"
    using ok_nth[of "map snd bs" i] i il nat_of_integer_less_ilength[of i bs] by (simp add: return_def)
  then have "env_fastype env (map snd bs) (Bound i) = return (snd (bs ! nat_of_integer i))"
    by (simp add: handle_def return_def)
  moreover have "tnorm \<theta> (snd (bs ! nat_of_integer i)) = T"
    using Bound.prems(3) i il by (simp add: bs_env_def)
  moreover have "tvars (snd (bs ! nat_of_integer i)) \<subseteq> KN" using btvars_nth[OF i(1) il] Bound.prems(5) by blast
  ultimately show ?case by blast
next
  case (Abs a A b)
  from Abs.prems(2) obtain W where c: "cert_typ alg ar (tsubst (tnorm_inst \<theta>) A)"
    and tb: "e\<langle>0:tsubst (tnorm_inst \<theta>) A\<rangle> \<turnstile> inst (tnorm_inst \<theta>) b : W" and T: "T = tsubst (tnorm_inst \<theta>) A \<rightarrow>\<^sub>T W"
    by auto
  have lb: "\<not> loose_bvar b (ilength ((a, A) # bs))" using Abs.prems(4) by (simp add: algebra_simps)
  have tv: "ttvars b \<union> btvars ((a, A) # bs) \<subseteq> KN" using Abs.prems(5) by (auto simp: btvars_def)
  from Abs.IH[OF Abs.prems(1) tb bs_env_Cons[OF Abs.prems(3) c] lb tv] obtain Ub where
    ub: "env_fastype env (map snd ((a, A) # bs)) b = return Ub" "tvars Ub \<subseteq> KN" "tnorm \<theta> Ub = W"
    by blast
  then show ?case using T Abs.prems(5) by auto
qed auto

lemma eta_norm_nonAbs_term:
  assumes "\<not> is_Abs t" "tyenv env = \<theta>" "e \<turnstile> inst (tnorm_inst \<theta>) t : T" "bs_env (tnorm_inst \<theta>) e bs"
    "\<not> loose_bvar t (ilength bs)" "ttvars t \<union> btvars bs \<subseteq> KN"
  shows "\<exists>t'. eta_norm env bs t = return t' \<and> ttvars t' \<subseteq> KN \<and> nabs t' = arity T \<and> (hnf env t \<longrightarrow> hnf env t')"
proof -
  from env_fastype_term[OF assms(2-6)] obtain U where
    U: "env_fastype env (map snd bs) t = return U" "tvars U \<subseteq> KN" "tnorm \<theta> U = T" by blast
  from etif_term[OF U(2), of t env] obtain t' where
    t': "etif \<theta> U t = return t'" "ttvars t' \<subseteq> ttvars t \<union> KN" "nabs t' = arity (tnorm \<theta> U)"
      "ahd env t \<longrightarrow> hnf env t'"
    using assms(1) by blast
  have "eta_norm env bs t = return t'"
    using U(1) t'(1) assms(1,2) by (simp add: eta_norm_nonAbs fastype_def)
  then show ?thesis using t' U(3) assms(1,6) by (auto simp: hnf_nonAbs)
qed

lemma eta_norm_term:
  "tyenv env = \<theta> \<Longrightarrow> e \<turnstile> inst (tnorm_inst \<theta>) t : T \<Longrightarrow> bs_env (tnorm_inst \<theta>) e bs \<Longrightarrow>
    \<not> loose_bvar t (ilength bs) \<Longrightarrow> ttvars t \<union> btvars bs \<subseteq> KN \<Longrightarrow>
    \<exists>t'. eta_norm env bs t = return t' \<and> ttvars t' \<subseteq> KN \<and> nabs t' = arity T \<and> (hnf env t \<longrightarrow> hnf env t')"
proof (induction t arbitrary: e T bs)
  case (Abs a A b)
  from Abs.prems(2) obtain W where c: "cert_typ alg ar (tsubst (tnorm_inst \<theta>) A)"
    and tb: "e\<langle>0:tsubst (tnorm_inst \<theta>) A\<rangle> \<turnstile> inst (tnorm_inst \<theta>) b : W" and T: "T = tsubst (tnorm_inst \<theta>) A \<rightarrow>\<^sub>T W"
    by auto
  have lb: "\<not> loose_bvar b (ilength ((a, A) # bs))" using Abs.prems(4) by (simp add: algebra_simps)
  have tv: "ttvars b \<union> btvars ((a, A) # bs) \<subseteq> KN" using Abs.prems(5) by (auto simp: btvars_def)
  from Abs.IH[OF Abs.prems(1) tb bs_env_Cons[OF Abs.prems(3) c] lb tv] obtain b' where
    b': "eta_norm env ((a, A) # bs) b = return b'" "ttvars b' \<subseteq> KN" "nabs b' = arity W" "hnf env b \<longrightarrow> hnf env b'"
    by blast
  then show ?case using T Abs.prems(5) by auto
qed (rule eta_norm_nonAbs_term; simp)+

end

subsection \<open>The size of \<open>\<eta>\<close>-long forms\<close>

text \<open>
  The size of the \<open>\<eta>\<close>-long form of a \<open>\<beta>\<close>-normal term, given the types of its loose bound
  variables. As in \<^const>\<open>msz\<close>, a flexible term counts as the \<open>\<eta>\<close>-expansion of its head
  without the arguments; a rigid term counts with the \<open>\<eta>\<close>-expansion to the arity of its type
  (\<open>tsz\<close> is the size of the \<open>\<eta>\<close>-long form of a bound variable of the type).
\<close>

fun tsz :: "ptyp \<Rightarrow> nat" where
  "tsz (Type a [T, U]) = (if a = STR ''fun'' then tsz T + tsz U + 2 else 1)"
| "tsz _ = 1"

lemma tsz_pos: "0 < tsz T"
  by (induction T rule: tsz.induct) auto

function lsz :: "(integer \<Rightarrow> ptyp) \<Rightarrow> pterm \<Rightarrow> nat" and asz :: "(integer \<Rightarrow> ptyp) \<Rightarrow> pterm \<Rightarrow> nat" where
  "lsz e (Abs a A t) = lsz (e\<langle>0:A\<rangle>) t + 2"
| "lsz e (Var x T) = 2 * arity T + 1"
| "lsz e (s $ t) = (case dhd s of
      Var x T \<Rightarrow> 2 * (arity T - Suc (dnargs s)) + 1
    | _ \<Rightarrow> tsz (spine_type e (s $ t)) + asz e (s $ t))"
| "lsz e (Bound i) = tsz (e i)"
| "lsz e (Const c T) = tsz T"
| "lsz e (Free x T) = tsz T"
| "asz e (s $ t) = asz e s + lsz e t"
| "asz e (Abs a A t) = 0"
| "asz e (Var x T) = 0"
| "asz e (Bound i) = 0"
| "asz e (Const c T) = 0"
| "asz e (Free x T) = 0"
  by pat_completeness auto
termination
  by (relation "measure (\<lambda>x. case x of Inl (e, t) \<Rightarrow> 2 * size t + 1 | Inr (e, t) \<Rightarrow> 2 * size t)") auto

lemma spine_type_lift: "0 \<le> k \<Longrightarrow> spine_type (e\<langle>k:A\<rangle>) (lift t k) = spine_type e t"
  by (induction t) (auto simp: integer_arith)

lemma lsz_lift: "0 \<le> k \<Longrightarrow> lsz (e\<langle>k:A\<rangle>) (lift t k) = lsz e t \<and> asz (e\<langle>k:A\<rangle>) (lift t k) = asz e t"
proof (induction t arbitrary: e k)
  case (Abs a B t)
  from Abs.IH[of "k + 1" "e\<langle>0:B\<rangle>"] Abs.prems show ?case by simp
next
  case (App s t)
  have IH: "asz (e\<langle>k:A\<rangle>) (lift s k) = asz e s" "lsz (e\<langle>k:A\<rangle>) (lift t k) = lsz e t"
    using App.IH App.prems by blast+
  have st: "spine_type (e\<langle>k:A\<rangle>) (lift (s $ t) k) = spine_type e (s $ t)"
    by (rule spine_type_lift[OF App.prems])
  show ?case
  proof (cases "dhd s")
    case (Bound i)
    then show ?thesis using IH st by (simp add: dhd_lift)
  qed (use IH st in \<open>simp_all add: dhd_lift\<close>)
qed (auto simp: integer_arith)

lemma not_App_apps_Abs: "\<not> is_Abs h \<Longrightarrow> \<not> is_Abs (h \<degree>\<degree> ts)"
  by (cases ts rule: rev_exhaust) (simp_all add: app_last[symmetric])

lemma asz_apps: "\<not> (\<exists>f u. h = f $ u) \<Longrightarrow> asz e (h \<degree>\<degree> ts) = sum_list (map (lsz e) ts)"
proof (induction ts rule: rev_induct)
  case Nil
  then show ?case by (cases h) simp_all
next
  case (snoc t ts)
  then show ?case by (simp add: app_last[symmetric])
qed

lemma lsz_rigid_apps: "rigid h \<Longrightarrow> lsz e (h \<degree>\<degree> ts) = tsz (spine_type e (h \<degree>\<degree> ts)) + sum_list (map (lsz e) ts)"
proof -
  assume r: "rigid h"
  then have nA: "\<not> (\<exists>f u. h = f $ u)" by (cases h) simp_all
  have "lsz e (h \<degree>\<degree> ts) = tsz (spine_type e (h \<degree>\<degree> ts)) + asz e (h \<degree>\<degree> ts)"
  proof (cases ts rule: rev_exhaust)
    case Nil
    with r show ?thesis by (cases h) simp_all
  next
    case (snoc ts' t)
    have "dhd (h \<degree>\<degree> ts') = h" using r by (cases h) simp_all
    with r snoc show ?thesis by (cases h) (simp_all add: app_last[symmetric])
  qed
  with asz_apps[OF nA] show ?thesis by simp
qed

lemma lsz_flex_apps: "lsz e (Var x T \<degree>\<degree> ts) = 2 * (arity T - length ts) + 1"
  by (cases ts rule: rev_exhaust) (simp_all add: app_last[symmetric])

lemma no_redex_incr_bv: "no_redex (incr_bv n k t) \<longleftrightarrow> no_redex t"
proof (induction t arbitrary: k)
  case (App s t)
  then show ?case by (cases s) auto
qed auto

lemma lsz_eta:
  assumes h: "rigid h \<or> (\<exists>x T. h = Var x T)" and ty: "e \<turnstile> h \<degree>\<degree> ts : A \<rightarrow>\<^sub>T B" and nr: "no_redex (h \<degree>\<degree> ts)"
  shows "lsz (e\<langle>0:A\<rangle>) (lift (h \<degree>\<degree> ts) 0 $ Bound 0) + 2 = lsz e (h \<degree>\<degree> ts)"
proof -
  have l: "lift (h \<degree>\<degree> ts) 0 $ Bound 0 = lift h 0 \<degree>\<degree> (map (\<lambda>t. lift t 0) ts @ [Bound 0])"
    by (simp only: incr_bv_apps app_last)
  have ll: "sum_list (map (lsz (e\<langle>0:A\<rangle>)) (map (\<lambda>t. lift t 0) ts)) = sum_list (map (lsz e) ts)"
    using lsz_lift[of 0 e A] by (simp add: comp_def)
  from h show ?thesis
  proof
    assume r: "rigid h"
    have nA: "\<not> is_Abs (h \<degree>\<degree> ts)" by (rule not_App_apps_Abs) (use r in \<open>cases h, simp_all\<close>)
    have "e\<langle>0:A\<rangle> \<turnstile> lift (h \<degree>\<degree> ts) 0 : A \<rightarrow>\<^sub>T B" by (rule lift_type[OF ty]) simp
    then have ty': "e\<langle>0:A\<rangle> \<turnstile> lift (h \<degree>\<degree> ts) 0 $ Bound 0 : B" by (rule typing.App) auto
    have nAl: "\<not> is_Abs (lift (h \<degree>\<degree> ts) 0)" using nA by (cases "h \<degree>\<degree> ts") simp_all
    have "no_redex (lift (h \<degree>\<degree> ts) 0)" using nr no_redex_incr_bv by blast
    then have nr': "no_redex (lift (h \<degree>\<degree> ts) 0 $ Bound 0)" using nAl by simp
    have st': "spine_type (e\<langle>0:A\<rangle>) (lift (h \<degree>\<degree> ts) 0 $ Bound 0) = B"
      by (rule spine_type_typing[OF ty' nr']) simp
    have st: "spine_type e (h \<degree>\<degree> ts) = A \<rightarrow>\<^sub>T B" by (rule spine_type_typing[OF ty nr nA])
    have "lsz (e\<langle>0:A\<rangle>) (lift (h \<degree>\<degree> ts) 0 $ Bound 0) = tsz B + sum_list (map (lsz e) ts) + tsz A"
      using lsz_rigid_apps[where e = "e\<langle>0:A\<rangle>" and ts = "map (\<lambda>t. lift t 0) ts @ [Bound 0]",
        OF lift_rigid[OF r, of 0]] st' ll
      by (simp add: l[symmetric])
    moreover have "lsz e (h \<degree>\<degree> ts) = tsz A + tsz B + 2 + sum_list (map (lsz e) ts)"
      using lsz_rigid_apps[OF r, of e ts] st by simp
    ultimately show ?thesis by simp
  next
    assume "\<exists>x T. h = Var x T"
    then obtain x T where hx: "h = Var x T" by blast
    from ty hx obtain Us where "e \<turnstile> Var x T : Us \<Rrightarrow> (A \<rightarrow>\<^sub>T B)" "e \<tturnstile> ts : Us" by (blast dest: list_app_typeD)
    then have "T = Us \<Rrightarrow> (A \<rightarrow>\<^sub>T B)" "length ts = length Us" using typings_nth by auto
    then have ar: "arity T = length ts + Suc (arity B)" by (simp add: arity_funs)
    have "lsz (e\<langle>0:A\<rangle>) (lift (h \<degree>\<degree> ts) 0 $ Bound 0) = 2 * (arity T - Suc (length ts)) + 1"
      using lsz_flex_apps[of "e\<langle>0:A\<rangle>" x T "map (\<lambda>t. lift t 0) ts @ [Bound 0]"] by (simp add: l hx)
    moreover have "lsz e (h \<degree>\<degree> ts) = 2 * (arity T - length ts) + 1" by (simp add: hx lsz_flex_apps)
    ultimately show ?thesis using ar by simp
  qed
qed


text \<open>The types of the bound variables of a list of binders:\<close>

fun benv :: "tinst \<Rightarrow> binders \<Rightarrow> integer \<Rightarrow> ptyp" where
  "benv \<rho> [] = (\<lambda>_. TFree STR '''' [])"
| "benv \<rho> (b # bs) = (benv \<rho> bs)\<langle>0:tsubst \<rho> (snd b)\<rangle>"

lemma bs_env_benv: "\<forall>(x, T)\<in>set bs. cert_typ alg ar (tsubst \<rho> T) \<Longrightarrow> bs_env \<rho> (benv \<rho> bs) bs"
proof (induction bs)
  case Nil
  show ?case by (simp add: bs_env_def)
next
  case (Cons b bs)
  obtain a T where b: "b = (a, T)" by force
  with Cons have "bs_env \<rho> (benv \<rho> bs) bs" "cert_typ alg ar (tsubst \<rho> T)" by auto
  from bs_env_Cons[OF this, of a] b show ?case by simp
qed

lemma typing_benv:
  assumes "bs_env \<rho> e bs" "e \<turnstile> s : T" "\<not> loose_bvar s (ilength bs)"
  shows "benv \<rho> bs \<turnstile> s : T"
proof (rule typing_env_cong[OF assms(2)])
  have b: "bs_env \<rho> (benv \<rho> bs) bs" by (rule bs_env_benv) (use assms(1) in \<open>simp add: bs_env_def\<close>)
  fix i assume i: "0 \<le> i" "loose_bvar1 s i"
  with loose_bvar1_less[OF assms(3)] have "i < ilength bs" by blast
  with b assms(1) i(1) show "benv \<rho> bs i = e i" by (simp add: bs_env_def)
qed

subsection \<open>The measure of a pair\<close>

definition LM :: "tinst \<Rightarrow> env \<Rightarrow> (integer \<Rightarrow> ptyp) \<Rightarrow> pterm \<Rightarrow> nat" where
  "LM \<rho> env e t = lsz e (bnorm (inst \<rho> (unf env t)))"

abbreviation rho0 :: "env \<Rightarrow> tinst" where
  "rho0 env \<equiv> tnorm_inst (tyenv env)"

definition dm :: "env \<Rightarrow> dpair \<Rightarrow> nat" where
  "dm env dp = (case dp of (rb, t, u) \<Rightarrow>
    LM (rho0 env) env (benv (rho0 env) rb) t + LM (rho0 env) env (benv (rho0 env) rb) u)"

lemma LM_head_norm:
  assumes "ok (head_norm env t) t'" "acyc env" "closed_env env" "e' \<turnstile> inst \<rho> (unf env t) : T"
  shows "LM \<rho> env e t' = LM \<rho> env e t"
  unfolding LM_def
  using bnorm_typed_reds[OF assms(4) inst_reds[OF head_norm_unf[OF assms(1) refl assms(2,3)]]] by simp

lemma LM_Abs:
  "e' \<turnstile> inst \<rho> (unf env (Abs a U t)) : T \<Longrightarrow> LM \<rho> env e (Abs a U t) = LM \<rho> env (e\<langle>0:tsubst \<rho> U\<rangle>) t + 2"
  unfolding LM_def by (simp add: bnorm_Abs_typed)

lemma LM_tenv: "tenv env1 = tenv env \<Longrightarrow> LM \<rho> env1 = LM \<rho> env"
proof -
  assume "tenv env1 = tenv env"
  from unf_tenv[OF this] show ?thesis by (simp only: LM_def[abs_def])
qed

lemma bnorm_ahd:
  assumes at: "atom h" and ty: "e \<turnstile> h \<degree>\<degree> xs : T"
  shows "bnorm (h \<degree>\<degree> xs) = h \<degree>\<degree> map bnorm xs" "e \<turnstile> h \<degree>\<degree> map bnorm xs : T" "no_redex (h \<degree>\<degree> map bnorm xs)"
proof -
  show b: "bnorm (h \<degree>\<degree> xs) = h \<degree>\<degree> map bnorm xs" by (rule bnorm_atom_apps[OF at ty])
  from bnorm_typed[OF ty] b show "e \<turnstile> h \<degree>\<degree> map bnorm xs : T" "no_redex (h \<degree>\<degree> map bnorm xs)"
    using subject_reduction_beta'[OF _ ty] by auto
qed

lemma LM_rigid:
  assumes "rigid h" "e \<turnstile> inst \<rho> (unf env (h \<degree>\<degree> ts)) : T"
  shows "LM \<rho> env e (h \<degree>\<degree> ts) = tsz T + sum_list (map (LM \<rho> env e) ts)"
proof -
  have i: "inst \<rho> (unf env (h \<degree>\<degree> ts)) = inst \<rho> h \<degree>\<degree> map (inst \<rho> \<circ> unf env) ts"
    using assms(1) by (simp add: unf_apps inst_apps unf_rigid)
  have r: "rigid (inst \<rho> h)" by (rule inst_rigid[OF assms(1)])
  then have at: "atom (inst \<rho> h)" by (simp add: rigid_iff)
  note b = bnorm_ahd[OF at assms(2)[unfolded i]]
  have nA: "\<not> is_Abs (inst \<rho> h \<degree>\<degree> map bnorm (map (inst \<rho> \<circ> unf env) ts))"
    by (rule not_App_apps_Abs) (use r in \<open>cases "inst \<rho> h", simp_all\<close>)
  have "LM \<rho> env e (h \<degree>\<degree> ts) = lsz e (inst \<rho> h \<degree>\<degree> map bnorm (map (inst \<rho> \<circ> unf env) ts))"
    by (simp add: LM_def i b(1))
  also have "\<dots> = tsz T + sum_list (map (lsz e) (map bnorm (map (inst \<rho> \<circ> unf env) ts)))"
    using lsz_rigid_apps[OF r] spine_type_typing[OF b(2,3) nA] by simp
  also have "\<dots> = tsz T + sum_list (map (LM \<rho> env e) ts)" by (simp add: LM_def[abs_def] comp_def)
  finally show ?thesis .
qed

lemma incr_boundvars_1: "incr_boundvars 1 t = lift t 0"
  by (simp add: incr_boundvars_def)

lemma LM_eta:
  assumes ac: "acyc env" and cl: "closed_env env"
    and h: "rigid h \<or> (\<exists>F U. h = Var F U \<and> vt_lookup (tenv env) F = None)"
    and ty: "e \<turnstile> inst \<rho> (unf env (h \<degree>\<degree> ts)) : A \<rightarrow>\<^sub>T B"
  shows "LM \<rho> env (e\<langle>0:A\<rangle>) (incr_boundvars 1 (h \<degree>\<degree> ts) $ Bound 0) + 2 = LM \<rho> env e (h \<degree>\<degree> ts)"
proof -
  have uh: "unf env h = h" using h by (auto simp: unf_rigid unf_Var[OF ac])
  let ?h = "inst \<rho> h" and ?xs = "map (inst \<rho> \<circ> unf env) ts"
  have i: "inst \<rho> (unf env (h \<degree>\<degree> ts)) = ?h \<degree>\<degree> ?xs" by (simp add: unf_apps inst_apps uh)
  have hv: "rigid ?h \<or> (\<exists>x T. ?h = Var x T)" using h inst_rigid by auto
  then have at: "atom ?h" by (auto simp: rigid_iff)
  note b = bnorm_ahd[OF at ty[unfolded i]]
  let ?N = "?h \<degree>\<degree> map bnorm ?xs"
  have nA: "\<not> is_Abs ?N" by (rule not_App_apps_Abs) (use at in \<open>cases ?h, simp_all\<close>)
  let ?X = "inst \<rho> (unf env (h \<degree>\<degree> ts))"
  have "unf env (lift (h \<degree>\<degree> ts) 0) = lift (unf env (h \<degree>\<degree> ts)) 0" by (rule unf_lift[OF ac cl]) simp
  then have u: "inst \<rho> (unf env (incr_boundvars 1 (h \<degree>\<degree> ts) $ Bound 0)) = lift ?X 0 $ Bound 0"
    by (simp only: incr_boundvars_1 unf_simps inst.simps inst_lift)
  have tyl: "e\<langle>0:A\<rangle> \<turnstile> lift ?X 0 : A \<rightarrow>\<^sub>T B" by (rule lift_type[OF ty]) simp
  have bl: "bnorm (lift ?X 0) = lift ?N 0" using bnorm_lift[OF ty, of 0] b(1) i by simp
  have "lift ?X 0 \<rightarrow>\<^sub>\<beta>\<^sup>* lift ?N 0" using bnorm_typed[OF tyl] bl by simp
  then have r: "lift ?X 0 $ Bound 0 \<rightarrow>\<^sub>\<beta>\<^sup>* lift ?N 0 $ Bound 0" by (rule rtrancl_beta_AppL)
  have nAl: "\<not> is_Abs (lift ?N 0)" using nA by (cases ?N) simp_all
  have "no_redex (lift ?N 0)" using b(3) no_redex_incr_bv by blast
  then have nr: "no_redex (lift ?N 0 $ Bound 0)" using nAl by simp
  have "bnorm (lift ?X 0 $ Bound 0) = lift ?N 0 $ Bound 0" by (rule bnorm_eqI[OF r nr])
  then have "LM \<rho> env (e\<langle>0:A\<rangle>) (incr_boundvars 1 (h \<degree>\<degree> ts) $ Bound 0) = lsz (e\<langle>0:A\<rangle>) (lift ?N 0 $ Bound 0)"
    by (simp only: LM_def u)
  moreover have "LM \<rho> env e (h \<degree>\<degree> ts) = lsz e ?N" by (simp only: LM_def i b(1))
  ultimately show ?thesis using lsz_eta[OF hv b(2,3)] by simp
qed

lemma inst_unf_incr:
  "acyc env \<Longrightarrow> closed_env env \<Longrightarrow>
    inst \<rho> (unf env (incr_boundvars 1 t $ Bound 0)) = lift (inst \<rho> (unf env t)) 0 $ Bound 0"
proof -
  assume ac: "acyc env" and cl: "closed_env env"
  have "unf env (lift t 0) = lift (unf env t) 0" by (rule unf_lift[OF ac cl]) simp
  then show ?thesis by (simp only: incr_boundvars_1 unf_simps inst.simps inst_lift)
qed

lemma t_apps: "t = head_of t \<degree>\<degree> snd (strip_comb t)"
  by (metis head_of_strip_comb prod.collapse strip_comb_apps)

lemma ahd_head: "ahd env t \<Longrightarrow> rigid (head_of t) \<or> (\<exists>F U. head_of t = Var F U \<and> vt_lookup (tenv env) F = None)"
  by (simp add: ahd_def)

lemma ahd_nonAbs: "ahd env t \<Longrightarrow> \<not> is_Abs t"
  by (cases t) (simp_all add: ahd_def)

context
  fixes \<theta> A n assumes ti: "tinv ar n \<theta> A"
begin

lemma LM_etif:
  assumes th: "tyenv env = \<theta>" and ac: "acyc env" and cl: "closed_env env"
  shows "tvars T \<subseteq> tvars_env \<theta> \<union> A \<Longrightarrow> ok (etif \<theta> T t) t' \<Longrightarrow> ahd env t \<Longrightarrow> cert_typ alg ar (tnorm \<theta> T) \<Longrightarrow>
    e \<turnstile> inst (tnorm_inst \<theta>) (unf env t) : tnorm \<theta> T \<Longrightarrow>
    e \<turnstile> inst (tnorm_inst \<theta>) (unf env t') : tnorm \<theta> T \<and> LM (tnorm_inst \<theta>) env e t' = LM (tnorm_inst \<theta>) env e t"
proof -
  let ?\<rho> = "tnorm_inst \<theta>"
  assume tv: "tvars T \<subseteq> tvars_env \<theta> \<union> A"
  have "tcons \<theta> T \<Longrightarrow> \<forall>t t' e. ok (etif \<theta> T t) t' \<longrightarrow> ahd env t \<longrightarrow> cert_typ alg ar (tnorm \<theta> T) \<longrightarrow>
    e \<turnstile> inst ?\<rho> (unf env t) : tnorm \<theta> T \<longrightarrow>
    e \<turnstile> inst ?\<rho> (unf env t') : tnorm \<theta> T \<and> LM ?\<rho> env e t' = LM ?\<rho> env e t"
  proof (induction rule: tnorm_induct[OF ti_ac[OF ti] ti_tc[OF ti], consumes 1, case_names TFree Type Unbound Bound])
    case (TFree a S)
    then show ?case by (subst etif.simps) simp
  next
    case (Type a Ts)
    show ?case
    proof (intro allI impI)
      fix t t' e
      assume ok: "ok (etif \<theta> (Type a Ts) t) t'" and ah: "ahd env t" and c: "cert_typ alg ar (tnorm \<theta> (Type a Ts))"
        and ty: "e \<turnstile> inst ?\<rho> (unf env t) : tnorm \<theta> (Type a Ts)"
      show "e \<turnstile> inst ?\<rho> (unf env t') : tnorm \<theta> (Type a Ts) \<and> LM ?\<rho> env e t' = LM ?\<rho> env e t"
      proof (cases "a = STR ''fun'' \<and> (\<exists>T1 U. Ts = [T1, U])")
        case True
        then obtain T1 U where Ts: "Ts = [T1, U]" and a: "a = STR ''fun''" by blast
        let ?t = "incr_boundvars 1 t $ Bound 0"
        from ok Ts a obtain u where u: "ok (etif \<theta> U ?t) u" and t': "t' = Abs STR '''' T1 u"
          by (subst (asm) etif.simps) auto
        from c Ts a have c1: "cert_typ alg ar (tnorm \<theta> T1)" and c2: "cert_typ alg ar (tnorm \<theta> U)"
          by (simp_all add: cert_typ_fun)
        have ty1: "e \<turnstile> inst ?\<rho> (unf env t) : tnorm \<theta> T1 \<rightarrow>\<^sub>T tnorm \<theta> U" using ty Ts a by simp
        have "e\<langle>0:tnorm \<theta> T1\<rangle> \<turnstile> lift (inst ?\<rho> (unf env t)) 0 : tnorm \<theta> T1 \<rightarrow>\<^sub>T tnorm \<theta> U"
          by (rule lift_type[OF ty1]) simp
        then have tyt: "e\<langle>0:tnorm \<theta> T1\<rangle> \<turnstile> inst ?\<rho> (unf env ?t) : tnorm \<theta> U"
          by (simp only: inst_unf_incr[OF ac cl]) (rule typing.App, auto)
        have aht: "ahd env ?t" using ahd_lift[OF ah] by (simp add: incr_boundvars_1)
        from Type(1)[of U] Ts u aht c2 tyt
        have IH: "e\<langle>0:tnorm \<theta> T1\<rangle> \<turnstile> inst ?\<rho> (unf env u) : tnorm \<theta> U"
          "LM ?\<rho> env (e\<langle>0:tnorm \<theta> T1\<rangle>) u = LM ?\<rho> env (e\<langle>0:tnorm \<theta> T1\<rangle>) ?t"
          by auto
        have tyt': "e \<turnstile> inst ?\<rho> (unf env t') : tnorm \<theta> (Type a Ts)" using IH(1) c1 t' Ts a by auto
        have "LM ?\<rho> env e t' = LM ?\<rho> env (e\<langle>0:tnorm \<theta> T1\<rangle>) u + 2"
          using LM_Abs[OF tyt'[unfolded t']] t' by simp
        also have "\<dots> = LM ?\<rho> env e t"
        proof -
          define h where "h = head_of t"
          define ts where "ts = snd (strip_comb t)"
          have tt: "t = h \<degree>\<degree> ts" unfolding h_def ts_def by (rule t_apps)
          have "LM ?\<rho> env (e\<langle>0:tnorm \<theta> T1\<rangle>) (incr_boundvars 1 (h \<degree>\<degree> ts) $ Bound 0) + 2 = LM ?\<rho> env e (h \<degree>\<degree> ts)"
            by (rule LM_eta[OF ac cl ahd_head[OF ah, folded h_def] ty1[unfolded tt]])
          with IH(2) tt show ?thesis by simp
        qed
        finally show ?thesis using tyt' by blast
      next
        case False
        with ok have "t' = t" by (subst (asm) etif.simps) (auto split: list.splits)
        with ty show ?thesis by simp
      qed
    qed
  next
    case (Unbound v S)
    then show ?case by (subst etif.simps) (simp add: type_lookup_ok)
  next
    case (Bound v S U)
    then show ?case by (subst etif.simps) (simp add: type_lookup_ok tnorm_TVar[OF ti_ac[OF ti]])
  qed
  then show "ok (etif \<theta> T t) t' \<Longrightarrow> ahd env t \<Longrightarrow> cert_typ alg ar (tnorm \<theta> T) \<Longrightarrow>
    e \<turnstile> inst ?\<rho> (unf env t) : tnorm \<theta> T \<Longrightarrow>
    e \<turnstile> inst ?\<rho> (unf env t') : tnorm \<theta> T \<and> LM ?\<rho> env e t' = LM ?\<rho> env e t"
    using tinv_tcons[OF ti tv] by blast
qed

lemma LM_eta_norm_nonAbs:
  assumes th: "tyenv env = \<theta>" and ac: "acyc env" and cl: "closed_env env" and nA: "\<not> is_Abs t"
    and ok: "ok (eta_norm env bs t) t'" and ty: "e \<turnstile> inst (tnorm_inst \<theta>) t : T" and bs: "bs_env (tnorm_inst \<theta>) e bs"
    and lb: "\<not> loose_bvar t (ilength bs)" and tv: "ttvars t \<union> btvars bs \<subseteq> tvars_env \<theta> \<union> A"
    and tyu: "e \<turnstile> inst (tnorm_inst \<theta>) (unf env t) : T" and h: "hnf env t"
  shows "e \<turnstile> inst (tnorm_inst \<theta>) (unf env t') : T \<and> LM (tnorm_inst \<theta>) env e t' = LM (tnorm_inst \<theta>) env e t"
proof -
  from ok nA obtain T0 where T0: "ok (fastype env bs t) T0" and et: "ok (etif \<theta> T0 t) t'"
    by (auto simp: eta_norm_nonAbs th)
  have "tsubst (tnorm_inst \<theta>) T0 = T"
    by (rule fastype_sound[OF T0 _ bs ty]) (simp add: th tsol_tnorm[OF ti_ac[OF ti]])
  then have tT: "tnorm \<theta> T0 = T" by simp
  from env_fastype_term[OF th ty bs lb tv] T0 have tv0: "tvars T0 \<subseteq> tvars_env \<theta> \<union> A"
    by (auto simp: fastype_def)
  have c: "cert_typ alg ar T" by (rule bs_env_cert[OF bs ty lb])
  from LM_etif[OF th ac cl tv0 et _ _ tyu[folded tT]] c h nA tT show ?thesis by (simp add: hnf_nonAbs)
qed

lemma LM_eta_norm:
  assumes th: "tyenv env = \<theta>" and ac: "acyc env" and cl: "closed_env env"
  shows "ok (eta_norm env bs t) t' \<Longrightarrow> e \<turnstile> inst (tnorm_inst \<theta>) t : T \<Longrightarrow> bs_env (tnorm_inst \<theta>) e bs \<Longrightarrow>
    \<not> loose_bvar t (ilength bs) \<Longrightarrow> ttvars t \<union> btvars bs \<subseteq> tvars_env \<theta> \<union> A \<Longrightarrow>
    e \<turnstile> inst (tnorm_inst \<theta>) (unf env t) : T \<Longrightarrow> hnf env t \<Longrightarrow>
    e \<turnstile> inst (tnorm_inst \<theta>) (unf env t') : T \<and> LM (tnorm_inst \<theta>) env e t' = LM (tnorm_inst \<theta>) env e t"
proof (induction t arbitrary: e T bs t')
  case (Abs a B0 b)
  let ?\<rho> = "tnorm_inst \<theta>"
  from Abs.prems(1) obtain b' where b': "ok (eta_norm env ((a, B0) # bs) b) b'" and t': "t' = Abs a B0 b'" by auto
  from Abs.prems(2) obtain W where c: "cert_typ alg ar (tsubst ?\<rho> B0)"
    and tb: "e\<langle>0:tsubst ?\<rho> B0\<rangle> \<turnstile> inst ?\<rho> b : W" and T: "T = tsubst ?\<rho> B0 \<rightarrow>\<^sub>T W"
    by auto
  from Abs.prems(6) T have tbu: "e\<langle>0:tsubst ?\<rho> B0\<rangle> \<turnstile> inst ?\<rho> (unf env b) : W" by auto
  have lb: "\<not> loose_bvar b (ilength ((a, B0) # bs))" using Abs.prems(4) by (simp add: algebra_simps)
  have tv: "ttvars b \<union> btvars ((a, B0) # bs) \<subseteq> tvars_env \<theta> \<union> A" using Abs.prems(5) by (auto simp: btvars_def)
  have hb: "hnf env b" using Abs.prems(7) by simp
  from Abs.IH[OF b' tb bs_env_Cons[OF Abs.prems(3) c] lb tv tbu hb]
  have IH: "e\<langle>0:tsubst ?\<rho> B0\<rangle> \<turnstile> inst ?\<rho> (unf env b') : W"
    "LM ?\<rho> env (e\<langle>0:tsubst ?\<rho> B0\<rangle>) b' = LM ?\<rho> env (e\<langle>0:tsubst ?\<rho> B0\<rangle>) b"
    by blast+
  have ty': "e \<turnstile> inst ?\<rho> (unf env t') : T" using IH(1) c T t' by auto
  show ?case using ty' LM_Abs[OF ty'[unfolded t']] LM_Abs[OF Abs.prems(6)] IH(2) t' by simp
qed (rule LM_eta_norm_nonAbs[OF th ac cl]; simp)+

end

end

end

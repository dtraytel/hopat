section \<open>Termination of \<open>SIMPL\<close>\<close>

theory Unify_Simpl_Term
  imports Unify_Simpl_Sound Unify_Seq "Pattern_Correctness.Pattern_Term_Unif"
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
  from env_fastype_term[OF ti th ty bs lb tv] T0 have tv0: "tvars T0 \<subseteq> tvars_env \<theta> \<union> A"
    by (auto simp: fastype_def return_def)
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
qed (rule LM_eta_norm_nonAbs[OF th ac cl], simp, assumption+)+

end

subsection \<open>Steps of simplification\<close>

text \<open>
  A step of \<open>SIMPL0\<close> extends the environment, with only type variables that are known (in \<open>A\<close> or
  the type environment) or new (\<^const>\<open>tnew\<close>); it either keeps the type environment, and then it
  reduces the number of unbound variables of the problem or keeps the term environment, or it
  reduces the number of unbound type variables reachable from \<open>K\<close>.
\<close>

definition sstep :: "(indexname \<times> psort) set \<Rightarrow> (indexname \<times> psort) set \<Rightarrow> (indexname \<times> ptyp) set \<Rightarrow>
    env \<Rightarrow> env \<Rightarrow> bool" where
  "sstep A K X env env' \<longleftrightarrow> extends env env' \<and> tvars_env (tyenv env) \<subseteq> tvars_env (tyenv env') \<and>
    tnew A env A env' \<and>
    (tyenv env' = tyenv env \<longrightarrow> card (ubv env' X) < card (ubv env X) \<or> tenv env' = tenv env) \<and>
    (tyenv env' \<noteq> tyenv env \<longrightarrow> card (uvarsA (tyenv env') K) < card (uvarsA (tyenv env) K))"

lemma sstep_refl: "sstep A K X env env"
  by (simp add: sstep_def)

lemma sstepD:
  assumes "sstep A K X env env'"
  shows "extends env env'" "tvars_env (tyenv env) \<subseteq> tvars_env (tyenv env')"
    "tyenv env' = tyenv env \<Longrightarrow> card (ubv env' X) < card (ubv env X) \<or> tenv env' = tenv env"
    "tyenv env' \<noteq> tyenv env \<Longrightarrow> card (uvarsA (tyenv env') K) < card (uvarsA (tyenv env) K)"
    "tnew A env A env'"
  using assms by (simp_all add: sstep_def)

lemma vt_lookup_antisym:
  assumes "\<And>x b. vt_lookup t x = Some b \<Longrightarrow> vt_lookup t' x = Some b"
    "\<And>x b. vt_lookup t' x = Some b \<Longrightarrow> vt_lookup t x = Some b"
  shows "t' = t"
  by (rule vt_eqI) (metis assms not_None_eq)

lemma extends_mid:
  assumes "extends env env1" "extends env1 env2"
  shows "tyenv env2 = tyenv env \<Longrightarrow> tyenv env1 = tyenv env"
    and "tenv env2 = tenv env \<Longrightarrow> tenv env1 = tenv env"
proof -
  have te: "textends (tyenv env) (tyenv env1)" "textends (tyenv env1) (tyenv env2)"
    using assms by (simp_all add: extends_def)
  show "tyenv env2 = tyenv env \<Longrightarrow> tyenv env1 = tyenv env" using te textends_antisym by metis
  assume e: "tenv env2 = tenv env"
  show "tenv env1 = tenv env"
  proof (rule vt_lookup_antisym)
    fix x b
    show "vt_lookup (tenv env) x = Some b \<Longrightarrow> vt_lookup (tenv env1) x = Some b"
      by (rule extends_lookup[OF assms(1)])
    show "vt_lookup (tenv env1) x = Some b \<Longrightarrow> vt_lookup (tenv env) x = Some b"
      using extends_lookup[OF assms(2)] e by metis
  qed
qed

lemma sstep_trans:
  assumes 1: "sstep A K X env env1" and 2: "sstep A K X env1 env2"
  shows "sstep A K X env env2"
proof -
  note a = sstepD[OF 1] and b = sstepD[OF 2]
  have c: "card (ubv env2 X) < card (ubv env X) \<or> tenv env2 = tenv env" if e2: "tyenv env2 = tyenv env"
  proof -
    have e1: "tyenv env1 = tyenv env" by (rule extends_mid(1)[OF a(1) b(1) e2])
    with e2 have "tyenv env2 = tyenv env1" by simp
    from a(3)[OF e1] b(3)[OF this] show ?thesis using ubv_tenv[of env1 env X] ubv_tenv[of env2 env1 X] by auto
  qed
  have d: "card (uvarsA (tyenv env2) K) < card (uvarsA (tyenv env) K)" if "tyenv env2 \<noteq> tyenv env"
  proof (cases "tyenv env1 = tyenv env")
    case True
    with that b(4) show ?thesis by simp
  next
    case False
    with a(4) b(4) show ?thesis by (cases "tyenv env2 = tyenv env1") auto
  qed
  have "tnew A env A env2" by (rule tnew_trans[OF a(5) b(5) extends_maxidx[OF a(1)]])
  then show ?thesis using extends_trans[OF a(1) b(1)] a(2) b(2) c d by (auto simp: sstep_def)
qed

lemma sstep_tyext:
  assumes "tenv env1 = tenv env" "textends (tyenv env) (tyenv env1)" "maxidx env \<le> maxidx env1"
    "tvars_env (tyenv env) \<subseteq> tvars_env (tyenv env1)" "tnew A env A env1"
    "tyenv env1 = tyenv env \<or> card (uvarsA (tyenv env1) K) < card (uvarsA (tyenv env) K)"
  shows "sstep A K X env env1"
  using assms by (auto simp: sstep_def extends_def)

lemma ulex_sstep:
  assumes "sstep A K X env0 env" "tyenv env = tyenv env0 \<Longrightarrow> tenv env = tenv env0 \<Longrightarrow> d < d0"
  shows "((card (uvarsA (tyenv env) K), card (ubv env X), d), (card (uvarsA (tyenv env0) K), card (ubv env0 X), d0)) \<in> ulex"
proof (cases "tyenv env = tyenv env0")
  case True
  from sstepD(3)[OF assms(1) True] show ?thesis
  proof
    assume "tenv env = tenv env0"
    with assms(2) True ubv_tenv[of env env0 X] show ?thesis by simp
  qed (use True in simp)
next
  case False
  with sstepD(4)[OF assms(1)] show ?thesis by simp
qed

text \<open>Type unification terminates, raising at most \<open>CANTUNIFY\<close>:\<close>

lemma cunify_types_term:
  assumes ei: "einv A K env" and fin: "finite K"
    and T: "tvars T \<subseteq> tvars_env (tyenv env) \<union> A" "wft ar T" "sorts_ok alg T"
    and U: "tvars U \<subseteq> tvars_env (tyenv env) \<union> A" "wft ar U" "sorts_ok alg U"
  shows "cuok (cunify_types alg T U env) (\<lambda>env'. einv A K env' \<and> tenv env' = tenv env \<and>
      textends (tyenv env) (tyenv env') \<and> maxidx env \<le> maxidx env' \<and>
      tvars_env (tyenv env) \<subseteq> tvars_env (tyenv env') \<and> tnew A env A env' \<and>
      (\<forall>\<rho>. tsol (tyenv env') \<rho> \<longrightarrow> tsubst \<rho> T = tsubst \<rho> U) \<and>
      (tyenv env' = tyenv env \<or> card (uvarsA (tyenv env') K) < card (uvarsA (tyenv env) K)))"
  using unify_types_term[OF ei fin T U]
  by (auto simp: cuok_def cunify_types_def return_def raise_def emit_def bindW_def raiseW_def returnW_def)

lemma cert_typ_rev:
  assumes ei: "einv A K env" and c: "cert_typ alg ar (tsubst \<rho> T)" and tv: "tvars T \<subseteq> tvars_env (tyenv env) \<union> A"
  shows "wft ar T" "sorts_ok alg T"
  using cert_typ_tsubst_rev[OF c tcert_mono[OF einvD(10)[OF ei] tv]] by blast+

text \<open>Typing of a well-formed pair at the types of its binders:\<close>

lemma pok_benv:
  assumes "pok A env rb X t u" "tsol (tyenv env) \<rho>" "cert_inst \<rho>"
  shows "\<exists>T. bs_env \<rho> (benv \<rho> rb) rb \<and> benv \<rho> rb \<turnstile> inst \<rho> t : T \<and> benv \<rho> rb \<turnstile> inst \<rho> u : T"
proof -
  note pd = pokD[OF assms(1)]
  from pd(9)[OF assms(2,3)] obtain e T where e: "bs_env \<rho> e rb" "e \<turnstile> inst \<rho> t : T" "e \<turnstile> inst \<rho> u : T" by blast
  have "bs_env \<rho> (benv \<rho> rb) rb" by (rule bs_env_benv) (use e(1) in \<open>simp add: bs_env_def\<close>)
  moreover have "benv \<rho> rb \<turnstile> inst \<rho> t : T" by (rule typing_benv[OF e(1,2)]) (simp add: pd(7))
  moreover have "benv \<rho> rb \<turnstile> inst \<rho> u : T" by (rule typing_benv[OF e(1,3)]) (simp add: pd(8))
  ultimately show ?thesis by blast
qed

lemma pok_unf:
  assumes "einv A K env" "winv env X" "pok A env rb X t u"
  shows "\<exists>T. bs_env (rho0 env) (benv (rho0 env) rb) rb \<and> benv (rho0 env) rb \<turnstile> inst (rho0 env) t : T \<and>
    benv (rho0 env) rb \<turnstile> inst (rho0 env) u : T \<and> benv (rho0 env) rb \<turnstile> inst (rho0 env) (unf env t) : T \<and>
    benv (rho0 env) rb \<turnstile> inst (rho0 env) (unf env u) : T"
proof -
  from pok_benv[OF assms(3) einv_rho0[OF assms(1)]] obtain T where
    T: "bs_env (rho0 env) (benv (rho0 env) rb) rb" "benv (rho0 env) rb \<turnstile> inst (rho0 env) t : T"
      "benv (rho0 env) rb \<turnstile> inst (rho0 env) u : T" by blast
  note pd = pokD[OF assms(3)]
  have "benv (rho0 env) rb \<turnstile> inst (rho0 env) (unf env t) : T" by (rule typing_unf0[OF assms(1,2) pd(1) T(2)])
  moreover have "benv (rho0 env) rb \<turnstile> inst (rho0 env) (unf env u) : T" by (rule typing_unf0[OF assms(1,2) pd(2) T(3)])
  ultimately show ?thesis using T by blast
qed

subsection \<open>Normalization of pairs\<close>

text \<open>The result of the normalization of a pair:\<close>

definition hpost :: "(indexname \<times> psort) set \<Rightarrow> (indexname \<times> psort) set \<Rightarrow> (indexname \<times> ptyp) set \<Rightarrow>
    env \<Rightarrow> dpair \<Rightarrow> dpair \<Rightarrow> env \<Rightarrow> bool" where
  "hpost A K X env dp dp' env' \<longleftrightarrow> (case dp' of (rb', t', u') \<Rightarrow>
    einv A K env' \<and> winv env' X \<and> pok A env' rb' X t' u' \<and> tenv env' = tenv env \<and> sstep A K X env env' \<and>
    (tyenv env' = tyenv env \<longrightarrow> dm env' dp' \<le> dm env dp) \<and> ahd env' t' \<and> ahd env' u')"

lemma hpost_refl:
  "einv A K env \<Longrightarrow> winv env X \<Longrightarrow> pok A env rb X t u \<Longrightarrow> ahd env t \<Longrightarrow> ahd env u \<Longrightarrow>
    hpost A K X env (rb, t, u) (rb, t, u) env"
  by (simp add: hpost_def sstep_refl)


lemma pok_Abs:
  assumes p: "pok A env bs X (Abs ns Ts ts) (Abs nt Tt tt)"
    and sol: "\<forall>\<rho>. tsol (tyenv env) \<rho> \<longrightarrow> tsubst \<rho> Ts = tsubst \<rho> Tt"
  shows "pok A env ((nm, Ts) # bs) X ts tt"
  unfolding pok_def
proof (intro conjI allI impI)
  note pd = pokD[OF p]
  show "vars ts \<union> vars tt \<subseteq> X \<union> evars env" using pd(1,2) by simp
  show "ttvars ts \<union> ttvars tt \<union> btvars ((nm, Ts) # bs) \<union> vtvars X \<subseteq> tvars_env (tyenv env) \<union> A"
    using pd(3-6) by (auto simp: ttvars_def btvars_def)
  show "\<not> loose_bvar ts (ilength ((nm, Ts) # bs))" using pd(7) by (simp add: algebra_simps)
  show "\<not> loose_bvar tt (ilength ((nm, Ts) # bs))" using pd(8) by (simp add: algebra_simps)
  fix \<rho> assume \<rho>: "tsol (tyenv env) \<rho>" "cert_inst \<rho>"
  obtain e T where ty: "bs_env \<rho> e bs" "e \<turnstile> inst \<rho> (Abs ns Ts ts) : T" "e \<turnstile> inst \<rho> (Abs nt Tt tt) : T"
    using pd(9)[OF \<rho>] by blast
  have eq: "tsubst \<rho> Ts = tsubst \<rho> Tt" using sol \<rho>(1) by blast
  from ty(2) obtain U where T: "T = tsubst \<rho> Ts \<rightarrow>\<^sub>T U" and c: "cert_typ alg ar (tsubst \<rho> Ts)"
    and t1: "e\<langle>0:tsubst \<rho> Ts\<rangle> \<turnstile> inst \<rho> ts : U" by auto
  from ty(3) obtain U' where T': "T = tsubst \<rho> Tt \<rightarrow>\<^sub>T U'"
    and t2: "e\<langle>0:tsubst \<rho> Tt\<rangle> \<turnstile> inst \<rho> tt : U'" by auto
  from T T' eq have "U' = U" by simp
  with t1 t2 eq bs_env_Cons[OF ty(1) c]
  show "\<exists>e T. bs_env \<rho> e ((nm, Ts) # bs) \<and> e \<turnstile> inst \<rho> ts : T \<and> e \<turnstile> inst \<rho> tt : T" by metis
qed

lemma dm_same:
  assumes "tenv env1 = tenv env" "tyenv env1 = tyenv env"
  shows "dm env1 = dm env"
proof (rule ext)
  fix dp
  show "dm env1 dp = dm env dp" using LM_tenv[OF assms(1)] assms(2) by (simp add: dm_def split: prod.splits)
qed

lemma dm_Abs:
  assumes ei: "einv A K env" and wi: "winv env X" and p: "pok A env rb X (Abs a T b1) (Abs b U b2)"
    and eq: "tsubst (rho0 env) T = tsubst (rho0 env) U"
  shows "dm env ((c, T) # rb, b1, b2) + 4 = dm env (rb, Abs a T b1, Abs b U b2)"
proof -
  from pok_unf[OF ei wi p] obtain W where
    W: "benv (rho0 env) rb \<turnstile> inst (rho0 env) (unf env (Abs a T b1)) : W"
      "benv (rho0 env) rb \<turnstile> inst (rho0 env) (unf env (Abs b U b2)) : W"
    by blast
  show ?thesis using LM_Abs[OF W(1)] LM_Abs[OF W(2)] eq by (simp add: dm_def)
qed

lemma new_dpair_term:
  assumes finK: "finite K"
  shows "al = alg \<Longrightarrow> einv A K env \<Longrightarrow> winv env X \<Longrightarrow> pok A env rb X t u \<Longrightarrow> nabs t = nabs u \<Longrightarrow>
    hnf env t \<Longrightarrow> hnf env u \<Longrightarrow> cuok (new_dpair al rb t u env) (\<lambda>(dp', env'). hpost A K X env (rb, t, u) dp' env')"
proof (induction al rb t u env rule: new_dpair.induct)
  case (1 al rb a T body1 b U body2 env)
  note al = "1.prems"(1)
  note IH = "1.IH"[unfolded al]
  note ei = "1.prems"(2) and wi = "1.prems"(3) and p = "1.prems"(4)
  let ?c = "if a = STR '''' then b else a"
  let ?\<rho> = "rho0 env"
  note pd = pokD[OF p] and r0 = einv_rho0[OF ei]
  obtain e0 T0 where ty0: "e0 \<turnstile> inst ?\<rho> (Abs a T body1) : T0" "e0 \<turnstile> inst ?\<rho> (Abs b U body2) : T0"
    using pd(9)[OF r0] by blast
  from ty0(1) have cT: "cert_typ alg ar (tsubst ?\<rho> T)" by auto
  from ty0(2) have cU: "cert_typ alg ar (tsubst ?\<rho> U)" by auto
  have kT: "tvars T \<subseteq> tvars_env (tyenv env) \<union> A" and kU: "tvars U \<subseteq> tvars_env (tyenv env) \<union> A"
    using pd(3,4) by (auto simp: ttvars_def)
  have nd: "new_dpair alg rb (Abs a T body1) (Abs b U body2) env =
      bindW (cunify_types alg T U env) (\<lambda>env'. new_dpair alg ((?c, T) # rb) body1 body2 env')"
    by simp
  note cu = cunify_types_term[OF ei finK kT cert_typ_rev[OF ei cT kT] kU cert_typ_rev[OF ei cU kU]]
  show ?case unfolding al nd
  proof (rule cuok_bindW[OF cu])
    fix env1 assume ok1: "okW (cunify_types alg T U env) env1" and P1: "einv A K env1 \<and> tenv env1 = tenv env \<and>
      textends (tyenv env) (tyenv env1) \<and> maxidx env \<le> maxidx env1 \<and>
      tvars_env (tyenv env) \<subseteq> tvars_env (tyenv env1) \<and> tnew A env A env1 \<and> (\<forall>\<rho>. tsol (tyenv env1) \<rho> \<longrightarrow> tsubst \<rho> T = tsubst \<rho> U) \<and>
      (tyenv env1 = tyenv env \<or> card (uvarsA (tyenv env1) K) < card (uvarsA (tyenv env) K))"
    then have ei1: "einv A K env1" and te: "tenv env1 = tenv env" and tx: "textends (tyenv env) (tyenv env1)"
      and mx: "maxidx env \<le> maxidx env1" and tv: "tvars_env (tyenv env) \<subseteq> tvars_env (tyenv env1)" and tn: "tnew A env A env1"
      and sol: "\<forall>\<rho>. tsol (tyenv env1) \<rho> \<longrightarrow> tsubst \<rho> T = tsubst \<rho> U"
      and card: "tyenv env1 = tyenv env \<or> card (uvarsA (tyenv env1) K) < card (uvarsA (tyenv env) K)"
      by blast+
    have wi1: "winv env1 X" by (rule winv_tyext[OF wi te tx mx])
    have st1: "sstep A K X env env1" by (rule sstep_tyext[OF te tx mx tv tn card])
    have p0: "pok A env1 rb X (Abs a T body1) (Abs b U body2)" by (rule pok_mono[OF p sstepD(1)[OF st1] tv])
    have p1: "pok A env1 ((?c, T) # rb) X body1 body2" by (rule pok_Abs[OF p0 sol])
    have h1: "hnf env1 body1" "hnf env1 body2" using "1.prems"(6,7) hnf_tenv[OF te] by simp_all
    have n1: "nabs body1 = nabs body2" using "1.prems"(5) by simp
    from IH[OF ok1 refl refl ei1 wi1 p1 n1 h1]
    show "cuok (new_dpair alg ((?c, T) # rb) body1 body2 env1)
        (\<lambda>(dp', env'). hpost A K X env (rb, Abs a T body1, Abs b U body2) dp' env')"
    proof (rule cuok_mono)
      fix x assume x0: "case x of (dp', env') \<Rightarrow> hpost A K X env1 ((?c, T) # rb, body1, body2) dp' env'"
      obtain rb' t' u' env' where x: "x = ((rb', t', u'), env')" by (cases x) auto
      from x0 x have h: "einv A K env'" "winv env' X" "pok A env' rb' X t' u'" "tenv env' = tenv env1"
        "sstep A K X env1 env'" "tyenv env' = tyenv env1 \<Longrightarrow> dm env' (rb', t', u') \<le> dm env1 ((?c, T) # rb, body1, body2)"
        "ahd env' t'" "ahd env' u'"
        by (simp_all add: hpost_def)
      have "dm env' (rb', t', u') \<le> dm env (rb, Abs a T body1, Abs b U body2)" if e': "tyenv env' = tyenv env"
      proof -
        have e1: "tyenv env1 = tyenv env" by (rule extends_mid(1)[OF sstepD(1)[OF st1] sstepD(1)[OF h(5)] e'])
        have "tsubst ?\<rho> T = tsubst ?\<rho> U" using sol einv_rho0(1)[OF ei1] e1 by auto
        then have "dm env ((?c, T) # rb, body1, body2) + 4 = dm env (rb, Abs a T body1, Abs b U body2)"
          by (rule dm_Abs[OF ei wi p])
        moreover have "dm env1 = dm env" by (rule dm_same[OF te e1])
        ultimately show ?thesis using h(6) e' e1 by simp
      qed
      then show "case x of (dp', env') \<Rightarrow> hpost A K X env (rb, Abs a T body1, Abs b U body2) dp' env'"
        using h x te sstep_trans[OF st1 h(5)] by (simp add: hpost_def)
    qed
  qed
qed (auto intro!: hpost_refl simp: hnf_nonAbs)

lemma pok_eta_norm:
  assumes p: "pok A env rb X t u" and et: "ok (eta_norm env rb t) t'" and tv: "ttvars t' \<subseteq> tvars_env (tyenv env) \<union> A"
  shows "pok A env rb X t' u"
  unfolding pok_def
proof (intro conjI allI impI)
  note pd = pokD[OF p] and E = eta_norm_sound[OF et]
  show "vars t' \<union> vars u \<subseteq> X \<union> evars env" using pd(1,2) E by simp
  show "ttvars t' \<union> ttvars u \<union> btvars rb \<union> vtvars X \<subseteq> tvars_env (tyenv env) \<union> A" using pd(4-6) tv by blast
  show "\<not> loose_bvar t' (ilength rb)" using E pd(7) ilength_nonneg[of rb] by blast
  show "\<not> loose_bvar u (ilength rb)" by (rule pd(8))
  fix \<rho> assume \<rho>: "tsol (tyenv env) \<rho>" "cert_inst \<rho>"
  from pd(9)[OF \<rho>] obtain e T where ty: "bs_env \<rho> e rb" "e \<turnstile> inst \<rho> t : T" "e \<turnstile> inst \<rho> u : T" by blast
  with E \<rho>(1) pd(7) show "\<exists>e T. bs_env \<rho> e rb \<and> e \<turnstile> inst \<rho> t' : T \<and> e \<turnstile> inst \<rho> u : T" by blast
qed

theorem head_norm_dpair_term:
  assumes finK: "finite K" and ei: "einv A K env" and wi: "winv env X" and p: "pok A env rb X t u"
  shows "cuok (head_norm_dpair alg env (rb, t, u)) (\<lambda>(dp', env'). hpost A K X env (rb, t, u) dp' env')"
proof -
  let ?\<theta> = "tyenv env" and ?\<rho> = "rho0 env" and ?e = "benv (rho0 env) rb"
  note e = einvD[OF ei]
  from hn_term[OF ei wi p] obtain t1 u1 where
    h: "head_norm env t = return t1" "head_norm env u = return u1" "pok A env rb X t1 u1" by blast
  have hf: "hnf env t1" "hnf env u1"
    using head_norm_hnf[OF h(1)[unfolded return_def] refl] head_norm_hnf[OF h(2)[unfolded return_def] refl] .
  from pok_unf[OF ei wi h(3)] obtain T where T: "bs_env ?\<rho> ?e rb" "?e \<turnstile> inst ?\<rho> t1 : T"
    "?e \<turnstile> inst ?\<rho> u1 : T" "?e \<turnstile> inst ?\<rho> (unf env t1) : T" "?e \<turnstile> inst ?\<rho> (unf env u1) : T" by blast
  from pok_unf[OF ei wi p] obtain T' where T': "?e \<turnstile> inst ?\<rho> (unf env t) : T'" "?e \<turnstile> inst ?\<rho> (unf env u) : T'"
    by blast
  note pd1 = pokD[OF h(3)]
  have tv1: "ttvars t1 \<union> btvars rb \<subseteq> tvars_env ?\<theta> \<union> A" "ttvars u1 \<union> btvars rb \<subseteq> tvars_env ?\<theta> \<union> A"
    using pd1(3-5) by blast+
  from eta_norm_term[OF e(2) refl T(2) T(1) pd1(7) tv1(1)] hf(1) obtain t2 where
    t2: "eta_norm env rb t1 = return t2" "ttvars t2 \<subseteq> tvars_env ?\<theta> \<union> A" "nabs t2 = arity T" "hnf env t2"
    by blast
  from eta_norm_term[OF e(2) refl T(3) T(1) pd1(8) tv1(2)] hf(2) obtain u2 where
    u2: "eta_norm env rb u1 = return u2" "ttvars u2 \<subseteq> tvars_env ?\<theta> \<union> A" "nabs u2 = arity T" "hnf env u2"
    by blast
  have Lt: "LM ?\<rho> env ?e t2 = LM ?\<rho> env ?e t"
    using LM_eta_norm[OF e(2) refl e(3) e(4) t2(1)[unfolded return_def] T(2) T(1) pd1(7) tv1(1) T(4) hf(1)]
      LM_head_norm[OF h(1)[unfolded return_def] e(3,4) T'(1)] by simp
  have Lu: "LM ?\<rho> env ?e u2 = LM ?\<rho> env ?e u"
    using LM_eta_norm[OF e(2) refl e(3) e(4) u2(1)[unfolded return_def] T(3) T(1) pd1(8) tv1(2) T(5) hf(2)]
      LM_head_norm[OF h(2)[unfolded return_def] e(3,4) T'(2)] by simp
  have dmeq: "dm env (rb, t2, u2) = dm env (rb, t, u)" using Lt Lu by (simp add: dm_def)
  have p2: "pok A env rb X t2 u2"
    using pok_sym[OF pok_eta_norm[OF pok_sym[OF pok_eta_norm[OF h(3) t2(1)[unfolded return_def] t2(2)]]
      u2(1)[unfolded return_def] u2(2)]] .
  have hd: "head_norm_dpair alg env (rb, t, u) = new_dpair alg rb t2 u2 env"
    by (simp add: head_norm_dpair_def h(1,2) t2(1) u2(1))
  show ?thesis unfolding hd
  proof (rule cuok_mono[OF new_dpair_term[OF finK refl ei wi p2 _ t2(4) u2(4)]])
    show "nabs t2 = nabs u2" using t2(3) u2(3) by simp
    fix x assume "case x of (dp', env') \<Rightarrow> hpost A K X env (rb, t2, u2) dp' env'"
    then show "case x of (dp', env') \<Rightarrow> hpost A K X env (rb, t, u) dp' env'"
      using dmeq by (auto simp: hpost_def split: prod.splits)
  qed
qed

subsection \<open>Assignments\<close>

lemma get_eta_var_cases: "get_eta_var rb n t = raiseW ASSIGN \<or> (\<exists>v T. get_eta_var rb n t = returnW (v, T))"
  by (induction rb n t rule: get_eta_var.induct) auto

lemma head_of_apps': "head_of (s \<degree>\<degree> ts) = head_of s"
  by (induction ts arbitrary: s) simp_all

text \<open>
  An assignment raises \<open>ASSIGN\<close> or \<open>CANTUNIFY\<close>, or binds the head variable; the result keeps the
  invariants and reduces the number of unbound variables (or of unbound type variables).
\<close>

definition apost :: "(indexname \<times> psort) set \<Rightarrow> (indexname \<times> psort) set \<Rightarrow> (indexname \<times> ptyp) set \<Rightarrow>
    env \<Rightarrow> env \<Rightarrow> bool" where
  "apost A K X env env' \<longleftrightarrow> einv A K env' \<and> winv env' X \<and> sstep A K X env env' \<and> tenv env' \<noteq> tenv env"

theorem assignment_term:
  assumes finX: "finite X" and finK: "finite K" and ei: "einv A K env" and wi: "winv env X"
    and p: "pok A env rb X t u" and ah: "ahd env t"
  shows "(\<exists>evs. assignment alg rb t u env = Some (evs, UErr ASSIGN)) \<or>
    cuok (assignment alg rb t u env) (apost A K X env)"
proof (cases "get_eta_var rb 0 t = raiseW ASSIGN")
  case True
  then show ?thesis by (simp add: assignment_def raiseW_def bindW_def)
next
  case False
  with get_eta_var_cases[of rb 0 t] obtain v T where gv: "get_eta_var rb 0 t = returnW (v, T)" by blast
  then have gev: "okW (get_eta_var rb 0 t) (v, T)" by simp
  let ?\<theta> = "tyenv env" and ?\<rho> = "rho0 env"
  note e = einvD[OF ei] and r0 = einv_rho0[OF ei] and pd = pokD[OF p]
  define "is" where "is = rev (map (\<lambda>j. 0 + integer_of_nat j) [0..<length rb])"
  have t: "t = app (Var v T) is" using get_eta_var_app[OF gev] by (simp add: is_def)
  have hv: "head_of t = Var v T" by (simp add: t app_apps head_of_apps')
  with ah have v0: "vt_lookup (tenv env) v = None" by (simp add: ahd_def)
  have vT: "(v, T) \<in> X \<union> evars env" using pd(1) by (auto simp: t app_apps vars_apps)
  have kT: "tvars T \<subseteq> tvars_env ?\<theta> \<union> A" using pd(3) by (simp add: t ttvars_def app_apps typs_apps)
  have vk: "vok env (vars u \<union> evars env)" using vok_mono[OF vok_winv[OF ei wi pd(6)]] pd(2) by blast
  from rigid_occurs_term_term[OF e(3,6,7) vk, of v] obtain oc where
    oc: "rigid_occurs_term env v u = return oc" "oc = NoOcc \<longrightarrow> (\<forall>y\<in>fst ` vars u. (v, y) \<notin> (dep env)\<^sup>*)"
    by blast
  show ?thesis
  proof (cases oc)
    case Rigid
    then show ?thesis using gv oc(1) by (simp add: assignment_def)
  next
    case Nonrigid
    then show ?thesis using gv oc(1) by (simp add: assignment_def raiseW_def)
  next
    case NoOcc
    from pd(9)[OF r0] obtain e0 T0 where ty0: "bs_env ?\<rho> e0 rb" "e0 \<turnstile> inst ?\<rho> t : T0" "e0 \<turnstile> inst ?\<rho> u : T0"
      by blast
    from body_type_term[OF e(2) refl kT] obtain T1 where bt: "body_type env T = return T1" "tvars T1 \<subseteq> tvars_env ?\<theta> \<union> A"
      by blast
    have tvu: "ttvars u \<union> btvars rb \<subseteq> tvars_env ?\<theta> \<union> A" using pd(4,5) by blast
    from env_fastype_term[OF e(2) refl ty0(3,1) pd(8) tvu] obtain T2 where
      ft: "env_fastype env (map snd rb) u = return T2" "tvars T2 \<subseteq> tvars_env ?\<theta> \<union> A" "tnorm ?\<theta> T2 = T0"
      by blast
    have c2: "cert_typ alg ar (tsubst ?\<rho> T2)" using bs_env_cert[OF ty0(1,3) pd(8)] ft(3) by simp
    from binder_types_term[OF e(2) refl kT] obtain Ts where bts: "binder_types env T = return Ts" by blast
    have "tsubst ?\<rho> T = map (tsubst ?\<rho>) Ts \<Rrightarrow> tsubst ?\<rho> T1"
      by (rule binder_body_type_sound[OF bts[unfolded return_def] refl bt(1)[unfolded return_def] r0(1)])
    moreover have "cert_typ alg ar (tsubst ?\<rho> T)"
    proof -
      from ty0(2) obtain Us where "e0 \<turnstile> Var v (tsubst ?\<rho> T) : Us"
        by (auto simp: t app_apps inst_apps dest!: list_app_typeD)
      then show ?thesis by auto
    qed
    ultimately have c1: "cert_typ alg ar (tsubst ?\<rho> T1)" by (simp add: cert_typ_funs)
    note cu = cunify_types_term[OF ei finK bt(2) cert_typ_rev[OF ei c1 bt(2)] ft(2) cert_typ_rev[OF ei c2 ft(2)]]
    have asg: "assignment alg rb t u env =
        bindW (cunify_types alg T1 T2 env) (\<lambda>env'. liftM (update (v, T) (rlist_abs rb u) env'))"
      using gv oc(1) bt(1) ft(1) NoOcc by (simp add: assignment_def fastype_def)
    have "cuok (assignment alg rb t u env) (apost A K X env)"
      unfolding asg
    proof (rule cuok_bindW[OF cu])
      fix env1 assume P1: "einv A K env1 \<and> tenv env1 = tenv env \<and>
        textends (tyenv env) (tyenv env1) \<and> maxidx env \<le> maxidx env1 \<and>
        tvars_env (tyenv env) \<subseteq> tvars_env (tyenv env1) \<and> tnew A env A env1 \<and> (\<forall>\<rho>. tsol (tyenv env1) \<rho> \<longrightarrow> tsubst \<rho> T1 = tsubst \<rho> T2) \<and>
        (tyenv env1 = tyenv env \<or> card (uvarsA (tyenv env1) K) < card (uvarsA (tyenv env) K))"
      then have ei1: "einv A K env1" and te: "tenv env1 = tenv env" and tx: "textends (tyenv env) (tyenv env1)"
        and mx: "maxidx env \<le> maxidx env1" and tv: "tvars_env (tyenv env) \<subseteq> tvars_env (tyenv env1)" and tn: "tnew A env A env1"
        and card: "tyenv env1 = tyenv env \<or> card (uvarsA (tyenv env1) K) < card (uvarsA (tyenv env) K)"
        by blast+
      have wi1: "winv env1 X" by (rule winv_tyext[OF wi te tx mx])
      have st1: "sstep A K X env env1" by (rule sstep_tyext[OF te tx mx tv tn card])
      have p1: "pok A env1 rb X t u" by (rule pok_mono[OF p sstepD(1)[OF st1] tv])
      let ?b = "rlist_abs rb u"
      have v1: "vt_lookup (tenv env1) v = None" using v0 te by simp
      obtain env' where upd: "update (v, T) ?b env1 = return env'" using update_ok[OF v1] by blast
      note upd' = upd[unfolded return_def]
      have vb: "vars ?b = vars u" by (simp add: rlist_abs_abs_list)
      have dep1: "dep env1 = dep env" using te by (simp add: dep_def)
      have ei': "einv A K env'"
      proof (rule einv_update[OF ei1 upd'])
        fix y U assume "(y, U) \<in> vars ?b"
        then have "(y, U) \<in> vars u" using vb by simp
        then have "y \<in> fst ` vars u" by (rule image_eqI[of _ fst "(y, U)", rotated]) simp
        from oc(2)[rule_format, OF NoOcc this] dep1 show "(v, y) \<notin> (dep env1)\<^sup>*" by simp
      next
        show "closed ?b" unfolding rlist_abs_abs_list
          by (rule closed_abs_list) (use pd(8) in \<open>simp add: ilength_eq\<close>)
      next
        have "vinv ?\<rho> env X" using winvD[OF wi r0] by blast
        then have "snd v \<le> maxidx env" using vT unfolding vinv_def by (blast dest: belowD)
        then show "snd v \<le> maxidx env1" using mx by simp
      next
        have "btvars (rev rb) = btvars rb" by (simp add: btvars_def)
        then show "tvars T \<union> ttvars ?b \<subseteq> tvars_env (tyenv env1) \<union> A"
          using kT pd(4,5) tv by (auto simp: rlist_abs_abs_list ttvars_abs_list)
      qed
      have wi': "winv env' X" by (rule winv_step[OF eta_var_step[OF gev upd'] wi1 p1])
      have Fin: "v \<in> fst ` (X \<union> evars env1)" using vT evars_extends[OF sstepD(1)[OF st1]] by force
      have lt: "card (ubv env' X) < card (ubv env1 X)"
        by (rule card_ubv_update(1)[OF finX upd' Fin]) (use vb pd(2) evars_extends[OF sstepD(1)[OF st1]] in auto)
      have st2: "sstep A K X env1 env'"
        using lt extends_update[OF upd'] ok_update(3)[OF upd'] by (simp add: sstep_def tnew_tyenv)
      have "tenv env' \<noteq> tenv env" using ok_update(2)[OF upd'] v0 te
        by (metis option.distinct(1) vt_lookup_update)
      then show "cuok (liftM (update (v, T) ?b env1)) (apost A K X env)"
        using upd ei' wi' sstep_trans[OF st1 st2] by (simp add: apost_def)
    qed
    then show ?thesis by blast
  qed
qed

subsection \<open>Results of simplification\<close>

text \<open>The invariant of a list of pairs, for the variables \<open>X\<close>:\<close>

definition sinv :: "(indexname \<times> psort) set \<Rightarrow> (indexname \<times> psort) set \<Rightarrow> (indexname \<times> ptyp) set \<Rightarrow>
    env \<Rightarrow> dpair list \<Rightarrow> bool" where
  "sinv A K X env dps \<longleftrightarrow> einv A K env \<and> winv env X \<and> (\<forall>(rb, t, u)\<in>set dps. pok A env rb X t u)"

lemma sinv_mono: "sinv A K X env dps \<Longrightarrow> set dps' \<subseteq> set dps \<Longrightarrow> sinv A K X env dps'"
  unfolding sinv_def by blast

lemma sinv_ext:
  assumes "sinv A K X env dps" "einv A K env'" "winv env' X" "sstep A K X env env'"
  shows "sinv A K X env' dps"
  using assms pok_mono[OF _ sstepD(1,2)[OF assms(4)]] unfolding sinv_def by blast

text \<open>
  The shapes of the results: the flex-flex pairs have variables as heads on both sides, the
  flex-rigid pairs a variable on the left and a rigid head on the right; no side is an
  abstraction. The head variables are unbound unless the term environment changed.
\<close>

definition ffs0 :: "dpair \<Rightarrow> bool" where
  "ffs0 dp \<longleftrightarrow> (case dp of (rb, t, u) \<Rightarrow>
    \<not> is_Abs t \<and> \<not> is_Abs u \<and> is_Var (head_of t) \<and> is_Var (head_of u))"

definition frs0 :: "dpair \<Rightarrow> bool" where
  "frs0 dp \<longleftrightarrow> (case dp of (rb, t, u) \<Rightarrow>
    \<not> is_Abs t \<and> \<not> is_Abs u \<and> is_Var (head_of t) \<and> rigid (head_of u))"

definition hunb :: "env \<Rightarrow> dpair \<Rightarrow> bool" where
  "hunb env dp \<longleftrightarrow> (case dp of (rb, t, u) \<Rightarrow>
    (\<forall>F T. head_of t = Var F T \<longrightarrow> vt_lookup (tenv env) F = None) \<and>
    (\<forall>F T. head_of u = Var F T \<longrightarrow> vt_lookup (tenv env) F = None))"

lemma hunb_tenv: "tenv env' = tenv env \<Longrightarrow> hunb env' dp = hunb env dp"
  by (simp add: hunb_def)

definition spost :: "(indexname \<times> psort) set \<Rightarrow> (indexname \<times> psort) set \<Rightarrow> (indexname \<times> ptyp) set \<Rightarrow>
    env \<Rightarrow> dpair list \<Rightarrow> dpair list \<Rightarrow> sstate \<Rightarrow> bool" where
  "spost A K X env ffs frs st' \<longleftrightarrow> (case st' of (env', ffs', frs') \<Rightarrow>
    \<exists>a b. ffs' = a @ ffs \<and> frs' = b @ frs \<and> sinv A K X env' (a @ b) \<and>
      (\<forall>dp\<in>set a. ffs0 dp) \<and> (\<forall>dp\<in>set b. frs0 dp) \<and>
      (tenv env' = tenv env \<longrightarrow> (\<forall>dp\<in>set (a @ b). hunb env' dp)) \<and> sstep A K X env env')"

lemma spost_refl: "sinv A K X env [] \<Longrightarrow> spost A K X env ffs frs (env, ffs, frs)"
  by (simp add: spost_def sstep_refl)

lemma sinv_union: "sinv A K X env xs \<Longrightarrow> sinv A K X env ys \<Longrightarrow> set zs \<subseteq> set xs \<union> set ys \<Longrightarrow> sinv A K X env zs"
  unfolding sinv_def by blast

lemma spost_new:
  assumes "sinv A K X env' (a @ b)" "\<forall>dp\<in>set a. ffs0 dp" "\<forall>dp\<in>set b. frs0 dp"
    "tenv env' = tenv env \<longrightarrow> (\<forall>dp\<in>set (a @ b). hunb env' dp)" "sstep A K X env env'"
  shows "spost A K X env ffs frs (env', a @ ffs, b @ frs)"
  using assms unfolding spost_def by blast

lemma spost_trans:
  assumes 1: "spost A K X env ffs frs (env1, ffs1, frs1)" and 2: "spost A K X env1 ffs1 frs1 st2"
  shows "spost A K X env ffs frs st2"
proof -
  obtain env2 ffs2 frs2 where st2: "st2 = (env2, ffs2, frs2)" by (cases st2)
  from 1 obtain a1 b1 where p1: "ffs1 = a1 @ ffs" "frs1 = b1 @ frs" "sinv A K X env1 (a1 @ b1)"
    "\<forall>dp\<in>set a1. ffs0 dp" "\<forall>dp\<in>set b1. frs0 dp" "tenv env1 = tenv env \<longrightarrow> (\<forall>dp\<in>set (a1 @ b1). hunb env1 dp)"
    "sstep A K X env env1"
    unfolding spost_def by blast
  from 2 st2 obtain a2 b2 where p2: "ffs2 = a2 @ ffs1" "frs2 = b2 @ frs1" "sinv A K X env2 (a2 @ b2)"
    "\<forall>dp\<in>set a2. ffs0 dp" "\<forall>dp\<in>set b2. frs0 dp" "tenv env2 = tenv env1 \<longrightarrow> (\<forall>dp\<in>set (a2 @ b2). hunb env2 dp)"
    "sstep A K X env1 env2"
    unfolding spost_def by blast
  have si: "sinv A K X env2 ((a2 @ a1) @ (b2 @ b1))"
  proof -
    have s1: "sinv A K X env2 (a1 @ b1)"
      by (rule sinv_ext[OF p1(3)]) (use p2(3,7) in \<open>simp_all add: sinv_def\<close>)
    show ?thesis by (rule sinv_union[OF p2(3) s1]) auto
  qed
  have hu: "\<forall>dp\<in>set ((a2 @ a1) @ (b2 @ b1)). hunb env2 dp" if e: "tenv env2 = tenv env"
  proof -
    have e1: "tenv env1 = tenv env" by (rule extends_mid(2)[OF sstepD(1)[OF p1(7)] sstepD(1)[OF p2(7)] e])
    with e have "tenv env2 = tenv env1" by simp
    with p1(6) p2(6) e1 hunb_tenv[OF this] show ?thesis by auto
  qed
  show ?thesis unfolding st2 spost_def prod.case
    by (rule exI[of _ "a2 @ a1"], rule exI[of _ "b2 @ b1"])
      (use p1 p2 si hu sstep_trans[OF p1(7) p2(7)] in auto)
qed

lemma cuok_handle_assign:
  assumes "(\<exists>evs. m = Some (evs, UErr ASSIGN)) \<or> cuok m P" "\<And>x. P x \<Longrightarrow> Q (f x)" "Q r"
  shows "cuok (handleW (bindW m (\<lambda>x. returnW (f x))) (\<lambda>e. case e of ASSIGN \<Rightarrow> returnW r | _ \<Rightarrow> raiseW e)) Q"
  using assms unfolding cuok_def
  by (auto simp: handleW_def bindW_def returnW_def raiseW_def split: option.splits ures.splits)

lemma head_typing: "e \<turnstile> inst \<rho> t : T \<Longrightarrow> \<exists>V. e \<turnstile> inst \<rho> (head_of t) : V"
  by (induction t arbitrary: T) auto

lemma head_Var_cert: "e \<turnstile> inst \<rho> t : T0 \<Longrightarrow> head_of t = Var v T \<Longrightarrow> cert_typ alg ar (tsubst \<rho> T)"
  using head_typing[of e \<rho> t T0] by auto

lemma head_Const_cert: "e \<turnstile> inst \<rho> t : T0 \<Longrightarrow> head_of t = Const c T \<Longrightarrow> cert_typ alg ar (tsubst \<rho> T)"
  using head_typing[of e \<rho> t T0] by auto

lemma head_Free_cert: "e \<turnstile> inst \<rho> t : T0 \<Longrightarrow> head_of t = Free c T \<Longrightarrow> cert_typ alg ar (tsubst \<rho> T)"
  using head_typing[of e \<rho> t T0] by auto

lemma ttvars_head: "ttvars (head_of t) \<subseteq> ttvars t"
  by (induction t) auto

lemma body_type_ok:
  assumes ei: "einv A K env" and tv: "tvars T \<subseteq> tvars_env (tyenv env) \<union> A"
    and c: "cert_typ alg ar (tsubst (rho0 env) T)"
  shows "\<exists>B. body_type env T = return B \<and> tvars B \<subseteq> tvars_env (tyenv env) \<union> A \<and> wft ar B \<and> sorts_ok alg B"
proof -
  note e = einvD[OF ei] and r0 = einv_rho0[OF ei]
  from body_type_term[OF e(2) refl tv] obtain B where bt: "body_type env T = return B"
    "tvars B \<subseteq> tvars_env (tyenv env) \<union> A" by blast
  from binder_types_term[OF e(2) refl tv] obtain Ts where bts: "binder_types env T = return Ts" by blast
  have "tsubst (rho0 env) T = map (tsubst (rho0 env)) Ts \<Rrightarrow> tsubst (rho0 env) B"
    by (rule binder_body_type_sound[OF bts[unfolded return_def] refl bt(1)[unfolded return_def] r0(1)])
  with c have "cert_typ alg ar (tsubst (rho0 env) B)" by (simp add: cert_typ_funs)
  with cert_typ_rev[OF ei this bt(2)] bt show ?thesis by blast
qed

lemma sum_dzip:
  "length ss = length ts \<Longrightarrow>
    sum_list (map f (dzip rb ss ts)) = sum_list (map (\<lambda>(s, t). f (rb, s, t)) (zip ss ts))"
  by (simp add: comp_def split_def)

lemma dm_args:
  assumes ei: "einv A K env" and wi: "winv env X" and p: "pok A env rb X (h \<degree>\<degree> ss) (h' \<degree>\<degree> ts)"
    and rh: "rigid h" "rigid h'" and len: "length ss = length ts"
  shows "sum_list (map (dm env) (dzip rb ss ts)) < dm env (rb, h \<degree>\<degree> ss, h' \<degree>\<degree> ts)"
proof -
  let ?L = "LM (rho0 env) env (benv (rho0 env) rb)"
  from pok_unf[OF ei wi p] obtain T where
    T: "benv (rho0 env) rb \<turnstile> inst (rho0 env) (unf env (h \<degree>\<degree> ss)) : T"
      "benv (rho0 env) rb \<turnstile> inst (rho0 env) (unf env (h' \<degree>\<degree> ts)) : T"
    by blast
  have s: "sum_list (map (dm env) (dzip rb ss ts)) = sum_list (map ?L ss) + sum_list (map ?L ts)"
    using len by (induction ss ts rule: list_induct2) (simp_all add: dm_def)
  have "dm env (rb, h \<degree>\<degree> ss, h' \<degree>\<degree> ts) = tsz T + sum_list (map ?L ss) + (tsz T + sum_list (map ?L ts))"
    using LM_rigid[OF rh(1) T(1)] LM_rigid[OF rh(2) T(2)] by (simp add: dm_def)
  with s tsz_pos[of T] show ?thesis by simp
qed

definition smeas :: "(indexname \<times> psort) set \<Rightarrow> (indexname \<times> ptyp) set \<Rightarrow> env \<Rightarrow> dpair \<Rightarrow> nat \<times> nat \<times> nat" where
  "smeas K X env dp = (card (uvarsA (tyenv env) K), card (ubv env X), dm env dp)"

lemma simrands_atoms:
  "\<not> (\<exists>f u. h = f $ u) \<Longrightarrow> \<not> (\<exists>f u. h' = f $ u) \<Longrightarrow> simrands F rb u0 h h' st = returnW st"
  by (cases h; cases h') simp_all

lemma simrands_snoc:
  "simrands F rb u0 (h \<degree>\<degree> (ss @ [s])) (h' \<degree>\<degree> (ts @ [t])) st =
    bindW (simrands F rb u0 (h \<degree>\<degree> ss) (h' \<degree>\<degree> ts) st) (F (rb, s, t))"
  by (simp add: app_last[symmetric])

lemma SIMPL0_unfold:
  "SIMPL0 al dp0 (env, ffs, frs) =
    bindW (head_norm_dpair al env dp0) (\<lambda>(dp, env'). case dp of (rb, t, u) \<Rightarrow> SIMPL0_rest SIMPL0 al rb t u env' ffs frs)"
  by (subst SIMPL0.simps, simp only: prod.case, rule arg_cong[where f = "bindW (head_norm_dpair al env dp0)"],
    rule ext, simp add: SIMPL0_rest_def split: prod.splits)


lemma fr_case:
  assumes finX: "finite X" and finK: "finite K" and ei: "einv A K env" and wi: "winv env X"
    and p: "pok A env rb X t u" and aht: "ahd env t" and ahu: "ahd env u"
    and hv: "head_of t = Var F Ft" and hr: "rigid (head_of u)"
  shows "cuok (handleW (bindW (assignment alg rb t u env) (\<lambda>env'. returnW (env', ffs, frs)))
    (\<lambda>e. case e of ASSIGN \<Rightarrow> returnW (env, ffs, (rb, t, u) # frs) | _ \<Rightarrow> raiseW e)) (spost A K X env ffs frs)"
proof (rule cuok_handle_assign[OF assignment_term[OF finX finK ei wi p aht]])
  fix env' assume "apost A K X env env'"
  then show "spost A K X env ffs frs (env', ffs, frs)" by (simp add: apost_def spost_def sinv_def)
next
  have "sinv A K X env ([] @ [(rb, t, u)])" by (simp add: sinv_def ei wi p)
  moreover have "frs0 (rb, t, u)" using ahd_nonAbs[OF aht] ahd_nonAbs[OF ahu] hv hr by (simp add: frs0_def)
  moreover have "hunb env (rb, t, u)" using aht hv hr by (auto simp: hunb_def ahd_def)
  ultimately show "spost A K X env ffs frs (env, ffs, (rb, t, u) # frs)"
    using spost_new[of A K X env "[]" "[(rb, t, u)]" env ffs frs] sstep_refl by simp
qed

lemma head_of_not_App: "\<not> (\<exists>f u. head_of t = f $ u)"
  by (induction t) auto

lemma sinv_dzip:
  assumes "einv A K env" "winv env X" "\<forall>(a, b)\<in>set (zip ss ts). pok A env rb X a b"
  shows "sinv A K X env (dzip rb ss ts)"
  unfolding sinv_def
proof (intro conjI ballI)
  fix dp assume "dp \<in> set (dzip rb ss ts)"
  then obtain a b where dp: "dp = (rb, a, b)" "(a, b) \<in> set (zip ss ts)" by auto
  with assms(3) show "case dp of (rb, t, u) \<Rightarrow> pok A env rb X t u" by auto
qed (use assms in auto)

context
  fixes A K X B
  assumes IH: "\<And>env1 dp1 ffs1 frs1. (smeas K X env1 dp1, B) \<in> ulex \<Longrightarrow> sinv A K X env1 [dp1] \<Longrightarrow>
      cuok (SIMPL0 alg dp1 (env1, ffs1, frs1)) (spost A K X env1 ffs1 frs1)"
    and finX: "finite X" and finK: "finite K"
begin

lemma simrands_term:
  assumes hh: "\<not> (\<exists>f u. h = f $ u)" "\<not> (\<exists>f u. h' = f $ u)"
    and B: "B = (card (uvarsA (tyenv env0) K), card (ubv env0 X), d0)"
  shows "length ss = length ts \<Longrightarrow> sinv A K X env (dzip rb ss ts) \<Longrightarrow> sstep A K X env0 env \<Longrightarrow>
    (tyenv env = tyenv env0 \<Longrightarrow> tenv env = tenv env0 \<Longrightarrow> sum_list (map (dm env) (dzip rb ss ts)) < d0) \<Longrightarrow>
    cuok (simrands (SIMPL0 alg) rb u0 (h \<degree>\<degree> ss) (h' \<degree>\<degree> ts) (env, ffs, frs)) (spost A K X env ffs frs)"
proof (induction ss arbitrary: ts ffs frs env rule: rev_induct)
  case Nil
  then have "ts = []" by simp
  with Nil show ?case using simrands_atoms[OF hh] spost_refl by simp
next
  case (snoc s ss)
  from snoc.prems(1) obtain ts' t where ts: "ts = ts' @ [t]" and len: "length ss = length ts'"
    by (cases ts rule: rev_exhaust) auto
  have dz: "dzip rb (ss @ [s]) ts = dzip rb ss ts' @ [(rb, s, t)]" using len ts by simp
  have si0: "sinv A K X env (dzip rb ss ts')" by (rule sinv_mono[OF snoc.prems(2)[unfolded dz]]) auto
  have lt0: "sum_list (map (dm env) (dzip rb ss ts')) < d0"
    if "tyenv env = tyenv env0" "tenv env = tenv env0" using snoc.prems(4)[OF that, unfolded dz] by simp
  have r0: "cuok (simrands (SIMPL0 alg) rb u0 (h \<degree>\<degree> ss) (h' \<degree>\<degree> ts') (env, ffs, frs)) (spost A K X env ffs frs)"
    by (rule snoc.IH[OF len si0 snoc.prems(3) lt0])
  show ?case unfolding ts simrands_snoc
  proof (rule cuok_bindW[OF r0])
    fix st1 assume sp1: "spost A K X env ffs frs st1"
    obtain env1 ffs1 frs1 where st1: "st1 = (env1, ffs1, frs1)" by (cases st1)
    from sp1 st1 obtain a1 b1 where s1: "sinv A K X env1 (a1 @ b1)" "sstep A K X env env1"
      unfolding spost_def by auto
    have si1: "sinv A K X env1 [(rb, s, t)]"
    proof (rule sinv_ext[OF sinv_mono[OF snoc.prems(2)] _ _ s1(2)])
      show "set [(rb, s, t)] \<subseteq> set (dzip rb (ss @ [s]) ts)" unfolding dz by simp
    qed (use s1(1) in \<open>simp_all add: sinv_def\<close>)
    have m: "(smeas K X env1 (rb, s, t), B) \<in> ulex" unfolding smeas_def B
    proof (rule ulex_sstep[OF sstep_trans[OF snoc.prems(3) s1(2)]])
      assume e1: "tyenv env1 = tyenv env0" "tenv env1 = tenv env0"
      have e0: "tyenv env = tyenv env0" "tenv env = tenv env0"
        using extends_mid[OF sstepD(1)[OF snoc.prems(3)] sstepD(1)[OF s1(2)]] e1 by auto
      then have "dm env1 = dm env" using e1 dm_same[of env1 env] by simp
      with snoc.prems(4)[OF e0, unfolded dz] show "dm env1 (rb, s, t) < d0" by simp
    qed
    from IH[OF m si1, of ffs1 frs1] show "cuok (SIMPL0 alg (rb, s, t) st1) (spost A K X env ffs frs)"
      unfolding st1 by (rule cuok_mono) (rule spost_trans[OF sp1[unfolded st1]])
  qed
qed

lemma rigid_rigid_term:
  assumes hp: "hpost A K X env0 dp0 (rb, t, u) env" and B: "B = smeas K X env0 dp0"
    and st2: "sstep A K X env env2" and te2: "tenv env2 = tenv env" and ei2: "einv A K env2" and wi2: "winv env2 X"
    and rh: "rigid (head_of t)" "rigid (head_of u)"
    and hh: "\<And>\<rho>. tsol (tyenv env2) \<rho> \<Longrightarrow> cert_inst \<rho> \<Longrightarrow> inst \<rho> (head_of t) = inst \<rho> (head_of u)"
  shows "cuok (simrands (SIMPL0 alg) rb u0 t u (env2, ffs, frs)) (spost A K X env ffs frs)"
proof -
  from hp have ei: "einv A K env" and wi: "winv env X" and p: "pok A env rb X t u"
    and st0: "sstep A K X env0 env" and dmle: "tyenv env = tyenv env0 \<Longrightarrow> dm env (rb, t, u) \<le> dm env0 dp0"
    by (simp_all add: hpost_def)
  define h where "h = head_of t"
  define ss where "ss = snd (strip_comb t)"
  define h' where "h' = head_of u"
  define ts where "ts = snd (strip_comb u)"
  have tt: "t = h \<degree>\<degree> ss" unfolding h_def ss_def by (rule t_apps)
  have uu: "u = h' \<degree>\<degree> ts" unfolding h'_def ts_def by (rule t_apps)
  have p2: "pok A env2 rb X (h \<degree>\<degree> ss) (h' \<degree>\<degree> ts)"
    using pok_mono[OF p sstepD(1,2)[OF st2]] tt uu by simp
  note ra = rigid_args_pok[OF p2 rh[folded h_def h'_def] hh[folded h_def h'_def] einv_rho0[OF ei2]]
  have si2: "sinv A K X env2 (dzip rb ss ts)" by (rule sinv_dzip[OF ei2 wi2 ra(2)])
  have B': "B = (card (uvarsA (tyenv env0) K), card (ubv env0 X), dm env0 dp0)" by (simp add: B smeas_def)
  have lt: "sum_list (map (dm env2) (dzip rb ss ts)) < dm env0 dp0"
    if e: "tyenv env2 = tyenv env0" "tenv env2 = tenv env0"
  proof -
    have e1: "tyenv env = tyenv env0" by (rule extends_mid(1)[OF sstepD(1)[OF st0] sstepD(1)[OF st2] e(1)])
    then have "dm env2 = dm env" using e(1) dm_same[OF te2] by simp
    moreover have "sum_list (map (dm env) (dzip rb ss ts)) < dm env (rb, h \<degree>\<degree> ss, h' \<degree>\<degree> ts)"
      by (rule dm_args[OF ei wi p[unfolded tt uu] rh[folded h_def h'_def] ra(1)])
    ultimately show ?thesis using dmle[OF e1] tt uu by simp
  qed
  have hA: "\<not> (\<exists>f u. h = f $ u)" "\<not> (\<exists>f u'. h' = f $ u')" unfolding h_def h'_def by (simp_all add: head_of_not_App)
  from simrands_term[OF hA B' ra(1) si2 sstep_trans[OF st0 st2] lt, of u0 ffs frs]
  have "cuok (simrands (SIMPL0 alg) rb u0 t u (env2, ffs, frs)) (spost A K X env2 ffs frs)"
    unfolding tt uu .
  then show ?thesis
  proof (rule cuok_mono)
    have "spost A K X env ffs frs (env2, [] @ ffs, [] @ frs)"
      by (rule spost_new) (use ei2 wi2 st2 in \<open>simp_all add: sinv_def\<close>)
    then show "spost A K X env2 ffs frs x \<Longrightarrow> spost A K X env ffs frs x" for x by (simp add: spost_trans)
  qed
qed

lemma SIMPL0_rest_term:
  assumes hp: "hpost A K X env0 dp0 (rb, t, u) env" and B: "B = smeas K X env0 dp0"
  shows "cuok (SIMPL0_rest SIMPL0 alg rb t u env ffs frs) (spost A K X env ffs frs)"
proof -
  from hp have ei: "einv A K env" and wi: "winv env X" and p: "pok A env rb X t u"
    and aht: "ahd env t" and ahu: "ahd env u"
    by (simp_all add: hpost_def)
  let ?\<rho> = "rho0 env"
  note e = einvD[OF ei] and r0 = einv_rho0[OF ei] and pd = pokD[OF p]
  obtain e0 T0 where ty0: "bs_env ?\<rho> e0 rb" "e0 \<turnstile> inst ?\<rho> t : T0" "e0 \<turnstile> inst ?\<rho> u : T0"
    using pd(9)[OF r0] by blast
  have tvh: "ttvars (head_of t) \<subseteq> tvars_env (tyenv env) \<union> A" "ttvars (head_of u) \<subseteq> tvars_env (tyenv env) \<union> A"
    using ttvars_head[of t] ttvars_head[of u] pd(3,4) by blast+
  have FR: "cuok (SIMPL0_rest SIMPL0 alg rb t u env ffs frs) (spost A K X env ffs frs)"
    if hv: "head_of t = Var F Ft" and hr: "rigid (head_of u)" for F Ft
  proof -
    have "SIMPL0_rest SIMPL0 alg rb t u env ffs frs =
      handleW (bindW (assignment alg rb t u env) (\<lambda>env'. returnW (env', ffs, frs)))
        (\<lambda>e. case e of ASSIGN \<Rightarrow> returnW (env, ffs, (rb, t, u) # frs) | _ \<Rightarrow> raiseW e)"
      using hv hr by (cases "head_of u") (simp_all add: SIMPL0_rest_def)
    with fr_case[OF finX finK ei wi p aht ahu hv hr] show ?thesis by simp
  qed
  have RF: "cuok (SIMPL0_rest SIMPL0 alg rb t u env ffs frs) (spost A K X env ffs frs)"
    if hv: "head_of u = Var F Fu" and hr: "rigid (head_of t)" for F Fu
  proof -
    have "SIMPL0_rest SIMPL0 alg rb t u env ffs frs =
      handleW (bindW (assignment alg rb u t env) (\<lambda>env'. returnW (env', ffs, frs)))
        (\<lambda>e. case e of ASSIGN \<Rightarrow> returnW (env, ffs, (rb, u, t) # frs) | _ \<Rightarrow> raiseW e)"
      using hv hr by (cases "head_of t") (simp_all add: SIMPL0_rest_def)
    with fr_case[OF finX finK ei wi pok_sym[OF p] ahu aht hv hr] show ?thesis by simp
  qed
  have CF: "cuok (SIMPL0_rest SIMPL0 alg rb t u env ffs frs) (spost A K X env ffs frs)"
    if ht: "head_of t = hc" and hu: "head_of u = hd"
      and c: "(hc = Const a Tc \<and> hd = Const a Tu) \<or> (hc = Free a Tc \<and> hd = Free a Tu)"
      and eq: "SIMPL0_rest SIMPL0 alg rb t u env ffs frs =
        bindW (cunify_types alg Tc Tu env) (\<lambda>env'. simrands (SIMPL0 alg) rb u t u (env', ffs, frs))"
    for hc hd a Tc Tu
  proof -
    have cT: "cert_typ alg ar (tsubst ?\<rho> Tc)"
      using c head_Const_cert[OF ty0(2)] head_Free_cert[OF ty0(2)] ht by blast
    have cU: "cert_typ alg ar (tsubst ?\<rho> Tu)"
      using c head_Const_cert[OF ty0(3)] head_Free_cert[OF ty0(3)] hu by blast
    have kT: "tvars Tc \<subseteq> tvars_env (tyenv env) \<union> A" using tvh(1) ht c by auto
    have kU: "tvars Tu \<subseteq> tvars_env (tyenv env) \<union> A" using tvh(2) hu c by auto
    note cu = cunify_types_term[OF ei finK kT cert_typ_rev[OF ei cT kT] kU cert_typ_rev[OF ei cU kU]]
    show ?thesis unfolding eq
    proof (rule cuok_bindW[OF cu])
      fix env2 assume P: "einv A K env2 \<and> tenv env2 = tenv env \<and>
        textends (tyenv env) (tyenv env2) \<and> maxidx env \<le> maxidx env2 \<and>
        tvars_env (tyenv env) \<subseteq> tvars_env (tyenv env2) \<and> tnew A env A env2 \<and> (\<forall>\<rho>. tsol (tyenv env2) \<rho> \<longrightarrow> tsubst \<rho> Tc = tsubst \<rho> Tu) \<and>
        (tyenv env2 = tyenv env \<or> card (uvarsA (tyenv env2) K) < card (uvarsA (tyenv env) K))"
      then have ei2: "einv A K env2" and te: "tenv env2 = tenv env" and tx: "textends (tyenv env) (tyenv env2)"
        and mx: "maxidx env \<le> maxidx env2" and tv: "tvars_env (tyenv env) \<subseteq> tvars_env (tyenv env2)" and tn: "tnew A env A env2"
        and sol: "\<forall>\<rho>. tsol (tyenv env2) \<rho> \<longrightarrow> tsubst \<rho> Tc = tsubst \<rho> Tu"
        and card: "tyenv env2 = tyenv env \<or> card (uvarsA (tyenv env2) K) < card (uvarsA (tyenv env) K)"
        by blast+
      have rh: "rigid (head_of t)" "rigid (head_of u)" using ht hu c by auto
      have hh: "inst \<rho> (head_of t) = inst \<rho> (head_of u)" if "tsol (tyenv env2) \<rho>" for \<rho>
        using sol that ht hu c by auto
      show "cuok (simrands (SIMPL0 alg) rb u t u (env2, ffs, frs)) (spost A K X env ffs frs)"
        by (rule rigid_rigid_term[OF hp B sstep_tyext[OF te tx mx tv tn card] te ei2 winv_tyext[OF wi te tx mx] rh hh])
    qed
  qed
  from ahd_head[OF aht] show ?thesis
  proof
    assume rt: "rigid (head_of t)"
    from ahd_head[OF ahu] show ?thesis
    proof
      assume ru: "rigid (head_of u)"
      show ?thesis
      proof (cases "head_of t")
        case (Const a Ta)
        show ?thesis
        proof (cases "\<exists>Tb. head_of u = Const a Tb")
          case True
          then obtain Tb where hb: "head_of u = Const a Tb" by blast
          show ?thesis
            by (rule CF[OF Const hb]) (simp_all add: SIMPL0_rest_def Const hb)
        next
          case False
          then show ?thesis using Const ru by (cases "head_of u") (auto simp: SIMPL0_rest_def)
        qed
      next
        case (Free a Ta)
        show ?thesis
        proof (cases "\<exists>Tb. head_of u = Free a Tb")
          case True
          then obtain Tb where hb: "head_of u = Free a Tb" by blast
          show ?thesis
            by (rule CF[OF Free hb]) (simp_all add: SIMPL0_rest_def Free hb)
        next
          case False
          then show ?thesis using Free ru by (cases "head_of u") (auto simp: SIMPL0_rest_def)
        qed
      next
        case (Bound i)
        show ?thesis
        proof (cases "head_of u = Bound i")
          case True
          have "SIMPL0_rest SIMPL0 alg rb t u env ffs frs = simrands (SIMPL0 alg) rb u t u (env, ffs, frs)"
            by (simp add: SIMPL0_rest_def Bound True)
          moreover have "cuok (simrands (SIMPL0 alg) rb u t u (env, ffs, frs)) (spost A K X env ffs frs)"
            by (rule rigid_rigid_term[OF hp B sstep_refl refl ei wi rt ru]) (simp add: Bound True)
          ultimately show ?thesis by simp
        next
          case False
          then show ?thesis using Bound ru by (cases "head_of u") (auto simp: SIMPL0_rest_def)
        qed
      qed (use rt in simp_all)
    next
      assume "\<exists>F U. head_of u = Var F U \<and> vt_lookup (tenv env) F = None"
      then obtain F U where "head_of u = Var F U" by blast
      from RF[OF this rt] show ?thesis .
    qed
  next
    assume "\<exists>F U. head_of t = Var F U \<and> vt_lookup (tenv env) F = None"
    then obtain F Ft where ht: "head_of t = Var F Ft" by blast
    from ahd_head[OF ahu] show ?thesis
    proof
      assume "rigid (head_of u)"
      from FR[OF ht this] show ?thesis .
    next
      assume "\<exists>G U. head_of u = Var G U \<and> vt_lookup (tenv env) G = None"
      then obtain G Gu where hu: "head_of u = Var G Gu" by blast
      have kF: "tvars Ft \<subseteq> tvars_env (tyenv env) \<union> A" using tvh(1) ht by simp
      have kG: "tvars Gu \<subseteq> tvars_env (tyenv env) \<union> A" using tvh(2) hu by simp
      from body_type_ok[OF ei kF head_Var_cert[OF ty0(2) ht]] obtain B1 where
        b1: "body_type env Ft = return B1" "tvars B1 \<subseteq> tvars_env (tyenv env) \<union> A" "wft ar B1" "sorts_ok alg B1"
        by blast
      from body_type_ok[OF ei kG head_Var_cert[OF ty0(3) hu]] obtain B2 where
        b2: "body_type env Gu = return B2" "tvars B2 \<subseteq> tvars_env (tyenv env) \<union> A" "wft ar B2" "sorts_ok alg B2"
        by blast
      have eq: "SIMPL0_rest SIMPL0 alg rb t u env ffs frs =
          bindW (cunify_types alg B1 B2 env) (\<lambda>env'. returnW (env', (rb, t, u) # ffs, frs))"
        by (simp add: SIMPL0_rest_def ht hu b1(1) b2(1))
      show ?thesis unfolding eq
      proof (rule cuok_bindW[OF cunify_types_term[OF ei finK b1(2-4) b2(2-4)]])
        fix env2 assume P: "einv A K env2 \<and> tenv env2 = tenv env \<and>
          textends (tyenv env) (tyenv env2) \<and> maxidx env \<le> maxidx env2 \<and>
          tvars_env (tyenv env) \<subseteq> tvars_env (tyenv env2) \<and> tnew A env A env2 \<and> (\<forall>\<rho>. tsol (tyenv env2) \<rho> \<longrightarrow> tsubst \<rho> B1 = tsubst \<rho> B2) \<and>
          (tyenv env2 = tyenv env \<or> card (uvarsA (tyenv env2) K) < card (uvarsA (tyenv env) K))"
        then have ei2: "einv A K env2" and te: "tenv env2 = tenv env" and tx: "textends (tyenv env) (tyenv env2)"
          and mx: "maxidx env \<le> maxidx env2" and tv: "tvars_env (tyenv env) \<subseteq> tvars_env (tyenv env2)" and tn: "tnew A env A env2"
          and card: "tyenv env2 = tyenv env \<or> card (uvarsA (tyenv env2) K) < card (uvarsA (tyenv env) K)"
          by blast+
        have st2: "sstep A K X env env2" by (rule sstep_tyext[OF te tx mx tv tn card])
        have wi2: "winv env2 X" by (rule winv_tyext[OF wi te tx mx])
        have "sinv A K X env2 ([(rb, t, u)] @ [])"
          using pok_mono[OF p sstepD(1,2)[OF st2]] ei2 wi2 by (simp add: sinv_def)
        moreover have "ffs0 (rb, t, u)" using ahd_nonAbs[OF aht] ahd_nonAbs[OF ahu] ht hu by (simp add: ffs0_def)
        moreover have "hunb env2 (rb, t, u)" using aht ahu ht hu te by (auto simp: hunb_def ahd_def)
        ultimately have "spost A K X env ffs frs (env2, [(rb, t, u)] @ ffs, [] @ frs)"
          using spost_new[of A K X env2 "[(rb, t, u)]" "[]" env ffs frs] st2 by simp
        then show "cuok (returnW (env2, (rb, t, u) # ffs, frs)) (spost A K X env ffs frs)" by simp
      qed
    qed
  qed
qed

lemma SIMPL0_step:
  assumes B: "B = smeas K X env0 dp0" and si: "sinv A K X env0 [dp0]"
  shows "cuok (SIMPL0 alg dp0 (env0, ffs, frs)) (spost A K X env0 ffs frs)"
proof -
  obtain rb t u where dp0: "dp0 = (rb, t, u)" by (cases dp0)
  from si dp0 have ei: "einv A K env0" and wi: "winv env0 X" and p: "pok A env0 rb X t u"
    by (simp_all add: sinv_def)
  show ?thesis unfolding SIMPL0_unfold
  proof (rule cuok_bindW[OF head_norm_dpair_term[OF finK ei wi p, folded dp0]])
    fix x assume hp0: "case x of (dp', env') \<Rightarrow> hpost A K X env0 dp0 dp' env'"
    obtain rb' t' u' env where x: "x = ((rb', t', u'), env)" by (cases x) auto
    from hp0 x have hp: "hpost A K X env0 dp0 (rb', t', u') env" by simp
    have r: "cuok (SIMPL0_rest SIMPL0 alg rb' t' u' env ffs frs) (spost A K X env ffs frs)"
      by (rule SIMPL0_rest_term[OF hp B])
    have "spost A K X env0 ffs frs (env, [] @ ffs, [] @ frs)"
      by (rule spost_new) (use hp in \<open>simp_all add: hpost_def sinv_def\<close>)
    then have "cuok (SIMPL0_rest SIMPL0 alg rb' t' u' env ffs frs) (spost A K X env0 ffs frs)"
      using cuok_mono[OF r spost_trans] by simp
    then show "cuok ((\<lambda>(dp, env'). case dp of (rb, t, u) \<Rightarrow> SIMPL0_rest SIMPL0 alg rb t u env' ffs frs) x)
        (spost A K X env0 ffs frs)" by (simp add: x)
  qed
qed

end

subsection \<open>Termination of \<open>SIMPL0\<close>\<close>

text \<open>
  \<^const>\<open>SIMPL0\<close> terminates on a well-formed pair, raising at most \<open>CANTUNIFY\<close>. The new pairs keep
  the invariant, are flex-flex or flex-rigid, and their head variables are unbound unless the
  term environment changed. The measure is \<^const>\<open>smeas\<close>.
\<close>

theorem SIMPL0_term:
  assumes fin: "finite X" "finite K" and si: "sinv A K X env [dp]"
  shows "cuok (SIMPL0 alg dp (env, ffs, frs)) (spost A K X env ffs frs)"
proof -
  have "\<forall>env dp ffs frs. smeas K X env dp = m \<longrightarrow> sinv A K X env [dp] \<longrightarrow>
      cuok (SIMPL0 alg dp (env, ffs, frs)) (spost A K X env ffs frs)" for m
  proof (induction m rule: wf_induct_rule[OF wf_ulex])
    case (1 m)
    show ?case
    proof (intro allI impI)
      fix env dp ffs frs assume m: "smeas K X env dp = m" and si: "sinv A K X env [dp]"
      show "cuok (SIMPL0 alg dp (env, ffs, frs)) (spost A K X env ffs frs)"
      proof (rule SIMPL0_step[OF _ fin m[symmetric] si])
        fix env1 dp1 ffs1 frs1 assume "(smeas K X env1 dp1, m) \<in> ulex" "sinv A K X env1 [dp1]"
        then show "cuok (SIMPL0 alg dp1 (env1, ffs1, frs1)) (spost A K X env1 ffs1 frs1)" using "1.IH" by blast
      qed
    qed
  qed
  with si show ?thesis by blast
qed

corollary SIMPL0_term':
  assumes "finite X" "finite K" "sinv A K X env [dp]"
  shows "cuok (SIMPL0 alg dp (env, ffs, frs)) (\<lambda>(env', ffs', frs'). \<exists>a b. ffs' = a @ ffs \<and> frs' = b @ frs \<and>
    sinv A K X env' (a @ b) \<and> (\<forall>dp\<in>set a. ffs0 dp) \<and> (\<forall>dp\<in>set b. frs0 dp) \<and>
    (tenv env' = tenv env \<longrightarrow> (\<forall>dp\<in>set (a @ b). hunb env' dp)) \<and> extends env env' \<and> sstep A K X env env')"
  by (rule cuok_mono[OF SIMPL0_term[OF assms]]) (auto simp: spost_def dest: sstepD(1))

lemma foldrW_SIMPL0_term:
  assumes fin: "finite X" "finite K"
  shows "sinv A K X env dps \<Longrightarrow> cuok (foldrW (SIMPL0 alg) dps (env, ffs, frs)) (spost A K X env ffs frs)"
proof (induction dps)
  case Nil
  then show ?case using spost_refl[of A K X env ffs frs] by (simp add: sinv_def)
next
  case (Cons dp dps)
  have r: "cuok (foldrW (SIMPL0 alg) dps (env, ffs, frs)) (spost A K X env ffs frs)"
    by (rule Cons.IH[OF sinv_mono[OF Cons.prems]]) auto
  show ?case unfolding foldrW.simps
  proof (rule cuok_bindW[OF r])
    fix st1 assume sp1: "spost A K X env ffs frs st1"
    obtain env1 ffs1 frs1 where st1: "st1 = (env1, ffs1, frs1)" by (cases st1)
    from sp1 st1 obtain a1 b1 where s1: "sinv A K X env1 (a1 @ b1)" "sstep A K X env env1"
      unfolding spost_def by auto
    have "sinv A K X env1 [dp]"
      by (rule sinv_ext[OF sinv_mono[OF Cons.prems] _ _ s1(2)]) (use s1(1) in \<open>simp_all add: sinv_def\<close>)
    from SIMPL0_term[OF fin this, of ffs1 frs1]
    show "cuok (SIMPL0 alg dp st1) (spost A K X env ffs frs)"
      unfolding st1 by (rule cuok_mono) (rule spost_trans[OF sp1[unfolded st1]])
  qed
qed

subsection \<open>Termination of \<open>SIMPL\<close>\<close>

definition chd :: "env \<Rightarrow> pterm \<Rightarrow> bool" where
  "chd env t \<longleftrightarrow> (case head_of t of Var F T \<Rightarrow> vt_lookup (tenv env) F \<noteq> None | _ \<Rightarrow> False)"

lemma not_chd_iff: "\<not> chd env t \<longleftrightarrow> (\<forall>F T. head_of t = Var F T \<longrightarrow> vt_lookup (tenv env) F = None)"
proof (cases "head_of t")
  case (Var F T)
  then show ?thesis by (cases "vt_lookup (tenv env) F") (auto simp: chd_def)
qed (auto simp: chd_def)

lemma hunb_chd: "hunb env (rb, t, u) \<longleftrightarrow> \<not> chd env t \<and> \<not> chd env u"
  by (simp only: hunb_def not_chd_iff prod.case)

lemma changed_ok:
  assumes ac: "tacyc (tyenv env)" and tc: "tcons_env (tyenv env)"
  shows "vok env (vars t \<union> evars env) \<Longrightarrow> changed env t = return (chd env t)"
proof (induction t)
  case (Var x T)
  have "lookup env x T = return (map_option snd (vt_lookup (tenv env) x))"
    by (rule lookup_ok[OF ac tc]) (use Var in \<open>auto intro: vok_mono\<close>)
  then show ?case by (cases "vt_lookup (tenv env) x") (auto simp: chd_def)
next
  case (App f u)
  then have "changed env f = return (chd env f)" by (auto intro: vok_mono)
  then show ?case by (simp add: chd_def)
qed (simp_all add: chd_def)

lemma existsM_ok: "(\<And>x. x \<in> set xs \<Longrightarrow> P x = return (Q x)) \<Longrightarrow> existsM P xs = return (\<exists>x\<in>set xs. Q x)"
  by (induction xs) auto

definition ff_shape :: "env \<Rightarrow> dpair \<Rightarrow> bool" where
  "ff_shape env dp \<longleftrightarrow> ffs0 dp \<and> hunb env dp"

definition fr_shape :: "env \<Rightarrow> dpair \<Rightarrow> bool" where
  "fr_shape env dp \<longleftrightarrow> frs0 dp \<and> hunb env dp"

definition simpl_post :: "(indexname \<times> psort) set \<Rightarrow> (indexname \<times> psort) set \<Rightarrow> (indexname \<times> ptyp) set \<Rightarrow>
    env \<Rightarrow> sstate \<Rightarrow> bool" where
  "simpl_post A K X env st' \<longleftrightarrow> (case st' of (env', ffs, frs) \<Rightarrow>
    sinv A K X env' (frs @ ffs) \<and> (\<forall>dp\<in>set ffs. ff_shape env' dp) \<and> (\<forall>dp\<in>set frs. fr_shape env' dp) \<and>
    sstep A K X env env')"

lemma simpl_post_trans: "sstep A K X env env1 \<Longrightarrow> simpl_post A K X env1 st \<Longrightarrow> simpl_post A K X env st"
  by (auto simp: simpl_post_def intro: sstep_trans split: prod.splits)

theorem SIMPL_term:
  assumes fin: "finite X" "finite K" and si: "sinv A K X env dps"
  shows "cuok (SIMPL alg env dps) (simpl_post A K X env)"
proof -
  have "\<forall>env dps. (card (uvarsA (tyenv env) K), card (ubv env X)) = m \<longrightarrow> sinv A K X env dps \<longrightarrow>
      cuok (SIMPL alg env dps) (simpl_post A K X env)" for m
  proof (induction m rule: wf_induct_rule[OF wf_lex_prod[OF wf_less_than wf_less_than]])
    case (1 m)
    show ?case
    proof (intro allI impI)
      fix env dps assume m: "(card (uvarsA (tyenv env) K), card (ubv env X)) = m" and si: "sinv A K X env dps"
      show "cuok (SIMPL alg env dps) (simpl_post A K X env)"
      proof (subst SIMPL.simps, rule cuok_bindW[OF foldrW_SIMPL0_term[OF fin si]])
        fix st assume sp: "spost A K X env [] [] st"
        obtain env' ffs frs where st: "st = (env', ffs, frs)" by (cases st)
        from sp st have ab: "sinv A K X env' (ffs @ frs)" "\<forall>dp\<in>set ffs. ffs0 dp" "\<forall>dp\<in>set frs. frs0 dp"
          "tenv env' = tenv env \<longrightarrow> (\<forall>dp\<in>set (ffs @ frs). hunb env' dp)" "sstep A K X env env'"
          unfolding spost_def by auto
        have si': "sinv A K X env' (frs @ ffs)" by (rule sinv_mono[OF ab(1)]) auto
        then have ei': "einv A K env'" and wi': "winv env' X" by (simp_all add: sinv_def)
        note e' = einvD[OF ei']
        let ?ch = "chd env'"
        have ex: "existsM (\<lambda>(_, t, u). do {b \<leftarrow> changed env' t; if b then return True else changed env' u}) (frs @ ffs) =
            return (\<exists>dp\<in>set (frs @ ffs). case dp of (_, t, u) \<Rightarrow> ?ch t \<or> ?ch u)"
        proof (rule existsM_ok)
          fix dp assume dp: "dp \<in> set (frs @ ffs)"
          obtain rb t u where dpe: "dp = (rb, t, u)" by (cases dp)
          from si' have "\<forall>x\<in>set (frs @ ffs). case x of (rb, t, u) \<Rightarrow> pok A env' rb X t u" by (simp add: sinv_def)
          from bspec[OF this dp] dpe have p: "pok A env' rb X t u" by simp
          note pd = pokD[OF p]
          have vk: "vok env' (X \<union> evars env')" by (rule vok_winv[OF ei' wi' pd(6)])
          have "changed env' t = return (?ch t)" by (rule changed_ok[OF e'(6,7) vok_mono[OF vk]]) (use pd(1) in blast)
          moreover have "changed env' u = return (?ch u)" by (rule changed_ok[OF e'(6,7) vok_mono[OF vk]]) (use pd(2) in blast)
          ultimately show "(case dp of (_, t, u) \<Rightarrow> do {b \<leftarrow> changed env' t; if b then return True else changed env' u}) =
              return (case dp of (_, t, u) \<Rightarrow> ?ch t \<or> ?ch u)" by (simp add: dpe)
        qed
        show "cuok ((\<lambda>st. case st of (env', ffs, frs) \<Rightarrow> let dps = frs @ ffs in
              bindW (liftM (existsM (\<lambda>(_, t, u). do {b \<leftarrow> changed env' t; if b then return True else changed env' u}) dps))
                (\<lambda>b. if b then SIMPL alg env' dps else returnW st)) st) (simpl_post A K X env)"
        proof (cases "\<exists>dp\<in>set (frs @ ffs). case dp of (_, t, u) \<Rightarrow> ?ch t \<or> ?ch u")
          case True
          have "tenv env' \<noteq> tenv env"
          proof
            assume "tenv env' = tenv env"
            with ab(4) have hu: "\<forall>dp\<in>set (frs @ ffs). hunb env' dp" by auto
            from True obtain dp where dp: "dp \<in> set (frs @ ffs)" "case dp of (_, t, u) \<Rightarrow> ?ch t \<or> ?ch u" by blast
            obtain rb t u where dpe: "dp = (rb, t, u)" by (cases dp)
            from bspec[OF hu dp(1)] dp(2) dpe show False by (simp add: hunb_chd)
          qed
          then have lt: "((card (uvarsA (tyenv env') K), card (ubv env' X)), m) \<in> less_than <*lex*> less_than"
            using sstepD(3,4)[OF ab(5)] m by (cases "tyenv env' = tyenv env") auto
          have "cuok (SIMPL alg env' (frs @ ffs)) (simpl_post A K X env')" using "1.IH"[OF lt] si' by blast
          then have "cuok (SIMPL alg env' (frs @ ffs)) (simpl_post A K X env)"
            by (rule cuok_mono) (rule simpl_post_trans[OF ab(5)])
          then show ?thesis using True ex st by simp
        next
          case False
          have "simpl_post A K X env (env', ffs, frs)"
            unfolding simpl_post_def prod.case
          proof (intro conjI ballI)
            show "sinv A K X env' (frs @ ffs)" by (rule si')
            show "sstep A K X env env'" by (rule ab(5))
            fix dp
            have hu: "hunb env' dp" if "dp \<in> set (frs @ ffs)"
            proof -
              obtain rb t u where dpe: "dp = (rb, t, u)" by (cases dp)
              from False that dpe have "\<not> ?ch t" "\<not> ?ch u" by auto
              then show ?thesis by (simp add: hunb_chd dpe)
            qed
            show "ff_shape env' dp" if "dp \<in> set ffs" using hu that ab(2) by (simp add: ff_shape_def)
            show "fr_shape env' dp" if "dp \<in> set frs" using hu that ab(3) by (simp add: fr_shape_def)
          qed
          then show ?thesis using False ex st by simp
        qed
      qed
    qed
  qed
  with si show ?thesis by blast
qed

end

end

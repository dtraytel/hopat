section \<open>Invariants of Higher-Order Unification: Types and Normal Forms\<close>

text \<open>
  The invariant of a list of pairs (\<open>sinv\<close>), the computations on types on a well-formed type
  environment (\<open>body_type\<close>, \<open>binder_types\<close>, \<open>fastype\<close>, \<open>eta_norm\<close>, the unification of
  types), head normal forms, and the predicates of the occurs check. The statements of
  soundness and of termination both use them; this theory contains no measure.
\<close>

theory Unify_Inv_Base
  imports Unify_Simpl_Sound Unify_Seq
begin

subsection \<open>The occurs check\<close>

context pure_sig_gen
begin

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

lemma good_trans: "\<forall>w\<in>set s1. good env v seen w \<Longrightarrow> good env v s1 y \<Longrightarrow> good env v seen y"
  unfolding good_def by (meson rtrancl_trans)

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

subsection \<open>Operations on types and head normal forms\<close>

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

lemma ahd_lift: "ahd env t \<Longrightarrow> ahd env (incr_bv 1 0 t $ Bound 0)"
proof -
  assume "ahd env t"
  moreover have "head_of (incr_bv 1 0 t $ Bound 0) = incr_bv 1 0 (head_of t)" by (simp add: head_of_incr_bv)
  ultimately show ?thesis unfolding ahd_def using lift_rigid[of "head_of t" 0] by auto
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

lemma t_apps: "t = head_of t \<degree>\<degree> snd (strip_comb t)"
  by (metis head_of_strip_comb prod.collapse strip_comb_apps)

subsection \<open>Unification of types\<close>

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
  by (auto simp: xokW_def cunify_types_def return_def raise_def emit_def bindW_def raiseW_def returnW_def)

lemma cert_typ_rev:
  assumes ei: "einv A K env" and c: "cert_typ alg ar (tsubst \<rho> T)" and tv: "tvars T \<subseteq> tvars_env (tyenv env) \<union> A"
  shows "wft ar T" "sorts_ok alg T"
  using cert_typ_tsubst_rev[OF c tcert_mono[OF einvD(10)[OF ei] tv]] by blast+

subsection \<open>The invariant of a list of pairs\<close>

text \<open>The invariant of a list of pairs, for the variables \<open>X\<close>:\<close>

definition sinv :: "(indexname \<times> psort) set \<Rightarrow> (indexname \<times> psort) set \<Rightarrow> (indexname \<times> ptyp) set \<Rightarrow>
    env \<Rightarrow> dpair list \<Rightarrow> bool" where
  "sinv A K X env dps \<longleftrightarrow> einv A K env \<and> winv env X \<and> (\<forall>(rb, t, u)\<in>set dps. upok A env rb X t u)"

definition frs0 :: "dpair \<Rightarrow> bool" where
  "frs0 dp \<longleftrightarrow> (case dp of (rb, t, u) \<Rightarrow>
    \<not> is_Abs t \<and> \<not> is_Abs u \<and> is_Var (head_of t) \<and> rigid (head_of u))"

definition hunb :: "env \<Rightarrow> dpair \<Rightarrow> bool" where
  "hunb env dp \<longleftrightarrow> (case dp of (rb, t, u) \<Rightarrow>
    (\<forall>F T. head_of t = Var F T \<longrightarrow> vt_lookup (tenv env) F = None) \<and>
    (\<forall>F T. head_of u = Var F T \<longrightarrow> vt_lookup (tenv env) F = None))"

lemma ttvars_head: "ttvars (head_of t) \<subseteq> ttvars t"
  by (induction t) auto

subsection \<open>Flex-rigid pairs and lists of pattern problems\<close>

definition fr_shape :: "env \<Rightarrow> dpair \<Rightarrow> bool" where
  "fr_shape env dp \<longleftrightarrow> frs0 dp \<and> hunb env dp"

end

context pure_sig_gen
begin

lemma foldM_unify_dstep:
  assumes "ok (foldM (\<lambda>(t, u) env. unify alg' t u env) tus env) env'"
  shows "dstep env (map (\<lambda>(t, u). ([], t, u)) tus) env' []"
  using assms
proof (induction rule: ok_foldM_induct)
  case (Nil b)
  then show ?case by (simp add: dstep_refl)
next
  case (Cons x xs b b1 b')
  obtain t u where x: "x = (t, u)" by force
  from Cons.hyps(1) have "unif alg' [] t u b = Some (Ok b1)" by (simp add: x unify_def)
  from unif_gsound[OF this refl] have "dstep b [([], t, u)] b1 []" by (rule step_okg_dstep)
  from dstep_frame[OF this, of "map (\<lambda>(t, u). ([], t, u)) xs"] Cons.IH
  show ?case by (simp add: x) (rule dstep_trans)
qed

end

end

section \<open>The Entry Point with Type Variables\<close>

theory Unify_Poly_Unifiers
  imports Unify_Poly_Match_Fin Unify_Unifiers Pure_Pattern_Correctness.Poly_Typing
begin

text \<open>
  \<^const>\<open>unifiers\<close> first tries pattern unification on the input pairs, one after the other. For
  problems with type variables, the invariant \<^const>\<open>pinv\<close> of the remaining pairs survives each
  step, so the fast path terminates without an exception, and otherwise the search does.
\<close>

subsection \<open>Pattern unification keeps the invariant of other terms\<close>

context wf_algebra
begin

text \<open>
  The analogue of @{thm [source] postok_penv_inv} for a set \<open>A\<close> of type variables and further
  terms \<open>rs\<close> that keep their types.
\<close>

lemma postok_pinv:
  assumes inv: "penv_inv alg ar W env" and A: "tinv ar (maxidx env) (tyenv env) A"
    and twW: "\<forall>x. tyw ar (tyenv env) A (W x)" and twe: "\<forall>U\<in>etys env. tyw ar (tyenv env) A U"
    and s: "pwf_term ar 0 s" "typed env W [] s T" and t: "pwf_term ar 0 t" "typed env W [] t T"
    and rs: "\<forall>(r, U)\<in>set rs. typed env W [] r U \<and> below (maxidx env) r \<and> (\<forall>X\<in>tys r. tyw ar (tyenv env) A X)"
    and srs: "(s, T) \<in> set rs" "(t, T) \<in> set rs"
    and post: "postok alg ar A [] s t env env'" and nac: "nacyc env'"
  obtains W' where "penv_inv alg ar W' env'" "\<forall>x. tyw ar (tyenv env') A (W' x)" "wcons W' env'"
    "\<forall>(r, U)\<in>set rs. typed env' W' [] r U"
proof -
  let ?\<theta> = "tyenv env" and ?\<theta>' = "tyenv env'"
  note i = penv_invD[OF inv]
  note p = post[unfolded postok_def]
  define W0 where "W0 = tctx env W"
  have i5: "env_typed_mod (tyenv env) W0 env" using i(5) unfolding W0_def .
  have ext: "textends ?\<theta> ?\<theta>'" "extends env' env" "maxidx env \<le> maxidx env'" using p by blast+
  have inv': "tinv ar (maxidx env') ?\<theta>' A" and srt': "tsorted alg ?\<theta>'"
    and tw: "\<forall>T\<in>etys env'. tyw ar ?\<theta>' A T" using p by blast+
  have ac: "tacyc ?\<theta>" "tcons_env ?\<theta>" using tinv_tacyc[OF A] tinv_tcons_env[OF A] by simp_all
  have ac': "tacyc ?\<theta>'" "tcons_env ?\<theta>'" using tinv_tacyc[OF inv'] tinv_tcons_env[OF inv'] by simp_all
  define B0 where "B0 = (\<Union>(r, U)\<in>set rs. tys r) \<union> etys env"
  define B where "B = B0 \<union> etys env'"
  have twB0: "tyw ar ?\<theta> A U" if "U \<in> B0" for U using that rs twe by (auto simp: B0_def)
  have tc0: "tcons ?\<theta> U" if "U \<in> B0" for U by (rule tyw_tcons[OF A twB0[OF that]])
  have twB: "tyw ar ?\<theta>' A U" if "U \<in> B" for U
    using that twB0 tw tyw_textends[OF ac'(1) ext(1)] by (auto simp: B_def)
  have tc': "tcons ?\<theta>' U" if "U \<in> B" for U by (rule tyw_tcons[OF inv' twB[OF that]])
  have Ap: "tinv ar (maxidx env) ?\<theta> (ptvars env s t)"
  proof (rule tinv_subset[OF A])
    have "U \<in> B0" if "U \<in> tys s \<union> tys t \<union> etys env" for U using that srs by (auto simp: B0_def)
    then show "ptvars env s t \<subseteq> tvars_env ?\<theta> \<union> A"
      using twB0 by (fastforce simp: ptvars_def etvars_def tyw_def)
  qed
  define Z where "Z = (\<Union>U\<in>B. tvars (tnorm ?\<theta>' U))"
  define N where "N = (\<Union>U\<in>B. tfnames (tnorm ?\<theta>' U))"
  define \<T> where "\<T> = {U. tnorm ?\<theta>' U = U \<and> tvars U \<subseteq> Z \<and> tfnames U \<subseteq> N}"
  have finB: "finite B" using finite_etys by (auto simp: B_def B0_def split: prod.splits)
  have finZ: "finite Z" and finN: "finite N" using finB by (simp_all add: Z_def N_def)
  have in\<T>: "tnorm ?\<theta>' U \<in> \<T>" if "U \<in> B" for U
    using that ac'(1) by (auto simp: \<T>_def Z_def N_def)
  obtain \<rho> where g': "gsol alg ar ?\<theta>' \<rho>" and tf: "tfree_on \<rho> ?\<theta>'"
    and fi: "\<And>T U. tcons ?\<theta>' T \<Longrightarrow> tcons ?\<theta>' U \<Longrightarrow> tvars (tnorm ?\<theta>' T) \<union> tvars (tnorm ?\<theta>' U) \<subseteq> Z \<Longrightarrow>
      tfnames (tnorm ?\<theta>' T) \<union> tfnames (tnorm ?\<theta>' U) \<subseteq> N \<Longrightarrow> tsubst \<rho> T = tsubst \<rho> U \<Longrightarrow>
      tnorm ?\<theta>' T = tnorm ?\<theta>' U"
    using faithful_exists[OF inv' srt' finZ finN] by blast
  have inj: "T = U" if "T \<in> \<T>" "U \<in> \<T>" "tsubst \<rho> T = tsubst \<rho> U" for T U
  proof -
    have "tcons ?\<theta>' T" "tcons ?\<theta>' U" using that(1,2) tcons_tnorm[OF ac'(1)] by (metis (mono_tags) \<T>_def mem_Collect_eq)+
    with fi[OF _ _ _ _ that(3)] that(1,2) show ?thesis by (auto simp: \<T>_def)
  qed
  have sub: "set Ts \<subseteq> \<T>" if "Type a Ts \<in> \<T>" for a Ts
  proof
    fix T assume T: "T \<in> set Ts"
    have "tnorm ?\<theta>' T = T" if "map (tnorm ?\<theta>') Us = Us" "T \<in> set Us" for Us
      using that by (induction Us) auto
    with \<open>Type a Ts \<in> \<T>\<close> T show "T \<in> \<T>" by (auto simp: \<T>_def)
  qed
  have arr: "(T \<rightarrow>\<^sub>T U) \<in> \<T>" if "T \<in> \<T>" "U \<in> \<T>" for T U
    using that by (auto simp: \<T>_def)
  have nty: "\<rho> v S \<noteq> Type a Ts" if "TVar v S \<in> \<T>" for v S a Ts
  proof -
    have "(v, S) \<in> tvars (tnorm ?\<theta>' (TVar v S))" using that by (simp add: \<T>_def)
    then have "vt_lookup ?\<theta>' v = None" by (rule tnorm_unbound[OF ac'(1)])
    with tf show ?thesis unfolding tfree_on_def by blast
  qed
  have g: "gsol alg ar ?\<theta> \<rho>" by (rule gsol_textends[OF ext(1) g'])
  have sol: "tsol ?\<theta> \<rho>" "tsol ?\<theta>' \<rho>" using g g' by (simp_all add: gsol_def)
  have io: "inst_ok ar (\<lambda>x. tsubst \<rho> (W0 x)) \<rho> [] s t env"
    using inst_ok_mod[OF inv Ap g s(1,2) t(1,2)] by (simp add: W0_def)
  from p g' io obtain W1
    where "ty_ext ar (\<lambda>x. tsubst \<rho> (W0 x)) (instE \<rho> env) W1 (instE \<rho> env')" by blast
  then have agV: "agreeV (maxidx env) (\<lambda>x. tsubst \<rho> (W0 x)) W1" and ety1: "env_typed W1 (instE \<rho> env')"
    and wf1: "wf_env ar (instE \<rho> env')" and fr1: "fresh_env (instE \<rho> env')"
    by (simp_all add: ty_ext_def)
  have ty1: "W1 x = tsubst \<rho> U \<and> has_type W1 [] (inst \<rho> u) (tsubst \<rho> U)"
    if "vt_lookup (tenv env') x = Some (U, u)" for x U u
    using env_typedD[OF ety1, of x] that by simp
  define X0 where "X0 = (\<Union>(r, U)\<in>set rs. vars r) \<union> fst ` bvps env \<union> {x. vt_lookup (tenv env) x \<noteq> None}"
  have X0: "snd x \<le> maxidx env \<and> (\<exists>U\<in>B0. W0 x = tnorm ?\<theta> U)" if "x \<in> X0" for x
  proof -
    have vp: "snd x \<le> maxidx env \<and> W0 x = tnorm ?\<theta> T"
      if "has_type W0 [] (tnormt ?\<theta> u) U" "(x, T) \<in> vps u" "below (maxidx env) u" for u U T
    proof -
      have "(x, tnorm ?\<theta> T) \<in> vps (tnormt ?\<theta> u)" using that(2) by (force simp: vps_tnormt)
      then have "W0 x = tnorm ?\<theta> T" by (rule has_type_vps[OF that(1)])
      moreover have "x \<in> vars u" using that(2) by (force simp: vars_vps)
      ultimately show ?thesis using that(3) by (simp add: below_def)
    qed
    from that consider r U where "(r, U) \<in> set rs" "x \<in> vars r" | "x \<in> fst ` bvps env"
      | U u where "vt_lookup (tenv env) x = Some (U, u)" by (auto simp: X0_def)
    then show ?thesis
    proof cases
      case 1
      from 1(1) rs have tyr: "has_type W0 [] (tnormt ?\<theta> r) (tnorm ?\<theta> U)" and br: "below (maxidx env) r"
        by (auto simp: typed_def W0_def)
      from 1(2) obtain T where "(x, T) \<in> vps r" by (auto simp: vars_vps)
      with vp[OF tyr _ br] vps_tys[of "(x, T)" r] 1(1) show ?thesis by (force simp: B0_def)
    next
      case 2
      then obtain T y U u where b: "vt_lookup (tenv env) y = Some (U, u)" and p: "(x, T) \<in> vps u"
        by (auto simp: bvps_def)
      have h: "has_type W0 [] (tnormt ?\<theta> u) (tnorm ?\<theta> U)" using env_typed_modD[OF i5 b] by blast
      have bl: "below (maxidx env) u" using fresh_envD[OF i(6) b] by blast
      have "T \<in> etys env" using vps_tys[OF p] etysI[OF b] by auto
      with vp[OF h p bl] show ?thesis by (auto simp: B0_def)
    next
      case 3
      then show ?thesis using env_typed_modD[OF i5 3] fresh_envD[OF i(6) 3] etysI[OF 3] by (auto simp: B0_def)
    qed
  qed
  define W' where "W' x = (if x \<in> X0 then tnorm ?\<theta>' (W0 x) else case vt_lookup (tenv env') x of
    Some (U, u) \<Rightarrow> tnorm ?\<theta>' U | None \<Rightarrow>
      if x \<in> fst ` bvps env' then tnorm ?\<theta>' (SOME T. (x, T) \<in> bvps env') else tnorm ?\<theta>' (W x))" for x
  have key: "W' x \<in> \<T> \<and> W1 x = tsubst \<rho> (W' x)"
    if "x \<in> X0 \<or> vt_lookup (tenv env') x \<noteq> None \<or> x \<in> fst ` bvps env'" for x
  proof (cases "x \<in> X0")
    case True
    with X0 obtain U where U: "U \<in> B0" "W0 x = tnorm ?\<theta> U"
      and ix: "snd x \<le> maxidx env" by blast
    have UB: "U \<in> B" using U(1) by (auto simp: B_def)
    have W'x: "W' x = tnorm ?\<theta>' U" using True U(2) by (simp add: W'_def tnorm_textends[OF ac'(1) ext(1)])
    have "W1 x = tsubst \<rho> (W0 x)" using agV ix unfolding agreeV_def by blast
    also have "\<dots> = tsubst \<rho> U" using U(2) tsubst_tnorm[OF ac sol(1) tc0[OF U(1)]] by simp
    also have "\<dots> = tsubst \<rho> (tnorm ?\<theta>' U)" using tsubst_tnorm[OF ac' sol(2) tc'[OF UB]] by simp
    finally show ?thesis using in\<T>[OF UB] W'x by simp
  next
    case False
    show ?thesis
    proof (cases "vt_lookup (tenv env') x")
      case (Some b)
      obtain U u where b: "b = (U, u)" by force
      have UB: "U \<in> B" using etysI[of env' x U u] Some b by (auto simp: B_def)
      have "W' x = tnorm ?\<theta>' U" using False Some b by (simp add: W'_def)
      moreover have "W1 x = tsubst \<rho> U" using ty1[of x U u] Some b by simp
      ultimately show ?thesis using in\<T>[OF UB] tsubst_tnorm[OF ac' sol(2) tc'[OF UB]] by simp
    next
      case None
      let ?T = "SOME T. (x, T) \<in> bvps env'"
      from that False None have xb: "x \<in> fst ` bvps env'" by force
      then have "\<exists>T. (x, T) \<in> bvps env'" by force
      then have "(x, ?T) \<in> bvps env'" by (rule someI_ex)
      then obtain y U u where b: "vt_lookup (tenv env') y = Some (U, u)" and p: "(x, ?T) \<in> vps u"
        by (auto simp: bvps_def)
      have TB: "?T \<in> B" using vps_tys[OF p] etysI[OF b] by (auto simp: B_def)
      have "W1 x = tsubst \<rho> ?T" using typed_inst_vps[OF conjunct2[OF ty1[OF b]] p] by simp
      moreover have "W' x = tnorm ?\<theta>' ?T" using False None xb by (simp add: W'_def)
      ultimately show ?thesis using in\<T>[OF TB] tsubst_tnorm[OF ac' sol(2) tc'[OF TB]] by simp
    qed
  qed
  have tm: "env_typed_mod ?\<theta>' W' env'"
    unfolding env_typed_mod_def
  proof (intro allI impI)
    fix x U u assume b: "vt_lookup (tenv env') x = Some (U, u)"
    have UB: "U \<in> B" and uB: "tys u \<subseteq> B" using etysI[OF b] by (auto simp: B_def)
    have kx: "W' x \<in> \<T>" "W1 x = tsubst \<rho> (W' x)" using key b by blast+
    note k = ty1[OF b]
    have eqU: "tsubst \<rho> (tnorm ?\<theta>' U) = tsubst \<rho> U" by (rule tsubst_tnorm[OF ac' sol(2) tc'[OF UB]])
    have Wx: "W' x = tnorm ?\<theta>' U" by (rule inj[OF kx(1) in\<T>[OF UB]]) (use kx(2) k eqU in simp)
    have "inst \<rho> (tnormt ?\<theta>' u) = inst \<rho> u"
      by (rule inst_tnormt[OF ac' sol(2)]) (use tc' uB in blast)
    then have hu: "has_type W1 (map (tsubst \<rho>) []) (inst \<rho> (tnormt ?\<theta>' u)) (tsubst \<rho> U)"
      using k by simp
    have "\<exists>U2\<in>\<T>. tsubst \<rho> U = tsubst \<rho> U2 \<and> has_type W' [] (tnormt ?\<theta>' u) U2"
    proof (rule has_type_reflect[where \<rho> = \<rho> and \<T> = \<T> and W = W', OF inj sub arr nty hu])
      show "tys (tnormt ?\<theta>' u) \<subseteq> \<T>" using uB in\<T> by (auto simp: tys_tnormt)
      fix y T assume "(y, T) \<in> vps (tnormt ?\<theta>' u)"
      then have "y \<in> fst ` bvps env'" using bvpsI[OF b] by (force simp: vps_tnormt)
      then show "W' y \<in> \<T> \<and> W1 y = tsubst \<rho> (W' y)" using key by blast
    qed simp_all
    then obtain U2 where "U2 \<in> \<T>" "tsubst \<rho> U = tsubst \<rho> U2" "has_type W' [] (tnormt ?\<theta>' u) U2" by blast
    moreover have "U2 = tnorm ?\<theta>' U" by (rule inj[OF calculation(1) in\<T>[OF UB]]) (use calculation(2) eqU in simp)
    ultimately show "W' x = tnorm ?\<theta>' U \<and> has_type W' [] (tnormt ?\<theta>' u) (tnorm ?\<theta>' U)" using Wx by simp
  qed
  have ti: "tinv ar (maxidx env') ?\<theta>' (etvars env')"
    by (rule tinv_subset[OF inv']) (use tw in \<open>auto simp: etvars_def tyw_def\<close>)
  have bi: "vt_lookup (tenv (instE \<rho> env')) x = Some (tsubst \<rho> U, inst \<rho> u)"
    if "vt_lookup (tenv env') x = Some (U, u)" for x U u
    using that by simp
  moreover have "pwf_env ar env'"
    unfolding pwf_env_def
  proof (intro allI impI)
    fix x U u assume b: "vt_lookup (tenv env') x = Some (U, u)"
    have "proper (inst \<rho> u) \<and> no_loose_bound (tr (inst \<rho> u)) 0"
      using wf1 bi[OF b] unfolding wf_env_def by blast
    moreover have "\<forall>T\<in>insert U (tys u). wft ar T" using tw etysI[OF b] by (auto simp: tyw_def)
    ultimately show "pwf_term ar 0 u \<and> wft ar U" by (simp add: pwf_term_def)
  qed
  moreover have "fresh_env env'"
    unfolding fresh_env_def using fresh_envD[OF fr1 bi] by simp
  moreover have nW': "tnorm ?\<theta>' (W' x) = W' x" for x
    by (simp add: W'_def tnorm_idem[OF ac'(1)] split: option.splits)
  ultimately have pinv: "penv_inv alg ar W' env'"
    using ti srt' nac mod_wt_env[OF tm nW'] by (simp add: penv_inv_def)
  have twW': "tyw ar ?\<theta>' A (W' x)" for x
  proof -
    have "tyw ar ?\<theta>' A (tnorm ?\<theta>' X)" if "tyw ar ?\<theta>' A X" for X by (rule tyw_tnorm[OF inv' that])
    moreover have "tyw ar ?\<theta>' A (tnorm ?\<theta>' (W0 x))" if "x \<in> X0"
    proof -
      from X0[OF that] obtain U where U: "U \<in> B0" "W0 x = tnorm ?\<theta> U" by blast
      have "tnorm ?\<theta>' (W0 x) = tnorm ?\<theta>' U" using U(2) by (simp add: tnorm_textends[OF ac'(1) ext(1)])
      then show ?thesis using tyw_tnorm[OF inv' twB[of U]] U(1) by (simp add: B_def)
    qed
    moreover have "tyw ar ?\<theta>' A U" if "vt_lookup (tenv env') x = Some (U, u)" for U u
      using tw etysI[OF that] by blast
    moreover have "tyw ar ?\<theta>' A (SOME T. (x, T) \<in> bvps env')" if "x \<in> fst ` bvps env'"
    proof -
      from that have "\<exists>T. (x, T) \<in> bvps env'" by force
      then have "(x, SOME T. (x, T) \<in> bvps env') \<in> bvps env'" by (rule someI_ex)
      then obtain y U u where b: "vt_lookup (tenv env') y = Some (U, u)"
        and p: "(x, SOME T. (x, T) \<in> bvps env') \<in> vps u"
        by (auto simp: bvps_def)
      show ?thesis using vps_tys[OF p] etysI[OF b] tw by auto
    qed
    moreover have "tyw ar ?\<theta>' A (W x)" using twW tyw_textends[OF ac'(1) ext(1)] by blast
    ultimately show ?thesis by (auto simp: W'_def split: option.splits)
  qed
  have wc: "wcons W' env'"
    unfolding wcons_def using env_typed_modD[OF tm] nW' by metis
  have ht: "typed env' W' [] u T"
    if "has_type W0 [] (tnormt ?\<theta> u) (tnorm ?\<theta> T)" "vars u \<subseteq> X0" for u T
    unfolding typed_def Poly_Typing.tctx_normal[OF tm nW']
  proof (rule has_type_vars)
    show "has_type (\<lambda>x. tnorm ?\<theta>' (W0 x)) (map (tnorm ?\<theta>') []) (tnormt ?\<theta>' u) (tnorm ?\<theta>' T)"
      using has_type_tnormt[OF that(1), of ?\<theta>']
      by (simp add: tnormt_textends[OF ac'(1) ext(1)] tnorm_textends[OF ac'(1) ext(1)])
  qed (use that(2) in \<open>auto simp: W'_def\<close>)
  have "\<forall>(r, U)\<in>set rs. typed env' W' [] r U"
  proof (clarify)
    fix r U assume rU: "(r, U) \<in> set rs"
    with rs have "has_type W0 [] (tnormt ?\<theta> r) (tnorm ?\<theta> U)" by (auto simp: typed_def W0_def)
    moreover have "vars r \<subseteq> X0" using rU by (auto simp: X0_def)
    ultimately show "typed env' W' [] r U" by (rule ht)
  qed
  then show thesis using that pinv twW' wc by blast
qed

end


subsection \<open>The pattern unification of the input pairs\<close>

context wf_algebra
begin

lemma foldM_unify_pinv:
  assumes finA: "finite A"
  shows "pinv alg ar A W env (dps_of tus) \<Longrightarrow>
    \<exists>r. foldM (\<lambda>(t, u) env. unify alg t u env) tus env = Some r \<and> fails_ok (Some r) \<and>
      (\<forall>env'. r = Ok env' \<longrightarrow> (\<exists>W'. pinv alg ar A W' env' []))"
proof (induction tus arbitrary: W env)
  case Nil
  then show ?case by (auto simp: return_def fails_ok_def intro: pinv_Nil)
next
  case (Cons tu tus)
  obtain t u where tu: "tu = (t, u)" by (cases tu)
  let ?\<theta> = "tyenv env"
  note pi = pinvD[OF Cons.prems]
  note pe = penv_invD[OF pi(1)]
  define Ty where "Ty p = (SOME U. typed env W [] (fst p) U \<and> typed env W [] (snd p) U)" for p
  have tyab: "typed env W [] a (Ty (a, b)) \<and> typed env W [] b (Ty (a, b))" if "(a, b) \<in> set (tu # tus)" for a b
  proof -
    from pi(4)[of "([], a, b)"] that have "\<exists>U. typed env W [] a U \<and> typed env W [] b U" by auto
    then show ?thesis unfolding Ty_def fst_conv snd_conv by (rule someI_ex)
  qed
  have dpab: "swf_dp ar ([], a, b) \<and> (\<forall>X\<in>tys a \<union> tys b. tyw ar ?\<theta> A X) \<and>
      below (maxidx env) a \<and> below (maxidx env) b" if "(a, b) \<in> set (tu # tus)" for a b
    using pi(4)[of "([], a, b)"] that by auto
  define rs where "rs = concat (map (\<lambda>p. [(fst p, Ty p), (snd p, Ty p)]) (tu # tus))"
  have rs: "\<forall>(r, U)\<in>set rs. typed env W [] r U \<and> below (maxidx env) r \<and> (\<forall>X\<in>tys r. tyw ar ?\<theta> A X)"
  proof (clarify)
    fix r U assume "(r, U) \<in> set rs"
    then have "\<exists>p\<in>set (tu # tus). (r = fst p \<or> r = snd p) \<and> U = Ty p"
      unfolding rs_def by (simp only: set_concat set_map) force
    then obtain a b where ab: "(a, b) \<in> set (tu # tus)" "r = a \<or> r = b" "U = Ty (a, b)"
      by (metis prod.collapse)
    then show "typed env W [] r U \<and> below (maxidx env) r \<and> (\<forall>X\<in>tys r. tyw ar ?\<theta> A X)"
      using tyab[OF ab(1)] dpab[OF ab(1)] by auto
  qed
  have srs: "(t, Ty (t, u)) \<in> set rs" "(u, Ty (t, u)) \<in> set rs" by (auto simp: rs_def tu)
  have tyt: "typed env W [] t (Ty (t, u))" "typed env W [] u (Ty (t, u))" using tyab[of t u] by (simp_all add: tu)
  from dpab[of t u] have wt: "swf_tm ar [] t" "swf_tm ar [] u" and twd: "\<forall>X\<in>tys t \<union> tys u. tyw ar ?\<theta> A X"
    and bl: "below (maxidx env) t" "below (maxidx env) u" by (simp_all add: tu swf_dp_def)
  have pw: "pwf_term ar 0 t" "pwf_term ar 0 u" using wt by (simp_all add: pwf_term_def swf_tm_def twft_tys)
  have Ap: "tinv ar (maxidx env) ?\<theta> (ptvars env t u)"
    by (rule tinv_subset[OF pi(2)]) (use twd pi(3) in \<open>fastforce simp: ptvars_def etvars_def tyw_def\<close>)
  have pre: "pre alg ar A [] t u env"
    unfolding pre_def
  proof (intro conjI allI impI pi(2) pe(2) bl)
    show "\<forall>T\<in>snd ` set [] \<union> tys t \<union> tys u \<union> etys env. tyw ar ?\<theta> A T" using twd pi(3) by auto
    fix \<rho> assume g: "gsol alg ar ?\<theta> \<rho>"
    show "\<exists>W. inst_ok ar W \<rho> [] t u env" using inst_ok_mod[OF pi(1) Ap g pw(1) tyt(1) pw(2) tyt(2)] by blast
  qed
  from unif_terminates[OF finA pre pe(3)] obtain r1 where u1: "unif alg [] t u env = Some r1" and tr: "tres A env r1"
    by blast
  note po = unif_post[OF u1 refl pre]
  show ?case
  proof (cases r1)
    case (Err e)
    then show ?thesis using u1 po tu by (auto simp: unify_def bindM_def post_all_def post_def fails_ok_def)
  next
    case (Ok env1)
    have pok: "postok alg ar A [] t u env env1" using po Ok by (simp add: post_all_def)
    have nac: "nacyc env1" using tr Ok by (simp add: tres_def)
    note p = pok[unfolded postok_def]
    obtain W1 where w1: "penv_inv alg ar W1 env1" "\<forall>x. tyw ar (tyenv env1) A (W1 x)" "wcons W1 env1"
      "\<forall>(r, U)\<in>set rs. typed env1 W1 [] r U"
      by (rule postok_pinv[OF pi(1,2) _ _ pw(1) tyt(1) pw(2) tyt(2) rs srs pok nac]) (use pi(3,5) in blast)+
    have ext: "textends ?\<theta> (tyenv env1)" "maxidx env \<le> maxidx env1" using p by blast+
    have ac1: "tacyc (tyenv env1)" using tinv_tacyc p by blast
    have dqs: "\<forall>dq\<in>set (dps_of tus). swf_dp ar dq \<and> (\<forall>T\<in>dtys dq. tyw ar (tyenv env1) A T) \<and>
        ptyped env1 W1 dq \<and> dp_below (maxidx env1) dq"
    proof
      fix dq assume "dq \<in> set (dps_of tus)"
      then obtain a b where dq: "dq = ([], a, b)" "(a, b) \<in> set tus" by auto
      then have ab: "(a, b) \<in> set (tu # tus)" by simp
      have "(a, Ty (a, b)) \<in> set rs" "(b, Ty (a, b)) \<in> set rs" using dq(2) by (force simp: rs_def)+
      then have "typed env1 W1 [] a (Ty (a, b))" "typed env1 W1 [] b (Ty (a, b))" using w1(4) by auto
      then show "swf_dp ar dq \<and> (\<forall>T\<in>dtys dq. tyw ar (tyenv env1) A T) \<and> ptyped env1 W1 dq \<and>
          dp_below (maxidx env1) dq"
        using dpab[OF ab] tyw_textends[OF ac1 ext(1)] below_mono[OF _ ext(2)] dq(1) by (auto simp: dp_below_def)
    qed
    have pi1: "pinv alg ar A W1 env1 (dps_of tus)"
      using w1 dqs p unfolding pinv_def by blast
    from Cons.IH[OF pi1] obtain r where r: "foldM (\<lambda>(t, u) env. unify alg t u env) tus env1 = Some r"
      "fails_ok (Some r)" "\<forall>env'. r = Ok env' \<longrightarrow> (\<exists>W'. pinv alg ar A W' env' [])" by blast
    have "foldM (\<lambda>(t, u) env. unify alg t u env) (tu # tus) env = Some r"
      using u1 Ok r(1) tu by (simp add: unify_def bindM_def)
    with r(2,3) show ?thesis by blast
  qed
qed

end

subsection \<open>Termination of \<^const>\<open>unifiers\<close>\<close>

context wf_algebra
begin

text \<open>
  For a well-typed problem with type variables, \<^const>\<open>unifiers\<close> terminates without an
  exception and enumerates finitely many unifiers in the invariant, for every configuration.
\<close>

theorem unifiers_pfin:
  assumes cfg: "cfg_alg cfg = alg" and finA: "finite A" and pi: "pinv alg ar A W env (dps_of tus)"
  obtains s where "unifiers alg env tus = Some (Ok s)"
    "fin cfg s (\<lambda>x. \<exists>env' tps. x = El_R env' tps \<and> (\<exists>W'. pinv alg ar A W' env' []))"
proof -
  from foldM_unify_pinv[OF finA pi] obtain r where
    r: "foldM (\<lambda>(t, u) env. unify alg t u env) tus env = Some r" "fails_ok (Some r)"
      "\<forall>env'. r = Ok env' \<longrightarrow> (\<exists>W'. pinv alg ar A W' env' [])"
    by blast
  show thesis
  proof (cases r)
    case (Ok env')
    with r have "unifiers alg env tus = Some (Ok (S_Single (El_R env' [])))"
      by (simp add: unifiers_def handle_def bindM_def return_def)
    moreover have "fin cfg (S_Single (El_R env' [])) (\<lambda>x. \<exists>env' tps. x = El_R env' tps \<and> (\<exists>W'. pinv alg ar A W' env' []))"
      using r(3) Ok by (auto intro: fin_Single)
    ultimately show thesis by (rule that)
  next
    case (Err e)
    with r(2) have "e = Pattern \<or> (\<exists>u. e = Unif u)" by (simp add: fails_ok_def exn_ok_def)
    then show thesis
    proof
      assume "e = Pattern"
      with r(1) Err have "unifiers alg env tus = Some (Ok (hounifiers [] env tus))"
        by (simp add: unifiers_def handle_def bindM_def return_def)
      moreover have "fin cfg (hounifiers [] env tus) (\<lambda>x. \<exists>env' tps. x = El_R env' tps \<and> (\<exists>W'. pinv alg ar A W' env' []))"
        by (rule hounifiers_pfin[OF cfg finA]) (use pi in simp)
      ultimately show thesis by (rule that)
    next
      assume "\<exists>u. e = Unif u"
      with r(1) Err have "unifiers alg env tus = Some (Ok S_Empty)"
        by (auto simp: unifiers_def handle_def bindM_def return_def)
      then show thesis by (rule that) simp
    qed
  qed
qed

end
end

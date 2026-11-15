section \<open>The Certified Results of Matching\<close>

theory Thm_Match
  imports Match_Range Thm_Rules2
begin

text \<open>
  \<open>Thm.match\<close> and \<open>Thm.first_order_match\<close> (\<open>gen_match\<close> of \<open>thm.ML\<close>) match the terms of two
  certified terms with \<open>Pattern.match\<close> or \<open>Pattern.first_order_match\<close> from the empty
  environment. From each binding \<open>?'a \<mapsto> T\<close> they make the certified type \<open>T\<close>, from each binding
  \<open>?x :: U \<mapsto> t\<close> the certified term \<open>t\<close> of type \<open>Envir.subst_type Tinsts U\<close>, for the variable \<open>?x\<close>
  of this type; both get the maximal index of the object and the sorts of the pattern and the
  object, without certification. \<open>Thm.instantiate\<close> takes such instantiations.

  The theorem says that these records are right: if the two certified terms are well formed and
  record the sorts of their terms, the types and terms made from the bindings are well formed
  (\<^const>\<open>ctyp_ok\<close>, \<^const>\<open>cterm_ok\<close>: certified types; closed terms of the recorded type;
  indices between \<open>0\<close> and the recorded maximal index; for types, sorts among the recorded
  ones), the terms record their sorts again, and the instantiated variables have proper
  indices (which \<open>Thm.instantiate\<close> checks, with the fix \<open>thm-instantiate-index\<close>). Being well
  formed is the premise of the rule \<open>instantiate\<close> on its instantiations; their sorts are
  finitely many sorts over the classes of the signature if those of the two certified terms are.
\<close>

lemma tsorts_tvars_tfrees: "tsorts T = snd ` tvars T \<union> snd ` tfrees T"
  by (induction T) auto

lemma tm_sorts_typs: "tm_sorts t = (\<Union>T\<in>typs t. tsorts T)"
  by (induction t) auto

lemma ttvars_sorts: "snd ` ttvars t \<subseteq> tm_sorts t" and ttfrees_sorts: "snd ` ttfrees t \<subseteq> tm_sorts t"
  unfolding tm_sorts_typs tsorts_tvars_tfrees ttvars_def ttfrees_def by blast+

lemma tm_sorts_sub: "tm_sorts t \<subseteq> snd ` ttvars t \<union> snd ` ttfrees t"
  by (induction t) (auto simp: tsorts_tvars_tfrees)

theorem match_cterms_ok:
  fixes ct1 ct2 :: cterm_data
  defines "c \<equiv> cd_sign ct2" and "mx \<equiv> ct_maxidx (cd_rep ct2)" and "Ss \<equiv> cd_sorts ct1 \<union> cd_sorts ct2"
  assumes ps: "pure_sig (sg_alg c) (sg_ar c)"
    and ok: "cterm_ok ct1" "cterm_ok ct2" and sg: "cd_sign ct1 = cd_sign ct2"
    and so: "tm_sorts (ct_t (cd_rep ct1)) \<subseteq> cd_sorts ct1" "tm_sorts (ct_t (cd_rep ct2)) \<subseteq> cd_sorts ct2"
    and m: "ok ((if fo then first_order_match else match) (sg_alg c) (ct_t (cd_rep ct1)) (ct_t (cd_rep ct2))
      (vt_empty, vt_empty)) (Tinsts, tinsts)"
  shows "vt_lookup Tinsts v = Some (S, T) \<Longrightarrow>
      ctyp_ok \<lparr>cty_T = T, cty_maxidx = mx, cty_sorts = Ss, cty_sign = c\<rparr> \<and> snd v \<noteq> -1"
    and "vt_lookup tinsts x = Some (U, t) \<Longrightarrow> ok (subst_type Tinsts U) T' \<Longrightarrow>
      cterm_ok \<lparr>cd_rep = CTerm t T' mx, cd_sorts = Ss, cd_sign = c\<rparr> \<and> tm_sorts t \<subseteq> Ss \<and> snd x \<noteq> -1"
proof -
  interpret pure_sig "sg_alg c" "sg_ar c" "sg_consts c" by (rule ps)
  let ?pt = "ct_t (cd_rep ct1)" and ?ob = "ct_t (cd_rep ct2)"
  have w1: "cterm_wf (cd_rep ct1)" and w2: "cterm_wf (cd_rep ct2)"
    using ok ps sg by (simp_all add: cterm_ok_def c_def)
  have cl: "closed ?pt" "closed ?ob" and ty: "\<And>e. e \<turnstile> ?pt : ct_T (cd_rep ct1)" "\<And>e. e \<turnstile> ?ob : ct_T (cd_rep ct2)"
    and ib: "ibelow mx ?ob" and mx: "-1 \<le> mx"
    and i1: "\<forall>v\<in>vars ?pt. 0 \<le> snd (fst v)" "\<forall>v\<in>ttvars ?pt. 0 \<le> snd (fst v)"
    and i2: "\<forall>v\<in>vars ?ob. 0 \<le> snd (fst v)" "\<forall>v\<in>ttvars ?ob. 0 \<le> snd (fst v)"
    using w1 w2 by (simp_all add: cterm_wf_def mx_def)
  note r = match_range[OF m cl ty(1)[of undefined] ty(2)[of undefined]]
  have e0: "btyped vt_empty vt_empty" "bstable (vt_empty, vt_empty)" "tye_cert vt_empty"
    by (simp_all add: btyped_def bstable_def tye_cert_def)
  have bt: "btyped Tinsts tinsts"
  proof (cases fo)
    case True
    with m have m': "ok (first_order_match (sg_alg c) ?pt ?ob (vt_empty, vt_empty)) (Tinsts, tinsts)" by simp
    have wp: "\<forall>U\<in>typs ?pt. wft (sg_ar c) U" using typing_typs_cert[OF ty(1)] by (auto simp: cert_wft)
    from first_order_match_sound(3)[OF m' cl(2) ty(2)[of undefined] wp] e0 show ?thesis by simp
  next
    case False
    with m have m': "ok (match (sg_alg c) ?pt ?ob (vt_empty, vt_empty)) (Tinsts, tinsts)" by simp
    from match_sound(3)[OF m' cl ty(1)[of undefined] ty(2)[of undefined]] e0 show ?thesis by simp
  qed
  show "ctyp_ok \<lparr>cty_T = T, cty_maxidx = mx, cty_sorts = Ss, cty_sign = c\<rparr> \<and> snd v \<noteq> -1"
    if l: "vt_lookup Tinsts v = Some (S, T)"
  proof -
    note rv = r(2)[OF l]
    have "cert_typ (sg_alg c) (sg_ar c) T" using r(1) l unfolding tye_cert_def by blast
    moreover have "0 \<le> snd (fst w) \<and> snd (fst w) \<le> mx" if "w \<in> tvars T" for w
      using that rv ib i2(2) by (auto simp: ibelow_def)
    moreover have "tsorts T \<subseteq> Ss"
    proof -
      from rv have s: "tvars T \<subseteq> ttvars ?ob" "tfrees T \<subseteq> ttfrees ?ob \<union> ttfrees ?pt" by blast+
      have "snd ` tvars T \<subseteq> tm_sorts ?ob" by (rule subset_trans[OF image_mono[OF s(1)] ttvars_sorts])
      moreover have "snd ` tfrees T \<subseteq> tm_sorts ?ob \<union> tm_sorts ?pt"
        using image_mono[OF s(2), of snd] ttfrees_sorts[of ?ob] ttfrees_sorts[of ?pt]
        unfolding image_Un by blast
      ultimately show ?thesis using so unfolding tsorts_tvars_tfrees Ss_def by blast
    qed
    moreover have "snd v \<noteq> -1" using rv i1(2) by auto
    ultimately show ?thesis using mx by (simp add: ctyp_ok_def)
  qed
  show "cterm_ok \<lparr>cd_rep = CTerm t T' mx, cd_sorts = Ss, cd_sign = c\<rparr> \<and> tm_sorts t \<subseteq> Ss \<and> snd x \<noteq> -1"
    if l: "vt_lookup tinsts x = Some (U, t)" and st: "ok (subst_type Tinsts U) T'"
  proof -
    note rx = r(3)[OF l]
    have T': "T' = tsubst (mtinst Tinsts) U" by (rule ok_subst_type[OF st])
    from bt l have "closed t \<and> (\<forall>e. e \<turnstile> t : T')" unfolding btyped_def T' by blast
    then have "closed t" "\<And>e. e \<turnstile> t : T'" by blast+
    moreover have "ibelow mx t" using rx ib by (auto simp: ibelow_def)
    moreover have "\<forall>v\<in>vars t. 0 \<le> snd (fst v)" "\<forall>v\<in>ttvars t. 0 \<le> snd (fst v)" using rx i2 by auto
    moreover have "snd x \<noteq> -1" using rx i1(1) by auto
    moreover have "tm_sorts t \<subseteq> Ss"
    proof -
      from rx have s: "ttvars t \<subseteq> ttvars ?ob" "ttfrees t \<subseteq> ttfrees ?ob \<union> ttfrees ?pt" by blast+
      have "snd ` ttvars t \<subseteq> tm_sorts ?ob" by (rule subset_trans[OF image_mono[OF s(1)] ttvars_sorts])
      moreover have "snd ` ttfrees t \<subseteq> tm_sorts ?ob \<union> tm_sorts ?pt"
        using image_mono[OF s(2), of snd] ttfrees_sorts[of ?ob] ttfrees_sorts[of ?pt]
        unfolding image_Un by blast
      ultimately have "snd ` ttvars t \<union> snd ` ttfrees t \<subseteq> tm_sorts ?ob \<union> tm_sorts ?pt"
        by (simp add: le_supI1)
      then have "tm_sorts t \<subseteq> tm_sorts ?ob \<union> tm_sorts ?pt" by (rule subset_trans[OF tm_sorts_sub])
      moreover have "tm_sorts ?ob \<union> tm_sorts ?pt \<subseteq> Ss" using so by (simp add: Ss_def le_supI1 le_supI2)
      ultimately show ?thesis by (rule subset_trans)
    qed
    ultimately show ?thesis using mx by (simp add: cterm_ok_def cterm_wf_def)
  qed
qed

end

section \<open>Proofs: Thm_Assumption\<close>

theory Thm_Assumption_Proofs
  imports "Thm_Soundness.Thm_Assumption" Thm_Subst_Rules_Proofs
begin

text \<open>
  The classic and tight proofs of the results of the rules of theory \<open>Thm_Assumption\<close> are valid
  (the part of the invariant of theorems that session \<open>Thm_Soundness\<close> leaves out).
\<close>

context prf_sig_gen
begin

lemma env_inv_props:
  assumes "env_inv E"
  shows "zenv_nn E" "eneg E" "tacyc (tyenv E)" "tcons_env (tyenv E)"
    "acyc E" "closed_env E" "\<forall>w\<in>evars E. 0 \<le> snd (fst w)"
proof -
  have b: "acyc E" "closed_env E" "tacyc (tyenv E)" "tcons_env (tyenv E)" "\<forall>(x, T)\<in>evars E. 0 \<le> snd x"
    "\<forall>p\<in>tvars_env (tyenv E). 0 \<le> snd (fst p)"
    "\<forall>x U u. vt_lookup (tenv E) x = Some (U, u) \<longrightarrow> (\<forall>p\<in>tvars U \<union> ttvars u. 0 \<le> snd (fst p))"
    using assms unfolding env_inv_def by blast+
  show "acyc E" "closed_env E" "tacyc (tyenv E)" "tcons_env (tyenv E)" by (fact b(1), fact b(2), fact b(3), fact b(4))
  show ev: "\<forall>w\<in>evars E. 0 \<le> snd (fst w)" using b(5) by (simp add: case_prod_beta)
  have bn: "(x, U, u) \<in> bnds E" if "vt_lookup (tenv E) x = Some (U, u)" for x U u
    using that by (simp add: bnds_def)
  have val: "pnn u" if "vt_lookup (tenv E) x = Some (U, u)" for x U u
  proof -
    have "vars u \<subseteq> evars E" using bn[OF that] unfolding evars_def by blast
    with ev have "\<forall>v\<in>vars u. 0 \<le> snd (fst v)" by blast
    moreover have "\<forall>p\<in>ttvars u. 0 \<le> snd (fst p)" using b(7) that by blast
    ultimately show ?thesis by (simp add: pnn_iff')
  qed
  show "zenv_nn E" unfolding zenv_nn_def using b(6) val by (auto simp: pnn_def)
  have x: "0 \<le> snd x" if "vt_lookup (tenv E) x = Some (U, u)" for x U u
  proof -
    have "(x, U) \<in> evars E" using bn[OF that] unfolding evars_def by blast
    with ev show ?thesis by force
  qed
  show "eneg E" unfolding eneg_def
    using tyenv_ok_nn[OF b(6)] val x pnn_noneg integer_nonneg_ne_m1 by blast
qed

end

context prf_sig_gen
begin

text \<open>Normalizing a classic proof keeps its invariants:\<close>

lemma norm_proof_remove_types_closed:
  assumes nq: "norm_proof_remove_types env p = returnW q" and ei: "env_inv env"
    and p: "prf_idx (\<lambda>i. 0 \<le> i) p" "prf_nolb 0 p"
  shows "prf_idx (\<lambda>i. 0 \<le> i) q \<and> prf_nolb 0 q"
proof -
  let ?E = "remove_types_env env"
  note e = env_inv_props[OF ei]
  have ac': "acyc ?E" "closed_env ?E" "tacyc (tyenv ?E)" using e(5,6,3) by (simp_all add: remove_types_env_props)
  have n: "norm_proof ?E p = returnW q" using nq by (simp add: norm_proof_remove_types_def)
  have "prf_idx (\<lambda>i. 0 \<le> i) q"
  proof (rule prf_idx_norm_proof[OF n])
    fix t t' assume t: "t \<in> prf_terms p" and nt: "ok (norm_term ?E t) t'"
    show "\<forall>v\<in>vars t'. 0 \<le> snd (fst v)"
    proof
      fix v assume "v \<in> vars t'"
      from vars_norm_term_idx[OF nt ac' this] obtain w where w: "w \<in> vars t \<union> evars env" "fst w = fst v"
        by (auto simp: remove_types_env_props)
      from w(1) have "0 \<le> snd (fst w)" using p(1) t e(7) by (auto simp: prf_idx_def)
      with w(2) show "0 \<le> snd (fst v)" by simp
    qed
  qed
  moreover have "prf_nolb 0 q"
    by (rule prf_nolb_norm_proof[OF n _ _ p(2)]) (use loose_bvar_norm_term[OF _ ac'] in auto)
  ultimately show ?thesis by blast
qed

text \<open>The tight proof of a result of \<^const>\<open>assumption\<close> keeps the invariants:\<close>

lemma zassumption_proof_props:
  assumes z: "zassumption_proof ztargs env Bs Bi n vis q = return r" and q: "zinv q" "znolb 0 q"
    and tac: "tacyc (tyenv env)" and en: "zenv_nn env" and ce: "closed_env env"
    and vv: "\<forall>(x, T)\<in>set (visible_vars vis). 0 \<le> snd x \<and> tnn T"
    and vt: "\<forall>(v, S)\<in>set (visible_tvars vis). 0 \<le> snd v"
    and pA: "\<forall>A\<in>set (Bs @ [Bi]). pnn A \<and> closed A"
  shows "zinv r \<and> znolb 0 r \<and> zhyps r \<subseteq> zhyps q"
proof -
  let ?normt = "\<lambda>t. bindM (zterm_of ztargs t) (znorm_term ztargs env)"
  from z obtain Ns N where Ns: "mapM ?normt Bs = return Ns" and N: "?normt Bi = return N"
    and zn: "znorm_proof ztargs env vis (ZAbsps Ns (ZAppps q (map ZBoundp (downto (integer_of_nat (length Bs) - 1) 0) @
      [zmk_asm_prf N n (zasm_count (-1) Bi)]))) = return r"
    by (auto simp: zassumption_proof_def Let_def bindZ_eq_returnZ)
  have normt: "zterm_ok t' \<and> \<not> zloose t' 0" if "?normt t = return t'" "t \<in> set (Bs @ [Bi])" for t t'
  proof -
    from that(1) obtain z where z: "zterm_of ztargs t = return z" "znorm_term ztargs env z = return t'"
      by (auto simp: bindZ_eq_returnZ)
    have "zterm_ok t'" using zterm_ok_zterm_of_pnn[OF z(1)] pA that(2) zterm_ok_znorm_term[OF z(2) tac en] by blast
    have "closed t" using pA that(2) by blast
    then have "\<not> zloose z 0" using zloose_zterm_of[OF z(1)] by (simp add: closed_def)
    from zloose_znorm_term[OF z(2) tac ce _ this] have "\<not> zloose t' 0" by simp
    with \<open>zterm_ok t'\<close> show ?thesis by blast
  qed
  have NsP: "zterm_ok t' \<and> \<not> zloose t' 0" if "t' \<in> set Ns" for t'
  proof -
    from list_all2_ex2[OF Ns[unfolded mapZ_eq_returnZ] that] obtain t where "t \<in> set Bs" "?normt t = return t'"
      by blast
    with normt show ?thesis by auto
  qed
  have NP: "zterm_ok N \<and> \<not> zloose N 0" by (rule normt[OF N]) simp
  let ?a = "ZAbsps Ns (ZAppps q (map ZBoundp (downto (integer_of_nat (length Bs) - 1) 0) @
      [zmk_asm_prf N n (zasm_count (-1) Bi)]))"
  have ai: "zinv ?a" using q(1) NsP NP zinv_zmk_asm_prf by (auto simp: zinv_ZAbsps zinv_ZAppps)
  have an: "znolb 0 ?a" using q(2) NsP NP zmk_asm_prf_closed by (auto simp: znolb_ZAbsps znolb_ZAppps)
  have ah: "zhyps ?a \<subseteq> zhyps q" using NP zmk_asm_prf_closed[of N 0] by (auto simp: zhyps_ZAppps)
  have zc: "zconsts_ok ?a" using ai by (simp add: zinv_def)
  note c = znorm_proof_closed[OF zn zc tac ce]
  show ?thesis using zinv_znorm_proof[OF zn ai tac en vv vt] c(1)[OF an] c(2) ah by blast
qed

text \<open>The proofs of the results of \<^const>\<open>assumption\<close> are valid and keep the invariants:\<close>

theorem assumption_proof_ok:
  assumes a: "okT (assumption i state) s0" and res: "aresult (unify_ops cfg vl) s0 r"
    and cfg: "cfg_alg cfg = alg" and st: "thm_inv (th_maxidx state) hs (th_tpairs state) (th_prop state)"
    and pr: "ares_proof (aseq_ctx s0) r pf = returnW q"
    and p: "prf_valid ax H (th_tpairs state) pf (th_prop state)" "prf_idx (\<lambda>i. 0 \<le> i) pf" "prf_nolb 0 pf"
    and nf: "nfree (ar_env r)" and l0: "\<forall>x\<in>loose. 0 \<le> snd x"
  shows "prf_valid ax H (th_tpairs (ar_thm r)) q (th_prop (ar_thm r)) \<and> prf_idx (\<lambda>i. 0 \<le> i) q \<and> prf_nolb 0 q"
proof -
  obtain tpairs Bs Bi C params asms concl l env tps A K X where
    d: "okT (dest_state state i) (tpairs, Bs, Bi, C)" and ap: "assum_problems (-1) Bi = (params, asms, concl)"
    and s0: "s0 = AQ_Try (ACtx (th_maxidx state) tpairs Bs Bi C params concl) asms 1" and l: "l < length asms"
    and ur: "ures (empty_env (th_maxidx state)) ((rlist_abs params (asms ! l), rlist_abs params concl) # tpairs) (El_R env tps)"
    and pw: "pwf (empty_env (th_maxidx state)) ((rlist_abs params (asms ! l), rlist_abs params concl) # tpairs)"
    and nt: "okT (newth (ACtx (th_maxidx state) tpairs Bs Bi C params concl) (integer_of_nat l + 1) (env, tps)) r"
    and re: "ar_env r = env" and ei: "einv A K env" and wi: "winv env X"
    and tw: "\<forall>(t, u)\<in>set tps. closed t \<and> closed u \<and>
      (\<forall>\<rho>. tsol (tyenv env) \<rho> \<longrightarrow> cert_inst \<rho> \<longrightarrow> (\<exists>e T. e \<turnstile> inst \<rho> t : T \<and> e \<turnstile> inst \<rho> u : T))"
    by (rule assumption_data[OF a res cfg st nf])
  have nf': "nfree env" using nf re by simp
  let ?ctx = "ACtx (th_maxidx state) tpairs Bs Bi C params concl"
  have pr': "ares_proof ?ctx r pf = returnW q" using pr s0 by simp
  have w: "wtp (th_prop state)" using st by (simp add: thm_inv_def wt_thm_def)
  have "prf_valid ax H (th_tpairs (ar_thm r)) q (th_prop (ar_thm r))"
  proof (rule ares_proof_valid[OF d ap l nt pr' p(1) w ei wi tw])
    show "nfree env" by (rule nf')
  next
    fix \<rho>' \<sigma>' F t u e assume sol: "solution \<rho>' \<sigma>' env" and ci: "cert_inst \<rho>'"
      and ts: "\<And>t u e. (t, u) \<in> set tps \<Longrightarrow> eqv F e (ap \<rho>' \<sigma>' t) (ap \<rho>' \<sigma>' u)"
      and tu: "(t, u) \<in> set ((rlist_abs params (asms ! l), rlist_abs params concl) # tpairs)"
    show "eqv F e (ap \<rho>' \<sigma>' t) (ap \<rho>' \<sigma>' u)" by (rule ures_solves_eqv[OF ur pw sol ci ts tu nf'])
  qed
  moreover have "prf_idx (\<lambda>i. 0 \<le> i) q \<and> prf_nolb 0 q"
  proof -
    have ev: "env_inv env" using assumption_thm_inv[OF a res cfg st nf l0] re by simp
    from pr' re obtain Ns where Ns: "liftMP (mapM (norm_term env) Bs) = returnW Ns"
      and q: "(if env_is_empty env then returnW (assumption_proof Ns Bi (integer_of_nat l + 1) pf)
        else norm_proof_remove_types env (assumption_proof Ns Bi (integer_of_nat l + 1) pf)) = returnW q"
      using okT_newth[OF nt] by (auto simp: ares_proof_def Let_def bindP_eq_returnP split: ares.splits)
    have p0: "prf_idx (\<lambda>i. 0 \<le> i) (assumption_proof Ns Bi (integer_of_nat l + 1) pf)"
      "prf_nolb 0 (assumption_proof Ns Bi (integer_of_nat l + 1) pf)"
      using p(2,3) by (auto simp: assumption_proof_def prf_idx_mk_AbsP prf_idx_proof_combP prf_idx_mk_asm_prf
        prf_nolb_proof_combP prf_nolb_mk_asm_prf)
    show ?thesis
    proof (cases "env_is_empty env")
      case True
      with q p0 show ?thesis by (simp add: returnW_def)
    next
      case False
      with q have "norm_proof_remove_types env (assumption_proof Ns Bi (integer_of_nat l + 1) pf) = returnW q" by simp
      from norm_proof_remove_types_closed[OF this ev p0] show ?thesis .
    qed
  qed
  ultimately show ?thesis by blast
qed

theorem assumption_zproof_ok:
  assumes a: "okT (assumption i state) s0" and res: "aresult (unify_ops cfg vl) s0 r"
    and cfg: "cfg_alg cfg = alg" and st: "thm_inv (th_maxidx state) hs (th_tpairs state) (th_prop state)"
    and z: "ares_zproof ztargs state (aseq_ctx s0) r pf = return q"
    and p: "zvalid ax H (th_tpairs state) pf (th_prop state)" "zinv pf" "znolb 0 pf"
    and H: "\<forall>h\<in>H. closed h" and nf: "nfree (ar_env r)" and l0: "\<forall>x\<in>loose. 0 \<le> snd x"
  shows "zvalid ax H (th_tpairs (ar_thm r)) q (th_prop (ar_thm r)) \<and> zinv q \<and> znolb 0 q \<and> zhyps q \<subseteq> zhyps pf"
proof -
  obtain tpairs Bs Bi C params asms concl l env tps A K X where
    d: "okT (dest_state state i) (tpairs, Bs, Bi, C)" and ap: "assum_problems (-1) Bi = (params, asms, concl)"
    and s0: "s0 = AQ_Try (ACtx (th_maxidx state) tpairs Bs Bi C params concl) asms 1" and l: "l < length asms"
    and ur: "ures (empty_env (th_maxidx state)) ((rlist_abs params (asms ! l), rlist_abs params concl) # tpairs) (El_R env tps)"
    and pw: "pwf (empty_env (th_maxidx state)) ((rlist_abs params (asms ! l), rlist_abs params concl) # tpairs)"
    and nt: "okT (newth (ACtx (th_maxidx state) tpairs Bs Bi C params concl) (integer_of_nat l + 1) (env, tps)) r"
    and re: "ar_env r = env" and ei: "einv A K env" and wi: "winv env X"
    and tw: "\<forall>(t, u)\<in>set tps. closed t \<and> closed u \<and>
      (\<forall>\<rho>. tsol (tyenv env) \<rho> \<longrightarrow> cert_inst \<rho> \<longrightarrow> (\<exists>e T. e \<turnstile> inst \<rho> t : T \<and> e \<turnstile> inst \<rho> u : T))"
    by (rule assumption_data[OF a res cfg st nf])
  have nf': "nfree env" using nf re by simp
  let ?ctx = "ACtx (th_maxidx state) tpairs Bs Bi C params concl"
  have z': "ares_zproof ztargs state ?ctx r pf = return q" using z s0 by simp
  have ev: "env_inv env" using assumption_thm_inv[OF a res cfg st nf l0] re by simp
  note e = env_inv_props[OF ev]
  note ds = okT_dest_state[OF d]
  have wS: "wtp (th_prop state)" using st by (simp add: thm_inv_def wt_thm_def)
  have P: "th_prop state = list_implies (Bs @ [Bi]) C"
    using list_implies_strip_prems[OF ds(2) wtpD(2)[OF wS, of "\<lambda>_. propT"]] by simp
  have pA: "\<forall>A\<in>set (Bs @ [Bi]). pnn A \<and> closed A"
    using thm_inv_pnn(1)[OF st] wtpD(1)[OF wS] P
    by (auto simp: pnn_list_implies closed_def loose_bvar_list_implies)
  have "zvalid ax H (th_tpairs (ar_thm r)) q (th_prop (ar_thm r))"
  proof (rule zares_proof_valid[OF d ap l nt z' p(1) st _ H _ ei wi e(3,4) e(2) tw])
    show "nfree env" by (rule nf')
  next
    show "\<forall>A\<in>set (Bs @ [Bi]). noneg A" using pA pnn_noneg by blast
    show "zconsts_ok pf" using p(2) by (simp add: zinv_def)
    fix \<rho>' \<sigma>' F t u e assume sol: "solution \<rho>' \<sigma>' env" and ci: "cert_inst \<rho>'"
      and ts: "\<And>t u e. (t, u) \<in> set tps \<Longrightarrow> eqv F e (ap \<rho>' \<sigma>' t) (ap \<rho>' \<sigma>' u)"
      and tu: "(t, u) \<in> set ((rlist_abs params (asms ! l), rlist_abs params concl) # tpairs)"
    show "eqv F e (ap \<rho>' \<sigma>' t) (ap \<rho>' \<sigma>' u)" by (rule ures_solves_eqv[OF ur pw sol ci ts tu nf'])
  qed
  moreover have "zinv q \<and> znolb 0 q \<and> zhyps q \<subseteq> zhyps pf"
  proof -
    from z' re obtain fp where fp: "ok (full_prop_of (th_tpairs state) (th_prop state)) fp"
      and za: "zassumption_proof ztargs env Bs Bi (integer_of_nat l + 1) [fp] pf = return q"
      using okT_newth[OF nt] by (auto simp: ares_zproof_def bindZ_eq_returnZ liftMZ_eq_returnZ split: ares.splits)
    have "\<forall>t\<in>set [fp]. pnn t" using thm_inv_full_prop_of(1)[OF st fp] by simp
    note vp = visible_pnn[OF this]
    show ?thesis by (rule zassumption_proof_props[OF za p(2,3) e(3) e(1) e(6) vp(1,2) pA])
  qed
  ultimately show ?thesis by blast
qed

end

context prf_sig
begin

theorem assumption_proof_ok:
  assumes a: "okT (assumption i state) s0" and res: "aresult (unify_ops cfg vl) s0 r"
    and cfg: "cfg_alg cfg = alg" and st: "thm_inv (th_maxidx state) hs (th_tpairs state) (th_prop state)"
    and pr: "ares_proof (aseq_ctx s0) r pf = returnW q"
    and p: "prf_valid ax H (th_tpairs state) pf (th_prop state)" "prf_idx (\<lambda>i. 0 \<le> i) pf" "prf_nolb 0 pf"
  shows "prf_valid ax H (th_tpairs (ar_thm r)) q (th_prop (ar_thm r)) \<and> prf_idx (\<lambda>i. 0 \<le> i) q \<and> prf_nolb 0 q"
  by (rule assumption_proof_ok[OF a res cfg st pr p nfree0]) simp

theorem assumption_zproof_ok:
  assumes a: "okT (assumption i state) s0" and res: "aresult (unify_ops cfg vl) s0 r"
    and cfg: "cfg_alg cfg = alg" and st: "thm_inv (th_maxidx state) hs (th_tpairs state) (th_prop state)"
    and z: "ares_zproof ztargs state (aseq_ctx s0) r pf = return q"
    and p: "zvalid ax H (th_tpairs state) pf (th_prop state)" "zinv pf" "znolb 0 pf"
    and H: "\<forall>h\<in>H. closed h"
  shows "zvalid ax H (th_tpairs (ar_thm r)) q (th_prop (ar_thm r)) \<and> zinv q \<and> znolb 0 q \<and> zhyps q \<subseteq> zhyps pf"
  by (rule assumption_zproof_ok[OF a res cfg st z p H nfree0]) simp

end

context prf_sig_gen
begin

theorem flexflex_proof_ok:
  assumes a: "okT (flexflex_rule (unify_ops cfg vl) th) s0" and res: "fresult (unify_ops cfg vl) smashT th s0 (env, th')"
    and cfg: "cfg_alg cfg = alg" and st: "thm_inv (th_maxidx th) hs (th_tpairs th) (th_prop th)"
    and ne: "\<not> (env_is_empty env \<and> \<not> (\<exists>(t, u)\<in>set (th_tpairs th). aconv_term t u))"
    and nq: "norm_proof_remove_types env pf = returnW q"
    and p: "prf_valid ax H (th_tpairs th) pf (th_prop th)" "prf_idx (\<lambda>i. 0 \<le> i) pf" "prf_nolb 0 pf"
    and nf: "nfree env" and l0: "\<forall>x\<in>loose. 0 \<le> snd x"
  shows "prf_valid ax H (th_tpairs th') q (th_prop th') \<and> prf_idx (\<lambda>i. 0 \<le> i) q \<and> prf_nolb 0 q"
proof -
  obtain A' K' X' where n: "ok (fnewth th env) th'" and ei: "einv A' K' env" and wi: "winv env X'"
    by (rule flexflex_data[OF a res cfg st nf])
  have ws: "wt_thm (th_maxidx th) hs (th_tpairs th) (th_prop th)" using st by (simp add: thm_inv_def)
  have ev: "env_inv env" using flexflex_thm_inv[OF a res cfg st nf l0] by simp
  have "prf_valid ax H (th_tpairs th') q (th_prop th')"
  proof (rule flexflex_proof_valid[OF n ne nq p(1) _ _ ei wi])
    show "wtp (th_prop th)" using ws by (simp add: wt_thm_def)
    show "closed t \<and> closed u \<and> (\<exists>T. \<forall>e. e \<turnstile> t : T \<and> e \<turnstile> u : T)" if "(t, u) \<in> set (th_tpairs th)" for t u
      using ws that by (auto simp: wt_thm_def)
    show "nfree env" by (rule nf)
  qed
  with norm_proof_remove_types_closed[OF nq ev p(2,3)] show ?thesis by blast
qed

theorem flexflex_zproof_ok:
  assumes a: "okT (flexflex_rule (unify_ops cfg vl) th) s0" and res: "fresult (unify_ops cfg vl) smashT th s0 (env, th')"
    and cfg: "cfg_alg cfg = alg" and st: "thm_inv (th_maxidx th) hs (th_tpairs th) (th_prop th)"
    and ne: "\<not> (env_is_empty env \<and> \<not> (\<exists>(t, u)\<in>set (th_tpairs th). aconv_term t u))"
    and z: "flexflex_zproof ztargs th env pf = return q"
    and p: "zvalid ax H (th_tpairs th) pf (th_prop th)" "zinv pf" "znolb 0 pf"
    and H: "\<forall>h\<in>H. closed h" and nf: "nfree env" and l0: "\<forall>x\<in>loose. 0 \<le> snd x"
  shows "zvalid ax H (th_tpairs th') q (th_prop th') \<and> zinv q \<and> znolb 0 q \<and> zhyps q \<subseteq> zhyps pf"
proof -
  obtain A' K' X' where n: "ok (fnewth th env) th'" and ei: "einv A' K' env" and wi: "winv env X'"
    by (rule flexflex_data[OF a res cfg st nf])
  have ev: "env_inv env" using flexflex_thm_inv[OF a res cfg st nf l0] by simp
  note e = env_inv_props[OF ev]
  have zc: "zconsts_ok pf" using p(2) by (simp add: zinv_def)
  have "zvalid ax H (th_tpairs th') q (th_prop th')"
    by (rule zflexflex_proof_valid[OF n ne z p(1) st ei wi e(3,4) e(2) H zc nf])
  moreover have "zinv q \<and> znolb 0 q \<and> zhyps q \<subseteq> zhyps pf"
  proof -
    from z obtain fp where fp: "ok (full_prop_of (th_tpairs th) (th_prop th)) fp"
      and zq: "znorm_proof ztargs env [fp] pf = return q"
      by (auto simp: flexflex_zproof_def bindZ_eq_returnZ liftMZ_eq_returnZ)
    have "\<forall>t\<in>set [fp]. pnn t" using thm_inv_full_prop_of(1)[OF st fp] by simp
    note vp = visible_pnn[OF this]
    note c = znorm_proof_closed[OF zq zc e(3) e(6)]
    show ?thesis using zinv_znorm_proof[OF zq p(2) e(3) e(1) vp(1,2)] c(1)[OF p(3)] c(2) by blast
  qed
  ultimately show ?thesis by blast
qed

end

context prf_sig
begin

theorem flexflex_proof_ok:
  assumes a: "okT (flexflex_rule (unify_ops cfg vl) th) s0" and res: "fresult (unify_ops cfg vl) smashT th s0 (env, th')"
    and cfg: "cfg_alg cfg = alg" and st: "thm_inv (th_maxidx th) hs (th_tpairs th) (th_prop th)"
    and ne: "\<not> (env_is_empty env \<and> \<not> (\<exists>(t, u)\<in>set (th_tpairs th). aconv_term t u))"
    and nq: "norm_proof_remove_types env pf = returnW q"
    and p: "prf_valid ax H (th_tpairs th) pf (th_prop th)" "prf_idx (\<lambda>i. 0 \<le> i) pf" "prf_nolb 0 pf"
  shows "prf_valid ax H (th_tpairs th') q (th_prop th') \<and> prf_idx (\<lambda>i. 0 \<le> i) q \<and> prf_nolb 0 q"
  by (rule flexflex_proof_ok[OF a res cfg st ne nq p nfree0]) simp

theorem flexflex_zproof_ok:
  assumes a: "okT (flexflex_rule (unify_ops cfg vl) th) s0" and res: "fresult (unify_ops cfg vl) smashT th s0 (env, th')"
    and cfg: "cfg_alg cfg = alg" and st: "thm_inv (th_maxidx th) hs (th_tpairs th) (th_prop th)"
    and ne: "\<not> (env_is_empty env \<and> \<not> (\<exists>(t, u)\<in>set (th_tpairs th). aconv_term t u))"
    and z: "flexflex_zproof ztargs th env pf = return q"
    and p: "zvalid ax H (th_tpairs th) pf (th_prop th)" "zinv pf" "znolb 0 pf"
    and H: "\<forall>h\<in>H. closed h"
  shows "zvalid ax H (th_tpairs th') q (th_prop th') \<and> zinv q \<and> znolb 0 q \<and> zhyps q \<subseteq> zhyps pf"
  by (rule flexflex_zproof_ok[OF a res cfg st ne z p H nfree0]) simp

end


lemma proofs_ok_eq_assumption:
  fixes th :: "'u pure_thm"
  assumes ok: "okT (eq_assumption i (rep_of th)) (n, r)" and d: "okT (dest_state (rep_of th) i) (tpairs, Bs, Bi, C)"
    and po_th: "is_prf_sig (sign_of th) \<Longrightarrow> proofs_ok (rep_thm th)"
  shows "is_prf_sig (th_sign (mk_thm r (shyps_of th) (hyps_of th) (sign_of th)
    (bindW (proof_of th) (\<lambda>p. returnW (assumption_proof Bs Bi n p)))
    (bindM (zproof_of th) (eq_assumption_zproof (pure_sig_gen.ztargs (sg_consts (sign_of th))) Bs Bi n)))) \<Longrightarrow>
    proofs_ok (mk_thm r (shyps_of th) (hyps_of th) (sign_of th)
    (bindW (proof_of th) (\<lambda>p. returnW (assumption_proof Bs Bi n p)))
    (bindM (zproof_of th) (eq_assumption_zproof (pure_sig_gen.ztargs (sg_consts (sign_of th))) Bs Bi n)))"
    (is "_ \<Longrightarrow> proofs_ok ?th")
proof -
  let ?c = "sign_of th"
  have P: "th_prop (rep_of th) = list_implies (Bs @ [Bi]) C"
    if w: "pure_sig_gen.wtp (sg_alg ?c) (sg_ar ?c) (sg_consts ?c) (th_prop (rep_of th))" and ps: "pure_sig (sg_alg ?c) (sg_ar ?c)"
  proof -
    interpret pure_sig "sg_alg ?c" "sg_ar ?c" "sg_consts ?c" by (rule ps)
    show ?thesis using list_implies_strip_prems[OF okT_dest_state(2)[OF d] wtpD(2)[OF w, of "\<lambda>_. propT"]] by simp
  qed
  assume psig: "is_prf_sig (th_sign ?th)"
  then interpret prf_sig "sg_alg ?c" "sg_ar ?c" "sg_consts ?c" "sg_close ?c" "sg_tyargs ?c"
    by (simp add: is_prf_sig_def)
  have ps: "pure_sig (sg_alg ?c) (sg_ar ?c)" using psig by (simp add: is_prf_sig_def prf_sig_def)
  have w0: "thm_wf (th_maxidx (rep_of th)) (hyps_of th) (th_tpairs (rep_of th)) (th_prop (rep_of th))"
    using pure_thm_wf[of th] ps by simp
  have w: "wtp (th_prop (rep_of th))" using w0 by (simp add: thm_wf_def wt_thm_def)
  note P' = P[OF w ps]
  have pP: "pnn (th_prop (rep_of th))" using w0 by (simp add: thm_wf_def vars_thm_def tvars_thm_def pnn_iff)
  have pA: "pnn A" if "A \<in> set (Bs @ [Bi])" for A
    using pP that P' typs_list_implies_sub(1)[OF that, of C] by (auto simp: pnn_def vars_list_implies)
  have cA: "closed A" if "A \<in> set (Bs @ [Bi])" for A
    using wtpD(1)[OF w] that P' by (auto simp: closed_def loose_bvar_list_implies)
  have H: "\<forall>h\<in>set (hyps_of th). closed h" using w0 by (auto simp: thm_wf_def wt_thm_def wtp_def)
  have p: "proofs_ok (rep_thm th)" by (rule po_th) (use psig in simp)
  show "proofs_ok ?th" unfolding proofs_ok_def Let_def mk_thm_sel
  proof (rule conjI; intro allI impI)
    fix pf assume "bindW (proof_of th) (\<lambda>p. returnW (assumption_proof Bs Bi n p)) = returnW pf"
    then obtain q where q: "proof_of th = returnW q" and pf: "pf = assumption_proof Bs Bi n q"
      by (auto simp: bindP_eq_returnP)
    have vq: "prf_valid (sg_ax ?c) (set (hyps_of th)) (th_tpairs (rep_of th)) q (th_prop (rep_of th))"
      "prf_idx (\<lambda>i. 0 \<le> i) q" "prf_nolb 0 q"
      using p q by (simp_all add: proofs_ok_def Let_def)
    have "prf_valid (sg_ax ?c) (set (hyps_of th)) (th_tpairs r) pf (th_prop r)"
      unfolding pf by (rule eq_assumption_proof_valid[OF ok d vq(1) w])
    moreover have "prf_idx (\<lambda>i. 0 \<le> i) pf" "prf_nolb 0 pf"
      using vq(2,3) by (auto simp: pf assumption_proof_def prf_idx_mk_AbsP prf_idx_proof_combP prf_idx_mk_asm_prf
        prf_nolb_proof_combP prf_nolb_mk_asm_prf)
    ultimately show "prf_valid (sg_ax ?c) (set (hyps_of th)) (th_tpairs r) pf (th_prop r) \<and>
        prf_idx (\<lambda>i. 0 \<le> i) pf \<and> prf_nolb 0 pf" by simp
  next
    fix z assume "bindM (zproof_of th) (eq_assumption_zproof ztargs Bs Bi n) = return z"
    then obtain q where q: "zproof_of th = return q" and z: "eq_assumption_zproof ztargs Bs Bi n q = return z"
      by (auto simp: bindZ_eq_returnZ)
    have vq: "zvalid (sg_ax ?c) (set (hyps_of th)) (th_tpairs (rep_of th)) q (th_prop (rep_of th))" "zinv q"
      "znolb 0 q" "zhyps_ok q"
      using p q by (simp_all add: proofs_ok_def Let_def)
    have "zvalid (sg_ax ?c) (set (hyps_of th)) (th_tpairs r) z (th_prop r)"
      by (rule zeq_assumption_proof_valid[OF ok d vq(1) w _ H z]) (use pA pnn_noneg in blast)
    moreover have "zinv z \<and> znolb 0 z \<and> zhyps z \<subseteq> zhyps q"
    proof -
      let ?env = "empty_env (-1) :: env"
      from z obtain Ns Z0 N where Ns: "list_all2 (\<lambda>B N. \<exists>Z. zterm_of ztargs B = return Z \<and>
          znorm_term ztargs ?env Z = return N) Bs Ns"
        and Z0: "zterm_of ztargs Bi = return Z0" and N: "znorm_term ztargs ?env Z0 = return N"
        and bn: "beta_norm_prooft (ZAbsps Ns (ZAppps q (map ZBoundp (downto (integer_of_nat (length Bs) - 1) 0) @
          [zmk_asm_prf N n (zasm_count (-1) Bi)]))) = Some z"
        by (auto simp: eq_assumption_zproof_def zassumption_proof_def znorm_proof_def Let_def bindZ_eq_returnZ
          mapZ_eq_returnZ liftOZ_eq_returnZ)
      have nt: "zterm_ok N' \<and> \<not> zloose N' 0" if "zterm_of ztargs A = return Z" "znorm_term ztargs ?env Z = return N'"
        "A \<in> set (Bs @ [Bi])" for A Z N'
      proof -
        have bt: "beta_norm_term Z = Some N'" using that(2) by (simp add: znorm_term_def liftOZ_eq_returnZ env_is_empty_def empty_env_def)
        show ?thesis using zterm_ok_beta_norm_term[OF bt zterm_ok_zterm_of_pnn[OF that(1) pA[OF that(3)]]]
          zloose_beta_norm_term[OF bt, of 0] zloose_zterm_of[OF that(1)] cA[OF that(3)] by (simp add: closed_def)
      qed
      have Nsz: "zterm_ok N' \<and> \<not> zloose N' 0" if "N' \<in> set Ns" for N'
      proof -
        from that obtain j where j: "j < length Ns" "N' = Ns ! j" by (auto simp: in_set_conv_nth)
        have jl: "j < length Bs" using j(1) list_all2_lengthD[OF Ns] by simp
        from list_all2_nthD[OF Ns jl] j(2) obtain Z where "zterm_of ztargs (Bs ! j) = return Z"
          "znorm_term ztargs ?env Z = return N'" by blast
        with nt nth_mem[OF jl] show ?thesis by simp
      qed
      have Nz: "zterm_ok N \<and> \<not> zloose N 0" by (rule nt[OF Z0 N]) simp
      have arg: "zinv (ZAbsps Ns (ZAppps q (map ZBoundp (downto (integer_of_nat (length Bs) - 1) 0) @
          [zmk_asm_prf N n (zasm_count (-1) Bi)])))"
        using vq(2) Nsz Nz zinv_zmk_asm_prf by (auto simp: zinv_ZAbsps zinv_ZAppps)
      have arg2: "znolb 0 (ZAbsps Ns (ZAppps q (map ZBoundp (downto (integer_of_nat (length Bs) - 1) 0) @
          [zmk_asm_prf N n (zasm_count (-1) Bi)])))"
        using vq(3) Nsz Nz zmk_asm_prf_closed by (auto simp: znolb_ZAbsps znolb_ZAppps)
      from zinv_beta_norm_prooft[OF bn arg] beta_norm_prooft_closed[OF bn, of 0] arg2
      show ?thesis using zmk_asm_prf_closed[of N 0] Nz by (auto simp: zhyps_ZAppps)
    qed
    ultimately show "zvalid (sg_ax ?c) (set (hyps_of th)) (th_tpairs r) z (th_prop r) \<and> zinv z \<and> znolb 0 z \<and>
        zhyps_ok z" using vq(4) by (auto simp: zhyps_ok_def)
  qed
qed

lemma proofs_ok_thm_of_ares_gen:
  assumes ps: "pure_sig (sg_alg (sign_of state)) (sg_ar (sign_of state))"
    and cfg: "cfg_alg cfg = sg_alg (sign_of state)"
    and sc: "scons (pure_sig_gen.tvars_thm (th_tpairs (rep_of state)) (th_prop (rep_of state)))"
    and a: "okT (assumption i (rep_of state)) s0" and res: "aresult (unify_ops cfg vl) s0 r"
    and nb: "binds_none (ar_env r) (ares_clash state)"
    and psig: "is_prf_sig (sign_of state)"
    and po_state: "is_prf_sig (sign_of state) \<Longrightarrow> proofs_ok (rep_thm state)"
  shows "proofs_ok (thm_of_ares (state :: 'u pure_thm) (aseq_ctx s0) r)"
proof -
  let ?c = "sign_of state" and ?th = "thm_of_ares state (aseq_ctx s0) r"
  let ?L = "ares_clash state"
  interpret pure_sig_gen "sg_alg ?c" "sg_ar ?c" "sg_consts ?c" ?L using ps unfolding pure_sig_def .
  have st0: "thm_inv0 (th_maxidx (rep_of state)) (hyps_of state) (th_tpairs (rep_of state)) (th_prop (rep_of state))"
    using pure_thm_inv0[OF ps] sc by simp
  have nfL: "nfree (ar_env r)" using nb by (rule nfree_binds_none)
  have l0: "\<forall>x\<in>?L. 0 \<le> snd x" using st0 by (fastforce simp: thm_inv0_def vclash_def ares_clash_def)
  have lv: "lvtcons (vars_thm (th_tpairs (rep_of state)) (th_prop (rep_of state)))"
    by (rule lvtcons_vclash) (simp add: ares_clash_def)
  have st: "thm_inv (th_maxidx (rep_of state)) (hyps_of state) (th_tpairs (rep_of state)) (th_prop (rep_of state))"
    by (rule iffD2[OF thm_inv_iff, OF conjI[OF st0 lv]])
  note ti = assumption_thm_inv[OF a res cfg st nfL l0]
  obtain tpairs Bs Bi C params asms concl l env tps where
    "okT (dest_state (rep_of state) i) (tpairs, Bs, Bi, C)" "assum_problems (-1) Bi = (params, asms, concl)"
    "s0 = AQ_Try (ACtx (th_maxidx (rep_of state)) tpairs Bs Bi C params concl) asms 1" "l < length asms"
    "ures (empty_env (th_maxidx (rep_of state))) ((rlist_abs params (asms ! l), rlist_abs params concl) # tpairs) (El_R env tps)"
    and nt: "okT (newth (ACtx (th_maxidx (rep_of state)) tpairs Bs Bi C params concl) (integer_of_nat l + 1) (env, tps)) r"
    "sinv (tvars_thm (th_tpairs (rep_of state)) (th_prop (rep_of state))) (tvars_thm (th_tpairs (rep_of state)) (th_prop (rep_of state)))
      (vars_thm (th_tpairs (rep_of state)) (th_prop (rep_of state))) (empty_env (th_maxidx (rep_of state)))
      (tdps ((rlist_abs params (asms ! l), rlist_abs params concl) # tpairs))"
    by (rule assumption_result[OF a res cfg st])
  have mx: "th_maxidx (ar_thm r) = maxidx (ar_env r)" using okT_newth[OF nt(1)] by simp
  have ws: "wt_thm (th_maxidx (rep_of state)) (hyps_of state) (th_tpairs (rep_of state)) (th_prop (rep_of state))"
    using st by (simp add: thm_inv_def)
  interpret prf_sig_gen "sg_alg ?c" "sg_ar ?c" "sg_consts ?c" ?L "sg_close ?c" "sg_tyargs ?c"
    using psig by (simp add: is_prf_sig_def prf_sig_gen_of)
  have po: "proofs_ok (rep_thm state)" by (rule po_state[OF psig])
  have sg: "th_sign ?th = ?c" by (simp add: thm_of_ares_def)
  show ?thesis unfolding proofs_ok_def Let_def sg
  proof (rule conjI; intro allI impI)
    fix p assume "th_proof ?th = returnW p"
    then obtain pf where pf: "proof_of state = returnW pf" and pr: "ares_proof (aseq_ctx s0) r pf = returnW p"
      by (auto simp: thm_of_ares_def bindP_eq_returnP)
    have vq: "prf_valid (sg_ax ?c) (set (hyps_of state)) (th_tpairs (rep_of state)) pf (th_prop (rep_of state))"
      "prf_idx (\<lambda>i. 0 \<le> i) pf" "prf_nolb 0 pf"
      using po pf by (simp_all add: proofs_ok_def Let_def)
    from assumption_proof_ok[OF a res cfg st pr vq nfL l0]
    show "prf_valid (sg_ax ?c) (set (th_hyps ?th)) (th_tpairs ?th) p (th_prop ?th) \<and> prf_idx (\<lambda>i. 0 \<le> i) p \<and> prf_nolb 0 p"
      by (simp add: thm_of_ares_def)
  next
    fix z assume "th_zproof ?th = return z"
    then obtain pf where pf: "zproof_of state = return pf"
      and z: "ares_zproof ztargs (rep_of state) (aseq_ctx s0) r pf = return z"
      by (auto simp: thm_of_ares_def bindZ_eq_returnZ)
    have vq: "zvalid (sg_ax ?c) (set (hyps_of state)) (th_tpairs (rep_of state)) pf (th_prop (rep_of state))"
      "zinv pf" "znolb 0 pf" "zhyps_ok pf"
      using po pf by (simp_all add: proofs_ok_def Let_def)
    have H: "\<forall>h\<in>set (hyps_of state). closed h" using ws by (auto simp: wt_thm_def dest: wtpD(1))
    note zr = assumption_zproof_ok[OF a res cfg st z vq(1-3) H nfL l0]
    have "zhyps_ok z" using zhyps_ok_mono[OF vq(4)] zr by blast
    with zr show "zvalid (sg_ax ?c) (set (th_hyps ?th)) (th_tpairs ?th) z (th_prop ?th) \<and> zinv z \<and> znolb 0 z \<and>
        zhyps_ok z"
      by (simp add: thm_of_ares_def)
  qed
qed

lemma proofs_ok_thm_of_fres_gen:
  assumes ps: "pure_sig (sg_alg (sign_of th)) (sg_ar (sign_of th))"
    and cfg: "cfg_alg cfg = sg_alg (sign_of th)" and sc: "scons (pure_sig_gen.tvars_thm (th_tpairs (rep_of th)) (th_prop (rep_of th)))"
    and a: "okT (flexflex_rule (unify_ops cfg vl) (rep_of th)) s0"
    and res: "fresult (unify_ops cfg vl) smashT (rep_of th) s0 (env, r)"
    and nb: "binds_none env (ares_clash th)"
    and psig: "is_prf_sig (sign_of th)"
    and po_th: "is_prf_sig (sign_of th) \<Longrightarrow> proofs_ok (rep_thm th)"
  shows "proofs_ok (thm_of_fres (th :: 'u pure_thm) env r)"
proof (cases "env_is_empty env \<and> \<not> (\<exists>(t, u)\<in>set (th_tpairs (rep_of th)). aconv_term t u)")
  case True
  then show ?thesis using po_th psig by (simp add: thm_of_fres_def)
next
  case False
  let ?c = "sign_of th" and ?th = "thm_of_fres th env r"
  have eq: "?th = with_cons (env_constraints env) (mk_thm r (shyps_of th \<union> env_sorts env) (hyps_of th) (sign_of th)
      (bindW (proof_of th) (norm_proof_remove_types env))
      (bindM (zproof_of th) (flexflex_zproof (pure_sig_gen.ztargs (sg_consts (sign_of th))) (rep_of th) env)))"
    unfolding thm_of_fres_def if_not_P[OF False] ..
  let ?L = "ares_clash th"
  interpret pure_sig_gen "sg_alg ?c" "sg_ar ?c" "sg_consts ?c" ?L using ps unfolding pure_sig_def .
  have st0: "thm_inv0 (th_maxidx (rep_of th)) (hyps_of th) (th_tpairs (rep_of th)) (th_prop (rep_of th))"
    using pure_thm_inv0[OF ps] sc by simp
  have nfL: "nfree env" using nb by (rule nfree_binds_none)
  have l0: "\<forall>x\<in>?L. 0 \<le> snd x" using st0 by (fastforce simp: thm_inv0_def vclash_def ares_clash_def)
  have lv: "lvtcons (vars_thm (th_tpairs (rep_of th)) (th_prop (rep_of th)))"
    by (rule lvtcons_vclash) (simp add: ares_clash_def)
  have st: "thm_inv (th_maxidx (rep_of th)) (hyps_of th) (th_tpairs (rep_of th)) (th_prop (rep_of th))"
    by (rule iffD2[OF thm_inv_iff, OF conjI[OF st0 lv]])
  note ti = flexflex_thm_inv[OF a res cfg st nfL l0]
  have ws: "wt_thm (th_maxidx (rep_of th)) (hyps_of th) (th_tpairs (rep_of th)) (th_prop (rep_of th))"
    using st by (simp add: thm_inv_def)
  interpret prf_sig_gen "sg_alg ?c" "sg_ar ?c" "sg_consts ?c" ?L "sg_close ?c" "sg_tyargs ?c"
    using psig by (simp add: is_prf_sig_def prf_sig_gen_of)
  have po: "proofs_ok (rep_thm th)" by (rule po_th[OF psig])
  show ?thesis unfolding proofs_ok_def Let_def eq with_cons_sel mk_thm_sel
  proof (rule conjI; intro allI impI)
    fix p assume "bindW (proof_of th) (norm_proof_remove_types env) = returnW p"
    then obtain pf where pf: "proof_of th = returnW pf" and nq: "norm_proof_remove_types env pf = returnW p"
      by (auto simp: bindP_eq_returnP)
    have vq: "prf_valid (sg_ax ?c) (set (hyps_of th)) (th_tpairs (rep_of th)) pf (th_prop (rep_of th))"
      "prf_idx (\<lambda>i. 0 \<le> i) pf" "prf_nolb 0 pf"
      using po pf by (simp_all add: proofs_ok_def Let_def)
    from flexflex_proof_ok[OF a res cfg st False nq vq nfL l0]
    show "prf_valid (sg_ax ?c) (set (hyps_of th)) (th_tpairs r) p (th_prop r) \<and> prf_idx (\<lambda>i. 0 \<le> i) p \<and> prf_nolb 0 p" .
  next
    fix z assume "bindM (zproof_of th) (flexflex_zproof ztargs (rep_of th) env) = return z"
    then obtain pf where pf: "zproof_of th = return pf" and z: "flexflex_zproof ztargs (rep_of th) env pf = return z"
      by (auto simp: bindZ_eq_returnZ)
    have vq: "zvalid (sg_ax ?c) (set (hyps_of th)) (th_tpairs (rep_of th)) pf (th_prop (rep_of th))"
      "zinv pf" "znolb 0 pf" "zhyps_ok pf"
      using po pf by (simp_all add: proofs_ok_def Let_def)
    have H: "\<forall>h\<in>set (hyps_of th). closed h" using ws by (auto simp: wt_thm_def dest: wtpD(1))
    note zr = flexflex_zproof_ok[OF a res cfg st False z vq(1-3) H nfL l0]
    have "zhyps_ok z" using zhyps_ok_mono[OF vq(4)] zr by blast
    with zr show "zvalid (sg_ax ?c) (set (hyps_of th)) (th_tpairs r) z (th_prop r) \<and> zinv z \<and> znolb 0 z \<and> zhyps_ok z"
      by blast
  qed
qed

end

section \<open>Proofs: Thm_Bicompose\<close>

theory Thm_Bicompose_Proofs
  imports Thm_Bicompose Thm_Axiom_Proofs
begin

text \<open>
  The classic and tight proofs of the results of the rules of theory \<open>Thm_Bicompose\<close> are valid
  (the part of the invariant of theorems that session \<open>Thm_Soundness\<close> leaves out).
\<close>

lemma proofs_ok_thm_of_bc:
  assumes ps: "pure_sig (sg_alg (sign_of state)) (sg_ar (sign_of state))"
    and cfg: "cfg_alg cfg = sg_alg (sign_of state)" and vl: "\<And>xs. length (vl xs) = length xs"
    and sr: "sign_of rule = sign_of state" and sc: "bc_scons state rule"
    and vc: "incremented \<Longrightarrow> bc_vcons state rule"
    and d: "okT (dest_state (rep_of state) i) (stpairs, Bs, Bi, C)"
    and ok: "okT (bicompose_aux (unify_ops cfg vl) (sg_alg (sign_of state)) flatten match_flg incremented
      (pthm_of (rep_of state)) (stpairs, Bs, Bi, C) False e (pthm_of (rep_of rule)) nsubgoal) xq"
    and rx: "pure_sig_gen.bresult (unify_ops cfg vl) xq x"
    and psig: "is_prf_sig (sign_of state)"
    and po_state: "is_prf_sig (sign_of state) \<Longrightarrow> proofs_ok (rep_thm state)"
    and po_rule: "is_prf_sig (sign_of rule) \<Longrightarrow> proofs_ok (rep_thm rule)"
  shows "proofs_ok (thm_of_bc (sign_of state) i (state :: 'u pure_thm) flatten e rule x)"
proof -
  let ?c = "sign_of state"
  interpret pure_sig "sg_alg ?c" "sg_ar ?c" "sg_consts ?c" by (rule ps)
  note a = bc_args[OF ps sr sc vc]
  note st = a(1) and ru = a(2) and tv = a(3) and vc' = a(4)
  obtain rAs B env where tp: "stpairs = th_tpairs (rep_of state)"
    and SP: "th_prop (rep_of state) = list_implies (Bs @ [Bi]) C"
    and ti: "thm_inv (maxidx (br_env x)) (hyps_of state @ hyps_of rule) (br_tpairs x) (br_prop x)"
    by (rule bicompose_setup[OF d ok rx cfg vl a]) blast
  interpret prf_sig "sg_alg ?c" "sg_ar ?c" "sg_consts ?c" "sg_close ?c" "sg_tyargs ?c"
    using psig by (simp add: is_prf_sig_def)
  have ps: "proofs_ok (rep_thm state)" by (rule po_state[OF psig])
  have pr: "proofs_ok (rep_thm rule)" by (rule po_rule) (simp add: sr psig)
  have sg_eq: "th_sign (thm_of_bc ?c i state flatten e rule x) = ?c" by (simp add: thm_of_bc_def)
  show ?thesis unfolding proofs_ok_def Let_def sg_eq
  proof (rule conjI; intro allI impI)
    fix p assume "th_proof (thm_of_bc ?c i state flatten e rule x) = returnW p"
    then obtain rp sp where rp: "proof_of rule = returnW rp" and sp: "proof_of state = returnW sp"
      and p: "bc_proof (rep_of state) i e flatten x rp sp = returnW p"
      by (auto simp: thm_of_bc_def bindP_eq_returnP)
    have "prf_valid (sg_ax ?c) (set (hyps_of state @ hyps_of rule)) (br_tpairs x) p (br_prop x) \<and>
        prf_idx (\<lambda>i. 0 \<le> i) p \<and> prf_nolb 0 p"
      by (rule bicompose_thm_proof_valid[OF d ok rx cfg vl st ru tv vc' _ _ _ _ _ _ p])
        (use ps sp pr rp sr in \<open>simp_all add: proofs_ok_def Let_def\<close>)
    then show "prf_valid (sg_ax ?c)
        (set (th_hyps (thm_of_bc ?c i state flatten e rule x))) (th_tpairs (thm_of_bc ?c i state flatten e rule x)) p
        (th_prop (thm_of_bc ?c i state flatten e rule x)) \<and> prf_idx (\<lambda>i. 0 \<le> i) p \<and> prf_nolb 0 p"
      by (simp add: thm_of_bc_def)
  next
    fix z assume "th_zproof (thm_of_bc ?c i state flatten e rule x) = return z"
    then obtain rp sp where rp: "zproof_of rule = return rp" and sp: "zproof_of state = return sp"
      and z: "bc_zproof ztargs (rep_of state) i e flatten (rep_of rule) x rp sp = return z"
      by (auto simp: thm_of_bc_def bindZ_eq_returnZ)
    have zs: "zinv sp" "znolb 0 sp" "zhyps_ok sp" "zinv rp" "znolb 0 rp" "zhyps_ok rp"
      using ps sp pr rp sr by (simp_all add: proofs_ok_def Let_def)
    have "zvalid (sg_ax ?c) (set (hyps_of state @ hyps_of rule)) (br_tpairs x) z (br_prop x) \<and> zinv z \<and>
        znolb 0 z \<and> zhyps z \<subseteq> zhyps sp \<union> zhyps rp"
      by (rule bicompose_thm_zproof_valid[OF d ok rx cfg vl st ru tv vc' _ zs(1,2) _ zs(4,5) z])
        (use ps sp pr rp sr in \<open>simp_all add: proofs_ok_def Let_def\<close>)
    moreover have "zhyps_ok z" if "zhyps z \<subseteq> zhyps sp \<union> zhyps rp"
      using that zs(3,6) by (auto simp: zhyps_ok_def)
    ultimately show "zvalid (sg_ax ?c)
        (set (th_hyps (thm_of_bc ?c i state flatten e rule x))) (th_tpairs (thm_of_bc ?c i state flatten e rule x)) z
        (th_prop (thm_of_bc ?c i state flatten e rule x)) \<and> zinv z \<and> znolb 0 z \<and> zhyps_ok z"
      by (simp add: thm_of_bc_def)
  qed
qed

lemma proofs_ok_thm_of_bc_gen:
  assumes ps: "pure_sig (sg_alg (sign_of state)) (sg_ar (sign_of state))"
    and cfg: "cfg_alg cfg = sg_alg (sign_of state)" and vl: "\<And>xs. length (vl xs) = length xs"
    and sr: "sign_of rule = sign_of state" and sc: "bc_scons state rule"
    and d: "okT (dest_state (rep_of state) i) (stpairs, Bs, Bi, C)"
    and ok: "okT (bicompose_aux (unify_ops cfg vl) (sg_alg (sign_of state)) flatten match_flg incremented
      (pthm_of (rep_of state)) (stpairs, Bs, Bi, C) False e (pthm_of (rep_of rule)) nsubgoal) xq"
    and rx: "pure_sig_gen.bresult (unify_ops cfg vl) xq x"
    and nb: "binds_none (br_env x) (bc_clash state rule x)"
    and psig: "is_prf_sig (sign_of state)"
    and po_state: "is_prf_sig (sign_of state) \<Longrightarrow> proofs_ok (rep_thm state)"
    and po_rule: "is_prf_sig (sign_of rule) \<Longrightarrow> proofs_ok (rep_thm rule)"
  shows "proofs_ok (thm_of_bc (sign_of state) i (state :: 'u pure_thm) flatten e rule x)"
proof -
  let ?c = "sign_of state"
  let ?X = "pure_sig_gen.vars_thm (th_tpairs (rep_of state)) (th_prop (rep_of state)) \<union>
    pure_sig_gen.vars_thm (th_tpairs (rep_of rule)) (th_prop (rep_of rule))"
  let ?V = "\<Union>A\<in>set (na_As (br_newas x)). vars A"
  let ?L = "bc_clash state rule x"
  interpret pure_sig_gen "sg_alg ?c" "sg_ar ?c" "sg_consts ?c" ?L using ps unfolding pure_sig_def .
  have tv: "scons (tvars_thm (th_tpairs (rep_of state)) (th_prop (rep_of state)) \<union>
      tvars_thm (th_tpairs (rep_of rule)) (th_prop (rep_of rule)))"
    using sc by (simp add: bc_scons_def)
  then have s1: "scons (tvars_thm (th_tpairs (rep_thm state)) (th_prop (rep_thm state)))"
    and s2: "scons (tvars_thm (th_tpairs (rep_thm rule)) (th_prop (rep_thm rule)))"
    by (auto simp: scons_def)
  have st: "thm_inv0 (th_maxidx (rep_of state)) (hyps_of state) (th_tpairs (rep_of state)) (th_prop (rep_of state))"
    using pure_thm_inv0[OF ps s1] by simp
  have ru: "thm_inv0 (th_maxidx (rep_of rule)) (hyps_of rule) (th_tpairs (rep_of rule)) (th_prop (rep_of rule))"
    using pure_thm_inv0[of rule] ps s2 sr by simp
  have h1: "?L = {} \<Longrightarrow> vtcons ?X" by (fastforce simp: bc_clash_def vclash_def vtcons_def)
  have h2: "nfree (br_env x)" using nb by (rule nfree_binds_none)
  have h3: "lvtcons (?X \<union> ?V)" by (rule lvtcons_vclash) (simp add: bc_clash_def)
  have h4: "?L \<subseteq> fst ` (?X \<union> ?V)" by (force simp: bc_clash_def vclash_def)
  have nm: "bc_names incremented ?X x" unfolding bc_names_def using h1 h2 h3 h4 by blast
  have vc': "incremented \<Longrightarrow> lvtcons ?X" using bc_names_inc[OF nm] .
  obtain rAs B env where tp: "stpairs = th_tpairs (rep_of state)"
    and SP: "th_prop (rep_of state) = list_implies (Bs @ [Bi]) C"
    and ti: "thm_inv (maxidx (br_env x)) (hyps_of state @ hyps_of rule) (br_tpairs x) (br_prop x)"
    by (rule bicompose_setup[OF d ok rx cfg vl st ru tv nm]) blast
  interpret prf_sig_gen "sg_alg ?c" "sg_ar ?c" "sg_consts ?c" ?L "sg_close ?c" "sg_tyargs ?c"
    using psig by (simp add: is_prf_sig_def prf_sig_gen_of)
  have ps: "proofs_ok (rep_thm state)" by (rule po_state[OF psig])
  have pr: "proofs_ok (rep_thm rule)" by (rule po_rule) (simp add: sr psig)
  have sg_eq: "th_sign (thm_of_bc ?c i state flatten e rule x) = ?c" by (simp add: thm_of_bc_def)
  show ?thesis unfolding proofs_ok_def Let_def sg_eq
  proof (rule conjI; intro allI impI)
    fix p assume "th_proof (thm_of_bc ?c i state flatten e rule x) = returnW p"
    then obtain rp sp where rp: "proof_of rule = returnW rp" and sp: "proof_of state = returnW sp"
      and p: "bc_proof (rep_of state) i e flatten x rp sp = returnW p"
      by (auto simp: thm_of_bc_def bindP_eq_returnP)
    have "prf_valid (sg_ax ?c) (set (hyps_of state @ hyps_of rule)) (br_tpairs x) p (br_prop x) \<and>
        prf_idx (\<lambda>i. 0 \<le> i) p \<and> prf_nolb 0 p"
      by (rule bicompose_thm_proof_valid[OF d ok rx cfg vl st ru tv nm _ _ _ _ _ _ p])
        (use ps sp pr rp sr in \<open>simp_all add: proofs_ok_def Let_def\<close>)
    then show "prf_valid (sg_ax ?c)
        (set (th_hyps (thm_of_bc ?c i state flatten e rule x))) (th_tpairs (thm_of_bc ?c i state flatten e rule x)) p
        (th_prop (thm_of_bc ?c i state flatten e rule x)) \<and> prf_idx (\<lambda>i. 0 \<le> i) p \<and> prf_nolb 0 p"
      by (simp add: thm_of_bc_def)
  next
    fix z assume "th_zproof (thm_of_bc ?c i state flatten e rule x) = return z"
    then obtain rp sp where rp: "zproof_of rule = return rp" and sp: "zproof_of state = return sp"
      and z: "bc_zproof ztargs (rep_of state) i e flatten (rep_of rule) x rp sp = return z"
      by (auto simp: thm_of_bc_def bindZ_eq_returnZ)
    have zs: "zinv sp" "znolb 0 sp" "zhyps_ok sp" "zinv rp" "znolb 0 rp" "zhyps_ok rp"
      using ps sp pr rp sr by (simp_all add: proofs_ok_def Let_def)
    have "zvalid (sg_ax ?c) (set (hyps_of state @ hyps_of rule)) (br_tpairs x) z (br_prop x) \<and> zinv z \<and>
        znolb 0 z \<and> zhyps z \<subseteq> zhyps sp \<union> zhyps rp"
      by (rule bicompose_thm_zproof_valid[OF d ok rx cfg vl st ru tv nm _ zs(1,2) _ zs(4,5) z])
        (use ps sp pr rp sr in \<open>simp_all add: proofs_ok_def Let_def\<close>)
    moreover have "zhyps_ok z" if "zhyps z \<subseteq> zhyps sp \<union> zhyps rp"
      using that zs(3,6) by (auto simp: zhyps_ok_def)
    ultimately show "zvalid (sg_ax ?c)
        (set (th_hyps (thm_of_bc ?c i state flatten e rule x))) (th_tpairs (thm_of_bc ?c i state flatten e rule x)) z
        (th_prop (thm_of_bc ?c i state flatten e rule x)) \<and> zinv z \<and> znolb 0 z \<and> zhyps_ok z"
      by (simp add: thm_of_bc_def)
  qed
qed

end

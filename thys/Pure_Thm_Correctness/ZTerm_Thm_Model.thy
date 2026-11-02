section \<open>Theorems with tight proofs: the model\<close>

theory ZTerm_Thm_Model
  imports ZTerm_Hidden
begin

subsection \<open>Theorems of the model with tight proofs\<close>

text \<open>
  A theorem of the model with its tight proof. As for classic proofs (theory \<open>Thm_Proof\<close>), the
  invariant holds for every choice of the propositions of axioms, oracles and theorems.
\<close>

record thm_zprf = thm_cert +
  th_zproof :: zproof

definition zprf_thm_ok :: "thm_zprf \<Rightarrow> bool" where
  "zprf_thm_ok th \<longleftrightarrow> thm_ok (thm_cert.truncate th) \<and> csig.zlb (sg_consts (th_cert th)) 0 (th_zproof th) \<and>
    (\<forall>ac aty. prf_wf_csig ac aty (sg_alg (th_cert th)) (sg_ar (th_cert th)) \<longrightarrow>
      prf_wf_csig.zthm_prf_inv (sg_consts (th_cert th)) ac aty (sg_alg (th_cert th)) (sg_ar (th_cert th))
        (th_maxidx th) (th_tpairs th) (th_prop th) (set (th_hyps th)) (th_zproof th))"

text \<open>\<open>Thm.trivial\<close> with the tight proof \<open>\<^bold>\<lambda>H: ?A. H\<close>.\<close>

definition trivial_zprf_thm :: thm_zprf where
  "trivial_zprf_thm = thm_cert.extend trivial_thm
    (thm_zprf.fields (ZAbsp (STR ''H'') (ZVar (STR ''A'', 0) ZProp) (ZBoundp 0)))"

lemma zprf_thm_ok_trivial: "zprf_thm_ok trivial_zprf_thm"
proof -
  let ?A = "Var (STR ''A'', 0) propT" and ?ar = "\<lambda>_ :: name. 0 :: nat" and ?ct = "\<lambda>_ :: name. None :: ptyp option"
  let ?p = "ZAbsp (STR ''H'') (ZVar (STR ''A'', 0) ZProp) (ZBoundp 0)"
  have "prf_wf_csig.zthm_prf_inv ?ct ac aty undefined ?ar 0 [] (implies $ ?A $ ?A) {} ?p"
    if "prf_wf_csig ac aty undefined ?ar" for ac aty
  proof -
    interpret prf_wf_csig ?ct ac aty undefined ?ar by fact
    have wp: "wft ?ar propT" "wft ?ar imp_type" by (simp_all add: propT_def imp_type_def tarity_def)
    have h: "has_type (\<lambda>_. propT) [] (implies $ ?A $ ?A) propT"
      by (simp add: has_type_implies has_type.Var)
    have ty: "tys (implies $ ?A $ ?A) = {imp_type, propT}" by (auto simp: implies_imp_type)
    then have w: "wt_term ?ar {} (\<lambda>_. propT) 0 (implies $ ?A $ ?A) propT"
      using h wp by (simp add: wt_term_def swf_tm_def implies_imp_type below_def tyA_def imp_type_def propT_def
        const_typ_ok_def)
    have wt: "wt_thm ?ar {} (\<lambda>_. propT) 0 [] (implies $ ?A $ ?A)"
      using w has_type_cok[OF h] by (simp add: wt_thm_def)
    have zd: "zdec (ZVar (STR ''A'', 0) ZProp) = ?A" by (simp add: propT_def)
    have v: "prf_valid undefined ?ar (\<lambda>_. propT) {} [] (zprf_tr ?p) (implies $ ?A $ ?A)"
      unfolding prf_valid_def
    proof (intro allI impI)
      fix V' \<rho> \<theta> assume ty: "inst_typed (\<lambda>_. propT) V' [] \<rho> \<theta>"
      have a: "wty V' [] (\<theta> (STR ''A'', 0)) propT" using inst_typedD[OF ty, of "(STR ''A'', 0)"] by simp
      have "prf_ok V' {} [] [\<theta> (STR ''A'', 0)] (PBound 0) (\<theta> (STR ''A'', 0))"
        using prf_ok.PBound[of 0 "[\<theta> (STR ''A'', 0)]" V' "[]" "{}"] a by simp
      then have "prf_ok V' {} [] [] (AbsP (STR ''H'') (Some (\<theta> (STR ''A'', 0))) (PBound 0))
          (implies $ \<theta> (STR ''A'', 0) $ \<theta> (STR ''A'', 0))"
        by (rule prf_ok.AbsP[OF a ann_ok_refl[OF a]])
      then show "prf_ok V' {} [] [] (prf_inst \<rho> \<theta> 0 (zprf_tr ?p)) (psubst \<rho> \<theta> 0 (implies $ ?A $ ?A))"
        by (simp add: zd implies_def imp_type_def propT_def incr_boundvars_def)
    qed
    have z: "zinv {} (\<lambda>_. propT) 0 ?p"
      by (auto simp: zinv_def zann_def zty_def propT_def intro!: exI[of _ "[]"] has_type.Var)
    show ?thesis unfolding zthm_prf_inv_def
      by (intro conjI exI[of _ "{}"] exI[of _ "\<lambda>_. propT"])
        (use wt v wp z in \<open>simp_all add: scons_def tcert_def tyA_def propT_def\<close>)
  qed
  moreover have "csig.zlb ?ct 0 ?p"
  proof -
    interpret csig ?ct .
    show ?thesis by simp
  qed
  ultimately show ?thesis using thm_ok_trivial
    by (simp add: zprf_thm_ok_def trivial_zprf_thm_def trivial_thm_def thm_cert.defs thm_zprf.defs)
qed

typedef (overloaded) zprf_thm = "{th. zprf_thm_ok th}"
  morphisms rep_zprf_thm Abs_zprf_thm
  using zprf_thm_ok_trivial by blast

abbreviation zprf_rep_of :: "zprf_thm \<Rightarrow> thm_rep" where
  "zprf_rep_of th \<equiv> thm_rep.truncate (rep_zprf_thm th)"

abbreviation zprf_cert_of :: "zprf_thm \<Rightarrow> sign" where
  "zprf_cert_of th \<equiv> th_cert (rep_zprf_thm th)"

abbreviation zproof_of :: "zprf_thm \<Rightarrow> zproof" where
  "zproof_of th \<equiv> th_zproof (rep_zprf_thm th)"

text \<open>\<open>Thm.assume\<close> with the tight proof \<open>ZHyp A\<close>.\<close>

definition assume_zprf_thm :: "sign \<Rightarrow> pterm \<Rightarrow> thm_zprf" where
  "assume_zprf_thm c A = thm_cert.extend (assume_thm c A)
    (thm_zprf.fields (ZHyp (valZ (zterm_of (csig.ztargs (sg_consts c)) A) (ZBound 0))))"

lemma zprf_thm_ok_assume:
  assumes A: "csig.hyp_ok (sg_consts c) (sg_ar c) A"
  shows "zprf_thm_ok (assume_zprf_thm c A)"
proof -
  obtain alg ar ct where c: "c = \<lparr>sg_alg = alg, sg_ar = ar, sg_consts = ct\<rparr>" by (cases c) auto
  let ?z = "valZ (zterm_of (csig.ztargs ct) A) (ZBound 0)"
  have "prf_wf_csig.zthm_prf_inv ct ac aty alg ar (-1) [] A {A} (ZHyp ?z)" if "prf_wf_csig ac aty alg ar" for ac aty
  proof -
    interpret prf_wf_csig ct ac aty alg ar by fact
    from A have hA: "hyp_ok ar A" by (simp add: c)
    then have v: "vars A = {}" and w: "wt_term ar {} (\<lambda>_. propT) (-1) A propT" and cA: "cok A"
      by (auto simp: hyp_ok_def)
    note hp = hyp_ok_props[OF hA]
    have wp: "wft ar propT"
      using w by (intro has_type_wft[of "\<lambda>_. propT" "[]" A]) (auto simp: wt_term_def tyA_def)
    have ht: "has_type (\<lambda>_. propT) [] A propT" using w by (simp add: wt_term_def)
    from zterm_of_zdec_cts[OF has_type_cts[OF ht]] v hp(2)
    obtain z where z: "zterm_of ztargs A = returnZ z" "zdec z = A" by fastforce
    have zz: "?z = z" using z(1) by simp
    have "prf_valid alg ar (\<lambda>_. propT) {A} [] (zprf_tr (ZHyp ?z)) A"
      unfolding prf_valid_def
    proof (intro allI impI)
      fix V' \<rho> \<theta>
      have "has_type V' [] A propT" using w v by (auto simp: wt_term_def intro: has_type_vars)
      then have "prf_ok V' {A} [] [] (Hyp A) A" using v by (intro prf_ok.Hyp) (simp_all add: wty_def)
      then show "prf_ok V' {A} [] [] (prf_inst \<rho> \<theta> 0 (zprf_tr (ZHyp ?z))) (psubst \<rho> \<theta> 0 A)"
        using psubst_ground[OF hp(1,2)] by (simp add: zz z(2))
    qed
    moreover have "zinv {} (\<lambda>_. propT) (-1) (ZHyp ?z)" by (simp add: zinv_def)
    ultimately show ?thesis unfolding zthm_prf_inv_def
      by (intro conjI exI[of _ "{}"] exI[of _ "\<lambda>_. propT"])
        (use w cA wp in \<open>simp_all add: scons_def tcert_def tyA_def wt_thm_def propT_def\<close>)
  qed
  moreover have "csig.zlb ct 0 (ZHyp ?z)"
  proof -
    interpret csig ct .
    show ?thesis by simp
  qed
  ultimately show ?thesis using thm_ok_assume[OF A]
    by (simp add: zprf_thm_ok_def assume_zprf_thm_def assume_thm_def thm_cert.defs thm_zprf.defs c)
qed


subsection \<open>Biresolution of theorems with tight proofs\<close>

text \<open>
  The tight proof of a new theorem: the tight proof that \<open>Thm.bicompose_aux\<close> builds
  (\<open>ZTerm.bicompose_proof\<close> applied to the lifted tight proof of the rule, renamed as the new
  premises, and the tight proof of the proof state).
\<close>

definition zbres_proof :: "thm_zprf \<Rightarrow> thm_zprf \<Rightarrow> integer \<Rightarrow> bool \<Rightarrow> bres \<Rightarrow> zproof Z" where
  "zbres_proof st ru i e x =
    (case SOME d. csig.okT (dest_state (thm_rep.truncate st) i) d of (stpairs, Bs, Bi, C) \<Rightarrow>
      let ta = csig.ztargs (sg_consts (th_cert st)); smax = th_maxidx st; inc = smax + 1;
        lr = lift_rule Bi smax (thm_rep.truncate ru)
      in zlift_proof ta Bi inc (map (lift_all inc Bi) (strip_imp_prems (th_prop ru))) (th_zproof ru) \<bind> (\<lambda>q.
        (case na_ren (br_newas x) of None \<Rightarrow> returnZ q | Some rr \<Rightarrow> zren_proof rr smax q) \<bind> (\<lambda>rp.
        zbicompose_proof ta (br_env x) smax True Bs (na_As (br_newas x)) (br_A x) (na_oldAs (br_newas x))
          (na_n (br_newas x)) (count_prems (strip_all_body Bi) + (if e then -1 else 0) + 1)
          [SOME v. ok (full_prop_of (th_tpairs st) (th_prop st)) v,
           SOME v. ok (full_prop_of (th_tpairs lr) (th_prop lr)) v] rp (th_zproof st))))"

text \<open>
  The condition under which the composition of tight proofs is shown correct: the renaming of the
  new premises keeps the hidden variables of the tight proof of the rule apart
  (@{const prf_wf_csig.zren_ok}).
\<close>

definition zbres_ok :: "thm_zprf \<Rightarrow> thm_zprf \<Rightarrow> integer \<Rightarrow> bool \<Rightarrow> bres \<Rightarrow> bool" where
  "zbres_ok st ru i e x =
    (case SOME d. csig.okT (dest_state (thm_rep.truncate st) i) d of (stpairs, Bs, Bi, C) \<Rightarrow>
      let ct = sg_consts (th_cert st); smax = th_maxidx st; inc = smax + 1;
        lr = lift_rule Bi smax (thm_rep.truncate ru);
        q = valZ (zlift_proof (csig.ztargs ct) Bi inc (map (lift_all inc Bi) (strip_imp_prems (th_prop ru)))
          (th_zproof ru)) ZNop
      in prf_wf_csig.zren_ok ct (br_newas x) smax (th_tpairs st) (th_prop st) (th_tpairs lr) (th_prop lr) (th_zproof st) q)"

definition zbres_prf_rec :: "sign \<Rightarrow> thm_zprf \<Rightarrow> thm_zprf \<Rightarrow> integer \<Rightarrow> bool \<Rightarrow> bres \<Rightarrow> thm_zprf" where
  "zbres_prf_rec c st ru i e x = thm_cert.extend (bres_rec c (thm_cert.truncate st) (thm_cert.truncate ru) x)
    (thm_zprf.fields (valZ (zbres_proof st ru i e x) ZNop))"

definition biresolution_zprf_thms :: "cfg \<Rightarrow> (name list \<Rightarrow> name list) \<Rightarrow> bool \<Rightarrow> bool \<Rightarrow> (bool \<times> zprf_thm) list \<Rightarrow>
    integer \<Rightarrow> zprf_thm \<Rightarrow> (zprf_thm \<times> (bool \<times> zprf_thm)) list option" where
  "biresolution_zprf_thms cfg vl trace match_flg brules i state =
    (let c = zprf_cert_of state;
      R = (\<lambda>xs. \<exists>s0. csig.okT (biresolution trace match_flg zprf_rep_of brules i (zprf_rep_of state)) s0 \<and>
        csig.brevals (unify_ops cfg vl) (sg_alg c) zprf_rep_of s0 xs)
     in if wf_algebra (sg_alg c) (sg_ar c) \<and> cfg_alg cfg = sg_alg c \<and> (\<forall>xs. length (vl xs) = length xs) \<and>
          (\<forall>r\<in>set brules. zprf_cert_of (snd r) = c) \<and> (\<exists>xs. R xs) \<and>
          (\<forall>(x, r)\<in>set (THE xs. R xs). zbres_ok (rep_zprf_thm state) (rep_zprf_thm (snd r)) i (fst r) x)
       then Some (map (\<lambda>(x, r). (Abs_zprf_thm (zbres_prf_rec c (rep_zprf_thm state) (rep_zprf_thm (snd r)) i (fst r) x), r))
         (THE xs. R xs))
       else None)"

theorem zbres_prf_rec_ok:
  fixes recf :: "'a \<Rightarrow> thm_zprf"
  assumes wf: "wf_algebra (sg_alg (th_cert st)) (sg_ar (th_cert st))"
    and br: "csig.okT (biresolution trace match_flg (\<lambda>r. thm_rep.truncate (recf r)) brules i
      (thm_rep.truncate st)) s0"
    and res: "csig.brresult (unify_ops cfg vl) (sg_alg (th_cert st)) (\<lambda>r. thm_rep.truncate (recf r)) s0
      (x, (e, rule))"
    and cfg: "cfg_alg cfg = sg_alg (th_cert st)" and vl: "\<And>xs. length (vl xs) = length xs"
    and state_ok: "zprf_thm_ok st"
    and rules: "\<forall>r\<in>set brules. zprf_thm_ok (recf (snd r)) \<and> th_cert (recf (snd r)) = th_cert st"
    and g: "zbres_ok st (recf rule) i e x"
  shows "zprf_thm_ok (zbres_prf_rec (th_cert st) st (recf rule) i e x)"
    "zbres_proof st (recf rule) i e x = returnZ (th_zproof (zbres_prf_rec (th_cert st) st (recf rule) i e x))"
proof -
  obtain alg ar ct where c: "th_cert st = \<lparr>sg_alg = alg, sg_ar = ar, sg_consts = ct\<rparr>"
    by (cases "th_cert st") (rule that)
  have wf': "wf_algebra alg ar" using wf by (simp add: c)
  have okc: "thm_ok (bres_rec (th_cert st) (thm_cert.truncate st) (thm_cert.truncate (recf rule)) x)"
  proof -
    have "thm_ok (bres_rec (th_cert (thm_cert.truncate st)) (thm_cert.truncate st) ((thm_cert.truncate \<circ> recf) rule) x)"
    proof (rule bres_rec_ok[where recf = "thm_cert.truncate \<circ> recf" and rule = rule])
      show "wf_algebra (sg_alg (th_cert (thm_cert.truncate st))) (sg_ar (th_cert (thm_cert.truncate st)))"
        using wf by simp
      show "csig.okT (biresolution trace match_flg (\<lambda>r. thm_rep.truncate ((thm_cert.truncate \<circ> recf) r)) brules i
          (thm_rep.truncate (thm_cert.truncate st))) s0"
        using br by (simp add: truncate_truncate comp_def)
      show "csig.brresult (unify_ops cfg vl) (sg_alg (th_cert (thm_cert.truncate st)))
          (\<lambda>r. thm_rep.truncate ((thm_cert.truncate \<circ> recf) r)) s0 (x, (e, rule))"
        using res by (simp add: comp_def)
      show "cfg_alg cfg = sg_alg (th_cert (thm_cert.truncate st))" using cfg by simp
      show "thm_ok (thm_cert.truncate st)" using state_ok by (simp add: zprf_thm_ok_def)
      show "\<forall>r\<in>set brules. thm_ok ((thm_cert.truncate \<circ> recf) (snd r)) \<and>
          th_cert ((thm_cert.truncate \<circ> recf) (snd r)) = th_cert (thm_cert.truncate st)"
        using rules by (simp add: zprf_thm_ok_def)
    qed (rule vl)
    then show ?thesis by simp
  qed
  interpret wf_csig ct alg ar using wf' by (simp add: wf_csig_def)
  note res' = res[unfolded c, simplified]
  from biresolution_result[OF br res'] obtain stpairs Bs Bi C goal
    where d: "okT (dest_state (thm_rep.truncate st) i) (stpairs, Bs, Bi, C)" and r: "(e, rule) \<in> set brules"
    by (rule biresolution_result[OF br res'], rule that, assumption+)
  have okr: "zprf_thm_ok (recf rule)" "th_cert (recf rule) = th_cert st" using rules r by force+
  have sm: "(SOME d. okT (dest_state (thm_rep.truncate st) i) d) = (stpairs, Bs, Bi, C)"
    using okT_det[OF someI[where P = "okT (dest_state (thm_rep.truncate st) i)", OF d] d] .
  let ?inc = "th_maxidx st + 1"
  let ?lr = "lift_rule Bi (th_maxidx st) (thm_rep.truncate (recf rule))"
  let ?lift = "zlift_proof (csig.ztargs ct) Bi ?inc (map (lift_all ?inc Bi) (strip_imp_prems (th_prop (recf rule))))
    (th_zproof (recf rule))"
  from g have g': "prf_wf_csig.zren_ok ct (br_newas x) (th_maxidx st) (th_tpairs st) (th_prop st)
      (th_tpairs ?lr) (th_prop ?lr) (th_zproof st) (valZ ?lift ZNop)"
    by (simp add: zbres_ok_def sm c Let_def)
  text \<open>The invariant for any choice of the propositions of axioms, oracles and theorems.\<close>
  have inv: "\<exists>p. zbres_proof st (recf rule) i e x = returnZ p \<and>
      prf_wf_csig.zthm_prf_inv ct ac aty alg ar (maxidx (br_env x)) (br_tpairs x) (br_prop x)
        (set (th_hyps st) \<union> set (th_hyps (recf rule))) p \<and> zlb 0 p"
    if pw: "prf_wf_csig ac aty alg ar" for ac aty
  proof -
    interpret P: prf_wf_csig ct ac aty alg ar by (rule pw)
    have cst: "th_cert (thm_cert.truncate st) = \<lparr>sg_alg = alg, sg_ar = ar, sg_consts = ct\<rparr>"
      using c by (simp add: thm_cert.truncate_def)
    have cru: "th_cert (thm_cert.truncate (recf rule)) = \<lparr>sg_alg = alg, sg_ar = ar, sg_consts = ct\<rparr>"
      using c okr(2) by (simp add: thm_cert.truncate_def)
    have tst: "thm_ok (thm_cert.truncate st)" "thm_ok (thm_cert.truncate (recf rule))"
      using state_ok okr(1) by (simp_all add: zprf_thm_ok_def)
    note pst = thm_ok_parts_rec[OF tst(1) cst] and pru = thm_ok_parts_rec[OF tst(2) cru]
    have si: "P.zthm_prf_inv (th_maxidx (thm_rep.truncate st)) (th_tpairs (thm_rep.truncate st))
        (th_prop (thm_rep.truncate st)) (set (th_hyps st)) (th_zproof st)" "zlb 0 (th_zproof st)"
      using state_ok pw c by (simp_all add: zprf_thm_ok_def thm_rep.truncate_def)
    have ri: "P.zthm_prf_inv (th_maxidx (thm_rep.truncate (recf rule))) (th_tpairs (thm_rep.truncate (recf rule)))
        (th_prop (thm_rep.truncate (recf rule))) (set (th_hyps (recf rule))) (th_zproof (recf rule))"
        "zlb 0 (th_zproof (recf rule))"
      using okr pw c by (simp_all add: zprf_thm_ok_def thm_rep.truncate_def)
    have hs: "\<forall>h\<in>set (th_hyps (recf rule)). hyp_ok ar h" using pru(2) by (simp add: thm_cert.truncate_def)
    from P.zbiresolution_prf_inv[OF br res' cfg[unfolded c, simplified] vl d
        pst(1)[unfolded truncate_truncate] pru(1)[unfolded truncate_truncate] si ri hs]
    obtain q where q: "?lift = returnZ q"
      and eS: "\<exists>vS. ok (full_prop_of (th_tpairs st) (th_prop st)) vS"
      and eR: "\<exists>vR. ok (full_prop_of (th_tpairs ?lr) (th_prop ?lr)) vR"
      and cmp: "\<forall>vS vR. ok (full_prop_of (th_tpairs st) (th_prop st)) vS \<longrightarrow>
        ok (full_prop_of (th_tpairs ?lr) (th_prop ?lr)) vR \<longrightarrow>
        P.zren_ok (br_newas x) (th_maxidx st) (th_tpairs st) (th_prop st) (th_tpairs ?lr) (th_prop ?lr) (th_zproof st) q \<longrightarrow>
        (\<exists>p. (case na_ren (br_newas x) of None \<Rightarrow> returnZ q | Some rr \<Rightarrow> zren_proof rr (th_maxidx st) q) \<bind>
          (\<lambda>rp. zbicompose_proof ztargs (br_env x) (th_maxidx st) True Bs (na_As (br_newas x)) (br_A x)
            (na_oldAs (br_newas x)) (na_n (br_newas x))
            (count_prems (strip_all_body Bi) + (if e then -1 else 0) + 1) [vS, vR] rp (th_zproof st)) = returnZ p \<and>
          P.zthm_prf_inv (maxidx (br_env x)) (br_tpairs x) (br_prop x)
            (set (th_hyps st) \<union> set (th_hyps (recf rule))) p \<and> zlb 0 p)"
      by (auto simp: Let_def cong: option.case_cong)
    have vS: "ok (full_prop_of (th_tpairs st) (th_prop st)) (SOME v. ok (full_prop_of (th_tpairs st) (th_prop st)) v)"
      using eS by (rule someI_ex)
    have vR: "ok (full_prop_of (th_tpairs ?lr) (th_prop ?lr)) (SOME v. ok (full_prop_of (th_tpairs ?lr) (th_prop ?lr)) v)"
      using eR by (rule someI_ex)
    from cmp[rule_format, OF vS vR] g' q show ?thesis
      by (simp add: zbres_proof_def sm c Let_def cong: option.case_cong)
  qed
  from inv[OF prf_wf_csig_some[OF wf']] obtain p0 where p0: "zbres_proof st (recf rule) i e x = returnZ p0"
    and zl: "zlb 0 p0"
    by blast
  have pr: "th_zproof (zbres_prf_rec (th_cert st) st (recf rule) i e x) = p0"
    by (simp add: zbres_prf_rec_def p0 thm_cert.defs thm_zprf.defs)
  show "zbres_proof st (recf rule) i e x = returnZ (th_zproof (zbres_prf_rec (th_cert st) st (recf rule) i e x))"
    by (simp add: pr p0)
  show "zprf_thm_ok (zbres_prf_rec (th_cert st) st (recf rule) i e x)"
    unfolding zprf_thm_ok_def
  proof (intro conjI allI impI)
    show "thm_ok (thm_cert.truncate (zbres_prf_rec (th_cert st) st (recf rule) i e x))"
      using okc by (simp add: zbres_prf_rec_def)
    show "csig.zlb (sg_consts (th_cert (zbres_prf_rec (th_cert st) st (recf rule) i e x))) 0
        (th_zproof (zbres_prf_rec (th_cert st) st (recf rule) i e x))"
      using zl pr by (simp add: zbres_prf_rec_def bres_rec_def thm_cert.defs thm_zprf.defs c)
    fix ac aty
    assume "prf_wf_csig ac aty
      (sg_alg (th_cert (zbres_prf_rec (th_cert st) st (recf rule) i e x)))
      (sg_ar (th_cert (zbres_prf_rec (th_cert st) st (recf rule) i e x)))"
    then have pw: "prf_wf_csig ac aty alg ar"
      by (simp add: zbres_prf_rec_def bres_rec_def thm_cert.defs thm_zprf.defs c)
    from inv[OF pw] p0 have "prf_wf_csig.zthm_prf_inv ct ac aty alg ar (maxidx (br_env x)) (br_tpairs x) (br_prop x)
        (set (th_hyps st) \<union> set (th_hyps (recf rule))) p0"
      by (auto simp: returnZ_def)
    then show "prf_wf_csig.zthm_prf_inv (sg_consts (th_cert (zbres_prf_rec (th_cert st) st (recf rule) i e x))) ac aty
      (sg_alg (th_cert (zbres_prf_rec (th_cert st) st (recf rule) i e x)))
      (sg_ar (th_cert (zbres_prf_rec (th_cert st) st (recf rule) i e x)))
      (th_maxidx (zbres_prf_rec (th_cert st) st (recf rule) i e x))
      (th_tpairs (zbres_prf_rec (th_cert st) st (recf rule) i e x))
      (th_prop (zbres_prf_rec (th_cert st) st (recf rule) i e x))
      (set (th_hyps (zbres_prf_rec (th_cert st) st (recf rule) i e x)))
      (th_zproof (zbres_prf_rec (th_cert st) st (recf rule) i e x))"
      using pr by (simp add: zbres_prf_rec_def bres_rec_def thm_cert.defs thm_zprf.defs c Un_commute)
  qed
qed

text \<open>
  Soundness: the results of \<^const>\<open>biresolution_zprf_thms\<close> are the new theorems of the results of
  \<^const>\<open>biresolution\<close>, with the tight proofs that \<open>ZTerm.bicompose_proof\<close> computes without
  exceptions; as theorems with tight proofs, they are well-typed and valid, and their tight proofs
  are valid and have typed annotations.
\<close>

theorem biresolution_zprf_thms_results:
  assumes "biresolution_zprf_thms cfg vl trace match_flg brules i state = Some ys" "(th, r) \<in> set ys"
  shows "\<exists>s0 x. csig.okT (biresolution trace match_flg zprf_rep_of brules i (zprf_rep_of state)) s0 \<and>
      csig.brresult (unify_ops cfg vl) (cfg_alg cfg) zprf_rep_of s0 (x, r) \<and>
      rep_zprf_thm th = zbres_prf_rec (zprf_cert_of state) (rep_zprf_thm state) (rep_zprf_thm (snd r)) i (fst r) x \<and>
      zbres_proof (rep_zprf_thm state) (rep_zprf_thm (snd r)) i (fst r) x = returnZ (zproof_of th) \<and>
      zprf_thm_ok (rep_zprf_thm th)"
    and "zprf_cert_of th = zprf_cert_of state"
proof -
  let ?c = "zprf_cert_of state"
  let ?R = "\<lambda>xs. \<exists>s0. csig.okT (biresolution trace match_flg zprf_rep_of brules i (zprf_rep_of state)) s0 \<and>
    csig.brevals (unify_ops cfg vl) (sg_alg ?c) zprf_rep_of s0 xs"
  from assms(1) have g: "wf_algebra (sg_alg ?c) (sg_ar ?c)" "cfg_alg cfg = sg_alg ?c" "\<forall>xs. length (vl xs) = length xs"
    "\<forall>r\<in>set brules. zprf_cert_of (snd r) = ?c" and ex: "\<exists>xs. ?R xs"
    and gd: "\<forall>(x, r)\<in>set (THE xs. ?R xs). zbres_ok (rep_zprf_thm state) (rep_zprf_thm (snd r)) i (fst r) x"
    and ys: "ys = map (\<lambda>(x, r). (Abs_zprf_thm (zbres_prf_rec ?c (rep_zprf_thm state) (rep_zprf_thm (snd r)) i (fst r) x), r))
      (THE xs. ?R xs)"
    by (auto simp: biresolution_zprf_thms_def Let_def split: if_splits)
  from ex obtain s0 xs where br: "csig.okT (biresolution trace match_flg zprf_rep_of brules i (zprf_rep_of state)) s0"
    and ev: "csig.brevals (unify_ops cfg vl) (sg_alg ?c) zprf_rep_of s0 xs"
    by blast
  have the: "(THE xs. ?R xs) = xs"
    by (rule the_equality) (use br ev in \<open>auto dest: csig.okT_det csig.brevals_det\<close>)
  with ys assms(2) obtain x where x: "(x, r) \<in> set xs"
    and th: "th = Abs_zprf_thm (zbres_prf_rec ?c (rep_zprf_thm state) (rep_zprf_thm (snd r)) i (fst r) x)"
    by auto
  have gx: "zbres_ok (rep_zprf_thm state) (rep_zprf_thm (snd r)) i (fst r) x" using gd x the by auto
  have res: "csig.brresult (unify_ops cfg vl) (sg_alg ?c) zprf_rep_of s0 (x, r)" by (rule csig.brevals_brresult[OF ev x])
  obtain e rule where r: "r = (e, rule)" by (cases r)
  have rules: "\<forall>r\<in>set brules. zprf_thm_ok (rep_zprf_thm (snd r)) \<and> zprf_cert_of (snd r) = ?c"
    using g(4) rep_zprf_thm by blast
  note ok = zbres_prf_rec_ok[where recf = rep_zprf_thm, OF g(1) br res[unfolded r] g(2) _ rep_zprf_thm[simplified] rules
    gx[unfolded r, simplified]]
  have okt: "zprf_thm_ok (zbres_prf_rec ?c (rep_zprf_thm state) (rep_zprf_thm (snd r)) i (fst r) x)"
    using ok(1) g(3) by (simp add: r)
  then have rep: "rep_zprf_thm th = zbres_prf_rec ?c (rep_zprf_thm state) (rep_zprf_thm (snd r)) i (fst r) x"
    by (simp add: th Abs_zprf_thm_inverse)
  then show "zprf_cert_of th = ?c" by (simp add: zbres_prf_rec_def bres_rec_def thm_cert.defs thm_zprf.defs)
  have "zbres_proof (rep_zprf_thm state) (rep_zprf_thm (snd r)) i (fst r) x = returnZ (zproof_of th)"
    using ok(2) g(3) rep by (simp add: r)
  then show "\<exists>s0 x. csig.okT (biresolution trace match_flg zprf_rep_of brules i (zprf_rep_of state)) s0 \<and>
      csig.brresult (unify_ops cfg vl) (cfg_alg cfg) zprf_rep_of s0 (x, r) \<and>
      rep_zprf_thm th = zbres_prf_rec ?c (rep_zprf_thm state) (rep_zprf_thm (snd r)) i (fst r) x \<and>
      zbres_proof (rep_zprf_thm state) (rep_zprf_thm (snd r)) i (fst r) x = returnZ (zproof_of th) \<and>
      zprf_thm_ok (rep_zprf_thm th)"
    using br res g(2) rep okt by auto
qed

end

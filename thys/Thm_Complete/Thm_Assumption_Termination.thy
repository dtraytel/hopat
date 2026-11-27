section \<open>Termination of \<open>assumption\<close> and \<open>flexflex_rule\<close>\<close>

theory Thm_Assumption_Termination
  imports "Thm_Soundness.Thm_Assumption" Bicompose_Termination
begin

text \<open>
  The lazy result sequences of \<open>assumption\<close> and \<open>flexflex_rule\<close> evaluate to the lists of their
  results, for theorems whose variables have one type for each name.
\<close>

subsection \<open>Termination\<close>

lemma aevals_step:
  assumes "\<And>y. okT (apull ops s') y \<Longrightarrow> okT (apull ops s) y" and "aevals ops s' ys"
  shows "aevals ops s ys"
  using assms(2)
proof cases
  case Nil
  then show ?thesis using assms(1) by (blast intro: aevals.Nil)
next
  case (Cons r s'' rs)
  then show ?thesis using assms(1) by (blast intro: aevals.Cons)
qed

context pure_sig
begin

text \<open>The normalizations of the terms of a theorem and of the flex-flex pairs of a unifier terminate:\<close>

lemma unif_norm_ok:
  assumes st: "thm_inv m hs tps0 P0"
    and si: "sinv (tvars_thm tps0 P0) K0 (vars_thm tps0 P0) (empty_env m) (tdps tus)"
    and ds: "dstep (empty_env m) (tdps tus) env' (tdps tps)" and ei': "einv A' K' env'"
    and AA: "tvars_thm tps0 P0 \<subseteq> A'"
    and t: "\<And>e. e \<turnstile> t : T" "vars t \<subseteq> vars_thm tps0 P0" "ttvars t \<subseteq> tvars_thm tps0 P0"
  shows "\<exists>t'. ok (norm_term env' t) t'"
proof -
  let ?A = "tvars_thm tps0 P0" and ?X = "vars_thm tps0 P0" and ?env = "empty_env m"
  have ev: "evars ?env = {}" by (simp add: evars_def bnds_def vt_is_empty_lookup)
  have dX: "dvars (tdps tus) \<subseteq> ?X" using sinv_dvars[OF si] ev by simp
  have wX: "winv ?env ?X" using si by (simp add: sinv_def)
  have wZ: "winv ?env (?X \<union> dvars (tdps tus))" using wX dX by (simp add: sup_absorb1)
  have wY': "winv env' ?X" by (rule dstep_winv_sub[OF ds si wZ])
  have vY: "vtvars ?X \<subseteq> tvars_env (tyenv env') \<union> A'"
    using AA by (auto simp: vtvars_def vars_thm_def tvars_thm_def dest!: vtvars_ttvars)
  have ty: "(\<lambda>j. tsubst (rho0 env') ((\<lambda>_. propT) j)) \<turnstile> inst (rho0 env') t : tsubst (rho0 env') T"
    by (rule typing_inst[OF t(1) cert_inst_inst_ok[OF einv_rho0(2)[OF ei']]])
  show ?thesis by (rule norm_term_ok[OF ei' wY' vY _ _ ty]) (use t(2,3) AA in blast)+
qed

lemma upok_norm_ok:
  assumes ei: "einv A K env" and wi: "winv env X" and p: "upok A env [] X t u"
  shows "\<exists>t'. ok (norm_term env t) t'" "\<exists>u'. ok (norm_term env u) u'"
proof -
  from upokD(9)[OF p einv_rho0[OF ei]] obtain e T where "e \<turnstile> inst (rho0 env) t : T" "e \<turnstile> inst (rho0 env) u : T"
    by blast
  then show "\<exists>t'. ok (norm_term env t) t'" "\<exists>u'. ok (norm_term env u) u'"
    using norm_term_ok[OF ei wi upokD(6)[OF p] upokD(1)[OF p] upokD(3)[OF p]]
      norm_term_ok[OF ei wi upokD(6)[OF p] upokD(2)[OF p] upokD(4)[OF p]] by blast+
qed

lemma norm_tpairs_ok:
  assumes "\<forall>(t, u)\<in>set tps. (\<exists>t'. ok (norm_term env t) t') \<and> (\<exists>u'. ok (norm_term env u) u')"
  shows "\<exists>tps'. ok (mapM (norm_tpair env) tps) tps'"
  by (rule ok_mapM_exI) (use assms in \<open>fastforce simp: norm_tpair_def\<close>)

text \<open>A unifier of an assumption yields a new theorem:\<close>

lemma newth_ok:
  assumes st: "thm_inv (th_maxidx state) hs (th_tpairs state) (th_prop state)"
    and d: "okT (dest_state state i) (tpairs, Bs, Bi, C)" and ap: "assum_problems (-1) Bi = (params, asms, concl)"
    and asm: "asm \<in> set asms"
    and ur: "ures (empty_env (th_maxidx state)) ((rlist_abs params asm, rlist_abs params concl) # tpairs) (El_R env tps)"
  shows "\<exists>r. okT (newth (ACtx (th_maxidx state) tpairs Bs Bi C params concl) n (env, tps)) r"
proof -
  let ?A = "tvars_thm (th_tpairs state) (th_prop state)" and ?X = "vars_thm (th_tpairs state) (th_prop state)"
  note si = assumption_sinv[OF st d ap asm]
  have urs: "uresult ?A (empty_env (th_maxidx state)) ((rlist_abs params asm, rlist_abs params concl) # tpairs) (El_R env tps)"
    by (rule uresD[OF ur _ _ si]) simp_all
  from uresultD(3)[OF urs] obtain A' K' X' where AA: "?A \<subseteq> A'" and ff: "ffres A' K' X' env tps" by blast
  note ds = uresultD(1)[OF urs]
  have ei: "einv A' K' env" and wi: "winv env X'" and tpok: "\<forall>(t, u)\<in>set tps. upok A' env [] X' t u"
    using ff by (simp_all add: ffres_def)
  note dsd = okT_dest_state[OF d]
  have wS: "wtp (th_prop state)" using st by (simp add: thm_inv_def wt_thm_def)
  have P: "th_prop state = list_implies (Bs @ [Bi]) C"
    using list_implies_strip_prems[OF dsd(2) wtpD(2)[OF wS, of "\<lambda>_. propT"]] by simp
  have w: "wtp (list_implies Bs C)" using wtp_list_implies_butlast(1) wS P by simp
  have v: "vars (list_implies Bs C) \<subseteq> ?X" using P by (auto simp: vars_thm_def vars_list_implies)
  have "ttvars Z \<subseteq> ttvars (list_implies (Bs @ [Bi]) C)" if "Z \<in> insert C (set Bs)" for Z
    using that ttvars_list_implies(1)[of Z "Bs @ [Bi]" C] ttvars_list_implies(2)[of C "Bs @ [Bi]"] by auto
  then have tt: "ttvars (list_implies Bs C) \<subseteq> ?A"
    using ttvars_list_implies_sub[of Bs C] P by (fastforce simp: tvars_thm_def)
  obtain P' where nP: "ok (norm_term env (list_implies Bs C)) P'"
    using unif_norm_ok[OF st si ds ei AA wtpD(2)[OF w] v tt] by blast
  have "\<forall>(t, u)\<in>set tps. (\<exists>t'. ok (norm_term env t) t') \<and> (\<exists>u'. ok (norm_term env u) u')"
  proof (intro ballI, clarify)
    fix t u assume "(t, u) \<in> set tps"
    with tpok have p: "upok A' env [] X' t u" by blast
    from upok_norm_ok[OF ei wi p] show "(\<exists>t'. ok (norm_term env t) t') \<and> (\<exists>u'. ok (norm_term env u) u')" by blast
  qed
  then obtain tps' where nt: "ok (mapM (norm_tpair env) tps) tps'" using norm_tpairs_ok by blast
  show ?thesis using nP nt by (cases "env_is_empty env") (auto simp: newth_def returnW_def)
qed

text \<open>The result sequence of \<^const>\<open>assumption\<close> on a theorem is finite:\<close>

theorem assumption_terminates:
  assumes a: "okT (assumption i state) s0" and cfg: "cfg_alg cfg = alg"
    and st: "thm_inv (th_maxidx state) hs (th_tpairs state) (th_prop state)"
  shows "\<exists>ys. aevals (unify_ops cfg vl) s0 ys"
proof -
  let ?ops = "unify_ops cfg vl" and ?m = "th_maxidx state"
  let ?A = "tvars_thm (th_tpairs state) (th_prop state)" and ?X = "vars_thm (th_tpairs state) (th_prop state)"
  from okT_assumption[OF a] obtain tpairs Bs Bi C params asms concl where
    d: "okT (dest_state state i) (tpairs, Bs, Bi, C)" and ap: "assum_problems (-1) Bi = (params, asms, concl)"
    and s0: "s0 = AQ_Try (ACtx ?m tpairs Bs Bi C params concl) asms 1" .
  let ?ctx = "ACtx ?m tpairs Bs Bi C params concl"
  let ?tus = "\<lambda>asm. (rlist_abs params asm, rlist_abs params concl) # tpairs"
  have pw: "pwf (empty_env ?m) (?tus asm)" if "asm \<in> set asms" for asm
    using assumption_sinv[OF st d ap that] unfolding pwf_def
    by (intro exI[of _ ?A] exI[of _ ?X] conjI finite_vars_thm finite_tvars_thm)
  have ap': "aprob ?ctx asm = ?tus asm" for asm by (simp add: aprob_def)
  have mapc: "\<exists>ys. aevals ?ops (AQ_Map ?ctx n us (drop (Suc k) asms) (n + 1)) ys"
    if k: "k < length asms" and tr: "\<exists>ys. aevals ?ops (AQ_Try ?ctx (drop (Suc k) asms) (n + 1)) ys"
      and f: "fin cfg us (ures (empty_env ?m) (?tus (asms ! k)))" for k n us
  proof -
    have pk: "pwf (empty_env ?m) (?tus (asms ! k))" by (rule pw) (use k in simp)
    have "\<forall>us. elen cfg us = e \<longrightarrow> fin cfg us (ures (empty_env ?m) (?tus (asms ! k))) \<longrightarrow>
        (\<exists>ys. aevals ?ops (AQ_Map ?ctx n us (drop (Suc k) asms) (n + 1)) ys)" for e
    proof (induction e)
      case 0
      show ?case
      proof (intro allI impI)
        fix us assume el: "elen cfg us = 0" and f: "fin cfg us (ures (empty_env ?m) (?tus (asms ! k)))"
        show "\<exists>ys. aevals ?ops (AQ_Map ?ctx n us (drop (Suc k) asms) (n + 1)) ys"
        proof (rule upull_fin_cases[OF f pk])
          assume "okT (upull cfg us) None"
          then have "okT (apull ?ops (AQ_Map ?ctx n us (drop (Suc k) asms) (n + 1))) y \<longleftrightarrow>
              okT (apull ?ops (AQ_Try ?ctx (drop (Suc k) asms) (n + 1))) y" for y
            by (subst apull.simps) (auto simp: unify_ops_def)
          with tr show ?thesis by (meson aevals_step)
        next
          fix env' tps us' assume "elen cfg us = Suc (elen cfg us')"
          with el show ?thesis by simp
        qed
      qed
    next
      case (Suc e)
      show ?case
      proof (intro allI impI)
        fix us assume el: "elen cfg us = Suc e" and f: "fin cfg us (ures (empty_env ?m) (?tus (asms ! k)))"
        show "\<exists>ys. aevals ?ops (AQ_Map ?ctx n us (drop (Suc k) asms) (n + 1)) ys"
        proof (rule upull_fin_cases[OF f pk])
          assume "okT (upull cfg us) None"
          then have "okT (apull ?ops (AQ_Map ?ctx n us (drop (Suc k) asms) (n + 1))) y \<longleftrightarrow>
              okT (apull ?ops (AQ_Try ?ctx (drop (Suc k) asms) (n + 1))) y" for y
            by (subst apull.simps) (auto simp: unify_ops_def)
          with tr show ?thesis by (meson aevals_step)
        next
          fix env' tps us' assume pu: "okT (upull cfg us) (Some ((env', tps), us'))"
            and ur: "ures (empty_env ?m) (?tus (asms ! k)) (El_R env' tps)"
            and f': "fin cfg us' (ures (empty_env ?m) (?tus (asms ! k)))" and el': "elen cfg us = Suc (elen cfg us')"
          obtain r where r: "okT (newth ?ctx n (env', tps)) r" using newth_ok[OF st d ap nth_mem[OF k] ur] by blast
          have "okT (apull ?ops (AQ_Map ?ctx n us (drop (Suc k) asms) (n + 1)))
              (Some (r, AQ_Map ?ctx n us' (drop (Suc k) asms) (n + 1)))"
            using pu r by (subst apull.simps) (auto simp: unify_ops_def)
          moreover from Suc.IH el el' f' obtain ys where "aevals ?ops (AQ_Map ?ctx n us' (drop (Suc k) asms) (n + 1)) ys"
            by auto
          ultimately show ?thesis by (blast intro: aevals.Cons)
        qed
      qed
    qed
    with f show ?thesis by blast
  qed
  have "\<forall>k. length asms - k = j \<longrightarrow> (\<exists>ys. aevals ?ops (AQ_Try ?ctx (drop k asms) (integer_of_nat k + 1)) ys)" for j
  proof (induction j)
    case 0
    show ?case
    proof (intro allI impI)
      fix k assume "length asms - k = 0"
      then have "drop k asms = []" by simp
      then have "okT (apull ?ops (AQ_Try ?ctx (drop k asms) (integer_of_nat k + 1))) None"
        by (subst apull.simps) (simp add: returnW_def)
      then show "\<exists>ys. aevals ?ops (AQ_Try ?ctx (drop k asms) (integer_of_nat k + 1)) ys" by (blast intro: aevals.Nil)
    qed
  next
    case (Suc j)
    show ?case
    proof (intro allI impI)
      fix k assume j: "length asms - k = Suc j"
      then have k: "k < length asms" by simp
      have dk: "drop k asms = asms ! k # drop (Suc k) asms" using k by (simp add: Cons_nth_drop_Suc)
      have n1: "integer_of_nat (Suc k) + 1 = integer_of_nat k + 1 + 1" by (simp add: integer_of_nat_Suc)
      have "\<exists>ys. aevals ?ops (AQ_Try ?ctx (drop (Suc k) asms) (integer_of_nat (Suc k) + 1)) ys"
        by (rule Suc.IH[rule_format]) (use j in simp)
      then obtain ys0 where tr: "aevals ?ops (AQ_Try ?ctx (drop (Suc k) asms) (integer_of_nat k + 1 + 1)) ys0"
        unfolding n1 by blast
      show "\<exists>ys. aevals ?ops (AQ_Try ?ctx (drop k asms) (integer_of_nat k + 1)) ys"
      proof (cases "could_unify (asms ! k) concl")
        case False
        then have "okT (apull ?ops (AQ_Try ?ctx (drop k asms) (integer_of_nat k + 1))) y \<longleftrightarrow>
            okT (apull ?ops (AQ_Try ?ctx (drop (Suc k) asms) (integer_of_nat k + 1 + 1))) y" for y
          by (subst apull.simps) (simp add: dk)
        with tr show ?thesis by (meson aevals_step)
      next
        case True
        have pk: "pwf (empty_env ?m) (?tus (asms ! k))" by (rule pw) (use k in simp)
        obtain us where us: "okT (bo_unifiers ?ops (empty_env ?m) (?tus (asms ! k))) us"
          and f: "fin cfg us (ures (empty_env ?m) (?tus (asms ! k)))"
          by (rule unifiers_ops_ok[OF cfg pk])
        have "okT (apull ?ops (AQ_Try ?ctx (drop k asms) (integer_of_nat k + 1))) y \<longleftrightarrow>
            okT (apull ?ops (AQ_Map ?ctx (integer_of_nat k + 1) us (drop (Suc k) asms) (integer_of_nat k + 1 + 1))) y" for y
          using True us by (subst apull.simps) (auto simp: dk dest: okT_det[OF us])
        with mapc[OF k _ f] tr show ?thesis by (meson aevals_step)
      qed
    qed
  qed
  note all = this
  have "\<exists>ys. aevals ?ops (AQ_Try ?ctx (drop 0 asms) (integer_of_nat 0 + 1)) ys"
    using spec[OF all[of "length asms"], of 0] by simp
  with s0 show ?thesis by simp
qed

text \<open>The result sequence of \<^const>\<open>flexflex_rule\<close> on a theorem is finite:\<close>

theorem flexflex_terminates:
  assumes a: "okT (flexflex_rule (unify_ops cfg vl) th) s0" and cfg: "cfg_alg cfg = alg"
    and st: "thm_inv (th_maxidx th) hs (th_tpairs th) (th_prop th)"
  shows "\<exists>ys. fevals (unify_ops cfg vl) smashT th s0 ys"
proof -
  let ?ops = "unify_ops cfg vl" and ?m = "th_maxidx th"
  let ?A = "tvars_thm (th_tpairs th) (th_prop th)" and ?X = "vars_thm (th_tpairs th) (th_prop th)"
  note si = flexflex_sinv[OF st]
  from a obtain us where s0: "s0 = FQ us" by (auto simp: flexflex_rule_def)
  have pw: "pwf (empty_env ?m) (th_tpairs th)"
    using si unfolding pwf_def by (intro exI[of _ ?A] exI[of _ ?X] conjI finite_vars_thm finite_tvars_thm)
  from a s0 have "okT (bo_unifiers ?ops (empty_env ?m) (th_tpairs th)) us" by (auto simp: flexflex_rule_def)
  note f = unifiers_ures[OF cfg pw this]
  have ws: "wt_thm ?m hs (th_tpairs th) (th_prop th)" using st by (simp add: thm_inv_def)
  have newok: "\<exists>x. okT (fpull ?ops smashT th (FQ us)) (Some (x, FQ us'))"
    if pu: "okT (upull cfg us) (Some ((env', tps), us'))" and ur: "ures (empty_env ?m) (th_tpairs th) (El_R env' tps)"
    for us us' env' tps
  proof -
    have urs: "uresult ?A (empty_env ?m) (th_tpairs th) (El_R env' tps)"
      by (rule uresD[OF ur _ _ si]) simp_all
    from uresultD(3)[OF urs] obtain A' K' X' e0 where AA: "?A \<subseteq> A'"
      and ff: "ffres A' K' X' env' tps" and fl: "fflex A' K' e0 env' tps" by blast
    from smash_flexflex_term[OF ff fl] obtain env where sm: "okW (smash_flexflex (env', tps)) env"
      and ds: "dstep env' (tdps tps) env []" and fv: "finv A' K' e0 env" by blast
    have ds': "dstep (empty_env ?m) (tdps (th_tpairs th)) env (tdps [])"
      using dstep_trans[OF uresultD(1)[OF urs] ds] by simp
    have ei: "einv A' K' env" using fv by (simp add: finv_def)
    have nok: "\<exists>t'. ok (norm_term env t) t'"
      if "\<And>e. e \<turnstile> t : T" "vars t \<subseteq> ?X" "ttvars t \<subseteq> ?A" for t T
      by (rule unif_norm_ok[OF st si ds' ei AA that])
    have "\<forall>(t, u)\<in>set (th_tpairs th). (\<exists>t'. ok (norm_term env t) t') \<and> (\<exists>u'. ok (norm_term env u) u')"
    proof (intro ballI, clarify)
      fix t u assume tu: "(t, u) \<in> set (th_tpairs th)"
      from wt_thm_pair[OF ws tu] obtain T where "\<And>e. e \<turnstile> t : T" "\<And>e. e \<turnstile> u : T" by blast
      with nok vars_tvars_thm(3,4)[OF tu] show "(\<exists>t'. ok (norm_term env t) t') \<and> (\<exists>u'. ok (norm_term env u) u')"
        by blast
    qed
    then obtain tps' where nt: "ok (mapM (norm_tpair env) (th_tpairs th)) tps'" using norm_tpairs_ok by blast
    have wP: "wtp (th_prop th)" using ws by (simp add: wt_thm_def)
    obtain P where nP: "ok (norm_term env (th_prop th)) P"
      using nok[OF wtpD(2)[OF wP] vars_tvars_thm(1,2)] by blast
    have "\<exists>th'. ok (fnewth th env) th'" using nt nP by (auto simp: fnewth_def Let_def)
    then obtain th' where "ok (fnewth th env) th'" by blast
    then show ?thesis using pu sm
      by (intro exI[of _ "(env, th')"]) (auto simp: fpull_def unify_ops_def smashT_def)
  qed
  have "\<forall>us. elen cfg us = e \<longrightarrow> fin cfg us (ures (empty_env ?m) (th_tpairs th)) \<longrightarrow>
      (\<exists>ys. fevals ?ops smashT th (FQ us) ys)" for e
  proof (induction e)
    case 0
    show ?case
    proof (intro allI impI)
      fix us assume el: "elen cfg us = 0" and f: "fin cfg us (ures (empty_env ?m) (th_tpairs th))"
      show "\<exists>ys. fevals ?ops smashT th (FQ us) ys"
      proof (rule upull_fin_cases[OF f pw])
        assume "okT (upull cfg us) None"
        then have "okT (fpull ?ops smashT th (FQ us)) None" by (auto simp: fpull_def unify_ops_def)
        then show ?thesis by (blast intro: fevals.Nil)
      next
        fix env' tps us' assume "elen cfg us = Suc (elen cfg us')"
        with el show ?thesis by simp
      qed
    qed
  next
    case (Suc e)
    show ?case
    proof (intro allI impI)
      fix us assume el: "elen cfg us = Suc e" and f: "fin cfg us (ures (empty_env ?m) (th_tpairs th))"
      show "\<exists>ys. fevals ?ops smashT th (FQ us) ys"
      proof (rule upull_fin_cases[OF f pw])
        assume "okT (upull cfg us) None"
        then have "okT (fpull ?ops smashT th (FQ us)) None" by (auto simp: fpull_def unify_ops_def)
        then show ?thesis by (blast intro: fevals.Nil)
      next
        fix env' tps us' assume pu: "okT (upull cfg us) (Some ((env', tps), us'))"
          and ur: "ures (empty_env ?m) (th_tpairs th) (El_R env' tps)"
          and f': "fin cfg us' (ures (empty_env ?m) (th_tpairs th))" and el': "elen cfg us = Suc (elen cfg us')"
        from newok[OF pu ur] obtain x where "okT (fpull ?ops smashT th (FQ us)) (Some (x, FQ us'))" by blast
        moreover from Suc.IH el el' f' obtain ys where "fevals ?ops smashT th (FQ us') ys" by auto
        ultimately show ?thesis by (blast intro: fevals.Cons)
      qed
    qed
  qed
  with f s0 show ?thesis by blast
qed

end

end

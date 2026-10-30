section \<open>Problems with Type Variables: Termination of the Search\<close>

theory Unify_Poly_Fin
  imports Unify_Poly_Simpl_Term Unify_Fin
begin

hide_const (open) Unify_Flexflex_Complete.inst

text \<open>
  The search of \<^const>\<open>hounifiers\<close> terminates on problems with type variables if \<^const>\<open>MATCH\<close>
  does: the analogue of \<^theory>\<open>Pure_Unify_Correctness.Unify_Fin\<close>. The flex-flex phase terminates
  normally since the flex-flex pairs of a simplification are solvable: a ground instance of the
  type environment and a solution of the ground instance of the problem that maps each unbound
  variable to a constant function solve them, also if their type is a function type.
\<close>

subsection \<open>Flex-flex pairs are solvable\<close>

context csig
begin

lemma Abs_m_add: "Abs_m (n + m) t = Abs_m n (Abs_m m t)"
  by (induction n) simp_all

lemma smash_side_gen:
  assumes ac: "acyc env" and ety: "env_typed W env"
    and ty: "has_type W Bs t B" and h: "head_of t = Var x T" and unb: "vt_lookup (tenv env) x = None"
  shows "mk_subst (smash_sol env W) (tr t) \<equiv>\<^sub>\<beta>\<^sub>\<eta>
    Abs_m (length (arg_types B)) (dB.Var (code (AFree STR '''' (res_type B))))"
proof -
  let ?args = "snd (strip_comb t)"
  let ?H = "Abs_m (length (arg_types B)) (dB.Var (code (AFree STR '''' (res_type B))))"
  let ?ts = "map (mk_subst (smash_sol env W) \<circ> tr) ?args"
  have t: "t = list_comb (Var x T) ?args" using head_of_list_comb[of t] h by simp
  from ty t obtain As where hv: "has_type W Bs (Var x T) (foldr fun_type As B)"
    and As: "list_all2 (has_type W Bs) ?args As"
    by (metis has_type_list_comb)
  from hv have Wx: "W x = foldr fun_type As B" by (auto elim: has_type.cases)
  have sa: "smash_atom W x = Abs_m (length ?ts) ?H"
    using Wx list_all2_lengthD[OF As] by (simp add: smash_atom_def arg_res_types_foldr Abs_m_add)
  have "mk_subst (smash_sol env W) (tr t) = smash_atom W x \<degree>\<degree> ?ts"
    by (subst t) (simp add: tr_list_comb mk_subst_list_app smash_sol_def env_map_unbound[OF ac ety unb])
  also have "\<dots> \<equiv>\<^sub>\<beta>\<^sub>\<eta> ?H"
    using Abs_m_apps_closed_head[of ?H ?ts "length ?ts" "[]"] by (simp add: sa loose_bound_Abs_m)
  finally show ?thesis .
qed

end

context wf_csig
begin

lemma pinv_smash:
  assumes pi0: "pinv alg ar A W env ffs" and g: "gsol alg ar (tyenv env) \<rho>"
    and ff: "\<forall>dp\<in>set ffs. pff_shape env W dp \<and> heads_unb env dp"
  shows "pcinv alg ar A W \<rho> (tau (ityp \<rho> env W)) (smash_sol (instE \<rho> env) (ityp \<rho> env W)) env ffs"
proof -
  let ?\<theta> = "tyenv env" and ?V = "ityp \<rho> env W" and ?e = "instE \<rho> env"
  let ?\<sigma> = "smash_sol (instE \<rho> env) (ityp \<rho> env W)"
  note pi = pinvD[OF pi0]
  note ei = env_invD[OF penv_inv_inst[OF pi(1) g]]
  have sol: "solution ?V (tau ?V) ?\<sigma> ?e" by (rule smash_solution[OF ei(1,3,2)])
  have sl: "tsol ?\<theta> \<rho>" using g by (simp add: gsol_def)
  have ac: "tacyc ?\<theta>" "tcons_env ?\<theta>" using tinv_tacyc[OF pi(2)] tinv_tcons_env[OF pi(2)] by simp_all
  have "dsolved ?\<sigma> (instd \<rho> dp)" if dp: "dp \<in> set ffs" for dp
  proof -
    obtain rb t u where dpe: "dp = (rb, t, u)" by (cases dp)
    from ff dp dpe obtain B where ty: "typed env W (map snd rb) t B" "typed env W (map snd rb) u B"
      and vt: "is_Var (head_of t)" "is_Var (head_of u)" and hu: "heads_unb env (rb, t, u)"
      by (auto simp: pff_shape_def)
    obtain x T y U where h: "head_of t = Var x T" "head_of u = Var y U"
      using vt by (cases "head_of t"; cases "head_of u") auto
    have unb: "vt_lookup (tenv env) x = None" "vt_lookup (tenv env) y = None"
      using hu h unfolding heads_unb_def prod.case by blast+
    from pi(4)[OF dp] dpe have tw: "\<forall>U\<in>dtys (rb, t, u). tyw ar ?\<theta> A U" by auto
    have tc: "tcons ?\<theta> U" if "U \<in> dtys (rb, t, u)" for U using tyw_tcons[OF pi(2)] tw that by blast
    have tcB: "tcons ?\<theta> (tnorm ?\<theta> B)" by (rule tcons_tnorm[OF ac(1)])
    let ?B = "tsubst \<rho> (tnorm ?\<theta> B)"
    have tyi: "has_type ?V (map snd (instb \<rho> rb)) (inst \<rho> t) ?B"
      "has_type ?V (map snd (instb \<rho> rb)) (inst \<rho> u) ?B"
      using typed_inst[OF ac sl _ tcB, of "map snd rb" t W] typed_inst[OF ac sl _ tcB, of "map snd rb" u W]
        tc ty by (auto simp: typed_tnorm[OF ac(1)] map_snd_instb)
    have hi: "head_of (inst \<rho> t) = Var x (tsubst \<rho> T)" "head_of (inst \<rho> u) = Var y (tsubst \<rho> U)"
      using h by simp_all
    have ui: "vt_lookup (tenv ?e) x = None" "vt_lookup (tenv ?e) y = None" using unb by simp_all
    have "mk_subst ?\<sigma> (tr (inst \<rho> t)) \<equiv>\<^sub>\<beta>\<^sub>\<eta> mk_subst ?\<sigma> (tr (inst \<rho> u))"
      using equiv_trans[OF smash_side_gen[OF ei(1,3) tyi(1) hi(1) ui(1)]
          equiv_sym[OF smash_side_gen[OF ei(1,3) tyi(2) hi(2) ui(2)]]] .
    then show ?thesis by (simp add: dpe instd_def dsolved_dsolvedB dsolvedB_def equiv_Abs_m)
  qed
  then show ?thesis using pi0 g sol by (auto simp: pcinv_def)
qed

theorem foldrW_padd_ffpair_term:
  assumes "pinv alg ar A W env ffs" "\<forall>dp\<in>set ffs. pff_shape env W dp \<and> heads_unb env dp"
    "fch W (tyenv env) \<theta>0 ffs"
  shows "\<exists>r. okW (foldrW (add_ffpair alg) ffs (env, [])) r"
proof -
  obtain \<rho> where g: "gsol alg ar (tyenv env) \<rho>" by (rule pinv_gsol_exists[OF assms(1)])
  from foldrW_padd_ffpair_complete[OF pinv_smash[OF assms(1) g assms(2)] assms(2,3)] show ?thesis by blast
qed

lemma foldrW_padd_ffpair_pinv:
  assumes "pinv alg ar A W env ffs" "\<forall>dp\<in>set ffs. pff_shape env W dp \<and> heads_unb env dp"
    "fch W (tyenv env) \<theta>0 ffs" and r: "okW (foldrW (add_ffpair alg) ffs (env, [])) r"
  shows "\<exists>W'. pinv alg ar A W' (fst r) []"
proof -
  obtain \<rho> where g: "gsol alg ar (tyenv env) \<rho>" by (rule pinv_gsol_exists[OF assms(1)])
  from foldrW_padd_ffpair_complete[OF pinv_smash[OF assms(1) g assms(2)] assms(2,3)] obtain env' tps' W' \<sigma>'
    where o: "okW (foldrW (add_ffpair alg) ffs (env, [])) (env', tps')"
      and c: "pcinv alg ar A W' \<rho> (tau (ityp \<rho> env W)) \<sigma>' env' []"
    by blast
  from o r have "r = (env', tps')" by auto
  then show ?thesis using pcinvD(1)[OF c] by auto
qed

end


subsection \<open>The search\<close>

text \<open>
  The new problems of \<^const>\<open>MATCH\<close>: they satisfy the invariant for a typing that agrees with the
  old one on the old variables, and their environments extend the old one.
\<close>

context csig
begin

definition pmres :: "algebra \<Rightarrow> (name \<Rightarrow> nat) \<Rightarrow> (indexname \<times> psort) set \<Rightarrow> (indexname \<Rightarrow> ptyp) \<Rightarrow> env \<Rightarrow>
    elem \<Rightarrow> bool" where
  "pmres alg ar A W env x \<longleftrightarrow> (\<exists>env' dps' W'. x = El_E env' dps' \<and> pinv alg ar A W' env' dps' \<and>
    agreeV (maxidx env) W W' \<and> maxidx env \<le> maxidx env' \<and> pextends env' env)"

lemma pmres_pinv: "pmres alg ar A W env x \<Longrightarrow> \<exists>env' dps' W'. x = El_E env' dps' \<and> pinv alg ar A W' env' dps'"
  unfolding pmres_def by blast

lemma pmres_mono:
  assumes "pmres alg ar A W env1 x" "pextends env1 env" "maxidx env \<le> maxidx env1"
  shows "pmres alg ar A W env x"
  using assms unfolding pmres_def by (blast intro: agreeV_mono pextends_trans order_trans)

text \<open>
  \<open>pmatch_fin\<close>: \<^const>\<open>MATCH\<close> on a flex-rigid pair yields, unless it fails, a finite enumeration of
  new problems that satisfy the invariant, as \<^const>\<open>match_fin\<close>.
\<close>

definition pmatch_fin :: "cfg \<Rightarrow> (name \<Rightarrow> nat) \<Rightarrow> (indexname \<times> psort) set \<Rightarrow> bool" where
  "pmatch_fin cfg ar A \<longleftrightarrow> (\<forall>W env dp dps. pinv (cfg_alg cfg) ar A W env (dp # dps) \<longrightarrow>
    pfr_shape env W dp \<longrightarrow> heads_unb env dp \<longrightarrow>
    cuok (MATCH cfg env dp dps) (\<lambda>ms. fin cfg ms (pmres (cfg_alg cfg) ar A W env)))"

lemma pmatch_finD:
  "pmatch_fin cfg ar A \<Longrightarrow> pinv (cfg_alg cfg) ar A W env (dp # dps) \<Longrightarrow> pfr_shape env W dp \<Longrightarrow>
    heads_unb env dp \<Longrightarrow> cuok (MATCH cfg env dp dps) (\<lambda>ms. fin cfg ms (pmres (cfg_alg cfg) ar A W env))"
  unfolding pmatch_fin_def by blast

lemma pinv_set: "set dps = set dps' \<Longrightarrow> pinv alg ar A W env dps \<longleftrightarrow> pinv alg ar A W env dps'"
  by (simp add: pinv_def)

end

context wf_csig
begin

text \<open>
  The search keeps a further invariant \<open>P\<close> of the typing and the environment that survives
  extensions of the environment by typings that agree on the old variables.
\<close>

lemma fin_AddUnify_pinv:
  assumes cfg: "cfg_alg cfg = alg" and M: "pmatch_fin cfg ar A" and fin: "finite A"
    and QR: "\<And>W env ffs \<theta>0 r. pinv alg ar A W env ffs \<Longrightarrow>
      (\<forall>dp\<in>set ffs. pff_shape env W dp \<and> heads_unb env dp) \<Longrightarrow> fch W (tyenv env) \<theta>0 ffs \<Longrightarrow>
      okW (foldrW (add_ffpair alg) ffs (env, [])) r \<Longrightarrow> P W env \<Longrightarrow> Q (El_R (fst r) (snd r))"
    and PS: "\<And>W env W' env' dps'. P W env \<Longrightarrow> pinv alg ar A W' env' dps' \<Longrightarrow> agreeV (maxidx env) W W' \<Longrightarrow>
      maxidx env \<le> maxidx env' \<Longrightarrow> pextends env' env \<Longrightarrow> P W' env'"
  shows "pinv alg ar A W env dps \<Longrightarrow> P W env \<Longrightarrow> fin cfg R Q \<Longrightarrow> fin cfg (S_AddUnify td env dps R) Q"
proof (induction "nat (int_of_integer (cfg_search_bound cfg + 1 - td))" arbitrary: td W env dps R rule: less_induct)
  case less
  let ?S = "SIMPL (cfg_alg cfg) env dps"
  let ?H = "\<lambda>e. case e of CANTUNIFY \<Rightarrow> pull cfg R | _ \<Rightarrow> raiseW e"
  have red: "resW (pull cfg (S_AddUnify td env dps R)) r \<longleftrightarrow> resW (handleW (bindW ?S (au_cont cfg td R)) ?H) r" for r
    by (rule resW_pull_AddUnify)
  from SIMPL_pterm[OF fin less.prems(1)] cfg consider (cu) evs where "?S = Some (evs, UErr CANTUNIFY)"
    | (ok) st where "okW ?S st" "ptsimpl_res alg ar A W dps env st"
    unfolding cuok_def by auto
  then show ?case
  proof cases
    case cu
    have "resW (pull cfg (S_AddUnify td env dps R)) r \<longleftrightarrow> resW (pull cfg R) r" for r
      using cu by (simp add: red bindW_def resW_handleW_err)
    from fin_res[OF this less.prems(3)] show ?thesis .
  next
    case ok
    obtain env' ffs frs where st: "st = (env', ffs, frs)" by (cases st)
    from ok(1) obtain evs where S: "?S = Some (evs, UOk st)" by blast
    have red': "resW (pull cfg (S_AddUnify td env dps R)) r \<longleftrightarrow> resW (handleW (au_cont cfg td R st) ?H) r" for r
      unfolding red by (rule resW_cong_handleW) (simp_all add: resW_bindW_ok[OF S])
    from ok(2) have inv': "pinv alg ar A W env' (ffs @ frs)" and ffsh: "\<And>dp. dp \<in> set ffs \<Longrightarrow> pff_shape env' W dp"
      and frsh: "\<And>dp. dp \<in> set frs \<Longrightarrow> pfr_shape env' W dp" and hu: "\<And>dp. dp \<in> set (ffs @ frs) \<Longrightarrow> heads_unb env' dp"
      and fc: "fch W (tyenv env') (tyenv env) ffs" and pe: "pextends env' env" "maxidx env \<le> maxidx env'"
      by (auto simp: st ptsimpl_res_def)
    have P': "P W env'" by (rule PS[OF less.prems(2) inv' agreeV_refl pe(2,1)])
    show ?thesis
    proof (cases frs)
      case Nil
      have inv0: "pinv alg ar A W env' ffs" using inv' Nil by simp
      have ffa: "\<forall>dp\<in>set ffs. pff_shape env' W dp \<and> heads_unb env' dp" using ffsh hu by auto
      from foldrW_padd_ffpair_term[OF inv0 ffa fc]
      obtain r evs2 where f: "foldrW (add_ffpair (cfg_alg cfg)) ffs (env', []) = Some (evs2, UOk r)"
        using cfg by auto
      have "resW (pull cfg (S_AddUnify td env dps R)) (UOk (Some (El_R (fst r) (snd r), R)))"
        unfolding red' by (simp add: st Nil au_cont_def f handleW_def bindW_def returnW_def resW_def)
      then obtain evs' where P: "pull cfg (S_AddUnify td env dps R) =
          Some (evs', UOk (Some (El_R (fst r) (snd r), R)))"
        by (auto simp: resW_def)
      from less.prems(3) obtain ys where ys: "evals cfg R ys" "\<forall>y\<in>set ys. Q y" by (auto simp: fin_def)
      have "Q (El_R (fst r) (snd r))" by (rule QR[OF inv0 ffa fc _ P']) (use f cfg in auto)
      from evals.Cons[OF P ys(1)] this ys(2) show ?thesis
        unfolding fin_def by (intro exI[of _ "El_R (fst r) (snd r) # ys"]) simp
    next
      case (Cons dp frs')
      show ?thesis
      proof (cases "cfg_search_bound cfg < td")
        case True
        have "resW (au_cont cfg td R st) r \<longleftrightarrow> resW (pull cfg R) r" for r
          by (simp add: au_cont_def st Cons True resW_emit)
        then have "resW (pull cfg (S_AddUnify td env dps R)) r \<longleftrightarrow> resW (pull cfg R) r" for r
          unfolding red' by (rule resW_handleW_fin[OF _ less.prems(3)])
        from fin_res[OF this less.prems(3)] show ?thesis .
      next
        case False
        have "set (dp # frs' @ ffs) = set (ffs @ frs)" by (auto simp: Cons)
        from pinv_set[OF this] inv' have invM: "pinv (cfg_alg cfg) ar A W env' (dp # frs' @ ffs)" using cfg by blast
        let ?M = "MATCH cfg env' dp (frs' @ ffs)"
        from pmatch_finD[OF M invM frsh[of dp] hu[of dp]] Cons cfg consider (cu) evs where "?M = Some (evs, UErr CANTUNIFY)"
          | (mok) ms where "okW ?M ms" "fin cfg ms (pmres alg ar A W env')"
          unfolding cuok_def by auto
        then show ?thesis
        proof cases
          case cu
          have "resW (au_cont cfg td R st) r \<longleftrightarrow> resW (raiseW CANTUNIFY) r" for r
            by (simp add: au_cont_def st Cons False resW_whenW_emit resW_bindW_err[OF cu] resW_raiseW)
          then have "resW (pull cfg (S_AddUnify td env dps R)) r \<longleftrightarrow> resW (pull cfg R) r" for r
            unfolding red' by (subst resW_cong_handleW[of _ "raiseW CANTUNIFY" ?H ?H])
              (simp_all add: raiseW_def resW_handleW_err)
          from fin_res[OF this less.prems(3)] show ?thesis .
        next
          case mok
          from mok(1) obtain evs where Mok: "?M = Some (evs, UOk ms)" by blast
          have IH: "fin cfg (S_AddUnify (td + 1) env'' dps'' R') Q"
            if "pinv alg ar A W'' env'' dps''" "P W'' env''" "fin cfg R' Q" for W'' env'' dps'' R'
            using less.hyps[OF depth_measure[OF False] that] .
          have IH': "fin cfg (S_AddUnify (td + 1) env'' dps'' R') Q"
            if "pinv alg ar A W'' env'' dps''" "agreeV (maxidx env') W W''" "maxidx env' \<le> maxidx env''"
              "pextends env'' env'" "fin cfg R' Q" for W'' env'' dps'' R'
            using IH[OF that(1) PS[OF P' that(1-4)] that(5)] .
          have "fin cfg (S_ItRight (td + 1) ms R) Q"
            by (rule fin_ItRight[OF fin_mono[OF mok(2)] less.prems(3)]) (auto simp: pmres_def intro: IH')
          moreover have "resW (au_cont cfg td R st) r \<longleftrightarrow> resW (pull cfg (S_ItRight (td + 1) ms R)) r" for r
            by (simp add: au_cont_def st Cons False resW_whenW_emit resW_bindW_ok[OF Mok])
          ultimately have "resW (pull cfg (S_AddUnify td env dps R)) r \<longleftrightarrow> resW (pull cfg (S_ItRight (td + 1) ms R)) r" for r
            unfolding red' by (intro resW_handleW_fin)
          from fin_res[OF this] \<open>fin cfg (S_ItRight (td + 1) ms R) Q\<close> show ?thesis by blast
        qed
      qed
    qed
  qed
qed

lemma fin_AddUnify_paux:
  assumes cfg: "cfg_alg cfg = alg" and M: "pmatch_fin cfg ar A" and fin: "finite A"
    and QR: "\<And>W env ffs \<theta>0 r. pinv alg ar A W env ffs \<Longrightarrow>
      (\<forall>dp\<in>set ffs. pff_shape env W dp \<and> heads_unb env dp) \<Longrightarrow> fch W (tyenv env) \<theta>0 ffs \<Longrightarrow>
      okW (foldrW (add_ffpair alg) ffs (env, [])) r \<Longrightarrow> Q (El_R (fst r) (snd r))"
  shows "pinv alg ar A W env dps \<Longrightarrow> fin cfg R Q \<Longrightarrow> fin cfg (S_AddUnify td env dps R) Q"
  using fin_AddUnify_pinv[OF cfg M fin, where P = "\<lambda>_ _. True" and Q = Q] QR by blast

text \<open>Hence \<^const>\<open>hounifiers\<close> enumerates finitely many unifiers in the invariant, if \<^const>\<open>MATCH\<close> does.\<close>

theorem hounifiers_pfin_match:
  assumes "cfg_alg cfg = alg" "pmatch_fin cfg ar A" "finite A"
    "pinv alg ar A W env (map (\<lambda>(t, u). (rb, t, u)) tus)"
  shows "fin cfg (hounifiers rb env tus) (\<lambda>x. \<exists>env' tps. x = El_R env' tps \<and> (\<exists>W'. pinv alg ar A W' env' []))"
  unfolding hounifiers_def
proof (rule fin_AddUnify_paux[OF assms(1-3) _ assms(4) fin_Empty])
  fix W env ffs \<theta>0 r
  assume "pinv alg ar A W env ffs" "\<forall>dp\<in>set ffs. pff_shape env W dp \<and> heads_unb env dp"
    "fch W (tyenv env) \<theta>0 ffs" "okW (foldrW (add_ffpair alg) ffs (env, [])) r"
  from foldrW_padd_ffpair_pinv[OF this]
  show "\<exists>env' tps. El_R (fst r) (snd r) = El_R env' tps \<and> (\<exists>W'. pinv alg ar A W' env' [])" by simp
qed

end

end

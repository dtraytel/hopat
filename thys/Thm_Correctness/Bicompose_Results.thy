section \<open>The results of \<open>bicompose_aux\<close>\<close>

theory Bicompose_Results
  imports Bicompose_Thm
begin

text \<open>
  The results of a call of \<^const>\<open>bicompose_aux\<close>, described without its internals, as the results
  of \<open>Unify.unifiers\<close> are: each result consists of a unifier of the problem of the call
  (\<open>bicompose_problem\<close>) and of the flex-flex pairs of the proof state and the rule, modulo
  the flex-flex pairs \<open>tps\<close> that it leaves, and of the proposition \<open>\<lbrakk>Bs; As'\<rbrakk> \<Longrightarrow> C\<close> with the
  unifier applied, up to \<open>\<beta>\<close>-reduction. The new premises \<open>As'\<close> are the premises of the rule that
  remain (all, or all but the first for elim-resolution), with variables that occur nowhere else
  renamed if the rule is lifted, and flattened if \<open>flatten\<close>.
\<close>

subsection \<open>Applying the environment\<close>

context pure_sig
begin

lemma env_apply_App [simp]: "env_apply env (s $ t) = env_apply env s $ env_apply env t"
  by (simp add: env_apply_def)

lemma env_apply_Abs [simp]: "env_apply env (Abs a T t) = Abs a (tnorm (tyenv env) T) (env_apply env t)"
  by (simp add: env_apply_def)

lemma env_apply_Const [simp]: "env_apply env (Const c T) = Const c (tnorm (tyenv env) T)"
  by (simp add: env_apply_def)

lemma env_apply_implies [simp]: "env_apply env implies = implies"
  by (simp add: implies_def propT_def)

lemma env_apply_list_implies:
  "env_apply env (list_implies Xs Y) = list_implies (map (env_apply env) Xs) (env_apply env Y)"
  by (induction Xs) (simp_all add: mk_implies_def)

lemma beta_reds_list_implies:
  "list_all2 (\<lambda>X Y. X \<rightarrow>\<^sub>\<beta>\<^sup>* Y) Xs Ys \<Longrightarrow> X \<rightarrow>\<^sub>\<beta>\<^sup>* Y \<Longrightarrow> list_implies Xs X \<rightarrow>\<^sub>\<beta>\<^sup>* list_implies Ys Y"
  by (induction Xs Ys rule: list_all2_induct) (auto simp: mk_implies_def)

text \<open>The environment acts as the identity on terms whose variables it does not bind:\<close>

lemma unb_env_apply: "unb env t \<Longrightarrow> acyc env \<Longrightarrow> tacyc (tyenv env) \<Longrightarrow> env_apply env t = t"
proof (rule env_apply_normal)
  assume u: "unb env t" and ac: "tacyc (tyenv env)"
  show "env_normal env t" unfolding env_normal_def
  proof (intro conjI ballI)
    fix v assume "v \<in> vars t"
    then show "case v of (x, T) \<Rightarrow> vt_lookup (tenv env) x = None" using u by (auto simp: unb_def)
  next
    fix U assume U: "U \<in> typs t"
    show "tnorm (tyenv env) U = U"
    proof (rule tnorm_unbound_id[OF ac])
      fix w S assume "(w, S) \<in> tvars U"
      then have "(w, S) \<in> ttvars t" using U by (auto simp: ttvars_def)
      then show "vt_lookup (tyenv env) w = None" using u by (auto simp: unb_def)
    qed
  qed
qed

text \<open>\<^const>\<open>norm_term_skip\<close> applies the environment and \<open>\<beta>\<close>-reduces, as \<^const>\<open>norm_term\<close>:\<close>

lemma norm_term_skip_env_apply:
  "okT (norm_term_skip env n t) t' \<Longrightarrow> skip_unb env n t \<Longrightarrow> e \<turnstile> t : propT \<Longrightarrow>
    acyc env \<Longrightarrow> closed_env env \<Longrightarrow> tacyc (tyenv env) \<Longrightarrow> env_apply env t \<rightarrow>\<^sub>\<beta>\<^sup>* t'"
proof (induction env n t arbitrary: e t' rule: norm_term_skip.induct)
  case (1 env n t)
  note ac = "1.prems"(4-6)
  show ?case
  proof (cases "n = 0")
    case True
    with "1.prems"(1) have "ok (norm_term env t) t'" by (simp add: norm_term_skip.simps)
    then show ?thesis by (rule norm_term_env_apply(1)[OF _ ac])
  next
    case n: False
    show ?thesis
    proof (cases "dest_all t")
      case (Some x)
      then obtain a T b where aTb: "dest_all t = Some (a, T, b)" by (cases x) auto
      from "1.prems"(1) n aTb obtain T' b' where T': "ok (norm_type (tyenv env) T) T'"
        and b': "okT (norm_term_skip env n b) b'" and t': "t' = all_const T' $ Abs a T' b'"
        by (auto simp: norm_term_skip.simps[of env n t])
      note ty = typing_dest_all[OF "1.prems"(3) aTb]
      have sk: "skip_unb env n b" using "1.prems"(2) n aTb by (simp add: skip_unb.simps[of env n t])
      have TT: "T' = tnorm (tyenv env) T"
      proof (cases "vt_is_empty (tyenv env)")
        case True
        then show ?thesis using T' by (simp add: norm_type_def tnorm_empty return_def)
      next
        case False
        then have "ok (norm_type_aux (tyenv env) T) T'" using T' by (simp add: norm_type_def)
        then show ?thesis using norm_type_aux_tnorm[OF _ refl ac(3)] by auto
      qed
      have IH: "env_apply env b \<rightarrow>\<^sub>\<beta>\<^sup>* b'"
        by (rule "1.IH"(2)[OF n aTb refl refl _ b' sk ty(5) ac]) (simp add: T')
      have "env_apply env t = all_const T' $ Abs a T' (env_apply env b)"
        using ty(1) TT by (simp add: all_const_def propT_def)
      then show ?thesis using IH t' by auto
    next
      case None
      show ?thesis
      proof (cases "dest_imp t")
        case (Some x)
        then obtain A B where AB: "dest_imp t = Some (A, B)" by (cases x) auto
        from "1.prems"(1) n None AB obtain B' where B': "okT (norm_term_skip env (n - 1) B) B'"
          and t': "t' = mk_implies A B'"
          by (auto simp: norm_term_skip.simps[of env n t])
        note ty = typing_dest_imp[OF "1.prems"(3) AB]
        have sk: "unb env A" "skip_unb env (n - 1) B"
          using "1.prems"(2) n None AB by (simp_all add: skip_unb.simps[of env n t])
        have IH: "env_apply env B \<rightarrow>\<^sub>\<beta>\<^sup>* B'"
          by (rule "1.IH"(1)[OF n None AB refl B' sk(2) ty(5) ac])
        have "env_apply env t = implies $ A $ env_apply env B"
          using ty(1) unb_env_apply[OF sk(1) ac(1,3)] by simp
        then show ?thesis using IH t' by (auto simp: mk_implies_def)
      next
        case None2: None
        with "1.prems"(1) n None show ?thesis by (simp add: norm_term_skip.simps[of env n t])
      qed
    qed
  qed
qed

text \<open>With \<open>match\<close>, \<^const>\<open>addth\<close> fails if the environment binds a variable of the proof state.\<close>

lemma addth_match:
  assumes "okT (addth ctx A na (env, tps)) r" "bc_match ctx"
  shows "Pure_Bicompose.above env (bc_smax ctx)"
proof (cases "env_is_empty env")
  case True
  then show ?thesis
    by (auto simp: Pure_Bicompose.above_def env_is_empty_def vt_above.rep_eq vt_is_empty.rep_eq)
next
  case False
  show ?thesis
  proof (rule ccontr)
    assume "\<not> Pure_Bicompose.above env (bc_smax ctx)"
    with assms False show False
      by (auto simp: addth_def raiseW_def bindW_def liftMT_def liftWT_def liftM_def
          split: option.splits xres.splits prod.splits)
  qed
qed

end


subsection \<open>The shape of the results\<close>

context bicompose_call
begin

theorem bicompose_aux_results:
  assumes rp: "rprop = list_implies As B" "nsubgoal = ilength As"
    and ok: "okT bcall s" and res: "bresult (unify_ops cfg vl) s r"
  obtains env tus0 tps n As0 tab r2 As1 As' where
    "incremented \<Longrightarrow> env = empty_env (max rmax smax)"
    "\<not> incremented \<Longrightarrow> okT (unify_var_types alg (stpairs, list_implies (Bs @ [Bi]) C) (rtpairs, rprop)
      (empty_env (max rmax smax))) (Some env)"
    "bicompose_problem lifted eres_flg Bi As B tus0"
    "extends env (br_env r)"
    "\<And>\<rho> \<sigma>. solution \<rho> \<sigma> (br_env r) \<Longrightarrow> cert_inst \<rho> \<Longrightarrow>
      \<forall>(t, u)\<in>set tps. ap \<rho> \<sigma> t \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma> u \<Longrightarrow>
      \<forall>(t, u)\<in>set (tus0 @ rtpairs @ stpairs). ap \<rho> \<sigma> t \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma> u"
    "As = (if eres_flg then [hd As] else []) @ As0" "br_A r = (if eres_flg then Some (hd As) else None)"
    "\<not> eres_flg \<Longrightarrow> n = 0"
    "As1 = As0 \<and> tab = [] \<or> lifted \<and> As1 = map (strip_apply (ren_term (tab, r2)) Bi) As0"
    "\<And>x. ren_name tab x \<noteq> x \<Longrightarrow> x \<notin> vnames (fst (if lifted then strip_assums2 B Bi else (B, Bi))) \<and>
      (\<forall>(t, u)\<in>set rtpairs. x \<notin> vnames t \<and> x \<notin> vnames u)"
    "list_all2 (\<lambda>A A'. if flatten then ok (flatten_params vl n A) A' else A' = A) As1 As'"
    "list_all2 (\<lambda>(t, u) (t', u'). env_apply (br_env r) t \<rightarrow>\<^sub>\<beta>\<^sup>* t' \<and> env_apply (br_env r) u \<rightarrow>\<^sub>\<beta>\<^sup>* u')
      tps (br_tpairs r)"
    "env_apply (br_env r) (list_implies (Bs @ As') C) \<rightarrow>\<^sub>\<beta>\<^sup>* br_prop r"
    "match_flg \<Longrightarrow> Pure_Bicompose.above (br_env r) smax"
proof -
  let ?S = "list_implies (Bs @ [Bi]) C"
  obtain rAs B0 env where sp0: "ok (strip_prems nsubgoal [] rprop) (rAs, B0)"
    and P0: "rprop = list_implies (rev rAs) B0"
    and pa: "pinv_all (call_spec cfg vl env flatten match_flg smax stpairs Bs Bi C lifted eres_flg rtpairs rAs B0)"
    and rc: "rchar (call_spec cfg vl env flatten match_flg smax stpairs Bs Bi C lifted eres_flg rtpairs rAs B0) r"
    and lr0: "lifted \<Longrightarrow> lifted_rule smax Bi (rev rAs) B0"
    and env: "incremented \<Longrightarrow> env = empty_env (max rmax smax)"
      "\<not> incremented \<Longrightarrow> okT (unify_var_types alg (stpairs, ?S) (rtpairs, rprop) (empty_env (max rmax smax)))
        (Some env)"
    using bicompose_aux_rchar[OF ok res cfg state rule tv inc] by metis
  have "strip_prems (ilength As) [] (list_implies As B) = return (rev As, B)"
    using strip_prems_list_implies[of As "[]" B] by simp
  with sp0 rp have rA: "rAs = rev As" and B0: "B0 = B" by (simp_all add: return_def)
  define nlift where "nlift = count_prems (strip_all_body Bi) + (if eres_flg then -1 else 0)"
  define BBi where "BBi = (if lifted then strip_assums2 B Bi else (B, Bi))"
  define ctx where "ctx = BCtx flatten match_flg lifted smax Bs Bi C rtpairs nlift BBi (BBi # rtpairs @ stpairs)"
  define sp where "sp = call_spec cfg vl env flatten match_flg smax stpairs Bs Bi C lifted eres_flg rtpairs rAs B"
  have sp': "sp = BSpec cfg vl env ctx rAs eres_flg"
    by (simp add: sp_def call_spec_def Let_def nlift_def BBi_def ctx_def)
  have ctx_sel: "bc_flatten ctx = flatten" "bc_match ctx = match_flg" "bc_lifted ctx = lifted"
    "bc_smax ctx = smax" "bc_Bs ctx = Bs" "bc_Bi ctx = Bi" "bc_C ctx = C" "bc_rtpairs ctx = rtpairs"
    "bc_nlift ctx = nlift" "bc_BBi ctx = BBi" "bc_dpairs ctx = BBi # rtpairs @ stpairs"
    by (simp_all add: ctx_def)
  have sp_sel: "sp_eres sp = eres_flg" "sp_ctx sp = ctx" "sp_vl sp = vl" "sp_rAs sp = rAs" "sp_env sp = env"
    by (simp_all add: sp')
  note pa = pa[folded sp_def[unfolded B0[symmetric]], unfolded B0] and rc = rc[unfolded B0]
  have pa': "pinv_all sp" using pa B0 by (simp add: sp_def)
  have rc': "rchar sp r" using rc by (simp add: sp_def)
  obtain A1o na tus env' tps Pre As0 n dps tps1 where its: "itsok sp A1o na tus"
    and ur: "ures env tus (El_R env' tps)" and ad: "okT (addth ctx A1o na (env', tps)) r"
    and rAs: "rev rAs = Pre @ As0" and na: "okT (newAs vl ctx As0 n dps tps1) na"
    and dps: "BBi \<in> set dps"
    and nb: "0 \<le> n" "n \<le> count_prems (strip_all_body Bi)"
      "nlift + (if 0 < n \<and> flatten then 1 else 0) \<le> count_prems (strip_all_body Bi)" "0 \<le> nlift"
    and A1o: "Pre = [] \<and> A1o = None \<and> n = 0 \<or> (\<exists>A1. Pre = [A1] \<and> A1o = Some A1 \<and> 1 \<le> n)"
    and pre: "\<And>A1. A1 \<in> set Pre \<Longrightarrow> eres_flg"
    by (rule rchar_data[OF sp' ctx_def nlift_def rc']) blast
  have pw: "pwf env tus" using itsok_pwf[OF its pa'] by (simp add: sp_sel)
  from ures_inv[OF ur pw] obtain A' K' X' where ei': "einv A' K' env'" by blast
  note e' = einvD[OF ei']
  have ac': "acyc env'" "closed_env env'" "tacyc (tyenv env')" using e' by blast+
  have rbr: "br_env r = env'" "br_A r = A1o" using ad by (cases rule: addth_cases; simp)+
  text \<open>The problem and the premises that remain.\<close>
  obtain tus0 where tus: "tus = tus0 @ rtpairs @ stpairs" and pb: "bicompose_problem lifted eres_flg Bi As B tus0"
    and pre': "Pre = (if eres_flg then [hd As] else [])"
  proof -
    from its consider (res) "\<not> eres_flg" "A1o = None" "tus = BBi # rtpairs @ stpairs"
      | (eres) m asm where "eres_flg" "1 \<le> m" "nat_of_integer m \<le> length (asms_of sp)"
        "A1o = Some (er_A1 (eres_of sp))" "asm = asms_of sp ! (nat_of_integer m - 1)" "tus = eres_prob sp asm"
      unfolding itsok_def sp_sel ctx_sel by blast
    then show thesis
    proof cases
      case res
      have "Pre = []" using A1o res(2) by auto
      then show thesis
        by (intro that[of "[BBi]"]) (use res in \<open>simp_all add: bicompose_problem_def BBi_def Let_def\<close>)
    next
      case eres
      have m1: "1 \<le> nat_of_integer m" using eres(2) by (simp add: integer_reps)
      obtain A1 As1 where rA1: "rev rAs = A1 # As1"
        using eres(3) m1 by (cases "rev rAs") (auto simp: asms_of_def sp')
      obtain params asms concl where ap: "assum_problems (nlift + 1) A1 = (params, asms, concl)"
        by (cases "assum_problems (nlift + 1) A1")
      have er: "eres_of sp = ER env params concl (rlist_abs params concl) A1 As1" "asms_of sp = asms"
        using rA1 ap by (simp_all add: eres_of_def asms_of_def sp' ctx_sel)
      have asm: "asm \<in> set asms" using eres(2,3,5) er(2) by (simp add: integer_reps)
      have cnt: "nlift + 1 = count_prems (strip_all_body Bi)" using eres(1) by (simp add: nlift_def)
      have As: "As = A1 # As1" using rA1 rA by simp
      have "Pre = [A1]" using A1o eres(4) er rAs rA1 by auto
      show thesis
      proof (rule that[of "[(rlist_abs params asm, rlist_abs params concl), BBi]"])
        show "tus = [(rlist_abs params asm, rlist_abs params concl), BBi] @ rtpairs @ stpairs"
          using eres(6) er by (simp add: eres_prob_def sp_sel ctx_sel)
        show "bicompose_problem lifted eres_flg Bi As B [(rlist_abs params asm, rlist_abs params concl), BBi]"
          unfolding bicompose_problem_def Let_def using eres(1) As ap cnt asm by (auto simp: BBi_def)
      qed (use \<open>Pre = [A1]\<close> As eres(1) in simp)
    qed
  qed
  have As: "As = (if eres_flg then [hd As] else []) @ As0" using rAs rA pre' by simp
  have nr: "\<not> eres_flg \<Longrightarrow> n = 0" using A1o pre' by auto
  have bA: "br_A r = (if eres_flg then Some (hd As) else None)"
    using A1o pre' rbr(2) by (cases eres_flg) auto
  text \<open>The unifier.\<close>
  have ext: "extends env env'"
    using uresultD(2)[OF ures_pwf[OF ur pw]] by blast
  have sol: "\<forall>(t, u)\<in>set (tus0 @ rtpairs @ stpairs). ap \<rho> \<sigma> t \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma> u"
    if "solution \<rho> \<sigma> env'" "cert_inst \<rho>" "\<forall>(t, u)\<in>set tps. ap \<rho> \<sigma> t \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma> u" for \<rho> \<sigma>
    using ures_solves[OF ur pw that] tus by simp
  text \<open>The new premises.\<close>
  obtain tab r2 where ren0: "\<And>x. ren_name tab x \<noteq> x \<Longrightarrow> (\<forall>(t, u)\<in>set dps. x \<notin> vnames t) \<and>
      (\<forall>(t, u)\<in>set (bc_rtpairs ctx @ tps1). x \<notin> vnames t \<and> x \<notin> vnames u)"
    and old0: "na_oldAs na = As0 \<and> tab = [] \<and> na_ren na = None \<or>
      bc_lifted ctx \<and> na_ren na = Some (tab, r2) \<and> na_oldAs na = map (strip_apply (ren_term (tab, r2)) (bc_Bi ctx)) As0"
    and flat0: "list_all2 (\<lambda>A1 A'. if bc_flatten ctx then ok (flatten_params vl n A1) A' else A1 = A')
      (na_oldAs na) (na_As na)"
    using newAs_ren[OF na] by blast
  note ren = ren0[unfolded ctx_sel] and old = old0[unfolded ctx_sel] and flat = flat0[unfolded ctx_sel]
  have ren': "x \<notin> vnames (fst BBi) \<and> (\<forall>(t, u)\<in>set rtpairs. x \<notin> vnames t \<and> x \<notin> vnames u)"
    if "ren_name tab x \<noteq> x" for x
    using ren[OF that] dps by fastforce
  have flat': "list_all2 (\<lambda>A A'. if flatten then ok (flatten_params vl n A) A' else A' = A)
      (na_oldAs na) (na_As na)"
    using flat by (rule list_all2_mono) auto
  text \<open>The proposition and the flex-flex pairs.\<close>
  have wS0: "wtp ?S" "ibelow smax ?S" and wR0: "wtp rprop" using state rule(1) by (simp_all add: wt_thm_def)
  have iS: "\<forall>X\<in>set Bs. ibelow smax X" "ibelow smax Bi" "ibelow smax C" using wS0(2) by simp_all
  have wR: "\<forall>X\<in>set (rev rAs). wtp X" using wtp_list_implies[OF wR0[unfolded P0]] by simp
  have wA0: "\<forall>A\<in>set As0. wtp A" using wR rAs by auto
  have lr: "lifted \<Longrightarrow> lifted_rule smax Bi As0 B"
  proof -
    assume l: lifted
    have "lifted_rule smax Bi (Pre @ As0) B" using lr0[OF l] rAs B0 by simp
    then show ?thesis by (induction Pre) (auto dest: lifted_rule_Cons)
  qed
  have wN: "\<forall>A\<in>set (na_As na). wtp A"
    using newAs_props[OF na, of B] lr iS(2) wA0 vl by (auto simp: ctx_sel)
  have eS: "env_apply env' X = X" if "X \<in> set Bs \<or> X = C" "Pure_Bicompose.above env' smax" for X
    using unb_env_apply[OF above_unb[OF that(2)] ac'(1,3)] iS that(1) by blast
  have nt: "env_apply env' X \<rightarrow>\<^sub>\<beta>\<^sup>* Y" if "ok (norm_term env' X) Y" for X Y
    by (rule norm_term_env_apply(1)[OF that ac'])
  have main: "list_all2 (\<lambda>(t, u) (t', u'). env_apply env' t \<rightarrow>\<^sub>\<beta>\<^sup>* t' \<and> env_apply env' u \<rightarrow>\<^sub>\<beta>\<^sup>* u')
      tps (br_tpairs r) \<and> env_apply env' (list_implies (Bs @ na_As na) C) \<rightarrow>\<^sub>\<beta>\<^sup>* br_prop r"
    using ad
  proof (cases rule: addth_cases)
    case empty
    then show ?thesis by (simp add: env_apply_empty list.rel_refl ctx_sel split: prod.splits)
  next
    case (norm ntps Hs C')
    have tp: "list_all2 (\<lambda>(t, u) (t', u'). env_apply env' t \<rightarrow>\<^sub>\<beta>\<^sup>* t' \<and> env_apply env' u \<rightarrow>\<^sub>\<beta>\<^sup>* u') tps ntps"
      using norm(3) by (rule list_all2_mono) (auto intro: nt split: prod.splits)
    have "env_apply env' (list_implies (Bs @ na_As na) C) \<rightarrow>\<^sub>\<beta>\<^sup>* list_implies Hs C'"
      unfolding env_apply_list_implies
      using norm(4)[unfolded ctx_sel]
    proof (elim disjE conjE exE)
      fix As'' assume ab: "Pure_Bicompose.above env' smax" and l: lifted and C': "C' = C" and Hs: "Hs = Bs @ As''"
        and sk: "list_all2 (\<lambda>X X'. okT (norm_term_skip env' nlift X) X') (na_As na) As''"
      have skips: "\<forall>X\<in>set (na_As na). \<forall>H\<in>set (take (nat_of_integer nlift) (spine_hyps X)).
          \<exists>H0\<in>set (spine_hyps Bi). vars H = vars H0 \<and> typs H = typs H0"
        using newAs_skip[OF na _ _ vl nb(4)] l lr nb(3) by (simp add: ctx_sel)
      have su: "skip_unb env' nlift X" if "X \<in> set (na_As na)" for X
      proof (rule skip_unb_take[OF nb(4)])
        show "\<forall>H\<in>set (take (nat_of_integer nlift) (spine_hyps X)). unb env' H"
        proof
          fix H assume "H \<in> set (take (nat_of_integer nlift) (spine_hyps X))"
          with skips that obtain H0 where H0: "H0 \<in> set (spine_hyps Bi)" "vars H = vars H0" "typs H = typs H0"
            by blast
          have "ibelow smax H0" by (rule ibelow_spine_hyps[OF iS(2) H0(1)])
          then have "ibelow smax H" using H0(2,3) by (simp add: ibelow_def ttvars_def)
          then show "unb env' H" by (rule above_unb[OF ab])
        qed
      qed
      have "list_all2 (\<lambda>X Y. X \<rightarrow>\<^sub>\<beta>\<^sup>* Y) (map (env_apply env') (Bs @ na_As na)) Hs"
        unfolding Hs list_all2_map1
      proof (rule list_all2_appendI)
        show "list_all2 (\<lambda>X Y. env_apply env' X \<rightarrow>\<^sub>\<beta>\<^sup>* Y) Bs Bs"
          by (rule list.rel_refl_strong) (simp add: eS[OF _ ab])
        show "list_all2 (\<lambda>X Y. env_apply env' X \<rightarrow>\<^sub>\<beta>\<^sup>* Y) (na_As na) As''"
        proof (rule list.rel_mono_strong[OF sk])
          fix X Y assume X: "X \<in> set (na_As na)" and n': "okT (norm_term_skip env' nlift X) Y"
          have "(\<lambda>_. propT) \<turnstile> X : propT" using wtpD(2)[of X "\<lambda>_. propT"] wN X by blast
          then show "env_apply env' X \<rightarrow>\<^sub>\<beta>\<^sup>* Y" by (rule norm_term_skip_env_apply[OF n' su[OF X] _ ac'])
        qed
      qed
      then show "list_implies (map (env_apply env') (Bs @ na_As na)) (env_apply env' C) \<rightarrow>\<^sub>\<beta>\<^sup>*
          list_implies Hs C'"
        using eS[OF _ ab] C' by (intro beta_reds_list_implies) simp_all
    next
      fix As'' assume ab: "Pure_Bicompose.above env' smax" and C': "C' = C" and Hs: "Hs = Bs @ As''"
        and nn: "list_all2 (\<lambda>X X'. ok (norm_term env' X) X') (na_As na) As''"
      have "list_all2 (\<lambda>X Y. X \<rightarrow>\<^sub>\<beta>\<^sup>* Y) (map (env_apply env') (Bs @ na_As na)) Hs"
        unfolding Hs list_all2_map1
      proof (rule list_all2_appendI)
        show "list_all2 (\<lambda>X Y. env_apply env' X \<rightarrow>\<^sub>\<beta>\<^sup>* Y) Bs Bs"
          by (rule list.rel_refl_strong) (simp add: eS[OF _ ab])
        show "list_all2 (\<lambda>X Y. env_apply env' X \<rightarrow>\<^sub>\<beta>\<^sup>* Y) (na_As na) As''"
          using nn by (rule list_all2_mono) (rule nt)
      qed
      then show "list_implies (map (env_apply env') (Bs @ na_As na)) (env_apply env' C) \<rightarrow>\<^sub>\<beta>\<^sup>*
          list_implies Hs C'"
        using eS[OF _ ab] C' by (intro beta_reds_list_implies) simp_all
    next
      assume nn: "list_all2 (\<lambda>X X'. ok (norm_term env' X) X') (Bs @ na_As na) Hs"
        and nC: "ok (norm_term env' C) C'"
      have "list_all2 (\<lambda>X Y. X \<rightarrow>\<^sub>\<beta>\<^sup>* Y) (map (env_apply env') (Bs @ na_As na)) Hs"
        unfolding list_all2_map1 using nn by (rule list_all2_mono) (rule nt)
      then show "list_implies (map (env_apply env') (Bs @ na_As na)) (env_apply env' C) \<rightarrow>\<^sub>\<beta>\<^sup>*
          list_implies Hs C'"
        using nt[OF nC] by (rule beta_reds_list_implies)
    qed
    then show ?thesis using tp norm(2) by simp
  qed
  have mt: "match_flg \<Longrightarrow> Pure_Bicompose.above env' smax" using addth_match[OF ad] by (simp add: ctx_sel)
  show thesis
  proof (rule that[of env tus0 tps As0 n "na_oldAs na" tab r2 "na_As na", OF env pb])
    show "extends env (br_env r)" using ext rbr by simp
  next
    fix \<rho> \<sigma> assume "solution \<rho> \<sigma> (br_env r)" "cert_inst \<rho>" "\<forall>(t, u)\<in>set tps. ap \<rho> \<sigma> t \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma> u"
    then show "\<forall>(t, u)\<in>set (tus0 @ rtpairs @ stpairs). ap \<rho> \<sigma> t \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma> u"
      using sol rbr by simp
  next
    show "na_oldAs na = As0 \<and> tab = [] \<or> lifted \<and> na_oldAs na = map (strip_apply (ren_term (tab, r2)) Bi) As0"
      using old by blast
  next
    fix x assume "ren_name tab x \<noteq> x"
    then show "x \<notin> vnames (fst (if lifted then strip_assums2 B Bi else (B, Bi))) \<and>
        (\<forall>(t, u)\<in>set rtpairs. x \<notin> vnames t \<and> x \<notin> vnames u)"
      using ren' by (simp add: BBi_def)
  qed (use As bA nr flat' main mt rbr in simp_all)
qed

end

end

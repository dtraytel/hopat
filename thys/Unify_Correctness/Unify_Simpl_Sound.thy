section \<open>Soundness of \<open>SIMPL\<close>\<close>

theory Unify_Simpl_Sound
  imports Unify_Base_Sound
begin

lemma incr_bv_incr_bv: "0 \<le> m \<Longrightarrow> 0 \<le> n \<Longrightarrow> incr_bv m k (incr_bv n k t) = incr_bv (m + n) k t"
  by (induction n k t arbitrary: m rule: incr_bv.induct) (auto simp: algebra_simps)

context pure_sig
begin

subsection \<open>Rigid-rigid pairs\<close>

abbreviation dzip :: "binders \<Rightarrow> pterm list \<Rightarrow> pterm list \<Rightarrow> dpair list" where
  "dzip bs ss ts \<equiv> map (\<lambda>(s, t). (bs, s, t)) (zip ss ts)"

text \<open>A pair of applications with the same rigid head (after instantiation) is decomposed into
  the pairs of arguments:\<close>

lemma dstep_rigid:
  assumes ext1: "extends env env1" and tenv1: "tenv env1 = tenv env"
    and heads: "\<And>\<rho> env'' e U U'. tsol (tyenv env'') \<rho> \<Longrightarrow> extends env1 env'' \<Longrightarrow>
      e \<turnstile> inst \<rho> h : U \<Longrightarrow> e \<turnstile> inst \<rho> h' : U' \<Longrightarrow> inst \<rho> h = inst \<rho> h'"
    and len: "length ss = length ts"
    and st: "dstep env1 (dzip bs ss ts) env' dps'"
  shows "dstep env [(bs, h \<degree>\<degree> ss, h' \<degree>\<degree> ts)] env' dps'"
proof (rule dstepI)
  show "extends env env'" using extends_trans[OF ext1 dstepD(1)[OF st]] .
  fix \<rho> env'' X assume tsol'': "tsol (tyenv env'') \<rho>" and ext': "extends env' env''" and wte: "wt_env \<rho> env"
    and d: "dtyped \<rho> [(bs, h \<degree>\<degree> ss, h' \<degree>\<degree> ts)]" and vi: "vinv \<rho> env (X \<union> dvars [(bs, h \<degree>\<degree> ss, h' \<degree>\<degree> ts)])"
  from d[unfolded dtyped_simps] obtain e T where bs: "bs_env \<rho> e bs" and tys: "e \<turnstile> inst \<rho> (h \<degree>\<degree> ss) : T"
    and tyt: "e \<turnstile> inst \<rho> (h' \<degree>\<degree> ts) : T" and lbs: "\<not> loose_bvar (h \<degree>\<degree> ss) (ilength bs)"
    and lbt: "\<not> loose_bvar (h' \<degree>\<degree> ts) (ilength bs)"
    by blast
  have ext1': "extends env1 env''" using extends_trans[OF dstepD(1)[OF st] ext'] .
  have dec: "\<exists>Us. e' \<turnstile> inst \<rho> h : Us \<Rrightarrow> T' \<and> e' \<tturnstile> map (inst \<rho>) ss : Us \<and> e' \<tturnstile> map (inst \<rho>) ts : Us \<and>
      inst \<rho> h = inst \<rho> h'"
    if tys: "e' \<turnstile> inst \<rho> (h \<degree>\<degree> ss) : T'" and tyt: "e' \<turnstile> inst \<rho> (h' \<degree>\<degree> ts) : T'" for e' T'
  proof -
    from tys obtain Us where th: "e' \<turnstile> inst \<rho> h : Us \<Rrightarrow> T'" and tss: "e' \<tturnstile> map (inst \<rho>) ss : Us"
      by (auto simp: inst_apps elim: list_app_typeE)
    from tyt obtain Us' where th': "e' \<turnstile> inst \<rho> h' : Us' \<Rrightarrow> T'" and tts: "e' \<tturnstile> map (inst \<rho>) ts : Us'"
      by (auto simp: inst_apps elim: list_app_typeE)
    have hh: "inst \<rho> h = inst \<rho> h'" by (rule heads[OF tsol'' ext1' th th'])
    from typings_nth[OF tss] typings_nth[OF tts] len have lens: "length Us = length Us'" by simp
    from typing_unique[OF th th'[folded hh]] funs_eq[OF lens] have UU: "Us = Us'" by simp
    with th tss tts hh show ?thesis by blast
  qed
  from dec[OF tys tyt] obtain Us where tss: "e \<tturnstile> map (inst \<rho>) ss : Us" and tts: "e \<tturnstile> map (inst \<rho>) ts : Us"
    by blast
  have wte1: "wt_env \<rho> env1" using wte by (simp add: wt_env_tenv[OF tenv1])
  have A: "dtyped \<rho> (dzip bs ss ts)"
    unfolding dtyped_def
  proof (intro ballI)
    fix p assume "p \<in> set (dzip bs ss ts)"
    then obtain i where i: "i < length ss" and p: "p = (bs, ss ! i, ts ! i)" using len by (auto simp: set_zip)
    have "e \<turnstile> inst \<rho> (ss ! i) : Us ! i" "e \<turnstile> inst \<rho> (ts ! i) : Us ! i"
      using typings_nth[OF tss] typings_nth[OF tts] i len by auto
    moreover have "\<not> loose_bvar (ss ! i) (ilength bs)" "\<not> loose_bvar (ts ! i) (ilength bs)"
      using lbs lbt i len by (auto simp: loose_bvar_apps)
    ultimately show "case p of (rb, t, u) \<Rightarrow> (\<exists>e T. bs_env \<rho> e rb \<and> e \<turnstile> inst \<rho> t : T \<and> e \<turnstile> inst \<rho> u : T) \<and>
        \<not> loose_bvar t (ilength rb) \<and> \<not> loose_bvar u (ilength rb)"
      using bs p by auto
  qed
  have sub: "X \<union> dvars (dzip bs ss ts) \<subseteq> X \<union> dvars [(bs, h \<degree>\<degree> ss, h' \<degree>\<degree> ts)]"
    by (auto simp: dvars_def vars_apps dest: set_zip_leftD set_zip_rightD)
  have B: "vinv \<rho> env1 (X \<union> dvars (dzip bs ss ts))"
    using vinv_mono[OF vinv_tenv[OF tenv1 ext1 vi] sub] .
  let ?E = "binds \<rho> env' \<union> dp_eqs \<rho> dps'"
  have r: "wt_env \<rho> env' \<and> dtyped \<rho> dps' \<and> vinv \<rho> env' (X \<union> dvars dps')"
    using dstepD(2)[OF st tsol'' ext' wte1 A B] by blast
  have D: "deqv ?E \<rho> (dzip bs ss ts)" by (rule dstepD(3)[OF st tsol'' ext' wte1 A B])
  have "deqv ?E \<rho> [(bs, h \<degree>\<degree> ss, h' \<degree>\<degree> ts)]"
    unfolding deqv_single
  proof (intro allI impI)
    fix e' T' assume bs': "bs_env \<rho> e' bs" and tys': "e' \<turnstile> inst \<rho> (h \<degree>\<degree> ss) : T'"
      and tyt': "e' \<turnstile> inst \<rho> (h' \<degree>\<degree> ts) : T'"
    from dec[OF tys' tyt'] obtain Vs where th: "e' \<turnstile> inst \<rho> h : Vs \<Rrightarrow> T'"
      and tss': "e' \<tturnstile> map (inst \<rho>) ss : Vs" and tts': "e' \<tturnstile> map (inst \<rho>) ts : Vs" and hh: "inst \<rho> h = inst \<rho> h'"
      by blast
    have "list_all2 (eqv ?E e') (map (inst \<rho>) ss) (map (inst \<rho>) ts)"
    proof (rule list_all2_all_nthI)
      show "length (map (inst \<rho>) ss) = length (map (inst \<rho>) ts)" using len by simp
      fix i assume "i < length (map (inst \<rho>) ss)"
      then have i: "i < length ss" by simp
      have "(bs, ss ! i, ts ! i) \<in> set (dzip bs ss ts)" using i len by (auto simp: set_zip)
      moreover have "e' \<turnstile> inst \<rho> (ss ! i) : Vs ! i" "e' \<turnstile> inst \<rho> (ts ! i) : Vs ! i"
        using typings_nth[OF tss'] typings_nth[OF tts'] i len by auto
      ultimately have "eqv ?E e' (inst \<rho> (ss ! i)) (inst \<rho> (ts ! i))" using D bs' by (fastforce simp: deqv_def)
      then show "eqv ?E e' (map (inst \<rho>) ss ! i) (map (inst \<rho>) ts ! i)" using i len by simp
    qed
    from eqv_apps[OF this eqv_refl[OF th]] tys' hh
    show "eqv ?E e' (inst \<rho> (h \<degree>\<degree> ss)) (inst \<rho> (h' \<degree>\<degree> ts))" by (simp add: inst_apps)
  qed
  with r show "wt_env \<rho> env' \<and> dtyped \<rho> dps' \<and> vinv \<rho> env' (X \<union> dvars dps') \<and>
      deqv (binds \<rho> env' \<union> dp_eqs \<rho> dps') \<rho> [(bs, h \<degree>\<degree> ss, h' \<degree>\<degree> ts)]"
    by blast
qed

text \<open>\<open>simrands\<close> decomposes the applications into their heads and arguments:\<close>

lemma simrands_sound:
  "(\<And>dp env ffs frs env' ffs' frs'. okW (f dp (env, ffs, frs)) (env', ffs', frs') \<Longrightarrow>
      \<exists>a b. ffs' = a @ ffs \<and> frs' = b @ frs \<and> dstep env [dp] env' (a @ b)) \<Longrightarrow>
    okW (simrands f bs u0 s t st) st' \<Longrightarrow>
    \<exists>a b ss ts. s = head_of s \<degree>\<degree> ss \<and> t = head_of t \<degree>\<degree> ts \<and> length ss = length ts \<and>
      fst (snd st') = a @ fst (snd st) \<and> snd (snd st') = b @ snd (snd st) \<and>
      dstep (fst st) (dzip bs ss ts) (fst st') (a @ b)"
proof (induction f bs u0 s t st arbitrary: st' rule: simrands.induct)
  case (1 f bs u0 f1 s1 g1 t1 st)
  from "1.prems"(2) obtain st1 where r1: "okW (simrands f bs u0 f1 g1 st) st1"
    and r2: "okW (f (bs, s1, t1) st1) st'"
    by auto
  from "1.IH"[OF "1.prems"(1) r1] obtain a1 b1 ss ts where
    ss: "f1 = head_of f1 \<degree>\<degree> ss" "g1 = head_of g1 \<degree>\<degree> ts" "length ss = length ts"
    and st1: "fst (snd st1) = a1 @ fst (snd st)" "snd (snd st1) = b1 @ snd (snd st)"
    and d1: "dstep (fst st) (dzip bs ss ts) (fst st1) (a1 @ b1)"
    by blast
  obtain env1 ffs1 frs1 where st1e: "st1 = (env1, ffs1, frs1)" by (cases st1)
  obtain env' ffs' frs' where st'e: "st' = (env', ffs', frs')" by (cases st')
  from "1.prems"(1)[OF r2[unfolded st1e st'e]] obtain a2 b2 where
    a2: "ffs' = a2 @ ffs1" "frs' = b2 @ frs1" and d2: "dstep env1 [(bs, s1, t1)] env' (a2 @ b2)"
    by blast
  have d2': "dstep (fst st1) [(bs, s1, t1)] (fst st') (a2 @ b2)" using d2 st1e st'e by simp
  have "dstep (fst st) (dzip bs (ss @ [s1]) (ts @ [t1])) (fst st') ((a2 @ a1) @ (b2 @ b1))"
    by (rule dstep_seq[OF d1 d2']) (use ss(3) in auto)
  moreover have "f1 $ s1 = head_of (f1 $ s1) \<degree>\<degree> (ss @ [s1])" "g1 $ t1 = head_of (g1 $ t1) \<degree>\<degree> (ts @ [t1])"
    using ss(1,2) by (metis foldl_Cons foldl_Nil foldl_append head_of.simps(1))+
  ultimately have "f1 $ s1 = head_of (f1 $ s1) \<degree>\<degree> (ss @ [s1]) \<and> g1 $ t1 = head_of (g1 $ t1) \<degree>\<degree> (ts @ [t1]) \<and>
      length (ss @ [s1]) = length (ts @ [t1]) \<and>
      fst (snd st') = (a2 @ a1) @ fst (snd st) \<and> snd (snd st') = (b2 @ b1) @ snd (snd st) \<and>
      dstep (fst st) (dzip bs (ss @ [s1]) (ts @ [t1])) (fst st') ((a2 @ a1) @ (b2 @ b1))"
    using ss(3) st1 a2 st1e st'e by auto
  then show ?case by blast
qed (auto simp: dstep_refl)

subsection \<open>Simplification of one pair\<close>

text \<open>The body of \<^const>\<open>SIMPL0\<close> after head normalization, parametric in the recursive call:\<close>

definition SIMPL0_rest :: "(algebra \<Rightarrow> dpair \<Rightarrow> sstate \<Rightarrow> sstate W) \<Rightarrow> algebra \<Rightarrow> binders \<Rightarrow> pterm \<Rightarrow> pterm \<Rightarrow>
    env \<Rightarrow> dpair list \<Rightarrow> dpair list \<Rightarrow> sstate W" where
  "SIMPL0_rest simpl al rbinder t u env ffs frs =
    (case (head_of t, head_of u) of
      (Var _ T, Var _ U) \<Rightarrow> do {
        T' \<leftarrow> liftM (body_type env T);
        U' \<leftarrow> liftM (body_type env U);
        env \<leftarrow> cunify_types al T' U' env;
        returnW (env, (rbinder, t, u) # ffs, frs)}
    | (Var _ _, _) \<Rightarrow>
        handleW (do {env' \<leftarrow> assignment al rbinder t u env; returnW (env', ffs, frs)})
          (\<lambda>e. case e of ASSIGN \<Rightarrow> returnW (env, ffs, (rbinder, t, u) # frs) | _ \<Rightarrow> raiseW e)
    | (_, Var _ _) \<Rightarrow>
        handleW (do {env' \<leftarrow> assignment al rbinder u t env; returnW (env', ffs, frs)})
          (\<lambda>e. case e of
            ASSIGN \<Rightarrow> returnW (env, ffs, (rbinder, u, t) # frs)
          | _ \<Rightarrow> raiseW e)
    | (Const a T, Const b U) \<Rightarrow>
        if a = b then do {
          env' \<leftarrow> cunify_types al T U env;
          simrands (simpl al) rbinder u t u (env', ffs, frs)}
        else raiseW CANTUNIFY
    | (Bound i, Bound j) \<Rightarrow>
        if i = j then simrands (simpl al) rbinder u t u (env, ffs, frs)
        else raiseW CANTUNIFY
    | (Free a T, Free b U) \<Rightarrow>
        if a = b then do {
          env' \<leftarrow> cunify_types al T U env;
          simrands (simpl al) rbinder u t u (env', ffs, frs)}
        else raiseW CANTUNIFY
    | _ \<Rightarrow> raiseW CANTUNIFY)"

lemma assign_handle_sound:
  assumes "okW (handleW (do {env' \<leftarrow> assignment alg' bs t u env; returnW (env', ffs, frs)})
    (\<lambda>e. case e of ASSIGN \<Rightarrow> returnW (env, ffs, (bs, t, u) # frs) | _ \<Rightarrow> raiseW e)) (env', ffs', frs')"
  shows "ffs' = ffs \<and> (frs' = frs \<and> dstep env [(bs, t, u)] env' [] \<or> frs' = (bs, t, u) # frs \<and> env' = env)"
proof -
  from assms[unfolded okW_handleW] consider
    (ok) "okW (do {env' \<leftarrow> assignment alg' bs t u env; returnW (env', ffs, frs)}) (env', ffs', frs')"
  | (err) e where "okW (case e of ASSIGN \<Rightarrow> returnW (env, ffs, (bs, t, u) # frs) | _ \<Rightarrow> raiseW e) (env', ffs', frs')"
    by blast
  then show ?thesis
  proof cases
    case ok
    then obtain env1 where a: "okW (assignment alg' bs t u env) env1" and e: "env' = env1" "ffs' = ffs" "frs' = frs"
      by auto
    with assignment_sound[OF a] show ?thesis by simp
  next
    case err
    then show ?thesis by (cases e) simp_all
  qed
qed

lemma SIMPL0_rest_sound:
  assumes IH: "\<And>dp env ffs frs env' ffs' frs'. okW (simpl alg' dp (env, ffs, frs)) (env', ffs', frs') \<Longrightarrow>
      \<exists>a b. ffs' = a @ ffs \<and> frs' = b @ frs \<and> dstep env [dp] env' (a @ b)"
    and r: "okW (SIMPL0_rest simpl alg' bs t u env ffs frs) (env', ffs', frs')"
  shows "\<exists>a b. ffs' = a @ ffs \<and> frs' = b @ frs \<and> dstep env [(bs, t, u)] env' (a @ b)"
proof -
  have FR: ?thesis if ht: "head_of t = Var x T" and hu: "\<not> is_Var (head_of u)" for x T
  proof -
    have "okW (handleW (do {env' \<leftarrow> assignment alg' bs t u env; returnW (env', ffs, frs)})
      (\<lambda>e. case e of ASSIGN \<Rightarrow> returnW (env, ffs, (bs, t, u) # frs) | _ \<Rightarrow> raiseW e)) (env', ffs', frs')"
      using r ht hu by (cases "head_of u") (simp_all add: SIMPL0_rest_def)
    from assign_handle_sound[OF this] show ?thesis
    proof (elim conjE disjE)
      assume "ffs' = ffs" "frs' = frs" "dstep env [(bs, t, u)] env' []"
      then have "ffs' = [] @ ffs \<and> frs' = [] @ frs \<and> dstep env [(bs, t, u)] env' ([] @ [])" by simp
      then show ?thesis by blast
    next
      assume "ffs' = ffs" "frs' = (bs, t, u) # frs" "env' = env"
      then show ?thesis using dstep_refl[of env "[(bs, t, u)]"] by simp
    qed
  qed
  have RF: ?thesis if hu: "head_of u = Var x U" and ht: "\<not> is_Var (head_of t)" for x U
  proof -
    have "okW (handleW (do {env' \<leftarrow> assignment alg' bs u t env; returnW (env', ffs, frs)})
      (\<lambda>e. case e of ASSIGN \<Rightarrow> returnW (env, ffs, (bs, u, t) # frs) | _ \<Rightarrow> raiseW e)) (env', ffs', frs')"
      using r ht hu by (cases "head_of t") (simp_all add: SIMPL0_rest_def)
    from assign_handle_sound[OF this] show ?thesis
    proof (elim conjE disjE)
      assume "ffs' = ffs" "frs' = frs" "dstep env [(bs, u, t)] env' []"
      then have "ffs' = [] @ ffs \<and> frs' = [] @ frs \<and> dstep env [(bs, t, u)] env' ([] @ [])"
        using dstep_swap_in[of env bs u t "[]" env' "[]"] by simp
      then show ?thesis by blast
    next
      assume "ffs' = ffs" "frs' = (bs, u, t) # frs" "env' = env"
      then show ?thesis using dstep_swap_out[OF dstep_refl[of env "[(bs, t, u)]"]] by simp
    qed
  qed
  text \<open>Rigid heads:\<close>
  have rigid: ?thesis
    if sr: "okW (simrands (simpl alg') bs u t u (env1, ffs, frs)) (env', ffs', frs')"
      and ext1: "extends env env1" and tenv1: "tenv env1 = tenv env"
      and heads: "\<And>\<rho> env'' e V V'. tsol (tyenv env'') \<rho> \<Longrightarrow> extends env1 env'' \<Longrightarrow>
        e \<turnstile> inst \<rho> (head_of t) : V \<Longrightarrow> e \<turnstile> inst \<rho> (head_of u) : V' \<Longrightarrow> inst \<rho> (head_of t) = inst \<rho> (head_of u)"
    for env1
  proof -
    from simrands_sound[OF IH sr] obtain a b ss ts where
      st: "t = head_of t \<degree>\<degree> ss" "u = head_of u \<degree>\<degree> ts" "length ss = length ts"
      and ab: "ffs' = a @ ffs" "frs' = b @ frs" and d: "dstep env1 (dzip bs ss ts) env' (a @ b)"
      by auto
    have "dstep env [(bs, head_of t \<degree>\<degree> ss, head_of u \<degree>\<degree> ts)] env' (a @ b)"
      by (rule dstep_rigid[OF ext1 tenv1 heads st(3) d])
    with st ab show ?thesis by auto
  qed
  have CF: ?thesis if ht: "head_of t = c T" and hu: "head_of u = c U" and c: "c = Const a \<or> c = Free a"
    and cu: "okW (cunify_types alg' T U env) env1"
    and sr: "okW (simrands (simpl alg') bs u t u (env1, ffs, frs)) (env', ffs', frs')" for c a T U env1
  proof (rule rigid[OF sr cunify_types_sound(2,1)[OF cu]])
    fix \<rho> env'' e V V' assume "tsol (tyenv env'') \<rho>" "extends env1 env''"
      "e \<turnstile> inst \<rho> (head_of t) : V" "e \<turnstile> inst \<rho> (head_of u) : V'"
    with heads_types[OF cu[unfolded cunify_types_ok] _ _ _ _ c] ht hu
    show "inst \<rho> (head_of t) = inst \<rho> (head_of u)" by simp
  qed
  show ?thesis
  proof (cases "head_of t")
    case tV: (Var x T)
    show ?thesis
    proof (cases "is_Var (head_of u)")
      case True
      then obtain y U where uV: "head_of u = Var y U" by (cases "head_of u") auto
      have "\<exists>T' U' env1. okW (cunify_types alg' T' U' env) env1 \<and> env' = env1 \<and> ffs' = (bs, t, u) # ffs \<and> frs' = frs"
        using r tV uV by (simp add: SIMPL0_rest_def) blast
      then obtain T' U' env1 where cu: "okW (cunify_types alg' T' U' env) env1"
        and st': "env' = env1" "ffs' = (bs, t, u) # ffs" "frs' = frs"
        by blast
      then show ?thesis using cunify_types_dstep[OF cu, of "[(bs, t, u)]"] by simp
    qed (rule FR[OF tV])
  next
    case tC: (Const a T)
    show ?thesis
    proof (cases "head_of u")
      case (Const b U)
      from r tC Const obtain env1 where ab: "a = b" and cu: "okW (cunify_types alg' T U env) env1"
        and sr: "okW (simrands (simpl alg') bs u t u (env1, ffs, frs)) (env', ffs', frs')"
        by (auto simp: SIMPL0_rest_def split: if_splits)
      show ?thesis by (rule CF[OF tC Const[folded ab] disjI1[OF refl] cu sr])
    next
      case (Var y U)
      with tC show ?thesis by (intro RF) simp_all
    qed (use r tC in \<open>simp_all add: SIMPL0_rest_def\<close>)
  next
    case tF: (Free a T)
    show ?thesis
    proof (cases "head_of u")
      case (Free b U)
      from r tF Free obtain env1 where ab: "a = b" and cu: "okW (cunify_types alg' T U env) env1"
        and sr: "okW (simrands (simpl alg') bs u t u (env1, ffs, frs)) (env', ffs', frs')"
        by (auto simp: SIMPL0_rest_def split: if_splits)
      show ?thesis by (rule CF[OF tF Free[folded ab] disjI2[OF refl] cu sr])
    next
      case (Var y U)
      with tF show ?thesis by (intro RF) simp_all
    qed (use r tF in \<open>simp_all add: SIMPL0_rest_def\<close>)
  next
    case tB: (Bound i)
    show ?thesis
    proof (cases "head_of u")
      case (Bound j)
      from r tB Bound have ij: "i = j"
        and sr: "okW (simrands (simpl alg') bs u t u (env, ffs, frs)) (env', ffs', frs')"
        by (auto simp: SIMPL0_rest_def split: if_splits)
      show ?thesis by (rule rigid[OF sr extends_refl refl]) (simp add: tB Bound ij)
    next
      case (Var y U)
      with tB show ?thesis by (intro RF) simp_all
    qed (use r tB in \<open>simp_all add: SIMPL0_rest_def\<close>)
  next
    case tA: (Abs a T s)
    show ?thesis
    proof (cases "head_of u")
      case (Var y U)
      with tA show ?thesis by (intro RF) simp_all
    qed (use r tA in \<open>simp_all add: SIMPL0_rest_def\<close>)
  next
    case tA: (App f s)
    show ?thesis
    proof (cases "head_of u")
      case (Var y U)
      with tA show ?thesis by (intro RF) simp_all
    qed (use r tA in \<open>simp_all add: SIMPL0_rest_def\<close>)
  qed
qed

lemma okW_of_Some: "m = Some r \<Longrightarrow> snd r = Ok x \<Longrightarrow> okW m x"
  by (cases r) simp

lemma SIMPL0_sound_aux:
  assumes "SIMPL0 alg' dp st = Some r"
  shows "snd r = Ok (env', ffs', frs') \<Longrightarrow> st = (env, ffs, frs) \<Longrightarrow>
    \<exists>a b. ffs' = a @ ffs \<and> frs' = b @ frs \<and> dstep env [dp] env' (a @ b)"
  using assms
proof (induction alg' dp st r arbitrary: env ffs frs env' ffs' frs' rule: SIMPL0.raw_induct[rotated, consumes 1])
  case (1 simpl alg' dp0 st r)
  have IH: "\<exists>a b. ffs2 = a @ ffs1 \<and> frs2 = b @ frs1 \<and> dstep env1 [dp] env2 (a @ b)"
    if "okW (simpl alg' dp (env1, ffs1, frs1)) (env2, ffs2, frs2)" for dp env1 ffs1 frs1 env2 ffs2 frs2
  proof -
    from that obtain evs where "simpl alg' dp (env1, ffs1, frs1) = Some (evs, Ok (env2, ffs2, frs2))" by blast
    from "1.IH"[OF this] show ?thesis by simp
  qed
  have "\<exists>bs t u env1. okW (head_norm_dpair alg' env dp0) ((bs, t, u), env1) \<and>
      okW (SIMPL0_rest simpl alg' bs t u env1 ffs frs) (env', ffs', frs')"
    using okW_of_Some[OF "1.hyps" "1.prems"(1)] "1.prems"(2) by (auto simp: SIMPL0_rest_def split: prod.splits)
  then obtain bs t u env1 where hn: "okW (head_norm_dpair alg' env dp0) ((bs, t, u), env1)"
    and rest: "okW (SIMPL0_rest simpl alg' bs t u env1 ffs frs) (env', ffs', frs')"
    by blast
  from SIMPL0_rest_sound[OF IH rest] obtain a b where
    ab: "ffs' = a @ ffs" "frs' = b @ frs" and d: "dstep env1 [(bs, t, u)] env' (a @ b)"
    by blast
  from dstep_trans[OF head_norm_dpair_sound(2)[OF hn] d] ab show ?case by blast
qed

theorem SIMPL0_sound:
  "okW (SIMPL0 alg' dp (env, ffs, frs)) (env', ffs', frs') \<Longrightarrow>
    \<exists>a b. ffs' = a @ ffs \<and> frs' = b @ frs \<and> dstep env [dp] env' (a @ b)"
  using SIMPL0_sound_aux by fastforce


subsection \<open>Simplification of all pairs\<close>

lemma foldrW_SIMPL0_sound:
  "okW (foldrW (SIMPL0 alg') dps (env, ffs, frs)) (env', ffs', frs') \<Longrightarrow>
    \<exists>a b. ffs' = a @ ffs \<and> frs' = b @ frs \<and> dstep env dps env' (a @ b)"
proof (induction dps arbitrary: env' ffs' frs')
  case Nil
  then show ?case using dstep_refl[of env "[]"] by simp
next
  case (Cons dp dps)
  from Cons.prems obtain env1 ffs1 frs1 where f: "okW (foldrW (SIMPL0 alg') dps (env, ffs, frs)) (env1, ffs1, frs1)"
    and s: "okW (SIMPL0 alg' dp (env1, ffs1, frs1)) (env', ffs', frs')"
    by auto
  from Cons.IH[OF f] obtain a1 b1 where ab1: "ffs1 = a1 @ ffs" "frs1 = b1 @ frs"
    and d1: "dstep env dps env1 (a1 @ b1)" by blast
  from SIMPL0_sound[OF s] obtain a2 b2 where ab2: "ffs' = a2 @ ffs1" "frs' = b2 @ frs1"
    and d2: "dstep env1 [dp] env' (a2 @ b2)" by blast
  have "dstep env (dp # dps) env' ((a2 @ a1) @ (b2 @ b1))" by (rule dstep_seq[OF d1 d2 refl])
  with ab1 ab2 show ?case by auto
qed

lemma SIMPL_sound_aux:
  assumes "SIMPL alg' env dps = Some r"
  shows "snd r = Ok (env', ffs, frs) \<Longrightarrow> dstep env dps env' (frs @ ffs)"
  using assms
proof (induction alg' env dps r arbitrary: env' ffs frs rule: SIMPL.raw_induct[rotated, consumes 1])
  case (1 simpl alg' env dps r)
  have IH: "dstep env1 dps1 env2 (frs2 @ ffs2)"
    if "okW (simpl alg' env1 dps1) (env2, ffs2, frs2)" for env1 dps1 env2 ffs2 frs2
  proof -
    from that obtain evs where "simpl alg' env1 dps1 = Some (evs, Ok (env2, ffs2, frs2))" by blast
    from "1.IH"[OF this] show ?thesis by simp
  qed
  have "\<exists>env1 ffs1 frs1. okW (foldrW (SIMPL0 alg') dps (env, [], [])) (env1, ffs1, frs1) \<and>
      (okW (simpl alg' env1 (frs1 @ ffs1)) (env', ffs, frs) \<or> (env', ffs, frs) = (env1, ffs1, frs1))"
    using okW_of_Some[OF "1.hyps" "1.prems"(1)] by (auto simp: Let_def split: prod.splits if_splits)
  then obtain env1 ffs1 frs1 where f: "okW (foldrW (SIMPL0 alg') dps (env, [], [])) (env1, ffs1, frs1)"
    and rest: "okW (simpl alg' env1 (frs1 @ ffs1)) (env', ffs, frs) \<or> (env', ffs, frs) = (env1, ffs1, frs1)"
    by blast
  from foldrW_SIMPL0_sound[OF f] have "dstep env dps env1 (ffs1 @ frs1)" by auto
  then have d: "dstep env dps env1 (frs1 @ ffs1)" by (rule dstep_set) auto
  from rest show ?case
  proof
    assume "okW (simpl alg' env1 (frs1 @ ffs1)) (env', ffs, frs)"
    from dstep_trans[OF d IH[OF this]] show ?thesis .
  qed (use d in simp)
qed

theorem SIMPL_sound: "okW (SIMPL alg' env dps) (env', ffs, frs) \<Longrightarrow> dstep env dps env' (frs @ ffs)"
  using SIMPL_sound_aux by fastforce

subsection \<open>Abstractions over types and their application\<close>

lemma types_abs_abs_list: "types_abs Ts u = abs_list (map (\<lambda>T. (STR '''', T)) Ts) u"
  by (induction Ts) simp_all

lemma types_abs_append: "types_abs (Ts @ Us) u = types_abs Ts (types_abs Us u)"
  by (induction Ts) simp_all

lemma inst_types_abs: "inst \<rho> (types_abs Ts u) = types_abs (map (tsubst \<rho>) Ts) (inst \<rho> u)"
  by (induction Ts) simp_all

lemma vsubst_types_abs: "vsubst \<sigma> (types_abs Ts u) = types_abs Ts (vsubst \<sigma> u)"
  by (induction Ts) simp_all

lemma ap_types_abs: "ap \<rho> \<sigma> (types_abs Ts u) = types_abs (map (tsubst \<rho>) Ts) (ap \<rho> \<sigma> u)"
  by (simp add: ap_def inst_types_abs vsubst_types_abs)

lemma vars_types_abs [simp]: "vars (types_abs Ts u) = vars u"
  by (induction Ts) simp_all

lemma loose_bvar_types_abs: "loose_bvar (types_abs Ts u) k \<longleftrightarrow> loose_bvar u (k + ilength Ts)"
  by (simp add: types_abs_abs_list loose_bvar_abs_list)

lemma closed_types_abs: "\<not> loose_bvar u (ilength Ts) \<Longrightarrow> closed (types_abs Ts u)"
  by (simp add: closed_def loose_bvar_types_abs)

lemma pushes_append: "pushes e (Ts @ Us) = pushes (pushes e Ts) Us"
  by (induction Ts arbitrary: e) simp_all

lemma typing_types_abs:
  "pushes e Ts \<turnstile> u : U \<Longrightarrow> \<forall>T\<in>set Ts. cert_typ alg ar T \<Longrightarrow> e \<turnstile> types_abs Ts u : Ts \<Rrightarrow> U"
  using typing_abs_list[of e "map (\<lambda>T. (STR '''', T)) Ts" u U]
  by (simp add: types_abs_abs_list comp_def)

lemma subst_abs_list:
  "(abs_list bs t)[s/k] = abs_list bs (t[incr_bv (ilength bs) 0 s/k + ilength bs])"
proof (induction bs arbitrary: s k)
  case (Cons b bs)
  obtain x T where b: "b = (x, T)" by (cases b)
  have "incr_bv (ilength bs) 0 (lift s 0) = incr_bv (ilength bs + 1) 0 s"
    by (simp add: incr_bv_incr_bv)
  with Cons.IH[of "lift s 0" "k + 1"] b show ?case by (simp add: algebra_simps)
qed simp

end

end

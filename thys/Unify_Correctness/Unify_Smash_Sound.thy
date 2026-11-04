section \<open>Soundness of Smashing Flex-Flex Pairs\<close>

theory Unify_Smash_Sound
  imports Unify_Sound
begin

context pure_sig
begin

text \<open>
  \<^const>\<open>smash_flexflex1\<close> binds the heads \<open>?v :: Ts \<Rrightarrow> B\<close> and \<open>?w :: Us \<Rrightarrow> B'\<close> of a flex-flex
  pair to the constant functions \<open>\<lambda>Ts. ?x\<close> and \<open>\<lambda>Us. ?x\<close> over one new variable \<open>?x :: B\<close>,
  where \<open>B\<close> is the body type of \<open>?v\<close> modulo the type environment. This is sound only if the
  body types agree, \<open>B = B'\<close>, and both sides take at most as many arguments as their heads have
  binder types, under every solution \<open>\<rho>\<close> of the type environment; both follow from the typing of
  the pair at the most general solution \<^const>\<open>tsol0\<close>. A typing at a single solution does not
  suffice: \<open>?v :: ?'a\<close> and \<open>?w :: Z \<Rightarrow> ?'b\<close> have the same type at \<open>?'a := Z \<Rightarrow> Y\<close>, \<open>?'b := Y\<close>,
  but \<open>\<lambda>z. ?x\<close> with \<open>?x :: ?'a\<close> is not of the type of \<open>?w\<close> there. Hence the pairs are required
  to be well-typed at all certified solutions of the type environment (\<open>gtyped\<close>); the most
  general solution is certified if the type environment is well-formed.
\<close>

definition gtyped :: "env \<Rightarrow> dpair list \<Rightarrow> bool" where
  "gtyped env dps \<longleftrightarrow>
    (\<forall>\<rho>. tsol (tyenv env) \<rho> \<longrightarrow> cert_inst \<rho> \<longrightarrow> wt_env \<rho> env \<and> dtyped \<rho> dps \<and> vinv \<rho> env (dvars dps))"

lemma gtyped_dstep:
  assumes "dstep env dps env' dps'" "gtyped env dps"
  shows "gtyped env' dps'"
  unfolding gtyped_def
proof (intro allI impI)
  fix \<rho> assume t: "tsol (tyenv env') \<rho>" and c: "cert_inst \<rho>"
  have "tsol (tyenv env) \<rho>" by (rule extends_tsol[OF t dstepD(1)[OF assms(1)]])
  with assms(2) c have "wt_env \<rho> env" "dtyped \<rho> dps" "vinv \<rho> env ({} \<union> dvars dps)"
    unfolding gtyped_def by auto
  from dstepD(2)[OF assms(1) t extends_refl this] show "wt_env \<rho> env' \<and> dtyped \<rho> dps' \<and> vinv \<rho> env' (dvars dps')"
    by simp
qed

subsection \<open>The most general solution\<close>

lemma tsol_tsol0: "tacyc \<theta> \<Longrightarrow> tcons_env \<theta> \<Longrightarrow> tsol \<theta> (tsol0 \<theta>)"
  unfolding tsol_def using tsubst_tsol0 tcons_envD by (simp add: tsol0_def)

lemma tsubst_tsol0_sol:
  assumes ac: "tacyc \<theta>" and tc: "tcons_env \<theta>" and sol: "tsol \<theta> \<rho>"
  shows "tsubst \<rho> (tsubst (tsol0 \<theta>) T) = tsubst \<rho> T"
proof -
  have "tsubst \<rho> (tsol0 \<theta> v S) = \<rho> v S" for v S
  proof (cases "vt_lookup \<theta> v")
    case (Some b)
    obtain S' U where b: "b = (S', U)" by force
    show ?thesis
    proof (cases "S = S'")
      case True
      have "tsubst \<rho> (tnorm \<theta> U) = tsubst \<rho> U"
        by (rule tsubst_tnorm[OF ac tc sol tcons_envD[OF tc Some[unfolded b]]])
      with Some b True tsolD[OF sol, of v S U] show ?thesis by (simp add: tsol0_def)
    qed (use Some b in \<open>simp add: tsol0_def\<close>)
  qed (simp add: tsol0_def)
  then show ?thesis by (simp add: tsubst_tsubst)
qed

subsection \<open>Function types\<close>

abbreviation nonfun :: "ptyp \<Rightarrow> bool" where
  "nonfun R \<equiv> \<not> (\<exists>A C. R = A \<rightarrow>\<^sub>T C)"

lemma funs_nonfun_eq: "nonfun R \<Longrightarrow> nonfun R' \<Longrightarrow> Ps \<Rrightarrow> R = Qs \<Rrightarrow> R' \<Longrightarrow> Ps = Qs \<and> R = R'"
proof (induction Ps arbitrary: Qs)
  case Nil
  then show ?case by (cases Qs) auto
next
  case (Cons P Ps)
  then show ?case by (cases Qs) auto
qed

lemma funs_nonfun_le: "nonfun R \<Longrightarrow> As \<Rrightarrow> Y = Ps \<Rrightarrow> R \<Longrightarrow> length As \<le> length Ps"
proof (induction As arbitrary: Ps)
  case (Cons A As)
  then show ?case by (cases Ps) auto
qed simp

lemma funs_drop: "length As \<le> length Ps \<Longrightarrow> As \<Rrightarrow> Y = Ps \<Rrightarrow> R \<Longrightarrow> Y = drop (length As) Ps \<Rrightarrow> R"
proof (induction As arbitrary: Ps)
  case (Cons A As)
  then show ?case by (cases Ps) auto
qed simp

lemma funs_len_eq: "length Ps = length Qs \<Longrightarrow> Ps \<Rrightarrow> R = Qs \<Rrightarrow> R' \<Longrightarrow> Ps = Qs"
proof (induction Ps arbitrary: Qs)
  case (Cons P Ps)
  then show ?case by (cases Qs) auto
qed simp

subsection \<open>Body types\<close>

lemma body_type_nonfun:
  assumes "body_type env T = Some r"
  shows "r = Ok B \<Longrightarrow> nonfun B"
  using assms
proof (induction env T r arbitrary: B rule: body_type.raw_induct[rotated, consumes 1])
  case (1 bt env T r)
  note h = "1.hyps"[unfolded "1.prems"(1)]
  show ?case
  proof (cases T)
    case (Type a Ts)
    show ?thesis
    proof (cases "a = STR ''fun'' \<and> (\<exists>T1 U. Ts = [T1, U])")
      case True
      then obtain T1 U where "Ts = [T1, U]" by auto
      with h Type True have "ok (bt env U) B" by simp
      from "1.IH"[OF this refl] show ?thesis .
    next
      case False
      with h Type have "B = T" by (auto split: list.splits if_splits)
      with Type False show ?thesis by auto
    qed
  next
    case (TVar v' S')
    from h TVar obtain lr where lr: "ok (type_lookup (tyenv env) v' S') lr"
      and rest: "ok (case lr of None \<Rightarrow> return T | Some T' \<Rightarrow> bt env T') B" by auto
    show ?thesis
    proof (cases lr)
      case None
      with rest have "B = T" by simp
      with TVar show ?thesis by simp
    next
      case (Some T')
      with rest have "ok (bt env T') B" by simp
      from "1.IH"[OF this refl] show ?thesis .
    qed
  next
    case (TFree a S)
    with h have "B = T" by simp
    with TFree show ?thesis by simp
  qed
qed

lemma body_type_tyenv:
  assumes "body_type env T = Some r"
  shows "tyenv env' = tyenv env \<Longrightarrow> body_type env' T = Some r"
  using assms
proof (induction env T r rule: body_type.raw_induct[rotated, consumes 1])
  case (1 bt env T r)
  note h = "1.hyps"
  show ?case
  proof (cases T)
    case (Type a Ts)
    show ?thesis
    proof (cases "a = STR ''fun'' \<and> (\<exists>T1 U. Ts = [T1, U])")
      case True
      then obtain T1 U where Ts: "Ts = [T1, U]" and a: "a = STR ''fun''" by auto
      with h Type have "bt env U = Some r" by simp
      from "1.IH"[OF this "1.prems"] Type Ts a show ?thesis by (subst body_type.simps) simp
    next
      case False
      with h Type show ?thesis by (subst body_type.simps) (auto split: list.splits if_splits)
    qed
  next
    case (TVar v' S')
    show ?thesis
    proof (cases "type_lookup (tyenv env) v' S'")
      case None
      with h TVar show ?thesis by (simp add: bindM_def)
    next
      case (Some lr)
      show ?thesis
      proof (cases lr)
        case (Err e)
        with h TVar Some "1.prems" show ?thesis by (subst body_type.simps) (simp add: bindM_def)
      next
        case (Ok lr')
        show ?thesis
        proof (cases lr')
          case None
          with h TVar Some Ok "1.prems" show ?thesis by (subst body_type.simps) (simp add: bindM_def)
        next
          case (Some T')
          with h TVar \<open>type_lookup (tyenv env) v' S' = Some lr\<close> Ok have "bt env T' = Some r"
            by (simp add: bindM_def)
          from "1.IH"[OF this "1.prems"] TVar \<open>type_lookup (tyenv env) v' S' = Some lr\<close> Ok Some "1.prems"
          show ?thesis by (subst body_type.simps) (simp add: bindM_def)
        qed
      qed
    qed
  next
    case (TFree a S)
    with h show ?thesis by (subst body_type.simps) simp
  qed
qed

lemma binder_types_body_type:
  assumes "binder_types env T = Some r"
  shows "r = Ok Ts \<Longrightarrow> \<exists>B. ok (body_type env T) B"
  using assms
proof (induction env T r arbitrary: Ts rule: binder_types.raw_induct[rotated, consumes 1])
  case (1 bt env T r)
  note h = "1.hyps"[unfolded "1.prems"(1)]
  show ?case
  proof (cases T)
    case (Type a Us)
    show ?thesis
    proof (cases "a = STR ''fun'' \<and> (\<exists>T1 U. Us = [T1, U])")
      case True
      then obtain T1 U where Us: "Us = [T1, U]" and a: "a = STR ''fun''" by auto
      from h Type Us a obtain Ts' where "ok (bt env U) Ts'" by auto
      from "1.IH"[OF this refl] Type Us a show ?thesis by (subst body_type.simps) simp
    next
      case False
      with Type show ?thesis by (subst body_type.simps) (auto split: list.splits)
    qed
  next
    case (TVar v S)
    from h TVar obtain lr where lr: "ok (type_lookup (tyenv env) v S) lr"
      and rest: "ok (case lr of None \<Rightarrow> return [] | Some T' \<Rightarrow> bt env T') Ts"
      by auto
    show ?thesis
    proof (cases lr)
      case None
      with lr TVar show ?thesis by (subst body_type.simps) (simp add: bindM_def)
    next
      case (Some T')
      with rest have "ok (bt env T') Ts" by simp
      from "1.IH"[OF this refl] lr Some TVar show ?thesis
        by (subst body_type.simps) (simp add: bindM_def)
    qed
  next
    case (TFree a S)
    then show ?thesis by (subst body_type.simps) simp
  qed
qed

lemma body_type_tsol0:
  assumes "ok (body_type env T) B"
  shows "nonfun (tsubst (tsol0 (tyenv env)) B)"
proof (cases B)
  case (TVar v S)
  from body_type_TVar[OF assms refl TVar] TVar show ?thesis by (simp add: tsol0_def)
next
  case (Type a Ts)
  from body_type_nonfun[OF assms refl] Type show ?thesis by auto
qed simp

subsection \<open>Flexible terms\<close>

lemma head_Var_apps:
  assumes "head_of t = Var v T"
  shows "t = Var v T \<degree>\<degree> snd (strip_comb t)"
proof -
  have "strip_comb t = (Var v T, snd (strip_comb t))" using fst_strip_comb[of t] assms by (metis prod.collapse)
  then show ?thesis by (rule strip_comb_apps)
qed

lemma flex_decomp: "head_of (strip_abs_body s) = Var v T \<Longrightarrow> \<exists>bs ts. s = abs_list bs (Var v T \<degree>\<degree> ts)"
proof (induction s)
  case (Abs a A b)
  then obtain bs ts where "b = abs_list bs (Var v T \<degree>\<degree> ts)" by auto
  then have "Abs a A b = abs_list ((a, A) # bs) (Var v T \<degree>\<degree> ts)" by (simp add: abs_list_def)
  then show ?case by blast
next
  case (App f u)
  then have "f $ u = abs_list [] (Var v T \<degree>\<degree> snd (strip_comb (f $ u)))"
    using head_Var_apps[of "f $ u"] by (simp add: abs_list_def)
  then show ?case by blast
qed (auto simp: abs_list_def intro: exI[of _ "[]"])

lemma typing_abs_list_replace:
  "e \<turnstile> abs_list bs s : map snd bs \<Rrightarrow> V \<Longrightarrow> pushes e (map snd bs) \<turnstile> s' : V \<Longrightarrow> e \<turnstile> abs_list bs s' : map snd bs \<Rrightarrow> V"
proof (induction bs arbitrary: e)
  case (Cons b bs)
  obtain x T where b: "b = (x, T)" by force
  from Cons.prems(1) b have "cert_typ alg ar T" "e\<langle>0:T\<rangle> \<turnstile> abs_list bs s : map snd bs \<Rrightarrow> V"
    by (auto simp: abs_list_def)
  with Cons.IH[of "e\<langle>0:T\<rangle>"] Cons.prems(2) b show ?case by (auto simp: abs_list_def)
qed (simp add: abs_list_def)

lemma conv_abs_list:
  "wt (abs_list bs s) \<Longrightarrow> wt (abs_list bs t) \<Longrightarrow> s \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> t \<Longrightarrow> abs_list bs s \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> abs_list bs t"
proof (induction bs)
  case (Cons b bs)
  obtain x T where b: "b = (x, T)" by force
  from Cons.prems b have "wt (abs_list bs s)" "wt (abs_list bs t)" by (auto simp: abs_list_def dest: wt_AbsD)
  from conv_Abs[OF _ _ Cons.IH[OF this Cons.prems(3)]] Cons.prems b show ?case by (simp add: abs_list_def)
qed (simp add: abs_list_def)

lemma flex_typing:
  assumes "e \<turnstile> inst \<rho> (abs_list bs (Var v T \<degree>\<degree> ts)) : X"
  obtains As V where "X = map (\<lambda>(x, T). tsubst \<rho> T) bs \<Rrightarrow> V" "tsubst \<rho> T = As \<Rrightarrow> V" "length As = length ts"
    "cert_typ alg ar (tsubst \<rho> T)"
proof -
  let ?bs = "map (\<lambda>(x, T). (x, tsubst \<rho> T)) bs"
  have ms: "map snd ?bs = map (\<lambda>(x, T). tsubst \<rho> T) bs" by (auto simp: split_def)
  from assms obtain V where X: "X = map snd ?bs \<Rrightarrow> V"
    and b: "pushes e (map snd ?bs) \<turnstile> Var v (tsubst \<rho> T) \<degree>\<degree> map (inst \<rho>) ts : V"
    by (auto simp: inst_abs_list inst_apps elim: typing_abs_listE)
  from b obtain As where h: "pushes e (map snd ?bs) \<turnstile> Var v (tsubst \<rho> T) : As \<Rrightarrow> V"
    and a: "pushes e (map snd ?bs) \<tturnstile> map (inst \<rho>) ts : As"
    by (rule list_app_typeE)
  from h have "tsubst \<rho> T = As \<Rrightarrow> V" "cert_typ alg ar (tsubst \<rho> T)" by auto
  moreover have "length As = length ts" using typings_nth[OF a] by simp
  ultimately show ?thesis using that[OF X[unfolded ms]] by blast
qed

lemma flex_type:
  assumes "e \<turnstile> inst \<rho> (abs_list bs (Var v T \<degree>\<degree> ts)) : X" "tsubst \<rho> T = Ps \<Rrightarrow> R"
  shows "nonfun R \<Longrightarrow> length ts \<le> length Ps"
    and "length ts \<le> length Ps \<Longrightarrow> X = (map (\<lambda>(x, T). tsubst \<rho> T) bs @ drop (length ts) Ps) \<Rrightarrow> R"
proof -
  obtain As V where X: "X = map (\<lambda>(x, T). tsubst \<rho> T) bs \<Rrightarrow> V" and T: "tsubst \<rho> T = As \<Rrightarrow> V"
    and l: "length As = length ts"
    by (rule flex_typing[OF assms(1)])
  show "nonfun R \<Longrightarrow> length ts \<le> length Ps" using funs_nonfun_le[of R As V Ps] T assms(2) l by simp
  show "X = (map (\<lambda>(x, T). tsubst \<rho> T) bs @ drop (length ts) Ps) \<Rrightarrow> R" if "length ts \<le> length Ps"
    using funs_drop[of As Ps V R] that T assms(2) l X by simp
qed

lemma aconv_abs_list_names': "map snd bs = map snd bs' \<Longrightarrow> aconv_term (abs_list bs t) (abs_list bs' t)"
proof (induction bs arbitrary: bs')
  case (Cons b bs)
  then obtain b' bs'' where "bs' = b' # bs''" "snd b = snd b'" "map snd bs = map snd bs''" by auto
  with Cons.IH show ?case by (cases b, cases b') (simp add: abs_list_def)
qed (simp add: abs_list_def)

lemma types_abs_append: "types_abs (Ps @ Qs) G = types_abs Ps (types_abs Qs G)"
  by (induction Ps) simp_all

lemma closed_types_abs: "closed G \<Longrightarrow> closed (types_abs Ps G)"
  by (simp add: types_abs_abs_list closed_abs_list closed_loose_bvar)

text \<open>A flexible term whose head is bound to a constant function:\<close>

lemma flex_conv:
  assumes ty: "e \<turnstile> inst \<rho> (abs_list bs (Var v T \<degree>\<degree> ts)) : X" and T: "tsubst \<rho> T = Ps \<Rrightarrow> R"
    and le: "length ts \<le> length Ps"
    and sv: "\<sigma> v (tsubst \<rho> T) \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> types_abs Ps G" and cl: "closed G" and tG: "\<And>e. e \<turnstile> G : R"
    and ws: "wt_subst \<sigma>"
  shows "ap \<rho> \<sigma> (abs_list bs (Var v T \<degree>\<degree> ts)) \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta>
    types_abs (map (\<lambda>(x, T). tsubst \<rho> T) bs @ drop (length ts) Ps) G"
proof -
  let ?bs = "map (\<lambda>(x, T). (x, tsubst \<rho> T)) bs" and ?ts = "map (ap \<rho> \<sigma>) ts"
  let ?H = "types_abs Ps G" and ?j = "length ts"
  have ms: "map snd ?bs = map (\<lambda>(x, T). tsubst \<rho> T) bs" by (auto simp: split_def)
  have ap: "ap \<rho> \<sigma> (abs_list bs (Var v T \<degree>\<degree> ts)) = abs_list ?bs (\<sigma> v (tsubst \<rho> T) \<degree>\<degree> ?ts)"
    by (simp add: ap_abs_list ap_apps)
  have cT: "cert_typ alg ar (tsubst \<rho> T)" by (rule flex_typing[OF ty]) assumption
  have cP: "\<forall>P\<in>set Ps. cert_typ alg ar P" using cT T cert_typ_funs by simp
  have tyap: "e \<turnstile> abs_list ?bs (\<sigma> v (tsubst \<rho> T) \<degree>\<degree> ?ts) : X" using typing_ap[OF ty ws] ap by simp
  then obtain V where X: "X = map snd ?bs \<Rrightarrow> V"
    and tb: "pushes e (map snd ?bs) \<turnstile> \<sigma> v (tsubst \<rho> T) \<degree>\<degree> ?ts : V"
    by (rule typing_abs_listE)
  from tb obtain As where th: "pushes e (map snd ?bs) \<turnstile> \<sigma> v (tsubst \<rho> T) : As \<Rrightarrow> V"
    and tts: "pushes e (map snd ?bs) \<tturnstile> ?ts : As"
    by (rule list_app_typeE)
  have AV: "As \<Rrightarrow> V = tsubst \<rho> T"
    using conv_typing_eq[OF th wt_subst_typing[OF ws cT] conv_refl] .
  have tH: "e' \<turnstile> ?H : Ps \<Rrightarrow> R" for e' by (rule typing_types_abs[OF tG cP])
  have tHa: "pushes e (map snd ?bs) \<turnstile> ?H \<degree>\<degree> ?ts : V"
    by (rule list_app_typeI[OF _ tts]) (use tH AV T in simp)
  have ty2: "e \<turnstile> abs_list ?bs (?H \<degree>\<degree> ?ts) : X"
    using typing_abs_list_replace[OF tyap[unfolded X] tHa] X by simp
  have c1: "abs_list ?bs (\<sigma> v (tsubst \<rho> T) \<degree>\<degree> ?ts) \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> abs_list ?bs (?H \<degree>\<degree> ?ts)"
  proof (rule conv_abs_list)
    show "wt (abs_list ?bs (\<sigma> v (tsubst \<rho> T) \<degree>\<degree> ?ts))" using tyap by (auto simp: wt_def)
    show "wt (abs_list ?bs (?H \<degree>\<degree> ?ts))" using ty2 by (auto simp: wt_def)
    show "\<sigma> v (tsubst \<rho> T) \<degree>\<degree> ?ts \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ?H \<degree>\<degree> ?ts"
      by (rule conv_apps[OF list_all2_refl _ _ sv]) (use tb tHa in \<open>auto simp: wt_def\<close>)
  qed
  let ?G' = "types_abs (drop ?j Ps) G"
  have H: "?H = abs_list (map (\<lambda>T. (STR '''', T)) (take ?j Ps)) ?G'"
    using types_abs_append[of "take ?j Ps" "drop ?j Ps" G] by (simp add: types_abs_abs_list)
  have clG': "closed ?G'" by (rule closed_types_abs[OF cl])
  have "?H \<degree>\<degree> ?ts \<rightarrow>\<^sub>\<beta>\<^sup>* ssub (?G' \<degree>\<degree> []) ?ts"
    unfolding H using beta_abs_list_ssub[of "map (\<lambda>T. (STR '''', T)) (take ?j Ps)" ?ts ?G'] le by simp
  also have "ssub (?G' \<degree>\<degree> []) ?ts = ?G'" using ssub_closed_apps[OF clG', of "[]" ?ts] by simp
  finally have red: "abs_list ?bs (?H \<degree>\<degree> ?ts) \<rightarrow>\<^sub>\<beta>\<^sup>* abs_list ?bs ?G'" by (rule beta_reds_abs_list)
  have "wt (abs_list ?bs (?H \<degree>\<degree> ?ts))" using ty2 by (auto simp: wt_def)
  from conv_beta_eta[OF this red] have c2: "abs_list ?bs (?H \<degree>\<degree> ?ts) \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> abs_list ?bs ?G'" .
  have "abs_list ?bs ?G' = abs_list (?bs @ map (\<lambda>T. (STR '''', T)) (drop ?j Ps)) G"
    by (simp add: types_abs_abs_list abs_list_def)
  moreover have "aconv_term (abs_list (?bs @ map (\<lambda>T. (STR '''', T)) (drop ?j Ps)) G)
      (types_abs (map (\<lambda>(x, T). tsubst \<rho> T) bs @ drop ?j Ps) G)"
    unfolding types_abs_abs_list by (rule aconv_abs_list_names') (simp add: ms[symmetric] comp_def)
  ultimately have c3: "abs_list ?bs ?G' \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> types_abs (map (\<lambda>(x, T). tsubst \<rho> T) bs @ drop ?j Ps) G"
    by (simp add: aconv_term_conv)
  from conv_trans[OF conv_trans[OF c1 c2] c3] show ?thesis unfolding ap .
qed

lemma inst_types_abs: "inst \<rho> (types_abs Ts t) = types_abs (map (tsubst \<rho>) Ts) (inst \<rho> t)"
  by (simp add: types_abs_abs_list inst_abs_list comp_def)

lemma ap_types_abs: "ap \<rho> \<sigma> (types_abs Ts t) = types_abs (map (tsubst \<rho>) Ts) (ap \<rho> \<sigma> t)"
  by (simp add: types_abs_abs_list ap_abs_list comp_def)

lemma vars_types_abs [simp]: "vars (types_abs Ts t) = vars t"
  by (simp add: types_abs_abs_list)

lemma vars_flex: "head_of (strip_abs_body s) = Var v T \<Longrightarrow> (v, T) \<in> vars s"
  using flex_decomp[of s v T] by (auto simp: vars_apps)

subsection \<open>Smashing one pair\<close>

lemma okW_var_head_of:
  assumes "okW (var_head_of env t) (v, T)"
  shows "\<exists>t'. ok (norm_term env t) t' \<and> head_of (strip_abs_body t') = Var v T"
proof -
  from assms obtain t' where n: "ok (norm_term env t) t'"
    and c: "okW (case head_of (strip_abs_body t') of Var v T \<Rightarrow> returnW (v, T) | _ \<Rightarrow> raiseW CANTUNIFY) (v, T)"
    by (auto simp: var_head_of_def)
  then have "head_of (strip_abs_body t') = Var v T" by (cases "head_of (strip_abs_body t')") auto
  with n show ?thesis by blast
qed

lemma okW_bindW_prod: "okW (bindW m (case_prod f)) y \<longleftrightarrow> (\<exists>a b. okW m (a, b) \<and> okW (f a b) y)"
  by auto

lemma ok_type_abs: "ok (type_abs env T t) r \<Longrightarrow> \<exists>Ts. ok (binder_types env T) Ts \<and> r = types_abs Ts t"
  by (cases "binder_types env T") (auto simp: type_abs_def bindM_def return_def split: res.splits)

lemma okW_smash_flexflex1:
  assumes "okW (smash_flexflex1 (t, u) env) env'"
  obtains v T w U B env1 var Us env2 Ts where "okW (var_head_of env t) (v, T)" "okW (var_head_of env u) (w, U)"
    "ok (body_type env T) B" "genvar (fst v) env B = (env1, var)"
    "ok (binder_types env1 U) Us" "ok (vupdate (w, U) (types_abs Us var) env1) env2"
    "ok (binder_types env1 T) Ts"
    "v = w \<and> T = U \<Longrightarrow> env' = env2 \<and> Ts = Us"
    "\<not> (v = w \<and> T = U) \<Longrightarrow> ok (vupdate (v, T) (types_abs Ts var) env2) env'"
proof -
  from assms obtain v T w U B where h: "okW (var_head_of env t) (v, T)" "okW (var_head_of env u) (w, U)"
    "ok (body_type env T) B"
    and r: "okW (let (env', var) = genvar (fst v) env B in do {
        tU \<leftarrow> liftM (type_abs env' U var);
        env'' \<leftarrow> liftM (vupdate (w, U) tU env');
        if v = w \<and> T = U then returnW env''
        else do {tT \<leftarrow> liftM (type_abs env' T var); liftM (vupdate (v, T) tT env'')}}) env'"
    using assms[unfolded smash_flexflex1_def prod.case okW_bindW_prod okW_bindW okW_liftM] by blast
  obtain env1 var where g: "genvar (fst v) env B = (env1, var)" by force
  from r g obtain tU env2 where tU: "ok (type_abs env1 U var) tU" and u2: "ok (vupdate (w, U) tU env1) env2"
    and r2: "okW (if v = w \<and> T = U then returnW env2
        else do {tT \<leftarrow> liftM (type_abs env1 T var); liftM (vupdate (v, T) tT env2)}) env'"
    by auto
  from ok_type_abs[OF tU] obtain Us where Us: "ok (binder_types env1 U) Us" "tU = types_abs Us var" by blast
  show ?thesis
  proof (cases "v = w \<and> T = U")
    case True
    with r2 have "env' = env2" by simp
    with True h g Us u2 show ?thesis using that[of v T w U B env1 var Us env2 Us] by auto
  next
    case False
    with r2 obtain tT where tT: "ok (type_abs env1 T var) tT" and u3: "ok (vupdate (v, T) tT env2) env'"
      by auto
    from ok_type_abs[OF tT] obtain Ts where Ts: "ok (binder_types env1 T) Ts" "tT = types_abs Ts var" by blast
    from False h g Us u2 Ts u3 show ?thesis using that[of v T w U B env1 var Us env2 Ts] by auto
  qed
qed

theorem smash_flexflex1_sound:
  assumes sm: "okW (smash_flexflex1 tu env) env'" and ac: "tacyc (tyenv env)" and tc: "tcons_env (tyenv env)"
    and gt: "gtyped env (tdps [tu])" and ci: "cert_inst (tsol0 (tyenv env))"
  shows "dstep env (tdps [tu]) env' []"
proof -
  obtain t u where tu: "tu = (t, u)" by force
  note gt = gt[unfolded tu]
  from okW_smash_flexflex1[OF sm[unfolded tu]] obtain v T w U B env1 var Us env2 Ts
    where hv: "okW (var_head_of env t) (v, T)" and hw: "okW (var_head_of env u) (w, U)"
      and bB: "ok (body_type env T) B" and g: "genvar (fst v) env B = (env1, var)"
      and bU: "ok (binder_types env1 U) Us" and u1: "ok (vupdate (w, U) (types_abs Us var) env1) env2"
      and bT: "ok (binder_types env1 T) Ts"
      and same: "v = w \<and> T = U \<Longrightarrow> env' = env2 \<and> Ts = Us"
      and diff: "\<not> (v = w \<and> T = U) \<Longrightarrow> ok (vupdate (v, T) (types_abs Ts var) env2) env'"
    by blast
  from okW_var_head_of[OF hv] obtain t' where nt: "ok (norm_term env t) t'" and ht: "head_of (strip_abs_body t') = Var v T"
    by blast
  from okW_var_head_of[OF hw] obtain u' where nu: "ok (norm_term env u) u'" and hu: "head_of (strip_abs_body u') = Var w U"
    by blast
  from flex_decomp[OF ht] obtain bst tst where t': "t' = abs_list bst (Var v T \<degree>\<degree> tst)" by blast
  from flex_decomp[OF hu] obtain bsu tsu where u': "u' = abs_list bsu (Var w U \<degree>\<degree> tsu)" by blast
  note gs = genvar_simps[OF g]
  define x where "x = (fst v, maxidx env + 1)"
  have var: "var = Var x B" using gs(4) by (simp add: x_def)
  let ?\<theta> = "tyenv env" and ?\<rho>0 = "tsol0 (tyenv env)"
  have ty1: "tyenv env1 = ?\<theta>" by (rule gs(2))
  have bB1: "ok (body_type env1 T) B" by (rule body_type_tyenv[OF bB ty1])
  from binder_types_body_type[OF bU refl] obtain B' where bB': "ok (body_type env1 U) B'" by blast
  have spT: "tsubst \<rho> T = map (tsubst \<rho>) Ts \<Rrightarrow> tsubst \<rho> B" if "tsol ?\<theta> \<rho>" for \<rho>
    by (rule binder_body_type_sound[OF bT refl bB1]) (use that ty1 in simp)
  have spU: "tsubst \<rho> U = map (tsubst \<rho>) Us \<Rrightarrow> tsubst \<rho> B'" if "tsol ?\<theta> \<rho>" for \<rho>
    by (rule binder_body_type_sound[OF bU refl bB']) (use that ty1 in simp)
  text \<open>The typing at the most general solution:\<close>
  have s0: "tsol ?\<theta> ?\<rho>0" by (rule tsol_tsol0[OF ac tc])
  from gt s0 ci have wte0: "wt_env ?\<rho>0 env" and d0: "dtyped ?\<rho>0 [([], t, u)]" unfolding gtyped_def by auto
  from d0 obtain e0 X0 where tyt0: "e0 \<turnstile> inst ?\<rho>0 t : X0" and tyu0: "e0 \<turnstile> inst ?\<rho>0 u : X0" by auto
  have tyt0': "e0 \<turnstile> inst ?\<rho>0 t' : X0" by (rule nsoundD(3)[OF norm_term_sound[OF nt s0 wte0] tyt0])
  have tyu0': "e0 \<turnstile> inst ?\<rho>0 u' : X0" by (rule nsoundD(3)[OF norm_term_sound[OF nu s0 wte0] tyu0])
  have nfB: "nonfun (tsubst ?\<rho>0 B)" using body_type_tsol0[OF bB] .
  have nfB': "nonfun (tsubst ?\<rho>0 B')" using body_type_tsol0[OF bB'] ty1 by simp
  have leT: "length tst \<le> length Ts"
    using flex_type(1)[OF tyt0'[unfolded t'] spT[OF s0] nfB] by simp
  have leU: "length tsu \<le> length Us"
    using flex_type(1)[OF tyu0'[unfolded u'] spU[OF s0] nfB'] by simp
  have X0t: "X0 = (map (\<lambda>(x, T). tsubst ?\<rho>0 T) bst @ drop (length tst) (map (tsubst ?\<rho>0) Ts)) \<Rrightarrow> tsubst ?\<rho>0 B"
    using flex_type(2)[OF tyt0'[unfolded t'] spT[OF s0]] leT by simp
  have X0u: "X0 = (map (\<lambda>(x, T). tsubst ?\<rho>0 T) bsu @ drop (length tsu) (map (tsubst ?\<rho>0) Us)) \<Rrightarrow> tsubst ?\<rho>0 B'"
    using flex_type(2)[OF tyu0'[unfolded u'] spU[OF s0]] leU by simp
  from funs_nonfun_eq[OF nfB nfB', of "map (\<lambda>(x, T). tsubst ?\<rho>0 T) bst @ drop (length tst) (map (tsubst ?\<rho>0) Ts)"
      "map (\<lambda>(x, T). tsubst ?\<rho>0 T) bsu @ drop (length tsu) (map (tsubst ?\<rho>0) Us)"] X0t X0u
  have eq0: "map (\<lambda>(x, T). tsubst ?\<rho>0 T) bst @ drop (length tst) (map (tsubst ?\<rho>0) Ts) =
      map (\<lambda>(x, T). tsubst ?\<rho>0 T) bsu @ drop (length tsu) (map (tsubst ?\<rho>0) Us)"
    and BB0: "tsubst ?\<rho>0 B = tsubst ?\<rho>0 B'"
    by simp_all
  have len: "length bst + (length Ts - length tst) = length bsu + (length Us - length tsu)"
    using arg_cong[OF eq0, of length] by simp
  have BB: "tsubst \<rho> B' = tsubst \<rho> B" if "tsol ?\<theta> \<rho>" for \<rho>
    using tsubst_tsol0_sol[OF ac tc that, of B] tsubst_tsol0_sol[OF ac tc that, of B'] BB0 by simp
  have a1: "asound env1 (w, U) (types_abs Us var) env2" by (rule vupdate_asound[OF u1 refl])
  have ext12: "extends env2 env'"
  proof (cases "v = w \<and> T = U")
    case True
    then show ?thesis using same by simp
  next
    case False
    show ?thesis by (rule asoundD(1)[OF vupdate_asound[OF diff[OF False] refl]])
  qed
  have ext: "extends env env'"
    by (rule extends_trans[OF extends_genvar[OF g] extends_trans[OF asoundD(1)[OF a1] ext12]])
  show ?thesis
  proof (rule dstepI[OF ext])
    fix \<rho> env'' X assume tsol'': "tsol (tyenv env'') \<rho>" and ext': "extends env' env''" and wte: "wt_env \<rho> env"
      and d: "dtyped \<rho> (tdps [tu])" and vi: "vinv \<rho> env (X \<union> dvars (tdps [tu]))"
    have ext2'': "extends env2 env''" by (rule extends_trans[OF ext12 ext'])
    have ext'': "extends env env''" by (rule extends_trans[OF ext ext'])
    have tsol: "tsol ?\<theta> \<rho>" by (rule extends_tsol[OF tsol'' ext''])
    note nst = norm_term_sound[OF nt tsol wte] and nsu = norm_term_sound[OF nu tsol wte]
    from d obtain e Y where tyt: "e \<turnstile> inst \<rho> t : Y" and tyu: "e \<turnstile> inst \<rho> u : Y" by (auto simp: tu)
    have tyt': "e \<turnstile> inst \<rho> t' : Y" by (rule nsoundD(3)[OF nst tyt])
    have tyu': "e \<turnstile> inst \<rho> u' : Y" by (rule nsoundD(3)[OF nsu tyu])
    note spT' = spT[OF tsol] and spU' = spU[OF tsol, unfolded BB[OF tsol]]
    define Wt where "Wt = map (\<lambda>(x, T). tsubst \<rho> T) bst @ drop (length tst) (map (tsubst \<rho>) Ts)"
    define Wu where "Wu = map (\<lambda>(x, T). tsubst \<rho> T) bsu @ drop (length tsu) (map (tsubst \<rho>) Us)"
    have Yt: "Y = Wt \<Rrightarrow> tsubst \<rho> B"
      using flex_type(2)[OF tyt'[unfolded t'] spT'] leT by (simp add: Wt_def)
    have Yu: "Y = Wu \<Rrightarrow> tsubst \<rho> B"
      using flex_type(2)[OF tyu'[unfolded u'] spU'] leU by (simp add: Wu_def)
    have W: "Wt = Wu" by (rule funs_len_eq[OF _ trans[OF Yt[symmetric] Yu]]) (use len in \<open>simp add: Wt_def Wu_def\<close>)
    have cT: "cert_typ alg ar (tsubst \<rho> T)" by (rule flex_typing[OF tyt'[unfolded t']]) assumption
    have cU: "cert_typ alg ar (tsubst \<rho> U)" by (rule flex_typing[OF tyu'[unfolded u']]) assumption
    have cTs: "\<forall>P\<in>set (map (tsubst \<rho>) Ts). cert_typ alg ar P" and cB: "cert_typ alg ar (tsubst \<rho> B)"
      using cT spT' cert_typ_funs by simp_all
    have cUs: "\<forall>P\<in>set (map (tsubst \<rho>) Us). cert_typ alg ar P" using cU spU' cert_typ_funs by simp
    have tyvar: "e' \<turnstile> inst \<rho> var : tsubst \<rho> B" for e' using cB by (auto simp: var)
    have tyT: "e' \<turnstile> inst \<rho> (types_abs Ts var) : tsubst \<rho> T" for e'
      using typing_types_abs[OF tyvar cTs] spT' by (simp add: inst_types_abs)
    have tyU: "e' \<turnstile> inst \<rho> (types_abs Us var) : tsubst \<rho> U" for e'
      using typing_types_abs[OF tyvar cUs] spU' by (simp add: inst_types_abs)
    have clv: "closed var" by (simp add: var closed_def)
    have clT: "closed (types_abs Ts var)" and clU: "closed (types_abs Us var)"
      by (simp_all add: closed_types_abs[OF clv])
    text \<open>The variables:\<close>
    have vi0: "vinv \<rho> env (X \<union> (vars t \<union> vars u))" using vi by (simp add: tu)
    have "vsim \<rho> {(v, T), (w, U)} ((vars t \<union> vars u) \<union> evars env)"
    proof -
      have "vsim \<rho> {(v, T)} (vars t \<union> evars env)"
        using nsoundD(1)[OF nst] vars_flex[OF ht] unfolding vsim_def by blast
      moreover have "vsim \<rho> {(w, U)} (vars u \<union> evars env)"
        using nsoundD(1)[OF nsu] vars_flex[OF hu] unfolding vsim_def by blast
      ultimately show ?thesis unfolding vsim_def by blast
    qed
    from vinv_genvar[OF g vinv_vsim[OF vi0 this]]
    have vi1: "vinv \<rho> env1 (vars var \<union> (X \<union> {(v, T), (w, U)}))" .
    have wte1: "wt_env \<rho> env1" using wte by (simp add: wt_env_genvar[OF g])
    have vi1': "vinv \<rho> env1 ((X \<union> insert (v, T) (vars (types_abs Ts var))) \<union> insert (w, U) (vars (types_abs Us var)))"
      by (rule vinv_mono[OF vi1]) auto
    have tyU': "e' \<turnstile> inst \<rho> (types_abs Us var) : tsubst \<rho> (snd (w, U))" for e' using tyU by simp
    have tyT': "e' \<turnstile> inst \<rho> (types_abs Ts var) : tsubst \<rho> (snd (v, T))" for e' using tyT by simp
    from asoundD(2)[OF a1 tsol'' ext2'' wte1 clU tyU' vi1']
    have r1: "wt_env \<rho> env2" "vinv \<rho> env2 (X \<union> insert (v, T) (vars (types_abs Ts var)))"
      "\<And>\<sigma>. solution \<rho> \<sigma> env'' \<Longrightarrow> \<sigma> w (tsubst \<rho> U) \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma> (types_abs Us var)"
      by auto
    have r2: "wt_env \<rho> env' \<and> vinv \<rho> env' X \<and>
        (\<forall>\<sigma>. solution \<rho> \<sigma> env'' \<longrightarrow> \<sigma> v (tsubst \<rho> T) \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma> (types_abs Ts var))"
    proof (cases "v = w \<and> T = U")
      case True
      with same have "env' = env2" "Ts = Us" by simp_all
      with True r1 show ?thesis by (auto elim: vinv_mono)
    next
      case False
      from asoundD(2)[OF vupdate_asound[OF diff[OF False] refl] tsol'' ext' r1(1) clT tyT' r1(2)]
      show ?thesis by simp
    qed
    have "ap \<rho> \<sigma> t \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma> u" if sol: "solution \<rho> \<sigma> env''" for \<sigma>
    proof -
      have ws: "wt_subst \<sigma>" by (rule solutionD(3)[OF sol])
      have sol0: "solution \<rho> \<sigma> env" by (rule solution_extends[OF sol ext''])
      let ?G = "\<sigma> x (tsubst \<rho> B)"
      have clG: "closed ?G" using ws unfolding wt_subst_def closed_subst_def by (cases x) simp
      have tG: "e' \<turnstile> ?G : tsubst \<rho> B" for e' by (rule wt_subst_typing[OF ws cB])
      have apv: "ap \<rho> \<sigma> (types_abs Ps var) = types_abs (map (tsubst \<rho>) Ps) ?G" for Ps
        by (simp add: ap_types_abs var)
      have "\<sigma> v (tsubst \<rho> T) \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma> (types_abs Ts var)" using r2 sol by simp
      then have svT: "\<sigma> v (tsubst \<rho> T) \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> types_abs (map (tsubst \<rho>) Ts) ?G" by (simp only: apv)
      have svU: "\<sigma> w (tsubst \<rho> U) \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> types_abs (map (tsubst \<rho>) Us) ?G"
        using r1(3)[OF sol] by (simp only: apv)
      have ct: "ap \<rho> \<sigma> t' \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> types_abs Wt ?G"
        unfolding t' Wt_def using flex_conv[OF tyt'[unfolded t'] spT' _ svT clG tG ws] leT by simp
      have cu: "ap \<rho> \<sigma> u' \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> types_abs Wu ?G"
        unfolding u' Wu_def using flex_conv[OF tyu'[unfolded u'] spU' _ svU clG tG ws] leU by simp
      have "ap \<rho> \<sigma> t \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma> t'" by (rule nsoundD(4)[OF nst tyt sol0])
      also have "\<dots> \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> types_abs Wt ?G" by (rule ct)
      also have "\<dots> \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma> u'" using conv_sym[OF cu] W by simp
      also have "\<dots> \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma> u" by (rule conv_sym[OF nsoundD(4)[OF nsu tyu sol0]])
      finally show ?thesis .
    qed
    with r2 show "wt_env \<rho> env' \<and> dtyped \<rho> [] \<and> vinv \<rho> env' (X \<union> dvars []) \<and>
        (\<forall>\<sigma>. solution \<rho> \<sigma> env'' \<longrightarrow> dsolved \<rho> \<sigma> [] \<longrightarrow> dsolved \<rho> \<sigma> (tdps [tu]))"
      by (simp add: tu)
  qed
qed

subsection \<open>Smashing all pairs\<close>

lemma vupdate_tyenv:
  assumes "vupdate aU t env = Some r"
  shows "r = Ok env' \<Longrightarrow> tyenv env' = tyenv env"
  using assms
proof (induction aU t env r arbitrary: env' rule: vupdate.raw_induct[rotated, consumes 1])
  case (1 vu aU t env r)
  obtain v T0 where aU: "aU = (v, T0)" by (cases aU)
  have up: "ok (case t of
      Var name' T \<Rightarrow>
        if fst aU = name' then return env
        else if indexname_less (fst aU) name' then lookup env name' T \<bind> (\<lambda>r.
          case r of None \<Rightarrow> update (name', T) (Var (fst aU) T) env | Some u \<Rightarrow> vu aU u env)
        else update aU t env
    | _ \<Rightarrow> update aU t env) env'"
    using "1.hyps" "1.prems" by simp
  have upd: "ok (update aU s env) env' \<Longrightarrow> tyenv env' = tyenv env" for s
    using ok_update(3)[of v T0 s env env'] aU by simp
  show ?case
  proof (cases t)
    case (Var name' T)
    consider "v = name'" | "v \<noteq> name'" "indexname_less v name'" | "v \<noteq> name'" "\<not> indexname_less v name'"
      by blast
    then show ?thesis
    proof cases
      case 1
      with up Var aU show ?thesis by simp
    next
      case 2
      with up Var aU obtain lr where lk: "ok (lookup env name' T) lr"
        and rest: "ok (case lr of None \<Rightarrow> update (name', T) (Var v T) env | Some u \<Rightarrow> vu aU u env) env'"
        by auto
      show ?thesis
      proof (cases lr)
        case None
        with rest show ?thesis using ok_update(3)[of name' T "Var v T" env env'] by simp
      next
        case (Some u)
        with rest have "ok (vu aU u env) env'" by simp
        from "1.IH"[OF this refl] show ?thesis .
      qed
    next
      case 3
      with up Var aU have "ok (update aU t env) env'" by simp
      then show ?thesis by (rule upd)
    qed
  qed (use up upd in auto)
qed

lemma smash_flexflex1_tyenv:
  assumes "okW (smash_flexflex1 tu env) env'"
  shows "tyenv env' = tyenv env"
proof -
  obtain t u where tu: "tu = (t, u)" by force
  from okW_smash_flexflex1[OF assms[unfolded tu]] obtain v T w U B env1 var Us env2 Ts
    where "okW (var_head_of env t) (v, T)" "okW (var_head_of env u) (w, U)"
      "ok (body_type env T) B" and g: "genvar (fst v) env B = (env1, var)"
      and "ok (binder_types env1 U) Us" and u1: "ok (vupdate (w, U) (types_abs Us var) env1) env2"
      and "ok (binder_types env1 T) Ts"
      and same: "v = w \<and> T = U \<Longrightarrow> env' = env2 \<and> Ts = Us"
      and diff: "\<not> (v = w \<and> T = U) \<Longrightarrow> ok (vupdate (v, T) (types_abs Ts var) env2) env'"
    by blast
  have "tyenv env2 = tyenv env" using vupdate_tyenv[OF u1 refl] genvar_simps(2)[OF g] by simp
  moreover have "tyenv env' = tyenv env2"
  proof (cases "v = w \<and> T = U")
    case False
    from vupdate_tyenv[OF diff[OF False] refl] show ?thesis .
  qed (use same in simp)
  ultimately show ?thesis by simp
qed

lemma gtyped_mono: "gtyped env dps \<Longrightarrow> set dps' \<subseteq> set dps \<Longrightarrow> gtyped env dps'"
  unfolding gtyped_def using dtyped_mono dvars_mono vinv_mono by metis

theorem foldrW_smash_flexflex1_sound:
  assumes "okW (foldrW smash_flexflex1 tps env) env'" "tacyc (tyenv env)" "tcons_env (tyenv env)"
    "gtyped env (tdps tps)" "cert_inst (tsol0 (tyenv env))"
  shows "dstep env (tdps tps) env' [] \<and> tyenv env' = tyenv env"
  using assms
proof (induction rule: okW_foldrW_induct)
  case (Nil b)
  then show ?case by (simp add: dstep_refl)
next
  case (Cons x xs b b1 b')
  obtain t u where x: "x = (t, u)" by force
  have g: "gtyped b (tdps xs)" by (rule gtyped_mono[OF Cons.prems(3)]) auto
  from Cons.IH[OF Cons.prems(1,2) g Cons.prems(4)] have s1: "dstep b (tdps xs) b1 []" and ty1: "tyenv b1 = tyenv b" by simp_all
  from dstep_frame[OF s1, of "tdps [x]"] have "dstep b (tdps xs @ tdps [x]) b1 (tdps [x])" by simp
  then have s1': "dstep b (tdps (x # xs)) b1 (tdps [x])" by (rule dstep_set) auto
  have g1: "gtyped b1 (tdps [x])" by (rule gtyped_dstep[OF s1' Cons.prems(3)])
  have s2: "dstep b1 (tdps [x]) b' []"
    by (rule smash_flexflex1_sound[OF Cons.hyps(2)]) (use ty1 Cons.prems g1 in simp_all)
  from dstep_trans[OF s1' s2] smash_flexflex1_tyenv[OF Cons.hyps(2)] ty1 show ?case by simp
qed

theorem smash_flexflex_sound:
  assumes "okW (smash_flexflex (env, tps)) env'" "tacyc (tyenv env)" "tcons_env (tyenv env)"
    "gtyped env (tdps tps)" "cert_inst (tsol0 (tyenv env))"
  shows "dstep env (tdps tps) env' []"
  using foldrW_smash_flexflex1_sound[of tps env env'] assms by (simp add: smash_flexflex_def)

text \<open>
  Hence smashing a unifier that the enumeration of \<^const>\<open>unifiers\<close> yields gives a unifier of
  the input without flex-flex pairs, if the input is in the invariant of the termination proof
  (for the soundness of \<^const>\<open>unifiers\<close>) and well-typed at every certified solution of its type
  environment, and the type environment of the unifier is acyclic and consistent in its sorts, with
  a certified most general solution.
\<close>

theorem unifiers_smash_sound:
  assumes cfg: "cfg_alg cfg = alg" and fin: "finite X" "finite K" and si: "sinv A K X env (tdps tus)"
    and u: "unifiers alg' env tus = Some (Ok s)" and es: "evals cfg s xs" and x: "El_R env' tps \<in> set xs"
    and sm: "okW (smash_flexflex (env', tps)) env''"
    and gt: "gtyped env (map (\<lambda>(t, u). ([], t, u)) tus)"
    and ac: "tacyc (tyenv env')" and tc: "tcons_env (tyenv env')" and ci: "cert_inst (tsol0 (tyenv env'))"
  shows "dstep env (map (\<lambda>(t, u). ([], t, u)) tus) env'' []"
proof -
  from unifiers_sound[OF cfg fin si u es x]
  have s1: "dstep env (map (\<lambda>(t, u). ([], t, u)) tus) env' (tdps tps)" by simp
  have "gtyped env' (tdps tps)" by (rule gtyped_dstep[OF s1 gt])
  from dstep_trans[OF s1 smash_flexflex_sound[OF sm ac tc this ci]] show ?thesis .
qed

end

end

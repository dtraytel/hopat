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
  to be well-typed at all solutions of the type environment (\<open>gtyped\<close>).
\<close>

definition gtyped :: "env \<Rightarrow> dpair list \<Rightarrow> bool" where
  "gtyped env dps \<longleftrightarrow>
    (\<forall>\<rho>. tsol (tyenv env) \<rho> \<longrightarrow> wt_env \<rho> env \<and> dtyped \<rho> dps \<and> vinv \<rho> env (dvars dps))"

lemma gtyped_dstep:
  assumes "dstep env dps env' dps'" "gtyped env dps"
  shows "gtyped env' dps'"
  unfolding gtyped_def
proof (intro allI impI)
  fix \<rho> assume t: "tsol (tyenv env') \<rho>"
  have "tsol (tyenv env) \<rho>" by (rule extends_tsol[OF t dstepD(1)[OF assms(1)]])
  with assms(2) have "wt_env \<rho> env" "dtyped \<rho> dps" "vinv \<rho> env ({} \<union> dvars dps)"
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

end

end

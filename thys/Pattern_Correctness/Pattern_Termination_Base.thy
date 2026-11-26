section \<open>Definitions and Invariants for the Termination of Pattern Unification\<close>

theory Pattern_Termination_Base
  imports Pattern_Size Pattern_Complete Pattern_Type_Reach
begin

context pure_sig_gen
begin

lemma nfree_strict: "loose = {} \<Longrightarrow> nfree env"
  unfolding nfree_def by simp

subsection \<open>Strong normalization with subterms\<close>

definition subt :: "pterm \<Rightarrow> pterm \<Rightarrow> bool" where
  "subt s t \<longleftrightarrow> (\<exists>a T. s = Abs a T t) \<or> (\<exists>u. s = t $ u) \<or> (\<exists>u. s = u $ t)"

lemma subt_beta: "subt x x1 \<Longrightarrow> x1 \<rightarrow>\<^sub>\<beta> w1 \<Longrightarrow> \<exists>w. x \<rightarrow>\<^sub>\<beta> w \<and> subt w w1"
  by (auto simp: subt_def)

lemma subts_beta: "subt\<^sup>*\<^sup>* x y \<Longrightarrow> y \<rightarrow>\<^sub>\<beta> z \<Longrightarrow> \<exists>w. x \<rightarrow>\<^sub>\<beta> w \<and> subt\<^sup>*\<^sup>* w z"
proof (induction rule: converse_rtranclp_induct)
  case (step x x1)
  from step.IH[OF step.prems] obtain w1 where "x1 \<rightarrow>\<^sub>\<beta> w1" "subt\<^sup>*\<^sup>* w1 z" by blast
  with subt_beta[OF step.hyps(1)] show ?case by (meson converse_rtranclp_into_rtranclp)
qed blast

lemma subt_size: "subt x y \<Longrightarrow> size y < size x"
  by (auto simp: subt_def)

text \<open>Strongly normalizing terms are strongly normalizing for reduction and subterms:\<close>

lemma termip_beta_subt:
  assumes "termip beta t"
  shows "termip (sup beta subt) t"
proof -
  have "\<forall>z. subt\<^sup>*\<^sup>* x z \<longrightarrow> termip (sup beta subt) z" if "termip beta x" for x
    using that
  proof (induction rule: accp_induct_rule)
    case (1 x)
    show ?case
    proof (intro allI impI)
      fix z assume "subt\<^sup>*\<^sup>* x z"
      then show "termip (sup beta subt) z"
      proof (induction z rule: measure_induct_rule[of size])
        case (less z)
        show ?case
        proof (rule accp.accI)
          fix z' assume "conversep (sup beta subt) z' z"
          then have "z \<rightarrow>\<^sub>\<beta> z' \<or> subt z z'" by auto
          then show "termip (sup beta subt) z'"
          proof
            assume "z \<rightarrow>\<^sub>\<beta> z'"
            from subts_beta[OF less.prems this] obtain w where "x \<rightarrow>\<^sub>\<beta> w" "subt\<^sup>*\<^sup>* w z'" by blast
            with "1.IH" show ?thesis by blast
          next
            assume "subt z z'"
            with less.prems have "subt\<^sup>*\<^sup>* x z'" by (rule rtranclp.rtrancl_into_rtrancl)
            with less.IH subt_size[OF \<open>subt z z'\<close>] show ?thesis by blast
          qed
        qed
      qed
    qed
  qed
  with assms show ?thesis by blast
qed

definition sn_less :: "(pterm \<times> pterm) set" where
  "sn_less = {(y, x). termip (sup beta subt) x \<and> (sup beta subt)\<^sup>+\<^sup>+ x y}"

lemma wf_sn_less: "wf sn_less"
proof (rule wfI_pf)
  fix A assume A: "A \<subseteq> sn_less `` A"
  show "A = {}"
  proof (rule ccontr)
    assume "A \<noteq> {}"
    then obtain x where "x \<in> A" by blast
    have "\<forall>y. (sup beta subt)\<^sup>*\<^sup>* x y \<longrightarrow> y \<notin> A" if "termip (sup beta subt) x" for x
      using that
    proof (induction rule: accp_induct_rule)
      case (1 x)
      show ?case
      proof (intro allI impI notI)
        fix y assume xy: "(sup beta subt)\<^sup>*\<^sup>* x y" and yA: "y \<in> A"
        from yA A obtain z where z: "z \<in> A" "(z, y) \<in> sn_less" by blast
        then have "(sup beta subt)\<^sup>+\<^sup>+ y z" by (simp add: sn_less_def)
        with xy have "(sup beta subt)\<^sup>+\<^sup>+ x z" by (rule rtranclp_tranclp_tranclp)
        then obtain x' where x': "sup beta subt x x'" "(sup beta subt)\<^sup>*\<^sup>* x' z"
          by (auto dest: tranclpD)
        have "conversep (sup beta subt) x' x" using x'(1) by (rule conversepI)
        from "1.IH"[OF this] x'(2) z(1) show False by blast
      qed
    qed
    moreover from \<open>x \<in> A\<close> A obtain z where "(z, x) \<in> sn_less" by blast
    then have "termip (sup beta subt) x" by (simp add: sn_less_def)
    ultimately show False using \<open>x \<in> A\<close> by blast
  qed
qed

lemma termip_sup_reds: "(sup beta subt)\<^sup>*\<^sup>* x y \<Longrightarrow> termip (sup beta subt) x \<Longrightarrow> termip (sup beta subt) y"
  by (induction rule: rtranclp_induct) (auto elim: accp_downward intro: conversepI)

lemma beta_reds_sup: "s \<rightarrow>\<^sub>\<beta>\<^sup>* t \<Longrightarrow> (sup beta subt)\<^sup>*\<^sup>* s t"
  by (induction rule: rtranclp_induct) (auto intro: rtranclp.rtrancl_into_rtrancl)


text \<open>The rank of the head of a term, for the induction on head normalization:\<close>

definition hrk :: "env \<Rightarrow> pterm \<Rightarrow> nat" where
  "hrk env t = (case t of Var x T \<Rightarrow> Suc (rk env x) | _ \<Rightarrow> 0)"


subsection \<open>Auxiliary computations\<close>

lemma mapM_return: "(\<And>x. x \<in> set xs \<Longrightarrow> \<exists>y. f x = return y) \<Longrightarrow> \<exists>ys. mapM f xs = return ys"
proof (induction xs)
  case (Cons a xs)
  then obtain y ys where "f a = return y" "mapM f xs = return ys" by (meson list.set_intros)
  then show ?case by simp
qed simp

lemma ints_of_result: "(\<exists>is. ints_of ts = return is) \<or> ints_of ts = raise Pattern"
proof (induction ts rule: ints_of.induct)
  case (2 i bs)
  then show ?case by auto
qed simp_all

lemma subt_apps: "u \<in> set ts \<Longrightarrow> subt\<^sup>+\<^sup>+ (h \<degree>\<degree> ts) u"
proof (induction ts rule: rev_induct)
  case (snoc v ts)
  have "subt (h \<degree>\<degree> (ts @ [v])) v" "subt (h \<degree>\<degree> (ts @ [v])) (h \<degree>\<degree> ts)" by (simp_all add: subt_def)
  with snoc show ?case by (auto intro: tranclp_into_tranclp2)
qed simp

lemma sup_subt_apps: "u \<in> set ts \<Longrightarrow> (sup beta subt)\<^sup>+\<^sup>+ (h \<degree>\<degree> ts) u"
proof -
  assume "u \<in> set ts"
  from subt_apps[OF this, where h = h] show ?thesis
  proof (induction rule: tranclp_induct)
    case (step y z)
    then show ?case by (meson sup2I2 tranclp.trancl_into_trancl)
  qed (simp add: tranclp.r_into_trancl)
qed

subsection \<open>Strong normalization of well-typed problems\<close>

lemma termip_inst: "termip beta s \<Longrightarrow> s = inst \<rho> t \<Longrightarrow> termip beta t"
proof (induction arbitrary: t rule: accp_induct_rule)
  case (1 s)
  show ?case
  proof (rule accp.accI)
    fix t' assume "conversep beta t' t"
    then have "inst \<rho> t \<rightarrow>\<^sub>\<beta> inst \<rho> t'" by (simp add: beta_inst)
    with "1.prems" show "termip beta t'" by (intro "1.IH") simp_all
  qed
qed

subsection \<open>Unbound variables\<close>

text \<open>The unbound variables of the problem \<open>X\<close> and the environment:\<close>

definition ubv :: "env \<Rightarrow> (indexname \<times> ptyp) set \<Rightarrow> indexname set" where
  "ubv env X = {x \<in> fst ` (X \<union> evars env). vt_lookup (tenv env) x = None}"

lemma finite_bnds: "finite (bnds env)"
proof -
  have "bnds env \<subseteq> (\<lambda>x. (x, the (vt_lookup (tenv env) x))) ` {x. vt_lookup (tenv env) x \<noteq> None}"
    by (force simp: bnds_def)
  then show ?thesis by (rule finite_subset) (rule finite_imageI[OF finite_vt_lookup])
qed

lemma finite_evars: "finite (evars env)"
  unfolding evars_def using finite_bnds by (simp add: split_def)

lemma finite_ubv: "finite X \<Longrightarrow> finite (ubv env X)"
  unfolding ubv_def using finite_evars by auto

lemma ubv_genvar: "genvar a env T = (env', G) \<Longrightarrow> ubv env' X = ubv env X"
  by (simp add: ubv_def genvar_simps evars_genvar)

lemma ubv_update:
  assumes "ok (update (G, Gty) b env) env'" "G \<in> fst ` (X \<union> evars env)"
  shows "ubv env' X \<subseteq> (ubv env X - {G}) \<union> {y \<in> fst ` vars b. vt_lookup (tenv env') y = None}"
  using assms ok_update(1,2)[OF assms(1)] evars_update[OF assms(1)] unfolding ubv_def by auto

lemma card_ubv_update:
  assumes "finite X" "ok (update (G, Gty) b env) env'" "G \<in> fst ` (X \<union> evars env)"
  shows "vars b \<subseteq> X \<union> evars env \<Longrightarrow> card (ubv env' X) < card (ubv env X)"
    and "vars b \<subseteq> X \<union> evars env \<union> {(H, Hty)} \<Longrightarrow> card (ubv env' X) \<le> card (ubv env X)"
proof -
  note u = ok_update[OF assms(2)]
  have G: "G \<in> ubv env X" using assms(3) u(1) by (simp add: ubv_def)
  have fin: "finite (ubv env X)" by (rule finite_ubv[OF assms(1)])
  show "card (ubv env' X) < card (ubv env X)" if "vars b \<subseteq> X \<union> evars env"
  proof -
    have "{y \<in> fst ` vars b. vt_lookup (tenv env') y = None} \<subseteq> ubv env X - {G}"
    proof
      fix y assume "y \<in> {y \<in> fst ` vars b. vt_lookup (tenv env') y = None}"
      then obtain T where yb: "(y, T) \<in> vars b" and y: "vt_lookup (tenv env') y = None" by force
      from y u(2) have "y \<noteq> G" "vt_lookup (tenv env) y = None" by (auto split: if_splits)
      with yb that show "y \<in> ubv env X - {G}" unfolding ubv_def by force
    qed
    then have "ubv env' X \<subseteq> ubv env X - {G}" using ubv_update[OF assms(2,3)] by blast
    moreover have "card (ubv env X - {G}) < card (ubv env X)" using fin G by (rule card_Diff1_less)
    ultimately show ?thesis using fin by (meson card_mono finite_Diff le_less_trans)
  qed
  show "card (ubv env' X) \<le> card (ubv env X)" if "vars b \<subseteq> X \<union> evars env \<union> {(H, Hty)}"
  proof -
    have "{y \<in> fst ` vars b. vt_lookup (tenv env') y = None} \<subseteq> (ubv env X - {G}) \<union> {H}"
    proof
      fix y assume "y \<in> {y \<in> fst ` vars b. vt_lookup (tenv env') y = None}"
      then obtain T where yb: "(y, T) \<in> vars b" and y: "vt_lookup (tenv env') y = None" by force
      from y u(2) have "y \<noteq> G" "vt_lookup (tenv env) y = None" by (auto split: if_splits)
      with yb that show "y \<in> (ubv env X - {G}) \<union> {H}" unfolding ubv_def by force
    qed
    then have "ubv env' X \<subseteq> insert H (ubv env X - {G})" using ubv_update[OF assms(2,3)] by blast
    then have "card (ubv env' X) \<le> card (insert H (ubv env X - {G}))"
      using fin by (intro card_mono) simp_all
    also have "\<dots> \<le> Suc (card (ubv env X - {G}))" by (simp add: card_insert_if fin)
    also have "\<dots> = card (ubv env X)" by (rule card_Suc_Diff1[OF fin G])
    finally show ?thesis .
  qed
qed


subsection \<open>Pruning extensions\<close>

lemma typing_abs_list_inv:
  "e \<turnstile> abs_list bs t : U \<Longrightarrow> \<exists>V. U = map snd bs \<Rrightarrow> V \<and> pushes e (map snd bs) \<turnstile> t : V"
proof (induction bs arbitrary: e U)
  case (Cons b bs)
  obtain x T where b: "b = (x, T)" by force
  with Cons.prems obtain U' where U: "U = T \<rightarrow>\<^sub>T U'" "e\<langle>0:T\<rangle> \<turnstile> abs_list bs t : U'" by auto
  from Cons.IH[OF U(2)] obtain V where "U' = map snd bs \<Rrightarrow> V" "pushes (e\<langle>0:T\<rangle>) (map snd bs) \<turnstile> t : V"
    by blast
  with U b show ?case by auto
qed simp

lemma typing_abs_listE:
  assumes "e \<turnstile> abs_list bs t : U"
  obtains V where "U = map snd bs \<Rrightarrow> V" "pushes e (map snd bs) \<turnstile> t : V"
  using typing_abs_list_inv[OF assms] by blast

lemma prune_arity:
  assumes "e \<turnstile> inst \<rho> (abs_list bs (Var H Hty \<degree>\<degree> map Bound ks)) : U"
  shows "\<exists>a. arity U = length bs + a \<and> arity (tsubst \<rho> Hty) = length ks + a"
proof -
  let ?e = "pushes e (map snd (map (\<lambda>(x, T). (x, tsubst \<rho> T)) bs))"
  from assms obtain V where U: "U = map snd (map (\<lambda>(x, T). (x, tsubst \<rho> T)) bs) \<Rrightarrow> V"
    and ty: "?e \<turnstile> Var H (tsubst \<rho> Hty) \<degree>\<degree> map Bound ks : V"
    by (auto simp: inst_abs_list inst_apps comp_def elim: typing_abs_listE)
  from list_app_typeD[OF ty] obtain Ks where Ks: "?e \<turnstile> Var H (tsubst \<rho> Hty) : Ks \<Rrightarrow> V \<and> ?e \<tturnstile> map Bound ks : Ks"
    by (rule exE)
  then have "tsubst \<rho> Hty = Ks \<Rrightarrow> V" by auto
  moreover have "length Ks = length ks" using typings_nth[of ?e "map Bound ks" Ks] Ks by simp
  ultimately show ?thesis using U by (intro exI[of _ "arity V"]) (simp add: arity_funs)
qed

subsection \<open>Extensions by fresh variables\<close>

text \<open>The new bindings of an extension contain only fresh variables:\<close>

definition newb :: "env \<Rightarrow> env \<Rightarrow> bool" where
  "newb env env' \<longleftrightarrow> extends env env' \<and>
    (\<forall>x U u y T. vt_lookup (tenv env') x = Some (U, u) \<longrightarrow> vt_lookup (tenv env) x = None \<longrightarrow>
      (y, T) \<in> vars u \<longrightarrow> maxidx env < snd y)"

definition bbelow :: "env \<Rightarrow> bool" where
  "bbelow env \<longleftrightarrow> (\<forall>x b. vt_lookup (tenv env) x = Some b \<longrightarrow> snd x \<le> maxidx env)"

lemma newbD:
  assumes "newb env env'"
  shows "extends env env'"
    and "vt_lookup (tenv env') x = Some (U, u) \<Longrightarrow> vt_lookup (tenv env) x = None \<Longrightarrow> (y, T) \<in> vars u \<Longrightarrow>
      maxidx env < snd y"
  using assms unfolding newb_def by blast+

lemma bbelowD: "bbelow env \<Longrightarrow> vt_lookup (tenv env) x = Some b \<Longrightarrow> snd x \<le> maxidx env"
  unfolding bbelow_def by blast

lemma bbelow_mono:
  assumes "bbelow env" "tenv env' = tenv env" "maxidx env \<le> maxidx env'"
  shows "bbelow env'"
  unfolding bbelow_def
proof (intro allI impI)
  fix x b assume "vt_lookup (tenv env') x = Some b"
  with assms(2) have "vt_lookup (tenv env) x = Some b" by simp
  then have "snd x \<le> maxidx env" by (rule bbelowD[OF assms(1)])
  with assms(3) show "snd x \<le> maxidx env'" by simp
qed

lemma newb_refl [simp]: "newb env env"
  by (simp add: newb_def)

lemma newb_trans:
  assumes "newb env env1" "newb env1 env2"
  shows "newb env env2"
  unfolding newb_def
proof (intro conjI allI impI)
  note e1 = newbD(1)[OF assms(1)] and e2 = newbD(1)[OF assms(2)]
  show "extends env env2" by (rule extends_trans[OF e1 e2])
  fix x U u y T assume x2: "vt_lookup (tenv env2) x = Some (U, u)" and x0: "vt_lookup (tenv env) x = None"
    and y: "(y, T) \<in> vars u"
  have le: "maxidx env \<le> maxidx env1" using e1 by (simp add: extends_def)
  show "maxidx env < snd y"
  proof (cases "vt_lookup (tenv env1) x")
    case None
    with newbD(2)[OF assms(2) x2 _ y] le show ?thesis by simp
  next
    case (Some b)
    with e2 x2 have "vt_lookup (tenv env1) x = Some (U, u)" using extends_lookup by fastforce
    from newbD(2)[OF assms(1) this x0 y] show ?thesis .
  qed
qed

lemma newb_genvar: "genvar a env T = (env', G) \<Longrightarrow> newb env env'"
  by (simp add: newb_def genvar_simps extends_genvar)

lemma newb_update:
  assumes "ok (update (F, T) u env) env'" "\<And>y U. (y, U) \<in> vars u \<Longrightarrow> maxidx env0 < snd y" "newb env0 env"
  shows "newb env0 env'"
  unfolding newb_def
proof (intro conjI allI impI)
  note u = ok_update[OF assms(1)]
  show "extends env0 env'" by (rule extends_trans[OF newbD(1)[OF assms(3)] extends_update[OF assms(1)]])
  fix x U' u' y T' assume x': "vt_lookup (tenv env') x = Some (U', u')" and x0: "vt_lookup (tenv env0) x = None"
    and y: "(y, T') \<in> vars u'"
  show "maxidx env0 < snd y"
  proof (cases "x = F")
    case True
    with x' u(2) have "u' = u" by simp
    with assms(2) y show ?thesis by blast
  next
    case False
    with x' u(2) have "vt_lookup (tenv env) x = Some (U', u')" by simp
    from newbD(2)[OF assms(3) this x0 y] show ?thesis .
  qed
qed

lemma dep_newb:
  assumes nb: "newb env env'" and bb: "bbelow env"
  shows "(y, x) \<in> (dep env')\<^sup>* \<Longrightarrow> (y, x) \<in> (dep env)\<^sup>* \<or> maxidx env < snd y"
proof (induction rule: converse_rtrancl_induct)
  case (step y z)
  from step.hyps(1) obtain U u T where z: "vt_lookup (tenv env') z = Some (U, u)" and yu: "(y, T) \<in> vars u"
    by (rule depE)
  show ?case
  proof (cases "vt_lookup (tenv env) z")
    case None
    from newbD(2)[OF nb z None yu] show ?thesis by simp
  next
    case (Some b)
    with newbD(1)[OF nb] z have zb: "vt_lookup (tenv env) z = Some (U, u)" using extends_lookup by fastforce
    then have "(y, z) \<in> dep env" using yu by (rule depI)
    moreover have "snd z \<le> maxidx env" using bbelowD[OF bb zb] .
    ultimately show ?thesis using step.IH by (auto intro: converse_rtrancl_into_rtrancl)
  qed
qed simp

lemma names_newb:
  assumes "acyc env" "acyc env'" "newb env env'" "bbelow env"
  shows "fst ` vars (unf env' t) \<subseteq> fst ` vars (unf env t) \<union> {y. maxidx env < snd y}"
proof
  fix y assume "y \<in> fst ` vars (unf env' t)"
  then obtain x where y: "vt_lookup (tenv env') y = None" "x \<in> fst ` vars t" "(y, x) \<in> (dep env')\<^sup>*"
    using vars_unf_name[OF assms(2)] by blast
  have "vt_lookup (tenv env) y = None"
  proof (rule ccontr)
    assume "vt_lookup (tenv env) y \<noteq> None"
    then obtain b where "vt_lookup (tenv env) y = Some b" by blast
    with extends_lookup[OF newbD(1)[OF assms(3)]] y(1) show False by simp
  qed
  with dep_newb[OF assms(3,4) y(3)] y(2) vars_unf_name[OF assms(1), of t]
  show "y \<in> fst ` vars (unf env t) \<union> {y. maxidx env < snd y}" by blast
qed

subsection \<open>The most general instantiation\<close>

text \<open>
  Normalization by an acyclic type environment whose bindings are certified is a certified type
  instantiation; it is the most general solution of the type environment.
\<close>

lemma sorts_ok_tsubst:
  "sorts_ok alg T \<Longrightarrow> (\<And>v S. (v, S) \<in> tvars T \<Longrightarrow> sorts_ok alg (\<rho> v S)) \<Longrightarrow> sorts_ok alg (tsubst \<rho> T)"
proof (induction T)
  case (Type a Ts)
  have "sorts_ok alg (tsubst \<rho> T)" if "T \<in> set Ts" for T
  proof (rule Type.IH[OF that])
    show "sorts_ok alg T" using Type.prems(1) that by simp
    fix v S assume "(v, S) \<in> tvars T"
    with that show "sorts_ok alg (\<rho> v S)" by (intro Type.prems(2)) auto
  qed
  then show ?case by simp
qed auto

lemma sorts_ok_tnorm:
  assumes ac: "tacyc \<theta>" and sc: "\<And>v S U. vt_lookup \<theta> v = Some (S, U) \<Longrightarrow> sorts_ok alg U"
    and "sorts_ok alg T"
  shows "sorts_ok alg (tnorm \<theta> T)"
proof -
  have var: "sorts_ok alg (tnorm \<theta> (TVar v S))" if "sort_ok alg S" for v S
    using that
  proof (induction v arbitrary: S rule: tdep_induct[OF ac])
    case (1 v)
    show ?case
    proof (cases "vt_lookup \<theta> v")
      case (Some b)
      obtain S0 U where b: "b = (S0, U)" by force
      have U: "sorts_ok alg U" using sc[of v S0 U] Some b by simp
      have "sorts_ok alg (tnorm \<theta> (TVar w S'))" if "(w, S') \<in> tvars U" for w S'
      proof (rule "1.IH")
        show "(w, v) \<in> tdep \<theta>" using that Some b by (force simp: tdep_def)
        show "sort_ok alg S'" using U that by (induction U) auto
      qed
      then have "sorts_ok alg (tsubst (\<lambda>w S'. tnorm \<theta> (TVar w S')) U)"
        using U by (intro sorts_ok_tsubst) auto
      then have "sorts_ok alg (tnorm \<theta> U)" unfolding tnorm_tsubst[of \<theta> U] .
      then show ?thesis using Some b by (simp add: tnorm_TVar[OF ac])
    qed (use "1.prems" in \<open>simp add: tnorm_TVar[OF ac]\<close>)
  qed
  have "sort_ok alg S" if "(v, S) \<in> tvars T" for v S using assms(3) that by (induction T) auto
  then show ?thesis by (subst tnorm_tsubst) (use var assms(3) in \<open>auto intro: sorts_ok_tsubst\<close>)
qed

lemma cert_inst_tnorm:
  assumes ac: "tacyc \<theta>" and b: "\<And>v S U. vt_lookup \<theta> v = Some (S, U) \<Longrightarrow> wft ar U \<and> sorts_ok alg U"
  shows "cert_inst (tnorm_inst \<theta>)"
  unfolding cert_inst_def cert_typ_def
proof (intro allI impI conjI)
  fix v S assume S: "sort_ok alg S"
  show "wft ar (tnorm \<theta> (TVar v S))" by (rule wft_tnorm[OF ac]) (use b in simp_all)
  show "sorts_ok alg (tnorm \<theta> (TVar v S))" by (rule sorts_ok_tnorm[OF ac]) (use b S in simp_all)
qed

lemma tsol_tnorm:
  assumes ac: "tacyc \<theta>"
  shows "tsol \<theta> (tnorm_inst \<theta>)"
  unfolding tsol_def
proof (intro allI impI)
  fix v S U assume "vt_lookup \<theta> v = Some (S, U)"
  then show "tnorm \<theta> (TVar v S) = tsubst (tnorm_inst \<theta>) U"
    by (subst tnorm_tsubst[symmetric]) (simp add: tnorm_TVar[OF ac])
qed

subsection \<open>Invariants\<close>

text \<open>
  The invariants of the termination proof hold for environments that need not have solutions.
  \<^item> \<open>einv A env\<close>: the type environment is acyclic, its type variables (and those of \<open>A\<close>) have
    unique sorts and indices at most \<^const>\<open>maxidx\<close>, and its bindings are certified; the term
    environment is acyclic, its bindings are closed and their variables are known.
  \<^item> \<open>winv env X\<close>: for every certified solution \<open>\<rho>\<close> of the type environment, the bindings are
    well-typed and the variables \<open>X\<close> of the problem are consistent (the invariants of soundness).
\<close>

definition einv :: "(indexname \<times> psort) set \<Rightarrow> (indexname \<times> psort) set \<Rightarrow> env \<Rightarrow> bool" where
  "einv A K env \<longleftrightarrow> tvinv A env \<and> scert alg (tyenv env) \<and> tcert alg (tvars_env (tyenv env) \<union> A) \<and>
    tcovered (tyenv env) K (tvars_env (tyenv env) \<union> A) \<and> acyc env \<and> closed_env env \<and> bbelow env \<and>
    tsorted alg (tyenv env)"

definition winv :: "env \<Rightarrow> (indexname \<times> ptyp) set \<Rightarrow> bool" where
  "winv env X \<longleftrightarrow> (\<forall>\<rho>. tsol (tyenv env) \<rho> \<longrightarrow> cert_inst \<rho> \<longrightarrow> wt_env \<rho> env \<and> vinv \<rho> env X)"

lemma einvD:
  assumes "einv A K env"
  shows "tvinv A env" "tinv ar (maxidx env) (tyenv env) A" "acyc env" "closed_env env" "bbelow env"
    "tacyc (tyenv env)" "tcons_env (tyenv env)"
    "vt_lookup (tyenv env) v = Some (S, U) \<Longrightarrow> sorts_ok alg U"
    "scert alg (tyenv env)" "tcert alg (tvars_env (tyenv env) \<union> A)"
    "tcovered (tyenv env) K (tvars_env (tyenv env) \<union> A)" "tsorted alg (tyenv env)"
  using assms tvinvD(1)[of A env] tinv_tacyc tinv_tcons_env unfolding einv_def scert_def by blast+

lemma winvD: "winv env X \<Longrightarrow> tsol (tyenv env) \<rho> \<Longrightarrow> cert_inst \<rho> \<Longrightarrow> wt_env \<rho> env \<and> vinv \<rho> env X"
  unfolding winv_def by blast

text \<open>The most general solution of the type environment is certified:\<close>

lemma einv_rho0:
  assumes "einv A K env"
  shows "tsol (tyenv env) (tnorm_inst (tyenv env))" "cert_inst (tnorm_inst (tyenv env))"
proof -
  note e = einvD[OF assms]
  show "tsol (tyenv env) (tnorm_inst (tyenv env))" by (rule tsol_tnorm[OF e(6)])
  show "cert_inst (tnorm_inst (tyenv env))"
    by (rule cert_inst_tnorm[OF e(6)]) (use e(2,8) tinv_wft in blast)
qed

lemma tsubst_tnorm_inst [simp]: "tsubst (tnorm_inst \<theta>) T = tnorm \<theta> T"
  by (simp flip: tnorm_tsubst)

text \<open>Hence lookups in a consistent problem do not raise exceptions.\<close>

lemma vok_winv:
  assumes "einv A K env" "winv env X" "vtvars X \<subseteq> tvars_env (tyenv env) \<union> A" "nfree env"
  shows "vok env (X \<union> evars env)"
proof -
  note e = einvD[OF assms(1)] and r0 = einv_rho0[OF assms(1)]
  have vi: "vinv (tnorm_inst (tyenv env)) env X" using winvD[OF assms(2) r0] by blast
  have "tcons (tyenv env) T \<and> (\<forall>U u. vt_lookup (tenv env) x = Some (U, u) \<longrightarrow>
      tnorm (tyenv env) T = tnorm (tyenv env) U)" if xT: "(x, T) \<in> X \<union> evars env" for x T
  proof (intro conjI allI impI)
    have "tvars T \<subseteq> tvars_env (tyenv env) \<union> A"
    proof (cases "(x, T) \<in> X")
      case True
      with assms(3) show ?thesis by (auto simp: vtvars_def)
    next
      case False
      with xT obtain y U u where yb: "vt_lookup (tenv env) y = Some (U, u)" "(x, T) = (y, U) \<or> (x, T) \<in> vars u"
        by (auto simp: evars_def bnds_def)
      moreover have "tvars T \<subseteq> ttvars u" if "(x, T) \<in> vars u" using that
        by (induction u) (auto simp: ttvars_def)
      ultimately show ?thesis using tvinvD(2)[OF e(1) yb(1)] by blast
    qed
    then show "tcons (tyenv env) T" by (rule tinv_tcons[OF e(2)])
    fix U u assume "vt_lookup (tenv env) x = Some (U, u)"
    then have "(x, U) \<in> X \<union> evars env" using evarsI[of env x U u] by blast
    moreover have "x \<notin> loose" by (rule nfreeD[OF assms(4) \<open>vt_lookup (tenv env) x = Some (U, u)\<close>])
    ultimately have "tsubst (tnorm_inst (tyenv env)) T = tsubst (tnorm_inst (tyenv env)) U"
      using xT vi unfolding vinv_def using vconsD by blast
    then show "tnorm (tyenv env) T = tnorm (tyenv env) U" by simp
  qed
  then show ?thesis unfolding vok_def by blast
qed

subsection \<open>Successful auxiliary computations\<close>

lemma size_funs: "size T \<le> size (Ts \<Rrightarrow> T)"
  by (induction Ts) auto

lemma funs_eq_length: "Ts \<Rrightarrow> T = Us \<Rrightarrow> T \<Longrightarrow> length Ts = length Us"
proof (induction Ts arbitrary: Us)
  case Nil
  show ?case
  proof (cases Us)
    case (Cons a list)
    with Nil have "size T = size (a \<rightarrow>\<^sub>T (list \<Rrightarrow> T))" by simp
    with size_funs[of T list] show ?thesis by simp
  qed simp
next
  case (Cons T' Ts)
  show ?case
  proof (cases Us)
    case Nil
    with Cons.prems have "size T = size (T' \<rightarrow>\<^sub>T (Ts \<Rrightarrow> T))" by simp
    with size_funs[of T Ts] show ?thesis by simp
  next
    case (Cons U Us')
    with Cons.prems Cons.IH[of Us'] show ?thesis by simp
  qed
qed

lemma update_ok: "vt_lookup (tenv env) F = None \<Longrightarrow> \<exists>env'. update (F, T) t env = return env'"
  by (cases env) (simp add: update_def update_new_def vt_defined_lookup)

lemma mkabs_ok: "\<forall>i\<in>set is. 0 \<le> i \<and> i < ilength bs \<Longrightarrow> mkabs bs is t = return (abs_list (map (\<lambda>i. bs ! nat_of_integer i) is) t)"
  using ok_mkabs[of bs "is" t] by (simp add: return_def)

lemma mk_ff_list_aux_ok: "length is = length js \<Longrightarrow> \<exists>ks. mk_ff_list_aux is js k = return ks"
proof (induction "is" js arbitrary: k rule: list_induct2)
  case (Cons i "is" j js)
  then obtain ks where "mk_ff_list_aux is js (k - 1) = return ks" by blast
  then show ?case by simp
qed simp

lemma mk_ff_list_ok: "length is = length js \<Longrightarrow> \<exists>ks. mk_ff_list is js = return ks"
  unfolding mk_ff_list_def by (rule mk_ff_list_aux_ok)

lemma split_type_funs: "split_type (Ts \<Rrightarrow> U) (ilength Ts) Acc = return (rev Ts @ Acc, U)"
proof (induction Ts arbitrary: Acc)
  case Nil
  then show ?case by (simp add: split_type.simps)
next
  case (Cons T Ts)
  have "ilength (T # Ts) \<noteq> 0" "ilength (T # Ts) - 1 = ilength Ts"
    by (simp_all add: ilength_eq integer_reps)
  with Cons.IH[of "T # Acc"] show ?case by (subst split_type.simps) simp
qed

lemma type_of_G_ok:
  assumes "tacyc (tyenv env)" "tcons_env (tyenv env)" "tcons (tyenv env) Fty"
    and "tnorm (tyenv env) Fty = Ts \<Rrightarrow> U" "\<forall>k\<in>set ks. 0 \<le> k \<and> k < ilength Ts"
  shows "\<exists>Gty. type_of_G env Fty (ilength Ts) ks = return Gty"
proof -
  have "\<exists>y. nth (rev Ts) k = return y" if "k \<in> set ks" for k
    using assms(5) that ok_nth[of "rev Ts" k] by (auto simp: return_def)
  then obtain Us where us: "mapM (nth (rev Ts)) ks = return Us" using mapM_return by blast
  have nt: "norm_type (tyenv env) Fty = return (Ts \<Rrightarrow> U)" using norm_type_ok[OF assms(1-3)] assms(4) by simp
  have st: "split_type (Ts \<Rrightarrow> U) (ilength Ts) [] = return (rev Ts, U)" using split_type_funs[of Ts U "[]"] by simp
  have "type_of_G env Fty (ilength Ts) ks = return (Us \<Rrightarrow> U)"
    unfolding type_of_G_def by (simp only: nt st us bindM_simps prod.case)
  then show ?thesis by blast
qed

subsection \<open>New type variables\<close>

text \<open>
  From \<open>env\<close> with the known type variables \<open>A\<close> to \<open>env'\<close> with the known type variables \<open>A'\<close>,
  only type variables that are known or have indices above the maximal index of \<open>env\<close> are
  introduced:
\<close>

definition tnew :: "(indexname \<times> psort) set \<Rightarrow> env \<Rightarrow> (indexname \<times> psort) set \<Rightarrow> env \<Rightarrow> bool" where
  "tnew A env A' env' \<longleftrightarrow>
    tvars_env (tyenv env') \<union> A' \<subseteq> tvars_env (tyenv env) \<union> A \<union> {p. maxidx env < snd (fst p)}"

lemma tnew_refl [simp]: "tnew A env A env"
  by (auto simp: tnew_def)

lemma tnew_trans:
  assumes "tnew A env A1 env1" "tnew A1 env1 A2 env2" "maxidx env \<le> maxidx env1"
  shows "tnew A env A2 env2"
  using assms unfolding tnew_def by fastforce

lemma tnew_tyenv: "tyenv env' = tyenv env \<Longrightarrow> A' \<subseteq> A \<Longrightarrow> tnew A env A' env'"
  by (auto simp: tnew_def)

lemma tnewD: "tnew A env A' env' \<Longrightarrow> tvars_env (tyenv env') \<subseteq> tvars_env (tyenv env) \<union> A \<union> {p. maxidx env < snd (fst p)}"
  by (auto simp: tnew_def)

subsection \<open>Type unification\<close>

lemma unify_types_term:
  assumes ei: "einv A K env" and fin: "finite K"
    and T: "tvars T \<subseteq> tvars_env (tyenv env) \<union> A" "wft ar T" "sorts_ok alg T"
    and U: "tvars U \<subseteq> tvars_env (tyenv env) \<union> A" "wft ar U" "sorts_ok alg U"
  shows "(\<exists>env'. unify_types alg T U env = return env' \<and> einv A K env' \<and> tenv env' = tenv env \<and>
      textends (tyenv env) (tyenv env') \<and> maxidx env \<le> maxidx env' \<and>
      tvars_env (tyenv env) \<subseteq> tvars_env (tyenv env') \<and> tnew A env A env' \<and>
      (\<forall>\<rho>. tsol (tyenv env') \<rho> \<longrightarrow> tsubst \<rho> T = tsubst \<rho> U) \<and>
      (tyenv env' = tyenv env \<or> card (uvarsA (tyenv env') K) < card (uvarsA (tyenv env) K))) \<or>
    (\<exists>u. unify_types alg T U env = raise (Unif u))"
proof (cases "T = U")
  case True
  then show ?thesis using ei by (simp add: unify_types_def)
next
  case False
  note e = einvD[OF ei]
  note ua = unify_aux_ok[OF e(2) U(1) T(1) U(2) T(2)]
  from ua show ?thesis
  proof (elim disjE exE conjE)
    fix \<theta>' n' assume r: "unify_aux alg U T (tyenv env, maxidx env) = return (\<theta>', n')"
      and st: "tstep alg ar A (\<lambda>\<rho>. tsubst \<rho> U = tsubst \<rho> T) (tyenv env) (maxidx env) \<theta>' n'"
      and sol: "\<forall>\<rho>. tsol \<theta>' \<rho> \<longrightarrow> tsubst \<rho> U = tsubst \<rho> T"
    let ?env' = "Envir n' (tenv env) \<theta>'"
    have r': "unify_types alg T U env = return ?env'"
      using False r by (simp add: unify_types_def type_unify_def)
    note s = tstepD[OF st]
    have tv: "tvars_env (tyenv env) \<subseteq> tvars_env \<theta>'" by (rule tvars_env_textends[OF s(1)])
    have ac': "tacyc \<theta>'" by (rule tinv_tacyc[OF s(3)])
    have cov: "tcovered (tyenv env) K (tvars_env (tyenv env) \<union> tvars U \<union> tvars T)"
      by (rule tcovered_mono[OF e(11)]) (use T U in blast)
    have "tvinv A ?env'"
      unfolding tvinv_def using s(3) tvinvD(2)[OF e(1)] tv by fastforce
    moreover have "scert alg \<theta>'"
      by (rule unify_aux_scert[OF e(2) U(1) T(1) U(2) T(2) e(9) U(3) T(3) e(10) r])
    moreover have "tcert alg (tvars_env \<theta>' \<union> A)" using s(6)[OF e(10)] e(10) by simp
    moreover have "tcovered \<theta>' K (tvars_env \<theta>' \<union> A)"
    proof -
      have "tcovered \<theta>' K (tvars_env \<theta>')" by (rule unify_aux_covered[OF e(2) U(1) T(1) U(2) T(2) cov r])
      moreover have "tcovered \<theta>' K A" by (rule tcovered_textends[OF ac' s(1)]) (use e(11) in simp)
      ultimately show ?thesis by simp
    qed
    moreover have "bbelow ?env'" by (rule bbelow_mono[OF e(5)]) (use s(2) in simp_all)
    moreover have "tsorted alg \<theta>'" by (rule tsorted_tstep[OF e(12) st])
    ultimately have "einv A K ?env'" using e(3,4) by (simp add: einv_def acyc_def dep_def closed_env_def)
    moreover have "\<theta>' = tyenv env \<or> card (uvarsA \<theta>' K) < card (uvarsA (tyenv env) K)"
      by (rule unify_aux_card[OF e(2) U(1) T(1) U(2) T(2) fin cov r])
    moreover have "tnew A env A ?env'" using s(7) by (auto simp: tnew_def)
    ultimately show ?thesis using r' s(1,2) tv sol by auto
  next
    assume "unify_aux alg U T (tyenv env, maxidx env) = raise TUnify"
    then show ?thesis using False by (simp add: unify_types_def type_unify_def)
  qed
qed

end

subsection \<open>Without loose names\<close>

context pure_sig
begin

lemma vok_winv:
  assumes "einv A K env" "winv env X" "vtvars X \<subseteq> tvars_env (tyenv env) \<union> A"
  shows "vok env (X \<union> evars env)"
  by (rule vok_winv[OF assms nfree0])

end

end

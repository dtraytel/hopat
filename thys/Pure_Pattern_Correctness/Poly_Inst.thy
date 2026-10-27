section \<open>Type Instances of Unification Problems\<close>

theory Poly_Inst
  imports Pattern_Correctness Type_Mgu
begin

text \<open>
  A polymorphic unification problem is related to its \<^emph>\<open>instances\<close>: the monomorphic problems
  obtained by instantiating the type variables by a type instantiation \<open>\<rho>\<close>, which drops the type
  environment. We show that the functions used by \<^const>\<open>unify\<close>, except for type unification,
  commute with instantiation: on the instance they compute the instance of the result, or raise
  an exception of the same kind.
\<close>


subsection \<open>Instances\<close>

fun inst :: "tinst \<Rightarrow> pterm \<Rightarrow> pterm" where
  "inst \<rho> (Const a T) = Const a (tsubst \<rho> T)"
| "inst \<rho> (Free a T) = Free a (tsubst \<rho> T)"
| "inst \<rho> (Var x T) = Var x (tsubst \<rho> T)"
| "inst \<rho> (Bound i) = Bound i"
| "inst \<rho> (Abs a T t) = Abs a (tsubst \<rho> T) (inst \<rho> t)"
| "inst \<rho> (s $ t) = inst \<rho> s $ inst \<rho> t"

definition instb :: "tinst \<Rightarrow> binders \<Rightarrow> binders" where
  "instb \<rho> bs = map (\<lambda>(a, T). (a, tsubst \<rho> T)) bs"

lift_definition vt_map :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a vartab \<Rightarrow> 'b vartab" is "\<lambda>f m. map_option f \<circ> m"
  by simp

lemma vt_lookup_map[simp]: "vt_lookup (vt_map f t) k = map_option f (vt_lookup t k)"
  by transfer simp

definition instE :: "tinst \<Rightarrow> env \<Rightarrow> env" where
  "instE \<rho> env = Envir (maxidx env) (vt_map (\<lambda>(U, u). (tsubst \<rho> U, inst \<rho> u)) (tenv env)) vt_empty"

lemma instE_simps[simp]:
  "maxidx (instE \<rho> env) = maxidx env" "tyenv (instE \<rho> env) = vt_empty"
  "vt_lookup (tenv (instE \<rho> env)) x = map_option (\<lambda>(U, u). (tsubst \<rho> U, inst \<rho> u)) (vt_lookup (tenv env) x)"
  by (simp_all add: instE_def)

lemma vt_is_empty_empty[simp]: "vt_is_empty vt_empty"
  by transfer simp

lemma instb_simps[simp]: "instb \<rho> [] = []" "instb \<rho> ((a, T) # bs) = (a, tsubst \<rho> T) # instb \<rho> bs"
  "length (instb \<rho> bs) = length bs" "map snd (instb \<rho> bs) = map (tsubst \<rho>) (map snd bs)"
  by (simp_all add: instb_def case_prod_beta)


subsection \<open>Structure of instances\<close>

lemma inst_simps[simp]:
  "is_Abs (inst \<rho> t) \<longleftrightarrow> is_Abs t" "is_Var (inst \<rho> t) \<longleftrightarrow> is_Var t" "is_Bound (inst \<rho> t) \<longleftrightarrow> is_Bound t"
  "proper (inst \<rho> t) \<longleftrightarrow> proper t" "vars (inst \<rho> t) = vars t"
  by (induction t) auto

lemma below_inst[simp]: "below m (inst \<rho> t) \<longleftrightarrow> below m t"
  by (simp add: below_def)

lemma vps_inst: "vps (inst \<rho> t) = (\<lambda>(x, T). (x, tsubst \<rho> T)) ` vps t"
  by (induction t) auto

lemma inst_incr_bv: "inst \<rho> (incr_bv inc lev t) = incr_bv inc lev (inst \<rho> t)"
  by (induction inc lev t rule: incr_bv.induct) auto

lemma inst_subst_bound_aux: "inst \<rho> (subst_bound_aux arg lev t) = subst_bound_aux (inst \<rho> arg) lev (inst \<rho> t)"
  by (induction arg lev t rule: subst_bound_aux.induct) (auto simp: incr_boundvars_def inst_incr_bv)

lemma inst_subst_bound: "inst \<rho> (subst_bound arg t) = subst_bound (inst \<rho> arg) (inst \<rho> t)"
  by (simp add: subst_bound_def inst_subst_bound_aux)

lemma inst_incr_aux: "inst \<rho> (incr_aux d t) = incr_aux d (inst \<rho> t)"
  by (induction d t rule: incr_aux.induct) auto

lemma inst_incr: "inst \<rho> (incr t) = incr (inst \<rho> t)"
  by (simp add: incr_def inst_incr_aux)

lemma inst_list_comb: "inst \<rho> (list_comb h ts) = list_comb (inst \<rho> h) (map (inst \<rho>) ts)"
  by (induction ts arbitrary: h) (auto simp: list_comb_def)

lemma inst_app: "inst \<rho> (app s is) = app (inst \<rho> s) is"
  by (induction "is" arbitrary: s) (auto simp: app_def)

lemma strip_comb_acc_inst:
  "strip_comb_acc (inst \<rho> t) (map (inst \<rho>) ts) = (inst \<rho> (fst (strip_comb_acc t ts)), map (inst \<rho>) (snd (strip_comb_acc t ts)))"
  by (induction t ts rule: strip_comb_acc.induct) auto

lemma strip_comb_inst:
  "strip_comb (inst \<rho> t) = (inst \<rho> (fst (strip_comb t)), map (inst \<rho>) (snd (strip_comb t)))"
  using strip_comb_acc_inst[of \<rho> t "[]"] by (simp add: strip_comb_def)

lemma no_loose_bound_inst[simp]: "no_loose_bound (tr (inst \<rho> t)) n \<longleftrightarrow> no_loose_bound (tr t) n"
  by (induction t arbitrary: n) auto


subsection \<open>Instances of results\<close>

text \<open>Exceptions carry terms and types; they are instantiated, too.\<close>

fun instu :: "tinst \<Rightarrow> unif_trace \<Rightarrow> unif_trace" where
  "instu \<rho> (Typ_Clash tye T U) = Typ_Clash vt_empty (tsubst \<rho> T) (tsubst \<rho> U)"
| "instu \<rho> (Clash_BB bs i j) = Clash_BB (instb \<rho> bs) i j"
| "instu \<rho> (Clash_B bs i a) = Clash_B (instb \<rho> bs) i a"
| "instu \<rho> (Proj_Fail env bs F is t) = Proj_Fail (instE \<rho> env) (instb \<rho> bs) F is (inst \<rho> t)"
| "instu \<rho> (Ocheck_Fail F t bs env) = Ocheck_Fail F (inst \<rho> t) (instb \<rho> bs) (instE \<rho> env)"
| "instu \<rho> u = u"

fun instx :: "tinst \<Rightarrow> exn \<Rightarrow> exn" where
  "instx \<rho> (Unif u) = Unif (instu \<rho> u)"
| "instx \<rho> (Type_Error s Ts ts) = Type_Error s (map (tsubst \<rho>) Ts) (map (inst \<rho>) ts)"
| "instx \<rho> (Term_Error s ts) = Term_Error s (map (inst \<rho>) ts)"
| "instx \<rho> e = e"

fun instr :: "tinst \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> 'a res \<Rightarrow> 'b res" where
  "instr \<rho> f (Ok x) = Ok (f x)"
| "instr \<rho> f (Err e) = Err (instx \<rho> e)"

lemma instr_ident[simp]: "instr \<rho> (\<lambda>a. a) r = instr \<rho> id r"
  by (simp add: id_def)

definition instM :: "tinst \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> 'a M \<Rightarrow> 'b M" where
  "instM \<rho> f m = map_option (instr \<rho> f) m"

lemma instM_simps[simp]:
  "instM \<rho> f (return x) = return (f x)" "instM \<rho> f (raise e) = raise (instx \<rho> e)"
  "instM \<rho> f None = None" "instM \<rho> f (Some (Ok x)) = Some (Ok (f x))"
  "instM \<rho> f (Some (Err e)) = Some (Err (instx \<rho> e))"
  by (simp_all add: instM_def return_def raise_def)

lemma bindM_Some_simps[simp]:
  "bindM (Some (Ok x)) f = f x" "bindM (Some (Err e)) f = Some (Err e)"
  by (simp_all add: bindM_def)

lemma instx_kinds[simp]:
  "instx \<rho> e = Pattern \<longleftrightarrow> e = Pattern" "(\<exists>u. instx \<rho> e = Unif u) \<longleftrightarrow> (\<exists>u. e = Unif u)"
  by (cases e; simp)+

lemma bindM_instM:
  assumes "\<And>x. m = Some (Ok x) \<Longrightarrow> g (f x) = instM \<rho> h (k x)"
  shows "bindM (instM \<rho> f m) g = instM \<rho> h (bindM m k)"
  using assms by (auto simp: bindM_def instM_def split: option.splits res.splits)

lemma handle_instM:
  assumes "\<And>e. m = Some (Err e) \<Longrightarrow> h' (instx \<rho> e) = instM \<rho> f (h e)"
  shows "handle (instM \<rho> f m) h' = instM \<rho> f (handle m h)"
  using assms by (auto simp: handle_def instM_def split: option.splits res.splits)

lemma instM_cong: "m = m' \<Longrightarrow> (\<And>x. m' = Some (Ok x) \<Longrightarrow> f x = g x) \<Longrightarrow> instM \<rho> f m = instM \<rho> g m'"
  unfolding instM_def by (cases m'; cases "the m'") auto

lemma instM_comp: "instM \<rho> f (instM \<rho>' g m) = instM \<rho> (f \<circ> g) m" if "\<And>e. instx \<rho> (instx \<rho>' e) = instx \<rho> e"
  unfolding instM_def by (cases m; cases "the m") (auto simp: that)

lemma mapM_instM:
  assumes "\<And>x. x \<in> set xs \<Longrightarrow> g (F x) = instM \<rho> G (f x)"
  shows "mapM g (map F xs) = instM \<rho> (map G) (mapM f xs)"
  using assms
proof (induction xs)
  case (Cons x xs)
  have 1: "g (F x) = instM \<rho> G (f x)" and 2: "mapM g (map F xs) = instM \<rho> (map G) (mapM f xs)"
    using Cons by simp_all
  show ?case
    by (simp only: list.map mapM.simps 1 2) (rule bindM_instM, rule bindM_instM, simp)
qed simp

lemma existsM_instM:
  assumes "\<And>x. x \<in> set xs \<Longrightarrow> g (F x) = instM \<rho> id (f x)"
  shows "existsM g (map F xs) = instM \<rho> id (existsM f xs)"
  using assms
proof (induction xs)
  case (Cons x xs)
  then show ?case by (simp, intro bindM_instM) (auto simp: return_def instM_def)
qed (simp add: return_def instM_def)

lemma foldM_instM:
  assumes "\<And>x b. x \<in> set xs \<Longrightarrow> P b \<Longrightarrow> g (F x) (H b) = instM \<rho> H (f x b) \<and>
      (\<forall>b'. f x b = Some (Ok b') \<longrightarrow> P b')"
    and "P b"
  shows "foldM g (map F xs) (H b) = instM \<rho> H (foldM f xs b)"
  using assms
proof (induction xs arbitrary: b)
  case (Cons x xs)
  have 1: "g (F x) (H b) = instM \<rho> H (f x b)" using Cons.prems by simp
  show ?case
  proof (simp only: list.map foldM.simps 1, rule bindM_instM)
    fix b' assume b': "f x b = Some (Ok b')"
    then have "P b'" using Cons.prems(1)[of x b] Cons.prems(2) by simp
    then show "foldM g (map F xs) (H b') = instM \<rho> H (foldM f xs b')"
      by (rule Cons.IH[rotated]) (use Cons.prems(1) in auto)
  qed
qed simp


subsection \<open>Lookup and head normalisation\<close>

text \<open>
  The instance decides the lookup of a variable occurrence as the original problem does if the
  types are equal modulo the type environment exactly if their instances are equal.
\<close>

definition lkdec :: "tinst \<Rightarrow> env \<Rightarrow> (indexname \<times> ptyp) set \<Rightarrow> bool" where
  "lkdec \<rho> env X \<longleftrightarrow> (\<forall>x T. (x, T) \<in> X \<longrightarrow> tcons (tyenv env) T \<and> (\<forall>U u. vt_lookup (tenv env) x = Some (U, u) \<longrightarrow>
    tcons (tyenv env) U \<and> (tnorm (tyenv env) T = tnorm (tyenv env) U \<longleftrightarrow> tsubst \<rho> T = tsubst \<rho> U)))"

definition bvps :: "env \<Rightarrow> (indexname \<times> ptyp) set" where
  "bvps env = {p. \<exists>x U u. vt_lookup (tenv env) x = Some (U, u) \<and> p \<in> vps u}"

lemma lkdec_mono: "lkdec \<rho> env X \<Longrightarrow> Y \<subseteq> X \<Longrightarrow> lkdec \<rho> env Y"
  by (auto simp: lkdec_def)

lemma bvpsI: "vt_lookup (tenv env) x = Some (U, u) \<Longrightarrow> vps u \<subseteq> bvps env"
  unfolding bvps_def by blast

definition tyok :: "env \<Rightarrow> bool" where
  "tyok env \<longleftrightarrow> tacyc (tyenv env) \<and> tcons_env (tyenv env)"

lemma lookup_inst:
  assumes ok: "tyok env" and d: "lkdec \<rho> env {(x, T)}"
  shows "lookup (instE \<rho> env) x (tsubst \<rho> T) = instM \<rho> (map_option (inst \<rho>)) (lookup env x T)"
proof (cases "vt_lookup (tenv env) x")
  case (Some p)
  obtain U u where p: "p = (U, u)" by force
  from d Some p have tc: "tcons (tyenv env) T" "tcons (tyenv env) U"
    and eq: "tnorm (tyenv env) T = tnorm (tyenv env) U \<longleftrightarrow> tsubst \<rho> T = tsubst \<rho> U"
    by (auto simp: lkdec_def)
  have "unified (tyenv env) T U = return (tnorm (tyenv env) T = tnorm (tyenv env) U)"
    using unified_ok ok tc by (simp add: tyok_def)
  then show ?thesis using Some p eq
    by (simp add: lookup_def unified_def var_clash_def)
qed (simp add: lookup_def)

lemma lookup_SomeD: "lookup env x T = Some (Ok (Some u)) \<Longrightarrow> \<exists>U. vt_lookup (tenv env) x = Some (U, u)"
  by (auto simp: lookup_def bindM_def return_def raise_def var_clash_def
      split: option.splits if_splits res.splits)

lemma head_norm_inst1:
  assumes "head_norm env t = Some r"
  shows "tyok env \<Longrightarrow> lkdec \<rho> env (vps t \<union> bvps env) \<Longrightarrow>
    head_norm (instE \<rho> env) (inst \<rho> t) = Some (instr \<rho> (inst \<rho>) r) \<and>
    (\<forall>t'. r = Ok t' \<longrightarrow> vps t' \<subseteq> vps t \<union> bvps env)"
  using assms
proof (induction env t r rule: head_norm.raw_induct[rotated, consumes 1])
  case (1 hn env t r)
  note ok = "1.prems"(1) and d = "1.prems"(2)
  show ?case
  proof (cases t)
    case (Var xi T)
    from "1.hyps" Var obtain lr where lr: "lookup env xi T = Some lr"
      by (cases "lookup env xi T") (auto simp: bindM_def)
    have lk: "lookup (instE \<rho> env) xi (tsubst \<rho> T) = instM \<rho> (map_option (inst \<rho>)) (lookup env xi T)"
      by (rule lookup_inst[OF ok lkdec_mono[OF d]]) (simp add: Var)
    have hi: "head_norm (instE \<rho> env) (inst \<rho> t) = bindM (lookup (instE \<rho> env) xi (tsubst \<rho> T))
        (\<lambda>r. case r of None \<Rightarrow> return (inst \<rho> t) | Some u \<Rightarrow> head_norm (instE \<rho> env) u)"
      by (subst head_norm.simps) (simp add: Var)
    show ?thesis
    proof (cases lr)
      case (Ok ro)
      show ?thesis
      proof (cases ro)
        case None
        then show ?thesis using "1.hyps" Var lr Ok hi lk by (auto simp: return_def)
      next
        case (Some u)
        from lr Ok Some obtain U where b: "vt_lookup (tenv env) xi = Some (U, u)"
          using lookup_SomeD by blast
        from "1.hyps" Var lr Ok Some have hu: "hn env u = Some r" by simp
        have "vps u \<subseteq> bvps env" by (rule bvpsI[OF b])
        with "1.IH"[OF hu ok lkdec_mono[OF d]] have
          "head_norm (instE \<rho> env) (inst \<rho> u) = Some (instr \<rho> (inst \<rho>) r)"
          "\<forall>t'. r = Ok t' \<longrightarrow> vps t' \<subseteq> vps t \<union> bvps env"
          by auto
        then show ?thesis using hi lk lr Ok Some by simp
      qed
    next
      case (Err e)
      then show ?thesis using "1.hyps" Var lr hi lk by auto
    qed
  next
    case (Abs a T body)
    from "1.hyps" Abs obtain rb where hb: "hn env body = Some rb"
      by (cases "hn env body") (auto simp: bindM_def)
    with "1.hyps" Abs have r: "r = (case rb of Ok b \<Rightarrow> Ok (pterm.Abs a T b) | Err e \<Rightarrow> Err e)"
      by (cases rb) (auto simp: bindM_def return_def)
    have "vps body \<union> bvps env \<subseteq> vps t \<union> bvps env" using Abs by auto
    note IH = "1.IH"[OF hb ok lkdec_mono[OF d this]]
    show ?thesis using IH Abs r
      by (subst head_norm.simps) (cases rb; auto simp: bindM_def return_def)
  next
    case (App f u)
    show ?thesis
    proof (cases "is_Abs f")
      case True
      then obtain a T body where f: "f = pterm.Abs a T body" by (cases f) auto
      from "1.hyps" App f have h: "hn env (subst_bound u body) = Some r" by simp
      have sub: "vps (subst_bound u body) \<union> bvps env \<subseteq> vps t \<union> bvps env"
        using vps_subst_bound[of u body] App f by auto
      note IH = "1.IH"[OF h ok lkdec_mono[OF d sub]]
      have "head_norm (instE \<rho> env) (inst \<rho> t) = head_norm (instE \<rho> env) (inst \<rho> (subst_bound u body))"
        by (subst head_norm.simps) (simp add: App f inst_subst_bound)
      then show ?thesis using IH sub by auto
    next
      case False
      have h: "bindM (hn env f) (\<lambda>nf. case nf of pterm.Abs _ _ body \<Rightarrow> hn env (subst_bound u body)
          | _ \<Rightarrow> return (nf $ u)) = Some r"
        using "1.hyps" App False by (cases f) auto
      then obtain rf where hf: "hn env f = Some rf" by (cases "hn env f") (auto simp: bindM_def)
      have subf: "vps f \<union> bvps env \<subseteq> vps t \<union> bvps env" using App by auto
      note IHf = "1.IH"[OF hf ok lkdec_mono[OF d subf]]
      have hi: "head_norm (instE \<rho> env) (inst \<rho> t) = bindM (head_norm (instE \<rho> env) (inst \<rho> f))
          (\<lambda>nf. case nf of pterm.Abs _ _ body \<Rightarrow> head_norm (instE \<rho> env) (subst_bound (inst \<rho> u) body)
            | _ \<Rightarrow> return (nf $ inst \<rho> u))"
        using False by (subst head_norm.simps) (cases f; simp add: App)
      show ?thesis
      proof (cases rf)
        case (Ok nf)
        have vnf: "vps nf \<subseteq> vps t \<union> bvps env" using IHf Ok subf by auto
        show ?thesis
        proof (cases "is_Abs nf")
          case True
          then obtain a T body where nf: "nf = pterm.Abs a T body" by (cases nf) auto
          from h hf Ok nf have h2: "hn env (subst_bound u body) = Some r" by simp
          have sub: "vps (subst_bound u body) \<union> bvps env \<subseteq> vps t \<union> bvps env"
            using vps_subst_bound[of u body] App vnf nf by auto
          note IH = "1.IH"[OF h2 ok lkdec_mono[OF d sub]]
          show ?thesis using hi IHf Ok nf IH sub by (simp add: inst_subst_bound) blast
        next
          case nA: False
          from h hf Ok nA have r: "r = Ok (nf $ u)" by (cases nf) (auto simp: return_def)
          show ?thesis using hi IHf Ok nA r vnf App by (cases nf) (auto simp: return_def)
        qed
      next
        case (Err e)
        then show ?thesis using h hf hi IHf by auto
      qed
    qed
  qed (use "1.hyps" in \<open>subst head_norm.simps; auto simp: return_def\<close>)+
qed

lemma head_norm_inst2:
  assumes "head_norm env' t' = Some r'"
  shows "env' = instE \<rho> env \<Longrightarrow> t' = inst \<rho> t \<Longrightarrow> tyok env \<Longrightarrow> lkdec \<rho> env (vps t \<union> bvps env) \<Longrightarrow>
    \<exists>r. head_norm env t = Some r \<and> r' = instr \<rho> (inst \<rho>) r"
  using assms
proof (induction env' t' r' arbitrary: t rule: head_norm.raw_induct[rotated, consumes 1])
  case (1 hn env' t' r' t)
  note e = "1.prems"(1) and tt = "1.prems"(2) and ok = "1.prems"(3) and d = "1.prems"(4)
  show ?case
  proof (cases t)
    case (Var xi T)
    have lk: "lookup env' xi (tsubst \<rho> T) = instM \<rho> (map_option (inst \<rho>)) (lookup env xi T)"
      unfolding e by (rule lookup_inst[OF ok lkdec_mono[OF d]]) (simp add: Var)
    from "1.hyps" tt Var lk obtain lr where lr: "lookup env xi T = Some lr"
      by (cases "lookup env xi T") (auto simp: instM_def)
    have hp: "head_norm env t = bindM (lookup env xi T)
        (\<lambda>r. case r of None \<Rightarrow> return t | Some u \<Rightarrow> head_norm env u)"
      by (subst head_norm.simps) (simp add: Var)
    show ?thesis
    proof (cases "lr = Ok None \<or> (\<exists>e. lr = Err e)")
      case True
      then show ?thesis using "1.hyps" tt Var lk hp lr by (auto simp: return_def)
    next
      case False
      then obtain u where lu: "lr = Ok (Some u)" by (cases lr) auto
      from lr lu obtain U where b: "vt_lookup (tenv env) xi = Some (U, u)" using lookup_SomeD by blast
      from "1.hyps" tt Var lk lr lu have hu: "hn env' (inst \<rho> u) = Some r'" by simp
      have "vps u \<union> bvps env \<subseteq> vps t \<union> bvps env" using bvpsI[OF b] by auto
      from "1.IH"[OF hu e refl ok lkdec_mono[OF d this]] show ?thesis using hp lr lu by simp
    qed
  next
    case (Abs a T body)
    from "1.hyps" tt Abs obtain rb where hb: "hn env' (inst \<rho> body) = Some rb"
      by (cases "hn env' (inst \<rho> body)") auto
    with "1.hyps" tt Abs have r': "r' = (case rb of Ok b \<Rightarrow> Ok (pterm.Abs a (tsubst \<rho> T) b) | Err e \<Rightarrow> Err e)"
      by (cases rb) (auto simp: return_def)
    have "vps body \<union> bvps env \<subseteq> vps t \<union> bvps env" using Abs by auto
    from "1.IH"[OF hb e refl ok lkdec_mono[OF d this]] obtain r where
      r: "head_norm env body = Some r" "rb = instr \<rho> (inst \<rho>) r" by blast
    show ?thesis using Abs r r' by (subst head_norm.simps) (cases r; auto simp: return_def)
  next
    case (App f u)
    show ?thesis
    proof (cases "is_Abs f")
      case True
      then obtain a T body where f: "f = pterm.Abs a T body" by (cases f) auto
      from "1.hyps" tt App f have h: "hn env' (inst \<rho> (subst_bound u body)) = Some r'"
        by (simp add: inst_subst_bound)
      have "vps (subst_bound u body) \<union> bvps env \<subseteq> vps t \<union> bvps env"
        using vps_subst_bound[of u body] App f by auto
      from "1.IH"[OF h e refl ok lkdec_mono[OF d this]] show ?thesis
        by (subst head_norm.simps) (simp add: App f)
    next
      case False
      have h: "bindM (hn env' (inst \<rho> f)) (\<lambda>nf. case nf of pterm.Abs _ _ body \<Rightarrow> hn env' (subst_bound (inst \<rho> u) body)
          | _ \<Rightarrow> return (nf $ inst \<rho> u)) = Some r'"
        using "1.hyps" tt App False by (cases f) auto
      then obtain rf where hf: "hn env' (inst \<rho> f) = Some rf" by (cases "hn env' (inst \<rho> f)") auto
      have subf: "vps f \<union> bvps env \<subseteq> vps t \<union> bvps env" using App by auto
      from "1.IH"[OF hf e refl ok lkdec_mono[OF d subf]] obtain rpf where
        pf: "head_norm env f = Some rpf" and rf: "rf = instr \<rho> (inst \<rho>) rpf" by blast
      have hp: "head_norm env t = bindM (head_norm env f) (\<lambda>nf. case nf of
          pterm.Abs _ _ body \<Rightarrow> head_norm env (subst_bound u body) | _ \<Rightarrow> return (nf $ u))"
        using False by (subst head_norm.simps) (cases f; simp add: App)
      show ?thesis
      proof (cases rpf)
        case (Ok nf)
        show ?thesis
        proof (cases "is_Abs nf")
          case True
          then obtain a T body where nf: "nf = pterm.Abs a T body" by (cases nf) auto
          from h hf rf Ok nf have h2: "hn env' (inst \<rho> (subst_bound u body)) = Some r'"
            by (simp add: inst_subst_bound)
          have "vps nf \<subseteq> vps f \<union> bvps env" using head_norm_inst1[OF pf ok lkdec_mono[OF d subf]] Ok by auto
          then have "vps (subst_bound u body) \<union> bvps env \<subseteq> vps t \<union> bvps env"
            using vps_subst_bound[of u body] App nf by auto
          from "1.IH"[OF h2 e refl ok lkdec_mono[OF d this]] show ?thesis using hp pf Ok nf by simp
        next
          case nA: False
          then show ?thesis using h hf rf hp pf Ok by (cases nf) (auto simp: return_def)
        qed
      qed (use h hf rf hp pf in simp)
    qed
  qed (use "1.hyps" tt in \<open>subst head_norm.simps; auto simp: return_def\<close>)+
qed
lemma head_norm_inst:
  assumes "tyok env" "lkdec \<rho> env (vps t \<union> bvps env)"
  shows "head_norm (instE \<rho> env) (inst \<rho> t) = instM \<rho> (inst \<rho>) (head_norm env t)"
proof (cases "head_norm env t")
  case None
  show ?thesis
  proof (cases "head_norm (instE \<rho> env) (inst \<rho> t)")
    case (Some r')
    from head_norm_inst2[OF Some refl refl assms] None show ?thesis by simp
  qed (simp add: None)
next
  case (Some r)
  then show ?thesis using head_norm_inst1[OF Some assms] by (simp add: instM_def)
qed

lemma lkdec_Un: "lkdec \<rho> env (X \<union> Y) \<longleftrightarrow> lkdec \<rho> env X \<and> lkdec \<rho> env Y"
  by (auto simp: lkdec_def)

lemma lkdec_UN: "lkdec \<rho> env (\<Union>(f ` A)) \<longleftrightarrow> (\<forall>a\<in>A. lkdec \<rho> env (f a))"
  unfolding lkdec_def by blast


subsection \<open>Lists of bound variables\<close>

lemma ints_of_inst: "ints_of (map (inst \<rho>) ts) = ints_of ts"
  by (induction ts rule: ints_of.induct) auto

lemma instM_ints_of: "instM \<rho> id (ints_of ts) = ints_of ts"
  by (induction ts rule: ints_of.induct)
    (auto simp: bindM_def instM_def return_def raise_def split: option.splits res.splits)

lemma ints_of'_inst:
  assumes "tyok env" "\<forall>t\<in>set ts. lkdec \<rho> env (vps t \<union> bvps env)"
  shows "ints_of' (instE \<rho> env) (map (inst \<rho>) ts) = instM \<rho> id (ints_of' env ts)"
proof -
  have "mapM (head_norm (instE \<rho> env)) (map (inst \<rho>) ts) = instM \<rho> (map (inst \<rho>)) (mapM (head_norm env) ts)"
    by (rule mapM_instM) (use head_norm_inst assms in blast)
  then show ?thesis unfolding ints_of'_def
    by (simp only:, intro bindM_instM) (simp add: ints_of_inst instM_ints_of)
qed


subsection \<open>The occurs check\<close>

lemma occurs_inst1:
  assumes "occurs F t env = Some r"
  shows "tyok env \<Longrightarrow> lkdec \<rho> env (vps t \<union> bvps env) \<Longrightarrow>
    occurs F (inst \<rho> t) (instE \<rho> env) = Some (instr \<rho> id r)"
  using assms
proof (induction F t env r rule: occurs.raw_induct[rotated, consumes 1])
  case (1 oc F t env r)
  note ok = "1.prems"(1) and d = "1.prems"(2)
  show ?case
  proof (cases t)
    case (Var G T)
    have lk: "lookup (instE \<rho> env) G (tsubst \<rho> T) = instM \<rho> (map_option (inst \<rho>)) (lookup env G T)"
      by (rule lookup_inst[OF ok lkdec_mono[OF d]]) (simp add: Var)
    from "1.hyps" Var obtain lr where lr: "lookup env G T = Some lr"
      by (cases "lookup env G T") auto
    have hi: "occurs F (inst \<rho> t) (instE \<rho> env) = bindM (lookup (instE \<rho> env) G (tsubst \<rho> T))
        (\<lambda>r. case r of Some u \<Rightarrow> occurs F u (instE \<rho> env) | None \<Rightarrow> return (F = G))"
      by (subst occurs.simps) (simp add: Var)
    show ?thesis
    proof (cases "lr = Ok None \<or> (\<exists>e. lr = Err e)")
      case True
      then show ?thesis using "1.hyps" Var lr hi lk by (auto simp: return_def)
    next
      case False
      then obtain u where lu: "lr = Ok (Some u)" by (cases lr) auto
      from lr lu obtain U where b: "vt_lookup (tenv env) G = Some (U, u)" using lookup_SomeD by blast
      from "1.hyps" Var lr lu have hu: "oc F u env = Some r" by simp
      have "vps u \<union> bvps env \<subseteq> vps t \<union> bvps env" using bvpsI[OF b] by auto
      from "1.IH"[OF hu ok lkdec_mono[OF d this]] show ?thesis using hi lk lr lu by simp
    qed
  next
    case (App t1 t2)
    from "1.hyps" App obtain r1 where h1: "oc F t1 env = Some r1" by (cases "oc F t1 env") auto
    have IH1: "occurs F (inst \<rho> t1) (instE \<rho> env) = Some (instr \<rho> id r1)"
      by (rule "1.IH"[OF h1 ok lkdec_mono[OF d]]) (auto simp: App)
    show ?thesis
    proof (cases "r1 = Ok False")
      case True
      with "1.hyps" App h1 have h2: "oc F t2 env = Some r" by simp
      have IH2: "occurs F (inst \<rho> t2) (instE \<rho> env) = Some (instr \<rho> id r)"
        by (rule "1.IH"[OF h2 ok lkdec_mono[OF d]]) (auto simp: App)
      show ?thesis using IH1 IH2 True App by (subst occurs.simps) simp
    next
      case False
      with "1.hyps" App h1 have "r = r1 \<and> r1 \<noteq> Ok False" by (cases r1) (auto simp: return_def)
      then show ?thesis using IH1 App by (subst occurs.simps) (cases r1; auto simp: return_def)
    qed
  next
    case (Abs a T u)
    from "1.hyps" Abs have h: "oc F u env = Some r" by simp
    have "occurs F (inst \<rho> u) (instE \<rho> env) = Some (instr \<rho> id r)"
      by (rule "1.IH"[OF h ok lkdec_mono[OF d]]) (auto simp: Abs)
    then show ?thesis using Abs by (subst occurs.simps) simp
  qed (use "1.hyps" in \<open>subst occurs.simps; auto simp: return_def\<close>)+
qed

lemma occurs_inst2:
  assumes "occurs F t' env' = Some r'"
  shows "env' = instE \<rho> env \<Longrightarrow> t' = inst \<rho> t \<Longrightarrow> tyok env \<Longrightarrow> lkdec \<rho> env (vps t \<union> bvps env) \<Longrightarrow>
    \<exists>r. occurs F t env = Some r \<and> r' = instr \<rho> id r"
  using assms
proof (induction F t' env' r' arbitrary: t rule: occurs.raw_induct[rotated, consumes 1])
  case (1 oc F t' env' r' t)
  note e = "1.prems"(1) and tt = "1.prems"(2) and ok = "1.prems"(3) and d = "1.prems"(4)
  show ?case
  proof (cases t)
    case (Var G T)
    have lk: "lookup env' G (tsubst \<rho> T) = instM \<rho> (map_option (inst \<rho>)) (lookup env G T)"
      unfolding e by (rule lookup_inst[OF ok lkdec_mono[OF d]]) (simp add: Var)
    from "1.hyps" tt Var lk obtain lr where lr: "lookup env G T = Some lr"
      by (cases "lookup env G T") (auto simp: instM_def)
    have hp: "occurs F t env = bindM (lookup env G T)
        (\<lambda>r. case r of Some u \<Rightarrow> occurs F u env | None \<Rightarrow> return (F = G))"
      by (subst occurs.simps) (simp add: Var)
    show ?thesis
    proof (cases "lr = Ok None \<or> (\<exists>e. lr = Err e)")
      case True
      then show ?thesis using "1.hyps" tt Var lk hp lr by (auto simp: return_def)
    next
      case False
      then obtain u where lu: "lr = Ok (Some u)" by (cases lr) auto
      from lr lu obtain U where b: "vt_lookup (tenv env) G = Some (U, u)" using lookup_SomeD by blast
      from "1.hyps" tt Var lk lr lu have hu: "oc F (inst \<rho> u) env' = Some r'" by simp
      have "vps u \<union> bvps env \<subseteq> vps t \<union> bvps env" using bvpsI[OF b] by auto
      from "1.IH"[OF hu e refl ok lkdec_mono[OF d this]] show ?thesis using hp lr lu by simp
    qed
  next
    case (App t1 t2)
    from "1.hyps" tt App obtain r1 where h1: "oc F (inst \<rho> t1) env' = Some r1"
      by (cases "oc F (inst \<rho> t1) env'") auto
    have sub1: "vps t1 \<union> bvps env \<subseteq> vps t \<union> bvps env" and sub2: "vps t2 \<union> bvps env \<subseteq> vps t \<union> bvps env"
      using App by auto
    from "1.IH"[OF h1 e refl ok lkdec_mono[OF d sub1]] obtain p1 where
      p1: "occurs F t1 env = Some p1" "r1 = instr \<rho> id p1" by (auto simp: id_def)
    have hp: "occurs F t env = bindM (occurs F t1 env) (\<lambda>b. if b then return True else occurs F t2 env)"
      by (subst occurs.simps) (simp add: App)
    show ?thesis
    proof (cases "p1 = Ok False")
      case True
      with "1.hyps" tt App h1 p1 have h2: "oc F (inst \<rho> t2) env' = Some r'" by simp
      from "1.IH"[OF h2 e refl ok lkdec_mono[OF d sub2]] show ?thesis using hp p1 True by (auto simp: id_def)
    next
      case False
      then show ?thesis using "1.hyps" tt App h1 p1 hp by (cases p1) (auto simp: return_def)
    qed
  next
    case (Abs a T u)
    from "1.hyps" tt Abs have h: "oc F (inst \<rho> u) env' = Some r'" by simp
    from "1.IH"[OF h e refl ok lkdec_mono[OF d]] show ?thesis
      by (subst occurs.simps) (auto simp: Abs id_def)
  qed (use "1.hyps" tt in \<open>subst occurs.simps; auto simp: return_def\<close>)+
qed

lemma occurs_inst:
  assumes "tyok env" "lkdec \<rho> env (vps t \<union> bvps env)"
  shows "occurs F (inst \<rho> t) (instE \<rho> env) = instM \<rho> id (occurs F t env)"
proof (cases "occurs F t env")
  case None
  show ?thesis
  proof (cases "occurs F (inst \<rho> t) (instE \<rho> env)")
    case (Some r')
    from occurs_inst2[OF Some refl refl assms] None show ?thesis by simp
  qed (simp add: None)
next
  case (Some r)
  then show ?thesis using occurs_inst1[OF Some assms] by (simp add: instM_def)
qed


subsection \<open>The rigid occurs check\<close>

lemma existsM_inst1:
  assumes "existsM f xs = Some r" "\<And>x r. x \<in> set xs \<Longrightarrow> f x = Some r \<Longrightarrow> g (F x) = Some (instr \<rho> id r)"
  shows "existsM g (map F xs) = Some (instr \<rho> id r)"
  using assms
proof (induction xs arbitrary: r)
  case (Cons x xs)
  from Cons.prems(1) obtain r1 where r1: "f x = Some r1" by (cases "f x") auto
  then have g1: "g (F x) = Some (instr \<rho> id r1)" using Cons.prems(2) by simp
  show ?case
  proof (cases "r1 = Ok False")
    case True
    then show ?thesis using Cons r1 g1 by simp
  next
    case False
    then show ?thesis using Cons.prems(1) r1 g1 by (cases r1) (auto simp: return_def)
  qed
qed (simp add: return_def)

lemma existsM_inst2:
  assumes "existsM g (map F xs) = Some r'"
    "\<And>x r'. x \<in> set xs \<Longrightarrow> g (F x) = Some r' \<Longrightarrow> \<exists>r. f x = Some r \<and> r' = instr \<rho> id r"
  shows "\<exists>r. existsM f xs = Some r \<and> r' = instr \<rho> id r"
  using assms
proof (induction xs arbitrary: r')
  case (Cons x xs)
  from Cons.prems(1) obtain r1' where r1': "g (F x) = Some r1'" by (cases "g (F x)") auto
  then obtain r1 where r1: "f x = Some r1" "r1' = instr \<rho> id r1" using Cons.prems(2) by force
  show ?case
  proof (cases "r1 = Ok False")
    case True
    then show ?thesis using Cons r1 r1' by simp
  next
    case False
    then show ?thesis using Cons.prems(1) r1 r1' by (cases r1) (auto simp: return_def)
  qed
qed (simp add: return_def)

lemma handle_Pattern_inst:
  "(case instx \<rho> e of Pattern \<Rightarrow> return False | _ \<Rightarrow> raise (instx \<rho> e)) =
    instM \<rho> id (case e of Pattern \<Rightarrow> return False | _ \<Rightarrow> raise e)"
  by (cases e) simp_all

lemma handle_Some_simps[simp]:
  "handle (Some (Ok x)) h = Some (Ok x)" "handle (Some (Err e)) h = h e"
  by (simp_all add: handle_def)

lemma handle_True_inst:
  assumes "m' = instM \<rho> id m"
  shows "handle (bindM m' (\<lambda>_. return True)) (\<lambda>e. case e of Pattern \<Rightarrow> return False | _ \<Rightarrow> raise e) =
    instM \<rho> id (handle (bindM m (\<lambda>_. return True)) (\<lambda>e. case e of Pattern \<Rightarrow> return False | _ \<Rightarrow> raise e))"
proof (cases m)
  case (Some x)
  then show ?thesis using assms by (cases x) (simp_all add: handle_Pattern_inst)
qed (simp add: assms)

lemma rigid_occurs_inst1:
  assumes "rigid_occurs F t env = Some r"
  shows "tyok env \<Longrightarrow> lkdec \<rho> env (vps t \<union> bvps env) \<Longrightarrow>
    rigid_occurs F (inst \<rho> t) (instE \<rho> env) = Some (instr \<rho> id r)"
  using assms
proof (induction F t env r rule: rigid_occurs.raw_induct[rotated, consumes 1])
  case (1 ro F t env r)
  note ok = "1.prems"(1) and d = "1.prems"(2)
  from "1.hyps" obtain hr where hr: "head_norm env t = Some hr" by (cases "head_norm env t") auto
  note hi = head_norm_inst[OF ok d] and hv = head_norm_inst1[OF hr ok d]
  show ?case
  proof (cases hr)
    case (Err e)
    then show ?thesis using "1.hyps" hr hi by (subst rigid_occurs.simps) auto
  next
    case (Ok t')
    have vt': "vps t' \<union> bvps env \<subseteq> vps t \<union> bvps env" using hv Ok by auto
    from "1.hyps" hr Ok have h: "(case t' of pterm.Abs _ _ u \<Rightarrow> ro F u env | _ \<Rightarrow>
        (let (h, ts) = strip_comb t' in (case h of
          pterm.Var G _ \<Rightarrow> if G = F then handle (do {_ \<leftarrow> ints_of' env ts; return True})
              (\<lambda>e. case e of Pattern \<Rightarrow> return False | _ \<Rightarrow> raise e) else return False
        | pterm.Abs _ _ _ \<Rightarrow> return False
        | _ \<Rightarrow> existsM (\<lambda>u. ro F u env) ts))) = Some r" by simp
    have hi': "rigid_occurs F (inst \<rho> t) (instE \<rho> env) = (case inst \<rho> t' of pterm.Abs _ _ u \<Rightarrow>
        rigid_occurs F u (instE \<rho> env) | _ \<Rightarrow>
        (let (h, ts) = strip_comb (inst \<rho> t') in (case h of
          pterm.Var G _ \<Rightarrow> if G = F then handle (do {_ \<leftarrow> ints_of' (instE \<rho> env) ts; return True})
              (\<lambda>e. case e of Pattern \<Rightarrow> return False | _ \<Rightarrow> raise e) else return False
        | pterm.Abs _ _ _ \<Rightarrow> return False
        | _ \<Rightarrow> existsM (\<lambda>u. rigid_occurs F u (instE \<rho> env)) ts)))"
      using hi hr Ok by (subst rigid_occurs.simps) simp
    show ?thesis
    proof (cases "is_Abs t'")
      case True
      then obtain a T u where t': "t' = pterm.Abs a T u" by (cases t') auto
      from h t' have hu: "ro F u env = Some r" by simp
      have "rigid_occurs F (inst \<rho> u) (instE \<rho> env) = Some (instr \<rho> id r)"
        by (rule "1.IH"[OF hu ok lkdec_mono[OF d]]) (use vt' t' in auto)
      then show ?thesis using hi' t' by simp
    next
      case nA: False
      obtain hd ts where st: "strip_comb t' = (hd, ts)" by force
      have sti: "strip_comb (inst \<rho> t') = (inst \<rho> hd, map (inst \<rho>) ts)"
        using strip_comb_inst[of \<rho> t'] st by simp
      have vts: "vps hd \<union> (\<Union>u\<in>set ts. vps u) \<subseteq> vps t'"
        using strip_comb_list_comb[OF st] vps_list_comb[of hd ts] by simp
      have dts: "\<forall>u\<in>set ts. lkdec \<rho> env (vps u \<union> bvps env)"
        using vts vt' by (intro ballI lkdec_mono[OF d]) auto
      from h nA st have h2: "(case hd of
          pterm.Var G _ \<Rightarrow> if G = F then handle (do {_ \<leftarrow> ints_of' env ts; return True})
              (\<lambda>e. case e of Pattern \<Rightarrow> return False | _ \<Rightarrow> raise e) else return False
        | pterm.Abs _ _ _ \<Rightarrow> return False
        | _ \<Rightarrow> existsM (\<lambda>u. ro F u env) ts) = Some r" by (cases t') auto
      from hi' nA sti have hi2: "rigid_occurs F (inst \<rho> t) (instE \<rho> env) = (case inst \<rho> hd of
          pterm.Var G _ \<Rightarrow> if G = F then handle (do {_ \<leftarrow> ints_of' (instE \<rho> env) (map (inst \<rho>) ts); return True})
              (\<lambda>e. case e of Pattern \<Rightarrow> return False | _ \<Rightarrow> raise e) else return False
        | pterm.Abs _ _ _ \<Rightarrow> return False
        | _ \<Rightarrow> existsM (\<lambda>u. rigid_occurs F u (instE \<rho> env)) (map (inst \<rho>) ts))"
        by (cases t') auto
      have io: "handle (do {_ \<leftarrow> ints_of' (instE \<rho> env) (map (inst \<rho>) ts); return True})
              (\<lambda>e. case e of Pattern \<Rightarrow> return False | _ \<Rightarrow> raise e) =
            instM \<rho> id (handle (do {_ \<leftarrow> ints_of' env ts; return True})
              (\<lambda>e. case e of Pattern \<Rightarrow> return False | _ \<Rightarrow> raise e))"
        by (rule handle_True_inst[OF ints_of'_inst[OF ok dts]])
      show ?thesis
      proof (cases hd)
        case (Var G T)
        then show ?thesis using h2 hi2 io by (auto simp: instM_def return_def split: if_splits)
      next
        case (Abs a T u)
        then show ?thesis using h2 hi2 by (auto simp: return_def)
      next
        case (Const a T)
        have "existsM (\<lambda>u. rigid_occurs F u (instE \<rho> env)) (map (inst \<rho>) ts) = Some (instr \<rho> id r)"
          by (rule existsM_inst1[where f = "\<lambda>u. ro F u env"]) (use h2 Const "1.IH" ok dts in auto)
        then show ?thesis using hi2 Const by simp
      next
        case (Free a T)
        have "existsM (\<lambda>u. rigid_occurs F u (instE \<rho> env)) (map (inst \<rho>) ts) = Some (instr \<rho> id r)"
          by (rule existsM_inst1[where f = "\<lambda>u. ro F u env"]) (use h2 Free "1.IH" ok dts in auto)
        then show ?thesis using hi2 Free by simp
      next
        case (Bound i)
        have "existsM (\<lambda>u. rigid_occurs F u (instE \<rho> env)) (map (inst \<rho>) ts) = Some (instr \<rho> id r)"
          by (rule existsM_inst1[where f = "\<lambda>u. ro F u env"]) (use h2 Bound "1.IH" ok dts in auto)
        then show ?thesis using hi2 Bound by simp
      next
        case (App f u)
        then show ?thesis using strip_comb_head[OF st] by simp
      qed
    qed
  qed
qed

lemma rigid_occurs_inst2:
  assumes "rigid_occurs F t' env' = Some r'"
  shows "env' = instE \<rho> env \<Longrightarrow> t' = inst \<rho> t \<Longrightarrow> tyok env \<Longrightarrow> lkdec \<rho> env (vps t \<union> bvps env) \<Longrightarrow>
    \<exists>r. rigid_occurs F t env = Some r \<and> r' = instr \<rho> id r"
  using assms
proof (induction F t' env' r' arbitrary: t rule: rigid_occurs.raw_induct[rotated, consumes 1])
  case (1 ro F t' env' r' t)
  note e = "1.prems"(1) and tt = "1.prems"(2) and ok = "1.prems"(3) and d = "1.prems"(4)
  note hi = head_norm_inst[OF ok d]
  from "1.hyps" e tt hi obtain hr where hr: "head_norm env t = Some hr"
    by (cases "head_norm env t") (auto simp: instM_def)
  note hv = head_norm_inst1[OF hr ok d]
  have hp: "rigid_occurs F t env = bindM (head_norm env t) (\<lambda>t'. case t' of pterm.Abs _ _ u \<Rightarrow>
        rigid_occurs F u env | _ \<Rightarrow>
        (let (h, ts) = strip_comb t' in (case h of
          pterm.Var G _ \<Rightarrow> if G = F then handle (do {_ \<leftarrow> ints_of' env ts; return True})
              (\<lambda>e. case e of Pattern \<Rightarrow> return False | _ \<Rightarrow> raise e) else return False
        | pterm.Abs _ _ _ \<Rightarrow> return False
        | _ \<Rightarrow> existsM (\<lambda>u. rigid_occurs F u env) ts)))"
    by (subst rigid_occurs.simps) simp
  show ?case
  proof (cases hr)
    case (Err e')
    then show ?thesis using "1.hyps" e tt hr hi hp by auto
  next
    case (Ok s)
    have vs: "vps s \<union> bvps env \<subseteq> vps t \<union> bvps env" using hv Ok by auto
    from "1.hyps" e tt hi hr Ok have h: "(case inst \<rho> s of pterm.Abs _ _ u \<Rightarrow> ro F u env' | _ \<Rightarrow>
        (let (h, ts) = strip_comb (inst \<rho> s) in (case h of
          pterm.Var G _ \<Rightarrow> if G = F then handle (do {_ \<leftarrow> ints_of' env' ts; return True})
              (\<lambda>e. case e of Pattern \<Rightarrow> return False | _ \<Rightarrow> raise e) else return False
        | pterm.Abs _ _ _ \<Rightarrow> return False
        | _ \<Rightarrow> existsM (\<lambda>u. ro F u env') ts))) = Some r'" by simp
    show ?thesis
    proof (cases "is_Abs s")
      case True
      then obtain a T u where s: "s = pterm.Abs a T u" by (cases s) auto
      from h s have hu: "ro F (inst \<rho> u) env' = Some r'" by simp
      from "1.IH"[OF hu e refl ok lkdec_mono[OF d]] vs s obtain r where
        "rigid_occurs F u env = Some r" "r' = instr \<rho> id r" by auto
      then show ?thesis using hp hr Ok s by simp
    next
      case nA: False
      obtain hd ts where st: "strip_comb s = (hd, ts)" by force
      have sti: "strip_comb (inst \<rho> s) = (inst \<rho> hd, map (inst \<rho>) ts)"
        using strip_comb_inst[of \<rho> s] st by simp
      have vts: "vps hd \<union> (\<Union>u\<in>set ts. vps u) \<subseteq> vps s"
        using strip_comb_list_comb[OF st] vps_list_comb[of hd ts] by simp
      have dts: "\<forall>u\<in>set ts. lkdec \<rho> env (vps u \<union> bvps env)"
        using vts vs by (intro ballI lkdec_mono[OF d]) auto
      from h nA sti have h2: "(case inst \<rho> hd of
          pterm.Var G _ \<Rightarrow> if G = F then handle (do {_ \<leftarrow> ints_of' env' (map (inst \<rho>) ts); return True})
              (\<lambda>e. case e of Pattern \<Rightarrow> return False | _ \<Rightarrow> raise e) else return False
        | pterm.Abs _ _ _ \<Rightarrow> return False
        | _ \<Rightarrow> existsM (\<lambda>u. ro F u env') (map (inst \<rho>) ts)) = Some r'" by (cases s) auto
      from hp hr Ok nA st have hp2: "rigid_occurs F t env = (case hd of
          pterm.Var G _ \<Rightarrow> if G = F then handle (do {_ \<leftarrow> ints_of' env ts; return True})
              (\<lambda>e. case e of Pattern \<Rightarrow> return False | _ \<Rightarrow> raise e) else return False
        | pterm.Abs _ _ _ \<Rightarrow> return False
        | _ \<Rightarrow> existsM (\<lambda>u. rigid_occurs F u env) ts)"
        by (cases s) auto
      have io: "handle (do {_ \<leftarrow> ints_of' env' (map (inst \<rho>) ts); return True})
              (\<lambda>e. case e of Pattern \<Rightarrow> return False | _ \<Rightarrow> raise e) =
            instM \<rho> id (handle (do {_ \<leftarrow> ints_of' env ts; return True})
              (\<lambda>e. case e of Pattern \<Rightarrow> return False | _ \<Rightarrow> raise e))"
        unfolding e by (rule handle_True_inst[OF ints_of'_inst[OF ok dts]])
      have ex: "\<exists>r. existsM (\<lambda>u. rigid_occurs F u env) ts = Some r \<and> r' = instr \<rho> id r"
        if "existsM (\<lambda>u. ro F u env') (map (inst \<rho>) ts) = Some r'"
        by (rule existsM_inst2[OF that]) (use "1.IH" e ok dts in auto)
      show ?thesis
      proof (cases hd)
        case (Var G T)
        then show ?thesis using h2 hp2 io
          by (cases "G = F"; cases "handle (bindM (ints_of' env ts) (\<lambda>_. return True))
              (\<lambda>e. case e of Pattern \<Rightarrow> return False | _ \<Rightarrow> raise e)") (auto simp: instM_def return_def)
      next
        case (Abs a T u)
        then show ?thesis using h2 hp2 by (auto simp: return_def)
      next
        case (App f u)
        then show ?thesis using strip_comb_head[OF st] by simp
      qed (use h2 hp2 ex in simp)+
    qed
  qed
qed

lemma rigid_occurs_inst:
  assumes "tyok env" "lkdec \<rho> env (vps t \<union> bvps env)"
  shows "rigid_occurs F (inst \<rho> t) (instE \<rho> env) = instM \<rho> id (rigid_occurs F t env)"
proof (cases "rigid_occurs F t env")
  case None
  show ?thesis
  proof (cases "rigid_occurs F (inst \<rho> t) (instE \<rho> env)")
    case (Some r')
    from rigid_occurs_inst2[OF Some refl refl assms] None show ?thesis by simp
  qed (simp add: None)
next
  case (Some r)
  then show ?thesis using rigid_occurs_inst1[OF Some assms] by (simp add: instM_def)
qed


subsection \<open>New variables and bindings\<close>

lemma nth_map_inst: "nth (map f xs) i = instM \<rho> f (nth xs i)"
  by (induction xs arbitrary: i) auto

lemma mkabs_inst: "mkabs (instb \<rho> bs) is (inst \<rho> t) = instM \<rho> (inst \<rho>) (mkabs bs is t)"
proof (induction "is")
  case (Cons i "is")
  have n: "nth (instb \<rho> bs) i = instM \<rho> (\<lambda>(a, T). (a, tsubst \<rho> T)) (nth bs i)"
    unfolding instb_def by (rule nth_map_inst)
  show ?case
    by (simp only: mkabs.simps n, rule bindM_instM)
      (auto simp: Cons intro!: bindM_instM split: prod.splits)
qed simp

lemma tsubst_foldr_fun: "tsubst \<rho> (foldr fun_type Us U) = foldr fun_type (map (tsubst \<rho>) Us) (tsubst \<rho> U)"
  by (induction Us) auto

lemma split_type_inst:
  assumes "(\<forall>v S a Us. (v, S) \<in> tvars T \<longrightarrow> \<rho> v S \<noteq> Type a Us) \<or> (\<exists>r. split_type T n Ts = Some (Ok r))"
  shows "split_type (tsubst \<rho> T) n (map (tsubst \<rho>) Ts) =
    instM \<rho> (\<lambda>(Us, U). (map (tsubst \<rho>) Us, tsubst \<rho> U)) (split_type T n Ts)"
  using assms
proof (induction T n Ts rule: split_type.induct)
  case (1 T n Ts)
  show ?case
  proof (cases "n = 0")
    case False
    show ?thesis
    proof (cases T)
      case (Type a Us)
      show ?thesis
      proof (cases "\<exists>T1 T2. Us = [T1, T2]")
        case True
        then obtain T1 T2 where Us: "Us = [T1, T2]" by blast
        show ?thesis
        proof (cases "a = STR ''fun''")
          case True
          have "(\<forall>v S a Us. (v, S) \<in> tvars T2 \<longrightarrow> \<rho> v S \<noteq> Type a Us) \<or>
              (\<exists>r. split_type T2 (n - 1) (T1 # Ts) = Some (Ok r))"
            using "1.prems" False Type Us True by (subst (asm) split_type.simps) auto
          from "1.IH"[OF False Type[unfolded Us True] refl refl refl refl this] show ?thesis
            using False Type Us True
            by (subst (1 2) split_type.simps) simp
        next
          case nf: False
          then show ?thesis using False Type Us by (subst (1 2) split_type.simps) simp
        qed
      next
        case False
        then have "tsubst \<rho> T \<noteq> Type (STR ''fun'') [T1, T2]" for T1 T2
          using Type by auto
        moreover have "\<forall>T1 T2. Us \<noteq> [T1, T2]" using False by blast
        ultimately show ?thesis using \<open>n \<noteq> 0\<close> Type
          by (subst (1 2) split_type.simps) (auto split: ptyp.splits list.splits)
      qed
    next
      case (TVar v S)
      have "\<forall>a Us. \<rho> v S \<noteq> Type a Us"
        using "1.prems" False TVar by (subst (asm) split_type.simps) (auto simp: raise_def)
      then show ?thesis using False TVar
        by (subst (1 2) split_type.simps) (auto split: ptyp.splits)
    qed (use False in \<open>subst (1 2) split_type.simps; simp\<close>)
  qed (subst (1 2) split_type.simps; simp)
qed

lemma norm_type_empty: "norm_type vt_empty T = return T"
  by (simp add: norm_type_def)

lemma type_of_G_inst:
  assumes ok: "tyok env" and tc: "tcons (tyenv env) T" and sol: "tsol (tyenv env) \<rho>"
    and sp: "(\<forall>v S a Us. (v, S) \<in> tvars (tnorm (tyenv env) T) \<longrightarrow> \<rho> v S \<noteq> Type a Us) \<or>
      (\<exists>r. split_type (tnorm (tyenv env) T) n [] = Some (Ok r))"
  shows "type_of_G (instE \<rho> env) (tsubst \<rho> T) n is = instM \<rho> (tsubst \<rho>) (type_of_G env T n is)"
proof -
  have ac: "tacyc (tyenv env)" and tce: "tcons_env (tyenv env)" using ok by (simp_all add: tyok_def)
  have T: "tsubst \<rho> T = tsubst \<rho> (tnorm (tyenv env) T)" using tsubst_tnorm[OF ac tce sol tc] by simp
  have st: "split_type (tsubst \<rho> T) n [] =
      instM \<rho> (\<lambda>(Us, U). (map (tsubst \<rho>) Us, tsubst \<rho> U)) (split_type (tnorm (tyenv env) T) n [])"
    unfolding T using split_type_inst[OF sp] by simp
  show ?thesis
    unfolding type_of_G_def instE_simps norm_type_empty norm_type_ok[OF ac tce tc] bindM_simps st
  proof (rule bindM_instM, clarsimp)
    fix Us U
    have mm: "mapM (nth (map (tsubst \<rho>) Us)) is = instM \<rho> (map (tsubst \<rho>)) (mapM (nth Us) is)"
      by (rule mapM_instM[of "is" _ id, simplified]) (rule nth_map_inst)
    show "mapM (nth (map (tsubst \<rho>) Us)) is \<bind> (\<lambda>Us'. return (foldr fun_type Us' (tsubst \<rho> U))) =
        instM \<rho> (tsubst \<rho>) (mapM (nth Us) is \<bind> (\<lambda>Us. return (foldr fun_type Us U)))"
      unfolding mm by (rule bindM_instM) (simp add: tsubst_foldr_fun)
  qed
qed

lemma genvar_inst:
  "genvar a (instE \<rho> env) (tsubst \<rho> T) = (instE \<rho> (fst (genvar a env T)), inst \<rho> (snd (genvar a env T)))"
  by (cases env) (simp add: genvar_def instE_def)

lemma vt_map_update: "vt_map f (vt_update (k, x) t) = vt_update (k, f x) (vt_map f t)"
  by transfer (auto simp: fun_eq_iff)

lemma vt_defined_map[simp]: "vt_defined (vt_map f t) k \<longleftrightarrow> vt_defined t k"
  by (simp add: vt_defined_lookup)

lemma update_inst:
  "update (F, tsubst \<rho> T) (inst \<rho> t) (instE \<rho> env) = instM \<rho> (instE \<rho>) (update (F, T) t env)"
  by (cases env) (simp add: update_def update_new_def instE_def vt_map_update)

lemma mk_hnf_inst: "mk_hnf (instb \<rho> bs) is (inst \<rho> G) js = instM \<rho> (inst \<rho>) (mk_hnf bs is G js)"
  by (simp add: mk_hnf_def flip: inst_app mkabs_inst)

lemma mk_new_hnf_inst:
  assumes "tyok env" "tcons (tyenv env) T" "tsol (tyenv env) \<rho>"
    "(\<forall>v S a Us. (v, S) \<in> tvars (tnorm (tyenv env) T) \<longrightarrow> \<rho> v S \<noteq> Type a Us) \<or>
      (\<exists>r. split_type (tnorm (tyenv env) T) (ilength is) [] = Some (Ok r))"
  shows "mk_new_hnf (instE \<rho> env) (instb \<rho> bs) is F (tsubst \<rho> T) js =
    instM \<rho> (instE \<rho>) (mk_new_hnf env bs is F T js)"
  unfolding mk_new_hnf_def type_of_G_inst[OF assms]
proof (rule bindM_instM)
  fix Gty
  obtain env' G where g: "genvar (fst F) env Gty = (env', G)" by force
  show "(let (env', G) = genvar (fst F) (instE \<rho> env) (tsubst \<rho> Gty)
        in mk_hnf (instb \<rho> bs) is G js \<bind> (\<lambda>t. update (F, tsubst \<rho> T) t env')) =
      instM \<rho> (instE \<rho>) (let (env', G) = genvar (fst F) env Gty
        in mk_hnf bs is G js \<bind> (\<lambda>t. update (F, T) t env'))"
    using genvar_inst[of "fst F" \<rho> env Gty] g
    by (simp add: mk_hnf_inst, intro bindM_instM) (simp add: update_inst)
qed


subsection \<open>Weak commutation\<close>

text \<open>
  New variable types are computed by splitting function types (\<^const>\<open>split_type\<close>). An
  instance may succeed where the original problem fails with \<open>Failure\<close>, unless the instantiation
  maps unbound type variables to types that are not type constructor applications.
\<close>

definition tfree_on :: "tinst \<Rightarrow> tyenv \<Rightarrow> bool" where
  "tfree_on \<rho> \<theta> \<longleftrightarrow> (\<forall>v S a Us. vt_lookup \<theta> v = None \<longrightarrow> \<rho> v S \<noteq> Type a Us)"

definition relI :: "tinst \<Rightarrow> bool \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> 'a M \<Rightarrow> 'b M \<Rightarrow> bool" where
  "relI \<rho> b f m m' \<longleftrightarrow> m' = instM \<rho> f m \<or> (\<not> b \<and> (\<exists>s. m = Some (Err (Failure s))))"

lemma relI_eq: "m' = instM \<rho> f m \<Longrightarrow> relI \<rho> b f m m'"
  by (simp add: relI_def)

lemma relI_True: "relI \<rho> True f m m' \<longleftrightarrow> m' = instM \<rho> f m"
  by (simp add: relI_def)

lemma relI_Ok: "relI \<rho> b f m m' \<Longrightarrow> m = Some (Ok x) \<Longrightarrow> m' = Some (Ok (f x))"
  by (auto simp: relI_def)

lemma relI_Err:
  "relI \<rho> b f m m' \<Longrightarrow> m = Some (Err e) \<Longrightarrow> (\<forall>s. e \<noteq> Failure s) \<Longrightarrow> m' = Some (Err (instx \<rho> e))"
  by (auto simp: relI_def)

lemma relI_bindM:
  assumes "relI \<rho> b f m m'" "\<And>x. m = Some (Ok x) \<Longrightarrow> relI \<rho> b g (k x) (k' (f x))"
  shows "relI \<rho> b g (bindM m k) (bindM m' k')"
  using assms by (auto simp: relI_def instM_def bindM_def split: option.splits res.splits)

lemma relI_handle:
  assumes "relI \<rho> b f m m'" "\<And>e. m = Some (Err e) \<Longrightarrow> relI \<rho> b f (h e) (h' (instx \<rho> e))"
    "\<And>s. h (Failure s) = Some (Err (Failure s))"
  shows "relI \<rho> b f (handle m h) (handle m' h')"
  using assms by (auto simp: relI_def instM_def handle_def split: option.splits res.splits)

lemma split_type_res:
  "(\<exists>r. split_type T n Ts = Some (Ok r)) \<or> (\<exists>s. split_type T n Ts = Some (Err (Failure s)))"
proof (induction T n Ts rule: split_type.induct)
  case (1 T n Ts)
  show ?case
    by (subst (1 2) split_type.simps)
      (use "1.IH" in \<open>auto simp: return_def raise_def split: ptyp.splits list.splits\<close>)
qed

lemma type_of_G_relI:
  assumes ok: "tyok env" and tc: "tcons (tyenv env) T" and sol: "tsol (tyenv env) \<rho>"
  shows "relI \<rho> (tfree_on \<rho> (tyenv env)) (tsubst \<rho>) (type_of_G env T n is)
    (type_of_G (instE \<rho> env) (tsubst \<rho> T) n is)"
proof -
  have ac: "tacyc (tyenv env)" and tce: "tcons_env (tyenv env)" using ok by (simp_all add: tyok_def)
  show ?thesis
  proof (cases "tfree_on \<rho> (tyenv env) \<or> (\<exists>r. split_type (tnorm (tyenv env) T) n [] = Some (Ok r))")
    case True
    then have "(\<forall>v S a Us. (v, S) \<in> tvars (tnorm (tyenv env) T) \<longrightarrow> \<rho> v S \<noteq> Type a Us) \<or>
        (\<exists>r. split_type (tnorm (tyenv env) T) n [] = Some (Ok r))"
      using tnorm_unbound[OF ac] by (auto simp: tfree_on_def)
    then show ?thesis by (intro relI_eq type_of_G_inst[OF ok tc sol])
  next
    case False
    then obtain s where "split_type (tnorm (tyenv env) T) n [] = Some (Err (Failure s))"
      using split_type_res by blast
    then show ?thesis using False
      by (simp add: relI_def type_of_G_def norm_type_ok[OF ac tce tc])
  qed
qed

lemma mk_new_hnf_relI:
  assumes "tyok env" "tcons (tyenv env) T" "tsol (tyenv env) \<rho>"
  shows "relI \<rho> (tfree_on \<rho> (tyenv env)) (instE \<rho>) (mk_new_hnf env bs is F T js)
    (mk_new_hnf (instE \<rho> env) (instb \<rho> bs) is F (tsubst \<rho> T) js)"
  unfolding mk_new_hnf_def
proof (rule relI_bindM[OF type_of_G_relI[OF assms]])
  fix Gty
  obtain env' G where g: "genvar (fst F) env Gty = (env', G)" by force
  show "relI \<rho> (tfree_on \<rho> (tyenv env)) (instE \<rho>)
      (let (env', G) = genvar (fst F) env Gty in mk_hnf bs is G js \<bind> (\<lambda>t. update (F, T) t env'))
      (let (env', G) = genvar (fst F) (instE \<rho> env) (tsubst \<rho> Gty)
        in mk_hnf (instb \<rho> bs) is G js \<bind> (\<lambda>t. update (F, tsubst \<rho> T) t env'))"
    using genvar_inst[of "fst F" \<rho> env Gty] g
    by (intro relI_eq, simp add: mk_hnf_inst, intro bindM_instM) (simp add: update_inst)
qed


subsection \<open>Consistent problems\<close>

text \<open>
  The precondition of the commutation of projections: the types of all occurrences and
  bindings of a variable are equal modulo the type environment, all variables are old, and
  \<open>\<rho>\<close> solves the type environment.
\<close>

definition bpairs :: "env \<Rightarrow> (indexname \<times> ptyp) set" where
  "bpairs env = {p. \<exists>U u. vt_lookup (tenv env) (fst p) = Some (U, u) \<and> snd p = U}"

definition hyp :: "tinst \<Rightarrow> env \<Rightarrow> (indexname \<times> ptyp) set \<Rightarrow> bool" where
  "hyp \<rho> env X \<longleftrightarrow> tyok env \<and> tsol (tyenv env) \<rho> \<and>
    (\<exists>V. \<forall>p\<in>X \<union> bvps env \<union> bpairs env.
      tcons (tyenv env) (snd p) \<and> tnorm (tyenv env) (snd p) = tnorm (tyenv env) (V (fst p))) \<and>
    (\<forall>p\<in>X \<union> bvps env \<union> bpairs env. snd (fst p) \<le> maxidx env)"

lemma hyp_mono: "hyp \<rho> env X \<Longrightarrow> X' \<subseteq> X \<union> bvps env \<Longrightarrow> hyp \<rho> env X'"
  unfolding hyp_def by blast

lemma hypD: "hyp \<rho> env X \<Longrightarrow> tyok env" "hyp \<rho> env X \<Longrightarrow> tsol (tyenv env) \<rho>"
  by (simp_all add: hyp_def)

lemma hyp_lkdec: "hyp \<rho> env X \<Longrightarrow> lkdec \<rho> env (X \<union> bvps env)"
  unfolding lkdec_def
proof (intro allI impI conjI)
  fix x T assume h: "hyp \<rho> env X" and xT: "(x, T) \<in> X \<union> bvps env"
  from h obtain V where V: "\<forall>p\<in>X \<union> bvps env \<union> bpairs env.
      tcons (tyenv env) (snd p) \<and> tnorm (tyenv env) (snd p) = tnorm (tyenv env) (V (fst p))"
    and ok: "tyok env" and sol: "tsol (tyenv env) \<rho>" by (auto simp: hyp_def)
  have VT: "tcons (tyenv env) T \<and> tnorm (tyenv env) T = tnorm (tyenv env) (V x)"
    using bspec[OF V, of "(x, T)"] xT by (simp only: fst_conv snd_conv) blast
  then show "tcons (tyenv env) T" by simp
  fix U u assume b: "vt_lookup (tenv env) x = Some (U, u)"
  then have "(x, U) \<in> bpairs env" by (simp add: bpairs_def)
  then have VU: "tcons (tyenv env) U \<and> tnorm (tyenv env) U = tnorm (tyenv env) (V x)"
    using bspec[OF V, of "(x, U)"] by simp
  then show "tcons (tyenv env) U" by simp
  have eq: "tnorm (tyenv env) T = tnorm (tyenv env) U" using VT VU by simp
  have ac: "tacyc (tyenv env)" and tce: "tcons_env (tyenv env)" using ok by (simp_all add: tyok_def)
  have "tsubst \<rho> T = tsubst \<rho> U"
    using tsubst_tnorm[OF ac tce sol, of T] tsubst_tnorm[OF ac tce sol, of U] eq VT VU by metis
  then show "tnorm (tyenv env) T = tnorm (tyenv env) U \<longleftrightarrow> tsubst \<rho> T = tsubst \<rho> U" using eq by simp
qed

end

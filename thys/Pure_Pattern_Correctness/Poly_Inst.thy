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

definition instM :: "tinst \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> 'a M \<Rightarrow> 'b M" where
  "instM \<rho> f m = map_option (instr \<rho> f) m"

lemma instM_simps[simp]:
  "instM \<rho> f (return x) = return (f x)" "instM \<rho> f (raise e) = raise (instx \<rho> e)"
  "instM \<rho> f None = None" "instM \<rho> f (Some (Ok x)) = Some (Ok (f x))"
  "instM \<rho> f (Some (Err e)) = Some (Err (instx \<rho> e))"
  by (simp_all add: instM_def return_def raise_def)

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

end

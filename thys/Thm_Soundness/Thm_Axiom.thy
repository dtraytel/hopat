section \<open>The axiom rule on the abstract type of theorems\<close>

theory Thm_Axiom
  imports Thm_Lift "Pure_Thm.Pure_Axiom"
begin

text \<open>
  \<open>Thm.axiom thy name\<close> on \<^typ>\<open>'u pure_thm\<close>: the axiom is looked up in the signature
  (\<^const>\<open>sg_axioms\<close>); the theorem has the sorts of the axiom as sort hypotheses
  (\<open>Sorts.insert_term\<close>), and the proofs of \<open>Proofterm.axiom_proof\<close> and \<open>ZTerm.axiom_proof\<close>.
  The models of a signature satisfy its axioms (\<^const>\<open>is_model\<close>), so the theorem is valid.
\<close>


subsection \<open>The closure of a proposition\<close>

text \<open>
  \<open>Logic.all\<close> (with \<open>Term.lambda\<close>) and \<open>Proofterm.forall_intr_variables_term\<close>: the closure of a
  proposition over its variables, in the order of their first occurrence. The proof checker of
  Isabelle (\<open>Proofterm.prop_of_atom\<close>) closes the proposition of an axiom so.
\<close>

definition all_var :: "pterm \<Rightarrow> pterm \<Rightarrow> pterm" where
  "all_var v B = (case v of
      Var (x, i) T \<Rightarrow> all_const T $ Abs (if x = STR '''' then STR ''uu'' else x) T (abstract_over v B)
    | Free x T \<Rightarrow> all_const T $ Abs (if x = STR '''' then STR ''uu'' else x) T (abstract_over v B)
    | _ \<Rightarrow> B)"

definition forall_closure :: "pterm \<Rightarrow> pterm" where
  "forall_closure B = foldr all_var (variables_of B) B"

lemma term_atoms_aterms: "term_atoms t = aterms t"
  by (induction t) simp_all

lemma term_variables_eq: "term_variables t = variables_of t"
  by (simp add: term_variables_def variables_of_def term_atoms_aterms)

lemma subst_abstract_over_aux_Var:
  "\<not> loose_bvar t lev \<Longrightarrow> 0 \<le> lev \<Longrightarrow> (abstract_over_aux (Var z T) lev t)[Var z T/lev] = t"
proof (induction t arbitrary: lev)
  case (Abs a U t)
  have "(abstract_over_aux (Var z T) (lev + 1) t)[Var z T/lev + 1] = t"
    by (rule Abs.IH) (use Abs.prems in simp_all)
  then show ?case by simp
next
  case (Bound i)
  then show ?case by (simp add: subst_Bound)
qed (simp_all add: aconv_term_atom)

lemma set_fold_insert_filter:
  "set (fold (\<lambda>a acc. if P a then List.insert a acc else acc) xs acc) = set acc \<union> {a \<in> set xs. P a}"
  by (induction xs arbitrary: acc) auto

lemma set_variables_of:
  "set (variables_of t) = {a \<in> set (aterms t). (\<exists>xi T. a = Var xi T) \<or> (\<exists>x T. a = Free x T)}"
proof -
  have "variables_of t = rev (fold (\<lambda>a acc. if (\<exists>xi T. a = Var xi T) \<or> (\<exists>x T. a = Free x T)
      then List.insert a acc else acc) (aterms t) [])"
    unfolding variables_of_def by (rule arg_cong[where f = rev], rule fold_cong) (auto split: pterm.splits)
  then show ?thesis by (simp add: set_fold_insert_filter)
qed

lemma Var_aterms_vars: "Var xi T \<in> set (aterms t) \<Longrightarrow> (xi, T) \<in> vars t"
  by (induction t) auto

lemma Free_aterms_fnames: "Free x T \<in> set (aterms t) \<Longrightarrow> x \<in> fnames t"
  by (induction t) auto

lemma variables_of_Var:
  assumes "fnames t = {}" "v \<in> set (variables_of t)"
  obtains xi T where "v = Var xi T" "(xi, T) \<in> vars t"
  using assms by (auto simp: set_variables_of dest: Var_aterms_vars Free_aterms_fnames)

lemma tyinst_ident: "tyinst vs (map (\<lambda>(v, S). TVar v S) vs) = TVar"
proof (intro ext)
  fix v S
  show "tyinst vs (map (\<lambda>(v, S). TVar v S) vs) v S = TVar v S"
    unfolding tyinst_def by (induction vs) auto
qed

text \<open>
  The type variables of a decoded term are type variables of the types of the tight term, with
  indices other than \<open>-1\<close>. So the instantiation of a new proof constant, which maps the type
  variables of the types of its proposition to themselves, records the identity for the type
  arguments of the proposition if these occur in it.
\<close>

lemma tvars_typ_of: "(v, S) \<in> tvars (typ_of Z) \<Longrightarrow> snd v \<noteq> -1 \<and> (v, S) \<in> set (ztyp_tvars Z)"
  by (induction Z) (auto simp: propT_def split: if_splits)

lemma (in pure_sig) tvars_zconst_typ:
  assumes a: "(v, S) \<in> tvars (zconst_typ c Us)"
  shows "\<exists>U\<in>set Us. (v, S) \<in> tvars U"
proof (cases "c = STR ''Pure.imp''")
  case True
  with a show ?thesis by (simp add: zconst_typ_def imp_type_def propT_def)
next
  case ni: False
  show ?thesis
  proof (cases "c = STR ''Pure.all''")
    case True
    with a ni show ?thesis by (auto simp: zconst_typ_def propT_def dummyT_def split: list.splits)
  next
    case na: False
    show ?thesis
    proof (cases "ctab c")
      case None
      with a ni na show ?thesis by (simp add: zconst_typ_def dummyT_def)
    next
      case (Some U0)
      let ?\<rho> = "\<lambda>v S. case map_of (zip (tparams U0) Us) (v, S) of Some X \<Rightarrow> X | None \<Rightarrow> dummyT"
      from a ni na Some have "(v, S) \<in> tvars (tsubst ?\<rho> U0)" by (simp add: zconst_typ_def)
      then obtain w S' where "(v, S) \<in> tvars (?\<rho> w S')" by (auto simp: tvars_tsubst)
      then obtain X where X: "map_of (zip (tparams U0) Us) (w, S') = Some X" "(v, S) \<in> tvars X"
        by (auto simp: dummyT_def split: option.splits)
      from map_of_SomeD[OF X(1)] have "X \<in> set Us" by (rule set_zip_rightD)
      with X(2) show ?thesis by blast
    qed
  qed
qed

lemma (in pure_sig) ttvars_zdec:
  "(v, S) \<in> ttvars (zdec z) \<Longrightarrow> snd v \<noteq> -1 \<and> (\<exists>Z\<in>set (zterm_types z). (v, S) \<in> set (ztyp_tvars Z))"
proof (induction z)
  case (ZVar xi T)
  then have "(v, S) \<in> tvars (typ_of T)" by (auto simp: ttvars_def split: if_splits)
  with tvars_typ_of[of v S T] show ?case by simp
next
  case (ZConst0 c)
  then show ?case using tvars_zconst_typ[of v S c "[]"] by (simp add: ttvars_def)
next
  case (ZConst1 c T)
  then have "(v, S) \<in> tvars (typ_of T)" using tvars_zconst_typ[of v S c "[typ_of T]"] by (simp add: ttvars_def)
  with tvars_typ_of[of v S T] show ?case by simp
next
  case (ZConst c Ts)
  then obtain T where "T \<in> set Ts" "(v, S) \<in> tvars (typ_of T)"
    using tvars_zconst_typ[of v S c "map typ_of Ts"] by (auto simp: ttvars_def)
  with tvars_typ_of[of v S T] show ?case by auto
next
  case (ZAbs a T t)
  from ZAbs.prems have "(v, S) \<in> tvars (typ_of T) \<or> (v, S) \<in> ttvars (zdec t)" by (auto simp: ttvars_def)
  then show ?case
  proof
    assume "(v, S) \<in> tvars (typ_of T)"
    with tvars_typ_of[of v S T] show ?thesis by simp
  next
    assume "(v, S) \<in> ttvars (zdec t)"
    from ZAbs.IH[OF this] show ?thesis by auto
  qed
next
  case (ZApp t u)
  from ZApp.prems have "(v, S) \<in> ttvars (zdec t) \<or> (v, S) \<in> ttvars (zdec u)" by (auto simp: ttvars_def)
  then show ?case using ZApp.IH by auto
next
  case (ZOfclass T c)
  then have "(v, S) \<in> tvars (typ_of T)"
    by (auto simp: ttvars_def Proof_Sig.of_class_def propT_def)
  with tvars_typ_of[of v S T] show ?case by simp
qed (simp_all add: ttvars_def)

lemma ztyp_tvars_typ_of: "(v, S) \<in> set (ztyp_tvars Z) \<Longrightarrow> tvars (typ_of (ZTVar v S)) \<subseteq> tvars (typ_of Z)"
  by (induction Z) (force simp: propT_def split: if_splits)+

lemma zinst_typs_ident:
  assumes "\<And>k. zt_lookup instT k = (if k \<in> K then Some (ZTVar (fst k) (snd k)) else None)"
    and "set vs \<subseteq> K" "\<And>v S. (v, S) \<in> set vs \<Longrightarrow> snd v \<noteq> -1"
  shows "zinst_typs instT vs = map (\<lambda>(v, S). TVar v S) vs"
  unfolding zinst_typs_def using assms(2,3) by (auto simp: assms(1))


subsection \<open>The type variables of an axiom\<close>

text \<open>The atomic types of a term are those of its types, without duplicates:\<close>

lemma set_fold_insert_distinct:
  "set (fold (\<lambda>T acc. if T \<in> set acc then acc else T # acc) xs acc) = set acc \<union> set xs \<and>
    (distinct acc \<longrightarrow> distinct (fold (\<lambda>T acc. if T \<in> set acc then acc else T # acc) xs acc))"
  by (induction xs arbitrary: acc) auto

lemma term_typs_typs: "set (term_typs t) = typs t"
  by (induction t) auto

lemma set_term_atyps: "set (term_atyps t) = tatoms t" and distinct_term_atyps: "distinct (term_atyps t)"
  using set_fold_insert_distinct[of "concat (map atyps (term_typs t))" "[]"]
  by (simp_all add: term_atyps_def tatoms_def term_typs_typs)

text \<open>Maps of types and their inverses:\<close>

lemma aterms_map_types: "aterms (map_types g t) = map (map_types g) (aterms t)"
  by (induction t) simp_all

lemma tatoms_map_types_atyps: "tatoms (map_types (map_atyps f) t) = (\<Union>U\<in>tatoms t. set (atyps (f U)))"
proof -
  have a: "set (atyps (map_atyps f T)) = (\<Union>U\<in>set (atyps T). set (atyps (f U)))" for T
    by (induction T) auto
  show ?thesis by (induction t) (auto simp: a)
qed

lemma tsubst_map_atyps:
  "(\<And>U. U \<in> set (atyps T) \<Longrightarrow> tsubst \<rho> (f U) = U) \<Longrightarrow> tsubst \<rho> (map_atyps f T) = T"
proof (induction T)
  case (Type a Ts)
  have "(tsubst \<rho> \<circ> map_atyps f) T = T" if "T \<in> set Ts" for T
    using Type.IH[OF that] Type.prems that by auto
  then show ?case by (simp add: map_idI)
qed simp_all

lemma inst_map_types_atyps:
  "(\<And>U. U \<in> tatoms t \<Longrightarrow> tsubst \<rho> (f U) = U) \<Longrightarrow> inst \<rho> (map_types (map_atyps f) t) = t"
  by (induction t) (auto intro!: tsubst_map_atyps)

text \<open>The variables of a term under an injective map of its atoms:\<close>

lemma fold_insert_map:
  assumes "inj_on h (set xs \<union> set acc)" "\<And>a. P (h a) \<longleftrightarrow> P a"
  shows "fold (\<lambda>a acc. if P a then List.insert a acc else acc) (map h xs) (map h acc) =
    map h (fold (\<lambda>a acc. if P a then List.insert a acc else acc) xs acc)"
  using assms(1)
proof (induction xs arbitrary: acc)
  case (Cons x xs)
  have i: "inj_on h (insert x (set acc))" using Cons.prems by (rule inj_on_subset) auto
  have ins: "List.insert (h x) (map h acc) = map h (List.insert x acc)"
    using i by (auto simp: List.insert_def inj_on_image_mem_iff)
  have "inj_on h (set xs \<union> set (if P x then List.insert x acc else acc))"
    using Cons.prems by (rule inj_on_subset) auto
  from Cons.IH[OF this] show ?case by (cases "P x") (simp_all add: assms(2) ins)
qed simp

lemma variables_of_map:
  assumes "inj_on h (set (aterms t))" "\<And>a. (\<exists>xi T. h a = Var xi T) \<or> (\<exists>x T. h a = Free x T) \<longleftrightarrow>
      (\<exists>xi T. a = Var xi T) \<or> (\<exists>x T. a = Free x T)"
    and "aterms t' = map h (aterms t)"
  shows "variables_of t' = map h (variables_of t)"
proof -
  let ?P = "\<lambda>a. (\<exists>xi T. a = Var xi T) \<or> (\<exists>x T. a = Free x T)"
  have v: "variables_of u = rev (fold (\<lambda>a acc. if ?P a then List.insert a acc else acc) (aterms u) [])" for u
    unfolding variables_of_def by (rule arg_cong[where f = rev], rule fold_cong) (auto split: pterm.splits)
  show ?thesis unfolding v assms(3) using fold_insert_map[of h "aterms t" "[]" ?P] assms(1,2)
    by (simp add: rev_map)
qed

lemma map_atyps_inj:
  assumes f: "\<And>U U'. U \<in> A \<Longrightarrow> U' \<in> A \<Longrightarrow> f U = f U' \<Longrightarrow> U = U'" and at: "\<And>U. U \<in> A \<Longrightarrow> \<exists>v S. f U = TVar v S"
    and A: "set (atyps T) \<subseteq> A" "set (atyps T') \<subseteq> A"
  shows "map_atyps f T = map_atyps f T' \<Longrightarrow> T = T'"
  using A
proof (induction T arbitrary: T')
  case (Type a Ts)
  show ?case
  proof (cases T')
    case (Type b Us)
    with Type.prems have ab: "a = b" and m: "map (map_atyps f) Ts = map (map_atyps f) Us" by simp_all
    have l: "length Ts = length Us" using m by (metis length_map)
    have "Ts ! i = Us ! i" if i: "i < length Ts" for i
    proof (rule Type.IH)
      show "Ts ! i \<in> set Ts" using i by simp
      show "set (atyps (Ts ! i)) \<subseteq> A" using Type.prems(2) i by (auto dest: nth_mem)
      show "set (atyps (Us ! i)) \<subseteq> A" using Type.prems(3) \<open>T' = Type b Us\<close> i l by (auto dest: nth_mem)
      show "map_atyps f (Ts ! i) = map_atyps f (Us ! i)" using arg_cong[OF m, of "\<lambda>xs. xs ! i"] i l by simp
    qed
    with ab l \<open>T' = Type b Us\<close> show ?thesis by (simp add: list_eq_iff_nth_eq)
  next
    case (TFree b S)
    with Type.prems at[of T'] show ?thesis by auto
  next
    case (TVar v S)
    with Type.prems at[of T'] show ?thesis by auto
  qed
next
  case (TFree a S)
  then show ?case using at f by (cases T') (fastforce simp: atyps.simps)+
next
  case (TVar v S)
  then show ?case using at f by (cases T') (fastforce simp: atyps.simps)+
qed


subsection \<open>Unconstraining an axiom without sort constraints\<close>

lemma map_atypsM_ok: "(\<And>U. U \<in> set (atyps T) \<Longrightarrow> ok (h U) (f U)) \<Longrightarrow> ok (map_atypsM h T) (map_atyps f T)"
proof (induction T)
  case (Type a Ts)
  have "list_all2 (\<lambda>x y. ok (map_atypsM h x) y) Ts (map (map_atyps f) Ts)"
    unfolding list_all2_conv_all_nth
  proof (intro conjI allI impI)
    fix i assume i: "i < length Ts"
    have "ok (h U) (f U)" if "U \<in> set (atyps (Ts ! i))" for U
      using Type.prems[of U] that nth_mem[OF i] by auto
    then show "ok (map_atypsM h (Ts ! i)) (map (map_atyps f) Ts ! i)"
      using Type.IH[OF nth_mem[OF i]] i by simp
  qed simp
  then show ?case by (simp add: ok_mapM)
qed simp_all

lemma map_typesM_ok:
  "(\<And>U. U \<in> tatoms t \<Longrightarrow> ok (h U) (f U)) \<Longrightarrow> ok (map_typesM (map_atypsM h) t) (map_types (map_atyps f) t)"
  by (induction t) (auto intro!: map_atypsM_ok)

text \<open>
  \<open>Logic.unconstrainT []\<close> on a proposition whose atomic types are type variables without sort
  constraints (as \<open>Theory.cert_axm\<close> ensures for axioms) renames them to the invented names, with
  index \<open>0\<close>, and adds no premises:
\<close>

lemma unconstrainT_sortfree:
  assumes sf: "\<forall>U\<in>tatoms A. \<exists>v. U = TVar v []"
    and len: "length (term_atyps A) \<le> length (invent (integer_of_nat (length (term_atyps A))))"
    and dis: "distinct (take (length (term_atyps A)) (invent (integer_of_nat (length (term_atyps A)))))"
    and ok: "ok (unconstrainT invent A) (outer, B)"
  obtains f \<rho> where "outer = []" "B = map_types (map_atyps f) A"
    "\<And>U. U \<in> tatoms A \<Longrightarrow> tsubst \<rho> (f U) = U" "\<And>U. U \<in> tatoms A \<Longrightarrow> \<exists>a. f U = TVar (a, 0) []"
    "\<And>v S. \<rho> v S = TVar v S \<or> (S = [] \<and> \<rho> v S \<in> tatoms A)" "\<And>U. U \<notin> tatoms A \<Longrightarrow> f U = U"
proof -
  define Ts where "Ts = term_atyps A"
  define names where "names = take (length Ts) (invent (integer_of_nat (length Ts)))"
  have lnames: "length names = length Ts" using len by (simp add: names_def Ts_def)
  have dnames: "distinct names" using dis by (simp add: names_def Ts_def)
  have dTs: "distinct Ts" and sTs: "set Ts = tatoms A" by (simp_all add: Ts_def distinct_term_atyps set_term_atyps)
  have sort0: "ok (sort_of_atyp T) []" if "T \<in> set Ts" for T
    using sf that sTs by (auto)
  have pres: "ok (mapM (\<lambda>T. do {S \<leftarrow> sort_of_atyp T; return (T, S)}) Ts) (map (\<lambda>T. (T, [])) Ts)"
    unfolding ok_mapM list_all2_map2 using sort0 by (auto simp: list_all2_conv_all_nth)
  let ?pm = "map2 (\<lambda>(T, S) a. (T, TVar (a, 0) S)) (map (\<lambda>T. (T, [])) Ts) names"
  have pm: "?pm = zip Ts (map (\<lambda>a. TVar (a, 0) []) names)"
    using lnames[symmetric] by (induction Ts names rule: list_induct2) auto
  define f where "f U = (case map_of (zip Ts (map (\<lambda>a. TVar (a, 0) []) names)) U of Some T' \<Rightarrow> T' | None \<Rightarrow> U)" for U
  define \<rho> where "\<rho> v S = (case map_of (zip (map (\<lambda>a. ((a, 0), [])) names) Ts) (v, S) of Some T \<Rightarrow> T | None \<Rightarrow> TVar v S)"
    for v S
  have fU: "f (Ts ! i) = TVar (names ! i, 0) []" if "i < length Ts" for i
    using that dTs lnames by (simp add: f_def map_of_zip_nth)
  have \<rho>U: "\<rho> (names ! i, 0) [] = Ts ! i" if "i < length Ts" for i
  proof -
    have "distinct (map (\<lambda>a. ((a, 0 :: integer), [] :: psort)) names)"
      using dnames by (simp add: distinct_map inj_on_def)
    with that lnames show ?thesis
      using map_of_zip_nth[of "map (\<lambda>a. ((a, 0 :: integer), [] :: psort)) names" Ts i] by (simp add: \<rho>_def)
  qed
  let ?cm = "map (\<lambda>(_, V). ((case V of TVar _ S \<Rightarrow> S | _ \<Rightarrow> []), V)) ?pm"
  have hU: "ok (unconstrain_atyp ?pm ?cm U) (f U)" if "U \<in> tatoms A" for U
  proof -
    from that sTs obtain i where i: "i < length Ts" "U = Ts ! i" by (metis in_set_conv_nth)
    have "map_of ?pm U = Some (TVar (names ! i, 0) [])"
      unfolding pm using i dTs lnames by (simp add: map_of_zip_nth)
    then show ?thesis using fU[OF i(1)] i(2) by (simp add: unconstrain_atyp_def)
  qed
  have e1: "mapM (\<lambda>T. do {S \<leftarrow> sort_of_atyp T; return (T, S)}) Ts = return (map (\<lambda>T. (T, [])) Ts)"
    using pres by (simp add: return_def)
  have e2: "map_typesM (map_atypsM (unconstrain_atyp ?pm ?cm)) A = return (map_types (map_atyps f) A)"
    using map_typesM_ok[of A "unconstrain_atyp ?pm ?cm" f] hU by (simp add: return_def)
  have cs: "concat (map (\<lambda>(_, V). case V of TVar ai S \<Rightarrow> map (\<lambda>c. mk_of_class (TVar ai []) c) S | _ \<Rightarrow> []) ?cm) = []"
    unfolding pm by (fastforce dest: set_zip_rightD)
  have lp: "length (map (\<lambda>T. (T, [] :: psort)) Ts) = length Ts" by simp
  have uc: "unconstrainT invent A = return ([], map_types (map_atyps f) A)"
    unfolding unconstrainT_def Let_def Ts_def[symmetric] e1 bindM_simps(1) lp names_def[symmetric] e2 cs
    by simp
  have ob: "(outer, B) = ([], map_types (map_atyps f) A)" using ok uc by (simp add: return_def)
  have "outer = []" using ob by simp
  moreover have "B = map_types (map_atyps f) A" using ob by simp
  moreover have "tsubst \<rho> (f U) = U" if "U \<in> tatoms A" for U
  proof -
    from that sTs obtain i where i: "i < length Ts" "U = Ts ! i" by (metis in_set_conv_nth)
    show ?thesis using fU[OF i(1)] \<rho>U[OF i(1)] i(2) by simp
  qed
  moreover have "\<exists>a. f U = TVar (a, 0) []" if "U \<in> tatoms A" for U
  proof -
    from that sTs obtain i where i: "i < length Ts" "U = Ts ! i" by (metis in_set_conv_nth)
    show ?thesis using fU[OF i(1)] i(2) by blast
  qed
  moreover have "\<rho> v S = TVar v S \<or> (S = [] \<and> \<rho> v S \<in> tatoms A)" for v S
  proof (cases "map_of (zip (map (\<lambda>a. ((a, 0), [])) names) Ts) (v, S)")
    case (Some T)
    from map_of_SomeD[OF Some] have "((v, S), T) \<in> set (zip (map (\<lambda>a. ((a, 0), [])) names) Ts)" .
    then have "S = []" "T \<in> set Ts" by (auto dest: set_zip_leftD set_zip_rightD)
    with Some sTs show ?thesis by (simp add: \<rho>_def)
  qed (simp add: \<rho>_def)
  moreover have "f U = U" if "U \<notin> tatoms A" for U
  proof -
    have "map_of (zip Ts (map (\<lambda>a. TVar (a, 0) []) names)) U = None"
      using that sTs by (auto simp: map_of_eq_None_iff dest: set_zip_leftD)
    then show ?thesis by (simp add: f_def)
  qed
  ultimately show thesis by (rule that)
qed


subsection \<open>The encoded proposition of an axiom\<close>

lemma zterm_of_App_cases:
  assumes "zterm_of ta (t $ u) = return z"
  shows "(\<exists>T c. z = ZOfclass T c) \<or> (\<exists>t' u'. zterm_of ta t = return t' \<and> zterm_of ta u = return u' \<and> z = ZApp t' u')"
  using assms by (auto simp: bindZ_eq_returnZ split: option.splits if_splits)

lemma zterm_of_Const_vars: "zterm_of ta (Const c T) = return z \<Longrightarrow> zterm_vars z = []"
proof -
  assume "zterm_of ta (Const c T) = return z"
  then obtain Us where "z = (case Us of [] \<Rightarrow> ZConst0 c | [U] \<Rightarrow> ZConst1 c (ztyp_of U) | _ \<Rightarrow> ZConst c (map ztyp_of Us))"
    by (auto simp: bindZ_eq_returnZ)
  then show ?thesis by (auto split: list.split)
qed

lemma zterm_vars_zterm_of:
  "zterm_of ta t = return z \<Longrightarrow> fnames t = {} \<Longrightarrow> v \<in> set (zterm_vars z) \<Longrightarrow>
    \<exists>T. (fst v, T) \<in> vars t \<and> snd v = ztyp_of T"
proof (induction t arbitrary: z)
  case (App t u)
  from zterm_of_App_cases[OF App.prems(1)] show ?case
  proof (elim disjE exE conjE)
    fix T c assume "z = ZOfclass T c"
    with App.prems(3) show ?thesis by simp
  next
    fix t' u' assume t': "zterm_of ta t = return t'" and u': "zterm_of ta u = return u'" and z: "z = ZApp t' u'"
    from App.prems(3) z have "v \<in> set (zterm_vars t') \<or> v \<in> set (zterm_vars u')" by simp
    then show ?thesis using App.IH(1)[OF t'] App.IH(2)[OF u'] App.prems(2) by auto
  qed
next
  case (Const c T)
  then show ?case using zterm_of_Const_vars[OF Const.prems(1)] by simp
next
  case (Abs a T b)
  from Abs.prems(1) obtain b' where "zterm_of ta b = return b'" "z = ZAbs a (ztyp_of T) b'"
    by (auto simp: bindZ_eq_returnZ)
  with Abs.IH Abs.prems(2,3) show ?case by auto
qed (auto simp: return_def)

text \<open>The propositions of the proof constants of the equality axioms have free variables:\<close>

lemma zequality_axiom_free: "a \<in> fst ` set zeq_vars \<Longrightarrow> \<exists>v\<in>set (zterm_vars (fst (zequality_axiom a))). snd (fst v) = -1"
  by (auto simp: zeq_vars_def zequality_axiom_def Let_def zax_eq_def zax_imp_def zax_var_def)

lemma not_zeq_const:
  assumes "\<forall>v\<in>set (zterm_vars A). 0 \<le> snd (fst v)"
  shows "\<not> zeq_const n A"
  using assms zequality_axiom_free by (fastforce simp: zeq_const_def)


subsection \<open>The signature condition\<close>

text \<open>
  The axioms of a theory are certified propositions without free (type) variables and sort
  constraints (\<open>Theory.add_axiom\<close>: \<open>Theory.cert_axm\<close> and \<open>Logic.varify_global\<close>), with
  non-negative indices, whose variables of the same name have the same type. For the proofs, the
  axiom and the proposition of its proof constant (\<open>Logic.unconstrainT\<close>, with the names invented by
  \<open>invent\<close>) may be used in proofs, under their name, closed as by \<open>Proofterm\<close>
  (\<^const>\<open>forall_closure\<close>) and with type arguments among their type variables. The names that
  \<open>invent\<close> returns are distinct, and there are enough of them (as for \<open>Name.invent_global_types\<close>).
\<close>

definition ax_ok :: "(integer \<Rightarrow> name list) \<Rightarrow> sign \<Rightarrow> name \<Rightarrow> pterm \<Rightarrow> bool" where
  "ax_ok invent c a A \<longleftrightarrow> pure_sig_gen.wtp (sg_alg c) (sg_ar c) (sg_consts c) A \<and>
    (\<forall>v\<in>vars A. 0 \<le> snd (fst v)) \<and> (\<forall>v\<in>ttvars A. 0 \<le> snd (fst v)) \<and> fnames A = {} \<and>
    (\<forall>U\<in>tatoms A. \<exists>v. U = TVar v []) \<and> pure_sig_gen.vtcons (vars A) \<and>
    (is_prf_sig c \<longrightarrow> sg_ax c A \<and> axm_name_ok a A \<and> sg_close c A = forall_closure A \<and>
      (\<forall>v\<in>set (sg_tyargs c A). v \<in> ttvars A) \<and>
      (\<forall>outer B. ok (unconstrainT invent A) (outer, B) \<longrightarrow> sg_ax c B \<and> axm_name_ok a B \<and>
        sg_close c B = forall_closure B \<and> (\<forall>v\<in>set (sg_tyargs c B). v \<in> ttvars B)))"

definition sign_axioms :: "(integer \<Rightarrow> name list) \<Rightarrow> sign \<Rightarrow> bool" where
  "sign_axioms invent c \<longleftrightarrow> (\<forall>n. n \<le> length (invent (integer_of_nat n)) \<and> distinct (invent (integer_of_nat n))) \<and>
    (\<forall>a A. sg_axioms c a = Some A \<longrightarrow> ax_ok invent c a A)"


subsection \<open>The rule\<close>

definition axiom_data :: "(integer \<Rightarrow> name list) \<Rightarrow> sign \<Rightarrow> name \<Rightarrow> pterm \<Rightarrow> thm_data" where
  "axiom_data invent c a A = mk_thm (axiom_rule A) (tm_sorts A) [] c (liftMP (axiom_proof invent a A))
    (zaxiom_proof_of (pure_sig_gen.ztargs (sg_consts c)) a A)"

lemma axiom_data_sel [simp]:
  "th_maxidx (axiom_data invent c a A) = maxidx_of_term A" "th_tpairs (axiom_data invent c a A) = []"
  "th_prop (axiom_data invent c a A) = A" "th_shyps (axiom_data invent c a A) = tm_sorts A"
  "th_hyps (axiom_data invent c a A) = []" "th_sign (axiom_data invent c a A) = c"
  "th_constraints (axiom_data invent c a A) = {}"
  by (simp_all add: axiom_data_def axiom_rule_def mk_rep_def)

lemma prop_args_vars: "ok (prop_args A) args \<Longrightarrow> list_all2 (\<lambda>u v. u = None \<or> u = Some v) args (variables_of A)"
  by (auto simp: prop_args_def Let_def list_all2_map1 split: pterm.splits intro!: list.rel_refl_strong)

lemma map_types_var_shape:
  "((\<exists>xi T. map_types g a = Var xi T) \<or> (\<exists>x T. map_types g a = Free x T)) \<longleftrightarrow>
    ((\<exists>xi T. a = Var xi T) \<or> (\<exists>x T. a = Free x T))"
  by (cases a) auto

lemma map_atyps_tsubst: "(\<And>U. U \<in> set (atyps T) \<Longrightarrow> \<exists>v S. U = TVar v S) \<Longrightarrow> map_atyps f T = tsubst (\<lambda>v S. f (TVar v S)) T"
proof (induction T)
  case (Type a Ts)
  have "map_atyps f T = tsubst (\<lambda>v S. f (TVar v S)) T" if "T \<in> set Ts" for T
  proof (rule Type.IH[OF that])
    fix U assume "U \<in> set (atyps T)"
    then show "\<exists>v S. U = TVar v S" using Type.prems[of U] that by auto
  qed
  then show ?case by simp
next
  case (TFree a S)
  then show ?case by auto
qed simp

lemma map_types_inst:
  "(\<And>U. U \<in> tatoms t \<Longrightarrow> \<exists>v S. U = TVar v S) \<Longrightarrow> map_types (map_atyps f) t = inst (\<lambda>v S. f (TVar v S)) t"
  by (induction t) (auto intro!: map_atyps_tsubst)

lemma tatoms_aterms: "a \<in> set (aterms t) \<Longrightarrow> tatoms a \<subseteq> tatoms t"
  by (induction t) auto

lemma tvars_atyps: "(v, S) \<in> tvars T \<Longrightarrow> TVar v S \<in> set (atyps T)"
  by (induction T) auto

lemma ttvars_tatoms: "(v, S) \<in> ttvars t \<Longrightarrow> TVar v S \<in> tatoms t"
  by (auto simp: ttvars_def tatoms_def dest: tvars_atyps)

lemma inj_map_types_aterms:
  assumes f: "\<And>U U'. U \<in> tatoms t \<Longrightarrow> U' \<in> tatoms t \<Longrightarrow> f U = f U' \<Longrightarrow> U = U'"
    and at: "\<And>U. U \<in> tatoms t \<Longrightarrow> \<exists>v S. f U = TVar v S"
  shows "inj_on (map_types (map_atyps f)) (set (aterms t))"
proof (rule inj_onI)
  fix x y assume x: "x \<in> set (aterms t)" and y: "y \<in> set (aterms t)"
    and e: "map_types (map_atyps f) x = map_types (map_atyps f) y"
  have ty: "set (atyps T) \<subseteq> tatoms t" if "z \<in> set (aterms t)" "T \<in> typs z" for z T
    using tatoms_aterms[OF that(1)] that(2) by (auto simp: tatoms_def)
  have inj: "map_atyps f T = map_atyps f T' \<Longrightarrow> T = T'" if "set (atyps T) \<subseteq> tatoms t" "set (atyps T') \<subseteq> tatoms t" for T T'
    by (rule map_atyps_inj[OF f at that])
  have tx: "\<And>T. T \<in> typs x \<Longrightarrow> set (atyps T) \<subseteq> tatoms t" and tyy: "\<And>T. T \<in> typs y \<Longrightarrow> set (atyps T) \<subseteq> tatoms t"
    using ty x y by blast+
  have "\<not> (\<exists>s u. x = s $ u)" "\<not> (\<exists>a T b. x = Abs a T b)" using x by (induction t) auto
  moreover have "\<not> (\<exists>s u. y = s $ u)" "\<not> (\<exists>a T b. y = Abs a T b)" using y by (induction t) auto
  moreover have tj: "map_atyps f T = map_atyps f T' \<Longrightarrow> T \<in> typs x \<Longrightarrow> T' \<in> typs y \<Longrightarrow> T = T'" for T T'
    using tx tyy inj by blast
  ultimately show "x = y" using e by (cases x; cases y) (auto dest!: tj)
qed

text \<open>The theorem of an axiom:\<close>

lemma thm_sem_axiom:
  assumes A: "sg_axioms c a = Some A" and sa: "sign_axioms invent c"
  shows "thm_sem TYPE('u) (axiom_data invent c a A)"
proof -
  have ao: "ax_ok invent c a A" using sa A by (simp add: sign_axioms_def)
  have inv: "n \<le> length (invent (integer_of_nat n))" "distinct (invent (integer_of_nat n))" for n
    using sa by (simp_all add: sign_axioms_def)
  have nnv: "\<forall>v\<in>vars A. 0 \<le> snd (fst v)" and nnt: "\<forall>v\<in>ttvars A. 0 \<le> snd (fst v)" and fA: "fnames A = {}"
    and sf: "\<forall>U\<in>tatoms A. \<exists>v. U = TVar v []" and vc: "pure_sig_gen.vtcons (vars A)"
    using ao by (simp_all add: ax_ok_def)
  have wtA: "pure_sig_gen.wtp (sg_alg c) (sg_ar c) (sg_consts c) A" using ao by (simp add: ax_ok_def)
  show ?thesis
  proof (rule thm_semI)
    assume "pure_sig (sg_alg (th_sign (axiom_data invent c a A))) (sg_ar (th_sign (axiom_data invent c a A)))"
    then interpret pure_sig "sg_alg c" "sg_ar c" "sg_consts c" by simp
    have "thm_wf (maxidx_of_term A) [] [] A"
      using wtA maxidx_of_term_ibelow[of A] maxidx_term_ge[of "-1" A] nnv nnt
      by (simp add: thm_wf_def wt_thm_def vars_thm_def tvars_thm_def maxidx_of_term_def)
    then show "pure_sig.thm_wf (sg_alg (th_sign (axiom_data invent c a A))) (sg_ar (th_sign (axiom_data invent c a A)))
        (sg_consts (th_sign (axiom_data invent c a A))) (th_maxidx (axiom_data invent c a A))
        (th_hyps (axiom_data invent c a A)) (th_tpairs (axiom_data invent c a A)) (th_prop (axiom_data invent c a A))"
      by simp
  next
    fix M :: "'u model"
    assume "is_model (th_sign (axiom_data invent c a A)) M"
    then have M: "is_model c M" by simp
    show "valid_in (th_sign (axiom_data invent c a A)) M (th_shyps (axiom_data invent c a A))
        (th_hyps (axiom_data invent c a A)) (th_tpairs (axiom_data invent c a A)) (th_prop (axiom_data invent c a A))"
      using is_model_axiom[OF M A] by simp
  qed
qed

end

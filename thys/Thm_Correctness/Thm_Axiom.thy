section \<open>The axiom rule on the abstract type of theorems\<close>

theory Thm_Axiom
  imports Thm_Rules4 "Pure_Thm.Pure_Axiom"
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

context prf_sig
begin

lemma all_var_typing:
  assumes R: "e \<turnstile> R : propT" "closed R" and T: "cert_typ alg ar T"
  shows "e \<turnstile> all_var (Var (x, i) T) R : propT" "closed (all_var (Var (x, i) T) R)"
proof -
  let ?b = "abstract_over_aux (Var (x, i) T) 0 R"
  have "e\<langle>0:T\<rangle> \<turnstile> ?b : propT"
    by (rule typing_abstract_over_aux[of _ _ T]) (use R in \<open>simp_all add: closed_def shift_def\<close>)
  then show "e \<turnstile> all_var (Var (x, i) T) R : propT"
    using T by (simp add: all_var_def abstract_over_def typing_all_const all_type_def cert_typ_fun)
  have "\<not> loose_bvar ?b 1"
    by (rule loose_bvar_abstract_over_aux) (use R(2) loose_bvar_mono in \<open>auto simp: closed_def\<close>)
  then show "closed (all_var (Var (x, i) T) R)"
    by (simp add: all_var_def abstract_over_def closed_def all_const_def)
qed

lemma all_var_beta:
  assumes R: "e \<turnstile> R : propT" "closed R" and T: "cert_typ alg ar T"
  obtains a f where "all_var (Var (x, i) T) R = all_const T $ f" "f $ Var (x, i) T \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> R"
proof -
  let ?b = "abstract_over_aux (Var (x, i) T) 0 R" and ?a = "if x = STR '''' then STR ''uu'' else x"
  have "e \<turnstile> all_var (Var (x, i) T) R : propT" by (rule all_var_typing[OF R T])
  then have tb: "e \<turnstile> Abs ?a T ?b : T \<rightarrow>\<^sub>T propT"
    by (auto simp: all_var_def abstract_over_def all_const_def)
  have "Abs ?a T ?b $ Var (x, i) T \<rightarrow>\<^sub>\<beta> ?b[Var (x, i) T/0]" by (rule beta.beta)
  moreover have "?b[Var (x, i) T/0] = R"
    by (rule subst_abstract_over_aux_Var) (use R(2) in \<open>simp_all add: closed_def\<close>)
  moreover have "wt (Abs ?a T ?b $ Var (x, i) T)"
    using tb T unfolding wt_def by (blast intro: typing.App typing.Var)
  ultimately have "Abs ?a T ?b $ Var (x, i) T \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> R" using conv_beta by metis
  then show thesis by (intro that[of "Abs ?a T ?b"]) (simp_all add: all_var_def abstract_over_def)
qed

end

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

context prf_sig
begin

lemma closure_typing:
  assumes "\<forall>v\<in>set vs. \<exists>xi T. v = Var xi T \<and> cert_typ alg ar T" "e \<turnstile> B : propT" "closed B"
  shows "e \<turnstile> foldr all_var vs B : propT \<and> closed (foldr all_var vs B)"
  using assms(1)
proof (induction vs)
  case (Cons w ws)
  from Cons.prems obtain y j U where w: "w = Var (y, j) U" and U: "cert_typ alg ar U" by force
  from Cons.IH Cons.prems have "e \<turnstile> foldr all_var ws B : propT" "closed (foldr all_var ws B)" by simp_all
  from all_var_typing[OF this U] show ?case by (simp add: w)
qed (use assms in simp)

end

context prf_sig
begin

text \<open>A proof of the closure applied to the variables, or to no arguments, proves the proposition:\<close>

lemma prf_ok_closure_chain:
  assumes "prf_ok ax H E e Hs p (foldr all_var vs B)"
    and vs: "\<forall>v\<in>set vs. \<exists>xi T. v = Var xi T \<and> cert_typ alg ar T"
    and B: "e \<turnstile> B : propT" "closed B"
    and os: "list_all2 (\<lambda>u v. u = None \<or> u = Some v) us vs"
  shows "prf_ok ax H E e Hs (foldl PAppt p us) B"
  using os assms(1) vs
proof (induction us vs arbitrary: p rule: list_all2_induct)
  case (Cons u us v vs)
  from Cons.prems(2) obtain x i T where v: "v = Var (x, i) T" and T: "cert_typ alg ar T" by force
  let ?R = "foldr all_var vs B"
  from closure_typing[OF _ B] Cons.prems(2) have tR: "e \<turnstile> ?R : propT" "closed ?R" by simp_all
  obtain f where f: "all_var (Var (x, i) T) ?R = all_const T $ f" "f $ Var (x, i) T \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ?R"
    by (rule all_var_beta[OF tR T])
  have "prf_ok ax H E e Hs p (all_const T $ f)" using Cons.prems(1) f(1) v by simp
  then have "prf_ok ax H E e Hs (PAppt p u) (f $ Var (x, i) T)"
    by (rule prf_ok.PAppt) (use Cons.hyps T v in \<open>auto simp: ann_ok_def ueq_refl intro: typing.Var\<close>)
  then have "prf_ok ax H E e Hs (PAppt p u) ?R" by (rule prf_ok.conv[OF _ f(2) tR(1)])
  from Cons.IH[OF this] Cons.prems(2) show ?case by simp
qed (simp add: assms)

text \<open>
  The proof constant of an axiom whose closure is that of \<open>Proofterm\<close>, applied to its variables
  (or to no arguments), proves the axiom:
\<close>

lemma prf_ok_axiom_chain:
  assumes ax: "ax B" and nm: "axm_name_ok n B" and cl: "close B = forall_closure B"
    and ta: "\<forall>(v, S)\<in>set (tyargs B). sort_ok alg S"
    and wB: "wtp B" and fB: "fnames B = {}"
    and us: "list_all2 (\<lambda>u v. u = None \<or> u = Some v) us (variables_of B)"
  shows "prf_ok ax H E e Hs (foldl PAppt (PAxm n B None) us) B"
proof -
  let ?Us = "map (\<lambda>(v, S). TVar v S) (tyargs B)"
  have vc: "\<forall>v\<in>set (variables_of B). \<exists>xi T. v = Var xi T \<and> cert_typ alg ar T"
  proof
    fix v assume "v \<in> set (variables_of B)"
    then obtain xi T where "v = Var xi T" "(xi, T) \<in> vars B" by (rule variables_of_Var[OF fB])
    with typing_vars_cert'[OF wtpD(2)[OF wB, of e]] show "\<exists>xi T. v = Var xi T \<and> cert_typ alg ar T" by blast
  qed
  have ct: "e \<turnstile> close B : propT"
    using closure_typing[OF vc wtpD(2)[OF wB] wtpD(1)[OF wB]] by (simp add: cl forall_closure_def)
  have ap: "atom_prop B ?Us = close B" by (simp add: atom_prop_def tyinst_ident)
  have ao: "atom_ok B None ?Us"
    unfolding atom_ok_def list_all2_map2 option.case(1)
    using ta by (auto intro!: list.rel_refl_strong simp: cert_typ_TVar simp del: has_sort.simps)
  have "prf_ok ax H E e Hs (PAxm n B None) (atom_prop B ?Us)"
    by (rule prf_ok.PAxm[of ax B, OF ax ao]) (use ct ap nm in simp_all)
  then have "prf_ok ax H E e Hs (PAxm n B None) (foldr all_var (variables_of B) B)"
    by (simp add: ap cl forall_closure_def)
  from prf_ok_closure_chain[OF this vc wtpD(2)[OF wB] wtpD(1)[OF wB] us] show ?thesis .
qed

end


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

lemma ok_unique: "ok m x \<Longrightarrow> ok m y \<Longrightarrow> x = y"
  by simp

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
  "ax_ok invent c a A \<longleftrightarrow> pure_sig.wtp (sg_alg c) (sg_ar c) (sg_consts c) A \<and>
    (\<forall>v\<in>vars A. 0 \<le> snd (fst v)) \<and> (\<forall>v\<in>ttvars A. 0 \<le> snd (fst v)) \<and> fnames A = {} \<and>
    (\<forall>U\<in>tatoms A. \<exists>v. U = TVar v []) \<and> pure_sig.vtcons (vars A) \<and>
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
    (zaxiom_proof_of (pure_sig.ztargs (sg_consts c)) a A)"

text \<open>
  \<open>axiom_thm invent c a\<close> (\<open>Thm.axiom thy a\<close>): \<open>None\<close> if there is no axiom of name \<open>a\<close> or the
  signature does not satisfy the condition on its axioms.
\<close>

definition axiom_thm :: "(integer \<Rightarrow> name list) \<Rightarrow> sign \<Rightarrow> name \<Rightarrow> 'u pure_thm option" where
  "axiom_thm invent c a =
    (case sg_axioms c a of
      None \<Rightarrow> None
    | Some A \<Rightarrow> if sign_axioms invent c then Some (Abs_thm (axiom_data invent c a A)) else None)"

lemma axiom_data_sel [simp]:
  "th_maxidx (axiom_data invent c a A) = maxidx_of_term A" "th_tpairs (axiom_data invent c a A) = []"
  "th_prop (axiom_data invent c a A) = A" "th_shyps (axiom_data invent c a A) = tm_sorts A"
  "th_hyps (axiom_data invent c a A) = []" "th_sign (axiom_data invent c a A) = c"
  by (simp_all add: axiom_data_def axiom_rule_def mk_rep_def)

lemma prf_idx_foldl_PAppt:
  "prf_idx P (foldl PAppt q us) \<longleftrightarrow> prf_idx P q \<and> (\<forall>u\<in>set us. \<forall>t\<in>set_option u. \<forall>v\<in>vars t. P (snd (fst v)))"
  by (induction us arbitrary: q) auto

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

lemma thm_ok_axiom:
  assumes A: "sg_axioms c a = Some A" and sa: "sign_axioms invent c"
  shows "thm_ok TYPE('u) (axiom_data invent c a A)"
proof -
  have ao: "ax_ok invent c a A" using sa A by (simp add: sign_axioms_def)
  have inv: "n \<le> length (invent (integer_of_nat n))" "distinct (invent (integer_of_nat n))" for n
    using sa by (simp_all add: sign_axioms_def)
  have nnv: "\<forall>v\<in>vars A. 0 \<le> snd (fst v)" and nnt: "\<forall>v\<in>ttvars A. 0 \<le> snd (fst v)" and fA: "fnames A = {}"
    and sf: "\<forall>U\<in>tatoms A. \<exists>v. U = TVar v []" and vc: "pure_sig.vtcons (vars A)"
    using ao by (simp_all add: ax_ok_def)
  have wtA: "pure_sig.wtp (sg_alg c) (sg_ar c) (sg_consts c) A" using ao by (simp add: ax_ok_def)
  show ?thesis
  proof (rule thm_okI)
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
  next
    assume psig: "is_prf_sig (th_sign (axiom_data invent c a A))"
    then have psig': "is_prf_sig c" by simp
    interpret prf_sig "sg_alg c" "sg_ar c" "sg_consts c" "sg_close c" "sg_tyargs c"
      using psig' by (simp add: is_prf_sig_def)
    have pA: "sg_ax c A" "axm_name_ok a A" "sg_close c A = forall_closure A" "\<forall>v\<in>set (sg_tyargs c A). v \<in> ttvars A"
      and pB: "\<And>outer B. ok (unconstrainT invent A) (outer, B) \<Longrightarrow> sg_ax c B \<and> axm_name_ok a B \<and>
        sg_close c B = forall_closure B \<and> (\<forall>v\<in>set (sg_tyargs c B). v \<in> ttvars B)"
      using ao psig' by (simp_all add: ax_ok_def)
    have wA: "wtp A" using wtA by simp
    have H: "\<And>h. h \<in> {} \<Longrightarrow> vars h = {} \<and> ttvars h = {}" by simp
    have nul: "\<And>P. prf_ok (sg_ax c) {} {} e [] P \<phi> = prf_ok (sg_ax c) {} (set []) e [] P \<phi>" for e \<phi> by simp
    show "proofs_ok (axiom_data invent c a A)" unfolding proofs_ok_def Let_def axiom_data_sel
    proof (rule conjI; intro allI impI)
      fix p assume "th_proof (axiom_data invent c a A) = returnW p"
      then have "ok (axiom_proof invent a A) p"
        by (auto simp: axiom_data_def liftMP_def returnW_def split: option.splits)
      then obtain args outer B where args: "ok (prop_args A) args" and un: "ok (unconstrainT invent A) (outer, B)"
        and p: "p = proof_combP (foldl PAppt (PAxm a B None) args) (map (\<lambda>(T, c). PClass T c) outer)"
        by (auto simp: axiom_proof_def split: prod.splits)
      obtain f \<rho> where o: "outer = []" and B: "B = map_types (map_atyps f) A"
        and fr: "\<And>U. U \<in> tatoms A \<Longrightarrow> tsubst \<rho> (f U) = U" and fv: "\<And>U. U \<in> tatoms A \<Longrightarrow> \<exists>a. f U = TVar (a, 0) []"
        and \<rho>: "\<And>v S. \<rho> v S = TVar v S \<or> (S = [] \<and> \<rho> v S \<in> tatoms A)" and fo: "\<And>U. U \<notin> tatoms A \<Longrightarrow> f U = U"
        by (rule unconstrainT_sortfree[OF sf inv(1) distinct_take[OF inv(2)] un]) blast
      have p': "p = foldl PAppt (PAxm a B None) args" by (simp add: p o proof_combP_def)
      note pb = pB[OF un]
      let ?\<rho>' = "\<lambda>v S. f (TVar v S)"
      have sfv: "\<And>U. U \<in> tatoms A \<Longrightarrow> \<exists>v S. U = TVar v S" using sf by blast
      have BI: "B = inst ?\<rho>' A" unfolding B by (rule map_types_inst[OF sfv])
      have ci': "cert_inst ?\<rho>'"
        unfolding cert_inst_def
      proof (intro allI impI)
        fix v S assume "sort_ok (sg_alg c) S"
        show "cert_typ (sg_alg c) (sg_ar c) (f (TVar v S))"
        proof (cases "TVar v S \<in> tatoms A")
          case True
          with fv obtain a' where "f (TVar v S) = TVar (a', 0) []" by blast
          then show ?thesis by (simp add: cert_typ_TVar sort_ok_def)
        next
          case False
          with \<open>sort_ok (sg_alg c) S\<close> show ?thesis by (simp add: fo cert_typ_TVar)
        qed
      qed
      have tyA: "\<And>e. e \<turnstile> A : propT" "closed A" using wtpD[OF wA] by blast+
      have "(\<lambda>j. tsubst ?\<rho>' ((\<lambda>_. propT) j)) \<turnstile> inst ?\<rho>' A : tsubst ?\<rho>' propT"
        by (rule typing_inst[OF tyA(1) cert_inst_inst_ok[OF ci']])
      then have tyB: "(\<lambda>j. tsubst ?\<rho>' ((\<lambda>_. propT) j)) \<turnstile> B : propT" by (simp add: BI propT_def)
      have wB: "wtp B" by (rule wtpI[OF _ tyB]) (use tyA(2) in \<open>simp add: BI closed_inst\<close>)
      have fB: "fnames B = {}" using fA by (simp add: B)
      have finj: "U = U'" if "U \<in> tatoms A" "U' \<in> tatoms A" "f U = f U'" for U U'
        using fr[OF that(1)] fr[OF that(2)] that(3) by metis
      have fat: "\<exists>v S. f U = TVar v S" if "U \<in> tatoms A" for U using fv[OF that] by blast
      have taB: "\<forall>(v, S)\<in>set (sg_tyargs c B). sort_ok (sg_alg c) S"
      proof (clarify)
        fix v S assume "(v, S) \<in> set (sg_tyargs c B)"
        with pb have "TVar v S \<in> tatoms B" by (auto intro: ttvars_tatoms)
        then obtain U where "U \<in> tatoms A" "TVar v S \<in> set (atyps (f U))"
          unfolding B tatoms_map_types_atyps by blast
        with fv show "sort_ok (sg_alg c) S" by (force simp: sort_ok_def)
      qed
      let ?g = "map_types (map_atyps f)"
      have vB: "variables_of B = map ?g (variables_of A)"
        by (rule variables_of_map[OF inj_map_types_aterms[OF finj fat] map_types_var_shape])
          (simp_all add: B aterms_map_types)
      let ?usB = "map (map_option ?g) args"
      have usB: "list_all2 (\<lambda>u v. u = None \<or> u = Some v) ?usB (variables_of B)"
        using prop_args_vars[OF args] unfolding vB list_all2_map1 list_all2_map2
        by (rule list_all2_mono) auto
      have idv: "prf_valid (sg_ax c) {} [] (foldl PAppt (PAxm a B None) ?usB) B"
      proof (rule prf_valid_genericI)
        show "\<And>h. h \<in> {} \<Longrightarrow> vars h = {} \<and> ttvars h = {}" by simp
        fix e
        show "prf_ok (sg_ax c) {} (set []) e [] (foldl PAppt (PAxm a B None) ?usB) B"
          by (rule prf_ok_axiom_chain[of "sg_ax c" B a, OF _ _ _ taB wB fB usB]) (use pb in simp_all)
      qed
      have c\<rho>: "cinst \<rho>"
        unfolding cinst_def wsinst_def cert_inst_def
      proof (intro conjI allI impI)
        fix v S
        show "has_sort (sg_alg c) (\<rho> v S) S" using \<rho>[of v S] by (metis has_sort_Nil has_sort_TVar_refl)
        assume "sort_ok (sg_alg c) S"
        consider "\<rho> v S = TVar v S" | "\<rho> v S \<in> tatoms A" using \<rho>[of v S] by blast
        then show "cert_typ (sg_alg c) (sg_ar c) (\<rho> v S)"
        proof cases
          case 1
          with \<open>sort_ok (sg_alg c) S\<close> show ?thesis by (simp add: cert_typ_TVar)
        next
          case 2
          with sf obtain w where "\<rho> v S = TVar w []" by blast
          then show ?thesis by (simp add: cert_typ_TVar sort_ok_def)
        qed
      qed
      have apv: "prf_valid (sg_ax c) {} [] (prf_ap \<rho> Var (foldl PAppt (PAxm a B None) ?usB)) (ap \<rho> Var B)"
        using prf_valid_ap[OF idv c\<rho> gsubst_Var H] by simp
      have iA: "inst \<rho> B = A" unfolding B by (rule inst_map_types_atyps[OF fr])
      have ia: "ap \<rho> Var (?g v) = v" if "v \<in> set (aterms A)" for v
        unfolding ap_def by (simp, rule inst_map_types_atyps[OF fr], use tatoms_aterms[OF that] in blast)
      have avs: "v \<in> set (variables_of A)" if "Some v \<in> set args" for v
      proof -
        from that obtain i where i: "i < length args" "args ! i = Some v" by (auto simp: in_set_conv_nth)
        have l: "list_all2 (\<lambda>u v. u = None \<or> u = Some v) args (variables_of A)" by (rule prop_args_vars[OF args])
        from list_all2_nthD[OF l i(1)] i(2) have "v = variables_of A ! i" by simp
        moreover have "i < length (variables_of A)" using i(1) l by (simp add: list_all2_lengthD)
        ultimately show "v \<in> set (variables_of A)" by simp
      qed
      have aA: "v \<in> set (aterms A)" if "Some v \<in> set args" for v
        using avs[OF that] by (simp add: set_variables_of)
      have av: "\<exists>xi T. v = Var xi T \<and> (xi, T) \<in> vars A" if "Some v \<in> set args" for v
        using avs[OF that] by (blast elim: variables_of_Var[OF fA])
      have "map (map_option (ap \<rho> Var)) ?usB = args"
        unfolding map_map
      proof (rule map_idI)
        fix u assume "u \<in> set args"
        show "(map_option (ap \<rho> Var) \<circ> map_option ?g) u = u"
        proof (cases u)
          case (Some v)
          with \<open>u \<in> set args\<close> have "v \<in> set (aterms A)" by (intro aA) simp
          then show ?thesis using Some by (simp add: ia)
        qed simp
      qed
      then have pe: "prf_ap \<rho> Var (foldl PAppt (PAxm a B None) ?usB) = p"
        unfolding p' prf_ap_def by (subst foldl_PAppt_map_option[where g = "ap \<rho> Var"]) simp_all
      have "prf_valid (sg_ax c) (set []) [] p A" using apv by (simp add: pe iA ap_def)
      moreover have "prf_idx (\<lambda>i. 0 \<le> i) p"
      proof -
        have "\<forall>u\<in>set args. \<forall>t\<in>set_option u. \<forall>v\<in>vars t. 0 \<le> snd (fst v)"
        proof (intro ballI)
          fix u t v assume "u \<in> set args" "t \<in> set_option u" "v \<in> vars t"
          then have "Some t \<in> set args" "v \<in> vars t" by auto
          with av nnv show "0 \<le> snd (fst v)" by fastforce
        qed
        then show ?thesis by (simp add: p' prf_idx_foldl_PAppt)
      qed
      moreover have "prf_nolb 0 p"
      proof -
        have "\<forall>u\<in>set args. \<forall>t. u = Some t \<longrightarrow> \<not> loose_bvar t 0"
          using av by fastforce
        then show ?thesis by (simp add: p' prf_nolb_foldl_PAppt')
      qed
      ultimately show "prf_valid (sg_ax c) (set []) [] p A \<and> prf_idx (\<lambda>i. 0 \<le> i) p \<and> prf_nolb 0 p" by blast
    next
      fix z assume "th_zproof (axiom_data invent c a A) = return z"
      then obtain zA where zA: "zterm_of ztargs A = return zA" and z: "z = ZConstp (zproof_const (ZAxiom a) zA)"
        by (auto simp: axiom_data_def zaxiom_proof_of_def bindZ_eq_returnZ)
      have tyA: "\<And>e. e \<turnstile> A : propT" "closed A" using wtpD[OF wA] by blast+
      have nA: "noneg A" using nnv nnt
        by (fastforce simp: noneg_def tnoneg_def ttvars_def integer_nonneg_ne_m1)
      have dz: "zdec zA = A"
        using zterm_of_zdec[OF tyA(1)] nA zA by (auto simp: noneg_def tnoneg_def)
      have zvA: "\<exists>T. (fst v, T) \<in> vars A \<and> snd v = ztyp_of T" if "v \<in> set (zterm_vars zA)" for v
        by (rule zterm_vars_zterm_of[OF zA fA that])
      have nz: "\<not> zeq_const a zA"
        by (rule not_zeq_const) (use zvA nnv in fastforce)
      define tab where "tab = fold (\<lambda>v. zv_update (v, ZVar (fst v) (snd v))) (zterm_vars zA) zv_empty"
      define instT where "instT = fold (\<lambda>v. zt_update (v, ZTVar (fst v) (snd v))) (concat (map ztyp_tvars (zterm_types zA))) zt_empty"
      have zc: "z = ZConstp ((ZAxiom a, zA), (instT, tab))" by (simp add: z zproof_const_def tab_def instT_def)
      have lk: "zv_lookup tab k = (if k \<in> set (zterm_vars zA) then Some (ZVar (fst k) (snd k)) else None)" for k
        by (simp add: tab_def zv_lookup_fold_update)
      let ?look = "\<lambda>xi. map_option zdec (zv_lookup_name tab xi)"
      have ztr: "zprf_tr z = zax_tr a A ?look" by (simp add: zc zconst_tr_def nz dz)
      have look: "?look xi = None \<or> ?look xi = Some (Var xi T)" if "(xi, T) \<in> vars A" for xi T
      proof (cases "zv_lookup_name tab xi")
        case (Some u)
        from zv_lookup_nameD[OF Some] obtain T' where "zv_lookup tab (xi, T') = Some u" by blast
        then have u: "(xi, T') \<in> set (zterm_vars zA)" "u = ZVar xi T'" by (simp_all add: lk split: if_splits)
        from zvA[OF u(1)] obtain T0 where "(xi, T0) \<in> vars A" "T' = ztyp_of T0" by auto
        moreover have "T0 = T" using vc \<open>(xi, T0) \<in> vars A\<close> that unfolding vtcons_def by blast
        ultimately have T': "T' = ztyp_of T" by simp
        have "snd xi \<noteq> -1" using nnv that by fastforce
        moreover have "typ_of (ztyp_of T) = T"
        proof (rule typ_of_ztyp_of)
          show "\<forall>(v, S)\<in>tvars T. snd v \<noteq> -1"
            using nnt that by (fastforce simp: ttvars_def integer_nonneg_ne_m1 dest: vars_typs)
        qed
        ultimately show ?thesis by (simp add: Some u T')
      qed simp
      have us: "list_all2 (\<lambda>u v. u = None \<or> u = Some v)
          (map (\<lambda>v. case v of Var xi _ \<Rightarrow> ?look xi | _ \<Rightarrow> None) (variables_of A)) (variables_of A)"
        unfolding list_all2_map1
        by (rule list.rel_refl_strong) (auto elim!: variables_of_Var[OF fA] dest: look)
      have taA: "\<forall>(v, S)\<in>set (sg_tyargs c A). sort_ok (sg_alg c) S"
        using pA(4) sf by (force dest: ttvars_tatoms simp: sort_ok_def)
      have v: "prf_valid (sg_ax c) {} [] (zprf_tr z) A"
        unfolding ztr zax_tr_def term_variables_eq
      proof (rule prf_valid_genericI)
        show "\<And>h. h \<in> {} \<Longrightarrow> vars h = {} \<and> ttvars h = {}" by simp
        fix e
        show "prf_ok (sg_ax c) {} (set []) e [] (foldl PAppt (PAxm a A None)
            (map (\<lambda>v. case v of Var xi _ \<Rightarrow> ?look xi | _ \<Rightarrow> None) (variables_of A))) A"
          by (rule prf_ok_axiom_chain[of "sg_ax c" A a, OF pA(1,2,3) taA wA fA us])
      qed
      have "zvalid (sg_ax c) (set []) [] z A" by (rule zvalidI[OF HOL.refl]) (use v in simp)
      moreover have "zinv z"
      proof -
        have "ztab_names_ok tab"
          unfolding ztab_names_ok_def
        proof (intro allI impI)
          fix k1 k2 assume "zv_lookup tab k1 \<noteq> None" "zv_lookup tab k2 \<noteq> None" "fst k1 = fst k2"
          then have "k1 \<in> set (zterm_vars zA)" "k2 \<in> set (zterm_vars zA)" "fst k1 = fst k2"
            by (simp_all add: lk split: if_splits)
          then obtain T1 T2 where "(fst k1, T1) \<in> vars A" "snd k1 = ztyp_of T1" "(fst k2, T2) \<in> vars A"
              "snd k2 = ztyp_of T2" "fst k1 = fst k2"
            using zvA by blast
          moreover from this(1,3,5) have "T1 = T2" using vc unfolding vtcons_def by metis
          ultimately show "k1 = k2" by (simp add: prod_eq_iff)
        qed
        moreover have "zterm_ok t" if "zv_lookup tab k = Some t" for k t
        proof -
          from that have k: "k \<in> set (zterm_vars zA)" "t = ZVar (fst k) (snd k)" by (simp_all add: lk split: if_splits)
          from zvA[OF k(1)] obtain T where T: "(fst k, T) \<in> vars A" "snd k = ztyp_of T" by blast
          have "tnn T" using nnt T(1) by (fastforce simp: tnn_def ttvars_def dest: vars_typs)
          with T nnv show ?thesis by (fastforce simp: k(2) ztyp_ok_ztyp_of)
        qed
        ultimately show ?thesis by (simp add: zc)
      qed
      moreover have "znolb 0 z" by (simp add: zc lk)
      moreover have "zhyps_ok z" by (simp add: zc zhyps_ok_def)
      ultimately show "zvalid (sg_ax c) (set []) [] z A \<and> zinv z \<and> znolb 0 z \<and> zhyps_ok z" by blast
    qed
  qed
qed

theorem axiom_thm:
  assumes "axiom_thm invent c a = Some th"
  obtains A where "sg_axioms c a = Some A" "sign_axioms invent c" "rep_thm th = axiom_data invent c a A"
proof -
  from assms obtain A where A: "sg_axioms c a = Some A" and sa: "sign_axioms invent c"
    and th: "th = Abs_thm (axiom_data invent c a A)"
    by (auto simp: axiom_thm_def split: option.splits if_splits)
  show thesis by (rule that[OF A sa]) (simp add: th Abs_thm_inverse thm_ok_axiom[OF A sa])
qed

lemma axiom_thm_defined: "sg_axioms c a \<noteq> None \<Longrightarrow> sign_axioms invent c \<Longrightarrow> axiom_thm invent c a \<noteq> None"
  by (auto simp: axiom_thm_def)

end
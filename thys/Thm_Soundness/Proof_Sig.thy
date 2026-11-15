section \<open>Signatures of proofs, and the decoding of tight terms\<close>

theory Proof_Sig
  imports Free_Subst "Pure_Thm.Pure_Rules"
begin

text \<open>
  The definitions on proofs that the statement of the rules needs: what a signature has to
  provide for the proof judgments (\<open>prf_sig\<close>, \<open>prf_eq\<close>), the type arguments of constants in
  tight terms (\<open>ztargs\<close>) and the decoding of tight terms (\<open>zdec\<close>). The judgments themselves
  and all theorems on proofs are in the theories \<open>Proof_Judgment\<close> to \<open>Proof_Closed\<close>, which no
  theory on the validity of theorems imports.
\<close>

subsection \<open>Propositions of atoms\<close>

text \<open>The instance of type variables at type arguments, by position:\<close>

definition tyinst :: "(indexname \<times> psort) list \<Rightarrow> ptyp list \<Rightarrow> tinst" where
  "tyinst vs Us v S = (case map_of (zip vs Us) (v, S) of Some U \<Rightarrow> U | None \<Rightarrow> TVar v S)"

text \<open>\<open>Logic.mk_of_class\<close>\<close>

definition of_class :: "ptyp \<Rightarrow> pclass \<Rightarrow> pterm" where
  "of_class T c = Const (c + STR ''_class'') (Type STR ''itself'' [T] \<rightarrow>\<^sub>T propT) $
    Const STR ''Pure.type'' (Type STR ''itself'' [T])"

text \<open>
  Axioms have unique names in Isabelle: the name \<open>Pure.reflexive\<close> stands for the reflexivity
  axiom of Pure, which \<open>Proofterm.is_reflexive_proof\<close> relies on.
\<close>

definition refl_axiom :: pterm where
  "refl_axiom = (let aT = TVar (String.implode [CHR 0x27, CHR ''a''], 0) []; x = Var (STR ''x'', 0) aT
    in Const STR ''Pure.eq'' (aT \<rightarrow>\<^sub>T aT \<rightarrow>\<^sub>T propT) $ x $ x)"

definition axm_name_ok :: "name \<Rightarrow> pterm \<Rightarrow> bool" where
  "axm_name_ok a A \<longleftrightarrow> (a = STR ''Pure.reflexive'' \<longrightarrow> A = refl_axiom)"

text \<open>
  The closure of the proposition of an atom over its variables and the order of its type
  variables are parameters; the closure is closed, has no schematic variables, and its type
  variables are among the type arguments.
\<close>

locale prf_sig_gen = pure_sig_gen alg ar ctab loose
  for alg :: algebra and ar :: "name \<Rightarrow> nat" and ctab :: "name \<Rightarrow> ptyp option"
    and loose :: "indexname set" +
  fixes close :: "pterm \<Rightarrow> pterm" and tyargs :: "pterm \<Rightarrow> (indexname \<times> psort) list"
  assumes closed_close: "closed (close A)" and vars_close: "vars (close A) = {}"
    and ttvars_close: "ttvars (close A) \<subseteq> set (tyargs A)"
    and ar_prop: "ar STR ''prop'' = 0"

text \<open>The same for a signature without loose names:\<close>

locale prf_sig = pure_sig alg ar ctab
  for alg :: algebra and ar :: "name \<Rightarrow> nat" and ctab :: "name \<Rightarrow> ptyp option" +
  fixes close :: "pterm \<Rightarrow> pterm" and tyargs :: "pterm \<Rightarrow> (indexname \<times> psort) list"
  assumes closed_close: "closed (close A)" and vars_close: "vars (close A) = {}"
    and ttvars_close: "ttvars (close A) \<subseteq> set (tyargs A)"
    and ar_prop: "ar STR ''prop'' = 0"

sublocale prf_sig \<subseteq> prf_sig_gen alg ar ctab "{}" close tyargs
  by unfold_locales (rule closed_close vars_close ttvars_close ar_prop)+

text \<open>The general locale holds where the locale without loose names holds:\<close>

lemma prf_sig_gen_of:
  assumes "prf_sig alg ar close tyargs"
  shows "prf_sig_gen alg ar close tyargs"
  using assms unfolding prf_sig_def prf_sig_gen_def prf_sig_axioms_def prf_sig_gen_axioms_def pure_sig_def
  by simp


subsection \<open>The equality axioms\<close>

text \<open>
  The closures of the equality axioms over their variables, in the order of
  \<open>Thm.forall_intr_vars\<close>, which \<open>Proofchecker.thm_of_proof\<close> uses for axioms and which the
  equality proofs of \<open>Proofterm\<close> instantiate:
\<close>

definition eq_names :: "name set" where
  "eq_names = {STR ''reflexive'', STR ''symmetric'', STR ''transitive'', STR ''equal_intr'', STR ''equal_elim'',
    STR ''abstract_rule'', STR ''combination''}"

definition eq_all :: "ptyp \<Rightarrow> pterm \<Rightarrow> pterm" where
  "eq_all T B = all_const T $ Abs STR ''x'' T B"

definition eq_closure :: "name \<Rightarrow> pterm" where
  "eq_closure a =
    (let aT = ax_aT; bT = ax_bT
     in if a = STR ''reflexive'' then eq_all aT (ax_eq aT (Bound 0) (Bound 0))
     else if a = STR ''symmetric'' then eq_all aT (eq_all aT (mk_implies (ax_eq aT (Bound 1) (Bound 0)) (ax_eq aT (Bound 0) (Bound 1))))
     else if a = STR ''transitive'' then
       eq_all aT (eq_all aT (eq_all aT (list_implies [ax_eq aT (Bound 2) (Bound 1), ax_eq aT (Bound 1) (Bound 0)]
         (ax_eq aT (Bound 2) (Bound 0)))))
     else if a = STR ''equal_intr'' then
       eq_all propT (eq_all propT (list_implies [mk_implies (Bound 1) (Bound 0), mk_implies (Bound 0) (Bound 1)]
         (ax_eq propT (Bound 1) (Bound 0))))
     else if a = STR ''equal_elim'' then
       eq_all propT (eq_all propT (list_implies [ax_eq propT (Bound 1) (Bound 0), Bound 1] (Bound 0)))
     else if a = STR ''abstract_rule'' then
       eq_all (aT \<rightarrow>\<^sub>T bT) (eq_all (aT \<rightarrow>\<^sub>T bT) (mk_implies (eq_all aT (ax_eq bT (Bound 2 $ Bound 0) (Bound 1 $ Bound 0)))
         (ax_eq (aT \<rightarrow>\<^sub>T bT) (Abs STR ''x'' aT (Bound 2 $ Bound 0)) (Abs STR ''x'' aT (Bound 1 $ Bound 0)))))
     else eq_all (aT \<rightarrow>\<^sub>T bT) (eq_all (aT \<rightarrow>\<^sub>T bT) (eq_all aT (eq_all aT
       (list_implies [ax_eq (aT \<rightarrow>\<^sub>T bT) (Bound 3) (Bound 2), ax_eq aT (Bound 1) (Bound 0)]
         (ax_eq bT (Bound 3 $ Bound 1) (Bound 2 $ Bound 0)))))))"

locale prf_eq = prf_sig alg ar ctab close tyargs
  for alg ar ctab close tyargs +
  fixes ax :: "pterm \<Rightarrow> bool"
  assumes eq_ok_ctab: "eq_ok"
    and eq_ax: "\<And>a. a \<in> eq_names \<Longrightarrow> ax (equality_axiom a)"
    and eq_close: "\<And>a. a \<in> eq_names \<Longrightarrow> close (equality_axiom a) = eq_closure a"
    and eq_tyargs: "\<And>a. a \<in> eq_names \<Longrightarrow> tyargs (equality_axiom a) = [((tvar_a, 0), []), ((tvar_b, 0), [])]"


subsection \<open>Tight terms\<close>

lemma ex_returnZ [simp]: "(\<exists>z. return x = return z \<and> P z) \<longleftrightarrow> P x"
  by (auto simp: return_def)

lemma returnZ_inj [simp]: "return x = return y \<longleftrightarrow> x = y"
  by (simp add: return_def)


subsection \<open>The monad\<close>

lemma bindZ_eq_returnZ: "bindM m f = return y \<longleftrightarrow> (\<exists>x. m = return x \<and> f x = return y)"
  by (auto simp: bindM_def return_def split: option.splits xres.splits)

lemma liftMZ_eq_returnZ: "liftMZ m = return x \<longleftrightarrow> ok m x"
  by (auto simp: liftMZ_def return_def split: option.splits xres.splits)

lemma liftOZ_eq_returnZ: "liftOZ m = return x \<longleftrightarrow> m = Some x"
  by (auto simp: liftOZ_def return_def)

lemma mapZ_eq_returnZ: "mapM f xs = return ys \<longleftrightarrow> list_all2 (\<lambda>x y. f x = return y) xs ys"
  by (induction xs arbitrary: ys) (auto simp: bindZ_eq_returnZ list_all2_Cons1)

text \<open>The same with \<^const>\<open>return\<close> unfolded:\<close>

lemmas Z_ok_simps = bindZ_eq_returnZ[unfolded return_def] liftMZ_eq_returnZ[unfolded return_def]
  liftOZ_eq_returnZ[unfolded return_def] mapZ_eq_returnZ[unfolded return_def]



subsection \<open>Types\<close>

lemma typ_of_ztyp_of: "\<forall>(v, S)\<in>tvars T. snd v \<noteq> -1 \<Longrightarrow> typ_of (ztyp_of T) = T"
proof (induction T rule: ztyp_of.induct)
  case (3 c)
  then show ?case by (simp add: propT_def)
next
  case (6 c T U V Ts)
  have h: "typ_of (ztyp_of X) = X" if X: "X \<in> set (T # U # V # Ts)" for X
  proof -
    have "\<forall>a\<in>tvars X. case a of (v, S) \<Rightarrow> snd v \<noteq> -1" using "6.prems" X by auto
    with X "6.IH"[of X] show ?thesis by auto
  qed
  have "map (typ_of \<circ> ztyp_of) (T # U # V # Ts) = T # U # V # Ts" by (rule map_idI) (simp add: h)
  then show ?case by (simp del: list.map add: comp_def)
qed auto

lemma set_dedup [simp]: "set (dedup xs) = set xs"
  by (induction xs rule: dedup.induct) auto

lemma distinct_dedup: "distinct (dedup xs)"
  by (induction xs rule: dedup.induct) auto

lemma set_typ_tvars [simp]: "set (typ_tvars T) = tvars T"
  by (induction T rule: typ_tvars.induct) auto

lemma map_of_zip_map_self: "distinct xs \<Longrightarrow> x \<in> set xs \<Longrightarrow> map_of (zip xs (map f xs)) x = Some (f x)"
  by (induction xs) auto

lemma tsubst_inj_tvars:
  "tsubst \<rho> U = tsubst \<rho>' U \<Longrightarrow> (v, S) \<in> tvars U \<Longrightarrow> \<rho> v S = \<rho>' v S"
proof (induction U)
  case (Type a Ts)
  then obtain T where T: "T \<in> set Ts" "(v, S) \<in> tvars T" by auto
  from Type.prems(1) have "\<forall>T\<in>set Ts. tsubst \<rho> T = tsubst \<rho>' T" by (simp add: map_eq_conv)
  with T Type.IH show ?case by blast
qed auto


subsection \<open>Type arguments of constants\<close>

text \<open>The type parameters of a declared type, in the order of their first occurrence.\<close>

definition tparams :: "ptyp \<Rightarrow> (indexname \<times> psort) list" where
  "tparams U = dedup (typ_tvars U)"

lemma set_tparams: "set (tparams U) = tvars U"
  by (simp add: tparams_def)

text \<open>The instance of a type parameter of \<open>U\<close> in an instance \<open>T\<close> of \<open>U\<close>.\<close>

definition targ :: "ptyp \<Rightarrow> ptyp \<Rightarrow> indexname \<times> psort \<Rightarrow> ptyp" where
  "targ U T p = (THE X. \<exists>\<rho>. T = tsubst \<rho> U \<and> \<rho> (fst p) (snd p) = X)"

lemma targ_eq: "T = tsubst \<rho> U \<Longrightarrow> (v, S) \<in> tvars U \<Longrightarrow> targ U T (v, S) = \<rho> v S"
  unfolding targ_def by (rule the_equality) (auto dest: tsubst_inj_tvars)

definition zeq_vars :: "(name \<times> name list) list" where
  "zeq_vars = [(STR ''reflexive'', [STR ''x'']), (STR ''symmetric'', [STR ''x'', STR ''y'']),
    (STR ''transitive'', [STR ''x'', STR ''y'', STR ''z'']), (STR ''equal_intr'', [STR ''A'', STR ''B'']),
    (STR ''equal_elim'', [STR ''A'', STR ''B'']), (STR ''abstract_rule'', [STR ''f'', STR ''g'']),
    (STR ''combination'', [STR ''f'', STR ''g'', STR ''x'', STR ''y''])]"

definition zv_lookup_name :: "'a zvtab \<Rightarrow> indexname \<Rightarrow> 'a option" where
  "zv_lookup_name t xi =
    (if \<exists>!T. zv_lookup t (xi, T) \<noteq> None then zv_lookup t (xi, THE T. zv_lookup t (xi, T) \<noteq> None)
     else None)"

text \<open>
  The type instances that a proof constant records, for a list of type variables. A type
  variable without an entry does not occur in the proposition of the constant; its instance is
  \<open>prop\<close>, which every map of types leaves as it is.
\<close>

lift_definition zt_lookup :: "'a ztvtab \<Rightarrow> indexname \<times> psort \<Rightarrow> 'a option" is "\<lambda>m k. m k" .

lemma zt_lookup_empty [simp]: "zt_lookup zt_empty k = None"
  by transfer simp

lemma zt_lookup_update [simp]: "zt_lookup (zt_update (k', x) t) k = (if k = k' then Some x else zt_lookup t k)"
  by transfer simp

lemma zt_lookup_map [simp]: "zt_lookup (zt_map f t) k = map_option f (zt_lookup t k)"
  by transfer simp

definition zinst_typs :: "ztyp ztvtab \<Rightarrow> (indexname \<times> psort) list \<Rightarrow> ptyp list" where
  "zinst_typs instT vs = map (\<lambda>v. case zt_lookup instT v of Some T \<Rightarrow> typ_of T | None \<Rightarrow> propT) vs"

lemma zinst_typs_map:
  assumes "\<And>k T. zt_lookup instT k = Some T \<Longrightarrow> h (typ_of T) = typ_of (hz T)" "h propT = propT"
    "\<And>k. zt_lookup instT' k = map_option hz (zt_lookup instT k)"
  shows "map h (zinst_typs instT vs) = zinst_typs instT' vs"
  unfolding zinst_typs_def by (auto simp: assms split: option.splits)

text \<open>
  The type variables of the equality axioms in tight proofs (free, index \<open>-1\<close>), in the order of
  the type arguments of the classic axioms, and the classic equality axioms with type arguments:
\<close>

definition zeq_tvars :: "(indexname \<times> psort) list" where
  "zeq_tvars = [((tvar_a, -1), []), ((tvar_b, -1), [])]"

definition equality_axmT :: "name \<Rightarrow> ptyp list \<Rightarrow> prf" where
  "equality_axmT a Us = PAxm (STR ''Pure.'' + a) (equality_axiom a) (Some Us)"

definition zeq_tr :: "name \<Rightarrow> ptyp list \<Rightarrow> (name \<Rightarrow> pterm option) \<Rightarrow> prf" where
  "zeq_tr n Us look =
    (case find (\<lambda>(a, xs). n = STR ''Pure.'' + a) zeq_vars of
      Some (a, xs) \<Rightarrow>
        (case those (map look xs) of
          Some ts \<Rightarrow> foldl (\<lambda>p t. PAppt p (Some t)) (equality_axmT a Us) ts
        | None \<Rightarrow> MinProof)
    | None \<Rightarrow> MinProof)"

text \<open>The proof constants of the equality axioms, and the translation of the other axioms:\<close>

definition zeq_const :: "name \<Rightarrow> zterm \<Rightarrow> bool" where
  "zeq_const n A \<longleftrightarrow> (\<exists>a\<in>fst ` set zeq_vars. n = STR ''Pure.'' + a \<and> A = fst (zequality_axiom a))"

text \<open>The variables of a term in the order of their first occurrence (\<open>Proofterm.variables_of\<close>):\<close>

fun term_atoms :: "pterm \<Rightarrow> pterm list" where
  "term_atoms (t $ u) = term_atoms t @ term_atoms u"
| "term_atoms (Abs _ _ b) = term_atoms b"
| "term_atoms t = [t]"

definition term_variables :: "pterm \<Rightarrow> pterm list" where
  "term_variables t = rev (fold (\<lambda>a acc. case a of Var _ _ \<Rightarrow> List.insert a acc | Free _ _ \<Rightarrow> List.insert a acc
    | _ \<Rightarrow> acc) (term_atoms t) [])"

definition zax_tr :: "name \<Rightarrow> pterm \<Rightarrow> ptyp list \<Rightarrow> (indexname \<Rightarrow> pterm option) \<Rightarrow> prf" where
  "zax_tr n A Us look =
    foldl PAppt (PAxm n A (Some Us)) (map (\<lambda>v. case v of Var xi _ \<Rightarrow> look xi | _ \<Rightarrow> None) (term_variables A))"

text \<open>
  Proof boxes of theorems are translated like axioms, to classic proof boxes of their propositions
  with their type arguments; the data of the box (serial, name, body), which the proof judgment
  does not inspect, is left unspecified.
\<close>

definition zthm_head :: "pterm \<Rightarrow> ptyp list \<Rightarrow> thm_header \<times> thm_body" where
  "zthm_head A Us = (Thm_Header undefined A (Some Us), undefined)"

definition zthm_tr :: "pterm \<Rightarrow> ptyp list \<Rightarrow> (indexname \<Rightarrow> pterm option) \<Rightarrow> prf" where
  "zthm_tr A Us look =
    foldl PAppt (PThm (zthm_head A Us)) (map (\<lambda>v. case v of Var xi _ \<Rightarrow> look xi | _ \<Rightarrow> None) (term_variables A))"

lemma hd_set_types_Thm_Header [simp]: "hd_set_types (Thm_Header i A Ts) Us = Thm_Header i A Us"
  by (simp add: hd_set_types_def)

context pure_sig_gen
begin

text \<open>
  \<open>Consts.typargs\<close>: \<open>Pure.imp\<close> has none, \<open>Pure.all\<close> the type of its bound variable; other
  constants the instances of the type parameters of their declared type, if the type is an
  instance of it (otherwise \<open>Type.raw_match\<close> raises an exception).
\<close>

definition ztargs :: ztypargs where
  "ztargs c T =
    (if c = STR ''Pure.imp'' then return []
     else if c = STR ''Pure.all'' then
       (case T of Type _ [Type _ [U, _], _] \<Rightarrow> return [U] | _ \<Rightarrow> raise (Type_Error STR ''typargs'' [T] []))
     else case ctab c of
       None \<Rightarrow> raise (Type_Error STR ''typargs'' [T] [])
     | Some U \<Rightarrow>
         if \<exists>\<rho>. T = tsubst \<rho> U then return (map (targ U T) (tparams U))
         else raise (Type_Error STR ''typargs'' [T] []))"

text \<open>The type of a constant with given type arguments.\<close>

definition zconst_typ :: "name \<Rightarrow> ptyp list \<Rightarrow> ptyp" where
  "zconst_typ c Us =
    (if c = STR ''Pure.imp'' then imp_type
     else if c = STR ''Pure.all'' then (case Us of [U] \<Rightarrow> (U \<rightarrow>\<^sub>T propT) \<rightarrow>\<^sub>T propT | _ \<Rightarrow> dummyT)
     else case ctab c of
       None \<Rightarrow> dummyT
     | Some U \<Rightarrow> tsubst (\<lambda>v S. case map_of (zip (tparams U) Us) (v, S) of Some X \<Rightarrow> X | None \<Rightarrow> dummyT) U)"

lemma ztargs_const_typ_ok:
  assumes "const_typ_ok ctab c T"
  shows "\<exists>Us. ztargs c T = return Us \<and> zconst_typ c Us = T \<and> (\<forall>U\<in>set Us. tvars U \<subseteq> tvars T)"
proof (cases "c = STR ''Pure.imp''")
  case True
  with assms show ?thesis by (simp add: ztargs_def zconst_typ_def const_typ_ok_def imp_type_def propT_def)
next
  case ni: False
  show ?thesis
  proof (cases "c = STR ''Pure.all''")
    case True
    with assms obtain U where T: "T = (U \<rightarrow>\<^sub>T propT) \<rightarrow>\<^sub>T propT"
      by (auto simp: const_typ_ok_def propT_def)
    then show ?thesis using True ni by (simp add: ztargs_def zconst_typ_def propT_def)
  next
    case na: False
    with ni assms obtain U \<rho> where U: "ctab c = Some U" and T: "T = tsubst \<rho> U"
      by (auto simp: const_typ_ok_def)
    let ?Us = "map (targ U T) (tparams U)"
    have "zconst_typ c ?Us = tsubst \<rho> U"
      unfolding zconst_typ_def using ni na U
    proof (simp, intro tsubst_cong)
      fix v S assume vS: "(v, S) \<in> tvars U"
      then have "map_of (zip (tparams U) ?Us) (v, S) = Some (targ U T (v, S))"
        by (intro map_of_zip_map_self) (simp_all add: tparams_def distinct_dedup)
      with targ_eq[OF T vS] show "(case map_of (zip (tparams U) ?Us) (v, S) of None \<Rightarrow> dummyT | Some X \<Rightarrow> X) = \<rho> v S"
        by simp
    qed
    moreover have "tvars X \<subseteq> tvars T" if "X \<in> set ?Us" for X
    proof -
      from that obtain v S where vS: "(v, S) \<in> tvars U" "X = targ U T (v, S)"
        by (auto simp: set_tparams)
      then have "X = \<rho> v S" using targ_eq[OF T] by simp
      then show ?thesis using vS(1) T by (auto simp: tvars_tsubst)
    qed
    ultimately show ?thesis using ni na U T by (auto simp: ztargs_def)
  qed
qed


subsection \<open>Decoding\<close>

fun zdec :: "zterm \<Rightarrow> pterm" where
  "zdec (ZVar xi T) = (if snd xi = -1 then Free (fst xi) (typ_of T) else Var xi (typ_of T))"
| "zdec (ZBound i) = Bound i"
| "zdec (ZConst0 c) = Const c (zconst_typ c [])"
| "zdec (ZConst1 c T) = Const c (zconst_typ c [typ_of T])"
| "zdec (ZConst c Ts) = Const c (zconst_typ c (map typ_of Ts))"
| "zdec (ZAbs a T t) = Abs a (typ_of T) (zdec t)"
| "zdec (ZApp t u) = zdec t $ zdec u"
| "zdec (ZOfclass T c) = of_class (typ_of T) c"

text \<open>
  The conversion of a well-typed term without schematic (type) variables of index \<open>-1\<close> never
  raises an exception, and decoding inverts it.
\<close>

lemma zterm_of_zdec:
  assumes "e \<turnstile> t : T" "\<forall>v\<in>vars t. snd (fst v) \<noteq> -1" "\<forall>U\<in>typs t. \<forall>(v, S)\<in>tvars U. snd v \<noteq> -1"
  shows "\<exists>z. zterm_of ztargs t = return z \<and> zdec z = t"
  using assms
proof (induction rule: typing.induct)
  case (Const c T e)
  from ztargs_const_typ_ok[OF Const.hyps(1)] obtain Us where u: "ztargs c T = return Us" "zconst_typ c Us = T"
    "\<forall>U\<in>set Us. tvars U \<subseteq> tvars T"
    by blast
  have r1: "typ_of (ztyp_of X) = X" if "X \<in> set Us" for X
  proof (rule typ_of_ztyp_of)
    show "\<forall>(v, S)\<in>tvars X. snd v \<noteq> -1" using that u(3) Const.prems(2) by fastforce
  qed
  then have r: "map typ_of (map ztyp_of Us) = Us" by (auto intro!: map_idI)
  show ?case
  proof (cases Us rule: remdups_adj.cases)
    case 1
    then show ?thesis using u by simp
  next
    case (2 U)
    then show ?thesis using u r by simp
  next
    case (3 U V Ws)
    then show ?thesis using u r by simp
  qed
next
  case (Free T e x)
  then show ?case by (simp add: typ_of_ztyp_of)
next
  case (Var T e x)
  then show ?case by (cases x) (simp add: typ_of_ztyp_of)
next
  case (Bound i e T)
  then show ?case by simp
next
  case (Abs T e t U a)
  then show ?case by (auto simp: typ_of_ztyp_of)
next
  case (App e s T U t)
  have ps: "\<forall>v\<in>vars s. snd (fst v) \<noteq> -1" "\<forall>U\<in>typs s. \<forall>(v, S)\<in>tvars U. snd v \<noteq> -1"
    and pt: "\<forall>v\<in>vars t. snd (fst v) \<noteq> -1" "\<forall>U\<in>typs t. \<forall>(v, S)\<in>tvars U. snd v \<noteq> -1"
    using App.prems by auto
  from App.IH(1)[OF ps] obtain zs where zs: "zterm_of ztargs s = return zs" "zdec zs = s" by blast
  from App.IH(2)[OF pt] obtain zt where zt: "zterm_of ztargs t = return zt" "zdec zt = t" by blast
  show ?case
  proof (cases "\<exists>T' c. match_of_class (s $ t) = Some (T', c) \<and> s $ t = mk_of_class T' c")
    case True
    then obtain T' c where m: "match_of_class (s $ t) = Some (T', c)" and e: "s $ t = mk_of_class T' c"
      by blast
    then have t: "t = Const STR ''Pure.type'' (Type STR ''itself'' [T'])" by (simp add: mk_of_class_def)
    have "typ_of (ztyp_of T') = T'" using pt(2) t by (intro typ_of_ztyp_of) auto
    then show ?thesis using m e by (simp add: of_class_def mk_of_class_def class_suffix_def propT_def)
  next
    case False
    then show ?thesis using zs zt by (auto split: option.splits)
  qed
qed

end

end

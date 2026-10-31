section \<open>A declarative judgment for proof terms\<close>

theory Proof_Judgment
  imports Proof_Subst
begin

text \<open>
  The judgment \<open>prf_ok V H Ts Hs p \<phi>\<close> states that the proof term \<open>p\<close> of
  \<^file>\<open>~~/src/Pure/proofterm.ML\<close> proves the proposition \<open>\<phi>\<close>. Here \<open>V\<close> gives the types of the schematic
  variables, \<open>H\<close> is the set of hypotheses (\<open>Hyp\<close>), \<open>Ts\<close> are the types of the bound
  variables of the term level (\<open>Abst\<close>) and \<open>Hs\<close> the propositions of the bound variables of the
  proof level (\<open>AbsP\<close>), innermost first.

  The judgment is declarative: it does not reconstruct missing annotations, but asks for terms
  and types that fit them. Annotations may contain \<^const>\<open>dummyT\<close>, which fits every type
  (\<open>Proofterm.remove_types\<close>). Propositions are identified up to \<open>\<beta>\<eta>\<close>-conversion of their
  translations, which forget the names and types of bound variables (rule \<open>conv\<close>).

  An axiom, oracle or theorem with proposition \<open>A\<close> proves an instance of the closure of \<open>A\<close>
  over its free and schematic variables, at the type arguments in the order of the type
  variables of \<open>A\<close>; with type arguments \<open>None\<close>, at some type arguments
  (\<open>Proofchecker.thm_of_proof\<close>). The closure and the order of the type variables are
  parameters (\<open>atom_closure\<close>, \<open>atom_tyargs\<close>); the results hold for every choice in which the
  closure is closed, has no schematic variables and its type variables are among the type
  arguments.
\<close>


subsection \<open>Annotations\<close>

inductive tmatch :: "ptyp \<Rightarrow> ptyp \<Rightarrow> bool" where
  dummy: "tmatch dummyT U"
| Type: "list_all2 tmatch Ts Us \<Longrightarrow> tmatch (Type a Ts) (Type a Us)"
| TFree: "tmatch (TFree a S) (TFree a S)"
| TVar: "tmatch (TVar v S) (TVar v S)"

lemma tmatch_refl[simp]: "tmatch T T"
  by (induction T) (auto intro: tmatch.intros list.rel_refl_strong)

inductive amatch :: "pterm \<Rightarrow> pterm \<Rightarrow> bool" where
  Const: "tmatch T U \<Longrightarrow> amatch (Const a T) (Const a U)"
| Free: "tmatch T U \<Longrightarrow> amatch (Free a T) (Free a U)"
| Var: "tmatch T U \<Longrightarrow> amatch (Var x T) (Var x U)"
| Bound: "amatch (Bound i) (Bound i)"
| Abs: "tmatch T U \<Longrightarrow> amatch t u \<Longrightarrow> amatch (Abs a T t) (Abs b U u)"
| App: "amatch s s' \<Longrightarrow> amatch t t' \<Longrightarrow> amatch (s $ t) (s' $ t')"

lemma amatch_refl[simp]: "amatch t t"
  by (induction t) (auto intro: amatch.intros)

definition tann_ok :: "ptyp option \<Rightarrow> ptyp \<Rightarrow> bool" where
  "tann_ok T U \<longleftrightarrow> (case T of None \<Rightarrow> True | Some T \<Rightarrow> tmatch T U)"

lemma tann_ok_simps[simp]: "tann_ok None U" "tann_ok (Some T) U \<longleftrightarrow> tmatch T U"
  by (simp_all add: tann_ok_def)


subsection \<open>Propositions of atoms\<close>

text \<open>Substitution of the type variables (schematic and fixed) of a type, and of the types of a term.\<close>

fun asubst :: "(ptyp \<Rightarrow> ptyp) \<Rightarrow> ptyp \<Rightarrow> ptyp" where
  "asubst f (Type a Ts) = Type a (map (asubst f) Ts)"
| "asubst f T = f T"

fun atyps :: "ptyp \<Rightarrow> ptyp set" where
  "atyps (Type a Ts) = \<Union> (atyps ` set Ts)"
| "atyps T = {T}"

fun map_types :: "(ptyp \<Rightarrow> ptyp) \<Rightarrow> pterm \<Rightarrow> pterm" where
  "map_types f (Const a T) = Const a (f T)"
| "map_types f (Free a T) = Free a (f T)"
| "map_types f (Var x T) = Var x (f T)"
| "map_types f (Bound i) = Bound i"
| "map_types f (Abs a T t) = Abs a (f T) (map_types f t)"
| "map_types f (s $ t) = map_types f s $ map_types f t"

lemma asubst_cong: "(\<And>a. a \<in> atyps T \<Longrightarrow> f a = g a) \<Longrightarrow> asubst f T = asubst g T"
  by (induction T) auto

lemma map_types_cong: "(\<And>T. T \<in> csig.tys t \<Longrightarrow> f T = g T) \<Longrightarrow> map_types f t = map_types g t"
  by (induction t) (auto simp: csig.tys.simps)

definition tyarg_inst :: "ptyp list \<Rightarrow> ptyp list \<Rightarrow> ptyp \<Rightarrow> ptyp" where
  "tyarg_inst vs Us a = (case map_of (zip vs Us) a of None \<Rightarrow> a | Some U \<Rightarrow> U)"

text \<open>\<open>Logic.mk_of_class\<close>\<close>

definition of_class :: "ptyp \<Rightarrow> pclass \<Rightarrow> pterm" where
  "of_class T c = Const (c + STR ''_class'') (Type STR ''itself'' [T] \<rightarrow>\<^sub>T propT) $
    Const STR ''Pure.type'' (Type STR ''itself'' [T])"

locale prf_csig = csig ctab
  for ctab :: "name \<Rightarrow> ptyp option" +
  fixes atom_closure :: "pterm \<Rightarrow> pterm" and atom_tyargs :: "pterm \<Rightarrow> ptyp list"
  assumes vars_atom_closure: "vars (atom_closure A) = {}"
    and atyps_atom_closure: "U \<in> tys (atom_closure A) \<Longrightarrow> atyps U \<subseteq> set (atom_tyargs A)"
    and closed_atom_closure: "\<not> loose_bvar (atom_closure A) 0"
begin

definition atom_prop :: "pterm \<Rightarrow> ptyp list \<Rightarrow> pterm" where
  "atom_prop A Us = map_types (asubst (tyarg_inst (atom_tyargs A) Us)) (atom_closure A)"

definition atom_ok :: "pterm \<Rightarrow> ptyp list option \<Rightarrow> ptyp list \<Rightarrow> bool" where
  "atom_ok A Us' Us \<longleftrightarrow> length Us = length (atom_tyargs A) \<and> (case Us' of None \<Rightarrow> True | Some Us'' \<Rightarrow> Us'' = Us)"

text \<open>
  A term annotation fits a term if it is proper, its schematic variables have non-negative
  indices, and both are \<open>\<beta>\<eta>\<close>-equal after removing the types of constants and abstractions
  (\<open>Proofterm.remove_types\<close>).
\<close>

definition ann_ok :: "pterm option \<Rightarrow> pterm \<Rightarrow> bool" where
  "ann_ok t u \<longleftrightarrow> (case t of None \<Rightarrow> True | Some t \<Rightarrow>
    proper t \<and> (\<forall>x\<in>vars t. 0 \<le> snd x) \<and> tr (remove_types t) \<equiv>\<^sub>\<beta>\<^sub>\<eta> tr (remove_types u))"

lemma ann_ok_simps[simp]: "ann_ok None u"
  "ann_ok (Some t) u \<longleftrightarrow> proper t \<and> (\<forall>x\<in>vars t. 0 \<le> snd x) \<and> tr (remove_types t) \<equiv>\<^sub>\<beta>\<^sub>\<eta> tr (remove_types u)"
  by (simp_all add: ann_ok_def)


subsection \<open>The judgment\<close>

text \<open>Schematic variables have non-negative indices.\<close>

definition wty :: "(indexname \<Rightarrow> ptyp) \<Rightarrow> ptyp list \<Rightarrow> pterm \<Rightarrow> ptyp \<Rightarrow> bool" where
  "wty V Ts t T \<longleftrightarrow> has_type V Ts t T \<and> (\<forall>v\<in>vars t. 0 \<le> snd v)"

inductive prf_ok :: "(indexname \<Rightarrow> ptyp) \<Rightarrow> pterm set \<Rightarrow> ptyp list \<Rightarrow> pterm list \<Rightarrow> prf \<Rightarrow> pterm \<Rightarrow> bool"
  for V H where
  conv: "prf_ok V H Ts Hs p \<phi> \<Longrightarrow> tr \<phi> \<equiv>\<^sub>\<beta>\<^sub>\<eta> tr \<psi> \<Longrightarrow> wty V Ts \<psi> propT \<Longrightarrow> prf_ok V H Ts Hs p \<psi>"
| MinProof: "wty V Ts \<phi> propT \<Longrightarrow> prf_ok V H Ts Hs MinProof \<phi>"
| PBound: "0 \<le> i \<Longrightarrow> nat_of_integer i < length Hs \<Longrightarrow> wty V Ts (Hs ! nat_of_integer i) propT \<Longrightarrow>
    prf_ok V H Ts Hs (PBound i) (Hs ! nat_of_integer i)"
| AbsP: "wty V Ts A propT \<Longrightarrow> ann_ok t A \<Longrightarrow> prf_ok V H Ts (A # Hs) p B \<Longrightarrow>
    prf_ok V H Ts Hs (AbsP a t p) (implies $ A $ B)"
| Abst: "tann_ok T U \<Longrightarrow> prf_ok V H (U # Ts) (map (incr_bv 1 0) Hs) p B \<Longrightarrow>
    prf_ok V H Ts Hs (Abst a T p) (all_const U $ Abs b U B)"
| PAppt: "prf_ok V H Ts Hs p (all_const U $ f) \<Longrightarrow> wty V Ts t U \<Longrightarrow> ann_ok t' t \<Longrightarrow>
    prf_ok V H Ts Hs (PAppt p t') (f $ t)"
| PAppp: "prf_ok V H Ts Hs p (implies $ A $ B) \<Longrightarrow> prf_ok V H Ts Hs q A \<Longrightarrow> prf_ok V H Ts Hs (PAppp p q) B"
| Hyp: "t \<in> H \<Longrightarrow> wty V Ts t propT \<Longrightarrow> prf_ok V H Ts Hs (Hyp t) t"
| PAxm: "atom_ok A Us' Us \<Longrightarrow> wty V Ts (atom_prop A Us) propT \<Longrightarrow>
    prf_ok V H Ts Hs (PAxm a A Us') (atom_prop A Us)"
| Oracle: "atom_ok A Us' Us \<Longrightarrow> wty V Ts (atom_prop A Us) propT \<Longrightarrow>
    prf_ok V H Ts Hs (Oracle a A Us') (atom_prop A Us)"
| PThm: "atom_ok (hd_prop h) (hd_types h) Us \<Longrightarrow> wty V Ts (atom_prop (hd_prop h) Us) propT \<Longrightarrow>
    prf_ok V H Ts Hs (PThm (h, b)) (atom_prop (hd_prop h) Us)"
| PClass: "wty V Ts (of_class T c) propT \<Longrightarrow> prf_ok V H Ts Hs (PClass T c) (of_class T c)"

lemma prf_ok_wty: "prf_ok V H Ts Hs p \<phi> \<Longrightarrow> wty V Ts \<phi> propT"
proof (induction rule: prf_ok.induct)
  case (AbsP Ts A t Hs p B a)
  then show ?case
    by (auto simp: wty_def implies_def propT_def intro!: has_type.App has_type.Const simp: const_typ_ok_def)
next
  case (Abst T U Ts Hs p B a b)
  then show ?case
    by (auto simp: wty_def all_const_def propT_def intro!: has_type.App has_type.Const has_type.Abs simp: const_typ_ok_def)
next
  case (PAppt Ts Hs p U f t t')
  then show ?case by (auto simp: wty_def all_const_def elim!: has_type_elims intro: has_type.App)
next
  case (PAppp Ts Hs p A B q)
  then show ?case by (auto simp: wty_def implies_def elim!: has_type_elims)
qed

subsection \<open>Lifting of terms\<close>

lemma incr_tvar_tsubst: "incr_tvar inc T = tsubst (\<lambda>v S. TVar (fst v, snd v + inc) S) T"
  by (induction inc T rule: incr_tvar.induct) auto

lemma incr_tvar_no_tvars: "tvars T = {} \<Longrightarrow> incr_tvar inc T = T"
  by (induction inc T rule: incr_tvar.induct) (auto simp: map_idI)

lemma incr_tvar_simps[simp]: "incr_tvar inc propT = propT" "incr_tvar inc dummyT = dummyT"
  by (simp_all add: propT_def dummyT_def)

lemma incr_tvar_foldr: "incr_tvar inc (foldr fun_type Ts T) = foldr fun_type (map (incr_tvar inc) Ts) (incr_tvar inc T)"
  by (induction Ts) auto

lemma incr_tvar_asubst: "incr_tvar inc (asubst f T) = asubst (incr_tvar inc \<circ> f) T"
  by (induction T) auto

lemma tmatch_incr_tvar: "tmatch T U \<Longrightarrow> tmatch (incr_tvar inc T) (incr_tvar inc U)"
proof (induction rule: tmatch.induct)
  case (Type Ts Us a)
  then show ?case by (simp only: incr_tvar.simps) (intro tmatch.Type, auto simp: list.rel_map elim: list.rel_mono_strong)
qed (auto intro: tmatch.intros simp del: incr_tvar.simps(3) simp: incr_tvar.simps(3)[of _ "fst v" "snd v" for v, simplified])

lemma tmatch_fun: "tmatch T T' \<Longrightarrow> tmatch U U' \<Longrightarrow> tmatch (T \<rightarrow>\<^sub>T U) (T' \<rightarrow>\<^sub>T U')"
  by (auto intro: tmatch.Type)

lemma tmatch_foldr: "tmatch T U \<Longrightarrow> tmatch (foldr fun_type Ts T) (foldr fun_type Ts U)"
  by (induction Ts) (auto intro: tmatch_fun)

lemma amatch_combound: "amatch t u \<Longrightarrow> amatch (combound t n k) (combound u n k)"
  by (induction k arbitrary: n) (auto intro: amatch.App amatch.Bound)

lemma amatch_incr_idx: "amatch t u \<Longrightarrow> amatch (incr_idx Us inc lev t) (incr_idx Us inc lev u)"
proof (induction arbitrary: lev rule: amatch.induct)
  case (Var T U x)
  then show ?case
    by (cases x) (auto intro!: amatch_combound amatch.Var tmatch_foldr tmatch_incr_tvar)
qed (auto intro: amatch.intros tmatch_incr_tvar)

lemma incr_bv_combound: "k \<le> n \<Longrightarrow> incr_bv 1 k (combound t n m) = combound (incr_bv 1 k t) (n + 1) m"
  by (induction m arbitrary: n) auto

lemma incr_idx_incr_bv:
  "0 \<le> k \<Longrightarrow> k \<le> lev \<Longrightarrow> incr_idx Us inc (lev + 1) (incr_bv 1 k t) = incr_bv 1 k (incr_idx Us inc lev t)"
  by (induction Us inc lev t arbitrary: k rule: incr_idx.induct) (auto simp: incr_bv_combound)

lemma has_type_combound:
  "has_type V Ts t (foldr fun_type Ws T) \<Longrightarrow> 0 \<le> n \<Longrightarrow> nat_of_integer n + length Ws \<le> length Ts \<Longrightarrow>
    (\<forall>j<length Ws. Ts ! (nat_of_integer n + j) = rev Ws ! j) \<Longrightarrow> has_type V Ts (combound t n (length Ws)) T"
proof (induction Ws arbitrary: n T rule: rev_induct)
  case (snoc W Ws)
  have n1: "nat_of_integer (n + 1) = Suc (nat_of_integer n)" using snoc.prems(2) by (rule nat_of_integer_plus1)
  have "has_type V Ts (combound t (n + 1) (length Ws)) (W \<rightarrow>\<^sub>T T)"
  proof (rule snoc.IH)
    show "\<forall>j<length Ws. Ts ! (nat_of_integer (n + 1) + j) = rev Ws ! j"
    proof (intro allI impI)
      fix j assume "j < length Ws"
      then have "Ts ! (nat_of_integer n + Suc j) = rev (Ws @ [W]) ! Suc j"
        using snoc.prems(4) by (drule_tac x = "Suc j" in spec) (simp del: rev_append)
      then show "Ts ! (nat_of_integer (n + 1) + j) = rev Ws ! j" by (simp add: n1)
    qed
  qed (use snoc.prems n1 in auto)
  moreover have "has_type V Ts (Bound n) W"
    using snoc.prems(2-4) by (intro has_type.Bound) (auto dest: spec[of _ 0])
  ultimately show ?case by (auto intro: has_type.App)
qed simp

text \<open>\<open>V'\<close> types the lifted schematic variables (of non-negative index) of \<open>V\<close>:\<close>

definition lift_venv :: "ptyp list \<Rightarrow> integer \<Rightarrow> (indexname \<Rightarrow> ptyp) \<Rightarrow> (indexname \<Rightarrow> ptyp) \<Rightarrow> bool" where
  "lift_venv Us inc V V' \<longleftrightarrow> (\<forall>x i. 0 \<le> i \<longrightarrow> V' (x, i + inc) = foldr fun_type Us (incr_tvar inc (V (x, i))))"

lemma integer_of_nat_Suc: "integer_of_nat (Suc n) = integer_of_nat n + 1"
  by (simp add: integer_eq_iff)

lemma integer_of_nat_nonneg[simp]: "0 \<le> integer_of_nat n"
  by (simp add: less_eq_integer.rep_eq integer_of_nat.rep_eq)

lemma nat_of_integer_of_nat[simp]: "nat_of_integer (integer_of_nat n) = n"
  by (simp add: nat_of_integer.rep_eq integer_of_nat.rep_eq)

lemma const_typ_ok_incr_tvar: "const_typ_ok c T \<Longrightarrow> const_typ_ok c (incr_tvar inc T)"
  by (simp add: incr_tvar_tsubst const_typ_ok_tsubst)

lemma has_type_incr_idx:
  "has_type V Ts t T \<Longrightarrow> lift_venv Us inc V V' \<Longrightarrow> \<forall>v\<in>vars t. 0 \<le> snd v \<Longrightarrow>
    has_type V' (map (incr_tvar inc) Ts @ rev Us) (incr_idx Us inc (integer_of_nat (length Ts)) t) (incr_tvar inc T)"
proof (induction rule: has_type.induct)
  case (Const a T V Ts)
  then show ?case by (auto intro: has_type.Const const_typ_ok_incr_tvar)
next
  case (Free V Ts a T)
  then show ?case by (auto intro: has_type.Free)
next
  case (Var V x T Ts)
  obtain a i where x: "x = (a, i)" by (cases x)
  let ?Ts = "map (incr_tvar inc) Ts @ rev Us"
  have "has_type V' ?Ts (Var (a, i + inc) (foldr fun_type Us (incr_tvar inc T)))
      (foldr fun_type Us (incr_tvar inc T))"
    using Var by (intro has_type.Var) (simp add: lift_venv_def x)
  then have "has_type V' ?Ts
      (combound (Var (a, i + inc) (foldr fun_type Us (incr_tvar inc T))) (integer_of_nat (length Ts)) (length Us))
      (incr_tvar inc T)"
    by (rule has_type_combound) (auto simp: nth_append)
  then show ?case by (simp add: x)
next
  case (Bound i Ts T V)
  then show ?case by (auto intro!: has_type.Bound simp: nth_append)
next
  case (Abs V T Ts t U x)
  then show ?case by (auto intro!: has_type.Abs simp: integer_of_nat_Suc)
next
  case (App V Ts s T U t)
  then show ?case by (auto intro: has_type.App)
qed

lemma vars_combound[simp]: "vars (combound t n k) = vars t"
  by (induction k arbitrary: n) auto

lemma vars_incr_idx: "vars (incr_idx Us inc lev t) = (\<lambda>v. (fst v, snd v + inc)) ` vars t"
  by (induction Us inc lev t rule: incr_idx.induct) auto

lemma wty_incr_idx:
  "wty V Ts t T \<Longrightarrow> lift_venv Us inc V V' \<Longrightarrow> 0 \<le> inc \<Longrightarrow>
    wty V' (map (incr_tvar inc) Ts @ rev Us) (incr_idx Us inc (integer_of_nat (length Ts)) t) (incr_tvar inc T)"
  by (auto simp: wty_def vars_incr_idx intro: has_type_incr_idx)

lemma remove_types_combound: "remove_types (combound t n k) = combound (remove_types t) n k"
  by (induction k arbitrary: n) auto

lemma remove_types_incr_idx: "remove_types (incr_idx Us inc lev t) = incr_idx Us inc lev (remove_types t)"
  by (induction Us inc lev t rule: incr_idx.induct) (simp_all add: remove_types_combound)

lemma proper_combound: "proper t \<Longrightarrow> 0 \<le> n \<Longrightarrow> proper (combound t n k)"
  by (induction k arbitrary: n) auto

lemma proper_incr_idx: "proper t \<Longrightarrow> 0 \<le> lev \<Longrightarrow> proper (incr_idx Us inc lev t)"
  by (induction Us inc lev t rule: incr_idx.induct) (auto intro: proper_combound)

lemma proper_remove_types[simp]: "proper (remove_types t) \<longleftrightarrow> proper t"
  by (induction t rule: remove_types.induct) auto

lemma vars_remove_types[simp]: "vars (remove_types t) = vars t"
  by (induction t rule: remove_types.induct) auto

lemma ann_ok_incr_idx:
  assumes "ann_ok t A" "0 \<le> lev" "0 \<le> inc"
  shows "ann_ok (map_option (incr_idx Us inc lev) t) (incr_idx Us inc lev A)"
proof (cases t)
  case (Some u)
  with assms have u: "proper u" "\<forall>x\<in>vars u. 0 \<le> snd x" "tr (remove_types u) \<equiv>\<^sub>\<beta>\<^sub>\<eta> tr (remove_types A)" by auto
  have "tr (remove_types (incr_idx Us inc lev u)) \<equiv>\<^sub>\<beta>\<^sub>\<eta> tr (remove_types (incr_idx Us inc lev A))"
    unfolding remove_types_incr_idx tr_incr_idx[OF assms(2)] by (rule vsubst_equiv[OF u(3)])
  with u Some assms(2,3) show ?thesis by (auto simp: proper_incr_idx vars_incr_idx)
qed simp

lemma incr_idx_no_vars: "vars t = {} \<Longrightarrow> incr_idx Us inc lev t = map_types (incr_tvar inc) t"
  by (induction Us inc lev t rule: incr_idx.induct) auto

lemma vars_map_types[simp]: "vars (map_types f t) = vars t"
  by (induction t) auto

lemma tys_map_types: "tys (map_types f t) = f ` tys t"
  by (induction t) auto

lemma map_types_comp: "map_types f (map_types g t) = map_types (f \<circ> g) t"
  by (induction t) auto

lemma tyarg_inst_map:
  assumes "a \<in> set vs" "length Us = length vs"
  shows "tyarg_inst vs (map f Us) a = f (tyarg_inst vs Us a)"
proof -
  have "map_of (zip vs Us) a \<noteq> None" using assms by (simp add: map_of_zip_is_None)
  then show ?thesis
    by (auto simp: tyarg_inst_def zip_map2 map_of_map split: option.split)
qed

lemma atom_prop_incr_idx:
  assumes "length Us = length (atom_tyargs A)"
  shows "incr_idx Ws inc lev (atom_prop A Us) = atom_prop A (map (incr_tvar inc) Us)"
proof -
  have "incr_idx Ws inc lev (atom_prop A Us) =
      map_types (incr_tvar inc \<circ> asubst (tyarg_inst (atom_tyargs A) Us)) (atom_closure A)"
    by (simp add: atom_prop_def incr_idx_no_vars vars_atom_closure map_types_comp)
  also have "\<dots> = atom_prop A (map (incr_tvar inc) Us)"
    unfolding atom_prop_def
  proof (rule map_types_cong)
    fix U assume U: "U \<in> tys (atom_closure A)"
    have "incr_tvar inc (asubst (tyarg_inst (atom_tyargs A) Us) U) =
        asubst (incr_tvar inc \<circ> tyarg_inst (atom_tyargs A) Us) U" by (rule incr_tvar_asubst)
    also have "\<dots> = asubst (tyarg_inst (atom_tyargs A) (map (incr_tvar inc) Us)) U"
      using atyps_atom_closure[OF U] assms by (intro asubst_cong) (auto simp: tyarg_inst_map)
    finally show "(incr_tvar inc \<circ> asubst (tyarg_inst (atom_tyargs A) Us)) U =
        asubst (tyarg_inst (atom_tyargs A) (map (incr_tvar inc) Us)) U" by simp
  qed
  finally show ?thesis .
qed

lemma atom_ok_incr: "atom_ok A Us' Us \<Longrightarrow> atom_ok A (map_option (map (incr_tvar inc)) Us') (map (incr_tvar inc) Us)"
  by (auto simp: atom_ok_def split: option.splits)

lemma incr_idx_of_class: "incr_idx Ws inc lev (of_class T c) = of_class (incr_tvar inc T) c"
  by (simp add: of_class_def propT_def)

lemma incr_idx_hyp: "vars h = {} \<Longrightarrow> \<forall>U\<in>tys h. tvars U = {} \<Longrightarrow> incr_idx Ws inc lev h = h"
proof -
  assume "vars h = {}" "\<forall>U\<in>tys h. tvars U = {}"
  moreover have "\<forall>U\<in>tys h. tvars U = {} \<Longrightarrow> map_types (incr_tvar inc) h = h"
    by (induction h) (auto simp: incr_tvar_no_tvars)
  ultimately show ?thesis by (simp add: incr_idx_no_vars)
qed

lemma incr_idx_implies[simp]: "incr_idx Ws inc lev implies = implies"
  by (simp add: implies_def propT_def)

lemma incr_idx_all_const[simp]: "incr_idx Ws inc lev (all_const U) = all_const (incr_tvar inc U)"
  by (simp add: all_const_def)


subsection \<open>Lifting of proofs\<close>

theorem prf_ok_lift_prf:
  assumes H: "\<forall>h\<in>H. vars h = {} \<and> (\<forall>U\<in>tys h. tvars U = {})"
    and V': "lift_venv Us inc V V'" and inc: "0 \<le> inc"
  shows "prf_ok V H Ts Hs p \<phi> \<Longrightarrow>
    prf_ok V' H (map (incr_tvar inc) Ts @ rev Us)
      (map (incr_idx Us inc (integer_of_nat (length Ts))) Hs)
      (lift_prf inc Us (integer_of_nat (length Ts)) p) (incr_idx Us inc (integer_of_nat (length Ts)) \<phi>)"
proof (induction rule: prf_ok.induct)
  case (conv Ts Hs p \<phi> \<psi>)
  have "tr (incr_idx Us inc (integer_of_nat (length Ts)) \<phi>) \<equiv>\<^sub>\<beta>\<^sub>\<eta> tr (incr_idx Us inc (integer_of_nat (length Ts)) \<psi>)"
    unfolding tr_incr_idx[OF integer_of_nat_nonneg] by (rule vsubst_equiv) (rule conv.hyps(2))
  with conv.IH show ?case
    using wty_incr_idx[OF conv.hyps(3) V' inc] by (auto intro: prf_ok.conv)
next
  case (MinProof Ts \<phi> Hs)
  then show ?case using wty_incr_idx[OF MinProof V' inc] by (auto intro: prf_ok.MinProof)
next
  case (PBound i Hs Ts)
  then show ?case
    using wty_incr_idx[OF PBound(3) V' inc] prf_ok.PBound[of i "map (incr_idx Us inc (integer_of_nat (length Ts))) Hs"]
    by simp
next
  case (AbsP Ts A t Hs p B a)
  have "ann_ok (map_option (incr_idx Us inc (integer_of_nat (length Ts))) t) (incr_idx Us inc (integer_of_nat (length Ts)) A)"
    using AbsP.hyps(2) inc by (intro ann_ok_incr_idx) simp_all
  with AbsP show ?case using wty_incr_idx[OF AbsP.hyps(1) V' inc] by (auto intro: prf_ok.AbsP)
next
  case (Abst T U Ts Hs p B a b)
  have eq: "map (incr_idx Us inc (integer_of_nat (length Ts) + 1) \<circ> incr_bv 1 0) Hs =
      map (incr_bv 1 0 \<circ> incr_idx Us inc (integer_of_nat (length Ts))) Hs"
    by (simp add: incr_idx_incr_bv)
  moreover have "tann_ok (map_option (incr_tvar inc) T) (incr_tvar inc U)"
    using Abst.hyps(1) by (cases T) (auto intro: tmatch_incr_tvar)
  moreover have "prf_ok V' H (incr_tvar inc U # map (incr_tvar inc) Ts @ rev Us)
      (map (incr_bv 1 0) (map (incr_idx Us inc (integer_of_nat (length Ts))) Hs))
      (lift_prf inc Us (integer_of_nat (length Ts) + 1) p) (incr_idx Us inc (integer_of_nat (length Ts) + 1) B)"
    using Abst.IH by (simp add: integer_of_nat_Suc eq)
  ultimately show ?case by (auto intro: prf_ok.Abst)
next
  case (PAppt Ts Hs p U f t t')
  have "ann_ok (map_option (incr_idx Us inc (integer_of_nat (length Ts))) t') (incr_idx Us inc (integer_of_nat (length Ts)) t)"
    using PAppt.hyps(3) inc by (intro ann_ok_incr_idx) simp_all
  with PAppt show ?case using wty_incr_idx[OF PAppt.hyps(2) V' inc] by (auto intro: prf_ok.PAppt)
next
  case (PAppp Ts Hs p A B q)
  then show ?case by (auto intro: prf_ok.PAppp)
next
  case (Hyp t Ts Hs)
  then show ?case using H wty_incr_idx[OF Hyp(2) V' inc] incr_idx_hyp[of t]
    by (auto intro: prf_ok.Hyp)
next
  case (PAxm A Us' Us0 Ts Hs a)
  then show ?case using wty_incr_idx[OF PAxm(2) V' inc]
    by (auto simp: atom_prop_incr_idx atom_ok_def intro!: prf_ok.PAxm atom_ok_incr)
next
  case (Oracle A Us' Us0 Ts Hs a)
  then show ?case using wty_incr_idx[OF Oracle(2) V' inc]
    by (auto simp: atom_prop_incr_idx atom_ok_def intro!: prf_ok.Oracle atom_ok_incr)
next
  case (PThm h Us0 Ts Hs b)
  let ?h = "hd_set_types h (map_option (map (incr_tvar inc)) (hd_types h))"
  have "atom_ok (hd_prop ?h) (hd_types ?h) (map (incr_tvar inc) Us0)"
    using PThm(1) by (auto simp: atom_ok_def split: option.splits)
  then show ?case using wty_incr_idx[OF PThm(2) V' inc] PThm(1) prf_ok.PThm[of ?h "map (incr_tvar inc) Us0"]
    by (auto simp: atom_prop_incr_idx atom_ok_def)
next
  case (PClass Ts T c Hs)
  then show ?case using wty_incr_idx[OF PClass V' inc] by (auto simp: incr_idx_of_class intro: prf_ok.PClass)
qed

subsection \<open>Weakening\<close>

text \<open>Proof-level weakening: a new hypothesis at position \<open>c\<close>.\<close>

fun incr_pbv :: "integer \<Rightarrow> prf \<Rightarrow> prf" where
  "incr_pbv c (PBound i) = (if c \<le> i then PBound (i + 1) else PBound i)"
| "incr_pbv c (AbsP a t p) = AbsP a t (incr_pbv (c + 1) p)"
| "incr_pbv c (Abst a T p) = Abst a T (incr_pbv c p)"
| "incr_pbv c (PAppt p t) = PAppt (incr_pbv c p) t"
| "incr_pbv c (PAppp p q) = PAppp (incr_pbv c p) (incr_pbv c q)"
| "incr_pbv c p = p"

text \<open>Term-level weakening: a new bound variable at position \<open>c\<close>.\<close>

fun incr_tbv :: "integer \<Rightarrow> prf \<Rightarrow> prf" where
  "incr_tbv c (AbsP a t p) = AbsP a (map_option (incr_bv 1 c) t) (incr_tbv c p)"
| "incr_tbv c (Abst a T p) = Abst a T (incr_tbv (c + 1) p)"
| "incr_tbv c (PAppt p t) = PAppt (incr_tbv c p) (map_option (incr_bv 1 c) t)"
| "incr_tbv c (PAppp p q) = PAppp (incr_tbv c p) (incr_tbv c q)"
| "incr_tbv c p = p"

lemma nat_of_integer_plus1': "0 \<le> c \<Longrightarrow> nat_of_integer (c + 1) = Suc (nat_of_integer c)"
  by (rule nat_of_integer_plus1)

lemma prf_ok_incr_pbv:
  "prf_ok V H Ts Hs p \<phi> \<Longrightarrow> 0 \<le> c \<Longrightarrow> nat_of_integer c \<le> length Hs \<Longrightarrow>
    prf_ok V H Ts (take (nat_of_integer c) Hs @ A # drop (nat_of_integer c) Hs) (incr_pbv c p) \<phi>"
proof (induction arbitrary: c A rule: prf_ok.induct)
  case (conv Ts Hs p \<phi> \<psi>)
  then show ?case by (auto intro: prf_ok.conv)
next
  case (PBound i Hs Ts)
  show ?case
  proof (cases "c \<le> i")
    case True
    then have "nat_of_integer c \<le> nat_of_integer i" by (simp add: integer_reps nat_mono)
    then have "(take (nat_of_integer c) Hs @ A # drop (nat_of_integer c) Hs) ! nat_of_integer (i + 1) = Hs ! nat_of_integer i"
      using PBound nat_of_integer_plus1[of i] by (simp add: nth_append)
    moreover have "nat_of_integer (i + 1) < length (take (nat_of_integer c) Hs @ A # drop (nat_of_integer c) Hs)"
      using PBound nat_of_integer_plus1[of i] by simp
    ultimately show ?thesis
      using True PBound prf_ok.PBound[of "i + 1" "take (nat_of_integer c) Hs @ A # drop (nat_of_integer c) Hs"]
      by simp
  next
    case False
    then have "nat_of_integer i < nat_of_integer c" using PBound(1) by (simp add: integer_reps)
    then have "(take (nat_of_integer c) Hs @ A # drop (nat_of_integer c) Hs) ! nat_of_integer i = Hs ! nat_of_integer i"
      using PBound.prems by (simp add: nth_append)
    then show ?thesis
      using False PBound prf_ok.PBound[of i "take (nat_of_integer c) Hs @ A # drop (nat_of_integer c) Hs"]
      by simp
  qed
next
  case (AbsP Ts A' t Hs p B a)
  have "prf_ok V H Ts (take (nat_of_integer (c + 1)) (A' # Hs) @ A # drop (nat_of_integer (c + 1)) (A' # Hs))
      (incr_pbv (c + 1) p) B"
    using AbsP.IH[of "c + 1" A] AbsP.prems nat_of_integer_plus1[of c] by simp
  then show ?case using AbsP nat_of_integer_plus1[of c] by (auto intro: prf_ok.AbsP)
next
  case (Abst T U Ts Hs p B a b)
  have "prf_ok V H (U # Ts) (take (nat_of_integer c) (map (incr_bv 1 0) Hs) @ incr_bv 1 0 A #
      drop (nat_of_integer c) (map (incr_bv 1 0) Hs)) (incr_pbv c p) B"
    using Abst by simp
  then show ?case using Abst by (auto intro: prf_ok.Abst simp: take_map drop_map)
next
  case (PAppp Ts Hs p A' B q)
  show ?case unfolding incr_pbv.simps by (rule prf_ok.PAppp[OF PAppp.IH(1)[OF PAppp.prems] PAppp.IH(2)[OF PAppp.prems]])
qed (auto intro: prf_ok.intros)

lemma prf_ok_append: "prf_ok V H Ts Hs p \<phi> \<Longrightarrow> prf_ok V H Ts (Hs @ Hs') p \<phi>"
proof (induction arbitrary: Hs' rule: prf_ok.induct)
  case (PBound i Hs Ts)
  then show ?case using prf_ok.PBound[of i "Hs @ Hs'"] by (simp add: nth_append)
next
  case (Abst T U Ts Hs p B a b)
  then show ?case using prf_ok.Abst[of T U V H Ts "Hs @ Hs'"] by simp
next
  case (PAppp Ts Hs p A' B q)
  then show ?case by (auto intro: prf_ok.PAppp)
qed (auto intro: prf_ok.intros)

lemma lift_equiv: "s \<equiv>\<^sub>\<beta>\<^sub>\<eta> t \<Longrightarrow> lift s k \<equiv>\<^sub>\<beta>\<^sub>\<eta> lift t k"
proof (induction rule: rtranclp_induct)
  case (step y z)
  from step.hyps(2) have "symcl \<beta>\<eta> (lift y k) (lift z k)"
    unfolding symcl.simps by (auto intro: eta_lift lift_preserves_beta)
  with step.IH show ?case by (rule rtranclp.rtrancl_into_rtrancl)
qed simp

lemma incr_bv_no_loose: "\<not> loose_bvar t k \<Longrightarrow> k \<le> c \<Longrightarrow> incr_bv n c t = t"
  by (induction n c t arbitrary: k rule: incr_bv.induct) fastforce+

lemma loose_bvar_map_types[simp]: "loose_bvar (map_types f t) k = loose_bvar t k"
  by (induction t arbitrary: k) auto

lemma incr_bv_atom_prop: "0 \<le> c \<Longrightarrow> incr_bv n c (atom_prop A Us) = atom_prop A Us"
  unfolding atom_prop_def by (rule incr_bv_no_loose[of _ 0]) (simp_all add: closed_atom_closure)

lemma incr_bv_incr_bv:
  "0 \<le> k \<Longrightarrow> 0 \<le> c \<Longrightarrow> incr_bv 1 (c + k + 1) (incr_bv 1 k t) = incr_bv 1 k (incr_bv 1 (c + k) t)"
  by (induction "1 :: integer" k t arbitrary: c rule: incr_bv.induct) (auto simp: add.assoc)

lemma amatch_incr_bv: "amatch t u \<Longrightarrow> amatch (incr_bv n c t) (incr_bv n c u)"
  by (induction arbitrary: c rule: amatch.induct) (auto intro: amatch.intros)

lemma remove_types_incr_bv: "remove_types (incr_bv n c t) = incr_bv n c (remove_types t)"
  by (induction n c t rule: incr_bv.induct) auto

lemma wty_incr_bv:
  "wty V Ts t T \<Longrightarrow> 0 \<le> c \<Longrightarrow> nat_of_integer c \<le> length Ts \<Longrightarrow>
    wty V (take (nat_of_integer c) Ts @ U # drop (nat_of_integer c) Ts) (incr_bv 1 c t) T"
  using has_type_incr_bv[of V Ts t T 1 c "[U]"] by (auto simp: wty_def vars_incr_bv integer_reps)

lemma incr_bv_implies[simp]: "incr_bv n c implies = implies"
  by (simp add: implies_def)

lemma incr_bv_all_const[simp]: "incr_bv n c (all_const U) = all_const U"
  by (simp add: all_const_def)

lemma tr_incr_bv1:
  "proper t \<Longrightarrow> 0 \<le> c \<Longrightarrow> tr (incr_bv 1 c t) = lift (tr t) (nat_of_integer c)"
  using tr_incr_bv[of t 1 c] by (simp add: integer_reps del: liftn_lift) (simp add: One_nat_def)

lemma ann_ok_incr_bv:
  assumes "ann_ok t A" "proper A" "0 \<le> c"
  shows "ann_ok (map_option (incr_bv 1 c) t) (incr_bv 1 c A)"
proof (cases t)
  case (Some u)
  with assms have u: "proper u" "\<forall>x\<in>vars u. 0 \<le> snd x" "tr (remove_types u) \<equiv>\<^sub>\<beta>\<^sub>\<eta> tr (remove_types A)" by auto
  have "tr (remove_types (incr_bv 1 c u)) \<equiv>\<^sub>\<beta>\<^sub>\<eta> tr (remove_types (incr_bv 1 c A))"
    using u assms(2,3) by (simp add: remove_types_incr_bv tr_incr_bv1 lift_equiv)
  with u Some assms show ?thesis by (auto simp: proper_incr_bv vars_incr_bv)
qed simp

lemma prf_ok_incr_tbv:
  assumes H: "\<forall>h\<in>H. \<not> loose_bvar h 0"
  shows "prf_ok V H Ts Hs p \<phi> \<Longrightarrow> 0 \<le> c \<Longrightarrow> nat_of_integer c \<le> length Ts \<Longrightarrow>
    prf_ok V H (take (nat_of_integer c) Ts @ U # drop (nat_of_integer c) Ts) (map (incr_bv 1 c) Hs)
      (incr_tbv c p) (incr_bv 1 c \<phi>)"
proof (induction arbitrary: c U rule: prf_ok.induct)
  case (conv Ts Hs p \<phi> \<psi>)
  have "proper \<phi>" "proper \<psi>"
    using prf_ok_wty[OF conv.hyps(1)] conv.hyps(3) by (auto simp: wty_def intro: has_type_proper)
  then have "tr (incr_bv 1 c \<phi>) \<equiv>\<^sub>\<beta>\<^sub>\<eta> tr (incr_bv 1 c \<psi>)"
    using conv.prems conv.hyps(2) by (simp add: tr_incr_bv1 lift_equiv)
  then show ?case using conv by (auto intro: prf_ok.conv wty_incr_bv)
next
  case (MinProof Ts \<phi> Hs)
  then show ?case by (auto intro: prf_ok.MinProof wty_incr_bv)
next
  case (PBound i Hs Ts)
  then show ?case
    using wty_incr_bv[OF PBound(3)] prf_ok.PBound[of i "map (incr_bv 1 c) Hs"] by simp
next
  case (AbsP Ts A t Hs p B a)
  have "prf_ok V H (take (nat_of_integer c) Ts @ U # drop (nat_of_integer c) Ts) (incr_bv 1 c A # map (incr_bv 1 c) Hs)
      (incr_tbv c p) (incr_bv 1 c B)"
    using AbsP.IH AbsP.prems by simp
  moreover have "ann_ok (map_option (incr_bv 1 c) t) (incr_bv 1 c A)"
    using AbsP(1,2) AbsP.prems by (intro ann_ok_incr_bv) (auto simp: wty_def intro: has_type_proper)
  ultimately show ?case using AbsP by (auto intro!: prf_ok.AbsP wty_incr_bv)
next
  case (Abst T U' Ts Hs p B a b)
  let ?Ts = "take (nat_of_integer c) Ts @ U # drop (nat_of_integer c) Ts"
  have eq: "map (incr_bv 1 (c + 1) \<circ> incr_bv 1 0) Hs = map (incr_bv 1 0 \<circ> incr_bv 1 c) Hs"
    using incr_bv_incr_bv[of 0 c] Abst.prems by simp
  have "prf_ok V H (U' # ?Ts) (map (incr_bv 1 0) (map (incr_bv 1 c) Hs)) (incr_tbv (c + 1) p) (incr_bv 1 (c + 1) B)"
    using Abst.IH[of "c + 1" U] Abst.prems nat_of_integer_plus1[of c] eq by simp
  then show ?case
    using Abst(1) prf_ok.Abst[of T U' V H ?Ts "map (incr_bv 1 c) Hs" "incr_tbv (c + 1) p" "incr_bv 1 (c + 1) B" a b]
    by simp
next
  case (PAppt Ts Hs p U' f t t')
  have "ann_ok (map_option (incr_bv 1 c) t') (incr_bv 1 c t)"
    using PAppt(2,3) PAppt.prems by (intro ann_ok_incr_bv) (auto simp: wty_def intro: has_type_proper)
  with PAppt show ?case by (auto intro!: prf_ok.PAppt wty_incr_bv simp: all_const_def)
next
  case (PAppp Ts Hs p A B q)
  have "prf_ok V H (take (nat_of_integer c) Ts @ U # drop (nat_of_integer c) Ts) (map (incr_bv 1 c) Hs) (incr_tbv c p)
      (implies $ incr_bv 1 c A $ incr_bv 1 c B)"
    using PAppp.IH(1)[OF PAppp.prems, where U = U] by simp
  then show ?case unfolding incr_tbv.simps
    using PAppp.IH(2)[OF PAppp.prems, where U = U] by (rule prf_ok.PAppp)
next
  case (Hyp t Ts Hs)
  have "incr_bv 1 c t = t" using H Hyp incr_bv_no_loose[of t 0 c 1] by auto
  moreover have "wty V (take (nat_of_integer c) Ts @ U # drop (nat_of_integer c) Ts) t propT"
    using wty_incr_bv[OF Hyp(2) Hyp.prems] calculation by simp
  ultimately show ?case using Hyp(1) by (simp add: prf_ok.Hyp)
next
  case (PAxm A Us' Us Ts Hs a)
  then show ?case using wty_incr_bv[OF PAxm(2)] by (auto simp: incr_bv_atom_prop intro: prf_ok.PAxm)
next
  case (Oracle A Us' Us Ts Hs a)
  then show ?case using wty_incr_bv[OF Oracle(2)] by (auto simp: incr_bv_atom_prop intro: prf_ok.Oracle)
next
  case (PThm h Us Ts Hs b)
  then show ?case using wty_incr_bv[OF PThm(2)] by (auto simp: incr_bv_atom_prop intro: prf_ok.PThm)
next
  case (PClass Ts T c' Hs)
  have "incr_bv 1 c (of_class T c') = of_class T c'" by (simp add: of_class_def)
  with wty_incr_bv[OF PClass(1) PClass.prems, of U] show ?case by (auto intro: prf_ok.PClass)
qed


subsection \<open>Lifting of rules\<close>

text \<open>The parameters of the subgoal, innermost first, as \<open>Logic.lift_all\<close> collects them.\<close>

fun lift_Ts :: "ptyp list \<Rightarrow> pterm \<Rightarrow> ptyp list" where
  "lift_Ts Ts (Const c U $ H $ B) = (if c = STR ''Pure.imp'' then lift_Ts Ts B else Ts)"
| "lift_Ts Ts (Const c U $ Abs a T B) = (if c = STR ''Pure.all'' then lift_Ts (T # Ts) B else Ts)"
| "lift_Ts Ts _ = Ts"

lemma has_type_imp_E:
  "has_type V Ts (Const STR ''Pure.imp'' U $ A $ B) T \<Longrightarrow>
    U = propT \<rightarrow>\<^sub>T propT \<rightarrow>\<^sub>T propT \<and> T = propT \<and> has_type V Ts A propT \<and> has_type V Ts B propT"
  by (auto elim!: has_type_elims simp: const_typ_ok_def propT_def)

lemma has_type_all_E:
  "has_type V Ts (Const STR ''Pure.all'' U $ Abs a T' B) T \<Longrightarrow>
    U = (T' \<rightarrow>\<^sub>T propT) \<rightarrow>\<^sub>T propT \<and> T = propT \<and> has_type V (T' # Ts) B propT"
  by (auto elim!: has_type_elims simp: const_typ_ok_def propT_def)

lemma incr_tvar_0[simp]: "incr_tvar 0 T = T"
  by (induction "0 :: integer" T rule: incr_tvar.induct) (auto simp: map_idI)

lemma incr_idx_0: "incr_idx [] 0 lev t = t"
  by (induction "[] :: ptyp list" "0 :: integer" lev t rule: incr_idx.induct) auto

lemma incr_indexes_incr_idx: "incr_indexes Ts inc t = incr_idx Ts inc 0 t"
  by (simp add: incr_indexes_def incr_idx_0)

lemma wty_leaf:
  "wty V [] A propT \<Longrightarrow> lift_venv (rev Ts) inc V V' \<Longrightarrow> 0 \<le> inc \<Longrightarrow>
    wty V' Ts (incr_indexes (rev Ts) inc A) propT"
  using wty_incr_idx[of V "[]" A propT "rev Ts" inc V'] by (simp add: incr_indexes_incr_idx)

lemma wty_lift_all_aux:
  "wty V' Ts G propT \<Longrightarrow> wty V [] A propT \<Longrightarrow> lift_venv (rev (lift_Ts Ts G)) inc V V' \<Longrightarrow> 0 \<le> inc \<Longrightarrow>
    wty V' Ts (lift_all_aux inc Ts G A) propT"
proof (induction inc Ts G A rule: lift_all_aux.induct)
  case (1 inc Ts c U H B t)
  show ?case
  proof (cases "c = STR ''Pure.imp''")
    case True
    with 1 show ?thesis using has_type_imp_E[of V' Ts U H B propT]
      by (auto simp: wty_def propT_def intro!: has_type.App has_type.Const simp: const_typ_ok_def)
  next
    case False
    with 1 show ?thesis by (simp add: wty_leaf)
  qed
next
  case (2 inc Ts c U a T B t)
  show ?case
  proof (cases "c = STR ''Pure.all''")
    case True
    with 2 show ?thesis using has_type_all_E[of V' Ts U a T B propT]
      by (auto simp: wty_def propT_def intro!: has_type.App has_type.Const has_type.Abs simp: const_typ_ok_def)
  next
    case False
    with 2 show ?thesis by (simp add: wty_leaf)
  qed
qed (simp_all add: wty_leaf)

text \<open>The proofs of the premises, applied to the parameters and assumptions passed so far.\<close>

definition spine :: "bool list \<Rightarrow> integer \<Rightarrow> integer \<Rightarrow> integer \<Rightarrow> prf" where
  "spine bs i j c = snd (snd (foldr mk_app bs (i - 1, j - 1, PBound c)))"

lemma foldr_mk_app_fst:
  "foldr mk_app bs (a, b, p) =
    (a - integer_of_nat (length (filter id bs)), b - integer_of_nat (length (filter Not bs)),
     snd (snd (foldr mk_app bs (a, b, p))))"
  by (induction bs) (auto simp: mk_app_def integer_of_nat_Suc split: prod.splits)

lemma foldr_mk_app_Cons:
  "snd (snd (foldr mk_app (x # bs) (a, b, p))) =
    (if x then PAppp (snd (snd (foldr mk_app bs (a, b, p)))) (PBound (a - integer_of_nat (length (filter id bs))))
     else PAppt (snd (snd (foldr mk_app bs (a, b, p)))) (Some (Bound (b - integer_of_nat (length (filter Not bs))))))"
proof -
  obtain a' b' r where e: "foldr mk_app bs (a, b, p) = (a', b', r)" by (cases "foldr mk_app bs (a, b, p)") auto
  then have "a' = a - integer_of_nat (length (filter id bs))" "b' = b - integer_of_nat (length (filter Not bs))"
    using foldr_mk_app_fst[of bs a b p] by simp_all
  with e show ?thesis by (simp add: mk_app_def)
qed

lemma foldr_mk_app_pbv:
  "integer_of_nat (length (filter id bs)) \<le> a + 1 \<Longrightarrow>
    snd (snd (foldr mk_app bs (a + 1, b, incr_pbv 0 p))) = incr_pbv 0 (snd (snd (foldr mk_app bs (a, b, p))))"
proof (induction bs)
  case (Cons x bs)
  show ?case unfolding foldr_mk_app_Cons using Cons by (cases x) (auto simp: integer_of_nat_Suc id_def)
qed simp

lemma foldr_mk_app_tbv:
  "integer_of_nat (length (filter Not bs)) \<le> b + 1 \<Longrightarrow>
    snd (snd (foldr mk_app bs (a, b + 1, incr_tbv 0 p))) = incr_tbv 0 (snd (snd (foldr mk_app bs (a, b, p))))"
proof (induction bs)
  case (Cons x bs)
  show ?case unfolding foldr_mk_app_Cons using Cons by (cases x) (auto simp: integer_of_nat_Suc id_def)
qed simp

lemma spine_True:
  assumes "i = integer_of_nat (length (filter id bs))" "0 \<le> c"
  shows "spine (True # bs) (i + 1) j (c + 1) = PAppp (incr_pbv 0 (spine bs i j c)) (PBound 0)"
proof -
  have "snd (snd (foldr mk_app bs (i - 1 + 1, j - 1, incr_pbv 0 (PBound c)))) = incr_pbv 0 (spine bs i j c)"
    unfolding spine_def using assms by (intro foldr_mk_app_pbv) simp
  then show ?thesis using assms unfolding spine_def foldr_mk_app_Cons by simp
qed

lemma spine_False:
  assumes "j = integer_of_nat (length (filter Not bs))"
  shows "spine (False # bs) i (j + 1) c = PAppt (incr_tbv 0 (spine bs i j c)) (Some (Bound 0))"
proof -
  have "snd (snd (foldr mk_app bs (i - 1, j - 1 + 1, incr_tbv 0 (PBound c)))) = incr_tbv 0 (spine bs i j c)"
    unfolding spine_def using assms by (intro foldr_mk_app_tbv) simp
  then show ?thesis using assms unfolding spine_def foldr_mk_app_Cons by simp
qed

lemma downto_map: "downto a b = map (\<lambda>m. a - integer_of_nat m) [0..<nat_of_integer (a - b + 1)]"
proof (induction a b rule: downto.induct)
  case (1 a b)
  show ?case
  proof (cases "a < b")
    case True
    then have "nat_of_integer (a - b + 1) = 0" by (simp add: integer_reps)
    with True show ?thesis by (simp add: downto.simps)
  next
    case False
    then have n: "nat_of_integer (a - b + 1) = Suc (nat_of_integer (a - b))" by (simp add: integer_reps)
    have "downto a b = a # downto (a - 1) b" using False by (simp add: downto.simps)
    also have "\<dots> = a # map (\<lambda>m. a - 1 - integer_of_nat m) [0..<nat_of_integer (a - b)]" using 1 False by simp
    also have "\<dots> = map (\<lambda>m. a - integer_of_nat m) [0..<Suc (nat_of_integer (a - b))]"
      by (simp del: upt_Suc add: map_upt_Suc integer_of_nat_Suc algebra_simps)
    finally show ?thesis by (simp only: n)
  qed
qed

lemma prf_ok_proof_combP:
  "prf_ok V H Ts Hs p (list_implies As B) \<Longrightarrow> list_all2 (prf_ok V H Ts Hs) qs As \<Longrightarrow>
    prf_ok V H Ts Hs (proof_combP p qs) B"
proof (induction As arbitrary: p qs)
  case Nil
  then show ?case by (simp add: proof_combP_def)
next
  case (Cons A As)
  then obtain q qs' where "qs = q # qs'" by (cases qs) auto
  with Cons show ?case by (auto simp: proof_combP_def intro: prf_ok.PAppp)
qed

lemma incr_idx_list_implies:
  "incr_idx Us inc lev (list_implies As B) = list_implies (map (incr_idx Us inc lev) As) (incr_idx Us inc lev B)"
  by (induction As) simp_all

lemma lift_prems_leaf:
  assumes H: "\<forall>h\<in>H. vars h = {} \<and> (\<forall>U\<in>tys h. tvars U = {}) \<and> \<not> loose_bvar h 0" and inc: "0 \<le> inc"
    and P: "prf_ok V H [] [] pf (list_implies As B)" and k: "k = integer_of_nat (length As)"
    and V': "lift_venv (rev Ts) inc V V'"
    and sp: "\<forall>m<length As. prf_ok V' H Ts Hs (spine bs i j (i + k - 1 - integer_of_nat m)) (incr_indexes (rev Ts) inc (As ! m))"
  shows "prf_ok V' H Ts Hs (proof_combP (lift_prf inc (rev Ts) 0 pf)
      (map (\<lambda>k. snd (snd (foldr mk_app bs (i - 1, j - 1, PBound k)))) (downto (i + k - 1) i)))
    (incr_indexes (rev Ts) inc B)"
proof -
  have H': "\<forall>h\<in>H. vars h = {} \<and> (\<forall>U\<in>tys h. tvars U = {})" using H by blast
  have "prf_ok V' H (map (incr_tvar inc) [] @ rev (rev Ts)) (map (incr_idx (rev Ts) inc (integer_of_nat 0)) [])
      (lift_prf inc (rev Ts) (integer_of_nat 0) pf) (incr_idx (rev Ts) inc (integer_of_nat 0) (list_implies As B))"
    using prf_ok_lift_prf[OF H' V' inc P] by simp
  then have "prf_ok V' H Ts Hs (lift_prf inc (rev Ts) 0 pf)
      (list_implies (map (incr_indexes (rev Ts) inc) As) (incr_indexes (rev Ts) inc B))"
    using prf_ok_append[of V' H Ts "[]" _ _ Hs]
    by (simp add: incr_idx_list_implies incr_indexes_incr_idx[abs_def])
  moreover have "map (\<lambda>k. snd (snd (foldr mk_app bs (i - 1, j - 1, PBound k)))) (downto (i + k - 1) i) =
      map (\<lambda>m. spine bs i j (i + k - 1 - integer_of_nat m)) [0..<length As]"
    by (simp add: downto_map k spine_def)
  moreover have "list_all2 (prf_ok V' H Ts Hs) (map (\<lambda>m. spine bs i j (i + k - 1 - integer_of_nat m)) [0..<length As])
      (map (incr_indexes (rev Ts) inc) As)"
    using sp by (auto simp: list_all2_conv_all_nth)
  ultimately show ?thesis by (auto intro: prf_ok_proof_combP)
qed

lemma lift_prems_leaf_gen:
  assumes H: "\<forall>h\<in>H. vars h = {} \<and> (\<forall>U\<in>tys h. tvars U = {}) \<and> \<not> loose_bvar h 0"
    and leaf: "lift_Ts Ts G = Ts" "\<And>A. lift_all_aux inc Ts G A = incr_indexes (rev Ts) inc A"
      "lift_prems inc k pf Ts bs i j G = proof_combP (lift_prf inc (rev Ts) 0 pf)
        (map (\<lambda>k. snd (snd (foldr mk_app bs (i - 1, j - 1, PBound k)))) (downto (i + k - 1) i))"
  shows "wty V' Ts G propT \<Longrightarrow> lift_venv (rev (lift_Ts Ts G)) inc V V' \<Longrightarrow>
    i = integer_of_nat (length (filter id bs)) \<Longrightarrow> length Ts = length (filter Not bs) \<Longrightarrow>
    j = integer_of_nat (length Ts) \<Longrightarrow>
    (\<forall>m<length As. prf_ok V' H Ts Hs (spine bs i j (i + k - 1 - integer_of_nat m)) (lift_all_aux inc Ts G (As ! m))) \<Longrightarrow>
    0 \<le> inc \<Longrightarrow> prf_ok V H [] [] pf (list_implies As B) \<Longrightarrow> k = integer_of_nat (length As) \<Longrightarrow>
    prf_ok V' H Ts Hs (lift_prems inc k pf Ts bs i j G) (lift_all_aux inc Ts G B)"
  unfolding leaf by (rule lift_prems_leaf[OF H])

lemma subst_lift_0: "subst (lift t (Suc 0)) (BVar 0) 0 = t"
  using subst_lift_Suc_BVar[of t 0] by simp

lemma prf_ok_lift_prems:
  assumes H: "\<forall>h\<in>H. vars h = {} \<and> (\<forall>U\<in>tys h. tvars U = {}) \<and> \<not> loose_bvar h 0"
  shows "wty V' Ts G propT \<Longrightarrow> lift_venv (rev (lift_Ts Ts G)) inc V V' \<Longrightarrow>
    i = integer_of_nat (length (filter id bs)) \<Longrightarrow> length Ts = length (filter Not bs) \<Longrightarrow>
    j = integer_of_nat (length Ts) \<Longrightarrow>
    (\<forall>m<length As. prf_ok V' H Ts Hs (spine bs i j (i + k - 1 - integer_of_nat m)) (lift_all_aux inc Ts G (As ! m))) \<Longrightarrow>
    0 \<le> inc \<Longrightarrow> prf_ok V H [] [] pf (list_implies As B) \<Longrightarrow> k = integer_of_nat (length As) \<Longrightarrow>
    prf_ok V' H Ts Hs (lift_prems inc k pf Ts bs i j G) (lift_all_aux inc Ts G B)"
proof (induction inc k pf Ts bs i j G arbitrary: Hs rule: lift_prems.induct)
  case (1 inc k pf Ts bs i j c U A' G')
  show ?case
  proof (cases "c = STR ''Pure.imp''")
    case True
    note tA = has_type_imp_E[of V' Ts U A' G' propT, OF 1(2)[unfolded wty_def True, THEN conjunct1]]
    have wA: "wty V' Ts A' propT" "wty V' Ts G' propT" using 1(2) tA by (auto simp: wty_def True)
    have "prf_ok V' H Ts (A' # Hs) (lift_prems inc k pf Ts (True # bs) (i + 1) j G') (lift_all_aux inc Ts G' B)"
    proof (rule 1(1)[OF True])
      show "\<forall>m<length As. prf_ok V' H Ts (A' # Hs) (spine (True # bs) (i + 1) j (i + 1 + k - 1 - integer_of_nat m))
          (lift_all_aux inc Ts G' (As ! m))"
      proof (intro allI impI)
        fix m assume m: "m < length As"
        have "integer_of_nat (Suc m) \<le> k" using m 1(10) by (simp add: less_eq_integer.rep_eq integer_of_nat.rep_eq)
        then have c0: "0 \<le> i + k - 1 - integer_of_nat m" using 1(4) integer_of_nat_nonneg[of "length (filter id bs)"]
          by (simp only: integer_of_nat_Suc)
        have "prf_ok V' H Ts (take (nat_of_integer 0) Hs @ A' # drop (nat_of_integer 0) Hs)
            (incr_pbv 0 (spine bs i j (i + k - 1 - integer_of_nat m))) (lift_all_aux inc Ts (Const c U $ A' $ G') (As ! m))"
          using 1(7) m by (intro prf_ok_incr_pbv) (auto simp: integer_reps)
        then have "prf_ok V' H Ts (A' # Hs) (incr_pbv 0 (spine bs i j (i + k - 1 - integer_of_nat m)))
            (implies $ A' $ lift_all_aux inc Ts G' (As ! m))"
          using True tA by (simp add: implies_def integer_reps)
        moreover have "prf_ok V' H Ts (A' # Hs) (PBound 0) A'"
          using prf_ok.PBound[of 0 "A' # Hs" V' Ts H] wA by (simp add: integer_reps)
        ultimately have "prf_ok V' H Ts (A' # Hs) (PAppp (incr_pbv 0 (spine bs i j (i + k - 1 - integer_of_nat m))) (PBound 0))
            (lift_all_aux inc Ts G' (As ! m))" by (rule prf_ok.PAppp)
        then show "prf_ok V' H Ts (A' # Hs) (spine (True # bs) (i + 1) j (i + 1 + k - 1 - integer_of_nat m))
            (lift_all_aux inc Ts G' (As ! m))"
          using spine_True[OF 1(4) c0, of j] by (simp add: algebra_simps)
      qed
    qed (use wA 1(3-6) 1(8-10) True in \<open>simp_all add: integer_of_nat_Suc\<close>)
    moreover have e: "Const STR ''Pure.imp'' U = implies" using tA by (simp add: implies_def)
    moreover have "lift_prems inc k pf Ts bs i j (Const c U $ A' $ G') =
        AbsP (STR ''H'') None (lift_prems inc k pf Ts (True # bs) (i + 1) j G')" using True by simp
    ultimately have "prf_ok V' H Ts Hs (AbsP (STR ''H'') None (lift_prems inc k pf Ts (True # bs) (i + 1) j G'))
        (implies $ A' $ lift_all_aux inc Ts G' B)" using wA by (auto intro!: prf_ok.AbsP)
    then show ?thesis using True tA by (simp add: implies_def)
  next
    case False
    then show ?thesis
      using lift_prems_leaf[OF H 1(8-10), of Ts V' Hs bs i j] 1(3) 1(7) by simp
  qed
next
  case (2 inc k pf Ts bs i j c U a T G')
  show ?case
  proof (cases "c = STR ''Pure.all''")
    case True
    note tG = has_type_all_E[of V' Ts U a T G' propT, OF 2(2)[unfolded wty_def True, THEN conjunct1]]
    have wG: "wty V' (T # Ts) G' propT" using 2(2) tG by (auto simp: wty_def True)
    have "prf_ok V' H (T # Ts) (map (incr_bv 1 0) Hs) (lift_prems inc k pf (T # Ts) (False # bs) i (j + 1) G')
        (lift_all_aux inc (T # Ts) G' B)"
    proof (rule 2(1)[OF True])
      show "\<forall>m<length As. prf_ok V' H (T # Ts) (map (incr_bv 1 0) Hs) (spine (False # bs) i (j + 1) (i + k - 1 - integer_of_nat m))
          (lift_all_aux inc (T # Ts) G' (As ! m))"
      proof (intro allI impI)
        fix m assume m: "m < length As"
        let ?X = "lift_all_aux inc (T # Ts) G' (As ! m)"
        let ?s = "spine bs i j (i + k - 1 - integer_of_nat m)"
        have sm: "prf_ok V' H Ts Hs ?s (all_const T $ Abs a T ?X)"
          using 2(7) m True tG by (simp add: all_const_def)
        have wX: "wty V' (T # Ts) ?X propT"
          using prf_ok_wty[OF sm] by (auto simp: wty_def all_const_def dest!: has_type_all_E)
        have Hc: "\<forall>h\<in>H. \<not> loose_bvar h 0" using H by blast
        have "prf_ok V' H (take (nat_of_integer 0) Ts @ T # drop (nat_of_integer 0) Ts) (map (incr_bv 1 0) Hs)
            (incr_tbv 0 ?s) (incr_bv 1 0 (all_const T $ Abs a T ?X))"
          using sm by (intro prf_ok_incr_tbv[OF Hc]) (auto simp: integer_reps)
        then have "prf_ok V' H (T # Ts) (map (incr_bv 1 0) Hs) (incr_tbv 0 ?s) (all_const T $ Abs a T (incr_bv 1 1 ?X))"
          by (simp add: all_const_def integer_reps)
        then have "prf_ok V' H (T # Ts) (map (incr_bv 1 0) Hs) (PAppt (incr_tbv 0 ?s) (Some (Bound 0)))
            (Abs a T (incr_bv 1 1 ?X) $ Bound 0)"
          by (rule prf_ok.PAppt) (auto simp: wty_def has_type_Bound_iff integer_reps)
        moreover have "tr (Abs a T (incr_bv 1 1 ?X) $ Bound 0) \<equiv>\<^sub>\<beta>\<^sub>\<eta> tr ?X"
        proof -
          have "proper ?X" using wX by (auto simp: wty_def intro: has_type_proper)
          then have e1: "tr (Abs a T (incr_bv 1 1 ?X) $ Bound 0) = dB.Abs (lift (tr ?X) (Suc 0)) \<degree> BVar 0"
            by (simp add: tr_incr_bv1 integer_reps)
          have e2: "dB.Abs (lift (tr ?X) (Suc 0)) \<degree> BVar 0 \<rightarrow>\<^sub>\<beta> tr ?X"
            using beta.beta[of "lift (tr ?X) (Suc 0)" "BVar 0"] by (simp only: subst_lift_0)
          show ?thesis unfolding e1 by (rule beta_into_equiv, rule r_into_rtranclp, rule e2)
        qed
        ultimately have "prf_ok V' H (T # Ts) (map (incr_bv 1 0) Hs) (PAppt (incr_tbv 0 ?s) (Some (Bound 0))) ?X"
          using wX by (rule prf_ok.conv)
        then show "prf_ok V' H (T # Ts) (map (incr_bv 1 0) Hs) (spine (False # bs) i (j + 1) (i + k - 1 - integer_of_nat m)) ?X"
          using spine_False[of j bs i] 2(5,6) by simp
      qed
    qed (use wG 2(3-6) 2(8-10) True in \<open>simp_all add: integer_of_nat_Suc\<close>)
    moreover have e: "Const STR ''Pure.all'' U = all_const T" using tG by (simp add: all_const_def)
    moreover have "lift_prems inc k pf Ts bs i j (Const c U $ Abs a T G') =
        Abst a None (lift_prems inc k pf (T # Ts) (False # bs) i (j + 1) G')" using True by simp
    ultimately have "prf_ok V' H Ts Hs (Abst a None (lift_prems inc k pf (T # Ts) (False # bs) i (j + 1) G'))
        (all_const T $ Abs a T (lift_all_aux inc (T # Ts) G' B))" by (auto intro!: prf_ok.Abst[where T = None, simplified])
    then show ?thesis using True tG by (simp add: all_const_def)
  next
    case False
    then show ?thesis
      using lift_prems_leaf[OF H 2(8-10), of Ts V' Hs bs i j] 2(3) 2(7) by simp
  qed
qed (rule lift_prems_leaf_gen[OF H]; (assumption | simp))+
lemma wty_list_implies:
  "wty V Ts (list_implies As B) propT \<Longrightarrow> (\<forall>A\<in>set As. wty V Ts A propT) \<and> wty V Ts B propT"
proof (induction As)
  case (Cons A As)
  from Cons.prems have "has_type V Ts (Const STR ''Pure.imp'' (propT \<rightarrow>\<^sub>T propT \<rightarrow>\<^sub>T propT) $ A $ list_implies As B) propT"
    "\<forall>v\<in>vars A \<union> vars (list_implies As B). 0 \<le> snd v" by (simp_all add: wty_def implies_def)
  then have "wty V Ts A propT" "wty V Ts (list_implies As B) propT" by (auto simp: wty_def dest!: has_type_imp_E)
  with Cons.IH show ?case by simp
qed simp

lemma prf_ok_mk_AbsP:
  "prf_ok V H Ts (rev Ps @ Hs) q X \<Longrightarrow> \<forall>P\<in>set Ps. wty V Ts P propT \<Longrightarrow>
    prf_ok V H Ts Hs (mk_AbsP Ps q) (list_implies Ps X)"
proof (induction Ps arbitrary: Hs)
  case (Cons P Ps)
  have "prf_ok V H Ts (P # Hs) (mk_AbsP Ps q) (list_implies Ps X)" using Cons by simp
  then show ?case using Cons.prems(2) by (auto simp: mk_AbsP_def intro: prf_ok.AbsP)
qed (simp add: mk_AbsP_def)

text \<open>
  \<open>Proofterm.lift_proof\<close>: a proof of the rule \<open>As \<Longrightarrow> B\<close> becomes a proof of the rule lifted
  over the subgoal \<open>G\<close>, whose premises are \<open>Logic.lift_all inc G\<close> of the premises. The types
  \<open>V'\<close> of the schematic variables of the lifted rule and of \<open>G\<close> agree with \<open>V\<close> on the lifted
  variables, which have indices of at least \<open>inc\<close>.
\<close>

theorem prf_ok_lift_proof:
  assumes H: "\<forall>h\<in>H. vars h = {} \<and> (\<forall>U\<in>tys h. tvars U = {}) \<and> \<not> loose_bvar h 0"
    and inc: "0 \<le> inc" and P: "prf_ok V H [] [] pf (list_implies As B)"
    and G: "wty V' [] G propT" and V': "lift_venv (rev (lift_Ts [] G)) inc V V'"
  shows "prf_ok V' H [] [] (lift_proof G inc (map (lift_all inc G) As) pf)
    (list_implies (map (lift_all inc G) As) (lift_all inc G B))"
proof -
  let ?Ps = "map (lift_all inc G) As"
  have wA: "\<forall>A\<in>set As. wty V [] A propT" "wty V [] B propT"
    using wty_list_implies[OF prf_ok_wty[OF P]] by auto
  have wP: "\<forall>P\<in>set ?Ps. wty V' [] P propT"
    using wA(1) G V' inc by (auto simp: lift_all_def intro: wty_lift_all_aux)
  have "prf_ok V' H [] (rev ?Ps) (lift_prems inc (integer_of_nat (length As)) pf [] [] 0 0 G) (lift_all_aux inc [] G B)"
  proof (rule prf_ok_lift_prems[OF H G V'])
    show "\<forall>m<length As. prf_ok V' H [] (rev ?Ps) (spine [] 0 0 (0 + integer_of_nat (length As) - 1 - integer_of_nat m))
        (lift_all_aux inc [] G (As ! m))"
    proof (intro allI impI)
      fix m assume m: "m < length As"
      have c: "integer_of_nat (length As) - 1 - integer_of_nat m = integer_of_nat (length As - Suc m)"
        using m by (simp add: integer_eq_iff integer_of_nat.rep_eq of_nat_diff)
      have "rev ?Ps ! (length As - Suc m) = lift_all inc G (As ! m)" using m by (simp add: rev_nth)
      moreover have "wty V' [] (lift_all inc G (As ! m)) propT" using wP m by auto
      ultimately show "prf_ok V' H [] (rev ?Ps) (spine [] 0 0 (0 + integer_of_nat (length As) - 1 - integer_of_nat m))
          (lift_all_aux inc [] G (As ! m))"
        using prf_ok.PBound[of "integer_of_nat (length As - Suc m)" "rev ?Ps" V' "[]" H] m
        by (simp add: spine_def c lift_all_def)
    qed
  qed (use inc P in simp_all)
  then show ?thesis using wP
    by (auto simp: lift_proof_def lift_all_def intro!: prf_ok_mk_AbsP)
qed

end

end

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
  closure has no schematic variables and its type variables are among the type arguments.
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

definition ann_ok :: "pterm option \<Rightarrow> pterm \<Rightarrow> bool" where
  "ann_ok t u \<longleftrightarrow> (case t of None \<Rightarrow> True | Some t \<Rightarrow> amatch t u)"

definition tann_ok :: "ptyp option \<Rightarrow> ptyp \<Rightarrow> bool" where
  "tann_ok T U \<longleftrightarrow> (case T of None \<Rightarrow> True | Some T \<Rightarrow> tmatch T U)"

lemma ann_ok_simps[simp]: "ann_ok None u" "ann_ok (Some t) u \<longleftrightarrow> amatch t u"
  "tann_ok None U" "tann_ok (Some T) U \<longleftrightarrow> tmatch T U"
  by (simp_all add: ann_ok_def tann_ok_def)


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
begin

definition atom_prop :: "pterm \<Rightarrow> ptyp list \<Rightarrow> pterm" where
  "atom_prop A Us = map_types (asubst (tyarg_inst (atom_tyargs A) Us)) (atom_closure A)"

definition atom_ok :: "pterm \<Rightarrow> ptyp list option \<Rightarrow> ptyp list \<Rightarrow> bool" where
  "atom_ok A Us' Us \<longleftrightarrow> length Us = length (atom_tyargs A) \<and> (case Us' of None \<Rightarrow> True | Some Us'' \<Rightarrow> Us'' = Us)"


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
    using AbsP.hyps(2) by (cases t) (auto intro: amatch_incr_idx)
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
    using PAppt.hyps(3) by (cases t') (auto intro: amatch_incr_idx)
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

end

end

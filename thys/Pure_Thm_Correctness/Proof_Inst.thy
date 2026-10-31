section \<open>Instantiation of proofs\<close>

theory Proof_Inst
  imports Proof_Judgment
begin

text \<open>
  An instantiation of the type variables by \<open>\<rho>\<close> and of the schematic variables by \<open>\<theta>\<close>; the
  values of \<open>\<theta>\<close> may contain loose bound variables, which refer to a context outside of the term
  and are lifted over the abstractions of the term. The instantiation ignores the types of the
  schematic variables; well-typed values have the instantiated types of the variables.
\<close>

fun psubst :: "tinst \<Rightarrow> (indexname \<Rightarrow> pterm) \<Rightarrow> integer \<Rightarrow> pterm \<Rightarrow> pterm" where
  "psubst \<rho> \<theta> lev (Var x T) = incr_boundvars lev (\<theta> x)"
| "psubst \<rho> \<theta> lev (Const c T) = Const c (tsubst \<rho> T)"
| "psubst \<rho> \<theta> lev (Free a T) = Free a (tsubst \<rho> T)"
| "psubst \<rho> \<theta> lev (Bound i) = Bound i"
| "psubst \<rho> \<theta> lev (Abs a T t) = Abs a (tsubst \<rho> T) (psubst \<rho> \<theta> (lev + 1) t)"
| "psubst \<rho> \<theta> lev (s $ t) = psubst \<rho> \<theta> lev s $ psubst \<rho> \<theta> lev t"

text \<open>The instantiation of a proof: of its term arguments, assumptions and types.\<close>

fun prf_inst :: "tinst \<Rightarrow> (indexname \<Rightarrow> pterm) \<Rightarrow> integer \<Rightarrow> prf \<Rightarrow> prf" where
  "prf_inst \<rho> \<theta> lev (Abst a T p) = Abst a (map_option (tsubst \<rho>) T) (prf_inst \<rho> \<theta> (lev + 1) p)"
| "prf_inst \<rho> \<theta> lev (AbsP a t p) = AbsP a (map_option (psubst \<rho> \<theta> lev) t) (prf_inst \<rho> \<theta> lev p)"
| "prf_inst \<rho> \<theta> lev (PAppt p t) = PAppt (prf_inst \<rho> \<theta> lev p) (map_option (psubst \<rho> \<theta> lev) t)"
| "prf_inst \<rho> \<theta> lev (PAppp p q) = PAppp (prf_inst \<rho> \<theta> lev p) (prf_inst \<rho> \<theta> lev q)"
| "prf_inst \<rho> \<theta> lev (PAxm a A Us) = PAxm a A (map_option (map (tsubst \<rho>)) Us)"
| "prf_inst \<rho> \<theta> lev (PClass T c) = PClass (tsubst \<rho> T) c"
| "prf_inst \<rho> \<theta> lev (Oracle a A Us) = Oracle a A (map_option (map (tsubst \<rho>)) Us)"
| "prf_inst \<rho> \<theta> lev (PThm (h, b)) = PThm (hd_set_types h (map_option (map (tsubst \<rho>)) (hd_types h)), b)"
| "prf_inst \<rho> \<theta> lev p = p"


subsection \<open>Terms\<close>

context prf_csig
begin

definition inst_code :: "tinst \<Rightarrow> (indexname \<Rightarrow> pterm) \<Rightarrow> nat \<Rightarrow> dB" where
  "inst_code \<rho> \<theta> n = (case atom_of n of
      AVar x \<Rightarrow> tr (\<theta> x)
    | AConst c T \<Rightarrow> dB.Var (code (AConst c (tsubst \<rho> T)))
    | AFree a T \<Rightarrow> dB.Var (code (AFree a (tsubst \<rho> T))))"

lemma tmatch_tsubst: "tmatch T U \<Longrightarrow> tmatch (tsubst \<rho> T) (tsubst \<rho> U)"
proof (induction rule: tmatch.induct)
  case (Type Ts Us a)
  then show ?case by (simp only: tsubst.simps) (intro tmatch.Type, auto simp: list.rel_map elim: list.rel_mono_strong)
next
  case (dummy U)
  have "tsubst \<rho> dummyT = dummyT" by (simp add: dummyT_def)
  then show ?case by (simp add: tmatch.dummy)
qed (auto intro: tmatch.intros)

lemma tr_incr_boundvars:
  "proper t \<Longrightarrow> 0 \<le> lev \<Longrightarrow> tr (incr_boundvars lev t) = liftn (nat_of_integer lev) (tr t) 0"
  using tr_incr_bv[of t lev 0] by (auto simp: incr_boundvars_def integer_reps)

lemma tr_psubst:
  "proper t \<Longrightarrow> (\<forall>x\<in>vars t. proper (\<theta> x)) \<Longrightarrow> 0 \<le> lev \<Longrightarrow>
    tr (psubst \<rho> \<theta> lev t) = vsubst (inst_code \<rho> \<theta>) (nat_of_integer lev) (tr t)"
proof (induction \<rho> \<theta> lev t rule: psubst.induct)
  case (5 \<rho> \<theta> lev a T t)
  then show ?case by (simp add: nat_of_integer_plus1)
qed (auto simp: inst_code_def tr_incr_boundvars)

lemma incr_bv_incr_bv_le: "m \<le> k \<Longrightarrow> k \<le> m + n \<Longrightarrow> incr_bv 1 k (incr_bv n m v) = incr_bv (n + 1) m v"
  by (induction n m v arbitrary: k rule: incr_bv.induct) auto

lemma incr_bv_0[simp]: "incr_bv 0 k v = v"
  by (induction "0 :: integer" k v rule: incr_bv.induct) auto

lemma incr_boundvars_eq: "incr_boundvars n v = incr_bv n 0 v"
  by (simp add: incr_boundvars_def)

lemma incr_boundvars_incr_bv:
  "0 \<le> k \<Longrightarrow> k \<le> n \<Longrightarrow> incr_bv 1 k (incr_boundvars n v) = incr_boundvars (n + 1) v"
  by (simp add: incr_boundvars_eq incr_bv_incr_bv_le)

lemma psubst_incr_bv:
  "0 \<le> k \<Longrightarrow> k \<le> lev \<Longrightarrow> psubst \<rho> \<theta> (lev + 1) (incr_bv 1 k t) = incr_bv 1 k (psubst \<rho> \<theta> lev t)"
  by (induction \<rho> \<theta> lev t arbitrary: k rule: psubst.induct) (auto simp: incr_boundvars_incr_bv)

lemma amatch_psubst: "amatch t u \<Longrightarrow> amatch (psubst \<rho> \<theta> lev t) (psubst \<rho> \<theta> lev u)"
proof (induction arbitrary: lev rule: amatch.induct)
  case (Var T U x)
  then show ?case by simp
qed (auto intro: amatch.intros tmatch_tsubst)


lemma vars_psubst: "vars (psubst \<rho> \<theta> lev t) = (\<Union>x\<in>vars t. vars (\<theta> x))"
  by (induction \<rho> \<theta> lev t rule: psubst.induct) (auto simp: incr_boundvars_eq vars_incr_bv)

lemma has_type_psubst:
  "has_type V Ts t T \<Longrightarrow> (\<forall>x\<in>vars t. has_type V' Us (\<theta> x) (tsubst \<rho> (V x))) \<Longrightarrow>
    has_type V' (map (tsubst \<rho>) Ts @ Us) (psubst \<rho> \<theta> (integer_of_nat (length Ts)) t) (tsubst \<rho> T)"
proof (induction rule: has_type.induct)
  case (Const a T V Ts)
  then show ?case by (auto intro: has_type.Const)
next
  case (Free V Ts a T)
  then show ?case by (auto intro: has_type.Free)
next
  case (Var V x T Ts)
  then have "has_type V' Us (\<theta> x) (tsubst \<rho> T)" by simp
  then show ?case
    using has_type_incr_bv[of V' Us "\<theta> x" "tsubst \<rho> T" "integer_of_nat (length Ts)" 0 "map (tsubst \<rho>) Ts"]
    by (simp add: incr_boundvars_eq integer_reps)
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

definition inst_typed :: "(indexname \<Rightarrow> ptyp) \<Rightarrow> (indexname \<Rightarrow> ptyp) \<Rightarrow> ptyp list \<Rightarrow> tinst \<Rightarrow> (indexname \<Rightarrow> pterm) \<Rightarrow> bool" where
  "inst_typed V V' Us \<rho> \<theta> \<longleftrightarrow> (\<forall>x. 0 \<le> snd x \<longrightarrow> wty V' Us (\<theta> x) (tsubst \<rho> (V x)))"

lemma inst_typedD: "inst_typed V V' Us \<rho> \<theta> \<Longrightarrow> 0 \<le> snd x \<Longrightarrow> wty V' Us (\<theta> x) (tsubst \<rho> (V x))"
  by (cases x) (simp add: inst_typed_def)

lemma inst_typed_vars:
  "inst_typed V V' Us \<rho> \<theta> \<Longrightarrow> wty V Ts t T \<Longrightarrow> x \<in> vars t \<Longrightarrow> wty V' Us (\<theta> x) (tsubst \<rho> (V x))"
  by (rule inst_typedD) (auto simp: wty_def)

lemma inst_typed_proper: "inst_typed V V' Us \<rho> \<theta> \<Longrightarrow> wty V Ts t T \<Longrightarrow> \<forall>x\<in>vars t. proper (\<theta> x)"
  by (auto dest!: inst_typed_vars simp: wty_def intro: has_type_proper)

lemma wty_psubst:
  assumes "wty V Ts t T" "inst_typed V V' Us \<rho> \<theta>"
  shows "wty V' (map (tsubst \<rho>) Ts @ Us) (psubst \<rho> \<theta> (integer_of_nat (length Ts)) t) (tsubst \<rho> T)"
proof -
  have x: "wty V' Us (\<theta> x) (tsubst \<rho> (V x))" if "x \<in> vars t" for x
    using assms(2,1) that by (rule inst_typed_vars)
  have "has_type V' (map (tsubst \<rho>) Ts @ Us) (psubst \<rho> \<theta> (integer_of_nat (length Ts)) t) (tsubst \<rho> T)"
    using assms(1) x by (intro has_type_psubst) (auto simp: wty_def)
  moreover have "\<forall>v\<in>vars (psubst \<rho> \<theta> (integer_of_nat (length Ts)) t). 0 \<le> snd v"
    using x by (auto simp: vars_psubst wty_def)
  ultimately show ?thesis by (simp add: wty_def)
qed

lemma psubst_no_vars: "vars t = {} \<Longrightarrow> psubst \<rho> \<theta> lev t = map_types (tsubst \<rho>) t"
  by (induction \<rho> \<theta> lev t rule: psubst.induct) auto

lemma tsubst_asubst: "tsubst \<rho> (asubst f T) = asubst (tsubst \<rho> \<circ> f) T"
  by (induction T) auto

lemma tsubst_no_tvars': "tvars T = {} \<Longrightarrow> tsubst \<rho> T = T"
  by (induction T) (auto simp: map_idI)

lemma atom_prop_psubst:
  assumes "length Us = length (atom_tyargs A)"
  shows "psubst \<rho> \<theta> lev (atom_prop A Us) = atom_prop A (map (tsubst \<rho>) Us)"
proof -
  have "psubst \<rho> \<theta> lev (atom_prop A Us) =
      map_types (tsubst \<rho> \<circ> asubst (tyarg_inst (atom_tyargs A) Us)) (atom_closure A)"
    by (simp add: atom_prop_def psubst_no_vars vars_atom_closure map_types_comp)
  also have "\<dots> = atom_prop A (map (tsubst \<rho>) Us)"
    unfolding atom_prop_def
  proof (rule map_types_cong)
    fix U assume U: "U \<in> csig.tys (atom_closure A)"
    have "tsubst \<rho> (asubst (tyarg_inst (atom_tyargs A) Us) U) = asubst (tsubst \<rho> \<circ> tyarg_inst (atom_tyargs A) Us) U"
      by (rule tsubst_asubst)
    also have "\<dots> = asubst (tyarg_inst (atom_tyargs A) (map (tsubst \<rho>) Us)) U"
      using atyps_atom_closure[OF U] assms by (intro asubst_cong) (auto simp: tyarg_inst_map)
    finally show "(tsubst \<rho> \<circ> asubst (tyarg_inst (atom_tyargs A) Us)) U =
        asubst (tyarg_inst (atom_tyargs A) (map (tsubst \<rho>) Us)) U" by simp
  qed
  finally show ?thesis .
qed

lemma psubst_hyp: "vars h = {} \<Longrightarrow> \<forall>U\<in>tys h. tvars U = {} \<Longrightarrow> psubst \<rho> \<theta> lev h = h"
proof -
  assume "vars h = {}" "\<forall>U\<in>tys h. tvars U = {}"
  moreover have "\<forall>U\<in>tys h. tvars U = {} \<Longrightarrow> map_types (tsubst \<rho>) h = h"
    by (induction h) (auto simp: tsubst_no_tvars')
  ultimately show ?thesis by (simp add: psubst_no_vars)
qed

lemma psubst_implies[simp]: "psubst \<rho> \<theta> lev implies = implies"
  by (simp add: implies_def propT_def)

lemma psubst_all_const[simp]: "psubst \<rho> \<theta> lev (all_const U) = all_const (tsubst \<rho> U)"
  by (simp add: all_const_def propT_def)

lemma psubst_of_class: "psubst \<rho> \<theta> lev (of_class T c) = of_class (tsubst \<rho> T) c"
  by (simp add: of_class_def propT_def)

lemma atom_ok_tsubst: "atom_ok A Us' Us \<Longrightarrow> atom_ok A (map_option (map (tsubst \<rho>)) Us') (map (tsubst \<rho>) Us)"
  by (auto simp: atom_ok_def split: option.splits)

theorem prf_ok_pinst:
  assumes H: "\<forall>h\<in>H. vars h = {} \<and> (\<forall>U\<in>tys h. tvars U = {})" and \<theta>: "inst_typed V V' Us \<rho> \<theta>"
  shows "prf_ok V H Ts Hs p \<phi> \<Longrightarrow>
    prf_ok V' H (map (tsubst \<rho>) Ts @ Us) (map (psubst \<rho> \<theta> (integer_of_nat (length Ts))) Hs)
      (prf_inst \<rho> \<theta> (integer_of_nat (length Ts)) p) (psubst \<rho> \<theta> (integer_of_nat (length Ts)) \<phi>)"
proof (induction rule: prf_ok.induct)
  case (conv Ts Hs p \<phi> \<psi>)
  have w: "wty V Ts \<phi> propT" "wty V Ts \<psi> propT" using prf_ok_wty[OF conv.hyps(1)] conv.hyps(3) by auto
  have pr: "proper \<phi>" "proper \<psi>" "\<forall>x\<in>vars \<phi>. proper (\<theta> x)" "\<forall>x\<in>vars \<psi>. proper (\<theta> x)"
    using w inst_typed_proper[OF \<theta>] by (auto simp: wty_def intro: has_type_proper)
  have "tr (psubst \<rho> \<theta> (integer_of_nat (length Ts)) \<phi>) \<equiv>\<^sub>\<beta>\<^sub>\<eta> tr (psubst \<rho> \<theta> (integer_of_nat (length Ts)) \<psi>)"
    unfolding tr_psubst[OF pr(1,3) integer_of_nat_nonneg] tr_psubst[OF pr(2,4) integer_of_nat_nonneg]
    by (rule vsubst_equiv) (rule conv.hyps(2))
  with conv.IH show ?case
    using wty_psubst[OF conv.hyps(3) \<theta>] by (auto intro: prf_ok.conv)
next
  case (MinProof Ts \<phi> Hs)
  then show ?case using wty_psubst[OF MinProof \<theta>] by (auto intro: prf_ok.MinProof)
next
  case (PBound i Hs Ts)
  then show ?case
    using wty_psubst[OF PBound(3) \<theta>] prf_ok.PBound[of i "map (psubst \<rho> \<theta> (integer_of_nat (length Ts))) Hs"]
    by simp
next
  case (AbsP Ts A t Hs p B a)
  have "ann_ok (map_option (psubst \<rho> \<theta> (integer_of_nat (length Ts))) t) (psubst \<rho> \<theta> (integer_of_nat (length Ts)) A)"
    using AbsP.hyps(2) by (cases t) (auto intro: amatch_psubst)
  with AbsP show ?case using wty_psubst[OF AbsP.hyps(1) \<theta>] by (auto intro: prf_ok.AbsP)
next
  case (Abst T U Ts Hs p B a b)
  have eq: "map (psubst \<rho> \<theta> (integer_of_nat (length Ts) + 1) \<circ> incr_bv 1 0) Hs =
      map (incr_bv 1 0 \<circ> psubst \<rho> \<theta> (integer_of_nat (length Ts))) Hs"
    by (simp add: psubst_incr_bv)
  have "tann_ok (map_option (tsubst \<rho>) T) (tsubst \<rho> U)"
    using Abst.hyps(1) by (cases T) (auto intro: tmatch_tsubst)
  moreover have "prf_ok V' H (tsubst \<rho> U # map (tsubst \<rho>) Ts @ Us)
      (map (incr_bv 1 0) (map (psubst \<rho> \<theta> (integer_of_nat (length Ts))) Hs))
      (prf_inst \<rho> \<theta> (integer_of_nat (length Ts) + 1) p) (psubst \<rho> \<theta> (integer_of_nat (length Ts) + 1) B)"
    using Abst.IH by (simp add: integer_of_nat_Suc eq)
  ultimately show ?case by (auto intro: prf_ok.Abst)
next
  case (PAppt Ts Hs p U f t t')
  have "ann_ok (map_option (psubst \<rho> \<theta> (integer_of_nat (length Ts))) t') (psubst \<rho> \<theta> (integer_of_nat (length Ts)) t)"
    using PAppt.hyps(3) by (cases t') (auto intro: amatch_psubst)
  with PAppt show ?case using wty_psubst[OF PAppt.hyps(2) \<theta>] by (auto intro: prf_ok.PAppt)
next
  case (PAppp Ts Hs p A B q)
  then show ?case by (auto intro: prf_ok.PAppp)
next
  case (Hyp t Ts Hs)
  then show ?case using H wty_psubst[OF Hyp(2) \<theta>] psubst_hyp[of t] by (auto intro: prf_ok.Hyp)
next
  case (PAxm A Us' Us0 Ts Hs a)
  then show ?case using wty_psubst[OF PAxm(2) \<theta>]
    by (auto simp: atom_prop_psubst atom_ok_def intro!: prf_ok.PAxm atom_ok_tsubst)
next
  case (Oracle A Us' Us0 Ts Hs a)
  then show ?case using wty_psubst[OF Oracle(2) \<theta>]
    by (auto simp: atom_prop_psubst atom_ok_def intro!: prf_ok.Oracle atom_ok_tsubst)
next
  case (PThm h Us0 Ts Hs b)
  let ?h = "hd_set_types h (map_option (map (tsubst \<rho>)) (hd_types h))"
  have "atom_ok (hd_prop ?h) (hd_types ?h) (map (tsubst \<rho>) Us0)"
    using PThm(1) by (auto simp: atom_ok_def split: option.splits)
  then show ?case using wty_psubst[OF PThm(2) \<theta>] PThm(1) prf_ok.PThm[of ?h "map (tsubst \<rho>) Us0"]
    by (auto simp: atom_prop_psubst atom_ok_def)
next
  case (PClass Ts T c Hs)
  then show ?case using wty_psubst[OF PClass \<theta>] by (auto simp: psubst_of_class intro: prf_ok.PClass)
qed

end

end

section \<open>Lifting proofs\<close>

theory Proof_Lift
  imports Proof_Judgment
begin

text \<open>
  \<^const>\<open>lift_proof\<close> turns a valid proof of a rule into a valid proof of the rule lifted over a
  subgoal (\<open>prf_valid_lift_proof\<close>). The proof of each lifted premise is applied to the
  parameters and assumptions of the subgoal (a spine), and the proof of the rule is lifted
  (\<^const>\<open>lift_prf\<close>). The lifted proof of the rule is a proof of an instance of the rule at
  fresh free variables for the parameters, which are then replaced by the parameters
  (\<open>prf_ok_fsubst\<close>).
\<close>


subsection \<open>Weakening\<close>

lemma integer_of_nat_0 [simp]: "integer_of_nat 0 = 0"
  by (simp add: integer_eq_iff integer_of_nat.rep_eq)

lemma integer_of_nat_Suc: "integer_of_nat (Suc n) = integer_of_nat n + 1"
  by (simp add: integer_eq_iff integer_of_nat.rep_eq)

lemma nat_of_integer_plus1: "0 \<le> c \<Longrightarrow> nat_of_integer (c + 1) = Suc (nat_of_integer c)"
  by (simp add: nat_of_integer.rep_eq less_eq_integer.rep_eq nat_add_distrib)

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
  "incr_tbv c (AbsP a t p) = AbsP a (map_option (\<lambda>t. lift t c) t) (incr_tbv c p)"
| "incr_tbv c (Abst a T p) = Abst a T (incr_tbv (c + 1) p)"
| "incr_tbv c (PAppt p t) = PAppt (incr_tbv c p) (map_option (\<lambda>t. lift t c) t)"
| "incr_tbv c (PAppp p q) = PAppp (incr_tbv c p) (incr_tbv c q)"
| "incr_tbv c p = p"

lemma ueq_cong:
  assumes "\<And>x y. sup beta eta x y \<Longrightarrow> sup beta eta (f x) (f y)"
  shows "equivclp (sup beta eta) x y \<Longrightarrow> equivclp (sup beta eta) (f x) (f y)"
proof (induction rule: equivclp_induct)
  case (step y z)
  have "sup beta eta (f y) (f z) \<or> sup beta eta (f z) (f y)" using step(2) assms by blast
  from equivclp_into_equivclp[OF step(3) this] show ?case .
qed simp

lemma ueq_lift: "s \<approx> t \<Longrightarrow> 0 \<le> k \<Longrightarrow> lift s k \<approx> lift t k"
proof -
  assume st: "s \<approx> t" and k: "0 \<le> k"
  have "sup beta eta x y \<Longrightarrow> sup beta eta (lift x k) (lift y k)" for x y
    using k by (auto intro: lift_preserves_beta eta_lift)
  from ueq_cong[OF this st] show ?thesis by simp
qed

context prf_sig
begin

lemma prf_ok_incr_pbv:
  "prf_ok ax H e Hs p \<phi> \<Longrightarrow> 0 \<le> c \<Longrightarrow> nat_of_integer c \<le> length Hs \<Longrightarrow>
    prf_ok ax H e (take (nat_of_integer c) Hs @ A # drop (nat_of_integer c) Hs) (incr_pbv c p) \<phi>"
proof (induction arbitrary: c A rule: prf_ok.induct)
  case (conv e Hs p \<phi> \<psi>)
  then show ?case by (auto intro: prf_ok.conv)
next
  case (PBound i Hs e)
  let ?Hs = "take (nat_of_integer c) Hs @ A # drop (nat_of_integer c) Hs"
  show ?case
  proof (cases "c \<le> i")
    case True
    then have "nat_of_integer c \<le> nat_of_integer i" by (simp add: integer_reps nat_mono)
    then have "?Hs ! nat_of_integer (i + 1) = Hs ! nat_of_integer i"
      using PBound nat_of_integer_plus1[of i] by (simp add: nth_append)
    moreover have "nat_of_integer (i + 1) < length ?Hs"
      using PBound nat_of_integer_plus1[of i] by simp
    ultimately show ?thesis
      using True PBound prf_ok.PBound[of "i + 1" ?Hs] by simp
  next
    case False
    then have "nat_of_integer i < nat_of_integer c" using PBound(1) by (simp add: integer_reps)
    then have "?Hs ! nat_of_integer i = Hs ! nat_of_integer i"
      using PBound.prems by (simp add: nth_append)
    then show ?thesis
      using False PBound prf_ok.PBound[of i ?Hs] by simp
  qed
next
  case (AbsP e A' t Hs p B a)
  have "prf_ok ax H e (take (nat_of_integer (c + 1)) (A' # Hs) @ A # drop (nat_of_integer (c + 1)) (A' # Hs))
      (incr_pbv (c + 1) p) B"
    using AbsP.IH[of "c + 1" A] AbsP.prems nat_of_integer_plus1[of c] by simp
  then show ?case using AbsP nat_of_integer_plus1[of c] by (auto intro: prf_ok.AbsP)
next
  case (Abst T U e Hs p B a b)
  have "prf_ok ax H (e\<langle>0:U\<rangle>) (take (nat_of_integer c) (map (incr_bv 1 0) Hs) @ incr_bv 1 0 A #
      drop (nat_of_integer c) (map (incr_bv 1 0) Hs)) (incr_pbv c p) B"
    using Abst by simp
  then show ?case using Abst by (auto intro: prf_ok.Abst simp: take_map drop_map)
next
  case (PAppp e Hs p A' B q)
  show ?case unfolding incr_pbv.simps
    by (rule prf_ok.PAppp[OF PAppp.IH(1)[OF PAppp.prems] PAppp.IH(2)[OF PAppp.prems]])
qed (auto intro: prf_ok.intros)

lemma prf_ok_incr_tbv:
  assumes H: "\<And>h. h \<in> H \<Longrightarrow> closed h"
  shows "prf_ok ax H e Hs p \<phi> \<Longrightarrow> 0 \<le> c \<Longrightarrow>
    prf_ok ax H (e\<langle>c:U\<rangle>) (map (\<lambda>h. lift h c) Hs) (incr_tbv c p) (lift \<phi> c)"
proof (induction arbitrary: c U rule: prf_ok.induct)
  case (conv e Hs p \<phi> \<psi>)
  then show ?case by (auto intro: prf_ok.conv conv_lift)
next
  case (PBound i Hs e)
  then show ?case using prf_ok.PBound[of i "map (\<lambda>h. lift h c) Hs"] by auto
next
  case (AbsP e A t Hs p B a)
  then show ?case by (auto intro!: prf_ok.AbsP intro: ueq_lift[simplified] simp: ann_ok_def split: option.splits)
next
  case (Abst T U' e Hs p B a b)
  have eq: "map (\<lambda>h. lift h (c + 1)) (map (incr_bv 1 0) Hs) = map (incr_bv 1 0) (map (\<lambda>h. lift h c) Hs)"
    using lift_lift[of 0 c] Abst.prems by simp
  have "prf_ok ax H (e\<langle>0:U'\<rangle>\<langle>c + 1:U\<rangle>) (map (\<lambda>h. lift h (c + 1)) (map (incr_bv 1 0) Hs)) (incr_tbv (c + 1) p)
      (lift B (c + 1))"
    using Abst.IH[of "c + 1" U] Abst.prems by simp
  then have "prf_ok ax H (e\<langle>c:U\<rangle>\<langle>0:U'\<rangle>) (map (incr_bv 1 0) (map (\<lambda>h. lift h c) Hs)) (incr_tbv (c + 1) p)
      (lift B (c + 1))"
    unfolding eq using shift_commute[OF Abst.prems, of e U U'] by simp
  then show ?case using Abst.hyps(1,2) by (simp add: prf_ok.Abst)
next
  case (PAppt e Hs p U' f t t')
  then show ?case by (auto intro!: prf_ok.PAppt intro: ueq_lift[simplified] simp: ann_ok_def split: option.splits)
next
  case (PAppp e Hs p A B q)
  have "prf_ok ax H (e\<langle>c:U\<rangle>) (map (\<lambda>h. lift h c) Hs) (incr_tbv c p) (implies $ lift A c $ lift B c)"
    using PAppp.IH(1)[OF PAppp.prems, of U] by simp
  then show ?case using PAppp.IH(2)[OF PAppp.prems, of U] by (simp add: prf_ok.PAppp)
next
  case (Hyp t e Hs)
  have "lift t c = t" using H[OF Hyp.hyps(1)] Hyp.prems by (rule incr_bv_closed)
  with Hyp lift_type[OF Hyp.hyps(2) Hyp.prems, of U] show ?case by (simp add: prf_ok.Hyp)
next
  case (PAxm A Us' Us e Hs a)
  have "lift (atom_prop A Us) c = atom_prop A Us" using closed_atom_prop PAxm.prems by (rule incr_bv_closed)
  with PAxm lift_type[OF PAxm.hyps(3) PAxm.prems, of U] show ?case by (simp add: prf_ok.PAxm)
next
  case (Oracle A Us' Us e Hs a)
  have "lift (atom_prop A Us) c = atom_prop A Us" using closed_atom_prop Oracle.prems by (rule incr_bv_closed)
  with Oracle lift_type[OF Oracle.hyps(3) Oracle.prems, of U] show ?case by (simp add: prf_ok.Oracle)
next
  case (PThm h Us e Hs b)
  have "lift (atom_prop (hd_prop h) Us) c = atom_prop (hd_prop h) Us"
    using closed_atom_prop PThm.prems by (rule incr_bv_closed)
  with PThm lift_type[OF PThm.hyps(3) PThm.prems, of U] show ?case by (simp add: prf_ok.PThm)
next
  case (PClass T c' e Hs)
  have "lift (of_class T c') c = of_class T c'" by (simp add: of_class_def)
  with PClass lift_type[OF PClass.hyps(2) PClass.prems, of U] show ?case by (simp add: prf_ok.PClass)
qed

end


subsection \<open>Spines\<close>

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

context prf_sig
begin

lemma prf_ap_spine: "prf_ap \<rho> \<sigma> (spine bs i j c) = spine bs i j c"
proof -
  have "prf_ap \<rho> \<sigma> (snd (snd (foldr mk_app bs (a, b, p)))) = snd (snd (foldr mk_app bs (a, b, prf_ap \<rho> \<sigma> p)))"
    for a b p
  proof (induction bs)
    case (Cons x bs)
    show ?case unfolding foldr_mk_app_Cons using Cons by (cases x) (simp_all add: prf_ap_def)
  qed simp
  then show ?thesis by (simp add: spine_def prf_ap_def)
qed

lemma prf_ap_proof_combP: "prf_ap \<rho> \<sigma> (proof_combP p qs) = proof_combP (prf_ap \<rho> \<sigma> p) (map (prf_ap \<rho> \<sigma>) qs)"
  by (induction qs arbitrary: p) (simp_all add: proof_combP_def prf_ap_def)

lemma prf_ap_mk_AbsP: "prf_ap \<rho> \<sigma> (mk_AbsP xs p) = mk_AbsP xs (prf_ap \<rho> \<sigma> p)"
  by (induction xs) (simp_all add: mk_AbsP_def prf_ap_def)

lemma mk_AbsP_length: "length xs = length ys \<Longrightarrow> mk_AbsP xs p = mk_AbsP ys p"
  by (induction xs ys rule: list_induct2) (simp_all add: mk_AbsP_def)

lemma prf_ok_proof_combP:
  "prf_ok ax H e Hs p (list_implies As B) \<Longrightarrow> list_all2 (prf_ok ax H e Hs) qs As \<Longrightarrow>
    prf_ok ax H e Hs (proof_combP p qs) B"
proof (induction As arbitrary: p qs)
  case Nil
  then show ?case by (simp add: proof_combP_def)
next
  case (Cons A As)
  then obtain q qs' where "qs = q # qs'" by (cases qs) auto
  with Cons show ?case by (auto simp: proof_combP_def intro: prf_ok.PAppp)
qed

lemma prf_ok_foldr_AbsP:
  "prf_ok ax H e (rev Ps @ Hs) q X \<Longrightarrow> \<forall>P\<in>set Ps. e \<turnstile> P : propT \<Longrightarrow> list_all2 ann_ok ts Ps \<Longrightarrow>
    prf_ok ax H e Hs (foldr (\<lambda>t p. AbsP (STR ''H'') t p) ts q) (list_implies Ps X)"
proof (induction Ps arbitrary: Hs ts)
  case (Cons P Ps)
  then obtain t ts' where ts: "ts = t # ts'" "ann_ok t P" "list_all2 ann_ok ts' Ps"
    by (cases ts) auto
  have "prf_ok ax H e (P # Hs) (foldr (\<lambda>t p. AbsP (STR ''H'') t p) ts' q) (list_implies Ps X)"
    using Cons ts by simp
  then show ?case using Cons.prems(2) ts by (auto intro: prf_ok.AbsP)
qed simp

lemma prf_ok_mk_AbsP:
  "prf_ok ax H e (rev Ps @ Hs) q X \<Longrightarrow> \<forall>P\<in>set Ps. e \<turnstile> P : propT \<Longrightarrow>
    prf_ok ax H e Hs (mk_AbsP Ps q) (list_implies Ps X)"
proof (induction Ps arbitrary: Hs)
  case (Cons P Ps)
  have "prf_ok ax H e (P # Hs) (mk_AbsP Ps q) (list_implies Ps X)" using Cons by simp
  then show ?case using Cons.prems(2) by (auto simp: mk_AbsP_def intro: prf_ok.AbsP)
qed (simp add: mk_AbsP_def)

end


subsection \<open>Parameters as fresh free variables\<close>

text \<open>
  \<open>pvar xs Us lev\<close> maps the fresh free variable \<open>xs ! k :: Us ! k\<close> to the parameter \<open>k\<close>
  (the outermost first) at level \<open>lev\<close>, and every other free variable to itself.
\<close>

definition pvar :: "name list \<Rightarrow> ptyp list \<Rightarrow> integer \<Rightarrow> name \<Rightarrow> ptyp \<Rightarrow> pterm" where
  "pvar xs Us lev x U = (case map_of (zip xs [0..<length xs]) x of
    Some k \<Rightarrow> if U = Us ! k then Bound (lev + of_nat (length xs - 1 - k)) else Free x U
  | None \<Rightarrow> Free x U)"

lemma lift_pvar: "0 \<le> lev \<Longrightarrow> lift (pvar xs Us lev x U) 0 = pvar xs Us (lev + 1) x U"
  by (auto simp: pvar_def algebra_simps split: option.split dest!: map_of_SomeD dest: set_zip_leftD)

lemma pvar_notin: "x \<notin> set xs \<Longrightarrow> pvar xs Us lev x U = Free x U"
  by (auto simp: pvar_def split: option.split dest!: map_of_SomeD dest: set_zip_leftD)

lemma pvar_nth:
  "distinct xs \<Longrightarrow> k < length xs \<Longrightarrow> pvar xs Us lev (xs ! k) (Us ! k) = Bound (lev + of_nat (length xs - 1 - k))"
  using map_of_zip_nth[of xs "[0..<length xs]" k] by (simp add: pvar_def)

lemma pvar_cases:
  assumes "pvar xs Us lev x U \<noteq> Free x U"
  obtains k where "k < length xs" "x = xs ! k" "U = Us ! k" "pvar xs Us lev x U = Bound (lev + of_nat (length xs - 1 - k))"
proof -
  obtain k where k: "map_of (zip xs [0..<length xs]) x = Some k" "U = Us ! k"
    using assms by (auto simp: pvar_def split: option.splits if_splits)
  from map_of_SomeD[OF k(1)] have "k < length xs" "x = xs ! k"
    by (auto simp: set_zip)
  with k that show ?thesis by (simp add: pvar_def)
qed

lemma fnames_combound [simp]: "fnames (combound t n k) = fnames t"
  by (induction t n k rule: combound.induct) simp_all

lemma fsubst_apps: "fsubst \<tau> (s \<degree>\<degree> ts) = fsubst \<tau> s \<degree>\<degree> map (fsubst \<tau>) ts"
  by (induction ts arbitrary: s) simp_all

lemma hd_set_types_twice [simp]: "hd_set_types (hd_set_types h Ts) Us = hd_set_types h Us"
  by (simp add: hd_set_types_def)

lemma prf_atoms_map_proof_terms [simp]: "prf_atoms (map_proof_terms f g p) = prf_atoms p"
  by (induction p rule: prf_atoms.induct) simp_all

context prf_sig
begin

lemma typing_pvar:
  assumes l: "length Us = length xs" and d: "distinct xs" and U: "cert_typ alg ar U"
  shows "pushes e Us \<turnstile> pvar xs Us 0 x U : U"
proof (cases "pvar xs Us 0 x U = Free x U")
  case False
  then obtain k where k: "k < length xs" "x = xs ! k" "U = Us ! k" "pvar xs Us 0 x U = Bound (of_nat (length xs - 1 - k))"
    by (rule pvar_cases) simp
  have "pushes e Us (of_nat (length xs - 1 - k)) = Us ! k" using pushes_of_nat[of "length xs - 1 - k" Us e] l k(1) by simp
  moreover have "(0 :: integer) \<le> of_nat (length xs - 1 - k)" by (rule of_nat_0_le_iff)
  ultimately have "pushes e Us \<turnstile> Bound (of_nat (length xs - 1 - k)) : U" using k(3) by (intro typing.Bound) simp_all
  with k(4) show ?thesis by simp
qed (use U in auto)

text \<open>The instance at the fresh variables, with the fresh variables replaced by the parameters:\<close>

lemma fsubst_ap_incr_idx:
  fixes xs :: "name list" and \<rho> :: tinst and Us :: "ptyp list"
  defines "Us' \<equiv> map (tsubst \<rho>) Us"
  defines "fs \<equiv> map (\<lambda>(F, T). Free F T) (zip xs Us')"
  assumes l: "length xs = length Us" and d: "distinct xs"
  shows "fnames (ap \<rho> \<sigma> (incr_idx Us inc lev t)) \<inter> set xs = {} \<Longrightarrow> 0 \<le> lev \<Longrightarrow>
    fsubst (pvar xs Us' lev) (ap (tinc inc \<rho>) (lsubst inc \<rho> Us \<sigma> fs) t) = ap \<rho> \<sigma> (incr_idx Us inc lev t)"
proof (induction t arbitrary: lev)
  case (Var xi T)
  obtain x i where xi: "xi = (x, i)" by (cases xi)
  let ?c = "\<sigma> (x, i + inc) (foldr fun_type Us' (tsubst (tinc inc \<rho>) T))"
  have ty: "tsubst \<rho> (foldr fun_type Us (incr_tvar inc T)) = foldr fun_type Us' (tsubst (tinc inc \<rho>) T)"
    unfolding Us'_def by (induction Us) (simp_all add: tsubst_incr_tvar)
  have r: "ap \<rho> \<sigma> (incr_idx Us inc lev (Var xi T)) = combound ?c lev (length Us)"
    by (simp add: xi ap_combound ty)
  have c: "fsubst (pvar xs Us' lev) ?c = ?c"
    by (rule fsubst_id) (use Var.prems(1) in \<open>auto simp: r fnames_combound intro: pvar_notin\<close>)
  have m: "map (fsubst (pvar xs Us' lev)) fs = map (\<lambda>i. Bound (lev + integer_of_nat i)) (rev [0..<length Us])"
  proof (rule nth_equalityI)
    show "length (map (fsubst (pvar xs Us' lev)) fs) = length (map (\<lambda>i. Bound (lev + integer_of_nat i)) (rev [0..<length Us]))"
      using l by (simp add: fs_def Us'_def)
    fix k assume "k < length (map (fsubst (pvar xs Us' lev)) fs)"
    then have k: "k < length xs" using l by (simp add: fs_def Us'_def)
    have "fs ! k = Free (xs ! k) (Us' ! k)" "length fs = length xs" using k l by (simp_all add: fs_def Us'_def)
    then show "map (fsubst (pvar xs Us' lev)) fs ! k = map (\<lambda>i. Bound (lev + integer_of_nat i)) (rev [0..<length Us]) ! k"
      using pvar_nth[OF d k, of Us' lev] k l by (simp add: rev_nth integer_of_nat_eq_of_nat of_nat_diff)
  qed
  have A: "ap (tinc inc \<rho>) (lsubst inc \<rho> Us \<sigma> fs) (Var xi T) = ?c \<degree>\<degree> fs"
    by (simp add: xi lsubst_def Us'_def)
  have B: "fsubst (pvar xs Us' lev) (?c \<degree>\<degree> fs) = ?c \<degree>\<degree> map (\<lambda>i. Bound (lev + integer_of_nat i)) (rev [0..<length Us])"
    by (simp only: fsubst_apps c m)
  have C: "ap \<rho> \<sigma> (incr_idx Us inc lev (Var xi T)) = ?c \<degree>\<degree> map (\<lambda>i. Bound (lev + integer_of_nat i)) (rev [0..<length Us])"
    using r by (simp only: combound_apps)
  show ?case by (simp only: A B C)
next
  case (Free y T)
  have "y \<notin> set xs" using Free.prems(1) by simp
  then show ?case by (simp add: pvar_notin tsubst_incr_tvar)
next
  case (Abs a T t)
  have "fsubst (\<lambda>x U. lift (pvar xs Us' lev x U) 0) = fsubst (pvar xs Us' (lev + 1))"
    using lift_pvar[OF Abs.prems(2)] by presburger
  with Abs show ?case by (simp add: tsubst_incr_tvar)
qed (simp_all add: tsubst_incr_tvar Int_Un_distrib2)

lemma prf_fsubst_prf_ap_lift_prf:
  fixes xs :: "name list" and \<rho> :: tinst and Us :: "ptyp list"
  defines "Us' \<equiv> map (tsubst \<rho>) Us"
  defines "fs \<equiv> map (\<lambda>(F, T). Free F T) (zip xs Us')"
  assumes l: "length xs = length Us" and d: "distinct xs"
  shows "prf_fnames (prf_ap \<rho> \<sigma> (lift_prf inc Us lev q)) \<inter> set xs = {} \<Longrightarrow> 0 \<le> lev \<Longrightarrow>
    prf_fsubst (pvar xs Us' lev) (prf_ap (tinc inc \<rho>) (lsubst inc \<rho> Us \<sigma> fs) q) = prf_ap \<rho> \<sigma> (lift_prf inc Us lev q)"
proof (induction q arbitrary: lev)
  case (Abst a T q)
  have "prf_fsubst (\<lambda>x U. lift (pvar xs Us' lev x U) 0) = prf_fsubst (pvar xs Us' (lev + 1))"
    using lift_pvar[OF Abst.prems(2)] by presburger
  with Abst show ?case by (cases T) (simp_all add: prf_ap_def tsubst_incr_tvar)
next
  case (AbsP a t q)
  then show ?case
    by (cases t) (simp_all add: prf_ap_def Int_Un_distrib2 fsubst_ap_incr_idx[where \<rho>=\<rho> and Us=Us, OF l d, folded Us'_def, folded fs_def])
next
  case (PAppt q t)
  then show ?case
    by (cases t) (simp_all add: prf_ap_def Int_Un_distrib2 fsubst_ap_incr_idx[where \<rho>=\<rho> and Us=Us, OF l d, folded Us'_def, folded fs_def])
next
  case (PAppp q1 q2)
  then show ?case by (simp add: prf_ap_def Int_Un_distrib2)
next
  case (PThm hb)
  then show ?case by (cases hb) (simp add: prf_ap_def tsubst_incr_tvar option.map_comp comp_def)
qed (simp_all add: prf_ap_def tsubst_incr_tvar option.map_comp comp_def)

end


subsection \<open>The lifted proof of the rule\<close>

context prf_sig
begin

text \<open>
  Inside the parameters \<open>ptys p\<close> of the subgoal, the lifted proof of a valid rule proves the
  lifted rule, for every instance that solves the lifted flex-flex pairs:
\<close>

lemma prf_ok_lift_prf:
  assumes pf: "prf_valid ax H tps pf P"
    and Hf: "finite H"
    and tps: "\<And>t u. (t, u) \<in> set tps \<Longrightarrow> closed t \<and> closed u \<and> (\<exists>T. \<forall>e. e \<turnstile> t : T \<and> e \<turnstile> u : T)"
    and Ts: "\<forall>T\<in>set (ptys p). cert_typ alg ar T"
    and \<rho>: "cinst \<rho>" and \<sigma>: "gsubst \<sigma>"
    and sol: "\<And>t u. (t, u) \<in> set tps \<Longrightarrow>
      ap \<rho> \<sigma> (abs_pre p (incr_idx (ptys p) inc 0 t)) \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma> (abs_pre p (incr_idx (ptys p) inc 0 u))"
  shows "prf_ok ax H (pushes e (map (tsubst \<rho>) (ptys p))) Hs (prf_ap \<rho> \<sigma> (lift_prf inc (ptys p) 0 pf))
    (ap \<rho> \<sigma> (incr_idx (ptys p) inc 0 P))"
proof -
  define Us where "Us = ptys p"
  define Us' where "Us' = map (tsubst \<rho>) Us"
  define N where "N = (\<Union>h\<in>H. fnames h) \<union> (\<Union>A\<in>prf_atoms pf. fnames (close A)) \<union>
    prf_fnames (prf_ap \<rho> \<sigma> (lift_prf inc Us 0 pf)) \<union> fnames (ap \<rho> \<sigma> (incr_idx Us inc 0 P))"
  have "finite N" using Hf by (simp add: N_def)
  then obtain xs where xs: "length xs = length Us" "distinct xs" "set xs \<inter> N = {}"
    by (rule fresh_name_list)
  define Fs where "Fs = zip xs Us'"
  define fs where "fs = map (\<lambda>(F, T). Free F T) Fs"
  define \<rho>0 where "\<rho>0 = tinc inc \<rho>"
  define \<sigma>0 where "\<sigma>0 = lsubst inc \<rho> Us \<sigma> fs"
  have sF: "map snd Fs = map (tsubst \<rho>) (ptys p)" using xs(1) by (simp add: Fs_def Us'_def Us_def)
  have cF: "\<forall>(F, T)\<in>set Fs. cert_typ alg ar T"
    using Ts cinstD(2)[OF \<rho>] by (auto simp: Fs_def Us'_def Us_def cert_typ_tsubst dest!: set_zip_rightD)
  have tfs: "e \<tturnstile> fs : map (tsubst \<rho>) Us" for e using typings_Frees[OF cF] sF by (simp add: fs_def Us_def)
  have \<rho>0: "cinst \<rho>0" by (simp add: \<rho>0_def cinst_tinc[OF \<rho>])
  have \<sigma>0: "gsubst \<sigma>0" unfolding \<sigma>0_def
    by (rule gsubst_lsubst[OF \<sigma> cinstD(2)[OF \<rho>] Ts[folded Us_def] _ tfs]) (simp add: fs_def closed_Frees)
  have sol0: "ap \<rho>0 \<sigma>0 t \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho>0 \<sigma>0 u" if tu: "(t, u) \<in> set tps" for t u
  proof -
    obtain T where c: "closed t" "closed u" "\<And>e. e \<turnstile> t : T" "\<And>e. e \<turnstile> u : T" using tps[OF tu] by blast
    note cv = sol[OF tu]
    have bt: "ap \<rho> \<sigma> (abs_pre p (incr_idx (ptys p) inc 0 X)) \<degree>\<degree> fs \<rightarrow>\<^sub>\<beta>\<^sup>* ap \<rho>0 \<sigma>0 X \<and>
        wt (ap \<rho> \<sigma> (abs_pre p (incr_idx (ptys p) inc 0 X)) \<degree>\<degree> fs)"
      if "closed X" "e \<turnstile> X : U" for X e U
      unfolding \<rho>0_def \<sigma>0_def fs_def Us_def
      using lift_beta[OF \<sigma> cinstD(2)[OF \<rho>] Ts sF cF that] by blast
    have 1: "ap \<rho> \<sigma> (abs_pre p (incr_idx (ptys p) inc 0 t)) \<degree>\<degree> fs \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho>0 \<sigma>0 t"
      using bt[OF c(1,3)] by (blast intro: conv_beta_eta)
    have 2: "ap \<rho> \<sigma> (abs_pre p (incr_idx (ptys p) inc 0 u)) \<degree>\<degree> fs \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho>0 \<sigma>0 u"
      using bt[OF c(2,4)] by (blast intro: conv_beta_eta)
    have 3: "ap \<rho> \<sigma> (abs_pre p (incr_idx (ptys p) inc 0 t)) \<degree>\<degree> fs \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma> (abs_pre p (incr_idx (ptys p) inc 0 u)) \<degree>\<degree> fs"
      by (rule conv_apps) (use bt[OF c(1,3)] bt[OF c(2,4)] cv in \<open>simp_all add: list.rel_refl\<close>)
    show ?thesis using conv_trans[OF conv_trans[OF conv_sym[OF 1] 3] 2] .
  qed
  let ?e = "pushes e Us'"
  have pr0: "prf_ok ax H ?e [] (prf_ap \<rho>0 \<sigma>0 pf) (ap \<rho>0 \<sigma>0 P)" by (rule prf_validD[OF pf \<rho>0 \<sigma>0 sol0])
  have "prf_ok ax H ?e (map (fsubst (pvar xs Us' 0)) []) (prf_fsubst (pvar xs Us' 0) (prf_ap \<rho>0 \<sigma>0 pf))
      (fsubst (pvar xs Us' 0) (ap \<rho>0 \<sigma>0 P))"
  proof (rule prf_ok_fsubst[where N = "set xs"])
    show "fnames h \<inter> set xs = {}" if "h \<in> H" for h using that xs(3) by (auto simp: N_def)
    show "prf_ok ax H ?e [] (prf_ap \<rho>0 \<sigma>0 pf) (ap \<rho>0 \<sigma>0 P)" by (rule pr0)
    show "?e \<turnstile> pvar xs Us' 0 x U : U" if "cert_typ alg ar U" for x U
      by (rule typing_pvar) (use xs that in \<open>simp_all add: Us'_def\<close>)
    show "pvar xs Us' 0 x U = Free x U" if "x \<notin> set xs" for x U using that by (rule pvar_notin)
    show "\<forall>A\<in>prf_atoms (prf_ap \<rho>0 \<sigma>0 pf). fnames (close A) \<inter> set xs = {}"
      using xs(3) by (auto simp: N_def prf_ap_def)
  qed
  moreover have "prf_fsubst (pvar xs Us' 0) (prf_ap \<rho>0 \<sigma>0 pf) = prf_ap \<rho> \<sigma> (lift_prf inc Us 0 pf)"
    unfolding \<rho>0_def \<sigma>0_def fs_def Fs_def Us'_def
    by (rule prf_fsubst_prf_ap_lift_prf[OF xs(1,2)]) (use xs(3) in \<open>auto simp: N_def\<close>)
  moreover have "fsubst (pvar xs Us' 0) (ap \<rho>0 \<sigma>0 P) = ap \<rho> \<sigma> (incr_idx Us inc 0 P)"
    unfolding \<rho>0_def \<sigma>0_def fs_def Fs_def Us'_def
    by (rule fsubst_ap_incr_idx[OF xs(1,2)]) (use xs(3) in \<open>auto simp: N_def\<close>)
  ultimately show ?thesis using prf_ok_append[of ax H ?e "[]" _ _ Hs] by (simp add: Us'_def Us_def)
qed

end


subsection \<open>The proof of the lifted rule\<close>

text \<open>
  The lifted proof with annotations \<open>fP\<close> of the lifted premises, \<open>fA\<close> of the assumptions and
  \<open>fT\<close> of the parameters of the subgoal: none in \<open>Proofterm.lift_proof\<close>, the propositions
  and types themselves in \<open>ZTerm.lift_proof\<close>.
\<close>

fun alift_prems :: "(pterm \<Rightarrow> pterm option) \<Rightarrow> (ptyp \<Rightarrow> ptyp option) \<Rightarrow> integer \<Rightarrow> integer \<Rightarrow> prf \<Rightarrow>
    ptyp list \<Rightarrow> bool list \<Rightarrow> integer \<Rightarrow> integer \<Rightarrow> pterm \<Rightarrow> prf" where
  "alift_prems fA fT inc k prf Ts bs i j (Const c U $ A $ B) =
    (if c = STR ''Pure.imp'' then AbsP (STR ''H'') (fA A) (alift_prems fA fT inc k prf Ts (True # bs) (i + 1) j B)
     else proof_combP (lift_prf inc (rev Ts) 0 prf)
       (map (\<lambda>k. snd (snd (foldr mk_app bs (i - 1, j - 1, PBound k)))) (downto (i + k - 1) i)))"
| "alift_prems fA fT inc k prf Ts bs i j (Const c U $ Abs a T t) =
    (if c = STR ''Pure.all'' then Abst a (fT T) (alift_prems fA fT inc k prf (T # Ts) (False # bs) i (j + 1) t)
     else proof_combP (lift_prf inc (rev Ts) 0 prf)
       (map (\<lambda>k. snd (snd (foldr mk_app bs (i - 1, j - 1, PBound k)))) (downto (i + k - 1) i)))"
| "alift_prems fA fT inc k prf Ts bs i j _ =
    proof_combP (lift_prf inc (rev Ts) 0 prf)
      (map (\<lambda>k. snd (snd (foldr mk_app bs (i - 1, j - 1, PBound k)))) (downto (i + k - 1) i))"

definition alift_proof :: "(pterm \<Rightarrow> pterm option) \<Rightarrow> (pterm \<Rightarrow> pterm option) \<Rightarrow> (ptyp \<Rightarrow> ptyp option) \<Rightarrow>
    pterm \<Rightarrow> integer \<Rightarrow> pterm list \<Rightarrow> prf \<Rightarrow> prf" where
  "alift_proof fP fA fT gprop inc prems prf = foldr (\<lambda>A p. AbsP (STR ''H'') (fP A) p) prems
    (alift_prems fA fT inc (integer_of_nat (length prems)) prf [] [] 0 0 gprop)"

lemma lift_prems_alift:
  "lift_prems inc k pf Ts bs i j G = alift_prems (\<lambda>_. None) (\<lambda>_. None) inc k pf Ts bs i j G"
  by (induction inc k pf Ts bs i j G rule: lift_prems.induct) simp_all

lemma lift_proof_alift:
  "lift_proof gprop inc prems prf = alift_proof (\<lambda>_. None) (\<lambda>_. None) (\<lambda>_. None) gprop inc prems prf"
  by (simp add: lift_proof_def alift_proof_def mk_AbsP_def lift_prems_alift)

lemma lift_all_aux_imp: "lift_all_aux inc Ts (implies $ A $ X) t = implies $ A $ lift_all_aux inc Ts X t"
  and alift_prems_imp:
    "alift_prems fA fT inc k prf Ts bs i j (implies $ A $ X) =
      AbsP (STR ''H'') (fA A) (alift_prems fA fT inc k prf Ts (True # bs) (i + 1) j X)"
  and lift_all_aux_all: "lift_all_aux inc Ts (all_const T $ Abs a T X) t = all_const T $ Abs a T (lift_all_aux inc (T # Ts) X t)"
  and alift_prems_all:
    "alift_prems fA fT inc k prf Ts bs i j (all_const T $ Abs a T X) =
      Abst a (fT T) (alift_prems fA fT inc k prf (T # Ts) (False # bs) i (j + 1) X)"
  by (simp_all add: implies_def all_const_def)

lemma alift_prems_atomic:
  "atomic G \<Longrightarrow> alift_prems fA fT inc k prf Ts bs i j G = proof_combP (lift_prf inc (rev Ts) 0 prf)
    (map (spine bs i j) (downto (i + k - 1) i))"
  by (cases "(fA, fT, inc, k, prf, Ts, bs, i, j, G)" rule: alift_prems.cases) (auto simp: atomic_def spine_def[abs_def])

lemma spine_Nil: "spine [] i j c = PBound c"
  by (simp add: spine_def)

context prf_sig
begin

lemma pushes_snoc: "pushes e (Ts @ [T]) = (pushes e Ts)\<langle>0:T\<rangle>"
  by (induction Ts arbitrary: e) (simp_all add: pushes.simps)

lemma incr_idx_list_implies:
  "incr_idx Us inc lev (list_implies As B) = list_implies (map (incr_idx Us inc lev) As) (incr_idx Us inc lev B)"
  by (induction As) (simp_all add: implies_def imp_type_def incr_tvar_propT)

lemma typing_ap_pushes:
  assumes t: "\<And>e'. pushes e' Us \<turnstile> t : T" and n: "\<not> loose_bvar t (ilength Us)"
    and \<rho>: "cinst \<rho>" and \<sigma>: "gsubst \<sigma>"
  shows "pushes e (map (tsubst \<rho>) Us) \<turnstile> ap \<rho> \<sigma> t : tsubst \<rho> T"
proof -
  let ?e0 = "\<lambda>_::integer. propT"
  have ty: "ienv \<rho> (pushes ?e0 Us) \<turnstile> ap \<rho> \<sigma> t : tsubst \<rho> T"
    by (rule typing_ap_inst[OF t cinstD(2)[OF \<rho>] gsubstD(1)[OF \<sigma>]])
  have il: "ilength (map (tsubst \<rho>) Us) = ilength Us" by (simp add: ilength_eq)
  show ?thesis
  proof (rule typing_env_cong[OF ty])
    fix i :: integer assume i: "0 \<le> i" "loose_bvar1 (ap \<rho> \<sigma> t) i"
    have "\<not> loose_bvar (ap \<rho> \<sigma> t) (ilength Us)" using n \<sigma> ilength_nonneg[of Us] by simp
    then have lt: "i < ilength Us" using loose_bvar1_less i(2) by blast
    then have "nat_of_integer i < length Us" using i(1) by (simp add: nat_of_integer_less_ilength)
    then show "pushes e (map (tsubst \<rho>) Us) i = tsubst \<rho> (pushes ?e0 Us i)"
      using pushes_nth[OF i(1), of e "map (tsubst \<rho>) Us"] pushes_nth[OF i(1), of ?e0 Us] lt il
      by (simp add: rev_map)
  qed
qed

lemma prf_ok_lift_prems:
  assumes H: "\<And>h. h \<in> H \<Longrightarrow> closed h" and \<rho>: "cinst \<rho>" and \<sigma>: "gsubst \<sigma>" and G0: "atomic G0"
    and k: "k = integer_of_nat (length As)"
    and fA: "\<And>A. fA A = None \<or> fA A = Some A" and fT: "\<And>T. fT T = None \<or> fT T = Some T"
  shows "\<forall>it\<in>set p. litem_ok it \<Longrightarrow> (\<And>e'. pushes e' (rev Ts) \<turnstile> lift_pre p G0 : propT) \<Longrightarrow>
    \<not> loose_bvar (lift_pre p G0) (ilength Ts) \<Longrightarrow>
    i = integer_of_nat (length (filter id bs)) \<Longrightarrow> length Ts = length (filter Not bs) \<Longrightarrow>
    j = integer_of_nat (length Ts) \<Longrightarrow>
    (\<forall>m<length As. prf_ok ax H (pushes e (map (tsubst \<rho>) (rev Ts))) Hs (spine bs i j (i + k - 1 - integer_of_nat m))
      (ap \<rho> \<sigma> (lift_all_aux inc Ts (lift_pre p G0) (As ! m)))) \<Longrightarrow>
    (\<And>Hs'. prf_ok ax H (pushes e (map (tsubst \<rho>) (rev Ts @ ptys p))) Hs'
      (prf_ap \<rho> \<sigma> (lift_prf inc (rev Ts @ ptys p) 0 pf))
      (ap \<rho> \<sigma> (incr_idx (rev Ts @ ptys p) inc 0 (list_implies As B)))) \<Longrightarrow>
    prf_ok ax H (pushes e (map (tsubst \<rho>) (rev Ts))) Hs
      (prf_ap \<rho> \<sigma> (alift_prems fA fT inc k pf Ts bs i j (lift_pre p G0))) (ap \<rho> \<sigma> (lift_all_aux inc Ts (lift_pre p G0) B))"
proof (induction p arbitrary: Ts bs i j Hs)
  case Nil
  let ?E = "pushes e (map (tsubst \<rho>) (rev Ts))"
  let ?f = "\<lambda>X. ap \<rho> \<sigma> (incr_idx (rev Ts) inc 0 X)"
  have "downto (i + k - 1) i = map (\<lambda>m. i + k - 1 - integer_of_nat m) [0..<length As]"
    by (simp add: downto_map k)
  then have "map (prf_ap \<rho> \<sigma>) (map (spine bs i j) (downto (i + k - 1) i)) =
      map (\<lambda>m. spine bs i j (i + k - 1 - integer_of_nat m)) [0..<length As]"
    by (simp add: prf_ap_spine)
  moreover have "list_all2 (prf_ok ax H ?E Hs) (map (\<lambda>m. spine bs i j (i + k - 1 - integer_of_nat m)) [0..<length As])
      (map ?f As)"
    using Nil.prems(7) G0 by (auto simp: list_all2_conv_all_nth lift_all_aux_atomic incr_indexes_idx)
  moreover have "prf_ok ax H ?E Hs (prf_ap \<rho> \<sigma> (lift_prf inc (rev Ts) 0 pf)) (list_implies (map ?f As) (?f B))"
    using Nil.prems(8)[of Hs] by (simp add: incr_idx_list_implies ap_list_implies comp_def)
  ultimately show ?case using G0
    by (auto simp: alift_prems_atomic lift_all_aux_atomic incr_indexes_idx prf_ap_proof_combP
      intro: prf_ok_proof_combP)
next
  case (Cons it p)
  let ?E = "pushes e (map (tsubst \<rho>) (rev Ts))"
  have ok: "litem_ok it" "\<forall>it\<in>set p. litem_ok it" using Cons.prems(1) by simp_all
  show ?case
  proof (cases it)
    case (LImp c A)
    note eqs = typing_lift_pre_imp[OF ok(1) Cons.prems(2) LImp]
    from ok(1) LImp obtain U where c: "c = Const STR ''Pure.imp'' U" by auto
    have ci: "c = implies" using eqs(1) LImp c by (simp add: implies_def)
    have nl: "\<not> loose_bvar A (ilength Ts)" "\<not> loose_bvar (lift_pre p G0) (ilength Ts)"
      using Cons.prems(3) LImp by simp_all
    have tA: "?E \<turnstile> ap \<rho> \<sigma> A : propT"
      using typing_ap_pushes[where Us = "rev Ts", OF typing_lift_pre_imp(2)[OF ok(1) Cons.prems(2) LImp] _ \<rho> \<sigma>] nl(1)
      by (simp add: ilength_eq)
    let ?A = "ap \<rho> \<sigma> A"
    have "prf_ok ax H ?E (?A # Hs) (prf_ap \<rho> \<sigma> (alift_prems fA fT inc k pf Ts (True # bs) (i + 1) j (lift_pre p G0)))
        (ap \<rho> \<sigma> (lift_all_aux inc Ts (lift_pre p G0) B))"
    proof (rule Cons.IH[OF ok(2) eqs(3) nl(2)])
      show "\<forall>m<length As. prf_ok ax H ?E (?A # Hs) (spine (True # bs) (i + 1) j (i + 1 + k - 1 - integer_of_nat m))
          (ap \<rho> \<sigma> (lift_all_aux inc Ts (lift_pre p G0) (As ! m)))"
      proof (intro allI impI)
        fix m assume m: "m < length As"
        have "integer_of_nat (Suc m) \<le> k" using m k by (simp add: less_eq_integer.rep_eq integer_of_nat.rep_eq)
        then have c0: "0 \<le> i + k - 1 - integer_of_nat m"
          using Cons.prems(4) integer_of_nat_nonneg[of "length (filter id bs)"] by (simp only: integer_of_nat_Suc; simp)
        have "prf_ok ax H ?E (take (nat_of_integer 0) Hs @ ?A # drop (nat_of_integer 0) Hs)
            (incr_pbv 0 (spine bs i j (i + k - 1 - integer_of_nat m))) (ap \<rho> \<sigma> (lift_all_aux inc Ts (lift_pre (it # p) G0) (As ! m)))"
          using Cons.prems(7) m by (intro prf_ok_incr_pbv) simp_all
        then have "prf_ok ax H ?E (?A # Hs) (incr_pbv 0 (spine bs i j (i + k - 1 - integer_of_nat m)))
            (implies $ ?A $ ap \<rho> \<sigma> (lift_all_aux inc Ts (lift_pre p G0) (As ! m)))"
          by (simp add: eqs(1) lift_all_aux_imp)
        moreover have "prf_ok ax H ?E (?A # Hs) (PBound 0) ?A"
          using prf_ok.PBound[of 0 "?A # Hs" ?E] tA by simp
        ultimately have "prf_ok ax H ?E (?A # Hs) (PAppp (incr_pbv 0 (spine bs i j (i + k - 1 - integer_of_nat m))) (PBound 0))
            (ap \<rho> \<sigma> (lift_all_aux inc Ts (lift_pre p G0) (As ! m)))" by (rule prf_ok.PAppp)
        then show "prf_ok ax H ?E (?A # Hs) (spine (True # bs) (i + 1) j (i + 1 + k - 1 - integer_of_nat m))
            (ap \<rho> \<sigma> (lift_all_aux inc Ts (lift_pre p G0) (As ! m)))"
          using spine_True[OF Cons.prems(4) c0, of j] by (simp add: algebra_simps)
      qed
      show "prf_ok ax H (pushes e (map (tsubst \<rho>) (rev Ts @ ptys p))) Hs'
          (prf_ap \<rho> \<sigma> (lift_prf inc (rev Ts @ ptys p) 0 pf)) (ap \<rho> \<sigma> (incr_idx (rev Ts @ ptys p) inc 0 (list_implies As B)))"
        for Hs' using Cons.prems(8)[of Hs'] LImp by simp
    qed (use Cons.prems(4-6) in \<open>simp_all add: integer_of_nat_Suc\<close>)
    moreover have "ann_ok (map_option (ap \<rho> \<sigma>) (fA A)) ?A" using fA[of A] by auto
    ultimately have "prf_ok ax H ?E Hs (AbsP (STR ''H'') (map_option (ap \<rho> \<sigma>) (fA A))
        (prf_ap \<rho> \<sigma> (alift_prems fA fT inc k pf Ts (True # bs) (i + 1) j (lift_pre p G0))))
        (implies $ ?A $ ap \<rho> \<sigma> (lift_all_aux inc Ts (lift_pre p G0) B))"
      using tA by (auto intro!: prf_ok.AbsP)
    then show ?thesis by (simp add: eqs(1) lift_all_aux_imp alift_prems_imp prf_ap_def)
  next
    case (LAll c a T)
    note eqs = typing_lift_pre_all[OF ok(1) Cons.prems(2) LAll]
    from ok(1) LAll obtain U where c: "c = Const STR ''Pure.all'' U" by auto
    have ca: "c = all_const T" using eqs(1) LAll c by (simp add: all_const_def)
    have cT: "cert_typ alg ar T"
      using typing_lift_pre[of "[it]" "pushes (\<lambda>_. propT) (rev Ts)" "lift_pre p G0"] ok(1) Cons.prems(2) LAll
      by simp
    let ?T = "tsubst \<rho> T"
    have E: "?E\<langle>0:?T\<rangle> = pushes e (map (tsubst \<rho>) (rev (T # Ts)))" by (simp add: pushes_snoc)
    have nl: "\<not> loose_bvar (lift_pre p G0) (ilength (T # Ts))"
      using Cons.prems(3) LAll by (simp add: algebra_simps)
    have ty: "pushes e' (rev (T # Ts)) \<turnstile> lift_pre p G0 : propT" for e'
      using typing_lift_pre_all(2)[OF ok(1) Cons.prems(2) LAll] by (simp add: pushes_snoc)
    have "prf_ok ax H (?E\<langle>0:?T\<rangle>) (map (incr_bv 1 0) Hs)
        (prf_ap \<rho> \<sigma> (alift_prems fA fT inc k pf (T # Ts) (False # bs) i (j + 1) (lift_pre p G0)))
        (ap \<rho> \<sigma> (lift_all_aux inc (T # Ts) (lift_pre p G0) B))"
      unfolding E
    proof (rule Cons.IH[OF ok(2) ty nl])
      show "\<forall>m<length As. prf_ok ax H (pushes e (map (tsubst \<rho>) (rev (T # Ts)))) (map (incr_bv 1 0) Hs)
          (spine (False # bs) i (j + 1) (i + k - 1 - integer_of_nat m))
          (ap \<rho> \<sigma> (lift_all_aux inc (T # Ts) (lift_pre p G0) (As ! m)))"
      proof (intro allI impI)
        fix m assume m: "m < length As"
        let ?X = "ap \<rho> \<sigma> (lift_all_aux inc (T # Ts) (lift_pre p G0) (As ! m))"
        let ?s = "spine bs i j (i + k - 1 - integer_of_nat m)"
        have sm: "prf_ok ax H ?E Hs ?s (all_const ?T $ Abs a ?T ?X)"
          using Cons.prems(7) m by (simp add: eqs(1) lift_all_aux_all)
        have tX: "?E\<langle>0:?T\<rangle> \<turnstile> ?X : propT"
          using prf_ok_typing[OF sm] by (auto simp: all_const_def)
        have "prf_ok ax H (?E\<langle>0:?T\<rangle>) (map (\<lambda>h. lift h 0) Hs) (incr_tbv 0 ?s) (lift (all_const ?T $ Abs a ?T ?X) 0)"
          by (rule prf_ok_incr_tbv[OF H sm order.refl])
        then have "prf_ok ax H (?E\<langle>0:?T\<rangle>) (map (incr_bv 1 0) Hs) (incr_tbv 0 ?s) (all_const ?T $ Abs a ?T (lift ?X 1))"
          by simp
        then have pa: "prf_ok ax H (?E\<langle>0:?T\<rangle>) (map (incr_bv 1 0) Hs) (PAppt (incr_tbv 0 ?s) (Some (Bound 0)))
            (Abs a ?T (lift ?X 1) $ Bound 0)"
          by (rule prf_ok.PAppt) auto
        have "Abs a ?T (lift ?X 1) $ Bound 0 \<rightarrow>\<^sub>\<beta>\<^sup>* ?X"
          using beta.beta[of a ?T "lift ?X 1" "Bound 0"] subst_lift_Bound[of 0 ?X] by simp
        then have cv: "Abs a ?T (lift ?X 1) $ Bound 0 \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ?X"
          using prf_ok_typing[OF pa] by (intro conv_beta_eta) (auto simp: wt_def)
        have "prf_ok ax H (?E\<langle>0:?T\<rangle>) (map (incr_bv 1 0) Hs) (PAppt (incr_tbv 0 ?s) (Some (Bound 0))) ?X"
          by (rule prf_ok.conv[OF pa cv tX])
        then show "prf_ok ax H (pushes e (map (tsubst \<rho>) (rev (T # Ts)))) (map (incr_bv 1 0) Hs)
            (spine (False # bs) i (j + 1) (i + k - 1 - integer_of_nat m)) ?X"
          using spine_False[of j bs i] Cons.prems(5,6) E by simp
      qed
      show "prf_ok ax H (pushes e (map (tsubst \<rho>) (rev (T # Ts) @ ptys p))) Hs'
          (prf_ap \<rho> \<sigma> (lift_prf inc (rev (T # Ts) @ ptys p) 0 pf))
          (ap \<rho> \<sigma> (incr_idx (rev (T # Ts) @ ptys p) inc 0 (list_implies As B)))"
        for Hs' using Cons.prems(8)[of Hs'] LAll by simp
    qed (use Cons.prems(4-6) in \<open>simp_all add: integer_of_nat_Suc\<close>)
    moreover have "tann_ok (map_option (tsubst \<rho>) (fT T)) ?T" using fT[of T] by auto
    ultimately have "prf_ok ax H ?E Hs (Abst a (map_option (tsubst \<rho>) (fT T))
        (prf_ap \<rho> \<sigma> (alift_prems fA fT inc k pf (T # Ts) (False # bs) i (j + 1) (lift_pre p G0))))
        (all_const ?T $ Abs a ?T (ap \<rho> \<sigma> (lift_all_aux inc (T # Ts) (lift_pre p G0) B)))"
      using cT cert_typ_tsubst[OF cT cinstD(2)[OF \<rho>]] by (auto intro!: prf_ok.Abst)
    then show ?thesis by (simp add: eqs(1) lift_all_aux_all alift_prems_all prf_ap_def)
  qed
qed

end


subsection \<open>Validity of the lifted proof\<close>

context prf_sig
begin

lemma typing_ap_wtp: "wtp X \<Longrightarrow> cinst \<rho> \<Longrightarrow> gsubst \<sigma> \<Longrightarrow> e \<turnstile> ap \<rho> \<sigma> X : propT"
proof -
  assume X: "wtp X" and \<rho>: "cinst \<rho>" and \<sigma>: "gsubst \<sigma>"
  have "ienv \<rho> (\<lambda>_. propT) \<turnstile> ap \<rho> \<sigma> X : tsubst \<rho> propT"
    by (rule typing_ap_inst[OF wtpD(2)[OF X] cinstD(2)[OF \<rho>] gsubstD(1)[OF \<sigma>]])
  moreover have "closed (ap \<rho> \<sigma> X)" using wtpD(1)[OF X] \<sigma> by (simp add: closed_def)
  ultimately show ?thesis by (auto simp: propT_def intro: typing_closed)
qed

lemma prf_ap_foldr_AbsP:
  "prf_ap \<rho> \<sigma> (foldr (\<lambda>A p. AbsP a (f A) p) xs q) =
    foldr (\<lambda>t p. AbsP a t p) (map (\<lambda>A. map_option (ap \<rho> \<sigma>) (f A)) xs) (prf_ap \<rho> \<sigma> q)"
  by (induction xs) (simp_all add: prf_ap_def)

theorem prf_valid_alift_proof:
  assumes pf: "prf_valid ax (set hs) (th_tpairs rule) pf (th_prop rule)"
    and w: "wt_thm rmax hs (th_tpairs rule) (th_prop rule)" and G: "wtp G"
    and fP: "\<And>A. fP A = None \<or> fP A = Some A"
    and fA: "\<And>A. fA A = None \<or> fA A = Some A" and fT: "\<And>T. fT T = None \<or> fT T = Some T"
  shows "prf_valid ax (set hs) (th_tpairs (lift_rule G gmax rule))
    (alift_proof fP fA fT G (gmax + 1) (map (lift_all (gmax + 1) G) (strip_imp_prems (th_prop rule))) pf)
    (th_prop (lift_rule G gmax rule))"
proof (rule prf_validI)
  fix e \<rho> \<sigma> assume \<rho>: "cinst \<rho>" and \<sigma>: "gsubst \<sigma>"
    and sol: "\<And>t u. (t, u) \<in> set (th_tpairs (lift_rule G gmax rule)) \<Longrightarrow> ap \<rho> \<sigma> t \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma> u"
  obtain p G0 where sp: "lsplit G = (p, G0)" by (cases "lsplit G")
  have pok: "G = lift_pre p G0" and ok: "\<forall>it\<in>set p. litem_ok it" and G0: "atomic G0"
    using lsplit_ok[OF sp] by simp_all
  define inc where "inc = gmax + 1"
  define P where "P = th_prop rule"
  define tps where "tps = th_tpairs rule"
  define As where "As = strip_imp_prems P"
  define B where "B = strip_imp_concl P"
  have wP: "wtp P" using w by (simp add: wt_thm_def P_def)
  have PAB: "P = list_implies As B" unfolding As_def B_def by (rule list_implies_strip_imp[OF wtpD(2)[OF wP]])
  have wAB: "(\<forall>A\<in>set As. wtp A) \<and> wtp B" using wtp_list_implies[of As As B B] wP PAB by simp
  have hs: "closed h" if "h \<in> set hs" for h using w that by (auto simp: wt_thm_def dest: wtpD(1))
  have tps0: "closed t \<and> closed u \<and> (\<exists>T. \<forall>e. e \<turnstile> t : T \<and> e \<turnstile> u : T)" if "(t, u) \<in> set tps" for t u
    using w that by (fastforce simp: wt_thm_def tps_def)
  have la: "lift_all inc G X = lift_pre p (incr_idx (ptys p) inc 0 X)" for X
    by (simp add: lift_all_lsplit[OF sp] incr_indexes_idx)
  have lT: "th_tpairs (lift_rule G gmax rule) =
      map (\<lambda>(t, u). (abs_pre p (incr_idx (ptys p) inc 0 t), abs_pre p (incr_idx (ptys p) inc 0 u))) tps"
    by (simp add: lift_rule_def Let_def lift_abs_lsplit[OF sp] incr_indexes_idx inc_def tps_def)
  have lP: "th_prop (lift_rule G gmax rule) = list_implies (map (lift_all inc G) As) (lift_all inc G B)"
    by (simp add: lift_rule_def Let_def inc_def As_def B_def P_def)
  have tG: "e' \<turnstile> lift_pre p G0 : propT" for e' using wtpD(2)[OF G] pok by simp
  have cTs: "\<forall>T\<in>set (ptys p). cert_typ alg ar T" using typing_lift_pre[OF ok tG] by simp
  have leaf: "prf_ok ax (set hs) (pushes e (map (tsubst \<rho>) (ptys p))) Hs'
      (prf_ap \<rho> \<sigma> (lift_prf inc (ptys p) 0 pf)) (ap \<rho> \<sigma> (incr_idx (ptys p) inc 0 P))" for Hs'
  proof (rule prf_ok_lift_prf[OF pf[folded tps_def P_def] _ tps0 cTs \<rho> \<sigma>])
    show "ap \<rho> \<sigma> (abs_pre p (incr_idx (ptys p) inc 0 t)) \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma> (abs_pre p (incr_idx (ptys p) inc 0 u))"
      if "(t, u) \<in> set tps" for t u
      by (rule sol) (use that in \<open>force simp: lT\<close>)
  qed simp_all
  let ?Qs = "map (\<lambda>A. ap \<rho> \<sigma> (lift_all inc G A)) As"
  have wQ: "wtp (lift_all inc G A)" if "A \<in> set As" for A
    unfolding la by (rule wtp_lift_pre_incr[OF sp G]) (use wAB that in auto)
  have tQ: "\<forall>Q\<in>set ?Qs. e \<turnstile> Q : propT" using typing_ap_wtp[OF wQ \<rho> \<sigma>] by auto
  have "prf_ok ax (set hs) (pushes e (map (tsubst \<rho>) (rev []))) (rev ?Qs)
      (prf_ap \<rho> \<sigma> (alift_prems fA fT inc (integer_of_nat (length As)) pf [] [] 0 0 (lift_pre p G0)))
      (ap \<rho> \<sigma> (lift_all_aux inc [] (lift_pre p G0) B))"
  proof (rule prf_ok_lift_prems[OF hs \<rho> \<sigma> G0 refl fA fT ok])
    show "pushes e' (rev []) \<turnstile> lift_pre p G0 : propT" for e' using tG by simp
    show "\<not> loose_bvar (lift_pre p G0) (ilength [])" using wtpD(1)[OF G] pok by (simp add: closed_def)
    show "\<forall>m<length As. prf_ok ax (set hs) (pushes e (map (tsubst \<rho>) (rev []))) (rev ?Qs)
        (spine [] 0 0 (0 + integer_of_nat (length As) - 1 - integer_of_nat m))
        (ap \<rho> \<sigma> (lift_all_aux inc [] (lift_pre p G0) (As ! m)))"
    proof (intro allI impI)
      fix m assume m: "m < length As"
      have c: "integer_of_nat (length As) - 1 - integer_of_nat m = integer_of_nat (length As - Suc m)"
        using m by (simp add: integer_eq_iff integer_of_nat.rep_eq of_nat_diff)
      have "rev ?Qs ! (length As - Suc m) = ap \<rho> \<sigma> (lift_all inc G (As ! m))" using m by (simp add: rev_nth)
      moreover have "e \<turnstile> ap \<rho> \<sigma> (lift_all inc G (As ! m)) : propT" using tQ m by simp
      ultimately show "prf_ok ax (set hs) (pushes e (map (tsubst \<rho>) (rev []))) (rev ?Qs)
          (spine [] 0 0 (0 + integer_of_nat (length As) - 1 - integer_of_nat m))
          (ap \<rho> \<sigma> (lift_all_aux inc [] (lift_pre p G0) (As ! m)))"
        using prf_ok.PBound[of "integer_of_nat (length As - Suc m)" "rev ?Qs" e] m pok
        by (simp add: spine_Nil c lift_all_def integer_of_nat_nonneg)
    qed
    show "prf_ok ax (set hs) (pushes e (map (tsubst \<rho>) (rev [] @ ptys p))) Hs'
        (prf_ap \<rho> \<sigma> (lift_prf inc (rev [] @ ptys p) 0 pf))
        (ap \<rho> \<sigma> (incr_idx (rev [] @ ptys p) inc 0 (list_implies As B)))" for Hs'
      using leaf[of Hs'] PAB by simp
  qed simp_all
  then have "prf_ok ax (set hs) e (rev ?Qs @ []) (prf_ap \<rho> \<sigma> (alift_prems fA fT inc (integer_of_nat (length As)) pf [] [] 0 0 G))
      (ap \<rho> \<sigma> (lift_all inc G B))"
    using pok by (simp add: lift_all_def)
  let ?prems = "map (lift_all (gmax + 1) G) (strip_imp_prems (th_prop rule))"
  let ?ts = "map (\<lambda>A. map_option (ap \<rho> \<sigma>) (fP A)) ?prems"
  have fa: "ann_ok (map_option (ap \<rho> \<sigma>) (fP A)) (ap \<rho> \<sigma> A)" for A using fP[of A] by auto
  have "list_all2 ann_ok ?ts ?Qs"
    using fa by (auto simp: list_all2_map1 list_all2_map2 inc_def As_def P_def intro!: list.rel_refl_strong)
  note r = prf_ok_foldr_AbsP[OF \<open>prf_ok ax (set hs) e (rev ?Qs @ []) _ _\<close> tQ this]
  have l1: "prf_ap \<rho> \<sigma> (alift_proof fP fA fT G (gmax + 1) ?prems pf) =
      foldr (\<lambda>t p. AbsP (STR ''H'') t p) ?ts (prf_ap \<rho> \<sigma> (alift_prems fA fT inc (integer_of_nat (length As)) pf [] [] 0 0 G))"
    by (simp add: alift_proof_def prf_ap_foldr_AbsP inc_def As_def P_def)
  have l3: "ap \<rho> \<sigma> (th_prop (lift_rule G gmax rule)) = list_implies ?Qs (ap \<rho> \<sigma> (lift_all inc G B))"
    by (simp add: lP ap_list_implies comp_def)
  show "prf_ok ax (set hs) e [] (prf_ap \<rho> \<sigma> (alift_proof fP fA fT G (gmax + 1) ?prems pf))
      (ap \<rho> \<sigma> (th_prop (lift_rule G gmax rule)))"
    unfolding l1 l3 by (rule r)
qed

corollary prf_valid_lift_proof:
  assumes "prf_valid ax (set hs) (th_tpairs rule) pf (th_prop rule)"
    and "wt_thm rmax hs (th_tpairs rule) (th_prop rule)" and "wtp G"
  shows "prf_valid ax (set hs) (th_tpairs (lift_rule G gmax rule))
    (lift_proof G (gmax + 1) (map (lift_all (gmax + 1) G) (strip_imp_prems (th_prop rule))) pf)
    (th_prop (lift_rule G gmax rule))"
  unfolding lift_proof_alift by (rule prf_valid_alift_proof[OF assms]) simp_all

end

end

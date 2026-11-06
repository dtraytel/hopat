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

lemma ueq_lift:
  assumes st: "s \<approx> t" and k: "0 \<le> k"
  shows "lift s k \<approx> lift t k"
proof -
  have "equivclp (sup beta eta) (lift x k) (lift y k)" if "equivclp (sup beta eta) x y" for x y
    using that
  proof (induction rule: equivclp_induct)
    case (step y z)
    have "sup beta eta (lift y k) (lift z k) \<or> sup beta eta (lift z k) (lift y k)"
      using step(2) k by (auto intro: beta_lift eta_lift)
    from equivclp_into_equivclp[OF step(3) this] show ?case .
  qed simp
  from this[OF st] show ?thesis by simp
qed

lemma lift_closed: "closed t \<Longrightarrow> 0 \<le> c \<Longrightarrow> incr_bv n c t = t"
  by (rule incr_bv_no_loose) (use loose_bvar_mono[of t c 0] in \<open>auto simp: closed_def\<close>)

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
  have "lift t c = t" using H[OF Hyp.hyps(1)] Hyp.prems by (rule lift_closed)
  with Hyp lift_type[OF Hyp.hyps(2) Hyp.prems, of U] show ?case by (simp add: prf_ok.Hyp)
next
  case (PAxm A Us' Us e Hs a)
  have "lift (atom_prop A Us) c = atom_prop A Us" using closed_atom_prop PAxm.prems by (rule lift_closed)
  with PAxm lift_type[OF PAxm.hyps(3) PAxm.prems, of U] show ?case by (simp add: prf_ok.PAxm)
next
  case (Oracle A Us' Us e Hs a)
  have "lift (atom_prop A Us) c = atom_prop A Us" using closed_atom_prop Oracle.prems by (rule lift_closed)
  with Oracle lift_type[OF Oracle.hyps(3) Oracle.prems, of U] show ?case by (simp add: prf_ok.Oracle)
next
  case (PThm h Us e Hs b)
  have "lift (atom_prop (hd_prop h) Us) c = atom_prop (hd_prop h) Us"
    using closed_atom_prop PThm.prems by (rule lift_closed)
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

lemma combound_apps: "combound c lev n = c \<degree>\<degree> map (\<lambda>i. Bound (lev + integer_of_nat i)) (rev [0..<n])"
proof (induction n arbitrary: lev)
  case (Suc n)
  have "rev [0..<Suc n] = rev (map Suc [0..<n]) @ [0]" by (simp add: upt_conv_Cons map_Suc_upt del: upt_Suc)
  then have "map (\<lambda>i. Bound (lev + integer_of_nat i)) (rev [0..<Suc n]) =
      map (\<lambda>i. Bound (lev + 1 + integer_of_nat i)) (rev [0..<n]) @ [Bound lev]"
    by (simp add: rev_map integer_of_nat_Suc algebra_simps)
  then show ?case using Suc.IH[of "lev + 1"] by simp
qed simp

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

end

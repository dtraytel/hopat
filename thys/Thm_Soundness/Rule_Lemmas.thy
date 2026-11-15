section \<open>Lemmas on the data of the rules\<close>

theory Rule_Lemmas
  imports Varify_Correct Equality_Correct Assumption_Correct Eta_Long_Correct Free_Subst
begin

text \<open>
  Facts on terms and on the models of single rules that the theories on the abstract type of
  theorems use, and that the theories on proofs (session \<open>Thm_Correctness\<close>) use as well.
\<close>

lemma vars_unname [simp]: "vars (unname t) = vars t"
  by (induction t) auto

lemma ttvars_unname [simp]: "ttvars (unname t) = ttvars t"
  by (induction t) auto

lemma permute_data_precise:
  assumes ok: "okT (permute_data j k rl) (th, prems', m)"
  defines "ps \<equiv> strip_imp_prems (th_prop rl)" and "C \<equiv> strip_imp_concl (th_prop rl)"
  assumes P: "th_prop rl = list_implies ps C"
  obtains J M where "j = integer_of_nat J" "m = integer_of_nat M" "J \<le> length ps" "M \<le> length ps - J"
    "prems' = take J ps @ drop M (drop J ps) @ take M (drop J ps)"
    "th = mk_rep (th_maxidx rl) (th_tpairs rl) (list_implies prems' C)"
proof -
  define J where "J = nat_of_integer j"
  have nr: "\<not> (j < 0 \<or> integer_of_nat (length ps) < j)"
    using ok by (auto simp: permute_data_def Let_def raiseW_def ps_def split: if_splits)
  then have jJ: "j = integer_of_nat J" "J \<le> length ps"
    by (simp_all add: J_def integer_eq_iff integer_of_nat.rep_eq nat_of_integer.rep_eq less_integer.rep_eq
      nat_le_iff)
  define nj where "nj = length (drop J ps)"
  define mm where "mm = (if k < 0 then integer_of_nat nj + k else k)"
  have cs: "(m = mm \<and> (mm = 0 \<or> mm = integer_of_nat nj) \<and> prems' = ps \<and>
        th = mk_rep (th_maxidx rl) (th_tpairs rl) (th_prop rl)) \<or>
      (m = mm \<and> 0 < mm \<and> mm < integer_of_nat nj \<and>
        prems' = take J ps @ drop (nat_of_integer mm) (drop J ps) @ take (nat_of_integer mm) (drop J ps) \<and>
        th = mk_rep (th_maxidx rl) (th_tpairs rl) (list_implies prems' C))"
    using ok nr unfolding permute_data_def Let_def
    by (auto simp: returnW_def raiseW_def ps_def C_def J_def nj_def mm_def split: if_splits)
  from cs show thesis
  proof (elim disjE conjE)
    assume m: "m = mm" and "mm = 0" and p': "prems' = ps"
      and th: "th = mk_rep (th_maxidx rl) (th_tpairs rl) (th_prop rl)"
    with P show thesis by (intro that[OF jJ(1), of 0]) (simp_all add: jJ(2))
  next
    assume m: "m = mm" and "mm = integer_of_nat nj" and p': "prems' = ps"
      and th: "th = mk_rep (th_maxidx rl) (th_tpairs rl) (th_prop rl)"
    with P show thesis by (intro that[OF jJ(1), of nj]) (simp_all add: jJ(2) nj_def)
  next
    assume m: "m = mm" and mm: "0 < mm" "mm < integer_of_nat nj"
      and p': "prems' = take J ps @ drop (nat_of_integer mm) (drop J ps) @ take (nat_of_integer mm) (drop J ps)"
      and th: "th = mk_rep (th_maxidx rl) (th_tpairs rl) (list_implies prems' C)"
    have "mm = integer_of_nat (nat_of_integer mm)" "nat_of_integer mm \<le> length ps - J"
      using mm by (simp_all add: integer_eq_iff integer_of_nat.rep_eq nat_of_integer.rep_eq less_integer.rep_eq
        nj_def)
    with m p' th show thesis by (intro that[OF jJ(1), of "nat_of_integer mm"]) (simp_all add: jJ(2))
  qed
qed

lemma rotate_data_precise:
  assumes ok: "okT (rotate_data k i state) (th, Bs, Bi', params, asms, m)"
  obtains tpairs Bi C M where "okT (dest_state state i) (tpairs, Bs, Bi, C)"
    "th = mk_rep (th_maxidx state) tpairs (list_implies (Bs @ [Bi']) C)"
    "params = strip_all_vars Bi" "asms = strip_imp_prems (strip_all_body Bi)"
    "m = integer_of_nat M" "M \<le> length asms"
    "Bi' = Bi \<and> (M = 0 \<or> M = length asms) \<or>
      Bi' = list_forall params (list_implies (drop M asms @ take M asms) (strip_imp_concl (strip_all_body Bi)))"
proof -
  obtain tpairs Bi C where d: "okT (dest_state state i) (tpairs, Bs, Bi, C)"
    and th: "th = mk_rep (th_maxidx state) tpairs (list_implies (Bs @ [Bi']) C)"
    and ps: "params = strip_all_vars Bi" "asms = strip_imp_prems (strip_all_body Bi)"
    and cs: "(0 = m \<or> m = integer_of_nat (length asms)) \<and> Bi' = Bi \<or>
      0 < m \<and> m < integer_of_nat (length asms) \<and> Bi' = list_forall params (list_implies (drop (nat_of_integer m) asms @
        take (nat_of_integer m) asms) (strip_imp_concl (strip_all_body Bi)))"
    using ok unfolding rotate_data_def Let_def
    by (auto simp: returnW_def raiseW_def simp del: strip_all_vars.simps split: if_splits)
  define M where "M = nat_of_integer m"
  have mM: "0 \<le> m \<Longrightarrow> m = integer_of_nat M"
    by (simp add: M_def integer_eq_iff integer_of_nat.rep_eq nat_of_integer.rep_eq less_eq_integer.rep_eq)
  from cs show thesis
  proof (elim disjE conjE)
    assume m: "0 = m" and b: "Bi' = Bi"
    show thesis by (rule that[OF d th ps, of 0]) (use m b in simp_all)
  next
    assume m: "m = integer_of_nat (length asms)" and b: "Bi' = Bi"
    show thesis by (rule that[OF d th ps, of "length asms"]) (use m b in simp_all)
  next
    assume m: "0 < m" "m < integer_of_nat (length asms)"
      and b: "Bi' = list_forall params (list_implies (drop (nat_of_integer m) asms @
        take (nat_of_integer m) asms) (strip_imp_concl (strip_all_body Bi)))"
    have "m = integer_of_nat M" using mM m by simp
    moreover have "M \<le> length asms" using m
      by (simp add: M_def less_integer.rep_eq integer_of_nat.rep_eq nat_of_integer.rep_eq)
    ultimately show thesis by (rule that[OF d th ps]) (rule disjI2, simp add: b M_def)
  qed
qed

lemma closed_no_loose: "closed t \<Longrightarrow> 0 \<le> k \<Longrightarrow> \<not> loose_bvar t k"
  using loose_bvar_mono by (auto simp: closed_def)

lemma closed_subst: "closed t \<Longrightarrow> 0 \<le> i \<Longrightarrow> t[s/i] = t"
  by (rule subst_no_loose) (rule closed_no_loose)

lemma clean_index_aux_ge: "clean_index_aux xs i = (ys, j) \<Longrightarrow> i \<le> j"
proof (induction xs i arbitrary: ys j rule: clean_index_aux.induct)
  case (1 xs i)
  show ?case
  proof (cases "xs \<noteq> [] \<and> last xs = CHR ''_''")
    case True
    with "1.prems" have "clean_index_aux (butlast xs) (i + 1) = (ys, j)" by (simp add: clean_index_aux.simps)
    from "1.IH"[OF True this] show ?thesis by simp
  next
    case False
    with "1.prems" show ?thesis by (simp add: clean_index_aux.simps)
  qed
qed

lemma clean_index_ge: "gi \<le> snd (clean_index (x, gi))"
proof -
  obtain ys j where e: "clean_index_aux (String.explode x) gi = (ys, j)"
    by (cases "clean_index_aux (String.explode x) gi")
  then show ?thesis using clean_index_aux_ge[OF e] by (simp add: clean_index_def)
qed

end

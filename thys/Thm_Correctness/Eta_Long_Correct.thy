section \<open>Soundness of the \<open>\<eta>\<close>-long conversion\<close>

theory Eta_Long_Correct
  imports Equality_Correct
begin

subsection \<open>\<open>\<eta>\<close>-expansion\<close>

lemma downto_snoc_gen: "b \<le> a \<Longrightarrow> downto a b = downto a (b + 1) @ [b]"
proof (induction a b rule: downto.induct)
  case (1 a b)
  show ?case
  proof (cases "a = b")
    case True
    then show ?thesis by (subst (1 2) downto.simps, subst downto.simps) (simp add: integer_arith)
  next
    case False
    with "1.prems" have ab: "b \<le> a - 1" "\<not> a < b" "\<not> a < b + 1" by (simp_all add: integer_arith)
    have "downto a b = a # downto (a - 1) b" using ab(2) by (subst downto.simps) simp
    also have "\<dots> = a # (downto (a - 1) (b + 1) @ [b])" using "1.IH"[OF ab(2) ab(1)] by simp
    moreover have "downto a (b + 1) = a # downto (a - 1) (b + 1)" using ab(3) by (subst downto.simps) simp
    ultimately show ?thesis by simp
  qed
qed

lemma downto_snoc: "0 \<le> k \<Longrightarrow> downto k 0 = downto k 1 @ [0]"
  using downto_snoc_gen[of 0 k] by simp

lemma downto_ge: "x \<in> set (downto a b) \<Longrightarrow> b \<le> x"
proof (induction a b rule: downto.induct)
  case (1 a b)
  show ?case
  proof (cases "a < b")
    case True
    with "1.prems" show ?thesis by (subst (asm) downto.simps) simp
  next
    case False
    with "1.prems" have "x = a \<or> x \<in> set (downto (a - 1) b)" by (subst (asm) downto.simps) simp
    with False "1.IH"[OF False] show ?thesis by (auto simp: integer_arith)
  qed
qed

lemma map_Suc_downto: "map (\<lambda>i. i + 1) (downto a b) = downto (a + 1) (b + 1)"
proof (induction a b rule: downto.induct)
  case (1 a b)
  show ?case
  proof (cases "a < b")
    case True
    then show ?thesis by (subst (1 2) downto.simps) simp
  next
    case False
    then have "\<not> a + 1 < b + 1" by (simp add: integer_arith)
    with False "1.IH"[OF False] show ?thesis by (subst (1 2) downto.simps) (simp add: algebra_simps)
  qed
qed

lemma incr_bv_Bound_downto:
  "0 \<le> b \<Longrightarrow> map (\<lambda>t. lift t 0) (map Bound (downto a b)) = map Bound (downto (a + 1) (b + 1))"
proof -
  assume b: "0 \<le> b"
  have "\<forall>i\<in>set (downto a b). 0 \<le> i" using b downto_ge by force
  then have "map (\<lambda>t. lift t 0) (map Bound (downto a b)) = map Bound (map (\<lambda>i. i + 1) (downto a b))"
    by (induction "downto a b") auto
  then show ?thesis by (simp add: map_Suc_downto)
qed

abbreviation abss :: "ptyp list \<Rightarrow> pterm \<Rightarrow> pterm" where
  "abss Bs b \<equiv> foldr (\<lambda>U b. Abs (STR ''x'') U b) Bs b"

lemma eta_reds_Abs: "s \<rightarrow>\<^sub>\<eta>\<^sup>* s' \<Longrightarrow> Abs a T s \<rightarrow>\<^sub>\<eta>\<^sup>* Abs a T s'"
  by (induction rule: rtranclp_induct) (auto intro: rtranclp.rtrancl_into_rtrancl eta.abs)

lemma eta_reds_abss: "s \<rightarrow>\<^sub>\<eta>\<^sup>* s' \<Longrightarrow> abss Bs s \<rightarrow>\<^sub>\<eta>\<^sup>* abss Bs s'"
  by (induction Bs) (auto intro: eta_reds_Abs)

lemma loose_bvar1_lift_self [simp]: "\<not> loose_bvar1 (incr_bv 1 k u) k"
  by (induction u arbitrary: k) auto

lemma eta_expand_reds:
  "abss Bs (incr_bv (ilength Bs) 0 t \<degree>\<degree> map Bound (downto (ilength Bs - 1) 0)) \<rightarrow>\<^sub>\<eta>\<^sup>* t"
proof (induction Bs rule: rev_induct)
  case Nil
  then show ?case by (simp add: downto.simps)
next
  case (snoc U Bs)
  let ?k = "ilength Bs"
  have k: "0 \<le> ?k" by (rule ilength_nonneg)
  have e: "ilength (Bs @ [U]) = ?k + 1" by (simp add: ilength_eq integer_of_nat_eq_of_nat)
  have eq: "incr_bv (?k + 1) 0 t \<degree>\<degree> map Bound (downto ?k 0) =
      lift (incr_bv ?k 0 t \<degree>\<degree> map Bound (downto (?k - 1) 0)) 0 $ Bound 0"
  proof -
    have "map (\<lambda>t. lift t 0) (map Bound (downto (?k - 1) 0)) = map Bound (downto ?k 1)"
      using incr_bv_Bound_downto[of 0 "?k - 1"] by simp
    with downto_snoc[OF k] incr_bv_Suc[OF k, of 0 t] show ?thesis by (simp add: incr_bv_apps)
  qed
  then have "Abs (STR ''x'') U (incr_bv (?k + 1) 0 t \<degree>\<degree> map Bound (downto ?k 0)) \<rightarrow>\<^sub>\<eta>
      incr_bv ?k 0 t \<degree>\<degree> map Bound (downto (?k - 1) 0)"
  proof -
    have "\<not> loose_bvar1 (lift (incr_bv ?k 0 t \<degree>\<degree> map Bound (downto (?k - 1) 0)) 0) 0"
      by (rule loose_bvar1_lift_self)
    from eta.eta[OF this, of "STR ''x''" U] have
      "Abs (STR ''x'') U (lift (incr_bv ?k 0 t \<degree>\<degree> map Bound (downto (?k - 1) 0)) 0 $ Bound 0) \<rightarrow>\<^sub>\<eta>
        incr_bv ?k 0 t \<degree>\<degree> map Bound (downto (?k - 1) 0)"
      by (simp only: subst_lift)
    then show ?thesis by (simp only: eq)
  qed
  then have "abss Bs (Abs (STR ''x'') U (incr_bv (?k + 1) 0 t \<degree>\<degree> map Bound (downto ?k 0))) \<rightarrow>\<^sub>\<eta>\<^sup>*
      abss Bs (incr_bv ?k 0 t \<degree>\<degree> map Bound (downto (?k - 1) 0))"
    by (intro eta_reds_abss) auto
  with snoc.IH show ?case by (simp add: e)
qed



subsection \<open>Auxiliary facts\<close>

lemma loose_bvar1_incr_bv:
  "loose_bvar1 (incr_bv n lev s) k \<Longrightarrow> 0 \<le> n \<Longrightarrow>
    (k < lev \<and> loose_bvar1 s k) \<or> (lev + n \<le> k \<and> loose_bvar1 s (k - n))"
proof (induction s arbitrary: lev k)
  case (Abs a T s)
  from Abs.prems(1) have "loose_bvar1 (incr_bv n (lev + 1) s) (k + 1)" by simp
  from Abs.IH[OF this Abs.prems(2)] show ?case by (auto simp: algebra_simps integer_arith)
next
  case (App s t)
  then show ?case by auto
qed (auto split: if_splits simp: integer_arith)

lemma map_rev_nth_downto:
  "map (\<lambda>j. rev Bs ! nat_of_integer j) (downto (ilength Bs - 1) 0) = Bs"
proof (induction Bs)
  case Nil
  then show ?case by (simp add: downto.simps)
next
  case (Cons U Bs)
  have k: "0 \<le> ilength Bs" by (rule ilength_nonneg)
  have e: "ilength (U # Bs) - 1 = ilength Bs" by (simp add: ilength_eq integer_of_nat_eq_of_nat)
  have d: "downto (ilength Bs) 0 = ilength Bs # downto (ilength Bs - 1) 0"
    using k by (subst downto.simps) (simp add: integer_arith)
  have "map (\<lambda>j. rev (U # Bs) ! nat_of_integer j) (downto (ilength Bs - 1) 0) =
      map (\<lambda>j. rev Bs ! nat_of_integer j) (downto (ilength Bs - 1) 0)"
  proof (rule map_cong[OF HOL.refl])
    fix j assume j: "j \<in> set (downto (ilength Bs - 1) 0)"
    have "0 \<le> j" "j \<le> ilength Bs - 1" by (rule downto_ge[OF j], rule downto_le[OF j])
    then have "nat_of_integer j < length Bs"
      by (simp add: ilength_eq integer_arith nat_of_integer.rep_eq integer_of_nat_eq_of_nat)
    then show "rev (U # Bs) ! nat_of_integer j = rev Bs ! nat_of_integer j" by (simp add: nth_append)
  qed
  moreover have "rev (U # Bs) ! nat_of_integer (ilength Bs) = U" by (simp add: ilength_eq nth_append)
  ultimately show ?case using Cons.IH by (simp only: e d list.map)
qed

context pure_sig
begin

lemma el_pushes_snoc: "pushes e (Ts @ [T]) = (pushes e Ts)\<langle>0:T\<rangle>"
  by (induction Ts arbitrary: e) simp_all

lemma pushes_above: "0 \<le> k \<Longrightarrow> pushes e Ts (k + ilength Ts) = e k"
proof (induction Ts arbitrary: e k)
  case (Cons T Ts)
  have "pushes (e\<langle>0:T\<rangle>) Ts ((k + 1) + ilength Ts) = (e\<langle>0:T\<rangle>) (k + 1)"
    by (rule Cons.IH) (use Cons.prems in \<open>simp add: integer_arith\<close>)
  moreover have "(k + 1) + ilength Ts = k + ilength (T # Ts)"
    by (simp add: ilength_eq integer_of_nat_eq_of_nat algebra_simps)
  ultimately show ?case using Cons.prems by (simp add: shift_def integer_arith)
qed simp

lemma pushes_below:
  "0 \<le> j \<Longrightarrow> j < ilength Ts \<Longrightarrow> pushes e Ts j = rev Ts ! nat_of_integer j"
proof (induction Ts arbitrary: j rule: rev_induct)
  case (snoc T Ts)
  show ?case
  proof (cases "j = 0")
    case True
    then show ?thesis by (simp add: el_pushes_snoc)
  next
    case False
    with snoc.prems have j: "0 \<le> j - 1" "j - 1 < ilength Ts"
      by (simp_all add: integer_arith ilength_eq integer_of_nat_eq_of_nat)
    have "nat_of_integer j = Suc (nat_of_integer (j - 1))"
      using False snoc.prems(1) by (simp add: integer_arith nat_of_integer.rep_eq)
    with snoc.IH[OF j] False snoc.prems(1) show ?thesis
      by (simp add: el_pushes_snoc shift_def integer_arith)
  qed
qed simp

lemma binder_types_funs: "\<exists>B. T = Pure_Rules.binder_types T \<Rrightarrow> B"
  by (induction T rule: Pure_Rules.binder_types.induct) auto

lemma typing_incr_pushes: "e \<turnstile> s : S \<Longrightarrow> pushes e Bs \<turnstile> incr_bv (ilength Bs) 0 s : S"
proof (induction Bs rule: rev_induct)
  case (snoc U Bs)
  have "(pushes e Bs)\<langle>0:U\<rangle> \<turnstile> lift (incr_bv (ilength Bs) 0 s) 0 : S" by (rule lift_type[OF snoc.IH[OF snoc.prems]]) simp
  moreover have "incr_bv (ilength Bs + 1) 0 s = lift (incr_bv (ilength Bs) 0 s) 0"
    by (rule incr_bv_Suc[OF ilength_nonneg])
  moreover have "ilength (Bs @ [U]) = ilength Bs + 1" by (simp add: ilength_eq integer_of_nat_eq_of_nat)
  ultimately show ?case by (simp add: el_pushes_snoc)
qed simp

lemma typing_abss: "pushes e Bs \<turnstile> b : B \<Longrightarrow> \<forall>U\<in>set Bs. cert_typ alg ar U \<Longrightarrow> e \<turnstile> abss Bs b : Bs \<Rrightarrow> B"
  by (induction Bs arbitrary: e) auto

lemma conv_abss: "wt (abss Bs s) \<Longrightarrow> wt (abss Bs s') \<Longrightarrow> s \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> s' \<Longrightarrow> abss Bs s \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> abss Bs s'"
  by (induction Bs) (auto intro: conv_Abs dest: wt_AbsD)

lemma cert_funs: "cert_typ alg ar (Bs \<Rrightarrow> B) \<Longrightarrow> \<forall>U\<in>set Bs. cert_typ alg ar U"
  by (induction Bs) (auto simp: cert_typ_fun)

end


subsection \<open>Correctness of \<open>eta_long\<close>\<close>

context pure_sig
begin

definition bvok :: "(integer \<Rightarrow> ptyp) \<Rightarrow> ptyp list \<Rightarrow> pterm \<Rightarrow> bool" where
  "bvok e Ts t \<longleftrightarrow> (\<forall>k. 0 \<le> k \<longrightarrow> loose_bvar1 t k \<longrightarrow>
    k < ilength Ts \<and> e k = Ts ! nat_of_integer k \<and> cert_typ alg ar (e k))"

end

context pure_sig
begin

lemma beta_reds_loose_bvar1: "t \<rightarrow>\<^sub>\<beta>\<^sup>* t' \<Longrightarrow> 0 \<le> k \<Longrightarrow> loose_bvar1 t' k \<Longrightarrow> loose_bvar1 t k"
  by (induction arbitrary: k rule: rtranclp_induct) (auto dest: free_beta)

end

context pure_sig
begin

definition lbsub :: "pterm \<Rightarrow> pterm \<Rightarrow> bool" where
  "lbsub s t \<longleftrightarrow> (\<forall>k. 0 \<le> k \<longrightarrow> loose_bvar1 s k \<longrightarrow> loose_bvar1 t k)"

end

context pure_sig
begin

lemma loose_bvar1_abss: "loose_bvar1 (abss Bs b) k \<Longrightarrow> loose_bvar1 b (k + ilength Bs)"
proof (induction Bs arbitrary: k)
  case (Cons U Bs)
  from Cons.prems have "loose_bvar1 (abss Bs b) (k + 1)" by simp
  from Cons.IH[OF this] show ?case by (simp add: ilength_eq integer_of_nat_eq_of_nat algebra_simps)
qed simp

end

context pure_sig
begin

lemma eta_long_correct:
  "Pure_Rules.eta_long Ts t = Some y \<Longrightarrow> y = Ok t' \<Longrightarrow> e \<turnstile> t : T \<Longrightarrow> bvok e Ts t \<Longrightarrow>
    e \<turnstile> t' : T \<and> t \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> t' \<and> lbsub t' t"
proof (induction Ts t y arbitrary: t' e T rule: Pure_Rules.eta_long.raw_induct[rotated, consumes 1])
  case (1 f Ts t y)
  have IH: "e' \<turnstile> s' : S \<and> s \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> s' \<and> lbsub s' s" if "ok (f Ts' s) s'" "e' \<turnstile> s : S" "bvok e' Ts' s" for Ts' s s' e' S
    using "1.IH"[OF that(1) HOL.refl that(2,3)] .
  from "1.hyps" "1.prems"(1) have hyps: "ok (case dest_Abs t of
     None \<Rightarrow>
       case strip_comb t of
       (u, ts) \<Rightarrow>
         if is_Abs u then beta_norm t \<bind> f Ts
         else fastype_of_term Ts t \<bind>
              (\<lambda>T. mapM (\<lambda>s. f (rev (Pure_Rules.binder_types T) @ Ts)
                    (incr_boundvars (integer_of_nat (length (Pure_Rules.binder_types T))) s)) ts \<bind>
                   (\<lambda>ts'. mapM (\<lambda>j. f (rev (Pure_Rules.binder_types T) @ Ts) (Bound j))
                           (downto (integer_of_nat (length (Pure_Rules.binder_types T)) - 1) 0) \<bind>
                          (\<lambda>bs. return (abss (Pure_Rules.binder_types T)
                            (list_comb (incr_boundvars (integer_of_nat (length (Pure_Rules.binder_types T))) u)
                              (ts' @ bs))))))
     | Some (s, T, b) \<Rightarrow> f (T # Ts) b \<bind> (\<lambda>b'. return (Abs s T b'))) t'"
    by simp
  note ty = "1.prems"(2) and bv = "1.prems"(3)
  have wt: "wt t" using ty by (auto simp: wt_def)
  show ?case
  proof (cases "dest_Abs t")
    case (Some x)
    then obtain a T0 b where t: "t = Abs a T0 b" by (cases t) auto
    from hyps t obtain b' where b': "ok (f (T0 # Ts) b) b'" and t': "t' = Abs a T0 b'" by auto
    from ty t obtain U where T: "T = T0 \<rightarrow>\<^sub>T U" and c0: "cert_typ alg ar T0" and tb: "e\<langle>0:T0\<rangle> \<turnstile> b : U" by auto
    have "bvok (e\<langle>0:T0\<rangle>) (T0 # Ts) b" unfolding bvok_def
    proof (intro allI impI)
      fix k assume k: "0 \<le> k" "loose_bvar1 b k"
      show "k < ilength (T0 # Ts) \<and> (e\<langle>0:T0\<rangle>) k = (T0 # Ts) ! nat_of_integer k \<and> cert_typ alg ar ((e\<langle>0:T0\<rangle>) k)"
      proof (cases "k = 0")
        case False
        with k have k1: "0 \<le> k - 1" "loose_bvar1 t (k - 1)" by (simp_all add: integer_arith t)
        from bv k1 have "k - 1 < ilength Ts" "e (k - 1) = Ts ! nat_of_integer (k - 1)" "cert_typ alg ar (e (k - 1))"
          unfolding bvok_def by blast+
        moreover have "nat_of_integer k = Suc (nat_of_integer (k - 1))"
          using False k(1) by (simp add: integer_arith nat_of_integer.rep_eq)
        ultimately show ?thesis using False k(1) by (simp add: integer_arith ilength_eq integer_of_nat_eq_of_nat)
      qed (use c0 ilength_nonneg[of Ts] in \<open>simp add: integer_arith ilength_eq integer_of_nat_eq_of_nat\<close>)
    qed
    from IH[OF b' tb this] have "e\<langle>0:T0\<rangle> \<turnstile> b' : U" "b \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> b'" "lbsub b' b" by auto
    moreover have "e \<turnstile> t' : T" using calculation(1) c0 by (auto simp: t' T)
    moreover have "lbsub t' t" using calculation(3) by (auto simp: lbsub_def t t' integer_arith)
    ultimately show ?thesis using conv_Abs[of a T0 b a b'] wt ty by (auto simp: t t' wt_def)
  next
    case None
    obtain u ts where sc: "strip_comb t = (u, ts)" by (cases "strip_comb t")
    have t: "t = u \<degree>\<degree> ts" by (rule strip_comb_apps[OF sc])
    show ?thesis
    proof (cases "is_Abs u")
      case True
      with hyps None sc obtain t2 where n: "ok (beta_norm t) t2" and r: "ok (f Ts t2) t'" by auto
      note red = beta_norm_reds[OF n]
      have t2: "e \<turnstile> t2 : T" by (rule subject_reduction_beta'[OF red ty])
      have "bvok e Ts t2" using bv beta_reds_loose_bvar1[OF red] by (auto simp: bvok_def)
      from IH[OF r t2 this] have "e \<turnstile> t' : T" "t2 \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> t'" "lbsub t' t2" by auto
      moreover have "t \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> t2" by (rule conv_beta_eta[OF wt red])
      moreover have "lbsub t' t" using calculation(3) beta_reds_loose_bvar1[OF red] by (auto simp: lbsub_def)
      ultimately show ?thesis by (blast intro: conv_trans)
    next
      case False
      let ?Bt = "Pure_Rules.binder_types T"
      let ?n = "integer_of_nat (length ?Bt)"
      let ?E = "pushes e ?Bt" and ?Ts' = "rev ?Bt @ Ts"
      have ft: "fastype_of_term Ts t = return T"
        using fastype_of_typed[OF ty] bv by (auto simp: bvok_def)
      from hyps None sc False ft obtain ts' bs where
        mts: "ok (mapM (\<lambda>s. f ?Ts' (incr_boundvars ?n s)) ts) ts'"
        and mbs: "ok (mapM (\<lambda>j. f ?Ts' (Bound j)) (downto (?n - 1) 0)) bs"
        and t': "t' = abss ?Bt (list_comb (incr_boundvars ?n u) (ts' @ bs))"
        by (auto simp: return_def)
      have nB: "?n = ilength ?Bt" by (simp add: ilength_eq)
      obtain B where TB: "T = ?Bt \<Rrightarrow> B" using binder_types_funs by blast
      have cT: "cert_typ alg ar T" by (rule typing_cert[OF ty]) (use bv in \<open>auto simp: bvok_def\<close>)
      have cB: "\<forall>U\<in>set ?Bt. cert_typ alg ar U" using cert_funs[of ?Bt B] cT TB by simp
      from ty t obtain Ss where tu: "e \<turnstile> u : Ss \<Rrightarrow> T" and tts: "e \<tturnstile> ts : Ss" by (auto elim: list_app_typeE)
      \<comment> \<open>the arguments\<close>
      have bvs: "bvok ?E ?Ts' (incr_bv ?n 0 s)" if s: "s \<in> set ts" for s
        unfolding bvok_def
      proof (intro allI impI)
        fix k assume k: "0 \<le> k" "loose_bvar1 (incr_bv ?n 0 s) k"
        from loose_bvar1_incr_bv[OF k(2)] k(1) have kn: "?n \<le> k" "loose_bvar1 s (k - ?n)" by auto
        have "loose_bvar1 t (k - ?n)" using kn(2) s t by (auto simp: loose_bvar1_apps)
        moreover have "0 \<le> k - ?n" using kn(1) by (simp add: integer_arith)
        ultimately have b: "k - ?n < ilength Ts" "e (k - ?n) = Ts ! nat_of_integer (k - ?n)" "cert_typ alg ar (e (k - ?n))"
          using bv unfolding bvok_def by blast+
        have "(k - ?n) + ilength ?Bt = k" using nB by simp
        then have E: "?E k = e (k - ?n)" using pushes_above[of "k - ?n" e ?Bt] \<open>0 \<le> k - ?n\<close> by simp
        have "nat_of_integer k = length ?Bt + nat_of_integer (k - ?n)"
          using kn(1) by (simp add: integer_arith nat_of_integer.rep_eq)
        then have "?Ts' ! nat_of_integer k = Ts ! nat_of_integer (k - ?n)" by (simp add: nth_append)
        moreover have "k < ilength ?Ts'" using b(1) by (simp add: ilength_eq integer_arith)
        ultimately show "k < ilength ?Ts' \<and> ?E k = ?Ts' ! nat_of_integer k \<and> cert_typ alg ar (?E k)"
          using E b by simp
      qed
      have l1: "list_all2 (\<lambda>s s'. ok (f ?Ts' (incr_boundvars ?n s)) s') ts ts'" using mts by (simp add: ok_mapM)
      have tl: "length ts = length Ss" using typings_nth[OF tts] by simp
      have rts: "list_all2 (\<lambda>s s'. ?E \<turnstile> s' : Ss ! i \<and> incr_bv ?n 0 s \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> s' \<and> lbsub s' (incr_bv ?n 0 s))
          [ts ! i] [ts' ! i]"
        if i: "i < length ts" for i
      proof -
        have s: "ts ! i \<in> set ts" using i by simp
        have "e \<turnstile> ts ! i : Ss ! i" using typings_nth[OF tts] i by simp
        then have "?E \<turnstile> incr_bv ?n 0 (ts ! i) : Ss ! i" using typing_incr_pushes nB by simp
        moreover have "ok (f ?Ts' (incr_bv ?n 0 (ts ! i))) (ts' ! i)"
          using list_all2_nthD[OF l1 i] by (simp add: incr_boundvars_incr_bv)
        ultimately show ?thesis using IH bvs[OF s] by simp
      qed
      have lts: "length ts' = length ts" using list_all2_lengthD[OF l1] by simp
      have tts': "?E \<tturnstile> ts' : Ss"
        by (rule typings_nthI) (use rts lts tl in auto)
      have cts: "list_all2 (\<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta>) (map (incr_bv ?n 0) ts) ts'"
        using rts lts by (auto simp: list_all2_conv_all_nth)
      \<comment> \<open>the new bound variables\<close>
      let ?ds = "downto (?n - 1) 0"
      have dj: "0 \<le> j \<and> j < ilength ?Bt" if "j \<in> set ?ds" for j
        using downto_ge[OF that] downto_le[OF that] nB by (simp add: integer_arith)
      have rbt: "rev ?Bt ! nat_of_integer j \<in> set ?Bt" if "j \<in> set ?ds" for j
      proof -
        have "nat_of_integer j < length (rev ?Bt)"
          using dj[OF that] by (simp add: ilength_eq integer_arith nat_of_integer.rep_eq nat_less_iff)
        from nth_mem[OF this] show ?thesis by simp
      qed
      have l2: "list_all2 (\<lambda>j b. ok (f ?Ts' (Bound j)) b) ?ds bs" using mbs by (simp add: ok_mapM)
      have rbs: "?E \<turnstile> b : rev ?Bt ! nat_of_integer j \<and> Bound j \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> b \<and> lbsub b (Bound j)"
        if jb: "j \<in> set ?ds" "ok (f ?Ts' (Bound j)) b" for j b
      proof -
        note d = dj[OF jb(1)]
        have Ej: "?E j = rev ?Bt ! nat_of_integer j" by (rule pushes_below) (use d in auto)
        have "?E \<turnstile> Bound j : rev ?Bt ! nat_of_integer j" using d Ej by auto
        moreover have "bvok ?E ?Ts' (Bound j)" unfolding bvok_def
        proof (intro allI impI)
          fix k assume "0 \<le> k" "loose_bvar1 (Bound j) k"
          then have k: "k = j" by simp
          have "nat_of_integer j < length ?Bt"
            using d by (simp add: ilength_eq integer_arith nat_of_integer.rep_eq nat_less_iff)
          then have "?Ts' ! nat_of_integer j = rev ?Bt ! nat_of_integer j" by (simp add: nth_append)
          moreover have "j < ilength ?Ts'" using d ilength_nonneg[of Ts] by (simp add: ilength_eq integer_arith)
          ultimately show "k < ilength ?Ts' \<and> ?E k = ?Ts' ! nat_of_integer k \<and> cert_typ alg ar (?E k)"
            using k Ej cB rbt[OF jb(1)] by simp
        qed
        ultimately show ?thesis using IH[OF jb(2)] by blast
      qed
      have lbs: "length bs = length ?ds" using list_all2_lengthD[OF l2] by simp
      have tbs: "?E \<tturnstile> bs : ?Bt"
      proof -
        have "?E \<tturnstile> bs : map (\<lambda>j. rev ?Bt ! nat_of_integer j) ?ds"
          by (rule typings_nthI) (use rbs list_all2_nthD[OF l2] lbs in auto)
        then show ?thesis using map_rev_nth_downto[of ?Bt] nB by simp
      qed
      have cbs: "list_all2 (\<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta>) (map Bound ?ds) bs"
        using rbs list_all2_nthD[OF l2] lbs by (auto simp: list_all2_conv_all_nth)
      have tbd: "?E \<tturnstile> map Bound ?ds : ?Bt"
      proof -
        have "?E \<tturnstile> map Bound ?ds : map (\<lambda>j. rev ?Bt ! nat_of_integer j) ?ds"
          by (rule typings_Bounds) (use dj pushes_below in auto)
        then show ?thesis using map_rev_nth_downto[of ?Bt] nB by simp
      qed
      \<comment> \<open>the bodies\<close>
      have tuE: "?E \<turnstile> incr_bv ?n 0 u : (Ss @ ?Bt) \<Rrightarrow> B"
        using typing_incr_pushes[OF tu, of ?Bt] nB TB by simp
      have tapp: "?E \<tturnstile> xs @ ys : Xs @ Ys" if "?E \<tturnstile> xs : Xs" "?E \<tturnstile> ys : Ys" for xs ys Xs Ys
        using that by (induction xs arbitrary: Xs) (auto split: list.splits)
      have tmts: "?E \<tturnstile> map (incr_bv ?n 0) ts : Ss"
        by (rule typings_nthI) (use typings_nth[OF tts] typing_incr_pushes nB in auto)
      have b1: "?E \<turnstile> incr_bv ?n 0 u \<degree>\<degree> (ts' @ bs) : B" by (rule list_app_typeI[OF tuE tapp[OF tts' tbs]])
      have b0: "?E \<turnstile> incr_bv ?n 0 u \<degree>\<degree> (map (incr_bv ?n 0) ts @ map Bound ?ds) : B"
        by (rule list_app_typeI[OF tuE tapp[OF tmts tbd]])
      have e0: "incr_bv ?n 0 t \<degree>\<degree> map Bound ?ds = incr_bv ?n 0 u \<degree>\<degree> (map (incr_bv ?n 0) ts @ map Bound ?ds)"
        by (simp add: t incr_bv_apps)
      have ct': "e \<turnstile> t' : T"
        using typing_abss[OF b1 cB] TB by (simp add: t' list_comb_apps incr_boundvars_incr_bv)
      have cR0: "e \<turnstile> abss ?Bt (incr_bv ?n 0 t \<degree>\<degree> map Bound ?ds) : T"
        using typing_abss[OF b0 cB] TB e0 by simp
      have r: "abss ?Bt (incr_bv ?n 0 t \<degree>\<degree> map Bound ?ds) \<rightarrow>\<^sub>\<eta>\<^sup>* t"
        using eta_expand_reds[of ?Bt t] nB by simp
      have wR0: "wt (abss ?Bt (incr_bv ?n 0 t \<degree>\<degree> map Bound ?ds))" using cR0 by (auto simp: wt_def)
      have c1: "t \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> abss ?Bt (incr_bv ?n 0 t \<degree>\<degree> map Bound ?ds)"
        by (rule conv_sym[OF beta_eta_conv[OF eta_reds_sup[OF r] wR0]])
      have "incr_bv ?n 0 u \<degree>\<degree> (map (incr_bv ?n 0) ts @ map Bound ?ds) \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> incr_bv ?n 0 u \<degree>\<degree> (ts' @ bs)"
        by (rule conv_apps[OF list_all2_appendI[OF cts cbs]]) (use b0 b1 in \<open>auto simp: wt_def\<close>)
      then have "abss ?Bt (incr_bv ?n 0 t \<degree>\<degree> map Bound ?ds) \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> abss ?Bt (incr_bv ?n 0 u \<degree>\<degree> (ts' @ bs))"
        using cR0 ct' e0 by (intro conv_abss) (auto simp: wt_def t' list_comb_apps incr_boundvars_incr_bv)
      then have c2: "abss ?Bt (incr_bv ?n 0 t \<degree>\<degree> map Bound ?ds) \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> t'"
        by (simp add: t' list_comb_apps incr_boundvars_incr_bv)
      have "lbsub t' t" unfolding lbsub_def
      proof (intro allI impI)
        fix k assume k: "0 \<le> k" "loose_bvar1 t' k"
        then have lb: "loose_bvar1 (incr_bv ?n 0 u \<degree>\<degree> (ts' @ bs)) (k + ?n)"
          using loose_bvar1_abss[of ?Bt _ k] nB by (simp add: t' list_comb_apps incr_boundvars_incr_bv)
        have kn: "0 \<le> k + ?n" "\<not> k + ?n < 0" "(k + ?n) - ?n = k" using k(1) by (simp_all add: integer_arith)
        from lb consider "loose_bvar1 (incr_bv ?n 0 u) (k + ?n)" | "\<exists>s'\<in>set ts'. loose_bvar1 s' (k + ?n)"
          | "\<exists>b\<in>set bs. loose_bvar1 b (k + ?n)"
          by (auto simp: loose_bvar1_apps)
        then show "loose_bvar1 t k"
        proof cases
          case 1
          from loose_bvar1_incr_bv[OF this] kn have "loose_bvar1 u k" by auto
          then show ?thesis by (simp add: t loose_bvar1_apps)
        next
          case 2
          then obtain i where i: "i < length ts'" "loose_bvar1 (ts' ! i) (k + ?n)" by (auto simp: in_set_conv_nth)
          with rts lts have "loose_bvar1 (incr_bv ?n 0 (ts ! i)) (k + ?n)" by (auto simp: lbsub_def kn)
          from loose_bvar1_incr_bv[OF this] kn have "loose_bvar1 (ts ! i) k" by auto
          with i lts show ?thesis by (auto simp: t loose_bvar1_apps)
        next
          case 3
          then obtain i where i: "i < length bs" "loose_bvar1 (bs ! i) (k + ?n)" by (auto simp: in_set_conv_nth)
          have m: "?ds ! i \<in> set ?ds" using i lbs by simp
          from rbs[OF m list_all2_nthD[OF l2]] i lbs have "loose_bvar1 (Bound (?ds ! i)) (k + ?n)"
            by (auto simp: lbsub_def kn)
          then have "?ds ! i = k + ?n" by simp
          moreover have "?ds ! i < ?n" using dj[OF m] nB by simp
          ultimately show ?thesis using k(1) by (simp add: integer_arith)
        qed
      qed
      then show ?thesis using ct' conv_trans[OF c1 c2] by simp
    qed
  qed
qed

end

context pure_model
begin

theorem eta_long_conversion_valid:
  assumes ok: "okT (eta_long_conversion (CTerm t T m)) th" and eq: "eq_ok"
    and c: "closed t" and ty: "\<And>e. e \<turnstile> t : T"
  shows "valid Sh [] (th_tpairs th) (th_prop th)"
proof -
  from ok obtain t' P where el: "ok (Pure_Rules.eta_long [] t) t'" and mk: "ok (mk_equals (t, t')) P"
    and th: "th = mk_rep m [] P"
    by (auto simp: eta_long_conversion_def)
  have bv: "bvok e [] t" for e using c by (simp add: bvok_def closed_iff_loose_bvar1)
  note r = eta_long_correct[OF el HOL.refl ty bv]
  have ty': "e \<turnstile> t' : T" for e using eta_long_correct[OF el HOL.refl ty bv, of e] by blast
  have cv: "t \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> t'" and lb: "lbsub t' t" using r by blast+
  have c': "closed t'" using c lb by (auto simp: lbsub_def closed_iff_loose_bvar1)
  have "valid Sh [] [] (eq_const T $ t $ t')" by (rule valid_conv_eq[OF eq c c' ty ty' cv])
  then show ?thesis using mk_equals_ok[OF mk c ty] by (simp add: th mk_rep_def)
qed

end

end

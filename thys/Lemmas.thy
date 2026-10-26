theory Lemmas
  imports Main Lambda "~~/src/HOL/Proofs/Lambda/Commutation" ParRed Eta ListApplication
    StrongNorm "HOL-Library.Linear_Temporal_Logic_on_Streams" "HOL-Library.BNF_Corec"
begin

lemma size_subst_trivial: "\<not> free s i \<Longrightarrow> size (s[x/i]) = size s"
  by (induct s arbitrary: x i) (auto simp: subst_BVar)

lemma eta_size_decreases: "t \<rightarrow>\<^sub>\<eta> u \<Longrightarrow> size u < size t"
  by (induct t u rule: eta.induct) (auto simp: size_subst_trivial)

theorem eta_termi: "termip eta t"
  by (rule accp_wfPD) (auto simp: wfP_def eta_size_decreases intro!: wf_subset[OF wf_measure[of size]])

inductive chain for R where
  "chain R [x]"
| "R x y \<Longrightarrow> chain R (y # ys) \<Longrightarrow> chain R (x # y # ys)"

coinductive ichain for R where
  "R x y \<Longrightarrow> ichain R (y ## s) \<Longrightarrow> ichain R (x ## y ## s)"

coinductive ichain' for R where
  "xs \<noteq> [] \<Longrightarrow> chain R (xs @ [shd s]) \<Longrightarrow> ichain' R s \<Longrightarrow> ichain' R (xs @- s)"

lemma ichain_ichain': "ichain R s \<Longrightarrow> ichain' R s"
proof (coinduction arbitrary: s)
  case ichain'
  then show ?case 
    by (auto intro!: exI[of _ "[shd s]"]  exI[of _ "stl s"] elim: ichain.cases intro!: chain.intros)
qed

lemma ichain'_ichain: "ichain' R s \<Longrightarrow> ichain R s"
proof (coinduction arbitrary: s)
  case ichain
  then show ?case
  proof (cases rule: ichain'.cases)
    case (1 xs s')
    then show ?thesis
      apply -
      apply (rule exI[of _ "hd xs"])
      apply (intro disjI2 exI[of _ "stl (tl xs @- s')"] exI[of _ "shd (tl xs @- s')"])
      apply (cases xs)
       apply (auto elim: chain.cases intro!: ichain'.intros
         simp flip: shift.simps simp: neq_Nil_conv)
      apply simp
      done
  qed
qed

lemma ichain_eq_ichain': "ichain R s \<longleftrightarrow> ichain' R s"
  using ichain'_ichain ichain_ichain' by blast

lemmas ichain_coinduct[case_names ichain] = ichain'.coinduct[folded ichain_eq_ichain']

lemmas ichain_intros = ichain'.intros[folded ichain_eq_ichain']

lemma ichain_last_intros:
  "xs \<noteq> [] \<Longrightarrow> chain R xs \<Longrightarrow> ichain R (last xs ## s) \<Longrightarrow> ichain R (xs @- s)"
  by (smt append_butlast_last_id ichain'.simps ichain'_ichain ichain_ichain' shift.simps(1) shift.simps(2) shift_append stream.sel(1))

context begin

private lemma termip_no_ichain: "termip R t \<Longrightarrow> \<not> (\<exists>s. ichain R (t ## s))"
  by (induct t rule: accp.induct) (auto elim: ichain.cases)

private primcorec wit where
  "wit R t = (let u = SOME u. R t u \<and> \<not> termip R u in u ## wit R u)"

private lemma not_termip_ichain: "\<not> termip R t \<Longrightarrow> ichain R (t ## wit R t)"
  apply (coinduction arbitrary: t pred: ichain)
  apply (subst wit.code)
  apply (auto simp: Let_def)
  apply (metis (mono_tags, lifting) accp.intros conversep.cases verit_sko_ex_indirect)
  apply (metis (mono_tags, lifting) accp.intros conversep.cases verit_sko_ex_indirect)
  done

lemma termip_iff_no_ichain: "termip R t \<longleftrightarrow> \<not> (\<exists>s. ichain R (t ## s))"
  by (meson not_termip_ichain termip_no_ichain)

end

context begin

thm eta_postponement'

lemma rtranclp_ex_chain: 
  "R\<^sup>*\<^sup>* s t \<Longrightarrow> \<exists>xs. chain R (s # xs) \<and> last (s # xs) = t"
  apply (induct s rule: converse_rtranclp_induct)
   apply (metis chain.intros(1) last_ConsL)
  apply (metis chain.intros(2) last_ConsR list.distinct(1))
  done

lemma tranclp_ex_chain: 
  "R\<^sup>+\<^sup>+ s t \<Longrightarrow> \<exists>xs. chain R (s # xs @ [t])"
  apply (induct s rule: converse_tranclp_induct)
   apply (metis append_Nil chain.intros)
  apply (metis append_Cons chain.intros(2))
  done

lemma chain_rtranclp: 
  "chain R s \<Longrightarrow> R\<^sup>*\<^sup>* (hd s) (last s)"
  by (induct s rule: chain.induct) auto

private friend_of_corec shift where
  "xs @- s = (case xs of [] \<Rightarrow> shd s ## stl s| x # xs' \<Rightarrow> x ## (xs' @- s))"
  by (simp split: list.splits) transfer_prover

private corec wit_postpone where
  "wit_postpone R S s =
     (let i = LEAST i. R (s !! i) (s !! Suc i);
          (xs, t, ys) = SOME (xs, t, ys). chain R (shd s # xs @ [t]) \<and> chain S (t # ys) \<and> last (t # ys) = s !! Suc i
     in shd s ## xs @- wit_postpone R S (t ## ys @- sdrop (Suc (Suc i)) s))"

lemma shd_wit_postpone[simp]: "shd (wit_postpone R S s) = shd s"
  by (subst wit_postpone.code) (auto simp: Let_def split_beta)

lemma ichain_stl: "ichain R s \<Longrightarrow> ichain R (stl s)"
  by (erule ichain.cases) auto

lemma ichain_sdrop: "ichain R s \<Longrightarrow> ichain R (sdrop i s)"
  by (induct i arbitrary: s) (auto simp: ichain_stl)

lemma ichain_stake: "ichain R s \<Longrightarrow> chain R (stake (Suc i) s)"
  by (induct i arbitrary: s) (auto dest: ichain_stl intro!: chain.intros elim: ichain.cases)

lemma chain_mono: "chain R xs \<Longrightarrow> R \<le> S \<Longrightarrow> chain S xs"
  by (induct xs rule: chain.induct) (auto intro: chain.intros)

lemma ichain_pairwise: "ichain R s \<Longrightarrow> R (s !! i) (s !! Suc i)"
  by (induct i arbitrary: s) (auto elim: ichain.cases dest: ichain_stl)

lemma pairwise_ichain: "(\<forall>i. R (s !! i) (s !! Suc i)) \<Longrightarrow> ichain R s"
  by (coinduction arbitrary: s) (metis snth.simps(1) snth.simps(2) stream.exhaust_sel)

lemma ichain_iff_pairwise: "ichain R s \<longleftrightarrow> (\<forall>i. R (s !! i) (s !! Suc i))"
  by (metis ichain_pairwise pairwise_ichain)

lemma ichain_wit_postpone:
  assumes "S\<^sup>*\<^sup>* OO R \<le> R\<^sup>+\<^sup>+ OO S\<^sup>*\<^sup>*" "\<And>u. termip S u" "ichain (sup R S) s"
  shows "ichain R (wit_postpone R S s)"
  using assms(3)
proof (coinduction arbitrary: s rule: ichain_coinduct)
  case ichain
  have *: "\<exists>i. R (s !! i) (s !! Suc i)"
  proof (rule ccontr)
    assume "\<nexists>i. R (s !! i) (s !! Suc i)"
    with ichain have "ichain S s"
      unfolding ichain_iff_pairwise by auto
    with assms(2) show False
      unfolding termip_iff_no_ichain by (metis stream.exhaust) 
  qed
  define i where "i = (LEAST i. R (s !! i) (s !! Suc i))"
  have  "R (s !! i) (s !! Suc i)"
    unfolding i_def by (rule LeastI2_ex[OF *])
  from ichain have "chain (sup R S) (stake (Suc i) s)"
    by (rule ichain_stake)
  moreover have "\<forall>k <i. \<not> R (s !! k) (s !! Suc k)"
    using not_less_Least[of _ "\<lambda>i. R (s !! i) (s !! Suc i)"]
    by (auto simp: i_def)
  ultimately have "chain S (stake (Suc i) s)"
    by (induct i arbitrary: s) (fastforce intro!: chain.intros elim: chain.cases simp: less_eq_Suc_le)+
  then have "S\<^sup>*\<^sup>* (shd s) (s !! i)"
    by (auto dest!: chain_rtranclp simp: last_conv_nth hd_conv_nth simp del: stake.simps split: if_splits)
  from assms(1)[THEN predicate2D, OF relcomppI, OF this \<open>R (s !! i) (s !! Suc i)\<close>]
  obtain t where r: "R\<^sup>+\<^sup>+ (shd s) t" and s: "S\<^sup>*\<^sup>* t (s !! Suc i)"
    by auto
  define p where "p = (SOME (xs, t, ys). chain R (shd s # xs @ [t]) \<and>
                                         chain S (t # ys) \<and> last (t # ys) = s !! Suc i)"
    (is "p = (SOME (xs, t, ys). ?chains xs t ys)")
  let ?xs = "fst p" let ?t = "fst (snd p)" let ?ys = "snd (snd p)"
  from tranclp_ex_chain[OF r] rtranclp_ex_chain[OF s] have "?chains ?xs ?t ?ys"
    unfolding p_def split_beta
    apply -
    apply (rule someI_ex)
    apply (auto split: if_splits)
    done
  then have [simp]: "chain R (shd s # ?xs @ [?t])" and chain: "chain S (?t # ?ys)"
    and last: "last (?t # ?ys) = s !! Suc i" by auto
  from ichain have "ichain (sup R S) (sdrop (Suc i) s)"
    by (rule ichain_sdrop)
  then have "ichain (sup R S) (?t ## ?ys @- sdrop (Suc (Suc i)) s)"
    apply (fold shift.simps)
    apply (rule ichain_last_intros)
     apply simp
     apply (simp add: chain_mono[OF chain])
    apply (unfold last)
    by (metis sdrop_simps(1) sdrop_simps(2) stream.collapse)
  then show ?case
    apply (intro exI[of _ "shd s # ?xs"] exI[of _ "wit_postpone R S (?t ## ?ys @- sdrop (Suc (Suc i)) s)"] conjI)
     apply (subst wit_postpone.code)
       apply (auto simp: Let_def i_def p_def split_beta) []
      apply simp
     apply simp
    apply (rule disjI1 exI conjI[OF refl])+
    apply assumption
    done
qed

lemma termip_sup:
  assumes "S\<^sup>*\<^sup>* OO R \<le> R\<^sup>+\<^sup>+ OO S\<^sup>*\<^sup>*" "\<And>u. termip S u"
  shows "termip R t \<Longrightarrow> termip (sup R S) t"
proof (unfold termip_iff_no_ichain, elim contrapos_nn exE)
  fix s
  assume "ichain (sup R S) (t ## s)"
  then have "ichain R (wit_postpone R S (t ## s))"
    by (rule ichain_wit_postpone[OF assms(1,2)])
  then show "\<exists>s. ichain R (t ## s)"
    by (subst (asm) wit_postpone.code) (auto simp: Let_def split_beta)
qed

end

theorem type_implies_termi_beta_eta: "e \<turnstile> t : T \<Longrightarrow> termip (sup beta eta) t"
  by (rule termip_sup[OF predicate2I eta_termi type_implies_termi])
    (auto simp: relcompp_apply intro: eta_postponement')

lemma list_application_last: "\<lbrakk>length xs = Suc m\<rbrakk> \<Longrightarrow> t \<degree>\<degree> xs = (t \<degree>\<degree> take m xs) \<degree> last xs"
proof (induction xs arbitrary: t m)
  case Nil
  then show ?case by auto
next
  case (Cons a xs)
  have "m = 0 \<Longrightarrow> ?case" proof -
    assume "m = 0"
    from Cons this show ?thesis by fastforce
  qed
  moreover have "m > 0 \<Longrightarrow> ?case" proof -
    assume 0: "m > 0"
    from this Cons have "length xs = Suc (m - 1)" by auto
    moreover have "t \<degree>\<degree> (a # xs) = (t \<degree> a) \<degree>\<degree> xs" by simp
    ultimately have "t \<degree>\<degree> (a # xs) = ((t \<degree> a) \<degree>\<degree> take (m - 1) xs) \<degree> last xs"
      using Cons by presburger
    moreover from 0 Cons have "(t \<degree> a) \<degree>\<degree> take (m - 1) xs = t \<degree>\<degree> take m (a # xs)"
      by (simp add: take_Cons')
    ultimately show ?thesis by fastforce
  qed
  ultimately show ?case by fastforce
qed

fun any :: "bool list \<Rightarrow> bool" where
"any [] = False" |
"any (x # xs) = (x \<or> any xs)"

lemma list_application_free:
"free (t \<degree>\<degree> xs) y = free t y \<or> any (map (\<lambda>x. free x y) xs)" proof (induction xs arbitrary: t)
  case Nil
  then show ?case by simp
next
  case (Cons a xs)
  have "t \<degree>\<degree> (a # xs) = (t \<degree> a) \<degree>\<degree> xs" by auto
  moreover have "map (\<lambda>x. free x y) (a # xs) = free a y # map (\<lambda>u. free u y) xs" by auto
  moreover have "any (free a y # map (\<lambda>u. free u y) xs) = free a y \<or> any (map (\<lambda>u. free u y) xs)"
    by auto
  ultimately show ?case using Cons by force
qed

fun Abs_m :: "nat \<Rightarrow> dB \<Rightarrow> dB" where
"Abs_m 0 t = t" |
"Abs_m m t = Abs (Abs_m (m - 1) t)"

lemma Abs_m: "Abs (Abs_m m t) = Abs_m m (Abs t)"
  apply(induction m)
   apply(auto)
  done

lemma Abs_m_eta: "s \<rightarrow>\<^sub>\<eta> t ==> Abs_m m s \<rightarrow>\<^sub>\<eta> Abs_m m t"
  apply(induction m)
   apply simp
  by force

lemma Abs_m_subst: "(Abs_m m t)[BVar x/n] = Abs_m m (t[BVar (x + m)/n + m])"
  apply (induction m arbitrary: x n) apply simp by force

inductive beta_m :: "nat \<Rightarrow> dB \<Rightarrow> dB \<Rightarrow> bool" where
"beta_m 0 t t" |
"r \<rightarrow>\<^sub>\<beta> s \<Longrightarrow> beta_m m s t \<Longrightarrow> beta_m (Suc m) r t"

inductive eta_m :: "nat \<Rightarrow> dB \<Rightarrow> dB \<Rightarrow> bool" where
"eta_m 0 t t" |
"r \<rightarrow>\<^sub>\<eta> s \<Longrightarrow> eta_m m s t \<Longrightarrow> eta_m (Suc m) r t"

fun list_subst :: "dB \<Rightarrow> nat list \<Rightarrow> nat \<Rightarrow> dB" where
"list_subst t [] _ = t" |
"list_subst t (x # xs) m = list_subst (t[BVar (x + m - 1) / m - 1]) xs (m - 1)"

lemma list_subst_1: "\<lbrakk>k \<le> m; length xs \<le> k\<rbrakk> \<Longrightarrow> list_subst (BVar m) xs k = BVar (m - length xs)"
  proof (induction k arbitrary: m xs)
  case 0
  then show ?case by simp
next
  case (Suc k)
  then show ?case proof (cases xs)
    case Nil
    then show ?thesis by simp
  next
    case (Cons a list)
    from this have "list_subst (BVar m) xs (Suc k) =
      list_subst (BVar m[BVar (a + Suc k - 1)/k]) list k" by fastforce
    moreover from Cons Suc have "BVar m[BVar (a + Suc k - 1) / k] = BVar (m - 1)" by fastforce
    ultimately have "list_subst (BVar m) xs (Suc k) = list_subst (BVar (m - 1)) list k" by argo
    from this Suc Cons show ?thesis by force
  qed
qed

lemma list_subst_2: "\<lbrakk>k - length xs > m; length xs \<le> k\<rbrakk> \<Longrightarrow> list_subst (BVar m) xs k = BVar m"
  proof (induction k arbitrary: m xs)
  case 0
  then show ?case by simp
next
  case (Suc k)
  then show ?case proof (cases xs)
    case Nil
    then show ?thesis by simp
  next
    case (Cons a list)
    from this have "list_subst (BVar m) xs (Suc k) =
      list_subst (BVar m[BVar (a + Suc k - 1)/k]) list k" by simp
    moreover from Cons Suc have "BVar m[BVar (a + Suc k - 1)/k] = BVar m" by fastforce
    ultimately have "list_subst (BVar m) xs (Suc k) = list_subst (BVar m) list k" by argo
    from this Suc Cons show ?thesis by simp
  qed
qed

lemma list_subst_3: "k > m \<Longrightarrow> list_subst (BVar m) (x # xs) (Suc k) = list_subst (BVar m) xs k"
  by simp

lemma list_subst_4: "k < m \<Longrightarrow> list_subst (BVar m) (x # xs) (Suc k) = list_subst (BVar (m - 1)) xs k"
  by fastforce

lemma list_subst_5: "k = m \<Longrightarrow> list_subst (BVar m) (x # xs) (Suc k) = list_subst (BVar (x + k)) xs k"
  by simp

lemma list_subst_Var: "list_subst (Var m) xs k = Var m"
  apply(induction xs arbitrary: k)
   apply simp
  by fastforce

lemma list_subst_App: "list_subst (App t1 t2) xs k = App (list_subst t1 xs k) (list_subst t2 xs k)"
  apply(induction xs arbitrary: t1 t2 k)
   apply simp
  by force

lemma list_subst_map [simp]: "list_subst (t \<degree>\<degree> ts) xs m =
  list_subst t xs m \<degree>\<degree> map (\<lambda>t. list_subst t xs m) ts" proof (induction ts arbitrary: t)
  case Nil
  then show ?case by simp
next
  case (Cons a ts)
  have "list_subst (t \<degree>\<degree> (a # ts)) xs m = list_subst (t \<degree> a \<degree>\<degree> ts) xs m" by simp
  moreover from Cons have "list_subst (t \<degree> a \<degree>\<degree> ts) xs m =
    list_subst (t \<degree> a) xs m \<degree>\<degree> map (\<lambda>t. list_subst t xs m) ts" by presburger
  ultimately have 1: "list_subst (t \<degree>\<degree> (a # ts)) xs m =
    list_subst (t \<degree> a) xs m \<degree>\<degree> map (\<lambda>t. list_subst t xs m) ts" by argo

  have "map (\<lambda>t. list_subst t xs m) (a # ts) =
    list_subst a xs m # (map (\<lambda>t. list_subst t xs m) ts)" by force
  moreover have "list_subst t xs m \<degree>\<degree> ((list_subst a xs m) # ts) =
    (list_subst t xs m) \<degree> (list_subst a xs m) \<degree>\<degree> ts" by simp
  moreover from list_subst_App have "(list_subst t xs m) \<degree> (list_subst a xs m) =
    list_subst (t \<degree> a) xs m" by presburger
  ultimately have 2: "list_subst t xs m \<degree>\<degree> map (\<lambda>t. list_subst t xs m) (a # ts) =
    list_subst (t \<degree> a) xs m \<degree>\<degree> map (\<lambda>t. list_subst t xs m) ts" by simp

  from 1 2 Cons have "list_subst (t \<degree> a) xs m \<degree>\<degree> map (\<lambda>t. list_subst t xs m) ts =
    list_subst t xs m \<degree>\<degree> map (\<lambda>t. list_subst t xs m) (a # ts)" by argo
  from this Cons show ?case by simp
qed

lemma list_subst_Abs: "m \<ge> length xs \<Longrightarrow> list_subst (Abs t) xs m = Abs (list_subst t xs (m + 1))"
  apply (induction xs arbitrary: m t)
  apply fastforce
  by simp

lemma Abs_m_list_subst: "n \<ge> length xs \<Longrightarrow>
list_subst (Abs_m m t) xs n = Abs_m m (list_subst t xs (n + m))" proof (induction xs arbitrary: t n)
  case Nil
  then show ?case by fastforce
next
  case (Cons a xs)
  then have n: "n > 0" by simp
  have 0: "list_subst (Abs_m m t) (a # xs) n =
    list_subst ((Abs_m m t)[BVar (a + n - 1)/n - 1]) xs (n - 1)" by fastforce
  with Abs_m_subst[of m t "a + n - 1" "n - 1"] have 1: "(Abs_m m t)[BVar (a + n - 1)/n - 1] =
    Abs_m m (t[BVar (a + n - 1 + m)/n - 1 + m])" by blast
  from Cons have "length xs \<le> n - 1" by simp
  with Cons have "list_subst (Abs_m m (t[BVar (a + n - 1 + m)/n - 1 + m])) xs (n - 1) =
    Abs_m m (list_subst (t[BVar (a + n - 1 + m)/n - 1 + m]) xs (n - 1 + m))" by blast
  moreover have "Abs_m m (list_subst t (a # xs) (n + m)) =
    Abs_m m (list_subst (t[BVar (a + (n + m) - 1)/n + m - 1]) xs (n + m - 1))" by simp
  moreover from n have "a + (n + m) - 1 = a + n - 1 + m" by auto
  moreover from n have "n + m - 1 = n - 1 + m" by auto
  ultimately show ?case using 0 Abs_m_subst by presburger
qed

lemma lemma15:
"\<lbrakk>length xs = m; xs = map BVar xs'\<rbrakk> \<Longrightarrow> beta_m m ((Abs_m m t) \<degree>\<degree> xs) (list_subst t xs' m)"
proof (induction m arbitrary: xs xs' t)
  case 0
  from this beta_m.intros(1) show ?case by simp
next
  case (Suc m)

  from this obtain y ys where 0: "xs = y # ys" by (meson length_Suc_conv)

  have "r \<rightarrow>\<^sub>\<beta> s \<Longrightarrow> r \<degree>\<degree> t \<rightarrow>\<^sub>\<beta> s \<degree>\<degree> t" for r s t proof (induction t arbitrary: r s)
    case Nil
    from this show ?case by simp
  next
    case (Cons a x)
    from this show ?case by simp
  qed
  moreover from 0 have "(Abs_m (m + 1) t) \<degree>\<degree> xs = (Abs (Abs_m m t) \<degree> y) \<degree>\<degree> ys" by simp
  moreover have "(Abs (Abs_m m t)) \<degree> y \<rightarrow>\<^sub>\<beta> (Abs_m m t)[y/0]" by simp
  ultimately have 1: "(Abs_m (m + 1) t) \<degree>\<degree> xs \<rightarrow>\<^sub>\<beta> (Abs_m m t)[y / 0] \<degree>\<degree> ys" by simp

  from Suc 0 obtain i where 2: "y = BVar i" by blast

  have 3: "(Abs_m m t)[BVar i / 0] = Abs_m m (t[BVar (i + m) / m])" proof (induction m arbitrary: t)
    case 0
    then show ?case by simp
  next
    case (Suc m)
    from this Abs_m show ?case by auto
  qed

  from Suc have "length xs' = Suc m" by simp
  from this obtain y' ys' where 4: "xs' = y' # ys'" by (meson length_Suc_conv)
  from this Suc 0 have "ys = map BVar ys'" by blast
  moreover from 4 Suc have "length ys' = m" by simp

  ultimately have "beta_m m ((Abs_m m (t[BVar (i + m) / m])) \<degree>\<degree> ys)
    (list_subst (t[BVar (i + m) / m]) ys' m)" using Suc 0 by simp
  moreover from 0 2 4 Suc have 
    "list_subst (t[BVar (i + m) / m]) ys' m = list_subst t xs' (m + 1)" by simp
  moreover from 1 2 3 have "(Abs_m (m + 1) t) \<degree>\<degree> xs \<rightarrow>\<^sub>\<beta> Abs_m m (t[BVar (i + m) / m]) \<degree>\<degree> ys" by simp
  ultimately show ?case using beta_m.intros(2) by simp
qed

fun downt :: "nat \<Rightarrow> nat \<Rightarrow> nat list" where
"downt 0 0 = [0]" |
"downt m n = (if m \<ge> n then m # (downt (m - 1) n) else [])"

lemma downt_length: "m \<ge> n \<Longrightarrow> length (downt m n) = m - n + 1" proof (induction m)
  case 0
  then show ?case by fastforce
next
  case (Suc m)
  have "m \<ge> n \<Longrightarrow> ?case" proof -
    assume "m \<ge> n"
    from this Suc show ?case by force
  qed
  moreover have "Suc m = n \<Longrightarrow> ?case" proof -
    assume "Suc m = n"
    from this Suc show ?case by force
  qed
  ultimately show ?case using Suc by fastforce
qed

lemma downt_last: "m \<ge> n \<Longrightarrow> last (downt m n) = n" proof (induction m)
  case 0
  then show ?case by auto
next
  case (Suc m)
  then have 0: "downt (Suc m) n = (Suc m) # (downt m n)" by simp
  have "m \<ge> n \<Longrightarrow> ?case" proof -
    assume "m \<ge> n"
    from this Suc 0 show ?case
      by (metis Suc_eq_plus1 downt_length last.simps length_0_conv nat.simps(3))
  qed
  moreover have "Suc m = n \<Longrightarrow> ?case" proof -
    assume "Suc m = n"
    from this Suc show ?case by fastforce
  qed
  ultimately show ?case using Suc by fastforce
qed

lemma downt_same: "downt i i = [i]"
  apply (cases i) by auto

lemma downt_empty: "m < n \<Longrightarrow> downt m n = []"
  using less_imp_Suc_add by force

lemma downt_list_app: "t \<degree>\<degree> (map BVar (downt m 0)) = (t \<degree>\<degree> (map BVar (downt m 1))) \<degree> BVar 0"
proof (induction m arbitrary: t)
  case 0
  then show ?case by simp
next
  case (Suc m)
  then show ?case by force
qed

lemma lemma16:
"0 \<le> i \<and> i \<le> m + j \<Longrightarrow> list_subst (BVar i) (downt m 0) (m + 1 + j) = BVar i"
(is "?a \<Longrightarrow> ?c(m)") proof -
  assume 1: "0 \<le> i \<and> i \<le> m + j"

  have "i < j \<or> (j \<le> i \<and> i \<le> m + j) \<Longrightarrow> 0 \<le> i \<and> i \<le> m + j" by fastforce

  moreover have "i < j \<Longrightarrow> ?c(m)" proof (induction m)
    case 0
    then show ?case by simp
  next
    case (Suc m)
    then show ?case by simp
  qed

  moreover have "(j \<le> i \<and> i \<le> m + j) \<Longrightarrow> ?c(m)" proof (induction m)
    case 0
    then show ?case by simp
  next
    case (Suc m)
    then have "i = m + 1 + j \<or> i < m + 1 + j \<Longrightarrow> j \<le> i \<and> i \<le> m + 1 + j" by simp

    moreover have "i = m + 1 + j \<Longrightarrow> ?c(m + 1)" proof -
      assume 2: "i = m + 1 + j"

      from this list_subst_5[of "m + 1 + j" "i" "m + 1" "downt m 0"] have
        "list_subst (BVar i) (downt (m + 1) 0) (Suc (m + 1 + j)) =
        list_subst (BVar (m + 1 + (m + 1 + j))) (downt m 0) (m + 1 + j)" by auto
      moreover have "Suc (m + 1 + j) = m + 1 + 1 + j" by simp
      ultimately have "list_subst (BVar i) (downt (m + 1) 0) (m + 1 + 1 + j) =
        list_subst (BVar (m + 1 + (m + 1 + j))) (downt m 0) (m + 1 + j)" by argo

      moreover from list_subst_1[of "m + 1 + j" "m + 1 + (m + 1 + j)" "downt m 0"] downt_length have
        "list_subst (BVar (m + 1 + (m + 1 + j))) (downt m 0) (m + 1 + j) = BVar (m + 1 + j)" by simp

      moreover have "m + 1 + j = j + 1 + m" by presburger

      ultimately show "?c(m + 1)" using 2 by argo
    qed

    moreover have "i < m + j \<Longrightarrow> ?c(m + 1)" proof -
      assume 2: "i < m + j"

      from this list_subst_3[of "m + 1 + j" "i" "m + 1" "downt m 0"] have
        "list_subst (BVar i) (downt (m + 1) 0) (Suc (m + 1 + j)) =
        list_subst (BVar i) (downt m 0) (m + 1 + j)" by auto

      from this Suc 2 show ?thesis by simp
    qed

    ultimately show ?case using Suc by fastforce
  qed

  ultimately show ?thesis using 1 by linarith
qed

lemma lemma17: "\<lbrakk>length xs = m + 1; xs = map BVar xs'; 0 \<le> i \<and> i \<le> m\<rbrakk>
\<Longrightarrow> list_subst (BVar i) xs' (m + 1) = xs ! (m - i)" proof (induction m arbitrary: xs xs')
  case 0
  then have "i = 0" by fastforce
  from 0 have "length xs' = 1" by simp
  from this obtain y' ys' where "xs' = y' # ys'" by (metis One_nat_def Suc_length_conv)
  from this 0 list_subst_4[of "0" "0" "y'" "ys'"] show ?case by auto
next
  case (Suc m)
  from this have "length xs' > 0" by fastforce
  from this obtain y' ys' where Cons': "xs' = y' # ys'" using id_take_nth_drop by fastforce
  from this Suc have 2: "length ys' = m + 1" by force

  from Suc Cons' obtain y ys where Cons: "xs = y # ys" by auto
  from this Cons' Suc have 3: "y = BVar y'" by blast

  have "i = m + 1 \<or> i \<le> m \<Longrightarrow> i \<le> Suc m" by auto

  moreover have "i = m + 1 \<Longrightarrow> ?case" proof -
    assume 1: "i = m + 1"

    from 1 Cons' list_subst_5 have
      "list_subst (BVar i) xs' (m + 2) = list_subst (BVar (y' + m + 1)) ys' (m + 1)" by fastforce
    moreover from 2 list_subst_1[of "m + 1" "y' + m + 1" "ys'"] have
      "list_subst (BVar (y' + m + 1)) ys' (m + 1) = BVar y'" by simp
    ultimately show ?case using Cons 1 3 by auto
  qed

  moreover from Suc have "i \<le> m \<Longrightarrow> ?case" proof -
    assume 1: "i \<le> m"
    from this Cons' list_subst_3 have
      "list_subst (BVar i) xs' (Suc m + 1) = list_subst (BVar i) ys' (m + 1)" by fastforce

    from this Suc 1 Cons show ?case by force
  qed

  ultimately show "?case" using Suc by fastforce
qed

inductive no_Abs :: "dB \<Rightarrow> bool" where
"no_Abs (BVar _)" |
"no_Abs (Var _)" |
"\<lbrakk>no_Abs t1; no_Abs t2\<rbrakk> \<Longrightarrow> no_Abs (App t1 t2)"

fun max_BVar :: "dB \<Rightarrow> nat" where
"max_BVar (BVar i) = i" |
"max_BVar (Var _) = 0" |
"max_BVar (App t1 t2) = max (max_BVar t1) (max_BVar t2)" |
"max_BVar (Abs t) = max_BVar t"

fun replace :: "dB \<Rightarrow> nat list \<Rightarrow> dB" where
"replace (BVar i) xs = BVar (xs ! (length xs - i - 1))" |
"replace (Var i) _ = Var i" |
"replace (App t1 t2) xs = App (replace t1 xs) (replace t2 xs)" |
"replace (Abs t) xs = Abs (replace t xs)"

lemma lemma18: "\<lbrakk>no_Abs t; max_BVar t \<le> m; xs = map BVar xs'; length xs = m + 1\<rbrakk> \<Longrightarrow>
beta_m (m + 1) ((Abs_m (m + 1) t) \<degree>\<degree> xs) (replace t xs')" (is "\<lbrakk>?a1; ?a2; ?a3; ?a4\<rbrakk> \<Longrightarrow> ?c") proof -
  assume a: ?a1 ?a2 ?a3 ?a4
  from this lemma15 have "beta_m (m + 1) ((Abs_m (m + 1) t) \<degree>\<degree> xs) (list_subst t xs' (m + 1))"
    by blast
  moreover from a have "list_subst t xs' (m + 1) = replace t xs'" proof (induction t)
    case (1 uu)
    then show ?case proof (induction m arbitrary: xs xs')
      case 0
      moreover from this obtain y' ys' where Cons: "xs' =  y' # ys'"
        by (metis Suc_eq_plus1 length_Suc_conv length_map)
      moreover from this 0 have "list_subst t xs' (0 + 1) = t[BVar y'/0]" by simp
      ultimately show ?case by simp
    next
      case (Suc m)

      from this obtain y' ys' where Cons': "xs' =  y' # ys'"
        by (metis Suc_eq_plus1 Suc_length_conv length_map)
      from this Suc have 2: "list_subst (BVar uu) xs' (Suc m + 1) =
        list_subst (BVar uu[BVar (y' + m + 1)/m + 1]) ys' (m + 1)" by force

      from Cons' Suc have 3: "length ys' = m + 1" by simp

      from Suc have 4: "uu \<le> m + 1" by auto
      from this have "uu < m + 1 \<or> uu = m + 1 \<Longrightarrow> True" by force
      moreover have "uu = m + 1 \<Longrightarrow> ?case" proof -
        assume 5: "uu = m + 1"
        then have "BVar uu[BVar (y' + m + 1)/m + 1] = BVar (y' + m + 1)" by simp
        from this 2 have "list_subst (BVar uu) xs' (Suc m + 1) =
          list_subst (BVar (y' + m + 1)) ys' (m + 1)" by argo
        moreover from list_subst_1 3 have "list_subst (BVar (y' + m + 1)) ys' (m + 1) = BVar y'"
          by auto
        moreover from Cons' 5 3 have "replace (BVar uu) xs' = BVar y'" by auto
        ultimately show ?thesis by presburger
      qed

      moreover have "uu < m + 1 \<Longrightarrow> ?case" proof -
        assume 5: "uu < m + 1"
        then have "BVar uu[BVar (y' + m + 1)/m + 1] = BVar uu" by fastforce
        from this 2 have "list_subst (BVar uu) xs' (Suc m + 1) =
          list_subst (BVar uu) ys' (m + 1)" by presburger
        moreover from 5 have "max_BVar (BVar uu) < m + 1" by simp
        ultimately have 6: "list_subst (BVar uu) xs' (Suc m + 1) = replace (BVar uu) ys'"
          using Suc 3 by simp

        from 5 Cons' have "replace (BVar uu) xs' = BVar (xs' ! (length xs' - uu - 1))" by simp
        moreover from 5 Cons' Suc have "xs' ! (length xs' - uu - 1) = ys' ! (length ys' - uu - 1)"
          by simp
        ultimately have "replace (BVar uu) xs' = replace (BVar uu) ys'" by force

        from 6 this show ?case by presburger
      qed
      ultimately show ?case using 4 by linarith
    qed
  next
    case (2 uv)
    from this list_subst_Var show ?case by force
  next
    case (3 t1 t2)
    from list_subst_App have "list_subst (t1 \<degree> t2) xs' (m + 1) = (list_subst t1 xs' (m + 1)) \<degree>
      (list_subst t2 xs' (m + 1))" by presburger
    from this 3 show ?case by simp
  qed

  ultimately show ?thesis by force
qed

fun no_loose_bound :: "dB \<Rightarrow> nat \<Rightarrow> bool" where
"no_loose_bound (BVar i) m = (i < m)" |
"no_loose_bound (Var _) _ = True" |
"no_loose_bound (App t1 t2) m = ((no_loose_bound t1 m) \<and> (no_loose_bound t2 m))" |
"no_loose_bound (Abs t) m = no_loose_bound t (m + 1)"

lemma loose_bound_free: "no_loose_bound t m = (\<forall>k. k \<ge> m \<longrightarrow> \<not>(free t k))"
proof (induction t arbitrary: m)
  case (BVar x)
  then show ?case using not_less by auto
next
  case (Var x)
  then show ?case by force
next
  case (App t1 t2)
  then show ?case by auto
next
  case (Abs t)
  show ?case proof
    from Abs show "no_loose_bound (Abs t) m \<Longrightarrow> \<forall>k\<ge>m. \<not> free (Abs t) k" by auto
  next
    show "\<forall>k\<ge>m. \<not> free (Abs t) k \<Longrightarrow> no_loose_bound (Abs t) m" proof -
      assume "\<forall>k\<ge>m. \<not> free (Abs t) k"
      then have "\<forall>k\<ge>m. \<not> free t (k + 1)" by simp
      then have "\<forall>k. k \<ge> m + 1 \<longrightarrow> \<not> free t k"
        by (metis Suc_eq_plus1 discrete le_add1 less_imp_Suc_add)
      with Abs show "no_loose_bound (Abs t) m" by auto
    qed
  qed
qed

lemma loose_bound_subst: "\<lbrakk>no_loose_bound s m; n \<ge> m\<rbrakk> \<Longrightarrow> s[x / n] = s"
  apply (induction s arbitrary: n m x) apply simp_all by force

lemma loose_bound_list_subst: "\<lbrakk>no_loose_bound s 0\<rbrakk> \<Longrightarrow> list_subst s xs m = s"
proof (induction xs arbitrary: s m)
  case Nil
  then show ?case by fastforce
next
  case (Cons a xs)
  have 0: "list_subst s (a # xs) m = list_subst (s[BVar (a + m - 1)/m - 1]) xs (m - 1)" by auto
  from Cons loose_bound_subst have "s[BVar (a + m - 1)/m - 1] = s" by blast
  moreover from this Cons have "no_loose_bound (s[BVar (a + m - 1)/m - 1]) 0" by argo
  ultimately have "list_subst (s[BVar (a + m - 1)/m - 1]) xs (m - 1) = s" using Cons by presburger
  from this 0 show ?case by presburger
qed

lemma loose_bound_Abs_m: "no_loose_bound (Abs_m m t) x = no_loose_bound t (x + m)"
  apply(induction m arbitrary: x)
   apply fastforce
  by force

fun list_max :: "nat list \<Rightarrow> nat" where
"list_max [] = 0" |
"list_max (x # xs) = max x (list_max xs)"

lemma lemma19: "\<lbrakk>no_loose_bound s 0; list_max zs' \<le> m; xs = map BVar xs'; length xs = m + 1;
zs = map BVar zs'\<rbrakk> \<Longrightarrow>
beta_m (m + 1) ((Abs_m (m + 1) (s \<degree>\<degree> zs)) \<degree>\<degree> xs) (s \<degree>\<degree> map (\<lambda>z. xs ! (m - z)) zs')"
(is "\<lbrakk>?a1; ?a2; ?a3; ?a4; ?a5\<rbrakk> \<Longrightarrow> ?c") proof -
  assume a: ?a1 ?a2 ?a3 ?a4 ?a5
  from this lemma15 have
    "beta_m (m + 1) ((Abs_m (m + 1) (s \<degree>\<degree> zs)) \<degree>\<degree> xs) (list_subst (s \<degree>\<degree> zs) xs' (m + 1))" by fast

  moreover have "list_subst (s \<degree>\<degree> zs) xs' (m + 1) = s \<degree>\<degree> map (\<lambda>z. xs ! (m - z)) zs'" proof -
    from list_subst_map have "list_subst (s \<degree>\<degree> zs) xs' (m + 1) =
      list_subst s xs' (m + 1) \<degree>\<degree> map (\<lambda>z. list_subst z xs' (m + 1)) zs" by presburger

    moreover from a loose_bound_list_subst have "list_subst s xs' (m + 1) = s" by blast

    moreover from a have "map (\<lambda>z. list_subst z xs' (m + 1)) zs = map (\<lambda>z. xs ! (m - z)) zs'"
    proof (induction zs arbitrary: zs')
      case Nil
      from this show ?case by auto
    next
      case (Cons a zs)
      from this obtain y' ys' where 0: "zs' = y' # ys'" by blast

      have 1: "map (\<lambda>z. list_subst z xs' (m + 1)) (a # zs) =
        list_subst a xs' (m + 1) # map (\<lambda>u. list_subst u xs' (m + 1)) zs" by simp

      from Cons obtain i where 3: "a = BVar i" by fast
      from this Cons have "i \<le> m" by force
      from this have "list_subst (BVar i) xs' (m + 1) = xs ! (m - i)" using Cons(4-5)
      proof (induction xs' arbitrary: xs m)
        case Nil
        then show ?case by simp
      next
        case (Cons a xs')
        from this have 0: "length xs' = m" by simp
        from Cons obtain y ys where 3: "xs = y # ys" by auto
        have 1: "list_subst (BVar i) (a # xs') (m + 1) =
          list_subst (BVar i[BVar (a + m)/m]) xs' m" by fastforce
        have "i = m \<Longrightarrow> ?case" proof -
          assume 2: "i = m"
          from this have "BVar i[BVar (a + m)/m] = BVar (a + m)" by simp
          moreover from this list_subst_1 0 have "list_subst (BVar (a + m)) xs' m = BVar a" by simp
          ultimately have "list_subst (BVar i) (a # xs') (m + 1) = BVar a" using 1 by argo
          moreover from 2 Cons have "xs ! (m - i) = BVar a" by force
          ultimately show ?thesis by argo
        qed
        moreover have "i < m \<Longrightarrow> ?case" proof -
          assume 2: "i < m"
          from this have "BVar i[BVar (a + m)/m] = BVar i" by simp
          from this 1 have
            5: "list_subst (BVar i) (a # xs') (m + 1) = list_subst (BVar i) xs' m" by presburger

          from 2 have 4: "m > 0" by simp

          from Cons 3 have "ys = map BVar xs'" by force
          moreover from Cons 3 have "length ys = m" by auto
          ultimately have "list_subst (BVar i) xs' m = ys ! (m - 1 - i)"
            using Cons(1)[of "m - 1" "ys"] 3 2 4 by auto

          moreover from 2 3 have "ys ! (m - 1 - i) = xs ! (m - i)" by simp
          ultimately show ?thesis using 5 by presburger
        qed
        moreover have "i = m \<or> i < m \<Longrightarrow> i \<le> m" by fastforce
        ultimately show ?case using Cons by linarith
      qed

      from this 1 3 have 2: "map (\<lambda>z. list_subst z xs' (m + 1)) (a # zs) =
        xs ! (m - i) # map (\<lambda>u. list_subst u xs' (m + 1)) zs" by argo

      from 0 have "map (\<lambda>z. xs ! (m - z)) zs' = xs ! (m - y') # map (\<lambda>z. xs ! (m - z)) ys'" by simp
      moreover from Cons 0 3 have "i = y'" by fastforce
      moreover from Cons 0 have "zs = map BVar ys'" by fast
      moreover from Cons 0 have "list_max ys' \<le> m" by simp
      ultimately show ?case using 2 3 Cons by metis
    qed

    ultimately show ?thesis by presburger
  qed

  ultimately show ?c by argo
qed

(* lemma 20 (as stated in Grobauer) for m = 0 *)
thm eta_m.intros(1)

lemma lemma20: "\<lbrakk>no_loose_bound t 0\<rbrakk> \<Longrightarrow>
eta_m (m + 1) (Abs_m (m + 1) (t \<degree>\<degree> (map BVar (downt m 0)))) t" proof (induction m)
  case 0
  fix dummy
  have "Abs_m (0 + 1) (t \<degree>\<degree> map BVar (downt 0 0)) = Abs (t \<degree> BVar 0)" by auto
  moreover from 0 loose_bound_free have "\<not>(free t 0)" by simp
  ultimately have "Abs_m (0 + 1) (t \<degree>\<degree> map BVar (downt 0 0)) \<rightarrow>\<^sub>\<eta> t[dummy / 0]" by fastforce
  moreover from 0 loose_bound_subst have "t[dummy / 0] = t" by blast
  ultimately show ?case using eta_m.intros by auto
next
  case (Suc m)
  from downt_list_app have 0: "t \<degree>\<degree> (map BVar (downt (Suc m) 0)) =
    (t \<degree>\<degree> (map BVar (downt (Suc m) 1))) \<degree> BVar 0" by fast

  from list_application_free have "free (t \<degree>\<degree> (map BVar (downt (Suc m) 1))) 0 =
    free t 0 \<or> any (map (\<lambda>x. free x 0) (map BVar (downt (Suc m) 1)))" by blast
  moreover from Suc loose_bound_free have "\<not> (free t 0)" by simp
  moreover have "\<not> (any (map (\<lambda>x. free x 0) (map BVar (downt (Suc m) 1))))"
  proof (induction m)
    case 0
    then show ?case by force
  next
    case (Suc m)
    then show ?case by simp
  qed
  ultimately have 1: "\<not> (free (t \<degree>\<degree> (map BVar (downt (Suc m) 1))) 0)" by blast

  fix dummy
  from Abs_m have "Abs_m (Suc m + 1) (t \<degree>\<degree> map BVar (downt (Suc m) 0)) =
    (Abs_m (m + 1) (Abs (t \<degree>\<degree> map BVar (downt (Suc m) 0))))" by simp
  from this 0 1 Abs_m_eta eta have "Abs_m (Suc m + 1) (t \<degree>\<degree> map BVar (downt (Suc m) 0)) \<rightarrow>\<^sub>\<eta>
    Abs_m (m + 1) ((t \<degree>\<degree> (map BVar (downt (Suc m) 1)))[dummy/0])" by metis

  moreover have "(t \<degree>\<degree> (map BVar (downt (Suc m) 1)))[dummy/0] =
     t[dummy / 0] \<degree>\<degree> (map BVar (downt m 0))" proof (induction m arbitrary: t)
    case 0
    then show ?case by force
  next
    case (Suc m)
    have "map BVar (downt (Suc (Suc m)) 1) = BVar (Suc (Suc m)) # map BVar (downt (Suc m) 1)"
      by auto
    from this have "t \<degree>\<degree> (map BVar (downt (Suc (Suc m)) 1)) =
      (t \<degree> BVar (Suc (Suc m))) \<degree>\<degree> (map BVar (downt (Suc m) 1))" by simp

    moreover from Suc have "((t \<degree> BVar (Suc (Suc m))) \<degree>\<degree> (map BVar (downt (Suc m) 1)))[dummy / 0] =
      (t \<degree> BVar (Suc (Suc m)))[dummy/0] \<degree>\<degree> (map BVar (downt m 0))" by blast

    moreover have "(t \<degree> BVar (Suc (Suc m)))[dummy/0] = t[dummy/0] \<degree> (BVar (Suc m))" by simp

    moreover have "t[dummy/0] \<degree> BVar (Suc (Suc m)) \<degree>\<degree> (map BVar (downt (Suc m) 0)) =
      t[dummy/0] \<degree>\<degree> (map BVar (downt (Suc (Suc m)) 0))" by fastforce

    ultimately show ?case by fastforce
  qed

  moreover from Suc loose_bound_subst have "t[dummy / 0] = t" by blast

  ultimately show ?case using Suc eta_m.intros(2) Suc_eq_plus1 diff_Suc_1 by metis
qed

lemma lemma21': "no_loose_bound t (m + 1 + j) \<Longrightarrow> list_subst t (downt m 0) (m + 1 + j) = t"
proof (induction t arbitrary: j)
  case (BVar x)
  from this have "x \<le> m + 1 + j - 1" by auto
  from this lemma16 show ?case by force
next
  case (Var x)
  from this list_subst_Var show ?case by presburger
next
  case (App t1 t2)
  moreover from this have "no_loose_bound t1 (m + 1 + j)" by force
  moreover from App have "no_loose_bound t2 (m + 1 + j)" by force
  ultimately show ?case using list_subst_App by auto
next
  case (Abs t)
  from this have "no_loose_bound t (m + 1 + j + 1)" by force
  from this Abs(1)[of "j + 1"] have "list_subst t (downt m 0) (m + 1 + j + 1) = t" by force

  moreover from list_subst_Abs downt_length have "list_subst (Abs t) (downt m 0) (m + 1 + j) =
    Abs (list_subst t (downt m 0) (m + 1 + j + 1))" by simp

  ultimately show ?case by argo
qed

(* lemma 21 (as stated in Grobauer) for m = 0 *)
thm beta_m.intros(1)

lemma lemma21:
"no_loose_bound (Abs_m (m + 1) t) 0 \<Longrightarrow>
beta_m (m + 1) ((Abs_m (m + 1) t) \<degree>\<degree> (map BVar (downt m 0))) t" proof -
  assume "no_loose_bound (Abs_m (m + 1) t) 0"
  from this loose_bound_Abs_m have "no_loose_bound t (m + 1)" by fastforce

  moreover from lemma15 downt_length have "beta_m (m + 1)
    ((Abs_m (m + 1) t) \<degree>\<degree> (map BVar (downt m 0))) (list_subst t (downt m 0) (m + 1))"
    by (metis diff_zero le0 length_map)

  ultimately show ?thesis using lemma21'[of "t" "m" "0"] by auto
qed

fun symcl :: "(dB \<Rightarrow> dB \<Rightarrow> bool) \<Rightarrow> (dB \<Rightarrow> dB \<Rightarrow> bool)" where
"symcl r = (\<lambda>x y. (r x y \<or> r y x))"

lemma symcl_symp: "symp (symcl r)" proof
  fix a b
  assume "symcl r a b"
  then show "symcl r b a" by fastforce
qed

abbreviation "closure r \<equiv> (symcl r)\<^sup>*\<^sup>*"

lemma closure_symmetric: "closure r a b \<Longrightarrow> closure r b a"
  by (metis symcl.simps sympD sympI symp_rtranclp)

abbreviation "eta_red t \<equiv> \<not>(\<exists>t'. eta t t')"

inductive gamma :: "dB \<times> nat list \<Rightarrow> dB \<times> nat list \<Rightarrow> bool" where
"gamma (Abs t, x # xs) (t[BVar x / 0], xs)"

lemma App_eq_foldl_conv2:
  "(t \<degree>\<degree> ts = r \<degree> s) = (if ts = [] then r \<degree> s = t else \<exists>ss. ts = ss @ [s] \<and> r = t \<degree>\<degree> ss)"
  by (rule trans[OF iffI App_eq_foldl_conv]; erule sym)

lemma eta_map_BVarD: "t \<degree>\<degree> map BVar xs \<rightarrow>\<^sub>\<eta> z \<Longrightarrow> \<exists>u. z = u \<degree>\<degree> map BVar xs \<and> t \<rightarrow>\<^sub>\<eta> u"
  apply (induct "t \<degree>\<degree> map BVar xs" z arbitrary: t xs rule: eta.induct)
     apply (auto simp: App_eq_foldl_conv map_eq_append_conv split: if_splits)
  apply (metis list.simps(8) list.simps(9))
  apply (metis list.simps(8) list.simps(9))
  done

lemma subst_BVar_eq_BVar_conv: "k < i \<Longrightarrow> k \<noteq> j \<Longrightarrow> t[BVar j/i] = BVar k \<longleftrightarrow> t = BVar k"
  by (cases t) (auto simp: subst_BVar)

lemma subst_BVar_etaD: "t[BVar x/i] \<rightarrow>\<^sub>\<eta> u \<Longrightarrow> \<exists>v. u = v[BVar x / i] \<and> t \<rightarrow>\<^sub>\<eta> v"
  apply (induct t arbitrary: u x i)
     apply (auto simp: subst_BVar split: if_splits)
     apply force
    apply force
  subgoal for t x i s dummy
    apply (erule thin_rl)
    apply (cases t)
       apply (auto simp: subst_BVar subst_BVar_eq_BVar_conv split: if_splits)
    apply (rule exI, rule conjI[OF _ eta[of _ dummy]])
     apply (auto simp: subst_subst[symmetric])
    done
  apply force
  done

lemma subst_BVar_betaD: "t[BVar x/i] \<rightarrow>\<^sub>\<beta> u \<Longrightarrow> \<exists>v. u = v[BVar x / i] \<and> t \<rightarrow>\<^sub>\<beta> v"
  apply (induct t arbitrary: u x i)
     apply (auto simp: subst_BVar split: if_splits)
  subgoal for t1 t2 x i s
    apply (cases t1)
       apply (auto simp: subst_BVar subst_BVar_eq_BVar_conv split: if_splits)
    apply (rule exI, rule conjI[OF _ beta.beta])
     apply (auto simp: subst_subst[symmetric])
    done
    apply force
   apply force
  apply force
  done

abbreviation "\<beta>\<eta> \<equiv> (sup beta eta)"
abbreviation "\<beta>\<eta>cl \<equiv> \<beta>\<eta>\<^sup>*\<^sup>*"

lemma subst_eta_red: "\<lbrakk>u = t[BVar x / i]; eta_red u\<rbrakk> \<Longrightarrow> eta_red t"
  apply (induct t arbitrary: u x i)
     apply (auto simp: subst_BVar split: if_splits)
  apply fast
    apply fast
  apply force
  by blast

lemma subst_BVar_betaetaD: "\<lbrakk>\<beta>\<eta> (t[BVar x/i]) u\<rbrakk> \<Longrightarrow>
\<exists>v. u = v[BVar x / i] \<and> \<beta>\<eta> t v"
  by (metis subst_BVar_betaD subst_BVar_etaD sup2E sup2I1 sup2I2)

lemma eta_list[simp, intro]: "t \<rightarrow>\<^sub>\<eta> u \<Longrightarrow> t \<degree>\<degree> ts \<rightarrow>\<^sub>\<eta> u \<degree>\<degree> ts"
  by (induct ts arbitrary: t u) auto

lemma betaeta_subst_BVar:
   "\<lbrakk>\<beta>\<eta>cl (t[BVar x / 0]) u\<rbrakk> \<Longrightarrow>
   \<exists>u'. u = u'[BVar x / 0] \<and> \<beta>\<eta>cl (Abs t \<degree> BVar x) (Abs u' \<degree> BVar x)"
proof (induct "t[BVar x / 0]" arbitrary: t rule: converse_rtranclp_induct)
  case base
  then show ?case by auto
next
  case (step z)
  from step(1) obtain t' where "z = t'[BVar x/0]" "\<beta>\<eta> t t'"
    by (blast dest!: subst_BVar_betaetaD)
  with step(3)[of t'] obtain u' where
    "u = u'[BVar x/0] \<and> \<beta>\<eta>cl (Abs t' \<degree> BVar x) (Abs u' \<degree> BVar x)" by blast
  moreover from \<open>\<beta>\<eta> t t'\<close> have "\<beta>\<eta>cl (Abs t \<degree> BVar x) (Abs t' \<degree> BVar x)"
    by (auto simp: r_into_rtranclp)
  ultimately show ?case
    by (intro exI[of _ u']) auto
qed

lemma betaeta_Abs: "\<beta>\<eta>cl t t' \<Longrightarrow> \<beta>\<eta>cl (Abs t) (Abs t')" proof (induction rule: rtranclp.induct)
  case (rtrancl_refl a)
  then show ?case by blast
next
  case (rtrancl_into_rtrancl a b c)
  from this have "\<beta>\<eta> (Abs b) (Abs c)" by blast
  from this rtrancl_into_rtrancl show ?case by (simp add: rtranclp.rtrancl_into_rtrancl)
qed

lemma subst_BVar_betaetacl: "\<lbrakk>\<beta>\<eta>cl (t[BVar x / i]) u\<rbrakk> \<Longrightarrow>
\<exists>v. u = v[BVar x / i] \<and> \<beta>\<eta>cl t v"
proof (induction "(t[BVar x / i])" arbitrary: t rule: converse_rtranclp_induct)
  case base
  then show ?case by blast
next
  case (step z)
  from this step show ?case by (metis converse_rtranclp_into_rtranclp subst_BVar_betaetaD)
qed

lemma list_application_eta_red: "\<lbrakk>s = t \<degree>\<degree> map BVar xs; eta_red s\<rbrakk> \<Longrightarrow> eta_red t"
  apply (induction t arbitrary: s)
     apply force
    apply force
  apply blast
  by force

lemma lemma22': "\<lbrakk>\<beta>\<eta>cl (t \<degree>\<degree> (map BVar xs)) s\<rbrakk> \<Longrightarrow>
  \<exists>t' s' ys. \<beta>\<eta>cl t t' \<and> gamma\<^sup>*\<^sup>* (t', xs) (s', ys) \<and> s' \<degree>\<degree> (map BVar ys) = s"
proof (induction "t \<degree>\<degree> (map BVar xs)" arbitrary: xs t rule: converse_rtranclp_induct)
  case base
  then show ?case by auto
next
  case (step z)
  have "\<exists>t''. z = t'' \<degree>\<degree> map BVar xs \<and> \<beta>\<eta> t t'' \<Longrightarrow> ?case" proof -
    assume "\<exists>t''. z = t'' \<degree>\<degree> map BVar xs \<and> \<beta>\<eta> t t''"
    then obtain t'' where 0: "z = t'' \<degree>\<degree> map BVar xs \<and> \<beta>\<eta> t t''" by presburger
    from this step have "\<exists>t' s' ys. \<beta>\<eta>cl t'' t' \<and> gamma\<^sup>*\<^sup>* (t', xs) (s', ys) \<and> s' \<degree>\<degree> map BVar ys = s"
      by blast
    moreover from 0 have "\<beta>\<eta>cl t'' t' \<Longrightarrow> \<beta>\<eta>cl t t'" for t'
      by (simp add: "0" converse_rtranclp_into_rtranclp)
    ultimately show ?case by fast
  qed
  moreover have "\<exists>t'' y' ys'. z = t''[BVar y' / 0] \<degree>\<degree> map BVar ys' \<and> t = Abs t'' \<and> xs = y' # ys'
    \<Longrightarrow> ?case" proof -
    assume "\<exists>t'' y' ys'. z = t''[BVar y' / 0] \<degree>\<degree> map BVar ys' \<and> t = Abs t'' \<and> xs = y' # ys'"
    then obtain t'' y' ys' where
      0: "z = t''[BVar y' / 0] \<degree>\<degree> map BVar ys' \<and> t = Abs t'' \<and> xs = y' # ys'" by blast

    from this step(3)[of "t''[BVar y' / 0]" ys'] step obtain t' s' ys where 1:
      "\<beta>\<eta>cl (t''[BVar y'/0]) t' \<and> gamma\<^sup>*\<^sup>* (t', ys') (s', ys) \<and> s' \<degree>\<degree> map BVar ys = s" by presburger

    from this betaeta_subst_BVar[of t'' y' t'] step obtain u' where 2:
      "t' = u'[BVar y'/0] \<and> \<beta>\<eta>cl (Abs t'' \<degree> BVar y') (Abs u' \<degree> BVar y')" by blast

    from 1 2 subst_BVar_betaetacl[of t'' y' 0 "u'[BVar y'/0]"] obtain v where 3:
      "u'[BVar y'/0] = v[BVar y'/0] \<and> \<beta>\<eta>cl t'' v" by fast

    from this 0 betaeta_Abs have 4: "\<beta>\<eta>cl t (Abs v)" by presburger

    from 0 gamma.intros have "gamma (Abs v, xs) (v[BVar y' / 0], ys')" by presburger
    moreover from 1 2 3 have "gamma\<^sup>*\<^sup>* (v[BVar y' / 0], ys') (s', ys)" by argo
    ultimately have 5: "gamma\<^sup>*\<^sup>* (Abs v, xs) (s', ys)" by fastforce

    from 1[THEN conjunct2[THEN conjunct2]] 4 5 show ?case by metis
  qed
  moreover from step(1) have "(\<exists>t''. z = t'' \<degree>\<degree> map BVar xs \<and> \<beta>\<eta> t t'') \<or>
    (\<exists>t'' y' ys'. z = t''[BVar y' / 0] \<degree>\<degree> map BVar ys' \<and> t = Abs t'' \<and> xs = y' # ys')" proof -

    have "(t \<degree>\<degree> map BVar xs) \<rightarrow>\<^sub>\<beta> z \<Longrightarrow> ?thesis" proof -
      assume "(t \<degree>\<degree> map BVar xs) \<rightarrow>\<^sub>\<beta> z"
      from this show ?thesis proof cases
        case (beta u v)
        have "xs = [] \<Longrightarrow> ?thesis" proof -
          assume 0: "xs = []"
          from this beta have "t = Abs u \<degree> v" by fastforce
          from this beta 0 have "z = u[v / 0] \<degree>\<degree> map BVar xs \<and> beta t (u[v / 0])" by force
          then show ?thesis by blast
        qed
        moreover have "xs = [x] \<Longrightarrow> ?thesis" for x proof -
          assume 0: "xs = [x]"
          from this beta have "t = Abs u \<and> BVar x = v" by simp
          moreover from 0 have "xs = x # []" by presburger
          ultimately show ?thesis using beta by auto
        qed
        moreover have "xs = (x # y # zs) \<Longrightarrow> False" for x y zs proof -
          assume 0: "xs = (x # y # zs)"
          from this beta have "t \<degree>\<degree> map BVar xs = t \<degree> BVar x \<degree> BVar y \<degree>\<degree> map BVar zs" by auto
          moreover have "Abs u \<degree> v \<noteq> t \<degree> BVar x \<degree> BVar y \<degree>\<degree> map BVar zs"
            by (simp add: App_eq_foldl_conv)
          ultimately show ?thesis using beta by force
        qed
        ultimately show ?thesis by (meson remdups_adj.cases)
      next
        case (appL u v w)
        then show ?thesis proof (induction xs arbitrary: t)
          case Nil
          then show ?case by simp
        next
          case (Cons a xs)
          then show ?case by auto
        qed
      next
        case (appR u v w)
        then have "\<exists>x. u = BVar x \<or> xs = []" proof (induction xs arbitrary: t)
          case Nil
          then show ?case by blast
        next
          case (Cons a xs)
          then show ?case by fastforce
        qed
        moreover have "\<exists>x. u = BVar x \<Longrightarrow> ?thesis" proof -
          assume "\<exists>x. u = BVar x"
          then obtain x where "u = BVar x" by blast
          from this appR have "BVar x \<rightarrow>\<^sub>\<beta> v" by fast
          then have False by fast
          then show ?thesis by fast
        qed
        moreover have "xs = [] \<Longrightarrow> ?thesis" proof -
          assume 0: "xs = []"
          from this appR have "t = w \<degree> u" by simp
          moreover from this appR 0 have "z = w \<degree> v \<and> beta (w \<degree> u) (w \<degree> v)" by fast
          ultimately show ?thesis using 0 by auto
        qed
        ultimately show ?thesis by fast
      next
        case (abs s t)
        then show ?thesis by fast
      qed
    qed

    moreover have "(t \<degree>\<degree> map BVar xs) \<rightarrow>\<^sub>\<eta> z \<Longrightarrow> ?thesis" using eta_map_BVarD by blast

    ultimately show ?thesis using step(1) by fast
  qed

  ultimately show ?case by blast
qed

lemma gamma_eta_red: "gamma (t, xs) (s, ys) \<Longrightarrow> eta_red t \<Longrightarrow> eta_red s"
  by (induct t xs s ys rule: gamma.induct[split_format(complete)]) (auto dest: subst_BVar_etaD)

lemma gamma_rtranclp_eta_red: "gamma\<^sup>*\<^sup>* (t, xs) (s, ys) \<Longrightarrow> eta_red t \<Longrightarrow> eta_red s"
  by (induct "(t, xs)" "(s, ys)" arbitrary: t xs s ys rule: rtranclp.induct)
    (auto dest: gamma_eta_red)

fun gamma_star :: "(dB \<times> nat list) \<Rightarrow> (dB \<times> nat list) \<Rightarrow> bool" where
"gamma_star (t, xs) (u, ys) =
(\<exists>t' zs. xs = zs @ ys \<and> t = Abs_m (length zs) t' \<and> u = list_subst t' zs (length zs))"

lemma gamma_star_1: "gamma (t, xs) (u, ys) \<Longrightarrow> gamma_star (t, xs) (u, ys)" proof -
  assume 0: "gamma (t, xs) (u, ys)"

  from 0 gamma.simps obtain t' where "t = Abs t'" by auto
  moreover from 0 gamma.simps obtain x where "xs = x # ys" by auto
  ultimately have "xs = [x] @ ys \<and> t = Abs t' \<and> u = t'[BVar x/0]" using 0 gamma.simps by simp
  then have "xs = [x] @ ys \<and> t = Abs_m (length [x]) t' \<and> u = list_subst t' [x] (length [x])"
    by auto
  with gamma_star.simps show ?thesis by blast
qed

lemma subst_Abs: "Abs t = t'[BVar x/i] \<Longrightarrow> \<exists>t''. t' = Abs t''"
  apply (induction t')
  apply (metis dB.distinct(5) subst_BVar)
  apply fastforce
  apply simp
  by blast

lemma subst_Abs_m: "\<lbrakk>t = Abs_m m t'; t = t''[BVar x/i]\<rbrakk> \<Longrightarrow> \<exists>t'''. t'' = Abs_m m t'''"
proof (induction m arbitrary: t t'' x i)
  case 0
  then show ?case by auto
next
  case (Suc m)
  from this(2) obtain t1 where t1: "t1 = Abs_m m t' \<and> t = Abs t1" by auto
  with Suc(3) have 0: "Abs t1 = t''[BVar x/i]" by argo
  with subst_Abs obtain t2 where t2: "t'' = Abs t2" by blast
  have "(Abs t2)[BVar x/i] = Abs (t2[BVar (x + 1)/i + 1])" by auto
  with 0 t2 have "t1 = t2[BVar (x + 1)/i + 1]" by simp
  with Suc(1)[of t1 t2 "x + 1" "i + 1"] t1 have "\<exists>t'''. t2 = Abs_m m t'''" by argo
  with t2 show ?case by simp
qed

lemma Abs_m_eq: "\<lbrakk>t = Abs_m m t'; t = Abs_m m t''\<rbrakk> \<Longrightarrow> t' = t''"
  apply (induction m arbitrary: t)
  apply simp
  by simp

lemma gamma_star_2: "\<lbrakk>gamma (t, xs) (u, ys); gamma_star (u, ys) (v, zs)\<rbrakk> \<Longrightarrow>
gamma_star (t, xs) (v, zs)" proof -

  assume "gamma_star (u, ys) (v, zs)"
  then obtain t' zs' where 0:
    "ys = zs' @ zs \<and> u = Abs_m (length zs') t' \<and> v = list_subst t' zs' (length zs')" by auto

  assume "gamma (t, xs) (u, ys)"
  with gamma.simps obtain t'' y where 1: "t = Abs t'' \<and> u = t''[BVar y/0] \<and> xs = y # ys" by auto

  from 0 1 have 2: "xs = y # zs' @ zs" by blast

  from 0 1 subst_Abs_m[of u "length zs'" t' t'' y 0] obtain t''' where t''':
    "t = Abs_m (length (y # zs')) t'''" by auto

  from 1 t''' have "t'' = Abs_m (length zs') t'''" by simp
  with Abs_m_subst[of "length zs'" t''' y 0] 1 have
    "u = Abs_m (length zs') (t'''[BVar (y + (length zs'))/length zs'])" by simp
  with 0 Abs_m_eq[of u "length zs'" t' "t'''[BVar (y + length zs')/length zs']"] have
    "t' = t'''[BVar (y + (length zs'))/length zs']" by argo
  with 0 have "v = list_subst (t'''[BVar (y + (length zs'))/length zs']) zs' (length zs')" by simp
  then have "v = list_subst t''' (y # zs') (length (y # zs'))" by auto

  with 2 t''' show ?thesis by auto
qed

lemma gamma_star_eq: "gamma_star (t, xs) (u, ys) = gamma\<^sup>*\<^sup>* (t, xs) (u, ys)" proof
  assume "gamma_star (t, xs) (u, ys)"
  then obtain zs t' where
    "xs = zs @ ys \<and> t = Abs_m (length zs) t' \<and> u = list_subst t' zs (length zs)" by auto
  then show "gamma\<^sup>*\<^sup>* (t, xs) (u, ys)" proof (induction zs arbitrary: xs t t')
    case Nil
    then show ?case by simp
  next
    case (Cons a zs)
    obtain xs' where xs': "xs' = zs @ ys" by simp
    obtain t'' where t'': "t'' = Abs_m (length zs) (t'[BVar (a + length zs)/length zs])" by simp
    from Cons have u: "u = list_subst (t'[BVar (a + length zs)/length zs]) zs (length zs)" by simp
    from xs' Cons Abs_m have "gamma (t, xs) ((Abs_m (length zs) t')[BVar a/0], xs')"
      by (metis Abs_m.simps(2) One_nat_def append_Cons diff_Suc_Suc diff_zero gamma.intros
          length_Cons)
    with Abs_m_subst t'' have "gamma(t, xs) (t'', xs')" by simp
    moreover from xs' t'' u Cons(1)[of xs' t'' "t'[BVar (a + length zs)/length zs]"] have
        "gamma\<^sup>*\<^sup>* (t'', xs') (u, ys)" by fast
    ultimately show ?case by simp
  qed
next
  assume "gamma\<^sup>*\<^sup>* (t, xs) (u, ys)"
  then show "gamma_star (t, xs) (u, ys)"
  proof (induction "(t, xs)" arbitrary: t xs rule: converse_rtranclp_induct)
    case base
    then show ?case by fastforce
  next
    case (step z)
    from this(1) gamma.cases obtain t'' where t'': "t = Abs t''" by blast
    from step(1) gamma.simps obtain x' xs' where xs': "xs = x' # xs'" by auto
    from step(1) t'' xs' have z: "z = (t''[BVar x'/0], xs')" by (simp add: gamma.simps)
    with step(3) have "gamma_star (t''[BVar x'/0], xs') (u, ys)" by presburger
    with step(1) t'' xs' z gamma_star_2 show ?case by blast
  qed
qed

lemma list_application_equiv: "\<lbrakk>s \<degree>\<degree> map BVar ys = s' \<degree>\<degree> map BVar ys'; length ys = length ys'\<rbrakk> \<Longrightarrow>
s = s' \<and> ys = ys'" proof (induction ys arbitrary: s s' ys')
  case Nil
  then show ?case by auto
next
  case (Cons a ys)
  have 0: "s \<degree>\<degree> map BVar (a # ys) = s \<degree> (BVar a) \<degree>\<degree> map BVar ys" by auto
  from Cons obtain x xs where ys': "ys' = x # xs"
    by (metis append_eq_append_conv append_self_conv list_max.elims)
  have "s' \<degree>\<degree> map BVar (x # xs) = s' \<degree> (BVar x) \<degree>\<degree> map BVar xs" by auto
  with 0 ys' Cons(1)[of "s \<degree> (BVar a)" "s' \<degree> (BVar x)" xs] Cons(2-3) show ?case by simp
qed

lemma confluence: "\<lbrakk>\<beta>\<eta>cl t t1; \<beta>\<eta>cl t t2\<rbrakk> \<Longrightarrow> \<exists>t'. \<beta>\<eta>cl t1 t' \<and> \<beta>\<eta>cl t2 t'"
  using confluent_beta_eta commute_def diamond_def square_def[of \<beta>\<eta>cl \<beta>\<eta>cl \<beta>\<eta>cl \<beta>\<eta>cl] by blast

abbreviation "normal t \<equiv> \<not>(\<exists>t'. \<beta>\<eta> t t')"

lemma normal_form_ex: "e \<turnstile> t : T \<Longrightarrow> \<exists>t'. \<beta>\<eta>cl t t' \<and> normal t'" proof -
  assume "e \<turnstile> t : T"
  with type_implies_termi_beta_eta have "termip \<beta>\<eta> t" by auto
  then show ?thesis proof (induction)
    case (1 x)
    then show ?case by (metis converse_rtranclp_into_rtranclp conversep_iff rtranclp.rtrancl_refl)
  qed
qed

lemma unique_normal_form: "\<lbrakk>\<beta>\<eta>cl t t'; \<beta>\<eta>cl t t''; normal t'; normal t''\<rbrakk> \<Longrightarrow> t' = t''" proof -
  assume "\<beta>\<eta>cl t t'" "\<beta>\<eta>cl t t''"
  with confluence obtain t''' where t''': "\<beta>\<eta>cl t' t''' \<and> \<beta>\<eta>cl t'' t'''" by blast

  assume "normal t'"
  with t''' have t': "t' = t'''" by (metis converse_rtranclpE)

  assume "normal t''"
  with t''' have "t'' = t'''" by (metis converse_rtranclpE)

  with t' show ?thesis by simp
qed

lemma subject_reduction_eta': "(e1, e2) \<turnstile> s : T \<Longrightarrow> \<not> free s i \<Longrightarrow>
(\<lambda>n. if n < i then e1 n else e1 (Suc n), e2) \<turnstile> s[dummy/i] : T"
  apply (induct e1 e2 s T arbitrary: dummy i rule: typing.induct[split_format(complete)])
     apply (auto simp: subst_BVar LambdaType.shift_def)
  apply (drule meta_spec2)
  apply (drule meta_mp)
   apply assumption
  apply (erule arg_cong[where f = "\<lambda>e1. (e1, _) \<turnstile> _ : _", THEN iffD1, rotated -1])
  apply (auto simp: fun_eq_iff)
  done

lemma subject_reduction_eta: "t \<rightarrow>\<^sub>\<eta> t' \<Longrightarrow> e \<turnstile> t : T \<Longrightarrow> e \<turnstile> t' : T"
proof (induction arbitrary: T e rule: eta.induct)
  case (eta s dummy)
  from this(2) show ?case proof cases
    case (Abs e1 U e2 V)
    from this(3) show ?thesis proof cases
      case (App U')
      then have "U = U'" by auto
      with App Abs have "(e1\<langle>0:U\<rangle>, e2) \<turnstile> s : U \<Rightarrow> V" by fast
      moreover from eta have "\<not> free s 0" by blast
      ultimately have "(e1, e2) \<turnstile> s[dummy/0] : U \<Rightarrow> V"
        using subject_reduction_eta'[of "e1\<langle>0:U\<rangle>" e2 s "U \<Rightarrow> V" 0 dummy]
        by auto
      with Abs show ?thesis by fast
    qed
  qed
next
  case (appL s t u)
  then show ?case by fast
next
  case (appR s t u)
  then show ?case by fast
next
  case (abs s t)
  then show ?case by blast
qed

theorem subject_reduction'_eta: "t \<rightarrow>\<^sub>\<eta>\<^sup>* t' \<Longrightarrow> e \<turnstile> t : T \<Longrightarrow> e \<turnstile> t' : T"
  by (induct set: rtranclp) (iprover intro: subject_reduction_eta)+

lemma subject_reduction_\<beta>\<eta>: "\<beta>\<eta>cl t t' \<Longrightarrow> e \<turnstile> t : T \<Longrightarrow> e \<turnstile> t' : T"
proof (induction rule: rtranclp.induct)
  case (rtrancl_refl a)
  then show ?case by simp
next
  case (rtrancl_into_rtrancl a b c)
  then show ?case using subject_reduction[of e b T c] subject_reduction_eta[of b c e T] by fast
qed

lemma gamma_normal': "\<lbrakk>normal t; gamma (t, x # xs) (t', xs)\<rbrakk> \<Longrightarrow> normal t'" proof -
  assume "gamma (t, x # xs) (t', xs)"
  with gamma.simps[of "(t, x # xs)" "(t', xs)"] obtain t'' where t'':
    "t = Abs t'' \<and> t' = t''[BVar x/0]" by blast
  assume "normal t"
  with t'' have "normal t''" by fast
  then have "normal (t''[BVar x/0])" using subst_BVar_betaetaD by blast
  with t'' show ?thesis by fast
qed

lemma gamma_normal'': "\<lbrakk>gamma\<^sup>*\<^sup>* (t, xs) (t', xs'); normal t\<rbrakk> \<Longrightarrow> normal t'"
proof (induction "(t, xs)" "(t', xs')" arbitrary: t xs t' xs' rule: rtranclp.induct)
  case rtrancl_refl
  then show ?case by blast
next
  case (rtrancl_into_rtrancl b)
  then show ?case using gamma_normal' gamma.cases[of b "(t', xs')"] fst_conv by metis
qed

abbreviation "gamma_red t xs \<equiv> \<not>(\<exists>t' xs'. gamma (t, xs) (t', xs'))"

lemma gamma_normal: "\<lbrakk>gamma\<^sup>*\<^sup>* (t, xs) (t', xs'); normal t; gamma_red t' xs'\<rbrakk> \<Longrightarrow>
normal (t' \<degree>\<degree> (map BVar xs'))" proof -
  assume "normal t" "gamma\<^sup>*\<^sup>* (t, xs) (t', xs')"
  with gamma_normal'' have "normal t'" by auto
  moreover assume "gamma_red t' xs'"
  ultimately show ?thesis proof (induction xs' arbitrary: t')
    case Nil
    then show ?case by simp
  next
    case (Cons a xs')
    moreover with gamma.intros have "normal (t' \<degree> (BVar a))"
      by (metis beta_cases(1) beta_cases(4) eta_cases(2) eta_cases(3) sup2CI sup2E)
    moreover from gamma.simps have "gamma_red (t' \<degree> (BVar a)) xs'" by blast
    ultimately show ?case by auto
  qed
qed

lemma gamma_term: "\<exists>t' xs'. gamma\<^sup>*\<^sup>* (t, xs) (t', xs') \<and> gamma_red t' xs'"
proof (induction xs arbitrary: t)
  case Nil
  from gamma.simps have "gamma_red t []" by simp
  then show ?case by blast
next
  case (Cons a xs)
  then show ?case proof (cases "gamma_red t (a # xs)")
    case True
    then show ?thesis by blast
  next
    case False
    with gamma.simps obtain t'' where "gamma (t, a # xs) (t'', xs)" by auto
    moreover with Cons obtain t' xs' where "gamma\<^sup>*\<^sup>* (t'', xs) (t', xs') \<and> gamma_red t' xs'" by blast
    ultimately have "gamma\<^sup>*\<^sup>* (t, a # xs) (t', xs') \<and> gamma_red t' xs'" by force
    then show ?thesis by auto
  qed
qed

lemma gamma_\<beta>\<eta>: "gamma (t, xs) (t', xs') \<Longrightarrow> \<beta>\<eta> (t \<degree>\<degree> map BVar xs) (t' \<degree>\<degree> map BVar xs')"
  using gamma.simps by auto

lemma gamma_\<beta>\<eta>cl: "gamma\<^sup>*\<^sup>* (t, xs) (t', xs') \<Longrightarrow> \<beta>\<eta>cl (t \<degree>\<degree> map BVar xs) (t' \<degree>\<degree> map BVar xs')"
proof (induction "(t, xs)" "(t', xs')" arbitrary: t xs t' xs' rule: rtranclp.induct)
  case rtrancl_refl
  then show ?case by blast
next
  case (rtrancl_into_rtrancl b)
  then show ?case using gamma.simps gamma_\<beta>\<eta> rtranclp.rtrancl_into_rtrancl by metis
qed

lemma \<beta>\<eta>_list_application: "\<beta>\<eta> t t' \<Longrightarrow> \<beta>\<eta> (t \<degree>\<degree> map BVar xs) (t' \<degree>\<degree> map BVar xs)"
  by fastforce

lemma \<beta>\<eta>cl_list_application: "\<beta>\<eta>cl t t' \<Longrightarrow> \<beta>\<eta>cl (t \<degree>\<degree> map BVar xs) (t' \<degree>\<degree> map BVar xs)"
proof (induction rule: rtranclp.induct)
  case (rtrancl_refl a)
  then show ?case by blast
next
  case (rtrancl_into_rtrancl a b c)
  then show ?case using \<beta>\<eta>_list_application rtranclp.rtrancl_into_rtrancl by metis
qed

lemma \<beta>\<eta>cl_not_free: "\<beta>\<eta>cl t t' \<Longrightarrow> \<not>free t i \<Longrightarrow> \<not>free t' i"
proof (induction rule: rtranclp.induct)
  case (rtrancl_refl a)
  then show ?case by presburger
next
  case (rtrancl_into_rtrancl a b c)
  then show ?case using free_beta free_eta by blast
qed

lemma \<beta>\<eta>cl_no_loose_bound: "\<beta>\<eta>cl t t' \<Longrightarrow> no_loose_bound t i \<Longrightarrow> no_loose_bound t' i" proof -
  assume "no_loose_bound t i"
  with loose_bound_free[of t i] have "(\<forall>k\<ge>i. \<not> free t k)" by blast
  moreover assume "\<beta>\<eta>cl t t'"
  ultimately have "(\<forall>k\<ge>i. \<not> free t' k)" using \<beta>\<eta>cl_not_free by fast
  with loose_bound_free show "no_loose_bound t' i" by blast
qed

lemma lemma22_t'': "\<lbrakk>\<beta>\<eta>cl t tx; \<beta>\<eta>cl t ty; gamma\<^sup>*\<^sup>* (tx, xs) (sx, xs'); gamma\<^sup>*\<^sup>* (ty, ys) (sy, ys');
sx \<degree>\<degree> (map BVar xs') = sy \<degree>\<degree> (map BVar ys'); e \<turnstile> (t \<degree>\<degree> map BVar xs) : T; e \<turnstile> (t \<degree>\<degree> map BVar ys) : T'\<rbrakk>
\<Longrightarrow> \<exists>t' sx' sy' xs'' ys''. \<beta>\<eta>cl tx t' \<and> \<beta>\<eta>cl ty t' \<and> gamma\<^sup>*\<^sup>* (t', xs) (sx', xs'') \<and>
gamma\<^sup>*\<^sup>* (t', ys) (sy', ys'') \<and> sx' \<degree>\<degree> (map BVar xs'') = sy' \<degree>\<degree> (map BVar ys'') \<and>
normal (sx' \<degree>\<degree> (map BVar xs'')) \<and> normal (sy' \<degree>\<degree> (map BVar ys''))" proof -
  assume txy: "\<beta>\<eta>cl t tx" "\<beta>\<eta>cl t ty"
  with confluence obtain t'' where t'': "\<beta>\<eta>cl tx t'' \<and> \<beta>\<eta>cl ty t''" by presburger

  assume "e \<turnstile> (t \<degree>\<degree> map BVar xs) : T"
  then obtain T'' where "e \<turnstile> t : T''" using list_app_typeD by blast
  with subject_reduction_\<beta>\<eta>[of _ _ e T''] txy t'' have "e \<turnstile> t'' : T''" by blast
  with normal_form_ex[OF this] obtain t' where t': "\<beta>\<eta>cl t'' t' \<and> normal t'" by blast

  from gamma_term obtain sx' xs'' where sx': "gamma\<^sup>*\<^sup>* (t', xs) (sx', xs'') \<and> gamma_red sx' xs''"
    by presburger
  with gamma_normal[of t' xs sx' xs''] t' have sx'_normal: "normal (sx' \<degree>\<degree> (map BVar xs''))" by fast

  from gamma_term obtain sy' ys'' where sy': "gamma\<^sup>*\<^sup>* (t', ys) (sy', ys'') \<and> gamma_red sy' ys''"
    by presburger
  with gamma_normal[of t' ys sy' ys''] t' have sy'_normal: "normal (sy' \<degree>\<degree> (map BVar ys''))" by fast

  assume "\<beta>\<eta>cl t tx" "gamma\<^sup>*\<^sup>* (tx, xs) (sx, xs')" "e \<turnstile> (t \<degree>\<degree> map BVar xs) : T"
  then have "\<exists>sx'1 xs''1. \<beta>\<eta>cl (sx \<degree>\<degree> (map BVar xs')) (sx'1 \<degree>\<degree> (map BVar xs''1)) \<and>
    normal (sx'1 \<degree>\<degree> (map BVar xs''1))" proof -
    assume "\<beta>\<eta>cl t tx"
    then have "\<beta>\<eta>cl (t \<degree>\<degree> map BVar xs) (tx \<degree>\<degree> map BVar xs)" using \<beta>\<eta>cl_list_application by simp
    moreover assume "gamma\<^sup>*\<^sup>* (tx, xs) (sx, xs')"
    ultimately have "\<beta>\<eta>cl (t \<degree>\<degree> map BVar xs) (sx \<degree>\<degree> map BVar xs')" using gamma_\<beta>\<eta>cl by force
    moreover assume "e \<turnstile> (t \<degree>\<degree> map BVar xs) : T"
    ultimately have "e \<turnstile> (sx \<degree>\<degree> map BVar xs') : T" using subject_reduction_\<beta>\<eta> by blast
    with normal_form_ex[OF this] show ?thesis by (metis foldl_Nil list.simps(8))
  qed
  then obtain sx'1 xs''1 where sx'1:
    "\<beta>\<eta>cl (sx \<degree>\<degree> (map BVar xs')) (sx'1 \<degree>\<degree> (map BVar xs''1)) \<and> normal (sx'1 \<degree>\<degree> (map BVar xs''1))"
    by blast

  assume "\<beta>\<eta>cl t ty" "gamma\<^sup>*\<^sup>* (ty, ys) (sy, ys')" "e \<turnstile> (t \<degree>\<degree> map BVar ys) : T'"
  then have "\<exists>sy'1 ys''1. \<beta>\<eta>cl (sy \<degree>\<degree> (map BVar ys')) (sy'1 \<degree>\<degree> (map BVar ys''1)) \<and>
    normal (sy'1 \<degree>\<degree> (map BVar ys''1))" proof -
    assume "\<beta>\<eta>cl t ty"
    then have "\<beta>\<eta>cl (t \<degree>\<degree> map BVar ys) (ty \<degree>\<degree> map BVar ys)" using \<beta>\<eta>cl_list_application by simp
    moreover assume "gamma\<^sup>*\<^sup>* (ty, ys) (sy, ys')"
    ultimately have "\<beta>\<eta>cl (t \<degree>\<degree> map BVar ys) (sy \<degree>\<degree> map BVar ys')" using gamma_\<beta>\<eta>cl by force
    moreover assume "e \<turnstile> (t \<degree>\<degree> map BVar ys) : T'"
    ultimately have "e \<turnstile> (sy \<degree>\<degree> map BVar ys') : T'" using subject_reduction_\<beta>\<eta> by blast
    with normal_form_ex[OF this] show ?thesis by (metis foldl_Nil list.simps(8))
  qed
  then obtain sy'1 ys''1 where sy'1:
    "\<beta>\<eta>cl (sy \<degree>\<degree> (map BVar ys')) (sy'1 \<degree>\<degree> (map BVar ys''1)) \<and> normal (sy'1 \<degree>\<degree> (map BVar ys''1))"
    by blast

  assume "gamma\<^sup>*\<^sup>* (tx, xs) (sx, xs')"
  then have sx'eq: "sx' \<degree>\<degree> (map BVar xs'') = sx'1 \<degree>\<degree> (map BVar xs''1)" proof -
    have "\<beta>\<eta>cl (tx \<degree>\<degree> map BVar xs) (sx' \<degree>\<degree> map BVar xs'')" proof -
      from t'' t' have "\<beta>\<eta>cl tx t'" by force
      with \<beta>\<eta>cl_list_application have "\<beta>\<eta>cl (tx \<degree>\<degree> map BVar xs) (t' \<degree>\<degree> map BVar xs)" by auto
      with sx' gamma_\<beta>\<eta>cl[of t' xs sx' xs''] show ?thesis by fastforce
    qed
    moreover from \<open>gamma\<^sup>*\<^sup>* (tx, xs) (sx, xs')\<close> have
      "\<beta>\<eta>cl (tx \<degree>\<degree> map BVar xs) (sx'1 \<degree>\<degree> map BVar xs''1)" proof -
      assume "gamma\<^sup>*\<^sup>* (tx, xs) (sx, xs')"
      with gamma_\<beta>\<eta>cl have "\<beta>\<eta>cl (tx \<degree>\<degree> map BVar xs) (sx \<degree>\<degree> map BVar xs')" by blast
      with sx'1 gamma_\<beta>\<eta>cl[of t' xs sx'1 xs''1] show ?thesis by auto
    qed
    ultimately show ?thesis using sx'1 sx'_normal unique_normal_form by presburger
  qed

  assume "gamma\<^sup>*\<^sup>* (ty, ys) (sy, ys')"
  then have sy'eq: "sy' \<degree>\<degree> (map BVar ys'') = sy'1 \<degree>\<degree> (map BVar ys''1)" proof -
    have "\<beta>\<eta>cl (ty \<degree>\<degree> map BVar ys) (sy' \<degree>\<degree> map BVar ys'')" proof -
      from t'' t' have "\<beta>\<eta>cl ty t'" by force
      with \<beta>\<eta>cl_list_application have "\<beta>\<eta>cl (ty \<degree>\<degree> map BVar ys) (t' \<degree>\<degree> map BVar ys)" by auto
      with sy' gamma_\<beta>\<eta>cl[of t' ys sy' ys''] show ?thesis by fastforce
    qed
    moreover from \<open>gamma\<^sup>*\<^sup>* (ty, ys) (sy, ys')\<close> have
      "\<beta>\<eta>cl (ty \<degree>\<degree> map BVar ys) (sy'1 \<degree>\<degree> map BVar ys''1)" proof -
      assume "gamma\<^sup>*\<^sup>* (ty, ys) (sy, ys')"
      with gamma_\<beta>\<eta>cl have "\<beta>\<eta>cl (ty \<degree>\<degree> map BVar ys) (sy \<degree>\<degree> map BVar ys')" by blast
      with sy'1 gamma_\<beta>\<eta>cl[of t' ys sy'1 ys''1] show ?thesis by auto
    qed
    ultimately show ?thesis using sy'1 sy'_normal unique_normal_form by presburger
  qed

  assume "sx \<degree>\<degree> (map BVar xs') = sy \<degree>\<degree> (map BVar ys')"
  have "sx' \<degree>\<degree> (map BVar xs'') = sy' \<degree>\<degree> map BVar ys''" proof -
    from sx'eq sx'1 have "\<beta>\<eta>cl (sx \<degree>\<degree> map BVar xs') (sx' \<degree>\<degree> map BVar xs'')" by argo
    moreover from sy'eq sy'1 \<open>sx \<degree>\<degree> (map BVar xs') = sy \<degree>\<degree> (map BVar ys')\<close> have
      "\<beta>\<eta>cl (sx \<degree>\<degree> map BVar xs') (sy' \<degree>\<degree> map BVar ys'')" by argo
    ultimately show ?thesis using sx'_normal sy'_normal unique_normal_form by blast
  qed

  moreover from t'' t' have "\<beta>\<eta>cl tx t'" by fastforce
  moreover from t'' t' have "\<beta>\<eta>cl ty t'" by fastforce
  ultimately show ?thesis using sx' sy' sx'_normal sy'_normal by blast
qed

lemma list_subst_partial:
"list_subst t (xs @ ys) m = list_subst (list_subst t xs m) ys (m - (length xs))"
proof (induction xs arbitrary: t m)
  case Nil
  then show ?case by simp
next
  case (Cons a xs)
  then show ?case by auto
qed

lemma subst_neq: "(t[BVar x/m] \<noteq> t[BVar y/m]) = (x \<noteq> y \<and> free t m)" proof
  assume "t[BVar x/m] \<noteq> t[BVar y/m]"
  moreover have "x = y \<Longrightarrow> t[BVar x/m] = t[BVar y/m]" by blast
  moreover have "\<not>(free t m) \<Longrightarrow> t[BVar x/m] = t[BVar y/m]" by simp
  ultimately show "(x \<noteq> y \<and> free t m)" by argo
next
  assume "(x \<noteq> y \<and> free t m)"
  then show "(t[BVar x/m] \<noteq> t[BVar y/m])"
    apply (induction t arbitrary: x y m) apply simp apply simp apply force by auto
qed

lemma list_subst_eq: "\<lbrakk>list_subst t xs m = list_subst t ys m; length xs = m; length ys = m; n \<le> m\<rbrakk>
\<Longrightarrow> list_subst t (take n xs) m = list_subst t (take n ys) m" proof (induction n)
  case 0
  then show ?case by force
next
  case (Suc n)

  obtain t' where t': "t' = list_subst t (take n xs) m" by blast

  from Suc obtain x' xs' where xs': "xs = (take n xs) @ x' # xs'"
    using Suc_le_lessD id_take_nth_drop by blast
  with t' list_subst_partial Suc have x: "list_subst t xs m = list_subst t' (x' # xs') (m - n)"
    by (metis Suc_leD length_take min.absorb2)

  from Suc obtain y' ys' where ys': "ys = (take n ys) @ y' # ys'"
    using Suc_le_lessD id_take_nth_drop by metis
  with t' list_subst_partial Suc have y: "list_subst t ys m = list_subst t' (y' # ys') (m - n)"
    by (metis Suc_leD length_take min.absorb2)

  from Suc x y have "list_subst t' (x' # xs') (m - n) = list_subst t' (y' # ys') (m - n)"
    by presburger
  moreover obtain m' where m': "m' = m - n - 1" by blast
  ultimately have 0: "list_subst (t'[BVar (x' + m')/m']) xs' m' =
    list_subst (t'[BVar (y' + m')/m']) ys' m'" using Suc(5) by simp

  moreover from Suc(3,4,5) xs' ys' length_take have lengths': "length xs' = length ys'"
    by (metis Suc_inject add_diff_cancel_left' length_Cons length_append)
  moreover from m' Suc xs' ys' have lengths: "length xs' = m' \<and> length ys' = m'"
    by (metis One_nat_def Suc_leD add_diff_cancel_left' add_diff_cancel_right' length_append
        length_take list.size(4) min.absorb2)
  ultimately have 1: "t'[BVar (x' + m')/m'] = t'[BVar (y' + m')/m']" proof -
    have "t'[BVar (x' + m')/m'] \<noteq> t'[BVar (y' + m')/m'] \<Longrightarrow>
      list_subst (t'[BVar (x' + m')/m']) xs' m' \<noteq> list_subst (t'[BVar (y' + m')/m']) ys' m'"
    proof -
      assume "t'[BVar (x' + m')/m'] \<noteq> t'[BVar (y' + m')/m']"
      moreover with subst_neq have "x' \<noteq> y'" by force
      moreover from lengths have "length xs' \<le> m' \<and> length ys' \<le> m'" by fastforce
      ultimately show ?thesis using lengths' proof (induction t' arbitrary: m')
        case (BVar x)
        then have x: "x = m'" by (metis subst.simps(1))
        then have "BVar x[BVar (x' + m')/m'] = BVar (x' + m')" by simp
        moreover from x have "BVar x[BVar (y' + m')/m'] = BVar (y' + m')" by simp
        moreover from list_subst_1 BVar have
          "list_subst (BVar (x' + m')) xs' m' = BVar (x' + m' - length xs')" by auto
        moreover from list_subst_1 BVar have
          "list_subst (BVar (y' + m')) ys' m' = BVar (y' + m' - length ys')" by auto
        moreover from BVar(2-4) have "BVar (x' + m' - length xs') \<noteq> BVar (y' + m' - length ys')"
          by auto
        ultimately show ?case by presburger
      next
        case (Var x)
        then show ?case by force
      next
        case (App t'1 t'2)

        from list_subst_App have 0: "list_subst ((t'1 \<degree> t'2)[BVar (x' + m')/m']) xs' m' =
          list_subst (t'1[BVar (x' + m')/m']) xs' m' \<degree> list_subst (t'2[BVar (x' + m')/m']) xs' m'"
          by simp

        from list_subst_App have 1: "list_subst ((t'1 \<degree> t'2)[BVar (y' + m')/m']) ys' m' =
          list_subst (t'1[BVar (y' + m')/m']) ys' m' \<degree> list_subst (t'2[BVar (y' + m')/m']) ys' m'"
          by simp

        from App(3) have "t'1[BVar (x' + m')/m'] \<degree> t'2[BVar (x' + m')/m'] \<noteq>
          t'1[BVar (y' + m')/m'] \<degree> t'2[BVar (y' + m')/m']" by fastforce
        then have "(t'1[BVar (x' + m')/m'] \<noteq> t'1[BVar (y' + m')/m']) \<or>
          (t'2[BVar (x' + m')/m'] \<noteq> t'2[BVar (y' + m')/m'])" by fast

        moreover have "t'1[BVar (x' + m')/m'] \<noteq> t'1[BVar (y' + m')/m'] \<Longrightarrow> ?case" proof -
          assume "t'1[BVar (x' + m')/m'] \<noteq> t'1[BVar (y' + m')/m']"
          with App(1)[of m'] App(3-6) have "list_subst (t'1[BVar (x' + m')/m']) xs' m' \<noteq>
            list_subst (t'1[BVar (y' + m')/m']) ys' m'" by fastforce
          with 0 1 show ?thesis by simp
        qed

        moreover have "t'2[BVar (x' + m')/m'] \<noteq> t'2[BVar (y' + m')/m'] \<Longrightarrow> ?case" proof -
          assume "t'2[BVar (x' + m')/m'] \<noteq> t'2[BVar (y' + m')/m']"
          with App(2)[of m'] App(3-6) have "list_subst (t'2[BVar (x' + m')/m']) xs' m' \<noteq>
            list_subst (t'2[BVar (y' + m')/m']) ys' m'" by fastforce
          with 0 1 show ?thesis by simp
        qed

        ultimately show ?case by fast
      next
        case (Abs t')
        moreover have "Abs t'[BVar (x' + m')/m'] = Abs (t'[BVar (x' + m' + 1)/m' + 1])" by simp
        moreover have "Abs t'[BVar (y' + m')/m'] = Abs (t'[BVar (y' + m' + 1)/m' + 1])" by simp
        ultimately have "t'[BVar (x' + m' + 1)/m' + 1] \<noteq> t'[BVar (y' + m' + 1)/m' + 1]" by auto
        with Abs(1)[of "m' + 1"] Abs(4,5) have 0:
          "list_subst (t'[BVar (x' + (m' + 1))/m' + 1]) xs' (m' + 1) \<noteq>
          list_subst (t'[BVar (y' + (m' + 1))/m' + 1]) ys' (m' + 1)" by fastforce

        have "list_subst (Abs t'[BVar (x' + m')/m']) xs' m' =
          list_subst (Abs (t'[BVar (x' + m' + 1)/m' + 1])) xs' m'" by simp
        moreover from list_subst_Abs Abs have x:
          "list_subst (Abs (t'[BVar (x' + m' + 1)/m' + 1])) xs' m' =
          Abs (list_subst (t'[BVar (x' + m' + 1)/m' + 1]) xs' (m' + 1))" by blast

        have "list_subst (Abs t'[BVar (y' + m')/m']) ys' m' =
          list_subst (Abs (t'[BVar (y' + m' + 1)/m' + 1])) ys' m'" by simp
        moreover from list_subst_Abs Abs have y:
          "list_subst (Abs (t'[BVar (y' + m' + 1)/m' + 1])) ys' m' =
          Abs (list_subst (t'[BVar (y' + m' + 1)/m' + 1]) ys' (m' + 1))" by blast

        from x y 0 show ?case by simp
      qed
    qed
    with 0 show ?thesis by fast
  qed

  from Suc have "m - n > 0" by linarith

  from xs' t' m' Suc have
    "list_subst t (take (Suc n) xs) m = list_subst t' [x'] (m - n)"
    by (metis Suc_leD Suc_le_lessD append_take_drop_id length_take list.sel(1) list_subst_partial
        min.absorb2 same_append_eq take_hd_drop)
  value "list_subst t' [x'] (m - n)"
  moreover from \<open>m - n > 0\<close> m' have "list_subst t' [x'] (m - n) = t'[BVar (x' + m')/m']" by simp
  ultimately have x: "list_subst t (take (Suc n) xs) m = t'[BVar (x' + m')/m']" by presburger

  from ys' t' m' Suc have
    "list_subst t (take (Suc n) ys) m = list_subst t' [y'] (m - n)"
    by (metis Suc_leD Suc_le_lessD append_take_drop_id length_take list.sel(1) list_subst_partial
        min.absorb2 same_append_eq take_hd_drop)
  value "list_subst t' [y'] (m - n)"
  moreover from \<open>m - n > 0\<close> m' have "list_subst t' [y'] (m - n) = t'[BVar (y' + m')/m']" by simp
  ultimately have y: "list_subst t (take (Suc n) ys) m = t'[BVar (y' + m')/m']" by presburger
  
  from 1 x y show ?case by argo
qed

lemma Abs_m_add: "Abs_m m t = Abs_m (m + n) t' \<Longrightarrow> t = Abs_m n t'"
  apply (induction m)
  apply force
  by fastforce

lemma Abs_m_less: "\<lbrakk>m \<le> n; t = Abs_m n t'\<rbrakk> \<Longrightarrow> \<exists>t''. t = Abs_m m t''"
proof (induction n arbitrary: m t)
  case 0
  then show ?case by blast
next
  case (Suc n)
  from this(3) have "t = Abs (Abs_m n t')" by force
  moreover from Suc(1)[of "m - 1" "Abs_m n t'"] Suc(2) have "\<exists>t''. Abs_m n t' = Abs_m (m - 1) t''"
    by fastforce
  ultimately show ?case proof (induction m)
    case 0
    then show ?case by simp
  next
    case (Suc m)
    then show ?case by auto
  qed
qed

lemma Abs_m_free: "free (Abs_m m t) i = free t (i + m)"
  apply (induction m arbitrary: i)
   apply auto[1]
  by simp

lemma lemma22'': "\<lbrakk>gamma_star (t, xs) (sx, xs'); gamma_star (t, ys) (sy, ys'); length xs = length ys;
sx \<degree>\<degree> map BVar xs' = sy \<degree>\<degree> map BVar ys'; normal (sx \<degree>\<degree> map BVar xs'); normal (sy \<degree>\<degree> map BVar ys')\<rbrakk>
\<Longrightarrow> length xs' = length ys'" proof -

  assume "gamma_star (t, xs) (sx, xs')"
  then obtain tx zx where tx:
    "xs = zx @ xs' \<and> t = Abs_m (length zx) tx \<and> sx = list_subst tx zx (length zx)" by auto

  assume "gamma_star (t, ys) (sy, ys')"
  then obtain ty zy where ty:
    "ys = zy @ ys' \<and> t = Abs_m (length zy) ty \<and> sy = list_subst ty zy (length zy)" by auto

  assume 1: "sx \<degree>\<degree> map BVar xs' = sy \<degree>\<degree> map BVar ys'"

  assume "normal (sy \<degree>\<degree> map BVar ys')"
  then have 2: "\<not>(\<exists>sy' ys''. gamma (sy, ys') (sy', ys''))" using gamma_\<beta>\<eta> by blast

  have 3: "length zx > length zy \<Longrightarrow> ?thesis" proof -
    assume "length zx > length zy"
    then obtain m where m: "m > 0 \<and> length zx = length zy + m" by (metis less_imp_add_positive)
    with tx have "t = Abs_m (length zy + m) tx" by presburger
    with ty have "Abs_m (length zy) ty = Abs_m (length zy + m) tx" by presburger
    with Abs_m_add[of "length zy" ty m tx] have "ty = Abs_m m tx" by fastforce
    with m have "ty = Abs (Abs_m (m - 1) tx)" using gr0_conv_Suc[of m] by auto
    with ty have "sy = list_subst (Abs (Abs_m (m - 1) tx)) zy (length zy)" by fastforce
    with list_subst_Abs have 0: "sy = Abs (list_subst (Abs_m (m - 1) tx) zy (length zy + 1))"
        by fast
    then show ?thesis proof (cases ys')
      case Nil
      from 1 0 Nil have "sx \<degree>\<degree> map BVar xs' = Abs (list_subst (Abs_m (m - 1) tx) zy (length zy + 1))"
        by simp
      then have "xs' = []" by blast
      with Nil show ?thesis by presburger
    next
      case (Cons a list)
      with 0 have
        "gamma (sy, ys') ((list_subst (Abs_m (m - 1) tx) zy (length zy + 1))[BVar a/0], list)"
        using gamma.intros by blast
      with 2 show ?thesis by presburger
    qed
  qed

  assume 1: "sx \<degree>\<degree> map BVar xs' = sy \<degree>\<degree> map BVar ys'"

  assume "normal (sx \<degree>\<degree> map BVar xs')"
  then have 2: "\<not>(\<exists>sx' xs''. gamma (sx, xs') (sx', xs''))" using gamma_\<beta>\<eta> by blast

  have 4: "length zy > length zx \<Longrightarrow> ?thesis" proof -
    assume "length zy > length zx"
    then obtain m where m: "m > 0 \<and> length zy = length zx + m" by (metis less_imp_add_positive)
    with ty have "t = Abs_m (length zx + m) ty" by presburger
    with tx have "Abs_m (length zx) tx = Abs_m (length zx + m) ty" by presburger
    with Abs_m_add[of "length zx" tx m ty] have "tx = Abs_m m ty" by fastforce
    with m have "tx = Abs (Abs_m (m - 1) ty)" using gr0_conv_Suc[of m] by auto
    with tx have "sx = list_subst (Abs (Abs_m (m - 1) ty)) zx (length zx)" by fastforce
    with list_subst_Abs have 0: "sx = Abs (list_subst (Abs_m (m - 1) ty) zx (length zx + 1))"
        by fast
    then show ?thesis proof (cases xs')
      case Nil
      from 1 0 Nil have "sy \<degree>\<degree> map BVar ys' = Abs (list_subst (Abs_m (m - 1) ty) zx (length zx + 1))"
        by simp
      then have "ys' = []" by blast
      with Nil show ?thesis by presburger
    next
      case (Cons a list)
      with 0 have
        "gamma (sx, xs') ((list_subst (Abs_m (m - 1) ty) zx (length zx + 1))[BVar a/0], list)"
        using gamma.intros by blast
      with 2 show ?thesis by presburger
    qed
  qed

  assume 0: "length xs = length ys"

  have "length zy = length zx \<Longrightarrow> ?thesis" proof -
    assume "length zy = length zx"
    with 0 tx ty show ?thesis by auto
  qed

  with 3 4 show ?thesis by linarith
qed

lemma gamma_append: "gamma\<^sup>*\<^sup>* (t, xs @ ys) (t', ys) \<Longrightarrow> gamma\<^sup>*\<^sup>* (t, xs @ zs) (t', zs)"
  by (metis append_same_eq gamma_star.simps gamma_star_eq)

lemma symcl_rtranclp: "r\<^sup>*\<^sup>* x y \<Longrightarrow> (symcl r)\<^sup>*\<^sup>* y x" proof (induction rule: rtranclp.induct)
case (rtrancl_refl a)
  then show ?case by blast
next
  case (rtrancl_into_rtrancl a b c)
  from this(2) have "(symcl r) c b" by fastforce
  with rtrancl_into_rtrancl(3) show ?case by (meson r_into_rtranclp rtranclp_trans)
qed

lemma symcl_confluence_rtranclp: "\<lbrakk>r\<^sup>*\<^sup>* x z; r\<^sup>*\<^sup>* y z\<rbrakk> \<Longrightarrow> (symcl r)\<^sup>*\<^sup>* x y" proof -
  assume "r\<^sup>*\<^sup>* y z"
  with symcl_rtranclp[of r y z] have "(symcl r)\<^sup>*\<^sup>* z y" by blast
  moreover assume "r\<^sup>*\<^sup>* x z"
  ultimately show ?thesis by (metis mono_rtranclp rtranclp_trans symcl.simps)
qed

lemma lemma22_lists:
"\<lbrakk>xs @ x # x_m = zs @ xs'; length xs < length zs\<rbrakk> \<Longrightarrow> \<exists>xs''. zs = xs @ x # xs''"
proof (induction xs arbitrary: zs)
  case Nil
  then show ?case using Cons_eq_append_conv by fastforce
next
  case (Cons a xs)
  from this(3) obtain z zs' where "zs = z # zs'"
    by (meson in_set_conv_nth list.set_cases)
  with Cons(2) have "xs @ x # x_m = zs' @ xs'" by auto
  with Cons show ?case by auto
qed

lemma list_subst_free:
"m > length xs \<Longrightarrow> free (list_subst t xs m) (m - length xs - 1) = free t (m - length xs - 1)"
proof (induction xs arbitrary: t m)
  case Nil
  then show ?case by simp
next
  case (Cons a xs)
  have "list_subst t (a # xs) m = list_subst (t[BVar (a + m - 1)/m - 1]) xs (m - 1)" by fastforce
  moreover from Cons(2) have "length xs < m - 1" by simp
  moreover have "(m - length (a # xs) - 1) = (m - 1 - length xs - 1)" by auto
  ultimately have 0:
    "free (list_subst t (a # xs) m) (m - length (a # xs) - 1) =
    free (t[BVar (a + m - 1)/m - 1]) (m - length (a # xs) - 1)"
    using Cons(1)[of "m - 1" "t[BVar (a + m - 1)/m - 1]"] by presburger

  from Cons(2) have "m - 1 > m - length (a # xs) - 1" by auto
  then have
    "free (t[BVar (a + m - 1)/m - 1]) (m - length (a # xs) - 1) = free t (m - length (a # xs) - 1)"
    by force
  with 0 show ?case by blast
qed

lemma closure_confluent: "closure \<beta>\<eta> t t' \<Longrightarrow> \<exists>s. \<beta>\<eta>cl t s \<and> \<beta>\<eta>cl t' s" proof -
  assume "closure \<beta>\<eta> t t'"
  then have "(symcl \<beta>\<eta>)\<^sup>*\<^sup>* t t'" by simp
  then show ?thesis proof (induction rule: rtranclp.induct)
    case (rtrancl_refl a)
    then show ?case by fast
  next
    case (rtrancl_into_rtrancl a b c)

    have "(sup (\<rightarrow>\<^sub>\<beta>) (\<rightarrow>\<^sub>\<eta>)) b c \<or> (sup (\<rightarrow>\<^sub>\<beta>) (\<rightarrow>\<^sub>\<eta>)) c b \<Longrightarrow> symcl (sup (\<rightarrow>\<^sub>\<beta>) (\<rightarrow>\<^sub>\<eta>)) b c" by simp

    moreover from rtrancl_into_rtrancl have "(sup (\<rightarrow>\<^sub>\<beta>) (\<rightarrow>\<^sub>\<eta>)) c b \<Longrightarrow> ?case"
      by (meson converse_rtranclp_into_rtranclp)

    moreover have "(sup (\<rightarrow>\<^sub>\<beta>) (\<rightarrow>\<^sub>\<eta>)) b c \<Longrightarrow> ?case" proof -
      assume 3: "(sup (\<rightarrow>\<^sub>\<beta>) (\<rightarrow>\<^sub>\<eta>)) b c"

      from Church_Rosser_confluent confluent_beta_eta have "Church_Rosser (sup (\<rightarrow>\<^sub>\<beta>) (\<rightarrow>\<^sub>\<eta>))"
        by fast
      from this 3 obtain z where 4: "(sup (\<rightarrow>\<^sub>\<beta>) (\<rightarrow>\<^sub>\<eta>))\<^sup>*\<^sup>* b z \<and> (sup (\<rightarrow>\<^sub>\<beta>) (\<rightarrow>\<^sub>\<eta>))\<^sup>*\<^sup>* c z" by blast

      from rtrancl_into_rtrancl obtain s' where 5:
        "(sup (\<rightarrow>\<^sub>\<beta>) (\<rightarrow>\<^sub>\<eta>))\<^sup>*\<^sup>* b s' \<and> (sup (\<rightarrow>\<^sub>\<beta>) (\<rightarrow>\<^sub>\<eta>))\<^sup>*\<^sup>* a s'" by blast

      from confluent_beta_eta this 4 have
        "\<exists>s. (sup (\<rightarrow>\<^sub>\<beta>) (\<rightarrow>\<^sub>\<eta>))\<^sup>*\<^sup>* s' s \<and> (sup (\<rightarrow>\<^sub>\<beta>) (\<rightarrow>\<^sub>\<eta>))\<^sup>*\<^sup>* z s" proof -
        from 4 5 have 6: "(sup (\<rightarrow>\<^sub>\<beta>) (\<rightarrow>\<^sub>\<eta>))\<^sup>*\<^sup>* b z \<and> (sup (\<rightarrow>\<^sub>\<beta>) (\<rightarrow>\<^sub>\<eta>))\<^sup>*\<^sup>* b s'" by blast
        from confluent_beta_eta diamond_def commute_def have "square (sup (\<rightarrow>\<^sub>\<beta>) (\<rightarrow>\<^sub>\<eta>))\<^sup>*\<^sup>*
          (sup (\<rightarrow>\<^sub>\<beta>) (\<rightarrow>\<^sub>\<eta>))\<^sup>*\<^sup>* (sup (\<rightarrow>\<^sub>\<beta>) (\<rightarrow>\<^sub>\<eta>))\<^sup>*\<^sup>* (sup (\<rightarrow>\<^sub>\<beta>) (\<rightarrow>\<^sub>\<eta>))\<^sup>*\<^sup>*" by blast 
        from this have "(\<forall>x y. (sup (\<rightarrow>\<^sub>\<beta>) (\<rightarrow>\<^sub>\<eta>))\<^sup>*\<^sup>* x y --> (\<forall>z. (sup (\<rightarrow>\<^sub>\<beta>) (\<rightarrow>\<^sub>\<eta>))\<^sup>*\<^sup>* x z -->
          (\<exists>u. (sup (\<rightarrow>\<^sub>\<beta>) (\<rightarrow>\<^sub>\<eta>))\<^sup>*\<^sup>* y u \<and> (sup (\<rightarrow>\<^sub>\<beta>) (\<rightarrow>\<^sub>\<eta>))\<^sup>*\<^sup>* z u)))" by (simp add: square_def)
        from this 6 show ?thesis by blast
      qed
      then obtain s'' where "(sup (\<rightarrow>\<^sub>\<beta>) (\<rightarrow>\<^sub>\<eta>))\<^sup>*\<^sup>* s' s'' \<and> (sup (\<rightarrow>\<^sub>\<beta>) (\<rightarrow>\<^sub>\<eta>))\<^sup>*\<^sup>* z s''"
        by presburger

      from this 4 5 have "(sup (\<rightarrow>\<^sub>\<beta>) (\<rightarrow>\<^sub>\<eta>))\<^sup>*\<^sup>* a s'' \<and> (sup (\<rightarrow>\<^sub>\<beta>) (\<rightarrow>\<^sub>\<eta>))\<^sup>*\<^sup>* c s''" by force
      from this 3 show ?thesis by blast
    qed

    ultimately show ?case using rtrancl_into_rtrancl by auto
  qed
qed

lemma lemma22:
"\<lbrakk>no_loose_bound t j;
(closure (sup beta eta)) (t \<degree>\<degree> map BVar (xs @ x # x_m)) (t \<degree>\<degree> map BVar (ys @ y # y_m));
length x_m = m; length y_m = m; length xs = length ys; e \<turnstile> t \<degree>\<degree> map BVar (xs @ x # x_m) : T;
e \<turnstile> t \<degree>\<degree> map BVar (ys @ y # y_m) : T'\<rbrakk> \<Longrightarrow>
(x = y \<longrightarrow>
(\<forall>z. (closure (sup beta eta)) (t \<degree>\<degree> map BVar (xs @ z # x_m)) (t \<degree>\<degree> map BVar (ys @ z # y_m))))
\<and> (x \<noteq> y \<longrightarrow> (\<exists>t'. \<beta>\<eta>cl t (Abs_m (length xs + 1) t') \<and> \<not>(free t' 0) \<and>
no_loose_bound t' (length xs + 1 + j)))" proof -

  assume "no_loose_bound t j"

  assume closure:
    "(closure (sup beta eta)) (t \<degree>\<degree> map BVar (xs @ x # x_m)) (t \<degree>\<degree> map BVar (ys @ y # y_m))"
  from this have
    "(symcl (sup beta eta))\<^sup>*\<^sup>* (t \<degree>\<degree> map BVar (xs @ x # x_m)) (t \<degree>\<degree> map BVar (ys @ y # y_m))" by simp

  with closure_confluent obtain s where s: "(sup beta eta)\<^sup>*\<^sup>* (t \<degree>\<degree> map BVar (xs @ x # x_m)) s \<and>
    (sup beta eta)\<^sup>*\<^sup>* (t \<degree>\<degree> map BVar (ys @ y # y_m)) s" by auto

  assume "e \<turnstile> t \<degree>\<degree> map BVar (xs @ x # x_m) : T" "e \<turnstile> t \<degree>\<degree> map BVar (ys @ y # y_m) : T'"
  moreover from s lemma22' obtain tx s'x xs' where tx:
    "\<beta>\<eta>cl t tx \<and> gamma\<^sup>*\<^sup>* (tx, xs @ x # x_m) (s'x, xs') \<and> s'x \<degree>\<degree> (map BVar xs') = s" by presburger
  moreover from s lemma22' obtain ty s'y ys' where ty:
    "\<beta>\<eta>cl t ty \<and> gamma\<^sup>*\<^sup>* (ty, ys @ y # y_m) (s'y, ys') \<and> s'y \<degree>\<degree> (map BVar ys') = s" by presburger

  ultimately have
    "\<exists>t' sx' sy' xs'' ys''. \<beta>\<eta>cl tx t' \<and> \<beta>\<eta>cl ty t' \<and> gamma\<^sup>*\<^sup>* (t', xs @ x # x_m) (sx', xs'') \<and>
    gamma\<^sup>*\<^sup>* (t', ys @ y # y_m) (sy', ys'') \<and> sx' \<degree>\<degree> map BVar xs'' = sy' \<degree>\<degree> map BVar ys'' \<and>
    normal (sx' \<degree>\<degree> map BVar xs'') \<and> normal (sy' \<degree>\<degree> map BVar ys'')"
    using lemma22_t''[of t tx ty "xs @ x # x_m" s'x xs' "ys @ y # y_m" s'y ys' e T T'] by argo

  then obtain t'' sx' xs'' sy' ys'' where
    "\<beta>\<eta>cl tx t'' \<and> \<beta>\<eta>cl ty t'' \<and> gamma\<^sup>*\<^sup>* (t'', xs @ x # x_m) (sx', xs'') \<and>
  gamma\<^sup>*\<^sup>* (t'', ys @ y # y_m) (sy', ys'') \<and> sx' \<degree>\<degree> map BVar xs'' = sy' \<degree>\<degree> map BVar ys'' \<and>
  normal (sx' \<degree>\<degree> map BVar xs'') \<and> normal (sy' \<degree>\<degree> map BVar ys'')" by blast

  with tx have t'': "\<beta>\<eta>cl t t'' \<and> gamma\<^sup>*\<^sup>* (t'', xs @ x # x_m) (sx', xs'') \<and>
    gamma\<^sup>*\<^sup>* (t'', ys @ y # y_m) (sy', ys'') \<and> sx' \<degree>\<degree> map BVar xs'' = sy' \<degree>\<degree> map BVar ys'' \<and>
    normal (sx' \<degree>\<degree> map BVar xs'') \<and> normal (sy' \<degree>\<degree> map BVar ys'')"
    by fastforce

  assume lens: "length xs = length ys" "length x_m = m" "length y_m = m"
  then have len: "length (xs @ x # x_m) = length (ys @ y # y_m)" by simp

  from t'' gamma_star_eq have gamma_star:
    "gamma_star (t'', xs @ x # x_m) (sx', xs'') \<and> gamma_star (t'', ys @ y # y_m) (sy', ys'')"
    by blast
  with len t'' lemma22''[of t'' "xs @ x # x_m" sx' xs'' "ys @ y # y_m" sy' ys''] have len':
    "length xs'' =  length ys''" by blast

  from gamma_star obtain tx' zsx where tx':
    "(xs @ x # x_m = zsx @ xs'' \<and> t'' = Abs_m (length zsx) tx' \<and>
    sx' = list_subst tx' zsx (length zsx))" by fastforce
  from gamma_star obtain ty' zsy where ty':
    "(ys @ y # y_m = zsy @ ys'' \<and> t'' = Abs_m (length zsy) ty' \<and>
    sy' = list_subst ty' zsy (length zsy))" by fastforce

  from list_application_equiv[of sx' xs'' sy' ys''] len' t'' have eq: "sx' = sy' \<and> xs'' = ys''"
    by fast

  from tx' ty' len' len have len'':  "length zsx = length zsy" by simp
  with tx' ty' Abs_m_eq[of t'' "length zsx" tx' ty'] have "tx' = ty'" by argo
  with tx' ty' list_subst_eq[of tx' zsx "length zsx" zsy] eq len'' have 0:
    "\<And>n. n \<le> length zsx \<Longrightarrow>
    list_subst tx' (take n zsx) (length zsx) = list_subst ty' (take n zsy) (length zsy)" by metis

  have "length zsx \<le> length xs \<Longrightarrow> ?thesis" proof
    assume a: "length zsx \<le> length xs"
    with tx' obtain xs''' where xs''': "xs'' = xs''' @ x # x_m" by (metis append_eq_append_conv_if)
    from a ty' lens len'' obtain ys''' where ys''': "ys'' = ys''' @ y # y_m"
      by (metis append_eq_append_conv_if)

    have "\<forall>z. closure \<beta>\<eta> (t \<degree>\<degree> map BVar (xs @ z # x_m)) (t \<degree>\<degree> map BVar (ys @ z # y_m))" proof
      fix z
  
      from xs''' ys''' eq lens have eq':
        "sx' \<degree>\<degree> map BVar (xs''' @ z # x_m) = sy' \<degree>\<degree> map BVar (ys''' @ z # y_m)" by auto
  
      from t'' xs''' have "gamma\<^sup>*\<^sup>* (t'', xs @ x # x_m) (sx', xs''' @ x # x_m)" by fastforce
      with gamma_append tx' xs''' have "gamma\<^sup>*\<^sup>* (t'', xs @ z # x_m) (sx', xs''' @ z # x_m)"
        by simp
  
      with t'' xs''' have
        "\<beta>\<eta>cl (t \<degree>\<degree> map BVar (xs @ z # x_m)) (sx' \<degree>\<degree> map BVar (xs''' @ z # x_m))"
        by (meson \<beta>\<eta>cl_list_application gamma_\<beta>\<eta>cl rtranclp_trans)
      then have x: "(symcl \<beta>\<eta>)\<^sup>*\<^sup>* (t \<degree>\<degree> map BVar (xs @ z # x_m)) (sx' \<degree>\<degree> map BVar (xs''' @ z # x_m))"
        by (metis mono_rtranclp symcl.elims)
  
      from t'' ys''' have "gamma\<^sup>*\<^sup>* (t'', ys @ y # y_m) (sy', ys''' @ y # y_m)" by fastforce
      with gamma_append ty' ys''' have "gamma\<^sup>*\<^sup>* (t'', ys @ z # y_m) (sy', ys''' @ z # y_m)"
        by simp
  
      with t'' ys''' have
        "\<beta>\<eta>cl (t \<degree>\<degree> map BVar (ys @ z # y_m)) (sy' \<degree>\<degree> map BVar (ys''' @ z # y_m))"
        by (meson \<beta>\<eta>cl_list_application gamma_\<beta>\<eta>cl rtranclp_trans)
      with symcl_rtranclp have y:
        "(symcl \<beta>\<eta>)\<^sup>*\<^sup>* (sy' \<degree>\<degree> map BVar (ys''' @ z # y_m)) (t \<degree>\<degree> map BVar (ys @ z # y_m))"
        by presburger
  
      from eq' x y show "closure \<beta>\<eta> (t \<degree>\<degree> map BVar (xs @ z # x_m)) (t \<degree>\<degree> map BVar (ys @ z # y_m))"
        by force
    qed
    then show
      "x = y \<longrightarrow> (\<forall>z. closure \<beta>\<eta> (t \<degree>\<degree> map BVar (xs @ z # x_m)) (t \<degree>\<degree> map BVar (ys @ z # y_m)))"
      by blast
  next
    assume a: "length zsx \<le> length xs"
    with tx' obtain xs''' where xs''': "xs'' = xs''' @ x # x_m" by (metis append_eq_append_conv_if)
    from a ty' lens len'' obtain ys''' where ys''': "ys'' = ys''' @ y # y_m"
      by (metis append_eq_append_conv_if)

    from eq xs''' ys''' have 0: "xs''' @ x # x_m = ys''' @ y # y_m" by argo

    from lens len' xs''' ys''' have "length xs''' = length ys'''" by auto
    with xs''' ys''' have "x \<noteq> y \<longrightarrow> xs''' @ x # x_m \<noteq> ys''' @ y # y_m" by simp

    with 0 show "x \<noteq> y \<longrightarrow> (\<exists>t'. \<beta>\<eta>cl t (Abs_m (length xs + 1) t') \<and> \<not> free t' 0 \<and>
      no_loose_bound t' (length xs + 1 + j))" by fast
  qed

  moreover have "length zsx > length xs \<Longrightarrow> ?thesis" proof
    assume a: "length zsx > length xs"
    with tx'[THEN conjunct1] lemma22_lists[of xs x x_m zsx xs''] obtain xs''' where xs''':
      "zsx = xs @ x # xs'''" by blast
    from a ty'[THEN conjunct1] lemma22_lists[of ys y y_m zsy ys''] lens len'' obtain ys''' where
      ys''': "zsy = ys @ y # ys'''" by metis

    from a tx'[THEN conjunct1] have "take (length xs) zsx = xs"
      by (metis append_eq_append_conv_if not_less)
    moreover from a ty'[THEN conjunct1] lens len'' have "take (length ys) zsy = ys"
      by (metis append_eq_append_conv_if not_less)
    ultimately have eq1: "list_subst tx' xs (length zsx) = list_subst ty' ys (length zsy)"
      using 0[of "length xs"] lens by force

    have "\<forall>z. closure \<beta>\<eta> (t \<degree>\<degree> map BVar (xs @ z # x_m)) (t \<degree>\<degree> map BVar (ys @ z # y_m))"
    proof
      fix z

      from eq1 lens len'' have
        "(list_subst tx' xs (length zsx))
      [BVar (z + length zsx - length xs - 1)/length zsx - length xs - 1] =
      list_subst ty' ys (length zsy)
      [BVar (z + length zsy - length ys - 1)/length zsy - length ys - 1]" by argo

      moreover from list_subst_partial[of tx' xs "[z]" "(length zsx)"] a have
        "(list_subst tx' xs (length zsx))
      [BVar (z + length zsx - length xs - 1)/length zsx - length xs - 1] =
      list_subst tx' (xs @ [z]) (length zsx)" by auto
      moreover from list_subst_partial[of ty' ys "[z]" "(length zsy)"] a lens len'' have
        "(list_subst ty' ys (length zsy))
      [BVar (z + length zsy - length ys - 1)/length zsy - length ys - 1] =
      list_subst ty' (ys @ [z]) (length zsy)" by auto

      ultimately have eq2:
        "list_subst tx' (xs @ [z]) (length zsx) = list_subst ty' (ys @ [z]) (length zsy)"
        by presburger

      obtain zsx' where zsx': "zsx' = xs @ z # xs'''" by blast
      moreover obtain zsy' where zsy': "zsy' = ys @ z # ys'''" by blast
      ultimately have len''': "length zsx = length zsx' \<and> length zsy = length zsy'"
        using xs''' ys''' by simp

      have 2: "length xs + 1 + m \<le> length zsx \<Longrightarrow>
      list_subst tx' (take (length xs + 1 + m) zsx') (length zsx) =
      list_subst ty' (take (length xs + 1 + m) zsy') (length zsy)" for m proof (induction m)
        case 0
        from zsx' have "take (length xs + 1) zsx' = xs @ [z]" by fastforce
        moreover from zsy' lens have "take (length xs + 1) zsy' = ys @ [z]" by fastforce
        ultimately show ?case using eq2 by force
      next
        case (Suc m)
        then have eq5: "list_subst tx' (take (length xs + 1 + m) zsx') (length zsx) =
        list_subst ty' (take (length xs + 1 + m) zsy') (length zsy)" by linarith
        from Suc(2) 0[of "length xs + 1 + m"] have eq4:
          "list_subst tx' (take (length xs + 1 + m) zsx) (length zsx) =
        list_subst ty' (take (length xs + 1 + m) zsy) (length zsy)" by linarith
        from Suc(2) 0[of "length xs + 1 + Suc m"] have eq3:
          "list_subst tx' (take (length xs + 1 + Suc m) zsx) (length zsx) =
        list_subst ty' (take (length xs + 1 + Suc m) zsy) (length zsy)" by fast

        obtain x' where x': "take (length xs + 1 + Suc m) zsx = (take (length xs + 1 + m) zsx) @ [x']"
          by (metis Suc.prems Suc_le_eq add_Suc_right take_Suc_conv_app_nth)
        from  len'' obtain y' where y':
          "take (length xs + 1 + Suc m) zsy = (take (length xs + 1 + m) zsy) @ [y']"
          by (metis Suc.prems Suc_le_eq add_Suc_right take_Suc_conv_app_nth)

        from Suc(2) have "length (take (length xs + 1 + m) zsx) = length xs + 1 + m" by simp

        with list_subst_partial[of tx' "take (length xs + 1 + m) zsx" "[x']" "length zsx"] x' have
          "list_subst tx' (take (length xs + 1 + Suc m) zsx) (length zsx) =
        list_subst (list_subst tx' (take (length xs + 1 + m) zsx) (length zsx)) [x']
        (length zsx - (length xs + 1 + m))" by simp
        with Suc(2) have x: "list_subst tx' (take (length xs + 1 + Suc m) zsx) (length zsx) =
        (list_subst tx' (take (length xs + 1 + m) zsx) (length zsx))
        [BVar (x' + length zsx - (length xs + 1 + Suc m))/length zsx - (length xs + 1 + Suc m)]"
          by fastforce

        from Suc(2) len'' have "length (take (length xs + 1 + m) zsy) = length xs + 1 + m" by simp

        with list_subst_partial[of ty' "take (length xs + 1 + m) zsy" "[y']" "length zsy"] y' have
          "list_subst ty' (take (length xs + 1 + Suc m) zsy) (length zsy) =
        list_subst (list_subst ty' (take (length xs + 1 + m) zsy) (length zsy)) [y']
        (length zsy - (length xs + 1 + m))" by simp
        with Suc(2) len'' have y: "list_subst ty' (take (length xs + 1 + Suc m) zsy) (length zsy) =
        (list_subst ty' (take (length xs + 1 + m) zsy) (length zsy))
        [BVar (y' + length zsy - (length xs + 1 + Suc m))/length zsy - (length xs + 1 + Suc m)]"
          by fastforce

        from x y eq3 len'' have "(list_subst tx' (take (length xs + 1 + m) zsx) (length zsx))
        [BVar (x' + length zsx - (length xs + 1 + Suc m))/length zsx - (length xs + 1 + Suc m)] =
        (list_subst ty' (take (length xs + 1 + m) zsy) (length zsy))
        [BVar (y' + length zsx - (length xs + 1 + Suc m))/length zsx - (length xs + 1 + Suc m)]"
          by argo

        with subst_neq len'' eq4 have 3:
          "(x' + length zsx - (length xs + 1 + Suc m)) = (y' + length zsx - (length xs + 1 + Suc m)) \<or>
        \<not>free (list_subst tx' (take (length xs + 1 + m) zsx) (length zsx))
        (length zsx - (length xs + 1 + Suc m))" by auto

        from Suc(2) have "length (take (length xs + 1 + m) zsx) < length zsx" by auto
        moreover from this have
          "length zsx - length (take (length xs + 1 + m) zsx) - 1 =
          length zsx - (length xs + 1 + Suc m)" by force
        ultimately have 4:
          "free (list_subst tx' (take (length xs + 1 + m) zsx) (length zsx))
          (length zsx - (length xs + 1 + Suc m)) =
          free tx' (length zsx - (length xs + 1 + Suc m))"
          using list_subst_free[of "take (length xs + 1 + m) zsx" "length zsx" tx'] by presburger

        from Suc(2) have "length (take (length xs + 1 + m) zsx') < length zsx" by auto
        moreover from this len''' have
          "length zsx - length (take (length xs + 1 + m) zsx') - 1 =
          length zsx - (length xs + 1 + Suc m)" by force
        ultimately have "free (list_subst tx' (take (length xs + 1 + m) zsx') (length zsx))
          (length zsx - (length xs + 1 + Suc m)) =
          free tx' (length zsx - (length xs + 1 + Suc m))"
          using list_subst_free[of "take (length xs + 1 + m) zsx'" "length zsx" tx'] by presburger

        with 4 have
          "free (list_subst tx' (take (length xs + 1 + m) zsx) (length zsx))
          (length zsx - (length xs + 1 + Suc m)) =
          free (list_subst tx' (take (length xs + 1 + m) zsx') (length zsx))
          (length zsx - (length xs + 1 + Suc m))" by fast

        with subst_neq eq5 3 have eq:
          "(list_subst tx' (take (length xs + 1 + m) zsx') (length zsx))
        [BVar (x' + length zsx - (length xs + 1 + Suc m))/length zsx - (length xs + 1 + Suc m)] =
        (list_subst ty' (take (length xs + 1 + m) zsy') (length zsy))
        [BVar (y' + length zsx - (length xs + 1 + Suc m))/length zsx - (length xs + 1 + Suc m)]"
          by auto

        from xs''' zsx' x' have x'':
          "take (length xs + 1 + Suc m) zsx' = (take (length xs + 1 + m) zsx') @ [x']" by simp

        from Suc(2) have x1: "(list_subst tx' (take (length xs + 1 + m) zsx') (length zsx))
        [BVar (x' + length zsx - (length xs + 1 + Suc m))/length zsx - (length xs + 1 + Suc m)] =
        list_subst (list_subst tx' (take (length xs + 1 + m) zsx') (length zsx)) [x']
        (length zsx - (length xs + 1 + m))" by fastforce

        from Suc(2) len''' have "length (take (length xs + 1 + m) zsx') = length xs + 1 + m" by simp

        with list_subst_partial[of tx' "take (length xs + 1 + m) zsx'" "[x']" "length zsx"] x'' have
          x2: "list_subst (list_subst tx' (take (length xs + 1 + m) zsx') (length zsx)) [x']
        (length zsx - (length xs + 1 + m)) =
        list_subst tx' (take (length xs + 1 + Suc m) zsx') (length zsx)" by argo

        from x1 x2 have x: "(list_subst tx' (take (length xs + 1 + m) zsx') (length zsx))
        [BVar (x' + length zsx - (length xs + 1 + Suc m))/length zsx - (length xs + 1 + Suc m)] =
        list_subst tx' (take (length xs + 1 + Suc m) zsx') (length zsx)" by argo

        from ys''' zsy' len'' lens y' have y'':
          "take (length xs + 1 + Suc m) zsy' = (take (length xs + 1 + m) zsy') @ [y']" by simp

        from Suc(2) len'' have y1: "(list_subst ty' (take (length xs + 1 + m) zsy') (length zsy))
        [BVar (y' + length zsy - (length xs + 1 + Suc m))/length zsy - (length xs + 1 + Suc m)] =
        list_subst (list_subst ty' (take (length xs + 1 + m) zsy') (length zsy)) [y']
        (length zsy - (length xs + 1 + m))" by fastforce

        from Suc(2) len''' len'' have "length (take (length xs + 1 + m) zsy') = length xs + 1 + m"
          by auto

        with list_subst_partial[of ty' "take (length xs + 1 + m) zsy'" "[y']" "length zsy"] y'' have
          y2: "list_subst (list_subst ty' (take (length xs + 1 + m) zsy') (length zsy)) [y']
        (length zsy - (length xs + 1 + m)) =
        list_subst ty' (take (length xs + 1 + Suc m) zsy') (length zsy)" by argo

        from y1 y2 have y: "(list_subst ty' (take (length xs + 1 + m) zsy') (length zsy))
        [BVar (y' + length zsy - (length xs + 1 + Suc m))/length zsy - (length xs + 1 + Suc m)] =
        list_subst ty' (take (length xs + 1 + Suc m) zsy') (length zsy)" by argo

        from x y eq len'' len''' show ?case by argo
      qed

      from a len''' zsx' obtain m' where "length xs + 1 + m' = length zsx" by auto

      with 2[of m'] len''' len'' have 3: "list_subst tx' zsx' (length zsx) =
      list_subst ty' zsy' (length zsy)" by fastforce

      from tx' zsx' xs''' obtain sx'' where sx'': "xs @ z # x_m = zsx' @ xs'' \<and> t'' =
      Abs_m (length zsx) tx' \<and> sx'' = list_subst tx' zsx' (length zsx)" by auto
      with len''' have "gamma_star (t'', xs @ z # x_m) (sx'', xs'')" by auto
      with gamma_star_eq gamma_\<beta>\<eta>cl have
        "\<beta>\<eta>cl (t'' \<degree>\<degree> map BVar (xs @ z # x_m)) (sx'' \<degree>\<degree> map BVar xs'')" by blast
      with t''[THEN conjunct1] have x: "\<beta>\<eta>cl (t \<degree>\<degree> map BVar (xs @ z # x_m)) (sx'' \<degree>\<degree> map BVar xs'')"
        by (meson \<beta>\<eta>cl_list_application rtranclp_trans)

      from ty' zsy' ys''' obtain sy'' where sy'': "ys @ z # y_m = zsy' @ ys'' \<and> t'' =
      Abs_m (length zsy) ty' \<and> sy'' = list_subst ty' zsy' (length zsy)" by auto
      with len''' have "gamma_star (t'', ys @ z # y_m) (sy'', ys'')" by auto
      with gamma_star_eq gamma_\<beta>\<eta>cl have
        "\<beta>\<eta>cl (t'' \<degree>\<degree> map BVar (ys @ z # y_m)) (sy'' \<degree>\<degree> map BVar ys'')" by blast
      with t''[THEN conjunct1] have "\<beta>\<eta>cl (t \<degree>\<degree> map BVar (ys @ z # y_m)) (sy'' \<degree>\<degree> map BVar ys'')"
        by (meson \<beta>\<eta>cl_list_application rtranclp_trans)
      then have y: "(symcl \<beta>\<eta>)\<^sup>*\<^sup>* (sy'' \<degree>\<degree> map BVar ys'') (t \<degree>\<degree> map BVar (ys @ z # y_m))"
        using symcl_rtranclp by blast

      from 3 sx'' sy'' have "sx'' = sy''" by meson

      with x y eq show "closure \<beta>\<eta> (t \<degree>\<degree> map BVar (xs @ z # x_m)) (t \<degree>\<degree> map BVar (ys @ z # y_m))"
        by (meson closure_symmetric rtranclp_trans symcl_rtranclp)
    qed
    then show
      "x = y \<longrightarrow> (\<forall>z. closure \<beta>\<eta> (t \<degree>\<degree> map BVar (xs @ z # x_m)) (t \<degree>\<degree> map BVar (ys @ z # y_m)))"
      by blast
  next
    assume a: "length zsx > length xs"
    with tx'[THEN conjunct2[THEN conjunct1]] Abs_m_less[of "length xs + 1" "length zsx" t'' tx']
    obtain t' where t': "t'' = Abs_m (length xs + 1) t'" by auto
    moreover from a have "length xs + 1 + (length zsx - length xs - 1) = length zsx" by fastforce
    ultimately have t'1: "t' = Abs_m (length zsx - length xs - 1) tx'"
      using tx'[THEN conjunct2[THEN conjunct1]]
        Abs_m_add[of "length xs + 1" t' "length zsx - length xs - 1" tx'] by presburger

    from a tx'[THEN conjunct1] lemma22_lists[of xs x x_m zsx xs''] obtain xs''' where xs''':
      "zsx = xs @ x # xs'''" by blast
    from a ty'[THEN conjunct1] lemma22_lists[of ys y y_m zsy ys''] lens len'' obtain ys''' where
      ys''': "zsy = ys @ y # ys'''" by metis

    from xs''' have "(take (length xs) zsx) = xs" by simp
    moreover from ys''' lens have "(take (length xs) zsy) = ys" by simp
    ultimately have eq1: 
      "list_subst tx' (xs) (length zsx) = list_subst ty' (ys) (length zsy)"
      using 0[of "length xs"] xs''' ys''' by force

    from xs''' have "(take (length xs + 1) zsx) = xs @ [x]" by simp
    moreover from ys''' lens have "(take (length xs + 1) zsy) = ys @ [y]" by simp
    ultimately have
      "list_subst tx' (xs @ [x]) (length zsx) = list_subst ty' (ys @ [y]) (length zsy)"
      using 0[of "length xs + 1"] xs''' ys''' by force

    moreover from list_subst_partial[of tx' xs "[x]" "length zsx"] a have
      "list_subst tx' (xs @ [x]) (length zsx) =
      (list_subst tx' xs (length zsx))
      [BVar (x + length zsx - length xs - 1)/length zsx - length xs - 1]" by fastforce

    moreover from list_subst_partial[of ty' ys "[y]" "length zsy"] a lens len'' have
      "list_subst ty' (ys @ [y]) (length zsy) =
      (list_subst ty' ys (length zsy))
      [BVar (y + length zsy - length ys - 1)/length zsy - length ys - 1]" by fastforce

    ultimately have
      "(list_subst tx' xs (length zsx))
      [BVar (x + length zsx - length xs - 1)/length zsx - length xs - 1] =
      (list_subst ty' ys (length zsy))
      [BVar (y + length zsx - length xs - 1)/length zsx - length xs - 1]" using lens len''  by argo

    with subst_neq[of "list_subst tx' xs (length zsx)" "x + length zsx - length xs - 1"
        "length zsx - length xs - 1" "y + length zsx - length xs - 1"] eq1 have
      1: "x + length zsx - length xs - 1 = y + length zsx - length xs - 1 \<or>
      \<not>free (list_subst tx' xs (length zsx)) (length zsx - length xs - 1)" by argo

    from a have 2: "(x + length zsx - length xs - 1 = y + length zsx - length xs - 1) = (x = y)"
      by fastforce

    show "x \<noteq> y \<longrightarrow> (\<exists>t'. \<beta>\<eta>cl t (Abs_m (length xs + 1) t') \<and> \<not> free t' 0 \<and>
      no_loose_bound t' (length xs + 1 + j))" proof
      assume a1: "x \<noteq> y"
      with 1 2 have "\<not>free (list_subst tx' xs (length zsx)) (length zsx - length xs - 1)" by auto
      with a list_subst_free[of xs "length zsx" tx'] have
        "\<not>free tx' (length zsx - length xs - 1)" by fast
      with Abs_m_free t' t'1 have "\<not> free t' 0" by auto

      from \<open>no_loose_bound t j\<close> t'' \<beta>\<eta>cl_no_loose_bound have "no_loose_bound t'' j" by blast
      with loose_bound_Abs_m[of "length xs + 1" t' j] t' have
        "no_loose_bound t' (j + length xs + 1)" by force
      then have "no_loose_bound t' (length xs + 1 + j)" by (simp add: add.commute)

      with t' t'' \<open>\<not> free t' 0\<close> show "\<exists>t'. \<beta>\<eta>cl t (Abs_m (length xs + 1) t') \<and> \<not> free t' 0 \<and>
        no_loose_bound t' (length xs + 1 + j)" by fast
    qed
  qed

  ultimately show ?thesis by fastforce
qed

fun replace_list :: "'a list \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a list" where
"replace_list [] _ _ = []" |
"replace_list (x # xs) y z = (if x = y then z else x) # replace_list xs y z"

lemma replace_list_append: "replace_list (xs @ ys) x z = replace_list xs x z @ replace_list ys x z"
  apply (induction xs) apply simp by simp

lemma replace_list_not_member: "x \<notin> set xs \<Longrightarrow> replace_list xs x z = xs"
  apply (induction xs) apply simp by auto

lemma replace_list_length: "length xs = length (replace_list xs x z)"
  apply (induction xs) apply simp by fastforce

lemma replace_list_index: "xs ! i \<noteq> x \<Longrightarrow> replace_list xs x y ! i = xs ! i"
proof (induction xs arbitrary: i)
  case Nil
  then show ?case by fastforce
next
  case (Cons a xs)
  then show ?case apply (cases i) by auto
qed

lemma replace_list_index': "replace_list xs x y ! i \<noteq> y \<Longrightarrow> replace_list xs x y ! i = xs ! i"
proof (induction xs arbitrary: i)
  case Nil
  then show ?case by simp
next
  case (Cons a xs)
  then show ?case apply (cases i) by auto
qed

fun replace_BVar :: "dB \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> dB" where
"replace_BVar (BVar x) y z = (if x = y then BVar z else BVar x)" |
"replace_BVar (Var x) _ _ = Var x" |
"replace_BVar (App t1 t2) y z = App (replace_BVar t1 y z) (replace_BVar t2 y z)" |
"replace_BVar (Abs t) y z = Abs (replace_BVar t (Suc y) (Suc z))"

lemma replace_BVar_no_loose_bound: "\<lbrakk>no_loose_bound t i; j \<ge> i\<rbrakk> \<Longrightarrow> replace_BVar t j x = t"
  apply (induction t arbitrary: i j x)
     apply fastforce
    apply simp
   apply force
  by force

lemma replace_BVar_list_application:
"replace_BVar (t \<degree>\<degree> map BVar xs) x z = replace_BVar t x z \<degree>\<degree> map BVar (replace_list xs x z)"
  apply (induction xs arbitrary: t) apply simp by fastforce

lemma replace_subst:
"replace_BVar (t[BVar y/i]) x z = (replace_BVar t (if x \<ge> i then x + 1 else x)
(if z \<ge> i then z + 1 else z))[BVar (if y = x then z else y)/i]"
proof (induction t arbitrary: x z i y)
  case (BVar x')
  then show ?case apply (rule linorder_cases[of x' i]) by auto
next
  case (Var x)
  then show ?case by force
next
  case (App t1 t2)
  then show ?case by simp
next
  case (Abs t)
  then show ?case by auto
qed

lemma replace_BVar_lift: "lift (replace_BVar s x z) i =
replace_BVar (lift s i) (if x \<ge> i then x + 1 else x) (if z \<ge> i then z + 1 else z)"
proof (induction s arbitrary: i x z)
  case (BVar x')
  then show ?case by auto
next
  case (Var x)
  then show ?case by simp
next
  case (App s1 s2)
  then show ?case by fastforce
next
  case (Abs s)
  then show ?case by simp
qed

lemma replace_subst': "replace_BVar (t[s/i]) x z = (replace_BVar t (if x \<ge> i then x + 1 else x)
(if z \<ge> i then z + 1 else z))[replace_BVar s x z/i]" proof (induction t arbitrary: s i x z)
  case (BVar x')
  then show ?case apply (rule linorder_cases[of x' i]) by auto
next
  case (Var x)
  then show ?case by force
next
  case (App t1 t2)
  then show ?case by fastforce
next
  case (Abs t)
  have "replace_BVar (Abs t[s/i]) x z = Abs (replace_BVar (t[lift s 0/i + 1]) (Suc x) (Suc z))"
    by simp
  with Abs(1)[of "lift s 0" "i + 1" "Suc x" "Suc z"] have
    "replace_BVar (t[lift s 0/i + 1]) (Suc x) (Suc z) =
    replace_BVar t (if i + 1 \<le> Suc x then Suc x + 1 else Suc x)
    (if i + 1 \<le> Suc z then Suc z + 1 else Suc z)[replace_BVar (lift s 0) (Suc x) (Suc z)/i + 1]"
    by blast
  moreover have "replace_BVar (Abs t) (if i \<le> x then x + 1 else x) (if i \<le> z then z + 1 else z)
    [replace_BVar s x z/i] = Abs (replace_BVar t (Suc (if i \<le> x then x + 1 else x))
    (Suc (if i \<le> z then z + 1 else z))[lift (replace_BVar s x z) 0/i + 1])" by auto
  moreover have
    "(Suc (if i \<le> x then x + 1 else x)) = (if i + 1 \<le> Suc x then Suc x + 1 else Suc x)" for x
    by simp
  moreover from replace_BVar_lift have
    "lift (replace_BVar s x z) 0 = replace_BVar (lift s 0) (Suc x) (Suc z)" by simp
  ultimately show ?case by force
qed

lemma replace_BVar_free: "\<lbrakk>\<not>free s i; z \<noteq> i\<rbrakk> \<Longrightarrow> \<not>free (replace_BVar s x z) i"
  apply (induction s arbitrary: i x z)
  by simp_all

lemma replace_list_subst:
"replace_BVar (list_subst t xs (length xs)) x z =
list_subst (replace_BVar t (x + length xs) (z + length xs)) (replace_list xs x z) (length xs)"
proof (induction xs arbitrary: t x z)
  case Nil
  then show ?case by simp
next
  case (Cons a xs)
  then show ?case using replace_subst by auto
qed

lemma replace_BVar_preserves_beta: "s \<rightarrow>\<^sub>\<beta> t \<Longrightarrow> replace_BVar s x z \<rightarrow>\<^sub>\<beta> replace_BVar t x z"
proof (induction arbitrary: x z rule: beta.induct)
  case (beta s t)
  have "replace_BVar (Abs s \<degree> t) x z = Abs (replace_BVar s (x + 1) (z + 1)) \<degree> replace_BVar t x z"
    by fastforce
  moreover from replace_subst'[of s t 0 x z] have "replace_BVar (s[t/0]) x z = 
    replace_BVar s (x + 1) (z + 1)[replace_BVar t x z/0]" by simp
  ultimately show ?case by fastforce
next
  case (appL s t u)
  then show ?case by auto
next
  case (appR s t u)
  then show ?case by simp
next
  case (abs s t)
  then show ?case by simp
qed


lemma replace_BVar_preserves_eta: "s \<rightarrow>\<^sub>\<eta> t \<Longrightarrow> replace_BVar s x z \<rightarrow>\<^sub>\<eta> replace_BVar t x z"
proof (induction arbitrary: x z rule: eta.induct)        
  case (eta s dummy)
  have "replace_BVar (Abs (s \<degree> BVar 0)) x z = Abs (replace_BVar s (x + 1) (z + 1) \<degree> BVar 0)" by simp
  moreover from replace_subst'[of s dummy 0 x z] have "replace_BVar (s[dummy/0]) x z =
    replace_BVar s (x + 1) (z + 1)[replace_BVar dummy x z/0]" by auto
  moreover from replace_BVar_free[of s 0 "z + 1" "x + 1"] eta have
    "\<not> free (replace_BVar s (x + 1) (z + 1)) 0" by simp
  ultimately show ?case using subst_not_free by auto
next
  case (appL s t u)
  then show ?case by force
next
  case (appR s t u)
  then show ?case by simp
next
  case (abs s t)
  then show ?case by simp
qed

lemma replace_BVar_preserves_closure:
"closure \<beta>\<eta> s t \<Longrightarrow> closure \<beta>\<eta> (replace_BVar s x z) (replace_BVar t x z)"
proof (induction rule: rtranclp.induct)
  case (rtrancl_refl a)
  then show ?case by blast
next
  case (rtrancl_into_rtrancl a b c)
  then show ?case
    by (metis (full_types) replace_BVar_preserves_beta replace_BVar_preserves_eta
        rtranclp.rtrancl_into_rtrancl sup2CI sup2E symcl.simps)
qed

lemma free_list_application:
"free (t \<degree>\<degree> map BVar xs) x = (free t x \<or> (find ((=) x) xs \<noteq> None))"
  apply (induction xs arbitrary: t) apply simp by simp

lemma subst_free: "\<lbrakk>j > i; free t j\<rbrakk> \<Longrightarrow> free (t[BVar x/i]) (j - 1)" by simp

lemma list_subst_free':
"\<lbrakk>n \<ge> m; n \<ge> length xs; free t n\<rbrakk> \<Longrightarrow> free (list_subst t xs m) (n - (length xs))"
proof (induction xs arbitrary: t m n)
  case Nil
  then show ?case by simp
next
  case (Cons a xs)
  have "list_subst t (a # xs) m = list_subst (t[BVar (a + m - 1)/m - 1]) xs (m - 1)" by fastforce
  with Cons(1)[of "m - 1" "n - 1" "t[BVar (a + m - 1)/m - 1]"] Cons(2-4) have
    "free (list_subst (t[BVar (a + m - 1)/m - 1]) xs (m - 1)) (n - 1 - length xs)" by auto
  then show ?case by simp
qed

lemma lemma23: "\<lbrakk>no_loose_bound t 0; no_loose_bound s 0;
closure \<beta>\<eta> (t \<degree>\<degree> map BVar (xs @ x # x_m)) (s \<degree>\<degree> map BVar y_n)\<rbrakk> \<Longrightarrow>

(x \<in> set y_n \<and> x \<notin> set xs \<longrightarrow>
(\<forall>z. closure \<beta>\<eta> (t \<degree>\<degree> map BVar (xs @ z # replace_list x_m x z))
(s \<degree>\<degree> map BVar (replace_list y_n x z)))) \<and>

(\<not>(x \<in> set y_n) \<longrightarrow> (\<exists>t'. \<beta>\<eta>cl t (Abs_m (length xs + 1) t') \<and> \<not>free t' 0 \<and>
no_loose_bound t' (length xs + 1)))" proof -
  assume "no_loose_bound s 0" "no_loose_bound t 0"

  assume "closure \<beta>\<eta> (t \<degree>\<degree> map BVar (xs @ x # x_m)) (s \<degree>\<degree> map BVar y_n)"
  then have "(symcl \<beta>\<eta>)\<^sup>*\<^sup>* (t \<degree>\<degree> map BVar (xs @ x # x_m)) (s \<degree>\<degree> map BVar y_n)" by simp
  with closure_confluent obtain r where r:
    "\<beta>\<eta>cl (t \<degree>\<degree> map BVar (xs @ x # x_m)) r \<and> \<beta>\<eta>cl (s \<degree>\<degree> map BVar y_n) r" by auto

  with lemma22' obtain t'' rx xs' where t'':
    "\<beta>\<eta>cl t t'' \<and> gamma\<^sup>*\<^sup>* (t'', xs @ x # x_m) (rx, xs') \<and> rx \<degree>\<degree> map BVar xs' = r" by presburger
  from r lemma22' obtain s'' ry ys' where s'':
    "\<beta>\<eta>cl s s'' \<and> gamma\<^sup>*\<^sup>* (s'', y_n) (ry, ys') \<and> ry \<degree>\<degree> map BVar ys' = r" by presburger

  from gamma_star_eq t'' gamma_star.simps obtain t' xs'' where t':
    "xs @ x # x_m = xs'' @ xs' \<and> t'' = Abs_m (length xs'') t' \<and>
    rx = list_subst t' xs'' (length xs'')" by meson
  from gamma_star_eq s'' gamma_star.simps obtain s' ys'' where s':
    "y_n = ys'' @ ys' \<and> s'' = Abs_m (length ys'') s' \<and>
    ry = list_subst s' ys'' (length ys'')" by meson

  show ?thesis proof
    show "x \<in> set y_n \<and> x \<notin> set xs \<longrightarrow>
      (\<forall>z. closure \<beta>\<eta> (t \<degree>\<degree> map BVar (xs @ z # replace_list x_m x z))
      (s \<degree>\<degree> map BVar (replace_list y_n x z)))" proof

      assume "x \<in> set y_n \<and> x \<notin> set xs"
      then have "x \<notin> set xs" by blast

      show "\<forall>z. closure \<beta>\<eta> (t \<degree>\<degree> map BVar (xs @ z # replace_list x_m x z))
        (s \<degree>\<degree> map BVar (replace_list y_n x z))" proof

        fix z
        have x4: "xs @ z # replace_list x_m x z = replace_list (xs @ x # x_m) x z" proof -
          from replace_list_append have
            "replace_list (xs @ x # x_m) x z = replace_list xs x z @ replace_list (x # x_m) x z"
            by fast
          moreover from \<open>x \<notin> set xs\<close> replace_list_not_member have "replace_list xs x z = xs"
            by fast
          ultimately show ?thesis by fastforce
        qed

        from t'' s'' have eq:
          "replace_BVar (rx \<degree>\<degree> map BVar xs') x z = replace_BVar (ry \<degree>\<degree> map BVar ys') x z" by argo

        from t' replace_BVar_list_application have x1:
          "replace_BVar (rx \<degree>\<degree> map BVar xs') x z =
        replace_BVar (list_subst t' xs'' (length xs'')) x z \<degree>\<degree> map BVar (replace_list xs' x z)"
          by auto
        from replace_list_subst[of t' xs'' x z] have x2:
          "replace_BVar (list_subst t' xs'' (length xs'')) x z =
        list_subst (replace_BVar t' (x + length xs'') (z + length xs'')) (replace_list xs'' x z)
        (length xs'')" by blast

        from \<open>no_loose_bound t 0\<close> t'' \<beta>\<eta>cl_no_loose_bound have "no_loose_bound t'' 0" by blast
        with t' loose_bound_Abs_m[of "length xs''" t' 0] have
          "no_loose_bound t' (length xs'')" by force
        with replace_BVar_no_loose_bound have x3:
          "replace_BVar t' (x + length xs'') (z + length xs'') = t'" by simp

        from t' replace_list_append have
          "replace_list (xs @ x # x_m) x z = replace_list xs'' x z @ replace_list xs' x z" by force
        moreover obtain rx' where rx':
          "rx' = list_subst t' (replace_list xs'' x z) (length xs'')" by blast
        ultimately have
          "gamma_star (t'', replace_list (xs @ x # x_m) x z) (rx', replace_list xs' x z)"
          using t'[THEN conjunct2[THEN conjunct1]] replace_list_length[of xs'' x z] by auto

        with t'' \<beta>\<eta>cl_list_application[of t t'' "replace_list (xs @ x # x_m) x z"]
          gamma_star_eq[of t'' "replace_list (xs @ x # x_m) x z" rx' "replace_list xs' x z"]
          gamma_\<beta>\<eta>cl[of t'' "replace_list (xs @ x # x_m) x z" rx' "replace_list xs' x z"] have x':
          "\<beta>\<eta>cl (t \<degree>\<degree> map BVar (replace_list (xs @ x # x_m) x z))
        (rx' \<degree>\<degree> map BVar (replace_list xs' x z))" by simp
        with x1 x2 x3 x4 rx' have "\<beta>\<eta>cl (t \<degree>\<degree> map BVar (xs @ z # replace_list x_m x z))
        (replace_BVar (rx \<degree>\<degree> map BVar xs') x z)" by argo
        then have x: "(symcl \<beta>\<eta>)\<^sup>*\<^sup>* (t \<degree>\<degree> map BVar (xs @ z # replace_list x_m x z))
        (replace_BVar (rx \<degree>\<degree> map BVar xs') x z)" by (metis mono_rtranclp symcl.elims)

        from s' replace_BVar_list_application have y1:
          "replace_BVar (ry \<degree>\<degree> map BVar ys') x z =
        replace_BVar (list_subst s' ys'' (length ys'')) x z \<degree>\<degree> map BVar (replace_list ys' x z)"
          by auto
        from replace_list_subst[of s' ys'' x z] have y2:
          "replace_BVar (list_subst s' ys'' (length ys'')) x z =
        list_subst (replace_BVar s' (x + length ys'') (z + length ys'')) (replace_list ys'' x z)
        (length ys'')" by blast

        from \<open>no_loose_bound s 0\<close> s'' \<beta>\<eta>cl_no_loose_bound have "no_loose_bound s'' 0" by blast
        with s' loose_bound_Abs_m[of "length ys''" s' 0] have
          "no_loose_bound s' (length ys'')" by force
        with replace_BVar_no_loose_bound have y3:
          "replace_BVar s' (x + length ys'') (z + length ys'') = s'" by simp

        from s' replace_list_append have
          "replace_list y_n x z = replace_list ys'' x z @ replace_list ys' x z" by force
        moreover obtain ry' where ry':
          "ry' = list_subst s' (replace_list ys'' x z) (length ys'')" by blast
        ultimately have
          "gamma_star (s'', replace_list y_n x z) (ry', replace_list ys' x z)"
          using s'[THEN conjunct2[THEN conjunct1]] replace_list_length[of ys'' x z] by auto

        with s'' \<beta>\<eta>cl_list_application[of s s'' "replace_list y_n x z"]
          gamma_star_eq[of s'' "replace_list y_n x z" ry' "replace_list ys' x z"]
          gamma_\<beta>\<eta>cl[of s'' "replace_list y_n x z" ry' "replace_list ys' x z"] have
          "\<beta>\<eta>cl (s \<degree>\<degree> map BVar (replace_list y_n x z))
        (ry' \<degree>\<degree> map BVar (replace_list ys' x z))" by simp
        with y1 y2 y3 ry' have "\<beta>\<eta>cl (s \<degree>\<degree> map BVar (replace_list y_n x z))
        (replace_BVar (ry \<degree>\<degree> map BVar ys') x z)" by argo
        with symcl_rtranclp[of \<beta>\<eta> "s \<degree>\<degree> map BVar (replace_list y_n x z)"
            "replace_BVar (ry \<degree>\<degree> map BVar ys') x z"] have y:
          "(symcl \<beta>\<eta>)\<^sup>*\<^sup>* (replace_BVar (ry \<degree>\<degree> map BVar ys') x z)
        (s \<degree>\<degree> map BVar (replace_list y_n x z))" by blast

        from x y eq show "closure \<beta>\<eta> (t \<degree>\<degree> map BVar (xs @ z # replace_list x_m x z))
        (s \<degree>\<degree> map BVar (replace_list y_n x z))" by fastforce
      qed
    qed
  next
    show "\<not>(x \<in> set y_n) \<longrightarrow> (\<exists>t'. \<beta>\<eta>cl t (Abs_m (length xs + 1) t') \<and> \<not> free t' 0 \<and>
      no_loose_bound t' (length xs + 1))" proof
      assume "\<not>(x \<in> set y_n)"
      have "\<not> free (s \<degree>\<degree> map BVar y_n) x" proof -
        from free_list_application[of s y_n x] have "free (s \<degree>\<degree> map BVar y_n) x =
          free s x \<or> find ((=) x) y_n \<noteq> None" by blast
        moreover from \<open>no_loose_bound s 0\<close> loose_bound_free have "\<not>free s x" by simp
        moreover from \<open>\<not>(x \<in> set y_n)\<close> have "find ((=) x) y_n = None"
          by (metis (full_types) find_None_iff)
        ultimately show ?thesis by fastforce
      qed

      moreover from s'' \<beta>\<eta>cl_list_application[of s s'' y_n] gamma_\<beta>\<eta>cl[of s'' y_n ry ys'] have
        "\<beta>\<eta>cl (s \<degree>\<degree> map BVar y_n) (ry \<degree>\<degree> map BVar ys')" by fastforce
      ultimately have "\<not> free (ry \<degree>\<degree> map BVar ys') x" using \<beta>\<eta>cl_not_free by presburger

      with t'' s'' have 0: "\<not> free (rx \<degree>\<degree> map BVar xs') x" by argo

      have "length xs'' \<le> length xs \<Longrightarrow> \<exists>t'. \<beta>\<eta>cl t (Abs_m (length xs + 1) t') \<and> \<not> free t' 0 \<and>
        no_loose_bound t' (length xs + 1)"
      proof -
        assume "length xs'' \<le> length xs"
        with t'[THEN conjunct1] obtain xs''' where xs''': "xs' = xs''' @ x # x_m"
          by (metis append_eq_append_conv_if)
        have "free (rx \<degree>\<degree> map BVar xs') x" proof -
          have "find ((=) x) (xs''' @ x # x_m) \<noteq> None"
            apply (induction xs''') apply simp by simp
          with xs''' free_list_application[of rx xs' x] show ?thesis by blast
        qed
        with 0 show ?thesis by blast
      qed

      moreover have
        "length xs'' > length xs \<Longrightarrow> \<exists>t'. \<beta>\<eta>cl t (Abs_m (length xs + 1) t') \<and> \<not> free t' 0 \<and>
          no_loose_bound t' (length xs + 1)" proof -
        assume "length xs'' > length xs"
        with t' obtain xs''' where xs''': "xs'' = xs @ x # xs'''" by (meson lemma22_lists)
        with t' Abs_m_less obtain t''' where t''': "t'' = Abs_m (length xs + 1) t'''" by fastforce
        with t' xs''' Abs_m_add have t'''2: "t''' = Abs_m (length xs''') t'"
          by (metis add.assoc length_Cons length_append plus_1_eq_Suc)

        from 0 free_list_application have "\<not>free rx x" by blast
        from t' xs''' list_subst_partial[of t' xs "x # xs'''" "length xs''"] have
          "rx = list_subst (list_subst t' xs (length xs'')) (x # xs''') (length (x # xs'''))"
          by simp
        then have 2: "rx =
          list_subst (list_subst t' xs (length xs'')[BVar (x + length xs''')/length xs''']) xs'''
          (length xs''')" by simp

        from xs''' list_subst_free[of xs "length xs''" t'] have 1:
          "free (list_subst t' xs (length xs'')) (length xs''') = free t' (length xs''')" by simp

        from t'''2 Abs_m_free have 0: "free t' (length xs''') = free t''' 0" by simp

        have "\<not>free t''' 0" proof
          assume "free t''' 0"
          with 0 have "free t' (length xs''')" by blast
          with 1 have "free (list_subst t' xs (length xs'')) (length xs''')" by argo
          then have "free (list_subst t' xs (length xs'')[BVar (x + length xs''')/length xs'''])
            (x + length xs''')" by force
          with list_subst_free'[of "length xs'''" "x + length xs'''" xs'''
              "list_subst t' xs (length xs'')[BVar (x + length xs''')/length xs''']"] have
            "free (list_subst (list_subst t' xs (length xs'')[BVar (x + length xs''')/length xs'''])
            xs''' (length xs''')) x" by simp
          with 2 have "free rx x" by presburger
          with \<open>\<not>free rx x\<close> show False by blast
        qed

        from \<open>no_loose_bound t 0\<close> t'' \<beta>\<eta>cl_no_loose_bound have "no_loose_bound t'' 0" by blast
        with loose_bound_Abs_m[of "length xs + 1" t'''] t''' have
          "no_loose_bound t''' (length xs + 1)" by force

        with t''' t''[THEN conjunct1] \<open>\<not>free t''' 0\<close> show ?thesis by fast
      qed

      ultimately show "\<exists>t'. \<beta>\<eta>cl t (Abs_m (length xs + 1) t') \<and> \<not> free t' 0 \<and>
        no_loose_bound t' (length xs + 1)" by fastforce
    qed
  qed
qed

lemma replace_BVar_Abs_m: "replace_BVar (Abs_m m t) x y = Abs_m m (replace_BVar t (x + m) (y + m))"
  apply (induction m arbitrary: x y)
   apply simp
  by auto

lemma replace_BVar_preserves_\<beta>\<eta>cl: "\<beta>\<eta>cl t t' \<Longrightarrow> \<beta>\<eta>cl (replace_BVar t x y) (replace_BVar t' x y)"
proof (induction rule: rtranclp.induct)
  case (rtrancl_refl a)
  then show ?case by blast
next
  case (rtrancl_into_rtrancl a b c)
  then show ?case using replace_BVar_preserves_beta replace_BVar_preserves_eta
    by (metis rtranclp.simps sup2CI sup2E)
qed

lemma \<beta>\<eta>_Abs: "\<beta>\<eta> (Abs t) (Abs t') \<Longrightarrow> \<beta>\<eta> t t'" proof -
  assume "\<beta>\<eta> (Abs t) (Abs t')"
  moreover have "beta (Abs t) (Abs t') \<Longrightarrow> ?thesis" by fast
  moreover have "eta (Abs t) (Abs t') \<Longrightarrow> ?thesis" proof -
    assume "eta (Abs t) (Abs t')"
    then show ?thesis proof cases
      case (eta s dummy)
      then show ?thesis proof (induction s arbitrary: t)
        case (BVar x)
        then show ?case by fastforce
      next
        case (Var x)
        then show ?case by simp
      next
        case (App s1 s2)
        then show ?case by force
      next
        case (Abs s)
        from this(2) have "beta t (s[BVar 0/0])" by blast
        moreover from Abs(3) have "t' = s[lift dummy 0/1]" by simp
        moreover from Abs(4) have "s[BVar 0/0] = s[lift dummy 0/1]" by simp
        ultimately show ?case by simp
      qed
    next
      case abs
      then show ?thesis by simp
    qed
  qed
  ultimately show ?thesis by fast
qed

lemma sym\<beta>\<eta>_Abs: "symcl \<beta>\<eta> (Abs t) (Abs t') \<Longrightarrow> symcl \<beta>\<eta> t t'" proof -
  assume "symcl \<beta>\<eta> (Abs t) (Abs t')"
  moreover have "\<beta>\<eta> (Abs t) (Abs t') \<Longrightarrow> ?thesis" using \<beta>\<eta>_Abs[of t t'] by force
  moreover have "\<beta>\<eta> (Abs t') (Abs t) \<Longrightarrow> ?thesis" using \<beta>\<eta>_Abs[of t' t] by auto
  ultimately show ?thesis by fastforce
qed

abbreviation "not_Abs t \<equiv> \<nexists>t'. t = Abs t'"

lemma \<beta>\<eta>cl_App: "\<beta>\<eta>cl s t \<Longrightarrow> \<beta>\<eta>cl (s \<degree> r) (t \<degree> r)"
  apply (induction rule: rtranclp.induct)
   apply blast
  by (metis beta.appL eta.appL rtranclp.simps sup2CI sup2E)

lemma \<beta>\<eta>cl_lift: "\<beta>\<eta>cl s t \<Longrightarrow> \<beta>\<eta>cl (lift s i) (lift t i)"
  apply (induction rule: rtranclp.induct)
   apply fast
  by (metis eta_lift lift_preserves_beta rtranclp.simps sup2CI sup2E)

lemma \<beta>\<eta>cl_Abs: "\<beta>\<eta>cl (Abs s) (Abs t) \<Longrightarrow> \<beta>\<eta>cl s t"
proof (induction "Abs s" arbitrary: s rule: converse_rtranclp_induct)
  case base
  then show ?case by simp
next
  case (step z)
  then show ?case proof (cases "not_Abs z")
    case True
    with step(1) have "eta (Abs s) z" by blast
    with True obtain z' dummy where z': "s = z' \<degree> BVar 0 \<and> \<not>free z' 0 \<and> z = z'[dummy/0]" by blast
    with step(2) have "\<beta>\<eta>cl (z'[dummy/0]) (Abs t)" by blast
    with \<beta>\<eta>cl_lift have "\<beta>\<eta>cl (lift (z'[dummy/0]) 0) (lift (Abs t) 0)" by blast
    moreover from z' lift_subst_dummy have "lift (z'[dummy/0]) 0 = z'" by blast
    ultimately have "\<beta>\<eta>cl s (Abs (lift t 1) \<degree> BVar 0)" using \<beta>\<eta>cl_App z' by simp
    moreover have "Abs (lift t 1) \<degree> BVar 0 \<rightarrow>\<^sub>\<beta> (lift t 1)[BVar 0/0]" by fast
    moreover have "(lift t 1)[BVar 0/0] = t" by fastforce
    ultimately show ?thesis by (metis rtranclp.simps sup2CI)
  next
    case False
    then obtain z' where z': "z = Abs z'" by fast
    with step(3)[of z'] have 0: "\<beta>\<eta>cl z' t" by blast
    from step(1) z' have "\<beta>\<eta> (Abs s) (Abs z')" by argo
    with \<beta>\<eta>_Abs have "\<beta>\<eta> s z'" by metis
    with 0 show ?thesis by (simp add: converse_rtranclp_into_rtranclp)
  qed
qed

lemma \<beta>\<eta>cl_confluence_Abs: "\<lbrakk>\<beta>\<eta>cl (Abs s) b; \<beta>\<eta>cl (Abs t) b\<rbrakk> \<Longrightarrow> \<exists>c. \<beta>\<eta>cl s c \<and> \<beta>\<eta>cl t c"
proof (induction "Abs s" arbitrary: s rule: converse_rtranclp_induct)
  case base
  then show ?case using \<beta>\<eta>cl_Abs by blast
next
  case (step z)
  then show ?case proof (cases "not_Abs z")
    case True
    with step(1) have "eta (Abs s) z" by blast
    with True obtain z' dummy where z': "s = z' \<degree> BVar 0 \<and> \<not>free z' 0 \<and> z = z'[dummy/0]" by blast
    with step(2) have "\<beta>\<eta>cl (z'[dummy/0]) b" by blast
    with \<beta>\<eta>cl_lift have "\<beta>\<eta>cl (lift (z'[dummy/0]) 0) (lift b 0)" by blast
    moreover from z' lift_subst_dummy have "lift (z'[dummy/0]) 0 = z'" by blast
    ultimately have 0: "\<beta>\<eta>cl s (lift b 0 \<degree> BVar 0)" using \<beta>\<eta>cl_App z' by simp

    from step(4) \<beta>\<eta>cl_lift have "\<beta>\<eta>cl (lift (Abs t) 0) (lift b 0)" by presburger
    with \<beta>\<eta>cl_App have "\<beta>\<eta>cl (Abs (lift t 1) \<degree> BVar 0) (lift b 0 \<degree> BVar 0)" by simp
    moreover have "Abs (lift t 1) \<degree> BVar 0 \<rightarrow>\<^sub>\<beta> (lift t 1)[BVar 0/0]" by fast
    moreover have "(lift t 1)[BVar 0/0] = t" by fastforce
    ultimately obtain t' where "\<beta>\<eta>cl (lift b 0 \<degree> BVar 0) t' \<and> \<beta>\<eta>cl t t'"
      using confluence[of "Abs (lift t 1) \<degree> BVar 0" "lift b 0 \<degree> BVar 0" t]
      by (metis r_into_rtranclp sup2CI)

    with 0 show ?thesis by (meson rtranclp_trans)
  next
    case False
    then obtain z' where z': "z = Abs z'" by fast
    with step(3)[of z'] step(4) obtain c where c: "\<beta>\<eta>cl z' c \<and> \<beta>\<eta>cl t c" by blast
    from step(1) z' have "\<beta>\<eta> (Abs s) (Abs z')" by argo
    with \<beta>\<eta>_Abs have "\<beta>\<eta> s z'" by metis
    with c show ?thesis by (meson converse_rtranclp_into_rtranclp)
  qed
qed

lemma fact5: "closure \<beta>\<eta> s t = closure \<beta>\<eta> (Abs s) (Abs t)" proof
  assume "closure \<beta>\<eta> s t"
  then have "(symcl \<beta>\<eta>)\<^sup>*\<^sup>* s t" by simp
  then have "(symcl \<beta>\<eta>)\<^sup>*\<^sup>* (Abs s) (Abs t)" proof (induction s t rule: rtranclp.induct)
    case (rtrancl_refl a)
    then show ?case by fast
  next
    case (rtrancl_into_rtrancl a b c)
    from this(2) have "symcl \<beta>\<eta> (Abs b) (Abs c)" by auto
    with rtrancl_into_rtrancl(3) show ?case by (simp add: rtranclp.rtrancl_into_rtrancl)
  qed
  then show "closure \<beta>\<eta> (Abs s) (Abs t)" by simp
next
  assume "closure \<beta>\<eta> (Abs s) (Abs t)"
  with closure_confluent[of "Abs s" "Abs t"] obtain b where
    "\<beta>\<eta>cl (Abs s) b \<and> \<beta>\<eta>cl (Abs t) b" by blast
  with \<beta>\<eta>cl_confluence_Abs[of s b t] obtain c where "\<beta>\<eta>cl s c \<and> \<beta>\<eta>cl t c" by blast
  with symcl_confluence_rtranclp[of \<beta>\<eta> s c t] show "closure \<beta>\<eta> s t" by auto
qed

lemma fact6: "closure \<beta>\<eta> (Abs s) t = closure \<beta>\<eta> s (lift t 0 \<degree> BVar 0)" proof -
  have "eta (Abs (lift t 0 \<degree> BVar 0)) t" by (metis eta free_lift not_less_zero subst_lift)
  then have "closure \<beta>\<eta> (Abs (lift t 0 \<degree> BVar 0)) t" by auto
  then have "closure \<beta>\<eta> (Abs s) (Abs (lift t 0 \<degree> BVar 0)) = closure \<beta>\<eta> (Abs s) t"
    by (meson closure_symmetric rtranclp_trans)
  moreover from fact5[of s "lift t 0 \<degree> BVar 0"] have
    "closure \<beta>\<eta> s (lift t 0 \<degree> BVar 0) = closure \<beta>\<eta> (Abs s) (Abs (lift t 0 \<degree> BVar 0))" by blast
  ultimately show ?thesis by blast
qed

fun mk_subst :: "(nat \<Rightarrow> dB) \<Rightarrow> dB \<Rightarrow> dB" where
"mk_subst xi (Var x) = xi x" |
"mk_subst _ (BVar x) = BVar x" |
"mk_subst xi (Abs t) = Abs (mk_subst xi t)" |
"mk_subst xi (r \<degree> s) = (mk_subst xi r) \<degree> (mk_subst xi s)"

abbreviation "subst_no_loose_bound xi \<equiv> \<forall>x. no_loose_bound (xi x) 0"

lemma mk_subst_free: "\<lbrakk>\<not>free t i; subst_no_loose_bound xi\<rbrakk> \<Longrightarrow> \<not>free (mk_subst xi t) i"
  apply (induction t arbitrary: i)
     apply simp
    apply (simp add: loose_bound_free)
   apply simp
  by simp

lemma mk_subst_loose_bound:
"\<lbrakk>no_loose_bound t i; subst_no_loose_bound xi\<rbrakk> \<Longrightarrow> no_loose_bound (mk_subst xi t) i"
  by (simp add: loose_bound_free mk_subst_free)

lemma fact7: "subst_no_loose_bound sigma \<Longrightarrow> mk_subst sigma (lift t i) = lift (mk_subst sigma t) i"
  apply (induction t arbitrary: i)
     apply simp
    apply (metis lift.simps(4) lift_subst_dummy loose_bound_free loose_bound_subst mk_subst.simps(1)
      zero_le)
   apply fastforce
  by auto

lemma mk_subst_subst: "subst_no_loose_bound sigma \<Longrightarrow>
mk_subst sigma (u[v/i]) = (mk_subst sigma u)[mk_subst sigma v/i]" proof (induction u arbitrary: i v)
  case (BVar x)
  show ?case apply (rule linorder_cases[of x i]) by auto
next
  case (Var x)
  then show ?case by (metis loose_bound_subst mk_subst.simps(1) subst_Var zero_le)
next
  case (App u1 u2)
  then show ?case by fastforce
next
  case (Abs u)
  then show ?case by (simp add: fact7)
qed

lemma mk_subst_preserves_beta:
"\<lbrakk>s \<rightarrow>\<^sub>\<beta> t; subst_no_loose_bound sigma\<rbrakk> \<Longrightarrow> mk_subst sigma s \<rightarrow>\<^sub>\<beta> mk_subst sigma t"
  apply (induction rule: beta.induct)
     apply (simp add: mk_subst_subst)
    apply simp
   apply simp
  by simp

lemma mk_subst_preserves_eta:
"\<lbrakk>s \<rightarrow>\<^sub>\<eta> t; subst_no_loose_bound sigma\<rbrakk> \<Longrightarrow> mk_subst sigma s \<rightarrow>\<^sub>\<eta> mk_subst sigma t"
proof (induction rule: eta.induct)
  case (eta s dummy)

  have 0: "mk_subst sigma (Abs (s \<degree> BVar 0)) = Abs (mk_subst sigma s \<degree> BVar 0)" by auto

  from mk_subst_subst eta(2) have 1:
    "mk_subst sigma (s[dummy/0]) = (mk_subst sigma s)[mk_subst sigma dummy/0]" by blast

  from eta mk_subst_free loose_bound_free have "\<not>free (mk_subst sigma s) 0" by blast
  then have "Abs (mk_subst sigma s \<degree> BVar 0) \<rightarrow>\<^sub>\<eta> (mk_subst sigma s)[dummy/0]" by blast

  moreover from eta(1) \<open>\<not>free (mk_subst sigma s) 0\<close> have
    "(mk_subst sigma s)[mk_subst sigma dummy/0] = (mk_subst sigma s)[dummy/0]" by simp

  ultimately show ?case using 0 1 by argo
next
  case (appL s t u)
  then show ?case by simp
next
  case (appR s t u)
  then show ?case by simp
next
  case (abs s t)
  then show ?case by simp
qed

lemma fact8_1: "\<lbrakk>s \<rightarrow>\<^sub>\<beta>\<^sup>* t; subst_no_loose_bound sigma\<rbrakk> \<Longrightarrow> mk_subst sigma s \<rightarrow>\<^sub>\<beta>\<^sup>* mk_subst sigma t"
proof (induction rule: rtranclp.induct)
case (rtrancl_refl a)
  then show ?case by fast
next
  case (rtrancl_into_rtrancl a b c)
  from this(2,4) mk_subst_preserves_beta[of b c sigma] have
    "mk_subst sigma b \<rightarrow>\<^sub>\<beta> mk_subst sigma c" by fast
  with rtrancl_into_rtrancl(3,4) show ?case by simp
qed

lemma fact8_2: "\<lbrakk>s \<rightarrow>\<^sub>\<eta>\<^sup>* t; subst_no_loose_bound sigma\<rbrakk> \<Longrightarrow> mk_subst sigma s \<rightarrow>\<^sub>\<eta>\<^sup>* mk_subst sigma t"
proof (induction rule: rtranclp.induct)
case (rtrancl_refl a)
  then show ?case by fast
next
  case (rtrancl_into_rtrancl a b c)
  from this(2,4) mk_subst_preserves_eta[of b c sigma] have
    "mk_subst sigma b \<rightarrow>\<^sub>\<eta> mk_subst sigma c" by fast
  with rtrancl_into_rtrancl(3,4) show ?case by simp
qed

lemma mk_subst_preserves_symcl\<beta>\<eta>: "\<lbrakk>symcl \<beta>\<eta> s t; subst_no_loose_bound sigma\<rbrakk> \<Longrightarrow>
symcl \<beta>\<eta> (mk_subst sigma s) (mk_subst sigma t)"
  using mk_subst_preserves_beta mk_subst_preserves_eta by auto

lemma fact8_3: "\<lbrakk>closure \<beta>\<eta> s t; subst_no_loose_bound sigma\<rbrakk> \<Longrightarrow>
closure \<beta>\<eta> (mk_subst sigma s) (mk_subst sigma t)" proof (induction rule: rtranclp.induct)
case (rtrancl_refl a)
  then show ?case by fast
next
  case (rtrancl_into_rtrancl a b c)
  then show ?case using mk_subst_preserves_symcl\<beta>\<eta>[of b c sigma]
    by (meson r_into_rtranclp rtranclp_trans)
qed

lemma closure_\<beta>\<eta>_App: "closure \<beta>\<eta> s t \<Longrightarrow> closure \<beta>\<eta> (s \<degree> r) (t \<degree> r)"
  apply (induction rule: rtranclp.induct)
   apply rule
  apply (erule rtranclp.rtrancl_into_rtrancl)
  by auto

lemma closure\<beta>\<eta>_list_application: "closure \<beta>\<eta> s t \<Longrightarrow> closure \<beta>\<eta> (s \<degree>\<degree> xs) (t \<degree>\<degree> xs)"
  apply (induction rule: rtranclp.induct)
   apply blast
  by (metis apps_preserves_beta eta_list rtranclp.rtrancl_into_rtrancl sup2CI sup2E symcl.simps)

lemma fact10: "\<lbrakk>list_all2 (\<noteq>) x_m y_m; e \<turnstile> t \<degree>\<degree> map BVar x_m : T; e \<turnstile> t \<degree>\<degree> map BVar y_m : T';
no_loose_bound t 0; closure \<beta>\<eta> (t \<degree>\<degree> map BVar x_m) (t \<degree>\<degree> map BVar y_m)\<rbrakk> \<Longrightarrow>
\<exists>t'. no_loose_bound t' 0 \<and> closure \<beta>\<eta> t (Abs_m (length x_m) t')"
proof (induction arbitrary: t rule: list_all2_induct)
  case Nil
  then show ?case by auto
next
  case (Cons x xs y ys)
  from lemma22[of t  0 "[]" x xs "[]" y ys "length xs" e T T'] Cons.prems Cons.hyps(1,2)
    list_all2_lengthD[of "(\<noteq>)" xs ys] obtain t' where t':
    "\<beta>\<eta>cl t (Abs_m (length [] + 1) t') \<and> \<not> free t' 0 \<and> no_loose_bound t' (length [] + 1)"
    by fastforce
  then have "no_loose_bound t' 0"
    by (metis add_cancel_right_left leI less_one list.size(3) loose_bound_free)
  then have "no_loose_bound (t'[BVar x/0]) 0" using loose_bound_subst by auto

  from \<open>no_loose_bound t' 0\<close> have "t'[BVar x/0] = t'" using loose_bound_subst by blast

  have x': "Abs t' \<degree>\<degree> map BVar (x # xs) \<rightarrow>\<^sub>\<beta> t'[BVar x/0] \<degree>\<degree> map BVar xs" by simp
  then have 0: "closure \<beta>\<eta> (t'[BVar x/0] \<degree>\<degree> map BVar xs) (Abs t' \<degree>\<degree> map BVar (x # xs))" by force

  from t'[THEN conjunct1] have "\<beta>\<eta>cl t (Abs t')" by fastforce
  then have "closure \<beta>\<eta> t (Abs t')" using symcl_confluence_rtranclp by blast

  with 0 have x: "closure \<beta>\<eta> (t'[BVar x/0] \<degree>\<degree> map BVar xs) (t \<degree>\<degree> map BVar (x # xs))"
    using closure\<beta>\<eta>_list_application[of t "Abs t'" "map BVar (x # xs)"]
    by (meson closure_symmetric rtranclp_trans)

  have y': "Abs t' \<degree>\<degree> map BVar (y # ys) \<rightarrow>\<^sub>\<beta> t'[BVar y/0] \<degree>\<degree> map BVar ys" by simp
  then have 0: "closure \<beta>\<eta> (t'[BVar y/0] \<degree>\<degree> map BVar ys) (Abs t' \<degree>\<degree> map BVar (y # ys))" by force

  from t'[THEN conjunct1] have "\<beta>\<eta>cl t (Abs t')" by fastforce
  then have "closure \<beta>\<eta> t (Abs t')" using symcl_confluence_rtranclp by blast

  with 0 have y: "closure \<beta>\<eta> (t'[BVar y/0] \<degree>\<degree> map BVar ys) (t \<degree>\<degree> map BVar (y # ys))"
    using closure\<beta>\<eta>_list_application[of t "Abs t'" "map BVar (y # ys)"]
    by (meson closure_symmetric rtranclp_trans)

  with x Cons.prems(4) have "closure \<beta>\<eta> (t'[BVar x/0] \<degree>\<degree> map BVar xs) (t'[BVar y/0] \<degree>\<degree> map BVar ys)"
    by (metis closure_symmetric rtranclp_trans)

  with subst_not_free t' have 1:
    "closure \<beta>\<eta> (t'[BVar x/0] \<degree>\<degree> map BVar xs) (t'[BVar x/0] \<degree>\<degree> map BVar ys)" by metis

  from x' \<open>\<beta>\<eta>cl t (Abs t')\<close> have "\<beta>\<eta>cl (t \<degree>\<degree> map BVar (x # xs)) (t'[BVar x/0] \<degree>\<degree> map BVar xs)"
    by (meson \<beta>\<eta>cl_list_application  rtranclp.rtrancl_into_rtrancl sup2CI)
  with Cons.prems(1) subject_reduction_\<beta>\<eta> have x'': "e \<turnstile> t'[BVar x/0] \<degree>\<degree> map BVar xs : T" by blast

  from y' \<open>\<beta>\<eta>cl t (Abs t')\<close> have "\<beta>\<eta>cl (t \<degree>\<degree> map BVar (y # ys)) (t'[BVar y/0] \<degree>\<degree> map BVar ys)"
    by (meson \<beta>\<eta>cl_list_application  rtranclp.rtrancl_into_rtrancl sup2CI)
  with Cons.prems(2) subject_reduction_\<beta>\<eta> have "e \<turnstile> t'[BVar y/0] \<degree>\<degree> map BVar ys : T'" by blast
  with subst_not_free t' have "e \<turnstile> t'[BVar x/0] \<degree>\<degree> map BVar ys : T'" by metis

  with Cons.IH[of "t'[BVar x/0]"] \<open>no_loose_bound (t'[BVar x/0]) 0\<close> x'' 1 obtain t'' where t'':
    "no_loose_bound t'' 0 \<and> closure \<beta>\<eta> (t'[BVar x/0]) (Abs_m (length xs) t'')" by blast
  with \<open>t'[BVar x/0] = t'\<close> \<open>closure \<beta>\<eta> t (Abs t')\<close> have
    "closure \<beta>\<eta> t (Abs (Abs_m (length xs) t''))" by (metis fact5 rtranclp_trans)
  then have "closure \<beta>\<eta> t (Abs_m (length (x # xs)) t'')" by fastforce
  with t'' show ?case by blast
qed

lemma fact11: "\<lbrakk>no_loose_bound s 0; no_loose_bound t 0;
closure \<beta>\<eta> (s \<degree>\<degree> map BVar x_m) (t \<degree>\<degree> map BVar y_n); set x_m \<inter> set y_n = {}\<rbrakk> \<Longrightarrow>
\<exists>s' t'. closure \<beta>\<eta> t (Abs_m (length y_n) t') \<and> closure \<beta>\<eta> s (Abs_m (length x_m) s') \<and>
closure \<beta>\<eta> t' s'"
proof (induction x_m arbitrary: s)
  case Nil
  then show ?case proof (induction y_n arbitrary: t)
    case Nil
    then show ?case by auto
  next
    case (Cons a y_n)
    have "a \<notin> set []" by simp
    moreover from Cons.prems(3) have "closure \<beta>\<eta> (t \<degree>\<degree> map BVar (a # y_n)) (s \<degree>\<degree> map BVar [])"
      using closure_symmetric by blast
    ultimately obtain t' where t':
      "\<beta>\<eta>cl t (Abs_m (length [] + 1) t') \<and> \<not> free t' 0 \<and> no_loose_bound t' (length [] + 1)"
      using lemma23[of t s "[]" a y_n "[]"] Cons.prems(1-3) by auto

    then have "no_loose_bound t' 0"
      by (metis add_cancel_right_left leI less_one list.size(3) loose_bound_free)
    then have "no_loose_bound (t'[BVar a/0]) 0" using loose_bound_subst by auto

    from \<open>no_loose_bound t' 0\<close> have "t'[BVar a/0] = t'" using loose_bound_subst by blast

    have y: "Abs t' \<degree>\<degree> map BVar (a # y_n) \<rightarrow>\<^sub>\<beta> t'[BVar a/0] \<degree>\<degree> map BVar y_n" by simp
    then have 0: "closure \<beta>\<eta> (t'[BVar a/0] \<degree>\<degree> map BVar y_n) (Abs t' \<degree>\<degree> map BVar (a # y_n))" by force

    from t'[THEN conjunct1] have "\<beta>\<eta>cl t (Abs t')" by fastforce
    then have "closure \<beta>\<eta> t (Abs t')" using symcl_confluence_rtranclp by blast

    with 0 have "closure \<beta>\<eta> (t'[BVar a/0] \<degree>\<degree> map BVar y_n) (t \<degree>\<degree> map BVar (a # y_n))"
      using closure\<beta>\<eta>_list_application[of t "Abs t'" "map BVar (a # y_n)"]
      by (meson closure_symmetric rtranclp_trans)
    with Cons.prems(3) have 1: "closure \<beta>\<eta> (s \<degree>\<degree> map BVar []) (t'[BVar a/0] \<degree>\<degree> map BVar y_n)"
      by (meson closure_symmetric rtranclp_trans)

    from y \<open>\<beta>\<eta>cl t (Abs t')\<close> have "\<beta>\<eta>cl (t \<degree>\<degree> map BVar (a # y_n)) (t'[BVar a/0] \<degree>\<degree> map BVar y_n)"
      by (meson \<beta>\<eta>cl_list_application  rtranclp.rtrancl_into_rtrancl sup2CI)

    from Cons.prems(4) have "set [] \<inter> set y_n = {}" by auto

    with Cons.IH[of "t'[BVar a/0]"] Cons.prems(1,3) 1 \<open>no_loose_bound (t'[BVar a/0]) 0\<close>
    obtain s' t'' where t'':
      "closure \<beta>\<eta> (t'[BVar a/0]) (Abs_m (length y_n) t'') \<and> closure \<beta>\<eta> s (Abs_m (length []) s') \<and>
    closure \<beta>\<eta> t'' s'" by auto

    with \<open>t'[BVar a/0] = t'\<close> \<open>closure \<beta>\<eta> t (Abs t')\<close> have
      "closure \<beta>\<eta> t (Abs (Abs_m (length y_n) t''))" by (metis fact5 rtranclp_trans)
    then have "closure \<beta>\<eta> t (Abs_m (length (a # y_n)) t'')" by fastforce

    with t'' show ?case by auto
  qed
next
  case (Cons a x_m)
  from Cons.prems(4) have "a \<notin> set y_n" by simp
  then obtain s' where s':
    "\<beta>\<eta>cl s (Abs_m (length [] + 1) s') \<and> \<not> free s' 0 \<and> no_loose_bound s' (length [] + 1)"
    using lemma23[of s t "[]" a x_m y_n] Cons.prems(1-3) by force
  then have "no_loose_bound s' 0"
    by (metis add_cancel_right_left leI less_one list.size(3) loose_bound_free)
  then have "no_loose_bound (s'[BVar a/0]) 0" using loose_bound_subst by auto

  from \<open>no_loose_bound s' 0\<close> have "s'[BVar a/0] = s'" using loose_bound_subst by blast

  have x: "Abs s' \<degree>\<degree> map BVar (a # x_m) \<rightarrow>\<^sub>\<beta> s'[BVar a/0] \<degree>\<degree> map BVar x_m" by simp
  then have 0: "closure \<beta>\<eta> (s'[BVar a/0] \<degree>\<degree> map BVar x_m) (Abs s' \<degree>\<degree> map BVar (a # x_m))" by force

  from s'[THEN conjunct1] have "\<beta>\<eta>cl s (Abs s')" by fastforce
  then have "closure \<beta>\<eta> s (Abs s')" using symcl_confluence_rtranclp by blast

  with 0 have "closure \<beta>\<eta> (s'[BVar a/0] \<degree>\<degree> map BVar x_m) (s \<degree>\<degree> map BVar (a # x_m))"
    using closure\<beta>\<eta>_list_application[of s "Abs s'" "map BVar (a # x_m)"]
    by (meson closure_symmetric rtranclp_trans)

  with Cons.prems(3) have 1: "closure \<beta>\<eta> (s'[BVar a/0] \<degree>\<degree> map BVar x_m) (t \<degree>\<degree> map BVar y_n)"
    by force

  from x \<open>\<beta>\<eta>cl s (Abs s')\<close> have "\<beta>\<eta>cl (s \<degree>\<degree> map BVar (a # x_m)) (s'[BVar a/0] \<degree>\<degree> map BVar x_m)"
    by (meson \<beta>\<eta>cl_list_application  rtranclp.rtrancl_into_rtrancl sup2CI)

  from Cons.prems(4) have "set x_m \<inter> set y_n = {}" by auto

  with Cons.IH[of "s'[BVar a/0]"] Cons.prems(2,4) 1 \<open>no_loose_bound (s'[BVar a/0]) 0\<close>
    obtain s'' t' where s'':
    "closure \<beta>\<eta> t (Abs_m (length y_n) t') \<and> closure \<beta>\<eta> (s'[BVar a/0]) (Abs_m (length x_m) s'') \<and>
    closure \<beta>\<eta> t' s''" by blast

  with \<open>s'[BVar a/0] = s'\<close> \<open>closure \<beta>\<eta> s (Abs s')\<close> have
    "closure \<beta>\<eta> s (Abs (Abs_m (length x_m) s''))" by (metis fact5 rtranclp_trans)
  then have "closure \<beta>\<eta> s (Abs_m (length (a # x_m)) s'')" by fastforce

  with s'' show ?case by blast
qed

fun decr :: "dB \<Rightarrow> nat \<Rightarrow> dB" where
"decr t i = t[BVar i/i]"

lemma decr_free: "\<not>free t i \<Longrightarrow> decr t i = t[s/i]" using subst_not_free[of t i "BVar i" s] by simp

lemma decr_no_loose_bound: "no_loose_bound t (i + 1) \<Longrightarrow> j < i \<Longrightarrow> no_loose_bound (decr t j) i"
proof (induction t arbitrary: i j)
  case (BVar x)
  then have "x \<le> i" by auto
  show ?case proof (cases "x > j")
    case True
    then have "decr (BVar x) j = BVar (x - 1)" using subst_BVar by auto
    then show ?thesis using \<open>x \<le> i\<close> True by auto
  next
    case False
    with BVar have "x < i" by linarith
    moreover from False have "decr (BVar x) j = BVar x" using subst_BVar by auto
    ultimately show ?thesis by force
  qed
next
  case (Var x)
  then show ?case by simp
next
  case (App t1 t2)
  then show ?case by simp
next
  case (Abs t)
  then show ?case by auto
qed

lemma loose_bound_app:
  "\<lbrakk>no_loose_bound t i; no_loose_bound t' j\<rbrakk> \<Longrightarrow> no_loose_bound (t \<degree> t') (max i j)"
  using loose_bound_free by auto

lemma typings_BVar_unique: "e \<tturnstile> map BVar xs : Ts \<Longrightarrow> e \<tturnstile> map BVar xs : Ts' \<Longrightarrow> Ts = Ts'"
proof (induction xs arbitrary: Ts Ts')
  case Nil
  then show ?case by simp
next
  case (Cons a xs)
  have "\<exists>T1 T2. Ts = T1 # T2" proof -
    have "Ts \<noteq> []" using Cons.prems(1) by fastforce
    then show ?thesis by (meson list.exhaust)
  qed
  then obtain T1 T2 where Ts: "Ts = T1 # T2" by fast
  with Cons.prems(1) have T1: "e \<turnstile> BVar a : T1 \<and> e \<tturnstile> map BVar xs : T2" by force

  have "\<exists>T1 T2. Ts' = T1 # T2" proof -
    have "Ts' \<noteq> []" using Cons.prems(2) by fastforce
    then show ?thesis by (meson list.exhaust)
  qed
  then obtain T3 T4 where Ts': "Ts' = T3 # T4" by fast
  with Cons.prems(2) have T3: "e \<turnstile> BVar a : T3 \<and> e \<tturnstile> map BVar xs : T4" by force

  with T1 Cons.IH[of T2 T4] have "T2 = T4" by argo
  moreover from T1 T3 have "T1 = T3" by blast
  ultimately show ?case using Ts Ts' by fast
qed

lemma fact12: "\<lbrakk>length x_m = length y_m; e \<tturnstile> map BVar x_m : Ts; e \<tturnstile> map BVar z_m : Ts;
e \<tturnstile> map BVar y_m : Ts'; e \<tturnstile> map BVar z'_m : Ts';
e \<turnstile> t \<degree>\<degree> map BVar x_m : T; e \<turnstile> t \<degree>\<degree> map BVar y_m : T'; no_loose_bound t j;
closure \<beta>\<eta> (t \<degree>\<degree> map BVar x_m) (t \<degree>\<degree> map BVar y_m); \<forall>i. x_m ! i = y_m ! i \<longrightarrow> z_m ! i = z'_m ! i;
length z_m = length x_m; length z'_m = length y_m\<rbrakk> \<Longrightarrow>
closure \<beta>\<eta> (t \<degree>\<degree> map BVar z_m) (t \<degree>\<degree> map BVar z'_m)"
proof (induction arbitrary: t z_m z'_m j Ts Ts' rule: list_induct2)
  case Nil
  then show ?case by simp
next
  case (Cons x xs y ys)
  from lemma22[of t j "[]" x xs "[]" y ys "length xs" e T T'] Cons.prems(5-8) Cons.hyps have 0:
    "(x = y \<longrightarrow> (\<forall>z. closure \<beta>\<eta> (t \<degree>\<degree> map BVar ([] @ z # xs)) (t \<degree>\<degree> map BVar ([] @ z # ys)))) \<and>
    (x \<noteq> y \<longrightarrow> (\<exists>t'. \<beta>\<eta>cl t (Abs_m (length [] + 1) t') \<and> \<not> free t' 0 \<and>
    no_loose_bound t' (length [] + 1 + j)))" by fastforce

  from Cons.prems(10) obtain z zs where zs: "z_m = z # zs"
    by (meson Suc_le_eq Suc_le_length_iff nth_equalityI)
  with Cons.prems(10) have "length zs = length xs" by simp
  from Cons.prems(11) obtain z' z's where z's: "z'_m = z' # z's"
    by (meson Suc_le_eq Suc_le_length_iff nth_equalityI)
  with Cons.prems(11) have "length z's = length ys" by simp

  have "\<exists>Tx T1. Ts = Tx # T1" proof -
    have "Ts \<noteq> []" using Cons.prems(1) by fastforce
    then show ?thesis by (meson list.exhaust)
  qed
  then obtain Tx T1 where T1: "Ts = Tx # T1" by blast
  with Cons.prems(1) have Txs: "e \<tturnstile> map BVar xs : T1" by fastforce
  from T1 Cons.prems(2) zs have Tzs: "e \<tturnstile> map BVar zs : T1" by force

  have "\<exists>Tx T2. Ts' = Tx # T2" proof -
    have "Ts' \<noteq> []" using Cons.prems(3) by fastforce
    then show ?thesis by (meson list.exhaust)
  qed
  then obtain Tx T2 where T2: "Ts' = Tx # T2" by blast
  with Cons.prems(3) have Tys: "e \<tturnstile> map BVar ys : T2" by fastforce
  from T2 Cons.prems(4) z's have Tz's: "e \<tturnstile> map BVar z's : T2" by force

  show ?case proof (cases "x = y")
    case True
    with 0 have "closure \<beta>\<eta> (t \<degree>\<degree> map BVar ([] @ z # xs)) (t \<degree>\<degree> map BVar ([] @ z # ys))" by blast
    then have 1: "closure \<beta>\<eta> (t \<degree> BVar z \<degree>\<degree> map BVar xs) (t \<degree> BVar z \<degree>\<degree> map BVar ys)" by auto

    have T: "e \<turnstile> t \<degree>\<degree> map BVar (z # xs) : T" proof -
      from Cons.prems(5) list_app_typeD[of e t "map BVar (x # xs)" T] obtain Ts where Ts:
        "e \<turnstile> t : Ts \<Rrightarrow> T \<and> e \<tturnstile> map BVar (x # xs) : Ts" by fast

      have "\<exists>Tx Ts'. Ts = Tx # Ts'" proof -
        have "Ts \<noteq> []" using Ts by fastforce
        then show ?thesis by (meson list.exhaust)
      qed
      then obtain Tx Ts' where Ts': "Ts = Tx # Ts'" by blast

      with Ts have Tx: "e \<turnstile> BVar x : Tx" by simp

      from Ts Cons.prems(1,2) zs typings_BVar_unique[of e "x # xs" Ts] have
        "e \<tturnstile> map BVar (z # zs) : Ts" by blast
      with Ts' have "e \<turnstile> BVar z : Tx" by simp
      with Ts Ts' have "e \<tturnstile> map BVar (z # xs) : Ts" by force
      with Ts list_app_typeI[of e t Ts T "map BVar (z # xs)"] show
        "e \<turnstile> t \<degree>\<degree> map BVar (z # xs) : T" by fastforce
    qed
    have T': "e \<turnstile> t \<degree>\<degree> map BVar (z # ys) : T'" proof -
      from Cons.prems(6) list_app_typeD[of e t "map BVar (y # ys)" T'] obtain Ts where Ts:
        "e \<turnstile> t : Ts \<Rrightarrow> T' \<and> e \<tturnstile> map BVar (y # ys) : Ts" by blast

      have "\<exists>Tx Ts'. Ts = Tx # Ts'" proof -
        have "Ts \<noteq> []" using Ts by fastforce
        then show ?thesis by (meson list.exhaust)
      qed
      then obtain Ty Ts' where Ts': "Ts = Ty # Ts'" by blast

      with Ts have Tx: "e \<turnstile> BVar y : Ty" by simp

      from Ts Cons.prems(3,4) z's typings_BVar_unique[of e "y # ys" Ts] have
        "e \<tturnstile> map BVar (z' # z's) : Ts" by blast
      with Ts' have "e \<turnstile> BVar z' : Ty" by simp
      with Ts Ts' have "e \<tturnstile> map BVar (z' # ys) : Ts" by force
      with Ts list_app_typeI[of e t Ts T' "map BVar (z' # ys)"] have
        "e \<turnstile> t \<degree>\<degree> map BVar (z' # ys) : T'" by fastforce
      moreover from True Cons.prems(9) zs z's have "z = z'" by (metis nth_Cons_0)
      ultimately show ?thesis by fast
    qed

    have "no_loose_bound (BVar z) (z + 1)" by simp
    with loose_bound_app Cons.prems(7) have 2:
      "no_loose_bound (t \<degree> BVar z) (max j (z + 1))" by blast

    from Cons.prems(9) zs z's have "\<forall>i. xs ! i = ys ! i \<longrightarrow> zs ! i = z's ! i"
      by (metis nth_Cons_Suc)

    with 1 2 T T' Cons.IH[of T1 zs T2 z's "t \<degree> BVar z" "max j (z + 1)"] Txs Tys Tzs Tz's
      \<open>length zs = length xs\<close> \<open>length z's = length ys\<close> have
      "closure \<beta>\<eta> (t \<degree> BVar z \<degree>\<degree> map BVar zs) (t \<degree> BVar z \<degree>\<degree> map BVar z's)" by fastforce

    moreover from True zs z's Cons.prems(9) have "z = z'" by (metis nth_Cons_0)
    ultimately show ?thesis using zs z's by force
  next
    case False
    with 0 obtain t' where t': "\<beta>\<eta>cl t (Abs_m (length [] + 1) t') \<and> \<not> free t' 0 \<and>
    no_loose_bound t' (length [] + 1 + j)" by blast
    have "no_loose_bound (t'[BVar x/0]) j" proof (cases j)
      case 0
      then show ?thesis using t' by (simp add: loose_bound_free)
    next
      case (Suc nat)
      with decr_no_loose_bound[of t' j 0] t' have "no_loose_bound (decr t' 0) j" by fastforce
      with t' show ?thesis using decr_free by presburger
    qed

    have x': "Abs t' \<degree>\<degree> map BVar (x # xs) \<rightarrow>\<^sub>\<beta> t'[BVar x/0] \<degree>\<degree> map BVar xs" by simp
    then have 0: "closure \<beta>\<eta> (t'[BVar x/0] \<degree>\<degree> map BVar xs) (Abs t' \<degree>\<degree> map BVar (x # xs))" by force

    from t'[THEN conjunct1] have "\<beta>\<eta>cl t (Abs t')" by fastforce
    then have "closure \<beta>\<eta> t (Abs t')" using symcl_confluence_rtranclp by blast

    with 0 have x: "closure \<beta>\<eta> (t'[BVar x/0] \<degree>\<degree> map BVar xs) (t \<degree>\<degree> map BVar (x # xs))"
      using closure\<beta>\<eta>_list_application[of t "Abs t'" "map BVar (x # xs)"]
      by (meson closure_symmetric rtranclp_trans)

    have y': "Abs t' \<degree>\<degree> map BVar (y # ys) \<rightarrow>\<^sub>\<beta> t'[BVar y/0] \<degree>\<degree> map BVar ys" by simp
    then have 0: "closure \<beta>\<eta> (t'[BVar y/0] \<degree>\<degree> map BVar ys) (Abs t' \<degree>\<degree> map BVar (y # ys))" by force

    from t'[THEN conjunct1] have "\<beta>\<eta>cl t (Abs t')" by fastforce
    then have "closure \<beta>\<eta> t (Abs t')" using symcl_confluence_rtranclp by blast

    with 0 have y: "closure \<beta>\<eta> (t'[BVar y/0] \<degree>\<degree> map BVar ys) (t \<degree>\<degree> map BVar (y # ys))"
      using closure\<beta>\<eta>_list_application[of t "Abs t'" "map BVar (y # ys)"]
      by (meson closure_symmetric rtranclp_trans)

    with x Cons.prems(8) have
      "closure \<beta>\<eta> (t'[BVar x/0] \<degree>\<degree> map BVar xs) (t'[BVar y/0] \<degree>\<degree> map BVar ys)"
      by (metis closure_symmetric rtranclp_trans)

    with subst_not_free t' have 1:
      "closure \<beta>\<eta> (t'[BVar x/0] \<degree>\<degree> map BVar xs) (t'[BVar x/0] \<degree>\<degree> map BVar ys)" by metis

    from x' \<open>\<beta>\<eta>cl t (Abs t')\<close> have "\<beta>\<eta>cl (t \<degree>\<degree> map BVar (x # xs)) (t'[BVar x/0] \<degree>\<degree> map BVar xs)"
      by (meson \<beta>\<eta>cl_list_application  rtranclp.rtrancl_into_rtrancl sup2CI)
    with Cons.prems(5) subject_reduction_\<beta>\<eta> have x'': "e \<turnstile> t'[BVar x/0] \<degree>\<degree> map BVar xs : T" by blast

    from y' \<open>\<beta>\<eta>cl t (Abs t')\<close> have "\<beta>\<eta>cl (t \<degree>\<degree> map BVar (y # ys)) (t'[BVar y/0] \<degree>\<degree> map BVar ys)"
      by (meson \<beta>\<eta>cl_list_application  rtranclp.rtrancl_into_rtrancl sup2CI)
    with Cons.prems(6) subject_reduction_\<beta>\<eta> have "e \<turnstile> t'[BVar y/0] \<degree>\<degree> map BVar ys : T'" by blast
    with subst_not_free t' have 2: "e \<turnstile> t'[BVar x/0] \<degree>\<degree> map BVar ys : T'" by metis

    from zs z's Cons.prems(9) have 3: "\<forall>i. xs ! i = ys ! i \<longrightarrow> zs ! i = z's ! i"
      by (metis nth_Cons_Suc)

    from zs Cons.prems(10) have "length zs = length xs" by simp
    moreover from z's Cons.prems(11) have "length z's = length ys" by simp

    ultimately have "closure \<beta>\<eta> (t'[BVar x/0] \<degree>\<degree> map BVar zs) (t'[BVar x/0] \<degree>\<degree> map BVar z's)"
      using Cons.IH[of T1 zs T2 z's "t'[BVar x/0]" j] \<open>no_loose_bound (t'[BVar x/0]) j\<close> x'' 1 2 3
        Txs Tys Tzs Tz's by blast
    with subst_not_free t' have 4:
      "closure \<beta>\<eta> (t'[BVar z/0] \<degree>\<degree> map BVar zs) (t'[BVar z'/0] \<degree>\<degree> map BVar z's)" by metis

    have "Abs t' \<degree>\<degree> map BVar (z # zs) \<rightarrow>\<^sub>\<beta> t'[BVar z/0] \<degree>\<degree> map BVar zs" by simp
    with \<open>\<beta>\<eta>cl t (Abs t')\<close> zs have "\<beta>\<eta>cl (t \<degree>\<degree> map BVar z_m) (t'[BVar z/0] \<degree>\<degree> map BVar zs)"
      by (meson \<beta>\<eta>cl_list_application  rtranclp.rtrancl_into_rtrancl sup2CI)
    then have x''': "closure \<beta>\<eta> (t \<degree>\<degree> map BVar z_m) (t'[BVar z/0] \<degree>\<degree> map BVar zs)"
      using symcl_confluence_rtranclp by blast

    have "Abs t' \<degree>\<degree> map BVar (z' # z's) \<rightarrow>\<^sub>\<beta> t'[BVar z'/0] \<degree>\<degree> map BVar z's" by simp
    with \<open>\<beta>\<eta>cl t (Abs t')\<close> z's have "\<beta>\<eta>cl (t \<degree>\<degree> map BVar z'_m) (t'[BVar z'/0] \<degree>\<degree> map BVar z's)"
      by (meson \<beta>\<eta>cl_list_application  rtranclp.rtrancl_into_rtrancl sup2CI)
    then have y''': "closure \<beta>\<eta> (t \<degree>\<degree> map BVar z'_m) (t'[BVar z'/0] \<degree>\<degree> map BVar z's)"
      using symcl_confluence_rtranclp by blast

    with x''' 4 show ?thesis by (metis closure_symmetric rtranclp_trans)
  qed
qed

lemma closure_replace_list: "\<lbrakk>no_loose_bound s i; no_loose_bound t j; x \<ge> i; x \<ge> j;
closure \<beta>\<eta> (s \<degree>\<degree> map BVar xs) (t \<degree>\<degree> map BVar ys)\<rbrakk> \<Longrightarrow>
closure \<beta>\<eta> (s \<degree>\<degree> map BVar (replace_list xs x y)) (t \<degree>\<degree> map BVar (replace_list ys x y))" proof -
  assume "closure \<beta>\<eta> (s \<degree>\<degree> map BVar xs) (t \<degree>\<degree> map BVar ys)"
  from replace_BVar_preserves_closure[OF this] have
    "closure \<beta>\<eta> (replace_BVar (s \<degree>\<degree> map BVar xs) x y) (replace_BVar (t \<degree>\<degree> map BVar ys) x y)"
    by blast
  moreover assume "no_loose_bound s i" "no_loose_bound t j" "x \<ge> i" "x \<ge> j"
  ultimately show ?thesis using replace_BVar_list_application replace_BVar_no_loose_bound by simp
qed

fun list_replace_list :: "nat list \<Rightarrow> nat list \<Rightarrow> nat list \<Rightarrow> nat list" where
"list_replace_list [] _ _ = []" |
"list_replace_list xs [] _ = xs" |
"list_replace_list xs _ [] = xs" |
"list_replace_list xs (y # ys) (z # zs) = list_replace_list (replace_list xs y z) ys zs"

lemma closure_list_replace_list: "\<lbrakk>length us = length vs; no_loose_bound s i; no_loose_bound t j;
list_all ((\<le>) i) us; list_all ((\<le>) j) us; closure \<beta>\<eta> (s \<degree>\<degree> map BVar xs) (t \<degree>\<degree> map BVar ys)\<rbrakk> \<Longrightarrow>
closure \<beta>\<eta> (s \<degree>\<degree> map BVar (list_replace_list xs us vs)) (t \<degree>\<degree> map BVar (list_replace_list ys us vs))"
proof (induction arbitrary: xs ys rule: list_induct2)
  case Nil
  have "list_replace_list xs [] [] = xs" apply (cases xs) by auto
  moreover have "list_replace_list ys [] [] = ys" apply (cases ys) by auto
  ultimately show ?case using Nil(5) by presburger
next
  case (Cons u us v vs)
  
  from Cons.prems(3,4) have "u \<ge> i" "u \<ge> j" by simp_all
  with Cons.prems(1,2,5) closure_replace_list[of s i t j u xs ys v] have
    "closure \<beta>\<eta> (s \<degree>\<degree> map BVar (replace_list xs u v)) (t \<degree>\<degree> map BVar (replace_list ys u v))"
    by fastforce

  moreover from Cons.prems(3,4) have "list_all ((\<le>) i) us" "list_all ((\<le>) j) us" by simp_all
  ultimately have
    "closure \<beta>\<eta> (s \<degree>\<degree> map BVar (list_replace_list (replace_list xs u v) us vs))
      (t \<degree>\<degree> map BVar (list_replace_list (replace_list ys u v) us vs))"
    using Cons.prems(1,2) Cons.IH[of "replace_list xs u v" "replace_list ys u v"] by blast

  moreover have
    "list_replace_list xs (u # us) (v # vs) = list_replace_list (replace_list xs u v) us vs"
    apply (cases xs) by auto
  moreover have
    "list_replace_list ys (u # us) (v # vs) = list_replace_list (replace_list ys u v) us vs"
    apply (cases ys) by auto

  ultimately show ?case by argo
qed

fun incr_list :: "nat list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat list" where
"incr_list xs x m n = list_replace_list xs (downt m n) (downt (m + x) (n + x))"

lemma incr_list_min: "\<lbrakk>list_all ((\<le>) i) xs; list_all (\<lambda>y. y \<le> j \<or> y \<ge> i + x) xs\<rbrakk> \<Longrightarrow>
list_all ((\<le>) (i + x)) (incr_list xs x j i)"
proof (induction "j - i" arbitrary: j xs)
  case 0
  then have "j \<le> i" by force
  have 1: "incr_list xs x j i = list_replace_list xs (downt j i) (downt (j + x) (i + x))" for xs by auto

  show ?case proof (cases "j = i")
    case True
    with downt_same have "list_replace_list xs (downt j i) (downt (j + x) (i + x)) =
      list_replace_list xs [j] [j + x]" for xs by force
    moreover have "list_replace_list xs [j] [j + x] = replace_list xs j (j + x)" for xs
      apply (cases xs) by auto
    ultimately have "incr_list xs x j i = replace_list xs j (j + x)" for xs
      using 1 by presburger
    with 0(2,3) show ?thesis proof (induction xs)
      case Nil
      then show ?case by auto
    next
      case (Cons a xs)

      from Cons have "list_all ((\<le>) (i + x)) (incr_list xs x j i)" by fastforce
      moreover from Cons(4)[of xs] have "incr_list xs x j i = replace_list xs j (j + x)" by blast
      ultimately have "list_all ((\<le>) (i + x)) (replace_list xs j (j + x))" by argo

      moreover from Cons(2,3) True have "list_all ((\<le>) (i + x)) [(if a = j then j + x else a)]"
        by auto
      moreover from Cons(4)[of "a # xs"] have
        "incr_list (a # xs) x j i = (if a = j then j + x else a) # replace_list xs j (j + x)"
        by force

      ultimately show ?case by force
    qed
  next
    case False
    with \<open>j \<le> i\<close> have "j < i" by fastforce
    with downt_empty have "list_replace_list xs (downt j i) (downt (j + x) (i + x)) =
      list_replace_list xs [] []" for xs by force
    moreover have "list_replace_list xs [] [] = xs" for xs apply (cases xs) by auto
    ultimately have "incr_list xs x j i = xs" for xs using 1 by presburger
    with 0(2,3) show ?thesis proof (induction xs)
      case Nil
      then show ?case by simp
    next
      case (Cons a xs)

      from Cons have "list_all ((\<le>) (i + x)) (incr_list xs x j i)" by fastforce
      moreover from Cons(4)[of xs] have "incr_list xs x j i = xs" by blast
      ultimately have "list_all ((\<le>) (i + x)) xs" by argo

      moreover from Cons(2,3) \<open>j < i\<close> have "list_all ((\<le>) (i + x)) [a]" by simp
      moreover from Cons(4)[of "a # xs"] have "incr_list (a # xs) x j i = a # xs" by blast
      ultimately show ?case by force
    qed
  qed
next
  case (Suc xa)
  then show ?case proof (cases xs)
    case Nil
    then show ?thesis by auto
  next
    case (Cons a list)

    have 0: "incr_list xs x j i = list_replace_list xs (downt j i) (downt (j + x) (i + x))" by simp

    from Suc(2) have "j > i \<and> j > 0" by linarith
    moreover from this obtain j' where "j = Suc j'" using gr0_conv_Suc by blast
    ultimately have 1: "downt j i = j # (downt (j - 1) i)" by simp

    from \<open>j > i \<and> j > 0\<close> \<open>j = Suc j'\<close> have 2:
      "downt (j + x) (i + x) = (j + x) # (downt (j + x - 1) (i + x))" by force

    from Cons have 3:
      "list_replace_list xs (j # (downt (j - 1) i)) ((j + x) # (downt (j + x - 1) (i + x))) =
      list_replace_list (replace_list xs j (j + x)) (downt (j - 1) i) (downt (j + x - 1) (i + x))"
      by fastforce

    from \<open>j > i \<and> j > 0\<close> have "incr_list (replace_list xs j (j + x)) x (j - 1) i =
      list_replace_list (replace_list xs j (j + x)) (downt (j - 1) i) (downt (j + x - 1) (i + x))"
      by simp

    with 0 1 2 3 have 4: "incr_list xs x j i = incr_list (replace_list xs j (j + x)) x (j - 1) i"
      by argo

    from Suc(2) have "xa = j - 1 - i" by fastforce
    moreover from Suc(3) have "list_all ((\<le>) i) (replace_list xs j (j + x))"
      apply (induction xs) by auto
    moreover from Suc(4) have "list_all (\<lambda>y. y \<le> j - 1 \<or> i + x \<le> y) (replace_list xs j (j + x))"
    proof (induction xs)
      case Nil
      then show ?case by auto
    next
      case (Cons a xs)
      then have "list_all (\<lambda>y. y \<le> j - 1 \<or> i + x \<le> y) (replace_list xs j (j + x))" by fastforce
      moreover have "replace_list (a # xs) j (j + x) =
        (if a = j then j + x else a) # replace_list xs j (j + x)" by auto

      moreover have "(\<lambda>y. y \<le> j - 1 \<or> i + x \<le> y) (if a = j then j + x else a)"
      proof (cases "a \<le> j - 1")
        case True
        with \<open>j > i \<and> j > 0\<close> show ?thesis by simp
      next
        case False
        from Cons(2) have "(\<lambda>y. y \<le> j \<or> i + x \<le> y) a" by simp
        with False have "a = j \<or> i + x \<le> a" by linarith
        with \<open>j > i \<and> j > 0\<close> show ?thesis by auto
      qed

      ultimately show ?case by simp
    qed

    ultimately have "list_all ((\<le>) (i + x)) (incr_list (replace_list xs j (j + x)) x (j - 1) i)"
      using Suc.hyps(1)[of "j - 1" "replace_list xs j (j + x)"] by fast
      
    with 4 show ?thesis by presburger
  qed
qed

lemma downt_min: "list_all ((\<le>) i) (downt j i)"
  apply (induction rule: downt.induct)
  by auto

lemma incr_list_closure: "\<lbrakk>closure \<beta>\<eta> (s \<degree>\<degree> map BVar xs) (t \<degree>\<degree> map BVar ys);
no_loose_bound s i; no_loose_bound t i\<rbrakk> \<Longrightarrow>
closure \<beta>\<eta> (s \<degree>\<degree> map BVar (incr_list xs x j i)) (t \<degree>\<degree> map BVar (incr_list ys x j i))"
proof -
  have "length (downt j i) = length (downt (j + x) (i + x))" proof (cases "i \<le> j")
    case True
    with downt_length show ?thesis by fastforce
  next
    case False
    then have "i > j" by force
    then have "downt j i = []" using less_imp_Suc_add by force
    moreover from \<open>i > j\<close> have "downt (j + x) (i + x) = []" using less_imp_Suc_add by force
    ultimately show ?thesis by presburger
  qed

  moreover from downt_min[of i j] have "list_all ((\<le>) i) (downt j i)" by fast

  moreover assume "no_loose_bound s i" "no_loose_bound t i"
    "closure \<beta>\<eta> (s \<degree>\<degree> map BVar xs) (t \<degree>\<degree> map BVar ys)"

  ultimately have
    "closure \<beta>\<eta> (s \<degree>\<degree> map BVar (list_replace_list xs (downt j i) (downt (j + x) (i + x))))
      (t \<degree>\<degree> map BVar (list_replace_list ys (downt j i) (downt (j + x) (i + x))))"
    using closure_list_replace_list[of "downt j i" "downt (j + x) (i + x)" s i t i xs ys] by fast

  then show ?thesis by simp
qed

lemma typing_cong_free:
  assumes "\<And>x. free t x \<Longrightarrow> e x = e' x"
  shows "(e, f) \<turnstile> t : T \<longleftrightarrow> (e', f) \<turnstile> t : T"
  using assms
proof (induction t arbitrary: e e' T)
  case (BVar x)
  then show ?case by auto
next
  case (Var x)
  then show ?case by auto
next
  case (App t1 t2)
  show ?case using App.prems App.IH[of e e'] by auto
next
  case (Abs t)
  have "\<And>x. free t x \<Longrightarrow> (e\<langle>0:U\<rangle>) x = (e'\<langle>0:U\<rangle>) x" for U
    using Abs.prems by (simp add: LambdaType.shift_def)
  then show ?case
    using Abs.IH[of "e\<langle>0:U\<rangle>" "e'\<langle>0:U\<rangle>" for U] by auto
qed

lemma replace_var_typing:
  assumes typed: "e \<turnstile> t \<degree> BVar x \<degree>\<degree> map BVar ys : T"
    and fresh_t: "\<not> free t x'"
    and fresh_ys: "x' \<notin> set ys"
  shows "((fst e)(x':=fst e x), snd e) \<turnstile> t \<degree> BVar x' \<degree>\<degree> map BVar ys : T"
proof -
  let ?Ts = "map (fst e) ys"
  from typed have "e \<turnstile> t : fst e x \<Rightarrow> ?Ts \<Rrightarrow> T"
    by (induction ys arbitrary: T rule: rev_induct) auto
  then have "((fst e)(x':=fst e x), snd e) \<turnstile> t : fst e x \<Rightarrow> ?Ts \<Rrightarrow> T"
    using typing_cong_free[of t "fst e" _ "snd e", simplified] fresh_t
    by (metis fun_upd_other)
  then have "((fst e)(x':=fst e x), snd e) \<turnstile> t \<degree> BVar x' : ?Ts \<Rrightarrow> T"
    by auto
  then show ?thesis
    using fresh_ys
    by (induction ys arbitrary: T rule: rev_induct) auto
qed

lemma free_list_application': "free (t \<degree>\<degree> us) x \<longleftrightarrow> free t x \<or> (\<exists>u\<in>set us. free u x)"
  by (induction us rule: rev_induct) auto

fun map_BVars :: "(nat \<Rightarrow> nat) \<Rightarrow> dB \<Rightarrow> dB" where
  "map_BVars f (BVar x) = BVar (f x)"
| "map_BVars f (Var x)  = Var x"
| "map_BVars f (App t1 t2) = App (map_BVars f t1) (map_BVars f t2)"
| "map_BVars f (Abs t) = Abs (map_BVars (\<lambda>x. case x of 0 \<Rightarrow> 0 | Suc a \<Rightarrow> Suc (f a)) t)"

lemma case_nat_id: "case_nat 0 Suc = id"
  by (simp add: fun_eq_iff split: nat.split)

lemma map_BVars_id: "(\<And>x. f x = x) \<Longrightarrow> map_BVars f t = t"
  by (induction t arbitrary: f) (simp_all add: case_nat_id)

lemma map_BVars_comp: "map_BVars f (map_BVars g t) = map_BVars (f \<circ> g) t"
  by (induction t arbitrary: f g)
    (auto simp add: fun_eq_iff split: nat.split
      intro: arg_cong[where f="\<lambda>x. map_BVars x _"])

lemma map_BVars_no_loose: "no_loose_bound t i \<Longrightarrow> \<forall>j<i. f j = j \<Longrightarrow> map_BVars f t = t"
  by (induction t arbitrary: f i) (auto split: nat.split)

lemma map_BVars_list_append: "map_BVars f (t \<degree>\<degree> map BVar xs) = map_BVars f t \<degree>\<degree> map (BVar \<circ> f) xs"
  by (induction xs rule: rev_induct) simp_all

fun delta_map :: "('a \<Rightarrow> bool) \<Rightarrow> 'a list \<Rightarrow> 'a list \<Rightarrow> 'a \<Rightarrow> 'a" where
  "delta_map P (x # xs) (y # ys) = (if P x then (delta_map P xs ys)(x:=y) else delta_map P xs ys)"
| "delta_map _ _ _ = (\<lambda>x. x)"

lemma delta_map_skip: "\<not> P z \<Longrightarrow> delta_map P xs ys z = z"
  by (induction P xs ys rule: delta_map.induct) auto

lemma map_delta_map: "list_all2 (\<lambda>x y. P x \<or> x = y) xs ys \<Longrightarrow> distinct xs \<Longrightarrow>
  map (delta_map P xs ys) xs = ys"
  by (induction P xs ys rule: delta_map.induct) (auto simp: delta_map_skip)

fun replace_BVar_list :: "dB \<Rightarrow> nat list \<Rightarrow> nat list \<Rightarrow> dB" where
"replace_BVar_list t [] _ = t" |
"replace_BVar_list t _ [] = t" |
"replace_BVar_list t (x # xs) (y # ys) = replace_BVar_list (replace_BVar t x y) xs ys"

lemma replace_BVar_list_preserves_closure:
  "closure \<beta>\<eta> s t \<Longrightarrow> closure \<beta>\<eta> (replace_BVar_list s xs zs) (replace_BVar_list t xs zs)"
  apply (induction arbitrary: s t rule: list_induct2')
     apply fastforce
    apply fastforce
   apply fastforce
  using replace_BVar_preserves_closure by force

lemma replace_BVar_list_Abs:
"replace_BVar_list (Abs t) xs ys = Abs (replace_BVar_list t (map Suc xs) (map Suc ys))"
  by (induction xs ys arbitrary: t rule: list_induct2') simp_all

lemma replace_BVar_list_Var: "replace_BVar_list (Var x) xs ys = Var x"
  by (induction xs ys rule: list_induct2') simp_all

lemma replace_BVar_list_App:
"replace_BVar_list (t1 \<degree> t2) xs ys = (replace_BVar_list t1 xs ys) \<degree> (replace_BVar_list t2 xs ys)"
  by (induction xs ys arbitrary: t1 t2 rule: list_induct2') simp_all

lemma replace_BVar_list_BVar: "list_all ((\<noteq>) x) xs \<Longrightarrow> replace_BVar_list (BVar x) xs ys = BVar x"
  by (induction xs ys rule: list_induct2') simp_all

lemma replace_BVar_list_append: "length xs = length ys \<Longrightarrow>
replace_BVar_list t (xs @ xs') (ys @ ys') = replace_BVar_list (replace_BVar_list t xs ys) xs' ys'"
  apply (induction xs ys arbitrary: t rule: list_induct2)
  by simp_all

fun max_loose_BVar :: "dB \<Rightarrow> nat" where
"max_loose_BVar (BVar i) = i" |
"max_loose_BVar (Var _) = 0" |
"max_loose_BVar (App t1 t2) = max (max_loose_BVar t1) (max_loose_BVar t2)" |
"max_loose_BVar (Abs t) = max_loose_BVar t - 1"

fun option_min :: "nat option \<Rightarrow> nat option \<Rightarrow> nat option" where
"option_min None None = None" |
"option_min (Some x) None = Some x" |
"option_min None (Some x) = Some x" |
"option_min (Some x) (Some y) = Some (min x y)"

fun min_loose_BVar :: "dB \<Rightarrow> nat \<Rightarrow> nat option" where
"min_loose_BVar (BVar i) j = (if i \<ge> j then Some (i - j) else None)" |
"min_loose_BVar (Var _) _ = None" |
"min_loose_BVar (App t1 t2) j = option_min (min_loose_BVar t1 j) (min_loose_BVar t2 j)" |
"min_loose_BVar (Abs t) j = min_loose_BVar t (Suc j)"

definition min_loose_BVar' :: "dB \<Rightarrow> nat" where
"min_loose_BVar' t = (case min_loose_BVar t 0 of None \<Rightarrow> 0 | Some x \<Rightarrow> x)"

lemma list_max_Suc: "xs \<noteq> [] \<Longrightarrow> list_max (map Suc xs) = Suc (list_max xs)"
  apply (induction xs) apply simp by fastforce

lemma upt_list_all_max: "list_all ((>) y) [x..<y]"
  apply (induction y)
   apply simp
  using Ball_set by fastforce

lemma upt_list_all_min: "list_all ((\<le>) x) [x..<y]"
  apply (induction y) by auto

fun loose_BVars :: "dB \<Rightarrow> nat set" where
  "loose_BVars (BVar i) = {i}"
| "loose_BVars (Var _) = {}"
| "loose_BVars (App t1 t2) = loose_BVars t1 \<union> loose_BVars t2"
| "loose_BVars (Abs t) = Suc -` loose_BVars t"

lemma finite_loose_BVars[simp]: "finite (loose_BVars t)"
  by (induction t) (simp_all add: finite_vimage_Suc_iff)

lemma no_loose_bound_BVars: "no_loose_bound t b \<Longrightarrow> loose_BVars t \<subseteq> {0..<b}"
  by (induction t arbitrary: b) (auto simp: atLeast0LessThan)

definition restr_mapping :: "('a \<Rightarrow> 'a) \<Rightarrow> 'a set \<Rightarrow> 'a \<Rightarrow> 'a" where
  "restr_mapping f A x = (if x \<in> A then f x else x)"

lemma restr_mapping_simps[simp]:
  "x \<in> A \<Longrightarrow> restr_mapping f A x = f x"
  "x \<notin> A \<Longrightarrow> restr_mapping f A x = x"
  unfolding restr_mapping_def by simp_all

lemma restr_mapping_id:
  "restr_mapping id A = id"
  "restr_mapping f {} = id"
  unfolding restr_mapping_def by auto

lemma restr_mapping_cong: "A = B \<Longrightarrow> (\<And>x. x \<in> B \<Longrightarrow> f x = g x) \<Longrightarrow>
  restr_mapping f A = restr_mapping g B"
  unfolding restr_mapping_def by auto

lemma map_BVars_restr_mapping: "loose_BVars t \<subseteq> A \<Longrightarrow> map_BVars (restr_mapping f A) t = map_BVars f t"
proof (induction t arbitrary: f A)
  case (Abs t)
  let ?f = "(\<lambda>x. case x of 0 \<Rightarrow> 0 | Suc a \<Rightarrow> Suc (f a))"
  let ?A = "insert 0 (Suc ` A)"
  have "loose_BVars t \<subseteq> ?A"
  proof
    fix x assume "x \<in> loose_BVars t"
    then show "x \<in> ?A"
      using Abs.prems by (cases x) auto
  qed
  with Abs.IH have "map_BVars (restr_mapping ?f ?A) t = map_BVars ?f t" .
  moreover have "restr_mapping ?f ?A =
    (\<lambda>x. case x of 0 \<Rightarrow> 0 | Suc a \<Rightarrow> Suc (restr_mapping f A a))"
    by (auto simp add: fun_eq_iff restr_mapping_def split: nat.split)
  ultimately show ?case by simp
qed simp_all

lemma replace_BVar_list_disjoint:
  assumes "\<And>x. x \<in> set xs \<Longrightarrow> f x \<notin> set xs"
  shows "replace_BVar_list t xs (map f xs) = map_BVars (restr_mapping f (set xs)) t"
  using assms
proof (induction xs arbitrary: f t)
  case Nil
  show ?case by (simp add: map_BVars_id)
next
  case (Cons x xs)
  have "replace_BVar_list t (x # xs) (map f (x # xs)) =
    replace_BVar_list (replace_BVar t x (f x)) xs (map f xs)"
    by simp
  also have "\<dots> = map_BVars (restr_mapping f (set xs)) (replace_BVar t x (f x))"
    using Cons by auto
  also have "\<dots> = map_BVars (restr_mapping f (set (x # xs))) t"
    using Cons.prems
  proof (induction t arbitrary: f x xs)
    case (BVar y)
    then show ?case by (simp add: restr_mapping_def)
  next
    case (Var y)
    show ?case by simp
  next
    case (App t1 t2)
    then show ?case by auto
  next
    case (Abs t)
    let ?f = "(\<lambda>x. case x of 0 \<Rightarrow> 0 | Suc a \<Rightarrow> Suc (f a))"
    let ?xs = "map Suc xs"
    have "y \<in> set (Suc x # ?xs) \<Longrightarrow> ?f y \<notin> set (Suc x # ?xs)" for y
      using Abs.prems by (auto split: nat.split)
    with Abs.IH have "map_BVars (restr_mapping ?f (set ?xs)) (replace_BVar t (Suc x) (?f (Suc x))) =
      map_BVars (restr_mapping ?f (set (Suc x # ?xs))) t" .
    moreover have "restr_mapping ?f (set ?xs) =
      (\<lambda>x. case x of 0 \<Rightarrow> 0 | Suc a \<Rightarrow> Suc (restr_mapping f (set xs) a))"
      by (auto simp add: fun_eq_iff restr_mapping_def split: nat.split)
    moreover have "restr_mapping ?f (set (Suc x # ?xs)) =
      (\<lambda>y. case y of 0 \<Rightarrow> 0 | Suc a \<Rightarrow> Suc (restr_mapping f (set (x # xs)) a))"
      by (auto simp add: fun_eq_iff restr_mapping_def split: nat.split)
    ultimately show ?case by auto
  qed
  finally show ?case .
qed

lemma map_BVars_replace: "\<exists>xs ys. map_BVars f t = replace_BVar_list t xs ys"
proof -
  define n where "n = Suc (Max (insert 0 (loose_BVars t)))"
  define u where "u = max n (Suc (Max (f ` {0..<n})))"
  define xs where "xs = [0..<n]"
  define zs where "zs = map (plus u) xs"
  define ys where "ys = map (\<lambda>x. f (x - u)) zs"
  define g where "g = restr_mapping (plus u) (set xs)"
  define h where "h = restr_mapping (\<lambda>x. f (x - u)) (set zs)"

  have loose_subset_xs: "loose_BVars t \<subseteq> set xs"
    unfolding xs_def n_def
    by (auto simp: less_Suc_eq)
  have "replace_BVar_list t (xs @ zs) (zs @ ys) =
    replace_BVar_list (replace_BVar_list t xs zs) zs ys"
    unfolding zs_def
    by (simp add: replace_BVar_list_append)
  also have "replace_BVar_list t xs zs = map_BVars g t"
    unfolding zs_def g_def
    by (rule replace_BVar_list_disjoint) (simp add: xs_def u_def)
  also have "replace_BVar_list (map_BVars g t) zs ys = map_BVars h (map_BVars g t)"
    unfolding ys_def h_def
  proof (rule replace_BVar_list_disjoint)
    fix z
    assume "z \<in> set zs"
    then obtain x where "x \<in> set xs" and "z = x + u"
      unfolding zs_def by auto
    then have "f x < u"
      unfolding xs_def u_def
      by (auto simp: less_eq_Suc_le intro!: max.coboundedI2)
    then show "f (z - u) \<notin> set zs"
      unfolding \<open>z = x + u\<close> zs_def
      by auto
  qed
  also have "\<dots> = map_BVars (restr_mapping (h \<circ> g) (set xs)) t"
    using loose_subset_xs
    by (simp add: map_BVars_restr_mapping map_BVars_comp)
  also have "\<dots> = map_BVars f t"
    unfolding g_def h_def zs_def
    using loose_subset_xs
    by (simp cong: restr_mapping_cong add: map_BVars_restr_mapping)
  finally show ?thesis
    by metis
qed

lemma map_BVars_preserves_closure:
  "closure \<beta>\<eta> s t \<Longrightarrow> closure \<beta>\<eta> (map_BVars f s) (map_BVars f t)"
proof -
  from map_BVars_replace[of f "s \<degree> t"] obtain xs ys where
    "map_BVars f (s \<degree> t) = replace_BVar_list (s \<degree> t) xs ys" by blast
  with replace_BVar_list_App[of s t xs ys] have
    "map_BVars f s = replace_BVar_list s xs ys" "map_BVars f t = replace_BVar_list t xs ys"
    by simp_all
  moreover assume "closure \<beta>\<eta> s t"
  ultimately show ?thesis using replace_BVar_list_preserves_closure[of s t xs ys] by argo
qed

lemma beta_m_into_closure_\<beta>\<eta>: "beta_m m t1 t2 \<Longrightarrow> closure \<beta>\<eta> t1 t2"
  by (induction pred: beta_m) (auto intro: converse_rtranclp_into_rtranclp)

lemma closure_\<beta>\<eta>_const_redex:
  assumes "\<not> free s 0"
  shows "closure \<beta>\<eta> (Abs s \<degree> t) (Abs s \<degree> t')"
proof -
  have "Abs s \<degree> t \<rightarrow>\<^sub>\<beta> s[t/0]" ..
  also have "s[t/0] = s[t'/0]"
    using assms by simp
  finally have "Abs s \<degree> t \<rightarrow>\<^sub>\<beta> s[t'/0]" by simp
  moreover have "Abs s \<degree> t' \<rightarrow>\<^sub>\<beta> s[t'/0]" ..
  ultimately show ?thesis
    by (meson r_into_rtranclp sup2CI symcl_confluence_rtranclp)
qed

lemma fact13_inductive:
  assumes no_loose: "no_loose_bound s 0" "no_loose_bound t 0"
    and typed: "e \<turnstile> s \<degree>\<degree> map BVar (zsa @ xs) : T" "e \<turnstile> t \<degree>\<degree> map BVar ys : T'"
    and length_eq: "length xs = length zsb" "length ys = length zs"
    and distinct: "distinct (zsa @ xs)" "distinct ys" "distinct (zsa @ zsb)" "set zsb \<inter> set ys = {}"
    and low_xs: "\<forall>b\<in>set xs. b < barrier"
    and high_z: "\<forall>b\<in>set zsa. b \<ge> barrier" "\<forall>b\<in>set zsb. b \<ge> barrier" "\<forall>b\<in>set zs. b \<ge> barrier"
    and ys_zs: "\<forall>j<length ys. ys ! j \<ge> barrier \<longrightarrow> ys ! j = zs ! j"
    and compat: "\<forall>i<length xs. \<forall>j<length ys. xs ! i = ys ! j \<longrightarrow> zsb ! i = zs ! j"
    and equiv: "closure \<beta>\<eta> (s \<degree>\<degree> map BVar (zsa @ xs)) (t \<degree>\<degree> map BVar ys)"
  shows "closure \<beta>\<eta> (s \<degree>\<degree> map BVar (zsa @ zsb)) (t \<degree>\<degree> map BVar zs)"
  using typed length_eq distinct low_xs high_z ys_zs compat equiv
proof (induction "length xs" arbitrary: e xs ys zsa zsb)
  case 0
  then have "xs = []" "zsb = []" by simp_all
  define f where "f = delta_map (greater barrier) ys zs"
  have "closure \<beta>\<eta> (map_BVars f (s \<degree>\<degree> map BVar zsa)) (map_BVars f (t \<degree>\<degree> map BVar ys))"
    using \<open>closure \<beta>\<eta> (s \<degree>\<degree> map BVar (zsa @ xs)) (t \<degree>\<degree> map BVar ys)\<close>
    by (simp only: \<open>xs = []\<close> map_BVars_preserves_closure append_Nil2)
  also have "map_BVars f (s \<degree>\<degree> map BVar zsa) = s \<degree>\<degree> map BVar zsa"
  proof -
    have "map_BVars f (s \<degree>\<degree> map BVar zsa) = s \<degree>\<degree> map (BVar \<circ> f) zsa"
      using no_loose(1)
      by (simp add: map_BVars_list_append map_BVars_no_loose)
    moreover have "map f zsa = map id zsa"
      using \<open>\<forall>a\<in>set zsa. barrier \<le> a\<close> unfolding f_def
      by (intro map_cong) (auto simp: delta_map_skip)
    ultimately show ?thesis by (simp add: map_map[symmetric])
  qed
  also have "map_BVars f (t \<degree>\<degree> map BVar ys) = t \<degree>\<degree> map BVar zs"
  proof -
    have "map_BVars f (t \<degree>\<degree> map BVar ys) = map_BVars f t \<degree>\<degree> map (BVar \<circ> f) ys"
      by (rule map_BVars_list_append)
    also have "map_BVars f t = t"
      using no_loose(2)
      by (simp add: map_BVars_no_loose)
    also have "map (BVar \<circ> f) ys = map BVar (map f ys)"
      by simp
    also have "list_all2 (\<lambda>y z. y < barrier \<or> y = z) ys zs"
      using \<open>length ys = length zs\<close> \<open>\<forall>j<length ys. barrier \<le> ys ! j \<longrightarrow> ys ! j = zs ! j\<close>
      by (fastforce intro!: list_all2_all_nthI)
    then have "map f ys = zs"
      unfolding f_def using \<open>distinct ys\<close>
      by (rule map_delta_map)
    finally show ?thesis .
  qed
  finally show ?case by (simp add: \<open>zsb = []\<close>)
next
  case (Suc m)
  note typed = Suc.prems(1-2)
  note length_eq = Suc.prems(3-4)
  note distinct = Suc.prems(5-8)
  note low_xs = Suc.prems(9)
  note high_z = Suc.prems(10-12)
  note ys_zs = Suc.prems(13)
  note compat = Suc.prems(14)
  note equiv = Suc.prems(15)

  obtain x xs' where [simp]: "xs = x # xs'"
    using Suc.hyps(2) by (metis length_Suc_conv)
  obtain z zsb' where [simp]: "zsb = z # zsb'"
    using Suc.hyps(2) length_eq by (metis length_Suc_conv)

  have "z \<notin> set xs'" using low_xs high_z by auto
  have "z \<notin> set ys" using distinct(4) by simp

  have "closure \<beta>\<eta> (s \<degree>\<degree> map BVar (zsa @ x # xs')) (t \<degree>\<degree> map BVar ys)"
    using equiv by simp
  moreover have "e \<turnstile> s \<degree>\<degree> map BVar (zsa @ x # xs') : T"
    using typed(1) by simp
  moreover note typed(2)
  moreover have "x \<notin> set zsa" using low_xs high_z by auto
  ultimately consider
    (match) "x \<in> set ys" and "\<forall>z. closure \<beta>\<eta> (s \<degree>\<degree> map BVar (zsa @ z # replace_list xs' x z))
       (t \<degree>\<degree> map BVar (replace_list ys x z))"
    | (no_match) "x \<notin> set ys" and "\<exists>t'. \<beta>\<eta>cl s (Abs_m (length zsa + 1) t') \<and> \<not> free t' 0 \<and> no_loose_bound t' (length zsa + 1)"
    using lemma23[OF no_loose] by blast
  then show ?case proof cases
    case match
    have replace_xs': "replace_list xs' x z = xs'"
      using distinct(1) by (simp add: replace_list_not_member)
    obtain ysa ysb where ys_eq: "ys = ysa @ x # ysb" and x_ysx: "x \<notin> set ysa" "x \<notin> set ysb"
      using match(1) distinct(2) split_list_last by force
    then have replace_ys: "replace_list ys x z = ysa @ z # ysb"
      by (simp add: replace_list_append replace_list_not_member)

    let ?e = "((fst e)(z:=fst e x), snd e)"
    have "closure \<beta>\<eta> (s \<degree>\<degree> map BVar ((zsa @ [z]) @ zsb')) (t \<degree>\<degree> map BVar zs)"
    proof (rule Suc.hyps(1)[of "replace_list xs' x z" ?e "zsa @ [z]" "replace_list ys x z" zsb',
        unfolded replace_xs' replace_ys])
      show "m = length xs'" using Suc.hyps(2) by simp
      show "?e \<turnstile> s \<degree>\<degree> map BVar ((zsa @ [z]) @ xs') : T"
        using typed(1) no_loose(1) distinct(3) \<open>z \<notin> set xs'\<close>
        by (auto simp: free_list_application' loose_bound_free intro!: replace_var_typing)
      show "?e \<turnstile> t \<degree>\<degree> map BVar (ysa @ z # ysb) : T'"
        using typed(2) no_loose(2) distinct(4) \<open>z \<notin> set ys\<close> unfolding ys_eq
        by (auto simp: free_list_application' loose_bound_free intro!: replace_var_typing)
      show "length xs' = length zsb'" and "length (ysa @ z # ysb) = length zs"
        using length_eq unfolding ys_eq by simp_all
      show "distinct ((zsa @ [z]) @ xs')"
        using \<open>z \<notin> set xs'\<close> distinct(1,3) by simp
      show "distinct (ysa @ z # ysb)"
        using \<open>z \<notin> set ys\<close> distinct(2) unfolding ys_eq by simp
      show "distinct ((zsa @ [z]) @ zsb')"
        using distinct(3) by simp
      show "set zsb' \<inter> set (ysa @ z # ysb) = {}"
        using distinct(3,4) unfolding ys_eq by simp
      show "\<forall>b\<in>set xs'. b < barrier"
        using low_xs by simp
      show "Ball (set (zsa @ [z])) ((\<le>) barrier)" and "Ball (set zsb') ((\<le>) barrier)"
        using high_z(1,2) by simp_all
      show "Ball (set zs) ((\<le>) barrier)" using high_z(3) .
      show "\<forall>j<length (ysa @ z # ysb). barrier \<le> (ysa @ z # ysb) ! j \<longrightarrow> (ysa @ z # ysb) ! j = zs ! j"
        using ys_zs unfolding ys_eq
        apply (auto simp: nth_append split: if_splits)
        by (smt Suc.hyps(2) \<open>xs = x # xs'\<close> \<open>zsb = z # zsb'\<close> add_Suc_right compat length_append length_eq(2) less_Suc_eq less_add_Suc1 list.size(4) not_less_eq nth_Cons' nth_Cons_0 nth_append_length ys_eq zero_less_Suc zero_less_diff)
      show "\<forall>i<length xs'. \<forall>j<length (ysa @ z # ysb). xs' ! i = (ysa @ z # ysb) ! j \<longrightarrow> zsb' ! i = zs ! j"
        using compat \<open>z \<notin> set xs'\<close> unfolding ys_eq
        apply (auto simp: nth_append nth_Cons split: if_splits nat.splits)
        apply (metis Suc.hyps(2) Suc_mono \<open>m = length xs'\<close> \<open>xs = x # xs'\<close> \<open>zsb = z # zsb'\<close> compat length_append nth_Cons_Suc nth_append trans_less_add1 ys_eq)
        by (metis not_less_eq)
      show "closure \<beta>\<eta> (s \<degree>\<degree> map BVar ((zsa @ [z]) @ xs')) (t \<degree>\<degree> map BVar (ysa @ z # ysb))"
        using match(2)[rule_format, of z] unfolding replace_xs' replace_ys by simp
    qed
    then show ?thesis by simp
  next
    case no_match
    then obtain s' where 1: "\<beta>\<eta>cl s (Abs_m (length zsa + 1) s')" and "\<not> free s' 0" and "no_loose_bound s' (length zsa + 1)"
      by blast
    have "closure \<beta>\<eta> (s \<degree>\<degree> map BVar (zsa @ xs)) (Abs_m (length zsa + 1) s' \<degree>\<degree> map BVar (zsa @ xs))"
      using 1 by (blast intro: closure\<beta>\<eta>_list_application closure_symmetric symcl_rtranclp)
    moreover have 2: "beta_m (length zsa) (Abs_m (length zsa) (Abs s') \<degree>\<degree> map BVar zsa) (list_subst (Abs s') zsa (length zsa))"
      by (rule lemma15) simp_all
    then have "closure \<beta>\<eta> ((Abs_m (length zsa) (Abs s') \<degree>\<degree> map BVar zsa) \<degree> BVar x \<degree>\<degree> map BVar xs')
        (Abs (list_subst s' zsa (length zsa + 1)) \<degree> BVar x \<degree>\<degree> map BVar xs')"
      by (simp only: closure_\<beta>\<eta>_App closure\<beta>\<eta>_list_application beta_m_into_closure_\<beta>\<eta> list_subst_Abs)
    moreover have "closure \<beta>\<eta> ((Abs (list_subst s' zsa (length zsa + 1)) \<degree> BVar x) \<degree>\<degree> map BVar xs')
        ((Abs (list_subst s' zsa (length zsa + 1)) \<degree> BVar z) \<degree>\<degree> map BVar xs')"
      using \<open>\<not> free s' 0\<close> list_subst_free
      by (fastforce intro!: closure\<beta>\<eta>_list_application closure_\<beta>\<eta>_const_redex)
    moreover have "closure \<beta>\<eta> ((Abs_m (length zsa) (Abs s') \<degree>\<degree> map BVar zsa) \<degree> BVar z \<degree>\<degree> map BVar xs')
        (Abs (list_subst s' zsa (length zsa + 1)) \<degree> BVar z \<degree>\<degree> map BVar xs')"
      using 2
      by (simp only: closure_\<beta>\<eta>_App closure\<beta>\<eta>_list_application beta_m_into_closure_\<beta>\<eta> list_subst_Abs)
    moreover have "closure \<beta>\<eta> (s \<degree>\<degree> map BVar (zsa @ z # xs')) (Abs_m (length zsa + 1) s' \<degree>\<degree> map BVar (zsa @ z # xs'))"
      using 1 by (blast intro: closure\<beta>\<eta>_list_application closure_symmetric symcl_rtranclp)
    ultimately have 3: "closure \<beta>\<eta> (s \<degree>\<degree> map BVar (zsa @ xs)) (s \<degree>\<degree> map BVar (zsa @ z # xs'))"
      by (simp add: Abs_m del: symcl.simps) (meson closure_symmetric rtranclp_trans)

    let ?e = "((fst e)(z:=fst e x), snd e)"
    have "closure \<beta>\<eta> (s \<degree>\<degree> map BVar ((zsa @ [z]) @ zsb')) (t \<degree>\<degree> map BVar zs)"
    proof (rule Suc.hyps(1)[of xs' ?e "zsa @ [z]" ys zsb'])
      show "m = length xs'" using Suc.hyps(2) by simp
      show "?e \<turnstile> s \<degree>\<degree> map BVar ((zsa @ [z]) @ xs') : T"
        using typed(1) no_loose(1) distinct(3) \<open>z \<notin> set xs'\<close>
        by (auto simp: free_list_application' loose_bound_free intro!: replace_var_typing)
      show "?e \<turnstile> t \<degree>\<degree> map BVar ys : T'"
        using typed(2) no_loose(2) \<open>z \<notin> set ys\<close>
        by (auto simp: free_list_application' loose_bound_free intro: typing_cong_free[of _ "fst e" _ "snd e", THEN iffD1])
      show "length xs' = length zsb'" and "length ys = length zs"
        using length_eq by simp_all
      show "distinct ((zsa @ [z]) @ xs')"
        using \<open>z \<notin> set xs'\<close> distinct(1,3) by simp
      show "distinct ys" by fact
      show "distinct ((zsa @ [z]) @ zsb')"
        using distinct(3) by simp
      show "set zsb' \<inter> set ys = {}"
        using distinct(4) by simp
      show "\<forall>b\<in>set xs'. b < barrier"
        using low_xs by simp
      show "Ball (set (zsa @ [z])) ((\<le>) barrier)" and "Ball (set zsb') ((\<le>) barrier)"
        using high_z(1,2) by simp_all
      show "Ball (set zs) ((\<le>) barrier)" using high_z(3) .
      show "\<forall>j<length ys. barrier \<le> ys ! j \<longrightarrow> ys ! j = zs ! j" by fact
      show "\<forall>i<length xs'. \<forall>j<length ys. xs' ! i = ys ! j \<longrightarrow> zsb' ! i = zs ! j"
        using compat by auto
      show "closure \<beta>\<eta> (s \<degree>\<degree> map BVar ((zsa @ [z]) @ xs')) (t \<degree>\<degree> map BVar ys)"
        using equiv 3
        by (simp del: symcl.simps) (meson closure_symmetric rtranclp_trans)
    qed
    then show ?thesis by simp
  qed
qed

lemma list_max_append: "list_max (xs @ ys) = max (list_max xs) (list_max ys)"
  by (induction xs) simp_all

lemma in_set_le_max: "x \<in> set xs \<Longrightarrow> x \<le> list_max xs"
  by (induction xs) auto

lemma fact13:
  assumes no_loose: "no_loose_bound s 0" "no_loose_bound t 0"
    and typed: "e \<turnstile> s \<degree>\<degree> map BVar x_m : T" "e \<turnstile> t \<degree>\<degree> map BVar y_n : T'"
    and length_eq: "length x_m = length z_m'" "length y_n = length z_n"
    and distinct: "distinct x_m" "distinct y_n" "distinct z_m'"
    and compat: "\<forall>i<length x_m. \<forall>j<length y_n. x_m ! i = y_n ! j \<longrightarrow> z_m' ! i = z_n ! j"
    and equiv: "closure \<beta>\<eta> (s \<degree>\<degree> map BVar x_m) (t \<degree>\<degree> map BVar y_n)"
  shows "closure \<beta>\<eta> (s \<degree>\<degree> map BVar z_m') (t \<degree>\<degree> map BVar z_n)"
proof -
  define barrier where "barrier = Suc (list_max (0 # x_m @ y_n))"
  let ?zs' = "map ((+) barrier) z_m'"
  let ?zs = "map ((+) barrier) z_n"
  let ?f = "\<lambda>x. x - barrier"

  have "closure \<beta>\<eta> (s \<degree>\<degree> map BVar ([] @ ?zs')) (t \<degree>\<degree> map BVar ?zs)"
    apply (rule fact13_inductive[of s t e "[]" x_m T y_n T' ?zs' ?zs barrier])
    apply (simp_all add: distinct_map barrier_def list_max_append)
                    apply fact+
    subgoal by (auto dest: in_set_le_max)
    subgoal by (auto dest: in_set_le_max)
    subgoal by (simp add: Suc_le_eq in_set_le_max leD)
    subgoal by (simp add: compat length_eq)
    using equiv by auto
  then have "closure \<beta>\<eta> (s \<degree>\<degree> map BVar ?zs') (t \<degree>\<degree> map BVar ?zs)"
    by simp
  then have "closure \<beta>\<eta> (map_BVars ?f (s \<degree>\<degree> map BVar ?zs')) (map_BVars ?f (t \<degree>\<degree> map BVar ?zs))"
    by (rule map_BVars_preserves_closure)
  also have "map_BVars ?f (s \<degree>\<degree> map BVar ?zs') = s \<degree>\<degree> map BVar z_m'"
    using no_loose(1)
    by (simp add: map_BVars_list_append map_BVars_no_loose del: map_map) (simp cong: map_cong)
  also have "map_BVars ?f (t \<degree>\<degree> map BVar ?zs) = t \<degree>\<degree> map BVar z_n"
    using no_loose(2)
    by (simp add: map_BVars_list_append map_BVars_no_loose del: map_map) (simp cong: map_cong)
  finally show ?thesis .
qed

fun index_of :: "nat \<Rightarrow> 'a list \<Rightarrow> 'a \<Rightarrow> nat option" where
  "index_of _ [] _ = None"
| "index_of i (x # xs) y = (if x = y then Some i else index_of (Suc i) xs y)"

lemma index_of_less_length: "index_of i xs y = Some j \<Longrightarrow> j < i + length xs"
  by (induction xs arbitrary: i) (fastforce split: if_splits)+

lemma index_of_less_length0: "index_of 0 xs y = Some i \<Longrightarrow> i < length xs"
  using index_of_less_length[of 0] by simp

lemma index_of_ge: "index_of i xs y = Some j \<Longrightarrow> i \<le> j"
  by (induction xs arbitrary: i) (fastforce split: if_splits)+

lemma index_of_eq_Some_inj: "index_of i xs y1 = Some j \<Longrightarrow> index_of i xs y2 = Some j \<Longrightarrow> y1 = y2"
  by (induction xs arbitrary: i) (auto split: if_splits dest: index_of_ge)

lemma distinct_index_of_nth: "distinct xs \<Longrightarrow> j < length xs \<Longrightarrow> index_of i xs (xs ! j) = Some (i + j)"
proof (induction xs arbitrary: i j)
  case Nil
  then show ?case by simp
next
  case (Cons x xs)
  show ?case proof (cases j)
    case 0
    then show ?thesis by simp
  next
    case (Suc nat)
    with Cons have "index_of (Suc i) xs (xs ! nat) = Some (Suc (i + nat))"
      by simp
    with Cons show ?thesis
      unfolding Suc by auto
  qed
qed

lemma fact14:
  assumes no_loose: "no_loose_bound s 0" "no_loose_bound t 0"
    and typed: "e \<turnstile> s \<degree>\<degree> map BVar x_m : T" "e \<turnstile> t \<degree>\<degree> map BVar y_n : T'"
    and length_eq: "length z_m = length x_m" "length z_m' = length x_m"
    and distinct: "distinct x_m" "distinct y_n" "distinct z_m'"
    and compat: "\<forall>i<length x_m. (\<exists>j<length y_n. x_m ! i = y_n ! j) \<longrightarrow> z_m ! i = z_m' ! i"
    and equiv: "closure \<beta>\<eta> (s \<degree>\<degree> map BVar x_m) (t \<degree>\<degree> map BVar y_n)"
  shows "closure \<beta>\<eta> (s \<degree>\<degree> map BVar z_m) (s \<degree>\<degree> map BVar z_m')"
proof -
  define b where "b = Suc (Max (insert 0 (set z_m')))"
  have 1: "z_m' ! i \<noteq> b + j" if "i < length z_m'" for i j
    unfolding b_def using that
    by (fastforce intro!: less_imp_neq trans_less_add1 le_imp_less_Suc Max_ge)
  define z_n where "z_n = map (\<lambda>j. case index_of 0 x_m (y_n ! j) of
      None \<Rightarrow> b + j | Some i \<Rightarrow> z_m' ! i) [0..<length y_n]"
  have "length y_n = length z_n"
    unfolding z_n_def by simp
  have "distinct z_n"
    unfolding z_n_def
    apply (simp add: distinct_map)
    apply (rule inj_onI)
    apply (simp split: option.splits)
      apply (erule notE[OF 1, rotated])
      apply (simp add: length_eq index_of_less_length0)
     apply (erule notE[OF 1, rotated, OF sym])
     apply (simp add: length_eq index_of_less_length0)
    apply (drule inj_on_nth[where I="{..<length z_m'}", OF \<open>distinct z_m'\<close>, THEN inj_onD, rotated])
       apply (simp_all add: length_eq index_of_less_length0)
    apply (drule (1) index_of_eq_Some_inj)
    using distinct(2) nth_eq_iff_index_eq by blast
  have 2: "z_n ! j = z_m ! i \<and> z_n ! j = z_m' ! i"
    if "i < length x_m" and "j < length y_n" and "y_n ! j = x_m ! i" for i j
    unfolding z_n_def
    using that compat
    by (fastforce simp add: distinct_index_of_nth[OF \<open>distinct x_m\<close>])

  have "closure \<beta>\<eta> (t \<degree>\<degree> map BVar z_n) (s \<degree>\<degree> map BVar z_m)"
    apply (rule fact13[of t s e y_n T' x_m T z_n z_m])
              apply (fact | simp add: length_eq)+
    using 2[THEN conjunct1] apply auto[]
    using closure_symmetric equiv by blast
  moreover have "closure \<beta>\<eta> (t \<degree>\<degree> map BVar z_n) (s \<degree>\<degree> map BVar z_m')"
    apply (rule fact13[of t s e y_n T' x_m T z_n z_m'])
              apply (fact | simp add: length_eq)+
    using 2[THEN conjunct2] apply auto[]
    using closure_symmetric equiv by blast
  ultimately show ?thesis
    by (meson closure_symmetric rtranclp_trans)
qed

end
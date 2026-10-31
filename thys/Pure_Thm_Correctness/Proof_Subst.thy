section \<open>Substitution under binders\<close>

theory Proof_Subst
  imports Bicompose_Typing "Pure_Thm.Pure_Proofterm"
begin

text \<open>
  Lifting a rule over the parameters of a subgoal replaces each schematic variable \<open>?x\<close> by
  \<open>?x' x\<^sub>1 \<dots> x\<^sub>n\<close>, where the \<open>x\<^sub>i\<close> are the parameters, bound outside of the rule. In
  de Bruijn terms, this is a substitution for free variables whose values contain loose bound
  variables; under \<open>k\<close> binders, they are lifted by \<open>k\<close> (\<open>vsubst\<close>). Unlike
  \<^const>\<open>mk_subst\<close> it preserves \<open>\<beta>\<close>- and \<open>\<eta>\<close>-reduction for arbitrary values.
\<close>

fun vsubst :: "(nat \<Rightarrow> dB) \<Rightarrow> nat \<Rightarrow> dB \<Rightarrow> dB" where
  "vsubst \<sigma> k (dB.Var x) = liftn k (\<sigma> x) 0"
| "vsubst \<sigma> k (BVar i) = BVar i"
| "vsubst \<sigma> k (dB.Abs t) = dB.Abs (vsubst \<sigma> (Suc k) t)"
| "vsubst \<sigma> k (s \<degree> t) = vsubst \<sigma> k s \<degree> vsubst \<sigma> k t"

lemma lift_liftn: "i \<le> j \<Longrightarrow> j \<le> i + k \<Longrightarrow> lift (liftn k a i) j = liftn (Suc k) a i"
  by (induction a arbitrary: i j) (auto simp del: liftn_lift)

lemma subst_liftn: "i \<le> j \<Longrightarrow> j \<le> i + k \<Longrightarrow> subst (liftn (Suc k) a i) b j = liftn k a i"
  by (induction a arbitrary: i j b) (auto simp: subst_BVar simp del: liftn_lift)

lemma free_liftn': "m \<le> i \<Longrightarrow> i < m + k \<Longrightarrow> \<not> free (liftn k a m) i"
  by (induction a arbitrary: m i) auto

lemma free_liftn: "i < k \<Longrightarrow> \<not> free (liftn k a 0) i"
  using free_liftn'[of 0 i k a] by simp

lemma lift_vsubst: "j \<le> k \<Longrightarrow> lift (vsubst \<sigma> k t) j = vsubst \<sigma> (Suc k) (lift t j)"
  by (induction t arbitrary: j k) (simp_all add: lift_liftn del: liftn_lift)

lemma subst_vsubst: "j \<le> k \<Longrightarrow> subst (vsubst \<sigma> (Suc k) s) (vsubst \<sigma> k u) j = vsubst \<sigma> k (subst s u j)"
proof (induction s arbitrary: j k u)
  case (Var x)
  then show ?case by (simp add: subst_liftn del: liftn_lift)
next
  case (BVar i)
  then show ?case by (simp add: subst_BVar)
next
  case (App s t)
  then show ?case by simp
next
  case (Abs s)
  have "lift (vsubst \<sigma> k u) 0 = vsubst \<sigma> (Suc k) (lift u 0)" by (rule lift_vsubst) simp
  with Abs.IH[of "Suc j" "Suc k" "lift u 0"] Abs.prems show ?case by simp
qed

lemma free_vsubst: "i < k \<Longrightarrow> free (vsubst \<sigma> k s) i \<longleftrightarrow> free s i"
  by (induction s arbitrary: i k) (auto simp: free_liftn)

lemma vsubst_beta: "s \<rightarrow>\<^sub>\<beta> t \<Longrightarrow> vsubst \<sigma> k s \<rightarrow>\<^sub>\<beta> vsubst \<sigma> k t"
proof (induction arbitrary: k rule: beta.induct)
  case (beta s t)
  have "dB.Abs (vsubst \<sigma> (Suc k) s) \<degree> vsubst \<sigma> k t \<rightarrow>\<^sub>\<beta> subst (vsubst \<sigma> (Suc k) s) (vsubst \<sigma> k t) 0"
    by (rule beta.beta)
  then show ?case by (simp add: subst_vsubst)
qed auto

lemma vsubst_eta: "s \<rightarrow>\<^sub>\<eta> t \<Longrightarrow> vsubst \<sigma> k s \<rightarrow>\<^sub>\<eta> vsubst \<sigma> k t"
proof (induction arbitrary: k rule: eta.induct)
  case (eta s d)
  have nf: "\<not> free (vsubst \<sigma> (Suc k) s) 0" using eta free_vsubst[of 0 "Suc k" \<sigma> s] by simp
  then have "dB.Abs (vsubst \<sigma> (Suc k) s \<degree> BVar 0) \<rightarrow>\<^sub>\<eta> subst (vsubst \<sigma> (Suc k) s) (vsubst \<sigma> k d) 0"
    by (rule eta.eta)
  then show ?case by (simp add: subst_vsubst)
qed auto

lemma vsubst_\<beta>\<eta>: "\<beta>\<eta> s t \<Longrightarrow> \<beta>\<eta> (vsubst \<sigma> k s) (vsubst \<sigma> k t)"
  by (auto intro: vsubst_beta vsubst_eta)

lemma vsubst_equiv: "s \<equiv>\<^sub>\<beta>\<^sub>\<eta> t \<Longrightarrow> vsubst \<sigma> k s \<equiv>\<^sub>\<beta>\<^sub>\<eta> vsubst \<sigma> k t"
proof (induction rule: rtranclp_induct)
  case (step y z)
  from step.hyps(2) have "symcl \<beta>\<eta> (vsubst \<sigma> k y) (vsubst \<sigma> k z)"
    unfolding symcl.simps by (elim disjE) (simp_all only: vsubst_\<beta>\<eta> simp_thms)
  with step.IH show ?case by (rule rtranclp.rtrancl_into_rtrancl)
qed simp


subsection \<open>Lifting of terms\<close>

lemma liftn_liftn_0: "liftn a (liftn b t k) k = liftn (a + b) t k"
  by (induction t arbitrary: k) auto

lemma nat_of_integer_plus1: "0 \<le> n \<Longrightarrow> nat_of_integer (n + 1) = Suc (nat_of_integer n)"
  by (simp add: integer_reps nat_add_distrib)

text \<open>\<^const>\<open>combound\<close> at level \<open>n\<close> is the one at level \<open>0\<close>, lifted by \<open>n\<close>:\<close>

lemma tr_combound_type: "tr (combound (Var x T) n k) = tr (combound (Var x U) n k)"
  by (induction k arbitrary: n) simp_all

lemma tr_combound:
  "0 \<le> n \<Longrightarrow> tr (combound (Var x T) n k) = liftn (nat_of_integer n) (tr (combound (Var x T) 0 k)) 0"
proof (induction k arbitrary: n)
  case 0
  then show ?case by simp
next
  case (Suc k)
  have n1: "0 \<le> n + 1" using Suc.prems by simp
  have "tr (combound (Var x T) (n + 1) k) = liftn (nat_of_integer (n + 1)) (tr (combound (Var x T) 0 k)) 0"
    by (rule Suc.IH[OF n1])
  then have a: "tr (combound (Var x T) (n + 1) k) = liftn (Suc (nat_of_integer n)) (tr (combound (Var x T) 0 k)) 0"
    by (simp only: nat_of_integer_plus1[OF Suc.prems])
  have "tr (combound (Var x T) 1 k) = liftn (nat_of_integer 1) (tr (combound (Var x T) 0 k)) 0"
    by (rule Suc.IH) simp
  then have b: "tr (combound (Var x T) 1 k) = liftn 1 (tr (combound (Var x T) 0 k)) 0"
    by (simp add: nat_of_integer.rep_eq one_integer.rep_eq del: liftn_lift)
  have "tr (combound (Var x T) n (Suc k)) = tr (combound (Var x T) (n + 1) k) \<degree> BVar (nat_of_integer n)"
    by simp
  also have "\<dots> = liftn (Suc (nat_of_integer n)) (tr (combound (Var x T) 0 k)) 0 \<degree> BVar (nat_of_integer n)"
    by (simp only: a)
  also have "\<dots> = liftn (nat_of_integer n) (liftn 1 (tr (combound (Var x T) 0 k)) 0 \<degree> BVar 0) 0"
    by (simp add: liftn_liftn_0 del: liftn_lift)
  also have "liftn 1 (tr (combound (Var x T) 0 k)) 0 \<degree> BVar 0 = tr (combound (Var x T) 0 (Suc k))"
    using b by (simp add: zero_integer.rep_eq del: liftn_lift)
  finally show ?case .
qed

text \<open>
  The values of the lifting substitution on the codes of atoms: schematic variables get the
  incremented index and are applied to the parameters; the types of constants and free
  variables get incremented type variables.
\<close>

definition lift_code :: "ptyp list \<Rightarrow> integer \<Rightarrow> nat \<Rightarrow> dB" where
  "lift_code Ts inc n =
    (case atom_of n of
      AVar xi \<Rightarrow> tr (combound (Var (fst xi, snd xi + inc) dummyT) 0 (length Ts))
    | AConst c T \<Rightarrow> dB.Var (code (AConst c (incr_tvar inc T)))
    | AFree x T \<Rightarrow> dB.Var (code (AFree x (incr_tvar inc T))))"

lemma tr_incr_idx:
  "0 \<le> lev \<Longrightarrow> tr (incr_idx Ts inc lev t) = vsubst (lift_code Ts inc) (nat_of_integer lev) (tr t)"
proof (induction Ts inc lev t rule: incr_idx.induct)
  case (1 Ts inc lev x i T)
  have "tr (incr_idx Ts inc lev (Var (x, i) T)) =
      liftn (nat_of_integer lev) (tr (combound (Var (x, i + inc) (foldr fun_type Ts (incr_tvar inc T))) 0 (length Ts))) 0"
    using tr_combound[OF 1] by simp
  also have "tr (combound (Var (x, i + inc) (foldr fun_type Ts (incr_tvar inc T))) 0 (length Ts)) =
      lift_code Ts inc (code (AVar (x, i)))"
    unfolding lift_code_def by (simp only: atom_of_code atom.case fst_conv snd_conv) (rule tr_combound_type)
  finally show ?case by simp
next
  case (3 Ts inc lev x T t)
  then show ?case by (simp add: nat_of_integer_plus1)
qed (simp_all add: lift_code_def del: liftn_lift)

end

section \<open>Substitution of free variables\<close>

theory Free_Subst
  imports Biresolution_Sound "Pure_Thm.Pure_Proofterm"
begin

text \<open>
  \<open>fsubst \<tau> t\<close> replaces the free variables of \<open>t\<close> by terms that may have loose bound
  variables (lifted below binders). It turns fresh free variables back into parameters.
\<close>

fun fsubst :: "(name \<Rightarrow> ptyp \<Rightarrow> pterm) \<Rightarrow> pterm \<Rightarrow> pterm" where
  "fsubst \<tau> (Free x T) = \<tau> x T"
| "fsubst \<tau> (Abs a T t) = Abs a T (fsubst (\<lambda>x U. lift (\<tau> x U) 0) t)"
| "fsubst \<tau> (s $ t) = fsubst \<tau> s $ fsubst \<tau> t"
| "fsubst \<tau> t = t"

lemma fsubst_lift: "0 \<le> k \<Longrightarrow> fsubst (\<lambda>x U. lift (\<tau> x U) k) (lift t k) = lift (fsubst \<tau> t) k"
proof (induction t arbitrary: \<tau> k)
  case (Abs a T t)
  have "fsubst (\<lambda>x U. lift (lift (\<tau> x U) k) 0) (lift t (k + 1)) = fsubst (\<lambda>x U. lift (lift (\<tau> x U) 0) (k + 1)) (lift t (k + 1))"
    using lift_lift[of 0 k] Abs.prems by simp
  also have "\<dots> = lift (fsubst (\<lambda>x U. lift (\<tau> x U) 0) t) (k + 1)"
    using Abs.IH[of "k + 1" "\<lambda>x U. lift (\<tau> x U) 0"] Abs.prems by simp
  finally show ?case by simp
qed simp_all

lemma fsubst_subst: "0 \<le> k \<Longrightarrow> fsubst \<tau> (t[s/k]) = (fsubst (\<lambda>x U. lift (\<tau> x U) k) t)[fsubst \<tau> s/k]"
proof (induction t arbitrary: \<tau> k s)
  case (Abs a T t)
  have "fsubst \<tau> ((Abs a T t)[s/k]) = Abs a T (fsubst (\<lambda>x U. lift (\<tau> x U) 0) (t[lift s 0/k + 1]))" by simp
  also have "\<dots> = Abs a T ((fsubst (\<lambda>x U. lift (lift (\<tau> x U) 0) (k + 1)) t)[fsubst (\<lambda>x U. lift (\<tau> x U) 0) (lift s 0)/k + 1])"
    using Abs.IH[of "k + 1"] Abs.prems by simp
  also have "\<dots> = Abs a T ((fsubst (\<lambda>x U. lift (lift (\<tau> x U) k) 0) t)[lift (fsubst \<tau> s) 0/k + 1])"
    using lift_lift[of 0 k] Abs.prems fsubst_lift[of 0 \<tau> s] by simp
  finally show ?case by simp
qed (simp_all add: subst_Bound)

lemma loose_bvar1_fsubst:
  "\<not> loose_bvar1 t k \<Longrightarrow> (\<And>x U. \<not> loose_bvar1 (\<tau> x U) k) \<Longrightarrow> 0 \<le> k \<Longrightarrow> \<not> loose_bvar1 (fsubst \<tau> t) k"
proof (induction t arbitrary: \<tau> k)
  case (Abs a T t)
  have "\<not> loose_bvar1 (lift (\<tau> x U) 0) (k + 1)" for x U using Abs.prems(2,3) by simp
  with Abs show ?case by simp
qed simp_all

lemma beta_fsubst: "s \<rightarrow>\<^sub>\<beta> t \<Longrightarrow> fsubst \<tau> s \<rightarrow>\<^sub>\<beta> fsubst \<tau> t"
proof (induction arbitrary: \<tau> set: beta)
  case (beta a T s t)
  show ?case using fsubst_subst[of 0 \<tau> s t] by simp
qed auto

lemma eta_fsubst: "s \<rightarrow>\<^sub>\<eta> t \<Longrightarrow> fsubst \<tau> s \<rightarrow>\<^sub>\<eta> fsubst \<tau> t"
proof (induction arbitrary: \<tau> set: eta)
  case (eta s a T d)
  have "\<not> loose_bvar1 (fsubst (\<lambda>x U. lift (\<tau> x U) 0) s) 0"
    by (rule loose_bvar1_fsubst) (use eta in simp_all)
  then show ?case using eta.eta[of "fsubst (\<lambda>x U. lift (\<tau> x U) 0) s" a T "fsubst \<tau> d"] fsubst_subst[of 0 \<tau> s d]
    by simp
qed auto

lemma beta_eta_fsubst: "(sup beta eta)\<^sup>*\<^sup>* s t \<Longrightarrow> (sup beta eta)\<^sup>*\<^sup>* (fsubst \<tau> s) (fsubst \<tau> t)"
  by (induction rule: rtranclp_induct) (auto intro: rtranclp.rtrancl_into_rtrancl beta_fsubst eta_fsubst)

lemma unname_fsubst: "unname (fsubst \<tau> t) = fsubst (\<lambda>x U. unname (\<tau> x U)) (unname t)"
  by (induction t arbitrary: \<tau>) simp_all

lemma fsubst_id: "(\<And>x U. x \<in> fnames t \<Longrightarrow> \<tau> x U = Free x U) \<Longrightarrow> fsubst \<tau> t = t"
  by (induction t arbitrary: \<tau>) auto

text \<open>Free variables with their types:\<close>

fun pfrees :: "pterm \<Rightarrow> (name \<times> ptyp) set" where
  "pfrees (Free x T) = {(x, T)}"
| "pfrees (Abs a T t) = pfrees t"
| "pfrees (s $ t) = pfrees s \<union> pfrees t"
| "pfrees _ = {}"

lemma finite_pfrees [simp]: "finite (pfrees t)"
  by (induction t) simp_all

lemma fnames_pfrees: "fnames t = fst ` pfrees t"
  by (induction t) auto

lemma fsubst_id_pfrees: "(\<And>x U. (x, U) \<in> pfrees t \<Longrightarrow> \<tau> x U = Free x U) \<Longrightarrow> fsubst \<tau> t = t"
  by (induction t arbitrary: \<tau>) auto

lemma fnames_inst [simp]: "fnames (inst \<rho> t) = fnames t"
  by (induction t) simp_all

text \<open>Natural numbers as integers:\<close>

lemma integer_of_nat_0 [simp]: "integer_of_nat 0 = 0"
  by (simp add: integer_eq_iff integer_of_nat.rep_eq)

lemma integer_of_nat_Suc: "integer_of_nat (Suc n) = integer_of_nat n + 1"
  by (simp add: integer_eq_iff integer_of_nat.rep_eq)

lemma integer_of_nat_ge0 [simp]: "0 \<le> integer_of_nat n"
  by (simp add: less_eq_integer.rep_eq integer_of_nat.rep_eq)

text \<open>The integers from \<open>a\<close> down to \<open>b\<close> are at most \<open>a\<close>:\<close>

lemma downto_le: "x \<in> set (downto a b) \<Longrightarrow> x \<le> a"
proof (induction a b rule: downto.induct)
  case (1 a b)
  show ?case
  proof (cases "a < b")
    case True
    with "1.prems" show ?thesis by (subst (asm) downto.simps) simp
  next
    case False
    with "1.prems" have "x = a \<or> x \<in> set (downto (a - 1) b)" by (subst (asm) downto.simps) simp
    with "1.IH"[OF False] show ?thesis by (auto simp: integer_arith)
  qed
qed

text \<open>Types and terms whose schematic variables and type variables have non-negative indices:\<close>

definition tnn :: "ptyp \<Rightarrow> bool" where
  "tnn T \<longleftrightarrow> (\<forall>(v, S)\<in>tvars T. 0 \<le> snd v)"

lemma tnn_simps [simp]:
  "tnn (Type a Ts) \<longleftrightarrow> (\<forall>T\<in>set Ts. tnn T)" "tnn (TFree a S)" "tnn (TVar v S) \<longleftrightarrow> 0 \<le> snd v"
  by (auto simp: tnn_def)

definition pnn :: "pterm \<Rightarrow> bool" where
  "pnn t \<longleftrightarrow> (\<forall>v\<in>vars t. 0 \<le> snd (fst v)) \<and> (\<forall>T\<in>typs t. tnn T)"

lemma pnn_simps [simp]: "pnn (s $ t) \<longleftrightarrow> pnn s \<and> pnn t" "pnn (Abs a T t) \<longleftrightarrow> tnn T \<and> pnn t"
  by (auto simp: pnn_def)

end

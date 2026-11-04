section \<open>Patch 05: unsaturated flex-rigid pairs (soundness)\<close>

theory Unpatched_05_Unify_Saturate
  imports Unpatched_Base
begin

subsection \<open>A proof of \<open>False\<close>\<close>

text \<open>
  The subgoal \<open>?v True = ?w \<and> undefined = undefined\<close> of the valid rule \<open>False_sat_aux\<close> has the
  type variable \<open>?'b\<close> of \<open>?v True\<close>, \<open>?w\<close> and \<open>undefined\<close>. Resolution with \<open>id ?x = id ?x \<and>
  undefined = undefined\<close>, where the second \<open>undefined\<close> has type \<open>nat \<Rightarrow> nat\<close>, simplifies the
  flex-rigid pair \<open>?v True =?= id ?x\<close> while \<open>?'b\<close> is unbound, so that it is not \<eta>-expanded, and
  then binds \<open>?'b := nat \<Rightarrow> nat\<close>. \<open>MATCH\<close> abstracts the copy \<open>id (?x' a)\<close> over both argument types
  of \<open>?v :: bool \<Rightarrow> nat \<Rightarrow> nat\<close>, where the bound variable meant for the argument \<open>True\<close> refers to
  the second abstraction: \<open>?v := \<lambda>a b. id (?x' b)\<close>, so \<open>?v True\<close> becomes \<open>\<lambda>b. id (?x' b)\<close>,
  whereas \<open>?w := id (?x' True)\<close>. The binding has a function arrow too many, but neither \<open>?v\<close> nor
  its binding is unified again. Resolution of \<open>\<not> ?Q (id (?x' True))\<close> with \<open>id_neq\<close> yields
  \<open>?Q := \<lambda>f. f 0 = f 1\<close> and \<open>?x' := \<lambda>t n. n\<close>, so that the subgoal \<open>?Q (\<lambda>b. id (?x' b))\<close> becomes
  \<open>id (\<lambda>n. n) = id (\<lambda>n. n)\<close>, which \<open>refl\<close> proves: resolution (\<open>Pattern.unify\<close>) does not check the
  types of the terms that it assigns.
\<close>

lemma False_sat_aux:
  "(v :: bool \<Rightarrow> 'b) True = w \<and> (undefined :: 'b) = undefined \<Longrightarrow> \<not> Q w \<Longrightarrow> Q (v True) \<Longrightarrow> False"
  by simp

lemma id_refl: "id x = id x \<and> (undefined :: nat \<Rightarrow> nat) = undefined"
  by simp

lemma id_neq: "\<not> (id (\<lambda>n::nat. n) 0 = id (\<lambda>n. n) 1)"
  by simp

lemma bad_sat: False
  apply (rule False_sat_aux)
    apply (rule id_refl)  \<comment> \<open>\<open>?w := id (?x' True)\<close>, but \<open>?v True\<close> becomes \<open>\<lambda>b. id (?x' b)\<close>\<close>
   apply (rule id_neq)  \<comment> \<open>\<open>?Q := \<lambda>f. f 0 = f 1\<close>, \<open>?x' := \<lambda>t n. n\<close>\<close>
  apply (rule refl)  \<comment> \<open>\<open>id (\<lambda>n. n) = id (\<lambda>n. n)\<close>\<close>
  done

subsection \<open>Ill-typed proof states\<close>

text \<open>
  \<open>SIMPL\<close> \<eta>-expands the pair \<open>?v True =?= undefined True\<close> according to the type \<open>?'b\<close> of
  both sides at the time; \<open>?v True\<close> is not expanded. The pair \<open>undefined =?= undefined\<close> of the
  second conjunct then binds \<open>?'b := nat \<Rightarrow> nat\<close>. \<open>MATCH\<close> abstracts the copy of the rigid side
  over both argument types of \<open>?v :: bool \<Rightarrow> nat \<Rightarrow> nat\<close>, although \<open>?v\<close> is applied to one
  argument only: it returns \<open>?v := \<lambda>a b. undefined b\<close>, where \<open>b :: nat\<close> is passed to
  \<open>undefined :: bool \<Rightarrow> nat \<Rightarrow> nat\<close>, and on backtracking \<open>?v := \<lambda>a b. undefined True\<close>, whose
  type has one function arrow too many. Neither solves the pair, and the resulting proof
  states are not well-typed. The correct unifier \<open>?v := \<lambda>a. undefined True\<close> is lost.
\<close>

lemma unsat_aux1: "(undefined :: bool \<Rightarrow> 'b) True = undefined True \<and> (undefined :: 'b) = undefined \<Longrightarrow> True"
  by simp

lemma unsat_aux2: "(v :: bool \<Rightarrow> 'r) True = w \<Longrightarrow> v True = w \<and> (undefined :: nat \<Rightarrow> nat) = undefined"
  by simp

lemma True
  apply (rule unsat_aux1)  \<comment> \<open>leaves the type variable \<open>?'b\<close> of \<open>unsat_aux1\<close> open\<close>
  ML_val \<open>
    (*both results of the next step are ill-typed*)
    val sts = results (resolve_tac \<^context> @{thms unsat_aux2} 1) (#goal @{Isar.goal});
    val _ = \<^assert> (length sts = 2);
    val _ = \<^assert> (forall (not o can (Sign.cert_term \<^theory>) o Thm.prop_of) sts);
  \<close>
  apply (rule unsat_aux2)  \<comment> \<open>an ill-typed proof state\<close>
  oops

end

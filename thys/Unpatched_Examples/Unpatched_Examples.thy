section \<open>What the fixes of \<open>unify.ML\<close> and \<open>pattern.ML\<close> prevent, in Isabelle2026\<close>

theory Unpatched_Examples
  imports Main
begin

text \<open>
  The examples check against the unpatched \<open>unify.ML\<close> and \<open>pattern.ML\<close> of Isabelle2026. The
  proof steps that fail are stated as comments and checked by ML assertions, so that the theory
  builds.
\<close>

ML \<open>
  (*the results of a tactic on a proof state*)
  fun results tac st = Seq.list_of (tac st);
  fun refl_results ctxt st = results (resolve_tac ctxt @{thms refl} 1) st;
\<close>


section \<open>Cyclic environments: a proof of \<open>False\<close> (fix 3, \<open>unify-cyclic\<close>)\<close>

text \<open>
  \<open>MATCH\<close> copies the rigid side of a flex-rigid pair \<open>?v =?= \<lambda>x. x (\<not> ?F ?v)\<close> into \<open>?v\<close>. The
  projection on \<open>x\<close> assigns its new variable \<open>?G := \<lambda>x. \<not> ?F ?v\<close> before \<open>?v\<close> is updated to
  \<open>\<lambda>x. x (?G x)\<close>, which closes a cycle in the environment. The cyclic environment is not a
  solution: it only stands for one if \<open>?F\<close> discards its argument, but \<open>?F\<close> stays open. Since
  neither \<open>?v\<close> nor \<open>?G\<close> occurs in the remaining proof state, normalization terminates, and a
  later step can instantiate \<open>?F\<close> such that the equation has no solution.

  The first component \<open>?G True =?= False\<close> is not a pattern, so that \<open>Unify.unifiers\<close> uses
  Huet's procedure instead of \<open>Pattern.unify\<close>, whose occurs check would reject the problem.
\<close>

lemma False_aux:
  assumes 1: "(G True, \<lambda>x::bool \<Rightarrow> bool. x (\<not> F v)) = (False, v)"
    and 2: "F = (\<lambda>w. w id)"
  shows False
proof -
  from 1 have "v = (\<lambda>x. x (\<not> F v))" by simp
  then have "v id = (\<not> v id)" using 2 by (metis id_apply)
  then show False by simp
qed

lemma bad: False
  apply (rule False_aux)
   apply (rule refl)  \<comment> \<open>the cyclic ``unifier'' of \<open>?v = \<lambda>x. x (\<not> ?F ?v)\<close>\<close>
  apply (rule refl)  \<comment> \<open>\<open>?F := \<lambda>w. w id\<close>\<close>
  done

lemma "0 = (1 :: nat)"
  using bad ..


section \<open>Unsaturated flex-rigid pairs (fix 4, \<open>unify-saturate\<close>)\<close>

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
  its binding is unified again. With \<open>?Q := \<lambda>f. f 0 = f 1\<close>, the subgoal about \<open>?v True\<close> becomes
  \<open>id (?x' 0) = id (?x' 1)\<close>, and the one about \<open>?w\<close> becomes \<open>id (?x' True) 0 \<noteq> id (?x' True) 1\<close>.
  The latter fixes \<open>?x' := \<lambda>t n. n\<close>, and the former becomes \<open>id (\<lambda>n. n) = id (\<lambda>n. n)\<close>, which
  \<open>refl\<close> proves: resolution (\<open>Pattern.unify\<close>) does not check the types of the terms that it
  assigns.
\<close>

lemma False_sat_aux:
  "(v :: bool \<Rightarrow> 'b) True = w \<and> (undefined :: 'b) = undefined \<Longrightarrow> Q = Q \<Longrightarrow> Q (v True) \<Longrightarrow> \<not> Q w \<Longrightarrow> False"
  by simp

lemma id_refl: "id (x :: 'r) = id x \<and> (undefined :: nat \<Rightarrow> nat) = undefined"
  by simp

lemma id_neq: "\<not> (id (\<lambda>n::nat. n) 0 = id (\<lambda>n. n) 1)"
  by simp

lemma bad_sat: False
  apply (rule False_sat_aux)
     apply (rule id_refl)  \<comment> \<open>\<open>?w := id (?x' True)\<close>, but \<open>?v True\<close> becomes \<open>\<lambda>b. id (?x' b)\<close>\<close>
    apply (rule refl[of "\<lambda>f::nat \<Rightarrow> nat. f 0 = f 1"])  \<comment> \<open>\<open>?Q := \<lambda>f. f 0 = f 1\<close>\<close>
   defer
   apply (rule id_neq)  \<comment> \<open>\<open>?x' := \<lambda>t n. n\<close>\<close>
  apply (rule refl)  \<comment> \<open>\<open>id (\<lambda>n. n) = id (\<lambda>n. n)\<close>\<close>
  done

lemma "0 = (1 :: nat)"
  using bad_sat ..

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


section \<open>Lost unifiers\<close>

subsection \<open>The occurs check of \<open>Pattern.unify\<close> (the \<open>pattern.ML\<close> fix)\<close>

text \<open>
  \<open>Pattern.unify\<close> raises \<open>Unif\<close> for \<open>?p =?= \<not> ?f ?p\<close> because \<open>?p\<close> occurs in the rigid side,
  although only under the flexible head \<open>?f\<close>. \<open>Unify.unifiers\<close> takes this as ``no unifier'',
  but \<open>?p := \<not> False\<close>, \<open>?f := \<lambda>_. False\<close> is one.
\<close>

lemma "\<exists>p f. p = (\<not> f p)"
  apply (intro exI)
  \<comment> \<open>\<open>apply (rule refl)\<close> fails\<close>
  ML_val \<open>\<^assert> (null (refl_results \<^context> (#goal @{Isar.goal})))\<close>
  oops

lemma "\<exists>p f. p = (\<not> f p)"
  by (intro exI[where x = "\<not> False"] exI[where x = "\<lambda>_. False"]) simp


subsection \<open>The rigid occurs check of \<open>Unify\<close> (fix 2, \<open>unify-rigid-occurs\<close>)\<close>

text \<open>
  \<open>rigid_occurs_term\<close> rejects \<open>?v := \<lambda>y. y (?v (\<lambda>z. d))\<close> because \<open>?v\<close> occurs on a rigid path,
  although its argument lets an instance discard the occurrence: \<open>?v := \<lambda>y. y d\<close> is a unifier.
\<close>

lemma "\<exists>v. \<forall>y. v y = y (v (\<lambda>z::'b. d::'b))"
  apply (rule exI, rule allI)
  \<comment> \<open>\<open>apply (rule refl)\<close> fails\<close>
  ML_val \<open>\<^assert> (null (refl_results \<^context> (#goal @{Isar.goal})))\<close>
  oops

lemma "\<exists>v. \<forall>y. v y = y (v (\<lambda>z::'b. d::'b))"
  by (rule exI[where x = "\<lambda>y. y d"]) simp


subsection \<open>Flex-flex pairs (fix 1, \<open>unify-flexflex\<close>)\<close>

text \<open>
  For \<open>\<lambda>j. ?F (\<lambda>z. z j) =?= \<lambda>j. ?G\<close>, \<open>clean_term\<close> deletes the argument of \<open>?F\<close>, which contains
  the banned bound variable \<open>j\<close> rigidly. The only unifier is \<open>?F := \<lambda>x. ?G\<close>; it does not cover
  \<open>?F := \<lambda>x. x (\<lambda>w. c)\<close>, \<open>?G := c\<close>, which the rest of the goal needs.
\<close>

lemma "\<exists>F G. (\<forall>j::bool. F (\<lambda>z. z j) = (G::bool)) \<and> F (\<lambda>z. True) = True \<and> F (\<lambda>z. False) = False"
  apply (rule exI, rule exI, rule conjI, rule allI)
  ML_val \<open>\<^assert> (length (refl_results \<^context> (#goal @{Isar.goal})) = 1)\<close>
   apply (rule refl)
  \<comment> \<open>the remaining subgoal \<open>?G = True \<and> ?G = False\<close> is unprovable\<close>
  oops

lemma "\<exists>F G. (\<forall>j::bool. F (\<lambda>z. z j) = (G::bool)) \<and> F (\<lambda>z. True) = True \<and> F (\<lambda>z. False) = False"
  by (rule exI[where x = "\<lambda>x. x (\<lambda>w. True)"], rule exI[where x = True]) simp


section \<open>Shared variables of different types with \<open>incremented = true\<close>\<close>

text \<open>
  With \<open>incremented = true\<close>, \<open>Thm.bicompose\<close> identifies the schematic variables of the proof
  state and the rule by their names. If a variable occurs with different types in both and gets
  bound, normalization raises an exception (\<open>Envir.lookup\<close>); if the types are unified, the
  variables are identified, which yields an instance of both theorems.
\<close>

ML_val \<open>
  val st = @{lemma "(z::bool) = True \<Longrightarrow> (x::nat) = x" by simp};
  val rl = @{lemma "(x::bool) = x" by simp};
  val r = Exn.result (fn () =>
    Thm.bicompose (SOME \<^context>) {flatten = true, match = false, incremented = true}
      (false, rl, 0) 1 st |> Seq.list_of) ();
  val _ = \<^assert>
    (case r of Exn.Exn (TYPE ("Variable has two distinct types", _, _)) => true | _ => false);
\<close>

end

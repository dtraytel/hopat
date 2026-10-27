theory Partial_Termination
  imports Main
begin

text \<open>This function does not terminate if there is no 0 in the (nonempty) list.\<close>

function (sequential, domintros) rotate_to_0 :: "nat list \<Rightarrow> nat list" where
  "rotate_to_0 [] = []"
| "rotate_to_0 (0 # xs) = 0 # xs"
| "rotate_to_0 (x # xs) = rotate_to_0 (xs @ [x])"
  by pat_completeness auto

text \<open>Even though we did not (and cannot) prove termination, we get conditional
  simplification and induction rules:\<close>

thm rotate_to_0.psimps rotate_to_0.pinduct

text \<open>These only hold for arguments satisfying the domain predicate
  \<^term>\<open>rotate_to_0_dom\<close>, which describes the arguments for which the
  function terminates. Since we passed "domintros" to the function command,
  we get some introduction rules for the domain predicate:\<close>

thm rotate_to_0.domintros

text \<open>We can now prove that the function terminates for all lists containing 0.
  In a certain sense, this replaces the invocation of the termination command.
  The index of the first 0 is used as the termination measure. Note that we have
  to thread an invariant through the recursive calls!\<close>

fun index_of :: "'a \<Rightarrow> 'a list \<Rightarrow> nat" where
  "index_of _ [] = 0"
| "index_of y (x # xs) = (if x = y then 0 else Suc (index_of y xs))"

lemma index_of_append1: "y \<in> set xs \<Longrightarrow> index_of y (xs @ ys) = index_of y xs"
  by (induction xs) auto

lemma rotate_to_0_termination: "0 \<in> set xs \<Longrightarrow> rotate_to_0_dom xs"
proof (induction xs rule: wf_induct[OF wf_measure[of "index_of 0"]])
  case (1 xs)
  show ?case proof (cases xs rule: rotate_to_0.cases) \<comment> \<open>case split over the function's equations\<close>
    case 1
    then show ?thesis by (auto intro: rotate_to_0.domintros)
  next
    case (2 xs')
    then show ?thesis by (auto intro: rotate_to_0.domintros)
  next
    case (3 x xs')
    then have "index_of 0 (xs' @ [Suc x]) < index_of 0 xs"
      using "1.prems" \<comment> \<open>using the invariant\<close>
      by (simp add: index_of_append1)
    moreover have "0 \<in> set (xs' @ [Suc x])" \<comment> \<open>the invariant is preserved\<close>
      using "1.prems" unfolding "3" by simp
    ultimately show ?thesis
      using "1.IH" unfolding "3" by (auto intro: rotate_to_0.domintros)
  qed
qed

end

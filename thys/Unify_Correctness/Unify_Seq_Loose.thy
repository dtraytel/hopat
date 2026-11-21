section \<open>Sequences of Results that Bind No Loose Name\<close>

theory Unify_Seq_Loose
  imports Unify_Seq_Dfd
begin

text \<open>
  The statements on the sequences of the search have two readings: without loose names, a
  sequence is finite and its elements satisfy a predicate (\<open>fin\<close>); with loose names, the
  enumeration of the sequence ends after finitely many elements, normally or with one of the
  exceptions of \<open>gexn\<close>, and the enumerated elements whose environments bind no loose name
  satisfy the predicate (\<open>cfin\<close>).
\<close>

fun eenv :: "elem \<Rightarrow> env" where
  "eenv (El_R env tps) = env"
| "eenv (El_E env dps) = env"

context pure_sig_gen
begin

definition lfin :: "cfg \<Rightarrow> seq \<Rightarrow> (elem \<Rightarrow> bool) \<Rightarrow> bool" where
  "lfin cfg s Q \<longleftrightarrow> (if loose = {} then fin cfg s Q else cfin cfg s (\<lambda>x. nfree (eenv x) \<longrightarrow> Q x))"

lemma lfin_strict: "loose = {} \<Longrightarrow> lfin cfg s Q \<longleftrightarrow> fin cfg s Q"
  unfolding lfin_def by simp

lemma lfin_looseI: "loose \<noteq> {} \<Longrightarrow> cfin cfg s (\<lambda>x. nfree (eenv x) \<longrightarrow> Q x) \<Longrightarrow> lfin cfg s Q"
  unfolding lfin_def by simp

lemma lfin_loose: "loose \<noteq> {} \<Longrightarrow> lfin cfg s Q \<Longrightarrow> cfin cfg s (\<lambda>x. nfree (eenv x) \<longrightarrow> Q x)"
  unfolding lfin_def by simp

lemma lfin_cfin: assumes "cfin cfg s Q" shows "lfin cfg s Q"
proof (cases "loose = {}")
  case True
  show ?thesis by (subst lfin_strict[OF True]) (rule cfin_fin[OF True assms])
next
  case False
  show ?thesis by (rule lfin_looseI[OF False cfin_mono[OF assms]]) simp
qed

lemma lfin_mono_nf:
  assumes "lfin cfg s P" "\<And>x. nfree (eenv x) \<Longrightarrow> P x \<Longrightarrow> Q x"
  shows "lfin cfg s Q"
proof (cases "loose = {}")
  case True
  from assms(1) have "fin cfg s P" by (subst (asm) lfin_strict[OF True])
  then have "fin cfg s Q" by (rule fin_mono) (rule assms(2)[OF nfree_strict[OF True]])
  then show ?thesis by (subst lfin_strict[OF True])
next
  case False
  show ?thesis by (rule lfin_looseI[OF False cfin_mono[OF lfin_loose[OF False assms(1)]]]) (use assms(2) in blast)
qed

lemma lfin_mono: "lfin cfg s P \<Longrightarrow> (\<And>x. P x \<Longrightarrow> Q x) \<Longrightarrow> lfin cfg s Q"
  by (rule lfin_mono_nf)

lemma lfin_Empty [simp]: "lfin cfg S_Empty Q"
  by (rule lfin_cfin) simp

lemma lfin_Single:
  assumes "nfree (eenv x) \<Longrightarrow> Q x" shows "lfin cfg (S_Single x) Q"
proof (cases "loose = {}")
  case True
  then have "Q x" using assms nfree_strict[OF True] by blast
  then show ?thesis by (rule lfin_cfin[OF cfin_Single])
next
  case False
  show ?thesis by (rule lfin_looseI[OF False cfin_Single]) (use assms in blast)
qed

text \<open>Pulling an element: it satisfies the predicate, and so does the rest of the sequence.\<close>

lemma evalx_pull:
  assumes "evalx cfg s xs" "pull cfg s = Some (evs, Ok (Some (x, s')))"
  obtains xs' where "xs = x # xs'" "evalx cfg s' xs'"
  using assms(1) by (cases rule: evalx.cases) (use assms(2) in auto)

lemma cfin_pull:
  assumes "cfin cfg s Q" "pull cfg s = Some (evs, Ok (Some (x, s')))"
  shows "Q x \<and> cfin cfg s' Q"
proof -
  from assms(1) obtain xs where xs: "evalx cfg s xs" "\<forall>y\<in>set xs. Q y" by (auto simp: cfin_def)
  from evalx_pull[OF xs(1) assms(2)] obtain xs' where "xs = x # xs'" "evalx cfg s' xs'" .
  with xs(2) show ?thesis by (auto simp: cfin_def)
qed

lemma evalx_det: "evalx cfg s xs \<Longrightarrow> evalx cfg s ys \<Longrightarrow> xs = ys"
proof (induction arbitrary: ys rule: evalx.induct)
  case (Nil s evs)
  from Nil.prems show ?case by (cases rule: evalx.cases) (use Nil.hyps in simp_all)
next
  case (Exn s evs e)
  from Exn.prems show ?case by (cases rule: evalx.cases) (use Exn.hyps in simp_all)
next
  case (Cons s evs x s' xs)
  from Cons.prems show ?case
  proof (cases rule: evalx.cases)
    case (Cons evs' x' s'' ys')
    with Cons.hyps(1) have "x' = x" "s'' = s'" by simp_all
    with Cons.IH[OF Cons(3)[unfolded \<open>s'' = s'\<close>]] Cons show ?thesis by simp
  qed (use Cons.hyps(1) in simp_all)
qed

lemma lfin_pull:
  assumes "lfin cfg s P" "pull cfg s = Some (evs, Ok (Some (x, s')))"
  shows "(nfree (eenv x) \<longrightarrow> P x) \<and> lfin cfg s' P"
proof (cases "loose = {}")
  case True
  from assms(1) have "cfin cfg s P" by (subst (asm) lfin_strict[OF True]) (rule fin_cfin)
  from cfin_pull[OF this assms(2)] show ?thesis by (auto intro: lfin_cfin)
next
  case False
  from cfin_pull[OF lfin_loose[OF False assms(1)] assms(2)] show ?thesis
    using False by (auto simp: lfin_looseI)
qed

end

end

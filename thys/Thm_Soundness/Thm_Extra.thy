section \<open>The sort hypotheses, hypotheses and constraints computed by the generated code\<close>

theory Thm_Extra
  imports Thm_Type "Pure_Thm.Pure_Extra"
begin

text \<open>
  The wrappers of \<open>thm.ML\<close> (\<open>bicompose_wrapper.ML\<close>) compute the sort hypotheses, hypotheses and
  sort constraints of the results with the operations of theory \<^theory>\<open>Pure_Thm.Pure_Extra\<close>
  (models of \<open>Sorts.union\<close>, \<open>Sorts.insert_term\<close>, \<open>Envir.insert_sorts\<close>, \<open>union_hyps\<close>,
  \<open>insert_hyps\<close>, \<open>remove_hyps\<close>, \<open>union_constraints\<close>, \<open>insert_constraints\<close>,
  \<open>insert_constraints_env\<close>), applied to the data of the premises as the rules on
  \<^typ>\<open>'u pure_thm\<close> apply the corresponding operations on sets. These operations compute the
  sets of the rules on \<^typ>\<open>'u pure_thm\<close>: sort hypotheses and constraints (without their
  theories) exactly, hypotheses up to \<open>\<alpha>\<close>-equivalence (\<open>union_hyps\<close> and \<open>insert_hyps\<close> keep one of
  two \<open>\<alpha>\<close>-equivalent hypotheses; \<open>remove_hyps\<close> removes the first one, which is the only one in
  an ordered list).
\<close>


subsection \<open>Sort hypotheses\<close>

lemma typ_sorts_tsorts: "typ_sorts T = tsorts T"
  by (induction T) auto

lemma term_sorts_tm_sorts: "term_sorts t = tm_sorts t"
  by (induction t) (auto simp: typ_sorts_tsorts)

lemma set_insert_term_sorts_tm: "set (insert_term_sorts t Ss) = tm_sorts t \<union> set Ss"
  by (simp add: term_sorts_tm_sorts)

lemma set_env_insert_sorts_tyenv: "set (env_insert_sorts tye Ss) = tyenv_sorts tye \<union> set Ss"
  by (auto simp: set_env_insert_sorts tyenv_sorts_def typ_sorts_tsorts)


subsection \<open>Sort constraints\<close>

lemma smash_atyps_eq: "smash_atyps T = map_atyps smash_atyp T"
  unfolding smash_atyps_def by (rule arg_cong[of _ _ "\<lambda>f. map_atyps f T"]) (auto simp: smash_atyp_def aT_def split: ptyp.splits)

lemma constraint_ignored_eq: "constraint_ignored T S \<longleftrightarrow> cons_ignored T S"
  by (simp add: constraint_ignored_def cons_ignored_def)

text \<open>The constraints without their theories:\<close>

abbreviation cons_set :: "'t constraint list \<Rightarrow> (ptyp \<times> psort) set" where
  "cons_set cs \<equiv> snd ` set cs"

lemma cons_set_union:
  "(\<And>a b. tord a b = EQUAL \<Longrightarrow> a = b) \<Longrightarrow> cons_set (union_constraints tord cs cs') = cons_set cs \<union> cons_set cs'"
  by (simp add: set_union_constraints image_Un)

lemma cons_set_insert:
  "(\<And>a b. tord a b = EQUAL \<Longrightarrow> a = b) \<Longrightarrow> cons_set (insert_constraint tord thy (T, S) cs) =
    (if cons_ignored T S then {} else {(map_atyps smash_atyp T, S)}) \<union> cons_set cs"
  by (auto simp: set_insert_constraint' constraint_ignored_eq smash_atyps_eq)

theorem cons_set_env:
  assumes t: "\<And>a b. tord a b = EQUAL \<Longrightarrow> a = b"
    and ac: "tacyc (tyenv env)" and tc: "tcons_env (tyenv env)"
    and ok: "env_insert_constraints tord thy (tyenv env) cs = Some (Ok cs')"
  shows "cons_set cs' = env_constraints env \<union> cons_set cs"
proof -
  have n: "T' = tnorm (tyenv env) T"
    if "vt_lookup (tyenv env) v = Some (S, T)" "norm_type (tyenv env) T = Some (Ok T')" for v S T T'
  proof -
    have "tcons (tyenv env) T" using tc that(1) unfolding tcons_env_def by blast
    then have "norm_type (tyenv env) T = return (tnorm (tyenv env) T)" by (rule norm_type_ok[OF ac tc])
    with that(2) show ?thesis by (simp add: return_def)
  qed
  have e: "set cs' = {(thy, smash_atyps (tnorm (tyenv env) T), S) | v S T.
      vt_lookup (tyenv env) v = Some (S, T) \<and> \<not> constraint_ignored (tnorm (tyenv env) T) S} \<union> set cs"
    by (rule set_env_insert_constraints[where nf = "tnorm (tyenv env)", OF t n ok]) blast+
  have "snd ` {(thy, smash_atyps (tnorm (tyenv env) T), S) | v S T.
      vt_lookup (tyenv env) v = Some (S, T) \<and> \<not> constraint_ignored (tnorm (tyenv env) T) S} = env_constraints env"
    unfolding env_constraints_def constraint_ignored_eq smash_atyps_eq by (auto simp: image_iff; metis)
  then show ?thesis by (simp add: e image_Un)
qed

end

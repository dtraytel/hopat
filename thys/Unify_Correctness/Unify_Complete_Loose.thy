section \<open>Completeness With Names at Two Types\<close>

theory Unify_Complete_Loose
  imports Unify_Complete
begin

text \<open>
  The completeness theorems of \<^const>\<open>unify\<close> and \<^const>\<open>unifiers\<close> are stated in the locale
  \<^locale>\<open>pure_sig\<close>, whose invariant \<open>vinv\<close> asks that every name of a schematic variable
  has one type under the type instantiation of the solution. In the general locale
  \<^locale>\<open>pure_sig_gen\<close>, the names in \<open>loose\<close> may keep two types in a solution: then the two
  occurrences are two different variables. This theory shows that completeness does not hold
  for such solutions, and that it does hold for the solutions that give every name one type,
  also when a name occurs with two types in the problem.
\<close>


subsection \<open>A counterexample\<close>

text \<open>
  A signature without classes, arities or constants of its own; \<open>Pure.all\<close> is built in. The
  name \<open>?x\<close> is loose.
\<close>

definition algL :: algebra where
  "algL = Algebra (\<lambda>_ _. False) (\<lambda>_. []) {}"

definition xL :: indexname where "xL = (STR ''x'', 0)"

abbreviation (input) "pT \<equiv> Type STR ''prop'' []"

lemma pure_sig_gen_L: "pure_sig_gen algL (\<lambda>_. 0)"
  unfolding pure_sig_gen_def by unfold_locales (simp_all add: algL_def class_le_def)

text \<open>
  The problem \<open>?x::prop =?= Pure.all (?x::prop \<Rightarrow> prop)\<close>. Its two sides are closed and of type
  \<open>prop\<close>.
\<close>

definition sL :: pterm where "sL = Var xL pT"
definition tL :: pterm where "tL = Const STR ''Pure.all'' ((pT \<rightarrow>\<^sub>T pT) \<rightarrow>\<^sub>T pT) $ Var xL (pT \<rightarrow>\<^sub>T pT)"

definition envL :: env where "envL = Envir 0 vt_empty vt_empty"

text \<open>
  Pattern unification fails with \<open>Unif\<close>: the occurs check of the flex-rigid pair compares the
  names of the variables only, and finds \<open>?x\<close> in a rigid position of the other side.
\<close>

lemma unify_L: "\<exists>u. unify algL sL tL envL = raise (Unif u)"
  apply (simp add: unify_def unif.simps sL_def tL_def head_norm.simps flexrigid_def occurs.simps
      lookup_def envL_def strip_comb_def ints_of'_def rigid_occurs.simps)
  done

lemma unifiers_L: "unifiers algL envL [(sL, tL)] = return S_Empty"
  using unify_L by (auto simp: unifiers_def handle_def raise_def return_def bindM_def)

text \<open>
  A solution: the identity on types, and \<open>?x::prop \<mapsto> Pure.all (?x::prop \<Rightarrow> prop)\<close>; the
  variable \<open>?x::prop \<Rightarrow> prop\<close> is left as it is.
\<close>

definition \<rho>L :: tinst where "\<rho>L = TVar"

definition \<sigma>L :: vsubst where
  "\<sigma>L y T = (if y = xL \<and> T = pT then Const STR ''Pure.all'' ((pT \<rightarrow>\<^sub>T pT) \<rightarrow>\<^sub>T pT) $ Var xL (pT \<rightarrow>\<^sub>T pT)
    else Var y T)"

context
begin

interpretation L: pure_sig_gen algL "\<lambda>_. 0" "\<lambda>_. None" "{xL}"
  by (rule pure_sig_gen_L)

lemma solves_L: "L.ap \<rho>L \<sigma>L sL = L.ap \<rho>L \<sigma>L tL"
  by (simp add: L.ap_def sL_def tL_def \<sigma>L_def \<rho>L_def)

lemma cert_L [simp]: "cert_typ algL (\<lambda>_. 0) pT" "cert_typ algL (\<lambda>_. 0) (pT \<rightarrow>\<^sub>T pT)"
  "cert_typ algL (\<lambda>_. 0) ((pT \<rightarrow>\<^sub>T pT) \<rightarrow>\<^sub>T pT)"
  by (simp_all add: cert_typ_def tarity_def)

lemma const_L [simp]: "const_typ_ok (\<lambda>_. None) STR ''Pure.all'' ((pT \<rightarrow>\<^sub>T pT) \<rightarrow>\<^sub>T pT)"
  by (simp add: const_typ_ok_def)

lemma typing_L: "L.typing e sL pT" "L.typing e tL pT"
  by (auto simp: sL_def tL_def)

lemma wt_subst_L: "L.wt_subst \<sigma>L"
  unfolding L.wt_subst_def closed_subst_def \<sigma>L_def using typing_L(2) by (auto simp: closed_def tL_def)

lemma cinv_L: "L.cinv \<rho>L \<sigma>L envL (\<lambda>_. pT) [] (vars sL \<union> vars tL) {}"
  unfolding L.cinv_def
proof (intro conjI)
  show "L.solution \<rho>L \<sigma>L envL"
  proof -
    have "wsinst algL \<rho>L" unfolding wsinst_def \<rho>L_def by (intro allI) (rule L.has_sort_TVar_refl)
    then show ?thesis using wt_subst_L by (simp add: L.solution_def tsol_def envL_def)
  qed
  show "L.wt_env \<rho>L envL" by (simp add: L.wt_env_def envL_def)
  show "L.bs_env \<rho>L (\<lambda>_. pT) []" by (simp add: L.bs_env_def)
  show "L.vinv \<rho>L envL (vars sL \<union> vars tL)"
    unfolding L.vinv_def L.vcons_def by (auto simp: below_def sL_def tL_def xL_def envL_def evars_def bnds_def)
  show "L.tvinv {} envL"
    by (simp add: L.tvinv_def tinv_def envL_def tacyc_def tdep_def tvars_env_def scons_def acyclic_def)
  show "L.btvars [] \<union> L.vtvars (vars sL \<union> vars tL) \<subseteq> tvars_env (tyenv envL) \<union> {}"
    by (simp add: L.btvars_def L.vtvars_def sL_def tL_def)
qed

lemma cterm_L: "L.cterm \<rho>L envL (\<lambda>_. pT) [] {} sL pT" "L.cterm \<rho>L envL (\<lambda>_. pT) [] {} tL pT"
  using typing_L by (auto simp: L.cterm_def \<rho>L_def sL_def tL_def ttvars_def)

theorem unify_incomplete_L: "\<not> L.step_cp envL [] sL tL (unify algL sL tL envL)"
proof
  assume "L.step_cp envL [] sL tL (unify algL sL tL envL)"
  from L.step_cpD[OF this cinv_L order_refl cterm_L] solves_L
  have "L.ccon \<rho>L \<sigma>L envL (\<lambda>_. pT) [] (vars sL \<union> vars tL) {} (unify algL sL tL envL)"
    by (simp add: L.conv_refl)
  then show False using unify_L by (auto simp: L.ccon_def raise_def)
qed

text \<open>
  The higher-order level: the problem satisfies the invariant of the search (\<open>sinv\<close>, with the
  loose name \<open>?x\<close>), and the solution satisfies the conditions of the invariant \<open>scinv\<close> of the
  completeness proof, with \<open>vinv\<close> of the general locale. In \<^locale>\<open>pure_sig\<close> these give an
  element of the sequence of \<^const>\<open>unifiers\<close> with an agreeing solution
  (\<open>pure_sig.unifiers_complete\<close>). Here the sequence is empty.
\<close>

theorem unifiers_incomplete_L:
  "L.sinv {} {} (vars sL \<union> vars tL) envL [([], sL, tL)]"
  "L.solution \<rho>L \<sigma>L envL \<and> L.wt_env \<rho>L envL \<and> L.vinv \<rho>L envL (vars sL \<union> vars tL) \<and> L.tvinv {} envL \<and>
    L.vtvars (vars sL \<union> vars tL) \<subseteq> tvars_env (tyenv envL) \<and>
    L.dtyped \<rho>L [([], sL, tL)] \<and> L.dsolved \<rho>L \<sigma>L [([], sL, tL)]"
  "unifiers algL envL [(sL, tL)] = return S_Empty"
  "\<not> ev cfg S_Empty x"
proof -
  note ci = cinv_L[unfolded L.cinv_def]
  have inst_s: "inst \<rho> sL = sL" and inst_t: "inst \<rho> tL = tL" for \<rho>
    by (simp_all add: sL_def tL_def)
  show "L.solution \<rho>L \<sigma>L envL \<and> L.wt_env \<rho>L envL \<and> L.vinv \<rho>L envL (vars sL \<union> vars tL) \<and> L.tvinv {} envL \<and>
    L.vtvars (vars sL \<union> vars tL) \<subseteq> tvars_env (tyenv envL) \<and>
    L.dtyped \<rho>L [([], sL, tL)] \<and> L.dsolved \<rho>L \<sigma>L [([], sL, tL)]"
  proof -
    have "\<exists>e T. L.bs_env \<rho>L e [] \<and> L.typing e (inst \<rho>L sL) T \<and> L.typing e (inst \<rho>L tL) T"
      using typing_L by (auto simp: inst_s inst_t L.bs_env_def)
    moreover have "\<not> loose_bvar sL (ilength []) \<and> \<not> loose_bvar tL (ilength [])"
      by (simp add: sL_def tL_def)
    ultimately show ?thesis using ci solves_L unfolding L.dtyped_def L.dsolved_def
      by (auto simp: L.conv_refl)
  qed
  have ei: "L.einv {} {} envL"
    using ci by (simp add: L.einv_def envL_def scert_def tcert_def tcovered_def L.acyc_def L.dep_def
        L.closed_env_def L.bbelow_def tsorted_def bsorted_def tvars_env_def acyclic_def)
  have wi: "L.winv envL (vars sL \<union> vars tL)"
    unfolding L.winv_def L.vinv_def L.vcons_def
    by (auto simp: L.wt_env_def below_def sL_def tL_def xL_def envL_def evars_def bnds_def)
  have up: "L.upok {} envL [] (vars sL \<union> vars tL) sL tL"
    unfolding L.upok_def
  proof (intro conjI allI impI)
    show "\<exists>e T. L.bs_env \<rho> e [] \<and> L.typing e (inst \<rho> sL) T \<and> L.typing e (inst \<rho> tL) T" for \<rho>
      using typing_L by (auto simp: inst_s inst_t L.bs_env_def)
  qed (auto simp: L.btvars_def L.vtvars_def ttvars_def sL_def tL_def evars_def bnds_def envL_def)
  show "L.sinv {} {} (vars sL \<union> vars tL) envL [([], sL, tL)]"
    using ei wi up by (simp add: L.sinv_def)
  show "unifiers algL envL [(sL, tL)] = return S_Empty" by (rule unifiers_L)
  show "\<not> ev cfg S_Empty x" by (auto elim: ev_EmptyE)
qed

end


subsection \<open>Completeness for the solutions that give every name one type\<close>

text \<open>
  The completeness proofs of \<^locale>\<open>pure_sig\<close> carry over to \<^locale>\<open>pure_sig_gen\<close>
  through an interpretation, since the algorithm does not depend on \<open>loose\<close>. For pattern
  unification the invariant is about the solution only: a name may occur with two types in the
  problem and the environment, as long as the solution gives them one type.
\<close>

context pure_sig_gen
begin

interpretation one: pure_sig alg ar ctab
  by (simp add: pure_sig_iff wf_algebra_axioms)

lemma one_vinv:
  "one.vinv \<rho> env X \<longleftrightarrow> vinv \<rho> env X \<and>
    (\<forall>x T U. (x, T) \<in> X \<union> evars env \<longrightarrow> (x, U) \<in> X \<union> evars env \<longrightarrow> tsubst \<rho> T = tsubst \<rho> U)"
  unfolding one.vinv_def vinv_def one.vcons_def vcons_def by blast

theorem unify_complete_one_type:
  assumes u: "unify alg s t env = Some r"
    and sol: "solution \<rho> \<sigma> env" and wte: "wt_env \<rho> env" and vi: "vinv \<rho> env (vars s \<union> vars t)"
    and one: "\<And>x T U. (x, T) \<in> vars s \<union> vars t \<union> evars env \<Longrightarrow> (x, U) \<in> vars s \<union> vars t \<union> evars env \<Longrightarrow>
      tsubst \<rho> T = tsubst \<rho> U"
    and tv: "tvinv A env" and tvs: "ttvars s \<union> ttvars t \<subseteq> tvars_env (tyenv env) \<union> A"
    and ty: "e \<turnstile> inst \<rho> s : T" "e \<turnstile> inst \<rho> t : T" and cl: "closed s" "closed t"
    and eq: "ap \<rho> \<sigma> s \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma> t"
  shows "no_unif (Some r)"
    and "r = Ok env' \<Longrightarrow> \<exists>\<rho>' \<sigma>'. solution \<rho>' \<sigma>' env' \<and> tagree (maxidx env) \<rho> \<rho>' \<and>
      sagree (maxidx env) \<sigma> \<sigma>' \<and> wt_env \<rho>' env' \<and> tvinv A env'"
proof -
  have vi1: "one.vinv \<rho> env (vars s \<union> vars t)" unfolding one_vinv using vi one by blast
  note uc = one.unify_complete[OF u sol wte vi1 tv tvs ty cl eq]
  show "no_unif (Some r)" by (rule uc(1))
  show "r = Ok env' \<Longrightarrow> \<exists>\<rho>' \<sigma>'. solution \<rho>' \<sigma>' env' \<and> tagree (maxidx env) \<rho> \<rho>' \<and>
      sagree (maxidx env) \<sigma> \<sigma>' \<and> wt_env \<rho>' env' \<and> tvinv A env'" by (rule uc(2))
qed

end

end

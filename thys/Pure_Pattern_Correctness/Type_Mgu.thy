section \<open>Most General Well-Sorted Type Unifiers\<close>

theory Type_Mgu
  imports Type_Unify
begin

text \<open>
  We show that \<^const>\<open>unify_aux\<close> terminates on acyclic, sort-consistent type environments and
  either computes a most general well-sorted unifier or fails with \<open>TUnify\<close>, in which case no
  well-sorted unifier exists. Solutions are instantiations \<open>\<rho>\<close> of type variables that
  satisfy all bindings; they are well-sorted if each type variable is mapped to a type of its sort.
\<close>


lemma return_raise_simps[simp]:
  "return x = return y \<longleftrightarrow> x = y" "raise e = raise e' \<longleftrightarrow> e = e'"
  "return x \<noteq> raise e" "raise e \<noteq> return x"
  by (simp_all add: return_def raise_def)


subsection \<open>Extensions of type environments\<close>

definition textends :: "tyenv \<Rightarrow> tyenv \<Rightarrow> bool" where
  "textends \<theta> \<theta>' \<longleftrightarrow> (\<forall>v x. vt_lookup \<theta> v = Some x \<longrightarrow> vt_lookup \<theta>' v = Some x)"

lemma textends_refl[simp]: "textends \<theta> \<theta>"
  by (simp add: textends_def)

lemma textends_trans: "textends \<theta>1 \<theta>2 \<Longrightarrow> textends \<theta>2 \<theta>3 \<Longrightarrow> textends \<theta>1 \<theta>3"
  by (simp add: textends_def)

lemma textends_update: "vt_lookup \<theta> v = None \<Longrightarrow> textends \<theta> (vt_update (v, x) \<theta>)"
  by (auto simp: textends_def)

lemma tdep_mono: "textends \<theta> \<theta>' \<Longrightarrow> tdep \<theta> \<subseteq> tdep \<theta>'"
  unfolding textends_def tdep_def by blast

lemma tacyc_textends: "textends \<theta> \<theta>' \<Longrightarrow> tacyc \<theta>' \<Longrightarrow> tacyc \<theta>"
  unfolding tacyc_def by (rule acyclic_subset[OF _ tdep_mono])

lemma tnorm_tsubst: "tnorm \<theta> T = tsubst (\<lambda>w S. tnorm \<theta> (TVar w S)) T"
  by (simp add: tnorm_def)

lemma tnorm_tnorm: "tnorm \<theta>' (tnorm \<theta> T) = tsubst (\<lambda>w S. tnorm \<theta>' (tnorm \<theta> (TVar w S))) T"
  by (induction T) auto

lemma tnorm_textends:
  assumes ac: "tacyc \<theta>'" and ext: "textends \<theta> \<theta>'"
  shows "tnorm \<theta>' (tnorm \<theta> T) = tnorm \<theta>' T"
proof -
  have ac0: "tacyc \<theta>" by (rule tacyc_textends[OF ext ac])
  have var: "tnorm \<theta>' (tnorm \<theta> (TVar v S)) = tnorm \<theta>' (TVar v S)" for v S
  proof (induction v arbitrary: S rule: tdep_induct[OF ac0])
    case (1 v)
    show ?case
    proof (cases "vt_lookup \<theta> v")
      case (Some b)
      obtain S0 U where b: "b = (S0, U)" by force
      have "tnorm \<theta>' (tnorm \<theta> U) = tsubst (\<lambda>w S. tnorm \<theta>' (tnorm \<theta> (TVar w S))) U"
        by (rule tnorm_tnorm)
      also have "\<dots> = tsubst (\<lambda>w S. tnorm \<theta>' (TVar w S)) U"
        by (rule tsubst_cong, rule "1.IH") (use Some b in \<open>force simp: tdep_def\<close>)
      also have "\<dots> = tnorm \<theta>' U" by (rule tnorm_tsubst[symmetric])
      finally show ?thesis
        using Some b ext by (simp add: tnorm_TVar[OF ac0] tnorm_TVar[OF ac] textends_def)
    qed (simp add: tnorm_TVar[OF ac0])
  qed
  show ?thesis
    by (subst tnorm_tnorm, simp only: var, rule tnorm_tsubst[symmetric])
qed


subsection \<open>Unbound variables of normal forms\<close>

definition uvars :: "tyenv \<Rightarrow> ptyp \<Rightarrow> indexname set" where
  "uvars \<theta> T = fst ` tvars (tnorm \<theta> T)"

lemma finite_uvars[simp]: "finite (uvars \<theta> T)"
  by (simp add: uvars_def)

lemma uvars_Type[simp]: "uvars \<theta> (Type a Ts) = (\<Union>T\<in>set Ts. uvars \<theta> T)"
  by (auto simp: uvars_def)

lemma uvars_tvars: "(w, S) \<in> tvars T \<Longrightarrow> uvars \<theta> (TVar w S) \<subseteq> uvars \<theta> T"
  by (subst (2) uvars_def, subst tnorm_tsubst) (force simp: uvars_def tvars_tsubst)

lemma uvars_TVar:
  "tacyc \<theta> \<Longrightarrow> uvars \<theta> (TVar w S) = (case vt_lookup \<theta> w of None \<Rightarrow> {w} | Some (S', U) \<Rightarrow> uvars \<theta> U)"
  by (auto simp: uvars_def split: option.splits)

lemma uvars_unbound: "tacyc \<theta> \<Longrightarrow> w \<in> uvars \<theta> T \<Longrightarrow> vt_lookup \<theta> w = None"
  by (auto simp: uvars_def dest: tnorm_unbound)

lemma uvars_textends:
  assumes ac: "tacyc \<theta>'" and ext: "textends \<theta> \<theta>'"
  shows "uvars \<theta>' T = (\<Union>w\<in>uvars \<theta> T. case vt_lookup \<theta>' w of None \<Rightarrow> {w} | Some (S', U) \<Rightarrow> uvars \<theta>' U)"
proof -
  have "uvars \<theta>' T = fst ` tvars (tsubst (\<lambda>w S. tnorm \<theta>' (TVar w S)) (tnorm \<theta> T))"
    by (simp add: uvars_def tnorm_textends[OF ac ext] flip: tnorm_tsubst)
  also have "\<dots> = (\<Union>(w, S)\<in>tvars (tnorm \<theta> T). uvars \<theta>' (TVar w S))"
    by (auto simp: tvars_tsubst uvars_def)
  also have "\<dots> = (\<Union>(w, S)\<in>tvars (tnorm \<theta> T). uvars \<theta>' (TVar w undefined))"
    by (simp add: uvars_TVar[OF ac])
  also have "\<dots> = (\<Union>w\<in>uvars \<theta> T. uvars \<theta>' (TVar w undefined))"
    by (force simp: uvars_def)
  finally show ?thesis by (simp add: uvars_TVar[OF ac])
qed

lemma uvars_mono:
  "tacyc \<theta>' \<Longrightarrow> textends \<theta> \<theta>' \<Longrightarrow> uvars \<theta> T \<subseteq> uvars \<theta> U \<Longrightarrow> uvars \<theta>' T \<subseteq> uvars \<theta>' U"
  by (simp add: uvars_textends) blast


subsection \<open>Renamings\<close>

text \<open>An extension that only renames unbound variables preserves sizes of normal forms.\<close>

definition renames :: "tyenv \<Rightarrow> tyenv \<Rightarrow> bool" where
  "renames \<theta> \<theta>' \<longleftrightarrow> (\<forall>v S. vt_lookup \<theta> v = None \<longrightarrow> (\<exists>u S'. tnorm \<theta>' (TVar v S) = TVar u S'))"

lemma size_tsubst_var:
  "(\<And>w S. (w, S) \<in> tvars T \<Longrightarrow> \<exists>u S'. \<rho> w S = TVar u S') \<Longrightarrow> size (tsubst \<rho> T) = size T"
proof (induction T)
  case (Type a Ts)
  then have "map (size \<circ> tsubst \<rho>) Ts = map size Ts"
    by (intro map_cong refl) force
  then show ?case by (simp add: size_list_conv_sum_list cong: map_cong)
qed force+

lemma renames_size:
  assumes ac: "tacyc \<theta>'" and ext: "textends \<theta> \<theta>'" and r: "renames \<theta> \<theta>'"
  shows "size (tnorm \<theta>' T) = size (tnorm \<theta> T)"
proof -
  have ac0: "tacyc \<theta>" by (rule tacyc_textends[OF ext ac])
  have "size (tnorm \<theta>' T) = size (tsubst (\<lambda>w S. tnorm \<theta>' (TVar w S)) (tnorm \<theta> T))"
    by (simp add: tnorm_textends[OF ac ext] flip: tnorm_tsubst)
  also have "\<dots> = size (tnorm \<theta> T)"
    by (rule size_tsubst_var) (use r tnorm_unbound[OF ac0] in \<open>auto simp: renames_def\<close>)
  finally show ?thesis .
qed

lemma renames_card:
  assumes ac: "tacyc \<theta>'" and ext: "textends \<theta> \<theta>'" and r: "renames \<theta> \<theta>'"
  shows "card (uvars \<theta>' T) \<le> card (uvars \<theta> T)"
proof -
  have ac0: "tacyc \<theta>" by (rule tacyc_textends[OF ext ac])
  have "\<exists>u. uvars \<theta>' (TVar w undefined) = {u}" if w: "w \<in> uvars \<theta> T" for w
  proof -
    obtain u S' where "tnorm \<theta>' (TVar w undefined) = TVar u S'"
      using r uvars_unbound[OF ac0 w] unfolding renames_def by blast
    then show ?thesis by (simp add: uvars_def)
  qed
  then obtain f where f: "\<And>w. w \<in> uvars \<theta> T \<Longrightarrow> uvars \<theta>' (TVar w undefined) = {f w}" by metis
  have "uvars \<theta>' T = f ` uvars \<theta> T"
    using f by (subst uvars_textends[OF ac ext]) (auto simp: uvars_TVar[OF ac, of _ undefined, symmetric])
  then show ?thesis by (simp add: card_image_le)
qed

lemma renames_refl[simp]: "tacyc \<theta> \<Longrightarrow> renames \<theta> \<theta>"
  by (simp add: renames_def)

lemma renames_trans:
  assumes ac: "tacyc \<theta>3" and ext: "textends \<theta>2 \<theta>3" "textends \<theta>1 \<theta>2"
    and r: "renames \<theta>1 \<theta>2" "renames \<theta>2 \<theta>3"
  shows "renames \<theta>1 \<theta>3"
  unfolding renames_def
proof (intro allI impI)
  fix v S assume v: "vt_lookup \<theta>1 v = None"
  then obtain u S' where u: "tnorm \<theta>2 (TVar v S) = TVar u S'" using r(1) unfolding renames_def by blast
  then have "vt_lookup \<theta>2 u = None"
    using tnorm_unbound[OF tacyc_textends[OF ext(1) ac], of u S' "TVar v S"] by simp
  then obtain u' S'' where "tnorm \<theta>3 (TVar u S') = TVar u' S''" using r(2) unfolding renames_def by blast
  moreover have "tnorm \<theta>3 (TVar v S) = tnorm \<theta>3 (TVar u S')"
    using tnorm_textends[OF ac ext(1), of "TVar v S"] u by simp
  ultimately show "\<exists>u S'. tnorm \<theta>3 (TVar v S) = TVar u S'" by auto
qed


subsection \<open>Acyclicity of updates\<close>

lemma tdep_update:
  "vt_lookup \<theta> v = None \<Longrightarrow> tdep (vt_update (v, (S, U)) \<theta>) = tdep \<theta> \<union> (\<lambda>w. (w, v)) ` fst ` tvars U"
  by (auto simp: tdep_def)

lemma tdep_rtrancl_uvars:
  assumes ac: "tacyc \<theta>" and "(x, w) \<in> (tdep \<theta>)\<^sup>*" "vt_lookup \<theta> x = None"
  shows "x \<in> uvars \<theta> (TVar w S)"
  using assms(2) proof (induction arbitrary: S rule: rtrancl_induct)
  case base
  then show ?case using assms(3) by (simp add: uvars_TVar[OF ac])
next
  case (step y z)
  then obtain S' U where "vt_lookup \<theta> z = Some (S', U)" "y \<in> fst ` tvars U" by (auto simp: tdep_def)
  then show ?case using step.IH uvars_tvars by (fastforce simp: uvars_TVar[OF ac])
qed

lemma rtrancl_into_target:
  assumes "(v, y) \<in> (r \<union> E)\<^sup>*" "snd ` E \<subseteq> {v}"
  shows "y = v \<or> (v, y) \<in> r\<^sup>*"
  using assms by (induction rule: rtrancl_induct) (auto intro: rtrancl_into_rtrancl)

lemma tacyc_update:
  assumes ac: "tacyc \<theta>" and v: "vt_lookup \<theta> v = None" "v \<notin> uvars \<theta> U"
  shows "tacyc (vt_update (v, (S, U)) \<theta>)"
proof -
  have "acyclic (tdep \<theta> \<union> (\<lambda>w. (w, v)) ` W)" if "W \<subseteq> fst ` tvars U" for W
  proof -
    have "finite W" using that by (rule finite_subset) simp
    then show ?thesis using that
    proof (induction W)
      case empty
      then show ?case using ac by (simp add: tacyc_def)
    next
      case (insert w W)
      have "(v, w) \<notin> (tdep \<theta> \<union> (\<lambda>w. (w, v)) ` W)\<^sup>*"
      proof
        assume "(v, w) \<in> (tdep \<theta> \<union> (\<lambda>w. (w, v)) ` W)\<^sup>*"
        then have "w = v \<or> (v, w) \<in> (tdep \<theta>)\<^sup>*" by (rule rtrancl_into_target) auto
        then have "(v, w) \<in> (tdep \<theta>)\<^sup>*" by auto
        then have "v \<in> uvars \<theta> (TVar w undefined)" by (rule tdep_rtrancl_uvars[OF ac _ v(1)])
        moreover obtain S' where "(w, S') \<in> tvars U" using insert.prems by auto
        then have "uvars \<theta> (TVar w undefined) \<subseteq> uvars \<theta> U"
          using uvars_tvars[of w S' U \<theta>] by (simp add: uvars_TVar[OF ac] split: option.splits)
        ultimately show False using v(2) by blast
      qed
      with insert show ?case by simp
    qed
  qed
  then show ?thesis using v(1) by (simp add: tacyc_def tdep_update)
qed


subsection \<open>Solutions\<close>

text \<open>
  A solution of a type environment instantiates type variables (with their sorts) such that all
  bindings hold. It is well-sorted if it maps each type variable to a type of its sort.
\<close>

type_synonym tinst = "indexname \<Rightarrow> psort \<Rightarrow> ptyp"

definition tsol :: "tyenv \<Rightarrow> tinst \<Rightarrow> bool" where
  "tsol \<theta> \<rho> \<longleftrightarrow> (\<forall>v S U. vt_lookup \<theta> v = Some (S, U) \<longrightarrow> \<rho> v S = tsubst \<rho> U)"

definition wsinst :: "algebra \<Rightarrow> tinst \<Rightarrow> bool" where
  "wsinst alg \<rho> \<longleftrightarrow> (\<forall>v S. has_sort alg (\<rho> v S) S)"

definition tagree :: "integer \<Rightarrow> tinst \<Rightarrow> tinst \<Rightarrow> bool" where
  "tagree n \<rho> \<rho>' \<longleftrightarrow> (\<forall>v S. snd v \<le> n \<longrightarrow> \<rho>' v S = \<rho> v S)"

lemma tsol_textends: "textends \<theta> \<theta>' \<Longrightarrow> tsol \<theta>' \<rho> \<Longrightarrow> tsol \<theta> \<rho>"
  unfolding tsol_def textends_def by blast

lemma tsol_update: "tsol \<theta> \<rho> \<Longrightarrow> \<rho> v S = tsubst \<rho> U \<Longrightarrow> tsol (vt_update (v, (S, U)) \<theta>) \<rho>"
  by (simp add: tsol_def)

lemma tsubst_tnorm:
  assumes ac: "tacyc \<theta>" and tc: "tcons_env \<theta>" and sol: "tsol \<theta> \<rho>"
  shows "tcons \<theta> T \<Longrightarrow> tsubst \<rho> (tnorm \<theta> T) = tsubst \<rho> T"
proof (induction rule: tnorm_induct[OF ac tc, consumes 1, case_names TFree Type Unbound Bound])
  case (Type a Ts)
  then show ?case by (auto intro!: map_cong)
next
  case (Bound v S U)
  then show ?case using sol by (simp add: tsol_def tnorm_TVar[OF ac])
qed (simp_all add: tnorm_TVar[OF ac])

lemma tagree_refl[simp]: "tagree n \<rho> \<rho>"
  by (simp add: tagree_def)

lemma tagree_trans: "tagree n \<rho>1 \<rho>2 \<Longrightarrow> tagree n' \<rho>2 \<rho>3 \<Longrightarrow> n \<le> n' \<Longrightarrow> tagree n \<rho>1 \<rho>3"
  by (simp add: tagree_def)

lemma tagree_tsubst: "tagree n \<rho> \<rho>' \<Longrightarrow> \<forall>p\<in>tvars T. snd (fst p) \<le> n \<Longrightarrow> tsubst \<rho>' T = tsubst \<rho> T"
  by (rule tsubst_cong) (auto simp: tagree_def)


subsection \<open>The invariant\<close>

text \<open>
  The type variables of the environment and of the problem (a set \<open>A\<close> of type variables) have
  unique sorts and indices at most \<open>n\<close>, the counter for new type variables.
\<close>

definition tvars_env :: "tyenv \<Rightarrow> (indexname \<times> psort) set" where
  "tvars_env \<theta> = {p. \<exists>v S U. vt_lookup \<theta> v = Some (S, U) \<and> (p = (v, S) \<or> p \<in> tvars U)}"

definition scons :: "(indexname \<times> psort) set \<Rightarrow> bool" where
  "scons A \<longleftrightarrow> (\<forall>v S S'. (v, S) \<in> A \<longrightarrow> (v, S') \<in> A \<longrightarrow> S = S')"

text \<open>The sorts of a set of type variables are certified.\<close>

definition tcert :: "algebra \<Rightarrow> (indexname \<times> psort) set \<Rightarrow> bool" where
  "tcert alg X \<longleftrightarrow> (\<forall>p\<in>X. sort_ok alg (snd p))"

lemma tcert_Un[simp]: "tcert alg (X \<union> Y) \<longleftrightarrow> tcert alg X \<and> tcert alg Y"
  and tcert_insert[simp]: "tcert alg (insert p X) \<longleftrightarrow> sort_ok alg (snd p) \<and> tcert alg X"
  and tcert_empty[simp]: "tcert alg {}"
  by (auto simp: tcert_def)

lemma tcert_mono: "tcert alg X \<Longrightarrow> Y \<subseteq> X \<Longrightarrow> tcert alg Y"
  by (auto simp: tcert_def)

lemma tcertD: "tcert alg X \<Longrightarrow> (v, S) \<in> X \<Longrightarrow> sort_ok alg S"
  unfolding tcert_def by (drule bspec) auto

definition tinv :: "(name \<Rightarrow> nat) \<Rightarrow> integer \<Rightarrow> tyenv \<Rightarrow> (indexname \<times> psort) set \<Rightarrow> bool" where
  "tinv ar n \<theta> A \<longleftrightarrow> tacyc \<theta> \<and> scons (tvars_env \<theta> \<union> A) \<and> (\<forall>p\<in>tvars_env \<theta> \<union> A. snd (fst p) \<le> n) \<and>
     (\<forall>v S U. vt_lookup \<theta> v = Some (S, U) \<longrightarrow> wft ar U)"

lemma tvars_envI: "vt_lookup \<theta> v = Some (S, U) \<Longrightarrow> (v, S) \<in> tvars_env \<theta>"
  and tvars_envI2: "vt_lookup \<theta> v = Some (S, U) \<Longrightarrow> tvars U \<subseteq> tvars_env \<theta>"
  by (auto simp: tvars_env_def)

lemma tvars_env_textends: "textends \<theta> \<theta>' \<Longrightarrow> tvars_env \<theta> \<subseteq> tvars_env \<theta>'"
  unfolding tvars_env_def textends_def by blast

lemma tvars_env_update:
  assumes "vt_lookup \<theta> v = None"
  shows "tvars_env (vt_update (v, (S, U)) \<theta>) = insert (v, S) (tvars U \<union> tvars_env \<theta>)"
proof -
  have eq: "vt_lookup (vt_update (v, (S, U)) \<theta>) w = Some x \<longleftrightarrow> (w = v \<and> x = (S, U)) \<or> vt_lookup \<theta> w = Some x"
    for w x using assms by auto
  show ?thesis unfolding tvars_env_def eq by auto
qed

lemma tinv_tacyc: "tinv ar n \<theta> A \<Longrightarrow> tacyc \<theta>"
  by (simp add: tinv_def)

lemma tinv_tcons: "tinv ar n \<theta> A \<Longrightarrow> tvars T \<subseteq> tvars_env \<theta> \<union> A \<Longrightarrow> tcons \<theta> T"
  unfolding tinv_def scons_def tcons_def by (blast dest: tvars_envI)

lemma tinv_tcons_env: "tinv ar n \<theta> A \<Longrightarrow> tcons_env \<theta>"
  unfolding tcons_env_def by (blast intro: tinv_tcons dest: tvars_envI2)

lemma tinv_wft: "tinv ar n \<theta> A \<Longrightarrow> vt_lookup \<theta> v = Some (S, U) \<Longrightarrow> wft ar U"
  by (simp add: tinv_def)

lemma tinv_idx: "tinv ar n \<theta> A \<Longrightarrow> p \<in> tvars_env \<theta> \<union> A \<Longrightarrow> snd (fst p) \<le> n"
  by (simp add: tinv_def)

lemma tinv_fresh:
  assumes "tinv ar n \<theta> A" "n < snd v"
  shows "vt_lookup \<theta> v = None"
proof (rule ccontr)
  assume "vt_lookup \<theta> v \<noteq> None"
  then obtain S U where "vt_lookup \<theta> v = Some (S, U)" by auto
  then have "snd v \<le> n" using tinv_idx[OF assms(1), of "(v, S)"] tvars_envI by simp
  with assms(2) show False by simp
qed

lemma tinv_mono: "tinv ar n \<theta> A \<Longrightarrow> n \<le> n' \<Longrightarrow> tinv ar n' \<theta> A"
  unfolding tinv_def by force

lemma tvars_tnorm:
  assumes ac: "tacyc \<theta>"
  shows "tvars (tnorm \<theta> T) \<subseteq> tvars T \<union> tvars_env \<theta>"
proof -
  have var: "tvars (tnorm \<theta> (TVar v S)) \<subseteq> insert (v, S) (tvars_env \<theta>)" for v S
  proof (induction v arbitrary: S rule: tdep_induct[OF ac])
    case (1 v)
    show ?case
    proof (cases "vt_lookup \<theta> v")
      case (Some b)
      obtain S0 U where b: "b = (S0, U)" by force
      have "tvars (tnorm \<theta> U) = (\<Union>(w, S')\<in>tvars U. tvars (tnorm \<theta> (TVar w S')))"
        by (subst tnorm_tsubst) (simp add: tvars_tsubst)
      also have "\<dots> \<subseteq> tvars_env \<theta>"
        using "1.IH" tvars_envI2[of \<theta> v S0 U] Some b by (fastforce simp: tdep_def)
      finally show ?thesis using Some b by (auto simp: tnorm_TVar[OF ac])
    qed (simp add: tnorm_TVar[OF ac])
  qed
  show ?thesis by (subst tnorm_tsubst) (use var in \<open>fastforce simp: tvars_tsubst\<close>)
qed

lemma wft_tnorm:
  assumes ac: "tacyc \<theta>" and wf: "\<And>v S U. vt_lookup \<theta> v = Some (S, U) \<Longrightarrow> wft ar U"
    and "wft ar T"
  shows "wft ar (tnorm \<theta> T)"
proof -
  have var: "wft ar (tnorm \<theta> (TVar v S))" for v S
  proof (induction v arbitrary: S rule: tdep_induct[OF ac])
    case (1 v)
    show ?case
    proof (cases "vt_lookup \<theta> v")
      case (Some b)
      obtain S0 U where b: "b = (S0, U)" by force
      have "wft ar (tnorm \<theta> (TVar w S'))" if "(w, S') \<in> tvars U" for w S'
      proof (rule "1.IH")
        show "(w, v) \<in> tdep \<theta>" using that Some b by (force simp: tdep_def)
      qed
      then have "wft ar (tsubst (\<lambda>w S'. tnorm \<theta> (TVar w S')) U)"
        using wf[of v S0 U] Some b by (intro wft_tsubst) auto
      then have "wft ar (tnorm \<theta> U)" unfolding tnorm_tsubst[of \<theta> U] .
      then show ?thesis using Some b by (simp add: tnorm_TVar[OF ac])
    qed (simp add: tnorm_TVar[OF ac])
  qed
  show ?thesis by (subst tnorm_tsubst) (use var assms(3) in \<open>auto intro: wft_tsubst\<close>)
qed

lemma tinv_update:
  assumes inv: "tinv ar n \<theta> A" and v: "vt_lookup \<theta> v = None" "v \<notin> uvars \<theta> U" "(v, S) \<in> tvars_env \<theta> \<union> A"
    and U: "wft ar U" "tvars U \<subseteq> tvars_env \<theta> \<union> A"
  shows "tinv ar n (vt_update (v, (S, U)) \<theta>) A"
proof -
  have "tvars_env (vt_update (v, (S, U)) \<theta>) \<union> A = tvars_env \<theta> \<union> A"
    using v U by (auto simp: tvars_env_update)
  then show ?thesis using inv v U tacyc_update[OF tinv_tacyc[OF inv] v(1,2)] by (auto simp: tinv_def)
qed

lemma tinv_update_fresh:
  assumes inv: "tinv ar n \<theta> A" and v: "vt_lookup \<theta> v = None" "(v, S) \<in> tvars_env \<theta> \<union> A"
  shows "tinv ar (n + 1) (vt_update (v, (S, TVar (a, n + 1) S')) \<theta>) A"
proof -
  have ac: "tacyc \<theta>" by (rule tinv_tacyc[OF inv])
  have fresh: "vt_lookup \<theta> (a, n + 1) = None" by (rule tinv_fresh[OF inv]) simp
  have "snd v \<le> n" using tinv_idx[OF inv v(2)] by simp
  then have "v \<notin> uvars \<theta> (TVar (a, n + 1) S')" using fresh by (auto simp: uvars_TVar[OF ac])
  then have ac': "tacyc (vt_update (v, (S, TVar (a, n + 1) S')) \<theta>)" by (rule tacyc_update[OF ac v(1)])
  have idx: "p \<in> tvars_env \<theta> \<union> A \<Longrightarrow> snd (fst p) \<le> n" for p by (rule tinv_idx[OF inv])
  have eq: "tvars_env (vt_update (v, (S, TVar (a, n + 1) S')) \<theta>) \<union> A =
      insert ((a, n + 1), S') (tvars_env \<theta> \<union> A)"
    using v by (auto simp: tvars_env_update)
  have sc: "scons (insert ((a, n + 1), S') (tvars_env \<theta> \<union> A))"
    using inv idx[of "((a, n + 1), _)"] unfolding tinv_def scons_def by fastforce
  have wf: "vt_lookup (vt_update (v, (S, TVar (a, n + 1) S')) \<theta>) w = Some (S0, U0) \<Longrightarrow> wft ar U0"
    for w S0 U0 using tinv_wft[OF inv, of w S0 U0] by (auto split: if_splits)
  have "\<forall>p\<in>insert ((a, n + 1), S') (tvars_env \<theta> \<union> A). snd (fst p) \<le> n + 1"
    using idx by force
  with ac' sc wf show ?thesis unfolding tinv_def eq by blast
qed


subsection \<open>Sortedness of bindings\<close>

definition bsorted :: "algebra \<Rightarrow> tyenv \<Rightarrow> indexname \<Rightarrow> bool" where
  "bsorted alg \<theta> v \<longleftrightarrow> (\<forall>S U. vt_lookup \<theta> v = Some (S, U) \<longrightarrow> has_sort alg (tnorm \<theta> U) S)"

context wf_algebra
begin

lemma has_sort_TVar_refl[simp]: "has_sort alg (TVar v S) S"
  by simp (use class_le_refl in blast)

lemma has_sort_textends:
  assumes ac: "tacyc \<theta>'" and ext: "textends \<theta> \<theta>'" and tc: "tcons \<theta>' (tnorm \<theta> T)"
    and new: "\<And>w. vt_lookup \<theta> w = None \<Longrightarrow> bsorted alg \<theta>' w"
    and hs: "has_sort alg (tnorm \<theta> T) S"
  shows "has_sort alg (tnorm \<theta>' T) S"
proof -
  have ac0: "tacyc \<theta>" by (rule tacyc_textends[OF ext ac])
  have "has_sort alg (tsubst (\<lambda>w S. tnorm \<theta>' (TVar w S)) (tnorm \<theta> T)) S"
  proof (rule has_sort_tsubst[OF hs], intro ballI, clarify)
    fix w S' assume w: "(w, S') \<in> tvars (tnorm \<theta> T)"
    show "has_sort alg (tnorm \<theta>' (TVar w S')) S'"
    proof (cases "vt_lookup \<theta>' w")
      case (Some b)
      obtain S'' U where b: "b = (S'', U)" by force
      with Some w tc have "S'' = S'" by (auto simp: tcons_def)
      with Some b new[OF tnorm_unbound[OF ac0 w]] show ?thesis
        by (simp add: bsorted_def tnorm_TVar[OF ac])
    qed (simp add: tnorm_TVar[OF ac], use class_le_refl in blast)
  qed
  then show ?thesis by (subst tnorm_textends[OF ac ext, symmetric], subst tnorm_tsubst, assumption)
qed

lemma bsorted_textends:
  assumes inv: "tinv ar n \<theta>' A" and ext: "textends \<theta> \<theta>'"
    and new: "\<And>w. vt_lookup \<theta> w = None \<Longrightarrow> bsorted alg \<theta>' w"
    and b: "bsorted alg \<theta> v"
  shows "bsorted alg \<theta>' v"
  unfolding bsorted_def
proof (intro allI impI)
  fix S U assume v': "vt_lookup \<theta>' v = Some (S, U)"
  show "has_sort alg (tnorm \<theta>' U) S"
  proof (cases "vt_lookup \<theta> v")
    case None
    with new v' show ?thesis by (simp add: bsorted_def)
  next
    case (Some x)
    with ext v' have v: "vt_lookup \<theta> v = Some (S, U)" by (simp add: textends_def)
    have "tvars (tnorm \<theta> U) \<subseteq> tvars_env \<theta>'"
      using tvars_tnorm[OF tacyc_textends[OF ext tinv_tacyc[OF inv]], of U] tvars_envI2[OF v]
        tvars_env_textends[OF ext] by blast
    then have "tcons \<theta>' (tnorm \<theta> U)" by (intro tinv_tcons[OF inv]) blast
    moreover have "has_sort alg (tnorm \<theta> U) S" using b v by (simp add: bsorted_def)
    ultimately show ?thesis using has_sort_textends[OF tinv_tacyc[OF inv] ext] new by blast
  qed
qed

end


subsection \<open>Steps\<close>

text \<open>
  A step from \<open>(\<theta>, n)\<close> to \<open>(\<theta>', n')\<close> extends the environment, preserves the invariant, adds only
  sorted bindings, and is complete for the instantiations satisfying \<open>P\<close>: they extend to
  well-sorted solutions of \<open>\<theta>'\<close> that agree on the old type variables.
\<close>

definition tstep :: "algebra \<Rightarrow> (name \<Rightarrow> nat) \<Rightarrow> (indexname \<times> psort) set \<Rightarrow> (tinst \<Rightarrow> bool) \<Rightarrow>
    tyenv \<Rightarrow> integer \<Rightarrow> tyenv \<Rightarrow> integer \<Rightarrow> bool" where
  "tstep alg ar A P \<theta> n \<theta>' n' \<longleftrightarrow> textends \<theta> \<theta>' \<and> n \<le> n' \<and> tinv ar n' \<theta>' A \<and>
     (\<forall>w. vt_lookup \<theta> w = None \<longrightarrow> bsorted alg \<theta>' w) \<and>
     (\<forall>\<rho>. wsinst alg \<rho> \<longrightarrow> tsol \<theta> \<rho> \<longrightarrow> P \<rho> \<longrightarrow> (\<exists>\<rho>'. wsinst alg \<rho>' \<and> tsol \<theta>' \<rho>' \<and> tagree n \<rho> \<rho>')) \<and>
     (tcert alg (tvars_env \<theta> \<union> A) \<longrightarrow> tcert alg (tvars_env \<theta>'))"

lemma tstepD:
  assumes "tstep alg ar A P \<theta> n \<theta>' n'"
  shows "textends \<theta> \<theta>'" "n \<le> n'" "tinv ar n' \<theta>' A" "\<And>w. vt_lookup \<theta> w = None \<Longrightarrow> bsorted alg \<theta>' w"
    "\<And>\<rho>. wsinst alg \<rho> \<Longrightarrow> tsol \<theta> \<rho> \<Longrightarrow> P \<rho> \<Longrightarrow> \<exists>\<rho>'. wsinst alg \<rho>' \<and> tsol \<theta>' \<rho>' \<and> tagree n \<rho> \<rho>'"
    "tcert alg (tvars_env \<theta> \<union> A) \<Longrightarrow> tcert alg (tvars_env \<theta>')"
  using assms by (simp_all add: tstep_def)

lemma tstep_refl: "tinv ar n \<theta> A \<Longrightarrow> tstep alg ar A P \<theta> n \<theta> n"
  by (auto simp: tstep_def bsorted_def)

lemma tstep_mono:
  "tstep alg ar A P \<theta> n \<theta>' n' \<Longrightarrow> (\<And>\<rho>. tsol \<theta> \<rho> \<Longrightarrow> Q \<rho> \<Longrightarrow> P \<rho>) \<Longrightarrow> tstep alg ar A Q \<theta> n \<theta>' n'"
  by (simp add: tstep_def)

lemma (in wf_algebra) tstep_trans:
  assumes s1: "tstep alg ar A P \<theta>1 n1 \<theta>2 n2" and s2: "tstep alg ar A Q \<theta>2 n2 \<theta>3 n3"
    and PQ: "\<And>\<rho> \<rho>'. P \<rho> \<Longrightarrow> tagree n1 \<rho> \<rho>' \<Longrightarrow> Q \<rho>'"
  shows "tstep alg ar A P \<theta>1 n1 \<theta>3 n3"
  unfolding tstep_def
proof (intro conjI allI impI)
  show ext: "textends \<theta>1 \<theta>3" by (rule textends_trans[OF tstepD(1)[OF s1] tstepD(1)[OF s2]])
  show "n1 \<le> n3" using tstepD(2)[OF s1] tstepD(2)[OF s2] by simp
  show inv: "tinv ar n3 \<theta>3 A" by (rule tstepD(3)[OF s2])
  fix w assume w: "vt_lookup \<theta>1 w = None"
  show "bsorted alg \<theta>3 w"
  proof (cases "vt_lookup \<theta>2 w")
    case None
    then show ?thesis by (rule tstepD(4)[OF s2])
  next
    case (Some x)
    show ?thesis
      by (rule bsorted_textends[OF inv tstepD(1)[OF s2] tstepD(4)[OF s2] tstepD(4)[OF s1 w]])
  qed
next
  fix \<rho> assume \<rho>: "wsinst alg \<rho>" "tsol \<theta>1 \<rho>" "P \<rho>"
  then obtain \<rho>' where \<rho>': "wsinst alg \<rho>'" "tsol \<theta>2 \<rho>'" "tagree n1 \<rho> \<rho>'" using tstepD(5)[OF s1] by blast
  then obtain \<rho>'' where "wsinst alg \<rho>''" "tsol \<theta>3 \<rho>''" "tagree n2 \<rho>' \<rho>''"
    using tstepD(5)[OF s2] PQ[OF \<rho>(3)] by blast
  then show "\<exists>\<rho>'. wsinst alg \<rho>' \<and> tsol \<theta>3 \<rho>' \<and> tagree n1 \<rho> \<rho>'"
    using \<rho>'(3) tagree_trans tstepD(2)[OF s1] by blast
next
  assume "tcert alg (tvars_env \<theta>1 \<union> A)"
  then have "tcert alg (tvars_env \<theta>2 \<union> A)" using tstepD(6)[OF s1] by simp
  then show "tcert alg (tvars_env \<theta>3)" by (rule tstepD(6)[OF s2])
qed


subsection \<open>Dereferencing\<close>

lemma devar_preserves:
  assumes ac: "tacyc \<theta>" and tc: "tcons_env \<theta>"
    and P: "\<And>v S U. vt_lookup \<theta> v = Some (S, U) \<Longrightarrow> P U"
  shows "tcons \<theta> T \<Longrightarrow> devar \<theta> T = return U \<Longrightarrow> P T \<Longrightarrow> P U"
proof (induction arbitrary: U rule: tnorm_induct[OF ac tc, consumes 1, case_names TFree Type Unbound Bound])
  case (Bound v S U' U)
  then show ?case using P[OF Bound(1)]
    by (subst (asm) devar.simps) (simp add: type_lookup_ok)
qed (subst (asm) devar.simps, simp add: type_lookup_ok bindM_def return_def)+

lemma tinv_devar:
  assumes inv: "tinv ar n \<theta> A" and T: "tvars T \<subseteq> tvars_env \<theta> \<union> A" "wft ar T"
  obtains U where "devar \<theta> T = return U" "tnorm \<theta> U = tnorm \<theta> T" "\<not> tbound \<theta> U"
    "tvars U \<subseteq> tvars_env \<theta> \<union> A" "wft ar U"
proof -
  obtain U where U: "devar \<theta> T = return U" "tnorm \<theta> U = tnorm \<theta> T" "\<not> tbound \<theta> U"
    using devar_ok[OF tinv_tacyc[OF inv] tinv_tcons_env[OF inv] tinv_tcons[OF inv T(1)]] by blast
  have "tvars U \<subseteq> tvars_env \<theta> \<union> A \<and> wft ar U"
    by (rule devar_preserves[OF tinv_tacyc[OF inv] tinv_tcons_env[OF inv] _ tinv_tcons[OF inv T(1)] U(1)])
      (use T inv in \<open>auto dest: tvars_envI2 tinv_wft\<close>)
  with U that show ?thesis by blast
qed


lemma tinst_fresh:
  fixes a :: name
  assumes inv: "tinv ar n \<theta> A" and \<rho>: "wsinst alg \<rho>" "tsol \<theta> \<rho>" and t: "has_sort alg t S0"
  defines "\<rho>' \<equiv> \<lambda>v S. if v = (a, n + 1) \<and> S = S0 then t else \<rho> v S"
  shows "wsinst alg \<rho>'" "tagree n \<rho> \<rho>'" "tsol \<theta> \<rho>'"
proof -
  show "wsinst alg \<rho>'" using \<rho>(1) t by (simp add: wsinst_def \<rho>'_def)
  show ag: "tagree n \<rho> \<rho>'" by (auto simp: tagree_def \<rho>'_def)
  show "tsol \<theta> \<rho>'" unfolding tsol_def
  proof (intro allI impI)
    fix v S U assume v: "vt_lookup \<theta> v = Some (S, U)"
    have "snd v \<le> n" using tinv_idx[OF inv, of "(v, S)"] tvars_envI[OF v] by simp
    then have "\<rho>' v S = \<rho> v S" by (auto simp: \<rho>'_def)
    also have "\<dots> = tsubst \<rho> U" using \<rho>(2) v by (simp add: tsol_def)
    also have "\<dots> = tsubst \<rho>' U"
      by (rule tagree_tsubst[OF ag, symmetric]) (use tinv_idx[OF inv] tvars_envI2[OF v] in blast)
    finally show "\<rho>' v S = tsubst \<rho>' U" .
  qed
qed

lemma ball_set_zip:
  "length xs = length ys \<Longrightarrow> (\<forall>p\<in>set (zip xs ys). Q p) \<longleftrightarrow> (\<forall>i<length xs. Q (xs ! i, ys ! i))"
  and bex_set_zip:
  "length xs = length ys \<Longrightarrow> (\<exists>p\<in>set (zip xs ys). Q p) \<longleftrightarrow> (\<exists>i<length xs. Q (xs ! i, ys ! i))"
  by (auto simp: set_zip)



subsection \<open>Correctness of \<^const>\<open>meet\<close>\<close>

context wf_algebra
begin

lemma has_sort_TVar_iff: "has_sort alg (TVar v S') S \<longleftrightarrow> sort_le alg S' S"
  and has_sort_TFree_iff: "has_sort alg (TFree a S') S \<longleftrightarrow> sort_le alg S' S"
  by (simp_all add: sort_le_iff)

text \<open>
  \<^const>\<open>meet\<close> constrains a type to a sort. It only renames type variables to new ones with
  smaller sorts, and it fails with \<open>TUnify\<close> only if no well-sorted solution gives the type the sort.
\<close>

lemma meet_ok:
  assumes "tinv ar n \<theta> A" "tvars T \<subseteq> tvars_env \<theta> \<union> A" "wft ar T" "\<not> tbound \<theta> T"
    "tcert alg (tvars_env \<theta> \<union> A) \<longrightarrow> sort_ok alg S"
  shows "(\<exists>\<theta>' n'. meet alg T S (\<theta>, n) = return (\<theta>', n') \<and>
      tstep alg ar A (\<lambda>\<rho>. has_sort alg (tsubst \<rho> T) S) \<theta> n \<theta>' n' \<and> renames \<theta> \<theta>' \<and>
      has_sort alg (tnorm \<theta>' T) S) \<or>
    (meet alg T S (\<theta>, n) = raise TUnify \<and>
      (\<forall>\<rho>. wsinst alg \<rho> \<longrightarrow> tsol \<theta> \<rho> \<longrightarrow> \<not> has_sort alg (tsubst \<rho> T) S))"
  using assms
proof (induction "size (tnorm \<theta> T)" arbitrary: \<theta> n T S rule: less_induct)
  case less
  note inv = less.prems(1)
  have ac: "tacyc \<theta>" by (rule tinv_tacyc[OF inv])
  show ?case
  proof (cases "S = []")
    case True
    then show ?thesis by (subst meet.simps) (simp add: tstep_refl[OF inv] ac)
  next
    case S: False
    show ?thesis
    proof (cases T)
      case (TVar xi S')
      with less.prems(4) have xi: "vt_lookup \<theta> xi = None" by simp
      have tn: "tnorm \<theta> T = T" using xi TVar by (simp add: tnorm_TVar[OF ac])
      show ?thesis
      proof (cases "sort_le alg S' S")
        case True
        then show ?thesis using TVar S tn
          by (subst meet.simps) (simp add: tstep_refl[OF inv] ac has_sort_TVar_iff del: has_sort.simps)
      next
        case False
        define V where "V = TVar (aT, n + 1) (inter_sort alg S' S)"
        define \<theta>' where "\<theta>' = vt_update (xi, (S', V)) \<theta>"
        have xiA: "(xi, S') \<in> tvars_env \<theta> \<union> A" using less.prems(2) TVar by simp
        have xin: "snd xi \<le> n" using tinv_idx[OF inv xiA] by simp
        have inv': "tinv ar (n + 1) \<theta>' A" unfolding \<theta>'_def V_def by (rule tinv_update_fresh[OF inv xi xiA])
        have ac': "tacyc \<theta>'" by (rule tinv_tacyc[OF inv'])
        have fresh: "vt_lookup \<theta>' (aT, n + 1) = None"
          using tinv_fresh[OF inv, of "(aT, n + 1)"] xin by (auto simp: \<theta>'_def)
        have tnV: "tnorm \<theta>' V = V" by (simp add: V_def tnorm_TVar[OF ac'] fresh)
        have lk: "vt_lookup \<theta>' xi = Some (S', V)" "w \<noteq> xi \<Longrightarrow> vt_lookup \<theta>' w = vt_lookup \<theta> w" for w
          by (simp_all add: \<theta>'_def)
        have tnT: "tnorm \<theta>' T = V" using TVar tnV by (simp add: tnorm_TVar[OF ac'] lk)
        have ext: "textends \<theta> \<theta>'" by (simp add: \<theta>'_def textends_update xi)
        have ren: "renames \<theta> \<theta>'"
          unfolding renames_def
        proof (intro allI impI)
          fix w S0 assume "vt_lookup \<theta> w = None"
          then show "\<exists>u S'. tnorm \<theta>' (TVar w S0) = TVar u S'"
            using tnV by (cases "w = xi") (auto simp: tnorm_TVar[OF ac'] lk V_def)
        qed
        have hsV: "has_sort alg V S'" "has_sort alg V S"
          using inter_sort_sem[of V S' S] by (simp_all add: V_def del: has_sort.simps)
        have bs: "bsorted alg \<theta>' w" if "vt_lookup \<theta> w = None" for w
          using that hsV tnV by (auto simp: bsorted_def \<theta>'_def)
        have ce: "tcert alg (tvars_env \<theta>')" if c: "tcert alg (tvars_env \<theta> \<union> A)"
        proof -
          have "sort_ok alg S'" by (rule tcertD[OF c xiA])
          moreover have "sort_ok alg S" using less.prems(5) c by blast
          ultimately show ?thesis using c
            by (simp add: \<theta>'_def tvars_env_update[OF xi] V_def sort_ok_inter_sort)
        qed
        have compl: "\<exists>\<rho>'. wsinst alg \<rho>' \<and> tsol \<theta>' \<rho>' \<and> tagree n \<rho> \<rho>'"
          if \<rho>: "wsinst alg \<rho>" "tsol \<theta> \<rho>" "has_sort alg (tsubst \<rho> T) S" for \<rho>
        proof -
          let ?t = "\<rho> xi S'"
          have "has_sort alg ?t (inter_sort alg S' S)"
            using \<rho> TVar by (simp add: inter_sort_sem wsinst_def)
          note fr = tinst_fresh[OF inv \<rho>(1,2) this, of aT]
          let ?\<rho>' = "\<lambda>v S0. if v = (aT, n + 1) \<and> S0 = inter_sort alg S' S then ?t else \<rho> v S0"
          have "tsol \<theta>' ?\<rho>'" unfolding \<theta>'_def
            by (rule tsol_update[OF fr(3)]) (use xin in \<open>auto simp: V_def\<close>)
          then show ?thesis using fr(1,2) by blast
        qed
        have "meet alg T S (\<theta>, n) = return (\<theta>', n + 1)"
          using TVar S False xi
          by (subst meet.simps) (simp add: gen_tyvar_def update_new_def vt_defined_lookup \<theta>'_def V_def)
        moreover have "tstep alg ar A (\<lambda>\<rho>. has_sort alg (tsubst \<rho> T) S) \<theta> n \<theta>' (n + 1)"
          using ext inv' bs compl ce by (simp add: tstep_def)
        ultimately show ?thesis using ren tnT hsV by auto
      qed
    next
      case (TFree a S')
      have "meet alg T S (\<theta>, n) = (if sort_le alg S' S then return (\<theta>, n) else raise TUnify)"
        using TFree S by (subst meet.simps) simp
      then show ?thesis using TFree
        by (simp add: tstep_refl[OF inv] ac has_sort_TFree_iff del: has_sort.simps)
    next
      case (Type a Ts)
      have wT: "length Ts = tarity ar a" "\<forall>Ti\<in>set Ts. wft ar Ti" using less.prems(3) Type by simp_all
      show ?thesis
      proof (cases "\<forall>c\<in>set S. map_of (arities alg a) c \<noteq> None")
        case False
        then obtain c where c: "c \<in> set S" "map_of (arities alg a) c = None" by auto
        obtain ce where md: "mg_domain alg a S = raise (Class_Error ce)" using mg_domain_error[OF S c] by blast
        have "meet alg T S (\<theta>, n) = raise TUnify"
          using Type S by (subst meet.simps) (simp add: mg_domain_unif_def md)
        moreover have "\<not> has_sort alg (tsubst \<rho> T) S" for \<rho> using c Type by force
        ultimately show ?thesis by blast
      next
        case True
        obtain Ds where Ds: "mg_domain alg a S = return Ds" "length Ds = tarity ar a"
          and char: "\<And>i U. i < tarity ar a \<Longrightarrow> has_sort alg U (Ds ! i) \<longleftrightarrow>
            (\<forall>c\<in>set S. \<forall>Ss. map_of (arities alg a) c = Some Ss \<longrightarrow> has_sort alg U (Ss ! i))"
          using mg_domain_ok[OF S True] by blast
        have zl: "length Ts = length Ds" using wT Ds by simp
        have hsT: "has_sort alg (Type a Us) S \<longleftrightarrow> (\<forall>i<length Us. has_sort alg (Us ! i) (Ds ! i))"
          if len: "length Us = tarity ar a" for Us
        proof
          assume "has_sort alg (Type a Us) S"
          then show "\<forall>i<length Us. has_sort alg (Us ! i) (Ds ! i)"
            using len char by (auto simp: has_sort_Type[OF len] simp del: has_sort.simps)
        next
          assume hs: "\<forall>i<length Us. has_sort alg (Us ! i) (Ds ! i)"
          show "has_sort alg (Type a Us) S" unfolding has_sort_Type[OF len]
          proof
            fix c assume c: "c \<in> set S"
            then obtain Ss where "map_of (arities alg a) c = Some Ss" using True by auto
            with c hs len char show "\<exists>Ss. map_of (arities alg a) c = Some Ss \<and>
                (\<forall>i<length Us. has_sort alg (Us ! i) (Ss ! i))" by auto
          qed
        qed
        define f where "f = (\<lambda>(T, S) st. do {T' \<leftarrow> devar (fst st) T; meet alg T' S st})"
        have meq: "meet alg T S (\<theta>, n) = foldM f (zip Ts Ds) (\<theta>, n)"
          using Type S by (subst meet.simps) (simp add: mg_domain_unif_def Ds f_def)
        have fold: "(\<exists>\<theta>2 n2. foldM f ps (\<theta>1, n1) = return (\<theta>2, n2) \<and>
            tstep alg ar A (\<lambda>\<rho>. \<forall>q\<in>set ps. has_sort alg (tsubst \<rho> (fst q)) (snd q)) \<theta>1 n1 \<theta>2 n2 \<and>
            renames \<theta>1 \<theta>2 \<and> (\<forall>q\<in>set ps. has_sort alg (tnorm \<theta>2 (fst q)) (snd q))) \<or>
          (foldM f ps (\<theta>1, n1) = raise TUnify \<and>
            (\<forall>\<rho>. wsinst alg \<rho> \<longrightarrow> tsol \<theta>1 \<rho> \<longrightarrow> \<not> (\<forall>q\<in>set ps. has_sort alg (tsubst \<rho> (fst q)) (snd q))))"
          if "set ps \<subseteq> set (zip Ts Ds)" "tinv ar n1 \<theta>1 A" "textends \<theta> \<theta>1" "renames \<theta> \<theta>1" "n \<le> n1"
          for ps \<theta>1 n1
          using that
        proof (induction ps arbitrary: \<theta>1 n1)
          case Nil
          then show ?case by (simp add: tstep_refl tinv_tacyc)
        next
          case (Cons p ps \<theta>1 n1)
          obtain Ti Di where p: "p = (Ti, Di)" by force
          have Ti: "Ti \<in> set Ts" using Cons.prems(1) p by (auto dest: set_zip_leftD)
          have inv1: "tinv ar n1 \<theta>1 A" by (rule Cons.prems(2))
          have ac1: "tacyc \<theta>1" by (rule tinv_tacyc[OF inv1])
          have tvA: "tvars (fst q) \<subseteq> tvars_env \<theta>1 \<union> A" if "q \<in> set (zip Ts Ds)" for q
            using less.prems(2) Type tvars_env_textends[OF Cons.prems(3)] set_zip_leftD[of "fst q" "snd q"] that
            by fastforce
          have TiA: "tvars Ti \<subseteq> tvars_env \<theta>1 \<union> A" using tvA[of p] Cons.prems(1) p by simp
          obtain Ti' where Ti': "devar \<theta>1 Ti = return Ti'" "tnorm \<theta>1 Ti' = tnorm \<theta>1 Ti" "\<not> tbound \<theta>1 Ti'"
            "tvars Ti' \<subseteq> tvars_env \<theta>1 \<union> A" "wft ar Ti'"
            using tinv_devar[OF inv1 TiA] wT(2) Ti by blast
          have "size (tnorm \<theta>1 Ti') = size (tnorm \<theta> Ti)"
            using Ti'(2) renames_size[OF ac1 Cons.prems(3,4)] by simp
          also have "size (tnorm \<theta> Ti) \<le> size_list size (map (tnorm \<theta>) Ts)"
            using Ti by (intro size_list_estimation'[of "tnorm \<theta> Ti"]) auto
          then have "size (tnorm \<theta> Ti) < size (tnorm \<theta> T)" by (simp add: Type)
          finally have sz: "size (tnorm \<theta>1 Ti') < size (tnorm \<theta> T)" .
          have fstep: "foldM f (p # ps) (\<theta>1, n1) = bindM (meet alg Ti' Di (\<theta>1, n1)) (foldM f ps)"
            using Ti'(1) by (simp add: p f_def)
          have sub: "tsubst \<rho> Ti' = tsubst \<rho> Ti" if "tsol \<theta>1 \<rho>" for \<rho>
            using tsubst_tnorm[OF ac1 tinv_tcons_env[OF inv1] that tinv_tcons[OF inv1 Ti'(4)]]
              tsubst_tnorm[OF ac1 tinv_tcons_env[OF inv1] that tinv_tcons[OF inv1 TiA]] Ti'(2) by simp
          have agr: "tsubst \<rho>' (fst q) = tsubst \<rho> (fst q)" if "q \<in> set ps" "tagree n1 \<rho> \<rho>'" for q \<rho> \<rho>'
            by (rule tagree_tsubst[OF that(2)])
              (use tvA[of q] that(1) Cons.prems(1) tinv_idx[OF inv1] in auto)
          have "Di \<in> set Ds" using Cons.prems(1) p by (auto dest: set_zip_rightD)
          then have Di: "sort_ok alg Di" by (rule mg_domain_sorts_ok[OF Ds(1)])
          have Di': "tcert alg (tvars_env \<theta>1 \<union> A) \<longrightarrow> sort_ok alg Di" using Di by blast
          from less.hyps[OF sz inv1 Ti'(4,5,3) Di'] show ?case
          proof (elim disjE exE conjE)
            fix \<theta>2 n2 assume m: "meet alg Ti' Di (\<theta>1, n1) = return (\<theta>2, n2)"
              and s1: "tstep alg ar A (\<lambda>\<rho>. has_sort alg (tsubst \<rho> Ti') Di) \<theta>1 n1 \<theta>2 n2"
              and r1: "renames \<theta>1 \<theta>2" and h1: "has_sort alg (tnorm \<theta>2 Ti') Di"
            have inv2: "tinv ar n2 \<theta>2 A" by (rule tstepD(3)[OF s1])
            have ac2: "tacyc \<theta>2" by (rule tinv_tacyc[OF inv2])
            have ext2: "textends \<theta> \<theta>2" by (rule textends_trans[OF Cons.prems(3) tstepD(1)[OF s1]])
            have ren2: "renames \<theta> \<theta>2" by (rule renames_trans[OF ac2 tstepD(1)[OF s1] Cons.prems(3,4) r1])
            have n2: "n \<le> n2" using Cons.prems(5) tstepD(2)[OF s1] by simp
            have pss: "set ps \<subseteq> set (zip Ts Ds)" using Cons.prems(1) by simp
            from Cons.IH[OF pss inv2 ext2 ren2 n2] show ?case
            proof (elim disjE exE conjE)
              fix \<theta>3 n3 assume m2: "foldM f ps (\<theta>2, n2) = return (\<theta>3, n3)"
                and s2: "tstep alg ar A (\<lambda>\<rho>. \<forall>q\<in>set ps. has_sort alg (tsubst \<rho> (fst q)) (snd q)) \<theta>2 n2 \<theta>3 n3"
                and r2: "renames \<theta>2 \<theta>3" and h2: "\<forall>q\<in>set ps. has_sort alg (tnorm \<theta>3 (fst q)) (snd q)"
              have inv3: "tinv ar n3 \<theta>3 A" by (rule tstepD(3)[OF s2])
              have ac3: "tacyc \<theta>3" by (rule tinv_tacyc[OF inv3])
              have s: "tstep alg ar A (\<lambda>\<rho>. \<forall>q\<in>set (p # ps). has_sort alg (tsubst \<rho> (fst q)) (snd q)) \<theta>1 n1 \<theta>3 n3"
                by (rule tstep_trans[OF tstep_mono[OF s1] s2]) (auto simp: p sub agr)
              have "tnorm \<theta>2 Ti = tnorm \<theta>2 Ti'"
                using tnorm_textends[OF ac2 tstepD(1)[OF s1], of Ti] tnorm_textends[OF ac2 tstepD(1)[OF s1], of Ti']
                  Ti'(2) by simp
              then have "has_sort alg (tnorm \<theta>2 Ti) Di" using h1 by simp
              moreover have "tcons \<theta>3 (tnorm \<theta>2 Ti)"
                using tvars_tnorm[OF ac2, of Ti] TiA tvars_env_textends[OF tstepD(1)[OF s1]]
                  tvars_env_textends[OF tstepD(1)[OF s2]]
                by (intro tinv_tcons[OF inv3]) blast
              ultimately have "has_sort alg (tnorm \<theta>3 Ti) Di"
                using has_sort_textends[OF ac3 tstepD(1)[OF s2]] tstepD(4)[OF s2] by blast
              then show ?case
                using m m2 fstep s h2 renames_trans[OF ac3 tstepD(1)[OF s2] tstepD(1)[OF s1] r1 r2]
                by (auto simp: p)
            next
              assume m2: "foldM f ps (\<theta>2, n2) = raise TUnify"
                and nf: "\<forall>\<rho>. wsinst alg \<rho> \<longrightarrow> tsol \<theta>2 \<rho> \<longrightarrow> \<not> (\<forall>q\<in>set ps. has_sort alg (tsubst \<rho> (fst q)) (snd q))"
              have "\<not> (\<forall>q\<in>set (p # ps). has_sort alg (tsubst \<rho> (fst q)) (snd q))"
                if \<rho>: "wsinst alg \<rho>" "tsol \<theta>1 \<rho>" for \<rho>
              proof
                assume all: "\<forall>q\<in>set (p # ps). has_sort alg (tsubst \<rho> (fst q)) (snd q)"
                then have "has_sort alg (tsubst \<rho> Ti') Di" using sub[OF \<rho>(2)] by (simp add: p)
                then obtain \<rho>' where \<rho>': "wsinst alg \<rho>'" "tsol \<theta>2 \<rho>'" "tagree n1 \<rho> \<rho>'"
                  using tstepD(5)[OF s1 \<rho>] by blast
                then obtain q where q: "q \<in> set ps" "\<not> has_sort alg (tsubst \<rho>' (fst q)) (snd q)"
                  using nf by blast
                then show False using all agr[OF q(1) \<rho>'(3)] by simp
              qed
              then show ?case using m m2 fstep by simp
            qed
          next
            assume m: "meet alg Ti' Di (\<theta>1, n1) = raise TUnify"
              and nf: "\<forall>\<rho>. wsinst alg \<rho> \<longrightarrow> tsol \<theta>1 \<rho> \<longrightarrow> \<not> has_sort alg (tsubst \<rho> Ti') Di"
            then show ?case using fstep sub by (auto simp: p)
          qed
        qed
        from fold[OF order_refl inv textends_refl renames_refl[OF ac] order_refl] show ?thesis
        proof (elim disjE exE conjE)
          fix \<theta>' n' assume m: "foldM f (zip Ts Ds) (\<theta>, n) = return (\<theta>', n')"
            and s: "tstep alg ar A (\<lambda>\<rho>. \<forall>q\<in>set (zip Ts Ds). has_sort alg (tsubst \<rho> (fst q)) (snd q)) \<theta> n \<theta>' n'"
            and r: "renames \<theta> \<theta>'" and h: "\<forall>q\<in>set (zip Ts Ds). has_sort alg (tnorm \<theta>' (fst q)) (snd q)"
          have "tstep alg ar A (\<lambda>\<rho>. has_sort alg (tsubst \<rho> T) S) \<theta> n \<theta>' n'"
            by (rule tstep_mono[OF s]) (simp add: Type hsT ball_set_zip[OF zl] bex_set_zip[OF zl] wT del: has_sort.simps)
          moreover have "has_sort alg (tnorm \<theta>' T) S"
            using h by (simp add: Type hsT ball_set_zip[OF zl] bex_set_zip[OF zl] wT del: has_sort.simps)
          ultimately show ?thesis using m meq r by auto
        next
          assume m: "foldM f (zip Ts Ds) (\<theta>, n) = raise TUnify"
            and nf: "\<forall>\<rho>. wsinst alg \<rho> \<longrightarrow> tsol \<theta> \<rho> \<longrightarrow>
              \<not> (\<forall>q\<in>set (zip Ts Ds). has_sort alg (tsubst \<rho> (fst q)) (snd q))"
          show ?thesis using meq m nf by (simp add: Type hsT ball_set_zip[OF zl] bex_set_zip[OF zl] wT del: has_sort.simps)
        qed
      qed
    qed
  qed
qed

end



subsection \<open>Correctness of \<^const>\<open>unify_aux\<close>\<close>

text \<open>Bindings decrease the number of unbound variables of a problem.\<close>

lemma uvars_update:
  assumes ac: "tacyc (vt_update (v, (S, U)) \<theta>)" and v: "vt_lookup \<theta> v = None" "v \<notin> uvars \<theta> U"
  shows "uvars (vt_update (v, (S, U)) \<theta>) X = (if v \<in> uvars \<theta> X then uvars \<theta> X - {v} \<union> uvars \<theta> U else uvars \<theta> X)"
proof -
  let ?\<theta>' = "vt_update (v, (S, U)) \<theta>"
  have ext: "textends \<theta> ?\<theta>'" by (rule textends_update[OF v(1)])
  have ac0: "tacyc \<theta>" by (rule tacyc_textends[OF ext ac])
  have g: "(case vt_lookup ?\<theta>' u of None \<Rightarrow> {u} | Some (S', U') \<Rightarrow> uvars ?\<theta>' U') = {u}"
    if "u \<in> uvars \<theta> Y" "u \<noteq> v" for u Y
    using uvars_unbound[OF ac0 that(1)] that(2) by simp
  have "uvars ?\<theta>' U = (\<Union>u\<in>uvars \<theta> U. {u})"
  proof (subst uvars_textends[OF ac ext], rule SUP_cong[OF refl])
    fix u assume "u \<in> uvars \<theta> U"
    with v(2) show "(case vt_lookup ?\<theta>' u of None \<Rightarrow> {u} | Some (S', U') \<Rightarrow> uvars ?\<theta>' U') = {u}"
      by (intro g) auto
  qed
  then have U': "uvars ?\<theta>' U = uvars \<theta> U" by simp
  have "uvars ?\<theta>' X = (\<Union>u\<in>uvars \<theta> X. if u = v then uvars \<theta> U else {u})"
  proof (subst uvars_textends[OF ac ext], rule SUP_cong[OF refl])
    fix u assume "u \<in> uvars \<theta> X"
    then show "(case vt_lookup ?\<theta>' u of None \<Rightarrow> {u} | Some (S', U') \<Rightarrow> uvars ?\<theta>' U') =
        (if u = v then uvars \<theta> U else {u})"
      using g[of u X] U' by (cases "u = v") simp_all
  qed
  then show ?thesis by auto
qed

lemma card_update_less:
  assumes ac: "tacyc (vt_update (v, (S, U)) \<theta>)" and v: "vt_lookup \<theta> v = None" "v \<notin> uvars \<theta> U"
    and X: "v \<in> uvars \<theta> X" "uvars \<theta> U \<subseteq> uvars \<theta> X"
  shows "card (uvars (vt_update (v, (S, U)) \<theta>) X) < card (uvars \<theta> X)"
proof -
  have eq: "uvars (vt_update (v, (S, U)) \<theta>) X = uvars \<theta> X - {v}"
    using uvars_update[OF ac v] X v(2) by auto
  show ?thesis unfolding eq by (rule card_Diff1_less[OF finite_uvars X(1)])
qed

lemma size_tsubst_tvars: "(v, S) \<in> tvars T \<Longrightarrow> size (\<rho> v S) \<le> size (tsubst \<rho> T)"
proof (induction T)
  case (Type a Ts)
  then obtain T where "T \<in> set Ts" "(v, S) \<in> tvars T" by auto
  with Type.IH have "size (\<rho> v S) \<le> size (tsubst \<rho> T)" by blast
  also have "\<dots> \<le> size_list size (map (tsubst \<rho>) Ts)"
    using \<open>T \<in> set Ts\<close> by (intro size_list_estimation'[of "tsubst \<rho> T"]) auto
  finally show ?case by simp
qed auto

lemma size_tsubst_Type: "(v, S) \<in> tvars (Type a Ts) \<Longrightarrow> size (\<rho> v S) < size (tsubst \<rho> (Type a Ts))"
proof -
  assume "(v, S) \<in> tvars (Type a Ts)"
  then obtain T where "T \<in> set Ts" "(v, S) \<in> tvars T" by auto
  have "size (\<rho> v S) \<le> size (tsubst \<rho> T)" by (rule size_tsubst_tvars) fact
  also have "\<dots> \<le> size_list size (map (tsubst \<rho>) Ts)"
    using \<open>T \<in> set Ts\<close> by (intro size_list_estimation'[of "tsubst \<rho> T"]) auto
  finally show ?thesis by simp
qed

context wf_algebra
begin

text \<open>Binding a type variable to a type that is not a variable, followed by \<^const>\<open>meet\<close>.\<close>

lemma bind_meet_ok:
  assumes inv: "tinv ar n \<theta> A" and v: "vt_lookup \<theta> v = None" "(v, S) \<in> tvars_env \<theta> \<union> A"
    and U: "tvars U \<subseteq> tvars_env \<theta> \<union> A" "wft ar U" "\<And>w S'. U \<noteq> TVar w S'"
  defines "r \<equiv> do {b \<leftarrow> type_occurs v \<theta> U;
    if b then raise TUnify else do {\<theta>1 \<leftarrow> update_new (v, (S, U)) \<theta>; meet alg U S (\<theta>1, n)}}"
  shows "(\<exists>\<theta>' n'. r = return (\<theta>', n') \<and> tstep alg ar A (\<lambda>\<rho>. \<rho> v S = tsubst \<rho> U) \<theta> n \<theta>' n' \<and>
      (\<forall>\<rho>. tsol \<theta>' \<rho> \<longrightarrow> \<rho> v S = tsubst \<rho> U) \<and>
      (\<forall>X. v \<in> uvars \<theta> X \<longrightarrow> uvars \<theta> U \<subseteq> uvars \<theta> X \<longrightarrow> card (uvars \<theta>' X) < card (uvars \<theta> X))) \<or>
    (r = raise TUnify \<and> (\<forall>\<rho>. wsinst alg \<rho> \<longrightarrow> tsol \<theta> \<rho> \<longrightarrow> \<rho> v S \<noteq> tsubst \<rho> U))"
proof -
  have ac: "tacyc \<theta>" by (rule tinv_tacyc[OF inv])
  have tcU: "tcons \<theta> U" by (rule tinv_tcons[OF inv U(1)])
  have tc: "tcons_env \<theta>" by (rule tinv_tcons_env[OF inv])
  show ?thesis
  proof (cases "v \<in> uvars \<theta> U")
    case True
    then obtain S' where vS': "(v, S') \<in> tvars (tnorm \<theta> U)" by (auto simp: uvars_def)
    have "S' = S"
      using inv vS' v(2) tvars_tnorm[OF ac, of U] U(1) unfolding tinv_def scons_def by blast
    with vS' have vS: "(v, S) \<in> tvars (tnorm \<theta> U)" by simp
    have "\<rho> v S \<noteq> tsubst \<rho> U" if "tsol \<theta> \<rho>" for \<rho>
    proof (cases U)
      case (Type a Us)
      then have "size (\<rho> v S) < size (tsubst \<rho> (tnorm \<theta> U))"
        using vS size_tsubst_Type[of v S a "map (tnorm \<theta>) Us"] by simp
      then show ?thesis using tsubst_tnorm[OF ac tc that tcU] by auto
    qed (use U(3) vS in auto)
    moreover have "r = raise TUnify"
      using True by (simp add: r_def type_occurs_ok[OF ac tc tcU v(1)] uvars_def)
    ultimately show ?thesis by blast
  next
    case False
    define \<theta>1 where "\<theta>1 = vt_update (v, (S, U)) \<theta>"
    have inv1: "tinv ar n \<theta>1 A" unfolding \<theta>1_def by (rule tinv_update[OF inv v(1) False v(2) U(2,1)])
    have ac1: "tacyc \<theta>1" by (rule tinv_tacyc[OF inv1])
    have ext1: "textends \<theta> \<theta>1" by (simp add: \<theta>1_def textends_update v(1))
    have lk1: "vt_lookup \<theta>1 v = Some (S, U)" by (simp add: \<theta>1_def)
    have U1: "tvars U \<subseteq> tvars_env \<theta>1 \<union> A" using U(1) tvars_env_textends[OF ext1] by blast
    have nb: "\<not> tbound \<theta>1 U" using U(3) by (cases U) auto
    have r: "r = meet alg U S (\<theta>1, n)"
      using False by (simp add: r_def type_occurs_ok[OF ac tc tcU v(1)] uvars_def update_new_def
          vt_defined_lookup v(1) \<theta>1_def)
    have sol1: "tsol \<theta>1 \<rho>" if "tsol \<theta> \<rho>" "\<rho> v S = tsubst \<rho> U" for \<rho>
      unfolding \<theta>1_def by (rule tsol_update[OF that])
    have Sok: "tcert alg (tvars_env \<theta>1 \<union> A) \<longrightarrow> sort_ok alg S"
      using tvars_envI[OF lk1] by (blast intro: tcertD)
    from meet_ok[OF inv1 U1 U(2) nb Sok] show ?thesis
    proof (elim disjE exE conjE)
      fix \<theta>' n' assume m: "meet alg U S (\<theta>1, n) = return (\<theta>', n')"
        and s: "tstep alg ar A (\<lambda>\<rho>. has_sort alg (tsubst \<rho> U) S) \<theta>1 n \<theta>' n'"
        and ren: "renames \<theta>1 \<theta>'" and hs: "has_sort alg (tnorm \<theta>' U) S"
      have ext: "textends \<theta> \<theta>'" by (rule textends_trans[OF ext1 tstepD(1)[OF s]])
      have ac': "tacyc \<theta>'" by (rule tinv_tacyc[OF tstepD(3)[OF s]])
      have bs: "bsorted alg \<theta>' w" if "vt_lookup \<theta> w = None" for w
      proof (cases "w = v")
        case True
        then show ?thesis using lk1 tstepD(1)[OF s] hs by (auto simp: bsorted_def textends_def)
      next
        case False
        then show ?thesis using that tstepD(4)[OF s] by (simp add: \<theta>1_def)
      qed
      have compl: "\<exists>\<rho>'. wsinst alg \<rho>' \<and> tsol \<theta>' \<rho>' \<and> tagree n \<rho> \<rho>'"
        if "wsinst alg \<rho>" "tsol \<theta> \<rho>" "\<rho> v S = tsubst \<rho> U" for \<rho>
        using tstepD(5)[OF s that(1) sol1[OF that(2,3)]] that(1,3) by (simp add: wsinst_def) metis
      have ce: "tcert alg (tvars_env \<theta>')" if "tcert alg (tvars_env \<theta> \<union> A)"
      proof (rule tstepD(6)[OF s])
        show "tcert alg (tvars_env \<theta>1 \<union> A)"
          using that tcertD[OF that v(2)] tcert_mono[OF that U(1)]
          by (simp add: \<theta>1_def tvars_env_update[OF v(1)])
      qed
      have "tstep alg ar A (\<lambda>\<rho>. \<rho> v S = tsubst \<rho> U) \<theta> n \<theta>' n'"
        using ext tstepD(2,3)[OF s] bs compl ce by (simp add: tstep_def)
      moreover have "\<rho> v S = tsubst \<rho> U" if "tsol \<theta>' \<rho>" for \<rho>
        using tsol_textends[OF tstepD(1)[OF s] that] lk1 by (simp add: tsol_def)
      moreover have "card (uvars \<theta>' X) < card (uvars \<theta> X)"
        if "v \<in> uvars \<theta> X" "uvars \<theta> U \<subseteq> uvars \<theta> X" for X
      proof -
        have "card (uvars \<theta>' X) \<le> card (uvars \<theta>1 X)" by (rule renames_card[OF ac' tstepD(1)[OF s] ren])
        also have "\<dots> < card (uvars \<theta> X)"
          unfolding \<theta>1_def by (rule card_update_less[OF ac1[unfolded \<theta>1_def] v(1) False that])
        finally show ?thesis .
      qed
      ultimately show ?thesis using m r by blast
    next
      assume m: "meet alg U S (\<theta>1, n) = raise TUnify"
        and nf: "\<forall>\<rho>. wsinst alg \<rho> \<longrightarrow> tsol \<theta>1 \<rho> \<longrightarrow> \<not> has_sort alg (tsubst \<rho> U) S"
      have "\<rho> v S \<noteq> tsubst \<rho> U" if "wsinst alg \<rho>" "tsol \<theta> \<rho>" for \<rho>
        using nf sol1[OF that(2)] that(1) unfolding wsinst_def by metis
      then show ?thesis using m r by blast
    qed
  qed
qed



text \<open>Binding a type variable to another one with a smaller sort.\<close>

lemma bind_var_ok:
  assumes inv: "tinv ar n \<theta> A" and v: "vt_lookup \<theta> v = None" "(v, S1) \<in> tvars_env \<theta> \<union> A"
    and w: "vt_lookup \<theta> w = None" "(w, S2) \<in> tvars_env \<theta> \<union> A" and vw: "v \<noteq> w"
    and le: "sort_le alg S1 S2"
  defines "\<theta>' \<equiv> vt_update (w, (S2, TVar v S1)) \<theta>"
  shows "tstep alg ar A (\<lambda>\<rho>. \<rho> v S1 = \<rho> w S2) \<theta> n \<theta>' n"
    and "tsol \<theta>' \<rho> \<Longrightarrow> \<rho> v S1 = \<rho> w S2"
    and "v \<in> uvars \<theta> X \<Longrightarrow> w \<in> uvars \<theta> X \<Longrightarrow> card (uvars \<theta>' X) < card (uvars \<theta> X)"
proof -
  have ac: "tacyc \<theta>" by (rule tinv_tacyc[OF inv])
  have nw: "w \<notin> uvars \<theta> (TVar v S1)" using vw v(1) by (simp add: uvars_TVar[OF ac])
  have inv': "tinv ar n \<theta>' A" unfolding \<theta>'_def by (rule tinv_update[OF inv w(1) nw w(2)]) (use v(2) in auto)
  have ac': "tacyc \<theta>'" by (rule tinv_tacyc[OF inv'])
  have lk: "vt_lookup \<theta>' w = Some (S2, TVar v S1)" "u \<noteq> w \<Longrightarrow> vt_lookup \<theta>' u = vt_lookup \<theta> u" for u
    by (simp_all add: \<theta>'_def)
  have tn: "tnorm \<theta>' (TVar v S1) = TVar v S1" using lk(2)[of v] vw v(1) by (simp add: tnorm_TVar[OF ac'])
  have bs: "bsorted alg \<theta>' u" if "vt_lookup \<theta> u = None" for u
    using that lk tn le by (cases "u = w") (auto simp: bsorted_def has_sort_TVar_iff simp del: has_sort.simps)
  have ce: "tcert alg (tvars_env \<theta>')" if "tcert alg (tvars_env \<theta> \<union> A)"
    using that tcertD[OF that v(2)] tcertD[OF that w(2)] by (simp add: \<theta>'_def tvars_env_update[OF w(1)])
  show "tstep alg ar A (\<lambda>\<rho>. \<rho> v S1 = \<rho> w S2) \<theta> n \<theta>' n"
    unfolding tstep_def using inv' bs ce
    by (auto simp: \<theta>'_def textends_update w(1) intro!: tsol_update)
  show "tsol \<theta>' \<rho> \<Longrightarrow> \<rho> v S1 = \<rho> w S2" using lk(1) by (simp add: tsol_def)
  show "v \<in> uvars \<theta> X \<Longrightarrow> w \<in> uvars \<theta> X \<Longrightarrow> card (uvars \<theta>' X) < card (uvars \<theta> X)"
    unfolding \<theta>'_def
    by (rule card_update_less[OF ac'[unfolded \<theta>'_def] w(1) nw]) (simp_all add: uvars_TVar[OF ac] v(1))
qed

text \<open>Binding two type variables with incomparable sorts to a new one.\<close>

lemma bind_new_ok:
  assumes inv: "tinv ar n \<theta> A" and v: "vt_lookup \<theta> v = None" "(v, S1) \<in> tvars_env \<theta> \<union> A"
    and w: "vt_lookup \<theta> w = None" "(w, S2) \<in> tvars_env \<theta> \<union> A" and vw: "v \<noteq> w"
  defines "V \<equiv> TVar (aT, n + 1) (inter_sort alg S1 S2)"
  defines "\<theta>1 \<equiv> vt_update (w, (S2, V)) \<theta>"
  defines "\<theta>2 \<equiv> vt_update (v, (S1, V)) \<theta>1"
  shows "tstep alg ar A (\<lambda>\<rho>. \<rho> v S1 = \<rho> w S2) \<theta> n \<theta>2 (n + 1)"
    and "tsol \<theta>2 \<rho> \<Longrightarrow> \<rho> v S1 = \<rho> w S2"
    and "v \<in> uvars \<theta> X \<Longrightarrow> w \<in> uvars \<theta> X \<Longrightarrow> card (uvars \<theta>2 X) < card (uvars \<theta> X)"
proof -
  have ac: "tacyc \<theta>" by (rule tinv_tacyc[OF inv])
  have idx: "snd v \<le> n" "snd w \<le> n" using tinv_idx[OF inv v(2)] tinv_idx[OF inv w(2)] by simp_all
  have fr: "vt_lookup \<theta> (aT, n + 1) = None" by (rule tinv_fresh[OF inv]) simp
  have inv1: "tinv ar (n + 1) \<theta>1 A" unfolding \<theta>1_def V_def by (rule tinv_update_fresh[OF inv w])
  have ac1: "tacyc \<theta>1" by (rule tinv_tacyc[OF inv1])
  have ext1: "textends \<theta> \<theta>1" by (simp add: \<theta>1_def textends_update w(1))
  have v1: "vt_lookup \<theta>1 v = None" using v(1) vw by (simp add: \<theta>1_def)
  have fr1: "vt_lookup \<theta>1 (aT, n + 1) = None" using fr idx by (auto simp: \<theta>1_def)
  have uV1: "uvars \<theta>1 V = {(aT, n + 1)}" by (simp add: V_def uvars_TVar[OF ac1] fr1)
  have nv: "v \<notin> uvars \<theta>1 V" using uV1 idx by auto
  have V1: "tvars V \<subseteq> tvars_env \<theta>1 \<union> A" using tvars_envI2[of \<theta>1 w S2 V] by (auto simp: \<theta>1_def)
  have inv2: "tinv ar (n + 1) \<theta>2 A" unfolding \<theta>2_def
    by (rule tinv_update[OF inv1 v1 nv]) (use v(2) tvars_env_textends[OF ext1] V1 in \<open>auto simp: V_def\<close>)
  have ac2: "tacyc \<theta>2" by (rule tinv_tacyc[OF inv2])
  have ext2: "textends \<theta>1 \<theta>2" by (simp add: \<theta>2_def textends_update v1)
  have fr2: "vt_lookup \<theta>2 (aT, n + 1) = None" using fr1 idx by (auto simp: \<theta>2_def)
  have tnV: "tnorm \<theta>2 V = V" by (simp add: V_def tnorm_TVar[OF ac2] fr2)
  have lk: "vt_lookup \<theta>2 v = Some (S1, V)" "vt_lookup \<theta>2 w = Some (S2, V)"
    "u \<noteq> v \<Longrightarrow> u \<noteq> w \<Longrightarrow> vt_lookup \<theta>2 u = vt_lookup \<theta> u" for u
    using vw by (simp_all add: \<theta>2_def \<theta>1_def)
  have hsV: "has_sort alg V S1" "has_sort alg V S2"
    using inter_sort_sem[of V S1 S2] by (simp_all add: V_def del: has_sort.simps)
  have bs: "bsorted alg \<theta>2 u" if "vt_lookup \<theta> u = None" for u
    using that lk tnV hsV by (cases "u = v \<or> u = w") (auto simp: bsorted_def)
  have compl: "\<exists>\<rho>'. wsinst alg \<rho>' \<and> tsol \<theta>2 \<rho>' \<and> tagree n \<rho> \<rho>'"
    if \<rho>: "wsinst alg \<rho>" "tsol \<theta> \<rho>" "\<rho> v S1 = \<rho> w S2" for \<rho>
  proof -
    have "has_sort alg (\<rho> v S1) (inter_sort alg S1 S2)"
      using \<rho> by (simp add: inter_sort_sem wsinst_def del: has_sort.simps) metis
    note fr' = tinst_fresh[OF inv \<rho>(1,2) this, of aT]
    let ?\<rho>' = "\<lambda>u S. if u = (aT, n + 1) \<and> S = inter_sort alg S1 S2 then \<rho> v S1 else \<rho> u S"
    have "tsol \<theta>1 ?\<rho>'" unfolding \<theta>1_def
      by (rule tsol_update[OF fr'(3)]) (use idx \<rho>(3) in \<open>auto simp: V_def\<close>)
    then have "tsol \<theta>2 ?\<rho>'" unfolding \<theta>2_def
      by (rule tsol_update) (use idx in \<open>auto simp: V_def\<close>)
    then show ?thesis using fr'(1,2) by blast
  qed
  have ce: "tcert alg (tvars_env \<theta>2)" if c: "tcert alg (tvars_env \<theta> \<union> A)"
  proof -
    have "sort_ok alg S1" "sort_ok alg S2" by (rule tcertD[OF c v(2)], rule tcertD[OF c w(2)])
    moreover have "tvars_env \<theta>1 = insert (w, S2) (tvars V \<union> tvars_env \<theta>)"
      by (simp add: \<theta>1_def tvars_env_update[OF w(1)])
    moreover have "tvars_env \<theta>2 = insert (v, S1) (tvars V \<union> tvars_env \<theta>1)"
      by (simp add: \<theta>2_def tvars_env_update[OF v1])
    ultimately show ?thesis using c by (simp add: V_def sort_ok_inter_sort)
  qed
  show "tstep alg ar A (\<lambda>\<rho>. \<rho> v S1 = \<rho> w S2) \<theta> n \<theta>2 (n + 1)"
    unfolding tstep_def using textends_trans[OF ext1 ext2] inv2 bs compl ce by auto
  show "tsol \<theta>2 \<rho> \<Longrightarrow> \<rho> v S1 = \<rho> w S2" using lk(1,2) by (simp add: tsol_def)
  assume X: "v \<in> uvars \<theta> X" "w \<in> uvars \<theta> X"
  have nwV: "w \<notin> uvars \<theta> V" using idx fr by (auto simp: V_def uvars_TVar[OF ac])
  have uV: "uvars \<theta> V = {(aT, n + 1)}" by (simp add: V_def uvars_TVar[OF ac] fr)
  have u1: "uvars \<theta>1 X = insert (aT, n + 1) (uvars \<theta> X - {w})"
    using uvars_update[OF ac1[unfolded \<theta>1_def] w(1) nwV, of X] X(2) uV unfolding \<theta>1_def by auto
  have "card (uvars \<theta>1 X) \<le> card (uvars \<theta> X - {w}) + 1"
    unfolding u1 by (simp add: card_insert_if)
  also have "\<dots> = card (uvars \<theta> X)" using X(2) card_gt_0_iff[of "uvars \<theta> X"] by auto
  finally have c1: "card (uvars \<theta>1 X) \<le> card (uvars \<theta> X)" .
  have "card (uvars \<theta>2 X) < card (uvars \<theta>1 X)"
    unfolding \<theta>2_def by (rule card_update_less[OF ac2[unfolded \<theta>2_def] v1 nv]) (use u1 X vw uV1 in auto)
  with c1 show "card (uvars \<theta>2 X) < card (uvars \<theta> X)" by simp
qed


text \<open>
  The main result on \<^const>\<open>unify_aux\<close>: it terminates and either fails with \<open>TUnify\<close> and
  there is no well-sorted unifier, or it returns a most general unifier: its solutions unify the
  types, and every well-sorted unifier extends to a well-sorted solution. Moreover, the number of
  unbound type variables of the problem decreases, unless the environment is unchanged.
\<close>

lemma unify_aux_ok:
  assumes "tinv ar n \<theta> A" "tvars T \<subseteq> tvars_env \<theta> \<union> A" "tvars U \<subseteq> tvars_env \<theta> \<union> A"
    "wft ar T" "wft ar U"
  shows "(\<exists>\<theta>' n'. unify_aux alg T U (\<theta>, n) = return (\<theta>', n') \<and>
      tstep alg ar A (\<lambda>\<rho>. tsubst \<rho> T = tsubst \<rho> U) \<theta> n \<theta>' n' \<and>
      (\<forall>\<rho>. tsol \<theta>' \<rho> \<longrightarrow> tsubst \<rho> T = tsubst \<rho> U) \<and>
      (\<forall>X. uvars \<theta> T \<union> uvars \<theta> U \<subseteq> uvars \<theta> X \<longrightarrow> \<theta>' = \<theta> \<or> card (uvars \<theta>' X) < card (uvars \<theta> X))) \<or>
    (unify_aux alg T U (\<theta>, n) = raise TUnify \<and>
      (\<forall>\<rho>. wsinst alg \<rho> \<longrightarrow> tsol \<theta> \<rho> \<longrightarrow> tsubst \<rho> T \<noteq> tsubst \<rho> U))"
  using assms
proof (induction "(card (uvars \<theta> T \<union> uvars \<theta> U), size (tnorm \<theta> T))" arbitrary: \<theta> n T U
    rule: wf_induct_rule[OF wf_lex_prod[OF wf_less_than wf_less_than], case_names less])
  case less
  note inv = less.prems(1)
  have ac: "tacyc \<theta>" by (rule tinv_tacyc[OF inv])
  have tc: "tcons_env \<theta>" by (rule tinv_tcons_env[OF inv])
  obtain T' where T': "devar \<theta> T = return T'" "tnorm \<theta> T' = tnorm \<theta> T" "\<not> tbound \<theta> T'"
    "tvars T' \<subseteq> tvars_env \<theta> \<union> A" "wft ar T'"
    by (rule tinv_devar[OF inv less.prems(2,4)])
  obtain U' where U': "devar \<theta> U = return U'" "tnorm \<theta> U' = tnorm \<theta> U" "\<not> tbound \<theta> U'"
    "tvars U' \<subseteq> tvars_env \<theta> \<union> A" "wft ar U'"
    by (rule tinv_devar[OF inv less.prems(3,5)])
  have sT: "tsubst \<rho> T' = tsubst \<rho> T" and sU: "tsubst \<rho> U' = tsubst \<rho> U" if "tsol \<theta> \<rho>" for \<rho>
    using tsubst_tnorm[OF ac tc that tinv_tcons[OF inv T'(4)]] tsubst_tnorm[OF ac tc that tinv_tcons[OF inv less.prems(2)]]
      tsubst_tnorm[OF ac tc that tinv_tcons[OF inv U'(4)]] tsubst_tnorm[OF ac tc that tinv_tcons[OF inv less.prems(3)]]
      T'(2) U'(2) by simp_all
  have uT: "uvars \<theta> T' = uvars \<theta> T" and uU: "uvars \<theta> U' = uvars \<theta> U"
    by (simp_all add: uvars_def T'(2) U'(2))
  let ?R = "unify_aux alg T U (\<theta>, n)"
  let ?Ok = "\<lambda>\<theta>' n'. ?R = return (\<theta>', n') \<and> tstep alg ar A (\<lambda>\<rho>. tsubst \<rho> T' = tsubst \<rho> U') \<theta> n \<theta>' n' \<and>
      (\<forall>\<rho>. tsol \<theta>' \<rho> \<longrightarrow> tsubst \<rho> T' = tsubst \<rho> U') \<and>
      (\<forall>X. uvars \<theta> T' \<union> uvars \<theta> U' \<subseteq> uvars \<theta> X \<longrightarrow> \<theta>' = \<theta> \<or> card (uvars \<theta>' X) < card (uvars \<theta> X))"
  let ?Fail = "?R = raise TUnify \<and> (\<forall>\<rho>. wsinst alg \<rho> \<longrightarrow> tsol \<theta> \<rho> \<longrightarrow> tsubst \<rho> T' \<noteq> tsubst \<rho> U')"
  have main: "(\<exists>\<theta>' n'. ?Ok \<theta>' n') \<or> ?Fail"
  proof -
    consider (VV) v S1 w S2 where "T' = TVar v S1" "U' = TVar w S2"
      | (VN) v S where "T' = TVar v S" "\<And>w S'. U' \<noteq> TVar w S'"
      | (NV) w S where "U' = TVar w S" "\<And>v S'. T' \<noteq> TVar v S'"
      | (TT) a Ts b Us where "T' = Type a Ts" "U' = Type b Us"
      | (FF) "\<And>v S. T' \<noteq> TVar v S" "\<And>v S. U' \<noteq> TVar v S" "\<And>a Ts b Us. T' = Type a Ts \<Longrightarrow> U' \<noteq> Type b Us"
      by (cases T'; cases U') auto
    then show ?thesis
    proof cases
      case (VV v S1 w S2)
      have v: "vt_lookup \<theta> v = None" "(v, S1) \<in> tvars_env \<theta> \<union> A" using T'(3,4) VV by auto
      have w: "vt_lookup \<theta> w = None" "(w, S2) \<in> tvars_env \<theta> \<union> A" using U'(3,4) VV by auto
      have uv: "uvars \<theta> T' = {v}" "uvars \<theta> U' = {w}" using v(1) w(1) VV by (simp_all add: uvars_TVar[OF ac])
      show ?thesis
      proof (cases "v = w")
        case True
        then have "S1 = S2" using v(2) w(2) inv unfolding tinv_def scons_def by blast
        then have "?R = return (\<theta>, n)" using True by (subst unify_aux.simps) (simp add: T'(1) U'(1) VV)
        then show ?thesis using True \<open>S1 = S2\<close> VV by (simp add: tstep_refl[OF inv])
      next
        case vw: False
        show ?thesis
        proof (cases "sort_le alg S1 S2")
          case le: True
          note b = bind_var_ok[OF inv v w vw le]
          have "?R = return (vt_update (w, (S2, TVar v S1)) \<theta>, n)"
            using vw le w(1) by (subst unify_aux.simps) (simp add: T'(1) U'(1) VV update_new_def vt_defined_lookup)
          then show ?thesis using b uv VV by auto
        next
          case nle: False
          show ?thesis
          proof (cases "sort_le alg S2 S1")
            case le: True
            note b = bind_var_ok[OF inv w v vw[symmetric] le]
            have "?R = return (vt_update (v, (S1, TVar w S2)) \<theta>, n)"
              using vw le nle v(1)
              by (subst unify_aux.simps) (simp add: T'(1) U'(1) VV update_new_def vt_defined_lookup)
            moreover have "tstep alg ar A (\<lambda>\<rho>. tsubst \<rho> T' = tsubst \<rho> U') \<theta> n (vt_update (v, (S1, TVar w S2)) \<theta>) n"
              by (rule tstep_mono[OF b(1)]) (auto simp: VV)
            moreover have "tsol (vt_update (v, (S1, TVar w S2)) \<theta>) \<rho> \<Longrightarrow> \<rho> v S1 = \<rho> w S2" for \<rho>
              using b(2) by metis
            ultimately show ?thesis using b(3) uv VV by auto
          next
            case nle2: False
            note b = bind_new_ok[OF inv v w vw]
            have "?R = return (vt_update (v, (S1, TVar (aT, n + 1) (inter_sort alg S1 S2)))
                (vt_update (w, (S2, TVar (aT, n + 1) (inter_sort alg S1 S2))) \<theta>), n + 1)"
              using vw nle nle2 v(1) w(1)
              by (subst unify_aux.simps) (simp add: T'(1) U'(1) VV update_new_def vt_defined_lookup gen_tyvar_def)
            then show ?thesis using b uv VV by auto
          qed
        qed
      qed
    next
      case (VN v S)
      have v: "vt_lookup \<theta> v = None" "(v, S) \<in> tvars_env \<theta> \<union> A" using T'(3,4) VN by auto
      have R: "?R = do {b \<leftarrow> type_occurs v \<theta> U';
          if b then raise TUnify else do {\<theta>1 \<leftarrow> update_new (v, (S, U')) \<theta>; meet alg U' S (\<theta>1, n)}}"
        using VN by (subst unify_aux.simps) (simp add: T'(1) U'(1) split: ptyp.split)
      from bind_meet_ok[OF inv v U'(4,5) VN(2)] show ?thesis
      proof (elim disjE exE conjE)
        fix \<theta>' n' assume r: "do {b \<leftarrow> type_occurs v \<theta> U';
            if b then raise TUnify else do {\<theta>1 \<leftarrow> update_new (v, (S, U')) \<theta>; meet alg U' S (\<theta>1, n)}} =
            return (\<theta>', n')"
          and s: "tstep alg ar A (\<lambda>\<rho>. \<rho> v S = tsubst \<rho> U') \<theta> n \<theta>' n'"
          and snd: "\<forall>\<rho>. tsol \<theta>' \<rho> \<longrightarrow> \<rho> v S = tsubst \<rho> U'"
          and m: "\<forall>X. v \<in> uvars \<theta> X \<longrightarrow> uvars \<theta> U' \<subseteq> uvars \<theta> X \<longrightarrow> card (uvars \<theta>' X) < card (uvars \<theta> X)"
        have "tstep alg ar A (\<lambda>\<rho>. tsubst \<rho> T' = tsubst \<rho> U') \<theta> n \<theta>' n'"
          by (rule tstep_mono[OF s]) (simp add: VN)
        then show ?thesis using R r snd m VN v(1) by (auto simp: uvars_TVar[OF ac])
      next
        assume "do {b \<leftarrow> type_occurs v \<theta> U';
            if b then raise TUnify else do {\<theta>1 \<leftarrow> update_new (v, (S, U')) \<theta>; meet alg U' S (\<theta>1, n)}} =
            raise TUnify" "\<forall>\<rho>. wsinst alg \<rho> \<longrightarrow> tsol \<theta> \<rho> \<longrightarrow> \<rho> v S \<noteq> tsubst \<rho> U'"
        then show ?thesis using R VN by auto
      qed
    next
      case (NV w S)
      have w: "vt_lookup \<theta> w = None" "(w, S) \<in> tvars_env \<theta> \<union> A" using U'(3,4) NV by auto
      have R: "?R = do {b \<leftarrow> type_occurs w \<theta> T';
          if b then raise TUnify else do {\<theta>1 \<leftarrow> update_new (w, (S, T')) \<theta>; meet alg T' S (\<theta>1, n)}}"
        using NV by (subst unify_aux.simps) (simp add: T'(1) U'(1) split: ptyp.split)
      from bind_meet_ok[OF inv w T'(4,5) NV(2)] show ?thesis
      proof (elim disjE exE conjE)
        fix \<theta>' n' assume r: "do {b \<leftarrow> type_occurs w \<theta> T';
            if b then raise TUnify else do {\<theta>1 \<leftarrow> update_new (w, (S, T')) \<theta>; meet alg T' S (\<theta>1, n)}} =
            return (\<theta>', n')"
          and s: "tstep alg ar A (\<lambda>\<rho>. \<rho> w S = tsubst \<rho> T') \<theta> n \<theta>' n'"
          and snd: "\<forall>\<rho>. tsol \<theta>' \<rho> \<longrightarrow> \<rho> w S = tsubst \<rho> T'"
          and m: "\<forall>X. w \<in> uvars \<theta> X \<longrightarrow> uvars \<theta> T' \<subseteq> uvars \<theta> X \<longrightarrow> card (uvars \<theta>' X) < card (uvars \<theta> X)"
        have "tstep alg ar A (\<lambda>\<rho>. tsubst \<rho> T' = tsubst \<rho> U') \<theta> n \<theta>' n'"
          by (rule tstep_mono[OF s]) (auto simp: NV)
        then show ?thesis using R r snd m NV w(1) by (auto simp: uvars_TVar[OF ac])
      next
        assume "do {b \<leftarrow> type_occurs w \<theta> T';
            if b then raise TUnify else do {\<theta>1 \<leftarrow> update_new (w, (S, T')) \<theta>; meet alg T' S (\<theta>1, n)}} =
            raise TUnify" "\<forall>\<rho>. wsinst alg \<rho> \<longrightarrow> tsol \<theta> \<rho> \<longrightarrow> \<rho> w S \<noteq> tsubst \<rho> T'"
        then show ?thesis using R NV by auto
      qed
    next
      case (TT a Ts b Us)
      show ?thesis
      proof (cases "a = b")
        case False
        have "?R = raise TUnify" using False by (subst unify_aux.simps) (simp add: T'(1) U'(1) TT)
        then show ?thesis using False TT by auto
      next
        case True
        have len: "length Ts = tarity ar a" "length Us = tarity ar a" using T'(5) U'(5) TT True by auto
        then have zl: "length Ts = length Us" by simp
        define g where "g = (\<lambda>(T, U) st. unify_aux alg T U st)"
        have R: "?R = foldM g (zip Ts Us) (\<theta>, n)"
          using True by (subst unify_aux.simps) (simp add: T'(1) U'(1) TT g_def)
        let ?PX = "Type a [T', U']"
        have uPX: "uvars \<theta> ?PX = uvars \<theta> T \<union> uvars \<theta> U" using uT uU by simp
        have sizes: "size (tnorm \<theta> Ti) < size (tnorm \<theta> T)" if "Ti \<in> set Ts" for Ti
        proof -
          have "size (tnorm \<theta> Ti) \<le> size_list size (map (tnorm \<theta>) Ts)"
            using that by (intro size_list_estimation'[of "tnorm \<theta> Ti"]) auto
          then show ?thesis using T'(2)[symmetric] by (simp add: TT)
        qed
        have fold: "(\<exists>\<theta>2 n2. foldM g ps (\<theta>1, n1) = return (\<theta>2, n2) \<and>
            tstep alg ar A (\<lambda>\<rho>. \<forall>q\<in>set ps. tsubst \<rho> (fst q) = tsubst \<rho> (snd q)) \<theta>1 n1 \<theta>2 n2 \<and>
            (\<forall>\<rho>. tsol \<theta>2 \<rho> \<longrightarrow> (\<forall>q\<in>set ps. tsubst \<rho> (fst q) = tsubst \<rho> (snd q))) \<and>
            (\<forall>X. uvars \<theta> T' \<union> uvars \<theta> U' \<subseteq> uvars \<theta> X \<longrightarrow> \<theta>2 = \<theta> \<or> card (uvars \<theta>2 X) < card (uvars \<theta> X))) \<or>
          (foldM g ps (\<theta>1, n1) = raise TUnify \<and>
            (\<forall>\<rho>. wsinst alg \<rho> \<longrightarrow> tsol \<theta>1 \<rho> \<longrightarrow> \<not> (\<forall>q\<in>set ps. tsubst \<rho> (fst q) = tsubst \<rho> (snd q))))"
          if "set ps \<subseteq> set (zip Ts Us)" "tinv ar n1 \<theta>1 A" "textends \<theta> \<theta>1" "n \<le> n1"
            "\<forall>X. uvars \<theta> T' \<union> uvars \<theta> U' \<subseteq> uvars \<theta> X \<longrightarrow> \<theta>1 = \<theta> \<or> card (uvars \<theta>1 X) < card (uvars \<theta> X)"
          for ps \<theta>1 n1
          using that
        proof (induction ps arbitrary: \<theta>1 n1)
          case Nil
          then show ?case by (simp add: tstep_refl)
        next
          case (Cons p ps \<theta>1 n1)
          obtain Ti Ui where p: "p = (Ti, Ui)" by force
          have pz: "(Ti, Ui) \<in> set (zip Ts Us)" using Cons.prems(1) p by simp
          have Ti: "Ti \<in> set Ts" and Ui: "Ui \<in> set Us" using pz by (auto dest: set_zip_leftD set_zip_rightD)
          have inv1: "tinv ar n1 \<theta>1 A" by (rule Cons.prems(2))
          have ac1: "tacyc \<theta>1" by (rule tinv_tacyc[OF inv1])
          have ext1: "textends \<theta> \<theta>1" by (rule Cons.prems(3))
          have tvA: "tvars (fst q) \<subseteq> tvars_env \<theta>1 \<union> A" "tvars (snd q) \<subseteq> tvars_env \<theta>1 \<union> A"
            if "q \<in> set (zip Ts Us)" for q
            using T'(4) U'(4) TT True that tvars_env_textends[OF ext1]
              set_zip_leftD[of "fst q" "snd q" Ts Us] set_zip_rightD[of "fst q" "snd q" Ts Us] by fastforce+
          have wf: "wft ar Ti" "wft ar Ui" using T'(5) U'(5) TT Ti Ui by auto
          have sub1: "uvars \<theta>1 Ti \<union> uvars \<theta>1 Ui \<subseteq> uvars \<theta>1 ?PX" using Ti Ui TT True by auto
          have "uvars \<theta> T' \<union> uvars \<theta> U' \<subseteq> uvars \<theta> ?PX" by simp
          then have mPX: "\<theta>1 = \<theta> \<or> card (uvars \<theta>1 ?PX) < card (uvars \<theta> ?PX)" using Cons.prems(5) by blast
          have c1: "card (uvars \<theta>1 Ti \<union> uvars \<theta>1 Ui) \<le> card (uvars \<theta>1 ?PX)"
            by (rule card_mono[OF finite_uvars sub1])
          have meas: "((card (uvars \<theta>1 Ti \<union> uvars \<theta>1 Ui), size (tnorm \<theta>1 Ti)),
              (card (uvars \<theta> T \<union> uvars \<theta> U), size (tnorm \<theta> T))) \<in> less_than <*lex*> less_than"
            using mPX c1 uPX sizes[OF Ti] by (auto simp: le_less)
          have agr: "tsubst \<rho>' (fst q) = tsubst \<rho> (fst q)" "tsubst \<rho>' (snd q) = tsubst \<rho> (snd q)"
            if "q \<in> set (zip Ts Us)" "tagree n1 \<rho> \<rho>'" for q \<rho> \<rho>'
            using tagree_tsubst[OF that(2)] tvA[OF that(1)] tinv_idx[OF inv1] by blast+
          have fstep: "foldM g (p # ps) (\<theta>1, n1) = bindM (unify_aux alg Ti Ui (\<theta>1, n1)) (foldM g ps)"
            by (simp add: p g_def)
          have pss: "set ps \<subseteq> set (zip Ts Us)" using Cons.prems(1) by simp
          from less.hyps[OF meas inv1 tvA[OF pz, simplified] wf] show ?case
          proof (elim disjE exE conjE)
            fix \<theta>2 n2 assume R1: "unify_aux alg Ti Ui (\<theta>1, n1) = return (\<theta>2, n2)"
              and s1: "tstep alg ar A (\<lambda>\<rho>. tsubst \<rho> Ti = tsubst \<rho> Ui) \<theta>1 n1 \<theta>2 n2"
              and snd1: "\<forall>\<rho>. tsol \<theta>2 \<rho> \<longrightarrow> tsubst \<rho> Ti = tsubst \<rho> Ui"
              and m1: "\<forall>X. uvars \<theta>1 Ti \<union> uvars \<theta>1 Ui \<subseteq> uvars \<theta>1 X \<longrightarrow> \<theta>2 = \<theta>1 \<or> card (uvars \<theta>2 X) < card (uvars \<theta>1 X)"
            have inv2: "tinv ar n2 \<theta>2 A" by (rule tstepD(3)[OF s1])
            have ext2: "textends \<theta> \<theta>2" by (rule textends_trans[OF ext1 tstepD(1)[OF s1]])
            have n2: "n \<le> n2" using Cons.prems(4) tstepD(2)[OF s1] by simp
            have m2: "\<forall>X. uvars \<theta> T' \<union> uvars \<theta> U' \<subseteq> uvars \<theta> X \<longrightarrow> \<theta>2 = \<theta> \<or> card (uvars \<theta>2 X) < card (uvars \<theta> X)"
            proof (intro allI impI)
              fix X assume X: "uvars \<theta> T' \<union> uvars \<theta> U' \<subseteq> uvars \<theta> X"
              have "uvars \<theta> ?PX \<subseteq> uvars \<theta> X" using X by simp
              then have "uvars \<theta>1 ?PX \<subseteq> uvars \<theta>1 X" by (rule uvars_mono[OF ac1 ext1])
              then have "\<theta>2 = \<theta>1 \<or> card (uvars \<theta>2 X) < card (uvars \<theta>1 X)" using m1 sub1 by blast
              moreover have "\<theta>1 = \<theta> \<or> card (uvars \<theta>1 X) < card (uvars \<theta> X)" using Cons.prems(5) X by blast
              ultimately show "\<theta>2 = \<theta> \<or> card (uvars \<theta>2 X) < card (uvars \<theta> X)" by auto
            qed
            from Cons.IH[OF pss inv2 ext2 n2 m2] show ?case
            proof (elim disjE exE conjE)
              fix \<theta>3 n3 assume R2: "foldM g ps (\<theta>2, n2) = return (\<theta>3, n3)"
                and s2: "tstep alg ar A (\<lambda>\<rho>. \<forall>q\<in>set ps. tsubst \<rho> (fst q) = tsubst \<rho> (snd q)) \<theta>2 n2 \<theta>3 n3"
                and snd2: "\<forall>\<rho>. tsol \<theta>3 \<rho> \<longrightarrow> (\<forall>q\<in>set ps. tsubst \<rho> (fst q) = tsubst \<rho> (snd q))"
                and m3: "\<forall>X. uvars \<theta> T' \<union> uvars \<theta> U' \<subseteq> uvars \<theta> X \<longrightarrow> \<theta>3 = \<theta> \<or> card (uvars \<theta>3 X) < card (uvars \<theta> X)"
              have PQ: "\<forall>q\<in>set ps. tsubst \<rho>' (fst q) = tsubst \<rho>' (snd q)"
                if "\<forall>q\<in>set (p # ps). tsubst \<rho> (fst q) = tsubst \<rho> (snd q)" "tagree n1 \<rho> \<rho>'" for \<rho> \<rho>'
              proof
                fix q assume q: "q \<in> set ps"
                then have qz: "q \<in> set (zip Ts Us)" using pss by blast
                show "tsubst \<rho>' (fst q) = tsubst \<rho>' (snd q)" using that(1) q agr[OF qz that(2)] by simp
              qed
              have "tstep alg ar A (\<lambda>\<rho>. \<forall>q\<in>set (p # ps). tsubst \<rho> (fst q) = tsubst \<rho> (snd q)) \<theta>1 n1 \<theta>3 n3"
                by (rule tstep_trans[OF tstep_mono[OF s1] s2 PQ]) (simp_all add: p)
              moreover have "\<forall>q\<in>set (p # ps). tsubst \<rho> (fst q) = tsubst \<rho> (snd q)" if "tsol \<theta>3 \<rho>" for \<rho>
                using snd1 snd2 that tsol_textends[OF tstepD(1)[OF s2] that] by (simp add: p)
              ultimately show ?case using fstep R1 R2 m3 by auto
            next
              assume R2: "foldM g ps (\<theta>2, n2) = raise TUnify"
                and nf: "\<forall>\<rho>. wsinst alg \<rho> \<longrightarrow> tsol \<theta>2 \<rho> \<longrightarrow> \<not> (\<forall>q\<in>set ps. tsubst \<rho> (fst q) = tsubst \<rho> (snd q))"
              have "\<not> (\<forall>q\<in>set (p # ps). tsubst \<rho> (fst q) = tsubst \<rho> (snd q))"
                if \<rho>: "wsinst alg \<rho>" "tsol \<theta>1 \<rho>" for \<rho>
              proof
                assume all: "\<forall>q\<in>set (p # ps). tsubst \<rho> (fst q) = tsubst \<rho> (snd q)"
                then obtain \<rho>' where \<rho>': "wsinst alg \<rho>'" "tsol \<theta>2 \<rho>'" "tagree n1 \<rho> \<rho>'"
                  using tstepD(5)[OF s1 \<rho>] by (auto simp: p)
                then obtain q where q: "q \<in> set ps" "tsubst \<rho>' (fst q) \<noteq> tsubst \<rho>' (snd q)"
                  using nf by blast
                then show False using all agr[OF _ \<rho>'(3), of q] pss by auto
              qed
              then show ?case using fstep R1 R2 by simp
            qed
          next
            assume "unify_aux alg Ti Ui (\<theta>1, n1) = raise TUnify"
              "\<forall>\<rho>. wsinst alg \<rho> \<longrightarrow> tsol \<theta>1 \<rho> \<longrightarrow> tsubst \<rho> Ti \<noteq> tsubst \<rho> Ui"
            then show ?case using fstep by (auto simp: p)
          qed
        qed
        have conv: "(\<forall>q\<in>set (zip Ts Us). tsubst \<rho> (fst q) = tsubst \<rho> (snd q)) \<longleftrightarrow> tsubst \<rho> T' = tsubst \<rho> U'"
          for \<rho> using zl by (simp add: TT True ball_set_zip[OF zl] list_eq_iff_nth_eq)
        from fold[OF order_refl inv textends_refl order_refl] show ?thesis
          unfolding conv R[symmetric] by simp
      qed
    next
      case FF
      have R: "?R = (if T' = U' then return (\<theta>, n) else raise TUnify)"
        using FF by (subst unify_aux.simps) (simp add: T'(1) U'(1) split: ptyp.split, metis)
      show ?thesis
      proof (cases "T' = U'")
        case True
        then show ?thesis using R by (simp add: tstep_refl[OF inv])
      next
        case False
        have "tsubst \<rho> T' \<noteq> tsubst \<rho> U'" for \<rho> using FF False by (cases T'; cases U') auto
        then show ?thesis using R False by simp
      qed
    qed
  qed
  then show ?case
  proof (elim disjE exE conjE)
    fix \<theta>' n' assume R: "?R = return (\<theta>', n')"
      and s: "tstep alg ar A (\<lambda>\<rho>. tsubst \<rho> T' = tsubst \<rho> U') \<theta> n \<theta>' n'"
      and snd: "\<forall>\<rho>. tsol \<theta>' \<rho> \<longrightarrow> tsubst \<rho> T' = tsubst \<rho> U'"
      and m: "\<forall>X. uvars \<theta> T' \<union> uvars \<theta> U' \<subseteq> uvars \<theta> X \<longrightarrow> \<theta>' = \<theta> \<or> card (uvars \<theta>' X) < card (uvars \<theta> X)"
    have "tstep alg ar A (\<lambda>\<rho>. tsubst \<rho> T = tsubst \<rho> U) \<theta> n \<theta>' n'"
      by (rule tstep_mono[OF s]) (simp add: sT sU)
    moreover have "tsubst \<rho> T = tsubst \<rho> U" if "tsol \<theta>' \<rho>" for \<rho>
      using snd that sT[OF tsol_textends[OF tstepD(1)[OF s] that]] sU[OF tsol_textends[OF tstepD(1)[OF s] that]]
      by simp
    ultimately show ?case using R m uT uU by blast
  next
    assume "?R = raise TUnify" "\<forall>\<rho>. wsinst alg \<rho> \<longrightarrow> tsol \<theta> \<rho> \<longrightarrow> tsubst \<rho> T' \<noteq> tsubst \<rho> U'"
    then show ?case using sT sU by auto
  qed
qed

end


subsection \<open>Existence of well-sorted solutions\<close>

text \<open>
  If all bindings are sorted, the environment has a well-sorted solution without type variables:
  instantiate the normal forms with free type variables of the respective sorts.
\<close>

definition tsorted :: "algebra \<Rightarrow> tyenv \<Rightarrow> bool" where
  "tsorted alg \<theta> \<longleftrightarrow> (\<forall>v. bsorted alg \<theta> v) \<and> tcert alg (tvars_env \<theta>)"

lemma tsorted_empty: "vt_is_empty \<theta> \<Longrightarrow> tsorted alg \<theta>"
  by (simp add: tsorted_def bsorted_def vt_is_empty_lookup tcert_def tvars_env_def)

context wf_algebra
begin

lemma sort_le_refl[simp]: "sort_le alg S S"
  unfolding sort_le_iff using class_le_refl by blast

lemma tsorted_tstep:
  assumes srt: "tsorted alg \<theta>" and s: "tstep alg ar A P \<theta> n \<theta>' n'" and A: "tcert alg A"
  shows "tsorted alg \<theta>'"
  unfolding tsorted_def
proof
  have \<theta>: "\<forall>v. bsorted alg \<theta> v" using srt by (simp add: tsorted_def)
  show "\<forall>v. bsorted alg \<theta>' v"
  proof
    fix v
    show "bsorted alg \<theta>' v"
    proof (cases "vt_lookup \<theta> v")
      case None
      then show ?thesis by (rule tstepD(4)[OF s])
    next
      case (Some x)
      show ?thesis by (rule bsorted_textends[OF tstepD(3,1)[OF s] tstepD(4)[OF s] \<theta>[rule_format]])
    qed
  qed
  show "tcert alg (tvars_env \<theta>')" using srt A by (intro tstepD(6)[OF s]) (simp add: tsorted_def)
qed

lemma tsol_exists:
  assumes inv: "tinv ar n \<theta> A" and srt: "tsorted alg \<theta>"
  obtains \<rho> where "wsinst alg \<rho>" "tsol \<theta> \<rho>" "\<And>v S. tvars (\<rho> v S) = {}"
proof -
  have ac: "tacyc \<theta>" by (rule tinv_tacyc[OF inv])
  have tc: "tcons_env \<theta>" by (rule tinv_tcons_env[OF inv])
  define \<rho>0 :: tinst where "\<rho>0 = (\<lambda>w S. TFree STR ''a'' S)"
  define \<rho> where "\<rho> = (\<lambda>v S. case vt_lookup \<theta> v of
      Some (S0, U) \<Rightarrow> if S = S0 then tsubst \<rho>0 (tnorm \<theta> U) else TFree STR ''a'' S
    | None \<Rightarrow> TFree STR ''a'' S)"
  have key: "tcons \<theta> T \<Longrightarrow> tsubst \<rho> T = tsubst \<rho>0 (tnorm \<theta> T)" for T
  proof (induction rule: tnorm_induct[OF ac tc, consumes 1, case_names TFree Type Unbound Bound])
    case (Type a Ts)
    then show ?case by simp
  next
    case (Unbound v S)
    then show ?case by (simp add: \<rho>_def \<rho>0_def tnorm_TVar[OF ac])
  next
    case (Bound v S U)
    then show ?case by (simp add: \<rho>_def tnorm_TVar[OF ac])
  qed simp
  have "tsol \<theta> \<rho>"
    unfolding tsol_def
  proof (intro allI impI)
    fix v S U assume v: "vt_lookup \<theta> v = Some (S, U)"
    then show "\<rho> v S = tsubst \<rho> U" using key[OF tcons_envD[OF tc v]] by (simp add: \<rho>_def)
  qed
  moreover have "wsinst alg \<rho>"
    unfolding wsinst_def
  proof (intro allI)
    fix v S
    have hs0: "\<forall>(w, S')\<in>tvars T. has_sort alg (\<rho>0 w S') S'" for T
      by (auto simp: \<rho>0_def has_sort_TFree_iff simp del: has_sort.simps)
    show "has_sort alg (\<rho> v S) S"
    proof (cases "vt_lookup \<theta> v")
      case (Some x)
      obtain S0 U where x: "x = (S0, U)" by force
      have "has_sort alg (tnorm \<theta> U) S0" using srt Some x by (simp add: tsorted_def bsorted_def)
      then have "has_sort alg (tsubst \<rho>0 (tnorm \<theta> U)) S0" by (rule has_sort_tsubst[OF _ hs0])
      then show ?thesis using Some x
        by (simp add: \<rho>_def has_sort_TFree_iff del: has_sort.simps)
    qed (simp add: \<rho>_def has_sort_TFree_iff del: has_sort.simps)
  qed
  moreover have "tvars (\<rho> v S) = {}" for v S
    by (auto simp: \<rho>_def \<rho>0_def tvars_tsubst split: option.splits if_splits)
  ultimately show ?thesis using that by blast
qed

end

end

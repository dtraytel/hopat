section \<open>Rigid Heads and Restrictions\<close>

theory Pattern_Rigid
  imports Pattern_Typing
begin

text \<open>
  De Bruijn lemmas for the completeness proof. Constants and free variables of Pure become
  free variables of \<^typ>\<open>dB\<close> that every unifier must fix; together with bound variables they
  are the rigid heads.
\<close>

subsection \<open>Rigid codes and solutions\<close>

definition rigid_code :: "nat \<Rightarrow> bool" where
  "rigid_code n \<longleftrightarrow> (\<exists>a T. n = code (AConst a T) \<or> n = code (AFree a T))"

lemma rigid_code_simps[simp]:
  "rigid_code (code (AConst a T))" "rigid_code (code (AFree a T))" "\<not> rigid_code (code (AVar x))"
  by (auto simp: rigid_code_def)

definition rigid_subst :: "(nat \<Rightarrow> dB) \<Rightarrow> bool" where
  "rigid_subst \<sigma> \<longleftrightarrow> (\<forall>n. rigid_code n \<longrightarrow> \<sigma> n = dB.Var n)"

lemma rigid_substD: "rigid_subst \<sigma> \<Longrightarrow> rigid_code n \<Longrightarrow> \<sigma> n = dB.Var n"
  by (simp add: rigid_subst_def)

subsection \<open>Restrictions of loose bound variables\<close>

text \<open>
  A term \<^emph>\<open>only depends on\<close> the bound variables in \<open>Z\<close> if it is equivalent to a term whose loose
  bound variables are in \<open>Z\<close>.
\<close>

definition dep_on :: "nat set \<Rightarrow> dB \<Rightarrow> bool" where
  "dep_on Z t \<longleftrightarrow> (\<exists>r. t \<equiv>\<^sub>\<beta>\<^sub>\<eta> r \<and> loose_BVars r \<subseteq> Z)"

lemma dep_onI: "t \<equiv>\<^sub>\<beta>\<^sub>\<eta> r \<Longrightarrow> loose_BVars r \<subseteq> Z \<Longrightarrow> dep_on Z t"
  by (auto simp: dep_on_def)

lemma dep_on_equiv: "s \<equiv>\<^sub>\<beta>\<^sub>\<eta> t \<Longrightarrow> dep_on Z t \<Longrightarrow> dep_on Z s"
  by (auto simp: dep_on_def intro: equiv_trans)

lemma atom_apps_dep_on:
  assumes "is_atom h" "dep_on Z (h \<degree>\<degree> as)"
  shows "loose_BVars h \<subseteq> Z" "\<And>a. a \<in> set as \<Longrightarrow> dep_on Z a"
proof -
  from assms(2) obtain r where r: "h \<degree>\<degree> as \<equiv>\<^sub>\<beta>\<^sub>\<eta> r" "loose_BVars r \<subseteq> Z" by (auto simp: dep_on_def)
  from closure_confluent[OF r(1)] obtain c where c: "\<beta>\<eta>cl (h \<degree>\<degree> as) c" "\<beta>\<eta>cl r c" by blast
  from atom_apps_\<beta>\<eta>cl[OF assms(1) c(1)] obtain bs where bs: "c = h \<degree>\<degree> bs" "list_all2 \<beta>\<eta>cl as bs"
    by blast
  have lc: "loose_BVars c \<subseteq> Z" using loose_BVars_\<beta>\<eta>cl[OF c(2)] r(2) by blast
  then show "loose_BVars h \<subseteq> Z" by (simp add: bs(1))
  fix a assume "a \<in> set as"
  then obtain i where i: "i < length as" "a = as ! i" by (auto simp: in_set_conv_nth)
  with bs(2) have "\<beta>\<eta>cl a (bs ! i)" "i < length bs" by (auto simp: list_all2_conv_all_nth)
  moreover have "loose_BVars (bs ! i) \<subseteq> Z" using lc bs(1) nth_mem[OF \<open>i < length bs\<close>] by auto
  ultimately show "dep_on Z a" by (auto intro: dep_onI \<beta>\<eta>cl_into_equiv)
qed

lemma loose_BVars_lift: "loose_BVars (lift t k) = (\<lambda>v. if v < k then v else Suc v) ` loose_BVars t"
  by (simp add: lift_map_BVars loose_BVars_map_BVars)

lemma Abs_dep_on:
  assumes "dep_on Z (dB.Abs t)"
  shows "dep_on (insert 0 (Suc ` Z)) t"
proof -
  from assms obtain r where r: "dB.Abs t \<equiv>\<^sub>\<beta>\<^sub>\<eta> r" "loose_BVars r \<subseteq> Z" by (auto simp: dep_on_def)
  from r(1) have t: "t \<equiv>\<^sub>\<beta>\<^sub>\<eta> lift r 0 \<degree> BVar 0" by (simp add: fact6)
  have "loose_BVars (lift r 0 \<degree> BVar 0) = insert 0 (Suc ` loose_BVars r)"
    by (auto simp: loose_BVars_lift)
  also have "\<dots> \<subseteq> insert 0 (Suc ` Z)" using r(2) by blast
  finally show ?thesis by (rule dep_onI[OF t])
qed

text \<open>
  The restriction lemma: if a closed term \<open>u\<close> applied to distinct bound variables \<open>zs\<close> only depends
  on the variables in \<open>Z\<close>, then \<open>u\<close> is equivalent to an abstraction of a closed term \<open>w\<close> applied
  to any list \<open>ks\<close> of the (de Bruijn) positions of these variables.
\<close>

lemma restrict_flex:
  assumes closed: "no_loose_bound u 0" and ty: "(e, \<tau>') \<turnstile> u : Ts \<Rrightarrow> U"
    and len: "length zs = length Ts" and zs: "distinct zs"
    and dep: "dep_on Z (u \<degree>\<degree> map BVar zs)"
    and ks: "\<And>k. k < length zs \<Longrightarrow> zs ! (length zs - Suc k) \<in> Z \<Longrightarrow> k \<in> set ks"
  obtains w where "no_loose_bound w 0" "(e, \<tau>') \<turnstile> w : map (env_ext e Ts) ks \<Rrightarrow> U"
    "u \<equiv>\<^sub>\<beta>\<^sub>\<eta> Abs_m (length zs) (w \<degree>\<degree> map BVar ks)"
proof -
  let ?m = "length zs"
  obtain r where r: "\<beta>\<eta>cl (u \<degree>\<degree> map BVar (downs ?m)) r" "normal r" "(env_ext e Ts, \<tau>') \<turnstile> r : U"
    "loose_BVars r \<subseteq> {..<?m}"
    using typed_nf_args[OF closed ty len[symmetric]] .
  let ?g = "\<lambda>i. zs ! (?m - Suc i)"
  note ren = nf_rename_args[OF closed r(1,2) refl zs]
  from dep obtain r' where r': "u \<degree>\<degree> map BVar zs \<equiv>\<^sub>\<beta>\<^sub>\<eta> r'" "loose_BVars r' \<subseteq> Z"
    by (auto simp: dep_on_def)
  have "r' \<equiv>\<^sub>\<beta>\<^sub>\<eta> map_BVars ?g r"
    using equiv_sym[OF r'(1)] \<beta>\<eta>cl_into_equiv[OF ren(1)] by (rule equiv_trans)
  then have "\<beta>\<eta>cl r' (map_BVars ?g r)" using ren(2) by (rule equiv_\<beta>\<eta>cl_normal)
  then have "loose_BVars (map_BVars ?g r) \<subseteq> Z" using loose_BVars_\<beta>\<eta>cl r'(2) by blast
  then have sub: "loose_BVars r \<subseteq> set ks"
    using r(4) ks by (auto simp: loose_BVars_map_BVars)
  define w where "w = abst ks r"
  have "no_loose_bound w 0" unfolding w_def by (rule loose_BVars_abst[OF sub])
  moreover have "(e, \<tau>') \<turnstile> w : map (env_ext e Ts) ks \<Rrightarrow> U"
    unfolding w_def by (rule typing_abst[OF r(3) sub])
  moreover have "u \<equiv>\<^sub>\<beta>\<^sub>\<eta> Abs_m ?m (w \<degree>\<degree> map BVar ks)"
  proof -
    have "u \<equiv>\<^sub>\<beta>\<^sub>\<eta> Abs_m ?m (u \<degree>\<degree> map BVar (downs ?m))"
      using eta_expand_equiv[OF closed] by (rule equiv_sym)
    also have "\<dots> \<equiv>\<^sub>\<beta>\<^sub>\<eta> Abs_m ?m r" using r(1) by (intro equiv_Abs_m \<beta>\<eta>cl_into_equiv)
    also have "r = appb w ks" by (simp add: w_def appb_abst_self[OF sub])
    also have "Abs_m ?m (appb w ks) \<equiv>\<^sub>\<beta>\<^sub>\<eta> Abs_m ?m (w \<degree>\<degree> map BVar ks)"
      by (intro equiv_Abs_m equiv_sym[OF beta_into_equiv] appb_reduces)
    finally show ?thesis .
  qed
  ultimately show ?thesis by (rule that)
qed

text \<open>Injective renamings of bound variables reflect equivalence of typed terms.\<close>

lemma map_BVars_equiv_reflect:
  assumes eq: "map_BVars f a \<equiv>\<^sub>\<beta>\<^sub>\<eta> map_BVars f b" and inj: "inj_on f (loose_BVars a \<union> loose_BVars b)"
    and ty: "(e, \<tau>) \<turnstile> a : T" "(e', \<tau>') \<turnstile> b : T'"
  shows "a \<equiv>\<^sub>\<beta>\<^sub>\<eta> b"
proof -
  obtain na where na: "\<beta>\<eta>cl a na" "normal na" using normal_form_ex[OF ty(1)] by blast
  obtain nb where nb: "\<beta>\<eta>cl b nb" "normal nb" using normal_form_ex[OF ty(2)] by blast
  have la: "loose_BVars na \<subseteq> loose_BVars a" and lb: "loose_BVars nb \<subseteq> loose_BVars b"
    using loose_BVars_\<beta>\<eta>cl na(1) nb(1) by blast+
  have "inj_on f (loose_BVars a)" "inj_on f (loose_BVars b)" using inj by (auto intro: inj_on_subset)
  note ra = normal_form_rename[OF na this(1)] and rb = normal_form_rename[OF nb this(2)]
  have "map_BVars f na = map_BVars f nb" by (rule normal_form_unique[OF eq ra rb])
  moreover have "inj_on f (loose_BVars na \<union> loose_BVars nb)"
    using inj la lb by (auto intro: inj_on_subset)
  ultimately have "na = nb" by (rule map_BVars_inj_eq)
  then show ?thesis
    using na(1) nb(1) by (metis \<beta>\<eta>cl_into_equiv equiv_sym equiv_trans)
qed

text \<open>A flex-flex problem with the same head (\<open>flexflex1\<close>).\<close>

lemma ff1_dep:
  assumes closed: "no_loose_bound u 0" and ty: "(e, \<tau>') \<turnstile> u : Ts \<Rrightarrow> U"
    and len: "length is = length Ts" "length js = length Ts" and dist: "distinct is" "distinct js"
    and eq: "u \<degree>\<degree> map BVar is \<equiv>\<^sub>\<beta>\<^sub>\<eta> u \<degree>\<degree> map BVar js"
  shows "dep_on {is ! p | p. p < length is \<and> is ! p = js ! p} (u \<degree>\<degree> map BVar is)"
proof -
  let ?m = "length Ts"
  obtain r where r: "\<beta>\<eta>cl (u \<degree>\<degree> map BVar (downs ?m)) r" "normal r" "(env_ext e Ts, \<tau>') \<turnstile> r : U"
    "loose_BVars r \<subseteq> {..<?m}"
    using typed_nf_args[OF closed ty refl] .
  have r1: "\<beta>\<eta>cl (u \<degree>\<degree> map BVar is) (map_BVars (\<lambda>i. is ! (?m - Suc i)) r)"
    "normal (map_BVars (\<lambda>i. is ! (?m - Suc i)) r)"
    using nf_rename_args[OF closed r(1,2) len(1) dist(1)] .
  have r2: "\<beta>\<eta>cl (u \<degree>\<degree> map BVar js) (map_BVars (\<lambda>i. js ! (?m - Suc i)) r)"
    "normal (map_BVars (\<lambda>i. js ! (?m - Suc i)) r)"
    using nf_rename_args[OF closed r(1,2) len(2) dist(2)] .
  have same: "map_BVars (\<lambda>i. is ! (?m - Suc i)) r = map_BVars (\<lambda>i. js ! (?m - Suc i)) r"
    by (rule normal_form_unique[OF eq r1 r2])
  show ?thesis
  proof (rule dep_onI[OF \<beta>\<eta>cl_into_equiv[OF r1(1)]])
    show "loose_BVars (map_BVars (\<lambda>i. is ! (?m - Suc i)) r) \<subseteq> {is ! p |p. p < length is \<and> is ! p = js ! p}"
    proof
      fix v assume "v \<in> loose_BVars (map_BVars (\<lambda>i. is ! (?m - Suc i)) r)"
      then obtain k where k: "k \<in> loose_BVars r" "v = is ! (?m - Suc k)"
        by (auto simp: loose_BVars_map_BVars)
      have "is ! (?m - Suc k) = js ! (?m - Suc k)" using map_BVars_eq_on[OF same k(1)] .
      moreover have "?m - Suc k < length is" using k(1) r(4) len by auto
      ultimately show "v \<in> {is ! p |p. p < length is \<and> is ! p = js ! p}" using k(2) by blast
    qed
  qed
qed

text \<open>A flex term equivalent to another closed term applied to some of its arguments.\<close>

lemma flex_bind_equiv:
  assumes closed_u: "no_loose_bound u 0" and tyu: "(E, \<tau>') \<turnstile> u \<degree>\<degree> map BVar zs : U"
    and zs: "distinct zs"
    and closed_w: "no_loose_bound w 0" and tyw: "(E, \<tau>') \<turnstile> w \<degree>\<degree> map BVar ys : U"
    and eq: "u \<degree>\<degree> map BVar zs \<equiv>\<^sub>\<beta>\<^sub>\<eta> w \<degree>\<degree> map BVar ys" and sub: "set ys \<subseteq> set zs"
  shows "u \<equiv>\<^sub>\<beta>\<^sub>\<eta> Abs_m (length zs) (w \<degree>\<degree> map BVar (map (\<lambda>y. the (Unification.idx zs y)) ys))"
proof -
  let ?m = "length zs" and ?g = "\<lambda>i. zs ! (length zs - Suc i)"
  let ?ks = "map (\<lambda>y. the (Unification.idx zs y)) ys"
  let ?Ts = "map E zs"
  have tyu': "(E', \<tau>') \<turnstile> u : ?Ts \<Rrightarrow> U" for E'
    using tyu closed_u by (auto simp: list_app_typing_iff typings_map_BVar intro: typing_closed)
  obtain r where r: "\<beta>\<eta>cl (u \<degree>\<degree> map BVar (downs ?m)) r" "normal r" "(env_ext E ?Ts, \<tau>') \<turnstile> r : U"
    "loose_BVars r \<subseteq> {..<?m}"
    using typed_nf_args[OF closed_u tyu'[of E] length_map] .
  have nr: "\<beta>\<eta>cl (u \<degree>\<degree> map BVar zs) (map_BVars ?g r)"
    using nf_rename_args[OF closed_u r(1,2) refl zs] by simp
  have idx: "Unification.idx zs y = Some (the (Unification.idx zs y))"
    "the (Unification.idx zs y) < ?m" "?g (the (Unification.idx zs y)) = y" if "y \<in> set ys" for y
    using that sub idx_None_iff[of zs y] idx_SomeD[of zs y] by auto
  have ks_g: "map ?g ?ks = ys" using idx(3) by (induction ys) auto
  have mapa: "map_BVars ?g (w \<degree>\<degree> map BVar ?ks) = w \<degree>\<degree> map BVar ys"
    unfolding map_BVars_closed_app[OF closed_w] ks_g by (rule refl)
  have tya: "(env_ext E ?Ts, \<tau>') \<turnstile> w \<degree>\<degree> map BVar ?ks : U"
  proof -
    have "(env_ext E ?Ts, \<tau>') \<turnstile> map_BVars (\<lambda>y. the (Unification.idx zs y)) (w \<degree>\<degree> map BVar ys) : U"
    proof (rule typing_map_BVars[OF tyw])
      fix v assume "v \<in> loose_BVars (w \<degree>\<degree> map BVar ys)"
      then have v: "v \<in> set ys" using no_loose_bound_loose_BVars[OF closed_w] by simp
      then show "env_ext E ?Ts (the (Unification.idx zs v)) = E v"
        using idx[OF v] by (simp add: env_ext_less)
    qed
    then show ?thesis unfolding map_BVars_closed_app[OF closed_w] .
  qed
  have "map_BVars ?g (w \<degree>\<degree> map BVar ?ks) \<equiv>\<^sub>\<beta>\<^sub>\<eta> map_BVars ?g r"
    unfolding mapa using equiv_sym[OF eq] \<beta>\<eta>cl_into_equiv[OF nr] by (rule equiv_trans)
  moreover have "inj_on ?g (loose_BVars (w \<degree>\<degree> map BVar ?ks) \<union> loose_BVars r)"
  proof (rule inj_on_subset)
    show "inj_on ?g {..<?m}" using zs by (auto simp: inj_on_def nth_eq_iff_index_eq)
    show "loose_BVars (w \<degree>\<degree> map BVar ?ks) \<union> loose_BVars r \<subseteq> {..<?m}"
      using r(4) idx(2) no_loose_bound_loose_BVars[OF closed_w] by auto
  qed
  ultimately have "w \<degree>\<degree> map BVar ?ks \<equiv>\<^sub>\<beta>\<^sub>\<eta> r" by (rule map_BVars_equiv_reflect[OF _ _ tya r(3)])
  have "u \<equiv>\<^sub>\<beta>\<^sub>\<eta> Abs_m ?m (u \<degree>\<degree> map BVar (downs ?m))"
    using eta_expand_equiv[OF closed_u] by (rule equiv_sym)
  also have "\<dots> \<equiv>\<^sub>\<beta>\<^sub>\<eta> Abs_m ?m r" using r(1) by (intro equiv_Abs_m \<beta>\<eta>cl_into_equiv)
  also have "\<dots> \<equiv>\<^sub>\<beta>\<^sub>\<eta> Abs_m ?m (w \<degree>\<degree> map BVar ?ks)"
    using \<open>w \<degree>\<degree> map BVar ?ks \<equiv>\<^sub>\<beta>\<^sub>\<eta> r\<close> by (rule equiv_Abs_m[OF equiv_sym])
  finally show ?thesis .
qed

end

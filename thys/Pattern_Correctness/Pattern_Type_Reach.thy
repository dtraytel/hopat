section \<open>Reachability of Type Variables in Type Unification\<close>

theory Pattern_Type_Reach
  imports Pattern_Types Pattern_Signature
begin

text \<open>
  The unbound type variables reachable from a set \<open>K\<close> of type variables (with sorts) are those
  of the normal forms of the variables in \<open>K\<close>. A set \<open>P\<close> is covered by \<open>K\<close> if the unbound
  variables reachable from \<open>P\<close> are reachable from \<open>K\<close>. Type unification (\<^const>\<open>unify_aux\<close>)
  preserves the coverage of the variables of the environment, and it does not increase the
  number of unbound variables reachable from \<open>K\<close>. It also preserves certified sorts of the
  binding types.
\<close>


subsection \<open>Coverage\<close>

definition uvarsA :: "tyenv \<Rightarrow> (indexname \<times> psort) set \<Rightarrow> indexname set" where
  "uvarsA \<theta> K = (\<Union>(v, S)\<in>K. uvars \<theta> (TVar v S))"

definition tcovered :: "tyenv \<Rightarrow> (indexname \<times> psort) set \<Rightarrow> (indexname \<times> psort) set \<Rightarrow> bool" where
  "tcovered \<theta> K P \<longleftrightarrow> (\<forall>(v, S)\<in>P. uvars \<theta> (TVar v S) \<subseteq> uvarsA \<theta> K)"

lemma tcoveredD: "tcovered \<theta> K P \<Longrightarrow> (v, S) \<in> P \<Longrightarrow> uvars \<theta> (TVar v S) \<subseteq> uvarsA \<theta> K"
  unfolding tcovered_def by blast

lemma tcovered_Un[simp]: "tcovered \<theta> K (P \<union> Q) \<longleftrightarrow> tcovered \<theta> K P \<and> tcovered \<theta> K Q"
  and tcovered_insert[simp]:
    "tcovered \<theta> K (insert (v, S) P) \<longleftrightarrow> uvars \<theta> (TVar v S) \<subseteq> uvarsA \<theta> K \<and> tcovered \<theta> K P"
  and tcovered_empty[simp]: "tcovered \<theta> K {}"
  by (auto simp: tcovered_def)

lemma tcovered_mono: "tcovered \<theta> K P \<Longrightarrow> Q \<subseteq> P \<Longrightarrow> tcovered \<theta> K Q"
  unfolding tcovered_def by blast

lemma uvars_tvars_Union: "uvars \<theta> T = (\<Union>(w, S)\<in>tvars T. uvars \<theta> (TVar w S))"
proof -
  have "uvars \<theta> T = fst ` tvars (tsubst (\<lambda>w S. tnorm \<theta> (TVar w S)) T)"
    by (simp add: uvars_def flip: tnorm_tsubst)
  then show ?thesis by (auto simp: tvars_tsubst uvars_def)
qed

lemma tcovered_tvars: "tcovered \<theta> K (tvars T) \<longleftrightarrow> uvars \<theta> T \<subseteq> uvarsA \<theta> K"
  unfolding tcovered_def uvars_tvars_Union[of \<theta> T] by blast

lemma uvarsA_textends:
  assumes ac: "tacyc \<theta>'" and ext: "textends \<theta> \<theta>'"
  shows "uvarsA \<theta>' K =
    (\<Union>w\<in>uvarsA \<theta> K. case vt_lookup \<theta>' w of None \<Rightarrow> {w} | Some (S', U) \<Rightarrow> uvars \<theta>' U)"
  unfolding uvarsA_def by (auto simp: uvars_textends[OF ac ext, of "TVar _ _"])

lemma tcovered_textends:
  assumes ac: "tacyc \<theta>'" and ext: "textends \<theta> \<theta>'" and c: "tcovered \<theta> K P"
  shows "tcovered \<theta>' K P"
  unfolding tcovered_def
proof (intro ballI)
  fix p assume p: "p \<in> P"
  obtain v S where vS: "p = (v, S)" by (cases p) blast
  have sub: "uvars \<theta> (TVar v S) \<subseteq> uvarsA \<theta> K" using tcoveredD[OF c] p vS by blast
  have "uvars \<theta>' (TVar v S) \<subseteq> uvarsA \<theta>' K"
    unfolding uvarsA_textends[OF ac ext] uvars_textends[OF ac ext, of "TVar v S"]
    using sub by blast
  then show "case p of (v, S) \<Rightarrow> uvars \<theta>' (TVar v S) \<subseteq> uvarsA \<theta>' K" by (simp add: vS)
qed

lemma uvarsA_bound:
  assumes ac: "tacyc \<theta>'" and ext: "textends \<theta> \<theta>'"
    and v: "v \<in> uvarsA \<theta> K" "vt_lookup \<theta>' v = Some (S, W)"
  shows "uvars \<theta>' W \<subseteq> uvarsA \<theta>' K"
proof -
  have "(case vt_lookup \<theta>' v of None \<Rightarrow> {v} | Some (S', U) \<Rightarrow> uvars \<theta>' U) = uvars \<theta>' W"
    using v(2) by simp
  then show ?thesis using v(1) unfolding uvarsA_textends[OF ac ext] by blast
qed

lemma tcovered_update:
  assumes ac: "tacyc (vt_update (v, (S, W)) \<theta>)" and v: "vt_lookup \<theta> v = None"
    and c: "tcovered \<theta> K P" "(v, S) \<in> P" "tvars_env \<theta> \<subseteq> P"
  shows "tcovered (vt_update (v, (S, W)) \<theta>) K (P \<union> tvars_env (vt_update (v, (S, W)) \<theta>))"
proof -
  let ?\<theta>' = "vt_update (v, (S, W)) \<theta>"
  have ext: "textends \<theta> ?\<theta>'" by (rule textends_update[OF v])
  have ac0: "tacyc \<theta>" by (rule tacyc_textends[OF ext ac])
  have "v \<in> uvarsA \<theta> K" using tcoveredD[OF c(1,2)] by (simp add: uvars_TVar[OF ac0] v)
  then have "uvars ?\<theta>' W \<subseteq> uvarsA ?\<theta>' K" by (rule uvarsA_bound[OF ac ext]) simp
  then have W: "tcovered ?\<theta>' K (tvars W)" by (simp add: tcovered_tvars)
  have P: "tcovered ?\<theta>' K P" by (rule tcovered_textends[OF ac ext c(1)])
  have "P \<union> tvars_env ?\<theta>' = P \<union> tvars W" using c(2,3) by (auto simp: tvars_env_update[OF v])
  then show ?thesis using P W by simp
qed


subsection \<open>Sorts of free type variables\<close>

fun fsorts_ok :: "algebra \<Rightarrow> ptyp \<Rightarrow> bool" where
  "fsorts_ok alg (Type a Ts) \<longleftrightarrow> (\<forall>T\<in>set Ts. fsorts_ok alg T)"
| "fsorts_ok alg (TFree a S) \<longleftrightarrow> sort_ok alg S"
| "fsorts_ok alg (TVar v S) \<longleftrightarrow> True"

lemma sorts_ok_fsorts: "sorts_ok alg T \<longleftrightarrow> fsorts_ok alg T \<and> tcert alg (tvars T)"
  by (induction T) (auto simp: tcert_def)

definition scert :: "algebra \<Rightarrow> tyenv \<Rightarrow> bool" where
  "scert alg \<theta> \<longleftrightarrow> (\<forall>v S U. vt_lookup \<theta> v = Some (S, U) \<longrightarrow> sorts_ok alg U)"

definition fscert :: "algebra \<Rightarrow> tyenv \<Rightarrow> bool" where
  "fscert alg \<theta> \<longleftrightarrow> (\<forall>v S U. vt_lookup \<theta> v = Some (S, U) \<longrightarrow> fsorts_ok alg U)"

lemma renames_new_TVar:
  assumes ac: "tacyc \<theta>'" and r: "renames \<theta> \<theta>'"
    and v: "vt_lookup \<theta> v = None" "vt_lookup \<theta>' v = Some (S, W)"
  shows "\<exists>u S'. W = TVar u S'"
proof -
  obtain u S' where "tnorm \<theta>' (TVar v S) = TVar u S'" using r v(1) unfolding renames_def by blast
  then have "tnorm \<theta>' W = TVar u S'" using v(2) by (simp add: tnorm_TVar[OF ac])
  then show ?thesis by (cases W) auto
qed


subsection \<open>Auxiliary facts\<close>

lemma bindM_eq_returnE: "bindM m f = return y \<Longrightarrow> \<exists>x. m = return x \<and> f x = return y"
  by (auto simp: bindM_def return_def split: option.splits res.splits)

context wf_algebra
begin

lemma meet_ok_return:
  assumes "tinv ar n \<theta> A" "tvars T \<subseteq> tvars_env \<theta> \<union> A" "wft ar T" "\<not> tbound \<theta> T"
    "tcert alg (tvars_env \<theta> \<union> A) \<longrightarrow> sort_ok alg S"
    and m: "meet alg T S (\<theta>, n) = return (\<theta>', n')"
  shows "tstep alg ar A (\<lambda>\<rho>. has_sort alg (tsubst \<rho> T) S) \<theta> n \<theta>' n'" "renames \<theta> \<theta>'"
  using meet_ok[OF assms(1-5)] m by auto

lemma unify_aux_ok_return:
  assumes "tinv ar n \<theta> A" "tvars T \<subseteq> tvars_env \<theta> \<union> A" "tvars U \<subseteq> tvars_env \<theta> \<union> A"
    "wft ar T" "wft ar U"
    and u: "unify_aux alg T U (\<theta>, n) = return (\<theta>', n')"
  shows "tstep alg ar A (\<lambda>\<rho>. tsubst \<rho> T = tsubst \<rho> U) \<theta> n \<theta>' n'"
    "\<forall>X. uvars \<theta> T \<union> uvars \<theta> U \<subseteq> uvars \<theta> X \<longrightarrow> \<theta>' = \<theta> \<or> card (uvars \<theta>' X) < card (uvars \<theta> X)"
  using unify_aux_ok[OF assms(1-5)] u by auto


subsection \<open>Coverage and \<^const>\<open>meet\<close>\<close>

lemma meet_covered:
  assumes "tinv ar n \<theta> A" "tvars T \<subseteq> tvars_env \<theta> \<union> A" "wft ar T" "\<not> tbound \<theta> T"
    "tcert alg (tvars_env \<theta> \<union> A) \<longrightarrow> sort_ok alg S"
    "tcovered \<theta> K (tvars_env \<theta>)" "tcovered \<theta> K (tvars T)"
    "meet alg T S (\<theta>, n) = return (\<theta>', n')"
  shows "tcovered \<theta>' K (tvars_env \<theta>')"
  using assms
proof (induction "size (tnorm \<theta> T)" arbitrary: \<theta> n T S \<theta>' n' rule: less_induct)
  case less
  note inv = less.prems(1)
  have ac: "tacyc \<theta>" by (rule tinv_tacyc[OF inv])
  note cov = less.prems(6,7)
  have s: "tstep alg ar A (\<lambda>\<rho>. has_sort alg (tsubst \<rho> T) S) \<theta> n \<theta>' n'"
    by (rule meet_ok_return(1)[OF less.prems(1-5,8)])
  have ac': "tacyc \<theta>'" by (rule tinv_tacyc[OF tstepD(3)[OF s]])
  show ?case
  proof (cases "S = []")
    case True
    then have "meet alg T S (\<theta>, n) = return (\<theta>, n)" by (subst meet.simps) simp
    then have "\<theta>' = \<theta>" using less.prems(8) by simp
    then show ?thesis using cov by simp
  next
    case S: False
    show ?thesis
    proof (cases T)
      case (TVar xi S')
      have xi: "vt_lookup \<theta> xi = None" using less.prems(4) TVar by (cases "vt_lookup \<theta> xi") auto
      show ?thesis
      proof (cases "sort_le alg S' S")
        case True
        then have "meet alg T S (\<theta>, n) = return (\<theta>, n)" using TVar S by (subst meet.simps) simp
        then have "\<theta>' = \<theta>" using less.prems(8) by simp
        then show ?thesis using cov by simp
      next
        case False
        define V where "V = TVar (aT, n + 1) (inter_sort alg S' S)"
        have "meet alg T S (\<theta>, n) = return (vt_update (xi, (S', V)) \<theta>, n + 1)"
          using TVar S False xi
          by (subst meet.simps) (simp add: gen_tyvar_def update_new_def vt_defined_lookup V_def)
        then have \<theta>': "\<theta>' = vt_update (xi, (S', V)) \<theta>" using less.prems(8) by simp
        have "tcovered \<theta>' K (insert (xi, S') (tvars_env \<theta>) \<union> tvars_env \<theta>')"
          unfolding \<theta>' by (rule tcovered_update[OF ac'[unfolded \<theta>'] xi]) (use cov TVar in auto)
        then show ?thesis by simp
      qed
    next
      case (TFree a S')
      have "meet alg T S (\<theta>, n) = (if sort_le alg S' S then return (\<theta>, n) else raise TUnify)"
        using TFree S by (subst meet.simps) simp
      then have "\<theta>' = \<theta>" using less.prems(8) by (simp split: if_splits)
      then show ?thesis using cov by simp
    next
      case (Type a Ts)
      have wT: "length Ts = tarity ar a" "\<forall>Ti\<in>set Ts. wft ar Ti" using less.prems(3) Type by simp_all
      define f where "f = (\<lambda>(T, S) st. do {T' \<leftarrow> devar (fst st) T; meet alg T' S st})"
      have "meet alg T S (\<theta>, n) = bindM (mg_domain_unif alg a S) (\<lambda>Ss. foldM f (zip Ts Ss) (\<theta>, n))"
        using Type S by (subst meet.simps) (simp add: f_def)
      then have "bindM (mg_domain_unif alg a S) (\<lambda>Ss. foldM f (zip Ts Ss) (\<theta>, n)) = return (\<theta>', n')"
        using less.prems(8) by simp
      then obtain Ds where md: "mg_domain_unif alg a S = return Ds"
        and fo: "foldM f (zip Ts Ds) (\<theta>, n) = return (\<theta>', n')"
        by (blast dest: bindM_eq_returnE)
      have Ds: "mg_domain alg a S = return Ds"
        using md by (auto simp: mg_domain_unif_def handle_def return_def raise_def
            split: option.splits res.splits exn.splits)
      have fold: "tcovered \<theta>2 K (tvars_env \<theta>2)"
        if "set ps \<subseteq> set (zip Ts Ds)" "tinv ar n1 \<theta>1 A" "textends \<theta> \<theta>1" "renames \<theta> \<theta>1"
          "tcovered \<theta>1 K (tvars_env \<theta>1)" "tcovered \<theta>1 K (tvars T)"
          "foldM f ps (\<theta>1, n1) = return (\<theta>2, n2)"
        for ps \<theta>1 n1 \<theta>2 n2
        using that
      proof (induction ps arbitrary: \<theta>1 n1)
        case Nil
        then show ?case by simp
      next
        case (Cons p ps \<theta>1 n1)
        obtain Ti Di where p: "p = (Ti, Di)" by force
        have Ti: "Ti \<in> set Ts" using Cons.prems(1) p by (auto dest: set_zip_leftD)
        have inv1: "tinv ar n1 \<theta>1 A" by (rule Cons.prems(2))
        have ac1: "tacyc \<theta>1" by (rule tinv_tacyc[OF inv1])
        have TiA: "tvars Ti \<subseteq> tvars_env \<theta>1 \<union> A"
          using less.prems(2) Type Ti tvars_env_textends[OF Cons.prems(3)] by fastforce
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
        obtain st where m: "meet alg Ti' Di (\<theta>1, n1) = return st" and m2: "foldM f ps st = return (\<theta>2, n2)"
          using bindM_eq_returnE[OF Cons.prems(7)[unfolded fstep]] by blast
        obtain \<theta>m nm where st: "st = (\<theta>m, nm)" by force
        have "Di \<in> set Ds" using Cons.prems(1) p by (auto dest: set_zip_rightD)
        then have Di: "sort_ok alg Di" by (rule mg_domain_sorts_ok[OF Ds])
        have Di': "tcert alg (tvars_env \<theta>1 \<union> A) \<longrightarrow> sort_ok alg Di" using Di by blast
        have "tcovered \<theta>1 K (tvars Ti)"
          by (rule tcovered_mono[OF Cons.prems(6)]) (use Ti Type in auto)
        then have covTi: "tcovered \<theta>1 K (tvars Ti')" using Ti'(2) by (simp add: tcovered_tvars uvars_def)
        have s1: "tstep alg ar A (\<lambda>\<rho>. has_sort alg (tsubst \<rho> Ti') Di) \<theta>1 n1 \<theta>m nm"
          and r1: "renames \<theta>1 \<theta>m"
          using meet_ok_return[OF inv1 Ti'(4,5,3) Di' m[unfolded st]] by blast+
        have cm: "tcovered \<theta>m K (tvars_env \<theta>m)"
          by (rule less.hyps[OF sz inv1 Ti'(4,5,3) Di' Cons.prems(5) covTi m[unfolded st]])
        have inv2: "tinv ar nm \<theta>m A" by (rule tstepD(3)[OF s1])
        have ac2: "tacyc \<theta>m" by (rule tinv_tacyc[OF inv2])
        have ext12: "textends \<theta>1 \<theta>m" by (rule tstepD(1)[OF s1])
        have ext2: "textends \<theta> \<theta>m" by (rule textends_trans[OF Cons.prems(3) ext12])
        have ren2: "renames \<theta> \<theta>m" by (rule renames_trans[OF ac2 ext12 Cons.prems(3,4) r1])
        have covT: "tcovered \<theta>m K (tvars T)" by (rule tcovered_textends[OF ac2 ext12 Cons.prems(6)])
        have pss: "set ps \<subseteq> set (zip Ts Ds)" using Cons.prems(1) by simp
        show ?case by (rule Cons.IH[OF pss inv2 ext2 ren2 cm covT m2[unfolded st]])
      qed
      show ?thesis by (rule fold[OF order_refl inv textends_refl renames_refl[OF ac] cov fo])
    qed
  qed
qed


subsection \<open>Invariants preserved by \<^const>\<open>unify_aux\<close>\<close>

text \<open>
  A generic preservation result: an invariant \<open>Inv\<close> of the environment is preserved if it is
  preserved by single bindings and by \<^const>\<open>meet\<close>, where \<open>Rt\<close> is a property of the types to be
  unified, which is preserved by extensions, dereferencing and taking components.
\<close>

lemma unify_aux_preserves:
  fixes Inv :: "tyenv \<Rightarrow> bool" and Rt :: "tyenv \<Rightarrow> ptyp \<Rightarrow> bool"
  assumes mono: "\<And>\<theta> \<theta>' T. tacyc \<theta>' \<Longrightarrow> textends \<theta> \<theta>' \<Longrightarrow> Rt \<theta> T \<Longrightarrow> Rt \<theta>' T"
    and dv: "\<And>\<theta> n T T'. tinv ar n \<theta> A \<Longrightarrow> tvars T \<subseteq> tvars_env \<theta> \<union> A \<Longrightarrow> Inv \<theta> \<Longrightarrow> Rt \<theta> T \<Longrightarrow>
      devar \<theta> T = return T' \<Longrightarrow> tnorm \<theta> T' = tnorm \<theta> T \<Longrightarrow> Rt \<theta> T'"
    and sub: "\<And>\<theta> a Ts T. Rt \<theta> (Type a Ts) \<Longrightarrow> T \<in> set Ts \<Longrightarrow> Rt \<theta> T"
    and bind: "\<And>\<theta> v S W. tacyc (vt_update (v, (S, W)) \<theta>) \<Longrightarrow> vt_lookup \<theta> v = None \<Longrightarrow> Inv \<theta> \<Longrightarrow>
      Rt \<theta> (TVar v S) \<Longrightarrow> Rt \<theta> W \<or> (\<exists>u S'. W = TVar u S') \<Longrightarrow> Inv (vt_update (v, (S, W)) \<theta>)"
    and mt: "\<And>\<theta> n T S \<theta>' n'. tinv ar n \<theta> A \<Longrightarrow> tvars T \<subseteq> tvars_env \<theta> \<union> A \<Longrightarrow> wft ar T \<Longrightarrow>
      \<not> tbound \<theta> T \<Longrightarrow> (tcert alg (tvars_env \<theta> \<union> A) \<longrightarrow> sort_ok alg S) \<Longrightarrow> Inv \<theta> \<Longrightarrow> Rt \<theta> T \<Longrightarrow>
      meet alg T S (\<theta>, n) = return (\<theta>', n') \<Longrightarrow> Inv \<theta>'"
    and inv: "tinv ar n \<theta> A" and tvT: "tvars T \<subseteq> tvars_env \<theta> \<union> A" and tvU: "tvars U \<subseteq> tvars_env \<theta> \<union> A"
    and wfT: "wft ar T" and wfU: "wft ar U" and I: "Inv \<theta>" and RT: "Rt \<theta> T" and RU: "Rt \<theta> U"
    and u: "unify_aux alg T U (\<theta>, n) = return (\<theta>', n')"
  shows "Inv \<theta>'"
  using inv tvT tvU wfT wfU I RT RU u
proof (induction "(card (uvars \<theta> T \<union> uvars \<theta> U), size (tnorm \<theta> T))" arbitrary: \<theta> n T U \<theta>' n'
    rule: wf_induct_rule[OF wf_lex_prod[OF wf_less_than wf_less_than], case_names less])
  case less
  note inv = less.prems(1)
  note I = less.prems(6)
  have ac: "tacyc \<theta>" by (rule tinv_tacyc[OF inv])
  have tc: "tcons_env \<theta>" by (rule tinv_tcons_env[OF inv])
  obtain T' where T': "devar \<theta> T = return T'" "tnorm \<theta> T' = tnorm \<theta> T" "\<not> tbound \<theta> T'"
    "tvars T' \<subseteq> tvars_env \<theta> \<union> A" "wft ar T'"
    by (rule tinv_devar[OF inv less.prems(2,4)])
  obtain U' where U': "devar \<theta> U = return U'" "tnorm \<theta> U' = tnorm \<theta> U" "\<not> tbound \<theta> U'"
    "tvars U' \<subseteq> tvars_env \<theta> \<union> A" "wft ar U'"
    by (rule tinv_devar[OF inv less.prems(3,5)])
  have RT': "Rt \<theta> T'" by (rule dv[OF inv less.prems(2,6,7) T'(1,2)])
  have RU': "Rt \<theta> U'" by (rule dv[OF inv less.prems(3,6,8) U'(1,2)])
  have uT: "uvars \<theta> T' = uvars \<theta> T" and uU: "uvars \<theta> U' = uvars \<theta> U"
    by (simp_all add: uvars_def T'(2) U'(2))
  let ?R = "unify_aux alg T U (\<theta>, n)"
  have u: "?R = return (\<theta>', n')" by (rule less.prems(9))
  consider (VV) v S1 w S2 where "T' = TVar v S1" "U' = TVar w S2"
    | (VN) v S where "T' = TVar v S" "\<And>w S'. U' \<noteq> TVar w S'"
    | (NV) w S where "U' = TVar w S" "\<And>v S'. T' \<noteq> TVar v S'"
    | (TT) a Ts b Us where "T' = Type a Ts" "U' = Type b Us"
    | (FF) "\<And>v S. T' \<noteq> TVar v S" "\<And>v S. U' \<noteq> TVar v S" "\<And>a Ts b Us. T' = Type a Ts \<Longrightarrow> U' \<noteq> Type b Us"
    by (cases T'; cases U') auto
  then show ?case
  proof cases
    case (VV v S1 w S2)
    have v: "vt_lookup \<theta> v = None" "(v, S1) \<in> tvars_env \<theta> \<union> A" using T'(3,4) VV by (auto simp del: not_None_eq)
    have w: "vt_lookup \<theta> w = None" "(w, S2) \<in> tvars_env \<theta> \<union> A" using U'(3,4) VV by (auto simp del: not_None_eq)
    show ?thesis
    proof (cases "v = w")
      case True
      then have "S1 = S2" using v(2) w(2) inv unfolding tinv_def scons_def by blast
      then have "?R = return (\<theta>, n)" using True by (subst unify_aux.simps) (simp add: T'(1) U'(1) VV)
      then show ?thesis using u I by simp
    next
      case vw: False
      show ?thesis
      proof (cases "sort_le alg S1 S2")
        case le: True
        note b = bind_var_ok[OF inv v w vw le]
        have "?R = return (vt_update (w, (S2, TVar v S1)) \<theta>, n)"
          using vw le w(1) by (subst unify_aux.simps) (simp add: T'(1) U'(1) VV update_new_def vt_defined_lookup)
        then have \<theta>': "\<theta>' = vt_update (w, (S2, TVar v S1)) \<theta>" using u by simp
        have ac': "tacyc (vt_update (w, (S2, TVar v S1)) \<theta>)" by (rule tinv_tacyc[OF tstepD(3)[OF b(1)]])
        show ?thesis unfolding \<theta>' by (rule bind[OF ac' w(1) I]) (use RU' VV in auto)
      next
        case nle: False
        show ?thesis
        proof (cases "sort_le alg S2 S1")
          case le: True
          note b = bind_var_ok[OF inv w v vw[symmetric] le]
          have "?R = return (vt_update (v, (S1, TVar w S2)) \<theta>, n)"
            using vw le nle v(1)
            by (subst unify_aux.simps) (simp add: T'(1) U'(1) VV update_new_def vt_defined_lookup)
          then have \<theta>': "\<theta>' = vt_update (v, (S1, TVar w S2)) \<theta>" using u by simp
          have ac': "tacyc (vt_update (v, (S1, TVar w S2)) \<theta>)" by (rule tinv_tacyc[OF tstepD(3)[OF b(1)]])
          show ?thesis unfolding \<theta>' by (rule bind[OF ac' v(1) I]) (use RT' VV in auto)
        next
          case nle2: False
          note b = bind_new_ok[OF inv v w vw]
          let ?V = "TVar (aT, n + 1) (inter_sort alg S1 S2)"
          let ?\<theta>1 = "vt_update (w, (S2, ?V)) \<theta>"
          let ?\<theta>2 = "vt_update (v, (S1, ?V)) ?\<theta>1"
          have "?R = return (?\<theta>2, n + 1)"
            using vw nle nle2 v(1) w(1)
            by (subst unify_aux.simps) (simp add: T'(1) U'(1) VV update_new_def vt_defined_lookup gen_tyvar_def)
          then have \<theta>': "\<theta>' = ?\<theta>2" using u by simp
          have ac2: "tacyc ?\<theta>2" by (rule tinv_tacyc[OF tstepD(3)[OF b(1)]])
          have v1: "vt_lookup ?\<theta>1 v = None" using v(1) vw by simp
          have ext12: "textends ?\<theta>1 ?\<theta>2" by (rule textends_update[OF v1])
          have ac1: "tacyc ?\<theta>1" by (rule tacyc_textends[OF ext12 ac2])
          have ext1: "textends \<theta> ?\<theta>1" by (rule textends_update[OF w(1)])
          have I1: "Inv ?\<theta>1" by (rule bind[OF ac1 w(1) I]) (use RU' VV in auto)
          have "Rt ?\<theta>1 (TVar v S1)" by (rule mono[OF ac1 ext1]) (use RT' VV in simp)
          then have "Inv ?\<theta>2" by (intro bind[OF ac2 v1 I1]) auto
          then show ?thesis by (simp add: \<theta>')
        qed
      qed
    qed
  next
    case (VN v S)
    have v: "vt_lookup \<theta> v = None" "(v, S) \<in> tvars_env \<theta> \<union> A" using T'(3,4) VN by (auto simp del: not_None_eq)
    have Req: "?R = do {b \<leftarrow> type_occurs v \<theta> U';
        if b then raise TUnify else do {\<theta>1 \<leftarrow> update_new (v, (S, U')) \<theta>; meet alg U' S (\<theta>1, n)}}"
      using VN by (subst unify_aux.simps) (simp add: T'(1) U'(1) split: ptyp.split)
    have tcU: "tcons \<theta> U'" by (rule tinv_tcons[OF inv U'(4)])
    show ?thesis
    proof (cases "v \<in> uvars \<theta> U'")
      case True
      then have "?R = raise TUnify" using Req by (simp add: type_occurs_ok[OF ac tc tcU v(1)] uvars_def)
      then show ?thesis using u by simp
    next
      case False
      define \<theta>1 where "\<theta>1 = vt_update (v, (S, U')) \<theta>"
      have inv1: "tinv ar n \<theta>1 A" unfolding \<theta>1_def by (rule tinv_update[OF inv v(1) False v(2) U'(5,4)])
      have ac1: "tacyc \<theta>1" by (rule tinv_tacyc[OF inv1])
      have ext1: "textends \<theta> \<theta>1" by (simp add: \<theta>1_def textends_update v(1))
      have lk1: "vt_lookup \<theta>1 v = Some (S, U')" by (simp add: \<theta>1_def)
      have U1: "tvars U' \<subseteq> tvars_env \<theta>1 \<union> A" using U'(4) tvars_env_textends[OF ext1] by blast
      have nb: "\<not> tbound \<theta>1 U'" using VN(2) by (cases U') auto
      have "?R = meet alg U' S (\<theta>1, n)"
        using Req False by (simp add: type_occurs_ok[OF ac tc tcU v(1)] uvars_def update_new_def
            vt_defined_lookup v(1) \<theta>1_def)
      then have m: "meet alg U' S (\<theta>1, n) = return (\<theta>', n')" using u by simp
      have Sok: "tcert alg (tvars_env \<theta>1 \<union> A) \<longrightarrow> sort_ok alg S"
        using tvars_envI[OF lk1] by (blast intro: tcertD)
      have I1: "Inv \<theta>1" unfolding \<theta>1_def by (rule bind[OF ac1[unfolded \<theta>1_def] v(1) I]) (use RT' RU' VN in auto)
      have RU1: "Rt \<theta>1 U'" by (rule mono[OF ac1 ext1 RU'])
      show ?thesis by (rule mt[OF inv1 U1 U'(5) nb Sok I1 RU1 m])
    qed
  next
    case (NV w S)
    have w: "vt_lookup \<theta> w = None" "(w, S) \<in> tvars_env \<theta> \<union> A" using U'(3,4) NV by (auto simp del: not_None_eq)
    have Req: "?R = do {b \<leftarrow> type_occurs w \<theta> T';
        if b then raise TUnify else do {\<theta>1 \<leftarrow> update_new (w, (S, T')) \<theta>; meet alg T' S (\<theta>1, n)}}"
      using NV by (subst unify_aux.simps) (simp add: T'(1) U'(1) split: ptyp.split)
    have tcT: "tcons \<theta> T'" by (rule tinv_tcons[OF inv T'(4)])
    show ?thesis
    proof (cases "w \<in> uvars \<theta> T'")
      case True
      then have "?R = raise TUnify" using Req by (simp add: type_occurs_ok[OF ac tc tcT w(1)] uvars_def)
      then show ?thesis using u by simp
    next
      case False
      define \<theta>1 where "\<theta>1 = vt_update (w, (S, T')) \<theta>"
      have inv1: "tinv ar n \<theta>1 A" unfolding \<theta>1_def by (rule tinv_update[OF inv w(1) False w(2) T'(5,4)])
      have ac1: "tacyc \<theta>1" by (rule tinv_tacyc[OF inv1])
      have ext1: "textends \<theta> \<theta>1" by (simp add: \<theta>1_def textends_update w(1))
      have lk1: "vt_lookup \<theta>1 w = Some (S, T')" by (simp add: \<theta>1_def)
      have T1: "tvars T' \<subseteq> tvars_env \<theta>1 \<union> A" using T'(4) tvars_env_textends[OF ext1] by blast
      have nb: "\<not> tbound \<theta>1 T'" using NV(2) by (cases T') auto
      have "?R = meet alg T' S (\<theta>1, n)"
        using Req False by (simp add: type_occurs_ok[OF ac tc tcT w(1)] uvars_def update_new_def
            vt_defined_lookup w(1) \<theta>1_def)
      then have m: "meet alg T' S (\<theta>1, n) = return (\<theta>', n')" using u by simp
      have Sok: "tcert alg (tvars_env \<theta>1 \<union> A) \<longrightarrow> sort_ok alg S"
        using tvars_envI[OF lk1] by (blast intro: tcertD)
      have I1: "Inv \<theta>1" unfolding \<theta>1_def by (rule bind[OF ac1[unfolded \<theta>1_def] w(1) I]) (use RT' RU' NV in auto)
      have RT1: "Rt \<theta>1 T'" by (rule mono[OF ac1 ext1 RT'])
      show ?thesis by (rule mt[OF inv1 T1 T'(5) nb Sok I1 RT1 m])
    qed
  next
    case (TT a Ts b Us)
    show ?thesis
    proof (cases "a = b")
      case False
      have "?R = raise TUnify" using False by (subst unify_aux.simps) (simp add: T'(1) U'(1) TT)
      then show ?thesis using u by simp
    next
      case True
      have len: "length Ts = tarity ar a" "length Us = tarity ar a" using T'(5) U'(5) TT True by auto
      define g where "g = (\<lambda>(T, U) st. unify_aux alg T U st)"
      have Req: "?R = foldM g (zip Ts Us) (\<theta>, n)"
        using True by (subst unify_aux.simps) (simp add: T'(1) U'(1) TT g_def)
      let ?PX = "Type a [T', U']"
      have uPX: "uvars \<theta> ?PX = uvars \<theta> T \<union> uvars \<theta> U" using uT uU by simp
      have sizes: "size (tnorm \<theta> Ti) < size (tnorm \<theta> T)" if "Ti \<in> set Ts" for Ti
      proof -
        have "size (tnorm \<theta> Ti) \<le> size_list size (map (tnorm \<theta>) Ts)"
          using that by (intro size_list_estimation'[of "tnorm \<theta> Ti"]) auto
        then show ?thesis using T'(2)[symmetric] by (simp add: TT)
      qed
      have fold: "Inv \<theta>2"
        if "set ps \<subseteq> set (zip Ts Us)" "tinv ar n1 \<theta>1 A" "textends \<theta> \<theta>1"
          "\<forall>X. uvars \<theta> T' \<union> uvars \<theta> U' \<subseteq> uvars \<theta> X \<longrightarrow> \<theta>1 = \<theta> \<or> card (uvars \<theta>1 X) < card (uvars \<theta> X)"
          "Inv \<theta>1" "foldM g ps (\<theta>1, n1) = return (\<theta>2, n2)"
        for ps \<theta>1 n1 \<theta>2 n2
        using that
      proof (induction ps arbitrary: \<theta>1 n1)
        case Nil
        then show ?case by simp
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
        then have mPX: "\<theta>1 = \<theta> \<or> card (uvars \<theta>1 ?PX) < card (uvars \<theta> ?PX)" using Cons.prems(4) by blast
        have c1: "card (uvars \<theta>1 Ti \<union> uvars \<theta>1 Ui) \<le> card (uvars \<theta>1 ?PX)"
          by (rule card_mono[OF finite_uvars sub1])
        have meas: "((card (uvars \<theta>1 Ti \<union> uvars \<theta>1 Ui), size (tnorm \<theta>1 Ti)),
            (card (uvars \<theta> T \<union> uvars \<theta> U), size (tnorm \<theta> T))) \<in> less_than <*lex*> less_than"
          using mPX c1 uPX sizes[OF Ti] by (auto simp: le_less)
        have fstep: "foldM g (p # ps) (\<theta>1, n1) = bindM (unify_aux alg Ti Ui (\<theta>1, n1)) (foldM g ps)"
          by (simp add: p g_def)
        obtain st where R1: "unify_aux alg Ti Ui (\<theta>1, n1) = return st" and R2: "foldM g ps st = return (\<theta>2, n2)"
          using bindM_eq_returnE[OF Cons.prems(6)[unfolded fstep]] by blast
        obtain \<theta>m nm where st: "st = (\<theta>m, nm)" by force
        have RTi: "Rt \<theta>1 Ti" by (rule mono[OF ac1 ext1 sub[OF RT'[unfolded TT] Ti]])
        have RUi: "Rt \<theta>1 Ui" by (rule mono[OF ac1 ext1 sub[OF RU'[unfolded TT] Ui]])
        note ok1 = unify_aux_ok_return[OF inv1 tvA[OF pz, simplified] wf R1[unfolded st]]
        have s1: "tstep alg ar A (\<lambda>\<rho>. tsubst \<rho> Ti = tsubst \<rho> Ui) \<theta>1 n1 \<theta>m nm" by (rule ok1(1))
        have m1: "\<forall>X. uvars \<theta>1 Ti \<union> uvars \<theta>1 Ui \<subseteq> uvars \<theta>1 X \<longrightarrow> \<theta>m = \<theta>1 \<or> card (uvars \<theta>m X) < card (uvars \<theta>1 X)"
          by (rule ok1(2))
        have Im: "Inv \<theta>m"
          by (rule less.hyps[OF meas inv1 tvA[OF pz, simplified] wf Cons.prems(5) RTi RUi R1[unfolded st]])
        have inv2: "tinv ar nm \<theta>m A" by (rule tstepD(3)[OF s1])
        have ext2: "textends \<theta> \<theta>m" by (rule textends_trans[OF ext1 tstepD(1)[OF s1]])
        have m2: "\<forall>X. uvars \<theta> T' \<union> uvars \<theta> U' \<subseteq> uvars \<theta> X \<longrightarrow> \<theta>m = \<theta> \<or> card (uvars \<theta>m X) < card (uvars \<theta> X)"
        proof (intro allI impI)
          fix X assume X: "uvars \<theta> T' \<union> uvars \<theta> U' \<subseteq> uvars \<theta> X"
          have "uvars \<theta> ?PX \<subseteq> uvars \<theta> X" using X by simp
          then have "uvars \<theta>1 ?PX \<subseteq> uvars \<theta>1 X" by (rule uvars_mono[OF ac1 ext1])
          then have "\<theta>m = \<theta>1 \<or> card (uvars \<theta>m X) < card (uvars \<theta>1 X)" using m1 sub1 by blast
          moreover have "\<theta>1 = \<theta> \<or> card (uvars \<theta>1 X) < card (uvars \<theta> X)" using Cons.prems(4) X by blast
          ultimately show "\<theta>m = \<theta> \<or> card (uvars \<theta>m X) < card (uvars \<theta> X)" by auto
        qed
        have pss: "set ps \<subseteq> set (zip Ts Us)" using Cons.prems(1) by simp
        show ?case by (rule Cons.IH[OF pss inv2 ext2 m2 Im R2[unfolded st]])
      qed
      show ?thesis by (rule fold[OF order_refl inv textends_refl _ I u[unfolded Req]]) simp
    qed
  next
    case FF
    have Req: "?R = (if T' = U' then return (\<theta>, n) else raise TUnify)"
      using FF by (subst unify_aux.simps) (simp add: T'(1) U'(1) split: ptyp.split, metis)
    then show ?thesis using u I by (cases "T' = U'") simp_all
  qed
qed


subsection \<open>Coverage is preserved by \<^const>\<open>unify_aux\<close>\<close>

lemma unify_aux_covered:
  assumes "tinv ar n \<theta> A" "tvars T \<subseteq> tvars_env \<theta> \<union> A" "tvars U \<subseteq> tvars_env \<theta> \<union> A" "wft ar T" "wft ar U"
    and "tcovered \<theta> K (tvars_env \<theta> \<union> tvars T \<union> tvars U)"
    and "unify_aux alg T U (\<theta>, n) = return (\<theta>', n')"
  shows "tcovered \<theta>' K (tvars_env \<theta>')"
proof -
  have c: "tcovered \<theta> K (tvars_env \<theta>)" "tcovered \<theta> K (tvars T)" "tcovered \<theta> K (tvars U)"
    using assms(6) by simp_all
  show ?thesis
  proof (rule unify_aux_preserves[where Inv = "\<lambda>\<theta>. tcovered \<theta> K (tvars_env \<theta>)"
        and Rt = "\<lambda>\<theta> T. tcovered \<theta> K (tvars T)", OF _ _ _ _ _ assms(1-5) c assms(7)])
    fix \<theta> \<theta>' T assume "tacyc \<theta>'" "textends \<theta> \<theta>'" "tcovered \<theta> K (tvars T)"
    then show "tcovered \<theta>' K (tvars T)" by (rule tcovered_textends)
  next
    fix \<theta> n T T'
    assume "tcovered \<theta> K (tvars T)" "tnorm \<theta> T' = tnorm \<theta> T"
    then show "tcovered \<theta> K (tvars T')" by (simp add: tcovered_tvars uvars_def)
  next
    fix \<theta> a Ts T assume "tcovered \<theta> K (tvars (Type a Ts))" "T \<in> set Ts"
    then show "tcovered \<theta> K (tvars T)" by (elim tcovered_mono) auto
  next
    fix \<theta> v S W
    assume ac: "tacyc (vt_update (v, (S, W)) \<theta>)" and v: "vt_lookup \<theta> v = None"
      and c: "tcovered \<theta> K (tvars_env \<theta>)" "tcovered \<theta> K (tvars (TVar v S))"
    have "tcovered (vt_update (v, (S, W)) \<theta>) K
        (insert (v, S) (tvars_env \<theta>) \<union> tvars_env (vt_update (v, (S, W)) \<theta>))"
      by (rule tcovered_update[OF ac v]) (use c in auto)
    then show "tcovered (vt_update (v, (S, W)) \<theta>) K (tvars_env (vt_update (v, (S, W)) \<theta>))" by simp
  next
    fix \<theta> n T S \<theta>' n'
    assume "tinv ar n \<theta> A" "tvars T \<subseteq> tvars_env \<theta> \<union> A" "wft ar T" "\<not> tbound \<theta> T"
      "tcert alg (tvars_env \<theta> \<union> A) \<longrightarrow> sort_ok alg S" "tcovered \<theta> K (tvars_env \<theta>)"
      "tcovered \<theta> K (tvars T)" "meet alg T S (\<theta>, n) = return (\<theta>', n')"
    then show "tcovered \<theta>' K (tvars_env \<theta>')" by (rule meet_covered)
  qed
qed

lemma unify_aux_card:
  assumes "tinv ar n \<theta> A" "tvars T \<subseteq> tvars_env \<theta> \<union> A" "tvars U \<subseteq> tvars_env \<theta> \<union> A" "wft ar T" "wft ar U"
    and fin: "finite K" and c: "tcovered \<theta> K (tvars_env \<theta> \<union> tvars T \<union> tvars U)"
    and u: "unify_aux alg T U (\<theta>, n) = return (\<theta>', n')"
  shows "\<theta>' = \<theta> \<or> card (uvarsA \<theta>' K) < card (uvarsA \<theta> K)"
proof -
  obtain xs where xs: "set xs = K" using finite_list[OF fin] by blast
  define X where "X = Type STR '''' (map (\<lambda>(v, S). TVar v S) xs)"
  have UX: "uvars \<theta>0 X = uvarsA \<theta>0 K" for \<theta>0 by (auto simp: X_def uvarsA_def xs[symmetric])
  have "uvars \<theta> T \<union> uvars \<theta> U \<subseteq> uvars \<theta> X"
    using c by (simp add: UX tcovered_tvars[symmetric])
  then have "\<theta>' = \<theta> \<or> card (uvars \<theta>' X) < card (uvars \<theta> X)"
    using unify_aux_ok_return(2)[OF assms(1-5) u] by blast
  then show ?thesis by (simp add: UX)
qed


subsection \<open>Certified sorts are preserved by \<^const>\<open>unify_aux\<close>\<close>

lemma meet_fscert:
  assumes "tinv ar n \<theta> A" "tvars T \<subseteq> tvars_env \<theta> \<union> A" "wft ar T" "\<not> tbound \<theta> T"
    "tcert alg (tvars_env \<theta> \<union> A) \<longrightarrow> sort_ok alg S"
    and f: "fscert alg \<theta>" and m: "meet alg T S (\<theta>, n) = return (\<theta>', n')"
  shows "fscert alg \<theta>'"
proof -
  note ok = meet_ok_return[OF assms(1-5) m]
  have ext: "textends \<theta> \<theta>'" by (rule tstepD(1)[OF ok(1)])
  have ac': "tacyc \<theta>'" by (rule tinv_tacyc[OF tstepD(3)[OF ok(1)]])
  show ?thesis unfolding fscert_def
  proof (intro allI impI)
    fix v S0 W assume lk: "vt_lookup \<theta>' v = Some (S0, W)"
    show "fsorts_ok alg W"
    proof (cases "vt_lookup \<theta> v")
      case None
      then obtain u S' where "W = TVar u S'" using renames_new_TVar[OF ac' ok(2) _ lk] by blast
      then show ?thesis by simp
    next
      case (Some x)
      then have "vt_lookup \<theta>' v = Some x" using ext unfolding textends_def by blast
      then have "vt_lookup \<theta> v = Some (S0, W)" using lk Some by simp
      then show ?thesis using f unfolding fscert_def by blast
    qed
  qed
qed

lemma unify_aux_fscert:
  assumes "tinv ar n \<theta> A" "tvars T \<subseteq> tvars_env \<theta> \<union> A" "tvars U \<subseteq> tvars_env \<theta> \<union> A" "wft ar T" "wft ar U"
    and "fscert alg \<theta>" "fsorts_ok alg T" "fsorts_ok alg U"
    and "unify_aux alg T U (\<theta>, n) = return (\<theta>', n')"
  shows "fscert alg \<theta>'"
proof (rule unify_aux_preserves[where Inv = "fscert alg" and Rt = "\<lambda>\<theta> T. fsorts_ok alg T",
      OF _ _ _ _ _ assms])
  fix \<theta> \<theta>' T assume "fsorts_ok alg T"
  then show "fsorts_ok alg T" .
next
  fix \<theta> n T T'
  assume inv: "tinv ar n \<theta> A" and T: "tvars T \<subseteq> tvars_env \<theta> \<union> A" and f: "fscert alg \<theta>"
    and fT: "fsorts_ok alg T" and d: "devar \<theta> T = return T'"
  show "fsorts_ok alg T'"
    by (rule devar_preserves[where P = "fsorts_ok alg", OF tinv_tacyc[OF inv] tinv_tcons_env[OF inv] _
          tinv_tcons[OF inv T] d fT])
      (use f in \<open>auto simp: fscert_def\<close>)
next
  fix \<theta> a Ts T assume "fsorts_ok alg (Type a Ts)" "T \<in> set Ts"
  then show "fsorts_ok alg T" by simp
next
  fix \<theta> v S W
  assume f: "fscert alg \<theta>" and W: "fsorts_ok alg W \<or> (\<exists>u S'. W = TVar u S')"
  have "fsorts_ok alg W" using W by auto
  then show "fscert alg (vt_update (v, (S, W)) \<theta>)" using f by (auto simp: fscert_def)
next
  fix \<theta> n T S \<theta>' n'
  assume "tinv ar n \<theta> A" "tvars T \<subseteq> tvars_env \<theta> \<union> A" "wft ar T" "\<not> tbound \<theta> T"
    "tcert alg (tvars_env \<theta> \<union> A) \<longrightarrow> sort_ok alg S" "fscert alg \<theta>"
    "meet alg T S (\<theta>, n) = return (\<theta>', n')"
  then show "fscert alg \<theta>'" by (rule meet_fscert)
qed

lemma unify_aux_scert:
  assumes "tinv ar n \<theta> A" "tvars T \<subseteq> tvars_env \<theta> \<union> A" "tvars U \<subseteq> tvars_env \<theta> \<union> A" "wft ar T" "wft ar U"
    and sc: "scert alg \<theta>" "sorts_ok alg T" "sorts_ok alg U" and tc: "tcert alg (tvars_env \<theta> \<union> A)"
    and u: "unify_aux alg T U (\<theta>, n) = return (\<theta>', n')"
  shows "scert alg \<theta>'"
proof -
  have f: "fscert alg \<theta>" using sc(1) by (auto simp: scert_def fscert_def sorts_ok_fsorts)
  have "fsorts_ok alg T" "fsorts_ok alg U" using sc(2,3) by (simp_all add: sorts_ok_fsorts)
  then have f': "fscert alg \<theta>'" by (rule unify_aux_fscert[OF assms(1-5) f _ _ u])
  have tc': "tcert alg (tvars_env \<theta>')"
    by (rule tstepD(6)[OF unify_aux_ok_return(1)[OF assms(1-5) u] tc])
  show ?thesis unfolding scert_def
  proof (intro allI impI)
    fix v S W assume lk: "vt_lookup \<theta>' v = Some (S, W)"
    have "fsorts_ok alg W" using f' lk unfolding fscert_def by blast
    moreover have "tcert alg (tvars W)" by (rule tcert_mono[OF tc' tvars_envI2[OF lk]])
    ultimately show "sorts_ok alg W" by (simp add: sorts_ok_fsorts)
  qed
qed

end

end

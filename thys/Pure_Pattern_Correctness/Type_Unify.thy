section \<open>Correctness of Order-Sorted Type Unification\<close>

theory Type_Unify
  imports Pure_Pattern.Pure_Envir
begin

text \<open>
  We verify the model of \<open>Type.unify\<close> (\<^const>\<open>unify_aux\<close>, with \<^const>\<open>meet\<close>,
  \<^const>\<open>devar\<close> and \<^const>\<open>type_occurs\<close>) and the auxiliary functions \<^const>\<open>unified\<close> and
  \<^const>\<open>norm_type\<close>: on acyclic, well-sorted type environments they terminate, and
  \<^const>\<open>unify_aux\<close> computes a most general well-sorted unifier, or fails with \<open>TUnify\<close> if none
  exists. The sort algebra is assumed to satisfy the invariants maintained by Isabelle: the
  subclass relation is transitive, and the arities are complete and coregular.
\<close>


subsection \<open>Well-formed types\<close>

definition tarity :: "(name \<Rightarrow> nat) \<Rightarrow> name \<Rightarrow> nat" where
  "tarity ar a = (if a = STR ''fun'' then 2 else ar a)"

fun wft :: "(name \<Rightarrow> nat) \<Rightarrow> ptyp \<Rightarrow> bool" where
  "wft ar (Type a Ts) \<longleftrightarrow> length Ts = tarity ar a \<and> (\<forall>T\<in>set Ts. wft ar T)"
| "wft ar _ \<longleftrightarrow> True"


lemma allM_return_gen:
  "(\<And>x. x \<in> set xs \<Longrightarrow> P x = return (Q x)) \<Longrightarrow> allM P xs = return (\<forall>x\<in>set xs. Q x)"
  by (induction xs) (auto simp: return_def bindM_def)


subsection \<open>Semantics of sorts\<close>

text \<open>
  A type has a sort if it belongs to all classes of the sort. A type variable or free type
  variable belongs to the superclasses of its sort; a type constructor application belongs to a
  class if the constructor has an arity for the class whose argument sorts the arguments have.
\<close>

function (sequential) has_sort :: "algebra \<Rightarrow> ptyp \<Rightarrow> psort \<Rightarrow> bool" where
  "has_sort alg (Type a Ts) S \<longleftrightarrow>
    (\<forall>c\<in>set S. \<exists>Ss. map_of (arities alg a) c = Some Ss \<and> length Ss = length Ts \<and>
      (\<forall>i<length Ts. has_sort alg (Ts ! i) (Ss ! i)))"
| "has_sort alg (TFree _ S') S \<longleftrightarrow> (\<forall>c\<in>set S. \<exists>c'\<in>set S'. class_le alg c' c)"
| "has_sort alg (TVar _ S') S \<longleftrightarrow> (\<forall>c\<in>set S. \<exists>c'\<in>set S'. class_le alg c' c)"
  by pat_completeness auto
termination
  by (relation "measure (\<lambda>(alg, T, S). size T)")
    (auto simp: less_Suc_eq_le intro!: size_list_estimation' dest: nth_mem)

text \<open>
  The classes declared in the algebra (those of \<open>Sorts.classes_of\<close>): a sort is certified
  (\<open>Sign.certify_sort\<close>) if its classes are declared. The arities of a well-formed algebra
  have certified sorts as their domains.
\<close>

consts classes :: "algebra \<Rightarrow> pclass set"

definition sort_ok :: "algebra \<Rightarrow> psort \<Rightarrow> bool" where
  "sort_ok alg S \<longleftrightarrow> set S \<subseteq> classes alg"

locale wf_algebra =
  fixes alg :: algebra and ar :: "name \<Rightarrow> nat"
  assumes class_less_trans: "class_less alg c1 c2 \<Longrightarrow> class_less alg c2 c3 \<Longrightarrow> class_less alg c1 c3"
    and arity_length: "map_of (arities alg a) c = Some Ss \<Longrightarrow> length Ss = tarity ar a"
    and arity_coregular: "class_le alg c1 c2 \<Longrightarrow> map_of (arities alg a) c1 = Some Ss1 \<Longrightarrow>
      \<exists>Ss2. map_of (arities alg a) c2 = Some Ss2 \<and> list_all2 (sort_le alg) Ss1 Ss2"
    and arity_sorts_ok: "map_of (arities alg a) c = Some Ss \<Longrightarrow> S \<in> set Ss \<Longrightarrow> sort_ok alg S"
begin

lemma class_le_refl[simp]: "class_le alg c c"
  by (simp add: class_le_def)

lemma class_le_trans: "class_le alg c1 c2 \<Longrightarrow> class_le alg c2 c3 \<Longrightarrow> class_le alg c1 c3"
  by (auto simp: class_le_def intro: class_less_trans)

lemma sort_le_iff: "sort_le alg S1 S2 \<longleftrightarrow> (\<forall>c\<in>set S2. \<exists>c'\<in>set S1. class_le alg c' c)"
  unfolding sort_le_def list_all_iff list_ex_iff using class_le_refl by blast

lemma has_sort_set: "set S = set S' \<Longrightarrow> has_sort alg T S \<longleftrightarrow> has_sort alg T S'"
  by (cases T) auto

lemma has_sort_mono: "has_sort alg T S1 \<Longrightarrow> sort_le alg S1 S2 \<Longrightarrow> has_sort alg T S2"
proof (induction T arbitrary: S1 S2)
  case (Type a Ts)
  show ?case
    unfolding has_sort.simps
  proof
    fix c2 assume "c2 \<in> set S2"
    with Type.prems(2) obtain c1 where c1: "c1 \<in> set S1" "class_le alg c1 c2" by (auto simp: sort_le_iff)
    with Type.prems(1) obtain Ss1 where Ss1: "map_of (arities alg a) c1 = Some Ss1" "length Ss1 = length Ts"
      "\<forall>i<length Ts. has_sort alg (Ts ! i) (Ss1 ! i)" by auto
    from arity_coregular[OF c1(2) Ss1(1)] obtain Ss2 where
      Ss2: "map_of (arities alg a) c2 = Some Ss2" "list_all2 (sort_le alg) Ss1 Ss2" by blast
    have "length Ss2 = length Ts" using Ss2(2) Ss1(2) by (simp add: list_all2_lengthD)
    moreover have "has_sort alg (Ts ! i) (Ss2 ! i)" if "i < length Ts" for i
      using Type.IH[OF nth_mem[OF that] Ss1(3)[rule_format, OF that]] Ss2(2) Ss1(2) that
      by (simp add: list_all2_conv_all_nth)
    ultimately show "\<exists>Ss. map_of (arities alg a) c2 = Some Ss \<and> length Ss = length Ts \<and>
        (\<forall>i<length Ts. has_sort alg (Ts ! i) (Ss ! i))" using Ss2(1) by blast
  qed
qed (simp add: sort_le_iff, meson class_le_trans)+

lemma has_class_up: "has_sort alg T [c1] \<Longrightarrow> class_le alg c1 c2 \<Longrightarrow> has_sort alg T [c2]"
  by (rule has_sort_mono) (auto simp: sort_le_iff)

lemma has_sort_iff_classes: "has_sort alg T S \<longleftrightarrow> (\<forall>c\<in>set S. has_sort alg T [c])"
  by (cases T) auto

lemma inter_class_set:
  assumes "\<And>c1 c2. Q c1 \<Longrightarrow> class_le alg c1 c2 \<Longrightarrow> Q c2"
  shows "(\<forall>c'\<in>set (inter_class alg c S). Q c') \<longleftrightarrow> Q c \<and> (\<forall>c'\<in>set S. Q c')"
  by (induction S) (auto intro: assms)

lemma has_sort_Nil[simp]: "has_sort alg T []"
  by (cases T) auto

lemma inter_class_sem:
  "has_sort alg T (inter_class alg c S) \<longleftrightarrow> has_sort alg T [c] \<and> has_sort alg T S"
  using inter_class_set[of "\<lambda>c. has_sort alg T [c]" c S] has_class_up[of T]
  by (simp only: has_sort_iff_classes[of T "inter_class alg c S"] has_sort_iff_classes[of T S])

lemma inter_sort_sem: "has_sort alg T (inter_sort alg S1 S2) \<longleftrightarrow> has_sort alg T S1 \<and> has_sort alg T S2"
proof -
  have "has_sort alg T (fold (inter_class alg) S1 S2) \<longleftrightarrow> has_sort alg T S1 \<and> has_sort alg T S2"
  proof (induction S1 arbitrary: S2)
    case (Cons c cs)
    then show ?case using has_sort_iff_classes[of T "c # cs"] has_sort_iff_classes[of T cs]
      by (simp add: inter_class_sem) blast
  qed simp
  then show ?thesis unfolding inter_sort_def by (subst has_sort_set[of _ "fold (inter_class alg) S1 S2"]) simp_all
qed


text \<open>The intersection of certified sorts and the domains of arities are certified.\<close>

lemma set_inter_class: "set (inter_class alg c S) \<subseteq> insert c (set S)"
  by (induction S) auto

lemma set_inter_sort: "set (inter_sort alg S1 S2) \<subseteq> set S1 \<union> set S2"
proof -
  have "set (fold (inter_class alg) S1 S2) \<subseteq> set S1 \<union> set S2"
  proof (induction S1 arbitrary: S2)
    case (Cons c cs)
    then show ?case using set_inter_class[of c S2] by fastforce
  qed simp
  then show ?thesis by (simp add: inter_sort_def)
qed

lemma sort_ok_inter_sort: "sort_ok alg S1 \<Longrightarrow> sort_ok alg S2 \<Longrightarrow> sort_ok alg (inter_sort alg S1 S2)"
  using set_inter_sort[of S1 S2] by (auto simp: sort_ok_def)

lemma mg_domain_sorts_ok:
  assumes "mg_domain alg a S = return Ds" "D \<in> set Ds"
  shows "sort_ok alg D"
proof -
  define dom where "dom = (\<lambda>c. case map_of (arities alg a) c of
      None \<Rightarrow> raise (Class_Error (No_Arity a c)) | Some Ss \<Rightarrow> return Ss)"
  define dom_inter where "dom_inter = (\<lambda>c Ss. do {Ds \<leftarrow> dom c; return (map2 (inter_sort alg) Ds Ss)})"
  have dom: "dom c = return Ss \<Longrightarrow> S' \<in> set Ss \<Longrightarrow> sort_ok alg S'" for c Ss S'
    by (cases "map_of (arities alg a) c")
      (auto simp: dom_def return_def raise_def intro: arity_sorts_ok)
  have fold: "foldM dom_inter xs Ds0 = return Ds' \<Longrightarrow> \<forall>D\<in>set Ds0. sort_ok alg D \<Longrightarrow>
      \<forall>D\<in>set Ds'. sort_ok alg D" for xs Ds0 Ds'
  proof (induction xs arbitrary: Ds0)
    case (Cons x xs)
    show ?case
    proof (cases "map_of (arities alg a) x")
      case None
      then show ?thesis using Cons.prems(1) by (simp add: dom_inter_def dom_def) (simp add: return_def raise_def)
    next
      case (Some Sx)
      then have dx: "dom x = return Sx" by (simp add: dom_def)
      have "\<forall>D\<in>set (map2 (inter_sort alg) Sx Ds0). sort_ok alg D"
        using dom[OF dx] Cons.prems(2) by (auto simp: set_zip intro!: sort_ok_inter_sort)
      with Cons.IH Cons.prems(1) dx show ?thesis by (simp add: dom_inter_def)
    qed
  qed (simp add: return_def)
  show ?thesis
  proof (cases S)
    case Nil
    then show ?thesis using assms(1) by (simp add: mg_domain_def) (simp add: return_def raise_def)
  next
    case (Cons c cs)
    then have md: "mg_domain alg a S = dom c \<bind> (\<lambda>Ds. foldM dom_inter cs Ds)"
      by (simp add: mg_domain_def dom_def dom_inter_def Let_def)
    show ?thesis
    proof (cases "map_of (arities alg a) c")
      case None
      then show ?thesis using assms(1) md by (simp add: dom_def) (simp add: return_def raise_def)
    next
      case (Some Sc)
      then have "dom c = return Sc" by (simp add: dom_def)
      with md assms(1) have "foldM dom_inter cs Sc = return Ds" by simp
      from fold[OF this] dom[OF \<open>dom c = return Sc\<close>] assms(2) show ?thesis by blast
    qed
  qed
qed

text \<open>The executable sort functions agree with the semantics.\<close>

lemma has_sort_Type:
  "length Ts = tarity ar a \<Longrightarrow> has_sort alg (Type a Ts) S \<longleftrightarrow>
    (\<forall>c\<in>set S. \<exists>Ss. map_of (arities alg a) c = Some Ss \<and> (\<forall>i<length Ts. has_sort alg (Ts ! i) (Ss ! i)))"
  using arity_length by auto

lemma mg_domain_ok:
  assumes "S \<noteq> []" "\<forall>c\<in>set S. map_of (arities alg a) c \<noteq> None"
  shows "\<exists>Ds. mg_domain alg a S = return Ds \<and> length Ds = tarity ar a \<and>
    (\<forall>i<tarity ar a. \<forall>T. has_sort alg T (Ds ! i) \<longleftrightarrow>
      (\<forall>c\<in>set S. \<forall>Ss. map_of (arities alg a) c = Some Ss \<longrightarrow> has_sort alg T (Ss ! i)))"
proof -
  obtain c cs where S: "S = c # cs" using assms(1) by (cases S) auto
  define dom where "dom = (\<lambda>c. case map_of (arities alg a) c of
      None \<Rightarrow> raise (Class_Error (No_Arity a c)) | Some Ss \<Rightarrow> return Ss)"
  define dom_inter where "dom_inter = (\<lambda>c Ss. do {Ds \<leftarrow> dom c; return (map2 (inter_sort alg) Ds Ss)})"
  have md: "mg_domain alg a S = dom c \<bind> (\<lambda>Ds. foldM dom_inter cs Ds)"
    by (simp add: mg_domain_def S dom_def dom_inter_def Let_def)
  from assms(2) S obtain Ss0 where Ss0: "map_of (arities alg a) c = Some Ss0" by auto
  have fold: "\<exists>Ds'. foldM dom_inter xs Ds = return Ds' \<and> length Ds' = tarity ar a \<and>
      (\<forall>i<tarity ar a. \<forall>T. has_sort alg T (Ds' ! i) \<longleftrightarrow>
        has_sort alg T (Ds ! i) \<and> (\<forall>c\<in>set xs. \<forall>Ss. map_of (arities alg a) c = Some Ss \<longrightarrow> has_sort alg T (Ss ! i)))"
    if "length Ds = tarity ar a" "set xs \<subseteq> set S" for xs Ds
    using that
  proof (induction xs arbitrary: Ds)
    case (Cons x xs)
    from Cons.prems(2) assms(2) obtain Sx where Sx: "map_of (arities alg a) x = Some Sx" by auto
    have lx: "length Sx = tarity ar a" by (rule arity_length[OF Sx])
    let ?D = "map2 (inter_sort alg) Sx Ds"
    have di: "dom_inter x Ds = return ?D" by (simp add: dom_inter_def dom_def Sx)
    have lD: "length ?D = tarity ar a" using lx Cons.prems(1) by simp
    from Cons.IH[OF lD] Cons.prems(2) obtain Ds' where Ds': "foldM dom_inter xs ?D = return Ds'"
      "length Ds' = tarity ar a"
      "\<forall>i<tarity ar a. \<forall>T. has_sort alg T (Ds' ! i) \<longleftrightarrow>
        has_sort alg T (?D ! i) \<and> (\<forall>c\<in>set xs. \<forall>Ss. map_of (arities alg a) c = Some Ss \<longrightarrow> has_sort alg T (Ss ! i))"
      by auto
    have "has_sort alg T (?D ! i) \<longleftrightarrow> has_sort alg T (Sx ! i) \<and> has_sort alg T (Ds ! i)"
      if "i < tarity ar a" for i T using that lx Cons.prems(1) by (simp add: inter_sort_sem)
    with Ds' di Sx show ?case by auto
  qed auto
  have sub: "set cs \<subseteq> set S" using S by auto
  from fold[OF arity_length[OF Ss0] sub] obtain Ds' where
    "foldM dom_inter cs Ss0 = return Ds'" "length Ds' = tarity ar a"
    "\<forall>i<tarity ar a. \<forall>T. has_sort alg T (Ds' ! i) \<longleftrightarrow>
      has_sort alg T (Ss0 ! i) \<and> (\<forall>c\<in>set cs. \<forall>Ss. map_of (arities alg a) c = Some Ss \<longrightarrow> has_sort alg T (Ss ! i))"
    by blast
  with md Ss0 S show ?thesis by (auto simp: dom_def)
qed

lemma mg_domain_error:
  assumes "S \<noteq> []" "c \<in> set S" "map_of (arities alg a) c = None"
  shows "\<exists>ce. mg_domain alg a S = raise (Class_Error ce)"
proof -
  obtain c0 cs where S: "S = c0 # cs" using assms(1) by (cases S) auto
  define dom where "dom = (\<lambda>c. case map_of (arities alg a) c of
      None \<Rightarrow> raise (Class_Error (No_Arity a c)) | Some Ss \<Rightarrow> return Ss)"
  define dom_inter where "dom_inter = (\<lambda>c Ss. do {Ds \<leftarrow> dom c; return (map2 (inter_sort alg) Ds Ss)})"
  have md: "mg_domain alg a S = dom c0 \<bind> (\<lambda>Ds. foldM dom_inter cs Ds)"
    by (simp add: mg_domain_def S dom_def dom_inter_def Let_def)
  have "\<exists>ce. foldM dom_inter xs Ds = raise (Class_Error ce)" if "c \<in> set xs" for xs Ds
    using that
  proof (induction xs arbitrary: Ds)
    case (Cons x xs)
    show ?case
    proof (cases "map_of (arities alg a) x")
      case None
      then show ?thesis by (auto simp: dom_inter_def dom_def)
    next
      case (Some Sx)
      with Cons assms(3) show ?thesis by (auto simp: dom_inter_def dom_def)
    qed
  qed simp
  then show ?thesis using md assms(2,3) S by (cases "c = c0") (auto simp: dom_def split: option.splits)
qed

lemma of_sort_sem: "wft ar T \<Longrightarrow> of_sort alg T S = return (has_sort alg T S)"
proof (induction T arbitrary: S)
  case (Type a Ts)
  show ?case
  proof (cases "S = []")
    case False
    have len: "length Ts = tarity ar a" using Type.prems by simp
    show ?thesis
    proof (cases "\<forall>c\<in>set S. map_of (arities alg a) c \<noteq> None")
      case True
      from mg_domain_ok[OF False True] obtain Ds where Ds: "mg_domain alg a S = return Ds"
        "length Ds = tarity ar a"
        "\<forall>i<tarity ar a. \<forall>T. has_sort alg T (Ds ! i) \<longleftrightarrow>
          (\<forall>c\<in>set S. \<forall>Ss. map_of (arities alg a) c = Some Ss \<longrightarrow> has_sort alg T (Ss ! i))" by blast
      have "allM (\<lambda>(T, S). of_sort alg T S) (zip Ts Ds) = return (\<forall>(T, S)\<in>set (zip Ts Ds). has_sort alg T S)"
        using Type.IH Type.prems by (intro allM_return_gen) (auto dest: set_zip_leftD)
      moreover have "(\<forall>(T, S)\<in>set (zip Ts Ds). has_sort alg T S) \<longleftrightarrow>
          (\<forall>i<length Ts. has_sort alg (Ts ! i) (Ds ! i))"
        using Ds(2) len by (auto simp: set_zip)
      moreover have "\<dots> \<longleftrightarrow> (\<forall>c\<in>set S. \<forall>Ss. map_of (arities alg a) c = Some Ss \<longrightarrow>
          (\<forall>i<length Ts. has_sort alg (Ts ! i) (Ss ! i)))"
        using Ds(3) len by auto
      moreover have "\<dots> \<longleftrightarrow> has_sort alg (Type a Ts) S"
        using True unfolding has_sort_Type[OF len] by fastforce
      ultimately show ?thesis using False Ds(1) by (subst of_sort.simps) (simp del: has_sort.simps)
    next
      case nT: False
      then obtain c where c: "c \<in> set S" "map_of (arities alg a) c = None" by auto
      from mg_domain_error[OF False c] obtain ce where "mg_domain alg a S = raise (Class_Error ce)" by blast
      moreover have "\<not> has_sort alg (Type a Ts) S" using c by force
      ultimately show ?thesis using False by (subst of_sort.simps) (simp del: has_sort.simps)
    qed
  qed (simp add: of_sort.simps)
qed (auto simp: of_sort.simps sort_le_iff)

end


subsection \<open>Type substitutions\<close>

fun tvars :: "ptyp \<Rightarrow> (indexname \<times> psort) set" where
  "tvars (Type _ Ts) = \<Union> (tvars ` set Ts)"
| "tvars (TFree _ _) = {}"
| "tvars (TVar v S) = {(v, S)}"

lemma finite_tvars[simp]: "finite (tvars T)"
  by (induction T) auto

fun tsubst :: "(indexname \<Rightarrow> psort \<Rightarrow> ptyp) \<Rightarrow> ptyp \<Rightarrow> ptyp" where
  "tsubst \<rho> (Type a Ts) = Type a (map (tsubst \<rho>) Ts)"
| "tsubst \<rho> (TFree a S) = TFree a S"
| "tsubst \<rho> (TVar v S) = \<rho> v S"

lemma tsubst_cong: "(\<And>v S. (v, S) \<in> tvars T \<Longrightarrow> \<rho> v S = \<rho>' v S) \<Longrightarrow> tsubst \<rho> T = tsubst \<rho>' T"
proof (induction T)
  case (Type a Ts)
  have "tsubst \<rho> T = tsubst \<rho>' T" if "T \<in> set Ts" for T
    by (rule Type.IH[OF that], rule Type.prems) (use that in auto)
  then show ?case by simp
qed auto

lemma tsubst_tsubst: "tsubst \<rho> (tsubst \<rho>' T) = tsubst (\<lambda>v S. tsubst \<rho> (\<rho>' v S)) T"
  by (induction T) auto

lemma tsubst_TVar[simp]: "tsubst TVar T = T"
  by (induction T) (auto simp: map_idI)

lemma tvars_tsubst: "tvars (tsubst \<rho> T) = (\<Union>(v, S)\<in>tvars T. tvars (\<rho> v S))"
  by (induction T) auto

lemma wft_tsubst: "wft ar T \<Longrightarrow> (\<forall>(v, S)\<in>tvars T. wft ar (\<rho> v S)) \<Longrightarrow> wft ar (tsubst \<rho> T)"
  by (induction T) auto

context wf_algebra
begin

lemma has_sort_tsubst:
  "has_sort alg T S \<Longrightarrow> (\<forall>(v, S')\<in>tvars T. has_sort alg (\<rho> v S') S') \<Longrightarrow> has_sort alg (tsubst \<rho> T) S"
proof (induction T arbitrary: S)
  case (Type a Ts)
  then show ?case by (fastforce dest: nth_mem)
next
  case (TVar v S')
  then show ?case by (auto intro: has_sort_mono simp: sort_le_iff)
qed simp

end


subsection \<open>Type environments\<close>

text \<open>
  \<open>(w, v) \<in> tdep \<theta>\<close>: the binding of the type variable \<open>v\<close> contains \<open>w\<close>. On acyclic type
  environments, \<^term>\<open>tnorm \<theta> T\<close> is the result of applying the bindings exhaustively.
\<close>

definition tdep :: "tyenv \<Rightarrow> (indexname \<times> indexname) set" where
  "tdep \<theta> = {(w, v). \<exists>S U. vt_lookup \<theta> v = Some (S, U) \<and> w \<in> fst ` tvars U}"

definition tacyc :: "tyenv \<Rightarrow> bool" where
  "tacyc \<theta> \<longleftrightarrow> acyclic (tdep \<theta>)"

lemma finite_tdep: "finite (tdep \<theta>)"
proof -
  let ?D = "{v. vt_lookup \<theta> v \<noteq> None}"
  have "tdep \<theta> \<subseteq> (\<Union>v\<in>?D. (\<lambda>w. (w, v)) ` fst ` tvars (snd (the (vt_lookup \<theta> v))))"
    by (force simp: tdep_def image_iff)
  moreover have "finite (\<Union>v\<in>?D. (\<lambda>w. (w, v)) ` fst ` tvars (snd (the (vt_lookup \<theta> v))))"
    using finite_vt_lookup[of \<theta>] by simp
  ultimately show ?thesis by (rule finite_subset)
qed

lemma wf_tdep: "tacyc \<theta> \<Longrightarrow> wf (tdep \<theta>)"
  by (simp add: tacyc_def finite_acyclic_wf finite_tdep)

definition tval_step :: "tyenv \<Rightarrow> (indexname \<Rightarrow> ptyp option) \<Rightarrow> indexname \<Rightarrow> ptyp option" where
  "tval_step \<theta> f v = (case vt_lookup \<theta> v of
     Some (S, U) \<Rightarrow> Some (tsubst (\<lambda>w S'. case f w of Some U' \<Rightarrow> U' | None \<Rightarrow> TVar w S') U)
   | None \<Rightarrow> None)"

definition tval :: "tyenv \<Rightarrow> indexname \<Rightarrow> ptyp option" where
  "tval \<theta> = wfrec (tdep \<theta>) (tval_step \<theta>)"

definition tnorm :: "tyenv \<Rightarrow> ptyp \<Rightarrow> ptyp" where
  "tnorm \<theta> = tsubst (\<lambda>w S. case tval \<theta> w of Some U \<Rightarrow> U | None \<Rightarrow> TVar w S)"

lemma adm_tval_step: "adm_wf (tdep \<theta>) (tval_step \<theta>)"
  unfolding adm_wf_def
proof (intro allI impI)
  fix f g :: "indexname \<Rightarrow> ptyp option" and v
  assume eq: "\<forall>w. (w, v) \<in> tdep \<theta> \<longrightarrow> f w = g w"
  show "tval_step \<theta> f v = tval_step \<theta> g v"
  proof (cases "vt_lookup \<theta> v")
    case (Some b)
    obtain S U where b: "b = (S, U)" by force
    have "tsubst (\<lambda>w S'. case f w of Some U' \<Rightarrow> U' | None \<Rightarrow> TVar w S') U =
        tsubst (\<lambda>w S'. case g w of Some U' \<Rightarrow> U' | None \<Rightarrow> TVar w S') U"
      by (rule tsubst_cong) (use eq Some b in \<open>force simp: tdep_def\<close>)
    with Some b show ?thesis by (simp add: tval_step_def)
  qed (simp add: tval_step_def)
qed

lemma tnorm_Type[simp]: "tnorm \<theta> (Type a Ts) = Type a (map (tnorm \<theta>) Ts)"
  and tnorm_TFree[simp]: "tnorm \<theta> (TFree a S) = TFree a S"
  by (simp_all add: tnorm_def)

context
  fixes \<theta> assumes ac: "tacyc \<theta>"
begin

lemma tval_eq: "tval \<theta> v = (case vt_lookup \<theta> v of Some (S, U) \<Rightarrow> Some (tnorm \<theta> U) | None \<Rightarrow> None)"
  unfolding tval_def
  by (subst wfrec_fixpoint[OF wf_tdep[OF ac] adm_tval_step])
    (simp add: tval_step_def tnorm_def tval_def split: option.splits)

lemma tnorm_TVar[simp]:
  "tnorm \<theta> (TVar v S) = (case vt_lookup \<theta> v of Some (S', U) \<Rightarrow> tnorm \<theta> U | None \<Rightarrow> TVar v S)"
  by (simp add: tnorm_def tval_eq[unfolded tnorm_def] split: option.splits)

lemma tdep_induct: "(\<And>v. (\<And>w. (w, v) \<in> tdep \<theta> \<Longrightarrow> P w) \<Longrightarrow> P v) \<Longrightarrow> P v"
  by (rule wf_induct_rule[OF wf_tdep[OF ac]]) blast

lemma tnorm_unbound: "(w, S) \<in> tvars (tnorm \<theta> T) \<Longrightarrow> vt_lookup \<theta> w = None"
proof -
  have B: "vt_lookup \<theta> v = Some (S', U) \<Longrightarrow> (w, S) \<in> tvars (tnorm \<theta> U) \<Longrightarrow> vt_lookup \<theta> w = None"
    for v S' U w S
  proof (induction v arbitrary: S' U w S rule: tdep_induct)
    case (1 v)
    have "(w, S) \<in> tvars (tnorm \<theta> T) \<Longrightarrow> vt_lookup \<theta> w = None"
      if "\<forall>x\<in>fst ` tvars T. (x, v) \<in> tdep \<theta>" for T w S
      using that
    proof (induction T)
      case (Type a Ts)
      then show ?case by fastforce
    next
      case (TVar x S0)
      have xv: "(x, v) \<in> tdep \<theta>" using TVar.prems(2) by simp
      show ?case
      proof (cases "vt_lookup \<theta> x")
        case None
        with TVar.prems(1) show ?thesis by simp
      next
        case (Some b)
        obtain S1 U1 where b: "b = (S1, U1)" by force
        with Some TVar.prems(1) "1.IH"[OF xv] show ?thesis by simp
      qed
    qed simp
    moreover have "\<forall>x\<in>fst ` tvars U. (x, v) \<in> tdep \<theta>" using "1.prems"(1) unfolding tdep_def by blast
    ultimately show ?case using "1.prems"(2) by blast
  qed
  show "(w, S) \<in> tvars (tnorm \<theta> T) \<Longrightarrow> vt_lookup \<theta> w = None"
  proof (induction T)
    case (TVar x S0)
    show ?case
    proof (cases "vt_lookup \<theta> x")
      case None
      with TVar show ?thesis by simp
    next
      case (Some b)
      obtain S1 U1 where "b = (S1, U1)" by force
      with Some TVar B[of x S1 U1 w S] show ?thesis by simp
    qed
  qed auto
qed

lemma tnorm_unbound_id: "(\<And>w S. (w, S) \<in> tvars T \<Longrightarrow> vt_lookup \<theta> w = None) \<Longrightarrow> tnorm \<theta> T = T"
proof (induction T)
  case (Type a Ts)
  have "tnorm \<theta> T = T" if "T \<in> set Ts" for T
    by (rule Type.IH[OF that], rule Type.prems) (use that in auto)
  then show ?case by (simp add: map_idI)
qed auto

lemma tnorm_idem[simp]: "tnorm \<theta> (tnorm \<theta> T) = tnorm \<theta> T"
  by (rule tnorm_unbound_id) (rule tnorm_unbound)

end


lemma vt_is_empty_lookup: "vt_is_empty t \<Longrightarrow> vt_lookup t k = None"
  by transfer simp

lemma tacyc_empty: "vt_is_empty \<theta> \<Longrightarrow> tacyc \<theta>"
  by (simp add: tacyc_def tdep_def vt_is_empty_lookup acyclic_def)

lemma tnorm_empty: "vt_is_empty \<theta> \<Longrightarrow> tnorm \<theta> T = T"
  by (rule tnorm_unbound_id[OF tacyc_empty]) (simp_all add: vt_is_empty_lookup)


subsection \<open>Sort consistency and the executable operations\<close>

text \<open>
  A type variable is identified with its sort: \<^const>\<open>type_lookup\<close> raises an exception if a
  variable occurs with a sort different from the one of its binding. We require consistency.
\<close>

declare split_paired_All[simp del] split_paired_Ex[simp del]

definition tcons :: "tyenv \<Rightarrow> ptyp \<Rightarrow> bool" where
  "tcons \<theta> T \<longleftrightarrow> (\<forall>v S S' U. (v, S) \<in> tvars T \<longrightarrow> vt_lookup \<theta> v = Some (S', U) \<longrightarrow> S' = S)"

definition tcons_env :: "tyenv \<Rightarrow> bool" where
  "tcons_env \<theta> \<longleftrightarrow> (\<forall>v S U. vt_lookup \<theta> v = Some (S, U) \<longrightarrow> tcons \<theta> U)"

lemma tcons_Type[simp]: "tcons \<theta> (Type a Ts) \<longleftrightarrow> (\<forall>T\<in>set Ts. tcons \<theta> T)"
  unfolding tcons_def by auto

lemma tcons_envD: "tcons_env \<theta> \<Longrightarrow> vt_lookup \<theta> v = Some (S, U) \<Longrightarrow> tcons \<theta> U"
  unfolding tcons_env_def by blast

definition tbound :: "tyenv \<Rightarrow> ptyp \<Rightarrow> bool" where
  "tbound \<theta> T = (case T of TVar v S \<Rightarrow> vt_lookup \<theta> v \<noteq> None | _ \<Rightarrow> False)"

lemma tbound_simps[simp]: "tbound \<theta> (TVar v S) \<longleftrightarrow> vt_lookup \<theta> v \<noteq> None"
  "\<not> tbound \<theta> (Type a Ts)" "\<not> tbound \<theta> (TFree a S)"
  by (simp_all add: tbound_def)

lemma tcons_TVar: "tcons \<theta> (TVar v S) \<longleftrightarrow> (\<forall>S' U. vt_lookup \<theta> v = Some (S', U) \<longrightarrow> S' = S)"
  by (simp add: tcons_def)

lemma tcons_simps[simp]: "tcons \<theta> (TFree a S)"
  by (simp add: tcons_def)

lemma type_lookup_ok:
  "vt_lookup \<theta> v = None \<Longrightarrow> type_lookup \<theta> v S = return None"
  "vt_lookup \<theta> v = Some (S, U) \<Longrightarrow> type_lookup \<theta> v S = return (Some U)"
  by (simp_all add: type_lookup_def)

context
  fixes \<theta> assumes ac: "tacyc \<theta>" and tc: "tcons_env \<theta>"
begin

lemma tnorm_induct[consumes 1, case_names TFree Type Unbound Bound]:
  assumes "tcons \<theta> T"
    and "\<And>a S. P (TFree a S)"
    and "\<And>a Ts. (\<And>T. T \<in> set Ts \<Longrightarrow> P T) \<Longrightarrow> \<forall>T\<in>set Ts. tcons \<theta> T \<Longrightarrow> P (Type a Ts)"
    and "\<And>v S. vt_lookup \<theta> v = None \<Longrightarrow> P (TVar v S)"
    and "\<And>v S U. vt_lookup \<theta> v = Some (S, U) \<Longrightarrow> tcons \<theta> U \<Longrightarrow> P U \<Longrightarrow> P (TVar v S)"
  shows "P T"
proof -
  have struct: "P T" if "tcons \<theta> T" "\<And>w S U. w \<in> fst ` tvars T \<Longrightarrow> vt_lookup \<theta> w = Some (S, U) \<Longrightarrow> P U" for T
    using that
  proof (induction T)
    case (Type a Ts)
    have IHs: "P T" if T: "T \<in> set Ts" for T
    proof (rule Type.IH[OF T])
      show "tcons \<theta> T" using Type.prems(1) T by simp
      fix w S U assume w: "w \<in> fst ` tvars T" "vt_lookup \<theta> w = Some (S, U)"
      show "P U" by (rule Type.prems(2)[OF _ w(2)]) (use w(1) T in auto)
    qed
    show ?case by (rule assms(3)[OF IHs]) (use Type.prems(1) in simp_all)
  next
    case (TVar w S)
    show ?case
    proof (cases "vt_lookup \<theta> w")
      case None
      then show ?thesis by (rule assms(4))
    next
      case (Some b)
      obtain S1 U where b: "b = (S1, U)" by force
      with Some TVar.prems(1) have "S1 = S" by (simp add: tcons_TVar)
      with Some b TVar.prems(2)[of w S U] tcons_envD[OF tc] show ?thesis by (intro assms(5)) simp_all
    qed
  qed (rule assms(2))
  have bound: "vt_lookup \<theta> v = Some (S, U) \<Longrightarrow> P U" for v S U
  proof (induction v arbitrary: S U rule: tdep_induct[OF ac])
    case (1 v)
    show ?case
    proof (rule struct)
      show "tcons \<theta> U" using "1.prems" by (rule tcons_envD[OF tc])
      fix w S' U' assume "w \<in> fst ` tvars U" "vt_lookup \<theta> w = Some (S', U')"
      moreover from this(1) "1.prems" have "(w, v) \<in> tdep \<theta>" unfolding tdep_def by blast
      ultimately show "P U'" using "1.IH" by blast
    qed
  qed
  show ?thesis using struct[OF assms(1)] bound by blast
qed

lemma devar_ok:
  assumes "tcons \<theta> T"
  shows "\<exists>U. devar \<theta> T = return U \<and> tnorm \<theta> U = tnorm \<theta> T \<and> tcons \<theta> U \<and> \<not> tbound \<theta> U"
  using assms
proof (induction rule: tnorm_induct)
  case (TFree a S)
  show ?case by (subst devar.simps) (rule exI[of _ "TFree a S"], simp)
next
  case (Type a Ts)
  show ?case by (subst devar.simps) (rule exI[of _ "Type a Ts"], simp add: Type.hyps)
next
  case (Unbound v S)
  then show ?case
    by (subst devar.simps) (simp add: type_lookup_ok, rule exI[of _ "TVar v S"], simp add: tcons_TVar)
next
  case (Bound v S U)
  then show ?case by (subst devar.simps) (auto simp: type_lookup_ok tnorm_TVar[OF ac])
qed

lemma norm_type_aux_ok: "tcons \<theta> T \<Longrightarrow> norm_type_aux \<theta> T = return (tnorm \<theta> T)"
proof (induction rule: tnorm_induct)
  case (Type a Ts)
  have "mapM (norm_type_aux \<theta>) Ts = return (map (tnorm \<theta>) Ts)"
    using Type.IH by (induction Ts) auto
  then show ?case by (subst norm_type_aux.simps) simp
qed (subst norm_type_aux.simps; simp add: type_lookup_ok tnorm_TVar[OF ac])+

lemma norm_type_ok: "tcons \<theta> T \<Longrightarrow> norm_type \<theta> T = return (tnorm \<theta> T)"
  by (simp add: norm_type_def norm_type_aux_ok tnorm_empty)

lemma type_occurs_ok:
  assumes "tcons \<theta> T" "vt_lookup \<theta> v = None"
  shows "type_occurs v \<theta> T = return (v \<in> fst ` tvars (tnorm \<theta> T))"
  using assms(1)
proof (induction rule: tnorm_induct)
  case (Type a Ts)
  have "existsM (type_occurs v \<theta>) Ts = return (\<exists>T\<in>set Ts. v \<in> fst ` tvars (tnorm \<theta> T))"
    using Type.IH by (induction Ts) (auto simp: return_def bindM_def)
  then show ?case by (subst type_occurs.simps) (simp add: image_UN)
next
  case (Bound w S U)
  with assms(2) have "v \<noteq> w" by auto
  with Bound show ?case by (subst type_occurs.simps) (simp add: type_lookup_ok tnorm_TVar[OF ac])
qed (subst type_occurs.simps; auto simp: type_lookup_ok tnorm_TVar[OF ac])+

lemma unified_aux_ok:
  "tcons \<theta> T \<Longrightarrow> tcons \<theta> T' \<Longrightarrow> unified_aux \<theta> T T' = return (tnorm \<theta> T = tnorm \<theta> T')"
proof (induction "size (tnorm \<theta> T)" arbitrary: T T' rule: less_induct)
  case less
  from devar_ok[OF less.prems(1)] obtain U where U: "devar \<theta> T = return U" "tnorm \<theta> U = tnorm \<theta> T"
    "tcons \<theta> U" "\<not> tbound \<theta> U" by blast
  from devar_ok[OF less.prems(2)] obtain U' where U': "devar \<theta> T' = return U'" "tnorm \<theta> U' = tnorm \<theta> T'"
    "tcons \<theta> U'" "\<not> tbound \<theta> U'" by blast
  show ?case
  proof (cases "\<exists>s Ts s' Ts'. U = Type s Ts \<and> U' = Type s' Ts'")
    case True
    then obtain s Ts s' Ts' where UU: "U = Type s Ts" "U' = Type s' Ts'" by blast
    have "allM (\<lambda>(T, T'). unified_aux \<theta> T T') (zip Ts Ts') =
        return (\<forall>(T, T')\<in>set (zip Ts Ts'). tnorm \<theta> T = tnorm \<theta> T')"
    proof (rule allM_return_gen)
      fix x assume x: "x \<in> set (zip Ts Ts')"
      obtain A B where xAB: "x = (A, B)" by force
      with x have "A \<in> set Ts" "B \<in> set Ts'" by (auto dest: set_zip_leftD set_zip_rightD)
      moreover have "size (tnorm \<theta> A) < size (tnorm \<theta> T)"
        using \<open>A \<in> set Ts\<close> U(2) UU(1)
        by (auto simp flip: U(2) intro!: le_imp_less_Suc size_list_estimation'[of A])
      ultimately show "(case x of (T, T') \<Rightarrow> unified_aux \<theta> T T') = return (case x of (T, T') \<Rightarrow> tnorm \<theta> T = tnorm \<theta> T')"
        using less.hyps U(3) U'(3) UU xAB by simp
    qed
    moreover have "list_all2 (\<lambda>T T'. tnorm \<theta> T = tnorm \<theta> T') Ts Ts' \<longleftrightarrow> map (tnorm \<theta>) Ts = map (tnorm \<theta>) Ts'"
      by (auto simp: list_all2_conv_all_nth list_eq_iff_nth_eq)
    moreover have "tnorm \<theta> T = Type s (map (tnorm \<theta>) Ts)" "tnorm \<theta> T' = Type s' (map (tnorm \<theta>) Ts')"
      using U(2) U'(2) UU by simp_all
    ultimately show ?thesis using U(1) U'(1) UU
      by (subst unified_aux.simps) (auto simp: list_all2_iff conj_commute)
  next
    case False
    have nf: "tnorm \<theta> V = V" if "\<not> (\<exists>a Vs. V = Type a Vs)" "\<not> tbound \<theta> V" for V
      using that by (cases V) (auto simp: tnorm_TVar[OF ac])
    have "(U = U') \<longleftrightarrow> tnorm \<theta> T = tnorm \<theta> T'"
    proof (cases "\<exists>a Vs. U = Type a Vs")
      case True
      then obtain a Vs where UT: "U = Type a Vs" by blast
      with False have nU': "\<not> (\<exists>a Vs. U' = Type a Vs)" by blast
      have "tnorm \<theta> T' = U'" using nf[OF nU' U'(4)] U'(2) by simp
      moreover have "tnorm \<theta> T = Type a (map (tnorm \<theta>) Vs)" using U(2) UT by simp
      ultimately show ?thesis using nU' UT by metis
    next
      case nU: False
      then have tT: "tnorm \<theta> T = U" using nf[OF nU U(4)] U(2) by simp
      show ?thesis
      proof (cases "\<exists>a Vs. U' = Type a Vs")
        case True
        then obtain a Vs where "U' = Type a Vs" by blast
        moreover from this have "tnorm \<theta> T' = Type a (map (tnorm \<theta>) Vs)" using U'(2) by simp
        ultimately show ?thesis using tT nU by auto
      next
        case False
        then have "tnorm \<theta> T' = U'" using nf[OF False U'(4)] U'(2) by simp
        with tT show ?thesis by simp
      qed
    qed
    then show ?thesis using U(1) U'(1) False by (subst unified_aux.simps) (cases U; cases U'; simp)
  qed
qed

lemma unified_ok: "tcons \<theta> T \<Longrightarrow> tcons \<theta> T' \<Longrightarrow> unified \<theta> T T' = return (tnorm \<theta> T = tnorm \<theta> T')"
  by (simp add: unified_def unified_aux_ok tnorm_empty)

end

end

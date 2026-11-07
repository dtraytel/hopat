section \<open>Models of Pure's Meta-Logic\<close>

theory Thm_Model
  imports Thm_Syntax
begin

text \<open>
  A Tarski semantics of Pure, given axiomatically. A universe provides sets with membership, a
  function space with application and extensional abstraction, and a two-element set of truth
  values (locale \<open>universe\<close>). A model of a signature interprets the type constructors as
  operations on nonempty sets, the classes as predicates on sets compatible with the class
  algebra, and the constants as elements of their interpreted types; the built-in connectives
  \<open>\<Longrightarrow>\<close> and \<open>\<And>\<close> are implication and quantification over the interpreted type, and the class
  constant \<open>OFCLASS(_, c)\<close> states membership in the class \<open>c\<close> (locale \<open>pure_model\<close>). A sort is
  inhabited if some nonempty set belongs to its classes; it may be empty. Terms are interpreted
  under a valuation \<open>\<eta>\<close> of the type variables (schematic and fixed) by nonempty sets, of their
  sorts if these are inhabited, and a valuation \<open>\<xi>\<close> of the term variables (schematic and
  fixed), indexed by name and type as they occur; \<open>bv\<close> gives the values of the loose bound
  variables. Theory \<open>Thm_Model_ZFC\<close> shows that the axioms are satisfiable.
\<close>


subsection \<open>An abstract universe\<close>

locale universe =
  fixes umem :: "'u \<Rightarrow> 'u \<Rightarrow> bool"  (infix \<open>\<in>\<^sub>u\<close> 50)
    and ufun :: "'u \<Rightarrow> 'u \<Rightarrow> 'u"
    and uapp :: "'u \<Rightarrow> 'u \<Rightarrow> 'u"
    and ulam :: "'u \<Rightarrow> ('u \<Rightarrow> 'u) \<Rightarrow> 'u"
    and ubool :: 'u and utrue :: 'u and ufalse :: 'u
  assumes uapp_mem: "f \<in>\<^sub>u ufun A B \<Longrightarrow> a \<in>\<^sub>u A \<Longrightarrow> uapp f a \<in>\<^sub>u B"
    and ulam_mem: "(\<And>a. a \<in>\<^sub>u A \<Longrightarrow> g a \<in>\<^sub>u B) \<Longrightarrow> ulam A g \<in>\<^sub>u ufun A B"
    and uapp_ulam: "a \<in>\<^sub>u A \<Longrightarrow> uapp (ulam A g) a = g a"
    and ufun_ext: "f \<in>\<^sub>u ufun A B \<Longrightarrow> f' \<in>\<^sub>u ufun A B \<Longrightarrow> (\<And>a. a \<in>\<^sub>u A \<Longrightarrow> uapp f a = uapp f' a) \<Longrightarrow> f = f'"
    and ubool_mem: "b \<in>\<^sub>u ubool \<longleftrightarrow> b = utrue \<or> b = ufalse"
    and utrue_ufalse: "utrue \<noteq> ufalse"
begin

definition une :: "'u \<Rightarrow> bool" where
  "une A \<longleftrightarrow> (\<exists>a. a \<in>\<^sub>u A)"

definition ubval :: "bool \<Rightarrow> 'u" where
  "ubval b = (if b then utrue else ufalse)"

lemma ubval_mem [simp]: "ubval b \<in>\<^sub>u ubool"
  by (simp add: ubval_def ubool_mem)

lemma ubval_true [simp]: "ubval b = utrue \<longleftrightarrow> b"
  using utrue_ufalse by (simp add: ubval_def)

lemma une_ubool: "une ubool"
  using ubool_mem by (auto simp: une_def)

lemma une_ufun: "une B \<Longrightarrow> une (ufun A B)"
  unfolding une_def using ulam_mem[of A "\<lambda>_. _" B] by blast

lemma ulam_cong:
  assumes "\<And>a. a \<in>\<^sub>u A \<Longrightarrow> g a \<in>\<^sub>u B" "\<And>a. a \<in>\<^sub>u A \<Longrightarrow> g a = g' a"
  shows "ulam A g = ulam A g'"
proof (rule ufun_ext[of _ A B])
  show "ulam A g \<in>\<^sub>u ufun A B" by (rule ulam_mem) (rule assms(1))
  show "ulam A g' \<in>\<^sub>u ufun A B" by (rule ulam_mem) (use assms in metis)
  show "uapp (ulam A g) a = uapp (ulam A g') a" if "a \<in>\<^sub>u A" for a
    using that assms(2)[OF that] by (simp add: uapp_ulam)
qed

lemma ulam_uapp: "f \<in>\<^sub>u ufun A B \<Longrightarrow> ulam A (uapp f) = f"
  by (rule ufun_ext[of _ A B]) (auto intro: ulam_mem uapp_mem simp: uapp_ulam)

end


subsection \<open>Models of a signature\<close>

text \<open>The interpretation of a type constructor; \<open>\<Rightarrow>\<close> and \<open>prop\<close> are built in.\<close>

definition tycon :: "('u \<Rightarrow> 'u \<Rightarrow> 'u) \<Rightarrow> 'u \<Rightarrow> (name \<Rightarrow> 'u list \<Rightarrow> 'u) \<Rightarrow> name \<Rightarrow> 'u list \<Rightarrow> 'u" where
  "tycon ufun ubool tcon a As =
    (if a = STR ''fun'' \<and> length As = 2 then ufun (As ! 0) (As ! 1)
     else if a = STR ''prop'' \<and> As = [] then ubool
     else tcon a As)"

text \<open>The domain type of \<open>Pure.all\<close> at its instance \<open>(U \<Rightarrow> prop) \<Rightarrow> prop\<close>:\<close>

fun all_dom :: "ptyp \<Rightarrow> ptyp" where
  "all_dom (Type _ (Type _ (U # _) # _)) = U"
| "all_dom _ = undefined"

text \<open>Well-sorted certified type instantiations:\<close>

context pure_sig
begin

definition cinst :: "tinst \<Rightarrow> bool" where
  "cinst \<rho> \<longleftrightarrow> wsinst alg \<rho> \<and> cert_inst \<rho>"

lemma cinstD: "cinst \<rho> \<Longrightarrow> wsinst alg \<rho>" "cinst \<rho> \<Longrightarrow> cert_inst \<rho>"
  unfolding cinst_def by blast+

text \<open>
  The constant \<open>cl_class\<close> of a declared class \<open>cl\<close>, of type \<open>'a itself \<Rightarrow> prop\<close>
  (\<open>Logic.const_of_class\<close>):
\<close>

definition class_const :: "name \<Rightarrow> pclass \<Rightarrow> bool" where
  "class_const c cl \<longleftrightarrow> c = cl + STR ''_class'' \<and> c \<noteq> STR ''Pure.imp'' \<and> c \<noteq> STR ''Pure.all'' \<and>
    cl \<in> classes alg \<and> (\<exists>A. ctab c = Some (Type STR ''itself'' [A] \<rightarrow>\<^sub>T propT))"

lemma literal_append_cancel: "a + s = b + (s :: String.literal) \<Longrightarrow> a = b"
  by (metis String.plus_literal.rep_eq String.explode_inject append_same_eq)

lemma class_const_unique: "class_const c cl \<Longrightarrow> class_const c cl' \<Longrightarrow> cl' = cl"
  unfolding class_const_def using literal_append_cancel by blast

lemma class_const_the: "class_const c cl \<Longrightarrow> (THE cl. class_const c cl) = cl"
  using class_const_unique by blast

end

text \<open>The sorts of the type variables and free type variables of a type:\<close>

fun tsorts :: "ptyp \<Rightarrow> psort set" where
  "tsorts (Type a Ts) = (\<Union>T\<in>set Ts. tsorts T)"
| "tsorts (TFree a S) = {S}"
| "tsorts (TVar v S) = {S}"

text \<open>The sorts of the bindings of a type environment (part of \<open>Envir.insert_sorts\<close>):\<close>

definition tyenv_sorts :: "tyenv \<Rightarrow> psort set" where
  "tyenv_sorts \<theta> = {S'. \<exists>v S U. vt_lookup \<theta> v = Some (S, U) \<and> S' \<in> tsorts U}"

text \<open>A type instantiation whose images have their sorts among those of the variable and \<open>Sh\<close>:\<close>

definition sbound :: "tinst \<Rightarrow> psort set \<Rightarrow> bool" where
  "sbound \<rho>0 Sh \<longleftrightarrow> (\<forall>v S. tsorts (\<rho>0 v S) \<subseteq> insert S Sh)"

fun fun_dom :: "ptyp \<Rightarrow> ptyp" where
  "fun_dom (Type _ (A # _)) = A"
| "fun_dom _ = undefined"

fun itself_arg :: "ptyp \<Rightarrow> ptyp" where
  "itself_arg (Type _ (Type _ (U # _) # _)) = U"
| "itself_arg _ = undefined"

type_synonym 'u tval = "(indexname \<Rightarrow> psort \<Rightarrow> 'u) \<times> (name \<Rightarrow> psort \<Rightarrow> 'u)"
type_synonym 'u vval = "(indexname \<Rightarrow> ptyp \<Rightarrow> 'u) \<times> (name \<Rightarrow> ptyp \<Rightarrow> 'u)"

locale pure_model = pure_sig alg ar ctab + universe umem ufun uapp ulam ubool utrue ufalse
  for alg :: algebra and ar :: "name \<Rightarrow> nat" and ctab :: "name \<Rightarrow> ptyp option"
    and umem :: "'u \<Rightarrow> 'u \<Rightarrow> bool" (infix \<open>\<in>\<^sub>u\<close> 50) and ufun uapp ulam ubool utrue ufalse +
  fixes tcon :: "name \<Rightarrow> 'u list \<Rightarrow> 'u"
    and cls :: "pclass \<Rightarrow> 'u \<Rightarrow> bool"
    and cval :: "name \<Rightarrow> 'u \<Rightarrow> 'u"
  assumes tcon_ne: "(\<And>A. A \<in> set As \<Longrightarrow> une A) \<Longrightarrow> une (tcon a As)"
    and cls_le: "class_le alg c1 c2 \<Longrightarrow> cls c1 A \<Longrightarrow> cls c2 A"
    and cls_arity: "map_of (arities alg a) c = Some Ss \<Longrightarrow> length As = length Ss \<Longrightarrow>
      (\<And>i c'. i < length Ss \<Longrightarrow> c' \<in> set (Ss ! i) \<Longrightarrow> cls c' (As ! i)) \<Longrightarrow>
      cls c (tycon ufun ubool tcon a As)"
    and cval_mem: "une A \<Longrightarrow> cval c A \<in>\<^sub>u A"
begin

abbreviation ucon :: "name \<Rightarrow> 'u list \<Rightarrow> 'u" where
  "ucon \<equiv> tycon ufun ubool tcon"

lemma ucon_fun [simp]: "ucon (STR ''fun'') [A, B] = ufun A B"
  and ucon_prop [simp]: "ucon (STR ''prop'') [] = ubool"
  by (simp_all add: tycon_def)


subsubsection \<open>Types\<close>

fun tsem :: "'u tval \<Rightarrow> ptyp \<Rightarrow> 'u" where
  "tsem \<eta> (Type a Ts) = ucon a (map (tsem \<eta>) Ts)"
| "tsem \<eta> (TFree a S) = snd \<eta> a S"
| "tsem \<eta> (TVar v S) = fst \<eta> v S"

definition ssem :: "psort \<Rightarrow> 'u \<Rightarrow> bool" where
  "ssem S A \<longleftrightarrow> (\<forall>c\<in>set S. cls c A)"

text \<open>
  A sort is inhabited in the model if some nonempty set belongs to its classes; a type is inhabited
  if the sorts of its type variables are:
\<close>

definition sinh :: "psort \<Rightarrow> bool" where
  "sinh S \<longleftrightarrow> (\<exists>A. une A \<and> ssem S A)"

definition tinh :: "ptyp \<Rightarrow> bool" where
  "tinh T \<longleftrightarrow> (\<forall>S\<in>tsorts T. sinh S)"

text \<open>
  Valuations of the type variables by nonempty sets, of their sorts if these are inhabited (the
  sort hypotheses of a theorem state that they are):
\<close>

definition good_t :: "'u tval \<Rightarrow> bool" where
  "good_t \<eta> \<longleftrightarrow> (\<forall>v S. une (fst \<eta> v S) \<and> (sort_ok alg S \<longrightarrow> sinh S \<longrightarrow> ssem S (fst \<eta> v S))) \<and>
    (\<forall>a S. une (snd \<eta> a S) \<and> (sort_ok alg S \<longrightarrow> sinh S \<longrightarrow> ssem S (snd \<eta> a S)))"

lemma tsem_ne:
  assumes "good_t \<eta>"
  shows "une (tsem \<eta> T)"
proof (induction T)
  case (Type a Ts)
  have ne: "une A" if "A \<in> set (map (tsem \<eta>) Ts)" for A
    using that Type.IH by auto
  show ?case
  proof (cases "a = STR ''fun'' \<and> length Ts = 2")
    case True
    then obtain T U where Ts: "Ts = [T, U]" by (auto simp: numeral_2_eq_2 length_Suc_conv)
    have "une (tsem \<eta> U)" using ne Ts by simp
    with True Ts show ?thesis by (simp add: tycon_def une_ufun)
  next
    case False
    have "une (tcon a (map (tsem \<eta>) Ts))" by (rule tcon_ne) (rule ne)
    with False show ?thesis using une_ubool by (auto simp: tycon_def)
  qed
qed (use assms in \<open>auto simp: good_t_def\<close>)

lemma tsem_sort:
  assumes "good_t \<eta>"
  shows "cert_typ alg ar T \<Longrightarrow> tinh T \<Longrightarrow> has_sort alg T S \<Longrightarrow> ssem S (tsem \<eta> T)"
proof (induction T arbitrary: S)
  case (Type a Ts)
  show ?case
    unfolding ssem_def
  proof
    fix c assume c: "c \<in> set S"
    with Type.prems(3) obtain Ss where Ss: "map_of (arities alg a) c = Some Ss" "length Ss = length Ts"
      and hs: "\<forall>i<length Ts. has_sort alg (Ts ! i) (Ss ! i)" by auto
    have "cls c (ucon a (map (tsem \<eta>) Ts))"
    proof (rule cls_arity[OF Ss(1)])
      show "length (map (tsem \<eta>) Ts) = length Ss" using Ss(2) by simp
      fix i c' assume i: "i < length Ss" and c': "c' \<in> set (Ss ! i)"
      have "Ts ! i \<in> set Ts" using i Ss(2) by simp
      moreover have "cert_typ alg ar (Ts ! i)" using Type.prems(1) i Ss(2) by (auto simp: cert_typ_def)
      moreover have "tinh (Ts ! i)" using Type.prems(2) i Ss(2) by (auto simp: tinh_def)
      ultimately have "ssem (Ss ! i) (tsem \<eta> (Ts ! i))" using Type.IH hs i Ss(2) by auto
      with c' i Ss(2) show "cls c' (map (tsem \<eta>) Ts ! i)" by (simp add: ssem_def)
    qed
    then show "cls c (tsem \<eta> (Type a Ts))" by simp
  qed
next
  case (TFree a S')
  have "ssem S' (snd \<eta> a S')" using assms TFree.prems(1,2) by (simp add: good_t_def cert_typ_def tinh_def)
  with TFree.prems(3) show ?case by (auto simp: ssem_def intro: cls_le)
next
  case (TVar v S')
  have "ssem S' (fst \<eta> v S')" using assms TVar.prems(1,2) by (cases v) (simp add: good_t_def cert_typ_def tinh_def)
  with TVar.prems(3) show ?case by (auto simp: ssem_def intro: cls_le)
qed


subsubsection \<open>Terms\<close>

definition imp_val :: 'u where
  "imp_val = ulam ubool (\<lambda>p. ulam ubool (\<lambda>q. ubval (p = utrue \<longrightarrow> q = utrue)))"

definition all_val :: "'u \<Rightarrow> 'u" where
  "all_val A = ulam (ufun A ubool) (\<lambda>f. ubval (\<forall>a. a \<in>\<^sub>u A \<longrightarrow> uapp f a = utrue))"

definition csem :: "'u tval \<Rightarrow> name \<Rightarrow> ptyp \<Rightarrow> 'u" where
  "csem \<eta> c T =
    (if c = STR ''Pure.imp'' then imp_val
     else if c = STR ''Pure.all'' then all_val (tsem \<eta> (all_dom T))
     else if \<exists>cl. class_const c cl then
       ulam (tsem \<eta> (fun_dom T)) (\<lambda>_. ubval (cls (THE cl. class_const c cl) (tsem \<eta> (itself_arg T))))
     else cval c (tsem \<eta> T))"

lemma csem_class:
  assumes cc: "class_const c cl"
  shows "csem \<eta> c T = ulam (tsem \<eta> (fun_dom T)) (\<lambda>_. ubval (cls cl (tsem \<eta> (itself_arg T))))"
proof -
  have "c \<noteq> STR ''Pure.imp''" "c \<noteq> STR ''Pure.all''" "\<exists>cl. class_const c cl"
    using cc by (auto simp: class_const_def)
  then show ?thesis unfolding csem_def using class_const_the[OF cc] by simp
qed

lemma csem_other:
  assumes "c \<noteq> STR ''Pure.imp''" "c \<noteq> STR ''Pure.all''" "\<not> (\<exists>cl. class_const c cl)"
  shows "csem \<eta> c T = cval c (tsem \<eta> T)"
  unfolding csem_def by (simp only: if_not_P[OF assms(1)] if_not_P[OF assms(2)] if_not_P[OF assms(3)])

lemma class_const_typ:
  assumes "class_const c cl" "const_typ_ok ctab c T"
  obtains A where "T = Type STR ''itself'' [A] \<rightarrow>\<^sub>T propT"
proof -
  from assms(1) obtain A0 where "ctab c = Some (Type STR ''itself'' [A0] \<rightarrow>\<^sub>T propT)"
    "c \<noteq> STR ''Pure.imp''" "c \<noteq> STR ''Pure.all''" by (auto simp: class_const_def)
  with assms(2) obtain \<rho> where "T = tsubst \<rho> (Type STR ''itself'' [A0] \<rightarrow>\<^sub>T propT)"
    by (auto simp: const_typ_ok_def)
  then show thesis by (intro that[of "tsubst \<rho> A0"]) (simp add: propT_def)
qed

definition push :: "'u \<Rightarrow> (integer \<Rightarrow> 'u) \<Rightarrow> integer \<Rightarrow> 'u" where
  "push v bv = (\<lambda>j. if j = 0 then v else bv (j - 1))"

fun sem :: "'u tval \<Rightarrow> 'u vval \<Rightarrow> (integer \<Rightarrow> 'u) \<Rightarrow> pterm \<Rightarrow> 'u" where
  "sem \<eta> \<xi> bv (Const c T) = csem \<eta> c T"
| "sem \<eta> \<xi> bv (Free x T) = snd \<xi> x T"
| "sem \<eta> \<xi> bv (Var x T) = fst \<xi> x T"
| "sem \<eta> \<xi> bv (Bound i) = (if 0 \<le> i then bv i else undefined)"
| "sem \<eta> \<xi> bv (Abs a T t) = ulam (tsem \<eta> T) (\<lambda>v. sem \<eta> \<xi> (push v bv) t)"
| "sem \<eta> \<xi> bv (s $ t) = uapp (sem \<eta> \<xi> bv s) (sem \<eta> \<xi> bv t)"

text \<open>Valuations of the term variables in their interpreted types, and of the loose bound variables:\<close>

definition good_v :: "'u tval \<Rightarrow> 'u vval \<Rightarrow> bool" where
  "good_v \<eta> \<xi> \<longleftrightarrow> (\<forall>x T. cert_typ alg ar T \<longrightarrow> fst \<xi> x T \<in>\<^sub>u tsem \<eta> T) \<and>
    (\<forall>a T. cert_typ alg ar T \<longrightarrow> snd \<xi> a T \<in>\<^sub>u tsem \<eta> T)"

definition good :: "'u tval \<Rightarrow> 'u vval \<Rightarrow> bool" where
  "good \<eta> \<xi> \<longleftrightarrow> good_t \<eta> \<and> good_v \<eta> \<xi>"

definition bvals :: "'u tval \<Rightarrow> (integer \<Rightarrow> ptyp) \<Rightarrow> (integer \<Rightarrow> 'u) \<Rightarrow> bool" where
  "bvals \<eta> e bv \<longleftrightarrow> (\<forall>i\<ge>0. bv i \<in>\<^sub>u tsem \<eta> (e i))"

lemma bvals_push: "bvals \<eta> e bv \<Longrightarrow> v \<in>\<^sub>u tsem \<eta> T \<Longrightarrow> bvals \<eta> (e\<langle>0:T\<rangle>) (push v bv)"
  by (auto simp: bvals_def push_def shift_def integer_arith)

lemma goodD: "good \<eta> \<xi> \<Longrightarrow> good_t \<eta>"
  "good \<eta> \<xi> \<Longrightarrow> cert_typ alg ar T \<Longrightarrow> fst \<xi> x T \<in>\<^sub>u tsem \<eta> T"
  "good \<eta> \<xi> \<Longrightarrow> cert_typ alg ar T \<Longrightarrow> snd \<xi> a T \<in>\<^sub>u tsem \<eta> T"
  by (auto simp: good_def good_v_def simp del: split_paired_All)

text \<open>Well-typed terms denote elements of their types:\<close>

theorem sem_typing:
  assumes g: "good \<eta> \<xi>"
  shows "e \<turnstile> t : T \<Longrightarrow> bvals \<eta> e bv \<Longrightarrow> sem \<eta> \<xi> bv t \<in>\<^sub>u tsem \<eta> T"
proof (induction arbitrary: bv rule: typing.induct)
  case (Const c T e)
  show ?case
  proof (cases "c = STR ''Pure.imp''")
    case True
    with Const.hyps(1) have "T = Type STR ''prop'' [] \<rightarrow>\<^sub>T Type STR ''prop'' [] \<rightarrow>\<^sub>T Type STR ''prop'' []"
      by (simp add: const_typ_ok_def)
    with True show ?thesis by (simp add: csem_def imp_val_def ulam_mem)
  next
    case nimp: False
    show ?thesis
    proof (cases "c = STR ''Pure.all''")
      case True
      with Const.hyps(1) nimp obtain U where "T = (U \<rightarrow>\<^sub>T Type STR ''prop'' []) \<rightarrow>\<^sub>T Type STR ''prop'' []"
        by (auto simp: const_typ_ok_def)
      with True nimp show ?thesis by (simp add: csem_def all_val_def ulam_mem)
    next
      case nall: False
      show ?thesis
      proof (cases "\<exists>cl. class_const c cl")
        case True
        then obtain cl where cc: "class_const c cl" by blast
        obtain A where T: "T = Type STR ''itself'' [A] \<rightarrow>\<^sub>T propT" by (rule class_const_typ[OF cc Const.hyps(1)])
        show ?thesis by (simp add: csem_class[OF cc] T propT_def ulam_mem)
      next
        case False
        show ?thesis
          using cval_mem[OF tsem_ne[OF goodD(1)[OF g]]] by (simp add: csem_other[OF nimp nall False])
      qed
    qed
  qed
next
  case (Bound i e T)
  then show ?case by (fastforce simp: bvals_def)
next
  case (Abs T e t U a)
  have "sem \<eta> \<xi> (push v bv) t \<in>\<^sub>u tsem \<eta> U" if "v \<in>\<^sub>u tsem \<eta> T" for v
    using Abs.IH bvals_push[OF Abs.prems that] by blast
  then show ?case by (simp add: ulam_mem)
next
  case (App e s T U t)
  then show ?case by (auto intro: uapp_mem)
qed (use g goodD in auto)


subsubsection \<open>Bound variables\<close>

lemma sem_bv_cong:
  "(\<And>i. 0 \<le> i \<Longrightarrow> loose_bvar1 t i \<Longrightarrow> bv i = bv' i) \<Longrightarrow> sem \<eta> \<xi> bv t = sem \<eta> \<xi> bv' t"
proof (induction t arbitrary: bv bv')
  case (Abs a T t)
  have "sem \<eta> \<xi> (push v bv) t = sem \<eta> \<xi> (push v bv') t" for v
  proof (rule Abs.IH)
    fix i assume "0 \<le> i" "loose_bvar1 t i"
    with Abs.prems[of "i - 1"] show "push v bv i = push v bv' i" by (auto simp: push_def integer_arith)
  qed
  then show ?case by simp
next
  case (App s t)
  have "sem \<eta> \<xi> bv s = sem \<eta> \<xi> bv' s" "sem \<eta> \<xi> bv t = sem \<eta> \<xi> bv' t"
    by (rule App.IH(1), use App.prems in simp) (rule App.IH(2), use App.prems in simp)
  then show ?case by simp
qed simp_all

lemma sem_bv_ext: "(\<And>i. 0 \<le> i \<Longrightarrow> bv i = bv' i) \<Longrightarrow> sem \<eta> \<xi> bv t = sem \<eta> \<xi> bv' t"
  by (rule sem_bv_cong) blast

lemma sem_closed: "closed t \<Longrightarrow> sem \<eta> \<xi> bv t = sem \<eta> \<xi> bv' t"
  by (rule sem_bv_cong) (use loose_bvar1_imp loose_bvar_mono in \<open>fastforce simp: closed_def\<close>)

lemma sem_incr_bv:
  "0 \<le> k \<Longrightarrow> 0 \<le> n \<Longrightarrow> sem \<eta> \<xi> bv (incr_bv n k t) = sem \<eta> \<xi> (\<lambda>i. if i < k then bv i else bv (i + n)) t"
proof (induction t arbitrary: k bv)
  case (Abs a T t)
  have "sem \<eta> \<xi> (push v bv) (incr_bv n (k + 1) t) = sem \<eta> \<xi> (push v (\<lambda>i. if i < k then bv i else bv (i + n))) t"
    for v
  proof -
    have "sem \<eta> \<xi> (push v bv) (incr_bv n (k + 1) t) =
        sem \<eta> \<xi> (\<lambda>i. if i < k + 1 then push v bv i else push v bv (i + n)) t"
      using Abs.IH[of "k + 1"] Abs.prems by simp
    also have "\<dots> = sem \<eta> \<xi> (push v (\<lambda>i. if i < k then bv i else bv (i + n))) t"
      by (rule sem_bv_ext) (use Abs.prems in \<open>auto simp: push_def integer_arith algebra_simps\<close>)
    finally show ?thesis .
  qed
  then show ?case by simp
next
  case (Bound i)
  then show ?case by (simp add: integer_arith)
qed simp_all

lemma sem_subst:
  "0 \<le> k \<Longrightarrow> sem \<eta> \<xi> bv (t[s/k]) =
    sem \<eta> \<xi> (\<lambda>i. if i < k then bv i else if i = k then sem \<eta> \<xi> bv s else bv (i - 1)) t"
proof (induction t arbitrary: k bv s)
  case (Bound i)
  then show ?case by (auto simp: subst_Bound integer_arith)
next
  case (Abs a T t)
  have "sem \<eta> \<xi> (push v bv) (t[lift s 0/k + 1]) =
      sem \<eta> \<xi> (push v (\<lambda>i. if i < k then bv i else if i = k then sem \<eta> \<xi> bv s else bv (i - 1))) t" for v
  proof -
    have l: "sem \<eta> \<xi> (push v bv) (lift s 0) = sem \<eta> \<xi> bv s"
      by (subst sem_incr_bv) (simp_all, rule sem_bv_ext, simp add: push_def integer_arith)
    have "sem \<eta> \<xi> (push v bv) (t[lift s 0/k + 1]) =
        sem \<eta> \<xi> (\<lambda>i. if i < k + 1 then push v bv i
          else if i = k + 1 then sem \<eta> \<xi> (push v bv) (lift s 0) else push v bv (i - 1)) t"
      by (rule Abs.IH) (use Abs.prems in simp)
    also have "\<dots> = sem \<eta> \<xi> (\<lambda>i. if i < k + 1 then push v bv i
          else if i = k + 1 then sem \<eta> \<xi> bv s else push v bv (i - 1)) t"
      by (simp only: l)
    also have "\<dots> = sem \<eta> \<xi> (push v (\<lambda>i. if i < k then bv i else if i = k then sem \<eta> \<xi> bv s else bv (i - 1))) t"
      by (rule sem_bv_ext) (use Abs.prems in \<open>auto simp: push_def integer_arith\<close>)
    finally show ?thesis .
  qed
  then show ?case by simp
qed auto


subsubsection \<open>Conversion\<close>

lemma sem_Abs_cong:
  assumes g: "good \<eta> \<xi>" and ts: "e\<langle>0:A\<rangle> \<turnstile> s : U" and bv: "bvals \<eta> e bv"
    and st: "\<And>v. v \<in>\<^sub>u tsem \<eta> A \<Longrightarrow> sem \<eta> \<xi> (push v bv) s = sem \<eta> \<xi> (push v bv) t"
  shows "sem \<eta> \<xi> bv (Abs a A s) = sem \<eta> \<xi> bv (Abs a A t)"
proof -
  have "ulam (tsem \<eta> A) (\<lambda>v. sem \<eta> \<xi> (push v bv) s) = ulam (tsem \<eta> A) (\<lambda>v. sem \<eta> \<xi> (push v bv) t)"
  proof (rule ulam_cong)
    fix v assume v: "v \<in>\<^sub>u tsem \<eta> A"
    show "sem \<eta> \<xi> (push v bv) s \<in>\<^sub>u tsem \<eta> U" by (rule sem_typing[OF g ts bvals_push[OF bv v]])
    show "sem \<eta> \<xi> (push v bv) s = sem \<eta> \<xi> (push v bv) t" by (rule st[OF v])
  qed
  then show ?thesis by simp
qed

lemma sem_beta:
  assumes g: "good \<eta> \<xi>"
  shows "s \<rightarrow>\<^sub>\<beta> t \<Longrightarrow> e \<turnstile> s : T \<Longrightarrow> bvals \<eta> e bv \<Longrightarrow> sem \<eta> \<xi> bv s = sem \<eta> \<xi> bv t"
proof (induction arbitrary: e T bv rule: beta.induct)
  case (beta a A b u)
  from beta.prems(1) obtain U where tb: "e\<langle>0:A\<rangle> \<turnstile> b : U" and tu: "e \<turnstile> u : A" by auto
  have m: "sem \<eta> \<xi> bv u \<in>\<^sub>u tsem \<eta> A" by (rule sem_typing[OF g tu beta.prems(2)])
  have "sem \<eta> \<xi> bv (b[u/0]) = sem \<eta> \<xi> (push (sem \<eta> \<xi> bv u) bv) b"
    by (subst sem_subst) (simp, rule sem_bv_ext, simp add: push_def)
  with m show ?case by (simp add: uapp_ulam)
next
  case (appL s t u)
  then show ?case by auto
next
  case (appR s t u)
  then show ?case by auto
next
  case (abs s t a A)
  from abs.prems(1) obtain U where ts: "e\<langle>0:A\<rangle> \<turnstile> s : U" by auto
  show ?case by (rule sem_Abs_cong[OF g ts abs.prems(2)]) (rule abs.IH[OF ts bvals_push[OF abs.prems(2)]])
qed

lemma sem_eta:
  assumes g: "good \<eta> \<xi>"
  shows "s \<rightarrow>\<^sub>\<eta> t \<Longrightarrow> e \<turnstile> s : T \<Longrightarrow> bvals \<eta> e bv \<Longrightarrow> sem \<eta> \<xi> bv s = sem \<eta> \<xi> bv t"
proof (induction arbitrary: e T bv rule: eta.induct)
  case (eta s a A d)
  have ty: "e \<turnstile> s[d/0] : T" by (rule subject_reduction_eta[OF eta.eta[OF eta.hyps] eta.prems(1)])
  from eta.prems(1) obtain U where T: "T = A \<rightarrow>\<^sub>T U" by auto
  have f: "sem \<eta> \<xi> bv (s[d/0]) \<in>\<^sub>u ufun (tsem \<eta> A) (tsem \<eta> U)"
    using sem_typing[OF g ty eta.prems(2)] T by simp
  have "sem \<eta> \<xi> (push v bv) s = sem \<eta> \<xi> bv (s[d/0])" for v
    by (subst sem_subst) (simp, rule sem_bv_cong, use eta.hyps in \<open>auto simp: push_def\<close>)
  then have "sem \<eta> \<xi> bv (Abs a A (s $ Bound 0)) = ulam (tsem \<eta> A) (uapp (sem \<eta> \<xi> bv (s[d/0])))"
    by (simp add: push_def)
  with ulam_uapp[OF f] show ?case by simp
next
  case (appL s t u)
  then show ?case by auto
next
  case (appR s t u)
  then show ?case by auto
next
  case (abs s t a A)
  from abs.prems(1) obtain U where ts: "e\<langle>0:A\<rangle> \<turnstile> s : U" by auto
  show ?case by (rule sem_Abs_cong[OF g ts abs.prems(2)]) (rule abs.IH[OF ts bvals_push[OF abs.prems(2)]])
qed

lemma sem_aconv: "aconv_term s t \<Longrightarrow> sem \<eta> \<xi> bv s = sem \<eta> \<xi> bv t"
  by (induction s t arbitrary: bv rule: aconv_term.induct) auto

lemma reds_typing: "(sup beta eta)\<^sup>*\<^sup>* s t \<Longrightarrow> e \<turnstile> s : T \<Longrightarrow> e \<turnstile> t : T"
proof (induction rule: rtranclp_induct)
  case (step t u)
  then have "e \<turnstile> t : T" by simp
  with step.hyps(2) show ?case using subject_reduction_beta subject_reduction_eta by blast
qed simp

lemma sem_reds:
  assumes g: "good \<eta> \<xi>"
  shows "(sup beta eta)\<^sup>*\<^sup>* s t \<Longrightarrow> e \<turnstile> s : T \<Longrightarrow> bvals \<eta> e bv \<Longrightarrow> sem \<eta> \<xi> bv s = sem \<eta> \<xi> bv t"
proof (induction rule: rtranclp_induct)
  case (step t u)
  have ty: "e \<turnstile> t : T" by (rule reds_typing[OF step.hyps(1) step.prems(1)])
  from step.hyps(2) have "sem \<eta> \<xi> bv t = sem \<eta> \<xi> bv u"
    using sem_beta[OF g _ ty step.prems(2)] sem_eta[OF g _ ty step.prems(2)] by auto
  with step.IH step.prems show ?case by simp
qed simp

text \<open>\<open>\<alpha>\<beta>\<eta>\<close>-conversion is sound:\<close>

theorem sem_conv:
  assumes g: "good \<eta> \<xi>" and ts: "e \<turnstile> s : T" and tt: "e \<turnstile> t : T" and c: "s \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> t"
    and bv: "bvals \<eta> e bv"
  shows "sem \<eta> \<xi> bv s = sem \<eta> \<xi> bv t"
proof -
  have "wt s" using ts by (auto simp: wt_def)
  with c obtain u v where r: "(sup beta eta)\<^sup>*\<^sup>* s u" "(sup beta eta)\<^sup>*\<^sup>* t v" and a: "aconv_term u v"
    using conv_iff by blast
  from sem_reds[OF g r(1) ts bv] sem_reds[OF g r(2) tt bv] sem_aconv[OF a] show ?thesis by simp
qed


subsubsection \<open>Instances\<close>

definition tinstv :: "'u tval \<Rightarrow> tinst \<Rightarrow> 'u tval" where
  "tinstv \<eta> \<rho> = (\<lambda>v S. tsem \<eta> (\<rho> v S), snd \<eta>)"

definition vinstv :: "tinst \<Rightarrow> 'u vval \<Rightarrow> 'u vval" where
  "vinstv \<rho> \<xi> = (\<lambda>x T. fst \<xi> x (tsubst \<rho> T), \<lambda>x T. snd \<xi> x (tsubst \<rho> T))"

definition vsubstv :: "'u tval \<Rightarrow> 'u vval \<Rightarrow> vsubst \<Rightarrow> 'u vval" where
  "vsubstv \<eta> \<xi> \<sigma> = (\<lambda>x T. sem \<eta> \<xi> (\<lambda>_. undefined) (\<sigma> x T), snd \<xi>)"

lemma tsem_tsubst: "tsem \<eta> (tsubst \<rho> T) = tsem (tinstv \<eta> \<rho>) T"
proof (induction T)
  case (Type a Ts)
  then show ?case by (simp add: comp_def cong: map_cong)
qed (simp_all add: tinstv_def)

lemma all_dom_tsubst: "all_dom (tsubst \<rho> ((U \<rightarrow>\<^sub>T V) \<rightarrow>\<^sub>T W)) = tsubst \<rho> U"
  by simp

lemma sem_inst:
  "e \<turnstile> t : T \<Longrightarrow> sem \<eta> \<xi> bv (inst \<rho> t) = sem (tinstv \<eta> \<rho>) (vinstv \<rho> \<xi>) bv t"
proof (induction arbitrary: bv rule: typing.induct)
  case (Const c T e)
  show ?case
  proof (cases "c = STR ''Pure.all''")
    case True
    with Const.hyps(1) obtain U where "T = (U \<rightarrow>\<^sub>T Type STR ''prop'' []) \<rightarrow>\<^sub>T Type STR ''prop'' []"
      by (auto simp: const_typ_ok_def)
    with True show ?thesis by (simp add: csem_def tsem_tsubst)
  next
    case nall: False
    show ?thesis
    proof (cases "\<exists>cl. class_const c cl")
      case True
      then obtain cl where cc: "class_const c cl" by blast
      obtain A where T: "T = Type STR ''itself'' [A] \<rightarrow>\<^sub>T propT" by (rule class_const_typ[OF cc Const.hyps(1)])
      show ?thesis by (simp add: csem_class[OF cc] T tsem_tsubst propT_def)
    next
      case False
      show ?thesis
      proof (cases "c = STR ''Pure.imp''")
        case True
        then show ?thesis by (simp add: csem_def)
      next
        case nimp: False
        have "csem \<eta> c (tsubst \<rho> T) = csem (tinstv \<eta> \<rho>) c T"
          by (simp add: csem_other[OF nimp nall False] tsem_tsubst)
        then show ?thesis by simp
      qed
    qed
  qed
qed (simp_all add: vinstv_def tsem_tsubst)

lemma sem_vsubst:
  assumes "closed_subst \<sigma>"
  shows "sem \<eta> \<xi> bv (vsubst \<sigma> t) = sem \<eta> (vsubstv \<eta> \<xi> \<sigma>) bv t"
  by (induction t arbitrary: bv) (simp_all add: vsubstv_def sem_closed[OF closed_substD[OF assms]])

text \<open>The valuation of an instance:\<close>

definition apv_t :: "'u tval \<Rightarrow> tinst \<Rightarrow> 'u tval" where
  "apv_t \<eta> \<rho> = tinstv \<eta> \<rho>"

definition apv_v :: "'u tval \<Rightarrow> 'u vval \<Rightarrow> tinst \<Rightarrow> vsubst \<Rightarrow> 'u vval" where
  "apv_v \<eta> \<xi> \<rho> \<sigma> = vinstv \<rho> (vsubstv \<eta> \<xi> \<sigma>)"

lemma sem_ap:
  "wt_subst \<sigma> \<Longrightarrow> e \<turnstile> t : T \<Longrightarrow> sem \<eta> \<xi> bv (ap \<rho> \<sigma> t) = sem (apv_t \<eta> \<rho>) (apv_v \<eta> \<xi> \<rho> \<sigma>) bv t"
  unfolding ap_def apv_t_def apv_v_def
  by (simp add: sem_vsubst wt_subst_def sem_inst)

text \<open>A type instantiation keeps the inhabited sorts inhabited:\<close>

definition inh_inst :: "tinst \<Rightarrow> bool" where
  "inh_inst \<rho> \<longleftrightarrow> (\<forall>v S. sort_ok alg S \<longrightarrow> sinh S \<longrightarrow> tinh (\<rho> v S))"

lemma inh_inst_TVar: "inh_inst TVar"
  by (simp add: inh_inst_def tinh_def)

lemma tinh_tsubst:
  "inh_inst \<rho> \<Longrightarrow> cert_typ alg ar T \<Longrightarrow> tinh T \<Longrightarrow> tinh (tsubst \<rho> T)"
proof (induction T)
  case (Type a Ts)
  then show ?case by (auto simp: tinh_def cert_typ_def)
next
  case (TVar v S)
  then show ?case by (cases v) (auto simp: inh_inst_def tinh_def cert_typ_def)
qed (simp_all add: tinh_def)

lemma inh_inst_comp: "inh_inst \<rho> \<Longrightarrow> cinst \<rho>0 \<Longrightarrow> inh_inst \<rho>0 \<Longrightarrow> inh_inst (\<lambda>v S. tsubst \<rho> (\<rho>0 v S))"
  unfolding inh_inst_def
proof (intro allI impI)
  fix v S assume r: "\<forall>v S. sort_ok alg S \<longrightarrow> sinh S \<longrightarrow> tinh (\<rho> v S)" and c: "cinst \<rho>0"
    and r0: "\<forall>v S. sort_ok alg S \<longrightarrow> sinh S \<longrightarrow> tinh (\<rho>0 v S)" and S: "sort_ok alg S" "sinh S"
  have "cert_typ alg ar (\<rho>0 v S)" using cinstD(2)[OF c] S(1) by (cases v) (simp add: cert_inst_def)
  then show "tinh (tsubst \<rho> (\<rho>0 v S))" by (rule tinh_tsubst[OF r[folded inh_inst_def]]) (use r0 S in blast)
qed

lemma inh_inst_sbound: "sbound \<rho>0 Sh \<Longrightarrow> (\<And>S. S \<in> Sh \<Longrightarrow> sinh S) \<Longrightarrow> inh_inst \<rho>0"
  unfolding inh_inst_def sbound_def tinh_def by blast

lemma good_ap:
  assumes g: "good \<eta> \<xi>" and \<rho>: "cinst \<rho>" and \<rho>i: "inh_inst \<rho>" and \<sigma>: "wt_subst \<sigma>"
  shows "good (apv_t \<eta> \<rho>) (apv_v \<eta> \<xi> \<rho> \<sigma>)"
proof -
  note gt = goodD(1)[OF g]
  have "good_t (apv_t \<eta> \<rho>)"
    unfolding good_t_def apv_t_def tinstv_def
  proof (intro conjI allI impI)
    fix v S
    show "une (fst (\<lambda>v S. tsem \<eta> (\<rho> v S), snd \<eta>) v S)" using tsem_ne[OF gt] by simp
    assume S: "sort_ok alg S" "sinh S"
    have c: "cert_typ alg ar (\<rho> v S)" using cinstD(2)[OF \<rho>] S by (cases v) (simp add: cert_inst_def)
    have "has_sort alg (\<rho> v S) S" using cinstD(1)[OF \<rho>] by (cases v) (simp add: wsinst_def)
    moreover have "tinh (\<rho> v S)" using \<rho>i S unfolding inh_inst_def by blast
    ultimately show "ssem S (fst (\<lambda>v S. tsem \<eta> (\<rho> v S), snd \<eta>) v S)" using tsem_sort[OF gt c] by simp
  qed (use gt in \<open>simp_all add: good_t_def\<close>)
  moreover have "good_v (apv_t \<eta> \<rho>) (apv_v \<eta> \<xi> \<rho> \<sigma>)"
    unfolding good_v_def
  proof (intro conjI allI impI)
    fix x T assume T: "cert_typ alg ar T"
    have c: "cert_typ alg ar (tsubst \<rho> T)" by (rule cert_typ_tsubst[OF T cinstD(2)[OF \<rho>]])
    have b0: "bvals \<eta> (\<lambda>_. propT) (\<lambda>_. utrue)" by (simp add: bvals_def propT_def ubool_mem)
    have "sem \<eta> \<xi> (\<lambda>_. utrue) (\<sigma> x (tsubst \<rho> T)) \<in>\<^sub>u tsem \<eta> (tsubst \<rho> T)"
      by (rule sem_typing[OF g wt_subst_typing[OF \<sigma> c] b0])
    moreover have "sem \<eta> \<xi> (\<lambda>_. undefined) (\<sigma> x (tsubst \<rho> T)) = sem \<eta> \<xi> (\<lambda>_. utrue) (\<sigma> x (tsubst \<rho> T))"
      by (rule sem_closed) (use \<sigma> in \<open>simp add: wt_subst_def closed_substD\<close>)
    ultimately show "fst (apv_v \<eta> \<xi> \<rho> \<sigma>) x T \<in>\<^sub>u tsem (apv_t \<eta> \<rho>) T"
      by (simp add: apv_v_def apv_t_def vinstv_def vsubstv_def flip: tsem_tsubst)
  next
    fix a T assume T: "cert_typ alg ar T"
    have c: "cert_typ alg ar (tsubst \<rho> T)" by (rule cert_typ_tsubst[OF T cinstD(2)[OF \<rho>]])
    show "snd (apv_v \<eta> \<xi> \<rho> \<sigma>) a T \<in>\<^sub>u tsem (apv_t \<eta> \<rho>) T"
      using goodD(3)[OF g c] by (simp add: apv_v_def apv_t_def vinstv_def vsubstv_def tsem_tsubst)
  qed
  ultimately show ?thesis by (simp add: good_def)
qed


subsubsection \<open>Propositions\<close>

text \<open>A closed proposition is true under a valuation:\<close>

definition holds_at :: "'u tval \<Rightarrow> 'u vval \<Rightarrow> pterm \<Rightarrow> bool" where
  "holds_at \<eta> \<xi> A \<longleftrightarrow> sem \<eta> \<xi> (\<lambda>_. utrue) A = utrue"

lemma sem_implies:
  "sem \<eta> \<xi> bv (implies $ A $ B) = ubval (sem \<eta> \<xi> bv A = utrue \<longrightarrow> sem \<eta> \<xi> bv B = utrue)"
  if "sem \<eta> \<xi> bv A \<in>\<^sub>u ubool" "sem \<eta> \<xi> bv B \<in>\<^sub>u ubool"
  using that by (simp add: implies_def csem_def imp_val_def uapp_ulam ulam_mem)

lemma sem_all:
  "sem \<eta> \<xi> bv (all_const T $ Abs a T b) = ubval (\<forall>v. v \<in>\<^sub>u tsem \<eta> T \<longrightarrow> sem \<eta> \<xi> (push v bv) b = utrue)"
  if "\<And>v. v \<in>\<^sub>u tsem \<eta> T \<Longrightarrow> sem \<eta> \<xi> (push v bv) b \<in>\<^sub>u ubool"
proof -
  have "ulam (tsem \<eta> T) (\<lambda>v. sem \<eta> \<xi> (push v bv) b) \<in>\<^sub>u ufun (tsem \<eta> T) ubool"
    by (rule ulam_mem) (rule that)
  then show ?thesis by (simp add: all_const_def csem_def all_val_def uapp_ulam uapp_ulam[OF _] all_type_def)
qed

end

end

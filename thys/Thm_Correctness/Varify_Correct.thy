section \<open>Soundness of generalizing free type variables\<close>

theory Varify_Correct
  imports Freeze_Correct Generalize_Rule_Correct
begin

subsection \<open>Maps on the atomic types of a term\<close>

abbreviation tmap :: "(ptyp \<Rightarrow> ptyp) \<Rightarrow> pterm \<Rightarrow> pterm" where
  "tmap \<phi> \<equiv> map_types (map_atyps \<phi>)"

lemma map_types_lift [simp]: "map_types f (incr_bv n k t) = incr_bv n k (map_types f t)"
  by (induction n k t rule: incr_bv.induct) auto

lemma map_types_subst [simp]: "map_types f (t[s/k]) = (map_types f t)[map_types f s/k]"
  by (induction t arbitrary: s k) (auto simp: subst_Bound)

lemma loose_bvar1_map_types [simp]: "loose_bvar1 (map_types f t) k = loose_bvar1 t k"
  by (induction t arbitrary: k) auto

lemma loose_bvar_map_types [simp]: "loose_bvar (map_types f t) k = loose_bvar t k"
  by (induction t arbitrary: k) auto

lemma beta_map_types: "s \<rightarrow>\<^sub>\<beta> t \<Longrightarrow> map_types f s \<rightarrow>\<^sub>\<beta> map_types f t"
  by (induction rule: beta.induct) auto

lemma eta_map_types: "s \<rightarrow>\<^sub>\<eta> t \<Longrightarrow> map_types f s \<rightarrow>\<^sub>\<eta> map_types f t"
  by (induction rule: eta.induct) auto

lemma alpha_map_types: "s \<rightarrow>\<^sub>\<alpha> t \<Longrightarrow> map_types f s \<rightarrow>\<^sub>\<alpha> map_types f t"
  by (induction set: alpha) auto

lemma map_types_comp: "map_types f (map_types g t) = map_types (f \<circ> g) t"
  by (induction t) auto

lemma map_atyps_comp: "map_atyps f (map_atyps g T) = map_atyps (\<lambda>A. map_atyps f (g A)) T"
  by (induction T) auto

lemma map_types_cong: "(\<And>U. U \<in> typs t \<Longrightarrow> f U = g U) \<Longrightarrow> map_types f t = map_types g t"
  by (induction t) auto

lemma map_atyps_cong: "(\<And>A. A \<in> set (atyps T) \<Longrightarrow> f A = g A) \<Longrightarrow> map_atyps f T = map_atyps g T"
  by (induction T) auto

lemma map_atyps_id: "(\<And>A. A \<in> set (atyps T) \<Longrightarrow> f A = A) \<Longrightarrow> map_atyps f T = T"
  by (induction T) (auto intro: map_idI)

lemma map_atyps_tsubst:
  "no_tfrees U \<Longrightarrow> map_atyps \<phi> (tsubst \<rho> U) = tsubst (\<lambda>v S. map_atyps \<phi> (\<rho> v S)) U"
  by (induction U) auto

lemma typs_map_types: "typs (map_types f t) = f ` typs t"
  by (induction t) auto

lemma atyps_map_atyps: "set (atyps (map_atyps f T)) = (\<Union>A\<in>set (atyps T). set (atyps (f A)))"
  by (induction T) auto

lemma vars_map_types: "vars (map_types f t) = (\<lambda>(x, T). (x, f T)) ` vars t"
  by (induction t) auto

lemma pfrees_map_types: "pfrees (map_types f t) = (\<lambda>(x, T). (x, f T)) ` pfrees t"
  by (induction t) auto

lemma inst_as_map_types: "inst \<rho> t = map_types (tsubst \<rho>) t"
  by (induction t) simp_all

lemma tsubst_as_map_atyps: "tsubst \<rho> T = map_atyps (\<lambda>A. case A of TVar v S \<Rightarrow> \<rho> v S | _ \<Rightarrow> A) T"
  by (induction T) auto

text \<open>The atomic types of a term:\<close>

definition tatoms :: "pterm \<Rightarrow> ptyp set" where
  "tatoms t = (\<Union>U\<in>typs t. set (atyps U))"

lemma tatoms_simps [simp]:
  "tatoms (s $ t) = tatoms s \<union> tatoms t" "tatoms (Abs a T t) = set (atyps T) \<union> tatoms t"
  "tatoms (Bound i) = {}" "tatoms (Var x T) = set (atyps T)" "tatoms (Const c T) = set (atyps T)"
  "tatoms (Free f T) = set (atyps T)"
  by (auto simp: tatoms_def)

lemma finite_tatoms [simp]: "finite (tatoms t)"
proof -
  have "finite (typs t)" by (induction t) auto
  then show ?thesis unfolding tatoms_def by blast
qed

lemma atyps_atom: "A \<in> set (atyps T) \<Longrightarrow> (\<exists>a S. A = TFree a S) \<or> (\<exists>v S. A = TVar v S)"
  by (induction T) auto

context pure_sig
begin

definition tmap_ok :: "(ptyp \<Rightarrow> ptyp) \<Rightarrow> bool" where
  "tmap_ok \<phi> \<longleftrightarrow> (\<forall>U. cert_typ alg ar U \<longrightarrow> cert_typ alg ar (map_atyps \<phi> U))"

lemma tmap_okI:
  assumes "\<And>a S. sort_ok alg S \<Longrightarrow> cert_typ alg ar (\<phi> (TFree a S))"
    "\<And>v S. sort_ok alg S \<Longrightarrow> cert_typ alg ar (\<phi> (TVar v S))"
  shows "tmap_ok \<phi>"
  unfolding tmap_ok_def
proof (intro allI impI)
  fix U show "cert_typ alg ar U \<Longrightarrow> cert_typ alg ar (map_atyps \<phi> U)"
    using assms by (induction U) (auto simp: cert_typ_def)
qed

lemma const_typ_ok_map_atyps: "const_typ_ok ctab c U \<Longrightarrow> const_typ_ok ctab c (map_atyps \<phi> U)"
  by (auto simp: const_typ_ok_def map_atyps_tsubst) blast

lemma map_atyps_shift: "(\<lambda>j. map_atyps \<phi> ((e\<langle>i:T\<rangle>) j)) = (\<lambda>j. map_atyps \<phi> (e j))\<langle>i:map_atyps \<phi> T\<rangle>"
  by (rule ext) (simp add: shift_def)

lemma typing_tmap:
  "e \<turnstile> t : T \<Longrightarrow> tmap_ok \<phi> \<Longrightarrow> (\<lambda>j. map_atyps \<phi> (e j)) \<turnstile> tmap \<phi> t : map_atyps \<phi> T"
proof (induction rule: typing.induct)
  case (Abs T e t U a)
  then show ?case by (auto simp: map_atyps_shift tmap_ok_def)
qed (auto simp: tmap_ok_def const_typ_ok_map_atyps)

lemma conv_tmap: "s \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> t \<Longrightarrow> tmap_ok \<phi> \<Longrightarrow> tmap \<phi> s \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> tmap \<phi> t"
proof -
  assume \<phi>: "tmap_ok \<phi>"
  have step: "conv_step s t \<Longrightarrow> conv_step (tmap \<phi> s) (tmap \<phi> t)" for s t
    unfolding conv_step_def wt_def
    by (meson alpha_map_types beta_map_types eta_map_types typing_tmap[OF _ \<phi>])
  show "s \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> t \<Longrightarrow> tmap \<phi> s \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> tmap \<phi> t"
    unfolding conv_def by (induction rule: equivclp_induct) (auto intro: equivclp_into_equivclp step)
qed

end

subsection \<open>Semantics of maps on atomic types\<close>

context pure_model
begin

definition tmapv :: "'u tval \<Rightarrow> (ptyp \<Rightarrow> ptyp) \<Rightarrow> 'u tval" where
  "tmapv \<eta> \<phi> = (\<lambda>v S. tsem \<eta> (\<phi> (TVar v S)), \<lambda>a S. tsem \<eta> (\<phi> (TFree a S)))"

definition vmapv :: "(ptyp \<Rightarrow> ptyp) \<Rightarrow> 'u vval \<Rightarrow> 'u vval" where
  "vmapv \<phi> \<xi> = (\<lambda>x T. fst \<xi> x (map_atyps \<phi> T), \<lambda>x T. snd \<xi> x (map_atyps \<phi> T))"

lemma tsem_map_atyps: "tsem \<eta> (map_atyps \<phi> T) = tsem (tmapv \<eta> \<phi>) T"
proof (induction T)
  case (Type a Ts)
  then show ?case by (simp add: comp_def cong: map_cong)
qed (simp_all add: tmapv_def)

lemma sem_tmap:
  "e \<turnstile> t : T \<Longrightarrow> sem \<eta> \<xi> bv (tmap \<phi> t) = sem (tmapv \<eta> \<phi>) (vmapv \<phi> \<xi>) bv t"
proof (induction arbitrary: bv rule: typing.induct)
  case (Const c T e)
  show ?case
  proof (cases "c = STR ''Pure.all''")
    case True
    with Const.hyps(1) obtain U where "T = (U \<rightarrow>\<^sub>T Type STR ''prop'' []) \<rightarrow>\<^sub>T Type STR ''prop'' []"
      by (auto simp: const_typ_ok_def)
    with True show ?thesis by (simp add: csem_def tsem_map_atyps)
  next
    case nall: False
    show ?thesis
    proof (cases "\<exists>cl. class_const c cl")
      case True
      then obtain cl where cc: "class_const c cl" by blast
      obtain A where T: "T = Type STR ''itself'' [A] \<rightarrow>\<^sub>T propT" by (rule class_const_typ[OF cc Const.hyps(1)])
      show ?thesis by (simp add: csem_class[OF cc] T tsem_map_atyps propT_def)
    next
      case False
      show ?thesis
      proof (cases "c = STR ''Pure.imp''")
        case True
        then show ?thesis by (simp add: csem_def)
      next
        case nimp: False
        show ?thesis
        proof (cases "c = STR ''Pure.eq'' \<and> eq_ok")
          case True
          then obtain A where T: "T = A \<rightarrow>\<^sub>T A \<rightarrow>\<^sub>T propT" using Const.hyps(1) eq_ok_typ by blast
          with True show ?thesis by (simp add: csem_eq tsem_map_atyps propT_def)
        next
          case neq: False
          have "csem \<eta> c (map_atyps \<phi> T) = csem (tmapv \<eta> \<phi>) c T"
            by (simp add: csem_other[OF nimp nall False neq] tsem_map_atyps)
          then show ?thesis by simp
        qed
      qed
    qed
  qed
qed (simp_all add: vmapv_def tsem_map_atyps)

text \<open>The semantics depends only on the values of the atomic types that occur:\<close>

lemma tsem_agree:
  "(\<And>A. A \<in> set (atyps U) \<Longrightarrow> tsem \<eta>1 A = tsem \<eta>2 A) \<Longrightarrow> tsem \<eta>1 U = tsem \<eta>2 U"
proof (induction U)
  case (Type a Ts)
  have "map (tsem \<eta>1) Ts = map (tsem \<eta>2) Ts"
    by (rule map_cong[OF HOL.refl]) (use Type.IH Type.prems in auto)
  then show ?case by (simp only: tsem.simps)
qed simp_all

lemma sem_tagree:
  "e \<turnstile> t : T \<Longrightarrow> (\<And>A. A \<in> tatoms t \<Longrightarrow> tsem \<eta>1 A = tsem \<eta>2 A) \<Longrightarrow> sem \<eta>1 \<xi> bv t = sem \<eta>2 \<xi> bv t"
proof (induction arbitrary: bv rule: typing.induct)
  case (Const c T e)
  have ag: "tsem \<eta>1 U = tsem \<eta>2 U" if "set (atyps U) \<subseteq> set (atyps T)" for U
    by (rule tsem_agree) (use that Const.prems in auto)
  show ?case
  proof (cases "c = STR ''Pure.all''")
    case True
    with Const.hyps(1) obtain U where "T = (U \<rightarrow>\<^sub>T Type STR ''prop'' []) \<rightarrow>\<^sub>T Type STR ''prop'' []"
      by (auto simp: const_typ_ok_def)
    with True ag show ?thesis by (simp add: csem_def)
  next
    case nall: False
    show ?thesis
    proof (cases "\<exists>cl. class_const c cl")
      case True
      then obtain cl where cc: "class_const c cl" by blast
      obtain A where T: "T = Type STR ''itself'' [A] \<rightarrow>\<^sub>T propT" by (rule class_const_typ[OF cc Const.hyps(1)])
      have "tsem \<eta>1 A = tsem \<eta>2 A" "tsem \<eta>1 (Type STR ''itself'' [A]) = tsem \<eta>2 (Type STR ''itself'' [A])"
        by (rule ag, simp add: T)+
      then show ?thesis by (simp add: csem_class[OF cc] T propT_def)
    next
      case False
      show ?thesis
      proof (cases "c = STR ''Pure.imp''")
        case True
        then show ?thesis by (simp add: csem_def)
      next
        case nimp: False
        show ?thesis
        proof (cases "c = STR ''Pure.eq'' \<and> eq_ok")
          case True
          then obtain A where T: "T = A \<rightarrow>\<^sub>T A \<rightarrow>\<^sub>T propT" using Const.hyps(1) eq_ok_typ by blast
          have "tsem \<eta>1 A = tsem \<eta>2 A" by (rule ag) (simp add: T)
          with True show ?thesis by (simp add: csem_eq T)
        next
          case neq: False
          show ?thesis using ag[of T] by (simp add: csem_other[OF nimp nall False neq])
        qed
      qed
    qed
  qed
next
  case (Abs T e t U a)
  have "tsem \<eta>1 T = tsem \<eta>2 T" by (rule tsem_agree) (use Abs.prems in auto)
  with Abs show ?case by simp
next
  case (App e t T U u)
  then show ?case by simp
qed simp_all

lemma sem_agree_all:
  assumes "e \<turnstile> t : T" "\<And>A. A \<in> tatoms t \<Longrightarrow> tsem \<eta>1 A = tsem \<eta>2 A"
    "\<And>x U. (x, U) \<in> vars t \<Longrightarrow> fst \<xi>1 x U = fst \<xi>2 x U"
    "\<And>a U. (a, U) \<in> pfrees t \<Longrightarrow> snd \<xi>1 a U = snd \<xi>2 a U"
  shows "sem \<eta>1 \<xi>1 bv t = sem \<eta>2 \<xi>2 bv t"
  using sem_tagree[OF assms(1,2)] sem_agree[OF assms(3,4)] by simp

end


subsection \<open>Generalizing free type variables under an instance\<close>

definition gen_atom :: "(name \<times> psort) set \<Rightarrow> (name \<Rightarrow> psort \<Rightarrow> indexname) \<Rightarrow> ptyp \<Rightarrow> ptyp" where
  "gen_atom A g T = (case T of TFree a S \<Rightarrow> if (a, S) \<in> A then TVar (g a S) S else T | _ \<Rightarrow> T)"

definition has_tf :: "(name \<times> psort) set \<Rightarrow> ptyp \<Rightarrow> bool" where
  "has_tf A U \<longleftrightarrow> (\<exists>(a, S)\<in>A. TFree a S \<in> set (atyps U))"

definition tf_in :: "(name \<times> psort) set \<Rightarrow> pterm \<Rightarrow> bool" where
  "tf_in A t \<longleftrightarrow> (\<exists>(a, S)\<in>A. TFree a S \<in> tatoms t)"

lemma atyps_atom_self: "A \<in> set (atyps T) \<Longrightarrow> atyps A = [A]"
  by (induction T) auto

lemma tvars_atyps: "(v, S) \<in> tvars T \<longleftrightarrow> TVar v S \<in> set (atyps T)"
  by (induction T) auto

lemma ttvars_tatoms: "(v, S) \<in> ttvars t \<longleftrightarrow> TVar v S \<in> tatoms t"
  by (auto simp: ttvars_def tatoms_def tvars_atyps)

lemma atyps_tsubst:
  "B \<in> set (atyps (tsubst \<rho> T)) \<Longrightarrow> B \<in> set (atyps T) \<or> (\<exists>(v, S)\<in>tvars T. B \<in> set (atyps (\<rho> v S)))"
  by (induction T) fastforce+

lemma tfree_atyps_tsubst: "TFree a S \<in> set (atyps T) \<Longrightarrow> TFree a S \<in> set (atyps (tsubst \<rho> T))"
  by (induction T) auto

lemma has_tf_tsubst: "has_tf A (tsubst \<rho> T) \<Longrightarrow> has_tf A T \<or> (\<exists>(v, S)\<in>tvars T. has_tf A (\<rho> v S))"
  unfolding has_tf_def using atyps_tsubst by fastforce

lemma vars_typ_atoms: "(x, T) \<in> vars t \<Longrightarrow> set (atyps T) \<subseteq> tatoms t"
  by (induction t) auto

lemma pfrees_typ_atoms: "(x, T) \<in> pfrees t \<Longrightarrow> set (atyps T) \<subseteq> tatoms t"
  by (induction t) auto

lemma vars_typ_tvars: "(x, T) \<in> vars t \<Longrightarrow> tvars T \<subseteq> ttvars t"
  by (induction t) auto

lemma pfrees_typ_tvars: "(x, T) \<in> pfrees t \<Longrightarrow> tvars T \<subseteq> ttvars t"
  by (induction t) auto

lemma has_tf_vars: "(x, T) \<in> vars t \<Longrightarrow> has_tf A T \<Longrightarrow> tf_in A t"
  using vars_typ_atoms by (fastforce simp: has_tf_def tf_in_def)

lemma has_tf_pfrees: "(x, T) \<in> pfrees t \<Longrightarrow> has_tf A T \<Longrightarrow> tf_in A t"
  using pfrees_typ_atoms by (fastforce simp: has_tf_def tf_in_def)

lemma tf_in_typs: "tf_in A t \<longleftrightarrow> (\<exists>U\<in>typs t. has_tf A U)"
  by (auto simp: tf_in_def has_tf_def tatoms_def)

lemma tf_in_inst: "tf_in A (inst \<rho> t) \<Longrightarrow> tf_in A t \<or> (\<exists>(v, S)\<in>ttvars t. has_tf A (\<rho> v S))"
  unfolding tf_in_typs inst_as_map_types typs_map_types ttvars_def
  using has_tf_tsubst by fastforce

lemma tatoms_vsubst:
  "B \<in> tatoms (vsubst \<sigma> t) \<Longrightarrow> B \<in> tatoms t \<or> (\<exists>(x, U)\<in>vars t. B \<in> tatoms (\<sigma> x U))"
  by (induction t) auto

lemma tf_in_vsubst: "tf_in A (vsubst \<sigma> t) \<Longrightarrow> tf_in A t \<or> (\<exists>(x, U)\<in>vars t. tf_in A (\<sigma> x U))"
  unfolding tf_in_def using tatoms_vsubst by fastforce

lemma has_tf_atom: "B \<in> set (atyps U) \<Longrightarrow> has_tf A B \<Longrightarrow> has_tf A U"
  using atyps_atom_self by (fastforce simp: has_tf_def)

lemma map_atyps_has_tf_id:
  assumes "\<not> has_tf A U" "\<And>a S. (a, S) \<notin> A \<Longrightarrow> \<psi> (TFree a S) = TFree a S" "\<And>v S. \<psi> (TVar v S) = TVar v S"
  shows "map_atyps \<psi> U = U"
proof (rule map_atyps_id)
  fix B assume B: "B \<in> set (atyps U)"
  from atyps_atom[OF B] show "\<psi> B = B"
  proof (elim disjE exE)
    fix a S assume "B = TFree a S"
    with B assms(1) have "(a, S) \<notin> A" by (auto simp: has_tf_def)
    with \<open>B = TFree a S\<close> show ?thesis by (simp add: assms(2))
  qed (simp add: assms(3))
qed

context pure_sig
begin

lemma typing_vars_cert': "e \<turnstile> t : T \<Longrightarrow> (x, U) \<in> vars t \<Longrightarrow> cert_typ alg ar U"
  by (induction rule: typing.induct) auto

lemma typing_ap_wtp0: "wtp X \<Longrightarrow> cinst \<rho> \<Longrightarrow> gsubst \<sigma> \<Longrightarrow> (\<lambda>j. propT) \<turnstile> ap \<rho> \<sigma> X : propT"
proof -
  assume X: "wtp X" and \<rho>: "cinst \<rho>" and \<sigma>: "gsubst \<sigma>"
  have "(\<lambda>j. tsubst \<rho> propT) \<turnstile> inst \<rho> X : tsubst \<rho> propT"
    by (rule typing_inst[OF wtpD(2)[OF X] cert_inst_inst_ok[OF cinstD(2)[OF \<rho>]]])
  then have "(\<lambda>j. propT) \<turnstile> inst \<rho> X : propT" by (simp add: propT_def)
  then show ?thesis by (rule typing_ap[OF _ gsubstD(1)[OF \<sigma>]])
qed

lemma tmap_ok_gen_atom: "tmap_ok (gen_atom A g)"
  by (rule tmap_okI) (auto simp: gen_atom_def cert_typ_def)

end

context pure_model
begin

lemma holds_gen_inst:
  assumes v: "valid Sh hs tps P" and wP: "wtp P" and wh: "\<And>h. h \<in> set hs \<Longrightarrow> wtp h"
    and nh: "\<And>h. h \<in> set hs \<Longrightarrow> \<not> tf_in A h"
    and nt: "\<And>t u. (t, u) \<in> set tps \<Longrightarrow> \<not> tf_in A t \<and> \<not> tf_in A u"
    and sh: "\<And>S. S \<in> Sh \<Longrightarrow> sinh S" and g: "good \<eta> \<xi>" and \<rho>: "cinst \<rho>" and \<rho>i: "inh_inst \<rho>"
    and \<sigma>: "gsubst \<sigma>"
    and R1: "\<And>X v S. X \<in> thm_terms hs tps P \<Longrightarrow> (v, S) \<in> ttvars X \<Longrightarrow> \<not> has_tf A (\<rho> v S)"
    and R2: "\<And>X x U. X \<in> thm_terms hs tps P \<Longrightarrow> (x, U) \<in> vars (inst \<rho> X) \<Longrightarrow> \<not> has_tf A U \<Longrightarrow>
      \<not> tf_in A (\<sigma> x U)"
    and sol: "\<And>t u. (t, u) \<in> set tps \<Longrightarrow> ap \<rho> \<sigma> t \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma> u"
    and hh: "\<And>h. h \<in> set hs \<Longrightarrow> holds_at \<eta> \<xi> (ap \<rho> \<sigma> h)"
  shows "holds_at \<eta> \<xi> (ap \<rho> \<sigma> (tmap (gen_atom A g) P))"
proof -
  let ?Ts = "thm_terms hs tps P" and ?gA = "gen_atom A g"
  define \<psi> where "\<psi> B = (case B of TFree a S \<Rightarrow> if (a, S) \<in> A then \<rho> (g a S) S else B | _ \<Rightarrow> B)" for B
  define \<eta>2 where "\<eta>2 = tmapv \<eta> \<psi>"
  define \<xi>2 where "\<xi>2 = (\<lambda>x U. if has_tf A U then sem \<eta> \<xi> (\<lambda>_. undefined) (\<sigma> x (map_atyps \<psi> U)) else fst \<xi> x U,
    \<lambda>x U. snd \<xi> x (map_atyps \<psi> U))"
  define \<sigma>P where "\<sigma>P x U = (if has_tf A U then Var x U else \<sigma> x U)" for x U
  have \<psi>id: "map_atyps \<psi> U = U" if "\<not> has_tf A U" for U
    by (rule map_atyps_has_tf_id[OF that]) (simp_all add: \<psi>_def)
  have c\<psi>: "tmap_ok \<psi>"
  proof (rule tmap_okI)
    fix a S assume S: "sort_ok alg S"
    have "cert_typ alg ar (\<rho> (g a S) S)" using cinstD(2)[OF \<rho>] S by (cases "g a S") (simp add: cert_inst_def)
    then show "cert_typ alg ar (\<psi> (TFree a S))" using S by (simp add: \<psi>_def cert_typ_def)
  qed (simp add: \<psi>_def cert_typ_def)
  have ws: "wt_subst \<sigma>" by (rule gsubstD(1)[OF \<sigma>])
  have b0: "bvals \<eta> (\<lambda>_. propT) (\<lambda>_. utrue)" by (simp add: bvals_def propT_def ubool_mem)
  have mem\<sigma>: "sem \<eta> \<xi> (\<lambda>_. undefined) (\<sigma> x U) \<in>\<^sub>u tsem \<eta> U" if c: "cert_typ alg ar U" for x U
  proof -
    have "sem \<eta> \<xi> (\<lambda>_. utrue) (\<sigma> x U) \<in>\<^sub>u tsem \<eta> U" by (rule sem_typing[OF g wt_subst_typing[OF ws c] b0])
    moreover have "sem \<eta> \<xi> (\<lambda>_. undefined) (\<sigma> x U) = sem \<eta> \<xi> (\<lambda>_. utrue) (\<sigma> x U)"
      by (rule sem_closed, rule closed_substD[OF gsubstD(2)[OF \<sigma>]])
    ultimately show ?thesis by simp
  qed
  have ts2: "tsem \<eta>2 U = tsem \<eta> (map_atyps \<psi> U)" for U by (simp add: \<eta>2_def tsem_map_atyps)
  have g2: "good \<eta>2 \<xi>2"
  proof -
    have ga: "good_t (apv_t \<eta> \<rho>)" by (rule goodD(1)[OF good_ap[OF g \<rho> \<rho>i ws]])
    have gt: "good_t \<eta>" by (rule goodD(1)[OF g])
    have "good_t \<eta>2"
      unfolding good_t_def
    proof (intro conjI allI impI)
      fix v S
      show "une (fst \<eta>2 v S)" using gt by (cases v) (simp add: \<eta>2_def tmapv_def \<psi>_def good_t_def)
      show "sort_ok alg S \<Longrightarrow> sinh S \<Longrightarrow> ssem S (fst \<eta>2 v S)"
        using gt by (cases v) (simp add: \<eta>2_def tmapv_def \<psi>_def good_t_def)
    next
      fix a S
      show "une (snd \<eta>2 a S)"
        using gt ga by (cases "g a S") (simp add: \<eta>2_def tmapv_def \<psi>_def good_t_def apv_t_def tinstv_def)
      show "sort_ok alg S \<Longrightarrow> sinh S \<Longrightarrow> ssem S (snd \<eta>2 a S)"
        using gt ga by (cases "g a S") (simp add: \<eta>2_def tmapv_def \<psi>_def good_t_def apv_t_def tinstv_def)
    qed
    moreover have "good_v \<eta>2 \<xi>2"
      unfolding good_v_def
    proof (intro conjI allI impI)
      fix x U assume c: "cert_typ alg ar U"
      have c': "cert_typ alg ar (map_atyps \<psi> U)" using c\<psi> c by (simp add: tmap_ok_def)
      show "fst \<xi>2 x U \<in>\<^sub>u tsem \<eta>2 U"
      proof (cases "has_tf A U")
        case True
        then show ?thesis using mem\<sigma>[OF c'] by (simp add: \<xi>2_def ts2)
      next
        case False
        then show ?thesis using goodD(2)[OF g c] by (simp add: \<xi>2_def ts2 \<psi>id)
      qed
    next
      fix a U assume c: "cert_typ alg ar U"
      have c': "cert_typ alg ar (map_atyps \<psi> U)" using c\<psi> c by (simp add: tmap_ok_def)
      show "snd \<xi>2 a U \<in>\<^sub>u tsem \<eta>2 U" using goodD(3)[OF g c'] by (simp add: \<xi>2_def ts2)
    qed
    ultimately show ?thesis by (simp add: good_def)
  qed
  have \<sigma>P: "gsubst \<sigma>P"
    unfolding gsubst_def wt_subst_def closed_subst_def
  proof (intro conjI allI impI)
    fix x U
    show "closed (\<sigma>P x U)"
      using closed_substD[OF gsubstD(2)[OF \<sigma>]] by (simp add: \<sigma>P_def closed_def)
    assume "cert_typ alg ar U"
    then show "\<exists>e. e \<turnstile> \<sigma>P x U : U"
      using wt_subst_typing[OF ws] by (auto simp: \<sigma>P_def)
  qed
  have nU: "\<not> has_tf A U" if X: "X \<in> ?Ts" "\<not> tf_in A X" and xU: "(x, U) \<in> vars (inst \<rho> X)" for X x U
  proof
    assume "has_tf A U"
    then have "tf_in A (inst \<rho> X)" by (rule has_tf_vars[OF xU])
    with tf_in_inst X R1 show False by blast
  qed
  have apeq: "ap \<rho> \<sigma>P X = ap \<rho> \<sigma> X" if X: "X \<in> ?Ts" "\<not> tf_in A X" for X
    unfolding ap_def by (rule vsubst_cong) (use nU[OF X] in \<open>simp add: \<sigma>P_def\<close>)
  have nap: "\<not> tf_in A (ap \<rho> \<sigma> X)" if X: "X \<in> ?Ts" "\<not> tf_in A X" for X
  proof
    assume "tf_in A (ap \<rho> \<sigma> X)"
    then have "tf_in A (inst \<rho> X) \<or> (\<exists>(x, U)\<in>vars (inst \<rho> X). tf_in A (\<sigma> x U))"
      unfolding ap_def by (rule tf_in_vsubst)
    then show False
    proof
      assume "tf_in A (inst \<rho> X)"
      with tf_in_inst X R1 show False by blast
    next
      assume "\<exists>(x, U)\<in>vars (inst \<rho> X). tf_in A (\<sigma> x U)"
      with R2[OF X(1)] nU[OF X] show False by blast
    qed
  qed
  have agree: "sem \<eta>2 \<xi>2 bv Y = sem \<eta> \<xi> bv Y" if Y: "e \<turnstile> Y : T" "\<not> tf_in A Y" for e Y T bv
  proof (rule sem_agree_all[OF Y(1)])
    fix B assume B: "B \<in> tatoms Y"
    have "\<not> has_tf A B"
    proof
      assume "has_tf A B"
      with B atyps_atom_self[of B] have "tf_in A Y"
        unfolding has_tf_def tf_in_def tatoms_def by force
      with Y(2) show False by blast
    qed
    then show "tsem \<eta>2 B = tsem \<eta> B" by (simp add: ts2 \<psi>id)
  next
    fix x U assume "(x, U) \<in> vars Y"
    with Y(2) have "\<not> has_tf A U" using has_tf_vars by blast
    then show "fst \<xi>2 x U = fst \<xi> x U" by (simp add: \<xi>2_def)
  next
    fix a U assume "(a, U) \<in> pfrees Y"
    with Y(2) have "\<not> has_tf A U" using has_tf_pfrees by blast
    then show "snd \<xi>2 a U = snd \<xi> a U" by (simp add: \<xi>2_def \<psi>id)
  qed
  have Ts: "P \<in> ?Ts" "\<And>h. h \<in> set hs \<Longrightarrow> h \<in> ?Ts" "\<And>t u. (t, u) \<in> set tps \<Longrightarrow> t \<in> ?Ts \<and> u \<in> ?Ts"
    by (force simp: thm_terms_def)+
  have tps': "ap \<rho> \<sigma>P t \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma>P u" if "(t, u) \<in> set tps" for t u
    using sol[OF that] apeq Ts(3)[OF that] nt[OF that] by simp
  have hs': "holds_at \<eta>2 \<xi>2 (ap \<rho> \<sigma>P h)" if h: "h \<in> set hs" for h
  proof -
    have "(\<lambda>j. propT) \<turnstile> ap \<rho> \<sigma> h : propT" by (rule typing_ap_wtp0[OF wh[OF h] \<rho> \<sigma>])
    with agree[OF this nap[OF Ts(2)[OF h] nh[OF h]]] hh[OF h] show ?thesis
      by (simp add: apeq[OF Ts(2)[OF h] nh[OF h]] holds_at_def)
  qed
  have HP: "holds_at \<eta>2 \<xi>2 (ap \<rho> \<sigma>P P)" by (rule validD[OF v sh g2 \<rho> \<rho>i \<sigma>P tps' hs'])
  have tP: "e \<turnstile> P : propT" for e by (rule wtpD(2)[OF wP])
  have tP': "e \<turnstile> tmap ?gA P : propT" for e
  proof -
    have "(\<lambda>j. map_atyps ?gA (propT)) \<turnstile> tmap ?gA P : map_atyps ?gA propT"
      by (rule typing_tmap[OF tP tmap_ok_gen_atom])
    then have "(\<lambda>j. propT) \<turnstile> tmap ?gA P : propT" by (simp add: propT_def)
    moreover have "closed (tmap ?gA P)" using wtpD(1)[OF wP] by (simp add: closed_def)
    ultimately show ?thesis by (rule typing_closed)
  qed
  have key: "tsubst \<rho> (map_atyps ?gA T) = map_atyps \<psi> (tsubst \<rho> T)" if T: "tvars T \<subseteq> ttvars P" for T
    unfolding tsubst_as_map_atyps map_atyps_comp
  proof (rule map_atyps_cong)
    fix B assume B: "B \<in> set (atyps T)"
    from atyps_atom[OF B] show "map_atyps (\<lambda>A. case A of TVar v S \<Rightarrow> \<rho> v S | _ \<Rightarrow> A) (?gA B) =
        map_atyps \<psi> (case B of TVar v S \<Rightarrow> \<rho> v S | _ \<Rightarrow> B)"
    proof (elim disjE exE)
      fix v S assume BV: "B = TVar v S"
      with B T have "(v, S) \<in> ttvars P" by (auto simp: tvars_atyps)
      then have "\<not> has_tf A (\<rho> v S)" by (rule R1[OF Ts(1)])
      then have "map_atyps \<psi> (\<rho> v S) = \<rho> v S" by (rule \<psi>id)
      with BV show ?thesis by (simp add: gen_atom_def)
    qed (auto simp: gen_atom_def \<psi>_def)
  qed
  have "sem (tmapv (apv_t \<eta> \<rho>) ?gA) (vmapv ?gA (apv_v \<eta> \<xi> \<rho> \<sigma>)) bv P =
      sem (apv_t \<eta>2 \<rho>) (apv_v \<eta>2 \<xi>2 \<rho> \<sigma>P) bv P" for bv
  proof (rule sem_agree_all[OF tP])
    fix B assume B: "B \<in> tatoms P"
    then obtain U where U: "U \<in> typs P" "B \<in> set (atyps U)" by (auto simp: tatoms_def)
    from atyps_atom[OF U(2)] show "tsem (tmapv (apv_t \<eta> \<rho>) ?gA) B = tsem (apv_t \<eta>2 \<rho>) B"
    proof (elim disjE exE)
      fix v S assume BV: "B = TVar v S"
      with B have "(v, S) \<in> ttvars P" by (simp add: ttvars_tatoms)
      then have "map_atyps \<psi> (\<rho> v S) = \<rho> v S" by (rule \<psi>id[OF R1[OF Ts(1)]])
      with BV show ?thesis
        by (simp add: tmapv_def gen_atom_def apv_t_def tinstv_def ts2)
    next
      fix a S assume "B = TFree a S"
      then show ?thesis
        by (simp add: tmapv_def gen_atom_def apv_t_def tinstv_def \<eta>2_def \<psi>_def)
    qed
  next
    fix x T assume xT: "(x, T) \<in> vars P"
    have k: "tsubst \<rho> (map_atyps ?gA T) = map_atyps \<psi> (tsubst \<rho> T)"
      by (rule key[OF vars_typ_tvars[OF xT]])
    show "fst (vmapv ?gA (apv_v \<eta> \<xi> \<rho> \<sigma>)) x T = fst (apv_v \<eta>2 \<xi>2 \<rho> \<sigma>P) x T"
    proof (cases "has_tf A (tsubst \<rho> T)")
      case True
      then show ?thesis by (simp add: vmapv_def apv_v_def vinstv_def vsubstv_def k \<sigma>P_def \<xi>2_def)
    next
      case False
      have xU: "(x, tsubst \<rho> T) \<in> vars (inst \<rho> P)" using xT by (auto simp: vars_inst)
      have c: "cert_typ alg ar (tsubst \<rho> T)"
        by (rule cert_typ_tsubst[OF typing_vars_cert'[OF tP xT] cinstD(2)[OF \<rho>]])
      have "sem \<eta>2 \<xi>2 (\<lambda>_. undefined) (\<sigma> x (tsubst \<rho> T)) = sem \<eta> \<xi> (\<lambda>_. undefined) (\<sigma> x (tsubst \<rho> T))"
        by (rule agree[OF wt_subst_typing[OF ws c] R2[OF Ts(1) xU False]])
      with False show ?thesis
        by (simp add: vmapv_def apv_v_def vinstv_def vsubstv_def k \<sigma>P_def \<psi>id)
    qed
  next
    fix a T assume aT: "(a, T) \<in> pfrees P"
    have k: "tsubst \<rho> (map_atyps ?gA T) = map_atyps \<psi> (tsubst \<rho> T)"
      by (rule key[OF pfrees_typ_tvars[OF aT]])
    show "snd (vmapv ?gA (apv_v \<eta> \<xi> \<rho> \<sigma>)) a T = snd (apv_v \<eta>2 \<xi>2 \<rho> \<sigma>P) a T"
      by (simp add: vmapv_def apv_v_def vinstv_def vsubstv_def k \<xi>2_def)
  qed
  then have "sem \<eta> \<xi> bv (ap \<rho> \<sigma> (tmap ?gA P)) = sem \<eta>2 \<xi>2 bv (ap \<rho> \<sigma>P P)" for bv
    using sem_ap[OF ws tP'] sem_tmap[OF tP] sem_ap[OF gsubstD(1)[OF \<sigma>P] tP] by simp
  with HP show ?thesis by (simp add: holds_at_def)
qed

end


subsection \<open>Renaming free type variables\<close>

definition ren :: "(name \<Rightarrow> psort \<Rightarrow> name) \<Rightarrow> ptyp \<Rightarrow> ptyp" where
  "ren p T = (case T of TFree a S \<Rightarrow> TFree (p a S) S | _ \<Rightarrow> T)"

lemma ren_simps [simp]: "ren p (TFree a S) = TFree (p a S) S" "ren p (TVar v S) = TVar v S"
  by (simp_all add: ren_def)

lemma map_atyps_ren_tsubst:
  "map_atyps (ren p) (tsubst \<rho> T) = tsubst (\<lambda>v S. map_atyps (ren p) (\<rho> v S)) (map_atyps (ren p) T)"
  by (induction T) auto

lemma tmap_ren_inst:
  "tmap (ren p) (inst \<rho> t) = inst (\<lambda>v S. map_atyps (ren p) (\<rho> v S)) (tmap (ren p) t)"
  by (induction t) (auto simp: map_atyps_ren_tsubst)

lemma tsorts_map_atyps_ren: "tsorts (map_atyps (ren p) T) = tsorts T"
  by (induction T) auto

lemma has_sort_map_atyps_ren: "has_sort alg (map_atyps (ren p) T) S \<longleftrightarrow> has_sort alg T S"
proof (induction T arbitrary: S)
  case (Type a Ts)
  have "(\<forall>i<length Ts. has_sort alg (map (map_atyps (ren p)) Ts ! i) (Ss ! i)) \<longleftrightarrow>
      (\<forall>i<length Ts. has_sort alg (Ts ! i) (Ss ! i))" for Ss
    using Type.IH by auto
  then show ?case by simp
qed auto

locale ren_inv =
  fixes p :: "name \<Rightarrow> psort \<Rightarrow> name"
  assumes inv: "\<And>a S. p (p a S) S = a"
begin

lemma map_atyps_ren_ren [simp]: "map_atyps (ren p) (map_atyps (ren p) T) = T"
  by (induction T) (auto simp: inv intro: map_idI)

lemma tmap_ren_ren [simp]: "tmap (ren p) (tmap (ren p) t) = t"
  by (induction t) auto

lemma tmap_ren_vsubst:
  "tmap (ren p) (vsubst \<sigma> t) = vsubst (\<lambda>x U. tmap (ren p) (\<sigma> x (map_atyps (ren p) U))) (tmap (ren p) t)"
  by (induction t) auto

end

context pure_sig
begin

lemma tmap_ok_ren: "tmap_ok (ren p)"
  by (rule tmap_okI) (simp_all add: cert_typ_def)

lemma tmap_ren_ap:
  "ren_inv p \<Longrightarrow> tmap (ren p) (ap \<rho> \<sigma> t) =
    ap (\<lambda>v S. map_atyps (ren p) (\<rho> v S)) (\<lambda>x U. tmap (ren p) (\<sigma> x (map_atyps (ren p) U))) (tmap (ren p) t)"
  by (simp add: ap_def ren_inv.tmap_ren_vsubst tmap_ren_inst)

lemma wtp_tmap: "wtp t \<Longrightarrow> tmap_ok \<phi> \<Longrightarrow> wtp (tmap \<phi> t)"
proof -
  assume t: "wtp t" and \<phi>: "tmap_ok \<phi>"
  have "(\<lambda>j. map_atyps \<phi> propT) \<turnstile> tmap \<phi> t : map_atyps \<phi> propT"
    by (rule typing_tmap[OF wtpD(2)[OF t] \<phi>])
  then have "(\<lambda>j. propT) \<turnstile> tmap \<phi> t : propT" by (simp add: propT_def)
  moreover have "closed (tmap \<phi> t)" using wtpD(1)[OF t] by (simp add: closed_def)
  ultimately show ?thesis using wtpI by blast
qed

end

context pure_model
begin

lemma tmapv_ren_ren: "ren_inv p \<Longrightarrow> tmapv (tmapv \<eta> (ren p)) (ren p) = \<eta>"
  by (simp add: tmapv_def ren_inv.inv)

lemma vmapv_ren_ren: "ren_inv p \<Longrightarrow> vmapv (ren p) (vmapv (ren p) \<xi>) = \<xi>"
  by (simp add: vmapv_def ren_inv.map_atyps_ren_ren)

lemma sem_tmap_ren:
  assumes "ren_inv p" "e \<turnstile> t : T"
  shows "sem (tmapv \<eta> (ren p)) (vmapv (ren p) \<xi>) bv (tmap (ren p) t) = sem \<eta> \<xi> bv t"
  using sem_tmap[OF assms(2), of "tmapv \<eta> (ren p)" "vmapv (ren p) \<xi>" bv "ren p"]
  by (simp add: tmapv_ren_ren[OF assms(1)] vmapv_ren_ren[OF assms(1)])

lemma good_ren: "good \<eta> \<xi> \<Longrightarrow> good (tmapv \<eta> (ren p)) (vmapv (ren p) \<xi>)"
proof -
  assume g: "good \<eta> \<xi>"
  note gt = goodD(1)[OF g]
  have "good_t (tmapv \<eta> (ren p))" using gt by (simp add: good_t_def tmapv_def)
  moreover have "good_v (tmapv \<eta> (ren p)) (vmapv (ren p) \<xi>)"
    unfolding good_v_def
  proof (intro conjI allI impI)
    fix x T assume "cert_typ alg ar T"
    then have c: "cert_typ alg ar (map_atyps (ren p) T)" using tmap_ok_ren by (simp add: tmap_ok_def)
    show "fst (vmapv (ren p) \<xi>) x T \<in>\<^sub>u tsem (tmapv \<eta> (ren p)) T"
      using goodD(2)[OF g c] by (simp add: vmapv_def tsem_map_atyps)
  next
    fix x T assume "cert_typ alg ar T"
    then have c: "cert_typ alg ar (map_atyps (ren p) T)" using tmap_ok_ren by (simp add: tmap_ok_def)
    show "snd (vmapv (ren p) \<xi>) x T \<in>\<^sub>u tsem (tmapv \<eta> (ren p)) T"
      using goodD(3)[OF g c] by (simp add: vmapv_def tsem_map_atyps)
  qed
  ultimately show ?thesis by (simp add: good_def)
qed

lemma cinst_ren: "cinst \<rho> \<Longrightarrow> cinst (\<lambda>v S. map_atyps (ren p) (\<rho> v S))"
  using tmap_ok_ren[of p]
  by (auto simp: cinst_def wsinst_def cert_inst_def has_sort_map_atyps_ren tmap_ok_def)

lemma inh_inst_ren: "inh_inst \<rho> \<Longrightarrow> inh_inst (\<lambda>v S. map_atyps (ren p) (\<rho> v S))"
  by (simp add: inh_inst_def tinh_def tsorts_map_atyps_ren)

lemma gsubst_ren:
  assumes "ren_inv p" "gsubst \<sigma>"
  shows "gsubst (\<lambda>x U. tmap (ren p) (\<sigma> x (map_atyps (ren p) U)))"
  unfolding gsubst_def wt_subst_def closed_subst_def
proof (intro conjI allI impI)
  fix x U
  show "closed (tmap (ren p) (\<sigma> x (map_atyps (ren p) U)))"
    using closed_substD[OF gsubstD(2)[OF assms(2)]] by (simp add: closed_def)
  assume "cert_typ alg ar U"
  then have "cert_typ alg ar (map_atyps (ren p) U)" using tmap_ok_ren by (simp add: tmap_ok_def)
  then have "(\<lambda>j. propT) \<turnstile> \<sigma> x (map_atyps (ren p) U) : map_atyps (ren p) U"
    by (rule wt_subst_typing[OF gsubstD(1)[OF assms(2)]])
  from typing_tmap[OF this tmap_ok_ren[of p]]
  show "\<exists>e. e \<turnstile> tmap (ren p) (\<sigma> x (map_atyps (ren p) U)) : U"
    by (auto simp: ren_inv.map_atyps_ren_ren[OF assms(1)])
qed

end

text \<open>Fresh names for finitely many free type variables:\<close>

lemma fresh_names:
  fixes A :: "(name \<times> psort) set" and N :: "name set"
  assumes "finite A" "finite N"
  obtains c where "inj_on c A" "c ` A \<inter> N = {}"
proof -
  have "infinite (UNIV - N)" using infinite_literal assms(2) by (simp add: Diff_infinite_finite)
  then obtain f :: "nat \<Rightarrow> name" where f: "inj f" "range f \<subseteq> UNIV - N"
    using infinite_countable_subset by blast
  obtain h :: "name \<times> psort \<Rightarrow> nat" and n where h: "inj_on h A"
    using finite_imp_inj_to_nat_seg[OF assms(1)] by blast
  have "inj_on (f \<circ> h) A" using f(1) h by (simp add: comp_inj_on inj_on_subset)
  moreover have "(f \<circ> h) ` A \<inter> N = {}" using f(2) by auto
  ultimately show ?thesis by (rule that)
qed

definition swap_names :: "(name \<times> psort) set \<Rightarrow> (name \<times> psort \<Rightarrow> name) \<Rightarrow> name \<Rightarrow> psort \<Rightarrow> name" where
  "swap_names A c a S =
    (if (a, S) \<in> A then c (a, S)
     else if \<exists>b. (b, S) \<in> A \<and> c (b, S) = a then (THE b. (b, S) \<in> A \<and> c (b, S) = a)
     else a)"

lemma swap_names_inv:
  assumes "inj_on c A" "\<And>a S b. (a, S) \<in> A \<Longrightarrow> (c (a, S), b) \<notin> A"
  shows "ren_inv (swap_names A c)"
proof
  fix a S
  have u: "(THE b. (b, S) \<in> A \<and> c (b, S) = c (a, S)) = a" if "(a, S) \<in> A"
    by (rule the_equality) (use that assms(1) in \<open>auto dest: inj_onD\<close>)
  show "swap_names A c (swap_names A c a S) S = a"
  proof (cases "(a, S) \<in> A")
    case True
    then show ?thesis using assms(2)[OF True, of S] u[OF True] by (auto simp: swap_names_def)
  next
    case nA: False
    show ?thesis
    proof (cases "\<exists>b. (b, S) \<in> A \<and> c (b, S) = a")
      case True
      then obtain b where b: "(b, S) \<in> A" "c (b, S) = a" by blast
      have "(THE b'. (b', S) \<in> A \<and> c (b', S) = a) = b"
        by (rule the_equality) (use b assms(1) in \<open>auto dest: inj_onD\<close>)
      with nA b have "swap_names A c a S = b" by (auto simp: swap_names_def)
      with b show ?thesis by (simp add: swap_names_def)
    next
      case False
      with nA have e: "swap_names A c a S = a" by (auto simp: swap_names_def)
      show ?thesis by (simp add: e)
    qed
  qed
qed

subsection \<open>Generalizing free type variables preserves validity\<close>

lemma finite_typs [simp]: "finite (typs t)"
  by (induction t) auto

lemma finite_ttvars [simp]: "finite (ttvars t)"
  by (simp add: ttvars_def)

lemma has_tf_mono: "has_tf A U \<Longrightarrow> A \<subseteq> B \<Longrightarrow> has_tf B U"
  by (auto simp: has_tf_def)

lemma tf_in_mono: "tf_in A t \<Longrightarrow> A \<subseteq> B \<Longrightarrow> tf_in B t"
  by (auto simp: tf_in_def)

lemma has_tf_tsubst_mono: "has_tf A T \<Longrightarrow> has_tf A (tsubst \<rho> T)"
  unfolding has_tf_def using tfree_atyps_tsubst by fastforce

lemma map_types_id: "(\<And>U. U \<in> typs t \<Longrightarrow> f U = U) \<Longrightarrow> map_types f t = t"
  by (induction t) auto

lemma tatoms_tmap: "tatoms (tmap \<phi> t) = (\<Union>B\<in>tatoms t. set (atyps (\<phi> B)))"
  by (auto simp: tatoms_def typs_map_types atyps_map_atyps)

context pure_model
begin

theorem valid_gen_tfrees:
  assumes v: "valid Sh hs tps P" and wP: "wtp P" and wh: "\<And>h. h \<in> set hs \<Longrightarrow> wtp h"
    and nh: "\<And>h. h \<in> set hs \<Longrightarrow> \<not> tf_in A h"
    and nt: "\<And>t u. (t, u) \<in> set tps \<Longrightarrow> \<not> tf_in A t \<and> \<not> tf_in A u"
  shows "valid Sh hs tps (tmap (gen_atom A g) P)"
proof (rule validI)
  fix \<eta> \<xi> \<rho> \<sigma> assume sh: "\<And>S. S \<in> Sh \<Longrightarrow> sinh S" and g: "good \<eta> \<xi>" and \<rho>: "cinst \<rho>"
    and \<rho>i: "inh_inst \<rho>" and \<sigma>: "gsubst \<sigma>"
    and sol: "\<And>t u. (t, u) \<in> set tps \<Longrightarrow> ap \<rho> \<sigma> t \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma> u"
    and hh: "\<And>h. h \<in> set hs \<Longrightarrow> holds_at \<eta> \<xi> (ap \<rho> \<sigma> h)"
  let ?Ts = "thm_terms hs tps P"
  define A0 where "A0 = {(a, S) \<in> A. TFree a S \<in> tatoms P}"
  have fA0: "finite A0"
  proof -
    have "A0 \<subseteq> (\<lambda>(a, S). TFree a S) -` tatoms P" by (auto simp: A0_def)
    moreover have "finite ((\<lambda>(a, S). TFree a S) -` tatoms P)"
      by (rule finite_vimageI) (auto simp: inj_on_def)
    ultimately show ?thesis by (rule finite_subset)
  qed
  define NB where "NB = (\<Union>X\<in>?Ts. tatoms X \<union> (\<Union>(v, S)\<in>ttvars X. set (atyps (\<rho> v S))) \<union>
    (\<Union>(x, U)\<in>vars (inst \<rho> X). tatoms (\<sigma> x U)))"
  define N where "N = {a. \<exists>S. TFree a S \<in> NB}"
  have fNB: "finite NB" by (auto simp: NB_def)
  have fN: "finite N"
  proof -
    have "N \<subseteq> (\<lambda>B. case B of TFree a S \<Rightarrow> a | _ \<Rightarrow> undefined) ` NB" by (force simp: N_def)
    then show ?thesis by (rule finite_surj[OF fNB])
  qed
  obtain c where c: "inj_on c A0" "c ` A0 \<inter> N = {}" using fresh_names[OF fA0 fN] by blast
  have XNB: "tatoms X \<subseteq> NB" if "X \<in> ?Ts" for X using that by (auto simp: NB_def)
  have PTs: "P \<in> ?Ts" by (simp add: thm_terms_def)
  have A0N: "a \<in> N" if "(a, S) \<in> A0" for a S
    using that XNB[OF PTs] by (auto simp: A0_def N_def)
  have cA0: "(c (a, S), b) \<notin> A0" if "(a, S) \<in> A0" for a S b
    using that c(2) A0N by blast
  define p where "p = swap_names A0 c"
  have ri: "ren_inv p" unfolding p_def by (rule swap_names_inv[OF c(1) cA0])
  have pA0: "p a S = c (a, S)" if "(a, S) \<in> A0" for a S using that by (simp add: p_def swap_names_def)
  have pfix: "p a S = a" if "a \<in> N" "(a, S) \<notin> A0" for a S
    using that c(2) by (auto simp: p_def swap_names_def)
  have K: "\<not> has_tf A0 (map_atyps (ren p) U)" if U: "set (atyps U) \<subseteq> NB" for U
  proof
    assume "has_tf A0 (map_atyps (ren p) U)"
    then obtain a' S' B where a': "(a', S') \<in> A0" and B: "B \<in> set (atyps U)"
      and BB: "TFree a' S' \<in> set (atyps (ren p B))"
      by (auto simp: has_tf_def atyps_map_atyps)
    from atyps_atom[OF B] show False
    proof (elim disjE exE)
      fix a S assume BF: "B = TFree a S"
      with BB have e: "a' = p a S" "S' = S" by simp_all
      from BF B U have aN: "a \<in> N" by (auto simp: N_def)
      show False
      proof (cases "(a, S) \<in> A0")
        case True
        then have "p a S = c (a, S)" by (rule pA0)
        with e a' cA0[OF True] show False by simp
      next
        case False
        with e a' pfix[OF aN] show False by simp
      qed
    qed (use BB in simp)
  qed
  have Kt: "\<not> tf_in A0 (tmap (ren p) Y)" if "tatoms Y \<subseteq> NB" for Y
    unfolding tf_in_typs typs_map_types using K that by (fastforce simp: tatoms_def)
  have F1: "map_atyps (ren p) U = U" if F: "\<And>a S. TFree a S \<in> set (atyps U) \<Longrightarrow> a \<in> N \<and> (a, S) \<notin> A0" for U
  proof (rule map_atyps_id)
    fix B assume B: "B \<in> set (atyps U)"
    from atyps_atom[OF B] show "ren p B = B"
      by (elim disjE exE) (use B F pfix in auto)
  qed
  have F1t: "tmap (ren p) Y = Y" if F: "\<And>a S. TFree a S \<in> tatoms Y \<Longrightarrow> a \<in> N \<and> (a, S) \<notin> A0" for Y
    by (rule map_types_id, rule F1) (use F in \<open>auto simp: tatoms_def\<close>)
  have FX: "a \<in> N \<and> (a, S) \<notin> A0" if "X \<in> ?Ts" "\<not> tf_in A X" "TFree a S \<in> tatoms X" for X a S
    using that XNB[OF that(1)] by (auto simp: N_def tf_in_def A0_def)
  define \<rho>1 where "\<rho>1 v S = map_atyps (ren p) (\<rho> v S)" for v S
  define \<sigma>1 where "\<sigma>1 x U = tmap (ren p) (\<sigma> x (map_atyps (ren p) U))" for x U
  let ?\<eta>1 = "tmapv \<eta> (ren p)" and ?\<xi>1 = "vmapv (ren p) \<xi>"
  let ?P' = "tmap (gen_atom A0 g) P"
  have P'eq: "tmap (gen_atom A g) P = ?P'"
    by (rule map_types_cong, rule map_atyps_cong) (auto simp: gen_atom_def A0_def tatoms_def split: ptyp.splits)
  have wP': "wtp ?P'" by (rule wtp_tmap[OF wP tmap_ok_gen_atom])
  have tr: "holds_at \<eta> \<xi> Y \<longleftrightarrow> holds_at ?\<eta>1 ?\<xi>1 (tmap (ren p) Y)" if "e \<turnstile> Y : T" for e Y T
    using sem_tmap_ren[OF ri that] by (simp add: holds_at_def)
  have conj: "ap \<rho>1 \<sigma>1 X = tmap (ren p) (ap \<rho> \<sigma> X)" if "tmap (ren p) X = X" for X
    using tmap_ren_ap[OF ri, of \<rho> \<sigma> X] that by (simp add: \<rho>1_def[abs_def] \<sigma>1_def[abs_def])
  have hT: "h \<in> ?Ts" if "h \<in> set hs" for h using that by (simp add: thm_terms_def)
  have tT: "t \<in> ?Ts \<and> u \<in> ?Ts" if "(t, u) \<in> set tps" for t u using that by (force simp: thm_terms_def)
  have fh: "tmap (ren p) h = h" if "h \<in> set hs" for h
    by (rule F1t) (use FX[OF hT[OF that] nh[OF that]] in blast)
  have ft: "tmap (ren p) t = t \<and> tmap (ren p) u = u" if "(t, u) \<in> set tps" for t u
    using F1t FX tT[OF that] nt[OF that] by blast
  have fP': "tmap (ren p) ?P' = ?P'"
  proof (rule F1t)
    fix a S assume "TFree a S \<in> tatoms ?P'"
    then obtain B where B: "B \<in> tatoms P" "TFree a S \<in> set (atyps (gen_atom A0 g B))"
      by (auto simp: tatoms_tmap)
    from B(1) obtain U where "B \<in> set (atyps U)" by (auto simp: tatoms_def)
    from atyps_atom[OF this] B(2) have "B = TFree a S \<and> (a, S) \<notin> A0"
      by (auto simp: gen_atom_def split: if_splits)
    with B(1) XNB[OF PTs] show "a \<in> N \<and> (a, S) \<notin> A0" by (auto simp: N_def)
  qed
  have "holds_at ?\<eta>1 ?\<xi>1 (ap \<rho>1 \<sigma>1 ?P')"
  proof (rule holds_gen_inst[OF v wP wh])
    show "\<not> tf_in A0 h" if "h \<in> set hs" for h using nh[OF that] tf_in_mono by (auto simp: A0_def)
    show "\<not> tf_in A0 t \<and> \<not> tf_in A0 u" if "(t, u) \<in> set tps" for t u
      using nt[OF that] tf_in_mono by (auto simp: A0_def)
    show "good ?\<eta>1 ?\<xi>1" by (rule good_ren[OF g])
    show "cinst \<rho>1" unfolding \<rho>1_def by (rule cinst_ren[OF \<rho>])
    show "inh_inst \<rho>1" unfolding \<rho>1_def by (rule inh_inst_ren[OF \<rho>i])
    show "gsubst \<sigma>1" unfolding \<sigma>1_def by (rule gsubst_ren[OF ri \<sigma>])
    show "\<not> has_tf A0 (\<rho>1 v S)" if "X \<in> ?Ts" "(v, S) \<in> ttvars X" for X v S
      unfolding \<rho>1_def by (rule K) (use that in \<open>auto simp: NB_def\<close>)
    show "\<not> tf_in A0 (\<sigma>1 x U)" if X: "X \<in> ?Ts" and xU: "(x, U) \<in> vars (inst \<rho>1 X)"
      and nU: "\<not> has_tf A0 U" for X x U
    proof -
      from xU obtain T where xT: "(x, T) \<in> vars X" and U: "U = tsubst \<rho>1 T" by (auto simp: vars_inst)
      have "\<not> has_tf A0 T" using nU U has_tf_tsubst_mono by blast
      then have T: "map_atyps (ren p) T = T"
        by (intro F1) (use XNB[OF X] vars_typ_atoms[OF xT] in \<open>auto simp: N_def has_tf_def\<close>)
      have "map_atyps (ren p) U = tsubst \<rho> T"
        by (simp add: U map_atyps_ren_tsubst T \<rho>1_def ren_inv.map_atyps_ren_ren[OF ri])
      moreover have "(x, tsubst \<rho> T) \<in> vars (inst \<rho> X)" using xT by (auto simp: vars_inst)
      then have "tatoms (\<sigma> x (tsubst \<rho> T)) \<subseteq> NB" using X by (force simp: NB_def)
      ultimately show ?thesis unfolding \<sigma>1_def by (simp add: Kt)
    qed
    show "ap \<rho>1 \<sigma>1 t \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho>1 \<sigma>1 u" if "(t, u) \<in> set tps" for t u
      using conv_tmap[OF sol[OF that] tmap_ok_ren] conj ft[OF that] by simp
    show "holds_at ?\<eta>1 ?\<xi>1 (ap \<rho>1 \<sigma>1 h)" if h: "h \<in> set hs" for h
      using hh[OF h] tr[OF typing_ap_wtp0[OF wh[OF h] \<rho> \<sigma>]] conj[OF fh[OF h]] by simp
  qed (use sh in auto)
  then show "holds_at \<eta> \<xi> (ap \<rho> \<sigma> (tmap (gen_atom A g) P))"
    using tr[OF typing_ap_wtp0[OF wP' \<rho> \<sigma>]] conj[OF fP'] by (simp add: P'eq)
qed

end

subsection \<open>\<open>Thm.generalize\<close> with free type variables\<close>

abbreviation tf_set :: "name list \<Rightarrow> (name \<times> psort) set" where
  "tf_set tfrees \<equiv> {(a, S). a \<in> set tfrees}"

lemma generalizeT_gen_atom:
  "generalizeT tfrees i T = map_atyps (gen_atom (tf_set tfrees) (\<lambda>a S. (a, i))) T"
  by (induction tfrees i T rule: generalizeT.induct) (auto simp: gen_atom_def)

lemma generalize_term_split:
  "generalize_term tfrees frees i t =
    generalize_term [] frees i (tmap (gen_atom (tf_set tfrees) (\<lambda>a S. (a, i))) t)"
  by (induction t) (simp_all add: generalizeT_gen_atom[symmetric])

lemma has_tfree_has_tf: "has_tfree tfrees T \<longleftrightarrow> has_tf (tf_set tfrees) T"
  by (induction T) (auto simp: has_tf_def)

lemma bad_term_tf_in:
  "\<not> bad_term tfrees frees t \<Longrightarrow> \<not> tf_in (tf_set tfrees) t \<and> \<not> bad_term [] frees t"
proof (induction t)
  case (Abs a T t)
  then show ?case by (auto simp: tf_in_def has_tfree_has_tf has_tf_def)
qed (auto simp: tf_in_def has_tfree_has_tf has_tf_def)

lemma tmap_gen_atom_id: "\<not> tf_in A t \<Longrightarrow> tmap (gen_atom A g) t = t"
  by (rule map_types_id, rule map_atyps_has_tf_id) (auto simp: tf_in_typs gen_atom_def)

lemma vars_tmap_index: "(x, T) \<in> vars (tmap \<phi> t) \<Longrightarrow> \<exists>U. (x, U) \<in> vars t"
  by (auto simp: vars_map_types)

lemma ttvars_tmap_gen_atom:
  assumes "(v, S) \<in> ttvars (tmap (gen_atom A g) t)"
  shows "(v, S) \<in> ttvars t \<or> (\<exists>a. (a, S) \<in> A \<and> v = g a S)"
proof -
  from assms obtain B where B: "B \<in> tatoms t" "TVar v S \<in> set (atyps (gen_atom A g B))"
    by (auto simp: ttvars_tatoms tatoms_tmap)
  from B(1) obtain U where "B \<in> set (atyps U)" by (auto simp: tatoms_def)
  from atyps_atom[OF this] B show ?thesis by (auto simp: gen_atom_def ttvars_tatoms split: if_splits)
qed

context pure_model
begin

lemma ibelow_mono: "ibelow m t \<Longrightarrow> m \<le> m' \<Longrightarrow> ibelow m' t"
  by (auto simp: ibelow_def)

theorem generalize_tfrees_valid:
  assumes ok: "okT (generalize tfrees frees i hs th0) th"
    and v: "valid Sh hs (th_tpairs th0) (th_prop th0)"
    and wt: "wt_thm m hs (th_tpairs th0) (th_prop th0)"
    and nt: "\<And>t u b. (t, u) \<in> set (th_tpairs th0) \<Longrightarrow> b \<in> set frees \<Longrightarrow> b \<notin> fnames t \<and> b \<notin> fnames u"
    and ntf: "\<And>t u. (t, u) \<in> set (th_tpairs th0) \<Longrightarrow>
      \<not> tf_in (tf_set tfrees) t \<and> \<not> tf_in (tf_set tfrees) u"
  shows "valid Sh hs (th_tpairs th) (th_prop th)"
proof (cases "tfrees = []")
  case True
  with ok have "okT (generalize [] frees i hs th0) th" by simp
  from generalize_valid[OF this v wt nt] show ?thesis .
next
  case False
  let ?A = "tf_set tfrees" and ?g = "\<lambda>a (S :: psort). (a, i)"
  let ?tps = "th_tpairs th0" and ?P = "th_prop th0"
  let ?P1 = "tmap (gen_atom ?A ?g) ?P" and ?gen = "generalize_term tfrees frees i"
    and ?genE = "generalize_term [] frees i"
  from ok False have i: "\<not> i \<le> th_maxidx th0" and nb: "\<And>h. h \<in> set hs \<Longrightarrow> \<not> bad_term tfrees frees h"
    and th: "th_tpairs th = map (\<lambda>(t, u). (?gen t, ?gen u)) ?tps" "th_prop th = ?gen ?P"
    by (auto simp: generalize_def returnW_def raiseW_def Let_def mk_rep_def split: if_splits)
  have wP: "wtp ?P" and hw: "\<And>h. h \<in> set hs \<Longrightarrow> wtp h \<and> vars h = {} \<and> ttvars h = {}"
    using wt by (auto simp: wt_thm_def)
  have tid: "tmap (gen_atom ?A ?g) t = t \<and> tmap (gen_atom ?A ?g) u = u" if "(t, u) \<in> set ?tps" for t u
    using ntf[OF that] by (simp add: tmap_gen_atom_id)
  have v1: "valid Sh hs ?tps ?P1"
    by (rule valid_gen_tfrees[OF v wP]) (use hw nb bad_term_tf_in ntf in blast)+
  have tps: "map (\<lambda>(t, u). (?gen t, ?gen u)) ?tps = map (\<lambda>(t, u). (?genE t, ?genE u)) ?tps"
    by (rule map_cong) (auto simp: generalize_term_split[of tfrees] dest: tid)
  have P: "?gen ?P = ?genE ?P1" by (rule generalize_term_split[of tfrees frees i ?P])
  show ?thesis
  proof (cases "frees = []")
    case True
    have g0: "?genE t = t" for t using True generalize_term_id[of frees t i] by simp
    have "map (\<lambda>(t, u). (?genE t, ?genE u)) ?tps = ?tps" by (simp add: g0 case_prod_beta')
    with v1 show ?thesis by (simp add: th tps P g0)
  next
    case nf: False
    define th1 where "th1 = mk_rep (th_maxidx th0) ?tps ?P1"
    define th' where "th' = mk_rep (maxidx_tpairs (map (\<lambda>(t, u). (?genE t, ?genE u)) ?tps)
      (maxidx_of_term (?genE ?P1))) (map (\<lambda>(t, u). (?genE t, ?genE u)) ?tps) (?genE ?P1)"
    have nb0: "\<forall>h\<in>set hs. \<not> bad_term [] frees h" using nb bad_term_tf_in by blast
    have ok1: "okT (generalize [] frees i hs th1) th'"
      using nf i nb0 by (simp add: generalize_def returnW_def Let_def th1_def th'_def mk_rep_def)
    have wt1: "wt_thm (max m i) hs ?tps ?P1"
    proof -
      have ib: "ibelow m ?P" using wt by (simp add: wt_thm_def)
      have "ibelow (max m i) ?P1"
        unfolding ibelow_def
      proof (intro conjI ballI)
        fix x assume "x \<in> vars ?P1"
        then obtain U where "(fst x, U) \<in> vars ?P" using vars_tmap_index[of "fst x" "snd x"] by auto
        with ib show "snd (fst x) \<le> max m i" by (force simp: ibelow_def)
      next
        fix q assume "q \<in> ttvars ?P1"
        then have "fst q \<in> fst ` ttvars ?P \<or> snd (fst q) = i"
          using ttvars_tmap_gen_atom[of "fst q" "snd q"] by force
        with ib show "snd (fst q) \<le> max m i" by (force simp: ibelow_def)
      qed
      moreover have "\<forall>(t, u)\<in>set ?tps. closed t \<and> closed u \<and> ibelow (max m i) t \<and> ibelow (max m i) u \<and>
          (\<exists>T. \<forall>e. e \<turnstile> t : T \<and> e \<turnstile> u : T)"
        using wt by (fastforce simp: wt_thm_def intro: ibelow_mono)
      ultimately show ?thesis using wt wtp_tmap[OF wP tmap_ok_gen_atom] by (simp add: wt_thm_def)
    qed
    have "valid Sh hs (th_tpairs th1) (th_prop th1)" using v1 by (simp add: th1_def mk_rep_def)
    from generalize_valid[OF ok1 this] wt1 nt have "valid Sh hs (th_tpairs th') (th_prop th')"
      by (simp add: th1_def mk_rep_def)
    then show ?thesis by (simp add: th'_def mk_rep_def th tps P)
  qed
qed

end

subsection \<open>\<open>Thm.varifyT_global\<close>\<close>

lemma set_term_typs: "set (term_typs t) = typs t"
  by (induction t) auto

lemma set_fold_tfree_insert:
  "set (fold (\<lambda>T acc. case T of TFree a S \<Rightarrow> List.insert (a, S) acc | _ \<Rightarrow> acc) Ts xs) =
    set xs \<union> {(a, S). TFree a S \<in> set Ts}"
  by (induction Ts arbitrary: xs) (auto split: ptyp.splits)

lemma set_add_tfrees: "set (add_tfrees t xs) = set xs \<union> {(a, S). TFree a S \<in> tatoms t}"
  by (auto simp: add_tfrees_def set_fold_tfree_insert set_term_typs tatoms_def)

lemma set_fold_add_tfrees:
  "set (fold add_tfrees hs xs) = set xs \<union> {(a, S). \<exists>h\<in>set hs. TFree a S \<in> tatoms h}"
  by (induction hs arbitrary: xs) (auto simp: set_add_tfrees)

lemma set_fold_bound: "(\<And>T xs. set (F T xs) \<subseteq> set xs \<union> X) \<Longrightarrow> set (fold F Ts xs) \<subseteq> set xs \<union> X"
proof (induction Ts arbitrary: xs)
  case (Cons T Ts)
  from Cons.IH[OF Cons.prems, of "F T xs"] Cons.prems[of T xs] show ?case by auto
qed simp

lemma set_fold_tfree_fixed:
  "set (fold (\<lambda>T acc. case T of TFree a S \<Rightarrow> if (a, S) \<in> set fixed then acc else List.insert (a, S) acc
      | _ \<Rightarrow> acc) Ts xs) \<subseteq> set xs \<union> - set fixed"
  by (rule set_fold_bound) (auto split: ptyp.splits)

lemma map_of_varify_global_names:
  assumes "map_of (varify_global_names vl fixed t) (a, S) = Some (v, S')"
  shows "(a, S) \<notin> set fixed \<and> S' = S"
proof -
  from map_of_SomeD[OF assms] obtain x y where
    "((a, S), (v, S')) = (case x of (a, S) \<Rightarrow> \<lambda>b. ((a, S), ((b, 0), S))) y"
    "x \<in> set (fold (\<lambda>T acc. case T of TFree a S \<Rightarrow> if (a, S) \<in> set fixed then acc else List.insert (a, S) acc
      | _ \<Rightarrow> acc) (concat (map atyps (term_typs t))) [])"
    by (auto simp: varify_global_names_def Let_def dest!: set_zip_leftD)
  then show ?thesis
    using set_fold_tfree_fixed[of fixed "concat (map atyps (term_typs t))" "[]"] by (auto split: prod.splits)
qed

definition varA :: "((name \<times> psort) \<times> (indexname \<times> psort)) list \<Rightarrow> (name \<times> psort) set" where
  "varA names = {(a, S). map_of names (a, S) \<noteq> None}"

definition varg :: "((name \<times> psort) \<times> (indexname \<times> psort)) list \<Rightarrow> name \<Rightarrow> psort \<Rightarrow> indexname" where
  "varg names a S = fst (the (map_of names (a, S)))"

lemma varify_tfree_gen_atom:
  assumes "\<And>a S v S'. map_of names (a, S) = Some (v, S') \<Longrightarrow> S' = S"
  shows "varify_tfree names = gen_atom (varA names) (varg names)"
proof
  fix T show "varify_tfree names T = gen_atom (varA names) (varg names) T"
    using assms by (auto simp: varify_tfree_def gen_atom_def varA_def varg_def split: ptyp.splits option.splits)
qed

lemma tmap_list_implies: "tmap \<phi> (list_implies As B) = list_implies (map (tmap \<phi>) As) (tmap \<phi> B)"
  by (induction As) (simp_all add: implies_def propT_def)

lemma ok_dest_equals_map_types:
  assumes "list_all2 (\<lambda>(t, u) q. \<exists>T. q = Const STR ''Pure.eq'' (T \<rightarrow>\<^sub>T T \<rightarrow>\<^sub>T propT) $ t $ u) tps eqs"
    "ok (mapM dest_equals xs) ys" "xs = rev (map (map_types f) eqs)"
  shows "rev ys = map (\<lambda>(t, u). (map_types f t, map_types f u)) tps"
proof -
  have "list_all2 (\<lambda>q tu. ok (dest_equals q) tu) xs ys" using assms(2) by (simp add: ok_mapM)
  then have "list_all2 (\<lambda>q tu. ok (dest_equals q) tu) (map (map_types f) eqs) (rev ys)"
    using assms(3) by (simp add: list_all2_rev1)
  then have L: "list_all2 (\<lambda>q tu. ok (dest_equals (map_types f q)) tu) eqs (rev ys)" by (simp add: list_all2_map1)
  have "list_all2 (\<lambda>tu tu'. tu' = (map_types f (fst tu), map_types f (snd tu))) tps (rev ys)"
    by (rule list_all2_trans[OF _ assms(1) L]) (auto simp: dest_equals_def return_def)
  then show ?thesis by (induction rule: list_all2_induct) (auto split: prod.splits)
qed

context pure_model
begin

theorem varifyT_global_valid:
  assumes ok: "okT (varifyT_global vl fixed hs th0) (names, th)"
    and v: "valid Sh hs (th_tpairs th0) (th_prop th0)"
    and wP: "wtp (th_prop th0)" and wh: "\<And>h. h \<in> set hs \<Longrightarrow> wtp h"
    and nt: "\<And>t u a S. (t, u) \<in> set (th_tpairs th0) \<Longrightarrow> TFree a S \<in> tatoms t \<union> tatoms u \<Longrightarrow>
      (a, S) \<in> set (fold add_tfrees hs fixed)"
  shows "valid Sh hs (th_tpairs th) (th_prop th)"
proof -
  let ?tps = "th_tpairs th0" and ?P = "th_prop th0" and ?tf = "fold add_tfrees hs fixed"
  from ok obtain P1 ts P3 tps0 where f: "ok (full_prop_of ?tps ?P) P1"
    and nm: "names = varify_global_names vl ?tf P1"
    and sp: "ok (strip_prems (integer_of_nat (length ?tps)) [] (map_types (map_atyps (varify_tfree names)) P1))
      (ts, P3)"
    and d: "ok (mapM dest_equals ts) tps0"
    and th: "th_tpairs th = rev tps0" "th_prop th = P3"
    by (auto simp: varifyT_global_def Let_def mk_rep_def split: prod.splits)
  let ?A = "varA names" and ?g = "varg names"
  have vt: "varify_tfree names = gen_atom ?A ?g"
    by (rule varify_tfree_gen_atom) (use map_of_varify_global_names nm in blast)
  have A: "(a, S) \<notin> set ?tf" if "(a, S) \<in> ?A" for a S
    using that map_of_varify_global_names nm by (auto simp: varA_def)
  obtain eqs where eqs: "list_all2 (\<lambda>(t, u) q. \<exists>T. q = Const STR ''Pure.eq'' (T \<rightarrow>\<^sub>T T \<rightarrow>\<^sub>T propT) $ t $ u) ?tps eqs"
    and P1: "P1 = list_implies eqs ?P"
    by (rule ok_full_prop_of[OF f])
  have l: "integer_of_nat (length ?tps) = ilength (map (tmap (gen_atom ?A ?g)) eqs)"
    using list_all2_lengthD[OF eqs] by (simp add: ilength_eq)
  from sp[unfolded vt P1 tmap_list_implies l strip_prems_list_implies]
  have ts: "ts = rev (map (tmap (gen_atom ?A ?g)) eqs)" and P3: "P3 = tmap (gen_atom ?A ?g) ?P"
    by (simp_all add: return_def)
  have ntf: "\<not> tf_in ?A t \<and> \<not> tf_in ?A u" if "(t, u) \<in> set ?tps" for t u
    using nt[OF that] A by (fastforce simp: tf_in_def)
  have "rev tps0 = map (\<lambda>(t, u). (tmap (gen_atom ?A ?g) t, tmap (gen_atom ?A ?g) u)) ?tps"
    by (rule ok_dest_equals_map_types[OF eqs d ts])
  also have "\<dots> = ?tps" using ntf by (auto intro!: map_idI simp: tmap_gen_atom_id)
  finally have tps: "th_tpairs th = ?tps" by (simp add: th)
  have nh: "\<not> tf_in ?A h" if "h \<in> set hs" for h
    using that A by (fastforce simp: tf_in_def set_fold_add_tfrees)
  from valid_gen_tfrees[OF v wP wh nh ntf] show ?thesis by (simp add: th(2) tps P3)
qed

end

end

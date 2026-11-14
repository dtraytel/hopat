section \<open>Transfer of theorems to extensions of their signature\<close>

theory Thm_Transfer
  imports Thm_Consistency Thm_Strip_Shyps
begin

text \<open>
  Isabelle transfers theorems to extensions of their theory (\<open>Thm.transfer\<close>, \<open>Thm.join_transfer\<close>).
  An extension of a signature may add classes, subclass relations and arities to the sort
  algebra, constants, axioms and atoms of proofs; it keeps the arities of the type constructors
  (which are total in the model, so a type constructor that a theory declares later is one with
  the arity it will get), the closures and type arguments of the atoms of proofs, and it does
  not turn constants into class constants (the constant of a new class is new). The axioms of
  the signature are well-typed, as \<open>Theory.add_axiom\<close> makes them, and the propositions of the
  atoms of proofs mention only constants of the signature. Under these conditions, the theorems
  of a signature are theorems of every extension.
\<close>


subsection \<open>Extensions of the sort algebra\<close>

definition alg_le :: "algebra \<Rightarrow> algebra \<Rightarrow> bool" where
  "alg_le A A' \<longleftrightarrow> classes A \<subseteq> classes A' \<and> (\<forall>c1 c2. class_less A c1 c2 \<longrightarrow> class_less A' c1 c2) \<and>
    (\<forall>a c Ss. map_of (arities A a) c = Some Ss \<longrightarrow> map_of (arities A' a) c = Some Ss)"

lemma class_le_mono: "alg_le A A' \<Longrightarrow> class_le A c1 c2 \<Longrightarrow> class_le A' c1 c2"
  by (auto simp: alg_le_def class_le_def)

lemma sort_ok_mono: "alg_le A A' \<Longrightarrow> sort_ok A S \<Longrightarrow> sort_ok A' S"
  by (auto simp: alg_le_def sort_ok_def)

lemma has_sort_mono:
  assumes "alg_le A A'"
  shows "has_sort A T S \<Longrightarrow> has_sort A' T S"
proof (induction T arbitrary: S)
  case (Type a Ts)
  show ?case
  proof (simp only: has_sort.simps, intro ballI)
    fix c assume c: "c \<in> set S"
    with Type.prems obtain Ss where Ss: "map_of (arities A a) c = Some Ss" "length Ss = length Ts"
      and h: "\<forall>i<length Ts. has_sort A (Ts ! i) (Ss ! i)" by auto
    have "map_of (arities A' a) c = Some Ss" using Ss(1) assms by (auto simp: alg_le_def)
    moreover have "\<forall>i<length Ts. has_sort A' (Ts ! i) (Ss ! i)" using h Type.IH by (auto dest: nth_mem)
    ultimately show "\<exists>Ss. map_of (arities A' a) c = Some Ss \<and> length Ss = length Ts \<and>
        (\<forall>i<length Ts. has_sort A' (Ts ! i) (Ss ! i))" using Ss(2) by blast
  qed
qed (auto intro: class_le_mono[OF assms])

lemma sorts_ok_mono: "alg_le A A' \<Longrightarrow> sorts_ok A T \<Longrightarrow> sorts_ok A' T"
  by (induction T) (auto dest: sort_ok_mono)

lemma cert_typ_mono: "alg_le A A' \<Longrightarrow> cert_typ A ar T \<Longrightarrow> cert_typ A' ar T"
  by (auto simp: cert_typ_def dest: sorts_ok_mono)


subsection \<open>Typing and conversion\<close>

lemma typing_mono:
  assumes "signature.typing ty1 c1 e t T" "\<And>T. ty1 T \<Longrightarrow> ty2 T" "\<And>c T. c1 c T \<Longrightarrow> c2 c T"
  shows "signature.typing ty2 c2 e t T"
  using assms(1) by (induction e t T rule: signature.typing.induct[of ty1 c1, consumes 1])
    (auto intro: assms(2,3) signature.typing.intros)

lemma conv_mono:
  assumes "signature.conv ty1 c1 s t" "\<And>T. ty1 T \<Longrightarrow> ty2 T" "\<And>c T. c1 c T \<Longrightarrow> c2 c T"
  shows "signature.conv ty2 c2 s t"
proof -
  have tm: "signature.typing ty2 c2 e t T" if "signature.typing ty1 c1 e t T" for e t T
    by (rule typing_mono[OF that assms(2,3)])
  have st: "signature.conv_step ty2 c2 x y" if "signature.conv_step ty1 c1 x y" for x y
    using that tm unfolding signature.conv_step_def signature.wt_def by blast
  show ?thesis
    using assms(1) unfolding signature.conv_def
  proof (induction rule: equivclp_induct)
    case (step t u)
    then show ?case
      by (auto dest: st intro: equivclp_trans[OF _ r_into_equivclp] equivclp_trans[OF _ equivclp_sym[OF r_into_equivclp]])
  qed simp
qed

text \<open>An extension of a signature:\<close>

locale sig_ext = S: pure_sig alg ar ctab + S': pure_sig alg' ar ctab'
  for alg alg' :: algebra and ar :: "name \<Rightarrow> nat" and ctab ctab' :: "name \<Rightarrow> ptyp option" +
  assumes alg_le: "alg_le alg alg'"
    and ctab_le: "\<And>a T. ctab a = Some T \<Longrightarrow> ctab' a = Some T"
    and class_consts: "\<And>cl. cl \<in> classes alg' \<Longrightarrow> cl \<notin> classes alg \<Longrightarrow> ctab (cl + STR ''_class'') = None"
begin

lemma cert_typ_ext: "cert_typ alg ar T \<Longrightarrow> cert_typ alg' ar T"
  by (rule cert_typ_mono[OF alg_le])

lemma has_sort_ext: "has_sort alg T S \<Longrightarrow> has_sort alg' T S"
  by (rule has_sort_mono[OF alg_le])

lemma sort_ok_ext: "sort_ok alg S \<Longrightarrow> sort_ok alg' S"
  by (rule sort_ok_mono[OF alg_le])

lemma const_typ_ok_ext: "const_typ_ok ctab c T \<Longrightarrow> const_typ_ok ctab' c T"
  by (auto simp: const_typ_ok_def dest: ctab_le split: if_splits)

lemma typing_ext: "S.typing e t T \<Longrightarrow> S'.typing e t T"
  by (rule typing_mono[OF _ cert_typ_ext const_typ_ok_ext])

lemma conv_ext: "S.conv s t \<Longrightarrow> S'.conv s t"
  by (rule conv_mono[OF _ cert_typ_ext const_typ_ok_ext])

lemma wtp_ext: "S.wtp A \<Longrightarrow> S'.wtp A"
  by (simp add: S.wtp_def S'.wtp_def typing_ext)

lemma thm_wf_ext: "S.thm_wf m hs tps P \<Longrightarrow> S'.thm_wf m hs tps P"
  unfolding S.thm_wf_def S'.thm_wf_def S.wt_thm_def S'.wt_thm_def
  by (auto 0 4 intro: wtp_ext typing_ext)

lemma eqv_ext: "S.eqv E e s t \<Longrightarrow> S'.eqv E e s t"
  by (induction rule: S.eqv.induct) (auto intro: S'.eqv.intros typing_ext conv_ext cert_typ_ext)

text \<open>Constants of the signature keep their interpretation:\<close>

lemma class_const_ext:
  assumes "ctab c \<noteq> None"
  shows "S'.class_const c cl \<longleftrightarrow> S.class_const c cl"
proof
  assume cc: "S'.class_const c cl"
  have "cl \<in> classes alg"
  proof (rule ccontr)
    assume "cl \<notin> classes alg"
    with cc class_consts have "ctab (cl + STR ''_class'') = None" by (auto simp: S'.class_const_def)
    with cc assms show False by (auto simp: S'.class_const_def)
  qed
  moreover from assms obtain T0 where "ctab c = Some T0" by blast
  ultimately show "S.class_const c cl" using cc ctab_le by (auto simp: S.class_const_def S'.class_const_def)
next
  assume "S.class_const c cl"
  then show "S'.class_const c cl"
    using alg_le ctab_le by (auto simp: S.class_const_def S'.class_const_def alg_le_def)
qed

lemma eq_ok_ext: "ctab STR ''Pure.eq'' \<noteq> None \<Longrightarrow> S'.eq_ok \<longleftrightarrow> S.eq_ok"
  using ctab_le by (auto simp: S.eq_ok_def S'.eq_ok_def)

lemma const_typ_ok_declared: "const_typ_ok ctab c T \<Longrightarrow> c = STR ''Pure.imp'' \<or> c = STR ''Pure.all'' \<or> ctab c \<noteq> None"
  by (auto simp: const_typ_ok_def split: if_splits)

end


subsection \<open>Semantics\<close>

text \<open>A model of the extension is a model of the signature, with the same values of its terms:\<close>

locale sem_ext = sig_ext alg alg' ar ctab ctab' +
  M': pure_model alg' ar ctab' umem ufun uapp ulam ubool utrue ufalse tcon cls cval
  for alg alg' ar ctab ctab' and umem :: "'u \<Rightarrow> 'u \<Rightarrow> bool" (infix \<open>\<in>\<^sub>u\<close> 50)
    and ufun uapp ulam ubool utrue ufalse tcon cls cval
begin

sublocale M: pure_model alg ar ctab umem ufun uapp ulam ubool utrue ufalse tcon cls cval
proof (rule pure_model.intro)
  show "pure_sig alg ar" by (rule S.pure_sig_axioms)
  show "universe umem ufun uapp ulam ubool utrue ufalse" by (rule M'.universe_axioms)
  show "pure_model_axioms alg umem ufun ubool tcon cls cval"
  proof
    show "M'.une (tcon a As)" if "\<And>A. A \<in> set As \<Longrightarrow> M'.une A" for a As using that by (rule M'.tcon_ne)
    show "cls c2 A" if "class_le alg c1 c2" "cls c1 A" for c1 c2 A
      using that by (auto intro: M'.cls_le class_le_mono[OF alg_le])
    show "cls c (tycon ufun ubool tcon a As)"
      if "map_of (arities alg a) c = Some Ss" "length As = length Ss"
        "\<And>i c'. i < length Ss \<Longrightarrow> c' \<in> set (Ss ! i) \<Longrightarrow> cls c' (As ! i)" for a c Ss As
      using that alg_le by (auto simp: alg_le_def intro: M'.cls_arity)
    show "cval c A \<in>\<^sub>u A" if "M'.une A" for c A using that by (rule M'.cval_mem)
  qed
qed

lemma csem_ext:
  assumes "const_typ_ok ctab c T"
  shows "M.csem \<eta> c T = M'.csem \<eta> c T"
proof -
  consider "c = STR ''Pure.imp''" | "c = STR ''Pure.all''" | "ctab c \<noteq> None"
    using const_typ_ok_declared[OF assms] by blast
  then show ?thesis
  proof cases
    case 3
    have cc: "(\<exists>cl. S.class_const c cl) \<longleftrightarrow> (\<exists>cl. S'.class_const c cl)"
      and the: "(THE cl. S.class_const c cl) = (THE cl. S'.class_const c cl)"
      using class_const_ext[OF 3] by simp_all
    have "S.eq_ok \<longleftrightarrow> S'.eq_ok" if "c = STR ''Pure.eq''" using eq_ok_ext 3 that by simp
    then show ?thesis unfolding M.csem_def M'.csem_def using cc the by auto
  qed (simp_all add: M.csem_def M'.csem_def)
qed

lemma sem_ext: "S.typing e t T \<Longrightarrow> M.sem \<eta> \<xi> bv t = M'.sem \<eta> \<xi> bv t"
proof (induction t arbitrary: e T bv)
  case (Abs a U t)
  then show ?case by (auto simp: M.sem.simps M'.sem.simps)
qed (auto simp: csem_ext)

lemma good_restrict: "M'.good \<eta> \<xi> \<Longrightarrow> M.good \<eta> \<xi>"
  unfolding M.good_def M'.good_def M.good_t_def M'.good_t_def M.good_v_def M'.good_v_def
  by (auto dest: sort_ok_ext cert_typ_ext)

text \<open>A good valuation of the signature extends to a good valuation of the extension:\<close>

definition ext_eta :: "'u tval \<Rightarrow> 'u tval" where
  "ext_eta \<eta> = (\<lambda>v S. if sort_ok alg S then fst \<eta> v S else M'.pick_set S,
    \<lambda>a S. if sort_ok alg S then snd \<eta> a S else M'.pick_set S)"

definition ext_xi :: "'u tval \<Rightarrow> 'u vval \<Rightarrow> 'u vval" where
  "ext_xi \<eta> \<xi> = (\<lambda>x T. if cert_typ alg ar T then fst \<xi> x T else SOME a. a \<in>\<^sub>u M'.tsem (ext_eta \<eta>) T,
    \<lambda>x T. if cert_typ alg ar T then snd \<xi> x T else SOME a. a \<in>\<^sub>u M'.tsem (ext_eta \<eta>) T)"

lemma tsem_ext_eta: "sorts_ok alg T \<Longrightarrow> M'.tsem (ext_eta \<eta>) T = M'.tsem \<eta> T"
proof (induction T)
  case (Type a Ts)
  have "map (M'.tsem (ext_eta \<eta>)) Ts = map (M'.tsem \<eta>) Ts"
    using Type.IH Type.prems by (auto simp: map_eq_conv)
  then show ?case by (metis M'.tsem.simps(1))
qed (simp_all add: ext_eta_def)

lemma good_ext_eta:
  assumes g: "M.good \<eta> \<xi>"
  shows "M'.good (ext_eta \<eta>) (ext_xi \<eta> \<xi>)"
proof -
  have gt: "M'.good_t (ext_eta \<eta>)"
    using M.goodD(1)[OF g] M'.pick_set
    by (auto simp: M.good_t_def M'.good_t_def ext_eta_def)
  have "fst (ext_xi \<eta> \<xi>) x T \<in>\<^sub>u M'.tsem (ext_eta \<eta>) T \<and> snd (ext_xi \<eta> \<xi>) y T \<in>\<^sub>u M'.tsem (ext_eta \<eta>) T"
    if "cert_typ alg' ar T" for x y T
  proof (cases "cert_typ alg ar T")
    case True
    then have "M'.tsem (ext_eta \<eta>) T = M'.tsem \<eta> T" by (intro tsem_ext_eta) (simp add: cert_typ_def)
    with True g show ?thesis by (cases x) (simp add: ext_xi_def M.good_def M.good_v_def)
  next
    case False
    have "\<exists>a. a \<in>\<^sub>u M'.tsem (ext_eta \<eta>) T" using M'.tsem_ne[OF gt, of T] by (simp add: M'.une_def)
    with False show ?thesis by (auto simp: ext_xi_def intro: someI_ex)
  qed
  with gt show ?thesis by (simp add: M'.good_def M'.good_v_def)
qed

lemma cert_typ_args: "cert_typ alg ar (Type a Ts) \<Longrightarrow> T \<in> set Ts \<Longrightarrow> cert_typ alg ar T"
  by (auto simp: cert_typ_def)

lemma csem_ext_eta:
  assumes c: "const_typ_ok ctab c T" and t: "cert_typ alg ar T"
  shows "M'.csem (ext_eta \<eta>) c T = M'.csem \<eta> c T"
proof -
  have ts: "M'.tsem (ext_eta \<eta>) U = M'.tsem \<eta> U" if "cert_typ alg ar U" for U
    using that by (intro tsem_ext_eta) (simp add: cert_typ_def)
  have ct': "const_typ_ok ctab' c T" by (rule const_typ_ok_ext[OF c])
  consider "c = STR ''Pure.imp''" | "c = STR ''Pure.all''" | "c \<noteq> STR ''Pure.imp''" "c \<noteq> STR ''Pure.all''"
    by blast
  then show ?thesis
  proof cases
    case 2
    from c 2 obtain U where "T = (U \<rightarrow>\<^sub>T propT) \<rightarrow>\<^sub>T propT" by (auto simp: const_typ_ok_def propT_def)
    with t have "cert_typ alg ar U" "all_dom T = U" by (auto simp: cert_typ_def)
    with 2 show ?thesis by (simp add: M'.csem_def ts)
  next
    case 3
    show ?thesis
    proof (cases "\<exists>cl. S'.class_const c cl")
      case True
      then obtain cl where cl: "S'.class_const c cl" by blast
      obtain A where "T = Type STR ''itself'' [A] \<rightarrow>\<^sub>T propT" by (rule M'.class_const_typ[OF cl ct'])
      with t have "cert_typ alg ar (fun_dom T)" "cert_typ alg ar (itself_arg T)"
        by (auto simp: cert_typ_def)
      then show ?thesis by (simp add: M'.csem_class[OF cl] ts)
    next
      case nc: False
      show ?thesis
      proof (cases "c = STR ''Pure.eq'' \<and> S'.eq_ok")
        case True
        then obtain A where "T = A \<rightarrow>\<^sub>T A \<rightarrow>\<^sub>T propT" using S'.eq_ok_typ ct' by metis
        with t have "cert_typ alg ar (fun_dom T)" by (auto simp: cert_typ_def)
        with True show ?thesis by (simp add: M'.csem_eq ts)
      next
        case False
        have "M'.csem \<eta>' c T = cval c (M'.tsem \<eta>' T)" for \<eta>'
          by (rule M'.csem_other) (use 3 nc False in auto)
        with t show ?thesis by (simp add: ts)
      qed
    qed
  qed (simp add: M'.csem_def)
qed

lemma sem_ext_eta: "S.typing e t T \<Longrightarrow> M'.sem (ext_eta \<eta>) (ext_xi \<eta> \<xi>) bv t = M'.sem \<eta> \<xi> bv t"
proof (induction t arbitrary: e T bv)
  case (Const c U)
  then show ?case by (auto simp: csem_ext_eta)
next
  case (Free x U)
  then show ?case by (auto simp: ext_xi_def)
next
  case (Var x U)
  then show ?case by (auto simp: ext_xi_def)
next
  case (Abs a U t)
  from Abs.prems obtain V where "cert_typ alg ar U" "S.typing (e\<langle>0:U\<rangle>) t V" by auto
  moreover then have "M'.tsem (ext_eta \<eta>) U = M'.tsem \<eta> U" by (intro tsem_ext_eta) (simp add: cert_typ_def)
  ultimately show ?case using Abs.IH by simp
next
  case (App t u)
  then show ?case by fastforce
qed simp

text \<open>Validity of the terms of the signature is the same in both signatures:\<close>

lemma gterm_typing: "S.gterm t T \<Longrightarrow> S.typing (\<lambda>_. propT) t T"
  by (simp add: S.gterm_def)

lemma holds_ext: "S.gterm A propT \<Longrightarrow> M.holds_at \<eta> \<xi> A \<longleftrightarrow> M'.holds_at \<eta> \<xi> A"
  by (drule gterm_typing) (simp add: M.holds_at_def M'.holds_at_def sem_ext)

lemma eq_at_ext: "S.gterm t T \<Longrightarrow> S.gterm u T \<Longrightarrow> M.eq_at \<eta> \<xi> t u \<longleftrightarrow> M'.eq_at \<eta> \<xi> t u"
  by (drule gterm_typing)+ (simp add: M.eq_at_def M'.eq_at_def sem_ext)

lemma holds_ext_eta: "S.gterm A propT \<Longrightarrow> M'.holds_at (ext_eta \<eta>) (ext_xi \<eta> \<xi>) A \<longleftrightarrow> M'.holds_at \<eta> \<xi> A"
  by (drule gterm_typing) (simp add: M'.holds_at_def sem_ext_eta)

lemma eq_at_ext_eta:
  "S.gterm t T \<Longrightarrow> S.gterm u T \<Longrightarrow> M'.eq_at (ext_eta \<eta>) (ext_xi \<eta> \<xi>) t u \<longleftrightarrow> M'.eq_at \<eta> \<xi> t u"
  by (drule gterm_typing)+ (simp add: M'.eq_at_def sem_ext_eta)

lemma gterm_ext: "S.gterm t T \<Longrightarrow> S'.gterm t T"
  by (simp add: S.gterm_def S'.gterm_def typing_ext)

lemma wf_terms_ext: "M.wf_terms hs tps P \<Longrightarrow> M'.wf_terms hs tps P"
  unfolding M.wf_terms_def M'.wf_terms_def by (auto 0 3 intro: gterm_ext)

theorem svalid_ext:
  assumes wf: "M.wf_terms hs tps P"
  shows "M'.svalid Sh hs tps P \<longleftrightarrow> M.svalid Sh hs tps P"
proof
  assume v: "M'.svalid Sh hs tps P"
  show "M.svalid Sh hs tps P"
  proof (rule M.svalidI)
    fix \<eta> \<xi> assume sh: "\<And>S. S \<in> Sh \<Longrightarrow> M.sinh S" and g: "M.good \<eta> \<xi>"
      and tp: "\<And>t u. (t, u) \<in> set tps \<Longrightarrow> M.eq_at \<eta> \<xi> t u" and hh: "\<And>h. h \<in> set hs \<Longrightarrow> M.holds_at \<eta> \<xi> h"
    have "M'.holds_at (ext_eta \<eta>) (ext_xi \<eta> \<xi>) P"
    proof (rule M'.svalidD[OF v _ good_ext_eta[OF g]])
      show "M'.sinh S" if "S \<in> Sh" for S using sh[OF that] by (simp add: M.sinh_def M'.sinh_def)
      fix t u assume tu: "(t, u) \<in> set tps"
      then obtain T where "S.gterm t T" "S.gterm u T" using wf by (auto simp: M.wf_terms_def)
      then show "M'.eq_at (ext_eta \<eta>) (ext_xi \<eta> \<xi>) t u" using tp[OF tu] by (simp add: eq_at_ext_eta eq_at_ext)
    next
      fix h assume h: "h \<in> set hs"
      then have "S.gterm h propT" using wf by (auto simp: M.wf_terms_def)
      then show "M'.holds_at (ext_eta \<eta>) (ext_xi \<eta> \<xi>) h" using hh[OF h] by (simp add: holds_ext_eta holds_ext)
    qed
    moreover have "S.gterm P propT" using wf by (simp add: M.wf_terms_def)
    ultimately show "M.holds_at \<eta> \<xi> P" by (simp add: holds_ext_eta holds_ext)
  qed
next
  assume v: "M.svalid Sh hs tps P"
  show "M'.svalid Sh hs tps P"
  proof (rule M'.svalidI)
    fix \<eta> \<xi> assume sh: "\<And>S. S \<in> Sh \<Longrightarrow> M'.sinh S" and g: "M'.good \<eta> \<xi>"
      and tp: "\<And>t u. (t, u) \<in> set tps \<Longrightarrow> M'.eq_at \<eta> \<xi> t u" and hh: "\<And>h. h \<in> set hs \<Longrightarrow> M'.holds_at \<eta> \<xi> h"
    have "M.holds_at \<eta> \<xi> P"
    proof (rule M.svalidD[OF v _ good_restrict[OF g]])
      show "M.sinh S" if "S \<in> Sh" for S using sh[OF that] by (simp add: M.sinh_def M'.sinh_def)
      fix t u assume tu: "(t, u) \<in> set tps"
      then obtain T where "S.gterm t T" "S.gterm u T" using wf by (auto simp: M.wf_terms_def)
      then show "M.eq_at \<eta> \<xi> t u" using tp[OF tu] by (simp add: eq_at_ext)
    next
      fix h assume h: "h \<in> set hs"
      then have "S.gterm h propT" using wf by (auto simp: M.wf_terms_def)
      then show "M.holds_at \<eta> \<xi> h" using hh[OF h] by (simp add: holds_ext)
    qed
    moreover have "S.gterm P propT" using wf by (simp add: M.wf_terms_def)
    ultimately show "M'.holds_at \<eta> \<xi> P" by (simp add: holds_ext)
  qed
qed

theorem valid_ext:
  assumes wf: "M.wf_terms hs tps P"
  shows "M'.valid Sh hs tps P \<longleftrightarrow> M.valid Sh hs tps P"
  using svalid_ext[OF wf] M.valid_svalid[OF wf] M'.valid_svalid[OF wf_terms_ext[OF wf]] by simp

end


subsection \<open>Proofs\<close>

text \<open>
  A tight proof records the constants of its terms by name; it is decoded with the types that the
  signature declares (\<^const>\<open>pure_sig.zdec\<close>), and a constant that only the extension declares is
  decoded differently in the extension. This does not affect the validity of the proof: the
  hypotheses of a valid proof are hypotheses of the theorem and the propositions of its proof
  constants are atoms of proofs, so both mention only constants of the signature; all other
  terms of the proof are annotations, of which the proof judgment erases the types of constants.
\<close>

fun zterm_consts :: "zterm \<Rightarrow> name set" where
  "zterm_consts (ZConst0 c) = {c}"
| "zterm_consts (ZConst1 c T) = {c}"
| "zterm_consts (ZConst c Ts) = {c}"
| "zterm_consts (ZAbs a T t) = zterm_consts t"
| "zterm_consts (ZApp t u) = zterm_consts t \<union> zterm_consts u"
| "zterm_consts _ = {}"

definition zt_decl :: "(name \<Rightarrow> ptyp option) \<Rightarrow> zterm \<Rightarrow> bool" where
  "zt_decl ct t \<longleftrightarrow> (\<forall>n\<in>zterm_consts t. n = STR ''Pure.imp'' \<or> n = STR ''Pure.all'' \<or> ct n \<noteq> None)"

fun term_consts :: "pterm \<Rightarrow> name set" where
  "term_consts (Const c T) = {c}"
| "term_consts (s $ t) = term_consts s \<union> term_consts t"
| "term_consts (Abs a T t) = term_consts t"
| "term_consts _ = {}"

definition const_decl :: "(name \<Rightarrow> ptyp option) \<Rightarrow> name \<Rightarrow> bool" where
  "const_decl ct n \<longleftrightarrow> n = STR ''Pure.imp'' \<or> n = STR ''Pure.all'' \<or> ct n \<noteq> None"

lemma zt_decl_const_decl: "zt_decl ct t \<longleftrightarrow> (\<forall>n\<in>zterm_consts t. const_decl ct n)"
  by (simp add: zt_decl_def const_decl_def)

context pure_sig
begin

lemma typing_consts_decl: "e \<turnstile> t : T \<Longrightarrow> n \<in> term_consts t \<Longrightarrow> const_decl ctab n"
  by (induction rule: typing.induct) (auto simp: const_decl_def const_typ_ok_def split: if_splits)

lemma zterm_consts_zdec: "zterm_consts t \<subseteq> term_consts (zdec t)"
  by (induction t) auto

lemma zt_decl_zdec: "\<forall>n\<in>term_consts (zdec t). const_decl ctab n \<Longrightarrow> zt_decl ctab t"
  using zterm_consts_zdec by (auto simp: zt_decl_const_decl)

end

text \<open>Proofs that differ in the types of the constants and abstractions of their annotations:\<close>

inductive prf_teq :: "prf \<Rightarrow> prf \<Rightarrow> bool" where
  refl: "prf_teq p p"
| Abst: "prf_teq p q \<Longrightarrow> prf_teq (Abst a T p) (Abst a T q)"
| AbsP: "rel_option (\<lambda>t t'. erase t = erase t') t t' \<Longrightarrow> prf_teq p q \<Longrightarrow> prf_teq (AbsP a t p) (AbsP a t' q)"
| PAppt: "prf_teq p q \<Longrightarrow> rel_option (\<lambda>t t'. erase t = erase t') t t' \<Longrightarrow> prf_teq (PAppt p t) (PAppt q t')"
| PAppp: "prf_teq p p' \<Longrightarrow> prf_teq q q' \<Longrightarrow> prf_teq (PAppp p q) (PAppp p' q')"

lemma prf_teq_foldl_PAppt:
  "list_all2 (rel_option (\<lambda>t t'. erase t = erase t')) ts ts' \<Longrightarrow> prf_teq p q \<Longrightarrow>
    prf_teq (foldl PAppt p ts) (foldl PAppt q ts')"
  by (induction arbitrary: p q rule: list_all2_induct) (auto intro: prf_teq.PAppt)

lemma prf_teq_foldl_PAppt_Some:
  "list_all2 (\<lambda>t t'. erase t = erase t') ts ts' \<Longrightarrow> prf_teq p q \<Longrightarrow>
    prf_teq (foldl (\<lambda>p t. PAppt p (Some t)) p ts) (foldl (\<lambda>p t. PAppt p (Some t)) q ts')"
  by (induction arbitrary: p q rule: list_all2_induct) (auto simp: prf_teq.PAppt)

lemma prf_atoms_foldl_PAppt [simp]: "prf_atoms (foldl PAppt p ts) = prf_atoms p"
  by (induction ts arbitrary: p) auto

lemma prf_atoms_foldl_PAppt_Some [simp]: "prf_atoms (foldl (\<lambda>p t. PAppt p (Some t)) p ts) = prf_atoms p"
  by (induction ts arbitrary: p) auto

text \<open>The class proofs of another proof of the same shape:\<close>

lemma prf_reclass_self: "pcerase w = pcerase a \<Longrightarrow> prf_reclass a w = w"
  by (induction a arbitrary: w; case_tac w; auto)

lemma prf_teq_reclass:
  "prf_teq a b \<Longrightarrow> pcerase w = pcerase a \<Longrightarrow> prf_teq w (prf_reclass b w)"
proof (induction arbitrary: w rule: prf_teq.induct)
  case (refl p)
  then show ?case by (simp add: prf_reclass_self prf_teq.refl)
next
  case (Abst p q a T)
  from Abst.prems obtain w1 where w: "w = Abst a T w1" "pcerase w1 = pcerase p" by (cases w) auto
  with Abst.IH[of w1] show ?case by (simp add: prf_teq.Abst)
next
  case (AbsP t t' p q a)
  from AbsP.prems obtain w1 where w: "w = AbsP a t w1" "pcerase w1 = pcerase p" by (cases w) auto
  with AbsP.IH[of w1] AbsP.hyps(1) show ?case by (simp add: prf_teq.AbsP)
next
  case (PAppt p q t t')
  from PAppt.prems obtain w1 where w: "w = PAppt w1 t" "pcerase w1 = pcerase p" by (cases w) auto
  with PAppt.IH[of w1] PAppt.hyps(2) show ?case by (simp add: prf_teq.PAppt)
next
  case (PAppp p p' q q')
  from PAppp.prems obtain w1 w2 where w: "w = PAppp w1 w2" "pcerase w1 = pcerase p" "pcerase w2 = pcerase q"
    by (cases w) auto
  with PAppp.IH(1)[of w1] PAppp.IH(2)[of w2] show ?case by (simp add: prf_teq.PAppp)
qed

context prf_sig
begin

lemma prf_teq_aeq: "prf_teq p q \<Longrightarrow> prf_aeq (prf_ap \<rho> \<sigma> p) (prf_ap \<rho> \<sigma> q)"
proof (induction rule: prf_teq.induct)
  case (AbsP t t' p q a)
  have "ann_eq (map_option (ap \<rho> \<sigma>) t) (map_option (ap \<rho> \<sigma>) t')"
    using AbsP.hyps(1) by (cases t; cases t') (auto simp: ann_eq_def dest: erase_ap_cong[of _ _ \<rho> \<sigma>])
  with AbsP.IH show ?case by (simp add: prf_ap_def prf_aeq.AbsP)
next
  case (PAppt p q t t')
  have "ann_eq (map_option (ap \<rho> \<sigma>) t) (map_option (ap \<rho> \<sigma>) t')"
    using PAppt.hyps(2) by (cases t; cases t') (auto simp: ann_eq_def dest: erase_ap_cong[of _ _ \<rho> \<sigma>])
  with PAppt.IH show ?case by (simp add: prf_ap_def prf_aeq.PAppt)
qed (auto simp: prf_ap_def intro: prf_aeq.intros)

lemma prf_ok_atoms: "prf_ok ax H E e Hs p \<phi> \<Longrightarrow> A \<in> prf_atoms p \<Longrightarrow> ax A"
  by (induction rule: prf_ok.induct) auto

lemma prf_valid_atoms:
  assumes "prf_valid ax H tps w \<phi>" "A \<in> prf_atoms w"
  shows "ax A"
proof -
  have "prf_ok ax H (pmap (ap (\<lambda>v S. TVar v S) (\<lambda>x T. Var x T)) (set tps)) (\<lambda>_. propT) []
      (prf_ap (\<lambda>v S. TVar v S) (\<lambda>x T. Var x T) w) (ap (\<lambda>v S. TVar v S) (\<lambda>x T. Var x T) \<phi>)"
    by (rule prf_validD[OF assms(1) cinst_TVar gsubst_Var])
  from prf_ok_atoms[OF this] assms(2) show ?thesis by (simp add: prf_ap_def)
qed

end

context sig_ext
begin

lemma zconst_typ_ext:
  "c = STR ''Pure.imp'' \<or> c = STR ''Pure.all'' \<or> ctab c \<noteq> None \<Longrightarrow> S'.zconst_typ c Us = S.zconst_typ c Us"
  using ctab_le by (auto simp: S.zconst_typ_def S'.zconst_typ_def)

lemma zdec_ext: "zt_decl ctab t \<Longrightarrow> S'.zdec t = S.zdec t"
  by (induction t) (auto simp: zt_decl_def zconst_typ_ext)

lemma erase_zdec_ext: "erase (S'.zdec t) = erase (S.zdec t)"
  by (induction t) auto

text \<open>The two translations of a tight proof whose hypotheses and proof constants have
  propositions over the constants of the smaller signature:\<close>

lemma zprf_tr_teq:
  assumes "\<And>t n. t \<in> prf_hyps (S.zprf_tr z) \<Longrightarrow> n \<in> term_consts t \<Longrightarrow> const_decl ctab n"
    and "\<And>A n. A \<in> prf_atoms (S.zprf_tr z) \<Longrightarrow> n \<in> term_consts A \<Longrightarrow> const_decl ctab n"
  shows "prf_teq (S.zprf_tr z) (S'.zprf_tr z)"
  using assms
proof (induction z)
  case (ZConstp c)
  obtain nm A instT tab where c: "c = ((nm, A), (instT, tab))" by (metis prod.collapse)
  have look: "rel_option (\<lambda>t t'. erase t = erase t')
      (map_option S.zdec (zv_lookup_name tab xi)) (map_option S'.zdec (zv_lookup_name tab xi))" for xi
    by (cases "zv_lookup_name tab xi") (simp_all add: erase_zdec_ext)
  show ?case
  proof (cases nm)
    case (ZAxiom n)
    show ?thesis
    proof (cases "zeq_const n A")
      case True
      have "prf_teq (zeq_tr n (\<lambda>x. map_option S.zdec (zv_lookup_name tab (x, -1))))
          (zeq_tr n (\<lambda>x. map_option S'.zdec (zv_lookup_name tab (x, -1))))"
      proof (cases "find (\<lambda>(a, xs). n = STR ''Pure.'' + a) zeq_vars")
        case None
        then show ?thesis by (simp add: zeq_tr_def prf_teq.refl)
      next
        case (Some axs)
        obtain a xs where axs: "axs = (a, xs)" by (cases axs)
        have "rel_option (list_all2 (\<lambda>t t'. erase t = erase t'))
            (those (map (\<lambda>x. map_option S.zdec (zv_lookup_name tab (x, -1))) xs))
            (those (map (\<lambda>x. map_option S'.zdec (zv_lookup_name tab (x, -1))) xs))"
        proof (induction xs)
          case (Cons x xs)
          then show ?case
            by (cases "zv_lookup_name tab (x, -1)") (auto simp: erase_zdec_ext split: option.splits elim: option.rel_cases)
        qed simp
        then show ?thesis
          unfolding zeq_tr_def Some axs
          by (auto elim!: option.rel_cases intro: prf_teq_foldl_PAppt_Some[OF _ prf_teq.refl] prf_teq.refl)
      qed
      with True ZAxiom show ?thesis by (simp add: c S.zconst_tr_def S'.zconst_tr_def)
    next
      case False
      have "S.zdec A \<in> prf_atoms (S.zprf_tr (ZConstp c))"
        using False ZAxiom by (simp add: c S.zconst_tr_def zax_tr_def)
      then have "zt_decl ctab A" using ZConstp.prems(2) by (intro S.zt_decl_zdec) blast
      then have A: "S'.zdec A = S.zdec A" by (rule zdec_ext)
      have "prf_teq (zax_tr n (S.zdec A) (\<lambda>xi. map_option S.zdec (zv_lookup_name tab xi)))
          (zax_tr n (S.zdec A) (\<lambda>xi. map_option S'.zdec (zv_lookup_name tab xi)))"
        unfolding zax_tr_def
        by (rule prf_teq_foldl_PAppt[OF _ prf_teq.refl])
          (auto simp: list_all2_map1 list_all2_map2 intro!: list_all2_refl look split: pterm.splits)
      with False ZAxiom A show ?thesis by (simp add: c S.zconst_tr_def S'.zconst_tr_def)
    qed
  next
    case (ZThm x)
    have "S.zdec A \<in> prf_atoms (S.zprf_tr (ZConstp c))"
      using ZThm by (simp add: c S.zconst_tr_def zthm_tr_def zthm_head_def)
    then have "zt_decl ctab A" using ZConstp.prems(2) by (intro S.zt_decl_zdec) blast
    then have A: "S'.zdec A = S.zdec A" by (rule zdec_ext)
    have "prf_teq (zthm_tr (S.zdec A) (\<lambda>xi. map_option S.zdec (zv_lookup_name tab xi)))
        (zthm_tr (S.zdec A) (\<lambda>xi. map_option S'.zdec (zv_lookup_name tab xi)))"
      unfolding zthm_tr_def
      by (rule prf_teq_foldl_PAppt[OF _ prf_teq.refl])
        (auto simp: list_all2_map1 list_all2_map2 intro!: list_all2_refl look split: pterm.splits)
    with ZThm A show ?thesis by (simp add: c S.zconst_tr_def S'.zconst_tr_def)
  qed (simp_all add: c S.zconst_tr_def S'.zconst_tr_def prf_teq.refl)
next
  case (ZHyp t)
  then have "zt_decl ctab t" by (intro S.zt_decl_zdec) simp
  then show ?case by (simp add: zdec_ext prf_teq.refl)
qed (auto intro: prf_teq.intros simp: erase_zdec_ext)

lemma bindM_Ok: "bindM m f = Some (Ok y) \<longleftrightarrow> (\<exists>x. m = Some (Ok x) \<and> f x = Some (Ok y))"
  by (auto simp: bindM_def split: option.splits xres.splits)

lemma liftMZ_Ok: "liftMZ m = Some (Ok y) \<longleftrightarrow> m = Some (Ok y)"
  by (auto simp: liftMZ_def split: option.splits xres.splits)

lemma ztargs_ext: "S.ztargs c T = Some (Ok Us) \<Longrightarrow> S'.ztargs c T = Some (Ok Us)"
  using ctab_le by (auto simp: S.ztargs_def S'.ztargs_def raise_def return_def split: if_splits option.splits)

lemma zterm_of_ext: "zterm_of S.ztargs t = Some (Ok z) \<Longrightarrow> zterm_of S'.ztargs t = Some (Ok z)"
proof (induction t arbitrary: z)
  case (Const c T)
  then show ?case by (auto simp: bindM_Ok liftMZ_Ok dest: ztargs_ext)
next
  case (App t u)
  show ?case
  proof (cases "match_of_class (t $ u)")
    case None
    with App show ?thesis by (auto simp: bindM_Ok)
  next
    case (Some Tc)
    have e: "zterm_of ta (t $ u) = (if t $ u = mk_of_class (fst Tc) (snd Tc)
        then return (ZOfclass (ztyp_of (fst Tc)) (snd Tc))
        else bindM (zterm_of ta t) (\<lambda>t'. bindM (zterm_of ta u) (\<lambda>u'. return (ZApp t' u'))))" for ta
      by (simp only: zterm_of.simps Some option.case)
    show ?thesis using App unfolding e by (auto simp: bindM_Ok split: if_splits)
  qed
next
  case (Abs a T t)
  then show ?case by (auto simp: bindM_Ok return_def)
qed (simp_all add: return_def)

lemma zhyps_ok_ext: "\<forall>h\<in>zhyps z. zt_decl ctab h \<Longrightarrow> S.zhyps_ok z \<Longrightarrow> S'.zhyps_ok z"
  unfolding S.zhyps_ok_def S'.zhyps_ok_def return_def
  using zdec_ext zterm_of_ext by metis

end

locale prf_ext = sig_ext alg alg' ar ctab ctab' +
  P: prf_sig alg ar ctab close tyargs + P': prf_sig alg' ar ctab' close tyargs
  for alg alg' ar ctab ctab' close tyargs
begin

lemma atom_ok_ext: "P.atom_ok A Us' Us \<Longrightarrow> P'.atom_ok A Us' Us"
  unfolding P.atom_ok_def P'.atom_ok_def by (auto elim!: list_all2_mono intro: has_sort_ext cert_typ_ext)

lemma prf_ok_ext:
  assumes ax: "\<And>A. ax A \<Longrightarrow> ax' A"
  shows "P.prf_ok ax H E e Hs p \<phi> \<Longrightarrow> P'.prf_ok ax' H E e Hs p \<phi>"
  by (induction rule: P.prf_ok.induct)
    (auto intro: P'.prf_ok.intros typing_ext conv_ext eqv_ext cert_typ_ext has_sort_ext atom_ok_ext ax)

lemma prf_valid_ext:
  assumes H: "\<And>h. h \<in> H \<Longrightarrow> vars h = {} \<and> ttvars h = {}" and ax: "\<And>A. ax A \<Longrightarrow> ax' A"
    and v: "P.prf_valid ax H tps p \<phi>"
  shows "P'.prf_valid ax' H tps p \<phi>"
proof -
  have "P.prf_ok ax H ((\<lambda>(l, r). (S.ap TVar Var l, S.ap TVar Var r)) ` set tps) e []
      (P.prf_ap TVar Var p) (S.ap TVar Var \<phi>)" for e
    using v P.cinst_TVar' P.gsubst_Var unfolding P.prf_valid_def by blast
  moreover have "S.ap TVar Var = (\<lambda>t. t)" using S.ap_Var_fun[of TVar] by (simp add: fun_eq_iff)
  ultimately have b: "P.prf_ok ax H (set tps) e [] p \<phi>" for e by (simp add: case_prod_Pair)
  have g: "P'.prf_ok ax' H (set tps) e [] p \<phi>" for e
    using prf_ok_ext[of ax ax' H "set tps" e "[]" p \<phi>] ax b by blast
  show ?thesis by (rule P'.prf_validI) (rule P'.prf_ok_ap_any[OF H g])
qed

text \<open>
  A valid tight proof stays valid in the extension: its hypotheses are hypotheses of the theorem
  and the propositions of its proof constants are axioms, so both mention only constants of the
  smaller signature; elsewhere the two translations differ in the types of constants in
  annotations, which the proof judgment erases.
\<close>

lemma zvalid_ext:
  assumes H: "\<And>h. h \<in> H \<Longrightarrow> vars h = {} \<and> ttvars h = {}" and ax: "\<And>A. ax A \<Longrightarrow> ax' A"
    and Hd: "\<And>h n. h \<in> H \<Longrightarrow> n \<in> term_consts h \<Longrightarrow> const_decl ctab n"
    and axd: "\<And>A n. ax A \<Longrightarrow> n \<in> term_consts A \<Longrightarrow> const_decl ctab n"
    and v: "P.zvalid ax H tps z \<phi>"
  shows "P'.zvalid ax' H tps z \<phi>" and "\<forall>h\<in>zhyps z. zt_decl ctab h"
proof -
  obtain w where w: "pcerase w = pcerase (S.zprf_tr z)" "P.prf_valid ax H tps w \<phi>" using v by (rule P.zvalidE)
  have hy: "prf_hyps (S.zprf_tr z) = prf_hyps w" using arg_cong[OF w(1), of prf_hyps] by simp
  have at: "prf_atoms (S.zprf_tr z) = prf_atoms w" using arg_cong[OF w(1), of prf_atoms] by simp
  have hd: "const_decl ctab n" if "t \<in> prf_hyps (S.zprf_tr z)" "n \<in> term_consts t" for t n
    using that P.prf_valid_hyps[OF w(2)] Hd unfolding hy by blast
  have ad: "const_decl ctab n" if "A \<in> prf_atoms (S.zprf_tr z)" "n \<in> term_consts A" for A n
    using that P.prf_valid_atoms[OF w(2)] axd unfolding at by blast
  show "\<forall>h\<in>zhyps z. zt_decl ctab h"
  proof
    fix h assume "h \<in> zhyps z"
    then have "S.zdec h \<in> prf_hyps (S.zprf_tr z)" using P.zhyps_prf_hyps[of z] by blast
    then show "zt_decl ctab h" using hd by (intro S.zt_decl_zdec) blast
  qed
  let ?w' = "prf_reclass (S'.zprf_tr z) w"
  have teq: "prf_teq w ?w'" by (rule prf_teq_reclass[OF zprf_tr_teq[OF hd ad] w(1)])
  have "P'.prf_valid ax' H tps w \<phi>" by (rule prf_valid_ext[OF H ax w(2)])
  then have "P'.prf_valid ax' H tps ?w' \<phi>" by (rule P'.prf_valid_aeq) (rule P'.prf_teq_aeq[OF teq])
  then show "P'.zvalid ax' H tps z \<phi>" by (rule P'.zvalidI[rotated]) simp
qed

end


subsection \<open>Transfer of theorems\<close>

definition sign_le :: "sign \<Rightarrow> sign \<Rightarrow> bool" where
  "sign_le c c' \<longleftrightarrow> pure_sig (sg_alg c) (sg_ar c) \<and> alg_le (sg_alg c) (sg_alg c') \<and> sg_ar c' = sg_ar c \<and>
    (\<forall>a T. sg_consts c a = Some T \<longrightarrow> sg_consts c' a = Some T) \<and>
    (\<forall>cl. cl \<in> classes (sg_alg c') \<longrightarrow> cl \<notin> classes (sg_alg c) \<longrightarrow> sg_consts c (cl + STR ''_class'') = None) \<and>
    (\<forall>a A. sg_axioms c a = Some A \<longrightarrow>
      sg_axioms c' a = Some A \<and> pure_sig.wtp (sg_alg c) (sg_ar c) (sg_consts c) A) \<and>
    (\<forall>A. sg_ax c A \<longrightarrow> sg_ax c' A) \<and> sg_close c' = sg_close c \<and> sg_tyargs c' = sg_tyargs c \<and>
    (\<forall>A n. sg_ax c A \<longrightarrow> n \<in> term_consts A \<longrightarrow> const_decl (sg_consts c) n)"

lemma sig_ext_sign_le:
  assumes "sign_le c c'" "pure_sig (sg_alg c') (sg_ar c')"
  shows "sig_ext (sg_alg c) (sg_alg c') (sg_ar c) (sg_consts c) (sg_consts c')"
  using assms by (auto simp: sign_le_def sig_ext_def sig_ext_axioms_def)

text \<open>A theorem of a signature is a theorem of its extensions:\<close>

theorem thm_ok_transfer:
  assumes ok: "thm_ok TYPE('u) th" and sl: "sign_le (th_sign th) c'"
  shows "thm_ok TYPE('u) (th\<lparr>th_sign := c'\<rparr>)"
proof -
  let ?c = "th_sign th"
  have ps: "pure_sig (sg_alg ?c) (sg_ar ?c)" and ar: "sg_ar c' = sg_ar ?c"
    and ax: "\<And>A. sg_ax ?c A \<Longrightarrow> sg_ax c' A" and cl: "sg_close c' = sg_close ?c" and ty: "sg_tyargs c' = sg_tyargs ?c"
    and axs: "\<And>a A. sg_axioms ?c a = Some A \<Longrightarrow> sg_axioms c' a = Some A \<and> pure_sig.wtp (sg_alg ?c) (sg_ar ?c) (sg_consts ?c) A"
    using sl by (auto simp: sign_le_def)
  have axd: "\<And>A n. sg_ax ?c A \<Longrightarrow> n \<in> term_consts A \<Longrightarrow> const_decl (sg_consts ?c) n"
    using sl by (auto simp: sign_le_def)
  from ok ps have wf: "pure_sig.thm_wf (sg_alg ?c) (sg_ar ?c) (sg_consts ?c) (th_maxidx th) (th_hyps th) (th_tpairs th) (th_prop th)"
    and val: "\<And>M :: 'u model. is_model ?c M \<Longrightarrow> valid_in ?c M (th_shyps th) (th_hyps th) (th_tpairs th) (th_prop th)"
    and prfs: "is_prf_sig ?c \<Longrightarrow> proofs_ok th"
    by (auto simp: thm_ok_def)
  show ?thesis
    unfolding thm_ok_def
  proof (intro conjI impI)
    assume ps': "pure_sig (sg_alg (th_sign (th\<lparr>th_sign := c'\<rparr>))) (sg_ar (th_sign (th\<lparr>th_sign := c'\<rparr>)))"
    then have ps'': "pure_sig (sg_alg c') (sg_ar c')" by simp
    interpret E: sig_ext "sg_alg ?c" "sg_alg c'" "sg_ar ?c" "sg_consts ?c" "sg_consts c'"
      by (rule sig_ext_sign_le[OF sl ps''])
    show "pure_sig.thm_wf (sg_alg (th_sign (th\<lparr>th_sign := c'\<rparr>))) (sg_ar (th_sign (th\<lparr>th_sign := c'\<rparr>)))
        (sg_consts (th_sign (th\<lparr>th_sign := c'\<rparr>))) (th_maxidx (th\<lparr>th_sign := c'\<rparr>))
        (th_hyps (th\<lparr>th_sign := c'\<rparr>)) (th_tpairs (th\<lparr>th_sign := c'\<rparr>)) (th_prop (th\<lparr>th_sign := c'\<rparr>))"
      using E.thm_wf_ext[OF wf] ar by simp
    show "\<forall>M :: 'u model. is_model (th_sign (th\<lparr>th_sign := c'\<rparr>)) M \<longrightarrow>
        valid_in (th_sign (th\<lparr>th_sign := c'\<rparr>)) M (th_shyps (th\<lparr>th_sign := c'\<rparr>)) (th_hyps (th\<lparr>th_sign := c'\<rparr>))
          (th_tpairs (th\<lparr>th_sign := c'\<rparr>)) (th_prop (th\<lparr>th_sign := c'\<rparr>))"
    proof (intro allI impI)
      fix M :: "'u model" assume m: "is_model (th_sign (th\<lparr>th_sign := c'\<rparr>)) M"
      then have m': "is_model c' M" by simp
      interpret V: sem_ext "sg_alg ?c" "sg_alg c'" "sg_ar ?c" "sg_consts ?c" "sg_consts c'"
        "m_mem M" "m_fun M" "m_app M" "m_lam M" "m_bool M" "m_true M" "m_false M" "m_tcon M" "m_cls M" "m_cval M"
        using is_modelD[OF m'] sig_ext_sign_le[OF sl ps''] ar unfolding sem_ext_def by simp
      have pm: "pure_model (sg_alg ?c) (sg_ar ?c) (m_mem M) (m_fun M) (m_app M) (m_lam M) (m_bool M) (m_true M)
          (m_false M) (m_tcon M) (m_cls M) (m_cval M)"
        by (rule V.M.pure_model_axioms)
      have "valid_in ?c M (tm_sorts A) [] [] A" if "sg_axioms ?c a = Some A" for a A
      proof -
        from axs[OF that] have a': "sg_axioms c' a = Some A" and w: "E.S.wtp A" by auto
        have "valid_in c' M (tm_sorts A) [] [] A" using is_model_axiom[OF m' a'] .
        moreover have "V.M.wf_terms [] [] A" using w by (simp add: V.M.wf_terms_def E.S.wtp_def E.S.gterm_def)
        ultimately show ?thesis using V.valid_ext ar by (simp add: valid_in_def)
      qed
      with pm have "is_model ?c M" by (simp add: is_model_def)
      then have "valid_in ?c M (th_shyps th) (th_hyps th) (th_tpairs th) (th_prop th)" by (rule val)
      moreover have "V.M.wf_terms (th_hyps th) (th_tpairs th) (th_prop th)"
        using wf by (auto simp: E.S.thm_wf_def intro: V.M.wt_thm_wf_terms)
      ultimately show "valid_in (th_sign (th\<lparr>th_sign := c'\<rparr>)) M (th_shyps (th\<lparr>th_sign := c'\<rparr>))
          (th_hyps (th\<lparr>th_sign := c'\<rparr>)) (th_tpairs (th\<lparr>th_sign := c'\<rparr>)) (th_prop (th\<lparr>th_sign := c'\<rparr>))"
        using V.valid_ext ar by (simp add: valid_in_def)
    qed
  next
    assume ip: "is_prf_sig (th_sign (th\<lparr>th_sign := c'\<rparr>))"
    then have ip': "prf_sig (sg_alg c') (sg_ar c') (sg_close c') (sg_tyargs c')" by (simp add: is_prf_sig_def)
    then have ps'': "pure_sig (sg_alg c') (sg_ar c')" by (simp add: prf_sig_def)
    have ipc: "prf_sig (sg_alg ?c) (sg_ar ?c) (sg_close ?c) (sg_tyargs ?c)"
      using ip' ps ar cl ty by (simp add: prf_sig_def)
    interpret PE: prf_ext "sg_alg ?c" "sg_alg c'" "sg_ar ?c" "sg_consts ?c" "sg_consts c'" "sg_close ?c" "sg_tyargs ?c"
      using sig_ext_sign_le[OF sl ps''] ipc ip' ar cl ty by (simp add: prf_ext_def)
    have po: "proofs_ok th" using prfs ipc by (simp add: is_prf_sig_def)
    have H: "h \<in> set (th_hyps th) \<Longrightarrow> vars h = {} \<and> ttvars h = {}" for h
      using wf by (simp add: PE.S.thm_wf_def PE.S.wt_thm_def)
    have Hd: "const_decl (sg_consts ?c) n" if "h \<in> set (th_hyps th)" "n \<in> term_consts h" for h n
    proof -
      from wf that(1) have "PE.S.wtp h" by (simp add: PE.S.thm_wf_def PE.S.wt_thm_def)
      from PE.S.typing_consts_decl[OF PE.S.wtpD(2)[OF this] that(2)] show ?thesis .
    qed
    have A: "PE.P'.prf_valid (sg_ax c') (set (th_hyps th)) (th_tpairs th) p (th_prop th) \<and>
        prf_idx (\<lambda>i. 0 \<le> i) p \<and> prf_nolb 0 p" if "th_proof th = returnW p" for p
      using po that PE.prf_valid_ext[OF H ax] by (simp add: proofs_ok_def Let_def)
    have B: "PE.P'.zvalid (sg_ax c') (set (th_hyps th)) (th_tpairs th) z (th_prop th) \<and> zinv z \<and> znolb 0 z \<and>
        PE.S'.zhyps_ok z" if "th_zproof th = return z" for z
    proof -
      from po that have v: "PE.P.zvalid (sg_ax ?c) (set (th_hyps th)) (th_tpairs th) z (th_prop th)"
        and i: "zinv z" "znolb 0 z" "PE.S.zhyps_ok z"
        by (simp_all add: proofs_ok_def Let_def)
      have zv1: "PE.P'.zvalid (sg_ax c') (set (th_hyps th)) (th_tpairs th) z (th_prop th)"
        by (rule PE.zvalid_ext(1)[OF _ _ _ _ v]) (use H ax Hd axd in blast)+
      have zv2: "\<forall>h\<in>zhyps z. zt_decl (sg_consts ?c) h"
        by (rule PE.zvalid_ext(2)[where ax' = "sg_ax c'", OF _ _ _ _ v]) (use H ax Hd axd in blast)+
      from zv1 PE.zhyps_ok_ext[OF zv2 i(3)] i(1,2) show ?thesis by simp
    qed
    show "proofs_ok (th\<lparr>th_sign := c'\<rparr>)"
      unfolding proofs_ok_def Let_def using A B by (simp add: ar cl ty)
  qed
qed


lemma cons_ok_transfer: "sign_le c c' \<Longrightarrow> cons_ok c C \<Longrightarrow> cons_ok c' C"
  by (auto simp: cons_ok_def sign_le_def dest: has_sort_mono)

text \<open>\<open>Thm.transfer\<close>, on theorems:\<close>

definition transfer_thm :: "sign \<Rightarrow> 'u pure_thm \<Rightarrow> 'u pure_thm option" where
  "transfer_thm c' th =
    (if sign_le (sign_of th) c' then Some (Abs_thm ((rep_thm th)\<lparr>th_sign := c'\<rparr>)) else None)"

lemma transfer_thm_rep:
  assumes "transfer_thm c' th = Some th'"
  shows "rep_thm th' = (rep_thm th)\<lparr>th_sign := c'\<rparr>"
proof -
  have t: "sign_le (th_sign (rep_thm th)) c'" and th': "th' = Abs_thm ((rep_thm th)\<lparr>th_sign := c'\<rparr>)"
    using assms by (auto simp: transfer_thm_def split: if_splits)
  have "cons_ok c' (cons_of th)"
    using cons_ok_transfer[of "sign_of th" c' "cons_of th"] t by simp
  then show ?thesis using th' rep_Abs_thm[OF thm_ok_transfer[OF thm_ok_rep t]] by simp
qed

lemma transfer_thm_Some: "sign_le (sign_of th) c' \<Longrightarrow> \<exists>th'. transfer_thm c' th = Some th'"
  by (simp add: transfer_thm_def)

end

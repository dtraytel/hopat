section \<open>Soundness of \<open>unconstrainT\<close>\<close>

theory Thm_Unconstrain
  imports Thm_Strip_Shyps "Pure_Thm.Pure_Unconstrain"
begin

text \<open>
  \<open>Thm.unconstrainT\<close> (theory \<^theory_text>\<open>Pure_Unconstrain\<close>) keeps theorems valid: in every model,
  the new proposition holds for all values of the unconstrained type variables, since the
  premises \<open>OFCLASS\<close> make them values of the sorts of the old type variables, and of the sort
  hypotheses, which are then inhabited. The proofs of the result are proof boxes, which the proof
  judgment admits as atoms of the signature; the tight proof box is translated like a classic
  one (\<^const>\<open>zthm_tr\<close>). The classic and tight proofs of the result are valid if the signature
  admits the propositions of the boxes (theory \<open>Thm_Unconstrain_Proofs\<close> of session
  \<open>Thm_Proofs\<close>).
\<close>

subsection \<open>The context of the unconstrained type variables\<close>

lemma mapM_sort_of_atyp:
  assumes "\<And>T. T \<in> set Ts \<Longrightarrow> (\<exists>a S. T = TFree a S) \<or> (\<exists>v S. T = TVar v S)"
  shows "ok (mapM (\<lambda>T. do {S \<leftarrow> sort_of_atyp T; return (T, S)}) Ts) (map (\<lambda>T. (T, atyp_sort T)) Ts)"
  unfolding ok_mapM list.rel_map list_all2_same
proof
  fix T assume "T \<in> set Ts"
  from assms[OF this] show "ok (do {S \<leftarrow> sort_of_atyp T; return (T, S)}) (T, atyp_sort T)"
    by (elim disjE exE) simp_all
qed

lemma term_atyps_atom: "T \<in> set (term_atyps P) \<Longrightarrow> (\<exists>a S. T = TFree a S) \<or> (\<exists>v S. T = TVar v S)"
proof -
  assume "T \<in> set (term_atyps P)"
  then obtain U where "T \<in> set (atyps U)" by (auto simp: set_term_atyps tatoms_def)
  then show ?thesis by (rule atyps_atom)
qed

lemma unconstrain_ctx_ok:
  assumes ok: "ok (unconstrain_ctx invent shyps P) (pm, cm)"
  defines "present \<equiv> map (\<lambda>T. (T, atyp_sort T)) (term_atyps P)"
  defines "extra \<equiv> fold (ord_remove sort_ord \<circ> snd) present shyps"
  defines "names \<equiv> invent (integer_of_nat (length (term_atyps P) + length extra))"
  shows "pm = map2 (\<lambda>(T, S) a. (T, TVar (a, 0) S)) present (take (length (term_atyps P)) names)"
    and "cm = map (\<lambda>(_, V). ((case V of TVar _ S \<Rightarrow> S | _ \<Rightarrow> []), V)) pm @
      map2 (\<lambda>S a. (S, TVar (a, 0) S)) extra (drop (length (term_atyps P)) names)"
proof -
  have p: "ok (mapM (\<lambda>T. do {S \<leftarrow> sort_of_atyp T; return (T, S)}) (term_atyps P)) present"
    unfolding present_def by (rule mapM_sort_of_atyp[OF term_atyps_atom])
  define PM where "PM = map2 (\<lambda>(T, S) a. (T, TVar (a, 0) S)) present (take (length (term_atyps P)) names)"
  define CM where "CM = map (\<lambda>(_, V). ((case V of TVar _ S \<Rightarrow> S | _ \<Rightarrow> []), V)) PM @
      map2 (\<lambda>S a. (S, TVar (a, 0) S)) extra (drop (length (term_atyps P)) names)"
  have lp: "length present = length (term_atyps P)" by (simp add: present_def)
  have "ok (unconstrain_ctx invent shyps P) (PM, CM)"
    unfolding unconstrain_ctx_def ok_bindM
    by (intro exI[of _ present] conjI p) (simp add: Let_def PM_def CM_def extra_def names_def lp)
  with ok have "(pm, cm) = (PM, CM)" by auto
  then show "pm = map2 (\<lambda>(T, S) a. (T, TVar (a, 0) S)) present (take (length (term_atyps P)) names)"
    and "cm = map (\<lambda>(_, V). ((case V of TVar _ S \<Rightarrow> S | _ \<Rightarrow> []), V)) pm @
      map2 (\<lambda>S a. (S, TVar (a, 0) S)) extra (drop (length (term_atyps P)) names)"
    by (simp_all only: PM_def CM_def prod.inject)
qed

lemma set_fold_ord_remove_sorts:
  "set xs - snd ` set ps \<subseteq> set (fold (ord_remove sort_ord \<circ> snd) ps xs)"
proof (induction ps arbitrary: xs)
  case (Cons p ps)
  have "set xs - {snd p} \<subseteq> set (ord_remove sort_ord (snd p) xs)"
    by (rule set_ord_remove) (simp add: sort_ord_EQUAL)
  with Cons.IH[of "ord_remove sort_ord (snd p) xs"] show ?case by auto
qed simp

lemma map_fst_map2_pair:
  "length xs = length ys \<Longrightarrow> map fst (map2 (\<lambda>(T, S) a. (T, g T S a)) xs ys) = map fst xs"
  by (induction xs ys rule: list_induct2) auto

lemma set_map2_pair:
  "(U, V) \<in> set (map2 (\<lambda>(T, S) a. (T, TVar (a, 0) S)) (map (\<lambda>T. (T, atyp_sort T)) Ts) ns) \<Longrightarrow>
    \<exists>a. V = TVar (a, 0) (atyp_sort U)"
  by (fastforce simp: set_zip)

text \<open>
  The facts about the context: the present atomic types become type variables with their sorts,
  every sort hypothesis is the sort of such a type variable or of an extra one, and the
  premises of the context state the classes of these sorts for the type variables without sort.
\<close>

lemma unconstrain_ctx_props:
  assumes ok: "ok (unconstrain_ctx invent shyps P) (pm, cm)"
    and inv: "\<And>k. k \<le> length (invent (integer_of_nat k))"
  shows "\<And>U. U \<in> tatoms P \<Longrightarrow> \<exists>a. map_of pm U = Some (TVar (a, 0) (atyp_sort U)) \<and>
      (atyp_sort U, TVar (a, 0) (atyp_sort U)) \<in> set cm"
    and "\<And>S. S \<in> set shyps \<Longrightarrow> \<exists>a. (S, TVar (a, 0) S) \<in> set cm"
    and "\<And>S V. (S, V) \<in> set cm \<Longrightarrow> \<exists>a. V = TVar (a, 0) S"
    and "\<And>S a c. (S, TVar a S) \<in> set cm \<Longrightarrow> c \<in> set S \<Longrightarrow> mk_of_class (TVar a []) c \<in> set (ctx_constraints cm)"
    and "\<And>S V. (S, V) \<in> set cm \<Longrightarrow> S \<in> set shyps \<or> (\<exists>U\<in>tatoms P. S = atyp_sort U)"
    and "fst ` set pm = tatoms P"
proof -
  let ?Ts = "term_atyps P"
  define present where "present = map (\<lambda>T. (T, atyp_sort T)) ?Ts"
  define extra where "extra = fold (ord_remove sort_ord \<circ> snd) present shyps"
  define names where "names = invent (integer_of_nat (length ?Ts + length extra))"
  note pc = unconstrain_ctx_ok[OF ok, folded present_def, folded extra_def, folded names_def]
  have ln: "length ?Ts + length extra \<le> length names" unfolding names_def by (rule inv)
  have lt: "length present = length (take (length ?Ts) names)" using ln by (simp add: present_def)
  have "map fst pm = map fst present" unfolding pc(1) by (rule map_fst_map2_pair[OF lt])
  moreover have "map fst present = ?Ts" by (simp add: present_def comp_def)
  ultimately have "set (map fst pm) = set ?Ts" by simp
  then have fpm: "fst ` set pm = set ?Ts" by simp
  show "fst ` set pm = tatoms P" using fpm by (simp add: set_term_atyps)
  have pmV: "\<exists>a. V = TVar (a, 0) (atyp_sort U)" if "(U, V) \<in> set pm" for U V
    by (rule set_map2_pair) (use that in \<open>simp add: pc(1) present_def\<close>)
  define F :: "ptyp \<times> ptyp \<Rightarrow> psort \<times> ptyp" where "F = (\<lambda>(_, V). ((case V of TVar _ S \<Rightarrow> S | _ \<Rightarrow> []), V))"
  define E where "E = map2 (\<lambda>S a. (S, TVar (a, 0) S)) extra (drop (length ?Ts) names)"
  have cm: "set cm = F ` set pm \<union> set E" by (simp add: pc(2) F_def E_def)
  have cmI: "(S', TVar a' S') \<in> set cm" if "(U, TVar a' S') \<in> set pm" for U a' S'
  proof -
    have "F (U, TVar a' S') \<in> F ` set pm" using that by (rule imageI)
    then show ?thesis by (simp add: cm F_def)
  qed
  have Ei: "S \<in> set extra \<and> (\<exists>a. V = TVar (a, 0) S)" if "(S, V) \<in> set E" for S V
    using that by (fastforce simp: E_def set_zip)
  have pmS: "\<exists>V. (U, V) \<in> set pm" if "U \<in> tatoms P" for U
    using that fpm by (force simp: set_term_atyps)
  show "\<exists>a. map_of pm U = Some (TVar (a, 0) (atyp_sort U)) \<and> (atyp_sort U, TVar (a, 0) (atyp_sort U)) \<in> set cm"
    if U: "U \<in> tatoms P" for U
  proof -
    from pmS[OF U] obtain V0 where "(U, V0) \<in> set pm" by blast
    then obtain V where V: "map_of pm U = Some V" by (blast dest: weak_map_of_SomeI)
    then have m: "(U, V) \<in> set pm" by (rule map_of_SomeD)
    from pmV[OF m] obtain a where a: "V = TVar (a, 0) (atyp_sort U)" by blast
    have "(atyp_sort U, V) \<in> set cm" using cmI[OF m[unfolded a]] by (simp add: a)
    with V a show ?thesis by blast
  qed
  show "\<exists>a. (S, TVar (a, 0) S) \<in> set cm" if S: "S \<in> set shyps" for S
  proof (cases "S \<in> snd ` set present")
    case True
    then obtain U where U: "U \<in> set ?Ts" "S = atyp_sort U" by (auto simp: present_def)
    then have "U \<in> fst ` set pm" using fpm by simp
    then obtain V where m: "(U, V) \<in> set pm" by auto
    from pmV[OF m] obtain a where a: "V = TVar (a, 0) (atyp_sort U)" by blast
    show ?thesis using cmI[OF m[unfolded a]] U(2) by blast
  next
    case False
    with S set_fold_ord_remove_sorts[of shyps present] have "S \<in> set extra" by (auto simp: extra_def)
    then obtain j where j: "j < length extra" "extra ! j = S" by (auto simp: in_set_conv_nth)
    have jl: "j < length (drop (length ?Ts) names)" using j(1) ln by simp
    have "E ! j = (S, TVar (drop (length ?Ts) names ! j, 0) S)" using j jl by (simp add: E_def)
    moreover have "j < length E" using j(1) jl by (simp add: E_def)
    ultimately have "(S, TVar (drop (length ?Ts) names ! j, 0) S) \<in> set E" by (metis nth_mem)
    then show ?thesis by (auto simp: cm)
  qed
  show "\<exists>a. V = TVar (a, 0) S" if "(S, V) \<in> set cm" for S V
  proof -
    from that have "(S, V) \<in> F ` set pm \<or> (S, V) \<in> set E" by (simp add: cm)
    then show ?thesis
    proof
      assume "(S, V) \<in> F ` set pm"
      then obtain U V' where m: "(U, V') \<in> set pm" "(S, V) = F (U, V')" by auto
      from pmV[OF m(1)] obtain a where "V' = TVar (a, 0) (atyp_sort U)" by blast
      with m(2) show ?thesis by (simp add: F_def)
    qed (use Ei in blast)
  qed
  show "mk_of_class (TVar a []) c \<in> set (ctx_constraints cm)" if "(S, TVar a S) \<in> set cm" "c \<in> set S" for S a c
  proof -
    let ?f = "\<lambda>(_, V). case V of TVar ai S \<Rightarrow> map (\<lambda>c. mk_of_class (TVar ai []) c) S | _ \<Rightarrow> []"
    have "?f (S, TVar a S) \<in> ?f ` set cm" by (rule imageI[OF that(1)])
    then have "set (?f (S, TVar a S)) \<subseteq> set (ctx_constraints cm)"
      unfolding ctx_constraints_def set_concat set_map by blast
    moreover have "mk_of_class (TVar a []) c \<in> set (?f (S, TVar a S))" using that(2) by simp
    ultimately show ?thesis by blast
  qed
  show "S \<in> set shyps \<or> (\<exists>U\<in>tatoms P. S = atyp_sort U)" if "(S, V) \<in> set cm" for S V
  proof -
    have ex: "set extra \<subseteq> set shyps" unfolding extra_def by (rule set_fold_ord_remove_sub)
    from that have "(S, V) \<in> F ` set pm \<or> (S, V) \<in> set E" by (simp add: cm)
    then show ?thesis
    proof
      assume "(S, V) \<in> F ` set pm"
      then obtain U V' where m: "(U, V') \<in> set pm" "(S, V) = F (U, V')" by auto
      from pmV[OF m(1)] obtain a where a: "V' = TVar (a, 0) (atyp_sort U)" by blast
      have "U \<in> tatoms P" using m(1) fpm by (force simp: set_term_atyps)
      with m(2) a show ?thesis by (auto simp: F_def)
    qed (use Ei ex in blast)
  qed
qed

text \<open>The new proposition: the atomic types become their unconstrained type variables.\<close>

definition unc_atyp :: "(ptyp \<times> ptyp) list \<Rightarrow> ptyp \<Rightarrow> ptyp" where
  "unc_atyp pm U = (case map_of pm U of Some (TVar ai _) \<Rightarrow> TVar ai [] | Some V \<Rightarrow> V | None \<Rightarrow> U)"

lemma unconstrain_term_ok:
  assumes ok: "ok (unconstrain_ctx invent shyps P) (pm, cm)"
    and inv: "\<And>k. k \<le> length (invent (integer_of_nat k))"
  shows "ok (unconstrain_term pm cm P) (tmap (unc_atyp pm) P)"
  unfolding unconstrain_term_def
proof (rule map_typesM_ok)
  fix U assume "U \<in> tatoms P"
  from unconstrain_ctx_props(1)[OF ok inv this] obtain a where "map_of pm U = Some (TVar (a, 0) (atyp_sort U))"
    by blast
  then show "ok (unconstrain_atyp pm cm U) (unc_atyp pm U)"
    by (simp add: unconstrain_atyp_def unc_atyp_def)
qed


subsection \<open>Validity\<close>

context pure_model
begin

lemma holds_mk_of_class:
  assumes g: "good \<eta> \<xi>" and cc: "class_const (c + STR ''_class'') c" and ty: "e \<turnstile> mk_of_class T c : propT"
  shows "holds_at \<eta> \<xi> (mk_of_class T c) \<longleftrightarrow> cls c (tsem \<eta> T)"
proof -
  from ty have tyT: "(\<lambda>_. propT) \<turnstile> Const STR ''Pure.type'' (Type STR ''itself'' [T]) : Type STR ''itself'' [T]"
    by (auto simp: mk_of_class_def)
  have bv: "bvals \<eta> (\<lambda>_. propT) (\<lambda>_. utrue)" by (simp add: bvals_def ubool_mem)
  have m: "sem \<eta> \<xi> (\<lambda>_. utrue) (Const STR ''Pure.type'' (Type STR ''itself'' [T])) \<in>\<^sub>u tsem \<eta> (Type STR ''itself'' [T])"
    by (rule sem_typing[OF g tyT bv])
  with cc show ?thesis
    by (simp add: holds_at_def mk_of_class_def class_suffix_def csem_class propT_def uapp_ulam)
qed

theorem unconstrain_prop_valid:
  assumes ok: "ok (unconstrain_prop invent shyps P) ((pm, cm), P1)"
    and v: "svalid (set shyps) [] [] P"
    and inv: "\<And>k. k \<le> length (invent (integer_of_nat k))"
    and wP: "wtp P" and w1: "wtp P1"
    and cc: "\<And>S c. (\<exists>V. (S, V) \<in> set cm) \<Longrightarrow> c \<in> set S \<Longrightarrow> class_const (c + STR ''_class'') c"
  shows "svalid {[]} [] [] P1"
proof (rule svalidI)
  fix \<eta> \<xi> assume g: "good \<eta> \<xi>"
  from ok obtain P' where ctx: "ok (unconstrain_ctx invent shyps P) (pm, cm)"
    and P': "ok (unconstrain_term pm cm P) P'" and P1: "P1 = list_implies (ctx_constraints cm) P'"
    by (auto simp: unconstrain_prop_def split: prod.splits)
  note cp = unconstrain_ctx_props[OF ctx inv]
  let ?\<phi> = "unc_atyp pm"
  have P'e: "P' = tmap ?\<phi> P" using P' unconstrain_term_ok[OF ctx inv] by simp
  have g1: "gterm P1 propT" using w1 by (simp add: gterm_def wtp_def)
  have tyc: "(\<lambda>_. propT) \<turnstile> A : propT" if "A \<in> set (ctx_constraints cm)" for A
    using typing_list_impliesD[of "\<lambda>_. propT" "ctx_constraints cm" P'] wtpD(2)[OF w1] that by (simp add: P1)
  interpret pure_valuation alg ar ctab umem ufun uapp ulam ubool utrue ufalse tcon cls cval \<eta> \<xi>
    by unfold_locales (rule g)
  show "holds_at \<eta> \<xi> P1" unfolding P1
  proof (rule holds_list_impliesI)
    show "gterm (list_implies (ctx_constraints cm) P') propT" using g1 by (simp add: P1)
    assume hc: "\<And>A. A \<in> set (ctx_constraints cm) \<Longrightarrow> holds A"
    \<comment> \<open>the classes of the unconstrained type variables\<close>
    have cl: "cls c (fst \<eta> a [])" if "(S, TVar a S) \<in> set cm" "c \<in> set S" for S a c
    proof -
      have A: "mk_of_class (TVar a []) c \<in> set (ctx_constraints cm)" by (rule cp(4)[OF that])
      have "holds (mk_of_class (TVar a []) c)" by (rule hc[OF A])
      then show ?thesis using holds_mk_of_class[OF g cc[OF _ that(2)] tyc[OF A]] that(1) by auto
    qed
    have ss: "ssem S (fst \<eta> a [])" if "(S, TVar a S) \<in> set cm" for S a
      using cl[OF that] by (simp add: ssem_def)
    have ne: "une (fst \<eta> v S)" for v S using goodD(1)[OF g] unfolding good_t_def by blast
    \<comment> \<open>the values of the old type variables\<close>
    let ?\<eta>' = "tmapv \<eta> ?\<phi>" and ?\<xi>' = "vmapv ?\<phi> \<xi>"
    have atom: "une (tsem \<eta> (?\<phi> U)) \<and> ssem (atyp_sort U) (tsem \<eta> (?\<phi> U))" if U: "U \<in> tatoms P" for U
    proof -
      from cp(1)[OF U] obtain a where a: "map_of pm U = Some (TVar (a, 0) (atyp_sort U))"
        "(atyp_sort U, TVar (a, 0) (atyp_sort U)) \<in> set cm" by blast
      then show ?thesis using ss[OF a(2)] ne by (simp add: unc_atyp_def)
    qed
    have id: "?\<phi> U = U" if "map_of pm U = None" for U using that by (simp add: unc_atyp_def)
    have dom: "map_of pm U = None \<or> U \<in> tatoms P" for U
    proof (cases "map_of pm U")
      case (Some V)
      then have "(U, V) \<in> set pm" by (rule map_of_SomeD)
      then show ?thesis using cp(6) by force
    qed simp
    have gt0: "good_t \<eta>" by (rule goodD(1)[OF g])
    have gA: "une (tsem \<eta> A) \<and> (sort_ok alg (atyp_sort A) \<longrightarrow> sinh (atyp_sort A) \<longrightarrow>
        ssem (atyp_sort A) (tsem \<eta> A))" if "(\<exists>v S. A = TVar v S) \<or> (\<exists>a S. A = TFree a S)" for A
      using that gt0 unfolding good_t_def by (elim disjE exE) (simp_all del: split_paired_All)
    have gphi: "une (tsem \<eta> (?\<phi> A)) \<and> (sort_ok alg (atyp_sort A) \<longrightarrow> sinh (atyp_sort A) \<longrightarrow>
        ssem (atyp_sort A) (tsem \<eta> (?\<phi> A)))" if A: "(\<exists>v S. A = TVar v S) \<or> (\<exists>a S. A = TFree a S)" for A
    proof (cases "A \<in> tatoms P")
      case True
      with atom show ?thesis by blast
    next
      case False
      then have "map_of pm A = None" using dom by blast
      then have "?\<phi> A = A" by (rule id)
      with gA[OF A] show ?thesis by simp
    qed
    have gt: "good_t ?\<eta>'"
      unfolding good_t_def
    proof (intro conjI allI impI)
      fix v S
      show "une (fst ?\<eta>' v S)" using gphi[of "TVar v S"] by (simp add: tmapv_def)
      show "ssem S (fst ?\<eta>' v S)" if "sort_ok alg S" "sinh S"
        using gphi[of "TVar v S"] that by (simp add: tmapv_def)
    next
      fix a S
      show "une (snd ?\<eta>' a S)" using gphi[of "TFree a S"] by (simp add: tmapv_def)
      show "ssem S (snd ?\<eta>' a S)" if "sort_ok alg S" "sinh S"
        using gphi[of "TFree a S"] that by (simp add: tmapv_def)
    qed
    have tok: "tmap_ok ?\<phi>"
    proof (rule tmap_okI)
      show "cert_typ alg ar (?\<phi> (TFree a S))" if "sort_ok alg S" for a S
        using that dom[of "TFree a S"] cp(1)[of "TFree a S"]
        by (auto simp: unc_atyp_def cert_typ_def sort_ok_def)
      show "cert_typ alg ar (?\<phi> (TVar v S))" if "sort_ok alg S" for v S
        using that dom[of "TVar v S"] cp(1)[of "TVar v S"]
        by (auto simp: unc_atyp_def cert_typ_def sort_ok_def)
    qed
    have gv: "good_v ?\<eta>' ?\<xi>'"
      unfolding good_v_def
    proof (intro conjI allI impI)
      fix x T assume "cert_typ alg ar T"
      then have c: "cert_typ alg ar (map_atyps ?\<phi> T)" using tok by (simp add: tmap_ok_def)
      show "fst ?\<xi>' x T \<in>\<^sub>u tsem ?\<eta>' T" using goodD(2)[OF g c] by (simp add: vmapv_def tsem_map_atyps)
    next
      fix x T assume "cert_typ alg ar T"
      then have c: "cert_typ alg ar (map_atyps ?\<phi> T)" using tok by (simp add: tmap_ok_def)
      show "snd ?\<xi>' x T \<in>\<^sub>u tsem ?\<eta>' T" using goodD(3)[OF g c] by (simp add: vmapv_def tsem_map_atyps)
    qed
    \<comment> \<open>the sort hypotheses are inhabited\<close>
    have sh: "sinh S" if "S \<in> set shyps" for S
    proof -
      from cp(2)[OF that] obtain a where a: "(S, TVar (a, 0) S) \<in> set cm" by blast
      show ?thesis using ss[OF a] ne[of "(a, 0)" "[]"] unfolding sinh_def by blast
    qed
    have "holds_at ?\<eta>' ?\<xi>' P"
      by (rule svalidD[OF v sh]) (simp_all add: good_def gt gv)
    then show "holds P'" using sem_tmap[OF wtpD(2)[OF wP]] by (simp add: P'e holds_at_def)
  qed
qed

text \<open>The rule: the new theorem is valid if the old one is.\<close>

theorem unconstrainT_valid:
  assumes ok: "okT (unconstrainT_rep invent shyps hyps th) th'"
    and v: "valid (set shyps) hyps (th_tpairs th) (th_prop th)"
    and inv: "\<And>k. k \<le> length (invent (integer_of_nat k))"
    and wP: "wtp (th_prop th)" and w1: "wtp (th_prop th')"
    and cc: "\<And>S c. S \<in> set shyps \<or> (\<exists>U\<in>tatoms (th_prop th). S = atyp_sort U) \<Longrightarrow> c \<in> set S \<Longrightarrow>
      class_const (c + STR ''_class'') c"
  shows "hyps = [] \<and> th_tpairs th' = [] \<and> valid {[]} [] [] (th_prop th')"
proof -
  from ok have h: "hyps = []" "th_tpairs th = []"
    by (auto simp: unconstrainT_rep_def raiseW_def returnW_def split: if_splits)
  from ok h obtain pm cm P1 where u: "ok (unconstrain_prop invent shyps (th_prop th)) ((pm, cm), P1)"
    and th': "th' = mk_rep (maxidx_of_term P1) [] P1"
    by (auto simp: unconstrainT_rep_def raiseW_def returnW_def liftMT_def liftM_def liftWT_def Let_def
      split: if_splits option.splits xres.splits prod.splits)
  from u have ctx: "ok (unconstrain_ctx invent shyps (th_prop th)) (pm, cm)"
    by (auto simp: unconstrain_prop_def split: prod.splits)
  have wf0: "wf_terms [] [] (th_prop th)" using wP by (simp add: wf_terms_def gterm_def wtp_def)
  have wf1: "wf_terms [] [] P1" using w1 by (simp add: wf_terms_def gterm_def wtp_def th' mk_rep_def)
  have "svalid (set shyps) [] [] (th_prop th)" using v h valid_svalid[OF wf0] by simp
  then have "svalid {[]} [] [] P1"
  proof (rule unconstrain_prop_valid[OF u _ inv wP])
    show "wtp P1" using w1 by (simp add: th' mk_rep_def)
    show "class_const (c + STR ''_class'') c" if "\<exists>V. (S, V) \<in> set cm" "c \<in> set S" for S c
      using that unconstrain_ctx_props(5)[OF ctx inv] cc by blast
  qed
  then have "valid {[]} [] [] P1" using valid_svalid[OF wf1] by simp
  with h show ?thesis by (simp add: th' mk_rep_def)
qed

end

subsection \<open>Closures over free and schematic variables\<close>

text \<open>
  The propositions of proof boxes are closed over their free and schematic variables
  (\<^const>\<open>forall_closure\<close>); the box applied to them (or to no arguments) proves the proposition.
\<close>

lemma subst_abstract_over_aux_Free:
  "\<not> loose_bvar t lev \<Longrightarrow> 0 \<le> lev \<Longrightarrow> (abstract_over_aux (Free a T) lev t)[Free a T/lev] = t"
proof (induction t arbitrary: lev)
  case (Abs b U t)
  have "(abstract_over_aux (Free a T) (lev + 1) t)[Free a T/lev + 1] = t"
    by (rule Abs.IH) (use Abs.prems in simp_all)
  then show ?case by simp
next
  case (Bound i)
  then show ?case by (simp add: subst_Bound)
qed (simp_all add: aconv_term_atom)

lemma typs_aterms: "a \<in> set (aterms t) \<Longrightarrow> typs a \<subseteq> typs t"
  by (induction t) auto

subsection \<open>The proposition of the tight proof box\<close>

context pure_sig
begin

lemma zdec_close_zprop [simp]: "zdec (close_zprop As B) = list_implies (map zdec As) (zdec B)"
  by (induction As) (simp_all add: zconst_typ_def implies_def imp_type_def)

lemma aterms_zdec_Var:
  "Var xi T \<in> set (aterms (zdec z)) \<Longrightarrow> \<exists>T'. (xi, T') \<in> set (zterm_vars z) \<and> T = typ_of T' \<and> snd xi \<noteq> -1"
  by (induction z) (auto simp: Proof_Sig.of_class_def split: if_splits)

end

text \<open>The variables of a converted term are those of the term:\<close>

lemma zterm_vars_zterm_of':
  "zterm_of ta t = return z \<Longrightarrow> v \<in> set (zterm_vars z) \<Longrightarrow>
    \<exists>T. snd v = ztyp_of T \<and> (Var (fst v) T \<in> set (aterms t) \<or> (snd (fst v) = -1 \<and> Free (fst (fst v)) T \<in> set (aterms t)))"
proof (induction t arbitrary: z)
  case (App t u)
  from zterm_of_App_cases[OF App.prems(1)] show ?case
  proof (elim disjE exE conjE)
    fix T c assume "z = ZOfclass T c"
    with App.prems(2) show ?thesis by simp
  next
    fix t' u' assume t': "zterm_of ta t = return t'" and u': "zterm_of ta u = return u'" and z: "z = ZApp t' u'"
    from App.prems(2) z have "v \<in> set (zterm_vars t') \<or> v \<in> set (zterm_vars u')" by simp
    then show ?thesis using App.IH(1)[OF t'] App.IH(2)[OF u'] by auto
  qed
next
  case (Const c T)
  then show ?case using zterm_of_Const_vars[OF Const.prems(1)] by simp
next
  case (Abs a T b)
  from Abs.prems(1) obtain b' where "zterm_of ta b = return b'" "z = ZAbs a (ztyp_of T) b'"
    by (auto simp: bindZ_eq_returnZ)
  with Abs.IH Abs.prems(2) show ?case by auto
qed (auto simp: return_def)


lemma zterm_vars_zincr_bv: "set (zterm_vars (zincr_bv inc lev t)) = set (zterm_vars t)"
  by (induction inc lev t rule: zincr_bv.induct) auto

lemma zterm_vars_zsubst_bound: "set (zterm_vars (zsubst_bound arg lev t)) \<subseteq> set (zterm_vars arg) \<union> set (zterm_vars t)"
  by (induction arg lev t rule: zsubst_bound.induct) (auto simp: zincr_boundvars_def zterm_vars_zincr_bv)

lemma zterm_vars_beta_norm:
  assumes "beta_norm_term t = Some t'"
  shows "set (zterm_vars t') \<subseteq> set (zterm_vars t)"
  using assms
proof (induction t t' rule: beta_norm_term.raw_induct[rotated, consumes 1])
  case (1 bn t t')
  note h = "1.hyps" and IH = "1.IH"
  have redex: "set (zterm_vars t') \<subseteq> set (zterm_vars u) \<union> set (zterm_vars body)"
    if "bn (subst_term_bound u body) = Some t'" for u body
    using IH[OF that] zterm_vars_zsubst_bound[of u 0 body] by (auto simp: subst_term_bound_def)
  show ?case
  proof (cases t)
    case (ZAbs a T b)
    with h obtain b' where b': "bn b = Some b'" and t': "t' = ZAbs a T b'" by (auto simp: bind_eq_Some_conv)
    show ?thesis using IH[OF b'] by (simp add: ZAbs t')
  next
    case (ZApp g u)
    show ?thesis
    proof (cases "\<exists>b U body. g = ZAbs b U body")
      case True
      then obtain b U body where g: "g = ZAbs b U body" by blast
      have "bn (subst_term_bound u body) = Some t'" using h ZApp g by simp
      from redex[OF this] show ?thesis by (auto simp: ZApp g)
    next
      case False
      with h ZApp obtain nf where hf: "bn g = Some nf"
        and rest: "(case nf of ZAbs _ _ body \<Rightarrow> bn (subst_term_bound u body)
          | _ \<Rightarrow> Option.bind (bn u) (\<lambda>nu. Some (ZApp nf nu))) = Some t'"
        by (cases g) (auto simp: bind_eq_Some_conv)
      note IHf = IH[OF hf]
      show ?thesis
      proof (cases "\<exists>b U body. nf = ZAbs b U body")
        case True
        then obtain b U body where nfb: "nf = ZAbs b U body" by blast
        have "bn (subst_term_bound u body) = Some t'" using rest nfb by simp
        from redex[OF this] IHf show ?thesis by (auto simp: ZApp nfb)
      next
        case False
        with rest obtain nu where hu: "bn u = Some nu" and t': "t' = ZApp nf nu"
          by (cases nf) (auto simp: bind_eq_Some_conv)
        show ?thesis using IHf IH[OF hu] by (auto simp: ZApp t')
      qed
    qed
  qed (use h in auto)
qed

lemma zterm_vars_close_zprop:
  "set (zterm_vars (close_zprop As B)) = (\<Union>A\<in>set As. set (zterm_vars A)) \<union> set (zterm_vars B)"
  by (induction As) auto


subsection \<open>The unconstrained proposition\<close>

lemma ctx_constraints_mem:
  "A \<in> set (ctx_constraints cm) \<Longrightarrow> \<exists>S' S ai cl. (S', TVar ai S) \<in> set cm \<and> cl \<in> set S \<and> A = mk_of_class (TVar ai []) cl"
  by (auto simp: ctx_constraints_def split: ptyp.splits) blast

lemma unconstrain_term_ok':
  assumes ok: "ok (unconstrain_ctx invent shyps P) (pm, cm)"
    and inv: "\<And>k. k \<le> length (invent (integer_of_nat k))" and t: "tatoms t \<subseteq> tatoms P"
  shows "ok (unconstrain_term pm cm t) (tmap (unc_atyp pm) t)"
  unfolding unconstrain_term_def
proof (rule map_typesM_ok)
  fix U assume "U \<in> tatoms t"
  with t have "U \<in> tatoms P" by blast
  from unconstrain_ctx_props(1)[OF ok inv this] obtain a where "map_of pm U = Some (TVar (a, 0) (atyp_sort U))"
    by blast
  then show "ok (unconstrain_atyp pm cm U) (unc_atyp pm U)"
    by (simp add: unconstrain_atyp_def unc_atyp_def)
qed

lemma unc_atyp_atom:
  assumes ok: "ok (unconstrain_ctx invent shyps P) (pm, cm)"
    and inv: "\<And>k. k \<le> length (invent (integer_of_nat k))" and U: "U \<in> tatoms P"
  obtains a where "unc_atyp pm U = TVar (a, 0) []" "map_of pm U = Some (TVar (a, 0) (atyp_sort U))"
  using unconstrain_ctx_props(1)[OF ok inv U] by (auto simp: unc_atyp_def)

text \<open>Distinct invented names make the unconstrained type variables distinct:\<close>

lemma unc_atyp_inj:
  assumes ok: "ok (unconstrain_ctx invent shyps P) (pm, cm)"
    and inv: "\<And>k. k \<le> length (invent (integer_of_nat k))" and dis: "\<And>k. distinct (invent (integer_of_nat k))"
    and U: "U \<in> tatoms P" "U' \<in> tatoms P" and e: "unc_atyp pm U = unc_atyp pm U'"
  shows "U = U'"
proof -
  let ?Ts = "term_atyps P"
  define present where "present = map (\<lambda>T. (T, atyp_sort T)) ?Ts"
  define extra where "extra = fold (ord_remove sort_ord \<circ> snd) present shyps"
  define names where "names = invent (integer_of_nat (length ?Ts + length extra))"
  let ?ns = "take (length ?Ts) names"
  note pc = unconstrain_ctx_ok[OF ok, folded present_def, folded extra_def, folded names_def]
  have dn: "distinct ?ns" unfolding names_def by (rule distinct_take[OF dis])
  have mem: "\<exists>i<length ?Ts. i < length ?ns \<and> X = ?Ts ! i \<and> a = ?ns ! i" if "(X, TVar (a, 0) S) \<in> set pm" for X a S
    using that by (auto simp: pc(1) present_def set_zip)
  from unc_atyp_atom[OF ok inv U(1)] obtain a where a: "unc_atyp pm U = TVar (a, 0) []"
    "map_of pm U = Some (TVar (a, 0) (atyp_sort U))" by blast
  from unc_atyp_atom[OF ok inv U(2)] obtain a' where a': "unc_atyp pm U' = TVar (a', 0) []"
    "map_of pm U' = Some (TVar (a', 0) (atyp_sort U'))" by blast
  have aa: "a = a'" using e a(1) a'(1) by simp
  from mem[OF map_of_SomeD[OF a(2)]] obtain i where i: "i < length ?Ts" "i < length ?ns" "U = ?Ts ! i" "a = ?ns ! i"
    by blast
  from mem[OF map_of_SomeD[OF a'(2)]] obtain j where j: "j < length ?Ts" "j < length ?ns" "U' = ?Ts ! j" "a' = ?ns ! j"
    by blast
  have "i = j" using nth_eq_iff_index_eq[OF dn i(2) j(2)] i(4) j(4) aa by simp
  with i(3) j(3) show ?thesis by simp
qed

text \<open>Variables of the same name have the same type:\<close>

definition vars_consistent :: "pterm \<Rightarrow> bool" where
  "vars_consistent t \<longleftrightarrow> (\<forall>xi T U. Var xi T \<in> set (aterms t) \<longrightarrow> Var xi U \<in> set (aterms t) \<longrightarrow> T = U) \<and>
    (\<forall>x T U. Free x T \<in> set (aterms t) \<longrightarrow> Free x U \<in> set (aterms t) \<longrightarrow> T = U)"

lemma map_types_Var_eq: "map_types g a = Var xi T \<longleftrightarrow> (\<exists>T0. a = Var xi T0 \<and> T = g T0)"
  by (cases a) auto

lemma map_types_Free_eq: "map_types g a = Free x T \<longleftrightarrow> (\<exists>T0. a = Free x T0 \<and> T = g T0)"
  by (cases a) auto

lemma vars_consistent_map_types:
  assumes "vars_consistent t"
  shows "vars_consistent (map_types g t)"
  unfolding vars_consistent_def aterms_map_types set_map
proof (intro conjI allI impI)
  fix xi T U assume "Var xi T \<in> map_types g ` set (aterms t)" "Var xi U \<in> map_types g ` set (aterms t)"
  then obtain T0 U0 where "Var xi T0 \<in> set (aterms t)" "T = g T0" "Var xi U0 \<in> set (aterms t)" "U = g U0"
    by (auto simp: image_iff map_types_Var_eq eq_commute[of "Var _ _"])
  with assms show "T = U" unfolding vars_consistent_def by metis
next
  fix x T U assume "Free x T \<in> map_types g ` set (aterms t)" "Free x U \<in> map_types g ` set (aterms t)"
  then obtain T0 U0 where "Free x T0 \<in> set (aterms t)" "T = g T0" "Free x U0 \<in> set (aterms t)" "U = g U0"
    by (auto simp: image_iff map_types_Free_eq eq_commute[of "Free _ _"])
  with assms show "T = U" unfolding vars_consistent_def by metis
qed

text \<open>The variables of the unconstrained proposition are those of the conclusion:\<close>

lemma variables_of_fold:
  "variables_of u = rev (fold (\<lambda>a acc. if (\<exists>xi T. a = Var xi T) \<or> (\<exists>x T. a = Free x T) then List.insert a acc else acc)
    (aterms u) [])"
  unfolding variables_of_def by (rule arg_cong[where f = rev], rule fold_cong) (auto split: pterm.splits)

lemma fold_insert_skip:
  "(\<forall>a\<in>set xs. \<not> Q a) \<Longrightarrow> fold (\<lambda>a acc. if Q a then List.insert a acc else acc) xs acc = acc"
  by (induction xs arbitrary: acc) auto

lemma variables_of_list_implies:
  assumes "\<forall>A\<in>set As. \<forall>a\<in>set (aterms A). \<not> ((\<exists>xi T. a = Var xi T) \<or> (\<exists>x T. a = Free x T))"
  shows "variables_of (list_implies As B) = variables_of B"
proof -
  let ?Q = "\<lambda>a. (\<exists>xi T. a = Var xi T) \<or> (\<exists>x T. a = Free x T)"
  let ?f = "\<lambda>a acc. if ?Q a then List.insert a acc else acc"
  have "fold ?f (aterms (list_implies As B)) [] = fold ?f (aterms B) []"
    using assms
  proof (induction As)
    case (Cons A As)
    have "fold ?f (aterms implies @ aterms A) [] = []"
      by (rule fold_insert_skip) (use Cons.prems in \<open>auto simp: implies_def\<close>)
    with Cons show ?case by simp
  qed simp
  then show ?thesis by (simp only: variables_of_fold)
qed

lemma vars_aterms: "a \<in> set (aterms t) \<Longrightarrow> vars a \<subseteq> vars t"
  by (induction t) auto

context pure_sig
begin

lemma closed_beta_reds: "s \<rightarrow>\<^sub>\<beta>\<^sup>* t \<Longrightarrow> closed s \<Longrightarrow> closed t"
  by (induction rule: rtranclp_induct) (auto simp: closed_def dest: loose_bvar_beta[of _ _ 0])

lemma cert_atyp_sort: "cert_typ alg ar T \<Longrightarrow> A \<in> set (atyps T) \<Longrightarrow> sort_ok alg (atyp_sort A)"
  by (induction T) (auto simp: cert_typ_def)

text \<open>The new proposition is well-formed:\<close>

lemma unconstrain_prop_wf:
  assumes ok: "ok (unconstrain_prop invent shyps P) ((pm, cm), P1)"
    and inv: "\<And>k. k \<le> length (invent (integer_of_nat k))"
    and w: "thm_wf m [] [] P" and so: "\<forall>S\<in>set shyps. sort_ok alg S"
    and oc: "\<forall>cl\<in>classes alg. \<forall>a. wtp (mk_of_class (TVar a []) cl)"
  shows "P1 = list_implies (ctx_constraints cm) (tmap (unc_atyp pm) P)"
    and "ok (unconstrain_ctx invent shyps P) (pm, cm)"
    and "\<And>S V cl. (S, V) \<in> set cm \<Longrightarrow> cl \<in> set S \<Longrightarrow> cl \<in> classes alg"
    and "thm_wf (maxidx_of_term P1) [] [] P1"
    and "\<forall>A\<in>set (ctx_constraints cm). wtp A" and "wtp (tmap (unc_atyp pm) P)"
proof -
  from ok obtain P' where ctx: "ok (unconstrain_ctx invent shyps P) (pm, cm)"
    and P': "ok (unconstrain_term pm cm P) P'" and P1: "P1 = list_implies (ctx_constraints cm) P'"
    by (auto simp: unconstrain_prop_def split: prod.splits)
  note cp = unconstrain_ctx_props[OF ctx inv]
  let ?\<phi> = "unc_atyp pm"
  have P'e: "P' = tmap ?\<phi> P" using P' unconstrain_term_ok[OF ctx inv] by simp
  show "ok (unconstrain_ctx invent shyps P) (pm, cm)" by (rule ctx)
  show "P1 = list_implies (ctx_constraints cm) (tmap ?\<phi> P)" by (simp add: P1 P'e)
  have wP: "wtp P" and nnv: "\<forall>v\<in>vars P. 0 \<le> snd (fst v)"
    using w by (simp_all add: thm_wf_def wt_thm_def vars_thm_def)
  have sU: "sort_ok alg (atyp_sort U)" if "U \<in> tatoms P" for U
  proof -
    from that obtain T where "T \<in> typs P" "U \<in> set (atyps T)" by (auto simp: tatoms_def)
    then show ?thesis using cert_atyp_sort typing_typs[OF wtpD(2)[OF wP]] by blast
  qed
  show cls: "cl \<in> classes alg" if "(S, V) \<in> set cm" "cl \<in> set S" for S V cl
    using cp(5)[OF that(1)] so sU that(2) by (auto simp: sort_ok_def)
  have dom: "map_of pm U = None \<or> U \<in> tatoms P" for U
  proof (cases "map_of pm U")
    case (Some V)
    then have "(U, V) \<in> set pm" by (rule map_of_SomeD)
    then show ?thesis using cp(6) by force
  qed simp
  have tok: "tmap_ok ?\<phi>"
  proof (rule tmap_okI)
    show "cert_typ alg ar (?\<phi> (TFree a S))" if "sort_ok alg S" for a S
      using that dom[of "TFree a S"] cp(1)[of "TFree a S"]
      by (auto simp: unc_atyp_def cert_typ_def sort_ok_def)
    show "cert_typ alg ar (?\<phi> (TVar v S))" if "sort_ok alg S" for v S
      using that dom[of "TVar v S"] cp(1)[of "TVar v S"]
      by (auto simp: unc_atyp_def cert_typ_def sort_ok_def)
  qed
  show "wtp (tmap ?\<phi> P)" by (rule wtp_tmap[OF wP tok])
  then have wP': "wtp P'" by (simp add: P'e)
  have cs: "\<exists>a cl. cl \<in> classes alg \<and> A = mk_of_class (TVar (a, 0) []) cl"
    if "A \<in> set (ctx_constraints cm)" for A
  proof -
    from ctx_constraints_mem[OF that] obtain S' S ai cl where m: "(S', TVar ai S) \<in> set cm" "cl \<in> set S"
      "A = mk_of_class (TVar ai []) cl" by blast
    from cp(3)[OF m(1)] obtain a where "TVar ai S = TVar (a, 0) S'" by blast
    then have a: "ai = (a, 0)" "S = S'" by simp_all
    with m cls[OF m(1)] show ?thesis by blast
  qed
  show wc: "\<forall>A\<in>set (ctx_constraints cm). wtp A" using cs oc by blast
  have ci: "ctx_constraints cm \<noteq> [] \<longrightarrow> cert_typ alg ar imp_type"
  proof
    assume "ctx_constraints cm \<noteq> []"
    then obtain A where A: "A \<in> set (ctx_constraints cm)" by (cases "ctx_constraints cm") auto
    from cs[OF A] obtain a cl where Ae: "A = mk_of_class (TVar (a, 0) []) cl" by blast
    have "(\<lambda>_. propT) \<turnstile> A : propT" using wc A by (auto dest: wtpD(2))
    then have "cert_typ alg ar (Type STR ''itself'' [TVar (a, 0) []] \<rightarrow>\<^sub>T Type STR ''prop'' [])"
      by (rule typing_typs) (simp add: Ae mk_of_class_def)
    then show "cert_typ alg ar imp_type" by (simp add: cert_typ_fun imp_type_def propT_def)
  qed
  have w1: "wtp P1" unfolding P1 by (rule wtp_list_impliesI[OF wc wP' ci])
  have nnv1: "\<forall>v\<in>vars P1. 0 \<le> snd (fst v)"
  proof
    fix v assume "v \<in> vars P1"
    then consider A where "A \<in> set (ctx_constraints cm)" "v \<in> vars A" | "v \<in> vars P'"
      by (auto simp: P1 vars_list_implies)
    then show "0 \<le> snd (fst v)"
    proof cases
      case 1
      then show ?thesis using cs[OF 1(1)] by (auto simp: mk_of_class_def)
    next
      case 2
      then show ?thesis using nnv by (auto simp: P'e vars_map_types)
    qed
  qed
  have nnt1: "\<forall>v\<in>ttvars P1. 0 \<le> snd (fst v)"
  proof
    fix v assume "v \<in> ttvars P1"
    then consider A where "A \<in> set (ctx_constraints cm)" "v \<in> ttvars A" | "v \<in> ttvars P'"
      using ttvars_list_implies_sub[of "ctx_constraints cm" P'] by (auto simp: P1)
    then show "0 \<le> snd (fst v)"
    proof cases
      case 1
      then show ?thesis using cs[OF 1(1)] by (auto simp: mk_of_class_def ttvars_def)
    next
      case 2
      then have "TVar (fst v) (snd v) \<in> tatoms P'" by (intro ttvars_tatoms) simp
      then obtain U where U: "U \<in> tatoms P" "TVar (fst v) (snd v) \<in> set (atyps (?\<phi> U))"
        unfolding P'e tatoms_tmap by blast
      from unc_atyp_atom[OF ctx inv U(1)] obtain a where "?\<phi> U = TVar (a, 0) []" by blast
      with U(2) show ?thesis by simp
    qed
  qed
  show "thm_wf (maxidx_of_term P1) [] [] P1"
    using w1 maxidx_of_term_ibelow[of P1] maxidx_term_ge[of "-1" P1] nnv1 nnt1
    by (simp add: thm_wf_def wt_thm_def vars_thm_def tvars_thm_def maxidx_of_term_def)
qed

end

subsection \<open>The rule on theorems\<close>

text \<open>
  As for the proof boxes of Isabelle, the signature must admit the propositions of the classic and
  the tight proof box (\<^const>\<open>sg_ax\<close>), closed as by \<open>Proofterm\<close>, with type arguments among their
  type variables; the tight proof box is translated to a classic one (\<^const>\<open>zthm_tr\<close>). The
  constants of the classes are declared (\<open>Logic.const_of_class\<close>).
\<close>

definition unc_box_ok :: "sign \<Rightarrow> pterm \<Rightarrow> bool" where
  "unc_box_ok c B \<longleftrightarrow> sg_ax c B \<and> sg_close c B = forall_closure B \<and> (\<forall>v\<in>set (sg_tyargs c B). v \<in> ttvars B)"

definition sign_ofclass :: "sign \<Rightarrow> bool" where
  "sign_ofclass c \<longleftrightarrow> (\<forall>cl\<in>classes (sg_alg c). pure_sig_gen.class_const (sg_alg c) (sg_consts c) (cl + STR ''_class'') cl \<and>
    (\<forall>a. pure_sig_gen.wtp (sg_alg c) (sg_ar c) (sg_consts c) (mk_of_class (TVar a []) cl)))"

definition zbox_prop :: "zproof \<Rightarrow> zterm" where
  "zbox_prop z = (case z of ZConstp ((_, A), _) \<Rightarrow> A | _ \<Rightarrow> ZBound 0)"

text \<open>
  The conditions of the rule: the invented names are distinct and enough (as for
  \<open>Name.invent_global_types\<close>), the box of a proposition has it as proposition and no type
  arguments, the sort hypotheses are certified, and the variables of the proposition have unique
  types. Isabelle does not check the last condition. Without it, the table of the instances of the
  tight proof box would have two keys of the same name; a type instantiation of the proof
  (\<open>ZTerm.map_insts\<close>, \<^const>\<open>map_insts\<close>) instantiates the types of the keys and may merge them,
  after which the box no longer has an instance for each variable of its proposition. The
  invariant of tight proofs (\<open>zconsts_ok\<close>, part of \<open>zinv\<close>, session \<open>Thm_Proofs\<close>) excludes such tables.
\<close>

definition unc_ok :: "(pterm \<Rightarrow> thm_header \<times> thm_body) \<Rightarrow> zthm_name \<Rightarrow> (integer \<Rightarrow> name list) \<Rightarrow> sign \<Rightarrow>
    psort list \<Rightarrow> pterm \<Rightarrow> thm_rep \<Rightarrow> bool" where
  "unc_ok box zn invent c shyps P r \<longleftrightarrow>
    (\<forall>n. n \<le> length (invent (integer_of_nat n)) \<and> distinct (invent (integer_of_nat n))) \<and>
    (\<forall>B. hd_prop (fst (box B)) = B \<and> hd_types (fst (box B)) = None) \<and>
    (\<forall>S\<in>set shyps. sort_ok (sg_alg c) S) \<and> sign_ofclass c \<and> vars_consistent P \<and>
    (is_prf_sig c \<longrightarrow> unc_box_ok c (th_prop r) \<and>
      (\<forall>z. zunconstrain_proof (pure_sig_gen.ztargs (sg_consts c)) zn invent shyps P = return z \<longrightarrow>
        unc_box_ok c (pure_sig_gen.zdec (sg_consts c) (zbox_prop z))))"

definition unconstrainT_data :: "(pterm \<Rightarrow> thm_header \<times> thm_body) \<Rightarrow> zthm_name \<Rightarrow> (integer \<Rightarrow> name list) \<Rightarrow>
    'u pure_thm \<Rightarrow> thm_rep \<Rightarrow> thm_data" where
  "unconstrainT_data box zn invent th r = mk_thm r {[]} [] (sign_of th)
    (bindW (proof_of th) (\<lambda>_. liftMP (unconstrain_thm_proof box invent (shyps_list (shyps_of th)) (th_prop (rep_of th)))))
    (bindM (zproof_of th) (\<lambda>_. zunconstrain_proof (pure_sig_gen.ztargs (sg_consts (sign_of th))) zn invent
      (shyps_list (shyps_of th)) (th_prop (rep_of th))))"

lemma unconstrainT_data_sel [simp]:
  "th_maxidx (unconstrainT_data box zn invent th r) = th_maxidx r"
  "th_tpairs (unconstrainT_data box zn invent th r) = th_tpairs r"
  "th_prop (unconstrainT_data box zn invent th r) = th_prop r"
  "th_shyps (unconstrainT_data box zn invent th r) = {[]}"
  "th_hyps (unconstrainT_data box zn invent th r) = []"
  "th_sign (unconstrainT_data box zn invent th r) = sign_of th"
  "th_constraints (unconstrainT_data box zn invent th r) = {}"
  by (simp_all add: unconstrainT_data_def)

theorem thm_sem_unconstrainT:
  fixes th :: "'u pure_thm"
  assumes ok: "okT (unconstrainT_rep invent (shyps_list (shyps_of th)) (hyps_of th) (rep_of th)) r"
    and fin: "finite (shyps_of th)"
    and uo: "unc_ok box zn invent (sign_of th) (shyps_list (shyps_of th)) (th_prop (rep_of th)) r"
  shows "thm_sem TYPE('u) (unconstrainT_data box zn invent th r)"
proof -
  let ?c = "sign_of th" and ?shyps = "shyps_list (shyps_of th)" and ?P = "th_prop (rep_of th)"
  have sl: "set ?shyps = shyps_of th" by (rule set_shyps_list[OF fin])
  have inv: "\<And>k. k \<le> length (invent (integer_of_nat k))" and dis: "\<And>k. distinct (invent (integer_of_nat k))"
    and bx: "\<And>B. hd_prop (fst (box B)) = B" "\<And>B. hd_types (fst (box B)) = None"
    and so: "\<forall>S\<in>set ?shyps. sort_ok (sg_alg ?c) S" and soc: "sign_ofclass ?c" and vcP: "vars_consistent ?P"
    using uo by (simp_all add: unc_ok_def)
  from ok have h: "hyps_of th = []" "th_tpairs (rep_of th) = []"
    by (auto simp: unconstrainT_rep_def raiseW_def returnW_def split: if_splits)
  from ok h obtain args pm cm P1 where args: "ok (prop_args ?P) args"
    and u: "ok (unconstrain_prop invent ?shyps ?P) ((pm, cm), P1)" and r: "r = mk_rep (maxidx_of_term P1) [] P1"
    by (auto simp: unconstrainT_rep_def raiseW_def returnW_def liftMT_def liftM_def liftWT_def Let_def
      split: if_splits option.splits xres.splits prod.splits)
  have rs: "th_maxidx r = maxidx_of_term P1" "th_tpairs r = []" "th_prop r = P1" by (simp_all add: r mk_rep_def)
  have oc: "pure_sig_gen.class_const (sg_alg ?c) (sg_consts ?c) (cl + STR ''_class'') cl"
    if "cl \<in> classes (sg_alg ?c)" for cl
    using soc that unfolding sign_ofclass_def by blast
  have ocw: "\<forall>cl\<in>classes (sg_alg ?c). \<forall>a. pure_sig_gen.wtp (sg_alg ?c) (sg_ar ?c) (sg_consts ?c) (mk_of_class (TVar a []) cl)"
    using soc by (simp add: sign_ofclass_def)
  show ?thesis
  proof (rule thm_semI)
    assume "pure_sig (sg_alg (th_sign (unconstrainT_data box zn invent th r))) (sg_ar (th_sign (unconstrainT_data box zn invent th r)))"
    then have ps: "pure_sig (sg_alg ?c) (sg_ar ?c)" by simp
    then interpret pure_sig "sg_alg ?c" "sg_ar ?c" "sg_consts ?c" .
    have w0: "thm_wf (th_maxidx (rep_of th)) [] [] ?P" using pure_thm_wf[of th] h ps by simp
    note uw = unconstrain_prop_wf[OF u inv w0 so ocw]
    show "pure_sig.thm_wf (sg_alg (th_sign (unconstrainT_data box zn invent th r)))
        (sg_ar (th_sign (unconstrainT_data box zn invent th r))) (sg_consts (th_sign (unconstrainT_data box zn invent th r)))
        (th_maxidx (unconstrainT_data box zn invent th r)) (th_hyps (unconstrainT_data box zn invent th r))
        (th_tpairs (unconstrainT_data box zn invent th r)) (th_prop (unconstrainT_data box zn invent th r))"
      using uw(4) by (simp add: rs)
  next
    fix M :: "'u model"
    assume ps: "pure_sig (sg_alg (th_sign (unconstrainT_data box zn invent th r))) (sg_ar (th_sign (unconstrainT_data box zn invent th r)))"
      and M: "is_model (th_sign (unconstrainT_data box zn invent th r)) M"
    interpret pure_model "sg_alg ?c" "sg_ar ?c" "sg_consts ?c" "m_mem M" "m_fun M" "m_app M" "m_lam M"
      "m_bool M" "m_true M" "m_false M" "m_tcon M" "m_cls M" "m_cval M"
      by (rule is_modelD) (use M in simp)
    have w0: "thm_wf (th_maxidx (rep_of th)) [] [] ?P" using pure_thm_wf[of th] h ps by simp
    note uw = unconstrain_prop_wf[OF u inv w0 so ocw]
    have v0: "valid (set ?shyps) (hyps_of th) (th_tpairs (rep_of th)) ?P"
      using pure_thm_valid_in[of th M] M sl by (simp add: valid_in_def)
    have "hyps_of th = [] \<and> th_tpairs r = [] \<and> valid {[]} [] [] (th_prop r)"
    proof (rule unconstrainT_valid[OF ok v0 inv])
      show "wtp ?P" using w0 by (simp add: thm_wf_def wt_thm_def)
      show "wtp (th_prop r)" using uw(4) by (simp add: rs thm_wf_def wt_thm_def)
      show "class_const (c + STR ''_class'') c"
        if "S \<in> set ?shyps \<or> (\<exists>U\<in>tatoms ?P. S = atyp_sort U)" "c \<in> set S" for S c
      proof -
        have "\<exists>V. (S, V) \<in> set cm"
        proof -
          note cp = unconstrain_ctx_props[OF uw(2) inv]
          from that(1) show ?thesis
          proof
            assume "S \<in> set ?shyps"
            from cp(2)[OF this] show ?thesis by blast
          next
            assume "\<exists>U\<in>tatoms ?P. S = atyp_sort U"
            then obtain U where "U \<in> tatoms ?P" "S = atyp_sort U" by blast
            with cp(1)[of U] show ?thesis by blast
          qed
        qed
        then obtain V where "(S, V) \<in> set cm" by blast
        from uw(3)[OF this that(2)] show ?thesis by (rule oc)
      qed
    qed
    then show "valid_in (th_sign (unconstrainT_data box zn invent th r)) M
        (th_shyps (unconstrainT_data box zn invent th r)) (th_hyps (unconstrainT_data box zn invent th r))
        (th_tpairs (unconstrainT_data box zn invent th r)) (th_prop (unconstrainT_data box zn invent th r))"
      by (simp add: valid_in_def)
  qed
qed

text \<open>
  \<open>Thm.unconstrainT\<close> on theorems: \<open>Thm.strip_shyps\<close> (with the logical types \<open>gts\<close>), then the
  rule on the stripped theorem; \<open>None\<close> if it raises an exception or a condition fails.
\<close>

definition unconstrainT_thm' :: "(pterm \<Rightarrow> thm_header \<times> thm_body) \<Rightarrow> zthm_name \<Rightarrow> (integer \<Rightarrow> name list) \<Rightarrow>
    'u pure_thm \<Rightarrow> 'u pure_thm option" where
  "unconstrainT_thm' box zn invent th =
    (case resT (unconstrainT_rep invent (shyps_list (shyps_of th)) (hyps_of th) (rep_of th)) of
      None \<Rightarrow> None
    | Some r \<Rightarrow>
        if finite (shyps_of th) \<and> unc_ok box zn invent (sign_of th) (shyps_list (shyps_of th)) (th_prop (rep_of th)) r
        then Some (Abs_thm (unconstrainT_data box zn invent th r)) else None)"

definition unconstrainT_thm :: "name list \<Rightarrow> (pterm \<Rightarrow> thm_header \<times> thm_body) \<Rightarrow> zthm_name \<Rightarrow>
    (integer \<Rightarrow> name list) \<Rightarrow> 'u pure_thm \<Rightarrow> 'u pure_thm option" where
  "unconstrainT_thm gts box zn invent th = Option.bind (strip_shyps_thm gts th) (unconstrainT_thm' box zn invent)"

theorem unconstrainT_thm'_rep:
  assumes "unconstrainT_thm' box zn invent th = Some th'"
  obtains r where "okT (unconstrainT_rep invent (shyps_list (shyps_of th)) (hyps_of th) (rep_of th)) r"
    "rep_thm th' = unconstrainT_data box zn invent th r"
proof -
  from assms obtain r where ok: "okT (unconstrainT_rep invent (shyps_list (shyps_of th)) (hyps_of th) (rep_of th)) r"
    and g: "finite (shyps_of th)" "unc_ok box zn invent (sign_of th) (shyps_list (shyps_of th)) (th_prop (rep_of th)) r"
    and th': "th' = Abs_thm (unconstrainT_data box zn invent th r)"
    by (auto simp: unconstrainT_thm'_def resT_Some split: option.splits if_splits)
  show thesis by (rule that[OF ok]) (simp add: th' Abs_thm_inverse thm_sem_unconstrainT[OF ok g])
qed

end

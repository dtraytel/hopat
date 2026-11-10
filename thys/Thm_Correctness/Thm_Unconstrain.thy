section \<open>Soundness of \<open>unconstrainT\<close>\<close>

theory Thm_Unconstrain
  imports Thm_Strip_Shyps "Pure_Thm.Pure_Unconstrain"
begin

text \<open>
  \<open>Thm.unconstrainT\<close> (theory \<^theory_text>\<open>Pure_Unconstrain\<close>) keeps theorems valid: in every model,
  the new proposition holds for all values of the unconstrained type variables, since the
  premises \<open>OFCLASS\<close> make them values of the sorts of the old type variables, and of the sort
  hypotheses, which are then inhabited. The proofs of the result are proof boxes; their validity
  is not covered here (the proof judgment treats proof boxes as atoms that the signature
  admits).
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

end

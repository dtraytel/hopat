section \<open>Stripping Sort Hypotheses of Theorems\<close>

theory Thm_Strip_Shyps
  imports Thm_Cterm
begin

text \<open>
  \<open>Thm.strip_shyps\<close> on theorems: the sort hypotheses of \<^const>\<open>strip_shyps_rep\<close> replace those of
  the theorem, and the proofs are those of \<^const>\<open>strip_shyps_proof\<close> and
  \<^const>\<open>zstrip_shyps_proof\<close>. The new sort hypotheses imply the old ones in every model
  (\<open>strip_shyps_sinh\<close>). In the proofs, the type variables that do not occur in the theorem are
  replaced by types of their sorts; such a replacement is a generalization of the free type
  variables among them, followed by an instantiation of type variables.
\<close>

subsection \<open>Replacing the hidden atomic types of classic proofs\<close>

context prf_sig
begin

lemma has_sort_TFree_self: "has_sort alg (TFree a S) S"
  by (rule has_sort_TFree_iff[THEN iffD2]) (rule sort_le_refl)

lemma prf_typs_terms_finite_idx:
  "finite (snd ` fst ` ((\<Union>U\<in>prf_typs q. tvars U) \<union> (\<Union>t\<in>prf_terms q. ttvars t)))"
  by (intro finite_imageI finite_UnI finite_UN_I) (simp_all add: ttvars_def)

text \<open>
  A map of the atomic types that keeps those of the hypotheses, flex-flex pairs and proposition
  (the set \<open>PR\<close>) and replaces the others by types of their sorts (given by \<open>\<psi>\<close>, if any) keeps
  classic proofs valid:
\<close>

theorem prf_valid_strip_atyps:
  assumes p: "prf_valid ax (set hs) tps q P" and wt: "wt_thm m hs tps P"
    and na: "\<And>X a S. X \<in> prf_atoms q \<Longrightarrow> TFree a S \<notin> tatoms (close X)"
    and np: "prf_nolb 0 q"
    and PR: "\<And>X. X \<in> insert P (set hs \<union> fst ` set tps \<union> snd ` set tps) \<Longrightarrow> tatoms X \<subseteq> PR"
    and \<psi>: "\<And>S T'. \<psi> S = Some T' \<Longrightarrow> has_sort alg T' S \<and> cert_typ alg ar T'"
    and \<phi>: "\<And>T. \<phi> T = (if T \<in> PR then T else case \<psi> (atyp_sort T) of Some T' \<Rightarrow> T' | None \<Rightarrow> T)"
  shows "prf_valid ax (set hs) tps (map_proof_terms (tmap \<phi>) (map_atyps \<phi>) q) P"
proof -
  define I where "I = snd ` fst ` ((\<Union>U\<in>prf_typs q. tvars U) \<union> (\<Union>t\<in>prf_terms q. ttvars t))"
  have fI: "finite I" unfolding I_def by (rule prf_typs_terms_finite_idx)
  define N where "N = Max (insert m I) + 1"
  have Mx: "x \<le> Max (insert m I)" if "x \<in> insert m I" for x using fI that by (intro Max_ge) simp_all
  have mN: "m < N" using Mx[of m] by (simp add: N_def)
  have IN: "i < N" if "i \<in> I" for i using Mx[of i] that by (simp add: N_def)
  define Ah where "Ah = {(a, S). TFree a S \<notin> PR}"
  define g where "g = (\<lambda>(a :: name) (S :: psort). (a, N))"
  define \<rho>0 where "\<rho>0 = (\<lambda>v S. if snd v = N then (case \<psi> S of Some T' \<Rightarrow> T' | None \<Rightarrow> TFree (fst v) S)
    else \<phi> (TVar v S))"
  let ?X = "insert P (set hs \<union> fst ` set tps \<union> snd ` set tps)"
  have wP: "wtp P" and hw: "\<And>h. h \<in> set hs \<Longrightarrow> wtp h \<and> vars h = {} \<and> ttvars h = {}"
    and ibP: "ibelow m P" and ibT: "\<And>t u. (t, u) \<in> set tps \<Longrightarrow> ibelow m t \<and> ibelow m u"
    using wt unfolding wt_thm_def by fast+
  \<comment> \<open>the type variables of the theorem are below \<open>N\<close>\<close>
  have tvX: "snd v < N" if X: "X \<in> ?X" and B: "TVar v S \<in> tatoms X" for X v S
  proof -
    from B obtain U where U: "U \<in> typs X" "TVar v S \<in> set (atyps U)" by (auto simp: tatoms_def)
    then have vt: "(v, S) \<in> ttvars X" using Varify_Correct.tvars_atyps[of v S U] by (auto simp: ttvars_def)
    have "ibelow m X \<or> ttvars X = {}"
      using X ibP ibT hw by auto
    then have "snd v \<le> m" using vt by (auto simp: ibelow_def)
    with mN show ?thesis by simp
  qed
  have \<phi>PR: "\<phi> B = B" if "B \<in> PR" for B using that \<phi>[of B] by simp
  \<comment> \<open>the instantiation\<close>
  have \<rho>0v: "has_sort alg (\<rho>0 v S) S \<and> (sort_ok alg S \<longrightarrow> cert_typ alg ar (\<rho>0 v S))" for v S
    using \<psi>[of S] has_sort_TFree_self[of "fst v" S] has_sort_TVar_refl[of v S]
    by (cases "snd v = N"; cases "\<psi> S"; cases "TVar v S \<in> PR") (auto simp: \<rho>0_def \<phi> cert_typ_def simp del: has_sort.simps)
  have \<rho>0: "cinst \<rho>0" unfolding cinst_def wsinst_def cert_inst_def using \<rho>0v by blast
  \<comment> \<open>generalization of the free type variables that do not occur in the theorem\<close>
  have nX: "tmap (gen_atom Ah g) X = X" if "X \<in> ?X" for X
    by (rule tmap_id_atoms) (use PR[OF that] in \<open>auto simp: gen_atom_def Ah_def split: ptyp.splits\<close>)
  have v1: "prf_valid ax (set hs) (map (\<lambda>(t, u). (tmap (gen_atom Ah g) t, tmap (gen_atom Ah g) u)) tps)
      (map_proof_terms (tmap (gen_atom Ah g)) (map_atyps (gen_atom Ah g)) q) (tmap (gen_atom Ah g) P)"
  proof (rule prf_valid_gen_tfrees[OF p wP])
    show "closed h \<and> vars h = {} \<and> ttvars h = {} \<and> \<not> tf_in Ah h" if "h \<in> set hs" for h
      using hw[OF that] wtpD(1) PR[of h] that by (auto simp: tf_in_def Ah_def)
    show "\<not> tf_in Ah (close X)" if "X \<in> prf_atoms q" for X
      using na[OF that] by (auto simp: tf_in_def)
  qed (simp_all add: np)
  have tps1: "map (\<lambda>(t, u). (tmap (gen_atom Ah g) t, tmap (gen_atom Ah g) u)) tps = tps"
  proof (rule map_idI)
    fix x assume x: "x \<in> set tps"
    obtain t u where xt: "x = (t, u)" by (cases x)
    have "t \<in> ?X" "u \<in> ?X" using x xt by force+
    then show "(\<lambda>(t, u). (tmap (gen_atom Ah g) t, tmap (gen_atom Ah g) u)) x = x"
      using nX by (simp add: xt)
  qed
  have P1: "tmap (gen_atom Ah g) P = P" by (rule nX) simp
  have v2: "prf_valid ax (set hs) (map (\<lambda>(t, u). (inst \<rho>0 t, inst \<rho>0 u)) tps)
      (map_proof_terms (inst \<rho>0) (tsubst \<rho>0) (map_proof_terms (tmap (gen_atom Ah g)) (map_atyps (gen_atom Ah g)) q))
      (inst \<rho>0 P)"
    using prf_valid_tinst[OF v1 \<rho>0] unfolding tps1 P1 .
  \<comment> \<open>the instantiation keeps the theorem\<close>
  have iX: "inst \<rho>0 X = X" if X: "X \<in> ?X" for X
  proof -
    have "tsubst \<rho>0 U = U" if U: "U \<in> typs X" for U
      unfolding tsubst_as_map_atyps
    proof (rule map_atyps_id)
      fix B assume B: "B \<in> set (atyps U)"
      have BX: "B \<in> tatoms X" using U B by (auto simp: tatoms_def)
      show "(case B of TVar v S \<Rightarrow> \<rho>0 v S | _ \<Rightarrow> B) = B"
      proof (cases B)
        case (TVar v S)
        have "snd v \<noteq> N" using tvX[OF X BX[unfolded TVar]] by simp
        moreover have "TVar v S \<in> PR" using PR[OF X] BX TVar by blast
        ultimately show ?thesis by (simp add: TVar \<rho>0_def \<phi>PR)
      qed simp_all
    qed
    then show ?thesis unfolding inst_as_map_types by (intro map_types_id) auto
  qed
  have tps2: "map (\<lambda>(t, u). (inst \<rho>0 t, inst \<rho>0 u)) tps = tps"
  proof (rule map_idI)
    fix x assume x: "x \<in> set tps"
    obtain t u where xt: "x = (t, u)" by (cases x)
    have "t \<in> ?X" "u \<in> ?X" using x xt by force+
    then show "(\<lambda>(t, u). (inst \<rho>0 t, inst \<rho>0 u)) x = x"
      using iX by (simp add: xt)
  qed
  have P2: "inst \<rho>0 P = P" by (rule iX) simp
  \<comment> \<open>the composition is the map\<close>
  have atom: "tsubst \<rho>0 (gen_atom Ah g B) = \<phi> B" if B: "B \<in> set (atyps U)" and fresh: "\<And>v S. (v, S) \<in> tvars U \<Longrightarrow> snd v < N"
    for B U
  proof -
    from atyps_atom[OF B] show ?thesis
    proof (elim disjE exE)
      fix a S assume Bf: "B = TFree a S"
      show ?thesis
      proof (cases "TFree a S \<in> PR")
        case True
        then show ?thesis by (simp add: Bf gen_atom_def Ah_def \<phi>PR)
      next
        case False
        then show ?thesis using \<phi>[of "TFree a S"]
          by (simp add: Bf gen_atom_def Ah_def g_def \<rho>0_def split: option.splits)
      qed
    next
      fix v S assume Bv: "B = TVar v S"
      have "(v, S) \<in> tvars U" using B Bv Varify_Correct.tvars_atyps by blast
      then have "snd v \<noteq> N" using fresh by fastforce
      then show ?thesis by (simp add: Bv gen_atom_def \<rho>0_def)
    qed
  qed
  have tyeq: "tsubst \<rho>0 (map_atyps (gen_atom Ah g) U) = map_atyps \<phi> U"
    if fresh: "\<And>v S. (v, S) \<in> tvars U \<Longrightarrow> snd v < N" for U
  proof -
    have "tsubst \<rho>0 (map_atyps (gen_atom Ah g) U) =
        map_atyps (\<lambda>B. map_atyps (\<lambda>A. case A of TVar v S \<Rightarrow> \<rho>0 v S | _ \<Rightarrow> A) (gen_atom Ah g B)) U"
      unfolding tsubst_as_map_atyps map_atyps_comp ..
    also have "\<dots> = map_atyps \<phi> U"
    proof (rule map_atyps_cong)
      fix B assume B: "B \<in> set (atyps U)"
      have "map_atyps (\<lambda>A. case A of TVar v S \<Rightarrow> \<rho>0 v S | _ \<Rightarrow> A) (gen_atom Ah g B) = tsubst \<rho>0 (gen_atom Ah g B)"
        unfolding tsubst_as_map_atyps ..
      also have "\<dots> = \<phi> B" by (rule atom[OF B fresh])
      finally show "map_atyps (\<lambda>A. case A of TVar v S \<Rightarrow> \<rho>0 v S | _ \<Rightarrow> A) (gen_atom Ah g B) = \<phi> B" .
    qed
    finally show ?thesis .
  qed
  have m: "map_proof_terms (inst \<rho>0) (tsubst \<rho>0) (map_proof_terms (tmap (gen_atom Ah g)) (map_atyps (gen_atom Ah g)) q) =
      map_proof_terms (tmap \<phi>) (map_atyps \<phi>) q"
    unfolding map_proof_terms_comp
  proof (rule map_proof_terms_cong2)
    fix t assume t: "t \<in> prf_terms q"
    have "map_types (tsubst \<rho>0 \<circ> map_atyps (gen_atom Ah g)) t = map_types (map_atyps \<phi>) t"
    proof (rule map_types_cong)
      fix U assume U: "U \<in> typs t"
      have "snd v < N" if "(v, S) \<in> tvars U" for v S
        using IN[of "snd v"] that t U by (force simp: I_def ttvars_def)
      then show "(tsubst \<rho>0 \<circ> map_atyps (gen_atom Ah g)) U = map_atyps \<phi> U" by (simp add: tyeq)
    qed
    then show "(inst \<rho>0 \<circ> tmap (gen_atom Ah g)) t = tmap \<phi> t"
      by (simp add: inst_as_map_types map_types_comp)
  next
    fix U assume U: "U \<in> prf_typs q"
    have "snd v < N" if "(v, S) \<in> tvars U" for v S
      using IN[of "snd v"] that U by (force simp: I_def)
    then show "(tsubst \<rho>0 \<circ> map_atyps (gen_atom Ah g)) U = map_atyps \<phi> U" by (simp add: tyeq)
  qed
  show ?thesis using v2 unfolding tps2 P2 m .
qed

end

subsection \<open>The replacement types of \<open>Thm.strip_shyps\<close>\<close>

lemma mem_typ_iff [simp]: "mem_typ T Ts \<longleftrightarrow> T \<in> set Ts"
  by (induction Ts) auto

lemma set_thm_atyps:
  "set (thm_atyps hyps tpairs prop) = (\<Union>X\<in>insert prop (set hyps \<union> fst ` set tpairs \<union> snd ` set tpairs). tatoms X)"
proof -
  have f: "set (fold (\<lambda>T acc. if T \<in> set acc then acc else T # acc) xs acc) = set acc \<union> set xs" for xs acc :: "ptyp list"
    using set_fold_insert_distinct[of xs acc] by simp
  show ?thesis
    by (auto simp: thm_atyps_def f tatoms_def term_typs_typs) blast+
qed

lemma set_ord_remove_sub: "set (ord_remove ord x xs) \<subseteq> set xs"
  by (induction xs) (auto split: order.splits)

lemma set_fold_ord_remove_sub: "set (fold (ord_remove ord \<circ> f) ys xs) \<subseteq> set xs"
proof (induction ys arbitrary: xs)
  case (Cons y ys)
  then show ?case using Cons.IH[of "ord_remove ord (f y) xs"] set_ord_remove_sub[of ord "f y" xs] by auto
qed simp

text \<open>The candidate replacements of \<^const>\<open>strip_atyp\<close>:\<close>

definition strip_cands :: "strip_data \<Rightarrow> (ptyp \<times> psort) list" where
  "strip_cands d = sd_present d @ sd_witnessed d @ map (\<lambda>S. (dummy_tfree S, S)) (sd_extra d)"

definition strip_repl :: "algebra \<Rightarrow> strip_data \<Rightarrow> psort \<Rightarrow> ptyp option" where
  "strip_repl alg d S = map_option fst (List.find (\<lambda>(T', S'). sort_le alg S' S) (strip_cands d))"

lemma strip_atyp_repl:
  "strip_atyp alg d T = (if T \<in> fst ` set (sd_present d) then Some T else strip_repl alg d (atyp_sort T))"
  by (simp add: strip_atyp_def strip_repl_def strip_cands_def)

lemma strip_shyps_data_present: "sd_present (strip_shyps_data alg gts shyps Ts) = map (\<lambda>T. (T, atyp_sort T)) Ts"
  by (simp add: strip_shyps_data_def present_sorts_def Let_def split: prod.splits)

context prf_sig
begin

definition cand_ok :: "ptyp \<times> psort \<Rightarrow> bool" where
  "cand_ok w \<longleftrightarrow> has_sort alg (fst w) (snd w) \<and> cert_typ alg ar (fst w) \<and> tnn (fst w)"

lemma mg_dom_Nil: "mg_dom alg t [] = None"
  by (simp add: mg_dom_def mg_domain_def raise_def)

lemma witness_sorts_cand_ok:
  assumes w: "witness_sorts alg gts hyps sorts = (witnessed, nw)" and hyps: "\<forall>w\<in>set hyps. cand_ok w"
  shows "\<forall>w\<in>set witnessed. cand_ok w"
proof -
  obtain rs st where rs: "witn_sorts alg gts hyps [] sorts ([], []) = (rs, st)" by (metis prod.exhaust)
  have "list_all2 (wres cand_ok) rs sorts \<and> (\<forall>w\<in>set (fst st). cand_ok w)"
  proof (rule witn_inv(2)[where Q = cand_ok, OF _ _ _ rs HOL.refl hyps])
    show "cand_ok (propT, [])"
      by (simp add: cand_ok_def cert_typ_def propT_def tarity_def ar_prop tnn_def)
  next
    fix T S1 S2 assume "cand_ok (T, S1)" "sort_le alg S1 S2"
    then show "cand_ok (T, S2)" by (auto simp: cand_ok_def intro: has_sort_mono)
  next
    fix t S SS Ts assume m: "mg_dom alg t S = Some SS" and l: "list_all2 (\<lambda>T D. cand_ok (T, D)) Ts SS"
    have hs: "list_all2 (\<lambda>T D. has_sort alg T D) Ts SS"
      using l by (rule list_all2_mono) (simp add: cand_ok_def)
    have S: "S \<noteq> []" using m mg_dom_Nil by auto
    then obtain c where c: "c \<in> set S" by (cases S) auto
    from mg_dom_sem[OF m c] obtain Ss where Ss: "map_of (arities alg t) c = Some Ss" "length Ss = length SS"
      by blast
    have len: "length Ts = tarity ar t"
      using arity_length[OF Ss(1)] Ss(2) list_all2_lengthD[OF l] by simp
    have "\<forall>T\<in>set Ts. cert_typ alg ar T \<and> tnn T"
    proof
      fix T assume "T \<in> set Ts"
      then obtain i where "i < length Ts" "Ts ! i = T" by (auto simp: in_set_conv_nth)
      with l show "cert_typ alg ar T \<and> tnn T" by (auto simp: list_all2_conv_all_nth cand_ok_def)
    qed
    then show "cand_ok (Type t Ts, S)"
      using mg_dom_has_sort[OF m hs] len by (auto simp: cand_ok_def cert_typ_def tnn_def)
  qed simp_all
  then have l: "list_all2 (wres cand_ok) rs sorts" ..
  have wi: "witnessed = List.map_filter (\<lambda>x. x) rs"
    using w rs by (auto simp: witness_sorts_def Let_def)
  show ?thesis
  proof
    fix w assume "w \<in> set witnessed"
    then have "Some w \<in> set rs" by (auto simp: wi set_map_filter_gen)
    then obtain i where "i < length rs" "rs ! i = Some w" by (auto simp: in_set_conv_nth)
    with l show "cand_ok w" by (cases w) (auto simp: list_all2_conv_all_nth wres_def)
  qed
qed

lemma strip_cands_ok:
  assumes Ts: "\<And>T. T \<in> set Ts \<Longrightarrow> ((\<exists>a S. T = TFree a S) \<or> (\<exists>v S. T = TVar v S)) \<and> cert_typ alg ar T \<and> tnn T"
    and sh: "\<And>S. S \<in> set shyps \<Longrightarrow> sort_ok alg S"
  shows "\<forall>w\<in>set (strip_cands (strip_shyps_data alg gts shyps Ts)). cand_ok w"
proof -
  define present where "present = map (\<lambda>T. (T, atyp_sort T)) Ts"
  define extra where "extra = fold (ord_remove sort_ord \<circ> snd) present shyps"
  obtain witnessed nw0 where w: "witness_sorts alg gts present extra = (witnessed, nw0)" by fastforce
  define nw where "nw = map (\<lambda>S. (minimize_sort alg S, S)) nw0"
  define extra' where "extra' = ord_make sort_ord (List.map_filter (\<lambda>(S, _). if \<exists>(S', _)\<in>set nw.
    sort_le alg S' S \<and> \<not> sort_le alg S S' then None else Some S) nw)"
  have d: "strip_cands (strip_shyps_data alg gts shyps Ts) =
      present @ witnessed @ map (\<lambda>S. (dummy_tfree S, S)) extra'"
    by (simp add: strip_cands_def strip_shyps_data_def present_sorts_def Let_def w nw_def extra'_def
      flip: present_def extra_def)
  have pr: "\<forall>w\<in>set present. cand_ok w"
  proof
    fix w assume "w \<in> set present"
    then obtain T where T: "T \<in> set Ts" "w = (T, atyp_sort T)" by (auto simp: present_def)
    from Ts[OF T(1)] show "cand_ok w"
      by (auto simp: T(2) cand_ok_def has_sort_TFree_self simp del: has_sort.simps)
  qed
  have wi: "\<forall>w\<in>set witnessed. cand_ok w" by (rule witness_sorts_cand_ok[OF w pr])
  have nw0: "set nw0 \<subseteq> set extra"
    using w set_fold_ord_remove_sub[of sort_ord snd witnessed extra] by (auto simp: witness_sorts_def Let_def)
  have ex: "set extra \<subseteq> set shyps"
    using set_fold_ord_remove_sub[of sort_ord snd present shyps] by (simp add: extra_def)
  have "sort_ok alg S" if "S \<in> set extra'" for S
  proof -
    from that obtain S0 where "S0 \<in> set nw0" "S = minimize_sort alg S0"
      by (auto simp: extra'_def set_ord_make sort_ord_EQUAL set_map_filter_gen nw_def split: if_splits)
    moreover have "set (minimize_sort alg S0) \<subseteq> set S0" by (auto simp: set_minimize_sort)
    ultimately show ?thesis using sh nw0 ex by (auto simp: sort_ok_def)
  qed
  then have "\<forall>w\<in>set (map (\<lambda>S. (dummy_tfree S, S)) extra'). cand_ok w"
    by (auto simp: cand_ok_def dummy_tfree_def cert_typ_def has_sort_TFree_self tnn_def simp del: has_sort.simps)
  with pr wi show ?thesis unfolding d by auto
qed

end

subsection \<open>The hypotheses of proofs\<close>

fun prf_hyps :: "prf \<Rightarrow> pterm set" where
  "prf_hyps (Hyp t) = {t}"
| "prf_hyps (Abst a T p) = prf_hyps p"
| "prf_hyps (AbsP a t p) = prf_hyps p"
| "prf_hyps (PAppt p t) = prf_hyps p"
| "prf_hyps (PAppp p q) = prf_hyps p \<union> prf_hyps q"
| "prf_hyps _ = {}"

lemma prf_hyps_pcerase [simp]: "prf_hyps (pcerase p) = prf_hyps p"
  by (induction p) simp_all

lemma prf_hyps_map_proof_terms [simp]: "prf_hyps (map_proof_terms f g p) = prf_hyps p"
proof (induction p)
  case (PThm x)
  then show ?case by (cases x) simp
qed simp_all

context prf_sig
begin

lemma zhyps_prf_hyps: "zdec ` zhyps p \<subseteq> prf_hyps (zprf_tr p)"
  by (induction p) auto

lemma prf_ok_hyps: "prf_ok ax H E e Hs p \<phi> \<Longrightarrow> prf_hyps p \<subseteq> H"
  by (induction rule: prf_ok.induct) auto

lemma cinst_TVar: "cinst (\<lambda>v S. TVar v S)"
  by (simp add: cinst_def wsinst_def cert_inst_def cert_typ_def del: has_sort.simps)

lemma gsubst_Var: "gsubst (\<lambda>x T. Var x T)"
  by (auto simp: gsubst_def wt_subst_def closed_subst_def closed_def)

text \<open>The hypotheses of valid proofs are among the given ones:\<close>

lemma prf_valid_hyps:
  assumes "prf_valid ax H tps w \<phi>"
  shows "prf_hyps w \<subseteq> H"
proof -
  have "prf_ok ax H (pmap (ap (\<lambda>v S. TVar v S) (\<lambda>x T. Var x T)) (set tps)) (\<lambda>_. propT) []
      (prf_ap (\<lambda>v S. TVar v S) (\<lambda>x T. Var x T) w) (ap (\<lambda>v S. TVar v S) (\<lambda>x T. Var x T) \<phi>)"
    by (rule prf_validD[OF assms cinst_TVar gsubst_Var])
  from prf_ok_hyps[OF this] show ?thesis by (simp add: prf_ap_def)
qed

lemma zvalid_hyps:
  assumes "zvalid ax H tps p \<phi>"
  shows "zdec ` zhyps p \<subseteq> H"
proof -
  obtain w where w: "pcerase w = pcerase (zprf_tr p)" "prf_valid ax H tps w \<phi>" using assms by (rule zvalidE)
  have "prf_hyps (zprf_tr p) = prf_hyps w" using arg_cong[OF w(1), of prf_hyps] by simp
  with zhyps_prf_hyps[of p] prf_valid_hyps[OF w(2)] show ?thesis by auto
qed

end


subsection \<open>Stripping tight proofs\<close>

lemma typ_of_ztvar_atyps: "(v, S) \<in> set (ztyp_tvars Z) \<Longrightarrow> typ_of (ZTVar v S) \<in> set (atyps (typ_of Z))"
  by (induction Z) (fastforce simp: propT_def)+

lemma ztyp_of_typ_of_ZTVar [simp]: "ztyp_of (typ_of (ZTVar v S)) = ZTVar v S"
  by (cases v) auto

lemma zsubst_type_id:
  "(\<And>v S. (v, S) \<in> set (ztyp_tvars Z) \<Longrightarrow> f (v, S) = None \<or> f (v, S) = Some (ZTVar v S)) \<Longrightarrow> zsubst_type f Z = Z"
proof (induction Z)
  case (ZTVar v S)
  then show ?case by (auto split: option.splits)
next
  case (ZType a Ts)
  have "zsubst_type f x = x" if x: "x \<in> set Ts" for x
    by (rule ZType.IH[OF x]) (use ZType.prems x in force)
  then show ?case by (simp add: map_idI)
qed simp_all

lemma zsubst_term_id: "(\<And>Z. Z \<in> set (zterm_types t) \<Longrightarrow> ty Z = Z) \<Longrightarrow> zsubst_term ty (\<lambda>_. None) t = t"
  by (induction t) (auto intro!: map_idI)

lemma zstrip_term_eq:
  "zstrip_term alg d t = return t' \<Longrightarrow> t' = zsubst_term (zstrip_type alg d) (\<lambda>_. None) t"
  by (auto simp: zstrip_term_def zstrip_check_def bindZ_eq_returnZ split: if_splits)

lemma zstrip_term_ok:
  "list_all (zstrip_ok alg d) (zterm_types t) \<Longrightarrow>
    zstrip_term alg d t = return (zsubst_term (zstrip_type alg d) (\<lambda>_. None) t)"
  by (simp add: zstrip_term_def zstrip_check_def bindZ_eq_returnZ)

lemma zstrip_term_present:
  assumes "\<And>Z v S. Z \<in> set (zterm_types t) \<Longrightarrow> (v, S) \<in> set (ztyp_tvars Z) \<Longrightarrow>
    strip_atyp alg d (typ_of (ZTVar v S)) = Some (typ_of (ZTVar v S))"
  shows "zstrip_term alg d t = return t"
proof -
  have ok: "list_all (zstrip_ok alg d) (zterm_types t)"
    using assms by (fastforce simp: zstrip_ok_def list_all_iff)
  have "zstrip_type alg d Z = Z" if "Z \<in> set (zterm_types t)" for Z
    unfolding zstrip_type_def by (rule zsubst_type_id) (use assms[OF that] in auto)
  then have "zsubst_term (zstrip_type alg d) (\<lambda>_. None) t = t" by (rule zsubst_term_id)
  with zstrip_term_ok[OF ok] show ?thesis by simp
qed

lemma mapM_cong_Z: "(\<And>x. x \<in> set xs \<Longrightarrow> f x = g x) \<Longrightarrow> (mapM f xs :: 'a list Z) = mapM g xs"
  by (induction xs) simp_all

lemma map_insts_cong:
  assumes "\<And>x T t. ((x, T), t) \<in> set (zv_dest (snd insts)) \<Longrightarrow> tm t = tm' t"
  shows "map_insts ty tm insts = map_insts ty tm' insts"
proof -
  obtain instT inst where i: "insts = (instT, inst)" by (cases insts)
  have "mapM (\<lambda>((x, T), t). do {t' \<leftarrow> tm t; return ((x, ty T), t')}) (zv_dest inst) =
      mapM (\<lambda>((x, T), t). do {t' \<leftarrow> tm' t; return ((x, ty T), t')}) (zv_dest inst)"
    by (rule mapM_cong_Z) (use assms in \<open>auto simp: i\<close>)
  then show ?thesis by (simp add: map_insts_def i)
qed

text \<open>
  A stripped tight proof whose hypotheses are kept agrees with the map of its types (which keeps
  hypotheses and class proofs) up to the types of its class proofs:
\<close>

context prf_sig
begin

lemma zstrip_proof_map:
  assumes "zstrip_proof alg d p = return p'" and "\<forall>h\<in>zhyps p. zstrip_term alg d h = return h"
    and tok: "\<And>T. ztyp_ok T \<Longrightarrow> ztyp_ok (zstrip_type alg d T)"
  shows "\<exists>q. map_zproof (zstrip_type alg d) (\<lambda>t. return (zsubst_term (zstrip_type alg d) (\<lambda>_. None) t)) p = return q \<and>
    pcerase (zprf_tr p') = pcerase (zprf_tr q) \<and> zhyps p' = zhyps q \<and> (zinv q \<longrightarrow> zinv p') \<and>
    (\<forall>k. znolb k q \<longrightarrow> znolb k p')"
  using assms(1,2)
proof (induction p arbitrary: p')
  case (ZConstp c)
  let ?tm = "\<lambda>t. return (zsubst_term (zstrip_type alg d) (\<lambda>_. None) t) :: zterm Z"
  obtain a insts where c: "c = (a, insts)" by (cases c)
  from ZConstp.prems(1) obtain insts' where ok: "zstrip_insts_ok alg d insts"
    and mi: "map_insts (zstrip_type alg d) (zstrip_term alg d) insts = return insts'" and p': "p' = ZConstp (a, insts')"
    by (auto simp: c zstrip_check_def bindZ_eq_returnZ split: if_splits)
  have "map_insts (zstrip_type alg d) ?tm insts = map_insts (zstrip_type alg d) (zstrip_term alg d) insts"
  proof (rule map_insts_cong)
    fix x T t assume "((x, T), t) \<in> set (zv_dest (snd insts))"
    with ok have "list_all (zstrip_ok alg d) (zterm_types t)"
      by (cases insts) (auto simp: zstrip_insts_ok_def list_all_iff)
    then show "?tm t = zstrip_term alg d t" by (rule zstrip_term_ok[symmetric])
  qed
  with mi have "map_zproof (zstrip_type alg d) ?tm (ZConstp c) = return p'"
    by (simp add: c p' bindZ_eq_returnZ)
  then show ?case by blast
next
  case (ZAbst a T p1)
  from ZAbst.prems(1) obtain p1' where r: "zstrip_proof alg d p1 = return p1'"
    and p': "p' = ZAbst a (zstrip_type alg d T) p1'"
    by (auto simp: zstrip_check_def bindZ_eq_returnZ split: if_splits)
  from ZAbst.IH[OF r] ZAbst.prems(2) obtain q1 where
    q1: "map_zproof (zstrip_type alg d) (\<lambda>t. return (zsubst_term (zstrip_type alg d) (\<lambda>_. None) t)) p1 = return q1"
      "pcerase (zprf_tr p1') = pcerase (zprf_tr q1)" "zhyps p1' = zhyps q1" "zinv q1 \<longrightarrow> zinv p1'"
      "\<forall>k. znolb k q1 \<longrightarrow> znolb k p1'"
    by auto
  show ?case by (rule exI[of _ "ZAbst a (zstrip_type alg d T) q1"]) (use q1 in \<open>simp add: p' bindZ_eq_returnZ\<close>)
next
  case (ZAbsp a t p1)
  from ZAbsp.prems(1) obtain t' p1' where t: "zstrip_term alg d t = return t'"
    and r: "zstrip_proof alg d p1 = return p1'" and p': "p' = ZAbsp a t' p1'"
    by (auto simp: bindZ_eq_returnZ)
  from ZAbsp.IH[OF r] ZAbsp.prems(2) obtain q1 where
    q1: "map_zproof (zstrip_type alg d) (\<lambda>t. return (zsubst_term (zstrip_type alg d) (\<lambda>_. None) t)) p1 = return q1"
      "pcerase (zprf_tr p1') = pcerase (zprf_tr q1)" "zhyps p1' = zhyps q1" "zinv q1 \<longrightarrow> zinv p1'"
      "\<forall>k. znolb k q1 \<longrightarrow> znolb k p1'"
    by auto
  show ?case by (rule exI[of _ "ZAbsp a t' q1"]) (use q1 zstrip_term_eq[OF t] in \<open>simp add: p' bindZ_eq_returnZ\<close>)
next
  case (ZAppt p1 t)
  from ZAppt.prems(1) obtain t' p1' where t: "zstrip_term alg d t = return t'"
    and r: "zstrip_proof alg d p1 = return p1'" and p': "p' = ZAppt p1' t'"
    by (auto simp: bindZ_eq_returnZ)
  from ZAppt.IH[OF r] ZAppt.prems(2) obtain q1 where
    q1: "map_zproof (zstrip_type alg d) (\<lambda>t. return (zsubst_term (zstrip_type alg d) (\<lambda>_. None) t)) p1 = return q1"
      "pcerase (zprf_tr p1') = pcerase (zprf_tr q1)" "zhyps p1' = zhyps q1" "zinv q1 \<longrightarrow> zinv p1'"
      "\<forall>k. znolb k q1 \<longrightarrow> znolb k p1'"
    by auto
  show ?case by (rule exI[of _ "ZAppt q1 t'"]) (use q1 zstrip_term_eq[OF t] in \<open>simp add: p' bindZ_eq_returnZ\<close>)
next
  case (ZAppp p1 p2)
  from ZAppp.prems(1) obtain p1' p2' where r1: "zstrip_proof alg d p1 = return p1'"
    and r2: "zstrip_proof alg d p2 = return p2'" and p': "p' = ZAppp p1' p2'"
    by (auto simp: bindZ_eq_returnZ)
  from ZAppp.IH(1)[OF r1] ZAppp.prems(2) obtain q1 where
    q1: "map_zproof (zstrip_type alg d) (\<lambda>t. return (zsubst_term (zstrip_type alg d) (\<lambda>_. None) t)) p1 = return q1"
      "pcerase (zprf_tr p1') = pcerase (zprf_tr q1)" "zhyps p1' = zhyps q1" "zinv q1 \<longrightarrow> zinv p1'"
      "\<forall>k. znolb k q1 \<longrightarrow> znolb k p1'"
    by auto
  from ZAppp.IH(2)[OF r2] ZAppp.prems(2) obtain q2 where
    q2: "map_zproof (zstrip_type alg d) (\<lambda>t. return (zsubst_term (zstrip_type alg d) (\<lambda>_. None) t)) p2 = return q2"
      "pcerase (zprf_tr p2') = pcerase (zprf_tr q2)" "zhyps p2' = zhyps q2" "zinv q2 \<longrightarrow> zinv p2'"
      "\<forall>k. znolb k q2 \<longrightarrow> znolb k p2'"
    by auto
  show ?case by (rule exI[of _ "ZAppp q1 q2"]) (use q1 q2 in \<open>simp add: p' bindZ_eq_returnZ\<close>)
next
  case (ZHyp h)
  from ZHyp.prems(1) obtain h' where h: "zstrip_term alg d h = return h'" and p': "p' = ZHyp h'"
    by (auto simp: bindZ_eq_returnZ)
  from ZHyp.prems(2) h have "h' = h" by simp
  then show ?case by (simp add: p')
next
  case (OFCLASSp T c)
  from OFCLASSp.prems(1) have p': "p' = OFCLASSp (zstrip_type alg d T) c"
    by (auto simp: zstrip_check_def bindZ_eq_returnZ split: if_splits)
  show ?case by (simp add: p' tok)
qed simp_all

lemma atyps_tsubst_rho: "(v, S) \<in> tvars D \<Longrightarrow> set (atyps (\<rho> v S)) \<subseteq> set (atyps (tsubst \<rho> D))"
  by (induction D) auto

lemma ztargs_atyps:
  assumes u: "ztargs c T = return Us" and U: "U \<in> set Us"
  shows "set (atyps U) \<subseteq> set (atyps T)"
proof (cases "c = STR ''Pure.imp''")
  case True
  with assms show ?thesis by (simp add: ztargs_def return_def)
next
  case ni: False
  show ?thesis
  proof (cases "c = STR ''Pure.all''")
    case True
    with ni assms show ?thesis
      by (auto simp: ztargs_def return_def raise_def split: ptyp.splits list.splits)
  next
    case na: False
    from u ni na obtain D where ex: "\<exists>\<rho>. T = tsubst \<rho> D" and Us: "Us = map (targ D T) (tparams D)"
      by (auto simp: ztargs_def return_def raise_def split: option.splits if_splits)
    from ex obtain \<rho> where T: "T = tsubst \<rho> D" by blast
    from U Us obtain p where p: "p \<in> tvars D" "U = targ D T p" by (auto simp: set_tparams)
    obtain v S where vS: "p = (v, S)" by (cases p)
    have "U = \<rho> v S" using targ_eq[OF T] p vS by simp
    then show ?thesis using atyps_tsubst_rho[of v S D \<rho>] p(1) vS T by simp
  qed
qed

lemma zterm_of_atyps:
  "zterm_of ztargs t = return z \<Longrightarrow> \<forall>U\<in>typs t. tnoneg U \<Longrightarrow> Z \<in> set (zterm_types z) \<Longrightarrow>
    set (atyps (typ_of Z)) \<subseteq> tatoms t"
proof (induction ztargs t arbitrary: z rule: zterm_of.induct)
  case (1 x T)
  then show ?case by (auto simp: return_def typ_of_ztyp_of_tnoneg)
next
  case (2 xi T)
  then show ?case by (auto simp: return_def typ_of_ztyp_of_tnoneg)
next
  case (4 c T)
  then obtain Us where u: "ztargs c T = return Us"
    and z: "z = (case Us of [] \<Rightarrow> ZConst0 c | [U] \<Rightarrow> ZConst1 c (ztyp_of U) | _ \<Rightarrow> ZConst c (map ztyp_of Us))"
    by (auto simp: Z_ok_simps return_def split: option.splits)
  from "4.prems"(3) obtain U where U: "U \<in> set Us" "Z = ztyp_of U"
    unfolding z by (cases Us rule: remdups_adj.cases) auto
  have "tnoneg T" using "4.prems"(2) by simp
  then have "tnoneg U" using ztargs_tvars[OF u U(1)] by (auto simp: tnoneg_def)
  then show ?case using ztargs_atyps[OF u U(1)] by (simp add: U(2) typ_of_ztyp_of_tnoneg)
next
  case (5 a T b)
  from "5.prems"(1) obtain b' where b: "zterm_of ztargs b = return b'" and z: "z = ZAbs a (ztyp_of T) b'"
    by (auto simp: Z_ok_simps return_def)
  from "5.prems"(3) have "Z = ztyp_of T \<or> Z \<in> set (zterm_types b')" by (simp add: z)
  then show ?case
  proof
    assume "Z = ztyp_of T"
    then show ?thesis using "5.prems"(2) by (simp add: typ_of_ztyp_of_tnoneg)
  next
    assume "Z \<in> set (zterm_types b')"
    with "5.hyps"[OF b] "5.prems"(2) show ?thesis by auto
  qed
next
  case (6 t u)
  show ?case
  proof (cases "match_of_class (t $ u)")
    case (Some Tc)
    show ?thesis
    proof (cases "t $ u = mk_of_class (fst Tc) (snd Tc)")
      case True
      have "(return (ZOfclass (ztyp_of (fst Tc)) (snd Tc)) :: zterm Z) = return z"
        using "6.prems"(1) unfolding zterm_of.simps(6) Some option.case if_P[OF True] .
      then have z: "z = ZOfclass (ztyp_of (fst Tc)) (snd Tc)" by simp
      have it: "Type STR ''itself'' [fst Tc] \<in> typs (t $ u)" using True by (simp add: mk_of_class_def)
      then have "tnoneg (fst Tc)" using "6.prems"(2) by (auto simp: tnoneg_def)
      moreover have "set (atyps (fst Tc)) \<subseteq> tatoms (t $ u)" using it by (force simp: tatoms_def)
      ultimately show ?thesis using "6.prems"(3) by (simp add: z typ_of_ztyp_of_tnoneg)
    next
      case False
      with Some "6.prems"(1) obtain t' u' where tu: "zterm_of ztargs t = return t'" "zterm_of ztargs u = return u'"
        "z = ZApp t' u'"
        by (auto simp: Z_ok_simps return_def)
      with "6.hyps"(3)[OF Some False tu(1)] "6.hyps"(4)[OF Some False tu(1) tu(2)] "6.prems"(2,3)
      show ?thesis by auto
    qed
  next
    case None
    with "6.prems"(1) obtain t' u' where tu: "zterm_of ztargs t = return t'" "zterm_of ztargs u = return u'"
      "z = ZApp t' u'"
      by (auto simp: Z_ok_simps return_def)
    with "6.hyps"(1)[OF None tu(1)] "6.hyps"(2)[OF None tu(1) tu(2)] "6.prems"(2,3)
    show ?thesis by auto
  qed
qed (simp add: return_def)

lemma typ_of_zstrip_type:
  assumes "\<And>T'. T' \<in> ran (\<lambda>T. strip_atyp alg d T) \<Longrightarrow> tnoneg T'"
  shows "typ_of (zstrip_type alg d Z) = map_atyps (\<lambda>T. case strip_atyp alg d T of Some T' \<Rightarrow> T' | None \<Rightarrow> T) (typ_of Z)"
proof (induction Z)
  case (ZTVar v S)
  show ?case
  proof (cases "strip_atyp alg d (typ_of (ZTVar v S))")
    case (Some T')
    then have "tnoneg T'" using assms by (auto simp: ran_def)
    with Some show ?thesis by (cases v) (auto simp: zstrip_type_def typ_of_ztyp_of_tnoneg split: if_splits)
  next
    case None
    then show ?thesis by (cases v) (auto simp: zstrip_type_def split: if_splits)
  qed
qed (simp_all add: zstrip_type_def propT_def)

text \<open>
  The stripped tight proof of a valid tight proof is valid if its hypotheses are encodings of
  hypotheses of the theorem; they are kept, since their atomic types occur in the theorem.
\<close>

theorem zstrip_proof_valid:
  assumes p: "zvalid ax (set hs) tps pf P" and wt: "wt_thm m hs tps P"
    and na: "\<And>X a S. TFree a S \<notin> tatoms (close X)"
    and np: "znolb 0 pf" and zi: "zinv pf" and zh: "zhyps_ok pf"
    and PR: "\<And>X. X \<in> insert P (set hs \<union> fst ` set tps \<union> snd ` set tps) \<Longrightarrow> tatoms X \<subseteq> PR"
    and PRn: "\<And>T. T \<in> PR \<Longrightarrow> tnn T"
    and \<psi>: "\<And>S T'. \<psi> S = Some T' \<Longrightarrow> has_sort alg T' S \<and> cert_typ alg ar T' \<and> tnn T'"
    and sa: "\<And>T. strip_atyp alg d T = (if T \<in> PR then Some T else \<psi> (atyp_sort T))"
    and z: "zstrip_proof alg d pf = return z1"
  shows "zvalid ax (set hs) tps z1 P \<and> zinv z1 \<and> znolb 0 z1 \<and> zhyps z1 = zhyps pf"
proof -
  let ?\<phi> = "\<lambda>T. case strip_atyp alg d T of Some T' \<Rightarrow> T' | None \<Rightarrow> T"
  have \<phi>: "?\<phi> T = (if T \<in> PR then T else case \<psi> (atyp_sort T) of Some T' \<Rightarrow> T' | None \<Rightarrow> T)" for T
    by (simp add: sa)
  have tnnS: "tnn T'" if "strip_atyp alg d T = Some T'" for T T'
    using that sa[of T] PRn \<psi> by (auto split: if_splits)
  have ran: "tnoneg T'" if "T' \<in> ran (\<lambda>T. strip_atyp alg d T)" for T'
  proof -
    from that obtain T where "strip_atyp alg d T = Some T'" by (auto simp: ran_def)
    then show ?thesis using tnnS tnn_tnoneg by blast
  qed
  have tyof: "typ_of (zstrip_type alg d Z) = map_atyps ?\<phi> (typ_of Z)" for Z
    by (rule typ_of_zstrip_type[OF ran])
  define f where "f = (\<lambda>(v, S). map_option ztyp_of (strip_atyp alg d (typ_of (ZTVar v S))))"
  have zt: "zstrip_type alg d = zsubst_type f" unfolding zstrip_type_def f_def ..
  have fok: "ztyp_ok U" if "f (v, S) = Some U" for v S U
  proof -
    from that obtain T' where T': "strip_atyp alg d (typ_of (ZTVar v S)) = Some T'" "U = ztyp_of T'"
      by (auto simp: f_def)
    show ?thesis unfolding T'(2) by (rule ztyp_ok_ztyp_of[OF tnnS[OF T'(1)]])
  qed
  have tok: "ztyp_ok (zstrip_type alg d T)" if "ztyp_ok T" for T
    unfolding zt by (rule ztyp_ok_zsubst_type[OF that fok])
  \<comment> \<open>the hypotheses are kept\<close>
  have H: "zdec ` zhyps pf \<subseteq> set hs" by (rule zvalid_hyps[OF p])
  have hk: "\<forall>h\<in>zhyps pf. zstrip_term alg d h = return h"
  proof
    fix h assume h: "h \<in> zhyps pf"
    have hs: "zdec h \<in> set hs" using H h by blast
    have zo: "zterm_of ztargs (zdec h) = return h" using zh h by (simp add: zhyps_ok_def)
    from wt hs have "ttvars (zdec h) = {}" by (simp add: wt_thm_def)
    then have tn: "\<forall>U\<in>typs (zdec h). tnoneg U" by (auto simp: ttvars_def tnoneg_def)
    show "zstrip_term alg d h = return h"
    proof (rule zstrip_term_present)
      fix Z v S assume Z: "Z \<in> set (zterm_types h)" and vS: "(v, S) \<in> set (ztyp_tvars Z)"
      have "typ_of (ZTVar v S) \<in> tatoms (zdec h)"
        using zterm_of_atyps[OF zo tn Z] typ_of_ztvar_atyps[OF vS] by blast
      then have "typ_of (ZTVar v S) \<in> PR" using PR[of "zdec h"] hs by blast
      then show "strip_atyp alg d (typ_of (ZTVar v S)) = Some (typ_of (ZTVar v S))" by (simp add: sa)
    qed
  qed
  from zstrip_proof_map[OF z hk tok] obtain q where
    m: "map_zproof (zstrip_type alg d) (\<lambda>t. return (zsubst_term (zstrip_type alg d) (\<lambda>_. None) t)) pf = return q"
    and pq: "pcerase (zprf_tr z1) = pcerase (zprf_tr q)" and hq: "zhyps z1 = zhyps q"
    and iq: "zinv q \<longrightarrow> zinv z1" and nq: "\<forall>k. znolb k q \<longrightarrow> znolb k z1"
    by blast
  have zcs: "zconsts_ok pf" using zi by (simp add: zinv_def)
  have vq: "zvalid ax (set hs) tps q P"
  proof (rule zvalid_map_typ[OF p zcs m tyof])
    fix w assume w: "pcerase w = pcerase (zprf_tr pf)" "prf_valid ax (set hs) tps w P"
    have "prf_nolb 0 (zprf_tr pf)" by (rule prf_nolb_zprf_tr[OF np])
    then have "prf_nolb 0 (pcerase w)" by (simp add: w(1))
    then have npw: "prf_nolb 0 w" by simp
    show "prf_valid ax (set hs) tps (map_proof_terms (tmap ?\<phi>) (map_atyps ?\<phi>) w) P"
    proof (rule prf_valid_strip_atyps[where \<psi> = \<psi>, OF w(2) wt _ npw PR])
      show "TFree a S \<notin> tatoms (close X)" if "X \<in> prf_atoms w" for X a S by (rule na)
      show "has_sort alg T' S \<and> cert_typ alg ar T'" if "\<psi> S = Some T'" for S T' using \<psi>[OF that] by blast
      show "?\<phi> T = (if T \<in> PR then T else case \<psi> (atyp_sort T) of Some T' \<Rightarrow> T' | None \<Rightarrow> T)" for T
        by (rule \<phi>)
    qed
  qed
  have vz: "zvalid ax (set hs) tps z1 P"
  proof -
    obtain w where w: "pcerase w = pcerase (zprf_tr q)" "prf_valid ax (set hs) tps w P" using vq by (rule zvalidE)
    show ?thesis by (rule zvalidI[OF _ w(2)]) (simp add: w(1) pq)
  qed
  have iz: "zinv q" "znolb 0 q" "zhyps q = zhyps pf"
    using zinv_map_zsubst_type[OF m[unfolded zt] zi fok] np by simp_all
  with vz iq nq hq show ?thesis by simp
qed

end


subsection \<open>Theorems\<close>

text \<open>The ordered list of the sort hypotheses of a theorem (\<open>Thm.shyps_of\<close>):\<close>

definition shyps_list :: "psort set \<Rightarrow> psort list" where
  "shyps_list S = ord_make sort_ord (SOME xs. set xs = S)"

lemma set_shyps_list: "finite S \<Longrightarrow> set (shyps_list S) = S"
  using someI_ex[OF finite_list[of S]] by (simp add: shyps_list_def set_ord_make sort_ord_EQUAL)

context prf_sig
begin

lemma cert_atyps: "cert_typ alg ar U \<Longrightarrow> A \<in> set (atyps U) \<Longrightarrow> cert_typ alg ar A"
  by (induction U) (auto simp: cert_typ_def)

text \<open>The data of \<open>Thm.strip_shyps\<close> for a well-formed theorem:\<close>

lemma strip_data_ok:
  fixes gts :: "name list"
  assumes w: "thm_wf m hs tps P" and so: "\<forall>S\<in>set shyps. sort_ok alg S"
  defines "Ts \<equiv> thm_atyps hs tps P"
  defines "d \<equiv> strip_shyps_data alg gts shyps Ts"
  shows "\<And>X. X \<in> insert P (set hs \<union> fst ` set tps \<union> snd ` set tps) \<Longrightarrow> tatoms X \<subseteq> set Ts"
    and "\<And>T. T \<in> set Ts \<Longrightarrow> tnn T"
    and "\<And>S T'. strip_repl alg d S = Some T' \<Longrightarrow> has_sort alg T' S \<and> cert_typ alg ar T' \<and> tnn T'"
    and "\<And>T. strip_atyp alg d T = (if T \<in> set Ts then Some T else strip_repl alg d (atyp_sort T))"
proof -
  let ?X = "insert P (set hs \<union> fst ` set tps \<union> snd ` set tps)"
  have wt: "wt_thm m hs tps P" and tn: "\<forall>v\<in>tvars_thm tps P. 0 \<le> snd (fst v)"
    using w by (simp_all add: thm_wf_def)
  have sT: "set Ts = (\<Union>X\<in>?X. tatoms X)" by (simp add: Ts_def set_thm_atyps)
  show X: "tatoms X \<subseteq> set Ts" if "X \<in> ?X" for X using that sT by blast
  \<comment> \<open>the terms of the theorem are well-typed\<close>
  have ty: "\<exists>e T. e \<turnstile> X : T" if "X \<in> ?X" for X
  proof -
    from that consider "X = P" | "X \<in> set hs" | "\<exists>(t, u)\<in>set tps. X = t \<or> X = u" by force
    then show ?thesis
    proof cases
      case 1
      then show ?thesis using wtpD(2)[of P] wt by (auto simp: wt_thm_def)
    next
      case 2
      then show ?thesis using wtpD(2)[of X] wt by (auto simp: wt_thm_def)
    next
      case 3
      then obtain t u where tu: "(t, u) \<in> set tps" "X = t \<or> X = u" by blast
      from wt tu(1) obtain T where "\<And>e. e \<turnstile> t : T" "\<And>e. e \<turnstile> u : T" by (fastforce simp: wt_thm_def)
      with tu(2) show ?thesis by blast
    qed
  qed
  have tvX: "(v, S) \<in> tvars_thm tps P" if "X \<in> ?X" "(v, S) \<in> ttvars X" for X v S
  proof -
    from that(1) have "X = P \<or> X \<in> set hs \<or> (\<exists>(t, u)\<in>set tps. X = t \<or> X = u)" by force
    moreover have "ttvars X = {}" if "X \<in> set hs" using that wt by (simp add: wt_thm_def)
    ultimately show ?thesis using that(2) by (auto simp: tvars_thm_def)
  qed
  have Ts: "((\<exists>a S. T = TFree a S) \<or> (\<exists>v S. T = TVar v S)) \<and> cert_typ alg ar T \<and> tnn T" if T: "T \<in> set Ts" for T
  proof -
    from T sT obtain X U where X: "X \<in> ?X" and U: "U \<in> typs X" and TU: "T \<in> set (atyps U)"
      by (auto simp: tatoms_def)
    from ty[OF X] obtain e V where "e \<turnstile> X : V" by blast
    then have "cert_typ alg ar U" using typing_typs U by blast
    then have c: "cert_typ alg ar T" by (rule cert_atyps[OF _ TU])
    have "tnn T"
    proof -
      from atyps_atom[OF TU] show ?thesis
      proof (elim disjE exE)
        fix a S assume "T = TFree a S"
        then show ?thesis by (simp add: tnn_def)
      next
        fix v S assume TV: "T = TVar v S"
        then have "(v, S) \<in> ttvars X" using U TU Varify_Correct.tvars_atyps[of v S U] by (auto simp: ttvars_def)
        then have "0 \<le> snd v" using tn tvX[OF X] by fastforce
        then show ?thesis by (simp add: TV tnn_def)
      qed
    qed
    with c atyps_atom[OF TU] show ?thesis by blast
  qed
  show "tnn T" if "T \<in> set Ts" for T using Ts[OF that] by blast
  have pres: "sd_present d = map (\<lambda>T. (T, atyp_sort T)) Ts" by (simp add: d_def strip_shyps_data_present)
  have co: "\<forall>w\<in>set (strip_cands d). cand_ok w"
    unfolding d_def by (rule strip_cands_ok) (use Ts so in blast)+
  show "has_sort alg T' S \<and> cert_typ alg ar T' \<and> tnn T'" if r: "strip_repl alg d S = Some T'" for S T'
  proof -
    from r have "\<exists>w. List.find (\<lambda>(T', S'). sort_le alg S' S) (strip_cands d) = Some w \<and> T' = fst w"
      by (auto simp: strip_repl_def)
    then obtain w where w: "List.find (\<lambda>(T', S'). sort_le alg S' S) (strip_cands d) = Some w" "T' = fst w"
      by blast
    from w(1) have wm: "w \<in> set (strip_cands d)" and le: "sort_le alg (snd w) S"
      by (auto simp: find_Some_iff dest: nth_mem)
    from co wm have "cand_ok w" by blast
    with le show ?thesis by (auto simp: cand_ok_def w(2) intro: has_sort_mono)
  qed
  show "strip_atyp alg d T = (if T \<in> set Ts then Some T else strip_repl alg d (atyp_sort T))" for T
    by (simp add: strip_atyp_repl pres image_image)
qed

end

text \<open>
  \<open>Thm.strip_shyps\<close> on theorems, with the logical types \<open>gts\<close> of the signature; the sort
  hypotheses are finite and certified, and the closures of the atoms of proofs have no free type
  variables (\<^const>\<open>sign_closed\<close>), as in Isabelle.
\<close>

definition strip_shyps_thm :: "name list \<Rightarrow> 'u pure_thm \<Rightarrow> 'u pure_thm option" where
  "strip_shyps_thm gts th =
    (let c = sign_of th; d = strip_shyps_rep (sg_alg c) gts (shyps_list (shyps_of th)) (hyps_of th) (rep_of th)
     in if finite (shyps_of th) \<and> sign_closed c \<and> (\<forall>S\<in>shyps_of th. sort_ok (sg_alg c) S)
        then Some (Abs_thm (mk_thm (rep_of th) (case d of Some d \<Rightarrow> set (sd_shyps d) | None \<Rightarrow> shyps_of th)
          (hyps_of th) c (bindW (proof_of th) (strip_shyps_proof (sg_alg c) d))
          (bindM (zproof_of th) (zstrip_shyps_proof (sg_alg c) d))))
        else None)"

lemma strip_shyps_rep_Some:
  "strip_shyps_rep alg gts shyps hyps r = Some d \<Longrightarrow>
    d = strip_shyps_data alg gts shyps (thm_atyps hyps (th_tpairs r) (th_prop r))"
  by (simp add: strip_shyps_rep_def split: if_splits)

lemma strip_typ_tmap: "map_types (strip_typ alg d) = tmap (\<lambda>T. case strip_atyp alg d T of Some T' \<Rightarrow> T' | None \<Rightarrow> T)"
  by (simp add: strip_typ_def)

theorem thm_ok_strip_shyps:
  fixes th :: "'u pure_thm" and gts :: "name list"
  defines "d \<equiv> strip_shyps_rep (sg_alg (sign_of th)) gts (shyps_list (shyps_of th)) (hyps_of th) (rep_of th)"
  assumes fin: "finite (shyps_of th)" and sc: "sign_closed (sign_of th)"
    and so: "\<forall>S\<in>shyps_of th. sort_ok (sg_alg (sign_of th)) S"
  shows "thm_ok TYPE('u) (mk_thm (rep_of th) (case d of Some d \<Rightarrow> set (sd_shyps d) | None \<Rightarrow> shyps_of th)
    (hyps_of th) (sign_of th) (bindW (proof_of th) (strip_shyps_proof (sg_alg (sign_of th)) d))
    (bindM (zproof_of th) (zstrip_shyps_proof (sg_alg (sign_of th)) d)))"
    (is "thm_ok _ ?th")
proof (rule thm_okI)
  let ?c = "sign_of th"
  let ?Ts = "thm_atyps (hyps_of th) (th_tpairs (rep_of th)) (th_prop (rep_of th))"
  have sl: "set (shyps_list (shyps_of th)) = shyps_of th" by (rule set_shyps_list[OF fin])
  have dS: "d' = strip_shyps_data (sg_alg ?c) gts (shyps_list (shyps_of th)) ?Ts" if "d = Some d'" for d'
    using strip_shyps_rep_Some[OF that[unfolded d_def]] by simp
  show "pure_sig.thm_wf (sg_alg (th_sign ?th)) (sg_ar (th_sign ?th)) (sg_consts (th_sign ?th))
      (th_maxidx ?th) (th_hyps ?th) (th_tpairs ?th) (th_prop ?th)"
    if "pure_sig (sg_alg (th_sign ?th)) (sg_ar (th_sign ?th))"
    using pure_thm_wf[of th] that by simp
next
  let ?c = "sign_of th"
  let ?Ts = "thm_atyps (hyps_of th) (th_tpairs (rep_of th)) (th_prop (rep_of th))"
  fix M :: "'u model"
  assume ps: "pure_sig (sg_alg (th_sign ?th)) (sg_ar (th_sign ?th))" and M: "is_model (th_sign ?th) M"
  interpret pure_model "sg_alg ?c" "sg_ar ?c" "sg_consts ?c" "m_mem M" "m_fun M" "m_app M" "m_lam M"
    "m_bool M" "m_true M" "m_false M" "m_tcon M" "m_cls M" "m_cval M"
    by (rule is_modelD) (use M in simp)
  have sl: "set (shyps_list (shyps_of th)) = shyps_of th" by (rule set_shyps_list[OF fin])
  have v0: "valid (shyps_of th) (hyps_of th) (th_tpairs (rep_of th)) (th_prop (rep_of th))"
    using pure_thm_valid_in[of th M] M by simp
  have sh: "sinh S" if all: "\<forall>S\<in>(case d of Some d \<Rightarrow> set (sd_shyps d) | None \<Rightarrow> shyps_of th). sinh S"
    and S: "S \<in> shyps_of th" for S
  proof (cases d)
    case None
    with all S show ?thesis by simp
  next
    case (Some d')
    then have d': "d' = strip_shyps_data (sg_alg ?c) gts (shyps_list (shyps_of th)) ?Ts"
      using strip_shyps_rep_Some[OF Some[unfolded d_def]] by simp
    show ?thesis
    proof (rule strip_shyps_sinh)
      show "sinh S'" if "S' \<in> set (sd_shyps (strip_shyps_data (sg_alg ?c) gts (shyps_list (shyps_of th)) ?Ts))" for S'
        using all that by (simp add: Some d')
      show "S \<in> set (shyps_list (shyps_of th))" using S sl by simp
    qed
  qed
  have "valid (case d of Some d \<Rightarrow> set (sd_shyps d) | None \<Rightarrow> shyps_of th) (hyps_of th) (th_tpairs (rep_of th))
      (th_prop (rep_of th))"
    using v0 sh unfolding valid_def by blast
  then show "valid_in (th_sign ?th) M (th_shyps ?th) (th_hyps ?th) (th_tpairs ?th) (th_prop ?th)"
    by (simp add: valid_in_def)
next
  let ?c = "sign_of th"
  let ?Ts = "thm_atyps (hyps_of th) (th_tpairs (rep_of th)) (th_prop (rep_of th))"
  assume psig: "is_prf_sig (th_sign ?th)"
  then interpret prf_sig "sg_alg ?c" "sg_ar ?c" "sg_consts ?c" "sg_close ?c" "sg_tyargs ?c"
    by (simp add: is_prf_sig_def)
  have ps: "pure_sig (sg_alg ?c) (sg_ar ?c)" using psig by (simp add: is_prf_sig_def prf_sig_def)
  have w0: "thm_wf (th_maxidx (rep_of th)) (hyps_of th) (th_tpairs (rep_of th)) (th_prop (rep_of th))"
    using pure_thm_wf[of th] ps by simp
  have wt: "wt_thm (th_maxidx (rep_of th)) (hyps_of th) (th_tpairs (rep_of th)) (th_prop (rep_of th))"
    using w0 by (simp add: thm_wf_def)
  have na: "TFree a S \<notin> tatoms (sg_close ?c X)" for X a S using sc by (simp add: sign_closed_def)
  have sl: "set (shyps_list (shyps_of th)) = shyps_of th" by (rule set_shyps_list[OF fin])
  have so': "\<forall>S\<in>set (shyps_list (shyps_of th)). sort_ok (sg_alg ?c) S" using so sl by simp
  note sd = strip_data_ok[OF w0 so']
  have dS: "d' = strip_shyps_data (sg_alg ?c) gts (shyps_list (shyps_of th)) ?Ts" if "d = Some d'" for d'
    using strip_shyps_rep_Some[OF that[unfolded d_def]] by simp
  have p: "proofs_ok (rep_thm th)" by (rule pure_thm_proofs_ok) (use psig in simp)
  have hc: "\<forall>h\<in>set (hyps_of th). closed h" using wt wtpD(1) by (auto simp: wt_thm_def)
  show "proofs_ok ?th" unfolding proofs_ok_def Let_def mk_thm_sel
  proof (rule conjI; intro allI impI)
    fix pf assume "bindW (proof_of th) (strip_shyps_proof (sg_alg ?c) d) = returnW pf"
    then obtain q where q: "proof_of th = returnW q" and pf: "strip_shyps_proof (sg_alg ?c) d q = returnW pf"
      by (auto simp: bindP_eq_returnP)
    have vq: "prf_valid (sg_ax ?c) (set (hyps_of th)) (th_tpairs (rep_of th)) q (th_prop (rep_of th))"
      "prf_idx (\<lambda>i. 0 \<le> i) q" "prf_nolb 0 q"
      using p q by (simp_all add: proofs_ok_def Let_def)
    show "prf_valid (sg_ax ?c) (set (hyps_of th)) (th_tpairs (rep_of th)) pf (th_prop (rep_of th)) \<and>
        prf_idx (\<lambda>i. 0 \<le> i) pf \<and> prf_nolb 0 pf"
    proof (cases d)
      case None
      with pf vq show ?thesis by (simp add: strip_shyps_proof_def returnW_def)
    next
      case (Some d')
      note d' = dS[OF Some]
      let ?\<phi> = "\<lambda>T. case strip_atyp (sg_alg ?c) d' T of Some T' \<Rightarrow> T' | None \<Rightarrow> T"
      from pf Some have pf': "pf = map_proof_terms (tmap ?\<phi>) (map_atyps ?\<phi>) q"
        by (simp add: strip_shyps_proof_def strip_proof_def returnW_def raiseW_def strip_typ_tmap
          split: if_splits) (simp add: strip_typ_def)
      have "prf_valid (sg_ax ?c) (set (hyps_of th)) (th_tpairs (rep_of th)) pf (th_prop (rep_of th))"
        unfolding pf'
      proof (rule prf_valid_strip_atyps[where \<psi> = "strip_repl (sg_alg ?c) d'", OF vq(1) wt _ vq(3)])
        show "TFree a S \<notin> tatoms (sg_close ?c X)" if "X \<in> prf_atoms q" for X a S by (rule na)
        show "tatoms X \<subseteq> set ?Ts" if "X \<in> insert (th_prop (rep_of th)) (set (hyps_of th) \<union>
            fst ` set (th_tpairs (rep_of th)) \<union> snd ` set (th_tpairs (rep_of th)))" for X
          by (rule sd(1)[OF that])
        show "has_sort (sg_alg ?c) T' S \<and> cert_typ (sg_alg ?c) (sg_ar ?c) T'"
          if "strip_repl (sg_alg ?c) d' S = Some T'" for S T'
          using sd(3)[OF that[unfolded d']] by (simp add: d')
        show "?\<phi> T = (if T \<in> set ?Ts then T else case strip_repl (sg_alg ?c) d' (atyp_sort T) of
            Some T' \<Rightarrow> T' | None \<Rightarrow> T)" for T
          unfolding d' by (subst sd(4)) simp
      qed
      moreover have "prf_idx (\<lambda>i. 0 \<le> i) pf" "prf_nolb 0 pf"
        using prf_idx_map_types[OF vq(2)] prf_nolb_map_types[OF vq(3)] by (simp_all add: pf')
      ultimately show ?thesis by simp
    qed
  next
    fix z assume "bindM (zproof_of th) (zstrip_shyps_proof (sg_alg ?c) d) = return z"
    then obtain q z1 where q: "zproof_of th = return q"
      and z1: "(case d of Some d \<Rightarrow> zstrip_proof (sg_alg ?c) d q | None \<Rightarrow> return q) = return z1"
      and bn: "beta_norm_prooft z1 = Some z"
      by (auto simp: bindZ_eq_returnZ zstrip_shyps_proof_def liftOZ_eq_returnZ)
    have vq: "zvalid (sg_ax ?c) (set (hyps_of th)) (th_tpairs (rep_of th)) q (th_prop (rep_of th))" "zinv q"
      "znolb 0 q" "zhyps_ok q"
      using p q by (simp_all add: proofs_ok_def Let_def)
    have v1: "zvalid (sg_ax ?c) (set (hyps_of th)) (th_tpairs (rep_of th)) z1 (th_prop (rep_of th)) \<and> zinv z1 \<and>
        znolb 0 z1 \<and> zhyps z1 = zhyps q"
    proof (cases d)
      case None
      with z1 vq show ?thesis by simp
    next
      case (Some d')
      note d' = dS[OF Some]
      from z1 Some have zs: "zstrip_proof (sg_alg ?c) d' q = return z1" by simp
      show ?thesis
      proof (rule zstrip_proof_valid[where \<psi> = "strip_repl (sg_alg ?c) d'", OF vq(1) wt _ vq(3,2,4) _ _ _ _ zs])
        show "TFree a S \<notin> tatoms (sg_close ?c X)" for X a S by (rule na)
        show "tatoms X \<subseteq> set ?Ts" if "X \<in> insert (th_prop (rep_of th)) (set (hyps_of th) \<union>
            fst ` set (th_tpairs (rep_of th)) \<union> snd ` set (th_tpairs (rep_of th)))" for X
          by (rule sd(1)[OF that])
        show "tnn T" if "T \<in> set ?Ts" for T by (rule sd(2)[OF that])
        show "has_sort (sg_alg ?c) T' S \<and> cert_typ (sg_alg ?c) (sg_ar ?c) T' \<and> tnn T'"
          if "strip_repl (sg_alg ?c) d' S = Some T'" for S T'
          using sd(3)[OF that[unfolded d']] by (simp add: d')
        show "strip_atyp (sg_alg ?c) d' T = (if T \<in> set ?Ts then Some T else strip_repl (sg_alg ?c) d' (atyp_sort T))"
          for T unfolding d' by (rule sd(4))
      qed
    qed
    have "zvalid (sg_ax ?c) (set (hyps_of th)) (th_tpairs (rep_of th)) z (th_prop (rep_of th))"
      by (rule zvalid_beta_norm[OF conjunct1[OF v1] bn hc])
    moreover have "zinv z" by (rule zinv_beta_norm_prooft[OF bn]) (use v1 in blast)
    moreover have "znolb 0 z" "zhyps z \<subseteq> zhyps z1" using beta_norm_prooft_closed[OF bn, of 0] v1 by simp_all
    moreover have "zhyps_ok z" by (rule zhyps_ok_mono[OF vq(4)]) (use v1 \<open>zhyps z \<subseteq> zhyps z1\<close> in simp)
    ultimately show "zvalid (sg_ax ?c) (set (hyps_of th)) (th_tpairs (rep_of th)) z (th_prop (rep_of th)) \<and>
        zinv z \<and> znolb 0 z \<and> zhyps_ok z" by blast
  qed
qed

theorem strip_shyps_thm_rep:
  assumes "strip_shyps_thm gts th = Some th'"
  shows "rep_of th' = rep_of th" "hyps_of th' = hyps_of th" "sign_of th' = sign_of th"
    "shyps_of th' = (case strip_shyps_rep (sg_alg (sign_of th)) gts (shyps_list (shyps_of th)) (hyps_of th) (rep_of th) of
      Some d \<Rightarrow> set (sd_shyps d) | None \<Rightarrow> shyps_of th)"
proof -
  from assms have g: "finite (shyps_of th)" "sign_closed (sign_of th)" "\<forall>S\<in>shyps_of th. sort_ok (sg_alg (sign_of th)) S"
    and th': "th' = Abs_thm (mk_thm (rep_of th) (case strip_shyps_rep (sg_alg (sign_of th)) gts
      (shyps_list (shyps_of th)) (hyps_of th) (rep_of th) of Some d \<Rightarrow> set (sd_shyps d) | None \<Rightarrow> shyps_of th)
      (hyps_of th) (sign_of th)
      (bindW (proof_of th) (strip_shyps_proof (sg_alg (sign_of th)) (strip_shyps_rep (sg_alg (sign_of th)) gts
        (shyps_list (shyps_of th)) (hyps_of th) (rep_of th))))
      (bindM (zproof_of th) (zstrip_shyps_proof (sg_alg (sign_of th)) (strip_shyps_rep (sg_alg (sign_of th)) gts
        (shyps_list (shyps_of th)) (hyps_of th) (rep_of th)))))"
    unfolding strip_shyps_thm_def Let_def by (auto split: if_splits)
  have "rep_thm th' = mk_thm (rep_of th) (case strip_shyps_rep (sg_alg (sign_of th)) gts
      (shyps_list (shyps_of th)) (hyps_of th) (rep_of th) of Some d \<Rightarrow> set (sd_shyps d) | None \<Rightarrow> shyps_of th)
      (hyps_of th) (sign_of th)
      (bindW (proof_of th) (strip_shyps_proof (sg_alg (sign_of th)) (strip_shyps_rep (sg_alg (sign_of th)) gts
        (shyps_list (shyps_of th)) (hyps_of th) (rep_of th))))
      (bindM (zproof_of th) (zstrip_shyps_proof (sg_alg (sign_of th)) (strip_shyps_rep (sg_alg (sign_of th)) gts
        (shyps_list (shyps_of th)) (hyps_of th) (rep_of th))))"
    unfolding th' by (rule Abs_thm_inverse) (simp add: thm_ok_strip_shyps[OF g])
  then show "rep_of th' = rep_of th" "hyps_of th' = hyps_of th" "sign_of th' = sign_of th"
    "shyps_of th' = (case strip_shyps_rep (sg_alg (sign_of th)) gts (shyps_list (shyps_of th)) (hyps_of th) (rep_of th) of
      Some d \<Rightarrow> set (sd_shyps d) | None \<Rightarrow> shyps_of th)"
    by (simp_all add: thm_rep.truncate_def mk_thm_def)
qed

text \<open>
  The sort hypotheses that \<open>Thm.strip_shyps\<close> leaves are sorts of the types of the theorem or
  minimized sorts of the old hypotheses: they are sorts over the classes of the signature.
\<close>

lemma sorts_ok_atyp: "sorts_ok alg U \<Longrightarrow> T \<in> set (atyps U) \<Longrightarrow> sort_ok alg (atyp_sort T)"
  by (induction U) auto

context pure_sig
begin

lemma strip_shyps_sort_ok:
  assumes Ts: "\<And>T. T \<in> set Ts \<Longrightarrow> sort_ok alg (atyp_sort T)"
    and sh: "\<And>S. S \<in> set shyps \<Longrightarrow> sort_ok alg S"
  shows "\<forall>S\<in>set (sd_shyps (strip_shyps_data alg gts shyps Ts)). sort_ok alg S"
proof -
  define present where "present = map (\<lambda>T. (T, atyp_sort T)) Ts"
  define extra where "extra = fold (ord_remove sort_ord \<circ> snd) present shyps"
  obtain witnessed nw0 where w: "witness_sorts alg gts present extra = (witnessed, nw0)" by fastforce
  define nw where "nw = map (\<lambda>S. (minimize_sort alg S, S)) nw0"
  define extra' where "extra' = ord_make sort_ord (List.map_filter (\<lambda>(S, _). if \<exists>(S', _)\<in>set nw.
    sort_le alg S' S \<and> \<not> sort_le alg S S' then None else Some S) nw)"
  have d: "sd_shyps (strip_shyps_data alg gts shyps Ts) = fold (ord_insert sort_ord \<circ> snd) present extra'"
    by (simp add: strip_shyps_data_def present_sorts_def Let_def w nw_def extra'_def
      flip: present_def extra_def)
  have ins: "set (fold (ord_insert sort_ord \<circ> snd) ps xs) = snd ` set ps \<union> set xs" for ps xs
    by (induction ps arbitrary: xs) (auto simp: set_ord_insert sort_ord_EQUAL)
  have nw0: "set nw0 \<subseteq> set extra"
    using w set_fold_ord_remove_sub[of sort_ord snd witnessed extra] by (auto simp: witness_sorts_def Let_def)
  have ex: "set extra \<subseteq> set shyps"
    using set_fold_ord_remove_sub[of sort_ord snd present shyps] by (simp add: extra_def)
  have e: "sort_ok alg S" if "S \<in> set extra'" for S
  proof -
    from that obtain S0 where "S0 \<in> set nw0" "S = minimize_sort alg S0"
      by (auto simp: extra'_def set_ord_make sort_ord_EQUAL set_map_filter_gen nw_def split: if_splits)
    moreover have "set (minimize_sort alg S0) \<subseteq> set S0" by (auto simp: set_minimize_sort)
    ultimately show ?thesis using sh nw0 ex by (auto simp: sort_ok_def)
  qed
  show ?thesis unfolding d ins using e Ts by (auto simp: present_def)
qed

end

lemma sorts_ok_strip_shyps:
  fixes th :: "'u pure_thm" and gts :: "name list"
  assumes ps: "pure_sig (sg_alg (sign_of th)) (sg_ar (sign_of th))" and fin: "finite (shyps_of th)"
    and so: "\<forall>S\<in>shyps_of th. sort_ok (sg_alg (sign_of th)) S"
  shows "\<forall>S\<in>(case strip_shyps_rep (sg_alg (sign_of th)) gts (shyps_list (shyps_of th)) (hyps_of th) (rep_of th) of
      Some d \<Rightarrow> set (sd_shyps d) | None \<Rightarrow> shyps_of th). sort_ok (sg_alg (sign_of th)) S"
proof (cases "strip_shyps_rep (sg_alg (sign_of th)) gts (shyps_list (shyps_of th)) (hyps_of th) (rep_of th)")
  case None
  then show ?thesis using so by simp
next
  case (Some d')
  let ?c = "sign_of th"
  let ?hs = "hyps_of th" and ?tps = "th_tpairs (rep_of th)" and ?P = "th_prop (rep_of th)"
  let ?X = "insert ?P (set ?hs \<union> fst ` set ?tps \<union> snd ` set ?tps)"
  interpret pure_sig "sg_alg ?c" "sg_ar ?c" "sg_consts ?c" by (rule ps)
  have wt: "wt_thm (th_maxidx (rep_of th)) ?hs ?tps ?P"
    using pure_thm_wf[of th] ps by (simp add: thm_wf_def)
  have ty: "\<exists>e T. e \<turnstile> X : T" if "X \<in> ?X" for X
  proof -
    from that consider "X = ?P" | "X \<in> set ?hs" | "\<exists>(t, u)\<in>set ?tps. X = t \<or> X = u" by force
    then show ?thesis
    proof cases
      case 1
      then show ?thesis using wtpD(2)[of ?P] wt by (auto simp: wt_thm_def)
    next
      case 2
      then show ?thesis using wtpD(2)[of X] wt by (auto simp: wt_thm_def)
    next
      case 3
      then obtain t u where tu: "(t, u) \<in> set ?tps" "X = t \<or> X = u" by blast
      from wt tu(1) obtain T where "\<And>e. e \<turnstile> t : T" "\<And>e. e \<turnstile> u : T" by (fastforce simp: wt_thm_def)
      with tu(2) show ?thesis by blast
    qed
  qed
  have Ts: "sort_ok (sg_alg ?c) (atyp_sort T)" if "T \<in> set (thm_atyps ?hs ?tps ?P)" for T
  proof -
    from that obtain X U where X: "X \<in> ?X" and U: "U \<in> typs X" and TU: "T \<in> set (atyps U)"
      by (auto simp: set_thm_atyps tatoms_def)
    from ty[OF X] obtain e V where "e \<turnstile> X : V" by blast
    then have "cert_typ (sg_alg ?c) (sg_ar ?c) U" using typing_typs U by blast
    then show ?thesis using sorts_ok_atyp TU by (auto simp: cert_typ_def)
  qed
  have sl: "set (shyps_list (shyps_of th)) = shyps_of th" by (rule set_shyps_list[OF fin])
  have so': "\<And>S. S \<in> set (shyps_list (shyps_of th)) \<Longrightarrow> sort_ok (sg_alg ?c) S" using so sl by simp
  have "d' = strip_shyps_data (sg_alg ?c) gts (shyps_list (shyps_of th)) (thm_atyps ?hs ?tps ?P)"
    using Some by (simp add: strip_shyps_rep_def split: if_splits)
  with strip_shyps_sort_ok[OF Ts so', where gts = gts] Some show ?thesis by simp
qed

end

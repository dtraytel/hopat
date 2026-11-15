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
  variables among them, followed by an instantiation of type variables (theory
  \<open>Thm_Strip_Shyps_Proofs\<close> of session \<open>Thm_Correctness\<close> shows that the proofs stay valid).
\<close>

subsection \<open>Replacing the hidden atomic types of classic proofs\<close>

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

subsection \<open>The hypotheses of proofs\<close>

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

subsection \<open>Theorems\<close>

text \<open>The ordered list of the sort hypotheses of a theorem (\<open>Thm.shyps_of\<close>):\<close>

definition shyps_list :: "psort set \<Rightarrow> psort list" where
  "shyps_list S = ord_make sort_ord (SOME xs. set xs = S)"

lemma set_shyps_list: "finite S \<Longrightarrow> set (shyps_list S) = S"
  using someI_ex[OF finite_list[of S]] by (simp add: shyps_list_def set_ord_make sort_ord_EQUAL)

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

theorem thm_sem_strip_shyps:
  fixes th :: "'u pure_thm" and gts :: "name list"
  defines "d \<equiv> strip_shyps_rep (sg_alg (sign_of th)) gts (shyps_list (shyps_of th)) (hyps_of th) (rep_of th)"
  assumes fin: "finite (shyps_of th)" and sc: "sign_closed (sign_of th)"
    and so: "\<forall>S\<in>shyps_of th. sort_ok (sg_alg (sign_of th)) S"
  shows "thm_sem TYPE('u) (mk_thm (rep_of th) (case d of Some d \<Rightarrow> set (sd_shyps d) | None \<Rightarrow> shyps_of th)
    (hyps_of th) (sign_of th) (bindW (proof_of th) (strip_shyps_proof (sg_alg (sign_of th)) d))
    (bindM (zproof_of th) (zstrip_shyps_proof (sg_alg (sign_of th)) d)))"
    (is "thm_sem _ ?th")
proof (rule thm_semI)
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
    unfolding th' by (rule Abs_thm_inverse) (simp add: thm_sem_strip_shyps[OF g])
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

section \<open>Termination of Matching\<close>

theory Match_Termination
  imports Match_Sound
begin

text \<open>
  First-order matching recurses on subterms of the object. Higher-order matching may grow
  one side by \<open>\<eta>\<close>-expansion, but only while removing an abstraction from the other side, so
  the number of abstractions decreases, and otherwise both sides shrink.
\<close>

subsection \<open>Terminating computations\<close>

lemma mt_mapM: "(\<And>x. x \<in> set xs \<Longrightarrow> \<exists>r. f x = Some r) \<Longrightarrow> \<exists>r. mapM f xs = Some r"
  by (induction xs) (auto simp: bindM_def return_def split: option.splits res.splits)

lemma mt_bindM:
  "\<exists>r. m = Some r \<Longrightarrow> (\<And>x. m = Some (Ok x) \<Longrightarrow> \<exists>r. f x = Some r) \<Longrightarrow> \<exists>r. bindM m f = Some r"
  by (auto simp: bindM_def split: res.splits)

lemma mt_handle:
  "\<exists>r. m = Some r \<Longrightarrow> (\<And>e. m = Some (Err e) \<Longrightarrow> \<exists>r. h e = Some r) \<Longrightarrow> \<exists>r. handle m h = Some r"
  by (auto simp: handle_def split: res.splits)

lemma mt_return [simp]: "\<exists>r. return x = Some r" and mt_raise [simp]: "\<exists>r. raise e = Some r"
  by (simp_all add: return_def raise_def)

lemma mt_nth: "\<exists>r. nth xs i = Some r"
  by (induction xs i rule: nth.induct) auto

lemma mt_mkabs: "\<exists>r. mkabs binders is t = Some r"
  by (induction "is") (auto intro!: mt_bindM mt_nth split: prod.splits)

lemma mt_ints_of: "\<exists>r. ints_of ts = Some r"
  by (induction ts rule: ints_of.induct) (auto intro!: mt_bindM)

lemma mt_idx: "\<exists>r. idx is j = Some r"
  by (induction "is") auto

subsection \<open>Auxiliary functions\<close>

lemma mt_foldM:
  "(\<And>x e. x \<in> set xs \<Longrightarrow> \<exists>r. f x e = Some r) \<Longrightarrow> \<exists>r. foldM f xs e = Some r"
  by (induction xs arbitrary: e) (auto intro!: mt_bindM)

lemma mt_allM: "(\<And>x. x \<in> set xs \<Longrightarrow> \<exists>r. P x = Some r) \<Longrightarrow> \<exists>r. allM P xs = Some r"
  by (induction xs) (auto intro!: mt_bindM)

lemma mg_domain_term: "\<exists>r. mg_domain alg a S = Some r"
  by (auto simp: mg_domain_def split: list.splits option.splits intro!: mt_bindM mt_foldM)

lemma of_sort_term: "\<exists>r. of_sort alg T S = Some r"
proof (induction alg T S rule: of_sort.induct)
  case (1 alg T S)
  have "\<exists>r. allM (\<lambda>(T, S). of_sort alg T S) (zip Ts Ss) = Some r"
    if "S \<noteq> []" "T = Type a Ts" "mg_domain alg a S = Some (Ok Ss)" for a Ts Ss
    using that by (intro mt_allM) (auto intro: 1[OF that(1,2) that(3)[folded return_def]])
  then show ?case
    by (subst of_sort.simps)
      (auto split: ptyp.splits exn.splits intro!: mt_handle mt_bindM mg_domain_term)
qed

lemma type_lookup_term: "\<exists>r. type_lookup tye v S = Some r"
  by (auto simp: type_lookup_def tvar_clash_def split: option.splits)

lemma update_new_term: "\<exists>r. update_new x te = Some r"
  by (simp add: update_new_def)

lemma typ_match_term: "\<exists>r. typ_match alg T U tye = Some r"
  by (induction alg T U tye rule: typ_match.induct)
    (auto split: option.splits intro!: mt_bindM mt_foldM type_lookup_term of_sort_term
      update_new_term)

lemma typ_match_m_term: "\<exists>r. typ_match_m alg T U tye = Some r"
  by (auto simp: typ_match_m_def split: exn.splits intro!: mt_handle typ_match_term)

lemma lookup1_term: "\<exists>r. lookup1 te x T = Some r"
  by (auto simp: lookup1_def var_clash_def split: option.splits)

lemma fastype_of_bound_term: "\<exists>r. fastype_of_bound Ts i = Some r"
  by (induction Ts i rule: fastype_of_bound.induct) auto

lemma fastype_of_atom_term: "\<exists>r. fastype_of_atom Ts t = Some r"
  by (induction Ts t rule: fastype_of_atom.induct) (auto intro: fastype_of_bound_term)

lemma range_type_ofT_term: "\<exists>r. range_type_ofT t T = Some r"
  by (induction t T rule: range_type_ofT.induct) auto

lemma fastype_of_term_term: "\<exists>r. fastype_of_term Ts t = Some r" "\<exists>r. range_type_of Ts t = Some r"
  by (induction Ts t and Ts t rule: fastype_of_term_range_type_of.induct)
    (auto intro!: mt_bindM fastype_of_atom_term range_type_ofT_term fastype_of_bound_term)

lemma fastype_of_term': "\<exists>r. fastype_of t = Some r"
  by (simp add: fastype_of_def fastype_of_term_term)

lemma subst_type_term: "\<exists>r. subst_type tye T = Some r"
proof -
  have "\<exists>r. subst_type_aux tye T = Some r"
    by (induction tye T rule: subst_type_aux.induct)
      (auto split: option.splits intro!: mt_bindM mt_mapM type_lookup_term)
  then show ?thesis by (simp add: subst_type_def)
qed

lemma mapbnd_term: "(\<And>i. \<exists>r. f i = Some r) \<Longrightarrow> \<exists>r. mapbnd f d t = Some r"
  by (induction f d t rule: mapbnd.induct) (auto simp: return_def intro!: mt_bindM)

lemma red_term: "\<exists>r. red t is js = Some r"
  by (induction t "is" js rule: red.induct) (auto intro!: mt_bindM mapbnd_term mt_nth)

lemma zip_eq_term: "\<exists>r. zip_eq xs ys = Some r"
  by (induction xs ys rule: zip_eq.induct) (auto intro!: mt_bindM)

lemma match_bind_term: "\<exists>r. match_bind itms binders x T is t = Some r"
  by (auto simp: match_bind_def Let_def intro!: mt_bindM mapbnd_term mt_idx mt_mkabs
    update_new_term)


subsection \<open>First-order matching\<close>

theorem fo_mtch_term: "\<exists>r. fo_mtch alg inAbs env pt ob = Some r"
proof (induction ob arbitrary: inAbs env pt rule: measure_induct_rule[of size])
  case (less ob)
  show ?case
    by (subst fo_mtch.simps)
      (auto simp: Let_def split: prod.splits pterm.splits option.splits
        intro!: mt_bindM less typ_match_m_term lookup1_term fastype_of_term' update_new_term)
qed


subsection \<open>Higher-order matching\<close>

fun nabs :: "pterm \<Rightarrow> nat" where
  "nabs (pterm.Abs _ _ t) = Suc (nabs t)"
| "nabs (s $ t) = nabs s + nabs t"
| "nabs _ = 0"

lemma nabs_incr: "nabs (incr t) = nabs t"
proof -
  have "nabs (incr_aux d t) = nabs t" for d by (induction d t rule: incr_aux.induct) auto
  then show ?thesis by (simp add: incr_def)
qed

lemma mt_strip_comb_apps: "strip_comb t = (h, ts) \<Longrightarrow> t = h \<degree>\<degree> ts"
proof -
  have "strip_comb_acc t us = (h, ts) \<Longrightarrow> t \<degree>\<degree> us = h \<degree>\<degree> ts" for us
    by (induction t us rule: strip_comb_acc.induct) simp_all
  from this[of "[]"] show "strip_comb t = (h, ts) \<Longrightarrow> t = h \<degree>\<degree> ts" by (simp add: strip_comb_def)
qed

lemma strip_comb_arg:
  assumes "strip_comb t = (h, ts)" "u \<in> set ts"
  shows "nabs u \<le> nabs t" "size u < size t"
proof -
  have "nabs (h \<degree>\<degree> ts) = nabs h + sum_list (map nabs ts)" for h
    by (induction ts arbitrary: h) simp_all
  moreover have "nabs u \<le> sum_list (map nabs ts)"
    using member_le_sum_list[of "nabs u" "map nabs ts"] assms(2) by simp
  ultimately show "nabs u \<le> nabs t" using mt_strip_comb_apps[OF assms(1)] by simp
  show "size u < size t"
    using strip_comb_acc_size[of t "[]" h ts u] assms by (simp add: strip_comb_def)
qed

theorem mtch_term: "\<exists>r. mtch alg binders pt ob env = Some r"
proof (induction "(pt, ob)" arbitrary: binders pt ob env
    rule: wf_induct[OF wf_measures[of "[\<lambda>(pt, ob). nabs pt + nabs ob, \<lambda>(pt, ob). size pt + size ob]"]])
  case 1
  have IH: "\<exists>r. mtch alg binders' p q env' = Some r"
    if "nabs p + nabs q < nabs pt + nabs ob \<or>
      nabs p + nabs q \<le> nabs pt + nabs ob \<and> size p + size q < size pt + size ob" for binders' p q env'
    using 1 that by (cases env') (auto simp: order.order_iff_strict)
  obtain iTs itms where e: "env = (iTs, itms)" by force
  show ?case
  proof (cases "Pure_Term.is_Abs pt")
    case True
    then obtain ns Ts ts where pt: "pt = pterm.Abs ns Ts ts" by (cases pt) auto
    show ?thesis
      by (subst mtch.simps)
        (auto simp: e pt nabs_incr split: pterm.splits intro!: mt_bindM subst_type_term IH)
  next
    case pA: False
    show ?thesis
    proof (cases "Pure_Term.is_Abs ob")
      case True
      then obtain nt Tt tt where ob: "ob = pterm.Abs nt Tt tt" by (cases ob) auto
      show ?thesis
        by (subst mtch.simps) (auto simp: e pA ob nabs_incr intro!: IH)
    next
      case oA: False
      obtain ph pargs where sp: "strip_comb pt = (ph, pargs)" by force
      obtain oh oargs where so: "strip_comb ob = (oh, oargs)" by force
      have args: "\<exists>r. foldM (\<lambda>(p, q). mtch alg binders p q) ps e = Some r"
        if zp: "ok (zip_eq pargs oargs) ps" for ps e
      proof (rule mt_foldM)
        fix x e assume xs: "x \<in> set ps"
        have "ps = zip pargs oargs" using zp by (simp add: ok_zip_eq)
        obtain p q where x: "x = (p, q)" by force
        with xs \<open>ps = zip pargs oargs\<close> have "p \<in> set pargs" "q \<in> set oargs"
          by (auto dest: set_zip_leftD set_zip_rightD)
        note x = x this
        show "\<exists>r. (\<lambda>(p, q). mtch alg binders p q) x e = Some r"
          using strip_comb_arg[OF sp x(2)] strip_comb_arg[OF so x(3)] by (auto simp: x intro!: IH)
      qed
      show ?thesis
        by (subst mtch.simps)
          (auto simp: e pA oA sp so Let_def split: pterm.splits option.splits exn.splits
            intro!: mt_bindM mt_handle typ_match_m_term lookup1_term mt_ints_of red_term
              match_bind_term zip_eq_term args)
    qed
  qed
qed


subsection \<open>Termination\<close>

theorem first_order_match_term: "\<exists>r. first_order_match alg pt ob env = Some r"
  by (simp add: first_order_match_def fo_mtch_term)

theorem match_term: "\<exists>r. match alg pt ob env = Some r"
  by (auto simp: match_def Let_def split: exn.splits
    intro!: mt_bindM mt_handle fastype_of_term' typ_match_m_term mtch_term first_order_match_term)

end

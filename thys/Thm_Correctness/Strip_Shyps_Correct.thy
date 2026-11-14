section \<open>Witnesses of sorts\<close>

theory Strip_Shyps_Correct
  imports Thm_Axiom "Pure_Thm.Pure_Sorts"
begin

text \<open>
  The witnesses of \<^const>\<open>witness_sorts\<close> (\<open>Sorts.witness_sorts\<close>) are sound: in every model,
  a sort with a witness is inhabited if the sorts of the given types (the present type variables
  of a theorem) are.
\<close>

subsection \<open>Minimal elements and ordered lists\<close>

lemma finite_minimal_below:
  assumes fin: "finite X" and x: "x \<in> X" and irr: "\<And>a. \<not> R a a" and tr: "\<And>a b c. R a b \<Longrightarrow> R b c \<Longrightarrow> R a c"
  shows "\<exists>m\<in>X. (m = x \<or> R m x) \<and> (\<forall>y\<in>X. \<not> R y m)"
  using x
proof (induction x rule: measure_induct_rule[where f = "\<lambda>x. card {y \<in> X. R y x}"])
  case (less x)
  show ?case
  proof (cases "\<exists>y\<in>X. R y x")
    case False
    with less.prems show ?thesis by blast
  next
    case True
    then obtain y where y: "y \<in> X" "R y x" by blast
    have "{z \<in> X. R z y} \<subset> {z \<in> X. R z x}"
      using y irr tr by blast
    then have "card {z \<in> X. R z y} < card {z \<in> X. R z x}"
      using fin by (intro psubset_card_mono) auto
    from less.IH[OF this y(1)] obtain m where "m \<in> X" "m = y \<or> R m y" "\<forall>z\<in>X. \<not> R z m" by blast
    with y tr show ?thesis by blast
  qed
qed

lemma string_ord_EQUAL: "string_ord a b = EQUAL \<longleftrightarrow> a = b"
  by (simp add: string_ord_def)

lemma set_ord_make: "(\<And>x y. ord x y = EQUAL \<longleftrightarrow> x = y) \<Longrightarrow> set (ord_make ord xs) = set xs"
proof -
  assume e: "\<And>x y. ord x y = EQUAL \<longleftrightarrow> x = y"
  have ins: "set (ord_insert ord x ys) = insert x (set ys)" for x ys
    by (induction ys) (auto simp: e split: order.splits)
  have "set (fold (ord_insert ord) xs acc) = set xs \<union> set acc" for acc
    by (induction xs arbitrary: acc) (auto simp: ins)
  then show ?thesis by (simp add: ord_make_def)
qed

subsection \<open>Invariants of the witnesses\<close>

text \<open>
  A property of the witnesses that holds for \<open>prop\<close> (the witness of the empty sort), is
  preserved by weaker sorts and by the arities of type constructors holds for the hypotheses and
  the solved sorts of \<^const>\<open>witn_sort\<close> if it holds for the given hypotheses.
\<close>

definition wres :: "(ptyp \<times> psort \<Rightarrow> bool) \<Rightarrow> (ptyp \<times> psort) option \<Rightarrow> psort \<Rightarrow> bool" where
  "wres Q r S \<longleftrightarrow> (\<forall>w. r = Some w \<longrightarrow> snd w = S \<and> Q w)"

lemma set_map_filter_gen: "set (List.map_filter f xs) = {y. \<exists>x\<in>set xs. f x = Some y}"
  by (induction xs) (auto simp: map_filter_simps split: option.splits)

lemma set_map_filter_id: "set (List.map_filter (\<lambda>x. x) xs) = {w. Some w \<in> set xs}"
  by (simp add: set_map_filter_gen)

lemma find_witn_get:
  "List.find (\<lambda>w. witn_get alg S w \<noteq> None) ws = Some w \<Longrightarrow> w \<in> set ws \<and> (\<exists>w'. witn_get alg S w = Some w')"
  by (auto simp: find_Some_iff dest: nth_mem)

theorem witn_inv:
  fixes Q :: "ptyp \<times> psort \<Rightarrow> bool"
  assumes Q0: "Q (propT, [])"
    and Qle: "\<And>T S1 S2. Q (T, S1) \<Longrightarrow> sort_le alg S1 S2 \<Longrightarrow> Q (T, S2)"
    and Qty: "\<And>t S SS Ts. mg_dom alg t S = Some SS \<Longrightarrow> list_all2 (\<lambda>T D. Q (T, D)) Ts SS \<Longrightarrow> Q (Type t Ts, S)"
  shows "witn_sort a gts hs path S st = (r, st') \<Longrightarrow> a = alg \<Longrightarrow> \<forall>w\<in>set hs. Q w \<Longrightarrow>
      \<forall>w\<in>set (fst st). Q w \<Longrightarrow> wres Q r S \<and> (\<forall>w\<in>set (fst st'). Q w)"
    and "witn_sorts a gts hs path Ss st = (rs, st') \<Longrightarrow> a = alg \<Longrightarrow> \<forall>w\<in>set hs. Q w \<Longrightarrow>
      \<forall>w\<in>set (fst st). Q w \<Longrightarrow> list_all2 (wres Q) rs Ss \<and> (\<forall>w\<in>set (fst st'). Q w)"
    and "witn_types a gts hs path ts S st = (r, st') \<Longrightarrow> a = alg \<Longrightarrow> \<forall>w\<in>set hs. Q w \<Longrightarrow>
      \<forall>w\<in>set (fst st). Q w \<Longrightarrow> wres Q r S \<and> (\<forall>w\<in>set (fst st'). Q w)"
proof (induction a gts hs path S st and a gts hs path Ss st and a gts hs path ts S st
    arbitrary: r st' and rs st' and r st' rule: witn_sort_witn_sorts_witn_types.induct)
  case (1 a gts hs path S solved failed)
  have a: "a = alg" and hy: "\<forall>w\<in>set hs. Q w" and wi: "\<forall>w\<in>set solved. Q w"
    using "1.prems"(2-4) by simp_all
  have get: "snd w' = S \<and> Q w'" if "witn_get a S w = Some w'" "Q w" for w w'
    using that Qle[of "fst w" "snd w" S] a by (auto simp: witn_get_def split: if_splits)
  show ?case
  proof (cases "S = []")
    case True
    with "1.prems"(1) wi Q0 show ?thesis by (auto simp: wres_def)
  next
    case S: False
    show ?thesis
    proof (cases "\<exists>F\<in>set failed. sort_le a S F")
      case True
      with "1.prems"(1) S wi show ?thesis by (auto simp: wres_def)
    next
      case nf: False
      show ?thesis
      proof (cases "List.find (\<lambda>w. witn_get a S w \<noteq> None) solved")
        case (Some w)
        from find_witn_get[OF Some] obtain w' where w: "w \<in> set solved" "witn_get a S w = Some w'" by blast
        have "snd w' = S \<and> Q w'" using get[OF w(2)] w(1) wi by blast
        with "1.prems"(1) S nf Some wi w(2) show ?thesis by (auto simp: wres_def)
      next
        case ns: None
        show ?thesis
        proof (cases "List.find (\<lambda>w. witn_get a S w \<noteq> None) hs")
          case (Some w)
          from find_witn_get[OF Some] obtain w' where w: "w \<in> set hs" "witn_get a S w = Some w'" by blast
          have "snd w' = S \<and> Q w'" using get[OF w(2)] w(1) hy by blast
          with "1.prems"(1) S nf ns Some wi w(2) show ?thesis by (auto simp: wres_def)
        next
          case nh: None
          from "1.prems"(1) S nf ns nh have "witn_types a gts hs path gts S (solved, failed) = (r, st')" by simp
          then show ?thesis using "1.IH" S nf ns nh a hy wi by simp
        qed
      qed
    qed
  qed
next
  case (2 a gts hs path st)
  then show ?case by simp
next
  case (3 a gts hs path S Ss st)
  obtain w st1 where w: "witn_sort a gts hs path S st = (w, st1)" by (metis prod.exhaust)
  obtain ws st2 where ws: "witn_sorts a gts hs path Ss st1 = (ws, st2)" by (metis prod.exhaust)
  from "3.prems"(1) w ws have rs: "rs = w # ws" "st' = st2" by simp_all
  from "3.IH"(1)[OF w "3.prems"(2-4)] have r1: "wres Q w S" "\<forall>w\<in>set (fst st1). Q w" by blast+
  from "3.IH"(2)[OF w[symmetric] HOL.refl ws "3.prems"(2,3) r1(2)]
  have "list_all2 (wres Q) ws Ss" "\<forall>w\<in>set (fst st2). Q w" by blast+
  with r1 rs show ?case by simp
next
  case (4 a gts hs path S solved failed)
  then show ?case by (auto simp: wres_def)
next
  case (5 a gts hs path t ts S st)
  note eq = "5.prems"(1) and a = "5.prems"(2) and hy = "5.prems"(3) and wi = "5.prems"(4)
  show ?case
  proof (cases "mg_dom a t S")
    case None
    with eq have "witn_types a gts hs path ts S st = (r, st')" by simp
    from "5.IH"(1)[OF None this a hy wi] show ?thesis .
  next
    case (Some SS)
    show ?thesis
    proof (cases "\<exists>D\<in>set SS. sort_le a D S \<or> Bex (set path) (sort_le a D)")
      case True
      with eq Some have "witn_types a gts hs path ts S st = (r, st')" by simp
      from "5.IH"(2)[OF Some True this a hy wi] show ?thesis .
    next
      case nb: False
      obtain ws solved' failed' where ws: "witn_sorts a gts hs (S # path) SS st = (ws, (solved', failed'))"
        by (metis prod.exhaust)
      from "5.IH"(3)[OF Some nb ws a hy wi]
      have l: "list_all2 (wres Q) ws SS" and wi': "\<forall>w\<in>set solved'. Q w" by simp_all
      show ?thesis
      proof (cases "\<forall>w\<in>set ws. w \<noteq> None")
        case True
        let ?w = "(Type t (map (fst \<circ> the) ws), S)"
        from eq Some nb ws True have r: "r = Some ?w" "st' = (?w # solved', failed')" by (simp_all add: Let_def)
        have q: "Q (fst (the (ws ! i)), SS ! i)" if i: "i < length SS" for i
        proof -
          have "i < length ws" using i l by (simp add: list_all2_lengthD)
          then obtain w where w: "ws ! i = Some w" using True nth_mem by fastforce
          have "wres Q (ws ! i) (SS ! i)" using l i by (simp add: list_all2_conv_all_nth)
          with w show ?thesis by (cases w) (simp add: wres_def)
        qed
        have "list_all2 (\<lambda>T D. Q (T, D)) (map (fst \<circ> the) ws) SS"
          unfolding list_all2_conv_all_nth using q list_all2_lengthD[OF l] by simp
        then have "Q ?w" using Qty[of t S SS] Some a by simp
        with r wi' show ?thesis by (simp add: wres_def)
      next
        case False
        with eq Some nb ws have "witn_types a gts hs path ts S (solved', failed') = (r, st')"
          by (auto simp: Let_def split: if_splits)
        from "5.IH"(4)[OF Some nb ws[symmetric] HOL.refl HOL.refl False this a hy] wi' show ?thesis by simp
      qed
    qed
  qed
qed

subsection \<open>Minimal sorts and the sorts of the witnesses\<close>

context wf_algebra
begin

lemma set_minimize_sort: "set (minimize_sort alg S) = {c \<in> set S. \<not> (\<exists>c'\<in>set S. class_less alg c' c)}"
proof (cases S)
  case Nil
  then show ?thesis by (simp add: minimize_sort_def)
next
  case (Cons a l)
  then show ?thesis
    by (cases l) (auto simp: minimize_sort_def set_ord_make string_ord_EQUAL class_less_irrefl)
qed

lemma minimize_sort_le: "sort_le alg (minimize_sort alg S) S"
  unfolding sort_le_iff set_minimize_sort
proof
  fix c assume "c \<in> set S"
  have "\<exists>m\<in>set S. (m = c \<or> class_less alg m c) \<and> (\<forall>y\<in>set S. \<not> class_less alg y m)"
    by (rule finite_minimal_below) (use \<open>c \<in> set S\<close> class_less_irrefl class_less_trans in blast)+
  then obtain m where "m \<in> set S" "m = c \<or> class_less alg m c" "\<forall>y\<in>set S. \<not> class_less alg y m" by blast
  then show "\<exists>c'\<in>{c \<in> set S. \<not> (\<exists>c'\<in>set S. class_less alg c' c)}. class_le alg c' c"
    by (auto simp: class_le_def)
qed

lemma minimize_sort_ge: "sort_le alg S (minimize_sort alg S)"
  unfolding sort_le_iff set_minimize_sort using class_le_refl by blast

lemma sort_le_trans: "sort_le alg S1 S2 \<Longrightarrow> sort_le alg S2 S3 \<Longrightarrow> sort_le alg S1 S3"
  unfolding sort_le_iff by (meson class_le_trans)


lemma mg_dom_sem:
  assumes m: "mg_dom alg t S = Some SS" and c: "c \<in> set S"
  shows "\<exists>Ss. map_of (arities alg t) c = Some Ss \<and> length Ss = length SS \<and>
    (\<forall>i<length SS. sort_le alg (SS ! i) (Ss ! i))"
proof -
  have md: "mg_domain alg t S = return SS"
    using m by (auto simp: mg_dom_def return_def split: option.splits xres.splits)
  have S: "S \<noteq> []" using c by auto
  have ar: "\<forall>c\<in>set S. map_of (arities alg t) c \<noteq> None"
  proof
    fix c' assume "c' \<in> set S"
    show "map_of (arities alg t) c' \<noteq> None"
    proof
      assume "map_of (arities alg t) c' = None"
      from mg_domain_error[OF S \<open>c' \<in> set S\<close> this] md show False by (auto simp: return_def raise_def)
    qed
  qed
  from mg_domain_ok[OF S ar] obtain Ds where Ds: "mg_domain alg t S = return Ds" "length Ds = tarity ar t"
    "\<And>i T. i < tarity ar t \<Longrightarrow> has_sort alg T (Ds ! i) \<longleftrightarrow>
      (\<forall>c\<in>set S. \<forall>Ss. map_of (arities alg t) c = Some Ss \<longrightarrow> has_sort alg T (Ss ! i))"
    by blast
  have DS: "Ds = SS" using Ds(1) md by (simp add: return_def)
  from ar c obtain Ss where Ss: "map_of (arities alg t) c = Some Ss" by blast
  have l: "length Ss = length SS" using arity_length[OF Ss] Ds(2) DS by simp
  have "sort_le alg (SS ! i) (Ss ! i)" if "i < length SS" for i
  proof -
    have i': "i < tarity ar t" using that Ds(2) DS by simp
    have "has_sort alg (TVar (STR '''', 0) (SS ! i)) (Ss ! i)"
      using Ds(3)[OF i', of "TVar (STR '''', 0) (SS ! i)"] has_sort_TVar_refl c Ss DS by auto
    then show ?thesis by (simp only: has_sort_TVar_iff)
  qed
  with Ss l show ?thesis by blast
qed

lemma mg_dom_has_sort:
  assumes m: "mg_dom alg t S = Some SS" and l: "list_all2 (\<lambda>T D. has_sort alg T D) Ts SS"
  shows "has_sort alg (Type t Ts) S"
proof -
  have "\<exists>Ss. map_of (arities alg t) c = Some Ss \<and> (\<forall>i<length Ts. has_sort alg (Ts ! i) (Ss ! i))"
    if c: "c \<in> set S" for c
  proof -
    from mg_dom_sem[OF m c] obtain Ss where Ss: "map_of (arities alg t) c = Some Ss" "length Ss = length SS"
      "\<And>i. i < length SS \<Longrightarrow> sort_le alg (SS ! i) (Ss ! i)"
      by blast
    have "has_sort alg (Ts ! i) (Ss ! i)" if "i < length Ts" for i
    proof -
      have iS: "i < length SS" using that l by (simp add: list_all2_lengthD)
      have "has_sort alg (Ts ! i) (SS ! i)" using l iS by (simp add: list_all2_conv_all_nth)
      then show "has_sort alg (Ts ! i) (Ss ! i)" by (rule has_sort_mono) (rule Ss(3)[OF iS])
    qed
    with Ss(1) show ?thesis by blast
  qed
  moreover have "length Ts = tarity ar t" if "S \<noteq> []"
  proof -
    from that obtain c where c: "c \<in> set S" by (cases S) auto
    from mg_dom_sem[OF m c] obtain Ss where "map_of (arities alg t) c = Some Ss" "length Ss = length SS"
      by blast
    with arity_length l show ?thesis by (simp add: list_all2_lengthD)
  qed
  ultimately show ?thesis
    by (cases "S = []") (fastforce simp: has_sort_Type dest: arity_length)+
qed

text \<open>The witnesses are of their sorts if the hypotheses are:\<close>

theorem witness_sorts_has_sort:
  assumes w: "witness_sorts alg gts hyps sorts = (witnessed, nw)"
    and hyps: "\<forall>w\<in>set hyps. has_sort alg (fst w) (snd w)"
  shows "\<forall>w\<in>set witnessed. has_sort alg (fst w) (snd w) \<and> snd w \<in> set sorts"
proof -
  obtain rs st where rs: "witn_sorts alg gts hyps [] sorts ([], []) = (rs, st)" by (metis prod.exhaust)
  have "list_all2 (wres (\<lambda>w. has_sort alg (fst w) (snd w))) rs sorts \<and>
      (\<forall>w\<in>set (fst st). has_sort alg (fst w) (snd w))"
  proof (rule witn_inv(2)[where Q = "\<lambda>w. has_sort alg (fst w) (snd w)", OF _ _ _ rs HOL.refl hyps])
    fix T S1 S2 assume "has_sort alg (fst (T, S1)) (snd (T, S1))" "sort_le alg S1 S2"
    then show "has_sort alg (fst (T, S2)) (snd (T, S2))" unfolding fst_conv snd_conv by (rule has_sort_mono)
  next
    fix t S SS Ts assume "mg_dom alg t S = Some SS" "list_all2 (\<lambda>T D. has_sort alg (fst (T, D)) (snd (T, D))) Ts SS"
    then show "has_sort alg (fst (Type t Ts, S)) (snd (Type t Ts, S))"
      unfolding fst_conv snd_conv by (rule mg_dom_has_sort)
  qed simp_all
  then have l: "list_all2 (wres (\<lambda>w. has_sort alg (fst w) (snd w))) rs sorts" ..
  have wi: "witnessed = List.map_filter (\<lambda>x. x) rs"
    using w rs by (auto simp: witness_sorts_def Let_def)
  have "\<exists>i<length sorts. rs ! i = Some w" if "w \<in> set witnessed" for w
  proof -
    have "Some w \<in> set rs" using that by (auto simp: wi set_map_filter_gen)
    then obtain i where "i < length rs" "rs ! i = Some w" by (auto simp: in_set_conv_nth)
    with list_all2_lengthD[OF l] show ?thesis by auto
  qed
  then show ?thesis
    using l by (fastforce simp: list_all2_conv_all_nth wres_def)
qed
end


subsection \<open>Soundness of the witnesses\<close>

context pure_model
begin

lemma sinh_Nil: "sinh []"
  using une_ubool by (auto simp: sinh_def ssem_def)

lemma ssem_sort_le: "sort_le alg S1 S2 \<Longrightarrow> une A \<Longrightarrow> ssem S1 A \<Longrightarrow> ssem S2 A"
  unfolding sort_le_iff ssem_def by (blast intro: cls_le)

lemma sinh_sort_le: "sort_le alg S1 S2 \<Longrightarrow> sinh S1 \<Longrightarrow> sinh S2"
  by (auto simp: sinh_def intro: ssem_sort_le)

lemma une_ucon: "(\<And>A. A \<in> set As \<Longrightarrow> une A) \<Longrightarrow> une (ucon t As)"
proof -
  assume ne: "\<And>A. A \<in> set As \<Longrightarrow> une A"
  show ?thesis
  proof (cases "t = STR ''fun'' \<and> length As = 2")
    case True
    then obtain A B where "As = [A, B]" by (auto simp: numeral_2_eq_2 length_Suc_conv)
    with ne True show ?thesis by (simp add: tycon_def une_ufun)
  next
    case False
    have "une (tcon t As)" by (rule tcon_ne) (rule ne)
    with False show ?thesis using une_ubool by (auto simp: tycon_def)
  qed
qed

lemma sinh_type:
  assumes m: "mg_dom alg t S = Some SS" and inh: "\<And>i. i < length SS \<Longrightarrow> sinh (SS ! i)"
  shows "sinh S"
proof -
  define As where "As = map (\<lambda>i. SOME A. une A \<and> ssem (SS ! i) A) [0..<length SS]"
  have As: "une (As ! i) \<and> ssem (SS ! i) (As ! i)" if "i < length SS" for i
    using someI_ex[OF inh[OF that, unfolded sinh_def]] that by (simp add: As_def)
  have lA: "length As = length SS" by (simp add: As_def)
  have "une (ucon t As)" by (rule une_ucon) (use As lA in \<open>auto simp: in_set_conv_nth\<close>)
  moreover have "ssem S (ucon t As)"
    unfolding ssem_def
  proof
    fix c assume c: "c \<in> set S"
    from mg_dom_sem[OF m c] obtain Ss where Ss: "map_of (arities alg t) c = Some Ss" "length Ss = length SS"
      "\<And>i. i < length SS \<Longrightarrow> sort_le alg (SS ! i) (Ss ! i)"
      by blast
    show "cls c (ucon t As)"
    proof (rule cls_arity[OF Ss(1)])
      show "length As = length Ss" using lA Ss(2) by simp
      show "une A" if "A \<in> set As" for A using that As lA by (auto simp: in_set_conv_nth)
      fix i c' assume "i < length Ss" "c' \<in> set (Ss ! i)"
      with Ss(2,3) As show "cls c' (As ! i)" by (metis ssem_def ssem_sort_le)
    qed
  qed
  ultimately show ?thesis by (auto simp: sinh_def)
qed

end


subsection \<open>Ordered lists of sorts\<close>

lemma fast_string_ord_EQUAL: "fast_string_ord a b = EQUAL \<longleftrightarrow> a = b"
  by (auto simp: fast_string_ord_def int_ord_def string_ord_def split: if_splits order.splits)

lemma fast_string_ord_refl [simp]: "fast_string_ord a a = EQUAL"
  by (simp add: fast_string_ord_EQUAL)

lemma sort_ord_EQUAL: "sort_ord S1 S2 = EQUAL \<longleftrightarrow> S1 = S2"
proof -
  have "dict_ord fast_string_ord xs ys = EQUAL \<longleftrightarrow> xs = ys" for xs ys
    by (induction fast_string_ord xs ys rule: dict_ord.induct)
      (auto simp: fast_string_ord_EQUAL split: order.splits)
  then show ?thesis by (simp add: sort_ord_def)
qed

lemma set_ord_insert: "(\<And>y. ord x y = EQUAL \<longleftrightarrow> x = y) \<Longrightarrow> set (ord_insert ord x xs) = insert x (set xs)"
  by (induction xs) (auto split: order.splits)

lemma set_ord_remove: "(\<And>y. ord x y = EQUAL \<longleftrightarrow> x = y) \<Longrightarrow> set xs - {x} \<subseteq> set (ord_remove ord x xs)"
  by (induction xs) (auto split: order.splits)

text \<open>
  \<open>Term_Ord.sort_ord\<close> is a linear order: the sort hypotheses of a theorem, which Isabelle keeps
  ordered, are determined by their set.
\<close>

definition ord_linear :: "('a \<Rightarrow> 'a \<Rightarrow> order) \<Rightarrow> bool" where
  "ord_linear ord \<longleftrightarrow> (\<forall>x y. ord x y = EQUAL \<longleftrightarrow> x = y) \<and> (\<forall>x y. ord x y = GREATER \<longleftrightarrow> ord y x = LESS) \<and>
    (\<forall>x y z. ord x y = LESS \<longrightarrow> ord y z = LESS \<longrightarrow> ord x z = LESS)"

lemma ord_linear_fast_string_ord: "ord_linear fast_string_ord"
proof -
  have L: "fast_string_ord a b = LESS \<longleftrightarrow>
      literal_size a < literal_size b \<or> literal_size a = literal_size b \<and> a < b" for a b
    by (auto simp: fast_string_ord_def int_ord_def string_ord_def split: if_splits order.splits)
  have G: "fast_string_ord a b = GREATER \<longleftrightarrow>
      literal_size b < literal_size a \<or> literal_size a = literal_size b \<and> b < a" for a b
    by (auto simp: fast_string_ord_def int_ord_def string_ord_def split: if_splits order.splits)
  show ?thesis
    unfolding ord_linear_def L G fast_string_ord_EQUAL by auto
qed

lemma ord_linear_dict_ord: "ord_linear ord \<Longrightarrow> ord_linear (dict_ord ord)"
proof -
  assume o: "ord_linear ord"
  from o have E: "\<And>x y. ord x y = EQUAL \<longleftrightarrow> x = y" and G: "\<And>x y. ord x y = GREATER \<longleftrightarrow> ord y x = LESS"
    and T: "\<And>x y z. ord x y = LESS \<Longrightarrow> ord y z = LESS \<Longrightarrow> ord x z = LESS"
    unfolding ord_linear_def by blast+
  have R: "ord x x = EQUAL" for x using E by simp
  have dE: "dict_ord ord xs ys = EQUAL \<longleftrightarrow> xs = ys" for xs ys
  proof (induction xs arbitrary: ys)
    case Nil
    show ?case by (cases ys) auto
  next
    case (Cons x xs)
    show ?case by (cases ys) (auto simp: E R Cons.IH split: order.splits)
  qed
  have dG: "dict_ord ord xs ys = GREATER \<longleftrightarrow> dict_ord ord ys xs = LESS" for xs ys
  proof (induction xs arbitrary: ys)
    case Nil
    show ?case by (cases ys) auto
  next
    case (Cons x xs)
    show ?case
    proof (cases ys)
      case (Cons y ys')
      have "ord x y = EQUAL \<longleftrightarrow> ord y x = EQUAL" using E by auto
      then show ?thesis using G[of x y] G[of y x] Cons.IH[of ys']
        by (cases "ord x y"; cases "ord y x"; simp add: Cons)
    qed simp
  qed
  have dT: "dict_ord ord xs ys = LESS \<Longrightarrow> dict_ord ord ys zs = LESS \<Longrightarrow> dict_ord ord xs zs = LESS" for xs ys zs
  proof (induction xs arbitrary: ys zs)
    case Nil
    then show ?case by (cases ys; cases zs) auto
  next
    case (Cons x xs)
    from Cons.prems obtain y ys' where ys: "ys = y # ys'" by (cases ys) auto
    from Cons.prems obtain z zs' where zs: "zs = z # zs'" by (cases zs) (auto simp: ys split: order.splits)
    from Cons.prems Cons.IH show ?case
      unfolding ys zs using T[of x y z] E[of x y] E[of y z] E[of x z]
      by (auto split: order.splits)
  qed
  show ?thesis unfolding ord_linear_def using dE dG dT by blast
qed

lemma ord_linear_sort_ord: "ord_linear sort_ord"
  unfolding sort_ord_def by (rule ord_linear_dict_ord[OF ord_linear_fast_string_ord])

lemma sorted_ord_unique:
  assumes o: "ord_linear ord"
    and "sorted_wrt (\<lambda>x y. ord x y = LESS) xs" "sorted_wrt (\<lambda>x y. ord x y = LESS) ys" "set xs = set ys"
  shows "xs = ys"
  using assms(2-4)
proof (induction xs arbitrary: ys)
  case Nil
  then show ?case by simp
next
  case (Cons x xs)
  from Cons.prems(3) obtain y ys' where ys: "ys = y # ys'" by (cases ys) auto
  from o have E: "\<And>x y. ord x y = EQUAL \<longleftrightarrow> x = y" and G: "\<And>x y. ord x y = GREATER \<longleftrightarrow> ord y x = LESS"
    unfolding ord_linear_def by blast+
  have irr: "ord a a \<noteq> LESS" for a using E[of a a] by auto
  have asym: "ord a b = LESS \<Longrightarrow> ord b a \<noteq> LESS" for a b
    using G[of a b] by auto
  have "x = y"
  proof (rule ccontr)
    assume ne: "x \<noteq> y"
    have "x \<in> set ys'" "y \<in> set xs" using Cons.prems(3) ne by (auto simp: ys)
    with Cons.prems(1,2) have "ord y x = LESS" "ord x y = LESS" by (auto simp: ys)
    with asym show False by blast
  qed
  moreover have "x \<notin> set xs" "y \<notin> set ys'" using Cons.prems(1,2) irr by (auto simp: ys)
  then have "set xs = set ys'" using Cons.prems(3) \<open>x = y\<close> by (auto simp: ys)
  with Cons.IH[of ys'] Cons.prems(1,2) have "xs = ys'" by (simp add: ys)
  ultimately show ?case by (simp add: ys)
qed

context pure_model
begin

text \<open>The witnessed sorts of \<^const>\<open>witness_sorts\<close> are inhabited, and every other sort is left:\<close>

theorem witness_sorts_sound:
  assumes w: "witness_sorts alg gts hyps sorts = (witnessed, nw)" and hyps: "\<forall>w\<in>set hyps. sinh (snd w)"
  shows "\<forall>w\<in>set witnessed. sinh (snd w)" "\<And>S. S \<in> set sorts \<Longrightarrow> sinh S \<or> S \<in> set nw"
proof -
  obtain rs st where rs: "witn_sorts alg gts hyps [] sorts ([], []) = (rs, st)" by (metis prod.exhaust)
  have Qty: "sinh S" if "mg_dom alg t S = Some SS" "list_all2 (\<lambda>T D. sinh D) Ts SS" for t S SS Ts
    using sinh_type[OF that(1)] that(2) by (simp add: list_all2_conv_all_nth)
  have "list_all2 (wres (\<lambda>w. sinh (snd w))) rs sorts \<and> (\<forall>w\<in>set (fst st). sinh (snd w))"
    by (rule witn_inv(2)[where Q = "\<lambda>w. sinh (snd w)", OF _ _ _ rs HOL.refl hyps])
      (auto intro: sinh_Nil sinh_sort_le Qty)
  then have l: "list_all2 (wres (\<lambda>w. sinh (snd w))) rs sorts" ..
  have wi: "witnessed = List.map_filter (\<lambda>x. x) rs" and nw: "nw = fold (ord_remove sort_ord \<circ> snd) witnessed sorts"
    using w rs by (auto simp: witness_sorts_def Let_def)
  have ws: "\<exists>i<length sorts. rs ! i = Some w" if "w \<in> set witnessed" for w
  proof -
    have "Some w \<in> set rs" using that by (auto simp: wi set_map_filter_gen)
    then obtain i where "i < length rs" "rs ! i = Some w" by (auto simp: in_set_conv_nth)
    with list_all2_lengthD[OF l] show ?thesis by auto
  qed
  show "\<forall>w\<in>set witnessed. sinh (snd w)"
    using ws l by (fastforce simp: list_all2_conv_all_nth wres_def)
  fix S assume S: "S \<in> set sorts"
  have rem: "set xs - snd ` set ws \<subseteq> set (fold (ord_remove sort_ord \<circ> snd) ws xs)" for ws xs
  proof (induction ws arbitrary: xs)
    case (Cons w ws)
    have "set xs - {snd w} \<subseteq> set (ord_remove sort_ord (snd w) xs)" by (rule set_ord_remove) (simp add: sort_ord_EQUAL)
    with Cons.IH[of "ord_remove sort_ord (snd w) xs"] show ?case by auto
  qed simp
  show "sinh S \<or> S \<in> set nw"
  proof (cases "S \<in> snd ` set witnessed")
    case True
    then show ?thesis using \<open>\<forall>w\<in>set witnessed. sinh (snd w)\<close> by auto
  next
    case False
    then show ?thesis using rem[of sorts witnessed] S by (auto simp: nw)
  qed
qed

text \<open>
  The sort hypotheses after \<open>Thm.strip_shyps\<close>: if they are inhabited, then so are the sort
  hypotheses before.
\<close>

theorem strip_shyps_sinh:
  assumes inh: "\<And>S. S \<in> set (sd_shyps (strip_shyps_data alg gts shyps Ts)) \<Longrightarrow> sinh S"
    and S: "S \<in> set shyps"
  shows "sinh S"
proof -
  let ?lt = "\<lambda>S1 S2. sort_le alg S1 S2 \<and> \<not> sort_le alg S2 S1"
  let ?m = "minimize_sort alg"
  define present where "present = map (\<lambda>T. (T, atyp_sort T)) Ts"
  define extra where "extra = fold (ord_remove sort_ord \<circ> snd) present shyps"
  obtain witnessed nw0 where w: "witness_sorts alg gts present extra = (witnessed, nw0)" by fastforce
  define nw where "nw = map (\<lambda>S. (?m S, S)) nw0"
  define extra' where "extra' = ord_make sort_ord (List.map_filter (\<lambda>(S, _). if \<exists>(S', _)\<in>set nw. ?lt S' S then None
    else Some S) nw)"
  have d: "sd_shyps (strip_shyps_data alg gts shyps Ts) = fold (ord_insert sort_ord \<circ> snd) present extra'"
    by (simp add: strip_shyps_data_def present_sorts_def Let_def w nw_def extra'_def flip: present_def extra_def)
  have ins: "set (fold (ord_insert sort_ord \<circ> snd) ps xs) = snd ` set ps \<union> set xs" for ps xs
    by (induction ps arbitrary: xs) (auto simp: set_ord_insert sort_ord_EQUAL)
  have shy: "set (sd_shyps (strip_shyps_data alg gts shyps Ts)) = snd ` set present \<union> set extra'"
    by (simp add: d ins)
  have pin: "\<forall>w\<in>set present. sinh (snd w)" using inh shy by blast
  have ws: "\<And>S. S \<in> set extra \<Longrightarrow> sinh S \<or> S \<in> set nw0"
    by (rule witness_sorts_sound(2)[OF w pin])
  have e': "set extra' = {M \<in> ?m ` set nw0. \<not> (\<exists>M'\<in>?m ` set nw0. ?lt M' M)}"
    unfolding extra'_def set_ord_make[OF sort_ord_EQUAL] set_map_filter_gen nw_def
    by (auto split: if_splits)
  have irr: "\<not> ?lt M M" for M by auto
  have tr: "?lt M1 M3" if "?lt M1 M2" "?lt M2 M3" for M1 M2 M3
    using that sort_le_trans by blast
  have nwinh: "sinh S" if S0: "S \<in> set nw0" for S
  proof -
    have "\<exists>M\<in>?m ` set nw0. (M = ?m S \<or> ?lt M (?m S)) \<and> (\<forall>M'\<in>?m ` set nw0. \<not> ?lt M' M)"
    proof (rule finite_minimal_below)
      show "?m S \<in> ?m ` set nw0" using S0 by simp
      show "?lt a c" if "?lt a b" "?lt b c" for a b c by (rule tr[OF that])
    qed (simp_all add: irr)
    then obtain M where M: "M \<in> ?m ` set nw0" "M = ?m S \<or> ?lt M (?m S)" "\<forall>M'\<in>?m ` set nw0. \<not> ?lt M' M"
      by blast
    have "M \<in> set extra'" using M(1,3) by (simp add: e')
    then have "sinh M" using inh shy by blast
    moreover have "sort_le alg M (?m S)" using M(2) by auto
    ultimately have "sinh (?m S)" by (rule sinh_sort_le[rotated])
    then show ?thesis by (rule sinh_sort_le[OF minimize_sort_le])
  qed
  have rem: "set xs - snd ` set ws \<subseteq> set (fold (ord_remove sort_ord \<circ> snd) ws xs)" for ws xs
  proof (induction ws arbitrary: xs)
    case (Cons w ws)
    have "set xs - {snd w} \<subseteq> set (ord_remove sort_ord (snd w) xs)" by (rule set_ord_remove) (simp add: sort_ord_EQUAL)
    with Cons.IH[of "ord_remove sort_ord (snd w) xs"] show ?case by auto
  qed simp
  show ?thesis
  proof (cases "S \<in> snd ` set present")
    case True
    then show ?thesis using pin by auto
  next
    case False
    then have "S \<in> set extra" using rem[of shyps present] S by (auto simp: extra_def)
    with ws nwinh show ?thesis by blast
  qed
qed

end

end
section \<open>Correctness of the Occurs Checks\<close>

theory Unify_Occurs
  imports
    Unify_Simpl
    "Pure_Pattern_Correctness.Pattern_Acyclic"
begin

context csig
begin

text \<open>
  \<open>unify.ML\<close> has two occurs checks: \<open>occurs_terms\<close> asks whether a variable \<open>v\<close> occurs in some
  terms modulo the environment, and \<open>rigid_occurs_term\<close> additionally distinguishes rigid
  occurrences. Both follow the bindings of the environment and keep a list \<open>seen\<close> of the
  variables already examined. We relate them to the variables reachable through the bindings
  (\<^const>\<open>reach\<close> of theory \<^theory>\<open>Pure_Pattern_Correctness.Pattern_Acyclic\<close>):

  \<^item> \<^emph>\<open>soundness\<close>: a reported occurrence is a variable \<open>v\<close> reachable from the terms;
  \<^item> \<^emph>\<open>completeness\<close>, for acyclic environments: if no occurrence is reported, \<open>v\<close> is not
    reachable. Then the assignment step of \<open>unify.ML\<close> keeps the environment acyclic.

  Variables are compared by name only, so we speak of the occurrences of \<open>v\<close> at any type.
\<close>

definition occ_in :: "env \<Rightarrow> indexname \<Rightarrow> (indexname \<times> ptyp) set \<Rightarrow> bool" where
  "occ_in env v X \<longleftrightarrow> (\<exists>T. (v, T) \<in> reach env X)"

lemma occ_in_mono: "X \<subseteq> reach env Y \<Longrightarrow> occ_in env v X \<Longrightarrow> occ_in env v Y"
  unfolding occ_in_def using reach_mono by blast

lemma occ_in_Un[simp]: "occ_in env v (X \<union> Y) \<longleftrightarrow> occ_in env v X \<or> occ_in env v Y"
  by (auto simp: occ_in_def reach_Un)

lemma occ_in_self: "occ_in env v {(v, T)}"
  using reach_incl by (fastforce simp: occ_in_def)

lemma lookup_lk:
  assumes "vt_is_empty (tyenv env)" "ok (lookup env w T) r"
  shows "r = lk env w T"
  using ok_lookup[OF assms] by (auto simp: lk_def)

lemma occ_in_lk: "lk env w T = Some u \<Longrightarrow> occ_in env v (vps u) \<Longrightarrow> occ_in env v {(w, T)}"
  using reach_lk by (fastforce simp: occ_in_def)


subsection \<open>Soundness\<close>

lemma occur_sound:
  assumes "occur t env v seen = Some r"
  shows "r = Ok (True, seen') \<Longrightarrow> vt_is_empty (tyenv env) \<Longrightarrow> occ_in env v (vps t)"
  using assms
proof (induction t env v seen r arbitrary: seen' rule: occur.raw_induct[rotated, consumes 1])
  case (1 oc t env v seen r)
  show ?case
  proof (cases t)
    case (Var w T)
    show ?thesis
    proof (cases "w \<in> set seen \<or> v = w")
      case True
      with "1.hyps" "1.prems"(1) Var show ?thesis by (auto simp: occ_in_self split: if_splits)
    next
      case False
      with "1.hyps" "1.prems"(1) Var obtain x where lk: "ok (lookup env w T) x"
        and rest: "(case x of None \<Rightarrow> return (False, w # seen) | Some u \<Rightarrow> oc u env v (w # seen)) = Some r"
        by (auto simp: bindM_def split: option.splits res.splits)
      from lookup_lk[OF "1.prems"(2) lk] have x: "x = lk env w T" .
      show ?thesis
      proof (cases x)
        case None
        with rest "1.prems"(1) show ?thesis by simp
      next
        case (Some u)
        with rest have "oc u env v (w # seen) = Some r" by simp
        from "1.IH"[OF this "1.prems"(1,2)] Some x Var show ?thesis by (simp add: occ_in_lk)
      qed
    qed
  next
    case (Abs a T body)
    with "1.hyps" "1.IH"[of body env v seen r] "1.prems" show ?thesis by simp
  next
    case (App f u)
    with "1.hyps" "1.prems"(1) obtain r1 where u: "oc u env v seen = Some (Ok r1)"
      and rest: "(if fst r1 then return (True, snd r1) else oc f env v (snd r1)) = Some r"
      by (auto simp: bindM_def split: option.splits res.splits)
    show ?thesis
    proof (cases "fst r1")
      case True
      then obtain s1 where "r1 = (True, s1)" by (cases r1) auto
      from "1.IH"[OF u, of s1] this "1.prems"(2) App show ?thesis by simp
    next
      case False
      with rest have "oc f env v (snd r1) = Some r" by simp
      from "1.IH"[OF this "1.prems"(1,2)] App show ?thesis by simp
    qed
  qed (use "1.hyps" "1.prems" in auto)
qed


subsection \<open>Completeness\<close>

text \<open>
  The list \<open>seen\<close> holds the variables already examined: either completely, so that \<open>v\<close> is not
  reachable from them, or partially, if they are on the current path through the bindings (the
  set \<open>P\<close>, with their types). In an acyclic environment the current term cannot reach the
  variables on the path, so skipping them loses no occurrence.
\<close>

definition done_var :: "env \<Rightarrow> indexname \<Rightarrow> indexname \<Rightarrow> bool" where
  "done_var env v w \<longleftrightarrow> (\<forall>T. \<not> occ_in env v {(w, T)})"

definition seen_ok :: "env \<Rightarrow> indexname \<Rightarrow> (indexname \<times> ptyp) set \<Rightarrow> indexname list \<Rightarrow> bool" where
  "seen_ok env v P seen \<longleftrightarrow> (\<forall>w\<in>set seen. w \<in> fst ` P \<or> done_var env v w)"

definition anc_ok :: "env \<Rightarrow> indexname \<Rightarrow> (indexname \<times> ptyp) set \<Rightarrow> (indexname \<times> ptyp) set \<Rightarrow> bool" where
  "anc_ok env v P X \<longleftrightarrow> (\<forall>w T. (w, T) \<in> P \<longrightarrow>
    w \<noteq> v \<and> lk env w T \<noteq> None \<and> reach env X \<subseteq> {y. (y, (w, T)) \<in> (dep env)\<^sup>+})"

lemma anc_ok_mono:
  assumes "X' \<subseteq> reach env X" "anc_ok env v P X"
  shows "anc_ok env v P X'"
proof -
  have "reach env X' \<subseteq> reach env X" by (rule reach_mono[OF assms(1)])
  with assms(2) show ?thesis unfolding anc_ok_def by blast
qed

lemma reach_bound: "lk env w T = Some u \<Longrightarrow> reach env {(w, T)} \<subseteq> insert (w, T) (reach env (vps u))"
proof
  fix y assume lk: "lk env w T = Some u" and "y \<in> reach env {(w, T)}"
  then have "(y, (w, T)) \<in> (dep env)\<^sup>*" by (simp add: reach_def)
  then show "y \<in> insert (w, T) (reach env (vps u))"
  proof (cases rule: rtranclE)
    case (step z)
    with lk have "z \<in> vps u" by (cases z) (auto simp: dep_iff)
    with step(1) show ?thesis by (auto simp: reach_def)
  qed simp
qed

lemma lk_other_type: "lk env w T = Some u \<Longrightarrow> T' \<noteq> T \<Longrightarrow> lk env w T' = None"
  by (auto simp: lk_def split: option.splits if_splits)

lemma not_occ_in_unbound: "lk env w T = None \<Longrightarrow> w \<noteq> v \<Longrightarrow> \<not> occ_in env v {(w, T)}"
  by (simp add: occ_in_def reach_unbound)

lemma not_occ_in_bound:
  assumes "lk env w T = Some u" "w \<noteq> v" "\<not> occ_in env v (vps u)"
  shows "done_var env v w"
  unfolding done_var_def
proof
  fix T'
  show "\<not> occ_in env v {(w, T')}"
  proof (cases "T' = T")
    case True
    with reach_bound[OF assms(1)] assms(2,3) show ?thesis by (auto simp: occ_in_def)
  qed (use lk_other_type[OF assms(1)] not_occ_in_unbound assms(2) in blast)
qed

text \<open>A variable on the current path is never reached again.\<close>

lemma anc_skip:
  assumes "anc_ok env v P {(w, T)}" "w \<in> fst ` P" "acyc env"
  shows "\<not> occ_in env v {(w, T)}"
proof -
  from assms(2) obtain Tw where wP: "(w, Tw) \<in> P" by auto
  with assms(1) have "w \<noteq> v \<and> lk env w Tw \<noteq> None \<and>
      reach env {(w, T)} \<subseteq> {y. (y, (w, Tw)) \<in> (dep env)\<^sup>+}"
    unfolding anc_ok_def by blast
  then have wv: "w \<noteq> v" and lkw: "lk env w Tw \<noteq> None"
    and r: "reach env {(w, T)} \<subseteq> {y. (y, (w, Tw)) \<in> (dep env)\<^sup>+}"
    by simp_all
  show ?thesis
  proof (cases "T = Tw")
    case True
    with r reach_incl[of "{(w, T)}" env] have "((w, Tw), (w, Tw)) \<in> (dep env)\<^sup>+" by auto
    with assms(3) have False unfolding acyc_def acyclic_def by blast
    then show ?thesis ..
  next
    case False
    from lkw obtain u where "lk env w Tw = Some u" by auto
    from lk_other_type[OF this False] wv show ?thesis by (rule not_occ_in_unbound)
  qed
qed

lemma occur_complete:
  assumes "occur t env v seen = Some r"
  shows "r = Ok (False, seen') \<Longrightarrow> vt_is_empty (tyenv env) \<Longrightarrow> acyc env \<Longrightarrow>
    anc_ok env v P (vps t) \<Longrightarrow> seen_ok env v P seen \<Longrightarrow>
    \<not> occ_in env v (vps t) \<and> seen_ok env v P seen'"
  using assms
proof (induction t env v seen r arbitrary: seen' P rule: occur.raw_induct[rotated, consumes 1])
  case (1 oc t env v seen r)
  note ok = "1.prems"(1) and e = "1.prems"(2) and ac = "1.prems"(3)
    and anc = "1.prems"(4) and sn = "1.prems"(5)
  show ?case
  proof (cases t)
    case (Var w T)
    show ?thesis
    proof (cases "w \<in> set seen")
      case True
      with "1.hyps" ok Var have s': "seen' = seen" by simp
      from True sn consider "w \<in> fst ` P" | "done_var env v w" by (auto simp: seen_ok_def)
      then have "\<not> occ_in env v {(w, T)}"
      proof cases
        case 1
        from anc_skip[OF _ this ac] anc Var show ?thesis by simp
      qed (simp add: done_var_def)
      with s' sn Var show ?thesis by simp
    next
      case False
      show ?thesis
      proof (cases "v = w")
        case True
        with False "1.hyps" ok Var show ?thesis by simp
      next
        case vw0: False
        then have vw: "w \<noteq> v" by simp
        with False "1.hyps" ok Var obtain x where lkp: "ok (lookup env w T) x"
          and rest: "(case x of None \<Rightarrow> return (False, w # seen)
            | Some u \<Rightarrow> oc u env v (w # seen)) = Some r"
          by (auto simp: bindM_def split: option.splits res.splits)
        from lookup_lk[OF e lkp] have x: "x = lk env w T" .
        show ?thesis
        proof (cases x)
          case None
          with rest ok have s': "seen' = w # seen" by simp
          from ok_lookup[OF e lkp] None have "vt_lookup (tenv env) w = None" by simp
          then have lkN: "lk env w T' = None" for T' by (simp add: lk_def)
          have dw: "done_var env v w"
            unfolding done_var_def using not_occ_in_unbound[OF lkN vw] by blast
          then have "\<not> occ_in env v {(w, T)}" by (simp add: done_var_def)
          with dw sn s' Var show ?thesis by (auto simp: seen_ok_def)
        next
          case (Some u)
          with rest have rec: "oc u env v (w # seen) = Some r" by simp
          from Some x have lku: "lk env w T = Some u" by simp
          let ?P = "insert (w, T) P"
          have anc': "anc_ok env v ?P (vps u)"
          proof -
            have "reach env (vps u) \<subseteq> {y. (y, (w, T)) \<in> (dep env)\<^sup>+}"
              using reach_lk_trancl[OF lku] by blast
            moreover have "anc_ok env v P (vps u)"
            proof (rule anc_ok_mono[OF _ anc])
              show "vps u \<subseteq> reach env (vps t)"
                using reach_incl[of "vps u" env] reach_lk[OF lku] Var by auto
            qed
            ultimately show ?thesis using vw lku by (auto simp: anc_ok_def)
          qed
          have sn': "seen_ok env v ?P (w # seen)" using sn by (auto simp: seen_ok_def)
          from "1.IH"[OF rec ok e ac anc' sn']
          have nu: "\<not> occ_in env v (vps u)" and s'': "seen_ok env v ?P seen'" by simp_all
          have dw: "done_var env v w" by (rule not_occ_in_bound[OF lku vw nu])
          then have "\<not> occ_in env v {(w, T)}" by (simp add: done_var_def)
          moreover have "seen_ok env v P seen'" using s'' dw by (auto simp: seen_ok_def)
          ultimately show ?thesis using Var by simp
        qed
      qed
    qed
  next
    case (Abs a T body)
    with "1.hyps" "1.IH"[of body env v seen r] "1.prems" show ?thesis by simp
  next
    case (App f u)
    with "1.hyps" ok obtain r1 where u: "oc u env v seen = Some (Ok r1)"
      and rest: "(if fst r1 then return (True, snd r1) else oc f env v (snd r1)) = Some r"
      by (auto simp: bindM_def split: option.splits res.splits)
    from rest ok obtain s1 where r1: "r1 = (False, s1)" and f: "oc f env v s1 = Some r"
      by (cases r1) (auto split: if_splits)
    have "vps u \<subseteq> reach env (vps t)" "vps f \<subseteq> reach env (vps t)"
      using reach_incl[of "vps t" env] App by auto
    then have ancu: "anc_ok env v P (vps u)" and ancf: "anc_ok env v P (vps f)"
      using anc_ok_mono anc by blast+
    from "1.IH"[OF u[unfolded r1] _ e ac ancu sn]
    have nu: "\<not> occ_in env v (vps u)" and s1: "seen_ok env v P s1" by simp_all
    from "1.IH"[OF f ok e ac ancf s1] nu App show ?thesis by simp
  qed (use "1.hyps" "1.prems" in \<open>auto simp: occ_in_def reach_def\<close>)
qed


subsection \<open>\<open>occurs_terms\<close>\<close>

abbreviation vps_list :: "pterm list \<Rightarrow> (indexname \<times> ptyp) set" where
  "vps_list ts \<equiv> \<Union> (vps ` set ts)"

lemma occurs_list_sound:
  "ok (occurs_list env v seen ts) (True, seen') \<Longrightarrow> vt_is_empty (tyenv env) \<Longrightarrow>
    occ_in env v (vps_list ts)"
proof (induction ts arbitrary: seen)
  case (Cons t ts)
  from Cons.prems(1) obtain r where o: "ok (occur t env v seen) r"
    and rest: "ok (if fst r then return (True, snd r) else occurs_list env v (snd r) ts) (True, seen')"
    by auto
  show ?case
  proof (cases "fst r")
    case True
    then obtain s where "r = (True, s)" by (cases r) auto
    from occur_sound[OF o[unfolded this] refl Cons.prems(2)] show ?thesis by simp
  next
    case False
    with rest Cons.IH Cons.prems(2) show ?thesis by simp
  qed
qed simp

lemma occurs_list_complete:
  "ok (occurs_list env v seen ts) (False, seen') \<Longrightarrow> vt_is_empty (tyenv env) \<Longrightarrow> acyc env \<Longrightarrow>
    anc_ok env v P (vps_list ts) \<Longrightarrow> seen_ok env v P seen \<Longrightarrow>
    \<not> occ_in env v (vps_list ts) \<and> seen_ok env v P seen'"
proof (induction ts arbitrary: seen)
  case (Cons t ts)
  from Cons.prems(1) obtain r where o: "ok (occur t env v seen) r"
    and rest: "ok (if fst r then return (True, snd r) else occurs_list env v (snd r) ts) (False, seen')"
    by auto
  from rest obtain s where r: "r = (False, s)" and ts: "ok (occurs_list env v s ts) (False, seen')"
    by (cases r) (auto split: if_splits)
  have s1: "vps t \<subseteq> reach env (vps_list (t # ts))" and s2: "vps_list ts \<subseteq> reach env (vps_list (t # ts))"
    using reach_incl[of "vps_list (t # ts)" env] by auto
  have at: "anc_ok env v P (vps t)" by (rule anc_ok_mono[OF s1 Cons.prems(4)])
  have ats: "anc_ok env v P (vps_list ts)" by (rule anc_ok_mono[OF s2 Cons.prems(4)])
  from occur_complete[OF o[unfolded r] refl Cons.prems(2,3) at Cons.prems(5)]
  have "\<not> occ_in env v (vps t)" "seen_ok env v P s" by simp_all
  with Cons.IH[OF ts Cons.prems(2,3) ats] show ?case by simp
qed (simp add: occ_in_def reach_def)

theorem occurs_terms_correct:
  assumes "vt_is_empty (tyenv env)" "acyc env" "ok (occurs_terms env v ts) b"
  shows "b \<longleftrightarrow> occ_in env v (vps_list ts)"
proof -
  from assms(3) obtain s where o: "ok (occurs_list env v [] ts) (b, s)"
    by (auto simp: occurs_terms_def)
  show ?thesis
  proof (cases b)
    case True
    with o have "ok (occurs_list env v [] ts) (True, s)" by simp
    from occurs_list_sound[OF this assms(1)] True show ?thesis by simp
  next
    case False
    with o have o': "ok (occurs_list env v [] ts) (False, s)" by simp
    have "anc_ok env v {} (vps_list ts)" "seen_ok env v {} []"
      by (simp_all add: anc_ok_def seen_ok_def)
    from occurs_list_complete[OF o' assms(1,2) this] False show ?thesis by simp
  qed
qed


subsection \<open>The rigid occurs check\<close>

lemma head_of_in_Var:
  assumes "head_of_in env t = Some r"
  shows "r = Ok (Var w T) \<Longrightarrow> vt_is_empty (tyenv env) \<Longrightarrow> (w, T) \<in> reach env (vps t)"
  using assms
proof (induction env t r rule: head_of_in.raw_induct[rotated, consumes 1])
  case (1 hd env t r)
  show ?case
  proof (cases t)
    case (App f u)
    with "1.hyps" "1.IH"[of env f r] "1.prems" reach_subset[of "vps f" "vps t" env] show ?thesis
      by auto
  next
    case (Var x U)
    with "1.hyps" "1.prems"(1) obtain y where lkp: "ok (lookup env x U) y"
      and rest: "(case y of Some u \<Rightarrow> hd env u | None \<Rightarrow> return t) = Some r"
      by (auto simp: bindM_def split: option.splits res.splits)
    from lookup_lk[OF "1.prems"(2) lkp] have y: "y = lk env x U" .
    show ?thesis
    proof (cases y)
      case None
      with rest "1.prems"(1) Var show ?thesis by (auto simp: reach_def)
    next
      case (Some u)
      with rest have "hd env u = Some r" by simp
      from "1.IH"[OF this "1.prems"] reach_lk[of env x U u] Some y Var show ?thesis by auto
    qed
  qed (use "1.hyps" "1.prems" in \<open>auto simp: reach_def\<close>)
qed

lemma nonrigid_cases:
  assumes "ok (nonrigid env v seen t) (oc, seen')"
  shows "\<exists>b. ok (occurs_list env v seen [t]) (b, seen') \<and> oc = (if b then Nonrigid else NoOcc)"
proof -
  from assms obtain x where x: "ok (occurs_list env v seen [t]) x"
    and r: "ok (case x of (b, s) \<Rightarrow> return (if b then Nonrigid else NoOcc, s)) (oc, seen')"
    unfolding nonrigid_def ok_bindM by blast
  obtain b s where "x = (b, s)" by (cases x)
  with x r show ?thesis by (auto simp del: occurs_list.simps)
qed

lemma nonrigid_sound:
  assumes "ok (nonrigid env v seen t) (oc, seen')" "oc \<noteq> NoOcc" "vt_is_empty (tyenv env)"
  shows "occ_in env v (vps t)"
proof -
  from nonrigid_cases[OF assms(1)] assms(2) have "ok (occurs_list env v seen [t]) (True, seen')"
    by (auto split: if_splits simp del: occurs_list.simps)
  from occurs_list_sound[OF this assms(3)] show ?thesis by simp
qed

lemma nonrigid_complete:
  assumes "ok (nonrigid env v seen t) (NoOcc, seen')" "vt_is_empty (tyenv env)" "acyc env"
    "anc_ok env v P (vps t)" "seen_ok env v P seen"
  shows "\<not> occ_in env v (vps t) \<and> seen_ok env v P seen'"
proof -
  from nonrigid_cases[OF assms(1)] have o: "ok (occurs_list env v seen [t]) (False, seen')"
    by (auto split: if_splits simp del: occurs_list.simps)
  from assms(4) have "anc_ok env v P (vps_list [t])" by simp
  from occurs_list_complete[OF o assms(2,3) this assms(5)] show ?thesis by simp
qed

lemma occomb_sound:
  assumes hyp: "\<And>seen t' r s. oc seen t' = Some (Ok (r, s)) \<Longrightarrow> r \<noteq> NoOcc \<Longrightarrow> occ_in env v (vps t')"
  shows "occomb oc seen t = Some (Ok (r, s)) \<Longrightarrow> r \<noteq> NoOcc \<Longrightarrow> occ_in env v (vps t)"
proof (induction t arbitrary: seen r s)
  case (App f t)
  from App.prems(1) obtain r1 where r1: "oc seen t = Some (Ok r1)"
    and rest: "ok (if fst r1 = Rigid then return (Rigid, snd r1)
      else occomb oc (snd r1) f \<bind> (\<lambda>r2. return (if fst r2 = NoOcc then fst r1 else fst r2, snd r2)))
      (r, s)"
    by auto
  show ?case
  proof (cases "fst r1 = Rigid")
    case True
    with hyp[of seen t "fst r1" "snd r1"] r1 show ?thesis by (simp add: prod_eq_iff)
  next
    case False
    with rest obtain r2 where r2: "occomb oc (snd r1) f = Some (Ok r2)"
      and r: "r = (if fst r2 = NoOcc then fst r1 else fst r2)" by auto
    show ?thesis
    proof (cases "fst r2 = NoOcc")
      case True
      with r hyp[of seen t "fst r1" "snd r1"] r1 App.prems(2) show ?thesis by simp
    next
      case False
      with App.IH(1)[of "snd r1" "fst r2" "snd r2"] r2 show ?thesis by simp
    qed
  qed
next
  case (Const a T)
  then show ?case using hyp[of seen "Const a T" r s] by simp
next
  case (Free a T)
  then show ?case using hyp[of seen "Free a T" r s] by simp
next
  case (Var x T)
  then show ?case using hyp[of seen "Var x T" r s] by simp
next
  case (Bound i)
  then show ?case using hyp[of seen "Bound i" r s] by simp
next
  case (Abs a T b)
  then show ?case using hyp[of seen "Abs a T b" r s] by simp
qed

lemma occomb_complete:
  assumes hyp: "\<And>seen t' s P. oc seen t' = Some (Ok (NoOcc, s)) \<Longrightarrow> anc_ok env v P (vps t') \<Longrightarrow>
      seen_ok env v P seen \<Longrightarrow> \<not> occ_in env v (vps t') \<and> seen_ok env v P s"
  shows "occomb oc seen t = Some (Ok (NoOcc, s)) \<Longrightarrow> anc_ok env v P (vps t) \<Longrightarrow>
    seen_ok env v P seen \<Longrightarrow> \<not> occ_in env v (vps t) \<and> seen_ok env v P s"
proof (induction t arbitrary: seen s)
  case (App f t)
  from App.prems(1) obtain r1 where r1: "oc seen t = Some (Ok r1)"
    and rest: "ok (if fst r1 = Rigid then return (Rigid, snd r1)
      else occomb oc (snd r1) f \<bind> (\<lambda>r2. return (if fst r2 = NoOcc then fst r1 else fst r2, snd r2)))
      (NoOcc, s)"
    by auto
  from rest have nr: "fst r1 = NoOcc" and r2: "occomb oc (snd r1) f = Some (Ok (NoOcc, s))"
    by (auto split: if_splits)
  have st: "vps t \<subseteq> reach env (vps (f $ t))" and sf: "vps f \<subseteq> reach env (vps (f $ t))"
    using reach_incl[of "vps (f $ t)" env] by auto
  have at: "anc_ok env v P (vps t)" by (rule anc_ok_mono[OF st App.prems(2)])
  have af: "anc_ok env v P (vps f)" by (rule anc_ok_mono[OF sf App.prems(2)])
  from r1 nr have "oc seen t = Some (Ok (NoOcc, snd r1))" by (cases r1) simp
  from hyp[OF this at App.prems(3)]
  have "\<not> occ_in env v (vps t)" "seen_ok env v P (snd r1)" by simp_all
  with App.IH(1)[OF r2 af] show ?case by simp
next
  case (Const a T)
  then show ?case using hyp[of seen "Const a T" s P] by simp
next
  case (Free a T)
  then show ?case using hyp[of seen "Free a T" s P] by simp
next
  case (Var x T)
  then show ?case using hyp[of seen "Var x T" s P] by simp
next
  case (Bound i)
  then show ?case using hyp[of seen "Bound i" s P] by simp
next
  case (Abs a T b)
  then show ?case using hyp[of seen "Abs a T b" s P] by simp
qed

lemma rocc_sound:
  assumes "rocc t env v seen = Some r"
  shows "r = Ok (oc, seen') \<Longrightarrow> oc \<noteq> NoOcc \<Longrightarrow> vt_is_empty (tyenv env) \<Longrightarrow> occ_in env v (vps t)"
  using assms
proof (induction t env v seen r arbitrary: oc seen' rule: rocc.raw_induct[rotated, consumes 1])
  case (1 R t env v seen r)
  note ok = "1.prems"(1) and nn = "1.prems"(2) and e = "1.prems"(3)
  have IH: "occ_in env v (vps t')" if "R t' env v s = Some (Ok (oc', s'))" "oc' \<noteq> NoOcc" for t' s oc' s'
    using "1.IH"[OF that(1) refl that(2) e] .
  show ?case
  proof (cases t)
    case (Var w T)
    show ?thesis
    proof (cases "w \<in> set seen \<or> v = w")
      case True
      with "1.hyps" ok nn Var show ?thesis by (auto simp: occ_in_self split: if_splits)
    next
      case False
      with "1.hyps" ok Var obtain x where lkp: "ok (lookup env w T) x"
        and rest: "(case x of None \<Rightarrow> return (NoOcc, w # seen) | Some u \<Rightarrow> R u env v (w # seen)) = Some r"
        by (auto simp: bindM_def split: option.splits res.splits)
      from lookup_lk[OF e lkp] have x: "x = lk env w T" .
      show ?thesis
      proof (cases x)
        case None
        with rest ok nn show ?thesis by simp
      next
        case (Some u)
        with rest ok have "R u env v (w # seen) = Some (Ok (oc, seen'))" by simp
        from IH[OF this nn] Some x Var show ?thesis by (simp add: occ_in_lk)
      qed
    qed
  next
    case (Abs a T body)
    with "1.hyps" ok IH[of body seen oc seen'] nn show ?thesis by simp
  next
    case (App f u)
    with "1.hyps" ok obtain h where hd: "ok (head_of_in env f) h"
      and rest: "(case h of
          Var w _ \<Rightarrow> if v = w \<and> pattern_occ v t then return (Rigid, seen) else nonrigid env v seen t
        | Abs _ _ _ \<Rightarrow> nonrigid env v seen t
        | _ \<Rightarrow> occomb (\<lambda>seen t. R t env v seen) seen t) = Some (Ok (oc, seen'))"
      by (auto simp: bindM_def simp del: occomb.simps split: option.splits res.splits)
    have sub: "vps f \<subseteq> vps t" using App by auto
    have occ: "occ_in env v (vps t)"
      if "occomb (\<lambda>seen t. R t env v seen) seen t = Some (Ok (oc, seen'))"
      using occomb_sound[where oc = "\<lambda>seen t. R t env v seen", OF IH that nn] .
    show ?thesis
    proof (cases h)
      case (Var w T')
      show ?thesis
      proof (cases "v = w \<and> pattern_occ v t")
        case True
        from head_of_in_Var[OF hd[unfolded Var] refl e] True
        have of: "occ_in env v (vps f)" by (auto simp: occ_in_def)
        have "vps f \<subseteq> reach env (vps t)" using subset_trans[OF sub reach_incl] .
        from occ_in_mono[OF this of] show ?thesis .
      next
        case False
        with rest Var have "ok (nonrigid env v seen t) (oc, seen')" by simp
        from nonrigid_sound[OF this nn e] show ?thesis .
      qed
    next
      case (Abs a T b)
      with rest have "ok (nonrigid env v seen t) (oc, seen')" by simp
      from nonrigid_sound[OF this nn e] show ?thesis .
    qed (use rest occ in \<open>auto simp del: occomb.simps\<close>)
  qed (use "1.hyps" ok nn in auto)
qed

lemma rocc_complete:
  assumes "rocc t env v seen = Some r"
  shows "r = Ok (NoOcc, seen') \<Longrightarrow> vt_is_empty (tyenv env) \<Longrightarrow> acyc env \<Longrightarrow>
    anc_ok env v P (vps t) \<Longrightarrow> seen_ok env v P seen \<Longrightarrow>
    \<not> occ_in env v (vps t) \<and> seen_ok env v P seen'"
  using assms
proof (induction t env v seen r arbitrary: seen' P rule: rocc.raw_induct[rotated, consumes 1])
  case (1 R t env v seen r)
  note ok = "1.prems"(1) and e = "1.prems"(2) and ac = "1.prems"(3)
    and anc = "1.prems"(4) and sn = "1.prems"(5)
  have IH: "\<not> occ_in env v (vps t') \<and> seen_ok env v Q s'"
    if "R t' env v s = Some (Ok (NoOcc, s'))" "anc_ok env v Q (vps t')" "seen_ok env v Q s"
    for t' s s' Q
    using "1.IH"[OF that(1) refl e ac that(2,3)] .
  show ?case
  proof (cases t)
    case (Var w T)
    show ?thesis
    proof (cases "w \<in> set seen")
      case True
      with "1.hyps" ok Var have s': "seen' = seen" by simp
      from True sn consider "w \<in> fst ` P" | "done_var env v w" by (auto simp: seen_ok_def)
      then have "\<not> occ_in env v {(w, T)}"
      proof cases
        case 1
        from anc_skip[OF _ this ac] anc Var show ?thesis by simp
      qed (simp add: done_var_def)
      with s' sn Var show ?thesis by simp
    next
      case False
      show ?thesis
      proof (cases "v = w")
        case True
        with False "1.hyps" ok Var show ?thesis by simp
      next
        case vw0: False
        then have vw: "w \<noteq> v" by simp
        with False "1.hyps" ok Var obtain x where lkp: "ok (lookup env w T) x"
          and rest: "(case x of None \<Rightarrow> return (NoOcc, w # seen)
            | Some u \<Rightarrow> R u env v (w # seen)) = Some r"
          by (auto simp: bindM_def split: option.splits res.splits)
        from lookup_lk[OF e lkp] have x: "x = lk env w T" .
        show ?thesis
        proof (cases x)
          case None
          with rest ok have s': "seen' = w # seen" by simp
          from ok_lookup[OF e lkp] None have "vt_lookup (tenv env) w = None" by simp
          then have lkN: "lk env w T' = None" for T' by (simp add: lk_def)
          have dw: "done_var env v w"
            unfolding done_var_def using not_occ_in_unbound[OF lkN vw] by blast
          then have "\<not> occ_in env v {(w, T)}" by (simp add: done_var_def)
          with dw sn s' Var show ?thesis by (auto simp: seen_ok_def)
        next
          case (Some u)
          with rest ok have rec: "R u env v (w # seen) = Some (Ok (NoOcc, seen'))" by simp
          from Some x have lku: "lk env w T = Some u" by simp
          let ?P = "insert (w, T) P"
          have anc': "anc_ok env v ?P (vps u)"
          proof -
            have "reach env (vps u) \<subseteq> {y. (y, (w, T)) \<in> (dep env)\<^sup>+}"
              using reach_lk_trancl[OF lku] by blast
            moreover have "anc_ok env v P (vps u)"
            proof (rule anc_ok_mono[OF _ anc])
              show "vps u \<subseteq> reach env (vps t)"
                using reach_incl[of "vps u" env] reach_lk[OF lku] Var by auto
            qed
            ultimately show ?thesis using vw lku by (auto simp: anc_ok_def)
          qed
          have sn': "seen_ok env v ?P (w # seen)" using sn by (auto simp: seen_ok_def)
          from IH[OF rec anc' sn']
          have nu: "\<not> occ_in env v (vps u)" and s'': "seen_ok env v ?P seen'" by simp_all
          have dw: "done_var env v w" by (rule not_occ_in_bound[OF lku vw nu])
          then have "\<not> occ_in env v {(w, T)}" by (simp add: done_var_def)
          moreover have "seen_ok env v P seen'" using s'' dw by (auto simp: seen_ok_def)
          ultimately show ?thesis using Var by simp
        qed
      qed
    qed
  next
    case (Abs a T body)
    with "1.hyps" ok anc sn IH[of body seen seen' P] show ?thesis by simp
  next
    case (App f u)
    with "1.hyps" ok obtain h where hd: "ok (head_of_in env f) h"
      and rest: "(case h of
          Var w _ \<Rightarrow> if v = w \<and> pattern_occ v t then return (Rigid, seen) else nonrigid env v seen t
        | Abs _ _ _ \<Rightarrow> nonrigid env v seen t
        | _ \<Rightarrow> occomb (\<lambda>seen t. R t env v seen) seen t) = Some (Ok (NoOcc, seen'))"
      by (auto simp: bindM_def simp del: occomb.simps split: option.splits res.splits)
    have occ: "\<not> occ_in env v (vps t) \<and> seen_ok env v P seen'"
      if "occomb (\<lambda>seen t. R t env v seen) seen t = Some (Ok (NoOcc, seen'))"
      using occomb_complete[where oc = "\<lambda>seen t. R t env v seen", OF IH that anc sn] .
    show ?thesis
    proof (cases h)
      case (Var w T')
      with rest have "ok (nonrigid env v seen t) (NoOcc, seen')" by (auto split: if_splits)
      from nonrigid_complete[OF this e ac anc sn] show ?thesis .
    next
      case (Abs a T b)
      with rest have "ok (nonrigid env v seen t) (NoOcc, seen')" by simp
      from nonrigid_complete[OF this e ac anc sn] show ?thesis .
    qed (use rest occ in \<open>auto simp del: occomb.simps\<close>)
  qed (use "1.hyps" ok sn in \<open>auto simp: occ_in_def reach_def\<close>)
qed

theorem rigid_occurs_term_sound:
  assumes "ok (rigid_occurs_term env v u) oc" "oc \<noteq> NoOcc" "vt_is_empty (tyenv env)"
  shows "occ_in env v (vps u)"
proof -
  from assms(1) obtain s where "ok (rocc u env v []) (oc, s)"
    by (auto simp: rigid_occurs_term_def)
  from rocc_sound[OF this refl assms(2,3)] show ?thesis .
qed

theorem rigid_occurs_term_complete:
  assumes "ok (rigid_occurs_term env v u) NoOcc" "vt_is_empty (tyenv env)" "acyc env"
  shows "\<not> occ_in env v (vps u)"
proof -
  from assms(1) obtain s where "ok (rocc u env v []) (NoOcc, s)"
    by (auto simp: rigid_occurs_term_def)
  moreover have "anc_ok env v {} (vps u)" "seen_ok env v {} []"
    by (simp_all add: anc_ok_def seen_ok_def)
  ultimately show ?thesis using rocc_complete[OF _ refl assms(2,3)] by blast
qed


subsection \<open>Assignments keep environments acyclic\<close>

lemma vps_rlist_abs: "vps (rlist_abs rb t) = vps t"
proof (induction rb arbitrary: t)
  case (Cons aT rb)
  obtain a T where "aT = (a, T)" by (cases aT)
  with Cons.IH[of "Abs a T t"] show ?case by simp
qed simp

theorem assignment_acyc:
  assumes "okW (assignment alg rb t u env) env'" "wf_env ar env" "wf_dp ar (rb, t, u)" "acyc env"
  shows "acyc env'"
proof -
  have e: "vt_is_empty (tyenv env)" by (rule wf_envD(1)[OF assms(2)])
  have bok: "binders_ok ar rb" and wt: "wf_tm ar rb t" and wu: "wf_tm ar rb u"
    using assms(3) by simp_all
  from assms(1) obtain v T oc where gev: "okW (get_eta_var rb 0 t) (v, T)"
    and oc: "ok (rigid_occurs_term env v u) oc"
    and rest: "okW (case oc of
        NoOcc \<Rightarrow> do {T1 \<leftarrow> liftM (body_type env T); T2 \<leftarrow> liftM (fastype env rb u);
          env' \<leftarrow> cunify_types alg T1 T2 env; liftM (update (v, T) (rlist_abs rb u) env')}
      | Nonrigid \<Rightarrow> raiseW ASSIGN | Rigid \<Rightarrow> raiseW CANTUNIFY) env'"
    by (auto simp: assignment_def)
  from rest have noocc: "oc = NoOcc" by (cases oc) auto
  with rest obtain T1 T2 env1 where b: "ok (body_type env T) T1" and f: "ok (fastype env rb u) T2"
    and cu: "okW (cunify_types alg T1 T2 env) env1"
    and upd: "ok (update (v, T) (rlist_abs rb u) env1) env'"
    by auto
  have gT: "ground ar T" using get_eta_var_ground[OF gev] wt by (simp add: wf_tm_def)
  have "ground ar T1" by (rule body_type_ground[OF e gT b])
  moreover have "ground ar T2" using fastype_ground[OF e bok _ f] wu by (simp add: wf_tm_def)
  ultimately have e1: "env1 = env" using cunify_types_ground cu by blast
  note up = ok_update[OF upd[unfolded e1]]
  have d: "dep env' = dep env \<union> (\<lambda>y. (y, (v, T))) ` vps (rlist_abs rb u)"
    by (rule dep_update[OF up(2,1)])
  from rigid_occurs_term_complete[OF oc[unfolded noocc] e assms(4)]
  have "(v, T) \<notin> reach env (vps (rlist_abs rb u))" by (auto simp: occ_in_def vps_rlist_abs)
  from acyclic_update[OF d this] assms(4) show ?thesis by (simp add: acyc_def)
qed

end

end

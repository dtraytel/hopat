section \<open>The Syntax of Lifted Rules and Proof States\<close>

theory Bicompose_Syntax
  imports Bicompose_Monad
begin

text \<open>
  A rule is lifted over a subgoal \<open>Bi\<close> by putting the parameters and assumptions of \<open>Bi\<close> in
  front of each of its premises and of its conclusion (\<open>Thm.lift_rule\<close>). We describe the
  common prefix by a list of items: an assumption \<open>c $ H $ _\<close> or a parameter
  \<open>c $ Abs a T _\<close>, where \<open>c\<close> is the respective constant of \<open>Bi\<close>. The functions
  \<^const>\<open>strip_assums2\<close>, \<^const>\<open>strip_apply\<close> and \<^const>\<open>strip_lifted\<close> of \<open>thm.ML\<close> strip off
  such prefixes.
\<close>


subsection \<open>Prefixes\<close>

datatype litem = LImp pterm pterm | LAll pterm name ptyp

fun lift_pre :: "litem list \<Rightarrow> pterm \<Rightarrow> pterm" where
  "lift_pre [] t = t"
| "lift_pre (LImp c H # p) t = c $ H $ lift_pre p t"
| "lift_pre (LAll c a T # p) t = c $ Abs a T (lift_pre p t)"

fun litem_ok :: "litem \<Rightarrow> bool" where
  "litem_ok (LImp c H) \<longleftrightarrow> (\<exists>U. c = Const STR ''Pure.imp'' U)"
| "litem_ok (LAll c a T) \<longleftrightarrow> (\<exists>U. c = Const STR ''Pure.all'' U)"

text \<open>Neither an implication nor a universal quantification (at the top).\<close>

definition atomic :: "pterm \<Rightarrow> bool" where
  "atomic t \<longleftrightarrow> dest_imp t = None \<and> dest_all t = None"

text \<open>The prefix of a subgoal: all its parameters and assumptions.\<close>

fun fun_of :: "pterm \<Rightarrow> pterm" where
  "fun_of (f $ _) = f"
| "fun_of t = t"

function lsplit :: "pterm \<Rightarrow> litem list \<times> pterm" where
  "lsplit t =
    (case dest_imp t of
      Some (H, B) \<Rightarrow> (case lsplit B of (p, t0) \<Rightarrow> (LImp (fun_of (fun_of t)) H # p, t0))
    | None \<Rightarrow>
      (case dest_all t of
        Some (a, T, b) \<Rightarrow> (case lsplit b of (p, t0) \<Rightarrow> (LAll (fun_of t) a T # p, t0))
      | None \<Rightarrow> ([], t)))"
  by auto
termination by (relation "measure size") (auto dest: dest_size)

declare lsplit.simps[simp del]

lemma dest_imp_lift_pre[simp]:
  "litem_ok i \<Longrightarrow> dest_imp (lift_pre (i # p) t) = (case i of LImp c H \<Rightarrow> Some (H, lift_pre p t) | _ \<Rightarrow> None)"
  by (cases i) auto

lemma dest_all_lift_pre[simp]:
  "litem_ok i \<Longrightarrow> dest_all (lift_pre (i # p) t) = (case i of LAll c a T \<Rightarrow> Some (a, T, lift_pre p t) | _ \<Rightarrow> None)"
  by (cases i) auto

lemma lsplit_lift_pre:
  assumes "\<forall>i\<in>set p. litem_ok i" "atomic t"
  shows "lsplit (lift_pre p t) = (p, t)"
  using assms
proof (induction p)
  case Nil
  then show ?case by (subst lsplit.simps) (simp add: atomic_def)
next
  case (Cons i p)
  then show ?case
    by (cases i) (subst lsplit.simps; auto)+
qed

lemma lsplit_ok:
  assumes "lsplit t = (p, t0)"
  shows "t = lift_pre p t0 \<and> (\<forall>i\<in>set p. litem_ok i) \<and> atomic t0"
  using assms
proof (induction t arbitrary: p t0 rule: measure_induct_rule[of size])
  case (less t)
  show ?case
  proof (cases "dest_imp t")
    case (Some HB)
    then obtain H B where HB: "HB = (H, B)" by (cases HB)
    with Some obtain U where t: "t = Const STR ''Pure.imp'' U $ H $ B" by (auto simp: dest_imp_Some)
    obtain q b0 where q: "lsplit B = (q, b0)" by (cases "lsplit B")
    from less.prems q t have "p = LImp (Const STR ''Pure.imp'' U) H # q" "t0 = b0"
      by (subst (asm) lsplit.simps; simp)+
    with less.IH[of B q b0] t q show ?thesis by simp
  next
    case None
    show ?thesis
    proof (cases "dest_all t")
      case (Some aTb)
      then obtain a T b where aTb: "aTb = (a, T, b)" by (cases aTb)
      with Some obtain U where t: "t = Const STR ''Pure.all'' U $ Abs a T b" by (auto simp: dest_all_Some)
      obtain q b0 where q: "lsplit b = (q, b0)" by (cases "lsplit b")
      from less.prems q t have "p = LAll (Const STR ''Pure.all'' U) a T # q" "t0 = b0"
        by (subst (asm) lsplit.simps; simp)+
      with less.IH[of b q b0] t q show ?thesis by simp
    next
      case None': None
      with None less.prems have "p = []" "t0 = t"
        by (subst (asm) lsplit.simps; simp)+
      with None None' show ?thesis by (simp add: atomic_def)
    qed
  qed
qed

lemma lsplit_lift_pre_iff:
  "lsplit t = (p, t0) \<longleftrightarrow> t = lift_pre p t0 \<and> (\<forall>i\<in>set p. litem_ok i) \<and> atomic t0"
  using lsplit_ok lsplit_lift_pre by blast

lemma lift_pre_append: "lift_pre (p @ q) t = lift_pre p (lift_pre q t)"
  by (induction p t rule: lift_pre.induct) auto

lemma atomic_lift_pre:
  assumes "\<forall>i\<in>set p. litem_ok i"
  shows "atomic (lift_pre p t) \<longleftrightarrow> p = [] \<and> atomic t"
proof (cases p)
  case (Cons i q)
  with assms show ?thesis by (cases i) (auto simp: atomic_def)
qed simp


subsection \<open>Premises\<close>

text \<open>Premises stripped by \<^const>\<open>strip_prems\<close> form a prefix of assumptions.\<close>

fun is_limp :: "litem \<Rightarrow> bool" where
  "is_limp (LImp _ _) = True"
| "is_limp _ = False"

fun lhyp :: "litem \<Rightarrow> pterm" where
  "lhyp (LImp _ H) = H"
| "lhyp (LAll _ _ T) = Bound 0"

lemma strip_prems_ok:
  "ok (strip_prems i As B) (As', B') \<Longrightarrow>
    \<exists>p. B = lift_pre p B' \<and> (\<forall>it\<in>set p. is_limp it \<and> litem_ok it) \<and>
      As' = rev (map lhyp p) @ As \<and> nat_of_integer i = length p \<and> 0 \<le> i"
proof (induction i As B rule: strip_prems.induct)
  case (1 i As B)
  show ?case
  proof (cases "i = 0")
    case True
    with "1.prems" show ?thesis by (subst (asm) strip_prems.simps) (auto intro!: exI[of _ "[]"])
  next
    case False
    then show ?thesis
    proof (cases "dest_imp B")
      case (Some AB)
      then obtain A B1 where AB: "AB = (A, B1)" by (cases AB)
      with Some obtain U where B: "B = Const STR ''Pure.imp'' U $ A $ B1" by (auto simp: dest_imp_Some)
      from "1.prems" False Some AB have r: "ok (strip_prems (i - 1) (A # As) B1) (As', B')"
        by (subst (asm) strip_prems.simps) simp
      from "1.IH"[OF False Some AB[symmetric] r] obtain p where
        p: "B1 = lift_pre p B'" "\<forall>it\<in>set p. is_limp it \<and> litem_ok it"
          "As' = rev (map lhyp p) @ A # As" "nat_of_integer (i - 1) = length p" "0 \<le> i - 1"
        by blast
      have "nat_of_integer i = Suc (length p)" "0 \<le> i"
        using p(4,5) False by (simp_all add: integer_reps)
      with p B show ?thesis
        by (intro exI[of _ "LImp (Const STR ''Pure.imp'' U) A # p"]) simp
    next
      case None
      with "1.prems" False show ?thesis by (subst (asm) strip_prems.simps) simp
    qed
  qed
qed


subsection \<open>Stripping lifted prefixes\<close>

text \<open>Abstractions over the parameters of a prefix, as built by \<^const>\<open>strip_assums2\<close>.\<close>

fun abs_pre :: "litem list \<Rightarrow> pterm \<Rightarrow> pterm" where
  "abs_pre [] t = t"
| "abs_pre (LImp c H # p) t = abs_pre p t"
| "abs_pre (LAll c a T # p) t = Abs a T (abs_pre p t)"

lemma strip_assums2_lift_pre:
  assumes "\<forall>i\<in>set p. litem_ok i" "atomic Bi0"
  shows "strip_assums2 (lift_pre p B0) (lift_pre p Bi0) = (abs_pre p B0, abs_pre p Bi0)"
  using assms
proof (induction p)
  case Nil
  then show ?case by (subst strip_assums2.simps) (auto simp: atomic_def split: option.splits)
next
  case (Cons i p)
  then show ?case by (cases i) (subst strip_assums2.simps; auto)+
qed

lemma strip_apply_lift_pre:
  assumes "\<forall>i\<in>set p. litem_ok i" "atomic Bi0"
  shows "strip_apply f (lift_pre p Bi0) (lift_pre p A0) = lift_pre p (f A0)"
  using assms
proof (induction p)
  case Nil
  then show ?case
    by (subst strip_apply.simps) (auto simp: atomic_def split: option.splits pterm.splits)
next
  case (Cons i p)
  then show ?case by (cases i) (subst strip_apply.simps; auto)+
qed

lemma strip_lifted_lift_pre:
  assumes "\<forall>i\<in>set p. litem_ok i" "atomic Bi0"
  shows "strip_lifted (lift_pre p Bi0) (lift_pre p A0) = A0"
  using assms
proof (induction p)
  case Nil
  then show ?case by (subst strip_lifted.simps) (auto simp: atomic_def split: option.splits)
next
  case (Cons i p)
  then show ?case by (cases i) (subst strip_lifted.simps; auto)+
qed

end

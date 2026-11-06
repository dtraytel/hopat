section \<open>The Syntax of Propositions, Lifted Rules and Proof States\<close>

theory Thm_Syntax
  imports
    "Unify_Correctness.Unify_Results"
    "Pure_Thm.Pure_Bicompose"
begin

text \<open>
  Syntactic facts about the functions of \<^theory>\<open>Pure_Thm.Pure_Bicompose\<close>: the monad of
  \<open>bicompose_aux\<close>, the meta-connectives and their typing, the prefixes of lifted rules, the
  structure found by the functions that strip premises and parameters, and what the renaming of
  \<open>rename_bvs\<close> leaves unchanged.
\<close>


subsection \<open>The monad of \<open>bicompose_aux\<close>\<close>

text \<open>A computation \<^emph>\<open>succeeds\<close> with value \<open>x\<close> if it returns \<open>x\<close> after emitting some events.\<close>

abbreviation okT :: "'a T \<Rightarrow> 'a \<Rightarrow> bool" where
  "okT m x \<equiv> (\<exists>evs. m = Some (evs, TOk x))"

lemma okT_returnT [simp]: "okT (returnT x) y \<longleftrightarrow> y = x"
  by (auto simp: returnT_def)

lemma okT_raiseT [simp]: "\<not> okT (raiseT e) y"
  by (auto simp: raiseT_def)

lemma okT_emitT [simp]: "okT (emitT e) y \<longleftrightarrow> y = ()"
  by (auto simp: emitT_def)

lemma okT_bindT [simp]: "okT (bindT m f) y \<longleftrightarrow> (\<exists>x. okT m x \<and> okT (f x) y)"
  by (auto simp: bindT_def map_option_eq_Some split: option.splits tres.splits)

lemma okT_handleT:
  "okT (handleT m h) y \<longleftrightarrow> okT m y \<or> (\<exists>evs e. m = Some (evs, TErr e) \<and> okT (h e) y)"
  by (auto simp: handleT_def map_option_eq_Some split: option.splits tres.splits)

lemma okT_liftWT [simp]: "okT (liftWT m) y \<longleftrightarrow> okW m y"
  by (auto simp: liftWT_def split: option.splits ures.splits)

lemma okT_liftMT [simp]: "okT (liftMT m) y \<longleftrightarrow> ok m y"
  by (simp add: liftMT_def)

lemma okT_mapT: "okT (mapT f xs) ys \<longleftrightarrow> list_all2 (\<lambda>x y. okT (f x) y) xs ys"
proof (induction xs arbitrary: ys)
  case (Cons x xs)
  then show ?case by (cases ys) auto
qed auto

lemma okT_of: "m = Some r \<Longrightarrow> snd r = TOk x \<Longrightarrow> okT m x"
  by (cases r) auto


subsection \<open>The meta-connectives\<close>

definition imp_type :: ptyp where
  "imp_type = propT \<rightarrow>\<^sub>T propT \<rightarrow>\<^sub>T propT"

definition all_type :: "ptyp \<Rightarrow> ptyp" where
  "all_type T = (T \<rightarrow>\<^sub>T propT) \<rightarrow>\<^sub>T propT"

lemma implies_imp_type: "implies = Const STR ''Pure.imp'' imp_type"
  by (simp add: implies_def imp_type_def)

lemma all_const_all_type: "all_const T = Const STR ''Pure.all'' (all_type T)"
  by (simp add: all_const_def all_type_def)

lemma tsubst_propT [simp]: "tsubst \<rho> propT = propT"
  by (simp add: propT_def)

lemma tsubst_imp_type [simp]: "tsubst \<rho> imp_type = imp_type"
  by (simp add: imp_type_def)

lemma tsubst_all_type [simp]: "tsubst \<rho> (all_type T) = all_type (tsubst \<rho> T)"
  by (simp add: all_type_def)

lemma list_implies_append: "list_implies (As @ As') B = list_implies As (list_implies As' B)"
  by (induction As) auto

lemma list_forall_append: "list_forall (xs @ ys) t = list_forall xs (list_forall ys t)"
  by (induction xs t rule: list_forall.induct) auto

lemma vars_list_implies: "vars (list_implies As B) = (\<Union>A\<in>set As. vars A) \<union> vars B"
  by (induction As) (auto simp: implies_def)

lemma vars_list_forall [simp]: "vars (list_forall ps B) = vars B"
  by (induction ps B rule: list_forall.induct) (auto simp: all_const_def)

lemma loose_bvar_list_implies:
  "loose_bvar (list_implies As B) k \<longleftrightarrow> (\<exists>A\<in>set As. loose_bvar A k) \<or> loose_bvar B k"
  by (induction As) (auto simp: implies_def)

lemma loose_bvar_list_forall: "loose_bvar (list_forall ps B) k \<longleftrightarrow> loose_bvar B (k + ilength ps)"
  by (induction ps B arbitrary: k rule: list_forall.induct) (auto simp: all_const_def algebra_simps)

lemma inst_implies [simp]: "inst \<rho> implies = implies"
  by (simp add: implies_imp_type)

lemma inst_all_const [simp]: "inst \<rho> (all_const T) = all_const (tsubst \<rho> T)"
  by (simp add: all_const_all_type)

lemma inst_list_implies: "inst \<rho> (list_implies As B) = list_implies (map (inst \<rho>) As) (inst \<rho> B)"
  by (induction As) auto

lemma vsubst_implies [simp]: "vsubst \<sigma> implies = implies"
  by (simp add: implies_def)

lemma vsubst_all_const [simp]: "vsubst \<sigma> (all_const T) = all_const T"
  by (simp add: all_const_def)

lemma vsubst_list_implies: "vsubst \<sigma> (list_implies As B) = list_implies (map (vsubst \<sigma>) As) (vsubst \<sigma> B)"
  by (induction As) auto

lemma incr_bv_implies [simp]: "incr_bv n k implies = implies"
  by (simp add: implies_def)

lemma incr_bv_all_const [simp]: "incr_bv n k (all_const T) = all_const T"
  by (simp add: all_const_def)

lemma dest_imp_implies [simp]: "dest_imp (implies $ A $ B) = Some (A, B)"
  by (simp add: implies_def)

lemma dest_all_all_const [simp]: "dest_all (all_const T $ Abs a T b) = Some (a, T, b)"
  by (simp add: all_const_def)

lemma dest_all_implies [simp]: "dest_all (implies $ A $ B) = None"
  by (simp add: implies_def)

lemma dest_imp_all_const [simp]: "dest_imp (all_const T $ Abs a T b) = None"
  by (simp add: all_const_def)

lemma dest_imp_all: "dest_imp A = Some (H, B) \<Longrightarrow> dest_all A = None"
  by (auto simp: dest_imp_Some)

context pure_sig
begin

text \<open>
  In a well-typed term, the constants \<open>Pure.imp\<close> and \<open>Pure.all\<close> have their built-in types, so
  the patterns of \<^const>\<open>dest_imp\<close> and \<^const>\<open>dest_all\<close> are the meta-connectives.
\<close>

lemma typing_implies:
  "e \<turnstile> implies $ A $ B : T \<longleftrightarrow>
    T = propT \<and> cert_typ alg ar imp_type \<and> e \<turnstile> A : propT \<and> e \<turnstile> B : propT"
  by (auto simp: implies_imp_type imp_type_def const_typ_ok_def propT_def)

lemma typing_all_const:
  "e \<turnstile> all_const T $ Abs a T b : U \<longleftrightarrow>
    U = propT \<and> cert_typ alg ar (all_type T) \<and> cert_typ alg ar T \<and> e\<langle>0:T\<rangle> \<turnstile> b : propT"
  by (auto simp: all_const_all_type all_type_def const_typ_ok_def propT_def)

lemma typing_dest_imp:
  assumes "e \<turnstile> A : T" "dest_imp A = Some (H, B)"
  shows "A = implies $ H $ B" "T = propT" "cert_typ alg ar imp_type" "e \<turnstile> H : propT" "e \<turnstile> B : propT"
proof -
  from assms(2) obtain U where A: "A = Const STR ''Pure.imp'' U $ H $ B" by (auto simp: dest_imp_Some)
  with assms(1) have "U = imp_type" by (auto simp: const_typ_ok_def imp_type_def propT_def)
  with A show "A = implies $ H $ B" by (simp add: implies_imp_type)
  with assms(1) show "T = propT" "cert_typ alg ar imp_type" "e \<turnstile> H : propT" "e \<turnstile> B : propT"
    by (simp_all only: typing_implies)
qed

lemma typing_dest_all:
  assumes "e \<turnstile> A : U" "dest_all A = Some (a, T, b)"
  shows "A = all_const T $ Abs a T b" "U = propT" "cert_typ alg ar (all_type T)" "cert_typ alg ar T"
    "e\<langle>0:T\<rangle> \<turnstile> b : propT"
proof -
  from assms(2) obtain V where A: "A = Const STR ''Pure.all'' V $ Abs a T b" by (auto simp: dest_all_Some)
  with assms(1) have "V = all_type T" by (auto simp: const_typ_ok_def all_type_def propT_def)
  with A show "A = all_const T $ Abs a T b" by (simp add: all_const_all_type)
  with assms(1) show "U = propT" "cert_typ alg ar (all_type T)" "cert_typ alg ar T" "e\<langle>0:T\<rangle> \<turnstile> b : propT"
    by (simp_all only: typing_all_const)
qed

lemma typing_list_impliesD:
  "e \<turnstile> list_implies As B : propT \<Longrightarrow> (\<forall>A\<in>set As. e \<turnstile> A : propT) \<and> e \<turnstile> B : propT"
  by (induction As) (auto simp: typing_implies)

lemma typing_list_impliesI:
  "\<forall>A\<in>set As. e \<turnstile> A : propT \<Longrightarrow> e \<turnstile> B : propT \<Longrightarrow> As \<noteq> [] \<longrightarrow> cert_typ alg ar imp_type \<Longrightarrow>
    e \<turnstile> list_implies As B : propT"
  by (induction As) (auto simp: typing_implies)

end


subsection \<open>Prefixes of lifted rules\<close>

text \<open>
  A rule is lifted over a subgoal \<open>Bi\<close> by putting the parameters and assumptions of \<open>Bi\<close> in
  front of each of its premises and of its conclusion (\<open>Thm.lift_rule\<close>). The common prefix is
  a list of items: an assumption \<open>c $ H $ _\<close> or a parameter \<open>c $ Abs a T _\<close>, where \<open>c\<close> is the
  respective constant of \<open>Bi\<close>. The functions \<^const>\<open>strip_assums2\<close>, \<^const>\<open>strip_apply\<close>
  and \<^const>\<open>strip_lifted\<close> of \<open>thm.ML\<close> strip off such prefixes.
\<close>

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

fun fun_of :: "pterm \<Rightarrow> pterm" where
  "fun_of (f $ _) = f"
| "fun_of t = t"

text \<open>The prefix of a subgoal: all its parameters and assumptions.\<close>

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

declare lsplit.simps [simp del]

lemma dest_imp_lift_pre [simp]:
  "litem_ok i \<Longrightarrow> dest_imp (lift_pre (i # p) t) = (case i of LImp c H \<Rightarrow> Some (H, lift_pre p t) | _ \<Rightarrow> None)"
  by (cases i) auto

lemma dest_all_lift_pre [simp]:
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

lemma lift_pre_append: "lift_pre (p @ q) t = lift_pre p (lift_pre q t)"
  by (induction p t rule: lift_pre.induct) auto

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

text \<open>The number of parameters, the types of the parameters (outermost first), the variables
  and the hypotheses of a prefix.\<close>

fun nall :: "litem list \<Rightarrow> nat" where
  "nall [] = 0"
| "nall (LImp c H # p) = nall p"
| "nall (LAll c a T # p) = Suc (nall p)"

fun ptys :: "litem list \<Rightarrow> ptyp list" where
  "ptys [] = []"
| "ptys (LImp c H # p) = ptys p"
| "ptys (LAll c a T # p) = T # ptys p"

fun phyps :: "litem list \<Rightarrow> pterm list" where
  "phyps [] = []"
| "phyps (LImp c H # p) = H # phyps p"
| "phyps (LAll c a T # p) = phyps p"

lemma vars_lift_pre: "vars (lift_pre p X) = (\<Union>i\<in>set p. vars (lift_pre [i] (Bound 0))) \<union> vars X"
  by (induction p X rule: lift_pre.induct) auto

lemma vars_abs_pre [simp]: "vars (abs_pre p X) = vars X"
  by (induction p X rule: abs_pre.induct) auto

lemma length_ptys: "length (ptys p) = nall p"
  by (induction p rule: ptys.induct) auto


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

lemma strip_prems_list_implies:
  "strip_prems (ilength As) Hs (list_implies As B) = return (rev As @ Hs, B)"
proof (induction As arbitrary: Hs)
  case Nil
  then show ?case by (subst strip_prems.simps) simp
next
  case (Cons A As)
  have "ilength (A # As) \<noteq> 0" by (simp add: ilength_eq integer_eq_iff integer_of_nat.rep_eq)
  with Cons show ?case
    by (subst strip_prems.simps) (simp add: mk_implies_def)
qed


subsection \<open>Parameters, assumptions and the spine\<close>

lemma strip_params_imp: "dest_imp A = Some (H, B) \<Longrightarrow> strip_params A = strip_params B"
  by (subst strip_params.simps) simp

lemma strip_params_all: "dest_imp A = None \<Longrightarrow> dest_all A = Some (a, T, b) \<Longrightarrow>
    strip_params A = (a, T) # strip_params b"
  by (subst strip_params.simps) simp

lemma strip_params_other: "dest_imp A = None \<Longrightarrow> dest_all A = None \<Longrightarrow> strip_params A = []"
  by (subst strip_params.simps) simp

text \<open>The hypotheses along the spine of a proposition.\<close>

function spine_hyps :: "pterm \<Rightarrow> pterm list" where
  "spine_hyps t =
    (case dest_imp t of
      Some (H, B) \<Rightarrow> H # spine_hyps B
    | None \<Rightarrow> (case dest_all t of Some (_, _, b) \<Rightarrow> spine_hyps b | None \<Rightarrow> []))"
  by auto
termination by (relation "measure size") (auto dest: dest_size)

declare spine_hyps.simps [simp del]

lemma spine_hyps_lift_pre: "\<forall>i\<in>set p. litem_ok i \<Longrightarrow> spine_hyps (lift_pre p X) = phyps p @ spine_hyps X"
proof (induction p)
  case (Cons i p)
  then show ?case by (cases i) (subst spine_hyps.simps; auto)+
qed simp

lemma spine_hyps_list_forall: "spine_hyps (list_forall vs X) = spine_hyps X"
proof (induction vs X rule: list_forall.induct)
  case (2 a T vs t)
  then show ?case by (subst spine_hyps.simps) (simp add: all_const_def)
qed simp

lemma spine_hyps_atomic: "atomic t \<Longrightarrow> spine_hyps t = []"
  by (subst spine_hyps.simps) (simp add: atomic_def)

lemma count_prems_nonneg: "0 \<le> count_prems t"
proof (induction t rule: measure_induct_rule[of size])
  case (less t)
  then show ?case by (subst count_prems.simps) (auto split: option.splits dest: dest_size)
qed

lemma count_prems_lift_pre_le:
  "\<forall>i\<in>set p. litem_ok i \<Longrightarrow> atomic Y \<Longrightarrow> count_prems (lift_pre p Y) \<le> ilength (phyps p)"
proof (induction p)
  case Nil
  then show ?case by (subst count_prems.simps) (simp add: atomic_def)
next
  case (Cons i p)
  then show ?case by (cases i) (subst count_prems.simps; auto)+
qed

lemma count_prems_lift_pre:
  "\<forall>i\<in>set p. litem_ok i \<Longrightarrow> atomic Y \<Longrightarrow> count_prems (strip_all_body (lift_pre p Y)) \<le> ilength (phyps p)"
proof (induction p)
  case Nil
  then show ?case by (subst strip_all_body.simps, subst count_prems.simps) (simp add: atomic_def)
next
  case (Cons i p)
  then show ?case
    by (cases i) (subst strip_all_body.simps; use count_prems_lift_pre_le[of "i # p" Y] in auto)+
qed

context pure_sig
begin

text \<open>The structure found by \<^const>\<open>assum_problems\<close>, for well-typed propositions.\<close>

lemma strip_assums_all_struct:
  "strip_assums_all params A = (params', A') \<Longrightarrow> e \<turnstile> A : propT \<Longrightarrow>
    \<exists>ps. params' = ps @ params \<and> A = list_forall (rev ps) A' \<and> pushes e (map snd (rev ps)) \<turnstile> A' : propT"
proof (induction params A arbitrary: e rule: strip_assums_all.induct)
  case (1 params t)
  show ?case
  proof (cases "dest_all t")
    case (Some aTb)
    then obtain a T b where aTb: "dest_all t = Some (a, T, b)" by (cases aTb) auto
    note ty = typing_dest_all[OF "1.prems"(2) aTb]
    from "1.prems"(1) aTb have "strip_assums_all ((a, T) # params) b = (params', A')"
      by (subst (asm) strip_assums_all.simps) simp
    from "1.IH"[OF aTb refl refl this ty(5)] obtain ps where
      "params' = ps @ (a, T) # params" "b = list_forall (rev ps) A'"
      "pushes (e\<langle>0:T\<rangle>) (map snd (rev ps)) \<turnstile> A' : propT" by blast
    with ty(1) show ?thesis by (intro exI[of _ "ps @ [(a, T)]"]) simp
  next
    case None
    with "1.prems" show ?thesis by (subst (asm) strip_assums_all.simps) auto
  qed
qed

lemma strip_assums_imp_struct:
  "strip_assums_imp k Hs B = (Hs', B') \<Longrightarrow> e \<turnstile> B : propT \<Longrightarrow>
    \<exists>qs. Hs' = rev qs @ Hs \<and> B = list_implies qs B' \<and> (\<forall>H\<in>set qs. e \<turnstile> H : propT) \<and> e \<turnstile> B' : propT"
proof (induction k Hs B rule: strip_assums_imp.induct)
  case (1 k Hs B)
  show ?case
  proof (cases "k = 0")
    case True
    with "1.prems" show ?thesis by (subst (asm) strip_assums_imp.simps) auto
  next
    case False
    show ?thesis
    proof (cases "dest_imp B")
      case (Some HB)
      then obtain H B1 where HB: "dest_imp B = Some (H, B1)" by (cases HB) auto
      note ty = typing_dest_imp[OF "1.prems"(2) HB]
      from "1.prems"(1) False HB have "strip_assums_imp (k - 1) (H # Hs) B1 = (Hs', B')"
        by (subst (asm) strip_assums_imp.simps) simp
      from "1.IH"[OF False HB refl this ty(5)] obtain qs where
        "Hs' = rev qs @ H # Hs" "B1 = list_implies qs B'" "\<forall>H\<in>set qs. e \<turnstile> H : propT" "e \<turnstile> B' : propT"
        by blast
      with ty show ?thesis by (intro exI[of _ "H # qs"]) simp
    next
      case None
      with "1.prems" False show ?thesis by (subst (asm) strip_assums_imp.simps) auto
    qed
  qed
qed

lemma assum_problems_struct:
  assumes "assum_problems k A = (params, asms, concl)" "e \<turnstile> A : propT"
  shows "A = list_forall (rev params) (list_implies asms concl)"
    "\<forall>H\<in>set asms. pushes e (map snd (rev params)) \<turnstile> H : propT"
    "pushes e (map snd (rev params)) \<turnstile> concl : propT"
proof -
  obtain ps A' where a: "strip_assums_all [] A = (ps, A')" by (cases "strip_assums_all [] A")
  obtain Hs B where b: "strip_assums_imp k [] A' = (Hs, B)" by (cases "strip_assums_imp k [] A'")
  from assms(1) a b have p: "params = ps" "asms = rev Hs" "concl = B"
    by (simp_all add: assum_problems_def)
  from strip_assums_all_struct[OF a assms(2)] have A: "A = list_forall (rev ps) A'"
    and tA': "pushes e (map snd (rev ps)) \<turnstile> A' : propT" by auto
  from strip_assums_imp_struct[OF b tA'] obtain qs where
    "Hs = rev qs" "A' = list_implies qs B" "\<forall>H\<in>set qs. pushes e (map snd (rev ps)) \<turnstile> H : propT"
    "pushes e (map snd (rev ps)) \<turnstile> B : propT" by auto
  with A p show "A = list_forall (rev params) (list_implies asms concl)"
    "\<forall>H\<in>set asms. pushes e (map snd (rev params)) \<turnstile> H : propT"
    "pushes e (map snd (rev params)) \<turnstile> concl : propT" by simp_all
qed

end

lemma strip_assums_imp_length:
  "strip_assums_imp k Hs B = (Hs', B') \<Longrightarrow> 0 \<le> k \<Longrightarrow> ilength Hs' \<le> ilength Hs + k"
proof (induction k Hs B rule: strip_assums_imp.induct)
  case (1 k Hs B)
  show ?case
  proof (cases "k = 0")
    case True
    with "1.prems" show ?thesis by (subst (asm) strip_assums_imp.simps) simp
  next
    case False
    show ?thesis
    proof (cases "dest_imp B")
      case (Some HB)
      then obtain H B1 where HB: "dest_imp B = Some (H, B1)" by (cases HB) auto
      with "1.prems"(1) False have "strip_assums_imp (k - 1) (H # Hs) B1 = (Hs', B')"
        by (subst (asm) strip_assums_imp.simps) simp
      moreover have "0 \<le> k - 1" using "1.prems"(2) False by (simp add: integer_reps)
      ultimately show ?thesis using "1.IH"[OF False HB refl] by simp
    next
      case None
      with "1.prems"(1) False have "Hs' = Hs" by (subst (asm) strip_assums_imp.simps) simp
      with "1.prems"(2) show ?thesis by simp
    qed
  qed
qed

lemma assum_problems_length: "assum_problems k A = (params, asms, concl) \<Longrightarrow> 0 \<le> k \<Longrightarrow> ilength asms \<le> k"
  by (auto simp: assum_problems_def ilength_eq dest!: strip_assums_imp_length split: prod.splits)
    (metis add.left_neutral integer_of_nat_0)

text \<open>Elim-resolution with a lifted rule uses lifted assumptions.\<close>

lemma strip_assums_imp_lift_pre:
  assumes "\<forall>i\<in>set p. litem_ok i" "atomic Y" "0 \<le> k" "k \<le> count_prems (lift_pre p Y)"
    "strip_assums_imp k Hs (lift_pre p X) = (Hs', B)"
  shows "set Hs' \<subseteq> set Hs \<union> set (phyps p)"
  using assms
proof (induction p arbitrary: k Hs)
  case Nil
  then have "k = 0" by (subst (asm) count_prems.simps) (simp add: atomic_def)
  with Nil.prems show ?case by (subst (asm) strip_assums_imp.simps) simp
next
  case (Cons i p)
  show ?case
  proof (cases "k = 0")
    case True
    with Cons.prems show ?thesis by (subst (asm) strip_assums_imp.simps) simp
  next
    case False
    show ?thesis
    proof (cases i)
      case (LImp c H)
      with Cons.prems(1) obtain U where c: "c = Const STR ''Pure.imp'' U" by auto
      have k: "0 \<le> k - 1" using Cons.prems(3) False by (simp add: integer_reps)
      from Cons.prems(4) LImp c have kc: "k - 1 \<le> count_prems (lift_pre p Y)"
        by (subst (asm) count_prems.simps) simp
      from Cons.prems(5) False LImp c
      have s: "strip_assums_imp (k - 1) (H # Hs) (lift_pre p X) = (Hs', B)"
        by (subst (asm) strip_assums_imp.simps) simp
      from Cons.prems(1) have "set Hs' \<subseteq> set (H # Hs) \<union> set (phyps p)"
        by (intro Cons.IH[OF _ Cons.prems(2) k kc s]) simp
      with LImp show ?thesis by auto
    next
      case (LAll c a T)
      with Cons.prems(1) obtain U where c: "c = Const STR ''Pure.all'' U" by auto
      from Cons.prems(4) LAll c have "k \<le> 0" by (subst (asm) count_prems.simps) simp
      with Cons.prems(3) False show ?thesis by simp
    qed
  qed
qed

lemma assum_problems_lift_pre:
  assumes "\<forall>i\<in>set p. litem_ok i" "atomic Y" "k \<le> count_prems (strip_all_body (lift_pre p Y))"
    "assum_problems k (lift_pre p X) = (params, asms, concl)" "0 \<le> k"
  shows "set asms \<subseteq> set (phyps p)"
proof -
  obtain ps A' where a: "strip_assums_all [] (lift_pre p X) = (ps, A')"
    by (cases "strip_assums_all [] (lift_pre p X)")
  obtain Hs B where b: "strip_assums_imp k [] A' = (Hs, B)" by (cases "strip_assums_imp k [] A'")
  from assms(4) a b have asms: "asms = rev Hs" by (simp add: assum_problems_def)
  have "set Hs \<subseteq> set (phyps p)" if "strip_assums_all qs (lift_pre p X) = (ps, A')" for qs
    using assms(1-3) that
  proof (induction p arbitrary: qs)
    case Nil
    then have "k = 0"
      using assms(5) by (subst (asm) strip_all_body.simps, subst (asm) count_prems.simps) (simp add: atomic_def)
    with b show ?case by (subst (asm) strip_assums_imp.simps) simp
  next
    case (Cons i p)
    show ?case
    proof (cases i)
      case (LImp c H)
      with Cons.prems(1) obtain U where c: "c = Const STR ''Pure.imp'' U" by auto
      from Cons.prems(4) LImp c have "A' = lift_pre (i # p) X"
        by (subst (asm) strip_assums_all.simps) simp
      with b have s: "strip_assums_imp k [] (lift_pre (i # p) X) = (Hs, B)" by simp
      from Cons.prems(3) LImp c have kc: "k \<le> count_prems (lift_pre (i # p) Y)"
        by (subst (asm) strip_all_body.simps) simp
      show ?thesis using strip_assums_imp_lift_pre[OF Cons.prems(1,2) assms(5) kc s] by simp
    next
      case (LAll c a T)
      with Cons.prems(1) obtain U where c: "c = Const STR ''Pure.all'' U" by auto
      from Cons.prems(4) LAll c have "strip_assums_all ((a, T) # qs) (lift_pre p X) = (ps, A')"
        by (subst (asm) strip_assums_all.simps) simp
      moreover from Cons.prems(3) LAll c have "k \<le> count_prems (strip_all_body (lift_pre p Y))"
        by (subst (asm) strip_all_body.simps) simp
      ultimately show ?thesis using Cons.IH Cons.prems(1,2) LAll by simp
    qed
  qed
  with a asms show ?thesis by simp
qed

end

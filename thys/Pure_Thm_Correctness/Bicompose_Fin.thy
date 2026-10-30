section \<open>Termination of \<open>bicompose_aux\<close>\<close>

theory Bicompose_Fin
  imports Bicompose_Correct Pure_Pattern_Correctness.Match_Exceptions
begin

text \<open>
  For a well-typed proof state and rule, \<open>bicompose_aux\<close> terminates, and pulling its sequence of
  results repeatedly yields finitely many results and then the end of the sequence, without an
  exception. The unifiers of a problem are finite in number and well-typed (@{thm [source]
  wf_algebra.unifiers_prres_rs}); the new theorem is normalized in their environments, so its
  components must be well-typed there as well. Renaming and flattening keep the new premises
  well-typed.
\<close>


subsection \<open>Typing of flattened premises\<close>

lemma has_type_list_forallI:
  "has_type W (rev (map snd ps) @ Ts) B propT \<Longrightarrow> has_type W Ts (list_forall ps B) propT"
  by (induction ps B arbitrary: Ts rule: list_forall.induct) (auto simp: has_type_all_const)

lemma has_type_incr_boundvars:
  assumes "has_type V Ts t T" "0 \<le> j" "length Us = nat_of_integer j"
  shows "has_type V (Us @ Ts) (incr_boundvars j t) T"
proof (cases "j = 0")
  case True
  with assms show ?thesis by (simp add: incr_boundvars_def integer_reps)
next
  case False
  from has_type_incr_bv[OF assms(1,2), of 0 Us] assms(3) show ?thesis
    by (simp add: incr_boundvars_def False)
qed

lemma ilength_0: "ilength xs = 0 \<longleftrightarrow> xs = []"
  by (simp add: ilength_eq integer_eq_iff integer_of_nat.rep_eq)

lemma remove_params_has_type:
  assumes "ok (remove_params j n A) A'" "ilength (strip_params A) = j" "cok A" "has_type W Ts A propT"
  shows "has_type W (rev (map snd (strip_params A)) @ Ts) A' propT"
  using assms
proof (induction j n A arbitrary: A' Ts rule: remove_params.induct)
  case (1 j n A)
  note rp = "1.prems"(1)
  show ?case
  proof (cases "j = 0 \<and> n \<le> 0")
    case True
    with rp "1.prems"(2,4) show ?thesis by (subst (asm) remove_params.simps) (simp add: ilength_0)
  next
    case False
    show ?thesis
    proof (cases "dest_imp A")
      case (Some HB)
      then obtain H B where HB: "dest_imp A = Some (H, B)" by (cases HB) auto
      from cok_dest_imp[OF "1.prems"(3) HB] have A: "A = implies $ H $ B" "cok H" "cok B" by auto
      have sp: "strip_params A = strip_params B" by (rule strip_params_imp[OF HB])
      have spB: "ilength (strip_params B) = j" using "1.prems"(2) sp by simp
      have ty: "has_type W Ts H propT" "has_type W Ts B propT"
        using "1.prems"(4) A(1) by (simp_all add: has_type_implies)
      show ?thesis
      proof (cases "n = 1")
        case True
        with rp False HB have "ok (remove_params j (n - 1) B) A'"
          by (subst (asm) remove_params.simps) simp
        from "1.IH"(2)[OF False HB refl True this spB A(3) ty(2)] sp show ?thesis by simp
      next
        case n1: False
        with rp False HB obtain B' where B': "ok (remove_params j (n - 1) B) B'"
          and A': "A' = implies $ incr_boundvars j H $ B'"
          by (subst (asm) remove_params.simps) (auto simp: bindM_def split: option.splits res.splits)
        from "1.IH"(3)[OF False HB refl n1 B' spB A(3) ty(2)]
        have "has_type W (rev (map snd (strip_params B)) @ Ts) B' propT" .
        moreover have "has_type W (rev (map snd (strip_params B)) @ Ts) (incr_boundvars j H) propT"
          by (rule has_type_incr_boundvars[OF ty(1)]) (use spB in \<open>simp_all add: ilength_eq integer_reps\<close>)
        ultimately show ?thesis using A' sp by (simp add: has_type_implies)
      qed
    next
      case None
      show ?thesis
      proof (cases "dest_all A")
        case (Some aTb)
        then obtain a T b where aTb: "dest_all A = Some (a, T, b)" by (cases aTb) auto
        from cok_dest_all[OF "1.prems"(3) aTb] have A: "A = all_const T $ Abs a T b" "cok b" by auto
        with rp False None aTb have r: "ok (remove_params (j - 1) n b) A'"
          by (subst (asm) remove_params.simps) simp
        have sp: "strip_params A = (a, T) # strip_params b" by (rule strip_params_all[OF None aTb])
        have spb: "ilength (strip_params b) = j - 1" using "1.prems"(2) sp by (simp add: ilength_Cons)
        have "has_type W (T # Ts) b propT" using "1.prems"(4) A(1) by (simp add: has_type_all_const)
        from "1.IH"(1)[OF False None aTb refl refl r spb A(2) this] sp show ?thesis by simp
      next
        case None': None
        with rp False None "1.prems" show ?thesis
          by (subst (asm) remove_params.simps) (auto split: if_splits simp: strip_params_other)
      qed
    qed
  qed
qed

lemma flatten_params_has_type:
  assumes "ok (flatten_params vl n A) A'" "length (vl (map fst (strip_params A))) = length (strip_params A)"
    "cok A" "has_type W Ts A propT"
  shows "has_type W Ts A' propT"
proof -
  let ?ps = "strip_params A"
  let ?vars = "zip (vl (map fst ?ps)) (map snd ?ps)"
  have sv: "map snd ?vars = map snd ?ps" using assms(2) by (simp add: map_snd_zip)
  from assms(1) obtain A'' where r: "ok (remove_params (ilength ?vars) n A) A''"
    and A': "A' = list_forall ?vars A''"
    by (auto simp: flatten_params_def Let_def)
  have j: "ilength ?ps = ilength ?vars" using assms(2) by (simp add: ilength_eq)
  from remove_params_has_type[OF r j assms(3,4)] sv A' show ?thesis
    by (simp add: has_type_list_forallI)
qed

subsection \<open>Normalizing the types of a proposition\<close>

text \<open>
  Typing modulo a type environment (\<^const>\<open>typed\<close>) is typing of the term with normalized types
  (\<^const>\<open>tnormt\<close>), which commutes with the operations on propositions.
\<close>

lemma tnorm_propT[simp]: "tnorm \<theta> propT = propT"
  by (simp add: propT_def)

lemma tnorm_imp_type[simp]: "tnorm \<theta> imp_type = imp_type"
  by (simp add: imp_type_def)

lemma tnorm_all_type[simp]: "tnorm \<theta> (all_type T) = all_type (tnorm \<theta> T)"
  by (simp add: all_type_def)

lemma all_type_neq_imp_type[simp]: "all_type T \<noteq> imp_type"
  by (simp add: all_type_def imp_type_def propT_def)

lemma tnormt_implies[simp]: "tnormt \<theta> implies = implies"
  by (simp add: implies_imp_type)

lemma tnormt_all_const[simp]: "tnormt \<theta> (all_const T) = all_const (tnorm \<theta> T)"
  by (simp add: all_const_all_type)

lemma dest_imp_tnormt: "dest_imp (tnormt \<theta> t) = map_option (\<lambda>(A, B). (tnormt \<theta> A, tnormt \<theta> B)) (dest_imp t)"
  by (cases t rule: dest_imp.cases) auto

lemma dest_all_tnormt:
  "dest_all (tnormt \<theta> t) = map_option (\<lambda>(a, T, b). (a, tnorm \<theta> T, tnormt \<theta> b)) (dest_all t)"
  by (cases t rule: dest_all.cases) auto

lemma cok_tnormt: "cok t \<Longrightarrow> cok (tnormt \<theta> t)"
  by (induction t rule: cok.induct) auto

lemma strip_params_tnormt: "strip_params (tnormt \<theta> A) = map (\<lambda>(a, T). (a, tnorm \<theta> T)) (strip_params A)"
proof (induction A rule: measure_induct_rule[of size])
  case (less A)
  show ?case
  proof (cases "dest_imp A")
    case (Some HB)
    then obtain H B where "dest_imp A = Some (H, B)" by (cases HB) auto
    with less[of B] show ?thesis
      by (simp add: strip_params_imp dest_imp_tnormt dest_imp_size)
  next
    case None
    show ?thesis
    proof (cases "dest_all A")
      case (Some aTb)
      then obtain a T b where "dest_all A = Some (a, T, b)" by (cases aTb) auto
      with None less[of b] show ?thesis
        by (simp add: strip_params_all dest_imp_tnormt dest_all_tnormt dest_all_size)
    next
      case None': None
      with None show ?thesis by (simp add: strip_params_other dest_imp_tnormt dest_all_tnormt)
    qed
  qed
qed

lemma tnormt_list_forall:
  "tnormt \<theta> (list_forall vs t) = list_forall (map (\<lambda>(a, T). (a, tnorm \<theta> T)) vs) (tnormt \<theta> t)"
  by (induction vs t rule: list_forall.induct) auto

lemma remove_params_tnormt:
  "ok (remove_params j n A) A' \<Longrightarrow> ok (remove_params j n (tnormt \<theta> A)) (tnormt \<theta> A')"
proof (induction j n A arbitrary: A' rule: remove_params.induct)
  case (1 j n A)
  note rp = "1.prems"
  show ?case
  proof (cases "j = 0 \<and> n \<le> 0")
    case True
    with rp show ?thesis by (subst (asm) remove_params.simps, subst remove_params.simps) simp
  next
    case False
    show ?thesis
    proof (cases "dest_imp A")
      case (Some HB)
      then obtain H B where HB: "dest_imp A = Some (H, B)" by (cases HB) auto
      have HB': "dest_imp (tnormt \<theta> A) = Some (tnormt \<theta> H, tnormt \<theta> B)" by (simp add: dest_imp_tnormt HB)
      show ?thesis
      proof (cases "n = 1")
        case True
        with rp False HB have "ok (remove_params j (n - 1) B) A'"
          by (subst (asm) remove_params.simps) simp
        from "1.IH"(2)[OF False HB refl True this] False True HB' show ?thesis
          by (subst remove_params.simps) simp
      next
        case n1: False
        with rp False HB obtain B' where B': "ok (remove_params j (n - 1) B) B'"
          and A': "A' = implies $ incr_boundvars j H $ B'"
          by (subst (asm) remove_params.simps) (auto simp: bindM_def split: option.splits res.splits)
        from "1.IH"(3)[OF False HB refl n1 B'] False n1 HB' A' show ?thesis
          by (subst remove_params.simps) (simp add: bindM_def)
      qed
    next
      case None
      have N': "dest_imp (tnormt \<theta> A) = None" by (simp add: dest_imp_tnormt None)
      show ?thesis
      proof (cases "dest_all A")
        case (Some aTb)
        then obtain a T b where aTb: "dest_all A = Some (a, T, b)" by (cases aTb) auto
        with rp False None have r: "ok (remove_params (j - 1) n b) A'"
          by (subst (asm) remove_params.simps) simp
        from "1.IH"(1)[OF False None aTb refl refl r] False N' aTb show ?thesis
          by (subst remove_params.simps) (simp add: dest_all_tnormt)
      next
        case None': None
        with rp False None have "A' = A" "\<not> 0 < n"
          by (subst (asm) remove_params.simps; auto split: if_splits)+
        with False N' None' show ?thesis
          by (subst remove_params.simps) (simp add: dest_all_tnormt)
      qed
    qed
  qed
qed

lemma map_fst_strip_params_tnormt: "map fst (strip_params (tnormt \<theta> A)) = map fst (strip_params A)"
  by (simp add: strip_params_tnormt case_prod_unfold comp_def)

lemma flatten_params_tnormt:
  assumes "ok (flatten_params vl n A) A'"
  shows "ok (flatten_params vl n (tnormt \<theta> A)) (tnormt \<theta> A')"
proof -
  let ?ps = "strip_params A"
  let ?vars = "zip (vl (map fst ?ps)) (map snd ?ps)"
  let ?vars' = "zip (vl (map fst (strip_params (tnormt \<theta> A)))) (map snd (strip_params (tnormt \<theta> A)))"
  from assms obtain A'' where r: "ok (remove_params (ilength ?vars) n A) A''"
    and A': "A' = list_forall ?vars A''"
    by (auto simp: flatten_params_def Let_def)
  have v: "?vars' = map (\<lambda>(a, T). (a, tnorm \<theta> T)) ?vars"
    by (simp add: map_fst_strip_params_tnormt strip_params_tnormt zip_map2 case_prod_unfold comp_def)
  have l: "ilength ?vars' = ilength ?vars" by (simp only: v ilength_eq length_map)
  have "flatten_params vl n (tnormt \<theta> A) =
      do {A'' \<leftarrow> remove_params (ilength ?vars) n (tnormt \<theta> A); return (list_forall ?vars' A'')}"
    by (simp only: flatten_params_def Let_def l)
  with remove_params_tnormt[OF r, of \<theta>] A' v show ?thesis
    by (simp add: tnormt_list_forall)
qed

lemma typed_flatten_params:
  assumes "ok (flatten_params vl n A) A'" "length (vl (map fst (strip_params A))) = length (strip_params A)"
    "cok A" "typed env W Ts A propT"
  shows "typed env W Ts A' propT"
proof -
  have "length (strip_params (tnormt (tyenv env) A)) = length (strip_params A)"
    by (simp add: strip_params_tnormt)
  then have l: "length (vl (map fst (strip_params (tnormt (tyenv env) A)))) = length (strip_params (tnormt (tyenv env) A))"
    using assms(2) by (simp only: map_fst_strip_params_tnormt)
  from flatten_params_has_type[OF flatten_params_tnormt[OF assms(1)] l cok_tnormt[OF assms(3)]]
    assms(4) show ?thesis
    by (simp add: typed_def)
qed


lemma typed_implies:
  "typed env W Ts (implies $ A $ B) propT \<longleftrightarrow> typed env W Ts A propT \<and> typed env W Ts B propT"
  by (simp add: typed_def has_type_implies)

lemma typed_all_const:
  "typed env W Ts (all_const T $ Abs a T b) propT \<longleftrightarrow> typed env W (T # Ts) b propT"
  by (simp add: typed_def has_type_all_const)

text \<open>The part of a lifted proposition after the prefix is typed in the context of the parameters.\<close>

lemma typed_lift_preD:
  assumes "\<forall>i\<in>set p. litem_ok i" "cok (lift_pre p X)" "typed env W Ts (lift_pre p X) propT"
  shows "typed env W (rev (ptys p) @ Ts) X propT"
  using assms
proof (induction p arbitrary: Ts)
  case (Cons i p)
  show ?case
  proof (cases i)
    case (LImp c H)
    with Cons.prems(1) obtain U where c: "c = Const STR ''Pure.imp'' U" by auto
    have "U = imp_type \<and> cok H \<and> cok (lift_pre p X)"
      by (rule cok_imp) (use Cons.prems(2) LImp c in simp_all)
    with Cons LImp c show ?thesis by (simp add: implies_imp_type[symmetric] typed_implies)
  next
    case (LAll c a T)
    with Cons.prems(1) obtain U where c: "c = Const STR ''Pure.all'' U" by auto
    with Cons.prems(2) LAll have "U = all_type T" "cok (lift_pre p X)" by auto
    with Cons LAll c show ?thesis by (simp add: all_const_all_type[symmetric] typed_all_const)
  qed
qed simp

lemma typed_lift_pre_cong:
  assumes "\<forall>i\<in>set p. litem_ok i" "cok (lift_pre p X)" "typed env W Ts (lift_pre p X) propT"
    "typed env W' (rev (ptys p) @ Ts) Y propT"
    "\<forall>H\<in>set (phyps p). \<forall>x\<in>vars H. tctx env W' x = tctx env W x"
  shows "typed env W' Ts (lift_pre p Y) propT"
  using assms
proof (induction p arbitrary: Ts)
  case (Cons i p)
  show ?case
  proof (cases i)
    case (LImp c H)
    with Cons.prems(1) obtain U where c: "c = Const STR ''Pure.imp'' U" by auto
    have "U = imp_type \<and> cok H \<and> cok (lift_pre p X)"
      by (rule cok_imp) (use Cons.prems(2) LImp c in simp_all)
    moreover from this Cons.prems(3) LImp c have "typed env W Ts H propT"
      by (simp add: implies_imp_type[symmetric] typed_implies)
    then have "typed env W' Ts H propT"
      by (rule typed_tctx_cong[OF _ refl]) (use Cons.prems(5) LImp in auto)
    ultimately show ?thesis
      using Cons LImp c by (simp add: implies_imp_type[symmetric] typed_implies)
  next
    case (LAll c a T)
    with Cons.prems(1) obtain U where c: "c = Const STR ''Pure.all'' U" by auto
    with Cons.prems(2) LAll have "U = all_type T" "cok (lift_pre p X)" by auto
    with Cons LAll c show ?thesis by (simp add: all_const_all_type[symmetric] typed_all_const)
  qed
qed simp


subsection \<open>Typing of renamed premises\<close>

text \<open>The renaming of the schematic variables, on index names.\<close>

definition ren_ix :: "ren \<Rightarrow> indexname \<Rightarrow> indexname" where
  "ren_ix r x = (ren_name (fst r) (fst x), snd x)"

lemma tnormt_ren_term: "tnormt \<theta> (ren_term r t) = ren_term r (tnormt \<theta> t)"
  by (induction r t rule: ren_term.induct) auto

lemma has_type_ren_term:
  "has_type V Ts t T \<Longrightarrow> (\<forall>x\<in>vars t. V' (ren_ix r x) = V x) \<Longrightarrow> has_type V' Ts (ren_term r t) T"
proof (induction rule: has_type.induct)
  case (Var V x T Ts)
  then show ?case by (cases x) (auto simp: ren_ix_def intro: has_type.Var)
qed (auto intro: has_type.intros)

lemma typed_ren_term:
  assumes "typed env W Ts t T" "\<forall>x\<in>vars t. tctx env W' (ren_ix r x) = tctx env W x"
  shows "typed env W' Ts (ren_term r t) T"
  using has_type_ren_term[OF assms(1)[unfolded typed_def], of "tctx env W'" r] assms(2)
  by (simp add: typed_def tnormt_ren_term)


subsection \<open>Flattening and normalization succeed\<close>

lemma remove_params_ok:
  "ilength (strip_params A) = j \<Longrightarrow> cok A \<Longrightarrow> n \<le> ilength (spine_hyps A) \<Longrightarrow> \<exists>A'. ok (remove_params j n A) A'"
proof (induction j n A rule: remove_params.induct)
  case (1 j n A)
  show ?case
  proof (cases "j = 0 \<and> n \<le> 0")
    case True
    then show ?thesis by (subst remove_params.simps) simp
  next
    case False
    show ?thesis
    proof (cases "dest_imp A")
      case (Some HB)
      then obtain H B where HB: "dest_imp A = Some (H, B)" by (cases HB) auto
      from cok_dest_imp[OF "1.prems"(2) HB] have cB: "cok B" by auto
      have spB: "ilength (strip_params B) = j" using "1.prems"(1) HB by (simp add: strip_params_imp)
      have sh: "spine_hyps A = H # spine_hyps B" using HB by (subst spine_hyps.simps) simp
      have n1: "n - 1 \<le> ilength (spine_hyps B)" using "1.prems"(3) sh by (simp add: ilength_Cons)
      show ?thesis
      proof (cases "n = 1")
        case True
        from "1.IH"(2)[OF False HB refl True spB cB n1] obtain B' where "ok (remove_params j (n - 1) B) B'"
          by blast
        with False HB True show ?thesis by (subst remove_params.simps) simp
      next
        case n1': False
        from "1.IH"(3)[OF False HB refl n1' spB cB n1] obtain B' where "ok (remove_params j (n - 1) B) B'" by blast
        with False HB n1' show ?thesis by (subst remove_params.simps) (simp add: bindM_def)
      qed
    next
      case None
      show ?thesis
      proof (cases "dest_all A")
        case (Some aTb)
        then obtain a T b where aTb: "dest_all A = Some (a, T, b)" by (cases aTb) auto
        from cok_dest_all[OF "1.prems"(2) aTb] have cb: "cok b" by auto
        have sp: "ilength (strip_params b) = j - 1"
          using "1.prems"(1) None aTb by (simp add: strip_params_all ilength_Cons)
        have sh: "spine_hyps A = spine_hyps b" using None aTb by (subst spine_hyps.simps) simp
        from "1.IH"(1)[OF False None aTb refl refl sp cb] "1.prems"(3) sh obtain A' where
          "ok (remove_params (j - 1) n b) A'" by auto
        with False None aTb show ?thesis by (subst remove_params.simps) simp
      next
        case None': None
        have "spine_hyps A = []" using None None' by (subst spine_hyps.simps) simp
        with "1.prems"(3) have "\<not> 0 < n" by simp
        with False None None' show ?thesis by (subst remove_params.simps) simp
      qed
    qed
  qed
qed

lemma flatten_params_ok:
  assumes "length (vl (map fst (strip_params A))) = length (strip_params A)" "cok A"
    "n \<le> ilength (spine_hyps A)"
  shows "\<exists>A'. ok (flatten_params vl n A) A'"
proof -
  let ?ps = "strip_params A"
  let ?vars = "zip (vl (map fst ?ps)) (map snd ?ps)"
  have "ilength ?ps = ilength ?vars" using assms(1) by (simp add: ilength_eq)
  from remove_params_ok[OF this assms(2,3)] show ?thesis
    by (auto simp: flatten_params_def Let_def)
qed

lemma tys_remove_params: "ok (remove_params j n A) A' \<Longrightarrow> cok A \<Longrightarrow> tys A' \<subseteq> tys A"
proof (induction j n A arbitrary: A' rule: remove_params.induct)
  case (1 j n A)
  note rp = "1.prems"(1)
  show ?case
  proof (cases "j = 0 \<and> n \<le> 0")
    case True
    with rp show ?thesis by (subst (asm) remove_params.simps) simp
  next
    case False
    show ?thesis
    proof (cases "dest_imp A")
      case (Some HB)
      then obtain H B where HB: "dest_imp A = Some (H, B)" by (cases HB) auto
      from cok_dest_imp[OF "1.prems"(2) HB] have A: "A = implies $ H $ B" "cok B" by auto
      show ?thesis
      proof (cases "n = 1")
        case True
        with rp False HB have "ok (remove_params j (n - 1) B) A'"
          by (subst (asm) remove_params.simps) simp
        from "1.IH"(2)[OF False HB refl True this A(2)] A(1) show ?thesis by auto
      next
        case n1: False
        with rp False HB obtain B' where B': "ok (remove_params j (n - 1) B) B'"
          and A': "A' = implies $ incr_boundvars j H $ B'"
          by (subst (asm) remove_params.simps) (auto simp: bindM_def split: option.splits res.splits)
        from "1.IH"(3)[OF False HB refl n1 B' A(2)] A A' show ?thesis
          by (auto simp: incr_boundvars_def tys_incr_bv)
      qed
    next
      case None
      show ?thesis
      proof (cases "dest_all A")
        case (Some aTb)
        then obtain a T b where aTb: "dest_all A = Some (a, T, b)" by (cases aTb) auto
        from cok_dest_all[OF "1.prems"(2) aTb] have A: "A = all_const T $ Abs a T b" "cok b" by auto
        with rp False None aTb have r: "ok (remove_params (j - 1) n b) A'"
          by (subst (asm) remove_params.simps) simp
        from "1.IH"(1)[OF False None aTb refl refl r A(2)] A(1) show ?thesis by auto
      next
        case None': None
        with rp False None show ?thesis by (subst (asm) remove_params.simps) (auto split: if_splits)
      qed
    qed
  qed
qed

lemma tys_strip_params: "cok A \<Longrightarrow> (a, T) \<in> set (strip_params A) \<Longrightarrow> all_type T \<in> tys A \<and> T \<in> tys A"
proof (induction A rule: measure_induct_rule[of size])
  case (less A)
  show ?case
  proof (cases "dest_imp A")
    case (Some HB)
    then obtain H B where HB: "dest_imp A = Some (H, B)" by (cases HB) auto
    from cok_dest_imp[OF less.prems(1) HB] less.prems(2) less.IH[of B] HB show ?thesis
      by (auto simp: strip_params_imp dest_imp_size)
  next
    case None
    show ?thesis
    proof (cases "dest_all A")
      case (Some aTb)
      then obtain a' T' b where aTb: "dest_all A = Some (a', T', b)" by (cases aTb) auto
      from cok_dest_all[OF less.prems(1) aTb] less.prems(2) less.IH[of b] None aTb show ?thesis
        by (auto simp: strip_params_all dest_all_size all_const_all_type)
    next
      case None': None
      with None less.prems(2) show ?thesis by (simp add: strip_params_other)
    qed
  qed
qed

lemma tys_flatten_params:
  assumes "ok (flatten_params vl n A) A'" "cok A"
  shows "tys A' \<subseteq> tys A"
proof -
  let ?ps = "strip_params A"
  let ?vars = "zip (vl (map fst ?ps)) (map snd ?ps)"
  from assms(1) obtain A'' where r: "ok (remove_params (ilength ?vars) n A) A''"
    and A': "A' = list_forall ?vars A''"
    by (auto simp: flatten_params_def Let_def)
  have "{all_type T, T} \<subseteq> tys A" if "(a, T) \<in> set ?vars" for a T
  proof -
    from that have "T \<in> set (map snd ?ps)" by (auto elim: in_set_zipE)
    then obtain a' where "(a', T) \<in> set ?ps" by auto
    from tys_strip_params[OF assms(2) this] show ?thesis by simp
  qed
  with tys_remove_params[OF r assms(2)] show ?thesis by (fastforce simp: A' tys_list_forall)
qed

lemma vars_remove_params: "ok (remove_params j n A) A' \<Longrightarrow> vars A' \<subseteq> vars A"
proof (induction j n A arbitrary: A' rule: remove_params.induct)
  case (1 j n A)
  note rp = "1.prems"(1)
  show ?case
  proof (cases "j = 0 \<and> n \<le> 0")
    case True
    with rp show ?thesis by (subst (asm) remove_params.simps) simp
  next
    case False
    show ?thesis
    proof (cases "dest_imp A")
      case (Some HB)
      then obtain H B where HB: "dest_imp A = Some (H, B)" by (cases HB) auto
      then obtain U where A: "A = Const STR ''Pure.imp'' U $ H $ B" by (auto simp: dest_imp_Some)
      show ?thesis
      proof (cases "n = 1")
        case True
        with rp False HB have "ok (remove_params j (n - 1) B) A'"
          by (subst (asm) remove_params.simps) simp
        from "1.IH"(2)[OF False HB refl True this] A show ?thesis by auto
      next
        case n1: False
        with rp False HB obtain B' where B': "ok (remove_params j (n - 1) B) B'"
          and A': "A' = implies $ incr_boundvars j H $ B'"
          by (subst (asm) remove_params.simps) (auto simp: bindM_def split: option.splits res.splits)
        from "1.IH"(3)[OF False HB refl n1 B'] A A' show ?thesis
          by (auto simp: incr_boundvars_def implies_def vars_incr_bv)
      qed
    next
      case None
      show ?thesis
      proof (cases "dest_all A")
        case (Some aTb)
        then obtain a T b where aTb: "dest_all A = Some (a, T, b)" by (cases aTb) auto
        then obtain U where A: "A = Const STR ''Pure.all'' U $ Abs a T b" by (auto simp: dest_all_Some)
        with rp False None aTb have r: "ok (remove_params (j - 1) n b) A'"
          by (subst (asm) remove_params.simps) simp
        from "1.IH"(1)[OF False None aTb refl refl r] A show ?thesis by auto
      next
        case None': None
        with rp False None show ?thesis by (subst (asm) remove_params.simps) (auto split: if_splits)
      qed
    qed
  qed
qed

lemma vars_flatten_params: "ok (flatten_params vl n A) A' \<Longrightarrow> vars A' \<subseteq> vars A"
  using vars_remove_params by (fastforce simp: flatten_params_def Let_def vars_list_forall)

context wf_algebra
begin

lemma norm_term_skip_ok:
  assumes pi: "pinv alg ar A W env []"
  shows "typed env W Ts t propT \<Longrightarrow> cok t \<Longrightarrow> \<forall>U\<in>set Ts \<union> tys t. tyw ar (tyenv env) A U \<Longrightarrow>
    below (maxidx env) t \<Longrightarrow> 0 \<le> n \<Longrightarrow> n \<le> ilength (spine_hyps t) \<Longrightarrow>
    \<exists>t'. okT (norm_term_skip env n t) t'"
proof (induction t arbitrary: n Ts rule: measure_induct_rule[of size])
  case (less t)
  note p = pinvD[OF pi]
  obtain \<rho> where g: "gsol alg ar (tyenv env) \<rho>" by (rule pinv_gsol_exists[OF pi])
  show ?case
  proof (cases "n = 0")
    case True
    from norm_term_pterm[OF pi g less.prems(1)] less.prems(3,4) obtain t' where "norm_term env t = return t'"
      by blast
    with True show ?thesis by (subst norm_term_skip.simps) (simp add: return_def liftMT_def liftM_def liftWT_def returnT_def)
  next
    case False
    show ?thesis
    proof (cases "dest_all t")
      case (Some aTb)
      then obtain a T b where aTb: "dest_all t = Some (a, T, b)" by (cases aTb) auto
      from cok_dest_all[OF less.prems(2) aTb] have t: "t = all_const T $ Abs a T b" and cb: "cok b" by auto
      have tb: "typed env W (T # Ts) b propT" using less.prems(1) t by (simp add: typed_all_const)
      have tw: "\<forall>U\<in>set (T # Ts) \<union> tys b. tyw ar (tyenv env) A U" using less.prems(3) t by auto
      have bb: "below (maxidx env) b" using less.prems(4) t by (simp add: below_def all_const_def)
      have "dest_imp t = None" using aTb by (auto simp: dest_all_Some)
      with aTb have sh: "spine_hyps t = spine_hyps b" by (subst spine_hyps.simps) simp
      have "\<exists>b'. okT (norm_term_skip env n b) b'"
        by (rule less.IH[OF dest_all_size[OF aTb] tb cb tw bb less.prems(5)]) (use less.prems(6) sh in simp)
      then obtain b' where b': "okT (norm_term_skip env n b) b'" by blast
      have "norm_type (tyenv env) T = return (tnorm (tyenv env) T)"
        by (rule norm_type_ok[OF tinv_tacyc[OF p(2)] tinv_tcons_env[OF p(2)] tyw_tcons[OF p(2)]])
          (use less.prems(3) t in auto)
      with False aTb b' show ?thesis by (subst norm_term_skip.simps) (auto simp: return_def)
    next
      case None
      show ?thesis
      proof (cases "dest_imp t")
        case (Some HB)
        then obtain H B where HB: "dest_imp t = Some (H, B)" by (cases HB) auto
        from cok_dest_imp[OF less.prems(2) HB] have t: "t = implies $ H $ B" and cB: "cok B" by auto
        have tB: "typed env W Ts B propT" using less.prems(1) t by (simp add: typed_implies)
        have tw: "\<forall>U\<in>set Ts \<union> tys B. tyw ar (tyenv env) A U" using less.prems(3) t by auto
        have bB: "below (maxidx env) B" using less.prems(4) t by (simp add: below_def implies_def)
        have sh: "spine_hyps t = H # spine_hyps B" using HB by (subst spine_hyps.simps) simp
        have n1: "0 \<le> n - 1" "n - 1 \<le> ilength (spine_hyps B)"
          using less.prems(5,6) False sh by (auto simp: ilength_Cons integer_reps)
        have "\<exists>B'. okT (norm_term_skip env (n - 1) B) B'"
          by (rule less.IH[OF conjunct2[OF dest_imp_size[OF HB]] tB cB tw bB n1])
        then obtain B' where "okT (norm_term_skip env (n - 1) B) B'" by blast
        with False None HB show ?thesis by (subst norm_term_skip.simps) auto
      next
        case None': None
        then have "spine_hyps t = []" using None by (subst spine_hyps.simps) simp
        with less.prems(5,6) False show ?thesis by simp
      qed
    qed
  qed
qed

end


subsection \<open>Typing of a call\<close>

context wf_algebra
begin

text \<open>Further terms of the proof state and the rule are typed in the environment of a call.\<close>

lemma rs_typed_tvinv:
  assumes "tvinv A m env" "\<forall>(X, T)\<in>set rs. \<exists>Wt. wt_mod ar A (tyenv env) W Wt m X T"
  shows "rs_typed ar A rs W env"
proof -
  let ?\<theta> = "tyenv env"
  from assms(1) have te: "vt_is_empty (tenv env)" and mx: "m \<le> maxidx env" and ti: "tinv ar (maxidx env) ?\<theta> A"
    by (simp_all add: tvinv_def)
  have ac: "tacyc ?\<theta>" by (rule tinv_tacyc[OF ti])
  have tw: "tyw ar ?\<theta> A T" if "tyA ar A T" for T
    by (rule tyw_textends[OF ac _ tyw_empty[OF that]]) (simp add: textends_def)
  have "typed env W [] X T \<and> below (maxidx env) X \<and> (\<forall>U\<in>tys X. tyw ar ?\<theta> A U)"
    if "wt_mod ar A ?\<theta> W Wt m X T" for X T Wt
  proof -
    from that have h: "has_type Wt [] X T" and ag: "\<forall>x\<in>vars X. tnorm ?\<theta> (Wt x) = tnorm ?\<theta> (W x)"
      and w: "below m X" "\<forall>U\<in>tys X. tyA ar A U"
      by (simp_all add: wt_mod_def wt_term_def)
    from has_type_tnormt[OF h] have "has_type (\<lambda>x. tnorm ?\<theta> (Wt x)) [] (tnormt ?\<theta> X) (tnorm ?\<theta> T)"
      by simp
    then have "has_type (tctx env W) [] (tnormt ?\<theta> X) (tnorm ?\<theta> T)"
      by (rule has_type_vars) (use ag te in \<open>simp add: vtyp_def vt_is_empty_lookup\<close>)
    then show ?thesis using w mx tw by (auto simp: typed_def intro: below_mono)
  qed
  with assms(2) show ?thesis by (fastforce simp: rs_typed_def)
qed

text \<open>
  The typing of a call: the proof state and the rule are typed by a common typing \<open>W\<close> modulo the
  type environment of the call.
\<close>

lemma call_typing:
  assumes state: "wt_thm ar A Ws smax stpairs (list_implies (Bs @ [Bi]) C)"
    and rule: "wt_thm ar A Wr rmax rtpairs rprop"
    and A: "scons A" "\<forall>p\<in>A. snd (fst p) \<le> max rmax smax" "\<forall>x. tyA ar A (Ws x)" "\<forall>x. tyA ar A (Wr x)"
    and inc: "incremented \<Longrightarrow>
      \<forall>x\<in>vars_thm stpairs (list_implies (Bs @ [Bi]) C) \<inter> vars_thm rtpairs rprop. Ws x = Wr x"
    and e1: "incremented \<Longrightarrow> env = empty_env (max rmax smax)"
    and e2: "\<not> incremented \<Longrightarrow> okT (unify_var_types alg (stpairs, list_implies (Bs @ [Bi]) C) (rtpairs, rprop)
      (empty_env (max rmax smax))) (Some env)"
  obtains W where "tvinv A (max rmax smax) env" "\<forall>x. tyA ar A (W x)"
    "\<forall>x\<in>vars_thm stpairs (list_implies (Bs @ [Bi]) C). tnorm (tyenv env) (Ws x) = tnorm (tyenv env) (W x)"
    "\<forall>x\<in>vars_thm rtpairs rprop. tnorm (tyenv env) (Wr x) = tnorm (tyenv env) (W x)"
proof -
  let ?S = "list_implies (Bs @ [Bi]) C"
  let ?VS = "vars_thm stpairs ?S"
  define W where "W x = (if x \<in> ?VS then Ws x else Wr x)" for x
  have tW: "\<forall>x. tyA ar A (W x)" using A(3,4) by (simp add: W_def)
  have aS: "\<forall>x\<in>?VS. tnorm (tyenv env) (Ws x) = tnorm (tyenv env) (W x)" by (simp add: W_def)
  show thesis
  proof (cases incremented)
    case True
    have "tvinv A (max rmax smax) env" using e1[OF True] tvinv_empty_env[OF A(1,2)] by simp
    moreover have "\<forall>x\<in>vars_thm rtpairs rprop. tnorm (tyenv env) (Wr x) = tnorm (tyenv env) (W x)"
      using inc[OF True] by (auto simp: W_def)
    ultimately show thesis using that tW aS by blast
  next
    case False
    have vps: "(x, Wt x) \<in> vps_thm tps P" if "wt_thm ar A Wt m tps P" "x \<in> vars_thm tps P" for Wt m tps P x
    proof -
      from that(2) consider "x \<in> vars P" | t u where "(t, u) \<in> set tps" "x \<in> vars t \<union> vars u"
        by (auto simp: vars_thm_def)
      then show ?thesis
      proof cases
        case 1
        with that(1) show ?thesis by (auto simp: wt_thm_def wt_term_def vps_thm_def dest: has_type_vps)
      next
        case 2
        with that(1) obtain T where "has_type Wt [] t T" "has_type Wt [] u T"
          by (auto simp: wt_thm_def wt_term_def)
        with 2 show ?thesis by (auto simp: vps_thm_def dest: has_type_vps)
      qed
    qed
    have tyv: "tyA ar A T" if "wt_thm ar A Wt m tps P" "(x, T) \<in> vps_thm tps P" for Wt m tps P x T
    proof -
      from that(2) consider "(x, T) \<in> vps P" | t u where "(t, u) \<in> set tps" "(x, T) \<in> vps t \<union> vps u"
        by (auto simp: vps_thm_def)
      then show ?thesis
      proof cases
        case 1
        with that(1) show ?thesis by (auto simp: wt_thm_def wt_term_def dest: vps_tys)
      next
        case 2
        with that(1) obtain T' where "wt_term ar A Wt m t T'" "wt_term ar A Wt m u T'"
          unfolding wt_thm_def by blast
        with 2 show ?thesis by (auto simp: wt_term_def dest: vps_tys)
      qed
    qed
    have "\<forall>(x, T)\<in>vps_thm stpairs ?S \<union> vps_thm rtpairs rprop. tyA ar A T"
      using tyv[OF state] tyv[OF rule] by blast
    note uv = unify_var_types_tvinv[OF e2[OF False] A(1,2) this]
    have "\<forall>x\<in>vars_thm rtpairs rprop. tnorm (tyenv env) (Wr x) = tnorm (tyenv env) (W x)"
    proof
      fix x assume x: "x \<in> vars_thm rtpairs rprop"
      show "tnorm (tyenv env) (Wr x) = tnorm (tyenv env) (W x)"
      proof (cases "x \<in> ?VS")
        case True
        from uv(2)[of x "Wr x" "Ws x"] vps[OF rule x] vps[OF state True] show ?thesis
          by (simp add: W_def True)
      qed (simp add: W_def)
    qed
    with uv(1) that tW aS show thesis by blast
  qed
qed

end


subsection \<open>The new premises are typed\<close>

lemma tys_ren_term[simp]: "tys (ren_term r t) = tys t"
  by (induction r t rule: ren_term.induct) auto

lemma tys_lift_pre_ren: "tys (lift_pre p (ren_term r X)) = tys (lift_pre p X)"
proof (induction p)
  case (Cons i p)
  then show ?case by (cases i) auto
qed simp

lemma ren_ix_inj:
  assumes "x1 \<in> vars (strip_lifted B A1)" "A1 \<in> set As" "x2 \<in> vars (strip_lifted B A2)" "A2 \<in> set As"
    "ren_ix (rename_bvs dpairs tpairs B As) x1 = ren_ix (rename_bvs dpairs tpairs B As) x2"
  shows "x1 = x2"
proof -
  have "fst x1 = fst x2"
    by (rule rename_bvs_inj[of "fst x1" "fst x2" As B dpairs tpairs]) (use assms in \<open>force simp: ren_ix_def\<close>)+
  moreover have "snd x1 = snd x2" using assms(5) by (simp add: ren_ix_def)
  ultimately show ?thesis by (simp add: prod_eq_iff)
qed

text \<open>The cases of \<^const>\<open>newAs\<close>, with the renaming of \<^const>\<open>rename_bvs\<close>.\<close>

lemma newAs_cases:
  assumes "okT (newAs vl ctx As0 n dps tps1) na"
  shows "list_all2 (\<lambda>A1 A'. if bc_flatten ctx then ok (flatten_params vl n A1) A' else A1 = A')
      (na_oldAs na) (na_As na)"
    "na_oldAs na = As0 \<or> (bc_lifted ctx \<and> na_oldAs na =
      map (strip_apply (ren_term (rename_bvs dps (bc_rtpairs ctx @ tps1) (bc_Bi ctx) As0)) (bc_Bi ctx)) As0)"
proof -
  have h: "\<not> okT (case e of UExn (PExn (Term_Error _ _)) \<Rightarrow> raiseT (THM (STR ''bicompose: 1st premise'') 0 Orule)
        | _ \<Rightarrow> raiseT e) y" for e and y :: newas
    by (auto simp: raiseT_def split: texn.splits uexn.splits exn.splits)
  from assms show "list_all2 (\<lambda>A1 A'. if bc_flatten ctx then ok (flatten_params vl n A1) A' else A1 = A')
      (na_oldAs na) (na_As na)"
    "na_oldAs na = As0 \<or> (bc_lifted ctx \<and> na_oldAs na =
      map (strip_apply (ren_term (rename_bvs dps (bc_rtpairs ctx @ tps1) (bc_Bi ctx) As0)) (bc_Bi ctx)) As0)"
    unfolding newAs_def
    by (auto simp: okT_handleT h ok_mapM list.rel_eq rename_bvars_def Let_def split: if_splits option.splits)
qed

context wf_algebra
begin

text \<open>
  The new premises are typed in the environment of a unifier, for a typing that agrees on the
  variables of the proof state, if the premises of the rule are and if the variables of the rule
  that do not occur in the problem are not bound in the environment.
\<close>

lemma newAs_typed:
  assumes na: "okT (newAs vl ctx As0 n dps tps1) na"
    and lr: "bc_lifted ctx \<Longrightarrow> lifted_rule (bc_smax ctx) (bc_Bi ctx) As0 B"
    and ib: "ibelow (bc_smax ctx) (bc_Bi ctx)"
    and pi: "pinv alg ar A W env []"
    and ty: "\<forall>X\<in>set As0. typed env W [] X propT \<and> wfp ar X \<and> below m X \<and> (\<forall>U\<in>tys X. tyw ar (tyenv env) A U)"
    and b0: "\<forall>X\<in>set As0. below m0 X"
    and fresh: "\<And>v. bc_lifted ctx \<Longrightarrow> bc_smax ctx < snd v \<Longrightarrow> snd v \<le> m0 \<Longrightarrow> (\<forall>(t, u)\<in>set dps. fst v \<notin> fst ` vars t) \<Longrightarrow>
      (\<forall>(t, u)\<in>set (bc_rtpairs ctx @ tps1). fst v \<notin> fst ` vars t \<and> fst v \<notin> fst ` vars u) \<Longrightarrow>
      vt_lookup (tenv env) v = None \<and> v \<notin> fst ` bvps env"
    and vl: "\<And>xs. length (vl xs) = length xs"
  obtains W' where "pinv alg ar A W' env []" "\<forall>x. snd x \<le> bc_smax ctx \<longrightarrow> W' x = W x"
    "\<forall>X\<in>set (na_As na). typed env W' [] X propT \<and> wfp ar X \<and> below m X \<and> (\<forall>U\<in>tys X. tyw ar (tyenv env) A U)"
proof -
  let ?P = "\<lambda>W' X. typed env W' [] X propT \<and> wfp ar X \<and> below m X \<and> (\<forall>U\<in>tys X. tyw ar (tyenv env) A U)"
  note nc = newAs_cases[OF na]
  have wfN: "\<forall>X\<in>set (na_As na). wfp ar X"
    using newAs_wfp[OF na lr _ vl] ty by blast
  text \<open>Flattening keeps the typing.\<close>
  have flat: "\<forall>X\<in>set (na_As na). ?P W' X" if "\<forall>X\<in>set (na_oldAs na). ?P W' X" for W'
  proof -
    have "list_all2 (\<lambda>A1 A'. ?P W' A1 \<longrightarrow> typed env W' [] A' propT \<and> below m A' \<and>
        (\<forall>U\<in>tys A'. tyw ar (tyenv env) A U)) (na_oldAs na) (na_As na)"
    proof (rule list_all2_mono[OF nc(1)])
      fix A1 A' assume f: "if bc_flatten ctx then ok (flatten_params vl n A1) A' else A1 = A'"
      show "?P W' A1 \<longrightarrow> typed env W' [] A' propT \<and> below m A' \<and> (\<forall>U\<in>tys A'. tyw ar (tyenv env) A U)"
      proof (cases "bc_flatten ctx")
        case True
        with f have fl: "ok (flatten_params vl n A1) A'" by simp
        show ?thesis
          using typed_flatten_params[OF fl vl[of "map fst (strip_params A1)", unfolded length_map], of env W' "[]"]
            tys_flatten_params[OF fl] vars_flatten_params[OF fl]
          by (auto simp: wfp_def below_def)
      qed (use f in simp)
    qed
    from list_all2_imp_all[OF this that] wfN show ?thesis by blast
  qed
  from nc(2) show thesis
  proof (elim disjE conjE)
    assume o: "na_oldAs na = As0"
    have "\<forall>X\<in>set (na_As na). ?P W X" by (rule flat) (use ty o in simp)
    then show thesis by (intro that[OF pi]) simp_all
  next
    assume lf: "bc_lifted ctx" and old: "na_oldAs na =
      map (strip_apply (ren_term (rename_bvs dps (bc_rtpairs ctx @ tps1) (bc_Bi ctx) As0)) (bc_Bi ctx)) As0"
    let ?r = "rename_bvs dps (bc_rtpairs ctx @ tps1) (bc_Bi ctx) As0"
    from lr[OF lf] obtain p Bi0 As0' where Bi: "bc_Bi ctx = lift_pre p Bi0"
      and ok: "\<forall>i\<in>set p. litem_ok i" and at: "atomic Bi0" and As0: "As0 = map (lift_pre p) As0'"
      and big: "\<forall>X\<in>set As0'. \<forall>x\<in>vars X. bc_smax ctx < snd x"
      by (rule lifted_rule_lift_pre)
    define RV where "RV = (\<Union>X\<in>set As0'. vars X)"
    have slB: "strip_lifted (bc_Bi ctx) (lift_pre p X) = X" for X
      by (simp add: Bi strip_lifted_lift_pre[OF ok at])
    have inj: "x1 = x2" if "x1 \<in> RV" "x2 \<in> RV" "ren_ix ?r x1 = ren_ix ?r x2" for x1 x2
    proof -
      from that(1,2) obtain X1 X2 where "X1 \<in> set As0'" "x1 \<in> vars X1" "X2 \<in> set As0'" "x2 \<in> vars X2"
        by (auto simp: RV_def)
      with ren_ix_inj[of x1 "bc_Bi ctx" "lift_pre p X1" As0 x2 "lift_pre p X2" dps "bc_rtpairs ctx @ tps1"]
        that(3) show ?thesis by (simp add: slB As0)
    qed
    have pv: "\<forall>x\<in>pvars p. snd x \<le> bc_smax ctx"
      using ib Bi lsplit_ok by (auto simp: ibelow_def vars_lift_pre)
    have RVm: "snd x \<le> m" if "x \<in> RV" for x
      using that ty As0 by (auto simp: RV_def below_def vars_lift_pre)
    have RVm0: "snd x \<le> m0" if "x \<in> RV" for x
      using that b0 As0 by (auto simp: RV_def below_def vars_lift_pre)
    text \<open>Renamed variables occur neither in the problem nor in the environment.\<close>
    have fr: "vt_lookup (tenv env) v = None \<and> v \<notin> fst ` bvps env"
      if "x \<in> RV" "ren_ix ?r x \<noteq> x" "v = x \<or> v = ren_ix ?r x" for x v
    proof (rule fresh[OF lf])
      have sx: "bc_smax ctx < snd x" using that(1) big by (auto simp: RV_def)
      have rn: "ren_name (fst ?r) (fst x) \<noteq> fst x" using that(2) by (cases x) (auto simp: ren_ix_def)
      show "bc_smax ctx < snd v" "snd v \<le> m0" using that(3) sx RVm0[OF that(1)] by (auto simp: ren_ix_def)
      have "fst v = fst x \<or> fst v = ren_name (fst ?r) (fst x)" using that(3) by (auto simp: ren_ix_def)
      then show "\<forall>(t, u)\<in>set dps. fst v \<notin> fst ` vars t"
        "\<forall>(t, u)\<in>set (bc_rtpairs ctx @ tps1). fst v \<notin> fst ` vars t \<and> fst v \<notin> fst ` vars u"
        using rename_bvs_unknowns[OF rn] rename_bvs_target[OF rn] by (elim disjE; simp only:)+
    qed
    define W' where "W' (v :: indexname) = (if \<exists>x\<in>RV. ren_ix ?r x = v \<and> x \<noteq> v
      then W (SOME x. x \<in> RV \<and> ren_ix ?r x = v \<and> x \<noteq> v) else W v)" for v
    have W'r: "W' (ren_ix ?r x) = W x" if "x \<in> RV" for x
    proof (cases "ren_ix ?r x = x")
      case True
      have "\<not> (\<exists>x'\<in>RV. ren_ix ?r x' = x \<and> x' \<noteq> x)" using inj that True by metis
      with True show ?thesis by (simp add: W'_def)
    next
      case False
      have "(SOME x'. x' \<in> RV \<and> ren_ix ?r x' = ren_ix ?r x \<and> x' \<noteq> ren_ix ?r x) = x"
        by (rule some_equality) (use that False inj in auto)
      with that False show ?thesis by (auto simp: W'_def)
    qed
    have W'ch: "\<exists>x\<in>RV. ren_ix ?r x = v \<and> x \<noteq> v" if "W' v \<noteq> W v" for v
      using that by (auto simp: W'_def split: if_splits)
    have W'small: "\<forall>x. snd x \<le> bc_smax ctx \<longrightarrow> W' x = W x"
    proof (intro allI impI)
      fix v :: indexname assume v: "snd v \<le> bc_smax ctx"
      show "W' v = W v"
      proof (rule ccontr)
        assume "W' v \<noteq> W v"
        from W'ch[OF this] obtain x where x: "x \<in> RV" "ren_ix ?r x = v" by blast
        from x(1) big have "bc_smax ctx < snd x" by (auto simp: RV_def)
        moreover have "snd v = snd x" using x(2) by (auto simp: ren_ix_def)
        ultimately show False using v by simp
      qed
    qed
    have pi': "pinv alg ar A W' env []"
    proof (rule pinv_cong[OF pi])
      show "\<forall>x. tyw ar (tyenv env) A (W' x)" using pinvD(5)[OF pi] by (simp add: W'_def)
      fix v assume "W' v \<noteq> W v"
      from W'ch[OF this] obtain x where "x \<in> RV" "ren_ix ?r x = v" "x \<noteq> v" by blast
      with fr[of x v] show "vt_lookup (tenv env) v = None \<and> v \<notin> fst ` bvps env \<and>
          (\<forall>(rb, t, u)\<in>set []. v \<notin> vars t \<and> v \<notin> vars u)" by auto
    qed
    have tc: "tctx env W' (ren_ix ?r x) = tctx env W x" if "x \<in> RV" for x
    proof (cases "ren_ix ?r x = x")
      case True
      have "W' x = W x" using W'r[OF that] True by simp
      with True show ?thesis by (auto simp: vtyp_def split: option.splits)
    next
      case False
      with fr[OF that False] W'r[OF that] show ?thesis by (simp add: vtyp_def)
    qed
    text \<open>The renamed premises.\<close>
    have "?P W' X" if "X \<in> set (na_oldAs na)" for X
    proof -
      from that old obtain X0 where X0: "X0 \<in> set As0'" "X = lift_pre p (ren_term ?r X0)"
        by (auto simp: As0 Bi strip_apply_lift_pre[OF ok at])
      have P0: "?P W (lift_pre p X0)" using ty X0(1) As0 by auto
      have tX0: "typed env W (rev (ptys p) @ []) X0 propT"
        by (rule typed_lift_preD[OF ok _ conjunct1[OF P0]]) (use P0 in \<open>simp add: wfp_def\<close>)
      have "typed env W' (rev (ptys p) @ []) (ren_term ?r X0) propT"
        by (rule typed_ren_term[OF tX0]) (use tc X0(1) in \<open>auto simp: RV_def\<close>)
      then have "typed env W' [] (lift_pre p (ren_term ?r X0)) propT"
      proof (rule typed_lift_pre_cong[OF ok _ conjunct1[OF P0], rotated])
        show "cok (lift_pre p X0)" using P0 by (simp add: wfp_def)
        show "\<forall>H\<in>set (phyps p). \<forall>x\<in>vars H. tctx env W' x = tctx env W x"
        proof (intro ballI)
          fix H x assume "H \<in> set (phyps p)" "x \<in> vars H"
          with pv vars_phyps have "snd x \<le> bc_smax ctx" by blast
          with W'small have "W' x = W x" by blast
          then show "tctx env W' x = tctx env W x" by (simp add: vtyp_def split: option.splits)
        qed
      qed
      then have "typed env W' [] X propT" using X0(2) by simp
      moreover have "below m X"
      proof -
        have "snd x \<le> m" if "x \<in> vars X0" for x using RVm[of x] X0(1) that by (auto simp: RV_def)
        with P0 X0(2) show ?thesis by (fastforce simp: below_def vars_lift_pre vars_ren_term)
      qed
      moreover have "\<forall>U\<in>tys X. tyw ar (tyenv env) A U"
      proof -
        have "tys X = tys (lift_pre p X0)" by (simp add: X0(2) tys_lift_pre_ren)
        with P0 show ?thesis by simp
      qed
      moreover have "wfp ar X" using P0 X0(2) by (simp add: wfp_lift_pre_ren_term)
      ultimately show ?thesis by blast
    qed
    with flat have "\<forall>X\<in>set (na_As na). ?P W' X" by blast
    with pi' W'small show thesis by (rule that)
  qed
qed

end


subsection \<open>The new theorem is built\<close>

lemma list_all2_exI: "\<forall>x\<in>set xs. \<exists>y. P x y \<Longrightarrow> \<exists>ys. list_all2 P xs ys"
  by (induction xs) (auto intro: list_all2_Cons)

lemma ok_mapM_exI: "\<forall>x\<in>set xs. \<exists>y. ok (f x) y \<Longrightarrow> \<exists>ys. ok (mapM f xs) ys"
  using list_all2_exI[of xs "\<lambda>x y. ok (f x) y"] by (simp add: ok_mapM)

lemma okT_mapT_exI: "\<forall>x\<in>set xs. \<exists>y. okT (f x) y \<Longrightarrow> \<exists>ys. okT (mapT f xs) ys"
  using list_all2_exI[of xs "\<lambda>x y. okT (f x) y"] by (simp add: okT_mapT)

context wf_algebra
begin

text \<open>A typed term is normalized without an exception.\<close>

lemma norm_term_ok:
  assumes "pinv alg ar A W env []" "typed env W Ts t T" "\<forall>U\<in>set Ts \<union> tys t. tyw ar (tyenv env) A U"
    "below (maxidx env) t"
  shows "\<exists>t'. ok (norm_term env t) t'"
proof -
  obtain \<rho> where g: "gsol alg ar (tyenv env) \<rho>" by (rule pinv_gsol_exists[OF assms(1)])
  from norm_term_pterm[OF assms(1) g assms(2-4)] show ?thesis by (auto simp: return_def)
qed

lemma ptpok_norm_ok:
  assumes "pinv alg ar A W env []" "ptpok ar A W env e0 (t, u)"
  shows "\<exists>t'. ok (norm_term env t) t'" "\<exists>u'. ok (norm_term env u) u'"
proof -
  from assms(2) obtain rb a b B where t: "t = rlist_abs rb a" and u: "u = rlist_abs rb b"
    and tw: "\<forall>U\<in>snd ` set rb \<union> tys a \<union> tys b. tyw ar (tyenv env) A U"
    and ty: "typed env W (map snd rb) a B" "typed env W (map snd rb) b B"
    and bl: "below (maxidx env) a" "below (maxidx env) b"
    by (auto simp: ptpok_def)
  show "\<exists>t'. ok (norm_term env t) t'"
    unfolding t by (rule norm_term_ok[OF assms(1) typed_rlist_abs[OF ty(1)]])
      (use tw bl in \<open>auto simp: tys_rlist_abs below_def vars_rlist_abs\<close>)
  show "\<exists>u'. ok (norm_term env u) u'"
    unfolding u by (rule norm_term_ok[OF assms(1) typed_rlist_abs[OF ty(2)]])
      (use tw bl in \<open>auto simp: tys_rlist_abs below_def vars_rlist_abs\<close>)
qed

text \<open>
  \<^const>\<open>addth\<close> succeeds, or raises \<open>COMPOSE\<close> if instantiations of the proof state are forbidden,
  if the flex-flex pairs, the other subgoals, the conclusion and the new premises are typed.
\<close>

definition wtprop :: "(indexname \<times> psort) set \<Rightarrow> (indexname \<Rightarrow> ptyp) \<Rightarrow> env \<Rightarrow> pterm \<Rightarrow> bool" where
  "wtprop A W env X \<longleftrightarrow> typed env W [] X propT \<and> wfp ar X \<and> below (maxidx env) X \<and>
    (\<forall>U\<in>tys X. tyw ar (tyenv env) A U)"

lemma wtprop_norm_ok: "pinv alg ar A W env [] \<Longrightarrow> wtprop A W env X \<Longrightarrow> \<exists>X'. ok (norm_term env X) X'"
  by (rule norm_term_ok) (auto simp: wtprop_def)

lemma addth_ok:
  assumes pi: "pinv alg ar A W env []" and tps: "\<forall>ab\<in>set tps. \<exists>e0. ptpok ar A W env e0 ab"
    and BC: "\<forall>X\<in>insert (bc_C ctx) (set (bc_Bs ctx)). wtprop A W env X"
    and pi': "pinv alg ar A W' env []" and As: "\<forall>X\<in>set (na_As na). wtprop A W' env X"
    and sk: "bc_lifted ctx \<Longrightarrow> 0 \<le> bc_nlift ctx \<and> (\<forall>X\<in>set (na_As na). bc_nlift ctx \<le> ilength (spine_hyps X))"
  shows "(\<exists>r. okT (addth ctx A1o na (env, tps)) r) \<or>
    (bc_match ctx \<and> (\<exists>evs. addth ctx A1o na (env, tps) = Some (evs, TErr COMPOSE)))"
proof -
  have nt: "\<exists>tps'. ok (mapM (norm_tpair env) tps) tps'"
  proof (rule ok_mapM_exI, intro ballI)
    fix ab assume "ab \<in> set tps"
    with tps obtain e0 t u where ab: "ab = (t, u)" "ptpok ar A W env e0 (t, u)" by (cases ab) blast
    from ptpok_norm_ok[OF pi ab(2)] show "\<exists>y. ok (norm_tpair env ab) y"
      by (auto simp: norm_tpair_def ab(1))
  qed
  have nBC: "\<exists>X'. ok (norm_term env X) X'" if "X \<in> insert (bc_C ctx) (set (bc_Bs ctx))" for X
    using wtprop_norm_ok[OF pi] BC that by blast
  have nA: "\<exists>X'. ok (norm_term env X) X'" if "X \<in> set (na_As na)" for X
    using wtprop_norm_ok[OF pi'] As that by blast
  show ?thesis
  proof (cases "env_is_empty env")
    case True
    then show ?thesis by (simp add: addth_def)
  next
    case False
    from nt obtain tps' where tps': "ok (mapM (norm_tpair env) tps) tps'" by blast
    show ?thesis
    proof (cases "above env (bc_smax ctx)")
      case ab: True
      show ?thesis
      proof (cases "bc_lifted ctx")
        case True
        have "\<exists>As'. okT (mapT (norm_term_skip env (bc_nlift ctx)) (na_As na)) As'"
        proof (rule okT_mapT_exI, intro ballI)
          fix X assume X: "X \<in> set (na_As na)"
          from As X have t: "wtprop A W' env X" by blast
          show "\<exists>X'. okT (norm_term_skip env (bc_nlift ctx) X) X'"
            by (rule norm_term_skip_ok[OF pi', of "[]"]) (use t sk[OF True] X in \<open>auto simp: wtprop_def wfp_def\<close>)
        qed
        then show ?thesis using False ab True tps' by (auto simp: addth_def)
      next
        case nl: False
        from ok_mapM_exI[of "na_As na" "norm_term env"] nA obtain As' where
          "ok (mapM (norm_term env) (na_As na)) As'" by blast
        then show ?thesis using False ab nl tps' by (auto simp: addth_def)
      qed
    next
      case nab: False
      show ?thesis
      proof (cases "bc_match ctx")
        case True
        then show ?thesis using False nab tps' by (auto simp: addth_def raiseT_def bindT_def liftMT_def liftWT_def liftM_def)
      next
        case nm: False
        from ok_mapM_exI[of "bc_Bs ctx @ na_As na" "norm_term env"] nA nBC obtain Hs where
          "ok (mapM (norm_term env) (bc_Bs ctx @ na_As na)) Hs" by fastforce
        moreover from nBC obtain C' where "ok (norm_term env (bc_C ctx)) C'" by blast
        ultimately show ?thesis using False nab nm tps' by (auto simp: addth_def)
      qed
    qed
  qed
qed

end


subsection \<open>Finite enumerations of results\<close>

text \<open>Pulling the sequence of results repeatedly yields \<open>rs\<close> and then the end of the sequence.\<close>

inductive bevals :: "'u bops \<Rightarrow> 'u bseq \<Rightarrow> bres list \<Rightarrow> bool" for ops where
  Nil: "okT (bpull ops s) None \<Longrightarrow> bevals ops s []"
| Cons: "okT (bpull ops s) (Some (r, s')) \<Longrightarrow> bevals ops s' rs \<Longrightarrow> bevals ops s (r # rs)"

lemma bevals_cong:
  assumes "\<And>x. okT (bpull ops s) x \<longleftrightarrow> okT (bpull ops s') x" "bevals ops s' rs"
  shows "bevals ops s rs"
  using assms(2) by cases (auto intro: bevals.intros simp: assms(1))

lemma bevals_results: "bevals ops s rs \<Longrightarrow> r \<in> set rs \<Longrightarrow> bresult ops s r"
  by (induction rule: bevals.induct) (auto intro: bresult.intros)

text \<open>The length of the enumeration of a sequence of unifiers.\<close>

definition elen :: "cfg \<Rightarrow> seq \<Rightarrow> nat" where
  "elen cfg s = length (THE xs. evals cfg s xs)"

lemma elen: "evals cfg s xs \<Longrightarrow> elen cfg s = length xs"
  unfolding elen_def by (rule arg_cong[of _ _ length], rule the_equality) (auto dest: evals_det)

context wf_algebra
begin

definition ulen :: "bspec \<Rightarrow> pterm \<Rightarrow> nat" where
  "ulen sp asm = (case unifiers alg (bs_env sp) (eres_prob sp asm) of Some (Ok s) \<Rightarrow> elen (bs_cfg sp) s | _ \<Rightarrow> 0)"

text \<open>A measure of the remaining work in a sequence of results.\<close>

fun bmu :: "bspec \<Rightarrow> seq bseq \<Rightarrow> nat" where
  "bmu sp BS_Empty = 0"
| "bmu sp (BS_Its ctx A na xq yq) =
    (case xq of UQ_Cell (_, us) \<Rightarrow> Suc (elen (bs_cfg sp) us) | UQ_Seq us \<Rightarrow> elen (bs_cfg sp) us) + 1 + bmu sp yq"
| "bmu sp (BS_Tryasms ctx er asms n) = (\<Sum>asm\<leftarrow>asms. 3 + ulen sp asm) + 1"

text \<open>
  The assumptions on a call: the new premises can be computed for the first unifier of each
  problem, and the new theorem can be built for each unifier.
\<close>

definition newas_ok :: "bspec \<Rightarrow> bool" where
  "newas_ok sp \<longleftrightarrow>
    (\<not> bs_eres sp \<longrightarrow> (\<forall>tps1. \<exists>na. okT (newAs (bs_vl sp) (bs_ctx sp) (rev (bs_rAs sp)) 0 [bc_BBi (bs_ctx sp)] tps1) na)) \<and>
    (bs_eres sp \<longrightarrow> (\<forall>n asm tps1. 1 \<le> n \<longrightarrow> nat_of_integer n \<le> length (asms_of sp) \<longrightarrow>
      asm = asms_of sp ! (nat_of_integer n - 1) \<longrightarrow>
      (\<exists>na. okT (newAs (bs_vl sp) (bs_ctx sp) (er_As (eres_of sp)) n
        [bc_BBi (bs_ctx sp), (er_concl' (eres_of sp), rlist_abs (er_params (eres_of sp)) asm)] tps1) na)))"

definition results_ok :: "bspec \<Rightarrow> bool" where
  "results_ok sp \<longleftrightarrow> (\<forall>A na tus env' tps. itsok sp A na tus \<longrightarrow>
    uelem alg (bs_cfg sp) (bs_env sp) tus (El_R env' tps) \<longrightarrow>
    (\<exists>r. okT (addth (bs_ctx sp) A na (env', tps)) r) \<or>
    (bc_match (bs_ctx sp) \<and> (\<exists>evs. addth (bs_ctx sp) A na (env', tps) = Some (evs, TErr COMPOSE))))"

end


context wf_algebra
begin

lemma unifiers_ops_ok:
  assumes "cfg_alg cfg = alg" "finite A" "pinv alg ar A W env (dps_of tus)"
  obtains us where "okT (bo_unifiers (unify_ops cfg vl) env tus) us" "uinv cfg A env tus us"
    "unifiers alg env tus = Some (Ok us)"
proof -
  from unifiers_uinv[OF assms] obtain s where s: "liftMT (unifiers alg env tus) = returnT s" "uinv cfg A env tus s"
    by blast
  have "unifiers alg env tus = Some (Ok s)"
    using s(1) by (cases "unifiers alg env tus") (auto simp: liftMT_def liftWT_def liftM_def returnT_def
      split: res.splits ures.splits)
  with s assms(1) show thesis by (intro that[of s]) (simp_all add: unify_ops_def)
qed

lemma uinv_elen:
  assumes "uinv cfg A env tus us" "okT (upull cfg us) (Some (x, us'))"
  shows "elen cfg us = Suc (elen cfg us')"
proof -
  from assms(1) obtain xs where es: "evals cfg us xs" by (auto simp: uinv_def)
  from assms(2) obtain evs y where p: "pull cfg us = Some (evs, UOk (Some (y, us')))"
    by (auto simp: upull_def bindW_def liftWT_def returnW_def raiseW_def
        split: option.splits ures.splits elem.splits)
  from evals_pull_Some[OF es p] obtain xs' where "xs = y # xs'" "evals cfg us' xs'" by blast
  with es show ?thesis by (simp add: elen)
qed

text \<open>The elimination resolution of the remaining assumptions terminates.\<close>

lemma tryasms_ok:
  assumes "cfg_alg (bs_cfg sp) = alg" "finite (bs_A sp)" "pinv_all sp" "bs_eres sp" "newas_ok sp"
  shows "ops = unify_ops (bs_cfg sp) (bs_vl sp) \<Longrightarrow> ctx = bs_ctx sp \<Longrightarrow> er = eres_of sp \<Longrightarrow>
    1 \<le> n \<Longrightarrow> asms = drop (nat_of_integer n - 1) (asms_of sp) \<Longrightarrow>
    \<exists>s. okT (tryasms ops ctx er asms n) s \<and> bmu sp s < bmu sp (BS_Tryasms ctx er asms n)"
proof (induction ops ctx er asms n rule: tryasms.induct)
  case 1
  then show ?case by simp
next
  case (2 ops ctx er asm rest n)
  note eqs = "2.prems"(1-3)
  note prems = "2.prems"(4-5)
  note nth = asms_of_nth[OF prems(2,1) refl]
  have n1: "1 \<le> n + 1" using prems(1) by simp
  have mono: "bmu sp (BS_Tryasms ctx er rest (n + 1)) < bmu sp (BS_Tryasms ctx er (asm # rest) n)" by simp
  show ?case
  proof (cases "could_unify asm (er_concl er)")
    case False
    from "2.IH"(2)[OF False eqs n1 nth(3)] False mono show ?thesis by auto
  next
    case True
    let ?asm' = "rlist_abs (er_params er) asm"
    let ?tus = "(?asm', er_concl' er) # bc_dpairs ctx"
    have tus: "?tus = eres_prob sp asm" using eqs by (simp add: eres_prob_def)
    have env: "er_env er = bs_env sp" using eqs by (simp add: eres_of_def split: list.splits prod.splits)
    from prems(2) have "asm \<in> set (asms_of sp)" by (metis in_set_dropD list.set_intros(1))
    with assms(3,4) obtain W where pi: "pinv alg ar (bs_A sp) W (bs_env sp) (dps_of (eres_prob sp asm))"
      by (auto simp: pinv_all_def)
    obtain us where us: "okT (bo_unifiers ops (er_env er) ?tus) us" and ui: "uinv (bs_cfg sp) (bs_A sp) (bs_env sp) (eres_prob sp asm) us"
      and un: "unifiers alg (bs_env sp) (eres_prob sp asm) = Some (Ok us)"
      by (rule unifiers_ops_ok[OF assms(1,2) pi]) (use eqs env tus in auto)
    show ?thesis
    proof (rule upull_uinv[OF ui], goal_cases none some)
      case none
      then obtain evs where r: "okT (bo_pull ops us) None" using eqs by (auto simp: unify_ops_def)
      from "2.IH"(1)[OF True refl us r refl eqs n1 nth(3)] obtain s where
        "okT (tryasms ops ctx er rest (n + 1)) s" "bmu sp s < bmu sp (BS_Tryasms ctx er rest (n + 1))"
        by blast
      with True us r mono show ?thesis by (auto simp: Let_def)
    next
      case (some env' tps us')
      have r: "okT (bo_pull ops us) (Some ((env', tps), us'))" using some(1) eqs by (simp add: unify_ops_def)
      have h: "\<And>n asm tps1. 1 \<le> n \<Longrightarrow> nat_of_integer n \<le> length (asms_of sp) \<Longrightarrow>
          asm = asms_of sp ! (nat_of_integer n - 1) \<Longrightarrow>
          \<exists>na. okT (newAs (bs_vl sp) (bs_ctx sp) (er_As (eres_of sp)) n
            [bc_BBi (bs_ctx sp), (er_concl' (eres_of sp), rlist_abs (er_params (eres_of sp)) asm)] tps1) na"
        using assms(5,4) unfolding newas_ok_def by blast
      from h[OF prems(1) nth(2) nth(1), of tps] obtain na where
        na: "okT (newAs (bs_vl sp) (bs_ctx sp) (er_As (eres_of sp)) n
          [bc_BBi (bs_ctx sp), (er_concl' (eres_of sp), rlist_abs (er_params (eres_of sp)) asm)] tps) na"
        by blast
      let ?s = "BS_Its ctx (Some (er_A1 er)) na (UQ_Cell ((env', tps), us')) (BS_Tryasms ctx er rest (n + 1))"
      have "okT (tryasms ops ctx er (asm # rest) n) ?s"
        using True us r na eqs by (auto simp: Let_def unify_ops_def)
      moreover have "elen (bs_cfg sp) us = Suc (elen (bs_cfg sp) us')" by (rule uinv_elen[OF ui some(1)])
      then have "bmu sp ?s < bmu sp (BS_Tryasms ctx er (asm # rest) n)"
        using un by (simp add: ulen_def)
      ultimately show ?thesis by blast
    qed
  qed
qed

text \<open>Pulling a sequence of results in the invariant yields finitely many results.\<close>

lemma bpull_bevals:
  assumes cfg: "cfg_alg (bs_cfg sp) = alg" and finA: "finite (bs_A sp)" and pa: "pinv_all sp"
    and nok: "newas_ok sp" and rok: "results_ok sp" and ops: "ops = unify_ops (bs_cfg sp) (bs_vl sp)"
  shows "binv sp s \<Longrightarrow> \<exists>rs. bevals ops s rs"
proof (induction "bmu sp s" arbitrary: s rule: less_induct)
  case less
  show ?case
  proof (cases s)
    case BS_Empty
    have "bpull ops BS_Empty = returnT None" by (subst bpull.simps) simp
    with BS_Empty show ?thesis by (intro exI[of _ "[]"] bevals.Nil) (simp add: returnT_def)
  next
    case (BS_Its ctx A na xq yq)
    from less.prems[unfolded BS_Its] obtain tus where ctx: "ctx = bs_ctx sp" and its: "itsok sp A na tus"
      and uq: "uqinv sp tus xq" and byq: "binv sp yq"
      by (auto elim: binv_ItsE)
    have bp: "bpull ops s = do {
        r \<leftarrow> (case xq of UQ_Cell c \<Rightarrow> returnT (Some c) | UQ_Seq us \<Rightarrow> bo_pull ops us);
        case r of
          None \<Rightarrow> bpull ops yq
        | Some (et, us') \<Rightarrow>
            handleT
              (do {th \<leftarrow> addth ctx A na et; returnT (Some (th, BS_Its ctx A na (UQ_Seq us') yq))})
              (\<lambda>e. case e of COMPOSE \<Rightarrow> bpull ops (BS_Its ctx A na (UQ_Seq us') yq) | _ \<Rightarrow> raiseT e)}"
      unfolding BS_Its by (subst bpull.simps) simp
    text \<open>The next unifier, if any.\<close>
    obtain rr where rr: "okT (case xq of UQ_Cell c \<Rightarrow> returnT (Some c) | UQ_Seq us \<Rightarrow> bo_pull ops us) rr"
      and el: "\<And>env' tps us'. rr = Some ((env', tps), us') \<Longrightarrow>
        uinv (bs_cfg sp) (bs_A sp) (bs_env sp) tus us' \<and> uelem alg (bs_cfg sp) (bs_env sp) tus (El_R env' tps) \<and>
        bmu sp (BS_Its ctx A na (UQ_Seq us') yq) < bmu sp s"
      and nn: "rr = None \<Longrightarrow> bmu sp yq < bmu sp s"
    proof (cases xq)
      case (UQ_Cell c)
      obtain env' tps us' where c: "c = ((env', tps), us')" by (cases c) auto
      show thesis
        by (rule that[of "Some c"]) (use uq UQ_Cell c BS_Its in \<open>auto simp: uqinv_def\<close>)
    next
      case (UQ_Seq us)
      have ui: "uinv (bs_cfg sp) (bs_A sp) (bs_env sp) tus us" using uq UQ_Seq by (simp add: uqinv_def)
      show thesis
      proof (rule upull_uinv[OF ui], goal_cases none some)
        case none
        then have "okT (bo_pull ops us) None" using ops by (auto simp: unify_ops_def)
        then show thesis by (intro that[of None]) (use UQ_Seq BS_Its in auto)
      next
        case (some env' tps us')
        have "elen (bs_cfg sp) us = Suc (elen (bs_cfg sp) us')" by (rule uinv_elen[OF ui some(1)])
        then show thesis
          by (intro that[of "Some ((env', tps), us')"]) (use some UQ_Seq BS_Its ops in \<open>auto simp: unify_ops_def\<close>)
      qed
    qed
    show ?thesis
    proof (cases rr)
      case None
      have eqv: "okT (bpull ops s) x \<longleftrightarrow> okT (bpull ops yq) x" for x
        using rr None unfolding bp by (auto simp: okT_bindT)
      from less.hyps[OF nn[OF None] byq] obtain rs where "bevals ops yq rs" by blast
      from bevals_cong[OF eqv this] show ?thesis by blast
    next
      case (Some c)
      then obtain env' tps us' where c: "rr = Some ((env', tps), us')" by (cases c) auto
      note e = el[OF c]
      let ?s' = "BS_Its ctx A na (UQ_Seq us') yq"
      have bi': "binv sp ?s'" unfolding ctx by (rule binv.Its[OF its _ byq]) (use e in \<open>simp add: uqinv_def\<close>)
      from less.hyps[OF conjunct2[OF conjunct2[OF e]] bi'] obtain rs where rs: "bevals ops ?s' rs" by blast
      from rok its conjunct1[OF conjunct2[OF e]] ctx
      consider th where "okT (addth ctx A na (env', tps)) th"
        | evs where "addth ctx A na (env', tps) = Some (evs, TErr COMPOSE)"
        unfolding results_ok_def by blast
      then show ?thesis
      proof cases
        case 1
        have "okT (bpull ops s) (Some (th, ?s'))"
          using rr c 1 unfolding bp by (auto simp: okT_bindT okT_handleT)
        from bevals.Cons[OF this rs] show ?thesis by blast
      next
        case 2
        have eqv: "okT (bpull ops s) x \<longleftrightarrow> okT (bpull ops ?s') x" for x
          using rr c 2 unfolding bp
          by (auto simp: okT_bindT okT_handleT bindT_def map_option_eq_Some split: option.splits tres.splits)
        from bevals_cong[OF eqv rs] show ?thesis by blast
      qed
    qed
  next
    case (BS_Tryasms ctx er asms n)
    from less.prems[unfolded BS_Tryasms] have er: "bs_eres sp" "1 \<le> n"
      "asms = drop (nat_of_integer n - 1) (asms_of sp)" "ctx = bs_ctx sp" "er = eres_of sp"
      by (auto elim: binv_TryasmsE)
    from tryasms_ok[OF cfg finA pa er(1) nok ops er(4,5,2,3)] obtain s'' where
      t: "okT (tryasms ops ctx er asms n) s''" and m: "bmu sp s'' < bmu sp (BS_Tryasms ctx er asms n)"
      by blast
    have b'': "binv sp s''" by (rule tryasms_binv[OF cfg finA pa er(1) ops er(4,5,2,3) t])
    have eqv: "okT (bpull ops s) x \<longleftrightarrow> okT (bpull ops s'') x" for x
      using t unfolding BS_Tryasms by (subst bpull.simps) (auto simp: okT_bindT)
    from less.hyps[OF _ b''] m BS_Tryasms obtain rs where "bevals ops s'' rs" by auto
    from bevals_cong[OF eqv this] show ?thesis by blast
  qed
qed

end


subsection \<open>The steps of a call succeed\<close>

lemma strip_prems_ok: "0 \<le> i \<Longrightarrow> i \<le> count_prems B \<Longrightarrow> \<exists>r. ok (strip_prems i As B) r"
proof (induction i As B rule: strip_prems.induct)
  case (1 i As B)
  show ?case
  proof (cases "i = 0")
    case False
    then obtain A B' where AB: "dest_imp B = Some (A, B')"
      using "1.prems" by (cases "dest_imp B") (auto simp: count_prems.simps[of B])
    have "i - 1 \<le> count_prems B'" using "1.prems"(2) AB by (subst (asm) count_prems.simps) simp
    moreover have "0 \<le> i - 1" using "1.prems"(1) False by (simp add: integer_reps)
    ultimately obtain r where "ok (strip_prems (i - 1) (A # As) B') r" using "1.IH"[OF False AB refl] by blast
    with False show ?thesis by (subst strip_prems.simps) (simp add: AB)
  qed (subst strip_prems.simps; simp)
qed

context wf_algebra
begin

lemma foldM_unify_types_ok:
  assumes "tvinv A m env" "tyA ar A T" "\<forall>U\<in>set Us. tyA ar A U"
  shows "\<exists>r. foldM (\<lambda>U env. unify_types alg T U env) Us env = Some r \<and> (\<forall>e. r = Err e \<longrightarrow> (\<exists>u. e = Unif u)) \<and>
    (\<forall>env'. r = Ok env' \<longrightarrow> tvinv A m env')"
  using assms
proof (induction Us arbitrary: env)
  case Nil
  then show ?case by (simp add: return_def)
next
  case (Cons U Us)
  from Cons.prems(1) have ti: "tinv ar (maxidx env) (tyenv env) A" and ts: "tsorted alg (tyenv env)"
    by (simp_all add: tvinv_def)
  have tU: "tyA ar A U" using Cons.prems(3) by simp
  show ?case
  proof (rule unify_types_cases[OF ti ts tyA_tyw[OF ti Cons.prems(2)] tyA_tyw[OF ti tU]], goal_cases Ok Err)
    case (Ok env1)
    have "tvinv A m env1" using unify_types_tvinv[of T U env env1 A m] Ok(1) Cons.prems(1,2) tU by simp
    from Cons.IH[OF this Cons.prems(2)] Cons.prems(3) Ok(1) show ?thesis by (simp add: bindM_def)
  next
    case (Err u)
    then show ?thesis by (simp add: bindM_def)
  qed
qed

lemma foldM_unify_vars_ok:
  assumes "tvinv A m env" "\<forall>(x, Ts)\<in>set tab. \<forall>T\<in>set Ts. tyA ar A T"
  shows "\<exists>r. foldM (\<lambda>(_, Ts) env. unify_vars alg Ts env) tab env = Some r \<and> (\<forall>e. r = Err e \<longrightarrow> (\<exists>u. e = Unif u))"
  using assms
proof (induction tab arbitrary: env)
  case Nil
  then show ?case by (simp add: return_def)
next
  case (Cons p tab)
  obtain x Ts where p: "p = (x, Ts)" by (cases p)
  have u: "\<exists>r. unify_vars alg Ts env = Some r \<and> (\<forall>e. r = Err e \<longrightarrow> (\<exists>u. e = Unif u)) \<and>
      (\<forall>env'. r = Ok env' \<longrightarrow> tvinv A m env')"
  proof (cases Ts)
    case Nil
    with Cons.prems(1) show ?thesis by (simp add: return_def)
  next
    case (Cons T Us)
    with foldM_unify_types_ok[OF \<open>tvinv A m env\<close>, of T Us] \<open>\<forall>(x, Ts)\<in>set (p # tab). \<forall>T\<in>set Ts. tyA ar A T\<close> p
    show ?thesis by simp
  qed
  then obtain r where r: "unify_vars alg Ts env = Some r" "\<forall>e. r = Err e \<longrightarrow> (\<exists>u. e = Unif u)"
    "\<forall>env'. r = Ok env' \<longrightarrow> tvinv A m env'" by blast
  show ?case
  proof (cases r)
    case (Ok env1)
    from Cons.IH[of env1] r(3) Ok Cons.prems(2) r(1) p show ?thesis by (simp add: bindM_def)
  next
    case (Err e)
    with r p show ?thesis by (simp add: bindM_def)
  qed
qed

lemma unify_var_types_ok:
  assumes state: "wt_thm ar A Ws m1 tps1 P1" and rule: "wt_thm ar A Wr m2 tps2 P2"
    and A: "scons A" "\<forall>p\<in>A. snd (fst p) \<le> m"
  shows "\<exists>r. okT (unify_var_types alg (tps1, P1) (tps2, P2) (empty_env m)) r"
proof -
  have fp: "\<exists>p. ok (full_prop_of tps P) p \<and> vps p = vps_thm tps P"
    if "wt_thm ar A Wt mt tps P" for Wt mt tps P
  proof -
    have "\<exists>e. ok (mk_equals tu) e" if "tu \<in> set tps" for tu
    proof -
      obtain t u where tu: "tu = (t, u)" by (cases tu)
      from \<open>wt_thm ar A Wt mt tps P\<close> that tu obtain T where "has_type Wt [] t T"
        by (auto simp: wt_thm_def wt_term_def)
      then show ?thesis by (auto simp: mk_equals_def tu fastype_of_closed return_def)
    qed
    then have "\<forall>tu\<in>set tps. \<exists>e. ok (mk_equals tu) e" by blast
    from ok_mapM_exI[OF this] obtain eqs where "ok (mapM mk_equals tps) eqs" by blast
    then have "ok (full_prop_of tps P) (list_implies eqs P)" by (simp add: full_prop_of_def)
    with vps_full_prop_of show ?thesis by blast
  qed
  from fp[OF state] obtain p1 where p1: "ok (full_prop_of tps1 P1) p1" "vps p1 = vps_thm tps1 P1" by blast
  from fp[OF rule] obtain p2 where p2: "ok (full_prop_of tps2 P2) p2" "vps p2 = vps_thm tps2 P2" by blast
  let ?tab = "sort_keys (add_vars p2 (add_vars p1 []))"
  have ty: "tyA ar A T" if "wt_thm ar A Wt mt tps P" "(x, T) \<in> vps_thm tps P" for Wt mt tps P x T
  proof -
    from that(2) consider "(x, T) \<in> vps P" | t u where "(t, u) \<in> set tps" "(x, T) \<in> vps t \<union> vps u"
      by (auto simp: vps_thm_def)
    then show ?thesis
    proof cases
      case 1
      with that(1) show ?thesis by (auto simp: wt_thm_def wt_term_def dest: vps_tys)
    next
      case 2
      with that(1) obtain T' where "wt_term ar A Wt mt t T'" "wt_term ar A Wt mt u T'"
        unfolding wt_thm_def by blast
      with 2 show ?thesis by (auto simp: wt_term_def dest: vps_tys)
    qed
  qed
  have "vtab ?tab = vps p1 \<union> vps p2"
    by (auto simp: vtab_def set_sort_keys vtab_add_vars[unfolded vtab_def] split: prod.splits)
  then have "\<forall>(x, Ts)\<in>set ?tab. \<forall>T\<in>set Ts. tyA ar A T"
    using ty[OF state] ty[OF rule] p1(2) p2(2) by (fastforce simp: vtab_def)
  from foldM_unify_vars_ok[OF tvinv_empty_env[OF A] this] obtain r where
    r: "foldM (\<lambda>(_, Ts) env. unify_vars alg Ts env) ?tab (empty_env m) = Some r"
      "\<forall>e. r = Err e \<longrightarrow> (\<exists>u. e = Unif u)"
    by blast
  show ?thesis
  proof (cases r)
    case (Ok env)
    with r(1) p1(1) p2(1) show ?thesis by (auto simp: unify_var_types_def Let_def returnT_def liftMT_def liftWT_def liftM_def)
  next
    case (Err e)
    with r obtain u where "e = Unif u" by blast
    with r(1) Err p1(1) p2(1) show ?thesis
      by (auto simp: unify_var_types_def Let_def emitT_def returnT_def)
  qed
qed

end


subsection \<open>The assumptions on a call hold\<close>

lemma remove_params_spine_len:
  "ok (remove_params j n A) A' \<Longrightarrow> length (spine_hyps A) \<le> length (spine_hyps A') + (if 0 < n then 1 else 0)"
proof (induction j n A arbitrary: A' rule: remove_params.induct)
  case (1 j n A)
  note rp = "1.prems"
  show ?case
  proof (cases "j = 0 \<and> n \<le> 0")
    case True
    with rp show ?thesis by (subst (asm) remove_params.simps) simp
  next
    case False
    show ?thesis
    proof (cases "dest_imp A")
      case (Some HB)
      then obtain H B where HB: "dest_imp A = Some (H, B)" by (cases HB) auto
      have sh: "spine_hyps A = H # spine_hyps B" using HB by (subst spine_hyps.simps) simp
      show ?thesis
      proof (cases "n = 1")
        case True
        with rp False HB have "ok (remove_params j (n - 1) B) A'"
          by (subst (asm) remove_params.simps) simp
        from "1.IH"(2)[OF False HB refl True this] True sh show ?thesis by simp
      next
        case n1: False
        with rp False HB obtain B' where B': "ok (remove_params j (n - 1) B) B'"
          and A': "A' = implies $ incr_boundvars j H $ B'"
          by (subst (asm) remove_params.simps) (auto simp: bindM_def split: option.splits res.splits)
        have sh': "spine_hyps A' = incr_boundvars j H # spine_hyps B'"
          using A' by (subst spine_hyps.simps) (simp add: implies_def)
        from "1.IH"(3)[OF False HB refl n1 B'] sh sh' n1 show ?thesis
          by (auto split: if_splits)
      qed
    next
      case None
      show ?thesis
      proof (cases "dest_all A")
        case (Some aTb)
        then obtain a T b where aTb: "dest_all A = Some (a, T, b)" by (cases aTb) auto
        with rp False None have r: "ok (remove_params (j - 1) n b) A'"
          by (subst (asm) remove_params.simps) simp
        have "spine_hyps A = spine_hyps b" using None aTb by (subst spine_hyps.simps) simp
        with "1.IH"(1)[OF False None aTb refl refl r] show ?thesis by simp
      next
        case None': None
        with rp False None show ?thesis by (subst (asm) remove_params.simps) (auto split: if_splits)
      qed
    qed
  qed
qed

lemma flatten_params_spine_len:
  "ok (flatten_params vl n A) A' \<Longrightarrow> length (spine_hyps A) \<le> length (spine_hyps A') + (if 0 < n then 1 else 0)"
  by (auto simp: flatten_params_def Let_def spine_hyps_list_forall dest!: remove_params_spine_len)

text \<open>The new premises of a lifted rule have the assumptions of the subgoal, but one.\<close>

lemma newAs_spine:
  assumes na: "okT (newAs vl ctx As0 n dps tps1) na" and lf: "bc_lifted ctx"
    and lr: "lifted_rule (bc_smax ctx) (bc_Bi ctx) As0 B"
  shows "\<forall>X\<in>set (na_As na). count_prems (strip_all_body (bc_Bi ctx)) \<le>
    ilength (spine_hyps X) + (if 0 < n \<and> bc_flatten ctx then 1 else 0)"
proof -
  note nc = newAs_cases[OF na]
  from lr obtain p Bi0 As0' where Bi: "bc_Bi ctx = lift_pre p Bi0"
    and ok: "\<forall>i\<in>set p. litem_ok i" and at: "atomic Bi0" and As0: "As0 = map (lift_pre p) As0'"
    by (rule lifted_rule_lift_pre)
  have cp: "count_prems (strip_all_body (bc_Bi ctx)) \<le> ilength (phyps p)"
    using count_prems_lift_pre[OF ok at] Bi by simp
  have old: "\<forall>A1\<in>set (na_oldAs na). length (phyps p) \<le> length (spine_hyps A1)"
  proof -
    have "\<forall>A1\<in>set (na_oldAs na). \<exists>Y. A1 = lift_pre p Y"
      using nc(2) lf by (auto simp: As0 Bi strip_apply_lift_pre[OF ok at])
    then show ?thesis by (auto simp: spine_hyps_lift_pre[OF ok])
  qed
  have "list_all2 (\<lambda>A1 A'. length (phyps p) \<le> length (spine_hyps A1) \<longrightarrow>
      length (phyps p) \<le> length (spine_hyps A') + (if 0 < n \<and> bc_flatten ctx then 1 else 0))
      (na_oldAs na) (na_As na)"
    by (rule list_all2_mono[OF nc(1)]) (auto split: if_splits dest: flatten_params_spine_len)
  from list_all2_imp_all[OF this old] cp show ?thesis
    by (fastforce simp: ilength_eq integer_reps integer_of_nat.rep_eq split: if_splits)
qed

context wf_algebra
begin

text \<open>The new premises can be computed: flattening finds the assumption deleted by elim-resolution.\<close>

lemma call_newas_ok:
  assumes sp: "sp = call_spec cfg A vl env flatten match_flg smax stpairs Bs Bi C lifted eres_flg rtpairs rAs B"
    and wR: "\<forall>X\<in>set (rev rAs). wfp ar X" and lr: "lifted \<Longrightarrow> lifted_rule smax Bi (rev rAs) B"
    and fl: "eres_flg \<Longrightarrow> flatten \<Longrightarrow> lifted" and vl: "\<And>xs. length (vl xs) = length xs"
  shows "newas_ok sp"
proof -
  define nlift where "nlift = count_prems (strip_all_body Bi) + (if eres_flg then -1 else 0)"
  define BBi where "BBi = (if lifted then strip_assums2 B Bi else (B, Bi))"
  define ctx where "ctx = BCtx flatten match_flg lifted smax Bs Bi C rtpairs nlift BBi (BBi # rtpairs @ stpairs)"
  have sp': "sp = BSpec cfg A vl env ctx rAs eres_flg"
    using sp by (simp add: call_spec_def Let_def nlift_def BBi_def ctx_def)
  text \<open>The new premises for a list \<open>As0\<close> of premises of the rule.\<close>
  have ex: "\<exists>na. okT (newAs vl ctx As0 n dps tps1) na"
    if As0: "set As0 \<subseteq> set (rev rAs)" and n: "flatten \<Longrightarrow> 0 < n \<Longrightarrow> lifted \<and> n \<le> count_prems (strip_all_body Bi)"
      and lr0: "lifted \<Longrightarrow> lifted_rule smax Bi As0 B" for As0 n dps tps1
  proof -
    let ?r = "rename_bvs dps (rtpairs @ tps1) Bi As0"
    define As1 where "As1 = (if lifted \<and> rename_bvars dps (rtpairs @ tps1) Bi As0 \<noteq> None
      then map (strip_apply (ren_term ?r) Bi) As0 else As0)"
    have fp: "\<exists>A'. ok (flatten_params vl n A1) A'" if "flatten" "A1 \<in> set As1" for A1
    proof (cases "lifted")
      case True
      from lr0[OF True] obtain p Bi0 As0' where Bi: "Bi = lift_pre p Bi0"
        and ok: "\<forall>i\<in>set p. litem_ok i" and at: "atomic Bi0" and As0': "As0 = map (lift_pre p) As0'"
        by (rule lifted_rule_lift_pre)
      from that(2) obtain Y where A1: "A1 = lift_pre p Y" and wY: "wfp ar A1"
        using As0 wR As0' by (auto simp: As1_def Bi strip_apply_lift_pre[OF ok at] wfp_lift_pre_ren_term split: if_splits)
      have "n \<le> ilength (spine_hyps A1)"
      proof (cases "0 < n")
        case True
        with n that(1) have "n \<le> count_prems (strip_all_body Bi)" by blast
        also have "\<dots> \<le> ilength (phyps p)" using count_prems_lift_pre[OF ok at] Bi by simp
        also have "\<dots> \<le> ilength (spine_hyps A1)"
          by (simp add: A1 spine_hyps_lift_pre[OF ok] ilength_eq integer_reps integer_of_nat.rep_eq)
        finally show ?thesis .
      qed (simp add: not_less order_trans[OF _ ilength_nonneg])
      with wY show ?thesis by (intro flatten_params_ok) (simp_all add: vl wfp_def)
    next
      case False
      with that(2) As0 wR have "wfp ar A1" by (auto simp: As1_def)
      moreover have "n \<le> ilength (spine_hyps A1)"
        using n[OF that(1)] False by (cases "0 < n") (auto simp: not_less intro: order_trans[OF _ ilength_nonneg])
      ultimately show ?thesis by (intro flatten_params_ok) (simp_all add: vl wfp_def)
    qed
    obtain As2 where As2: "if flatten then ok (mapM (flatten_params vl n) As1) As2 else As2 = As1"
      using ok_mapM_exI[of As1 "flatten_params vl n"] fp by (cases flatten) auto
    have "okT (newAs vl ctx As0 n dps tps1)
        (NewAs As2 As1 (if lifted then rename_bvars dps (rtpairs @ tps1) Bi As0 else None) n)"
    proof (cases "rename_bvars dps (rtpairs @ tps1) Bi As0")
      case None
      with As2 show ?thesis by (simp add: newAs_def ctx_def As1_def okT_handleT split: if_splits)
    next
      case (Some r)
      then have "r = ?r" by (simp add: rename_bvars_def Let_def split: if_splits)
      with Some As2 show ?thesis by (simp add: newAs_def ctx_def As1_def okT_handleT split: if_splits)
    qed
    then show ?thesis by blast
  qed
  show ?thesis
    unfolding newas_ok_def
  proof (intro conjI impI allI)
    assume "\<not> bs_eres sp"
    show "\<exists>na. okT (newAs (bs_vl sp) (bs_ctx sp) (rev (bs_rAs sp)) 0 [bc_BBi (bs_ctx sp)] tps1) na" for tps1
      using ex[of "rev rAs" 0] lr by (simp add: sp')
  next
    fix n asm tps1 assume er: "bs_eres sp" and n: "1 \<le> n" "nat_of_integer n \<le> length (asms_of sp)"
      and asm: "asm = asms_of sp ! (nat_of_integer n - 1)"
    have n1: "1 \<le> nat_of_integer n" using n(1) by (simp add: integer_reps)
    obtain A1 As where rA: "rev rAs = A1 # As"
      using n(2) n1 by (cases "rev rAs") (auto simp: asms_of_def sp')
    obtain params asms concl where ap: "assum_problems (nlift + 1) A1 = (params, asms, concl)"
      by (cases "assum_problems (nlift + 1) A1")
    have e: "eres_of sp = ER env params concl (rlist_abs params concl) A1 As" "asms_of sp = asms"
      using rA ap by (simp_all add: eres_of_def asms_of_def sp' ctx_def)
    have cnt: "nlift + 1 = count_prems (strip_all_body Bi)" using er by (simp add: nlift_def sp')
    have "ilength asms \<le> nlift + 1"
      by (rule assum_problems_length[OF ap]) (use cnt count_prems_nonneg in simp)
    moreover have "n \<le> ilength asms" using n e(2) by (simp add: ilength_eq integer_reps integer_of_nat.rep_eq)
    ultimately have "n \<le> count_prems (strip_all_body Bi)" using cnt by simp
    with fl er have nn: "flatten \<Longrightarrow> 0 < n \<Longrightarrow> lifted \<and> n \<le> count_prems (strip_all_body Bi)"
      by (simp add: sp')
    have lrA: "lifted_rule smax Bi As B" if "lifted" using lr[OF that] rA by (auto dest: lifted_rule_Cons)
    have sub: "set As \<subseteq> set (rev rAs)" using rA by auto
    show "\<exists>na. okT (newAs (bs_vl sp) (bs_ctx sp) (er_As (eres_of sp)) n
        [bc_BBi (bs_ctx sp), (er_concl' (eres_of sp), rlist_abs (er_params (eres_of sp)) asm)] tps1) na"
      unfolding e using ex[OF sub nn lrA] by (simp add: sp')
  qed
qed

end

context wf_algebra
begin

text \<open>
  The new theorem can be built for every unifier: its components are typed in the environment
  of the unifier, and the renamed variables of the new premises do not occur in it.
\<close>

lemma call_results_ok:
  assumes sp: "sp = call_spec cfg A vl env flatten match_flg smax stpairs Bs Bi C lifted eres_flg rtpairs rAs B"
    and cfg: "cfg_alg cfg = alg" and finA: "finite A" and pa: "pinv_allW sp W"
    and rs: "rs_typed ar A (map (\<lambda>X. (X, propT)) (C # Bs @ rev rAs)) W env"
    and te: "vt_is_empty (tenv env)"
    and wS: "\<forall>X\<in>set (C # Bs). wfp ar X" "ibelow smax Bi"
      "\<forall>(t, u)\<in>set stpairs. \<forall>x\<in>vars t \<union> vars u. snd x \<le> smax"
    and wR: "\<forall>X\<in>set (rev rAs). wfp ar X" "lifted \<Longrightarrow> lifted_rule smax Bi (rev rAs) B"
    and vl: "\<And>xs. length (vl xs) = length xs"
  shows "results_ok sp"
proof -
  define nlift where "nlift = count_prems (strip_all_body Bi) + (if eres_flg then -1 else 0)"
  define BBi where "BBi = (if lifted then strip_assums2 B Bi else (B, Bi))"
  define ctx where "ctx = BCtx flatten match_flg lifted smax Bs Bi C rtpairs nlift BBi (BBi # rtpairs @ stpairs)"
  let ?rs = "map (\<lambda>X. (X, propT)) (C # Bs @ rev rAs)"
  have sp': "sp = BSpec cfg A vl env ctx rAs eres_flg"
    using sp by (simp add: call_spec_def Let_def nlift_def BBi_def ctx_def)
  have ctx_sel: "bc_flatten ctx = flatten" "bc_lifted ctx = lifted" "bc_smax ctx = smax" "bc_Bs ctx = Bs"
    "bc_Bi ctx = Bi" "bc_C ctx = C" "bc_rtpairs ctx = rtpairs" "bc_nlift ctx = nlift" "bc_BBi ctx = BBi"
    "bc_dpairs ctx = BBi # rtpairs @ stpairs"
    by (simp_all add: ctx_def)
  have pv: "\<forall>x\<in>pvars p. snd x \<le> smax" if "lsplit Bi = (p, Bi0)" for p Bi0
    using wS(2) lsplit_ok[OF that] by (auto simp: ibelow_def vars_lift_pre)
  show ?thesis
    unfolding results_ok_def
  proof (intro allI impI)
    fix A1o na tus env' tps
    assume its: "itsok sp A1o na tus" and ue: "uelem alg (bs_cfg sp) (bs_env sp) tus (El_R env' tps)"
    text \<open>The problem, the premises \<open>As0\<close> that stay, and the data of the renaming.\<close>
    obtain As0 n dps tps1 where na: "okT (newAs vl ctx As0 n dps tps1) na"
      and As0: "set As0 \<subseteq> set (rev rAs)" and lr0: "lifted \<Longrightarrow> lifted_rule smax Bi As0 B"
      and pi: "pinv alg ar A W env (dps_of tus)" and BBid: "BBi \<in> set dps"
      and nl: "0 \<le> nlift" "nlift + (if 0 < n \<and> flatten then 1 else 0) \<le> count_prems (strip_all_body Bi)"
      and tusv: "\<And>t u v. lifted \<Longrightarrow> (t, u) \<in> set tus \<Longrightarrow> smax < snd v \<Longrightarrow>
        (\<forall>(t', u')\<in>set dps. fst v \<notin> fst ` vars t') \<Longrightarrow>
        (\<forall>(t', u')\<in>set rtpairs. fst v \<notin> fst ` vars t' \<and> fst v \<notin> fst ` vars u') \<Longrightarrow>
        v \<notin> vars t \<and> v \<notin> vars u"
    proof -
      text \<open>The pairs common to all problems.\<close>
      have common: "v \<notin> vars t \<and> v \<notin> vars u"
        if lf: "lifted" and tu: "(t, u) \<in> set (BBi # rtpairs @ stpairs)" and sv: "smax < snd v"
          and d: "\<forall>(t', u')\<in>set dps. fst v \<notin> fst ` vars t'" and bd: "BBi \<in> set dps"
          and r: "\<forall>(t', u')\<in>set rtpairs. fst v \<notin> fst ` vars t' \<and> fst v \<notin> fst ` vars u'"
        for t u v dps
      proof -
        from wR(2)[OF lf] obtain p Bi0 B0 where ls: "lsplit Bi = (p, Bi0)" and B: "B = lift_pre p B0"
          by (auto simp: lifted_rule_def)
        from lsplit_ok[OF ls] have Bi: "Bi = lift_pre p Bi0" and ok: "\<forall>i\<in>set p. litem_ok i"
          and at: "atomic Bi0" by auto
        have BBi': "BBi = (abs_pre p B0, abs_pre p Bi0)"
          using lf by (simp add: BBi_def B Bi strip_assums2_lift_pre[OF ok at])
        from tu consider "(t, u) = BBi" | "(t, u) \<in> set rtpairs" | "(t, u) \<in> set stpairs" by auto
        then show ?thesis
        proof cases
          case 1
          have "fst v \<notin> fst ` vars (abs_pre p B0)" using d bd BBi' by fastforce
          moreover have "\<forall>x\<in>vars (abs_pre p Bi0). snd x \<le> smax"
            using wS(2) by (auto simp: Bi vars_abs_pre ibelow_def vars_lift_pre)
          ultimately show ?thesis using 1 BBi' sv by (force simp: vars_abs_pre)
        next
          case 2
          with r show ?thesis by force
        next
          case 3
          with wS(3) sv show ?thesis by force
        qed
      qed
      from its consider (res) tps1 where "\<not> eres_flg" "A1o = None" "tus = BBi # rtpairs @ stpairs"
          "okT (newAs vl ctx (rev rAs) 0 [BBi] tps1) na"
        | (eres) n asm tps1 where "eres_flg" "1 \<le> n" "nat_of_integer n \<le> length (asms_of sp)"
          "asm = asms_of sp ! (nat_of_integer n - 1)" "tus = eres_prob sp asm"
          "okT (newAs vl ctx (er_As (eres_of sp)) n
            [BBi, (er_concl' (eres_of sp), rlist_abs (er_params (eres_of sp)) asm)] tps1) na"
        using its unfolding itsok_def by (cases eres_flg; simp add: sp' ctx_sel; blast)
      then show thesis
      proof cases
        case res
        have pi: "pinv alg ar A W env (dps_of tus)" using pa res by (simp add: pinv_allW_def sp' ctx_sel)
        have tv: "v \<notin> vars t \<and> v \<notin> vars u"
          if "lifted" "(t, u) \<in> set tus" "smax < snd v" "\<forall>(t', u')\<in>set [BBi]. fst v \<notin> fst ` vars t'"
            "\<forall>(t', u')\<in>set rtpairs. fst v \<notin> fst ` vars t' \<and> fst v \<notin> fst ` vars u'" for t u v
          by (rule common[of t u v "[BBi]"]) (use that res(3) in auto)
        show thesis
          by (rule that[OF res(4) _ wR(2) pi _ _ _ tv])
            (use res(1) count_prems_nonneg[of "strip_all_body Bi"] in \<open>auto simp: nlift_def\<close>)
      next
        case eres
        have n1: "1 \<le> nat_of_integer n" using eres(2) by (simp add: integer_reps)
        obtain A1 As where rA: "rev rAs = A1 # As"
          using eres(3) n1 by (cases "rev rAs") (auto simp: asms_of_def sp')
        obtain params asms concl where ap: "assum_problems (nlift + 1) A1 = (params, asms, concl)"
          by (cases "assum_problems (nlift + 1) A1")
        have er: "eres_of sp = ER env params concl (rlist_abs params concl) A1 As" "asms_of sp = asms"
          using rA ap by (simp_all add: eres_of_def asms_of_def sp' ctx_sel)
        have asm: "asm \<in> set asms" using eres(2-4) er(2) by (simp add: integer_reps)
        have cnt: "nlift + 1 = count_prems (strip_all_body Bi)" using eres(1) by (simp add: nlift_def)
        have "ilength asms \<le> nlift + 1"
          by (rule assum_problems_length[OF ap]) (use cnt count_prems_nonneg in simp)
        moreover have "n \<le> ilength asms" using eres(2,3) er(2)
          by (simp add: ilength_eq integer_reps integer_of_nat.rep_eq)
        ultimately have nle: "n \<le> nlift + 1" by simp
        have pi: "pinv alg ar A W env (dps_of tus)"
          using pa eres(1,5) asm er(2) by (auto simp: pinv_allW_def sp')
        have tus: "tus = (rlist_abs params asm, rlist_abs params concl) # BBi # rtpairs @ stpairs"
          using eres(5) er by (simp add: eres_prob_def sp' ctx_sel)
        let ?dps = "[BBi, (rlist_abs params concl, rlist_abs params asm)]"
        have lrA: "lifted \<Longrightarrow> lifted_rule smax Bi As B" using wR(2) rA by (auto dest: lifted_rule_Cons)
        have tv: "v \<notin> vars t \<and> v \<notin> vars u"
          if lf: "lifted" and tu: "(t, u) \<in> set tus" and sv: "smax < snd v"
            and d: "\<forall>(t', u')\<in>set ?dps. fst v \<notin> fst ` vars t'"
            and r: "\<forall>(t', u')\<in>set rtpairs. fst v \<notin> fst ` vars t' \<and> fst v \<notin> fst ` vars u'" for t u v
        proof (cases "(t, u) = (rlist_abs params asm, rlist_abs params concl)")
          case True
          from wR(2)[OF lf] rA obtain p Bi0 As0' where ls: "lsplit Bi = (p, Bi0)"
            and As': "A1 # As = map (lift_pre p) As0'" by (auto simp: lifted_rule_def) (metis list.map(2))
          from lsplit_ok[OF ls] have Bi: "Bi = lift_pre p Bi0" and ok: "\<forall>i\<in>set p. litem_ok i"
            and at: "atomic Bi0" by auto
          from As' obtain X1 where A1: "A1 = lift_pre p X1" by (cases As0') auto
          have "set asms \<subseteq> set (phyps p)"
            using assum_problems_lift_pre[OF ok at _ ap[unfolded A1]] Bi cnt count_prems_nonneg[of "strip_all_body Bi"]
            by simp
          with asm have "\<forall>x\<in>vars asm. snd x \<le> smax" using pv[OF ls] vars_phyps by blast
          moreover have "fst v \<notin> fst ` vars (rlist_abs params concl)" using d by simp
          ultimately show ?thesis using True sv by (force simp: vars_rlist_abs)
        next
          case False
          with tu tus have "(t, u) \<in> set (BBi # rtpairs @ stpairs)" by auto
          from common[OF lf this sv d _ r] show ?thesis by simp
        qed
        show thesis
        proof (rule that[OF eres(6)[unfolded er, simplified] _ lrA pi _ _ _ tv])
          show "set As \<subseteq> set (rev rAs)" using rA by auto
          show "BBi \<in> set ?dps" by simp
          show "0 \<le> nlift" "nlift + (if 0 < n \<and> flatten then 1 else 0) \<le> count_prems (strip_all_body Bi)"
            using nle cnt eres(2) by auto
        qed
      qed
    qed
    text \<open>The unifier is in the invariant, and further terms stay typed in it.\<close>
    from ue obtain s0 xs0 where u0: "unifiers alg env tus = Some (Ok s0)" "evals cfg s0 xs0"
      "El_R env' tps \<in> set xs0"
      by (auto simp: uelem_def sp')
    from unifiers_prres_rs[OF cfg finA pi rs] obtain s where
      "unifiers alg env tus = Some (Ok s)"
      "fin cfg s (\<lambda>x. \<exists>env' tps. x = El_R env' tps \<and> prres_rs alg ar A ?rs env' tps)"
      by blast
    from uelem_fin[OF ue[unfolded sp', simplified] this] have "prres_rs alg ar A ?rs env' tps" by simp
    then obtain W' e0 where pi': "pinv alg ar A W' env' []" and tp: "\<forall>ab\<in>set tps. ptpok ar A W' env' e0 ab"
      and rs': "rs_typed ar A ?rs W' env'"
      by (auto simp: prres_rs_def)
    text \<open>Renamed variables of the rule do not occur in the unifier.\<close>
    have fr: "vt_lookup (tenv env') v = None \<and> v \<notin> fst ` bvps env'"
      if "bc_lifted ctx" "bc_smax ctx < snd v" "snd v \<le> maxidx env"
        "\<forall>(t, u)\<in>set dps. fst v \<notin> fst ` vars t"
        "\<forall>(t, u)\<in>set (bc_rtpairs ctx @ tps1). fst v \<notin> fst ` vars t \<and> fst v \<notin> fst ` vars u" for v
    proof (rule unifiers_fresh[OF cfg finA pi u0])
      show "vt_lookup (tenv env) v = None" using te by (simp add: vt_is_empty_lookup)
      show "v \<notin> fst ` bvps env" using te by (auto simp: bvps_def vt_is_empty_lookup)
      show "snd v \<le> maxidx env" by fact
      have "\<forall>(t', u')\<in>set rtpairs. fst v \<notin> fst ` vars t' \<and> fst v \<notin> fst ` vars u'"
        using that(5) by (simp add: ctx_sel)
      then show "\<forall>(t, u)\<in>set tus. v \<notin> vars t \<and> v \<notin> vars u"
        using tusv[of _ _ v] that(1,2,4) by (auto simp: ctx_sel)
    qed
    have ty: "\<forall>X\<in>set As0. typed env' W' [] X propT \<and> wfp ar X \<and> below (maxidx env') X \<and>
        (\<forall>U\<in>tys X. tyw ar (tyenv env') A U)"
      using rs' As0 wR(1) by (fastforce simp: rs_typed_def)
    have b0: "\<forall>X\<in>set As0. below (maxidx env) X" using rs As0 by (fastforce simp: rs_typed_def)
    have lr0': "bc_lifted ctx \<Longrightarrow> lifted_rule (bc_smax ctx) (bc_Bi ctx) As0 B" using lr0 by (simp add: ctx_sel)
    have ib: "ibelow (bc_smax ctx) (bc_Bi ctx)" using wS(2) by (simp add: ctx_sel)
    obtain W'' where pi'': "pinv alg ar A W'' env' []" and "\<forall>x. snd x \<le> bc_smax ctx \<longrightarrow> W'' x = W' x"
      and As': "\<forall>X\<in>set (na_As na). typed env' W'' [] X propT \<and> wfp ar X \<and> below (maxidx env') X \<and>
        (\<forall>U\<in>tys X. tyw ar (tyenv env') A U)"
      by (rule newAs_typed[OF na lr0' ib pi' ty b0 fr vl])
    have "(\<exists>r. okT (addth ctx A1o na (env', tps)) r) \<or>
        (bc_match ctx \<and> (\<exists>evs. addth ctx A1o na (env', tps) = Some (evs, TErr COMPOSE)))"
    proof (rule addth_ok[OF pi' _ _ pi''])
      show "\<forall>ab\<in>set tps. \<exists>e0. ptpok ar A W' env' e0 ab" using tp by blast
      show "\<forall>X\<in>insert (bc_C ctx) (set (bc_Bs ctx)). wtprop A W' env' X"
        using rs' wS(1) by (fastforce simp: rs_typed_def wtprop_def ctx_sel)
      show "\<forall>X\<in>set (na_As na). wtprop A W'' env' X" using As' by (simp add: wtprop_def)
      assume lf: "bc_lifted ctx"
      from newAs_spine[OF na lf lr0'[OF lf]] nl
      show "0 \<le> bc_nlift ctx \<and> (\<forall>X\<in>set (na_As na). bc_nlift ctx \<le> ilength (spine_hyps X))"
        by (fastforce simp: ctx_sel split: if_splits)
    qed
    then show "(\<exists>r. okT (addth (bs_ctx sp) A1o na (env', tps)) r) \<or>
        (bc_match (bs_ctx sp) \<and> (\<exists>evs. addth (bs_ctx sp) A1o na (env', tps) = Some (evs, TErr COMPOSE)))"
      by (simp add: sp')
  qed
qed

end

subsection \<open>Termination\<close>

lemma strip_prems_length:
  "ok (strip_prems i As B) (rAs, B') \<Longrightarrow> 0 \<le> i \<Longrightarrow> length rAs = nat_of_integer i + length As"
proof (induction i As B rule: strip_prems.induct)
  case (1 i As B)
  show ?case
  proof (cases "i = 0")
    case True
    with "1.prems" show ?thesis by (subst (asm) strip_prems.simps) simp
  next
    case False
    with "1.prems"(1) obtain A B'' where AB: "dest_imp B = Some (A, B'')"
      and r: "ok (strip_prems (i - 1) (A # As) B'') (rAs, B')"
      by (subst (asm) strip_prems.simps) (auto split: option.splits)
    from "1.IH"[OF False AB refl r] "1.prems"(2) False show ?thesis by (simp add: integer_reps)
  qed
qed

lemma bindT_Some_TOk: "bindT (Some ([], TOk x)) f = f x"
  by (simp add: bindT_def option.map_id)

lemma handleT_Some_TOk: "handleT (Some (evs, TOk x)) h = Some (evs, TOk x)"
  by (simp add: handleT_def)

context wf_algebra
begin

lemma bicompose_body_ok:
  assumes cfg: "cfg_alg (bs_cfg sp) = alg" and finA: "finite (bs_A sp)" and pa: "pinv_all sp"
    and nok: "newas_ok sp" and ne: "bs_eres sp \<Longrightarrow> bs_rAs sp \<noteq> []"
  shows "\<exists>s. okT (bicompose_body (unify_ops (bs_cfg sp) (bs_vl sp)) (bs_ctx sp) (bs_env sp) (bs_eres sp) (bs_rAs sp)) s"
proof (cases "bs_eres sp")
  case True
  then obtain A1 As where rA: "rev (bs_rAs sp) = A1 # As" using ne by (cases "rev (bs_rAs sp)") auto
  obtain params asms concl where ap: "assum_problems (bc_nlift (bs_ctx sp) + 1) A1 = (params, asms, concl)"
    by (cases "assum_problems (bc_nlift (bs_ctx sp) + 1) A1")
  have er: "ER (bs_env sp) params concl (rlist_abs params concl) A1 As = eres_of sp"
    using rA ap by (simp add: eres_of_def)
  have asms: "asms = drop (nat_of_integer 1 - 1) (asms_of sp)" using rA ap by (simp add: asms_of_def)
  from tryasms_ok[OF cfg finA pa True nok refl refl refl _ asms] obtain s where
    "okT (tryasms (unify_ops (bs_cfg sp) (bs_vl sp)) (bs_ctx sp) (eres_of sp) asms 1) s" by auto
  with True rA ap er show ?thesis by (auto simp: bicompose_body_def)
next
  case False
  from pa False obtain W where pi: "pinv alg ar (bs_A sp) W (bs_env sp) (dps_of (bc_dpairs (bs_ctx sp)))"
    by (auto simp: pinv_all_def)
  obtain us where us: "okT (bo_unifiers (unify_ops (bs_cfg sp) (bs_vl sp)) (bs_env sp) (bc_dpairs (bs_ctx sp))) us"
    and ui: "uinv (bs_cfg sp) (bs_A sp) (bs_env sp) (bc_dpairs (bs_ctx sp)) us"
    by (rule unifiers_ops_ok[OF cfg finA pi])
  show ?thesis
  proof (rule upull_uinv[OF ui], goal_cases none some)
    case none
    with us False show ?thesis by (auto simp: bicompose_body_def unify_ops_def)
  next
    case (some env' tps us')
    from nok False obtain na where
      "okT (newAs (bs_vl sp) (bs_ctx sp) (rev (bs_rAs sp)) 0 [bc_BBi (bs_ctx sp)] tps) na"
      unfolding newas_ok_def by blast
    with us some(1) False show ?thesis by (auto simp: bicompose_body_def unify_ops_def)
  qed
qed

text \<open>
  A call of \<open>bicompose_aux\<close> for a well-typed proof state and rule: either the types of the
  variables cannot be unified, or the body is called with a specification whose problems are
  well-typed and whose new premises and new theorems can be built.
\<close>

lemma bicompose_aux_call:
  assumes cfg: "cfg_alg cfg = alg" and finA: "finite A"
    and state: "wt_thm ar A Ws smax stpairs (list_implies (Bs @ [Bi]) C)" "ibelow smax (list_implies (Bs @ [Bi]) C)"
    and rule: "wt_thm ar A Wr rmax rtpairs rprop" "lifted \<Longrightarrow> lifted_over smax Bi rprop nsubgoal"
    and A: "scons A" "\<forall>p\<in>A. snd (fst p) \<le> max rmax smax" "\<forall>x. tyA ar A (Ws x)" "\<forall>x. tyA ar A (Wr x)"
    and inc: "incremented \<Longrightarrow>
      \<forall>x\<in>vars_thm stpairs (list_implies (Bs @ [Bi]) C) \<inter> vars_thm rtpairs rprop. Ws x = Wr x"
    and ns: "0 \<le> nsubgoal" "nsubgoal \<le> count_prems rprop" and er: "eres_flg \<Longrightarrow> 0 < nsubgoal"
    and fl: "eres_flg \<Longrightarrow> flatten \<Longrightarrow> lifted"
    and vl: "\<And>xs. length (vl xs) = length xs"
  obtains (types) "\<not> incremented"
      "okT (unify_var_types alg (stpairs, list_implies (Bs @ [Bi]) C) (rtpairs, rprop) (empty_env (max rmax smax))) None"
      "okT (bicompose_aux (unify_ops cfg vl) alg flatten match_flg incremented
        (smax, stpairs, list_implies (Bs @ [Bi]) C) (stpairs, Bs, Bi, C) lifted eres_flg (rmax, rtpairs, rprop) nsubgoal) BS_Empty"
  | (call) rAs B env s W where "ok (strip_prems nsubgoal [] rprop) (rAs, B)"
      "incremented \<Longrightarrow> env = empty_env (max rmax smax)"
      "\<not> incremented \<Longrightarrow> okT (unify_var_types alg (stpairs, list_implies (Bs @ [Bi]) C) (rtpairs, rprop)
        (empty_env (max rmax smax))) (Some env)"
      "okT (bicompose_aux (unify_ops cfg vl) alg flatten match_flg incremented
        (smax, stpairs, list_implies (Bs @ [Bi]) C) (stpairs, Bs, Bi, C) lifted eres_flg (rmax, rtpairs, rprop) nsubgoal) s"
      "okT (bicompose_body (unify_ops cfg vl)
        (bs_ctx (call_spec cfg A vl env flatten match_flg smax stpairs Bs Bi C lifted eres_flg rtpairs rAs B))
        env eres_flg rAs) s"
      "pinv_allW (call_spec cfg A vl env flatten match_flg smax stpairs Bs Bi C lifted eres_flg rtpairs rAs B) W"
      "newas_ok (call_spec cfg A vl env flatten match_flg smax stpairs Bs Bi C lifted eres_flg rtpairs rAs B)"
      "results_ok (call_spec cfg A vl env flatten match_flg smax stpairs Bs Bi C lifted eres_flg rtpairs rAs B)"
proof -
  let ?S = "list_implies (Bs @ [Bi]) C" and ?m = "max rmax smax"
  let ?nlift = "count_prems (strip_all_body Bi) + (if eres_flg then -1 else 0)"
  let ?ctx = "\<lambda>B. BCtx flatten match_flg lifted smax Bs Bi C rtpairs ?nlift
    (if lifted then strip_assums2 B Bi else (B, Bi))
    ((if lifted then strip_assums2 B Bi else (B, Bi)) # rtpairs @ stpairs)"
  from strip_prems_ok[OF ns] obtain rAsB where sp0: "ok (strip_prems nsubgoal [] rprop) rAsB" by blast
  obtain rAs B where rAsB: "rAsB = (rAs, B)" by (cases rAsB)
  note sp1 = sp0[unfolded rAsB]
  have eq: "bicompose_aux (unify_ops cfg vl) alg flatten match_flg incremented (smax, stpairs, ?S)
      (stpairs, Bs, Bi, C) lifted eres_flg (rmax, rtpairs, rprop) nsubgoal =
    bindT (if incremented then returnT (Some (empty_env ?m))
        else unify_var_types alg (stpairs, ?S) (rtpairs, rprop) (empty_env ?m))
      (\<lambda>r. case r of None \<Rightarrow> returnT BS_Empty
        | Some env \<Rightarrow> bicompose_body (unify_ops cfg vl) (?ctx B) env eres_flg rAs)"
    using sp1 by (cases eres_flg; cases lifted; cases incremented)
      (simp_all add: bicompose_aux_def Let_def liftMT_def liftWT_def liftM_def returnT_def bindT_Some_TOk handleT_Some_TOk)
  obtain r where r: "okT (if incremented then returnT (Some (empty_env ?m))
      else unify_var_types alg (stpairs, ?S) (rtpairs, rprop) (empty_env ?m)) r"
    using unify_var_types_ok[OF state(1) rule(1) A(1,2)] by (cases incremented) auto
  show thesis
  proof (cases r)
    case None
    with r have ni: "\<not> incremented" by (auto simp: returnT_def split: if_splits)
    with r None have "okT (unify_var_types alg (stpairs, ?S) (rtpairs, rprop) (empty_env ?m)) None" by simp
    moreover from r None have "okT (bicompose_aux (unify_ops cfg vl) alg flatten match_flg incremented
        (smax, stpairs, ?S) (stpairs, Bs, Bi, C) lifted eres_flg (rmax, rtpairs, rprop) nsubgoal) BS_Empty"
      unfolding eq by (auto simp: okT_bindT returnT_def)
    ultimately show thesis by (rule types[OF ni])
  next
    case (Some env)
    let ?sp = "call_spec cfg A vl env flatten match_flg smax stpairs Bs Bi C lifted eres_flg rtpairs rAs B"
    have e1: "incremented \<Longrightarrow> env = empty_env ?m" and
      e2: "\<not> incremented \<Longrightarrow> okT (unify_var_types alg (stpairs, ?S) (rtpairs, rprop) (empty_env ?m)) (Some env)"
      using r Some by (auto split: if_splits)
    from call_typing[OF state(1) rule(1) A inc e1 e2] obtain W where tv: "tvinv A ?m env"
      and tW: "\<forall>x. tyA ar A (W x)"
      and agS: "\<forall>x\<in>vars_thm stpairs ?S. tnorm (tyenv env) (Ws x) = tnorm (tyenv env) (W x)"
      and agR: "\<forall>x\<in>vars_thm rtpairs rprop. tnorm (tyenv env) (Wr x) = tnorm (tyenv env) (W x)"
      by blast
    have lift: "\<exists>p Bi0 B0. lsplit Bi = (p, Bi0) \<and> B = lift_pre p B0" if lifted
      using lifted_over_lifted_rule[OF rule(2)[OF that] sp1] by (auto simp: lifted_rule_def)
    have paW: "pinv_allW ?sp W" by (rule pinv_all_tvinv[OF state(1) rule(1) sp1 lift tv tW agS agR])
    have pa: "pinv_all ?sp" by (rule pinv_allW_pinv_all[OF paW])
    have P: "rprop = list_implies (rev rAs) B"
      by (rule list_implies_strip_prems[OF sp1]) (use rule(1) in \<open>simp add: wt_thm_def\<close>)
    have wS: "\<forall>X\<in>set Bs. wt_term ar A Ws smax X propT" "wt_term ar A Ws smax Bi propT"
      "wt_term ar A Ws smax C propT"
      using wt_term_list_implies[of ar A Ws smax "Bs @ [Bi]" C] state(1) by (auto simp: wt_thm_def)
    have wR: "\<forall>X\<in>set (rev rAs). wt_term ar A Wr rmax X propT"
      using wt_term_list_implies[of ar A Wr rmax "rev rAs" B] rule(1) P by (auto simp: wt_thm_def)
    have rs: "rs_typed ar A (map (\<lambda>X. (X, propT)) (C # Bs @ rev rAs)) W env"
    proof (rule rs_typed_tvinv[OF tv])
      have "\<exists>Wt. wt_mod ar A (tyenv env) W Wt ?m X propT" if "X \<in> set (C # Bs)" for X
        using that wS agS by (intro exI[of _ Ws] wt_modI[of _ _ _ smax]) (auto simp: vars_thm_def vars_list_implies)
      moreover have "\<exists>Wt. wt_mod ar A (tyenv env) W Wt ?m X propT" if "X \<in> set (rev rAs)" for X
        using that wR agR P by (intro exI[of _ Wr] wt_modI[of _ _ _ rmax]) (auto simp: vars_thm_def vars_list_implies)
      ultimately show "\<forall>(X, T)\<in>set (map (\<lambda>X. (X, propT)) (C # Bs @ rev rAs)). \<exists>Wt. wt_mod ar A (tyenv env) W Wt ?m X T"
        by auto
    qed
    have te: "vt_is_empty (tenv env)" using tv by (simp add: tvinv_def)
    have wfSp: "wfp ar ?S" "wfp ar rprop"
      using state(1) rule(1) by (simp_all add: wt_thm_def wt_term_def wfp_def swf_tm_def)
    have wfS: "\<forall>X\<in>set (C # Bs). wfp ar X" "ibelow smax Bi"
      using wfp_list_impliesD[OF wfSp(1)] state(2) by auto
    have stp: "\<forall>(t, u)\<in>set stpairs. \<forall>x\<in>vars t \<union> vars u. snd x \<le> smax"
      using state(1) by (fastforce simp: wt_thm_def wt_term_def below_def)
    have wfR: "\<forall>X\<in>set (rev rAs). wfp ar X" using wfp_list_impliesD[OF wfSp(2)[unfolded P]] by simp
    have lr: "lifted \<Longrightarrow> lifted_rule smax Bi (rev rAs) B"
      using lifted_over_lifted_rule[OF rule(2) sp1] by simp
    have nok: "newas_ok ?sp" by (rule call_newas_ok[OF refl wfR lr fl vl])
    have rok: "results_ok ?sp" by (rule call_results_ok[OF refl cfg finA paW rs te wfS stp wfR lr vl])
    have sel: "bs_cfg ?sp = cfg" "bs_vl ?sp = vl" "bs_A ?sp = A" "bs_env ?sp = env" "bs_eres ?sp = eres_flg"
      "bs_rAs ?sp = rAs" "bs_ctx ?sp = ?ctx B"
      by (simp_all add: call_spec_def Let_def)
    have ne: "eres_flg \<Longrightarrow> rAs \<noteq> []" using strip_prems_length[OF sp1 ns(1)] er by (auto simp: integer_reps)
    from bicompose_body_ok[of ?sp] cfg finA pa nok ne sel obtain s where
      b: "okT (bicompose_body (unify_ops cfg vl) (?ctx B) env eres_flg rAs) s" by auto
    have "okT (bicompose_aux (unify_ops cfg vl) alg flatten match_flg incremented
        (smax, stpairs, ?S) (stpairs, Bs, Bi, C) lifted eres_flg (rmax, rtpairs, rprop) nsubgoal) s"
      using r Some b unfolding eq by (auto simp: okT_bindT returnT_def)
    from call[OF sp1 e1 e2 this _ paW nok rok] b sel show thesis by simp
  qed
qed

text \<open>
  The main theorem on termination: for a well-typed proof state and a well-typed rule, lifted over
  the subgoal if \<open>lifted\<close>, \<open>bicompose_aux\<close> terminates without an exception, and so does pulling
  its sequence of results, which is finite. The rule must have at least \<open>nsubgoal\<close> premises, one
  at least for elim-resolution, which flattens parameters only for lifted rules.
\<close>

theorem bicompose_aux_terminates:
  assumes cfg: "cfg_alg cfg = alg" and finA: "finite A"
    and state: "wt_thm ar A Ws smax stpairs (list_implies (Bs @ [Bi]) C)" "ibelow smax (list_implies (Bs @ [Bi]) C)"
    and rule: "wt_thm ar A Wr rmax rtpairs rprop" "lifted \<Longrightarrow> lifted_over smax Bi rprop nsubgoal"
    and A: "scons A" "\<forall>p\<in>A. snd (fst p) \<le> max rmax smax" "\<forall>x. tyA ar A (Ws x)" "\<forall>x. tyA ar A (Wr x)"
    and inc: "incremented \<Longrightarrow>
      \<forall>x\<in>vars_thm stpairs (list_implies (Bs @ [Bi]) C) \<inter> vars_thm rtpairs rprop. Ws x = Wr x"
    and ns: "0 \<le> nsubgoal" "nsubgoal \<le> count_prems rprop" and er: "eres_flg \<Longrightarrow> 0 < nsubgoal"
    and fl: "eres_flg \<Longrightarrow> flatten \<Longrightarrow> lifted"
    and vl: "\<And>xs. length (vl xs) = length xs"
  shows "\<exists>s rs. okT (bicompose_aux (unify_ops cfg vl) alg flatten match_flg incremented
      (smax, stpairs, list_implies (Bs @ [Bi]) C) (stpairs, Bs, Bi, C) lifted eres_flg (rmax, rtpairs, rprop) nsubgoal) s \<and>
    bevals (unify_ops cfg vl) s rs"
proof (rule bicompose_aux_call[where lifted = lifted and incremented = incremented and eres_flg = eres_flg
      and flatten = flatten and match_flg = match_flg, OF assms], (assumption+)?, goal_cases types call)
  case types
  have "bpull (unify_ops cfg vl) BS_Empty = returnT None" by (subst bpull.simps) simp
  then have "bevals (unify_ops cfg vl) BS_Empty []" by (auto intro: bevals.Nil)
  with types(3) show ?thesis by blast
next
  case (call rAs B env s W)
  let ?sp = "call_spec cfg A vl env flatten match_flg smax stpairs Bs Bi C lifted eres_flg rtpairs rAs B"
  have sel: "bs_cfg ?sp = cfg" "bs_vl ?sp = vl" "bs_A ?sp = A" "bs_env ?sp = env" "bs_eres ?sp = eres_flg"
    "bs_rAs ?sp = rAs"
    by (simp_all add: call_spec_def Let_def)
  have pa: "pinv_all ?sp" by (rule pinv_allW_pinv_all[OF call(6)])
  have "binv ?sp s" by (rule bicompose_body_binv) (use call(5) cfg finA pa sel in simp_all)
  from bpull_bevals[OF _ _ pa call(7,8) _ this] cfg finA sel obtain rs where "bevals (unify_ops cfg vl) s rs"
    by auto
  with call(4) show ?thesis by blast
qed

end

end

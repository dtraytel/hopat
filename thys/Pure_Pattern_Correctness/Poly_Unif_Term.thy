section \<open>Termination of Polymorphic Unification\<close>

theory Poly_Unif_Term
  imports Poly_Unif_Correct
begin

text \<open>
  Polymorphic unification runs in lockstep with the monomorphic unification of a faithful ground
  instance as long as its type environment is unchanged. Each change of the type environment
  reduces the number of unbound type variables reachable from the problem. Termination follows
  from the termination of the monomorphic algorithm by induction on this number.
\<close>


subsection \<open>Steps of type unification\<close>

text \<open>The counter for new type variables only changes together with the type environment.\<close>

definition tgrow :: "tstate \<Rightarrow> tstate \<Rightarrow> bool" where
  "tgrow st st' \<longleftrightarrow> textends (fst st) (fst st') \<and> (fst st' = fst st \<longrightarrow> snd st' = snd st)"

lemma tgrow_refl[simp]: "tgrow st st"
  by (simp add: tgrow_def)

lemma textends_antisym: "textends \<theta> \<theta>' \<Longrightarrow> textends \<theta>' \<theta> \<Longrightarrow> \<theta>' = \<theta>"
  unfolding textends_def by (rule vt_eqI) (metis not_None_eq)

lemma tgrow_trans: "tgrow st1 st2 \<Longrightarrow> tgrow st2 st3 \<Longrightarrow> tgrow st1 st3"
  unfolding tgrow_def by (metis textends_antisym textends_trans)

lemma update_new_tgrow: "update_new (v, x) \<theta> = Some (Ok \<theta>') \<Longrightarrow> tgrow (\<theta>, n) (\<theta>', n')"
proof -
  assume u: "update_new (v, x) \<theta> = Some (Ok \<theta>')"
  then have v: "vt_lookup \<theta> v = None" and \<theta>': "\<theta>' = vt_update (v, x) \<theta>"
    unfolding update_new_def vt_defined_lookup
    by (simp_all add: raise_def return_def split: if_splits) (metis not_None_eq surj_pair)
  then have "textends \<theta> \<theta>'" by (simp add: textends_update)
  moreover have "\<theta>' \<noteq> \<theta>" using v \<theta>' by (metis option.distinct(1) vt_lookup_update)
  ultimately show ?thesis by (simp add: tgrow_def)
qed

lemma foldM_tgrow:
  "foldM f xs st = Some (Ok st') \<Longrightarrow> (\<And>x st st'. x \<in> set xs \<Longrightarrow> f x st = Some (Ok st') \<Longrightarrow> tgrow st st') \<Longrightarrow>
    tgrow st st'"
proof (induction xs arbitrary: st)
  case (Cons x xs)
  from Cons.prems(1) obtain st1 where "f x st = Some (Ok st1)" "foldM f xs st1 = Some (Ok st')"
    by (auto simp: bindM_def split: option.splits res.splits)
  with Cons show ?case by (meson list.set_intros tgrow_trans)
qed (simp add: return_def)

lemma meet_tgrow: "meet alg T S st = Some r \<Longrightarrow> r = Ok st' \<Longrightarrow> tgrow st st'"
proof (induction alg T S st r arbitrary: st' rule: meet.raw_induct[rotated, consumes 1])
  case (1 meet alg T S st r)
  obtain tye cnt where st: "st = (tye, cnt)" by force
  have step: "tgrow st1 st2"
    if "(\<lambda>(T, S) st. devar (fst st) T \<bind> (\<lambda>T'. meet alg T' S st)) x st1 = Some (Ok st2)" for x st1 st2
    using that "1.IH" by (auto simp: bindM_def split: option.splits res.splits prod.splits)
  show ?case
  proof (cases "S = []")
    case True
    with "1.hyps" "1.prems" show ?thesis by (simp add: return_def)
  next
    case False
    show ?thesis
    proof (cases T)
      case (TVar xi S')
      with "1.hyps" "1.prems" False st show ?thesis
        by (auto simp: Let_def return_def bindM_def gen_tyvar_def split: if_splits option.splits res.splits
          intro: update_new_tgrow)
    next
      case (TFree a S')
      with "1.hyps" "1.prems" False st show ?thesis by (auto simp: return_def raise_def split: if_splits)
    next
      case (Type a Ts)
      from "1.hyps" "1.prems" False Type st obtain Ss where
        "foldM (\<lambda>(T, S) st. devar (fst st) T \<bind> (\<lambda>T'. meet alg T' S st)) (zip Ts Ss) st = Some (Ok st')"
        by (auto simp: bindM_def split: option.splits res.splits)
      from foldM_tgrow[OF this step] show ?thesis .
    qed
  qed
qed

lemma unify_aux_tgrow: "unify_aux alg T U st = Some r \<Longrightarrow> r = Ok st' \<Longrightarrow> tgrow st st'"
proof (induction alg T U st r arbitrary: st' rule: unify_aux.raw_induct[rotated, consumes 1])
  case (1 unify_aux alg T U st r)
  obtain tye cnt where st: "st = (tye, cnt)" by force
  have step: "tgrow st1 st2" if "(\<lambda>(T, U) st. unify_aux alg T U st) x st1 = Some (Ok st2)" for x st1 st2
    using that "1.IH" by (auto split: prod.splits)
  from "1.hyps" "1.prems" st obtain T' U' where dT: "devar tye T = Some (Ok T')" and dU: "devar tye U = Some (Ok U')"
    and r: "(case (T', U') of
        (TVar v S1, TVar w S2) \<Rightarrow>
          if v = w then (if S1 = S2 then return st else tvar_clash v S1 S2)
          else if sort_le alg S1 S2 then do {tye' \<leftarrow> update_new (w, (S2, T')) tye; return (tye', cnt)}
          else if sort_le alg S2 S1 then do {tye' \<leftarrow> update_new (v, (S1, U')) tye; return (tye', cnt)}
          else do {
            let (S, cnt') = gen_tyvar (inter_sort alg S1 S2) cnt;
            tye' \<leftarrow> update_new (w, (S2, S)) tye;
            tye'' \<leftarrow> update_new (v, (S1, S)) tye';
            return (tye'', cnt')}
      | (TVar v S, _) \<Rightarrow> do {
          b \<leftarrow> type_occurs v tye U';
          if b then raise TUnify else do {tye' \<leftarrow> update_new (v, (S, U')) tye; meet alg U' S (tye', cnt)}}
      | (_, TVar v S) \<Rightarrow> do {
          b \<leftarrow> type_occurs v tye T';
          if b then raise TUnify else do {tye' \<leftarrow> update_new (v, (S, T')) tye; meet alg T' S (tye', cnt)}}
      | (Type a Ts, Type b Us) \<Rightarrow>
          if a \<noteq> b then raise TUnify
          else foldM (\<lambda>(T, U) st. unify_aux alg T U st) (zip Ts Us) st
      | _ \<Rightarrow> if T' = U' then return st else raise TUnify) = Some (Ok st')"
    by (auto simp: bindM_def split: option.splits res.splits)
  show ?case
  proof (cases T')
    case T'v: (TVar v S1)
    show ?thesis
    proof (cases U')
      case (TVar w S2)
      have tt: "tgrow (tye, cnt) (tye'', cnt')" if "update_new (w, x) tye = Some (Ok tye')"
        "update_new (v, y) tye' = Some (Ok tye'')" for x y tye' tye'' cnt'
        using update_new_tgrow[OF that(1), of cnt cnt] update_new_tgrow[OF that(2), of cnt cnt']
        by (rule tgrow_trans)
      from r T'v TVar st show ?thesis
        by (auto simp: Let_def return_def raise_def bindM_def gen_tyvar_def tvar_clash_def
          split: if_splits option.splits res.splits intro: update_new_tgrow tt)
    qed (use r T'v st in \<open>auto simp: return_def raise_def bindM_def split: if_splits option.splits res.splits
      intro: tgrow_trans[OF update_new_tgrow meet_tgrow]\<close>)
  next
    case (Type a Ts)
    show ?thesis
    proof (cases U')
      case (Type b Us)
      from r \<open>T' = Type a Ts\<close> Type st
      have "foldM (\<lambda>(T, U) st. unify_aux alg T U st) (zip Ts Us) st = Some (Ok st')"
        by (auto simp: raise_def split: if_splits)
      from foldM_tgrow[OF this step] show ?thesis .
    qed (use r \<open>T' = Type a Ts\<close> st in \<open>auto simp: return_def raise_def bindM_def split: if_splits option.splits
      res.splits intro: tgrow_trans[OF update_new_tgrow meet_tgrow]\<close>)
  next
    case (TFree a S)
    with r st show ?thesis
      by (cases U') (auto simp: return_def raise_def bindM_def split: if_splits option.splits res.splits
        intro: tgrow_trans[OF update_new_tgrow meet_tgrow])
  qed
qed

lemma unify_types_same:
  assumes "unify_types alg T U env = Some (Ok env1)" "tyenv env1 = tyenv env"
  shows "env1 = env"
proof (cases "T = U")
  case False
  with assms(1) obtain \<theta>' n' where u: "unify_aux alg U T (tyenv env, maxidx env) = Some (Ok (\<theta>', n'))"
    and e: "env1 = Envir n' (tenv env) \<theta>'"
    by (auto simp: unify_types_def type_unify_def handle_def bindM_def return_def raise_def
      split: option.splits res.splits prod.splits exn.splits)
  from unify_aux_tgrow[OF u refl] e assms(2) show ?thesis by (cases env) (simp add: tgrow_def)
qed (use assms in \<open>simp add: unify_types_def return_def\<close>)


subsection \<open>Acyclic environments\<close>

text \<open>
  The dependencies between the variables of an environment, ignoring their types. The instances of
  a well-typed environment are acyclic if and only if these dependencies are.
\<close>

definition ndep :: "env \<Rightarrow> (indexname \<times> indexname) set" where
  "ndep env = {(y, x). \<exists>U u. vt_lookup (tenv env) x = Some (U, u) \<and> y \<in> vars u}"

definition nacyc :: "env \<Rightarrow> bool" where
  "nacyc env \<longleftrightarrow> acyclic (ndep env)"

lemma nacyc_same_tenv: "tenv env1 = tenv env \<Longrightarrow> nacyc env1 \<longleftrightarrow> nacyc env"
  by (simp add: nacyc_def ndep_def)

lemma trancl_map_prod_inj:
  assumes "inj g"
  shows "(x, y) \<in> (map_prod g g ` R)\<^sup>+ \<Longrightarrow> \<exists>a b. x = g a \<and> y = g b \<and> (a, b) \<in> R\<^sup>+"
    and "(a, b) \<in> R\<^sup>+ \<Longrightarrow> (g a, g b) \<in> (map_prod g g ` R)\<^sup>+"
proof -
  show "(x, y) \<in> (map_prod g g ` R)\<^sup>+ \<Longrightarrow> \<exists>a b. x = g a \<and> y = g b \<and> (a, b) \<in> R\<^sup>+"
  proof (induction rule: trancl_induct)
    case (step y z)
    then obtain a b c d where "x = g a" "y = g b" "(a, b) \<in> R\<^sup>+" "y = g c" "z = g d" "(c, d) \<in> R" by auto
    with injD[OF assms] show ?case by (metis trancl_into_trancl)
  qed auto
  show "(a, b) \<in> R\<^sup>+ \<Longrightarrow> (g a, g b) \<in> (map_prod g g ` R)\<^sup>+"
    by (induction rule: trancl_induct) (auto intro: trancl_into_trancl)
qed

lemma acyclic_map_prod_inj: "inj g \<Longrightarrow> acyclic (map_prod g g ` R) \<longleftrightarrow> acyclic R"
  unfolding acyclic_def by (metis injD trancl_map_prod_inj)

lemma acyc_instE:
  assumes ty: "env_typed W (instE \<rho> env)"
  shows "acyc (instE \<rho> env) \<longleftrightarrow> nacyc env"
proof -
  define g where "g = (\<lambda>z. (z, W z))"
  have "dep (instE \<rho> env) = map_prod g g ` ndep env"
  proof (intro set_eqI iffI)
    fix p assume "p \<in> dep (instE \<rho> env)"
    then obtain y x T u where p: "p = (y, (x, T))" and l: "lk (instE \<rho> env) x T = Some u" and y: "y \<in> vps u"
      by (auto simp: dep_def)
    from lkD[OF l] obtain U u0 where b: "vt_lookup (tenv env) x = Some (U, u0)" and T: "T = tsubst \<rho> U"
      and u: "u = inst \<rho> u0" by auto
    from env_typedD[OF ty lkD[OF l]] have Wx: "W x = T" and tyu: "has_type W [] u T" by simp_all
    have Wy: "W (fst y) = snd y" using has_type_vps[OF tyu, of "fst y" "snd y"] y by simp
    have "fst y \<in> vars u0" using y u vps_vars[of y u] by simp
    with b have n: "(fst y, x) \<in> ndep env" by (auto simp: ndep_def)
    have "p = map_prod g g (fst y, x)" using p Wx Wy by (simp add: g_def prod_eq_iff)
    with n show "p \<in> map_prod g g ` ndep env" by blast
  next
    fix p assume "p \<in> map_prod g g ` ndep env"
    then obtain y x U u where p: "p = (g y, g x)" and b: "vt_lookup (tenv env) x = Some (U, u)"
      and y: "y \<in> vars u" by (auto simp: ndep_def)
    have b': "vt_lookup (tenv (instE \<rho> env)) x = Some (tsubst \<rho> U, inst \<rho> u)" using b by simp
    from env_typedD[OF ty b'] have Wx: "W x = tsubst \<rho> U" and tyu: "has_type W [] (inst \<rho> u) (tsubst \<rho> U)"
      by simp_all
    have "(y, W y) \<in> vps (inst \<rho> u)" by (rule vps_typed[OF tyu]) (use y in simp)
    moreover have "lk (instE \<rho> env) x (W x) = Some (inst \<rho> u)" using b Wx by (simp add: lk_def)
    ultimately show "p \<in> dep (instE \<rho> env)" using p by (auto simp: g_def dep_def)
  qed
  moreover have "inj g" by (auto simp: g_def inj_def)
  ultimately show ?thesis by (simp add: acyc_def nacyc_def acyclic_map_prod_inj)
qed

lemma inst_env_inv:
  assumes "pre alg ar A bs s t env" "gsol alg ar (tyenv env) \<rho>" "nacyc env"
  obtains W U where "env_inv ar W (instE \<rho> env)" "binders_ok ar (instb \<rho> bs)"
    "wf_term ar (length (instb \<rho> bs)) (inst \<rho> s)" "wf_term ar (length (instb \<rho> bs)) (inst \<rho> t)"
    "has_type W (map snd (instb \<rho> bs)) (inst \<rho> s) U" "has_type W (map snd (instb \<rho> bs)) (inst \<rho> t) U"
    "below (maxidx (instE \<rho> env)) (inst \<rho> s)" "below (maxidx (instE \<rho> env)) (inst \<rho> t)"
proof -
  from preD(6)[OF assms(1,2)] obtain W where i: "inst_ok ar W \<rho> bs s t env" by blast
  from inst_okD(7)[OF i] obtain U where "has_type W (map snd (instb \<rho> bs)) (inst \<rho> s) U"
    "has_type W (map snd (instb \<rho> bs)) (inst \<rho> t) U" by blast
  moreover have "env_inv ar W (instE \<rho> env)"
    using inst_okD(1-3)[OF i] acyc_instE[OF inst_okD(2)[OF i]] assms(3) by (simp add: env_inv_def)
  ultimately show ?thesis using that inst_okD(4-6)[OF i] preD(4,5)[OF assms(1)] by simp
qed

text \<open>Results of the monomorphic algorithm on instances are acyclic.\<close>

lemma inst_result_nacyc:
  assumes "pre alg ar A bs s t env" "gsol alg ar (tyenv env) \<rho>" "nacyc env"
    and u: "unif alg (instb \<rho> bs) (inst \<rho> s) (inst \<rho> t) (instE \<rho> env) = Some (Ok (instE \<rho> env'))"
  shows "nacyc env'"
proof -
  obtain W U where h: "env_inv ar W (instE \<rho> env)" "binders_ok ar (instb \<rho> bs)"
    "wf_term ar (length (instb \<rho> bs)) (inst \<rho> s)" "wf_term ar (length (instb \<rho> bs)) (inst \<rho> t)"
    "has_type W (map snd (instb \<rho> bs)) (inst \<rho> s) U" "has_type W (map snd (instb \<rho> bs)) (inst \<rho> t) U"
    "below (maxidx (instE \<rho> env)) (inst \<rho> s)" "below (maxidx (instE \<rho> env)) (inst \<rho> t)"
    by (rule inst_env_inv[OF assms(1-3)])
  from unif_term[OF refl h, where alg = alg] u obtain W' where "env_inv ar W' (instE \<rho> env')" by (auto simp: uq_def)
  then show ?thesis using acyc_instE by (auto simp: env_inv_def)
qed


subsection \<open>The measure\<close>

context wf_algebra
begin

lemma unify_types_card:
  assumes fin: "finite A" and inv: "tinv ar (maxidx env) (tyenv env) A" and srt: "tsorted alg (tyenv env)"
    and T: "tyw ar (tyenv env) A T" and U: "tyw ar (tyenv env) A U"
    and u: "unify_types alg T U env = Some (Ok env1)"
  shows "tyenv env1 = tyenv env \<or> card (uvarsA (tyenv env1) A) < card (uvarsA (tyenv env) A)"
proof -
  obtain xs where xs: "set xs = A" using finite_list[OF fin] by blast
  define X where "X = Type STR '''' (map (\<lambda>(v, S). TVar v S) xs)"
  have UX: "uvars \<theta> X = uvarsA \<theta> A" for \<theta> by (auto simp: X_def uvarsA_def xs[symmetric])
  have X: "uvars (tyenv env) T \<union> uvars (tyenv env) U \<subseteq> uvars (tyenv env) X" using T U UX by (simp add: tyw_def)
  from unify_types_poly[OF inv srt T U] u
  have "uvars (tyenv env) T \<union> uvars (tyenv env) U \<subseteq> uvars (tyenv env) X \<Longrightarrow>
      tyenv env1 = tyenv env \<or> card (uvars (tyenv env1) X) < card (uvars (tyenv env) X)"
    by auto
  from this[OF X] show ?thesis by (simp add: UX)
qed

end

text \<open>
  The property of terminating runs: results are acyclic, and either keep the type environment or
  reduce the measure.
\<close>

definition tres :: "(indexname \<times> psort) set \<Rightarrow> env \<Rightarrow> env res \<Rightarrow> bool" where
  "tres A env r \<longleftrightarrow> (\<forall>env'. r = Ok env' \<longrightarrow> nacyc env' \<and>
    (tyenv env' = tyenv env \<or> card (uvarsA (tyenv env') A) < card (uvarsA (tyenv env) A)))"

lemma tres_Err[simp]: "tres A env (Err e)"
  by (simp add: tres_def)

lemma tres_trans: "tres A env (Ok e1) \<Longrightarrow> tres A e1 r \<Longrightarrow> tres A env r"
  unfolding tres_def by (metis order.strict_trans)

text \<open>Results related to the results of a faithful instance as long as the type environment is kept.\<close>

definition lock :: "tinst \<Rightarrow> env \<Rightarrow> env res \<Rightarrow> env res \<Rightarrow> bool" where
  "lock \<rho> env r r' \<longleftrightarrow> (\<forall>env'. r = Ok env' \<longrightarrow> tyenv env' = tyenv env \<longrightarrow> r' = Ok (instE \<rho> env'))"

lemma lock_Err[simp]: "lock \<rho> env (Err e) r'"
  by (simp add: lock_def)


subsection \<open>Sequences of equations\<close>

context wf_algebra
begin

text \<open>Sequences of equations terminate if all problems with a smaller measure do.\<close>

lemma foldM_oih:
  assumes "prel alg ar A bs ps env" "nacyc env" "card (uvarsA (tyenv env) A) < k"
    and OIH: "\<And>bs s t env. pre alg ar A bs s t env \<Longrightarrow> nacyc env \<Longrightarrow> card (uvarsA (tyenv env) A) < k \<Longrightarrow>
      \<exists>r. unif alg bs s t env = Some r \<and> tres A env r"
  shows "\<exists>r. foldM (\<lambda>(s, t) e. unif alg bs s t e) ps env = Some r \<and> tres A env r"
  using assms(1-3)
proof (induction ps arbitrary: env)
  case Nil
  then show ?case by (simp add: return_def tres_def)
next
  case (Cons p ps)
  obtain s t where p: "p = (s, t)" by force
  note pre = Cons.prems(1)[unfolded p]
  from OIH[OF prel_ConsD[OF pre] Cons.prems(2,3)] obtain r1 where r1: "unif alg bs s t env = Some r1"
    and q1: "tres A env r1" by blast
  show ?case
  proof (cases r1)
    case (Err e)
    with r1 p show ?thesis by simp
  next
    case (Ok e1)
    have "post_all alg ar A bs s t env (Ok e1)" by (rule unif_post[OF r1[unfolded Ok] refl prel_ConsD[OF pre]])
    then have ok: "postok alg ar A bs s t env e1" by (simp add: post_all_def)
    from q1 Ok have n1: "nacyc e1"
      and c1: "tyenv e1 = tyenv env \<or> card (uvarsA (tyenv e1) A) < card (uvarsA (tyenv env) A)"
      by (auto simp: tres_def)
    then have "card (uvarsA (tyenv e1) A) < k" using Cons.prems(3) by auto
    from Cons.IH[OF prel_step[OF pre ok] n1 this] obtain r
      where "foldM (\<lambda>(s, t) e. unif alg bs s t e) ps e1 = Some r" "tres A e1 r" by blast
    with r1 Ok p q1 show ?thesis by (auto intro: tres_trans)
  qed
qed

text \<open>Sequences of equations run in lockstep with a faithful instance.\<close>

lemma foldM_lock:
  assumes fo: "foldM (\<lambda>(s, t) e. uni alg (instb \<rho> bs) s t e) (map (map_prod (inst \<rho>) (inst \<rho>)) ps) (instE \<rho> env)
      = Some r'"
    and pre: "prel alg ar A bs ps env" and n: "nacyc env" and th: "tyenv env = \<theta>"
    and k: "card (uvarsA \<theta> A) = k"
    and IH: "\<And>s t e r'. (s, t) \<in> set ps \<Longrightarrow> uni alg (instb \<rho> bs) (inst \<rho> s) (inst \<rho> t) (instE \<rho> e) = Some r' \<Longrightarrow>
      tyenv e = \<theta> \<Longrightarrow> pre alg ar A bs s t e \<Longrightarrow> nacyc e \<Longrightarrow>
      \<exists>r. unif alg bs s t e = Some r \<and> tres A e r \<and> lock \<rho> e r r'"
    and OIH: "\<And>bs s t env. pre alg ar A bs s t env \<Longrightarrow> nacyc env \<Longrightarrow> card (uvarsA (tyenv env) A) < k \<Longrightarrow>
      \<exists>r. unif alg bs s t env = Some r \<and> tres A env r"
  shows "\<exists>r. foldM (\<lambda>(s, t) e. unif alg bs s t e) ps env = Some r \<and> tres A env r \<and> lock \<rho> env r r'"
  using fo pre n th IH
proof (induction ps arbitrary: env r')
  case Nil
  then show ?case by (simp add: return_def tres_def lock_def)
next
  case (Cons p ps)
  obtain s t where p: "p = (s, t)" by force
  note pre = Cons.prems(2)[unfolded p]
  from Cons.prems(1) p have "uni alg (instb \<rho> bs) (inst \<rho> s) (inst \<rho> t) (instE \<rho> env) \<bind>
      (\<lambda>e. foldM (\<lambda>(s, t) e. uni alg (instb \<rho> bs) s t e) (map (map_prod (inst \<rho>) (inst \<rho>)) ps) e) = Some r'"
    by simp
  then obtain r1' where u1: "uni alg (instb \<rho> bs) (inst \<rho> s) (inst \<rho> t) (instE \<rho> env) = Some r1'"
    and rest: "\<And>e1'. r1' = Ok e1' \<Longrightarrow>
      foldM (\<lambda>(s, t) e. uni alg (instb \<rho> bs) s t e) (map (map_prod (inst \<rho>) (inst \<rho>)) ps) e1' = Some r'"
    by (auto simp: bindM_def split: option.splits res.splits)
  from Cons.prems(5)[OF _ u1 Cons.prems(4) prel_ConsD[OF pre] Cons.prems(3)] p
  obtain r1 where r1: "unif alg bs s t env = Some r1" and q1: "tres A env r1" and l1: "lock \<rho> env r1 r1'"
    by auto
  show ?case
  proof (cases r1)
    case (Err e)
    with r1 p show ?thesis by simp
  next
    case (Ok e1)
    have "post_all alg ar A bs s t env (Ok e1)" by (rule unif_post[OF r1[unfolded Ok] refl prel_ConsD[OF pre]])
    then have pre1: "prel alg ar A bs ps e1" by (intro prel_step[OF pre]) (simp add: post_all_def)
    from q1 Ok have n1: "nacyc e1"
      and c1: "tyenv e1 = tyenv env \<or> card (uvarsA (tyenv e1) A) < card (uvarsA (tyenv env) A)"
      by (auto simp: tres_def)
    show ?thesis
    proof (cases "tyenv e1 = \<theta>")
      case True
      with l1 Ok Cons.prems(4) have "r1' = Ok (instE \<rho> e1)" by (simp add: lock_def)
      from Cons.IH[OF rest[OF this] pre1 n1 True] Cons.prems(5) obtain r
        where r: "foldM (\<lambda>(s, t) e. unif alg bs s t e) ps e1 = Some r" and q: "tres A e1 r" and l: "lock \<rho> e1 r r'"
        by force
      have "lock \<rho> env r r'" using l True Cons.prems(4) by (simp add: lock_def)
      with r r1 Ok p q1 q show ?thesis by (auto intro: tres_trans)
    next
      case False
      with c1 Cons.prems(4) k have lt: "card (uvarsA (tyenv e1) A) < k" by auto
      from foldM_oih[OF pre1 n1 lt OIH] obtain r
        where r: "foldM (\<lambda>(s, t) e. unif alg bs s t e) ps e1 = Some r" and q: "tres A e1 r" by blast
      have "lock \<rho> env r r'"
        unfolding lock_def
      proof (intro allI impI)
        fix env' assume "r = Ok env'" "tyenv env' = tyenv env"
        with q False lt Cons.prems(4) k show "r' = Ok (instE \<rho> env')" by (auto simp: tres_def)
      qed
      with r r1 Ok p q1 q show ?thesis by (auto intro: tres_trans)
    qed
  qed
qed

end

end

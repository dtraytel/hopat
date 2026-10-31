section \<open>Termination of Polymorphic Unification\<close>

theory Poly_Unif_Term
  imports Poly_Unif_Correct
begin

context csig
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

end

context wf_csig
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

context csig
begin

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

end

context wf_csig
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

lemma zip_map_inst: "zip (map f xs) (map f ys) = map (map_prod f f) (zip xs ys)"
  by (induction xs ys rule: list_induct2') simp_all

text \<open>Equal rigid heads, after the step on the type environment.\<close>

lemma rigid_lock:
  assumes pre: "pre alg ar A bs s t env"
    and shs: "strip_comb s = (h, ss)" and sht: "strip_comb t = (h', ts)"
    and rh: "is_rigid h" "is_rigid h'"
    and te: "tenv env1 = tenv env"
    and st: "tstep alg ar A (\<lambda>\<rho>. inst \<rho> h = inst \<rho> h') (tyenv env) (maxidx env) (tyenv env1) (maxidx env1)"
    and srt1: "tsorted alg (tyenv env1)"
    and eq1: "\<And>\<rho>. gsol alg ar (tyenv env1) \<rho> \<Longrightarrow> inst \<rho> h = inst \<rho> h'"
    and n: "nacyc env" and k: "card (uvarsA (tyenv env) A) = k"
    and c: "env1 = env \<or> card (uvarsA (tyenv env1) A) < k"
    and fo': "env1 = env \<Longrightarrow> zip_eq (map (inst \<rho>) ss) (map (inst \<rho>) ts) \<bind>
      (\<lambda>ps. foldM (\<lambda>(s, t) e. uni alg (instb \<rho> bs) s t e) ps (instE \<rho> env)) = Some r'"
    and IH: "\<And>s t e r'. uni alg (instb \<rho> bs) (inst \<rho> s) (inst \<rho> t) (instE \<rho> e) = Some r' \<Longrightarrow>
      tyenv e = tyenv env \<Longrightarrow> pre alg ar A bs s t e \<Longrightarrow> nacyc e \<Longrightarrow>
      \<exists>r. unif alg bs s t e = Some r \<and> tres A e r \<and> lock \<rho> e r r'"
    and OIH: "\<And>bs s t env. pre alg ar A bs s t env \<Longrightarrow> nacyc env \<Longrightarrow> card (uvarsA (tyenv env) A) < k \<Longrightarrow>
      \<exists>r. unif alg bs s t env = Some r \<and> tres A env r"
  shows "\<exists>r. zip_eq ss ts \<bind> (\<lambda>ps. foldM (\<lambda>(s, t) e. unif alg bs s t e) ps env1) = Some r \<and>
    tres A env r \<and> lock \<rho> env r r'"
proof -
  have len: "length ss = length ts" by (rule rigid_decomp(1)[OF pre shs sht rh te st srt1]) (fact eq1)
  have pre1: "prel alg ar A bs (zip ss ts) env1" by (rule rigid_decomp(2)[OF pre shs sht rh te st srt1]) (fact eq1)
  have n1: "nacyc env1" using n nacyc_same_tenv[OF te] by simp
  have z: "zip_eq ss ts = return (zip ss ts)" by (rule zip_eq_return[OF len])
  from c show ?thesis
  proof
    assume e: "env1 = env"
    have "foldM (\<lambda>(s, t) e. uni alg (instb \<rho> bs) s t e) (map (map_prod (inst \<rho>) (inst \<rho>)) (zip ss ts))
        (instE \<rho> env) = Some r'"
      using fo'[OF e] len by (simp add: zip_eq_return zip_map_inst)
    then have "\<exists>r. foldM (\<lambda>(s, t) e. unif alg bs s t e) (zip ss ts) env = Some r \<and> tres A env r \<and> lock \<rho> env r r'"
      by (rule foldM_lock[OF _ pre1[unfolded e] n refl k]) (blast intro: IH OIH)+
    with e z show ?thesis by simp
  next
    assume lt: "card (uvarsA (tyenv env1) A) < k"
    from foldM_oih[OF pre1 n1 lt OIH] obtain r
      where r: "foldM (\<lambda>(s, t) e. unif alg bs s t e) (zip ss ts) env1 = Some r" and q: "tres A env1 r" by blast
    have t1: "tres A env (Ok env1)" using n1 lt k by (simp add: tres_def)
    have "lock \<rho> env r r'"
      unfolding lock_def
    proof (intro allI impI)
      fix env' assume "r = Ok env'" "tyenv env' = tyenv env"
      with q lt k show "r' = Ok (instE \<rho> env')" by (auto simp: tres_def)
    qed
    with r z tres_trans[OF t1 q] show ?thesis by simp
  qed
qed


subsection \<open>Lockstep with a faithful instance\<close>

text \<open>
  By induction on the computation of the monomorphic algorithm on a faithful instance: the
  polymorphic algorithm follows it as long as the type environment is kept, and terminates by the
  induction hypothesis \<open>OIH\<close> on the measure once the type environment changes.
\<close>

lemma lockstep:
  assumes fin: "finite A"
    and OIH: "\<And>bs s t env. pre alg ar A bs s t env \<Longrightarrow> nacyc env \<Longrightarrow> card (uvarsA (tyenv env) A) < k \<Longrightarrow>
      \<exists>r. unif alg bs s t env = Some r \<and> tres A env r"
    and u: "unif alg' bs' s' t' e' = Some r'"
  shows "alg' = alg \<Longrightarrow> bs' = instb \<rho> bs \<Longrightarrow> s' = inst \<rho> s \<Longrightarrow> t' = inst \<rho> t \<Longrightarrow> e' = instE \<rho> env \<Longrightarrow>
    gsol alg ar (tyenv env) \<rho> \<Longrightarrow> tfree_on \<rho> (tyenv env) \<Longrightarrow> card (uvarsA (tyenv env) A) = k \<Longrightarrow>
    pre alg ar A bs s t env \<Longrightarrow> nacyc env \<Longrightarrow>
    \<exists>r. unif alg bs s t env = Some r \<and> tres A env r \<and> lock \<rho> env r r'"
  using u
proof (induction alg' bs' s' t' e' r' arbitrary: bs s t env rule: unif.raw_induct[rotated, consumes 1])
  case (1 uni alg' bs' s' t' e' r')
  note eqs = "1.prems"(1-5)
  have g: "gsol alg ar (tyenv env) \<rho>" and tf: "tfree_on \<rho> (tyenv env)" and k: "card (uvarsA (tyenv env) A) = k"
    and pre: "pre alg ar A bs s t env" and n: "nacyc env" using "1.prems" by simp_all
  have sol: "tsol (tyenv env) \<rho>" using g by (simp add: gsol_def)
  have IH: "\<exists>r. unif alg bs1 s1 t1 e1 = Some r \<and> tres A e1 r \<and> lock \<rho> e1 r r1'"
    if "uni alg (instb \<rho> bs1) (inst \<rho> s1) (inst \<rho> t1) (instE \<rho> e1) = Some r1'" "tyenv e1 = tyenv env"
      "pre alg ar A bs1 s1 t1 e1" "nacyc e1" for bs1 s1 t1 e1 r1'
    using "1.IH"[OF that(1) refl refl refl refl refl] g tf k that(2-4) by simp
  have u: "head_norm (instE \<rho> env) (inst \<rho> s) \<bind> (\<lambda>s''. head_norm (instE \<rho> env) (inst \<rho> t) \<bind>
      (\<lambda>t''. ustep uni alg (instb \<rho> bs) s'' t'' (instE \<rho> env))) = Some r'"
    using "1.hyps" eqs unfolding ustep_def by (simp only:)
  from u obtain rs' where hs': "head_norm (instE \<rho> env) (inst \<rho> s) = Some rs'"
    by (cases "head_norm (instE \<rho> env) (inst \<rho> s)") (auto simp: bindM_def)
  have hsr: "head_norm (instE \<rho> env) (inst \<rho> s) = instM \<rho> (inst \<rho>) (head_norm env s)"
    by (rule pre_head_norm_inst(1)[OF pre sol])
  with hs' obtain rs where hs: "head_norm env s = Some rs" by (cases "head_norm env s") (simp_all add: instM_def)
  from pre_head_norm_Ok[OF pre hs] obtain s0 where rs: "rs = Ok s0" by blast
  have hs'': "head_norm (instE \<rho> env) (inst \<rho> s) = Some (Ok (inst \<rho> s0))" using hsr hs rs by simp
  from u hs'' obtain rt' where ht': "head_norm (instE \<rho> env) (inst \<rho> t) = Some rt'"
    by (cases "head_norm (instE \<rho> env) (inst \<rho> t)") (auto simp: bindM_def)
  have htr: "head_norm (instE \<rho> env) (inst \<rho> t) = instM \<rho> (inst \<rho>) (head_norm env t)"
    by (rule pre_head_norm_inst(2)[OF pre sol])
  with ht' obtain rt where ht: "head_norm env t = Some rt" by (cases "head_norm env t") (simp_all add: instM_def)
  from pre_head_norm_Ok[OF pre_commute[THEN iffD2, OF pre] ht] obtain t0 where rt: "rt = Ok t0" by blast
  have ht'': "head_norm (instE \<rho> env) (inst \<rho> t) = Some (Ok (inst \<rho> t0))" using htr ht rt by simp
  note hs = hs[unfolded rs] and ht = ht[unfolded rt]
  from u hs'' ht'' have ust': "ustep uni alg (instb \<rho> bs) (inst \<rho> s0) (inst \<rho> t0) (instE \<rho> env) = Some r'"
    by simp
  have ust: "unif alg bs s t env = ustep unif alg bs s0 t0 env" by (subst unif_ustep) (simp add: hs ht)
  from pre_head_norm[OF pre hs ht] have pre0: "pre alg ar A bs s0 t0 env" by blast
  show ?case
  proof (cases "is_Abs s0")
    case sA: True
    then obtain ns Ts ts where s0a: "s0 = pterm.Abs ns Ts ts" by (cases s0) auto
    show ?thesis
    proof (cases "is_Abs t0")
      case True
      then obtain nt Tt tt where t0a: "t0 = pterm.Abs nt Tt tt" by (cases t0) auto
      define nm where "nm = (if ns = STR '''' then nt else ns)"
      have pu: "unif alg bs s t env = unify_types alg Ts Tt env \<bind> (\<lambda>env'. unif alg ((nm, Ts) # bs) ts tt env')"
        using ust by (simp add: ustep_def s0a t0a Let_def nm_def)
      have iu: "unify_types alg (tsubst \<rho> Ts) (tsubst \<rho> Tt) (instE \<rho> env) \<bind>
          (\<lambda>env'. uni alg ((nm, tsubst \<rho> Ts) # instb \<rho> bs) (inst \<rho> ts) (inst \<rho> tt) env') = Some r'"
        using ust' by (simp add: ustep_def s0a t0a Let_def nm_def)
      note pre0' = pre0[unfolded s0a t0a]
      have twT: "tyw ar (tyenv env) A Ts" "tyw ar (tyenv env) A Tt" using preD(3)[OF pre0'] by auto
      from preD(1,2)[OF pre0'] twT show ?thesis
      proof (cases rule: unify_types_cases)
        case (Ok env1)
        note d = AA_decomp(1)[OF pre0' Ok(2,3,5), where nm = nm]
        from unify_types_card[OF fin preD(1,2)[OF pre0'] twT Ok(1)]
        show ?thesis
        proof
          assume same: "tyenv env1 = tyenv env"
          have e1: "env1 = env" by (rule unify_types_same[OF Ok(1) same])
          have "tsubst \<rho> Ts = tsubst \<rho> Tt" using Ok(4) sol same by simp
          with iu have "uni alg (instb \<rho> ((nm, Ts) # bs)) (inst \<rho> ts) (inst \<rho> tt) (instE \<rho> env) = Some r'"
            by (simp add: unify_types_def return_def)
          from IH[OF this refl d[unfolded e1] n] obtain r where
            "unif alg ((nm, Ts) # bs) ts tt env = Some r" "tres A env r" "lock \<rho> env r r'" by blast
          with pu Ok(1) e1 show ?thesis by simp
        next
          assume lt: "card (uvarsA (tyenv env1) A) < card (uvarsA (tyenv env) A)"
          have n1: "nacyc env1" using n nacyc_same_tenv[OF Ok(2)] by simp
          from OIH[OF d n1] lt k obtain r where r: "unif alg ((nm, Ts) # bs) ts tt env1 = Some r"
            and q: "tres A env1 r" by auto
          have t1: "tres A env (Ok env1)" using n1 lt by (simp add: tres_def)
          have "lock \<rho> env r r'"
            unfolding lock_def
          proof (intro allI impI)
            fix env' assume "r = Ok env'" "tyenv env' = tyenv env"
            with q lt show "r' = Ok (instE \<rho> env')" by (auto simp: tres_def)
          qed
          with pu Ok(1) r tres_trans[OF t1 q] show ?thesis by simp
        qed
      next
        case (Err u)
        with pu show ?thesis by simp
      qed
    next
      case False
      have pu: "unif alg bs s t env = unif alg ((ns, Ts) # bs) ts (incr t0 $ Bound 0) env"
        using ust by (simp add: ustep_def s0a False)
      have "uni alg (instb \<rho> ((ns, Ts) # bs)) (inst \<rho> ts) (inst \<rho> (incr t0 $ Bound 0)) (instE \<rho> env) = Some r'"
        using ust' False by (simp add: ustep_def s0a inst_incr)
      from IH[OF this refl A1_decomp(1)[OF pre0[unfolded s0a] False] n] pu show ?thesis by simp
    qed
  next
    case nsA: False
    show ?thesis
    proof (cases "is_Abs t0")
      case True
      then obtain nt Tt tt where t0a: "t0 = pterm.Abs nt Tt tt" by (cases t0) auto
      have pu: "unif alg bs s t env = unif alg ((nt, Tt) # bs) (incr s0 $ Bound 0) tt env"
        using ust nsA by (simp add: ustep_def t0a)
      have "uni alg (instb \<rho> ((nt, Tt) # bs)) (inst \<rho> (incr s0 $ Bound 0)) (inst \<rho> tt) (instE \<rho> env) = Some r'"
        using ust' nsA by (simp add: ustep_def t0a inst_incr)
      from IH[OF this refl A2_decomp(1)[OF pre0[unfolded t0a] nsA] n] pu show ?thesis by simp
    next
      case nAt: False
      obtain hs' ss where shs: "strip_comb s0 = (hs', ss)" by force
      obtain ht' ts where sht: "strip_comb t0 = (ht', ts)" by force
      have shs': "strip_comb (inst \<rho> s0) = (inst \<rho> hs', map (inst \<rho>) ss)"
        and sht': "strip_comb (inst \<rho> t0) = (inst \<rho> ht', map (inst \<rho>) ts)"
        using strip_comb_inst[of \<rho> s0] strip_comb_inst[of \<rho> t0] shs sht by simp_all
      consider (Flex) "is_Var hs' \<or> is_Var ht'" | (Clash) "\<not> is_Var hs'" "\<not> is_Var ht'" "\<not> same_head hs' ht'"
        | (Rigid) "\<not> is_Var hs'" "\<not> is_Var ht'" "same_head hs' ht'"
        by blast
      then show ?thesis
      proof cases
        case Flex
        then have fl: "is_Var (fst (strip_comb s0)) \<or> is_Var (fst (strip_comb t0))" using shs sht by simp
        have fl': "is_Var (fst (strip_comb (inst \<rho> s0))) \<or> is_Var (fst (strip_comb (inst \<rho> t0)))"
          using fl by (simp add: strip_comb_inst)
        have pu: "unif alg bs s t env = flexstep env bs s0 t0" using ust ustep_flexstep[OF nsA nAt fl] by simp
        have iu: "flexstep (instE \<rho> env) (instb \<rho> bs) (inst \<rho> s0) (inst \<rho> t0) = Some r'"
          using ust' ustep_flexstep[OF _ _ fl'] nsA nAt by simp
        have "relJ \<rho> True (instE \<rho>) (flexstep env bs s0 t0)
            (flexstep (instE \<rho> env) (instb \<rho> bs) (inst \<rho> s0) (inst \<rho> t0))"
          using flexstep_relJ[OF pre_hyp[OF pre0 sol], of bs] tf by simp
        from relJ_exact[OF this] iu obtain r where r: "flexstep env bs s0 t0 = Some r"
          and r': "r' = instr \<rho> (instE \<rho>) r"
          by (cases "flexstep env bs s0 t0") (auto simp: instM_def)
        have "tres A env r"
          unfolding tres_def
        proof (intro allI impI conjI)
          fix env' assume ok: "r = Ok env'"
          show "tyenv env' = tyenv env \<or> card (uvarsA (tyenv env') A) < card (uvarsA (tyenv env) A)"
            using flexstep_ext[OF r[unfolded ok]] by (simp add: ext_def)
          have "unif alg (instb \<rho> bs) (inst \<rho> s) (inst \<rho> t) (instE \<rho> env) = Some (Ok (instE \<rho> env'))"
            using unif_inst_head_norm[OF pre hs ht sol] ustep_flexstep[OF _ _ fl'] nsA nAt iu r' ok by simp
          from inst_result_nacyc[OF pre g n this] show "nacyc env'" .
        qed
        moreover have "lock \<rho> env r r'" using r' by (auto simp: lock_def)
        ultimately show ?thesis using pu r by simp
      next
        case Clash
        note c = nsA nAt shs sht Clash
        have "ustep uni alg (instb \<rho> bs) (inst \<rho> s0) (inst \<rho> t0) (instE \<rho> env) =
            instM \<rho> (instE \<rho>) (ustep unif alg bs s0 t0 env)"
          by (rule ustep_clash(1)[OF c])
        with ust' obtain r where r: "ustep unif alg bs s0 t0 env = Some r"
          by (cases "ustep unif alg bs s0 t0 env") (auto simp: instM_def)
        have "\<forall>env'. r \<noteq> Ok env'" using ustep_clash(2)[OF c, where uni = unif and bs = bs and env = env] r by simp
        then obtain e where "r = Err e" by (cases r) auto
        with ust r show ?thesis by simp
      next
        case Rigid
        have IH': "\<exists>r. unif alg bs s1 t1 e1 = Some r \<and> tres A e1 r \<and> lock \<rho> e1 r r1'"
          if "uni alg (instb \<rho> bs) (inst \<rho> s1) (inst \<rho> t1) (instE \<rho> e1) = Some r1'" "tyenv e1 = tyenv env"
            "pre alg ar A bs s1 t1 e1" "nacyc e1" for s1 t1 e1 r1'
          using IH[OF that] .
        from Rigid(3) consider (C) a Ta Tb where "hs' = Const a Ta" "ht' = Const a Tb"
          | (F) a Ta Tb where "hs' = Free a Ta" "ht' = Free a Tb" | (B) i where "hs' = Bound i" "ht' = Bound i"
          by (auto simp: same_head_def)
        then show ?thesis
        proof cases
          case B
          have pu: "unif alg bs s t env = zip_eq ss ts \<bind> (\<lambda>ps. foldM (\<lambda>(s, t) e. unif alg bs s t e) ps env)"
            using ust by (simp add: ustep_def nsA nAt shs sht B Let_def)
          have iu: "zip_eq (map (inst \<rho>) ss) (map (inst \<rho>) ts) \<bind>
              (\<lambda>ps. foldM (\<lambda>(s, t) e. uni alg (instb \<rho> bs) s t e) ps (instE \<rho> env)) = Some r'"
            using ust' nsA nAt shs' sht' B by (simp add: ustep_def Let_def)
          have rig: "is_rigid (Bound i)" by (rule pre_Bound_rigid[OF pre0 shs[unfolded B(1)]])
          have "\<exists>r. zip_eq ss ts \<bind> (\<lambda>ps. foldM (\<lambda>(s, t) e. unif alg bs s t e) ps env) = Some r \<and>
              tres A env r \<and> lock \<rho> env r r'"
            by (rule rigid_lock[OF pre0 shs sht _ _ refl tstep_refl[OF preD(1)[OF pre0]] preD(2)[OF pre0]
                  _ n k _ _ IH' OIH])
              (use rig B iu in simp_all)
          with pu show ?thesis by simp
        next
          case C
          have pu: "unif alg bs s t env = unify_types alg Ta Tb env \<bind>
              (\<lambda>env'. zip_eq ss ts \<bind> (\<lambda>ps. foldM (\<lambda>(s, t) e. unif alg bs s t e) ps env'))"
            using ust by (simp add: ustep_def nsA nAt shs sht C Let_def)
          have iu: "unify_types alg (tsubst \<rho> Ta) (tsubst \<rho> Tb) (instE \<rho> env) \<bind> (\<lambda>env'.
              zip_eq (map (inst \<rho>) ss) (map (inst \<rho>) ts) \<bind>
              (\<lambda>ps. foldM (\<lambda>(s, t) e. uni alg (instb \<rho> bs) s t e) ps env')) = Some r'"
            using ust' nsA nAt shs' sht' C by (simp add: ustep_def Let_def)
          have twT: "tyw ar (tyenv env) A Ta" "tyw ar (tyenv env) A Tb"
            using preD(3)[OF pre0] tys_strip_comb[OF shs] tys_strip_comb[OF sht] C by auto
          from preD(1,2)[OF pre0] twT show ?thesis
          proof (cases rule: unify_types_cases)
            case (Ok env1)
            have st: "tstep alg ar A (\<lambda>\<rho>. inst \<rho> hs' = inst \<rho> ht') (tyenv env) (maxidx env) (tyenv env1) (maxidx env1)"
              by (rule tstep_mono[OF Ok(3)]) (simp add: C)
            have c: "env1 = env \<or> card (uvarsA (tyenv env1) A) < k"
              using unify_types_card[OF fin preD(1,2)[OF pre0] twT Ok(1)] unify_types_same[OF Ok(1)] k by auto
            have "\<exists>r. zip_eq ss ts \<bind> (\<lambda>ps. foldM (\<lambda>(s, t) e. unif alg bs s t e) ps env1) = Some r \<and>
                tres A env r \<and> lock \<rho> env r r'"
            proof (rule rigid_lock[OF pre0 shs sht _ _ Ok(2) st Ok(5) _ n k c _ IH' OIH])
              show "is_rigid hs'" "is_rigid ht'" using C by (simp_all add: is_rigid_def)
              show "inst \<rho>' hs' = inst \<rho>' ht'" if "gsol alg ar (tyenv env1) \<rho>'" for \<rho>'
                using Ok(4) that by (simp add: gsol_def C)
              assume e1: "env1 = env"
              have "tsubst \<rho> Ta = tsubst \<rho> Tb" using Ok(4) sol e1 by simp
              with iu show "zip_eq (map (inst \<rho>) ss) (map (inst \<rho>) ts) \<bind>
                  (\<lambda>ps. foldM (\<lambda>(s, t) e. uni alg (instb \<rho> bs) s t e) ps (instE \<rho> env)) = Some r'"
                by (simp add: unify_types_def return_def)
            qed
            with pu Ok(1) show ?thesis by simp
          next
            case (Err u)
            with pu show ?thesis by simp
          qed
        next
          case F
          have pu: "unif alg bs s t env = unify_types alg Ta Tb env \<bind>
              (\<lambda>env'. zip_eq ss ts \<bind> (\<lambda>ps. foldM (\<lambda>(s, t) e. unif alg bs s t e) ps env'))"
            using ust by (simp add: ustep_def nsA nAt shs sht F Let_def)
          have iu: "unify_types alg (tsubst \<rho> Ta) (tsubst \<rho> Tb) (instE \<rho> env) \<bind> (\<lambda>env'.
              zip_eq (map (inst \<rho>) ss) (map (inst \<rho>) ts) \<bind>
              (\<lambda>ps. foldM (\<lambda>(s, t) e. uni alg (instb \<rho> bs) s t e) ps env')) = Some r'"
            using ust' nsA nAt shs' sht' F by (simp add: ustep_def Let_def)
          have twT: "tyw ar (tyenv env) A Ta" "tyw ar (tyenv env) A Tb"
            using preD(3)[OF pre0] tys_strip_comb[OF shs] tys_strip_comb[OF sht] F by auto
          from preD(1,2)[OF pre0] twT show ?thesis
          proof (cases rule: unify_types_cases)
            case (Ok env1)
            have st: "tstep alg ar A (\<lambda>\<rho>. inst \<rho> hs' = inst \<rho> ht') (tyenv env) (maxidx env) (tyenv env1) (maxidx env1)"
              by (rule tstep_mono[OF Ok(3)]) (simp add: F)
            have c: "env1 = env \<or> card (uvarsA (tyenv env1) A) < k"
              using unify_types_card[OF fin preD(1,2)[OF pre0] twT Ok(1)] unify_types_same[OF Ok(1)] k by auto
            have "\<exists>r. zip_eq ss ts \<bind> (\<lambda>ps. foldM (\<lambda>(s, t) e. unif alg bs s t e) ps env1) = Some r \<and>
                tres A env r \<and> lock \<rho> env r r'"
            proof (rule rigid_lock[OF pre0 shs sht _ _ Ok(2) st Ok(5) _ n k c _ IH' OIH])
              show "is_rigid hs'" "is_rigid ht'" using F by (simp_all add: is_rigid_def)
              show "inst \<rho>' hs' = inst \<rho>' ht'" if "gsol alg ar (tyenv env1) \<rho>'" for \<rho>'
                using Ok(4) that by (simp add: gsol_def F)
              assume e1: "env1 = env"
              have "tsubst \<rho> Ta = tsubst \<rho> Tb" using Ok(4) sol e1 by simp
              with iu show "zip_eq (map (inst \<rho>) ss) (map (inst \<rho>) ts) \<bind>
                  (\<lambda>ps. foldM (\<lambda>(s, t) e. uni alg (instb \<rho> bs) s t e) ps (instE \<rho> env)) = Some r'"
                by (simp add: unify_types_def return_def)
            qed
            with pu Ok(1) show ?thesis by simp
          next
            case (Err u)
            with pu show ?thesis by simp
          qed
        qed
      qed
    qed
  qed
qed


subsection \<open>Termination\<close>

theorem unif_terminates:
  assumes fin: "finite A" and pre: "pre alg ar A bs s t env" and n: "nacyc env"
  shows "\<exists>r. unif alg bs s t env = Some r \<and> tres A env r"
proof -
  have "\<forall>bs s t env. card (uvarsA (tyenv env) A) = k \<longrightarrow> pre alg ar A bs s t env \<longrightarrow> nacyc env \<longrightarrow>
      (\<exists>r. unif alg bs s t env = Some r \<and> tres A env r)" for k
  proof (induction k rule: less_induct)
    case (less k)
    have OIH: "\<exists>r. unif alg bs s t env = Some r \<and> tres A env r"
      if "pre alg ar A bs s t env" "nacyc env" "card (uvarsA (tyenv env) A) < k" for bs s t env
      using less.IH[OF that(3)] that(1,2) by blast
    show ?case
    proof (intro allI impI)
      fix bs s t env assume k: "card (uvarsA (tyenv env) A) = k" and pre: "pre alg ar A bs s t env"
        and n: "nacyc env"
      obtain \<rho> where g: "gsol alg ar (tyenv env) \<rho>" and tf: "tfree_on \<rho> (tyenv env)"
        by (rule faithful_tfree[OF preD(1,2)[OF pre]])
      obtain W U where h: "env_inv ar W (instE \<rho> env)" "binders_ok ar (instb \<rho> bs)"
        "wf_term ar (length (instb \<rho> bs)) (inst \<rho> s)" "wf_term ar (length (instb \<rho> bs)) (inst \<rho> t)"
        "has_type W (map snd (instb \<rho> bs)) (inst \<rho> s) U" "has_type W (map snd (instb \<rho> bs)) (inst \<rho> t) U"
        "below (maxidx (instE \<rho> env)) (inst \<rho> s)" "below (maxidx (instE \<rho> env)) (inst \<rho> t)"
        by (rule inst_env_inv[OF pre g n])
      from unif_term[OF refl h, where alg = alg]
      obtain r' where u: "unif alg (instb \<rho> bs) (inst \<rho> s) (inst \<rho> t) (instE \<rho> env) = Some r'" by blast
      from lockstep[OF fin _ u refl refl refl refl refl g tf k pre n] OIH
      show "\<exists>r. unif alg bs s t env = Some r \<and> tres A env r" by blast
    qed
  qed
  with pre n show ?thesis by blast
qed

end

end

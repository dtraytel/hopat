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

end

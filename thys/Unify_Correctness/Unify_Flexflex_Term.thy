section \<open>Termination of the Treatment of Flex-Flex Pairs\<close>

theory Unify_Flexflex_Term
  imports Unify_Simpl_Term Unify_Flexflex_Sound
begin

context pure_sig
begin

subsection \<open>Unification of types that are equal in the most general solution\<close>

lemma tnorm_nonType: "tacyc \<theta> \<Longrightarrow> \<not> tbound \<theta> T \<Longrightarrow> \<not> (\<exists>a Ts. T = Type a Ts) \<Longrightarrow> tnorm \<theta> T = T"
  by (cases T) (auto simp: tnorm_TVar split: option.splits)

lemma unify_aux_same:
  assumes ac: "tacyc \<theta>" and tc: "tcons_env \<theta>"
  shows "tcons \<theta> T \<Longrightarrow> tcons \<theta> U \<Longrightarrow> tnorm \<theta> T = tnorm \<theta> U \<Longrightarrow> unify_aux alg' T U (\<theta>, n) = return (\<theta>, n)"
proof (induction "size (tnorm \<theta> T)" arbitrary: T U rule: less_induct)
  case less
  obtain T' where T': "devar \<theta> T = return T'" "tnorm \<theta> T' = tnorm \<theta> T" "tcons \<theta> T'" "\<not> tbound \<theta> T'"
    using devar_ok[OF ac tc less.prems(1)] by blast
  obtain U' where U': "devar \<theta> U = return U'" "tnorm \<theta> U' = tnorm \<theta> U" "tcons \<theta> U'" "\<not> tbound \<theta> U'"
    using devar_ok[OF ac tc less.prems(2)] by blast
  have eq: "tnorm \<theta> T' = tnorm \<theta> U'" using T'(2) U'(2) less.prems(3) by simp
  have unf: "unify_aux alg' T U (\<theta>, n) = (case (T', U') of
        (TVar v S1, TVar w S2) \<Rightarrow>
          if v = w then (if S1 = S2 then return (\<theta>, n) else tvar_clash v S1 S2)
          else if sort_le alg' S1 S2 then do {tye' \<leftarrow> update_new (w, (S2, T')) \<theta>; return (tye', n)}
          else if sort_le alg' S2 S1 then do {tye' \<leftarrow> update_new (v, (S1, U')) \<theta>; return (tye', n)}
          else do {
            let (S, cnt') = gen_tyvar (inter_sort alg' S1 S2) n;
            tye' \<leftarrow> update_new (w, (S2, S)) \<theta>;
            tye'' \<leftarrow> update_new (v, (S1, S)) tye';
            return (tye'', cnt')}
      | (TVar v S, _) \<Rightarrow> do {
          b \<leftarrow> type_occurs v \<theta> U';
          if b then raise TUnify else do {tye' \<leftarrow> update_new (v, (S, U')) \<theta>; meet alg' U' S (tye', n)}}
      | (_, TVar v S) \<Rightarrow> do {
          b \<leftarrow> type_occurs v \<theta> T';
          if b then raise TUnify else do {tye' \<leftarrow> update_new (v, (S, T')) \<theta>; meet alg' T' S (tye', n)}}
      | (Type a Ts, Type b Us) \<Rightarrow>
          if a \<noteq> b then raise TUnify
          else foldM (\<lambda>(T, U) st. unify_aux alg' T U st) (zip Ts Us) (\<theta>, n)
      | _ \<Rightarrow> if T' = U' then return (\<theta>, n) else raise TUnify)"
    by (subst unify_aux.simps) (simp add: T'(1) U'(1))
  show ?case
  proof (cases "\<exists>a Ts. T' = Type a Ts")
    case False
    have tT: "tnorm \<theta> T' = T'" by (rule tnorm_nonType[OF ac T'(4) False])
    have "\<not> (\<exists>a Us. U' = Type a Us)"
    proof
      assume "\<exists>a Us. U' = Type a Us"
      then obtain a Us where "U' = Type a Us" by blast
      with eq tT False show False by auto
    qed
    then have "tnorm \<theta> U' = U'" by (rule tnorm_nonType[OF ac U'(4)])
    with tT eq have "U' = T'" by simp
    with unf False show ?thesis by (cases T') auto
  next
    case True
    then obtain a Ts where Ta: "T' = Type a Ts" by blast
    have "\<exists>Us. U' = Type a Us"
    proof (cases "\<exists>b Us. U' = Type b Us")
      case True
      then obtain b Us where "U' = Type b Us" by blast
      with eq Ta show ?thesis by auto
    next
      case False
      then have "tnorm \<theta> U' = U'" by (rule tnorm_nonType[OF ac U'(4)])
      with eq Ta False show ?thesis by auto
    qed
    then obtain Us where Ua: "U' = Type a Us" by blast
    from eq Ta Ua have mm: "map (tnorm \<theta>) Ts = map (tnorm \<theta>) Us" by simp
    then have len: "length Ts = length Us" by (metis length_map)
    have sz: "size (tnorm \<theta> V) < size (tnorm \<theta> T)" if "V \<in> set Ts" for V
    proof -
      have "size (tnorm \<theta> V) < size (Type a (map (tnorm \<theta>) Ts))"
        using that by (induction Ts) auto
      moreover have "tnorm \<theta> T = Type a (map (tnorm \<theta>) Ts)" using T'(2) Ta by simp
      ultimately show ?thesis by simp
    qed
    have "foldM (\<lambda>(T, U) st. unify_aux alg' T U st) (zip Ts' Us') (\<theta>, n) = return (\<theta>, n)"
      if "set Ts' \<subseteq> set Ts" "set Us' \<subseteq> set Us" "map (tnorm \<theta>) Ts' = map (tnorm \<theta>) Us'" for Ts' Us'
      using that
    proof (induction Ts' arbitrary: Us')
      case (Cons V Vs)
      then obtain W Ws where Us': "Us' = W # Ws" by (cases Us') auto
      have tV: "tcons \<theta> V" using T'(3) Ta Cons.prems(1) by auto
      have tW: "tcons \<theta> W" using U'(3) Ua Cons.prems(2) Us' by auto
      have "unify_aux alg' V W (\<theta>, n) = return (\<theta>, n)"
        using less.hyps[OF sz tV tW] Cons.prems Us' by auto
      with Cons.IH[of Ws] Cons.prems Us' show ?case by simp
    qed simp
    from this[OF order_refl order_refl mm] unf Ta Ua show ?thesis by simp
  qed
qed

end

end

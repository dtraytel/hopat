section \<open>Soundness of the Search\<close>

theory Unify_Pull
  imports Unify_Flexflex
begin

context csig
begin

text \<open>
  Pulling a sequence that satisfies the invariant \<^const>\<open>sinv\<close> of its goal produces an
  element that satisfies the goal and a rest that satisfies the invariant again. For the
  sequences of \<open>hounifiers\<close>, the elements are unifiers.
\<close>


subsection \<open>Pulling sequences\<close>

lemma not_okW_pull_fail[simp]: "\<not> okW pull_fail y"
  by (simp add: pull_fail_def)

lemma okW_CANTUNIFY_handler':
  "okW (case e of CANTUNIFY \<Rightarrow> m | _ \<Rightarrow> raiseW e) y \<Longrightarrow> okW m y"
  by (cases e) auto

text \<open>Decomposing the successful evaluation of the closures.\<close>

lemma okW_bind_opt:
  assumes "okW (bindW m (\<lambda>r. case r of None \<Rightarrow> A | Some (y, q) \<Rightarrow> B y q)) z"
  shows "(okW m None \<and> okW A z) \<or> (\<exists>y q. okW m (Some (y, q)) \<and> okW (B y q) z)"
proof -
  from assms obtain r where r: "okW m r" "okW (case r of None \<Rightarrow> A | Some (y, q) \<Rightarrow> B y q) z"
    unfolding okW_bindW by blast
  show ?thesis
  proof (cases r)
    case None
    with r show ?thesis by simp
  next
    case (Some p)
    with r show ?thesis by (cases p) auto
  qed
qed

lemma okW_map_C:
  assumes "okW (bindW m (\<lambda>r. case r of None \<Rightarrow> returnW None
    | Some (y, q) \<Rightarrow> (case y of El_C a b c \<Rightarrow> f a b c q | _ \<Rightarrow> pull_fail))) (Some z)"
  shows "\<exists>a b c q. okW m (Some (El_C a b c, q)) \<and> okW (f a b c q) (Some z)"
proof -
  from okW_bind_opt[OF assms] obtain y q where "okW m (Some (y, q))"
    "okW (case y of El_C a b c \<Rightarrow> f a b c q | _ \<Rightarrow> pull_fail) (Some z)" by auto
  then show ?thesis by (cases y) auto
qed

lemma okW_map_D:
  assumes "okW (bindW m (\<lambda>r. case r of None \<Rightarrow> returnW None
    | Some (y, q) \<Rightarrow> (case y of El_D a b c \<Rightarrow> f a b c q | _ \<Rightarrow> pull_fail))) (Some z)"
  shows "\<exists>a b c q. okW m (Some (El_D a b c, q)) \<and> okW (f a b c q) (Some z)"
proof -
  from okW_bind_opt[OF assms] obtain y q where "okW m (Some (y, q))"
    "okW (case y of El_D a b c \<Rightarrow> f a b c q | _ \<Rightarrow> pull_fail) (Some z)" by auto
  then show ?thesis by (cases y) auto
qed

lemma okW_bind_E:
  assumes "okW (bindW m (\<lambda>r. case r of None \<Rightarrow> A
    | Some (y, q) \<Rightarrow> (case y of El_E a b \<Rightarrow> f a b q | _ \<Rightarrow> pull_fail))) z"
  shows "(okW m None \<and> okW A z) \<or> (\<exists>a b q. okW m (Some (El_E a b, q)) \<and> okW (f a b q) z)"
proof -
  from okW_bind_opt[OF assms] consider (n) "okW m None \<and> okW A z"
    | (s) y q where "okW m (Some (y, q))" "okW (case y of El_E a b \<Rightarrow> f a b q | _ \<Rightarrow> pull_fail) z"
    by blast
  then show ?thesis
  proof cases
    case (s y q)
    then show ?thesis by (cases y) auto
  qed simp
qed

lemma okW_whenW_then: "okW (bindW (whenW b (emit e)) (\<lambda>_. M)) z \<Longrightarrow> okW M z"
  by (auto simp: okW_whenW split: if_splits)

lemma okW_emit_then: "okW (bindW (emit e) (\<lambda>_. M)) z \<Longrightarrow> okW M z"
  by auto

lemma okW_handle_CANTUNIFY:
  assumes "okW (handleW M (\<lambda>e. case e of CANTUNIFY \<Rightarrow> N | _ \<Rightarrow> raiseW e)) z"
  shows "okW M z \<or> okW N z"
proof -
  from assms have "okW M z \<or> (\<exists>evs e. M = Some (evs, UErr e) \<and>
      okW (case e of CANTUNIFY \<Rightarrow> N | _ \<Rightarrow> raiseW e) z)"
    by (simp only: okW_handleW)
  then show ?thesis
  proof (elim disjE)
    assume "\<exists>evs e. M = Some (evs, UErr e) \<and> okW (case e of CANTUNIFY \<Rightarrow> N | _ \<Rightarrow> raiseW e) z"
    then obtain e where "okW (case e of CANTUNIFY \<Rightarrow> N | _ \<Rightarrow> raiseW e) z" by metis
    from okW_CANTUNIFY_handler'[OF this] show ?thesis ..
  qed (rule disjI1)
qed

lemma okW_bind_triple:
  assumes "okW (bindW m (\<lambda>(a, b, c). f a b c)) z"
  shows "\<exists>a b c. okW m (a, b, c) \<and> okW (f a b c) z"
proof -
  from assms obtain st where "okW m st" "okW ((\<lambda>(a, b, c). f a b c) st) z" unfolding okW_bindW by blast
  then show ?thesis by (cases st) auto
qed

lemma addunify_cases:
  assumes "okW (handleW
    (bindW (whenW b1 (emit e1)) (\<lambda>_. bindW (SIMPL alg env dps) (\<lambda>(env', ffs, frs).
      case frs of
        [] \<Rightarrow> bindW (foldrW (add_ffpair alg) ffs (env', [])) (\<lambda>r. returnW (Some (El_R (fst r) (snd r), reseq)))
      | dp # frigid' \<Rightarrow>
          if b2 then bindW (emit e2) (\<lambda>_. Q)
          else bindW (whenW b3 (emit (e3 env' frs ffs)))
            (\<lambda>_. bindW (MATCH cfg env' dp (frigid' @ ffs)) R))))
    (\<lambda>e. case e of CANTUNIFY \<Rightarrow> bindW (whenW b4 (emit e4)) (\<lambda>_. Q) | _ \<Rightarrow> raiseW e)) z"
  shows "okW Q z \<or>
    (\<exists>env' ffs env'' tps. okW (SIMPL alg env dps) (env', ffs, []) \<and>
      okW (foldrW (add_ffpair alg) ffs (env', [])) (env'', tps) \<and> z = Some (El_R env'' tps, reseq)) \<or>
    (\<exists>env' ffs dp frigid' ms. okW (SIMPL alg env dps) (env', ffs, dp # frigid') \<and>
      okW (MATCH cfg env' dp (frigid' @ ffs)) ms \<and> okW (R ms) z)"
proof -
  from okW_handle_CANTUNIFY[OF assms] show ?thesis
  proof (elim disjE)
    assume "okW (bindW (whenW b1 (emit e1)) (\<lambda>_. bindW (SIMPL alg env dps) (\<lambda>(env', ffs, frs).
      case frs of
        [] \<Rightarrow> bindW (foldrW (add_ffpair alg) ffs (env', [])) (\<lambda>r. returnW (Some (El_R (fst r) (snd r), reseq)))
      | dp # frigid' \<Rightarrow>
          if b2 then bindW (emit e2) (\<lambda>_. Q)
          else bindW (whenW b3 (emit (e3 env' frs ffs)))
            (\<lambda>_. bindW (MATCH cfg env' dp (frigid' @ ffs)) R)))) z"
    from okW_bind_triple[OF okW_whenW_then[OF this]] obtain env' ffs frs where
      S: "okW (SIMPL alg env dps) (env', ffs, frs)"
      and c: "okW (case frs of
        [] \<Rightarrow> bindW (foldrW (add_ffpair alg) ffs (env', [])) (\<lambda>r. returnW (Some (El_R (fst r) (snd r), reseq)))
      | dp # frigid' \<Rightarrow>
          if b2 then bindW (emit e2) (\<lambda>_. Q)
          else bindW (whenW b3 (emit (e3 env' frs ffs)))
            (\<lambda>_. bindW (MATCH cfg env' dp (frigid' @ ffs)) R)) z"
      by blast
    show ?thesis
    proof (cases frs)
      case Nil
      with c obtain r where r: "okW (foldrW (add_ffpair alg) ffs (env', [])) r"
        "z = Some (El_R (fst r) (snd r), reseq)" by auto
      obtain env'' tps where "r = (env'', tps)" by (cases r)
      with r have "okW (foldrW (add_ffpair alg) ffs (env', [])) (env'', tps)"
        "z = Some (El_R env'' tps, reseq)" by simp_all
      with S Nil show ?thesis by blast
    next
      case (Cons dp frigid')
      show ?thesis
      proof (cases b2)
        case True
        with c Cons have "okW Q z" by (auto dest: okW_emit_then)
        then show ?thesis by blast
      next
        case False
        with c Cons have "okW (bindW (whenW b3 (emit (e3 env' frs ffs)))
            (\<lambda>_. bindW (MATCH cfg env' dp (frigid' @ ffs)) R)) z" by simp
        from okW_whenW_then[OF this] obtain ms where "okW (MATCH cfg env' dp (frigid' @ ffs)) ms"
          "okW (R ms) z" unfolding okW_bindW by blast
        with S Cons show ?thesis by blast
      qed
    qed
  next
    assume "okW (bindW (whenW b4 (emit e4)) (\<lambda>_. Q)) z"
    from okW_whenW_then[OF this] show ?thesis by blast
  qed
qed

end

end

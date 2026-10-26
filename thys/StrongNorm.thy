(*  Title:      HOL/Proofs/Lambda/StrongNorm.thy
    Author:     Stefan Berghofer
    Copyright   2000 TU Muenchen
*)

section \<open>Strong normalization for simply-typed lambda calculus\<close>

theory StrongNorm imports LambdaType InductTermi begin

text \<open>
Formalization by Stefan Berghofer. Partly based on a paper proof by
Felix Joachimski and Ralph Matthes @{cite "Matthes-Joachimski-AML"}.
\<close>


subsection \<open>Properties of \<open>IT\<close>\<close>

lemma lift_IT [intro!]: "IT t \<Longrightarrow> IT (lift t i)"
  apply (induct arbitrary: i set: IT)
    apply (simp (no_asm))
     apply (rule conjI)
      apply fastforce
     apply fastforce
    apply fastforce
   apply auto[1]
  by auto

lemma lifts_IT: "listsp IT ts \<Longrightarrow> listsp IT (map (\<lambda>t. lift t 0) ts)"
  by (induct ts) auto

lemma subst_BVar_IT: "IT r \<Longrightarrow> IT (r[BVar i/j])"
  apply (induct arbitrary: i j set: IT)
    txt \<open>Case \<^term>\<open>BVar\<close>:\<close>
       apply (simp (no_asm) add: subst_BVar)
    apply
    ((rule conjI impI)+,
      rule IT.BVar,
      erule listsp.induct,
      simp (no_asm),
      simp (no_asm),
      rule listsp.Cons,
      fast,
      assumption)+
    apply fastforce
   txt \<open>Case \<^term>\<open>Lambda\<close>:\<close>
   apply atomize
   apply simp
   apply (rule IT.Lambda)
   apply fast
  txt \<open>Case \<^term>\<open>Beta\<close>:\<close>
  apply atomize
  apply (simp (no_asm_use) add: subst_subst [symmetric])
  apply (rule IT.Beta)
   apply auto
  done

lemma subst_Var_IT: "IT r \<Longrightarrow> IT (r[Var i/j])"
  apply (induct arbitrary: i j set: IT)
    txt \<open>Case \<^term>\<open>Var\<close>:\<close>
       apply (simp (no_asm) add: subst_BVar)
    apply
    ((rule conjI impI)+,
      rule IT.Var,
      erule listsp.induct,
      simp (no_asm),
      simp (no_asm),
      rule listsp.Cons,
      fast,
      assumption)+
    apply fastforce
    apply fastforce
   txt \<open>Case \<^term>\<open>Lambda\<close>:\<close>
   apply atomize
   apply simp
   apply (rule IT.Lambda)
   apply fast
  txt \<open>Case \<^term>\<open>Beta\<close>:\<close>
  apply atomize
  apply (simp (no_asm_use) add: subst_subst [symmetric])
  apply (rule IT.Beta)
   apply auto
  done

lemma BVar_IT: "IT (BVar n)"
  apply (subgoal_tac "IT (BVar n \<degree>\<degree> [])")
   apply simp
  apply (rule IT.BVar)
  apply (rule listsp.Nil)
  done

lemma Var_IT: "IT (Var n)"
  apply (subgoal_tac "IT (Var n \<degree>\<degree> [])")
   apply simp
  apply (rule IT.Var)
  apply (rule listsp.Nil)
  done

lemma app_BVar_IT: "IT t \<Longrightarrow> IT (t \<degree> BVar i)"
  apply (induct set: IT)
    apply (subst app_last)
    apply (rule IT.BVar)
    apply simp
    apply (rule listsp.Cons)
     apply (rule BVar_IT)
     apply (rule listsp.Nil)
  apply (subst app_last)
    apply (rule IT.Var)
    apply simp
    apply (rule listsp.Cons)
     apply (rule BVar_IT)
     apply (rule listsp.Nil)
   apply (rule IT.Beta [where ?ss = "[]", unfolded foldl_Nil [THEN eq_reflection]])
    apply (erule subst_BVar_IT)
   apply (rule BVar_IT)
  apply (subst app_last)
  apply (rule IT.Beta)
   apply (subst app_last [symmetric])
   apply assumption
  apply assumption
  done

lemma app_Var_IT: "IT t \<Longrightarrow> IT (t \<degree> Var i)"
  apply (induct set: IT)
     apply (subst app_last)
    apply (rule IT.BVar)
    apply simp
    apply (rule listsp.Cons)
     apply (rule Var_IT)
     apply (rule listsp.Nil)
  apply (subst app_last)
    apply (rule IT.Var)
    apply simp
    apply (rule listsp.Cons)
     apply (rule Var_IT)
     apply (rule listsp.Nil)
   apply (rule IT.Beta [where ?ss = "[]", unfolded foldl_Nil [THEN eq_reflection]])
    apply (erule subst_Var_IT)
   apply (rule Var_IT)
  apply (subst app_last)
  apply (rule IT.Beta)
   apply (subst app_last [symmetric])
   apply assumption
  apply assumption
  done


subsection \<open>Well-typed substitution preserves termination\<close>

lemma subst_type_IT:
  "\<And>t e' e'' T u i. IT t \<Longrightarrow> (e'\<langle>i:U\<rangle>, e'') \<turnstile> t : T \<Longrightarrow>
    IT u \<Longrightarrow> (e', e'') \<turnstile> u : U \<Longrightarrow> IT (t[u/i])"
  (is "PROP ?P U" is "\<And>t e' e'' T u i. _ \<Longrightarrow> PROP ?Q t e' e'' T u i U")
proof (induct U)
  fix T t
  assume MI1: "\<And>T1 T2. T = T1 \<Rightarrow> T2 \<Longrightarrow> PROP ?P T1"
  assume MI2: "\<And>T1 T2. T = T1 \<Rightarrow> T2 \<Longrightarrow> PROP ?P T2"
  assume "IT t"
  thus "\<And>e' e'' T' u i. PROP ?Q t e' e'' T' u i T"
  proof induct
    fix e' e'' T' u i
    assume uIT: "IT u"
    assume uT: "(e', e'') \<turnstile> u : T"
    {
      case (BVar rs n e1 T'1 u1 i1)
      assume nT: "(e'\<langle>i:T\<rangle>, e'') \<turnstile> BVar n \<degree>\<degree> rs : T'"
      let ?ty = "\<lambda>t. \<exists>T'. (e'\<langle>i:T\<rangle>, e'') \<turnstile> t : T'"
      let ?R = "\<lambda>t. \<forall>e' e'' T' u i.
        (e'\<langle>i:T\<rangle>, e'') \<turnstile> t : T' \<longrightarrow> IT u \<longrightarrow> (e', e'') \<turnstile> u : T \<longrightarrow> IT (t[u/i])"
      show "IT ((BVar n \<degree>\<degree> rs)[u/i])"
      proof (cases "n = i")
        case True
        show ?thesis
        proof (cases rs)
          case Nil
          with uIT True show ?thesis by simp
        next
          case (Cons a as)
          with nT have "(e'\<langle>i:T\<rangle>, e'') \<turnstile> BVar n \<degree> a \<degree>\<degree> as : T'" by simp
          then obtain Ts
              where headT: "(e'\<langle>i:T\<rangle>, e'') \<turnstile> BVar n \<degree> a : Ts \<Rrightarrow> T'"
              and argsT: "(e'\<langle>i:T\<rangle>, e'') \<tturnstile> as : Ts"
            by (rule list_app_typeE)
          from headT obtain T''
              where varT: "(e'\<langle>i:T\<rangle>, e'') \<turnstile> BVar n : T'' \<Rightarrow> Ts \<Rrightarrow> T'"
              and argT: "(e'\<langle>i:T\<rangle>, e'') \<turnstile> a : T''"
            by cases simp_all
          from varT True have T: "T = T'' \<Rightarrow> Ts \<Rrightarrow> T'"
            by cases auto
          with uT have uT': "(e', e'') \<turnstile> u : T'' \<Rightarrow> Ts \<Rrightarrow> T'" by simp
          from T have "IT ((BVar 0 \<degree>\<degree> map (\<lambda>t. lift t 0)
            (map (\<lambda>t. t[u/i]) as))[(u \<degree> a[u/i])/0])"
          proof (rule MI2)
            from T have "IT ((lift u 0 \<degree> BVar 0)[a[u/i]/0])"
            proof (rule MI1)
              have "IT (lift u 0)" by (rule lift_IT [OF uIT])
              thus "IT (lift u 0 \<degree> BVar 0)" by (rule app_BVar_IT)
              show "(e'\<langle>0:T''\<rangle>, e'') \<turnstile> lift u 0 \<degree> BVar 0 : Ts \<Rrightarrow> T'"
              proof (rule typing.App)
                show "(e'\<langle>0:T''\<rangle>, e'') \<turnstile> lift u 0 : T'' \<Rightarrow> Ts \<Rrightarrow> T'"
                  by (rule lift_type) (rule uT')
                show "(e'\<langle>0:T''\<rangle>, e'') \<turnstile> BVar 0 : T''"
                  by (rule typing.BVar) simp
              qed
              from BVar have "?R a" by cases (simp_all add: Cons)
              with argT uIT uT show "IT (a[u/i])" by blast
              from argT uT show "(e', e'') \<turnstile> a[u/i] : T''"
                by (rule subst_lemma) simp
            qed
            thus "IT (u \<degree> a[u/i])" by simp
            from BVar have "listsp ?R as"
              by cases (simp_all add: Cons)
            moreover from argsT have "listsp ?ty as"
              by (rule lists_typings)
            ultimately have "listsp (\<lambda>t. ?R t \<and> ?ty t) as"
              by simp
            hence "listsp IT (map (\<lambda>t. lift t 0) (map (\<lambda>t. t[u/i]) as))"
              (is "listsp IT (?ls as)")
            proof induct
              case Nil
              show ?case by fastforce
            next
              case (Cons b bs)
              hence I: "?R b" by simp
              from Cons obtain U where "(e'\<langle>i:T\<rangle>, e'') \<turnstile> b : U" by fast
              with uT uIT I have "IT (b[u/i])" by blast
              hence "IT (lift (b[u/i]) 0)" by (rule lift_IT)
              hence "listsp IT (lift (b[u/i]) 0 # ?ls bs)"
                by (rule listsp.Cons) (rule Cons)
              thus ?case by simp
            qed
            thus "IT (BVar 0 \<degree>\<degree> ?ls as)" by (rule IT.BVar)
            have "(e'\<langle>0:Ts \<Rrightarrow> T'\<rangle>, e'') \<turnstile> BVar 0 : Ts \<Rrightarrow> T'"
              by (rule typing.BVar) simp
            moreover from uT argsT have "(e', e'') \<tturnstile> map (\<lambda>t. t[u/i]) as : Ts"
              by (rule substs_lemma)
            hence "(e'\<langle>0:Ts \<Rrightarrow> T'\<rangle>, e'') \<tturnstile> ?ls as : Ts"
              by (rule lift_types)
            ultimately show "(e'\<langle>0:Ts \<Rrightarrow> T'\<rangle>, e'') \<turnstile> BVar 0 \<degree>\<degree> ?ls as : T'"
              by (rule list_app_typeI)
            from argT uT have "(e', e'') \<turnstile> a[u/i] : T''"
              by (rule subst_lemma) (rule refl)
            with uT' show "(e', e'') \<turnstile> u \<degree> a[u/i] : Ts \<Rrightarrow> T'"
              by (rule typing.App)
          qed
          with Cons True show ?thesis
            by (simp add: comp_def)
        qed
      next
        case False
        from BVar have "listsp ?R rs" by simp
        moreover from nT obtain Ts where "(e'\<langle>i:T\<rangle>, e'') \<tturnstile> rs : Ts"
          by (rule list_app_typeE)
        hence "listsp ?ty rs" by (rule lists_typings)
        ultimately have "listsp (\<lambda>t. ?R t \<and> ?ty t) rs"
          by simp
        hence "listsp IT (map (\<lambda>x. x[u/i]) rs)"
        proof induct
          case Nil
          show ?case by fastforce
        next
          case (Cons a as)
          hence I: "?R a" by simp
          from Cons obtain U where "(e'\<langle>i:T\<rangle>, e'') \<turnstile> a : U" by fast
          with uT uIT I have "IT (a[u/i])" by blast
          hence "listsp IT (a[u/i] # map (\<lambda>t. t[u/i]) as)"
            by (rule listsp.Cons) (rule Cons)
          thus ?case by simp
        qed
        with False show ?thesis by (auto simp add: subst_BVar)
      qed
    next
      case (Var rs n e1 T'1 u1 i1)
      assume nT: "(e'\<langle>i:T\<rangle>, e'') \<turnstile> Var n \<degree>\<degree> rs : T'"
      let ?ty = "\<lambda>t. \<exists>T'. (e'\<langle>i:T\<rangle>, e'') \<turnstile> t : T'"
      let ?R = "\<lambda>t. \<forall>e' e'' T' u i.
        (e'\<langle>i:T\<rangle>, e'') \<turnstile> t : T' \<longrightarrow> IT u \<longrightarrow> (e', e'') \<turnstile> u : T \<longrightarrow> IT (t[u/i])"
      show "IT ((Var n \<degree>\<degree> rs)[u/i])" proof -
        from Var have "listsp ?R rs" by simp
        moreover from nT obtain Ts where "(e'\<langle>i:T\<rangle>, e'') \<tturnstile> rs : Ts"
          by (rule list_app_typeE)
        hence "listsp ?ty rs" by (rule lists_typings)
        ultimately have "listsp (\<lambda>t. ?R t \<and> ?ty t) rs"
          by simp
        hence "listsp IT (map (\<lambda>x. x[u/i]) rs)"
        proof induct
          case Nil
          show ?case by fastforce
        next
          case (Cons a as)
          hence I: "?R a" by simp
          from Cons obtain U where "(e'\<langle>i:T\<rangle>, e'') \<turnstile> a : U" by fast
          with uT uIT I have "IT (a[u/i])" by blast
          hence "listsp IT (a[u/i] # map (\<lambda>t. t[u/i]) as)"
            by (rule listsp.Cons) (rule Cons)
          thus ?case by simp
        qed
        then show ?thesis by auto
      qed
    next
      case (Lambda r e1 T'1 u1 i1)
      assume "(e'\<langle>i:T\<rangle>, e'') \<turnstile> Abs r : T'"
        and "\<And>e' e'' T' u i. PROP ?Q r e' e'' T' u i T"
      with uIT uT show "IT (Abs r[u/i])"
        by fastforce
    next
      case (Beta r a as e1 T'1 u1 i1)
      assume T: "(e'\<langle>i:T\<rangle>, e'') \<turnstile> Abs r \<degree> a \<degree>\<degree> as : T'"
      assume SI1: "\<And>e' e'' T' u i. PROP ?Q (r[a/0] \<degree>\<degree> as) e' e'' T' u i T"
      assume SI2: "\<And>e' e'' T' u i. PROP ?Q a e' e'' T' u i T"
      have "IT (Abs (r[lift u 0/Suc i]) \<degree> a[u/i] \<degree>\<degree> map (\<lambda>t. t[u/i]) as)"
      proof (rule IT.Beta)
        have "Abs r \<degree> a \<degree>\<degree> as \<rightarrow>\<^sub>\<beta> r[a/0] \<degree>\<degree> as"
          by (rule apps_preserves_beta) (rule beta.beta)
        with T have "(e'\<langle>i:T\<rangle>, e'') \<turnstile> r[a/0] \<degree>\<degree> as : T'"
          by (rule subject_reduction)
        hence "IT ((r[a/0] \<degree>\<degree> as)[u/i])"
          using uIT uT by (rule SI1)
        thus "IT (r[lift u 0/Suc i][a[u/i]/0] \<degree>\<degree> map (\<lambda>t. t[u/i]) as)"
          by (simp del: subst_map add: subst_subst subst_map [symmetric])
        from T obtain U where "(e'\<langle>i:T\<rangle>, e'') \<turnstile> Abs r \<degree> a : U"
          by (rule list_app_typeE) fast
        then obtain T'' where "(e'\<langle>i:T\<rangle>, e'') \<turnstile> a : T''" by cases simp_all
        thus "IT (a[u/i])" using uIT uT by (rule SI2)
      qed
      thus "IT ((Abs r \<degree> a \<degree>\<degree> as)[u/i])" by simp
    }
  qed
qed


subsection \<open>Well-typed terms are strongly normalizing\<close>

lemma type_implies_IT':
  assumes "(e', e'') \<turnstile> t : T"
  shows "IT t"
  using assms
proof (induct "(e', e'')" t T arbitrary: e' e'')
  case BVar
  show ?case by (rule BVar_IT)
next
  case Var
  show ?case by (rule Var_IT)
next
  case Abs
  then show ?case by blast
next
  case (App  s T U t)
  have "IT ((BVar 0 \<degree> lift t 0)[s/0])"
  proof (rule subst_type_IT)
    have "IT (lift t 0)" using \<open>IT t\<close> by (rule lift_IT)
    hence "listsp IT [lift t 0]" by (rule listsp.Cons) (rule listsp.Nil)
    hence "IT (BVar 0 \<degree>\<degree> [lift t 0])" by (rule IT.BVar)
    also have "BVar 0 \<degree>\<degree> [lift t 0] = BVar 0 \<degree> lift t 0" by simp
    finally show "IT \<dots>" .
    have "(e'\<langle>0:T \<Rightarrow> U\<rangle>, e'') \<turnstile> BVar 0 : T \<Rightarrow> U"
      by (rule typing.BVar) simp
    moreover have "(e'\<langle>0:T \<Rightarrow> U\<rangle>, e'') \<turnstile> lift t 0 : T"
      by (rule lift_type) (rule App.hyps)
    ultimately show "(e'\<langle>0:T \<Rightarrow> U\<rangle>, e'') \<turnstile> BVar 0 \<degree> lift t 0 : U"
      by (rule typing.App)
    show "IT s" by fact
    show "(e', e'') \<turnstile> s : T \<Rightarrow> U" by fact
  qed
  thus ?case by simp
qed

lemma type_implies_IT:
  assumes "e \<turnstile> t : T"
  shows "IT t"
  using assms
proof -
  from assms obtain e' e'' where "e = (e', e'')" by fastforce
  with assms have "(e', e'') \<turnstile> t : T" by simp
  with type_implies_IT' show ?thesis by simp
qed

theorem type_implies_termi: "e \<turnstile> t : T \<Longrightarrow> termip beta t"
proof -
  assume "e \<turnstile> t : T"
  hence "IT t" by (rule type_implies_IT)
  thus ?thesis by (rule IT_implies_termi)
qed

end

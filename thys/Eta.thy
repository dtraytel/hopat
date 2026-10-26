section \<open>Eta-reduction\<close>

theory Eta imports ParRed begin

subsection \<open>Definition of eta-reduction and relatives\<close>

primrec
  free :: "dB => nat => bool"
where
    "free (BVar j) i = (j = i)"
  | "free (s \<degree> t) i = (free s i \<or> free t i)"
  | "free (Abs s) i = free s (i + 1)"
  | "free (Var _) _ = False"

inductive
  eta :: "[dB, dB] => bool"  (infixl "\<rightarrow>\<^sub>\<eta>" 50)
where
    eta [simp, intro]: "\<not> free s 0 ==> Abs (s \<degree> BVar 0) \<rightarrow>\<^sub>\<eta> s[dummy/0]"
  | appL [simp, intro]: "s \<rightarrow>\<^sub>\<eta> t ==> s \<degree> u \<rightarrow>\<^sub>\<eta> t \<degree> u"
  | appR [simp, intro]: "s \<rightarrow>\<^sub>\<eta> t ==> u \<degree> s \<rightarrow>\<^sub>\<eta> u \<degree> t"
  | abs [simp, intro]: "s \<rightarrow>\<^sub>\<eta> t ==> Abs s \<rightarrow>\<^sub>\<eta> Abs t"

abbreviation
  eta_reds :: "[dB, dB] => bool"   (infixl "\<rightarrow>\<^sub>\<eta>\<^sup>*" 50) where
  "s \<rightarrow>\<^sub>\<eta>\<^sup>* t == eta\<^sup>*\<^sup>* s t"

abbreviation
  eta_red0 :: "[dB, dB] => bool"   (infixl "\<rightarrow>\<^sub>\<eta>\<^sup>=" 50) where
  "s \<rightarrow>\<^sub>\<eta>\<^sup>= t == eta\<^sup>=\<^sup>= s t"

inductive_cases eta_cases [elim!]:
  "Abs s \<rightarrow>\<^sub>\<eta> z"
  "s \<degree> t \<rightarrow>\<^sub>\<eta> u"
  "BVar i \<rightarrow>\<^sub>\<eta> t"
  "Var i \<rightarrow>\<^sub>\<eta> t"

subsection \<open>Properties of \<open>eta\<close>, \<open>subst\<close> and \<open>free\<close>\<close>

lemma subst_not_free [simp]: "\<not> free s i \<Longrightarrow> s[t/i] = s[u/i]"
  by (induct s arbitrary: i t u) (simp_all add: subst_BVar)

lemma free_lift [simp]:
    "free (lift t k) i = (i < k \<and> free t i \<or> k < i \<and> free t (i - 1))"
  apply (induct t arbitrary: i k)
  apply (auto cong: conj_cong)
  done

lemma free_subst [simp]:
    "free (s[t/k]) i =
      (free s k \<and> free t i \<or> free s (if i < k then i else i + 1))"
  apply (induct s arbitrary: i k t)
    prefer 3
     apply simp
    apply blast
   prefer 3
   apply simp
   apply (simp add: diff_Suc subst_BVar split: nat.split)
  apply auto
  done

lemma free_eta: "s \<rightarrow>\<^sub>\<eta> t ==> free t i = free s i"
  by (induct arbitrary: i set: eta) (simp_all cong: conj_cong)

lemma not_free_eta:
    "[| s \<rightarrow>\<^sub>\<eta> t; \<not> free s i |] ==> \<not> free t i"
  by (simp add: free_eta)

lemma eta_subst [simp]:
    "s \<rightarrow>\<^sub>\<eta> t ==> s[u/i] \<rightarrow>\<^sub>\<eta> t[u/i]"
  by (induct arbitrary: u i set: eta) (simp_all add: subst_subst [symmetric])

theorem lift_subst_dummy: "\<not> free s i \<Longrightarrow> lift (s[dummy/i]) i = s"
  by (induct s arbitrary: i dummy) simp_all

subsection \<open>Confluence of \<open>eta\<close>\<close>

lemma square_eta: "square eta eta (eta\<^sup>=\<^sup>=) (eta\<^sup>=\<^sup>=)"
  apply (unfold square_def id_def)
  apply (rule impI [THEN allI [THEN allI]])
  apply (erule eta.induct)
     apply (slowsimp intro: subst_not_free eta_subst free_eta [THEN iffD1])
    apply safe
       prefer 5
         apply (blast intro!: eta_subst intro: free_eta [THEN iffD1])
      apply blast+
  done

theorem eta_confluent: "confluent eta"
  apply (rule square_eta [THEN square_reflcl_confluent])
  done

subsection \<open>Congruence rules for \<open>eta\<^sup>*\<close>\<close>

lemma rtrancl_eta_Abs: "s \<rightarrow>\<^sub>\<eta>\<^sup>* s' ==> Abs s \<rightarrow>\<^sub>\<eta>\<^sup>* Abs s'"
  by (induct set: rtranclp)
    (blast intro: rtranclp.rtrancl_into_rtrancl)+

lemma rtrancl_eta_AppL: "s \<rightarrow>\<^sub>\<eta>\<^sup>* s' ==> s \<degree> t \<rightarrow>\<^sub>\<eta>\<^sup>* s' \<degree> t"
  by (induct set: rtranclp)
    (blast intro: rtranclp.rtrancl_into_rtrancl)+

lemma rtrancl_eta_AppR: "t \<rightarrow>\<^sub>\<eta>\<^sup>* t' ==> s \<degree> t \<rightarrow>\<^sub>\<eta>\<^sup>* s \<degree> t'"
  by (induct set: rtranclp) (blast intro: rtranclp.rtrancl_into_rtrancl)+

lemma rtrancl_eta_App:
    "[| s \<rightarrow>\<^sub>\<eta>\<^sup>* s'; t \<rightarrow>\<^sub>\<eta>\<^sup>* t' |] ==> s \<degree> t \<rightarrow>\<^sub>\<eta>\<^sup>* s' \<degree> t'"
  by (blast intro!: rtrancl_eta_AppL rtrancl_eta_AppR intro: rtranclp_trans)

subsection \<open>Commutation of \<open>beta\<close> and \<open>eta\<close>\<close>

lemma free_beta:
    "s \<rightarrow>\<^sub>\<beta> t ==> free t i \<Longrightarrow> free s i"
  by (induct arbitrary: i set: beta) auto

lemma beta_subst [intro]: "s \<rightarrow>\<^sub>\<beta> t ==> s[u/i] \<rightarrow>\<^sub>\<beta> t[u/i]"
  by (induct arbitrary: u i set: beta) (simp_all add: subst_subst [symmetric])

lemma subst_BVar_Suc [simp]: "t[BVar i/i] = t[BVar(i)/i + 1]"
  by (induct t arbitrary: i) (auto elim!: linorder_neqE simp: subst_BVar)

lemma eta_lift [simp]: "s \<rightarrow>\<^sub>\<eta> t ==> lift s i \<rightarrow>\<^sub>\<eta> lift t i"
  by (induct arbitrary: i set: eta) simp_all

lemma rtrancl_eta_subst: "s \<rightarrow>\<^sub>\<eta> t \<Longrightarrow> u[s/i] \<rightarrow>\<^sub>\<eta>\<^sup>* u[t/i]"
  apply (induct u arbitrary: s t i)
    apply (simp_all add: subst_BVar)
    apply blast
   apply (blast intro: rtrancl_eta_App)
  apply (blast intro!: rtrancl_eta_Abs eta_lift)
  done

lemma rtrancl_eta_subst':
  fixes s t :: dB
  assumes eta: "s \<rightarrow>\<^sub>\<eta>\<^sup>* t"
  shows "s[u/i] \<rightarrow>\<^sub>\<eta>\<^sup>* t[u/i]" using eta
  by induct (iprover intro: eta_subst)+

lemma rtrancl_eta_subst'':
  fixes s t :: dB
  assumes eta: "s \<rightarrow>\<^sub>\<eta>\<^sup>* t"
  shows "u[s/i] \<rightarrow>\<^sub>\<eta>\<^sup>* u[t/i]" using eta
  by induct (iprover intro: rtrancl_eta_subst rtranclp_trans)+

lemma square_beta_eta: "square beta eta (eta\<^sup>*\<^sup>*) (beta\<^sup>=\<^sup>=)"
  apply (unfold square_def)
  apply (rule impI [THEN allI [THEN allI]])
  apply (erule beta.induct)
     apply (slowsimp intro: rtrancl_eta_subst eta_subst)
    apply (blast intro: rtrancl_eta_AppL)
   apply (blast intro: rtrancl_eta_AppR)
  apply simp
  apply (slowsimp intro: rtrancl_eta_Abs free_beta
    iff del: dB.distinct simp: dB.distinct)    (*23 seconds?*)
  done

lemma confluent_beta_eta: "confluent (sup beta eta)"
  apply (assumption |
    rule square_rtrancl_reflcl_commute confluent_Un
      beta_confluent eta_confluent square_beta_eta)+
  done

subsection \<open>Eta-postponement theorem\<close>

text \<open>
  Based on a paper proof due to Andreas Abel.
  Unlike the proof by Masako Takahashi @{cite "Takahashi-IandC"}, it does not
  use parallel eta reduction, which only seems to complicate matters unnecessarily.
  Generalized to count the number of beta reduction steps. (Dmitriy Traytel)
\<close>

inductive counting_par_beta :: "[dB, nat, dB] => bool"  ("_ =>[_] _" [50, 50, 50] 50)
  where
    var [simp, intro!]: "BVar n =>[0] BVar n"
  | var' [simp, intro!]: "Var n =>[0] Var n"
  | abs [simp, intro!]: "s =>[i] t ==> Abs s =>[i] Abs t"
  | app [simp, intro!]: "[| s =>[i] s'; t =>[j] t'; k = i + j|] ==> s \<degree> t =>[k] s' \<degree> t'"
  | beta [simp, intro!]: "[| s =>[i] s'; t =>[j] t'; k = i + j + 1|] ==> (Abs s) \<degree> t =>[k] s'[t'/0]"

inductive_cases par_beta_cases [elim!]:
  "BVar n =>[i] t"
  "Var n =>[i] t"
  "Abs s =>[i] Abs t"
  "(Abs s) \<degree> t =>[i] u"
  "s \<degree> t =>[i] u"
  "Abs s =>[i] t"

lemma counting_par_beta_refl [simp]: "t =>[0] t"
  by (induct t) simp_all


lemma counting_par_beta_lift [simp]:
    "t =>[i] t' \<Longrightarrow> lift t n =>[i] lift t' n"
  by (induct t i t' arbitrary: n rule: counting_par_beta.induct) auto

theorem eta_case:
  fixes s :: dB
  assumes free: "\<not> free s 0"
  and s: "s[dummy/0] =>[i] u"
  shows "\<exists>t'. Abs (s \<degree> BVar 0) =>[i] t' \<and> t' \<rightarrow>\<^sub>\<eta>\<^sup>* u"
proof -
  from s have "lift (s[dummy/0]) 0 =>[i] lift u 0" by (auto simp del: lift_subst)
  with free have "s =>[i] lift u 0" by (simp add: lift_subst_dummy del: lift_subst)
  hence "Abs (s \<degree> BVar 0) =>[i] Abs (lift u 0 \<degree> BVar 0)" by auto
  moreover have "\<not> free (lift u 0) 0" by simp
  hence "Abs (lift u 0 \<degree> BVar 0) \<rightarrow>\<^sub>\<eta> lift u 0[dummy/0]"
    by (rule eta.eta)
  hence "Abs (lift u 0 \<degree> BVar 0) \<rightarrow>\<^sub>\<eta>\<^sup>* u" by simp
  ultimately show ?thesis
    by (intro exI conjI) auto
qed

theorem eta_par_beta:
  assumes st: "s \<rightarrow>\<^sub>\<eta> t"
  and tu: "t =>[i] u"
shows "\<exists>t' j. s =>[j] t' \<and> t' \<rightarrow>\<^sub>\<eta>\<^sup>* u \<and> j \<ge> i" using tu st
proof (induct t i u arbitrary: s)
  case (var n)
  thus ?case by (force intro: par_beta_refl exI[of _ 0] exI[of _ s])
next
  case (var' n)
  thus ?case by (force intro: par_beta_refl exI[of _ 0] exI[of _ s])
next
  case (abs s' i t)
  note abs' = this
  from \<open>s \<rightarrow>\<^sub>\<eta> Abs s'\<close> show ?case
  proof cases
    case (eta s'' dummy)
    from abs have "Abs s' =>[i] Abs t" by simp
    with eta abs(3) have "s''[dummy/0] =>[i] Abs t" by simp
    with \<open>\<not> free s'' 0\<close> have "\<exists>t'. Abs (s'' \<degree> BVar 0) =>[i] t' \<and> t' \<rightarrow>\<^sub>\<eta>\<^sup>* Abs t"
      by (rule eta_case)
    with eta show ?thesis by force
  next
    case (abs r)
    from \<open>r \<rightarrow>\<^sub>\<eta> s'\<close>
    obtain t' j where r: "r =>[j] t'" and t': "t' \<rightarrow>\<^sub>\<eta>\<^sup>* t" and j: "j \<ge> i"
      using abs'(2)[of r] abs'(3) by blast
    from r have "Abs r =>[j] Abs t'" by simp
    moreover from t' have "Abs t' \<rightarrow>\<^sub>\<eta>\<^sup>* Abs t" by (rule rtrancl_eta_Abs)
    ultimately show ?thesis using abs j by blast
  qed
next
  case (app u i u' t j t' k)
  from \<open>s \<rightarrow>\<^sub>\<eta> u \<degree> t\<close> show ?case
  proof cases
    case (eta s' dummy)
    from app have "u \<degree> t =>[k] u' \<degree> t'" by simp
    with eta have "s'[dummy/0] =>[k] u' \<degree> t'" by simp
    with \<open>\<not> free s' 0\<close> have "\<exists>r. Abs (s' \<degree> BVar 0) =>[k] r \<and> r \<rightarrow>\<^sub>\<eta>\<^sup>* u' \<degree> t'"
      by (rule eta_case)
    with eta show ?thesis by auto
  next
    case (appL s')
    from \<open>s' \<rightarrow>\<^sub>\<eta> u\<close>
    obtain r l where s': "s' =>[l] r" and r: "r \<rightarrow>\<^sub>\<eta>\<^sup>* u'" and l: "l \<ge> i"
      by (iprover dest: app)
    from s' and app have "s' \<degree> t =>[l + j] r \<degree> t'" by simp
    moreover from r have "r \<degree> t' \<rightarrow>\<^sub>\<eta>\<^sup>* u' \<degree> t'" by (simp add: rtrancl_eta_AppL)
    ultimately show ?thesis using appL l app(5)
      by (intro exI conjI) auto
  next
    case (appR s')
    from \<open>s' \<rightarrow>\<^sub>\<eta> t\<close>
    obtain r l where s': "s' =>[l] r" and r: "r \<rightarrow>\<^sub>\<eta>\<^sup>* t'" and l: "l \<ge> j"
      by (iprover dest: app)
    from s' and app have "u \<degree> s' =>[i + l] u' \<degree> r" by simp
    moreover from r have "u' \<degree> r \<rightarrow>\<^sub>\<eta>\<^sup>* u' \<degree> t'" by (simp add: rtrancl_eta_AppR)
    ultimately show ?thesis using appR l app(5)
      by (intro exI conjI) auto
  qed
next
  case (beta u i u' t j t' k)
  from \<open>s \<rightarrow>\<^sub>\<eta> Abs u \<degree> t\<close> show ?case
  proof cases
    case (eta s' dummy)
    from beta have "Abs u \<degree> t =>[k] u'[t'/0]" by simp
    with eta have "s'[dummy/0] =>[k] u'[t'/0]" by simp
    with \<open>\<not> free s' 0\<close> have "\<exists>r. Abs (s' \<degree> BVar 0) =>[k] r \<and> r \<rightarrow>\<^sub>\<eta>\<^sup>* u'[t'/0]"
      by (rule eta_case)
    with eta show ?thesis by auto
  next
    case (appL s')
    from \<open>s' \<rightarrow>\<^sub>\<eta> Abs u\<close> show ?thesis
    proof cases
      case (eta s'' dummy)
      have "Abs (lift u 1) = lift (Abs u) 0" by simp
      also from eta have "\<dots> = s''" by (simp add: lift_subst_dummy del: lift_subst)
      finally have s: "s = Abs (Abs (lift u 1) \<degree> BVar 0) \<degree> t" using appL and eta by simp
      from beta have "lift u 1 =>[i] lift u' 1" by simp
      hence "Abs (lift u 1) \<degree> BVar 0 =>[i + 1] lift u' 1[BVar 0/0]"
        using counting_par_beta.var by fastforce
      hence "Abs (Abs (lift u 1) \<degree> BVar 0) \<degree> t =>[k + 1] lift u' 1[BVar 0/0][t'/0]"
        using \<open>t =>[j] t'\<close> \<open>k = i + j + 1\<close> by simp
      with s have "s =>[k + 1] u'[t'/0]" by simp
      thus ?thesis
        by force
    next
      case (abs r)
      from \<open>r \<rightarrow>\<^sub>\<eta> u\<close>
      obtain r'' l where r: "r =>[l] r''" and r'': "r'' \<rightarrow>\<^sub>\<eta>\<^sup>* u'" and l: "l \<ge> i"
        by (iprover dest: beta)
      from r and beta(3) have "Abs r \<degree> t =>[l + j + 1] r''[t'/0]" by simp
      moreover from r'' have "r''[t'/0] \<rightarrow>\<^sub>\<eta>\<^sup>* u'[t'/0]"
        by (rule rtrancl_eta_subst')
      ultimately show ?thesis using abs appL l beta(5)
        by force
    qed
  next
    case (appR s')
    from \<open>s' \<rightarrow>\<^sub>\<eta> t\<close>
    obtain r l where s': "s' =>[l] r" and r: "r \<rightarrow>\<^sub>\<eta>\<^sup>* t'" and l: "l \<ge> j"
      by (iprover dest: beta)
    from s' and beta have "Abs u \<degree> s' =>[i + l + 1] u'[r/0]" by simp
    moreover from r have "u'[r/0] \<rightarrow>\<^sub>\<eta>\<^sup>* u'[t'/0]"
      by (rule rtrancl_eta_subst'')
    ultimately show ?thesis using appR l beta(5)
      by fastforce
  qed
qed

theorem eta_postponement:
  assumes eta: "s \<rightarrow>\<^sub>\<eta>\<^sup>* t" and beta: "t =>[i] u"
  shows "\<exists>t' j. s =>[j] t' \<and> t' \<rightarrow>\<^sub>\<eta>\<^sup>* u \<and> j \<ge> i" using eta beta
proof (induct arbitrary: u i)
  case base
  thus ?case by blast
next
  case (step s' s'' s''')
  then obtain t' j where s': "s' =>[j] t'" and t': "t' \<rightarrow>\<^sub>\<eta>\<^sup>* s'''" and j: "j \<ge> i"
    by (auto dest: eta_par_beta)
  from s' obtain t'' l where s: "s =>[l] t''" and t'': "t'' \<rightarrow>\<^sub>\<eta>\<^sup>* t'" and l: "l \<ge> j"
    using step by blast
  from t'' and t' have "t'' \<rightarrow>\<^sub>\<eta>\<^sup>* s'''" by (rule rtranclp_trans)
  with s j l show ?case by force
qed

lemma beta_counting_par_beta: "beta t u \<Longrightarrow> t =>[1] u"
  by (induct t u rule: beta.induct) auto

lemma relpow_beta_Abs: "((\<rightarrow>\<^sub>\<beta>) ^^ i) s t \<Longrightarrow> ((\<rightarrow>\<^sub>\<beta>) ^^ i) (Abs s) (Abs t)"
  apply (induct i arbitrary: s)
   apply simp
  apply (erule relpowp_Suc_E2)
  apply (rule relpowp_Suc_I2)
   apply auto
  done

lemma relpow_beta_App:
   "((\<rightarrow>\<^sub>\<beta>) ^^ i) s1 s2 \<Longrightarrow> ((\<rightarrow>\<^sub>\<beta>) ^^ j) t1 t2 \<Longrightarrow> ((\<rightarrow>\<^sub>\<beta>) ^^ (i + j)) (s1 \<degree> t1) (s2 \<degree> t2)"
  apply (induct i arbitrary: s1 j)
  subgoal for s1 j
    apply (induct j arbitrary: t1)
     apply simp
    apply (erule relpowp_Suc_E2)
    unfolding add_0
    apply (rule relpowp_Suc_I2)
     apply auto
    done
  subgoal for i s1 j
    apply (erule relpowp_Suc_E2)
    unfolding add_Suc
    apply (rule relpowp_Suc_I2)
     apply auto
    done
  done

lemma counting_par_beta_beta: "t =>[i] u \<Longrightarrow> (beta^^i) t u"
  by (induct t i u rule: counting_par_beta.induct)
    (force simp: relpow_beta_Abs relpow_beta_App relcompp_apply)+

theorem eta_postponement':
  assumes eta: "s \<rightarrow>\<^sub>\<eta>\<^sup>* t" and beta: "t \<rightarrow>\<^sub>\<beta> u"
  shows "\<exists>t'. tranclp (\<rightarrow>\<^sub>\<beta>) s t' \<and> t' \<rightarrow>\<^sub>\<eta>\<^sup>* u"
proof -
  from eta_postponement[OF eta beta_counting_par_beta[OF beta]]
  obtain t' j where "s =>[j] t'" and *: "t' \<rightarrow>\<^sub>\<eta>\<^sup>* u" "j \<ge> 1" by blast
  with counting_par_beta_beta have "(beta^^j) s t'" by blast
  with * show ?thesis by (auto intro!: exI[of _ t'] simp: tranclp_power Suc_le_eq)
qed

end
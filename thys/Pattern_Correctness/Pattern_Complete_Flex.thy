section \<open>Completeness of the Flex-Flex Steps\<close>

theory Pattern_Complete_Flex
  imports Pattern_Complete_Steps
begin

context pure_sig
begin

subsection \<open>Extending solutions\<close>

definition supd :: "vsubst \<Rightarrow> indexname \<Rightarrow> ptyp \<Rightarrow> pterm \<Rightarrow> vsubst" where
  "supd \<sigma> x T w = (\<lambda>y U. if y = x \<and> U = T then w else \<sigma> y U)"

lemma supd_eq [simp]: "supd \<sigma> x T w x T = w"
  by (simp add: supd_def)

lemma wt_subst_supd: "wt_subst \<sigma> \<Longrightarrow> closed w \<Longrightarrow> (\<And>e. e \<turnstile> w : T) \<Longrightarrow> wt_subst (supd \<sigma> x T w)"
  unfolding wt_subst_def closed_subst_def supd_def by auto

lemma sagree_supd: "n < snd x \<Longrightarrow> sagree n \<sigma> (supd \<sigma> x T w)"
  unfolding sagree_def supd_def by auto

lemma ap_sagree: "sagree n \<sigma> \<sigma>' \<Longrightarrow> below n (vars t) \<Longrightarrow> ap \<rho> \<sigma>' t = ap \<rho> \<sigma> t"
  unfolding ap_def
  by (rule vsubst_cong) (auto simp: vars_inst sagree_def below_def)

text \<open>A solution extends to new bindings, of variables that are not bound yet:\<close>

lemma solution_extend:
  assumes sol: "solution \<rho> \<sigma> env" and vi: "vinv \<rho> env X"
    and \<sigma>': "sagree (maxidx env) \<sigma> \<sigma>'" "wt_subst \<sigma>'"
    and ty: "tyenv env' = tyenv env"
    and old: "\<And>x b. vt_lookup (tenv env) x = Some b \<Longrightarrow> vt_lookup (tenv env') x = Some b"
    and new: "\<And>x U u. vt_lookup (tenv env') x = Some (U, u) \<Longrightarrow> vt_lookup (tenv env) x = None \<Longrightarrow>
      \<sigma>' x (tsubst \<rho> U) \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma>' u"
  shows "solution \<rho> \<sigma>' env'"
  unfolding solution_def
proof (intro conjI allI impI)
  note s = solutionD[OF sol]
  show "wsinst alg \<rho>" by (rule s(1))
  show "tsol (tyenv env') \<rho>" using s(2) ty by simp
  show "wt_subst \<sigma>'" by (rule \<sigma>'(2))
  fix x U u assume b': "vt_lookup (tenv env') x = Some (U, u)"
  show "\<sigma>' x (tsubst \<rho> U) \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma>' u"
  proof (cases "vt_lookup (tenv env) x")
    case None
    then show ?thesis by (rule new[OF b'])
  next
    case (Some b)
    with old b' have b: "vt_lookup (tenv env) x = Some (U, u)" by fastforce
    have "(x, U) \<in> X \<union> evars env" using evarsI[OF b] by simp
    moreover have "\<forall>p\<in>X \<union> evars env. snd (fst p) \<le> maxidx env" using vi by (simp add: vinv_def below_def)
    ultimately have bx: "snd x \<le> maxidx env" by force
    have bu: "below (maxidx env) (vars u)" using vi evarsI2[OF b] by (auto simp: vinv_def below_def)
    have "\<sigma>' x (tsubst \<rho> U) = \<sigma> x (tsubst \<rho> U)" using \<sigma>'(1) bx by (cases x) (simp add: sagree_def)
    moreover have "ap \<rho> \<sigma>' u = ap \<rho> \<sigma> u" by (rule ap_sagree[OF \<sigma>'(1) bu])
    ultimately show ?thesis using s(4)[OF b] by simp
  qed
qed


subsection \<open>The type invariant for new bindings\<close>

lemma tvinv_genvar: "genvar a env T = (env', G) \<Longrightarrow> tvinv A env \<Longrightarrow> tvinv A env'"
  unfolding tvinv_def using tinv_mono by (auto simp: genvar_simps)

lemma tvinv_update:
  assumes "ok (update (F, T) t env) env'" "tvinv A env" "tvars T \<union> ttvars t \<subseteq> tvars_env (tyenv env) \<union> A"
  shows "tvinv A env'"
  using assms ok_update[OF assms(1)] unfolding tvinv_def by (auto split: if_splits)

lemma tvars_funs: "tvars (Ts \<Rrightarrow> T) = (\<Union>U\<in>set Ts. tvars U) \<union> tvars T"
  by (induction Ts) auto

lemma type_of_G_tvars:
  assumes "ok (type_of_G env T n is) G" "tvinv A env" "tvars T \<subseteq> tvars_env (tyenv env) \<union> A"
  shows "tvars G \<subseteq> tvars_env (tyenv env) \<union> A"
proof -
  let ?\<theta> = "tyenv env"
  have inv: "tinv ar (maxidx env) ?\<theta> A" by (rule tvinvD(1)[OF assms(2)])
  have nt: "norm_type ?\<theta> T = return (tnorm ?\<theta> T)"
    by (rule norm_type_ok[OF tinv_tacyc[OF inv] tinv_tcons_env[OF inv] tinv_tcons[OF inv assms(3)]])
  from assms(1) nt obtain Ts U Us where st: "ok (split_type (tnorm ?\<theta> T) n []) (Ts, U)"
    and us: "ok (mapM (nth Ts) is) Us" and G: "G = foldr (\<rightarrow>\<^sub>T) Us U"
    by (auto simp: type_of_G_def split: prod.splits)
  from ok_split_type[OF st] obtain Vs where Vs: "tnorm ?\<theta> T = foldr (\<rightarrow>\<^sub>T) Vs U" "Ts = rev Vs"
    by auto
  have tvn: "tvars (tnorm ?\<theta> T) \<subseteq> tvars_env ?\<theta> \<union> A"
    using tvars_tnorm[OF tinv_tacyc[OF inv], of T] assms(3) by blast
  have nth_set: "x \<in> set Ts" if "ok (nth Ts i) x" for i x
    using that nat_of_integer_less_ilength[of i Ts] by (auto simp: ok_nth)
  have "list_all2 (\<lambda>i x. ok (nth Ts i) x) is Us" using us by (simp add: ok_mapM)
  then have "set Us \<subseteq> set Ts" by (induction rule: list_all2_induct) (auto dest: nth_set)
  then show ?thesis using tvn Vs G by (auto simp: tvars_funs)
qed


subsection \<open>Flex-flex problems with the same head\<close>

lemma ok_mk_ff_list_aux_complete:
  "ok (mk_ff_list_aux is js k) ks \<Longrightarrow> p < length is \<Longrightarrow> is ! p = js ! p \<Longrightarrow> k - integer_of_nat p \<in> set ks"
proof (induction "is" js k arbitrary: ks p rule: mk_ff_list_aux.induct)
  case (2 i "is" j js k)
  show ?case
  proof (cases p)
    case 0
    with "2.prems" show ?thesis by (auto simp: integer_reps)
  next
    case (Suc p')
    obtain ks' where ks': "ok (mk_ff_list_aux is js (k - 1)) ks'" "set ks' \<subseteq> set ks"
    proof (cases "i = j")
      case True
      with "2.prems"(1) obtain ks' where "ok (mk_ff_list_aux is js (k - 1)) ks'" "ks = k # ks'" by auto
      then show ?thesis using that by auto
    next
      case False
      with "2.prems"(1) have "ok (mk_ff_list_aux is js (k - 1)) ks" by simp
      then show ?thesis using that by auto
    qed
    from "2.IH"[OF _ ks'(1)] "2.prems" Suc have "k - 1 - integer_of_nat p' \<in> set ks'"
      by (cases "i = j") auto
    moreover have "k - 1 - integer_of_nat p' = k - integer_of_nat p" using Suc by (simp add: integer_reps)
    ultimately show ?thesis using ks'(2) by auto
  qed
qed auto

lemma ok_mk_ff_list_complete:
  assumes "ok (mk_ff_list is js) ks" "0 \<le> k" "k < ilength is" "bren (rev is) k = bren (rev js) k"
  shows "k \<in> set ks"
proof -
  have len: "length is = length js" using ok_mk_ff_list(1)[OF assms(1)] .
  define p where "p = length is - 1 - nat_of_integer k"
  have nk: "nat_of_integer k < length is" using assms(2,3) by (rule nat_of_integer_less_ilength)
  then have p: "p < length is" by (simp add: p_def)
  have "rev is ! nat_of_integer k = is ! p" "rev js ! nat_of_integer k = js ! p"
    using nk len by (simp_all add: rev_nth p_def)
  moreover have "bren (rev is) k = rev is ! nat_of_integer k" "bren (rev js) k = rev js ! nat_of_integer k"
    using assms(2,3) len by (simp_all add: bren_rev ilength_eq)
  ultimately have "is ! p = js ! p" using assms(4) by simp
  from ok_mk_ff_list_aux_complete[OF assms(1)[unfolded mk_ff_list_def] p this]
  have "ilength is - 1 - integer_of_nat p \<in> set ks" .
  moreover have "ilength is - 1 - integer_of_nat p = k"
    using nk assms(2) by (simp add: p_def ilength_eq integer_reps of_nat_diff)
  ultimately show ?thesis by simp
qed

end

end

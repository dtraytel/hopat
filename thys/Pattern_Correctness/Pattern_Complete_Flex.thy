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

lemma ttvars_abs_list: "ttvars (abs_list bs t) = btvars bs \<union> ttvars t"
  by (induction bs) (auto simp: btvars_def)

lemma btvars_nths:
  assumes "\<forall>i\<in>set is. 0 \<le> i \<and> i < ilength bs"
  shows "btvars (map (\<lambda>i. bs ! nat_of_integer i) is) \<subseteq> btvars bs"
proof -
  have "set (map (\<lambda>i. bs ! nat_of_integer i) is) \<subseteq> set bs"
    using assms by (auto intro!: nth_mem simp: nat_of_integer_less_ilength)
  then show ?thesis unfolding btvars_def by blast
qed

lemma app_Bounds_less: "\<not> loose_bvar (app s is) n \<Longrightarrow> \<forall>i\<in>set is. i < n"
  by (auto simp: app_apps loose_bvar_apps not_le)

lemma ttvars_app [simp]: "ttvars (app s is) = ttvars s"
  by (simp add: app_apps ttvars_apps)

text \<open>The data of a flex problem \<open>F xs\<close> in the invariant:\<close>

lemma flex_data:
  assumes inv: "cinv \<rho> \<sigma> env e bs X A" and c: "cterm \<rho> env e bs A (app (Var F Fty) xs) T"
  shows "tsubst \<rho> Fty = map e xs \<Rrightarrow> T" "cert_typ alg ar (tsubst \<rho> Fty)"
    "\<forall>i\<in>set xs. 0 \<le> i \<and> i < ilength bs"
    "closed (\<sigma> F (tsubst \<rho> Fty))" "\<And>e'. e' \<turnstile> \<sigma> F (tsubst \<rho> Fty) : map e xs \<Rrightarrow> T"
    "ap \<rho> \<sigma> (app (Var F Fty) xs) = \<sigma> F (tsubst \<rho> Fty) \<degree>\<degree> map Bound xs"
    "map snd (map (\<lambda>(x, T). (x, tsubst \<rho> T)) (map (\<lambda>i. bs ! nat_of_integer i) xs)) = map e xs"
    "\<forall>i\<in>set xs. cert_typ alg ar (e i)"
    "tvars Fty \<subseteq> tvars_env (tyenv env) \<union> A"
proof -
  note i = inv[unfolded cinv_def]
  have \<sigma>: "wt_subst \<sigma>" using i solutionD(3) by blast
  have ty: "e \<turnstile> inst \<rho> (app (Var F Fty) xs) : T" using c by (simp add: cterm_def)
  from ty obtain F1: "tsubst \<rho> Fty = map e xs \<Rrightarrow> T" and F2: "cert_typ alg ar (tsubst \<rho> Fty)"
    and F3: "\<forall>i\<in>set xs. 0 \<le> i" by (rule typing_appE)
  show "tsubst \<rho> Fty = map e xs \<Rrightarrow> T" "cert_typ alg ar (tsubst \<rho> Fty)" by (rule F1, rule F2)
  show xs: "\<forall>i\<in>set xs. 0 \<le> i \<and> i < ilength bs"
    using F3 app_Bounds_less[of "Var F Fty" xs "ilength bs"] c by (auto simp: cterm_def)
  show "closed (\<sigma> F (tsubst \<rho> Fty))" using \<sigma> by (cases F) (simp add: wt_subst_def closed_subst_def)
  show "e' \<turnstile> \<sigma> F (tsubst \<rho> Fty) : map e xs \<Rrightarrow> T" for e'
    using wt_subst_typing[OF \<sigma> F2] F1 by simp
  show "ap \<rho> \<sigma> (app (Var F Fty) xs) = \<sigma> F (tsubst \<rho> Fty) \<degree>\<degree> map Bound xs"
    by (simp add: app_apps ap_apps comp_def)
  note bt = bs_types[OF _ xs]
  show "map snd (map (\<lambda>(x, T). (x, tsubst \<rho> T)) (map (\<lambda>i. bs ! nat_of_integer i) xs)) = map e xs"
    using bt(1) i by blast
  have "cert_typ alg ar U" if "U \<in> set (map e xs)" for U
    using bt(2) bt(1) i that by (metis image_set)
  then show "\<forall>i\<in>set xs. cert_typ alg ar (e i)" by auto
  show "tvars Fty \<subseteq> tvars_env (tyenv env) \<union> A" using c by (simp add: cterm_def)
qed

lemma step_cp_flexflex1:
  "step_cp env bs (app (Var F Fty) is) (app (Var F Gty) js) (flexflex1 env bs F Fty is js)"
proof (rule step_cpI)
  fix \<rho> \<sigma> e X A T
  assume inv: "cinv \<rho> \<sigma> env e bs X A" and X: "vars (app (Var F Fty) is) \<union> vars (app (Var F Gty) js) \<subseteq> X"
    and cs: "cterm \<rho> env e bs A (app (Var F Fty) is) T" and ct: "cterm \<rho> env e bs A (app (Var F Gty) js) T"
    and eq: "ap \<rho> \<sigma> (app (Var F Fty) is) \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma> (app (Var F Gty) js)"
  note i = inv[unfolded cinv_def]
  have sol: "solution \<rho> \<sigma> env" and wte: "wt_env \<rho> env" and bse: "bs_env \<rho> e bs"
    and vi: "vinv \<rho> env X" and tv0: "tvinv A env" using i by blast+
  have XX: "X \<union> {(F, Fty), (F, Gty)} = X" using X by auto
  have vi': "vinv \<rho> env (X \<union> {(F, Fty), (F, Gty)})" using vi by (simp only: XX)
  have FG: "tsubst \<rho> Fty = tsubst \<rho> Gty" by (rule vinv_FG[OF vi'])
  note fd = flex_data[OF inv cs] and gd = flex_data[OF inv ct]
  have tyF: "e \<turnstile> inst \<rho> (app (Var F Fty) is) : T" and tyG: "e \<turnstile> inst \<rho> (app (Var F Gty) js) : T"
    using cs ct by (simp_all add: cterm_def)
  show "ccon \<rho> \<sigma> env e bs X A (flexflex1 env bs F Fty is js)"
  proof (cases "is = js")
    case True
    then show ?thesis using ccon_Ok[OF inv] by (simp add: flexflex1_def)
  next
    case False
    have nu: "no_unif (flexflex1 env bs F Fty is js)"
      using False by (simp add: flexflex1_def) (intro no_unif_bindM no_unif_mk_ff_list no_unif_mk_new_hnf)
    have "\<exists>\<rho>' \<sigma>'. cinv \<rho>' \<sigma>' env' e bs X A \<and> tagree (maxidx env) \<rho> \<rho>' \<and> sagree (maxidx env) \<sigma> \<sigma>' \<and>
      tvars_env (tyenv env) \<subseteq> tvars_env (tyenv env') \<and> maxidx env \<le> maxidx env'"
      if ff: "ok (flexflex1 env bs F Fty is js) env'" for env'
    proof -
      from ff False obtain ks where ks: "ok (mk_ff_list is js) ks"
        and hnf: "ok (mk_new_hnf env bs is F Fty ks) env'"
        by (auto simp: flexflex1_def)
      from hnf obtain Gty' where Gty': "ok (type_of_G env Fty (ilength is) ks) Gty'"
        and rest: "ok (let (env1, G) = genvar (fst F) env Gty' in
          mk_hnf bs is G ks \<bind> (\<lambda>t. update (F, Fty) t env1)) env'"
        by (auto simp: mk_new_hnf_def)
      obtain env1 G where G: "genvar (fst F) env Gty' = (env1, G)" by force
      with rest obtain u where u: "ok (mkabs bs is (app G ks)) u" and upd: "ok (update (F, Fty) u env1) env'"
        by (auto simp: mk_hnf_def)
      note g = genvar_simps[OF G]
      let ?G = "(fst F, maxidx env + 1)"
      let ?Ts = "map e is"
      let ?u = "\<sigma> F (tsubst \<rho> Fty)"
      let ?bs = "map (\<lambda>(x, T). (x, tsubst \<rho> T)) (map (\<lambda>i. bs ! nat_of_integer i) is)"
      have len: "length is = length js" using ok_mk_ff_list(1)[OF ks] .
      have uG: "?u = \<sigma> F (tsubst \<rho> Gty)" using FG by simp
      have eq': "?u \<degree>\<degree> map Bound is \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ?u \<degree>\<degree> map Bound js"
        using eq fd(6) gd(6) uG by simp
      have wtu: "wt (?u \<degree>\<degree> map Bound is)"
        using typing_apps_Bounds[OF fd(4) fd(5)] fd(3) by (auto simp: wt_def)
      have c1: "\<forall>U\<in>set ?Ts. cert_typ alg ar U" using fd(8) by auto
      have c2: "length is = length ?Ts" "\<forall>i\<in>set is. 0 \<le> i" using fd(3) by auto
      have c3: "length js = length ?Ts" "\<forall>i\<in>set js. 0 \<le> i" using gd(3) len by auto
      have c4: "\<forall>k\<in>set ks. 0 \<le> k \<and> k < ilength ?Ts" using ok_mk_ff_list(2)[OF ks] by simp
      have c5: "k \<in> set ks" if "0 \<le> k" "k < ilength ?Ts" "bren (rev is) k = bren (rev js) k" for k
        using ok_mk_ff_list_complete[OF ks] that by simp
      obtain w where w: "closed w" "\<forall>e'. e' \<turnstile> w : map (\<lambda>k. rev ?Ts ! nat_of_integer k) ks \<Rrightarrow> T"
        "?u \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> abs_list ?bs (w \<degree>\<degree> map Bound ks)"
        by (rule flex_same_sem[OF fd(4) fd(5) fd(7) c1 c2 c3 eq' wtu c4 c5])
      have tsol: "tsol (tyenv env) \<rho>" using solutionD(2)[OF sol] .
      have tG: "tsubst \<rho> Gty' = map (\<lambda>k. rev ?Ts ! nat_of_integer k) ks \<Rrightarrow> T"
        using type_of_G_sound(1)[OF Gty' tsol fd(1)] by simp
      let ?\<sigma>' = "supd \<sigma> ?G (tsubst \<rho> Gty') w"
      have \<sigma>': "wt_subst ?\<sigma>'" using wt_subst_supd[OF solutionD(3)[OF sol] w(1)] w(2) tG by simp
      have sa: "sagree (maxidx env) \<sigma> ?\<sigma>'" by (rule sagree_supd) simp
      have Fold: "snd F \<le> maxidx env" using vi X unfolding vinv_def below_def by force
      have u': "u = abs_list (map (\<lambda>i. bs ! nat_of_integer i) is) (app (Var ?G Gty') ks)"
        using u by (simp add: ok_mkabs g(4))
      have sol': "solution \<rho> ?\<sigma>' env'"
      proof (rule solution_extend[OF sol vi sa \<sigma>'])
        show "tyenv env' = tyenv env" using ok_update(3)[OF upd] g(2) by simp
        show "vt_lookup (tenv env') x = Some b" if "vt_lookup (tenv env) x = Some b" for x b
          using that ok_update(1,2)[OF upd] g(1) by auto
        fix x U u0 assume new: "vt_lookup (tenv env') x = Some (U, u0)" "vt_lookup (tenv env) x = None"
        then have x: "x = F" "U = Fty" "u0 = u" using ok_update(2)[OF upd] g(1) by (auto split: if_splits)
        have "F \<noteq> ?G" using Fold by (cases F) auto
        then have "?\<sigma>' F (tsubst \<rho> Fty) = ?u" by (simp add: supd_def)
        moreover have "ap \<rho> ?\<sigma>' u = abs_list ?bs (w \<degree>\<degree> map Bound ks)"
          by (simp add: u' ap_abs_list ap_apps app_apps comp_def)
        ultimately show "?\<sigma>' x (tsubst \<rho> U) \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> ?\<sigma>' u0" using w(3) x by simp
      qed
      have wv: "wt_env \<rho> env' \<and> vinv \<rho> env' X"
        using flexflex1_sound(2)[OF ff sol' extends_refl wte bse tyF tyG vi'] by blast
      have tv': "tvinv A env'"
      proof (rule tvinv_update[OF upd tvinv_genvar[OF G tv0]])
        have "tvars Gty' \<subseteq> tvars_env (tyenv env) \<union> A" by (rule type_of_G_tvars[OF Gty' tv0 fd(9)])
        moreover have "btvars (map (\<lambda>i. bs ! nat_of_integer i) is) \<subseteq> tvars_env (tyenv env) \<union> A"
          using btvars_nths[OF fd(3)] i by blast
        ultimately show "tvars Fty \<union> ttvars u \<subseteq> tvars_env (tyenv env1) \<union> A"
          using fd(9) g(2) by (auto simp: u' ttvars_abs_list)
      qed
      have "cinv \<rho> ?\<sigma>' env' e bs X A" using sol' wv tv' i ok_update(3)[OF upd] g(2) by (simp add: cinv_def)
      moreover have "maxidx env \<le> maxidx env'" using ok_update(4)[OF upd] g(3) by simp
      moreover have "tyenv env' = tyenv env" using ok_update(3)[OF upd] g(2) by simp
      ultimately show ?thesis using sa by (intro exI[of _ \<rho>] exI[of _ ?\<sigma>']) simp
    qed
    with nu show ?thesis unfolding ccon_def by blast
  qed
qed

end

end

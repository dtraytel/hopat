section \<open>Termination of the Flex-Flex Cases\<close>

theory Pattern_Term_Flex
  imports Pattern_Termination
begin

context pure_sig_gen
begin

subsection \<open>New variables and bindings keep the invariant\<close>

lemma einv_genvar: "genvar a env T = (env', G) \<Longrightarrow> einv A K env \<Longrightarrow> einv A K env'"
proof -
  assume g: "genvar a env T = (env', G)" and ei: "einv A K env"
  note gs = genvar_simps[OF g] and e = einvD[OF ei]
  have "bbelow env'" by (rule bbelow_mono[OF e(5)]) (simp_all add: gs)
  moreover have "closed_env env'" using e(4) by (simp add: closed_env_def gs)
  ultimately show ?thesis
    using ei tvinv_genvar[OF g e(1)] acyc_genvar[OF g] by (simp add: einv_def gs)
qed

lemma bbelow_update:
  assumes "bbelow env" "ok (update (F, T) u env) env'" "snd F \<le> maxidx env"
  shows "bbelow env'"
  unfolding bbelow_def
proof (intro allI impI)
  note o = ok_update[OF assms(2)]
  fix x b assume "vt_lookup (tenv env') x = Some b"
  then have "x = F \<or> vt_lookup (tenv env) x = Some b" using o(2) by (simp split: if_splits)
  then show "snd x \<le> maxidx env'"
  proof
    assume "x = F"
    with assms(3) o(4) show ?thesis by simp
  next
    assume "vt_lookup (tenv env) x = Some b"
    from bbelowD[OF assms(1) this] o(4) show ?thesis by simp
  qed
qed

lemma closed_env_update: "closed_env env \<Longrightarrow> ok (update (F, T) u env) env' \<Longrightarrow> closed u \<Longrightarrow> closed_env env'"
  using ok_update(2)[of F T u env env'] by (simp add: closed_env_def)

lemma einv_update:
  assumes ei: "einv A K env" and upd: "ok (update (F, T) u env) env'"
    and acy: "\<And>y U. (y, U) \<in> vars u \<Longrightarrow> (F, y) \<notin> (dep env)\<^sup>*" and cl: "closed u"
    and F: "snd F \<le> maxidx env" and tv: "tvars T \<union> ttvars u \<subseteq> tvars_env (tyenv env) \<union> A"
  shows "einv A K env'"
proof -
  note e = einvD[OF ei] and o = ok_update[OF upd]
  have "tvinv A env'" by (rule tvinv_update[OF upd e(1) tv])
  moreover have "acyc env'" by (rule acyc_update[OF upd e(3) acy])
  moreover have "closed_env env'" by (rule closed_env_update[OF e(4) upd cl])
  moreover have "bbelow env'" by (rule bbelow_update[OF e(5) upd F])
  ultimately show ?thesis using ei by (simp add: einv_def o(3))
qed

lemma loose_bvar_app_Var: "\<not> loose_bvar (app (Var x T) ks) n \<longleftrightarrow> (\<forall>k\<in>set ks. k < n)"
  by (auto simp: app_apps loose_bvar_apps)

lemma not_dep_unbound:
  "vt_lookup (tenv env) G = None \<Longrightarrow> F \<noteq> G \<Longrightarrow> (F, G) \<notin> (dep env)\<^sup>*"
  by (auto elim: rtranclE elim!: depE)

text \<open>A binding to a new variable applied to bound variables:\<close>

lemma bind_new_term:
  assumes ei: "einv A K env" and fin: "finite X"
    and F: "vt_lookup (tenv env) F = None" "(F, Fty) \<in> X \<union> evars env" "snd F \<le> maxidx env"
    and gv: "genvar a env Hty = (env1, H)"
    and xs: "\<forall>i\<in>set xs. 0 \<le> i \<and> i < ilength bs" and ks: "\<forall>k\<in>set ks. 0 \<le> k \<and> k < ilength xs"
    and tv: "tvars Fty \<subseteq> tvars_env (tyenv env) \<union> A" "btvars bs \<subseteq> tvars_env (tyenv env) \<union> A"
      "tvars Hty \<subseteq> tvars_env (tyenv env) \<union> A"
  shows "\<exists>env'. (mk_hnf bs xs H ks \<bind> (\<lambda>t. update (F, Fty) t env1)) = return env' \<and>
    einv A K env' \<and> tyenv env' = tyenv env \<and> extends env env' \<and> prunes env env' X \<and>
    card (ubv env' X) \<le> card (ubv env X) \<and> newb env env' \<and>
    vt_lookup (tenv env') F = Some (Fty, abs_list (map (\<lambda>i. bs ! nat_of_integer i) xs) (app H ks))"
proof -
  note e = einvD[OF ei] and g = genvar_simps[OF gv]
  let ?H = "(a, maxidx env + 1)" and ?u = "abs_list (map (\<lambda>i. bs ! nat_of_integer i) xs) (app H ks)"
  have H: "H = Var ?H Hty" by (rule g(4))
  have mk: "mk_hnf bs xs H ks = return ?u" by (simp add: mk_hnf_def mkabs_ok[OF xs])
  have F1: "vt_lookup (tenv env1) F = None" using F(1) g(1) by simp
  obtain env' where upd: "update (F, Fty) ?u env1 = return env'" using update_ok[OF F1] by blast
  note u = ok_update[OF upd[unfolded return_def]]
  have FH: "F \<noteq> ?H" using F(3) by auto
  have H1: "vt_lookup (tenv env1) ?H = None"
  proof (rule ccontr)
    assume "vt_lookup (tenv env1) ?H \<noteq> None"
    then obtain b where "vt_lookup (tenv env) ?H = Some b" using g(1) by auto
    from bbelowD[OF e(5) this] show False by simp
  qed
  have H': "vt_lookup (tenv env') ?H = None" using H1 FH u(2) by simp
  have vu: "vars ?u = {(?H, Hty)}" by (simp add: H)
  have cl: "closed ?u"
    by (rule closed_abs_list) (use ks in \<open>simp add: H loose_bvar_app_Var ilength_eq\<close>)
  have ei1: "einv A K env1" by (rule einv_genvar[OF gv ei])
  have ei': "einv A K env'"
  proof (rule einv_update[OF ei1 upd[unfolded return_def] _ cl])
    fix y U assume "(y, U) \<in> vars ?u"
    with vu have "y = ?H" by simp
    then show "(F, y) \<notin> (dep env1)\<^sup>*" using not_dep_unbound[OF H1 FH] by simp
  next
    show "snd F \<le> maxidx env1" using F(3) g(3) by simp
  next
    have "btvars (map (\<lambda>i. bs ! nat_of_integer i) xs) \<subseteq> btvars bs" by (rule btvars_nths[OF xs])
    then show "tvars Fty \<union> ttvars ?u \<subseteq> tvars_env (tyenv env1) \<union> A"
      using tv by (auto simp: ttvars_abs_list H g(2))
  qed
  have ext1: "extends env env1" by (rule extends_genvar[OF gv])
  have ext': "extends env1 env'" by (rule extends_update[OF upd[unfolded return_def]])
  have pr: "prunes env env' X"
  proof (rule prunes_trans[OF prunes_genvar[OF gv] _ ext' ext1])
    show "prunes env1 env' X"
      by (rule prunes_update[OF upd[unfolded return_def], of "map (\<lambda>i. bs ! nat_of_integer i) xs" ?H Hty ks])
        (use einvD[OF ei1] einvD[OF ei'] cl H' in \<open>simp_all add: H app_apps\<close>)
  qed
  have Fin: "F \<in> fst ` (X \<union> evars env1)" using F(2) evars_genvar[OF gv] by (metis fst_conv image_eqI)
  have "card (ubv env' X) \<le> card (ubv env1 X)"
    by (rule card_ubv_update(2)[OF fin upd[unfolded return_def] Fin, of ?H Hty]) (use vu in simp)
  then have card: "card (ubv env' X) \<le> card (ubv env X)" by (simp add: ubv_genvar[OF gv])
  have nb: "newb env env'"
    by (rule newb_update[OF upd[unfolded return_def] _ newb_genvar[OF gv]]) (use vu in simp)
  show ?thesis using mk upd ei' u(2,3) g(2) extends_trans[OF ext1 ext'] pr card nb by auto
qed


subsection \<open>Flex-flex problems with the same head\<close>

lemma flexflex1_term:
  assumes ei: "einv A K env" and wi: "winv env X" and fin: "finite X"
    and F: "vt_lookup (tenv env) F = None" "(F, Fty) \<in> X \<union> evars env" "(F, Gty) \<in> X \<union> evars env"
    and tyF: "e \<turnstile> inst (tnorm_inst (tyenv env)) (app (Var F Fty) is) : T"
    and tyG: "e \<turnstile> inst (tnorm_inst (tyenv env)) (app (Var F Gty) js) : T"
    and lF: "\<not> loose_bvar (app (Var F Fty) is) (ilength bs)"
    and tv: "tvars Fty \<subseteq> tvars_env (tyenv env) \<union> A" "btvars bs \<subseteq> tvars_env (tyenv env) \<union> A"
    and nl: "is \<noteq> js \<Longrightarrow> F \<notin> loose"
  shows "\<exists>env'. flexflex1 env bs F Fty is js = return env' \<and> einv A K env' \<and> tyenv env' = tyenv env \<and>
    extends env env' \<and> prunes env env' X \<and> card (ubv env' X) \<le> card (ubv env X)"
proof (cases "is = js")
  case True
  then show ?thesis using ei by (auto simp: flexflex1_def intro: prunes_same)
next
  case False
  let ?\<theta> = "tyenv env" let ?\<rho> = "tnorm_inst ?\<theta>"
  note e = einvD[OF ei] and r0 = einv_rho0[OF ei]
  have vi: "vinv ?\<rho> env X" using winvD[OF wi r0] by blast
  from tyF obtain F1: "tsubst ?\<rho> Fty = map e is \<Rrightarrow> T" and is0: "\<forall>i\<in>set is. 0 \<le> i" by (rule typing_appE)
  from tyG obtain G1: "tsubst ?\<rho> Gty = map e js \<Rrightarrow> T" by (rule typing_appE)
  have "tsubst ?\<rho> Fty = tsubst ?\<rho> Gty" using vi F(2,3) nl[OF False] unfolding vinv_def by (blast dest: vconsD)
  with F1 G1 have "length (map e is) = length (map e js)" using funs_eq_length by metis
  then obtain ks where ks: "mk_ff_list is js = return ks" using mk_ff_list_ok by force
  have ks': "\<forall>k\<in>set ks. 0 \<le> k \<and> k < ilength (map e is)"
    using ok_mk_ff_list(2)[OF ks[unfolded return_def]] by (simp add: ilength_eq)
  have tc: "tcons ?\<theta> Fty" by (rule tinv_tcons[OF e(2) tv(1)])
  obtain Hty where tg: "type_of_G env Fty (ilength (map e is)) ks = return Hty"
    using type_of_G_ok[OF e(6,7) tc _ ks'] F1 by force
  have tvH: "tvars Hty \<subseteq> tvars_env ?\<theta> \<union> A"
    by (rule type_of_G_tvars[OF tg[unfolded return_def] e(1) tv(1)])
  obtain env1 H where gv: "genvar (fst F) env Hty = (env1, H)" by force
  have xs: "\<forall>i\<in>set is. 0 \<le> i \<and> i < ilength bs" using is0 app_Bounds_less[OF lF] by blast
  have Fb: "snd F \<le> maxidx env" using vi F(2) unfolding vinv_def by (blast dest: belowD)
  from bind_new_term[OF ei fin F(1,2) Fb gv xs ks'[simplified ilength_eq length_map, folded ilength_eq] tv tvH]
  obtain env' where r: "(mk_hnf bs is H ks \<bind> (\<lambda>t. update (F, Fty) t env1)) = return env'"
    and post: "einv A K env'" "tyenv env' = tyenv env" "extends env env'" "prunes env env' X"
      "card (ubv env' X) \<le> card (ubv env X)"
    by blast
  have "flexflex1 env bs F Fty is js = return env'"
    using False ks tg gv r by (simp add: flexflex1_def mk_new_hnf_def ilength_eq)
  with post show ?thesis by blast
qed

text \<open>Otherwise the result binds the variable:\<close>

lemma flexflex1_binds:
  assumes "ok (flexflex1 env bs F Fty is js) env'" "is \<noteq> js"
  shows "vt_lookup (tenv env') F \<noteq> None"
proof -
  from assms obtain ks where "ok (mk_new_hnf env bs is F Fty ks) env'"
    by (auto simp: flexflex1_def)
  then obtain Gty where m: "ok (case genvar (fst F) env Gty of
      (env1, G) \<Rightarrow> mk_hnf bs is G ks \<bind> (\<lambda>t. update (F, Fty) t env1)) env'"
    by (auto simp: mk_new_hnf_def Let_def)
  obtain env1 G where g: "genvar (fst F) env Gty = (env1, G)" by force
  from m g obtain t where "ok (update (F, Fty) t env1) env'" by auto
  from ok_update(2)[OF this] show ?thesis by simp
qed

subsection \<open>Flex-flex problems with different heads\<close>

text \<open>A binding to a known unbound variable decreases the number of unbound variables:\<close>

lemma bind_old_term:
  assumes ei: "einv A K env" and fin: "finite X"
    and F: "vt_lookup (tenv env) F = None" "(F, Fty) \<in> X \<union> evars env" "snd F \<le> maxidx env"
    and V: "vt_lookup (tenv env) V = None" "V \<noteq> F" "(V, Vty) \<in> X \<union> evars env"
    and xs: "\<forall>i\<in>set xs. 0 \<le> i \<and> i < ilength bs" and ks: "\<forall>k\<in>set ks. 0 \<le> k \<and> k < ilength xs"
    and tv: "tvars Fty \<subseteq> tvars_env (tyenv env) \<union> A" "btvars bs \<subseteq> tvars_env (tyenv env) \<union> A"
      "tvars Vty \<subseteq> tvars_env (tyenv env) \<union> A"
  shows "\<exists>env'. (mkabs bs xs (app (Var V Vty) ks) \<bind> (\<lambda>t. update (F, Fty) t env)) = return env' \<and>
    einv A K env' \<and> tyenv env' = tyenv env \<and> extends env env' \<and> card (ubv env' X) < card (ubv env X)"
proof -
  let ?u = "abs_list (map (\<lambda>i. bs ! nat_of_integer i) xs) (app (Var V Vty) ks)"
  have mk: "mkabs bs xs (app (Var V Vty) ks) = return ?u" by (rule mkabs_ok[OF xs])
  obtain env' where upd: "update (F, Fty) ?u env = return env'" using update_ok[OF F(1)] by blast
  note u = ok_update[OF upd[unfolded return_def]]
  have vu: "vars ?u = {(V, Vty)}" by simp
  have cl: "closed ?u"
    by (rule closed_abs_list) (use ks in \<open>simp add: loose_bvar_app_Var ilength_eq\<close>)
  have ei': "einv A K env'"
  proof (rule einv_update[OF ei upd[unfolded return_def] _ cl F(3)])
    fix y U assume "(y, U) \<in> vars ?u"
    with vu have "y = V" by simp
    then show "(F, y) \<notin> (dep env)\<^sup>*" using not_dep_unbound[OF V(1)] V(2) by auto
  next
    have "btvars (map (\<lambda>i. bs ! nat_of_integer i) xs) \<subseteq> btvars bs" by (rule btvars_nths[OF xs])
    then show "tvars Fty \<union> ttvars ?u \<subseteq> tvars_env (tyenv env) \<union> A"
      using tv by (auto simp: ttvars_abs_list)
  qed
  have Fin: "F \<in> fst ` (X \<union> evars env)" using F(2) by (metis fst_conv image_eqI)
  have "card (ubv env' X) < card (ubv env X)"
    by (rule card_ubv_update(1)[OF fin upd[unfolded return_def] Fin]) (use vu V(3) in simp)
  then show ?thesis using mk upd ei' u(3) extends_update[OF upd[unfolded return_def]] by auto
qed

lemma ok_mapM_idx_return: "set ys \<subseteq> set xs \<Longrightarrow> mapM (idx xs) ys = return (map (bidx xs) ys)"
  using ok_mapM_idx_bidx[of xs ys "map (bidx xs) ys"] by (simp add: return_def)

lemma bidx_range: "set ys \<subseteq> set xs \<Longrightarrow> \<forall>k\<in>set (map (bidx xs) ys). 0 \<le> k \<and> k < ilength xs"
  using bidx_less by auto

lemma ff_term:
  assumes ei: "einv A K env" and wi: "winv env X" and fin: "finite X"
    and F: "vt_lookup (tenv env) F = None" "(F, Fty) \<in> X \<union> evars env"
    and G: "vt_lookup (tenv env) G = None" "(G, Gty) \<in> X \<union> evars env" "G \<noteq> F"
    and tyF: "e \<turnstile> inst (tnorm_inst (tyenv env)) (app (Var F Fty) is) : T"
    and tyG: "e \<turnstile> inst (tnorm_inst (tyenv env)) (app (Var G Gty) js) : T"
    and lF: "\<not> loose_bvar (app (Var F Fty) is) (ilength bs)"
    and lG: "\<not> loose_bvar (app (Var G Gty) js) (ilength bs)"
    and tv: "tvars Fty \<subseteq> tvars_env (tyenv env) \<union> A" "tvars Gty \<subseteq> tvars_env (tyenv env) \<union> A"
      "btvars bs \<subseteq> tvars_env (tyenv env) \<union> A"
  shows "\<exists>env'. ff env bs F Fty is G Gty js = return env' \<and> einv A K env' \<and> tyenv env' = tyenv env \<and>
    extends env env' \<and> card (ubv env' X) < card (ubv env X)"
proof -
  let ?\<theta> = "tyenv env" let ?\<rho> = "tnorm_inst ?\<theta>"
  note e = einvD[OF ei] and r0 = einv_rho0[OF ei]
  have vi: "vinv ?\<rho> env X" using winvD[OF wi r0] by blast
  from tyF obtain F1: "tsubst ?\<rho> Fty = map e is \<Rrightarrow> T" and is0: "\<forall>i\<in>set is. 0 \<le> i" by (rule typing_appE)
  from tyG obtain js0: "\<forall>i\<in>set js. 0 \<le> i" by (rule typing_appE)
  have xs: "\<forall>i\<in>set is. 0 \<le> i \<and> i < ilength bs" using is0 app_Bounds_less[OF lF] by blast
  have ys: "\<forall>i\<in>set js. 0 \<le> i \<and> i < ilength bs" using js0 app_Bounds_less[OF lG] by blast
  have Fb: "snd F \<le> maxidx env" using vi F(2) unfolding vinv_def by (blast dest: belowD)
  have Gb: "snd G \<le> maxidx env" using vi G(2) unfolding vinv_def by (blast dest: belowD)
  show ?thesis
  proof (cases "subset js is")
    case True
    then have sub: "set js \<subseteq> set is" by (auto simp: subset_def list_all_iff)
    from bind_old_term[OF ei fin F Fb G(1,3,2) xs bidx_range[OF sub] tv(1,3,2)]
    obtain env' where r: "(mkabs bs is (app (Var G Gty) (map (bidx is) js)) \<bind> (\<lambda>t. update (F, Fty) t env)) = return env'"
      and post: "einv A K env'" "tyenv env' = tyenv env" "extends env env'" "card (ubv env' X) < card (ubv env X)"
      by blast
    have "ff env bs F Fty is G Gty js = return env'"
      using True r by (simp add: ff_def ok_mapM_idx_return[OF sub])
    with post show ?thesis by blast
  next
    case False
    let ?ks = "inter js is"
    have subI: "set ?ks \<subseteq> set is" and subJ: "set ?ks \<subseteq> set js" by (auto simp: inter_def)
    have tc: "tcons ?\<theta> Fty" by (rule tinv_tcons[OF e(2) tv(1)])
    have ksF: "\<forall>k\<in>set (map (bidx is) ?ks). 0 \<le> k \<and> k < ilength (map e is)"
      using bidx_range[OF subI] by (simp add: ilength_eq)
    obtain Hty where tg: "type_of_G env Fty (ilength (map e is)) (map (bidx is) ?ks) = return Hty"
      using type_of_G_ok[OF e(6,7) tc _ ksF] F1 by force
    have tvH: "tvars Hty \<subseteq> tvars_env ?\<theta> \<union> A"
      by (rule type_of_G_tvars[OF tg[unfolded return_def] e(1) tv(1)])
    obtain env1 H where gv: "genvar (fst G) env Hty = (env1, H)" by force
    note g = genvar_simps[OF gv]
    from bind_new_term[OF ei fin F Fb gv xs bidx_range[OF subI] tv(1,3) tvH]
    obtain env2 where r1: "(mk_hnf bs is H (map (bidx is) ?ks) \<bind> (\<lambda>t. update (F, Fty) t env1)) = return env2"
      and p1: "einv A K env2" "tyenv env2 = tyenv env" "extends env env2" "card (ubv env2 X) \<le> card (ubv env X)"
      and lk: "vt_lookup (tenv env2) F = Some (Fty, abs_list (map (\<lambda>i. bs ! nat_of_integer i) is) (app H (map (bidx is) ?ks)))"
      by blast
    let ?H = "(fst G, maxidx env + 1)"
    have H: "H = Var ?H Hty" by (rule g(4))
    have Hin: "(?H, Hty) \<in> X \<union> evars env2" using evarsI2[OF lk] H by auto
    have ext2: "extends env env2" by (rule p1(3))
    have H2: "vt_lookup (tenv env2) ?H = None"
    proof -
      have "vt_lookup (tenv env1) ?H = None"
      proof (rule ccontr)
        assume "vt_lookup (tenv env1) ?H \<noteq> None"
        then obtain b where "vt_lookup (tenv env) ?H = Some b" using g(1) by auto
        from bbelowD[OF e(5) this] show False by simp
      qed
      moreover have "?H \<noteq> F" using Fb by auto
      ultimately show ?thesis using r1 by (auto simp: mk_hnf_def mkabs_ok[OF xs] update_def update_new_def
          vt_defined_lookup split: env.splits if_splits)
    qed
    have G2: "vt_lookup (tenv env2) G = None"
      using r1 G(1,3) g(1) by (auto simp: mk_hnf_def mkabs_ok[OF xs] update_def update_new_def
          vt_defined_lookup split: env.splits if_splits)
    have "(G, Gty) \<in> X \<union> evars env2" using G(2) evars_extends[OF ext2] by blast
    moreover have "snd G \<le> maxidx env2" using Gb ext2 by (auto simp: extends_def)
    moreover have "?H \<noteq> G" by (simp add: prod_eq_iff) (use Gb in simp)
    moreover have "tvars Gty \<subseteq> tvars_env (tyenv env2) \<union> A" "btvars bs \<subseteq> tvars_env (tyenv env2) \<union> A"
      "tvars Hty \<subseteq> tvars_env (tyenv env2) \<union> A"
      using tv tvH p1(2) by simp_all
    ultimately obtain env' where r2:
        "(mkabs bs js (app (Var ?H Hty) (map (bidx js) ?ks)) \<bind> (\<lambda>t. update (G, Gty) t env2)) = return env'"
      and p2: "einv A K env'" "tyenv env' = tyenv env2" "extends env2 env'" "card (ubv env' X) < card (ubv env2 X)"
      using bind_old_term[OF p1(1) fin G2 _ _ H2 _ Hin ys bidx_range[OF subJ]] by blast
    have "ff env bs F Fty is G Gty js = return env'"
      using False r1 r2 tg gv
      by (simp add: ff_def Let_def ok_mapM_idx_return[OF subI] ok_mapM_idx_return[OF subJ] mk_hnf_def H
          mkabs_ok[OF xs] mkabs_ok[OF ys])
    with p1 p2 show ?thesis by (auto intro: extends_trans)
  qed
qed

lemma flexflex2_term:
  assumes ei: "einv A K env" and wi: "winv env X" and fin: "finite X"
    and F: "vt_lookup (tenv env) F = None" "(F, Fty) \<in> X \<union> evars env"
    and G: "vt_lookup (tenv env) G = None" "(G, Gty) \<in> X \<union> evars env" "G \<noteq> F"
    and tyF: "e \<turnstile> inst (tnorm_inst (tyenv env)) (app (Var F Fty) is) : T"
    and tyG: "e \<turnstile> inst (tnorm_inst (tyenv env)) (app (Var G Gty) js) : T"
    and lF: "\<not> loose_bvar (app (Var F Fty) is) (ilength bs)"
    and lG: "\<not> loose_bvar (app (Var G Gty) js) (ilength bs)"
    and tv: "tvars Fty \<subseteq> tvars_env (tyenv env) \<union> A" "tvars Gty \<subseteq> tvars_env (tyenv env) \<union> A"
      "btvars bs \<subseteq> tvars_env (tyenv env) \<union> A"
  shows "\<exists>env'. flexflex2 env bs F Fty is G Gty js = return env' \<and> einv A K env' \<and> tyenv env' = tyenv env \<and>
    extends env env' \<and> card (ubv env' X) < card (ubv env X)"
proof (cases "indexname_less G F")
  case True
  then show ?thesis using ff_term[OF ei wi fin F G tyF tyG lF lG tv] by (simp add: flexflex2_def)
next
  case False
  then show ?thesis using ff_term[OF ei wi fin G(1,2) F G(3)[symmetric] tyG tyF lG lF tv(2,1,3)]
    by (simp add: flexflex2_def)
qed

end

subsection \<open>Without loose names\<close>

context pure_sig
begin

lemma flexflex1_term:
  assumes ei: "einv A K env" and wi: "winv env X" and fin: "finite X"
    and F: "vt_lookup (tenv env) F = None" "(F, Fty) \<in> X \<union> evars env" "(F, Gty) \<in> X \<union> evars env"
    and tyF: "e \<turnstile> inst (tnorm_inst (tyenv env)) (app (Var F Fty) is) : T"
    and tyG: "e \<turnstile> inst (tnorm_inst (tyenv env)) (app (Var F Gty) js) : T"
    and lF: "\<not> loose_bvar (app (Var F Fty) is) (ilength bs)"
    and tv: "tvars Fty \<subseteq> tvars_env (tyenv env) \<union> A" "btvars bs \<subseteq> tvars_env (tyenv env) \<union> A"
  shows "\<exists>env'. flexflex1 env bs F Fty is js = return env' \<and> einv A K env' \<and> tyenv env' = tyenv env \<and>
    extends env env' \<and> prunes env env' X \<and> card (ubv env' X) \<le> card (ubv env X)"
  by (rule flexflex1_term[OF assms]) simp

end

end

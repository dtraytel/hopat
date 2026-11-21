section \<open>New Variables and Bindings Keep the Invariant\<close>

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

end

end

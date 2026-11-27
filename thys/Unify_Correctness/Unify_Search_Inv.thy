section \<open>Invariants of the Search\<close>

theory Unify_Search_Inv
  imports Unify_Match_Termination Unify_Flexflex_Simpl Unify_Search_Sound Unify_Seq_Termination
begin

text \<open>
  The invariant of the nodes of the search, for its termination (theory
  \<open>Unify_Search_Termination\<close>, theorem \<open>hounifiers_cfin\<close>): the search of
  \<^const>\<open>hounifiers\<close> ends after finitely many unifiers: the depth of the search is bounded by \<^const>\<open>cfg_search_bound\<close>, each node simplifies
  its problem (\<^const>\<open>SIMPL\<close>, theorem @{thm [source] pure_sig_gen.SIMPL_dfd}) and enumerates finitely
  many new problems by \<^const>\<open>MATCH\<close> (theorem @{thm [source] pure_sig_gen.MATCH_fin_c}). A leaf
  without flex-rigid pairs returns a unifier after the treatment of its flex-flex pairs by
  \<^const>\<open>add_ffpair\<close>, which raises no exception on the flex-flex pairs of \<^const>\<open>SIMPL\<close>
  (theorem @{thm [source] pure_sig_gen.SIMPL_add_ffpair_ok}).

  The same induction gives the soundness of the search: the invariant gives the hypothesis of
  \<^const>\<open>MATCH\<close> (theorem \<open>sinv_MATCH_ok\<close> below), whose new problems are then steps
  from the problem of the node (theorem @{thm [source] pure_sig_gen.MATCH_sound}).
\<close>

context pure_sig_gen
begin

text \<open>The unifiers: the results of \<^const>\<open>add_ffpair\<close> on the flex-flex pairs of a simplified problem,
  with the type variables \<open>A0\<close> of the original problem \<open>env0\<close> among the known ones, and only type
  variables that are known in the original problem or new (\<^const>\<open>tnew\<close>).\<close>

definition rres :: "(indexname \<times> psort) set \<Rightarrow> env \<Rightarrow> elem \<Rightarrow> bool" where
  "rres A0 env0 x \<longleftrightarrow> (\<exists>env' tps. x = El_R env' tps \<and> (\<exists>A K X env ffs. finite X \<and> finite K \<and> A0 \<subseteq> A \<and>
    tnew A0 env0 A env \<and>
    sinv A K X env ffs \<and> (\<forall>dp\<in>set ffs. ff_shape env dp) \<and> okW (foldrW (add_ffpair alg) ffs (env, [])) (env', tps) \<and>
    finv A K env env' \<and> (\<forall>(t, u)\<in>set tps. ttvars t \<union> ttvars u \<subseteq> tvars_env (tyenv env) \<union> A) \<and>
    (\<forall>(t, u)\<in>set tps. flexb env t \<and> flexb env u)))"

lemma resW_handleW_bindW_ok: "okW m x \<Longrightarrow> resW (handleW (bindW m f) h) r \<longleftrightarrow> resW (handleW (f x) h) r"
  by (rule resW_cong_handleW) (simp_all add: resW_bindW_ok)

lemma resW_handleW_whenW: "resW (handleW (bindW (whenW b (emit e)) (\<lambda>_. m)) h) r \<longleftrightarrow> resW (handleW m h) r"
  by (rule resW_cong_handleW) (simp_all add: resW_whenW_emit)

lemma resW_handleW_emit: "resW (handleW (bindW (emit e) (\<lambda>_. m)) h) r \<longleftrightarrow> resW (handleW m h) r"
  by (rule resW_cong_handleW) (simp_all add: resW_emit)

lemma resW_handleW_bindW_err:
  assumes "m = Some (evs, Err e)"
  shows "resW (handleW (bindW m f) h) r \<longleftrightarrow> resW (h e) r"
proof -
  have "bindW m f = Some (evs, Err e)" using assms by (simp add: bindW_def)
  then show ?thesis by (rule resW_handleW_err)
qed

text \<open>
  A node of the search: the simplified problem either has no flex-rigid pair, and the treatment of
  its flex-flex pairs gives a unifier, or the assignments of \<^const>\<open>MATCH\<close> to its first flex-rigid
  pair continue the search. Without loose names this is the evaluation of the node by
  \<^const>\<open>pull\<close>; with loose names it is a statement on the elements whose environment binds no
  loose name, and such an element comes from a simplified problem whose environment binds none.
\<close>

text \<open>
  A node of the search at depth \<open>td\<close>, followed by a finite enumeration, for a problem that is a
  step from the problem \<open>dps0\<close> of the root:
\<close>

text \<open>
  The search terminates with finitely many unifiers, each of which is a step from the input pairs
  to its flex-flex pairs. With loose names, this holds for the unifiers whose environment binds no
  loose name.
\<close>

end


end

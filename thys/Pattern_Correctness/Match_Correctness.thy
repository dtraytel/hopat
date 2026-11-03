section \<open>Correctness of Matching\<close>

theory Match_Correctness
  imports Match_Pattern
begin

context pure_sig
begin

text \<open>
  The final results on \<open>Pattern.match\<close> (\<^const>\<open>match\<close>) and \<open>Pattern.first_order_match\<close>
  (\<^const>\<open>first_order_match\<close>): they terminate; a result extends the environment and instantiates
  the pattern to a term equivalent to the object (@{thm [source] match_sound},
  @{thm [source] first_order_match_sound}); and on well-typed inputs they fail only with
  \<open>Match\<close>; and they find a matcher whenever one exists (@{thm [source] match_complete} for
  higher-order patterns against \<open>\<beta>\<close>-normal objects, @{thm [source] first_order_match_complete}
  for \<open>\<alpha>\<close>-equivalent instances). A matching environment \<open>(tye, te)\<close> instantiates the
  pattern by \<^const>\<open>minst\<close>; the object is not instantiated.
\<close>

theorem match_terminates: "\<exists>r. match alg pt ob env = Some r"
  by (rule match_term)

theorem first_order_match_terminates: "\<exists>r. first_order_match alg pt ob env = Some r"
  by (rule first_order_match_term)

text \<open>
  Well-typed inputs: the pattern and the object are closed and typed, each variable of the
  pattern has a unique type, also in the term environment, each type variable of the pattern has
  a unique sort, also in the type environment, and the bindings are closed.
\<close>

theorem match_exn:
  assumes "match alg pt ob env = Some r"
    and "closed pt" "closed ob" "e \<turnstile> pt : pT" "e \<turnstile> ob : oT"
    and "scons (ptvs pt)" "tsorts (fst env) (ptvs pt)"
    and "vfun (vars pt)" "vagree (snd env) (vars pt)" "bclosed (snd env)"
  shows "(\<exists>env'. r = Ok env') \<or> r = Err Match"
proof -
  have wp: "\<forall>T\<in>typs pt. wft ar T" using typing_typs_cert[OF assms(4)] by (auto simp: cert_wft)
  have wo: "\<forall>T\<in>typs ob. wft ar T" using typing_typs_cert[OF assms(5)] by (auto simp: cert_wft)
  have wpT: "wft ar pT" using typing_cert_closed[OF assms(4,2)] by (rule cert_wft)
  have woT: "wft ar oT" using typing_cert_closed[OF assms(5,3)] by (rule cert_wft)
  have E: "{i. 0 \<le> i \<and> loose_bvar1 pt i} = {}" using assms(2) by (simp add: closed_iff_loose_bvar1)
  have "tvars pT \<subseteq> ptvs pt \<union> (\<Union>i\<in>{i. 0 \<le> i \<and> loose_bvar1 pt i}. tvars (e i))"
    by (rule typing_tvars[OF assms(4)])
  then have tv: "tvars pT \<subseteq> ptvs pt" unfolding E by simp
  have m0: "match alg pt ob env = typ_match_m alg pT oT (fst env) \<bind> (\<lambda>iTs.
      handle (mtch alg [] pt ob (iTs, snd env))
        (\<lambda>e. case e of Pattern \<Rightarrow> first_order_match alg pt ob (iTs, snd env) | _ \<Rightarrow> raise e))"
    by (simp add: match_def Let_def fastype_of_closed[OF assms(4,2)] fastype_of_closed[OF assms(5,3)]
      return_def)
  from typ_match_m_exn[OF wpT woT tv assms(6,7)] show ?thesis
  proof (elim disjE exE conjE)
    fix iTs' assume tm: "typ_match_m alg pT oT (fst env) = Some (Ok iTs')" and ts': "tsorts iTs' (ptvs pt)"
    obtain rm where m: "mtch alg [] pt ob (iTs', snd env) = Some rm" using mtch_term by blast
    have "(\<exists>env'. rm = Ok env' \<and> tsorts (fst env') (ptvs pt) \<and> vagree (snd env') (vars pt) \<and>
        bclosed (snd env')) \<or> (\<exists>ex. rm = Err ex \<and> (ex = Match \<or> ex = Pattern))"
      by (rule mtch_exn[OF m refl typing_nbounds[OF assms(4)] _ wp wo order.refl assms(6) _ order.refl
        assms(8)]) (use assms(2,9,10) ts' in \<open>simp_all add: closed_def\<close>)
    then show ?thesis
    proof (elim disjE exE conjE)
      fix env' assume "rm = Ok env'"
      with assms(1) m0 tm m show ?thesis by (auto simp del: ok_typ_match_m)
    next
      fix ex assume "rm = Err ex" "ex = Match"
      with assms(1) m0 tm m show ?thesis by (simp del: ok_typ_match_m add: raise_def)
    next
      fix ex assume rm: "rm = Err ex" and "ex = Pattern"
      then have rm': "rm = Err Pattern" by simp
      obtain rf where f: "fo_mtch alg False (iTs', snd env) pt ob = Some rf" using fo_mtch_term by blast
      have "(\<exists>env'. rf = Ok env' \<and> tsorts (fst env') (ptvs pt) \<and> vagree (snd env') (vars pt)) \<or> rf = Err Match"
        by (rule fo_mtch_exn[OF f refl wp assms(5) _ order.refl assms(6) _ order.refl assms(8)])
          (use assms(3,9) ts' in simp_all)
      moreover have "r = rf"
        using assms(1) m0 tm m rm' f by (simp del: ok_typ_match_m add: first_order_match_def)
      ultimately show ?thesis by auto
    qed
  next
    assume "typ_match_m alg pT oT (fst env) = Some (Err Match)"
    with assms(1) m0 show ?thesis by (simp del: ok_typ_match_m)
  qed
qed

theorem first_order_match_exn:
  assumes "first_order_match alg pt ob env = Some r"
    and "\<forall>T\<in>typs pt. wft ar T" "closed ob" "e \<turnstile> ob : oT"
    and "scons (ptvs pt)" "tsorts (fst env) (ptvs pt)"
    and "vfun (vars pt)" "vagree (snd env) (vars pt)"
  shows "(\<exists>env'. r = Ok env') \<or> r = Err Match"
proof -
  have f: "fo_mtch alg False env pt ob = Some r" using assms(1) by (simp add: first_order_match_def)
  have "(\<exists>env'. r = Ok env' \<and> tsorts (fst env') (ptvs pt) \<and> vagree (snd env') (vars pt)) \<or> r = Err Match"
    by (rule fo_mtch_exn[OF f refl assms(2,4) _ order.refl assms(5,6) order.refl assms(7,8)])
      (use assms(3) in simp)
  then show ?thesis by auto
qed

text \<open>Completeness for the patterns recognized by \<open>Pattern.pattern\<close> without \<open>\<beta>\<close>-redexes:\<close>

corollary match_complete_pattern:
  assumes "closed pt" "closed ob" "e \<turnstile> pt : pT" "e \<turnstile> ob : oT"
    and "pattern pt" "no_redex pt" "no_redex ob"
    and "scons (ptvs pt)" "vfun (vars pt)"
    and "tagrees (fst env) \<rho> (ptvs pt)" "\<forall>(x, T)\<in>vars pt. vt_lookup (snd env) x = None"
    and "cert_inst \<rho>" "wt_subst \<sigma>" "tsubst \<rho> pT = oT" "ap \<rho> \<sigma> pt \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ob"
  shows "\<exists>env'. match alg pt ob env = Some (Ok env')"
  by (rule match_complete[OF assms(1-4) pattern_ppat[OF assms(5,6)] assms(7-15)])

end

end

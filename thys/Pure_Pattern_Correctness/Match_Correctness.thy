section \<open>Correctness of Matching\<close>

theory Match_Correctness
  imports Match_Exceptions
begin

text \<open>
  The final results on \<open>Pattern.match\<close> (\<^const>\<open>match\<close>): it terminates; a result is a
  matcher; on well-typed inputs it fails only with \<open>Match\<close>; and it finds a matcher of a
  linear higher-order pattern against an object without \<open>\<beta>\<close>-redexes whenever one exists.
  A matching environment \<open>(tye, te)\<close> instantiates the pattern by \<^const>\<open>minst\<close>; the object is
  not instantiated.
\<close>

declare sup_apply[simp del]

subsection \<open>Types of terms\<close>

lemma has_type_tvars: "has_type W Ts t T \<Longrightarrow> tvars T \<subseteq> tvs t \<union> \<Union> (tvars ` set Ts)"
proof (induction t arbitrary: Ts T)
  case (Bound i)
  then have "T \<in> set Ts" by (auto simp: has_type_Bound_iff)
  then show ?case by auto
next
  case (Abs x T0 u)
  from Abs.prems obtain U where "T = T0 \<rightarrow>\<^sub>T U" "has_type W (T0 # Ts) u U"
    by (auto elim: has_type_elims)
  with Abs.IH[of "T0 # Ts" U] show ?case by auto
next
  case (App s u)
  from App.prems obtain T' where "has_type W Ts s (T' \<rightarrow>\<^sub>T T)" by (auto elim: has_type_elims)
  with App.IH(1)[of Ts "T' \<rightarrow>\<^sub>T T"] show ?case by auto
qed (auto elim: has_type_elims)

lemma has_type_vtys: "has_type W Ts t T \<Longrightarrow> vtys t \<subseteq> {(x, W x) | x. True}"
  by (induction rule: has_type.induct) auto

lemma has_type_ctys: "has_type W Ts t T \<Longrightarrow> ctys t \<subseteq> tys t"
  by (induction rule: has_type.induct) auto

lemma fastype_of_closed: "has_type W [] t T \<Longrightarrow> fastype_of t = return T"
  using fastype_of_typed[of W "[]" t] by (simp add: fastype_of_def)

context wf_algebra
begin

subsection \<open>Main results\<close>

theorem match_terminates: "\<exists>r. match alg pt ob env = Some r"
  by (rule match_term)

text \<open>Soundness: see @{thm match_sound}.\<close>

text \<open>
  Well-typed inputs: the pattern and the object are closed and typed (with the types \<open>W x\<close> of
  their variables), all their types are well-formed, the type variables of the pattern have
  unique sorts, also in the type environment, and the term environment binds closed terms with
  the types given by \<open>W\<close>.
\<close>

definition wt_input :: "(indexname \<Rightarrow> ptyp) \<Rightarrow> pterm \<Rightarrow> pterm \<Rightarrow> match_env \<Rightarrow> bool" where
  "wt_input W pt ob env \<longleftrightarrow> (\<exists>pT. has_type W [] pt pT) \<and> (\<exists>oT. has_type W [] ob oT) \<and>
    (\<forall>T\<in>tys pt \<union> tys ob. wft ar T) \<and> scons (tvs pt) \<and> tsorts (fst env) (tvs pt) \<and>
    (\<forall>x U u. vt_lookup (snd env) x = Some (U, u) \<longrightarrow> U = W x) \<and> mte_ok (snd env)"

theorem match_exn:
  assumes "wt_input W pt ob env" "match alg pt ob env = Some r"
  shows "(\<exists>env'. r = Ok env') \<or> r = Err Match"
proof -
  from assms(1) obtain pT oT where tp: "has_type W [] pt pT" and to: "has_type W [] ob oT"
    and w: "\<forall>T\<in>tys pt \<union> tys ob. wft ar T" and sc: "scons (tvs pt)" and ts: "tsorts (fst env) (tvs pt)"
    and ag: "\<forall>x U u. vt_lookup (snd env) x = Some (U, u) \<longrightarrow> U = W x" and mok: "mte_ok (snd env)"
    by (auto simp: wt_input_def)
  let ?V = "{(x, W x) | x. True}"
  have vf: "vfun ?V" by (auto simp: vfun_def)
  have va: "vagree (snd env) ?V" using ag by (auto simp: vagree_def)
  have wp: "wft ar pT" using has_type_wft[OF tp] w by auto
  have wo: "wft ar oT" using has_type_wft[OF to] w by auto
  have tv: "tvars pT \<subseteq> tvs pt" using has_type_tvars[OF tp] by simp
  have m0: "match alg pt ob env = typ_match_m alg pT oT (fst env) \<bind> (\<lambda>iTs.
      handle (mtch alg [] pt ob (iTs, snd env))
        (\<lambda>e. case e of Pattern \<Rightarrow> first_order_match alg pt ob (iTs, snd env) | _ \<Rightarrow> raise e))"
    by (simp add: match_def Let_def fastype_of_closed[OF tp] fastype_of_closed[OF to] return_def)
  from typ_match_m_exn[OF wp wo tv sc ts] show ?thesis
  proof (elim disjE exE conjE)
    fix iTs' assume tm: "typ_match_m alg pT oT (fst env) = Some (Ok iTs')" and ts': "tsorts iTs' (tvs pt)"
    obtain rm where m: "mtch alg [] pt ob (iTs', snd env) = Some rm" using mtch_term by blast
    have "(\<exists>env'. rm = Ok env' \<and> tsorts (fst env') (tvs pt) \<and> vagree (snd env') ?V \<and> mte_ok (snd env')) \<or>
        (\<exists>ex. rm = Err ex \<and> (ex = Match \<or> ex = Pattern \<and> \<not> (ppat pt \<and> rfree ob)))"
      by (rule mtch_exn[where A = "tvs pt" and V = ?V, OF m refl])
        (use tp to w sc ts' vf va mok has_type_vtys[OF tp] has_type_ctys[OF tp] has_type_ctys[OF to]
          has_type_closed[OF tp] in \<open>auto simp: has_type_proper\<close>)
    then show ?thesis
    proof (elim disjE exE conjE)
      fix env' assume "rm = Ok env'" "tsorts (fst env') (tvs pt)" "vagree (snd env') ?V" "mte_ok (snd env')"
      with assms(2) m0 tm m show ?thesis by (cases env') (auto simp del: ok_typ_match_m)
    next
      fix ex assume "rm = Err ex" "ex = Match"
      with assms(2) m0 tm m show ?thesis by (simp del: ok_typ_match_m add: raise_def)
    next
      fix ex assume rm: "rm = Err ex" and "ex = Pattern" "\<not> (ppat pt \<and> rfree ob)"
      then have rm': "rm = Err Pattern" by simp
      obtain rf where f: "fo_mtch alg False (iTs', snd env) pt ob = Some rf" using fo_mtch_term by blast
      have "(\<exists>env'. rf = Ok env' \<and> tsorts (fst env') (tvs pt) \<and> vagree (snd env') ?V) \<or> rf = Err Match"
        by (rule fo_mtch_exn[where A = "tvs pt" and V = ?V and W = W, OF f refl])
          (use to w sc ts' vf va has_type_vtys[OF tp] has_type_closed[OF to] in auto)
      moreover have "r = rf"
        using assms(2) m0 tm m rm' f by (simp del: ok_typ_match_m add: first_order_match_def)
      ultimately show ?thesis by auto
    qed
  next
    assume "typ_match_m alg pT oT (fst env) = Some (Err Match)"
    with assms(2) m0 show ?thesis by (simp del: ok_typ_match_m)
  qed
qed

theorem match_complete:
  assumes "wt_input W pt ob env" "has_type W [] pt pT" "has_type W [] ob oT"
    "ppat pt" "linear pt" "rfree ob"
    "tagrees (fst env) (mtinst tye) (tvs pt)" "\<forall>x\<in>vars pt. vt_lookup (snd env) x = None"
    "mte_ok te" "minst (tye, te) pt \<equiv>\<^sub>\<beta>\<^sub>\<eta> tr ob" "tsubst (mtinst tye) pT = oT"
  shows "\<exists>env'. match alg pt ob env = Some (Ok env')"
proof -
  from assms(1) have w: "\<forall>T\<in>tys pt \<union> tys ob. wft ar T" and sc: "scons (tvs pt)"
    by (auto simp: wt_input_def)
  let ?\<rho> = "mtinst tye"
  have wp: "wft ar pT" using has_type_wft[OF assms(2)] w by auto
  have wo: "wft ar oT" using has_type_wft[OF assms(3)] w by auto
  have tv: "tvars pT \<subseteq> tvs pt" using has_type_tvars[OF assms(2)] by simp
  have "tmatcher alg (fst env) ?\<rho> pT oT"
    using assms(11) tagrees_mono[OF assms(7) tv] by (simp add: tmatcher_tagrees)
  moreover have "scons (tvars pT)" using sc tv unfolding scons_def by blast
  ultimately obtain iTs' where tm: "typ_match alg pT oT (fst env) = return iTs'"
    and "textends (fst env) iTs'" "\<forall>(v, S)\<in>tvars pT. vt_lookup iTs' v = Some (S, ?\<rho> v S)"
    "\<forall>v. vt_lookup iTs' v \<noteq> None \<longrightarrow> vt_lookup (fst env) v \<noteq> None \<or> (\<exists>S. (v, S) \<in> tvars pT)"
    using typ_match_complete[OF wp wo] by blast
  then have "tmcomplete ?\<rho> pT (fst env) iTs'" by (simp add: tmcomplete_def)
  then have ag: "tagrees iTs' ?\<rho> (tvs pt)" by (rule tagrees_step[OF assms(7) sc tv])
  have "\<exists>env'. ok (mtch alg [] pt ob (iTs', snd env)) env' \<and> tagrees (fst env') ?\<rho> (tvs pt) \<and>
      (\<forall>x. vt_lookup (snd env') x \<noteq> None \<longrightarrow> vt_lookup (snd (iTs', snd env)) x \<noteq> None \<or> x \<in> vars pt)"
    by (rule mtch_complete[where A = "tvs pt"])
      (use assms(2-10) ag sc w has_type_ctys[OF assms(2)] has_type_ctys[OF assms(3)]
        has_type_closed[OF assms(2)] in \<open>auto simp: has_type_proper\<close>)
  then obtain env' where "ok (mtch alg [] pt ob (iTs', snd env)) env'" by blast
  moreover have "typ_match_m alg pT oT (fst env) = Some (Ok iTs')" using tm by (simp add: return_def)
  ultimately show ?thesis
    by (simp del: ok_typ_match_m add: match_def Let_def fastype_of_closed[OF assms(2)]
      fastype_of_closed[OF assms(3)] return_def)
qed

end

declare sup_apply[simp]

end

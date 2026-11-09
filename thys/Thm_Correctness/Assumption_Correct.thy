section \<open>Soundness of proof by an equivalent assumption\<close>

theory Assumption_Correct
  imports Rules_Correct "Pure_Thm.Pure_Assumption"
begin

lemma find_index_from_SomeD: "find_index_from P xs k = Some n \<Longrightarrow> \<exists>x\<in>set xs. P x"
  by (induction P xs k rule: find_index_from.induct) (auto split: if_splits)

context pure_valuation
begin

text \<open>A subgoal one of whose assumptions is equivalent to its conclusion holds:\<close>

lemma hb_list_forall_taut:
  assumes \<rho>: "cert_inst \<rho>" and \<sigma>: "gsubst \<sigma>" and bv: "bvals \<eta> (ienv \<rho> e) bv"
    and ty: "e \<turnstile> list_forall ps (list_implies As B) : propT" and A: "A \<in> set As" and c: "aeconv A B"
  shows "hb bv (ap \<rho> \<sigma> (list_forall ps (list_implies As B)))"
proof -
  from ty have cs: "\<forall>(a, T)\<in>set ps. cert_typ alg ar (all_type T) \<and> cert_typ alg ar T"
    and tX: "pushes e (map snd ps) \<turnstile> list_implies As B : propT"
    by (simp_all add: typing_list_forall)
  note tD = typing_list_impliesD[OF tX]
  let ?e = "pushes e (map snd ps)"
  have tA: "?e \<turnstile> A : propT" using tD A by blast
  have cv: "A \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> B" by (rule aeconv_conv[OF c]) (use tA tD in \<open>auto simp: wt_def\<close>)
  have "hb (vpushes bv us) (ap \<rho> \<sigma> (list_implies As B))" if us: "pvals \<rho> ps us" for us
  proof -
    note bv' = bvals_vpushes_p[OF us bv]
    note ta = typing_ap_inst[OF _ \<rho> gsubstD(1)[OF \<sigma>]]
    have "sem \<eta> \<xi> (vpushes bv us) (ap \<rho> \<sigma> A) = sem \<eta> \<xi> (vpushes bv us) (ap \<rho> \<sigma> B)"
      by (rule sem_conv[OF good ta[OF tA] ta[OF tD[THEN conjunct2]] conv_ap[OF cv \<rho> gsubstD(1)[OF \<sigma>]]])
        (rule bv')
    then show ?thesis
      using sem_list_implies[of "map (ap \<rho> \<sigma>) As" "vpushes bv us" "ap \<rho> \<sigma> B"] sem_ap_bool[OF \<rho> \<sigma> _ bv'] tD A
      by (auto simp: ap_list_implies)
  qed
  then show ?thesis using holds_list_forall[OF \<rho> \<sigma> bv tX cs] by simp
qed

end

lemma eq_assumption_ok:
  assumes "okT (eq_assumption i state) (n, th)"
  shows "\<exists>tpairs Bs Bi C params asms concl. okT (dest_state state i) (tpairs, Bs, Bi, C) \<and>
    assum_problems (-1) Bi = (params, asms, concl) \<and> (\<exists>a\<in>set asms. aeconv a concl) \<and>
    th = \<lparr>th_maxidx = th_maxidx state, th_tpairs = tpairs, th_prop = list_implies Bs C\<rparr>"
proof -
  obtain tpairs Bs Bi C where d: "okT (dest_state state i) (tpairs, Bs, Bi, C)" and
    r: "okT (case assum_problems (-1) Bi of (_, asms, concl) \<Rightarrow>
      (case find_index_from (\<lambda>asm. aeconv asm concl) asms 0 of
        None \<Rightarrow> raiseW (THM (STR ''eq_assumption'') 0 State)
      | Some n \<Rightarrow> returnW (n + 1,
          \<lparr>th_maxidx = th_maxidx state, th_tpairs = tpairs, th_prop = list_implies Bs C\<rparr>))) (n, th)"
    using assms by (auto simp: eq_assumption_def)
  obtain params asms concl where a: "assum_problems (-1) Bi = (params, asms, concl)"
    by (cases "assum_problems (-1) Bi") auto
  with r obtain k where "find_index_from (\<lambda>asm. aeconv asm concl) asms 0 = Some k"
    and th: "th = \<lparr>th_maxidx = th_maxidx state, th_tpairs = tpairs, th_prop = list_implies Bs C\<rparr>"
    by (auto simp: returnW_def raiseW_def split: option.splits)
  with d a show ?thesis by (blast dest: find_index_from_SomeD)
qed

context pure_model
begin

theorem eq_assumption_valid:
  assumes ok: "okT (eq_assumption i state) (n, th)"
    and v: "valid Sh hs (th_tpairs state) (th_prop state)" and w: "wtp (th_prop state)"
  shows "valid Sh hs (th_tpairs th) (th_prop th)"
proof -
  from ok obtain tpairs Bs Bi C params asms concl where d: "okT (dest_state state i) (tpairs, Bs, Bi, C)"
    and ap: "assum_problems (-1) Bi = (params, asms, concl)" and f: "\<exists>a\<in>set asms. aeconv a concl"
    and th: "th = \<lparr>th_maxidx = th_maxidx state, th_tpairs = tpairs, th_prop = list_implies Bs C\<rparr>"
    using eq_assumption_ok[OF ok] by blast
  note ds = okT_dest_state[OF d]
  have P: "th_prop state = list_implies (Bs @ [Bi]) C"
    using list_implies_strip_prems[OF ds(2) wtpD(2)[OF w, of "\<lambda>_. propT"]] by simp
  have tP: "(\<lambda>_. propT) \<turnstile> list_implies (Bs @ [Bi]) C : propT" using wtpD(2)[OF w] P by simp
  note tD = typing_list_impliesD[OF tP]
  have tBi: "(\<lambda>_. propT) \<turnstile> Bi : propT" using tD by simp
  note st = assum_problems_struct[OF ap tBi]
  have tBi': "(\<lambda>_. propT) \<turnstile> list_forall (rev params) (list_implies asms concl) : propT"
    using tBi st(1) by simp
  have wBs: "wtp (list_implies Bs C)"
  proof (rule wtpI)
    show "closed (list_implies Bs C)" using wtpD(1)[OF w] P by (simp add: closed_def loose_bvar_list_implies)
    show "(\<lambda>_. propT) \<turnstile> list_implies Bs C : propT"
      using tD typing_list_implies_imp[OF tP] by (intro typing_list_impliesI) auto
  qed
  have "valid Sh hs tpairs (list_implies Bs C)"
  proof (rule validI)
    fix \<eta> \<xi> \<rho> \<sigma> assume sh: "\<And>S. S \<in> Sh \<Longrightarrow> sinh S" and g: "good \<eta> \<xi>" and \<rho>: "cinst \<rho>"
      and \<rho>i: "inh_inst \<rho>" and \<sigma>: "gsubst \<sigma>"
      and sol: "\<And>t u. (t, u) \<in> set tpairs \<Longrightarrow> ap \<rho> \<sigma> t \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma> u"
      and hh: "\<And>h. h \<in> set hs \<Longrightarrow> holds_at \<eta> \<xi> (ap \<rho> \<sigma> h)"
    interpret pure_valuation alg ar ctab umem ufun uapp ulam ubool utrue ufalse tcon cls cval \<eta> \<xi>
      by unfold_locales (rule g)
    note gt = gterm_ap_wtp[OF _ cinstD(2)[OF \<rho>] \<sigma>]
    have "holds (ap \<rho> \<sigma> (list_implies (Bs @ [Bi]) C))"
      using validD[OF v sh g \<rho> \<rho>i \<sigma>] sol hh ds(1) P by simp
    then have h0: "(\<forall>A\<in>set (Bs @ [Bi]). holds (ap \<rho> \<sigma> A)) \<longrightarrow> holds (ap \<rho> \<sigma> C)"
      using holds_list_implies[of "map (ap \<rho> \<sigma>) (Bs @ [Bi])" "ap \<rho> \<sigma> C"] gt[OF w] P
      by (simp add: ap_list_implies)
    obtain a where a: "a \<in> set asms" "aeconv a concl" using f by blast
    have "holds (ap \<rho> \<sigma> Bi)"
      using hb_list_forall_taut[OF cinstD(2)[OF \<rho>] \<sigma> bvals0 tBi' a] st(1) by (simp add: holds_hb)
    with h0 have "(\<forall>A\<in>set Bs. holds (ap \<rho> \<sigma> A)) \<longrightarrow> holds (ap \<rho> \<sigma> C)" by simp
    then show "holds_at \<eta> \<xi> (ap \<rho> \<sigma> (list_implies Bs C))"
      using holds_list_implies[of "map (ap \<rho> \<sigma>) Bs" "ap \<rho> \<sigma> C"] gt[OF wBs]
      by (simp add: ap_list_implies)
  qed
  then show ?thesis using ds(1) by (simp add: th)
qed

end

end

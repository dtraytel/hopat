section \<open>Soundness of the Search for Every Element of the Enumeration\<close>

theory Unify_Typed_Pattern
  imports Unify_Result_Base
begin

subsection \<open>The search, without termination\<close>

text \<open>
  The soundness of the search of \<^const>\<open>hounifiers\<close> in theory \<open>Unify_Search_Inv\<close> is proved
  together with its termination, by an invariant (\<open>sinv\<close>) whose preservation is proved
  only for results that bind no loose name. Here the search is treated by induction on the
  evaluation \<open>ev\<close>, which needs no termination: every element of the enumeration is a step
  from the input pairs (\<open>dstep\<close>, which makes no hypothesis on the names since the steps were
  generalized), for any invariant \<open>NI\<close> of the nodes of the search that gives the hypothesis
  \<open>MATCH_ok\<close> of \<^const>\<open>MATCH\<close> and is kept by a step of the search.
\<close>

context pure_sig_gen
begin

inductive sgood :: "(env \<Rightarrow> dpair list \<Rightarrow> bool) \<Rightarrow> cfg \<Rightarrow> env \<Rightarrow> dpair list \<Rightarrow> seq \<Rightarrow> bool"
  for NI cfg env0 dps0 where
  Empty: "sgood NI cfg env0 dps0 S_Empty"
| AddUnify: "dstep env0 dps0 env dps \<Longrightarrow> NI env dps \<Longrightarrow> sgood NI cfg env0 dps0 R \<Longrightarrow>
    sgood NI cfg env0 dps0 (S_AddUnify td env dps R)"
| ItRight: "(\<And>y. ev cfg xq y \<Longrightarrow> \<exists>env dps. y = El_E env dps \<and> dstep env0 dps0 env dps \<and> NI env dps) \<Longrightarrow>
    sgood NI cfg env0 dps0 R \<Longrightarrow> sgood NI cfg env0 dps0 (S_ItRight td xq R)"

inductive_cases sgood_AddUnifyE: "sgood NI cfg env0 dps0 (S_AddUnify td env dps R)"
inductive_cases sgood_ItRightE: "sgood NI cfg env0 dps0 (S_ItRight td xq R)"

lemma ev_sgood:
  assumes NI_match: "\<And>env dps env' ffs dp frs. NI env dps \<Longrightarrow>
      okW (SIMPL (cfg_alg cfg) env dps) (env', ffs, dp # frs) \<Longrightarrow> MATCH_ok env' dp"
    and NI_step: "\<And>env dps env' ffs dp frs ms env2 dps2. NI env dps \<Longrightarrow>
      okW (SIMPL (cfg_alg cfg) env dps) (env', ffs, dp # frs) \<Longrightarrow> okW (MATCH cfg env' dp (frs @ ffs)) ms \<Longrightarrow>
      ev cfg ms (El_E env2 dps2) \<Longrightarrow> NI env2 dps2"
  shows "ev cfg s x \<Longrightarrow> sgood NI cfg env0 dps0 s \<Longrightarrow> elem_ok (GR env0 dps0) x"
proof (induction rule: ev.induct)
  case (au_tail reseq x td env dps)
  from au_tail.prems show ?case by (rule sgood_AddUnifyE) (rule au_tail.IH)
next
  case (au_res env dps env' ffs r td reseq)
  from au_res.prems have d0: "dstep env0 dps0 env dps" by (rule sgood_AddUnifyE)
  obtain e1 tps where r: "r = (e1, tps)" by (cases r)
  have d1: "dstep env dps env' ffs" using SIMPL_sound[OF au_res.hyps(1)] by simp
  have d2: "dstep env' ffs e1 (tdps tps)" using foldrW_add_ffpair_sound[OF au_res.hyps(2)[unfolded r]] by simp
  from dstep_trans[OF dstep_trans[OF d0 d1] d2] show ?case by (simp add: r)
next
  case (au_match env dps env' ffs dp frs td ms reseq x)
  from au_match.prems obtain d0: "dstep env0 dps0 env dps" and ni: "NI env dps" and sR: "sgood NI cfg env0 dps0 reseq"
    by (rule sgood_AddUnifyE) blast
  have d1: "dstep env dps env' (dp # frs @ ffs)" using SIMPL_sound[OF au_match.hyps(1)] by simp
  have mo: "MATCH_ok env' dp" by (rule NI_match[OF ni au_match.hyps(1)])
  have sq: "seqinv (GE env' (dp # frs @ ffs)) ms" by (rule MATCH_sound[OF au_match.hyps(3) mo])
  have "sgood NI cfg env0 dps0 (S_ItRight (td + 1) ms reseq)"
  proof (rule sgood.ItRight[OF _ sR])
    fix y assume y: "ev cfg ms y"
    from ev_sound[OF y sq] obtain env2 dps2 where y2: "y = El_E env2 dps2" and d2: "dstep env' (dp # frs @ ffs) env2 dps2"
      by (cases y) auto
    have "NI env2 dps2" by (rule NI_step[OF ni au_match.hyps(1,3) y[unfolded y2]])
    with y2 dstep_trans[OF dstep_trans[OF d0 d1] d2]
    show "\<exists>env dps. y = El_E env dps \<and> dstep env0 dps0 env dps \<and> NI env dps" by blast
  qed
  then show ?case by (rule au_match.IH)
next
  case (ir_tail yq x td xq)
  from ir_tail.prems show ?case by (rule sgood_ItRightE) (rule ir_tail.IH)
next
  case (ir_head xq env dps td x yq)
  from ir_head.prems obtain h: "\<And>y. ev cfg xq y \<Longrightarrow> \<exists>env dps. y = El_E env dps \<and> dstep env0 dps0 env dps \<and> NI env dps"
    by (rule sgood_ItRightE) blast
  from h[OF ir_head.hyps(1)] have "dstep env0 dps0 env dps" "NI env dps" by auto
  then have "sgood NI cfg env0 dps0 (S_AddUnify td env dps S_Empty)" by (intro sgood.AddUnify sgood.Empty)
  from ir_head.IH(2)[OF this] show ?case .
qed (auto elim: sgood.cases)

theorem hounifiers_ev_sound:
  assumes NI0: "NI env (map (\<lambda>(t, u). (rb, t, u)) tus)"
    and NI_match: "\<And>env dps env' ffs dp frs. NI env dps \<Longrightarrow>
      okW (SIMPL (cfg_alg cfg) env dps) (env', ffs, dp # frs) \<Longrightarrow> MATCH_ok env' dp"
    and NI_step: "\<And>env dps env' ffs dp frs ms env2 dps2. NI env dps \<Longrightarrow>
      okW (SIMPL (cfg_alg cfg) env dps) (env', ffs, dp # frs) \<Longrightarrow> okW (MATCH cfg env' dp (frs @ ffs)) ms \<Longrightarrow>
      ev cfg ms (El_E env2 dps2) \<Longrightarrow> NI env2 dps2"
    and ev: "ev cfg (hounifiers rb env tus) x"
  shows "elem_ok (GR env (map (\<lambda>(t, u). (rb, t, u)) tus)) x"
proof (rule ev_sgood[OF NI_match NI_step ev[unfolded hounifiers_def]])
  show "sgood NI cfg env (map (\<lambda>(t, u). (rb, t, u)) tus) (S_AddUnify 1 env (map (\<lambda>(t, u). (rb, t, u)) tus) S_Empty)"
    by (intro sgood.AddUnify sgood.Empty dstep_refl NI0)
qed

end

end

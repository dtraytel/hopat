section \<open>The Elements of the Search Sequences\<close>

theory Unify_Search
  imports Unify_Simpl_Complete
begin

context csig
begin

text \<open>
  The lazy sequences of \<open>unify.ML\<close> are represented by the closures \<^typ>\<open>seq\<close> that
  \<^const>\<open>Pure_Unify.pull\<close> evaluates. We characterize their elements by an inductive relation
  \<open>ev cfg s x\<close>, with one rule per way in which \<^const>\<open>Pure_Unify.pull\<close> produces an element,
  independently of the order of the depth-first search. Every rule requires the computations
  on the way to the element to succeed. Completeness of the search then splits into two parts:
  the sequence of unifiers has a suitable element (theory \<open>Unify_Complete\<close>), and pulling a
  sequence until it is exhausted yields all its elements (below).
\<close>

inductive ev :: "cfg \<Rightarrow> seq \<Rightarrow> elem \<Rightarrow> bool" for cfg where
  single: "ev cfg (S_Single x) x"
| au_tail: "ev cfg reseq x \<Longrightarrow> ev cfg (S_AddUnify td env dps reseq) x"
| au_res: "okW (SIMPL (cfg_alg cfg) env dps) (env', ffs, []) \<Longrightarrow>
    okW (foldrW (add_ffpair (cfg_alg cfg)) ffs (env', [])) r \<Longrightarrow>
    ev cfg (S_AddUnify td env dps reseq) (El_R (fst r) (snd r))"
| au_match: "okW (SIMPL (cfg_alg cfg) env dps) (env', ffs, dp # frs) \<Longrightarrow> \<not> td > cfg_search_bound cfg \<Longrightarrow>
    okW (MATCH cfg env' dp (frs @ ffs)) ms \<Longrightarrow> ev cfg (S_ItRight (td + 1) ms reseq) x \<Longrightarrow>
    ev cfg (S_AddUnify td env dps reseq) x"
| ir_tail: "ev cfg yq x \<Longrightarrow> ev cfg (S_ItRight td xq yq) x"
| ir_head: "ev cfg xq (El_E env dps) \<Longrightarrow> (\<And>R. ev cfg (S_AddUnify td env dps R) x) \<Longrightarrow>
    ev cfg (S_ItRight td xq yq) x"
| new_dset: "ev cfg xq (El_C u' env' dps') \<Longrightarrow> okW (new_dset vT Ts u' env' dps') y \<Longrightarrow>
    ev cfg (S_MapNewDset vT Ts xq) y"
| map_abs: "ev cfg xq (El_C body' env' dps') \<Longrightarrow>
    ev cfg (S_MapAbs a T xq) (El_C (Abs a T body') env' dps')"
| proj: "make_args vname Ts env Us = (env', args) \<Longrightarrow>
    okW (SIMPL (cfg_alg cfg) env'
      ((rb, list_comb targ (map (\<lambda>arg. list_comb (head_of arg) targs) args), u) # dpairs))
      (env2, frigid, fflex) \<Longrightarrow>
    ev cfg (S_Proj vname env Ts Us targs rb u dpairs head targ tail)
      (El_C (list_comb head args) env2 (frigid @ fflex))"
| proj_tail: "ev cfg tail x \<Longrightarrow> ev cfg (S_Proj vname env Ts Us targs rb u dpairs head targ tail) x"
| map_join: "ev cfg xq (El_D uargs' env' dps') \<Longrightarrow>
    ev cfg (S_MapJoin uhead xq) (El_C (list_comb uhead uargs') env' dps')"
| maps: "ev cfg xq (El_D uargs env dps) \<Longrightarrow> okW (copycons cfg vname rb targs uarg uargs env dps) cs \<Longrightarrow>
    ev cfg cs x \<Longrightarrow> ev cfg (S_Maps vname rb targs uarg xq) x"
| append_l: "ev cfg xq x \<Longrightarrow> ev cfg (S_Append xq yq) x"
| append_r: "ev cfg yq x \<Longrightarrow> ev cfg (S_Append xq yq) x"
| map_cons: "ev cfg xq (El_C uarg' env' dps') \<Longrightarrow>
    ev cfg (S_MapCons uargs xq) (El_D (uarg' # uargs) env' dps')"

end

end

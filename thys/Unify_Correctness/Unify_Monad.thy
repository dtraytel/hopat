section \<open>Successful Computations of the Writer Monad\<close>

theory Unify_Monad
  imports "Pattern_Correctness.Env_Apply" "Pure_Unify.Pure_Unify"
begin

text \<open>
  A computation of type \<^typ>\<open>'a W\<close> \<^emph>\<open>succeeds\<close> with value \<open>x\<close> if it returns \<open>x\<close> after
  emitting some events. The events only drive tracing, so correctness abstracts over them.
\<close>

abbreviation okW :: "('a, event, 'e) WE \<Rightarrow> 'a \<Rightarrow> bool" where
  "okW m x \<equiv> (\<exists>evs. m = Some (evs, Ok x))"

lemma okW_simps [simp]:
  "okW (returnW x) y \<longleftrightarrow> y = x"
  "\<not> okW (raiseW e) y"
  "okW (emit ev) u \<longleftrightarrow> u = ()"
  "\<not> okW None y"
  by (auto simp: returnW_def raiseW_def emit_def)

lemma okW_bindW [simp]: "okW (bindW m f) y \<longleftrightarrow> (\<exists>x. okW m x \<and> okW (f x) y)"
  by (auto simp: bindW_def map_option_eq_Some split: option.splits xres.splits)

lemma okW_whenW: "okW (whenW b m) y \<longleftrightarrow> (if b then okW m y else y = ())"
  by (auto simp: whenW_def)

lemma okW_handleW:
  "okW (handleW m h) y \<longleftrightarrow> okW m y \<or> (\<exists>evs e. m = Some (evs, Err e) \<and> okW (h e) y)"
  by (auto simp: handleW_def map_option_eq_Some split: option.splits xres.splits)

lemma okW_liftM [simp]: "okW (liftM m) y \<longleftrightarrow> ok m y"
  by (auto simp: liftM_def split: option.splits xres.splits)

lemma okW_det: "okW m x \<Longrightarrow> okW m y \<Longrightarrow> x = y"
  by auto

lemma okW_foldrW_induct [consumes 1, case_names Nil Cons]:
  assumes "okW (foldrW f xs b) b'"
    and "\<And>b. P [] b b"
    and "\<And>x xs b b1 b'. okW (foldrW f xs b) b1 \<Longrightarrow> P xs b b1 \<Longrightarrow> okW (f x b1) b' \<Longrightarrow> P (x # xs) b b'"
  shows "P xs b b'"
  using assms(1) by (induction xs arbitrary: b') (auto intro: assms(2,3))

text \<open>The result of a computation, abstracting from the events:\<close>

definition resW :: "('a, event, 'e) WE \<Rightarrow> ('a, 'e) xres \<Rightarrow> bool" where
  "resW m r \<longleftrightarrow> (\<exists>evs. m = Some (evs, r))"

lemma resW_simps [simp]:
  "resW (returnW x) r \<longleftrightarrow> r = Ok x"
  "resW (raiseW e) r \<longleftrightarrow> r = Err e"
  "\<not> resW None r"
  "resW m (Ok x) \<longleftrightarrow> okW m x"
  by (auto simp: resW_def returnW_def raiseW_def)

lemma resW_bindW_ok: "okW m x \<Longrightarrow> resW (bindW m f) r \<longleftrightarrow> resW (f x) r"
  by (auto simp: resW_def bindW_def map_option_eq_Some)

lemma resW_handleW_ok: "okW m x \<Longrightarrow> resW (handleW m h) r \<longleftrightarrow> r = Ok x"
  by (auto simp: resW_def handleW_def)

lemma resW_handleW_err: "m = Some (evs, Err e) \<Longrightarrow> resW (handleW m h) r \<longleftrightarrow> resW (h e) r"
  by (auto simp: resW_def handleW_def map_option_eq_Some)

end

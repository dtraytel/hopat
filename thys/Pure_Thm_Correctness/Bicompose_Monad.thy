section \<open>Reasoning about the Monad of \<open>bicompose_aux\<close>\<close>

theory Bicompose_Monad
  imports
    "Pure_Unify_Correctness.Unify_Poly_Unifiers"
    "Pure_Unify_Correctness.Unify_Poly_Smash"
    "Pure_Thm.Pure_Bicompose"
begin

context csig
begin

text \<open>
  As for the writer monad of \<open>unify.ML\<close> (\<^const>\<open>okW\<close>), a computation of type \<^typ>\<open>'a T\<close>
  \<^emph>\<open>succeeds\<close> with value \<open>x\<close> if it returns \<open>x\<close> after emitting some events.
\<close>

abbreviation okT :: "'a T \<Rightarrow> 'a \<Rightarrow> bool" where
  "okT m x \<equiv> (\<exists>evs. m = Some (evs, TOk x))"

lemma okT_returnT[simp]: "okT (returnT x) y \<longleftrightarrow> y = x"
  by (auto simp: returnT_def)

lemma okT_raiseT[simp]: "\<not> okT (raiseT e) y"
  by (auto simp: raiseT_def)

lemma okT_emitT[simp]: "okT (emitT e) y \<longleftrightarrow> y = ()"
  by (auto simp: emitT_def)

lemma not_okT_None[simp]: "\<not> okT None y"
  by auto

lemma okT_bindT[simp]: "okT (bindT m f) y \<longleftrightarrow> (\<exists>x. okT m x \<and> okT (f x) y)"
  by (auto simp: bindT_def map_option_eq_Some split: option.splits tres.splits)

lemma okT_handleT:
  "okT (handleT m h) y \<longleftrightarrow> okT m y \<or> (\<exists>evs e. m = Some (evs, TErr e) \<and> okT (h e) y)"
  by (auto simp: handleT_def map_option_eq_Some split: option.splits tres.splits)

lemma okT_liftWT[simp]: "okT (liftWT m) y \<longleftrightarrow> okW m y"
  by (auto simp: liftWT_def split: option.splits ures.splits)

lemma okT_liftMT[simp]: "okT (liftMT m) y \<longleftrightarrow> ok m y"
  by (simp add: liftMT_def)

lemma okT_mapT: "okT (mapT f xs) ys \<longleftrightarrow> list_all2 (\<lambda>x y. okT (f x) y) xs ys"
proof (induction xs arbitrary: ys)
  case (Cons x xs)
  then show ?case by (cases ys) auto
qed auto

lemma okT_det: "okT m x \<Longrightarrow> okT m y \<Longrightarrow> x = y"
  by auto

text \<open>A handler that only catches one exception.\<close>

lemma okT_handle_only:
  assumes "okT (handleT m (\<lambda>e. if e = e0 then h else raiseT e)) y"
  shows "okT m y \<or> (\<exists>evs. m = Some (evs, TErr e0)) \<and> okT h y"
  using assms by (auto simp: okT_handleT raiseT_def split: if_splits)

lemma okT_bind_opt:
  assumes "okT (bindT m (\<lambda>r. case r of None \<Rightarrow> A | Some (y, q) \<Rightarrow> B y q)) z"
  shows "(okT m None \<and> okT A z) \<or> (\<exists>y q. okT m (Some (y, q)) \<and> okT (B y q) z)"
proof -
  from assms obtain r where "okT m r" "okT (case r of None \<Rightarrow> A | Some (y, q) \<Rightarrow> B y q) z"
    by auto
  then show ?thesis by (cases r) auto
qed

end

end

section \<open>Successful Computations\<close>

theory Pattern_Monad
  imports "Pure_Pattern.Pure_Pattern" "Pure_Lambda.Pure_Lambda"
begin

text \<open>Soundness is about successful computations: \<open>ok m x\<close> says that \<open>m\<close> returns \<open>x\<close>.\<close>

abbreviation ok :: "'a M \<Rightarrow> 'a \<Rightarrow> bool" where
  "ok m x \<equiv> m = Some (Ok x)"

lemma ok_simps [simp]:
  "ok (return x) y \<longleftrightarrow> x = y"
  "\<not> ok (raise e) y"
  "\<not> ok None y"
  by (simp_all add: return_def raise_def)

lemma ok_bindM [simp]: "ok (bindM m f) y \<longleftrightarrow> (\<exists>x. ok m x \<and> ok (f x) y)"
  by (auto simp: bindM_def split: option.splits res.splits)

lemma ok_handle: "ok (handle m h) y \<longleftrightarrow> ok m y \<or> (\<exists>e. m = Some (Err e) \<and> ok (h e) y)"
  by (auto simp: handle_def split: option.splits res.splits)

lemma ok_mapM: "ok (mapM f xs) ys \<longleftrightarrow> list_all2 (\<lambda>x y. ok (f x) y) xs ys"
  by (induction xs arbitrary: ys) (auto simp: list_all2_Cons1)

lemma ok_zip_eq: "ok (zip_eq xs ys) ps \<longleftrightarrow> length xs = length ys \<and> ps = zip xs ys"
  by (induction xs ys arbitrary: ps rule: zip_eq.induct) auto

lemma ok_update_new: "ok (update_new (k, x) t) t' \<longleftrightarrow> vt_lookup t k = None \<and> t' = vt_update (k, x) t"
  by (auto simp: update_new_def vt_defined_lookup)

lemma ok_type_lookup:
  "ok (type_lookup \<theta> v S) r \<longleftrightarrow>
    (case vt_lookup \<theta> v of None \<Rightarrow> r = None | Some (S', U) \<Rightarrow> S' = S \<and> r = Some U)"
  by (auto simp: type_lookup_def tvar_clash_def split: option.splits)

lemma ok_foldM_induct [consumes 1, case_names Nil Cons]:
  assumes "ok (foldM f xs b) b'"
    and "\<And>b. P [] b b"
    and "\<And>x xs b b1 b'. ok (f x b) b1 \<Longrightarrow> ok (foldM f xs b1) b' \<Longrightarrow> P xs b1 b' \<Longrightarrow> P (x # xs) b b'"
  shows "P xs b b'"
  using assms(1) by (induction xs arbitrary: b) (auto intro: assms(2,3))


subsection \<open>Integers of ML\<close>

lemma ilength_eq: "ilength xs = integer_of_nat (length xs)"
  by (induction xs) (simp_all add: integer_eq_iff)

lemma ilength_nonneg [simp]: "0 \<le> ilength xs"
  by (simp add: ilength_eq integer_arith)

lemma ok_nth: "ok (nth xs i) x \<longleftrightarrow> 0 \<le> i \<and> i < ilength xs \<and> x = xs ! nat_of_integer i"
proof (induction xs arbitrary: i)
  case (Cons y ys)
  show ?case
  proof (cases "i \<le> 0")
    case False
    then have "nat_of_integer i = Suc (nat_of_integer (i - 1))"
      by (simp add: integer_arith nat_of_integer.rep_eq)
    with False Cons.IH[of "i - 1"] show ?thesis by (auto simp: integer_arith)
  qed (use ilength_nonneg[of ys] in \<open>auto simp: integer_arith\<close>)
qed simp


subsection \<open>Computations that do not raise \<open>Pattern\<close>\<close>

definition pok :: "('a \<Rightarrow> bool) \<Rightarrow> 'a M \<Rightarrow> bool" where
  "pok P m \<longleftrightarrow> (case m of Some (Ok x) \<Rightarrow> P x | Some (Err e) \<Rightarrow> e \<noteq> Pattern | None \<Rightarrow> True)"

abbreviation no_pat :: "'a M \<Rightarrow> bool" where
  "no_pat m \<equiv> pok (\<lambda>_. True) m"

lemma pok_simps [simp]:
  "pok P (return x) \<longleftrightarrow> P x" "pok P (raise e) \<longleftrightarrow> e \<noteq> Pattern" "pok P None"
  "pok P (Some (Ok x)) \<longleftrightarrow> P x" "pok P (Some (Err e)) \<longleftrightarrow> e \<noteq> Pattern"
  by (simp_all add: pok_def return_def raise_def)

lemma pok_IH: "(\<And>r. m = Some r \<Longrightarrow> pok P (Some r)) \<Longrightarrow> pok P m"
  by (cases m) auto

lemma pok_bindM: "pok P m \<Longrightarrow> (\<And>x. ok m x \<Longrightarrow> P x \<Longrightarrow> pok Q (f x)) \<Longrightarrow> pok Q (bindM m f)"
  by (auto simp: pok_def bindM_def split: option.splits res.splits)

lemma pok_handle:
  "pok P m \<Longrightarrow> (\<And>e. m = Some (Err e) \<Longrightarrow> e \<noteq> Pattern \<Longrightarrow> pok P (h e)) \<Longrightarrow> pok P (handle m h)"
  by (auto simp: pok_def handle_def split: option.splits res.splits)

lemma pok_mono: "pok P m \<Longrightarrow> (\<And>x. ok m x \<Longrightarrow> P x \<Longrightarrow> Q x) \<Longrightarrow> pok Q m"
  by (auto simp: pok_def split: option.splits res.splits)

lemma pok_okI: "no_pat m \<Longrightarrow> (\<And>x. ok m x \<Longrightarrow> P x) \<Longrightarrow> pok P m"
  by (auto simp: pok_def split: option.splits res.splits)

lemma pok_mapM: "(\<And>x. x \<in> set xs \<Longrightarrow> no_pat (f x)) \<Longrightarrow> no_pat (mapM f xs)"
  by (induction xs) (auto intro!: pok_bindM)

lemma pok_foldM:
  "P b \<Longrightarrow> (\<And>x b. x \<in> set xs \<Longrightarrow> P b \<Longrightarrow> pok P (f x b)) \<Longrightarrow> pok P (foldM f xs b)"
  by (induction xs arbitrary: b) (auto intro!: pok_bindM)

lemma pok_allM: "(\<And>x. x \<in> set xs \<Longrightarrow> no_pat (f x)) \<Longrightarrow> no_pat (allM f xs)"
  by (induction xs) (auto intro!: pok_bindM)

lemma pok_existsM: "(\<And>x. x \<in> set xs \<Longrightarrow> no_pat (f x)) \<Longrightarrow> no_pat (existsM f xs)"
  by (induction xs) (auto intro!: pok_bindM)

lemma pok_conj: "pok P m \<Longrightarrow> (\<And>x. ok m x \<Longrightarrow> Q x) \<Longrightarrow> pok (\<lambda>x. P x \<and> Q x) m"
  by (auto simp: pok_def split: option.splits res.splits)

lemma existsM_FalseD: "existsM P xs = Some (Ok False) \<Longrightarrow> x \<in> set xs \<Longrightarrow> P x = Some (Ok False)"
  by (induction xs) (auto simp: bindM_def return_def split: option.splits res.splits if_splits)


end

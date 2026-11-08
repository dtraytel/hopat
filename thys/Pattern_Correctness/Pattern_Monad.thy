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
  by (auto simp: bindM_def split: option.splits xres.splits)

lemma ok_handle: "ok (handle m h) y \<longleftrightarrow> ok m y \<or> (\<exists>e. m = Some (Err e) \<and> ok (h e) y)"
  by (auto simp: handle_def split: option.splits xres.splits)

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


subsection \<open>Computations that do not raise given exceptions\<close>

definition xok :: "(exn \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> 'a M \<Rightarrow> bool" where
  "xok E P m \<longleftrightarrow> (case m of Some (Ok x) \<Rightarrow> P x | Some (Err e) \<Rightarrow> \<not> E e | None \<Rightarrow> True)"

text \<open>Computations that do not raise \<open>Pattern\<close>:\<close>

abbreviation pok :: "('a \<Rightarrow> bool) \<Rightarrow> 'a M \<Rightarrow> bool" where
  "pok P m \<equiv> xok (\<lambda>e. e = Pattern) P m"

abbreviation no_pat :: "'a M \<Rightarrow> bool" where
  "no_pat m \<equiv> pok (\<lambda>_. True) m"

lemma xok_simps [simp]:
  "xok E P (return x) \<longleftrightarrow> P x" "xok E P (raise e) \<longleftrightarrow> \<not> E e" "xok E P None"
  "xok E P (Some (Ok x)) \<longleftrightarrow> P x" "xok E P (Some (Err e)) \<longleftrightarrow> \<not> E e"
  by (simp_all add: xok_def return_def raise_def)

lemma xok_IH: "(\<And>r. m = Some r \<Longrightarrow> xok E P (Some r)) \<Longrightarrow> xok E P m"
  by (cases m) auto

lemma xok_bindM: "xok E P m \<Longrightarrow> (\<And>x. ok m x \<Longrightarrow> P x \<Longrightarrow> xok E Q (f x)) \<Longrightarrow> xok E Q (bindM m f)"
  by (auto simp: xok_def bindM_def split: option.splits xres.splits)

lemma xok_handle:
  "xok E P m \<Longrightarrow> (\<And>e. m = Some (Err e) \<Longrightarrow> \<not> E e \<Longrightarrow> xok E P (h e)) \<Longrightarrow> xok E P (handle m h)"
  by (auto simp: xok_def handle_def split: option.splits xres.splits)

lemma xok_mono: "xok E P m \<Longrightarrow> (\<And>x. ok m x \<Longrightarrow> P x \<Longrightarrow> Q x) \<Longrightarrow> xok E Q m"
  by (auto simp: xok_def split: option.splits xres.splits)

lemma xok_okI: "xok E (\<lambda>_. True) m \<Longrightarrow> (\<And>x. ok m x \<Longrightarrow> P x) \<Longrightarrow> xok E P m"
  by (auto simp: xok_def split: option.splits xres.splits)

lemma xok_mapM: "(\<And>x. x \<in> set xs \<Longrightarrow> xok E (\<lambda>_. True) (f x)) \<Longrightarrow> xok E (\<lambda>_. True) (mapM f xs)"
  by (induction xs) (auto intro!: xok_bindM)

lemma xok_foldM:
  "P b \<Longrightarrow> (\<And>x b. x \<in> set xs \<Longrightarrow> P b \<Longrightarrow> xok E P (f x b)) \<Longrightarrow> xok E P (foldM f xs b)"
  by (induction xs arbitrary: b) (auto intro!: xok_bindM)

lemma xok_allM: "(\<And>x. x \<in> set xs \<Longrightarrow> xok E (\<lambda>_. True) (f x)) \<Longrightarrow> xok E (\<lambda>_. True) (allM f xs)"
  by (induction xs) (auto intro!: xok_bindM)

lemma xok_existsM: "(\<And>x. x \<in> set xs \<Longrightarrow> xok E (\<lambda>_. True) (f x)) \<Longrightarrow> xok E (\<lambda>_. True) (existsM f xs)"
  by (induction xs) (auto intro!: xok_bindM)

lemma xok_conj: "xok E P m \<Longrightarrow> (\<And>x. ok m x \<Longrightarrow> Q x) \<Longrightarrow> xok E (\<lambda>x. P x \<and> Q x) m"
  by (auto simp: xok_def split: option.splits xres.splits)

lemma existsM_FalseD: "existsM P xs = Some (Ok False) \<Longrightarrow> x \<in> set xs \<Longrightarrow> P x = Some (Ok False)"
  by (induction xs) (auto simp: bindM_def return_def split: option.splits xres.splits if_splits)


lemma ok_lookup1:
  "ok (lookup1 te x T) r \<Longrightarrow>
    (r = None \<and> vt_lookup te x = None) \<or> (\<exists>u. r = Some u \<and> vt_lookup te x = Some (T, u))"
  by (auto simp: lookup1_def var_clash_def split: option.splits if_splits)

end

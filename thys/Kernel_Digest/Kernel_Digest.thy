section \<open>Digests of the theorems of HOL\<close>

theory Kernel_Digest
  imports "Pure_Pattern.Pure_Test_Support"
begin

text \<open>
  A test of a whole kernel: for every fact of \<open>Main\<close>, a hash value of its theorems in full
  (proposition with all types and sorts, flex-flex pairs, hypotheses, sort hypotheses, maximal
  index). The session exports one line per fact (\<^verbatim>\<open>kernel_digest\<close>) and prints the hash value of
  all lines. Two builds of HOL with different kernels (the patched \<^verbatim>\<open>thm.ML\<close> and the one with
  the generated code, see \<^verbatim>\<open>patches/test_generated\<close>) have the same theorems if the exports are
  equal.
\<close>

ML \<open>
local
  val thy = \<^theory>\<open>Main\<close>;
  val basis: LargeWord.word = 0wxcbf29ce484222325;
  fun hash s = LargeWord.toString (Exact.hash_string s basis);
  val thm: thm Exact.T = fn th =>
    Exact.triple Exact.term (Exact.list Exact.term) (Exact.pair (Exact.list Exact.sort) Exact.int)
      (Thm.full_prop_of th, Thm.hyps_of th, (Thm.shyps_of th, Thm.maxidx_of th));
  val facts = Global_Theory.all_thms_of thy true;
  val lines = facts |> map (fn (name, th) =>
    let val s = Exact.content thm th
    in Thm_Name.print name ^ " " ^ hash s ^ (if Exact.is_large s then " large" else "") end);
  val text = cat_lines lines;
in
  val _ = Export.export \<^theory> \<^path_binding>\<open>kernel_digest\<close> [XML.Text text];
  val _ = writeln ("Kernel digest: " ^ string_of_int (length lines) ^ " theorems, " ^
    string_of_int (length (filter (String.isSuffix " large") lines)) ^ " large, hash " ^ hash text);
end
\<close>

end

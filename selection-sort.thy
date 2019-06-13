theory "selection-sort"
  imports Main "HOL-Library.Multiset"
begin

lemma min_membership: "m = Min(set (x#xs)) \<Longrightarrow> m \<in> set (x#xs)"
proof(induct xs arbitrary: x m)
  case Nil
  then show ?case by simp
next
  case (Cons a xs)
  then show "m \<in> set (x # a # xs)"
  proof(cases "m = Min (set (a#xs))")
    case True
    have "m \<in> set (a# xs)" using Cons.hyps True by simp
    moreover have "m \<in> set (x # a # xs)" using calculation by auto
    then show "m \<in> set (x # a # xs)" by assumption
  next
    case False
    have "m \<in> {Min ({x} \<union> set (a # xs))}" by (metis Cons.prems insertCI insert_is_Un list.simps(15))
    moreover have "m \<notin> set (a # xs)" by (metis Cons.prems False List.finite_set Min_eqI Min_le insertI2 list.simps(15))
    moreover have "m \<in> {Min ({x})}" by (metis (mono_tags, lifting) List.finite_set Min_in calculation(1) calculation(2) insert_iff insert_is_Un list.simps(15) set_empty singleton_iff)
    moreover have "m \<in> {x}" using Min_singleton calculation by simp
    moreover have  "m \<in> set (x # a # xs)" using calculation by auto
    then show "m \<in> set (x # a # xs)" by assumption
  qed
qed

lemma remove_member: "y \<in> set (x#xs) \<Longrightarrow> length (remove1 y (x#xs)) < length (x#xs)"
proof(induct xs arbitrary: y x)
  case Nil
  then show ?case by simp
next
  case (Cons a xs)
  then show "length (remove1 y (x # a # xs)) < length (x # a # xs)"
  proof(cases "y \<in> set (a # xs)")
    case True
    have "length (remove1 y (a # xs)) < length (a # xs)" using Cons.hyps True by simp
    moreover have "length (remove1 y (a # xs)) < length (x # a # xs)" using calculation by simp
    moreover have "length (remove1 y (x #a # xs)) < length (x # a # xs)" using calculation by simp
    then show "length (remove1 y (x # a # xs)) < length (x # a # xs)" by assumption
  next
    case False
    have "y \<in> {x} \<union> set (a # xs)" using Cons.prems by auto
    moreover have "y \<in> {x}" using False calculation by simp
    moreover have "length (remove1 y ([x])) < length ([x])" using calculation by simp
    moreover have "length (remove1 y ([x])) < length (x # a # xs)" using calculation by simp
    moreover have "length (remove1 y (x # a # xs)) < length (x # a # xs)" using calculation by simp
    then show "length (remove1 y (x # a # xs)) < length (x # a # xs)" by assumption
  qed
qed

(*no tail-recursive*)
function selection_sort:: "nat list \<Rightarrow> nat list" where
"selection_sort [] = []" |
"selection_sort (x#xs) = (let min = Min (set(x#xs)); rest = remove1 min (x#xs)  in min#selection_sort(rest))"
by pat_completeness auto
termination by (meson "termination" in_measure min_membership remove_member wf_measure)

value "selection_sort [2,4,10,0,0]"

theorem selection_sort_output_sorted: "sorted (selection_sort(xs))"
proof(induct xs rule:selection_sort.induct)
  case 1
  then show ?case by simp
next
  case (2 x xs)
  let ?min = "Min (set (x # xs))"
  let  ?rest = "remove1 ?min (x # xs)"
  have "sorted (selection_sort ?rest)" using "2.hyps" by simp
  moreover have "sorted (?min#selection_sort ?rest)" by (smt List.finite_set Min_antimono calculation selection_sort.elims selection_sort.simps(1) set_empty set_remove1_subset sorted1 sorted2)
  moreover have "sorted (?min#selection_sort ((x # xs)))" by (metis List.finite_set Min_le calculation(2) min_membership selection_sort.simps(2) sorted2)
  moreover have "sorted (selection_sort ((x # xs)))" using calculation(3) sorted.simps(2) by simp
  then show "sorted (selection_sort (x # xs))" by assumption
qed

lemma 100: "e \<in> set xs \<Longrightarrow> rest = remove1 e xs \<Longrightarrow> mset xs = mset rest + {#e#}"
proof(induct xs)
  case Nil
  then show ?case by simp
next
  case (Cons a xs)
  then show ?case by (metis add.right_neutral insert_DiffM mset_remove1 set_mset_mset union_mset_add_mset_right)
qed

theorem "mset (selection_sort(xs)) = mset xs"
proof(induct xs rule: selection_sort.induct)
case 1
then show ?case by simp
next
  case (2 x xs)
  then show ?case by (metis "100" add.right_neutral min_membership mset.simps(2) selection_sort.simps(2) union_mset_add_mset_right)
qed











(*tail-recursive version*)

lemma p_200 [simp]: "m = Max(set (x#xs)) \<Longrightarrow> m \<in> set (x#xs)"
proof(induct xs)
  case Nil
  then show ?case by simp
next
  case (Cons a xs)
  then show ?case using eq_Max_iff by blast
qed

function (sequential) tr_selection_sort:: "nat list \<Rightarrow> nat list \<Rightarrow> nat list" where
"tr_selection_sort [] accum = accum" |
"tr_selection_sort (xs) accum = (let m = Max (set(xs)) in tr_selection_sort(remove1 m (xs)) (m#accum))"
by pat_completeness auto
termination
apply(relation "measure (\<lambda>(xs,accum). size xs)")
apply simp
by (metis case_prod_conv in_measure p_200 remove_member)

value "tr_selection_sort [2,4,10,0,0] []"

theorem tr_ss_s: "sorted (ACCUM) \<Longrightarrow> \<forall>A e. A \<in> (set ACCUM) \<and> e \<in> set xs \<and> A \<le> e  \<Longrightarrow> sorted (tr_selection_sort xs ACCUM)"
proof(induct xs rule:tr_selection_sort.induct)
case (1 accum)
then show ?case by blast
next
case (2 v va accum)
  then show ?case by (simp add: sorted01)
qed

theorem tr_ss_permutation: "sorted (ACCUM) \<Longrightarrow> \<forall>A e. A \<in> (set ACCUM) \<and> e \<in> set xs \<and> A \<le> e  \<Longrightarrow> mset (tr_selection_sort xs ACCUM) = mset xs + mset ACCUM"
proof(induct xs arbitrary: ACCUM)
  case Nil
  then show ?case by simp
next
  case (Cons a xs)
  then show ?case by blast
qed



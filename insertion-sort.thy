theory "insertion-sort"
  imports Main "HOL-Library.Multiset"
begin

declare[[names_short]]

fun insert:: "nat \<Rightarrow> nat list \<Rightarrow> nat list" where
insert_Nil: "insert x [] = [x]" |
insert_Cons: "insert x (y#ys) = (if x \<le> y then (x#y#ys) else y#insert x ys)"

value "insert 1 [2,4,10]"

fun insert_sort:: "nat list \<Rightarrow> nat list" where
insert_sort_Nil : "insert_sort []  = []" |
insert_sort_Cons: "insert_sort (x#xs)  = insert x (insert_sort(xs))"

value "insert_sort [2,4,10,0,3]"

lemma sorted_accepts_insert : "\<lbrakk>sorted(y#ys); \<not> x \<le> y\<rbrakk> \<Longrightarrow> sorted (y#insert x ys)"
proof(induction ys arbitrary: y rule: sorted.induct)
  case 1
  then show ?case by auto
next
  case (2 x ys)
  then show ?case by (metis insert_Cons le_cases sorted2)
qed

lemma insert_output_sorted : "sorted(ys) \<Longrightarrow> sorted (insert x ys)"
proof (induct ys rule: insert.induct)
  case (1 x)
  then show ?case by simp
next
  case (2 x y ys)
  then show ?case
  proof(cases " x \<le> y")
    case True
    have "sorted (y#ys)" using "local.2.prems" by blast
    also have "sorted (x#y#ys)" using "local.2.prems" True sorted2 by blast
    then have "sorted (insert x (y # ys))"  by simp
    then show "sorted (insert x (y # ys))" by assumption
  next
    case False
    have "sorted ys" using "local.2.prems" List.linorder_class.sorted.simps(2) by blast
    also have "sorted (insert x ys)" by (simp add: "local.2.hyps" False calculation)
    moreover have "sorted (y#insert x ys)" using "local.2.prems" False sorted_accepts_insert by blast
    then have "sorted (insert x (y # ys))" by (simp add: False)
    then show "sorted (insert x (y # ys))" by assumption
  qed
qed

theorem insert_sort_output_sorted : "sorted(insert_sort(ys))"
proof (induct ys rule:insert_sort.induct)
  case 1
  have "sorted []" by simp
  also have "sorted (insert_sort [])" by simp
  then show ?case by assumption
next
  case (2 x xs)
  moreover have "sorted(insert x (insert_sort(xs)))" by (simp add: "local.2.hyps" insert_output_sorted)
  then have "sorted (insert_sort (x # xs))" by simp
  then show "sorted (insert_sort (x # xs))" by assumption
qed

lemma insert_is_permutation_of_input: "mset (insert x ys) = mset (x#ys)"
proof(induct ys arbitrary: x)
  case Nil
  then show ?case  by simp
next
  case (Cons a ys)
  then show ?case by simp
qed

theorem insert_sort_is_permutation_of_input: "mset (insert_sort xs) = mset xs" 
proof(induct xs rule: insert_sort.induct)
  case 1
  then show ?case by simp
next
  case (2 x xs)
  then show ?case by (simp add: insert_is_permutation_of_input)
qed

fun insert_sort_tail:: "nat list \<Rightarrow> nat list \<Rightarrow> nat list" where
insert_sort_tail_Nil : "insert_sort_tail [] accum  = accum" |
insert_sort_tail_Cons: "insert_sort_tail (x#xs) accum  = insert_sort_tail (xs) (insert x accum)"

value "insert_sort_tail ([2,4,10]) ([])"

theorem insert_sort_tail_output_sorted: "sorted(ACCUM) \<Longrightarrow> sorted(insert_sort_tail xs ACCUM)"
proof(induct xs arbitrary:ACCUM)
  case Nil
  then show ?case by simp
next
  case (Cons a xs)
  then show ?case by (simp add: insert_output_sorted)
qed

theorem insert_sort_tail_is_permutation_of_input: "mset (insert_sort_tail xs ACCUM) = mset (xs@ACCUM)"
proof(induct xs arbitrary:ACCUM)
  case Nil
  then show ?case by simp
next
  case (Cons a xs)
  then show ?case by (simp add: insert_is_permutation_of_input)
qed
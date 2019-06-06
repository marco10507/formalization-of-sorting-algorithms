theory "insertion-sort-tail-recursive"
  imports Main "HOL-Library.Multiset"
begin

declare[[names_short]]

fun insert_a:: "nat \<Rightarrow> nat list \<Rightarrow> nat list" where
insert_a_Nil: "insert_a x [] = [x]" |
insert_a_Cons: "insert_a x (y#ys) = (if x \<le> y then (x#y#ys) else y#insert_a x ys)"

value "insert_a 1 [2,4,10]"

fun insert_sort:: "nat list \<Rightarrow> nat list" where
insert_sort_Nil : "insert_sort []  = []" |
insert_sort_Cons: "insert_sort (x#xs)  = insert_a x (insert_sort(xs))"

value "insert_sort [2,4,10,0,3]"

lemma p_1 : "sorted(ys) \<Longrightarrow> sorted (insert_a x ys)"
proof (induct ys rule: insert_a.induct)
  case (1 x)
  then show ?case by simp
next
  case (2 x y ys)
  then show ?case
  proof(cases " x \<le> y")
    case True
    have "sorted (y#ys)" using "local.2.prems" by blast
    also have "sorted (x#y#ys)" using "local.2.prems" True sorted2 by blast
    then have "sorted (insert_a x (y # ys))"  by simp
    then show "sorted (insert_a x (y # ys))" by assumption
  next
    case False
    have "sorted ys" using "local.2.prems" List.linorder_class.sorted.simps(2) by blast
    also have "sorted (insert_a x ys)" by (simp add: "local.2.hyps" False calculation)
    moreover have "sorted (y#insert_a x ys)" by (smt "insertion-sort-tail-recursive.insert_a.elims" "local.2.prems" False calculation(2) le_cases sorted2)
    then have "sorted (insert_a x (y # ys))" by (simp add: False)
    then show "sorted (insert_a x (y # ys))" by assumption
  qed
qed

theorem p_2 : "sorted(insert_sort(ys))"
proof (induct ys rule:insert_sort.induct)
  case 1
  have "sorted []"
    by simp
  also have "sorted (insert_sort [])"
    by simp
  then show ?case by assumption
next
  case (2 x xs)
  have "sorted (insert_sort (x # xs)) = sorted(insert_a x (insert_sort(xs)))"
    by simp
  also have "sorted(insert_a x (insert_sort(xs)))"
    by (simp add: "local.2.hyps" p_1)
  finally show "sorted (insert_sort (x # xs))" by this
qed

lemma p_20: "mset (insert_a x ys) = mset (x#ys)"
proof(induct ys arbitrary: x)
  case Nil
  then show ?case  by simp
next
  case (Cons a ys)
  then show ?case by simp
qed

theorem p_30: "mset (insert_sort xs) = mset xs" 
proof(induct xs rule: insert_sort.induct)
  case 1
  then show ?case by simp
next
  case (2 x xs)
  then show ?case by (simp add: p_20)
qed

fun insert_sort_tail:: "nat list \<Rightarrow> nat list \<Rightarrow> nat list" where
insert_sort_tail_Nil : "insert_sort_tail [] accum  = accum" |
insert_sort_tail_Cons: "insert_sort_tail (x#xs) accum  = insert_sort_tail (xs) (insert_a x accum)"

value "insert_sort_tail ([2,4,10]) ([])"

theorem p_60: "sorted(ACCUM) \<Longrightarrow> sorted(insert_sort_tail xs ACCUM)"
proof(induct xs arbitrary:ACCUM)
  case Nil
  then show ?case by simp
next
  case (Cons a xs)
  then show ?case by (simp add: p_1)
qed

lemma p_70: "mset (insert_sort_tail xs ACCUM) = mset (xs@ACCUM)"
proof(induct xs arbitrary:ACCUM)
  case Nil
  then show ?case by simp
next
  case (Cons a xs)
  then show ?case by (simp add: p_20)
qed
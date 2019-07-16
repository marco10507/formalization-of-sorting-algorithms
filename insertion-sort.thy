theory "insertion-sort"
  imports Main "HOL-Library.Multiset"
begin

declare[[names_short]]

fun insert:: "nat \<Rightarrow> nat list \<Rightarrow> nat list" where
insert_Nil: "insert x [] = [x]" |
insert_Cons: "insert x (y#ys) = (if x < y then (x#y#ys) else y#insert x ys)"

value "insert 1 [2,4,10]"

fun insert_sort:: "nat list \<Rightarrow> nat list" where
insert_sort_Nil : "insert_sort []  = []" |
insert_sort_Cons: "insert_sort (x#xs)  = insert x (insert_sort(xs))"

value "insert_sort [2,4,10,0,3]"

lemma sorted3 : "\<lbrakk>sorted(y#ys); \<not> x < y\<rbrakk> \<Longrightarrow> sorted (y#insert x ys) = (y \<le> x \<and> sorted(insert x ys))"
proof(induction ys arbitrary: y rule: sorted.induct)
  case 1
  then show ?case by auto
next
  case (2 x ys)
  then show ?case using insert_Cons leI less_imp_le_nat sorted2 by metis
qed

thm  insert.induct

lemma insert_output_sorted : "sorted(ys) \<Longrightarrow> sorted (insert y ys)"
proof (induct ys rule: insert.induct)
  case (1 x)
  then show ?case by simp
next
  case (2 x y ys)
  then show ?case
  proof (cases "x < y")
    case True
    then show "sorted (insert x (y#ys))"
    proof (simp only: True insert_Cons if_True [[simp_trace]])
      show "sorted (x # y # ys)"
      proof(simp)
        from True have "x \<le> y" by simp
        moreover from "local.2.prems" calculation have "(\<forall>xa\<in>set ys. x \<le> xa)" by auto
        moreover from "local.2.prems"(1) have "(\<forall>x\<in>set ys. y \<le> x)" by simp
        moreover from "local.2.prems"(1) have "sorted ys" by simp
        ultimately show "x \<le> y \<and> (\<forall>xa\<in>set ys. x \<le> xa) \<and> (\<forall>x\<in>set ys. y \<le> x) \<and> sorted ys" by blast
      qed
    qed
  next
    case False
    then show "sorted (insert x (y # ys))"
      thm  "2.hyps"
    proof(simp only:False insert_Cons if_False [[simp_trace]])
      show "sorted (y # insert x ys)"
      proof(simp  del:List.linorder_class.sorted.simps add: False sorted3 "local.2.prems")
        from False have "y \<le> x" by simp
        moreover from "local.2.hyps" "local.2.prems" False have "sorted (insert x ys)"  by simp
        ultimately show "y \<le> x \<and> sorted (insert x ys)" by blast
      qed
    qed
  qed
qed

theorem insert_sort_output_sorted : "sorted(insert_sort(ys))"
proof (induct ys rule:insert_sort.induct)
  case 1
  then show ?case by simp
next
  case (2 x xs)
  show "sorted (insert_sort (x # xs))"
  proof (simp only: insert_sort_Cons)
     from "local.2.hyps" and insert_output_sorted show "sorted (insert x (insert_sort xs))" by simp
  qed
qed

lemma insert_is_permutation_of_input: "mset (insert y ys) = mset (y#ys)"
proof(induct ys rule:insert.induct)
  case (1 x)
  show "mset (insert x []) = mset [x]" by simp
next
  case (2 x y ys)
  then show ?case
  proof (cases "x < y")
    case True
    then show "mset (insert x (y # ys)) = mset (x # y # ys)"  by simp
  next
    case False
    have "mset (insert x (y # ys)) = mset (y#insert x ys)" using False by simp
    also have "... = {#y#} + mset(insert x ys)" by simp
    also have "... = {#y#} + mset (x # ys)" using "local.2.hyps" False by simp
    also have "... = mset (x # y # ys)"  by simp
    finally show "mset (insert x (y # ys)) = mset (x # y # ys)" by this
  qed
qed

theorem insert_sort_is_permutation_of_input: "mset (insert_sort ys) = mset ys" 
proof(induct ys rule: insert_sort.induct)
  case 1
  then show "mset (insert_sort []) = mset []" by simp
next
  case (2 x xs)
  have "mset (insert_sort (x # xs)) = mset (insert x (insert_sort(xs)))" by simp
  also have "... =  mset(x#(insert_sort(xs)))" using  insert_is_permutation_of_input by simp
  also have "... =  {#x#} + mset(insert_sort(xs))" by simp
  also have "... =  {#x#} +  mset xs" using "local.2.hyps" by simp
  also have "... =  mset (x # xs)" using "local.2.hyps" by simp
  finally show "mset (insert_sort (x # xs)) = mset (x # xs)" by this
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
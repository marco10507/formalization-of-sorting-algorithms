theory "insertion-sort"
  imports Main "HOL-Library.Multiset"
begin

declare[[names_short]]

fun insert:: "nat \<Rightarrow> nat list \<Rightarrow> nat list" where
insert_Nil: "insert x [] = [x]" |
insert_Cons: "insert x (y#ys) = (if x < y then (x#y#ys) else y#insert x ys)"

value "insert 1 [2,4,10]"

fun insertion_sort:: "nat list \<Rightarrow> nat list" where
insertion_sort_Nil : "insertion_sort []  = []" |
insertion_sort_Cons: "insertion_sort (x#xs)  = insert x (insertion_sort(xs))"

value "insert_sort [2,4,10,0,3]"

lemma sorted3 : "\<lbrakk>sorted(y#ys); \<not> x < y\<rbrakk> \<Longrightarrow> sorted (y#insert x ys) = (y \<le> x \<and> sorted(insert x ys))"
proof(induction ys  rule: sorted.induct)
  case 1
  then show "sorted (y # insert x []) = (y \<le> x \<and> sorted (insert x []))" by auto
next
  case (2 x ys)
  then show ?case by (simp del:List.linorder_class.sorted.simps add:sorted2_simps)
qed

lemma insert_order: "sorted(ys) \<Longrightarrow> sorted (insert y ys)"
proof (induct ys  rule: insert.induct)
  case (1 x)
  then show "sorted (insert x [])" by simp
next
  case (2 x y ys)
  then show "sorted (insert x (y # ys))"
  proof (cases "x < y")
    case True
    then show "sorted (insert x (y#ys))"
    proof (simp only: True insert_Cons if_True)
      show "sorted (x # y # ys)"
      proof(simp)
        show "x \<le> y \<and> (\<forall>xa\<in>set ys. x \<le> xa) \<and> (\<forall>x\<in>set ys. y \<le> x) \<and> sorted ys"
        proof(intro conjI)
          show "x \<le> y" by (simp add: True le_less)
        next
          show "\<forall>xa\<in>set ys. x \<le> xa" using "local.2.prems" True by auto
        next
          show "(\<forall>x\<in>set ys. y \<le> x)" using "local.2.prems" List.linorder_class.sorted.simps(2) by blast
        next
          show "sorted ys" using "local.2.prems" List.linorder_class.sorted.simps(2) by blast
        qed
      qed
    qed
  next
    case False
    then show "sorted (insert x (y # ys))"
    proof(simp only:False insert_Cons if_False)
      show "sorted (y # insert x ys)"
      proof(simp  del:List.linorder_class.sorted.simps add: False sorted3 "local.2.prems")
        show "y \<le> x \<and> sorted (insert x ys)" 
        proof(rule conjI)
          show "y \<le> x" by (simp add: False leI)
        next
          have "sorted ys" using "local.2.prems" List.linorder_class.sorted.simps(2) by blast
          then show "sorted (insert x ys)" by (simp add: "local.2.hyps" False)
        qed
      qed
    qed
  qed
qed

theorem insertion_sort_order : "sorted(insertion_sort(ys))"
proof (induct ys rule:insertion_sort.induct)
  case 1
  then show "sorted (insertion_sort [])" by simp
next
  case (2 x xs)
  show "sorted (insertion_sort (x # xs))"
  proof (simp only: insertion_sort_Cons)
    show "sorted (insert x (insertion_sort xs))" by (simp only: "local.2.hyps" insert_order)
  qed
qed

lemma insert_permutation: "mset (insert y ys) = mset (y#ys)"
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

theorem insert_sort_permutation: "mset (insertion_sort ys) = mset ys"
proof(induct ys rule: insertion_sort.induct)
  case 1
  then show "mset (insertion_sort []) = mset []" by simp
next
  case (2 x xs)
  have "mset (insertion_sort (x # xs)) = mset (insert x (insertion_sort(xs)))" by simp
  also have "... =  mset(x#(insertion_sort(xs)))" using  insert_permutation by simp
  also have "... =  {#x#} + mset(insertion_sort(xs))" by simp
  also have "... =  {#x#} +  mset xs" using "local.2.hyps" by simp
  also have "... =  mset (x # xs)" using "local.2.hyps" by simp
  finally show "mset (insertion_sort (x # xs)) = mset (x # xs)" by this
qed

fun insertion_sort_tail:: "nat list \<Rightarrow> nat list \<Rightarrow> nat list" where
insertion_sort_tail_Nil : "insertion_sort_tail [] accum  = accum" |
insertion_sort_tail_Cons: "insertion_sort_tail (x#xs) accum  = insertion_sort_tail (xs) (insert x accum)"

value "insert_sort_tail ([2,4,10]) ([])"

theorem insert_sort_tail_order: "sorted(ACCUM) \<Longrightarrow> sorted(insertion_sort_tail xs ACCUM)"
proof(induct xs arbitrary:ACCUM)
  case Nil
  then show "sorted (insertion_sort_tail [] ACCUM)" by simp
next
  case (Cons a xs)
  then show "sorted (insertion_sort_tail (a # xs) ACCUM)" by (simp add: insert_order)
qed

theorem insertion_sort_tail_permutation: "mset (insertion_sort_tail xs ACCUM) = mset (xs@ACCUM)"
proof(induct xs arbitrary:ACCUM)
  case Nil
  then show "mset (insertion_sort_tail [] ACCUM) = mset ([] @ ACCUM)" by simp
next
  case (Cons a xs)
  then show ?case by (simp add: insert_permutation)
qed
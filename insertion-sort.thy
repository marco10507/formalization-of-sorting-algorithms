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


lemma sorted_accepts_insert : "\<lbrakk>sorted(y#ys); \<not> x < y\<rbrakk> \<Longrightarrow> sorted (y#insert x ys)"
proof(induction ys arbitrary: y rule: sorted.induct)
  case 1
  then show ?case by auto
next
  case (2 x ys)
  then show ?case  by (metis insert_Cons leI less_imp_le_nat sorted2)
qed

thm insert.induct

lemma insert_output_sorted : "sorted(ys) \<Longrightarrow> sorted (insert y ys)"
proof (induct ys rule: insert.induct)
  case (1 x)
  then show ?case by simp
next
  case (2 x y ys)
  then show ?case
  proof (cases "x < y" )
    case True
    {
      have "sorted (insert x (y # ys)) \<equiv> sorted (x#y#ys)"  by (simp add: True)
      also have "... \<equiv> ((\<forall>z \<in> set (y#ys). x \<le> z) \<and> sorted(y#ys))" using "local.2.prems" List.linorder_class.sorted.simps(2) by simp
      ultimately have "sorted (insert x (y # ys)) \<equiv> ((\<forall>z \<in> set (y#ys). x \<le> z) \<and> sorted(y#ys))" by simp
    }
    moreover have "((\<forall>z \<in> set (y#ys). x \<le> z)) \<and> (sorted(y#ys))"
    proof
      show "((\<forall>z \<in> set (y#ys). x \<le> z))" using "local.2.prems" True by auto
      show "(sorted(y#ys))" using "local.2.prems" by auto
    qed
    ultimately show "sorted (insert x (y # ys))" by simp
  next
    case False
    moreover{
      have "sorted (insert x (y # ys)) \<equiv> sorted (y#insert x (ys))" by (simp add: False)
    }

    moreover {
      have "sorted (y#insert x (ys))" using "local.2.prems" False sorted_accepts_insert by auto
    }

    ultimately show "sorted (insert x (y # ys))" by simp
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
  moreover{
    have "sorted (insert_sort (x # xs)) \<equiv> sorted(insert x (insert_sort(xs)))" by simp
  }

  moreover {
    have "sorted(insert x (insert_sort(xs)))" using  "local.2.hyps" insert_output_sorted by simp
  }

  ultimately show "sorted (insert_sort (x # xs))" by simp
qed

lemma insert_is_permutation_of_input: "mset (insert y ys) = mset (y#ys)"
proof(induct ys rule:insert.induct)
  case (1 x)
  then show ?case by simp
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
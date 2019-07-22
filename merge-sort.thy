theory "merge-sort"
  imports Main "HOL-Library.Multiset"
begin

declare[[names_short]]

text \<open>tail recursive\<close>

function merge:: "nat list \<Rightarrow> nat list \<Rightarrow> nat list" where 
"merge xs [] = xs" |
"merge [] ys = ys" |
"merge  (x#xs) (y#ys) = (if x \<le> y then x#merge xs (y#ys) else y#merge (x#xs) ys)"
by pat_completeness auto
termination
proof (relation "measure (\<lambda>(xs,ys). length xs + length ys)")
  show "wf (measure (\<lambda>(xs, ys). length xs + length ys))" by simp
next
  fix xs ys::"nat list"
  fix x y :: nat
  assume a1: "x \<le> y"
  show "((xs, y#ys), x#xs, y#ys) \<in> measure (\<lambda>(xs, ys). length xs + length ys)" 
  proof (simp only: in_measure)
    show "(case (xs, y#ys) of (xs, ys) \<Rightarrow> length xs + length ys) < (case (x#xs, y#ys) of (xs, ys) \<Rightarrow> length xs + length ys)"
    proof(simp only: prod.case)
      show "length xs + length (y#ys) < length (x#xs) + length (y#ys)" by simp
    qed
  qed
next
  fix xs ys::"nat list"
  fix x y :: nat
  assume a2: "\<not> x \<le> y "
  show "((x#xs, ys), x#xs, y#ys) \<in> measure (\<lambda>(xs, ys). length xs + length ys)"
  proof (simp only: in_measure)
    show "(case (x# xs, ys) of (xs, ys) \<Rightarrow> length xs + length ys) < (case (x#xs, y#ys) of (xs, ys) \<Rightarrow> length xs + length ys)" 
    proof(simp only: prod.case)
      show "length (x#xs) + length ys < length (x#xs) + length (y#ys)" by simp
    qed
  qed
qed

value "merge ([1,2,3]) ([1,2,3,10])"

lemma sorted4 :"\<lbrakk>sorted (y#ys);sorted (x#xs);sorted (merge (xs) (y#ys)); x \<le> y\<rbrakk> \<Longrightarrow> sorted(x#merge (xs) (y#ys))"
proof(induction xs rule: sorted.induct)
  case 1
  then show ?case by auto
next
  case (2 x ys)
  then show ?case by (metis merge.simps(3) sorted2)
qed

lemma sorted5 :"\<lbrakk>sorted (y#ys);sorted (x#xs);sorted (merge (x#xs) (ys)); y \<le> x\<rbrakk> \<Longrightarrow> sorted (y#merge (x#xs) (ys))"
proof(induction ys  rule: sorted.induct)
  case 1
  then show ?case  by auto
next
  case (2 x ys)
  then show ?case by (metis merge.simps(3) sorted2)
qed

lemma merge_order: "\<lbrakk>sorted (xs);sorted(ys)\<rbrakk> \<Longrightarrow> sorted(merge xs ys)"
proof(induct xs ys rule: merge.induct)
  case (1 xs)
  then show "sorted (merge xs [])" by simp
next
  case (2 ys)
  then show "sorted (merge [] ys)" by simp
next
  case (3 x xs y ys)
  then show "sorted (merge (x # xs) (y # ys))"
  proof(cases "x \<le> y")
    case True
    then show "sorted (merge (x # xs) (y # ys))"  
    proof (simp only: merge.simps True if_True)
      have "sorted (merge xs (y # ys))" using "3.hyps"(1) "3.prems"(1) "3.prems"(2) True sorted.simps(2) by simp
      then show "sorted (x # merge xs (y # ys))"  by (simp only: "3.prems"(1) "3.prems"(2) True sorted4)
    qed
  next
    case False
    then show "sorted (merge (x # xs) (y # ys))"
    proof (simp only: merge.simps False if_False)
      have "sorted(merge (x # xs) ys)" using "3.hyps"(2) "3.prems"(1) "3.prems"(2) False sorted.simps(2) by simp
      moreover have "y \<le> x" using False nat_le_linear by simp
      ultimately show "sorted (y # merge (x # xs) ys)" by (simp only: "3.prems"(1) "3.prems"(2) False sorted5)
    qed
  qed
qed

lemma merge_permutation: "mset (merge xs ys) = mset xs + mset ys"
proof(induct xs ys rule: merge.induct)
  case (1 ys)
  have "mset (merge ys []) = mset (ys)" by simp
  also have "... =  mset ys + mset []" by simp
  finally show "mset (merge ys []) = mset ys + mset []" by this
next
  case (2 xs)  
  have "mset (merge [] xs) = mset (xs)" by simp
  also have "... =  mset xs + mset []" by simp
  then show "mset (merge [] xs) = mset [] + mset xs" by simp
next
  case (3 x xs y ys)
  then show ?case
  proof(cases "x \<le> y")
    case True
    have "mset (merge (x # xs) (y # ys)) = mset (x#merge xs (y # ys))" using True by simp 
    also have "... =  {#x#} +  mset (merge xs (y # ys))" by simp
    also have "... =  {#x#} +  mset xs + mset (y # ys)" using "3.hyps"(1) True  by (simp)
    also have "... =   mset (x # xs) + mset (y # ys)" by (simp add: "3.hyps"(1) True)
    finally show "mset (merge (x # xs) (y # ys)) = mset (x # xs) + mset (y # ys)" by this
  next
    case False
    have "mset (merge (x # xs) (y # ys)) = mset (y#merge (x#xs) ys)" using False by simp 
    also have "... =  {#y#} +  mset(merge (x#xs) ys)" by simp
    also have "... =  {#y#} +  mset (x # xs) + mset ys" by (simp add: "3.hyps"(2) False)
    also have "... =  mset (x # xs) + mset (y # ys)" by simp
    finally show "mset (merge (x # xs) (y # ys)) = mset (x # xs) + mset (y # ys)" by this
  qed
qed

value "merge [1,2,3] [1,4,5,6]"

fun merge_sort:: "nat list \<Rightarrow> nat list" where
"merge_sort [] = []" |
"merge_sort [x] = [x]" |
"merge_sort (x#xs) = ( let  half = ((length (x#xs)) div 2); left = take half (x#xs); right = drop half (x#xs) in  merge (merge_sort (left)) (merge_sort (right)))"

value "msort [9,8,7,6,5,4]"

theorem merge_sort_order: "sorted(merge_sort xs)"
proof(induct xs rule:merge_sort.induct)
  case 1
  then show ?case by simp
next
  case (2 x)
  then show ?case by simp
next
  case (3 v vb vc)
  thm  "3.hyps"
  let ?half = "length (v # vb # vc) div 2"
  let ?left = "take ?half (v # vb # vc)"
  let ?right = "drop ?half (v # vb # vc)"
  show "sorted (merge_sort (v # vb # vc))" 
  proof (simp only: merge_sort.simps Let_def)
    have "sorted ((merge_sort (?left)))" using "3.hyps"(1) by simp
    moreover have "sorted ((merge_sort (?right)))" using "3.hyps"(2) by simp
    ultimately show "sorted (merge (merge_sort (?left)) (merge_sort (?right)))" by (simp only:merge_order)
  qed
qed

theorem merge_sort_permutation: "mset (merge_sort xs) = mset xs"
proof(induct xs rule:merge_sort.induct)
  case 1
  then show "mset (merge_sort []) = mset []" by simp
next
  case (2 x)
  then show "mset (merge_sort [x]) = mset [x]" by simp
next
  case (3 v vb vc)
  let ?half = "length (v # vb # vc) div 2"
  let ?left = "take ?half (v # vb # vc)"
  let ?right = "drop ?half (v # vb # vc)"
  have "mset (merge_sort (v # vb # vc)) = mset(merge (merge_sort ?left) (merge_sort ?right))" by simp
  also have "... = mset(merge_sort ?left) + mset(merge_sort ?right)" using merge_permutation by simp
  also have "... = mset(?left) + mset(?right)"  by (simp add: "3.hyps"(1) "3.hyps"(2))
  also have "... = mset (v # vb # vc)"  by (metis append_take_drop_id mset_append)
  finally show "mset (merge_sort (v # vb # vc)) = mset (v # vb # vc)" by this
qed

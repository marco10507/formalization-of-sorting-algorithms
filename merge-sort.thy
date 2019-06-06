theory "merge-sort"
  imports Main "HOL-Library.Multiset"
begin

function merge:: "nat list \<Rightarrow> nat list \<Rightarrow> nat list" where 
"merge xs [] = xs" |
"merge [] ys = ys" |
"merge  (x#xs) (y#ys) = (if x \<le> y then x#merge xs (y#ys) else y#merge (x#xs) ys)"
by pat_completeness auto
termination 
  apply (relation "measure (\<lambda>(xs,ys). length xs + length ys)")
  apply (auto)
done

lemma ghj: "mset (merge xs ys) = mset xs + mset ys"
proof(induct xs ys rule: merge.induct)
case (1 ys)
  then show ?case by simp
next
  case (2 xs)
  then show ?case by simp
next
  case (3 x xs y ys)
  then show ?case
  proof(cases "x \<le> y")
    case True
    then show ?thesis using [[simp_trace_new]] "3.hyps"(1) by simp
  next
    case False
    then show ?thesis using [[simp_trace_new]] "3.hyps"(2) by simp
  qed
qed

lemma asd :"\<lbrakk>sorted (y#ys);sorted (x#xs);sorted (xs);sorted (merge (xs) (y#ys)); x \<le> y\<rbrakk> \<Longrightarrow> sorted(x#merge (xs) (y#ys))"
proof(induction xs rule: sorted.induct)
  case 1
  then show ?case by auto
next
  case (2 x ys)
  then show ?case by fastforce
qed

lemma zxc :"\<lbrakk>sorted (y#ys);sorted (x#xs);sorted (ys);sorted (merge (x#xs) (ys)); y \<le> x\<rbrakk> \<Longrightarrow> sorted(y#merge (x#xs) (ys))"
proof(induction ys rule: sorted.induct)
  case 1
  then show ?case by auto
next
  case (2 x ys)
  then show ?case by fastforce
qed

theorem rty: "sorted (xs) \<Longrightarrow> sorted(ys) \<Longrightarrow> sorted(merge xs ys)"
proof(induct xs ys rule: merge.induct)
  fix ys let ?case = "sorted (merge [] ys)"
  assume case1_assums: "sorted ys" and "sorted []"
  then show ?case using [[simp_trace]]  by simp
next
  fix xs let ?case = "sorted (merge xs [])"
  assume case2_assums: "sorted xs" and "sorted []"
  then show ?case by simp
next
  fix x xs y ys let ?case = "sorted (merge (x # xs) (y # ys))"
  assume case3_hyp1: "x \<le> y \<Longrightarrow> sorted xs \<Longrightarrow> sorted (y # ys) \<Longrightarrow> sorted (merge xs (y # ys))" and case3_hyp2: "\<not> x \<le> y \<Longrightarrow> sorted (x # xs) \<Longrightarrow> sorted ys \<Longrightarrow> sorted (merge (x # xs) ys)"
  assume case3_prem1: "sorted (x # xs)" and case3_prem2:"sorted (y # ys)"
  then show ?case
  proof(cases "x \<le> y")
    let ?thesis = "sorted (merge (x # xs) (y # ys))"
    assume true_assum: " x \<le> y"
    have "sorted xs" using case3_prem1 sorted.simps(2) by blast
    also have "sorted (y # ys)" using case3_prem2 by blast
    moreover have "sorted (merge xs (y # ys))" using calculation(1) case3_hyp1 case3_prem2 true_assum by blast
    moreover have "sorted (x#merge xs (y # ys))" using asd calculation(1) calculation(3) case3_prem1 case3_prem2 true_assum by blast
    then have "sorted (merge (x # xs) (y # ys))" by (simp add: true_assum)
    then show ?thesis by assumption
  next
    let ?thesis = "sorted (merge (x # xs) (y # ys))"
    assume false_assum: "\<not> x \<le> y"
    have "sorted (x # xs)" using case3_prem1 by blast
    also have "sorted ys" using case3_prem2 sorted.simps(2) by blast
    moreover have "sorted (merge (x # xs) ys)" using case3_hyp2 calculation(2) case3_prem1 false_assum by blast
    moreover have "sorted (y#merge (x # xs) ys)" using calculation(2) calculation(3) case3_prem1 case3_prem2 false_assum nat_le_linear zxc by blast
    then have "sorted (merge (x # xs) (y # ys))" by (simp add: false_assum)
    then show "sorted (merge (x # xs) (y # ys))" by assumption
  qed
qed

value "merge [1,2,3] [1,4,5,6]"

fun msort:: "nat list \<Rightarrow> nat list" where
"msort [] = []" |
"msort [x] = [x]" |
"msort xs = (
  let 
    half = ((length xs) div 2); 
    left = take half xs; 
    right = drop half xs 
  in 
   merge (msort (left)) (msort (right))
)"

value "msort [9,8,7,6,5,4]"

thm msort.induct

theorem iop: "sorted(msort xs)"
proof(induct xs rule:msort.induct)
  case 1
  then show ?case by simp
next
  case (2 x)
  then show ?case by simp
next
  case (3 v vb vc)
  let ?half = "length (v # vb # vc) div 2"
  let ?left = "take ?half (v # vb # vc)"
  let ?right = "drop ?half (v # vb # vc)"
  have "sorted (msort ?left)" using "3.hyps"(1) by blast
  moreover have "sorted (msort ?right)" using [[simp_trace]]  "3.hyps"(2) by blast
  moreover have "sorted(merge (msort (?left)) (msort (?right)))" using calculation(1) calculation(2) rty by blast
  then have "sorted (msort (v # vb # vc))" by simp
  then show "sorted (msort (v # vb # vc))" by assumption
qed

lemma cvb: "let half = (length xs) div 2; left = take half xs; right = drop half xs in left@right = xs"
proof(induct xs)
  case Nil
  then show ?case by simp
next
  case (Cons a xs)
  then show ?case by simp
qed

theorem bnm: "mset (msort xs) = mset xs"
proof(induct xs rule:msort.induct)
  case 1
  then show ?case by simp
next
  case (2 x)
  then show ?case by simp
next
  case (3 v vb vc)
  let ?half = "length (v # vb # vc) div 2"
  let ?left = "take ?half (v # vb # vc)"
  let ?right = "drop ?half (v # vb # vc)"
  have " mset (msort ?left) = mset ?left" using "3.hyps"(1) by blast
  moreover have "mset (msort ?right) = mset ?right" using "3.hyps"(2) by blast
  moreover have "mset (merge (msort (?left)) (msort (?right))) = mset ?left + mset ?right" using "3.hyps"(2) calculation(1) ghj by auto
  moreover have "mset (msort (v # vb # vc)) = mset ?left + mset ?right" using calculation(3) by auto
  moreover have "mset ?left + mset ?right = mset (v # vb # vc)" using [[simp_trace]] cvb mset_append by (metis) (*this might be more expended to show smothly the transition to mset (v # vb # vc) *)
  then have "mset (msort (v # vb # vc)) = mset (v # vb # vc)" using calculation(4) by auto
  then show "mset (msort (v # vb # vc)) = mset (v # vb # vc)" by assumption
qed

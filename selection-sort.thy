theory "selection-sort"
  imports Main "HOL-Library.Multiset"
begin

lemma min_membership: "m = Min(set (x#xs)) \<Longrightarrow> m \<in> set (x#xs)"
proof(induct xs arbitrary: x m)
  case Nil  
  have "m = Min (set [x])" using Nil.prems by simp
  also have "... \<in> set [x]" by simp
  finally show "m \<in> set [x]" by this
next
  case (Cons a xs)
   have "m = Min (set (x # a # xs))" using Cons.prems by simp
   also have "... \<in> set (x # a # xs)"  using Min_in by blast
   finally show "m \<in> set (x # a # xs)" by this
qed

lemma remove_member: "y \<in> set (x#xs) \<Longrightarrow> length (remove1 y (x#xs)) < length (x#xs)"
proof(induct xs arbitrary: y x)
  case Nil
  have "length (remove1 y [x]) = length (remove1 x [x])" using Nil.prems by simp
  also have "length (remove1 x [x]) = length []" by simp
  also have "length [] < length [x]" by simp
  finally show "length (remove1 y [x]) < length [x]" by this
next
next
  case (Cons a xs)
  then show "length (remove1 y (x # a # xs)) < length (x # a # xs)"
  proof(cases "y \<in> set (a # xs)")
    case True
    have "length (remove1 y (x # a # xs)) = length (x#remove1 y (a # xs))" using One_nat_def Suc_pred True length_Cons length_pos_if_in_set length_remove1 remove1.simps(2)  by metis
    also have "... = length [x] + length (remove1 y (a # xs))"  by simp
    also have "... < length [x] + length (a # xs)" using Cons.hyps True by simp
    also have "... = length (x # a # xs)" by simp
    finally show "length (remove1 y (x # a # xs)) < length (x # a # xs)" by this
  next
    case False
    have "length (remove1 y (x # a # xs)) = length (remove1 x (x # a # xs))" using Cons.prems False by simp
    also have "... = length (a # xs)" by simp
    also have "... < length (x # a # xs)" by simp
    finally show "length (remove1 y (x # a # xs)) < length (x # a # xs)" by this
  qed
qed
 
                                                                                                            
(*no tail-recursive*)
function selection_sort:: "nat list \<Rightarrow> nat list" where
selection_sort_Null:  "selection_sort [] = []" |
selection_sort_Cons: "selection_sort (x#xs) = (let min = Min (set(x#xs)); rest = remove1 min (x#xs) in min#selection_sort(rest))"
by pat_completeness auto                   
termination by (meson "termination" in_measure min_membership remove_member wf_measure)

value "selection_sort [2,4,10,0,0]"


theorem selection_sort_is_permutation_of_input: "mset (selection_sort(xs)) = mset xs"
proof(induct xs rule: selection_sort.induct)
case 1
then show ?case by simp
next
  case (2 x xs)
  let ?min = "Min (set (x # xs))"
  let ?rest = "remove1 ?min (x # xs)"
  have IH: "mset (selection_sort ?rest) = mset ?rest" using "2.hyps" by simp
  then show "mset (selection_sort (x # xs)) = mset (x # xs)"
  proof(cases "?min = x")
    case True
    have "mset (selection_sort (x # xs)) = mset(?min#selection_sort(?rest))" by (metis "selection-sort.selection_sort_Cons")
    also have "... = mset(x#selection_sort(xs))" using True by simp
    also have "... = {#x#}  + mset(selection_sort(xs))" by simp
    also have "... = {#x#}  + mset(xs)" using IH True by simp
    also have "... = mset (x#xs)" by simp
    finally show "mset (selection_sort (x # xs)) = mset (x # xs)" by this
  next
    case False
    have c1: "mset (selection_sort (x # xs)) = mset( Min (set (x # xs)) #selection_sort(remove1 ( Min (set (x # xs)) ) (x # xs)))" by (metis "selection-sort.selection_sort_Cons")
    also have c2:"... = {#Min (set (x # xs))#} +  mset (selection_sort(remove1 ( Min (set (x # xs)) ) (x # xs)))" by simp
    also have c3: "... = {#Min (set (x # xs))#} +  mset (remove1 (Min (set (x # xs))) (x # xs))" by (simp add: "2.hyps")
    also have c4:"... = {#Min (set (x # xs))#} + mset (x#remove1 (Min (set (x # xs))) (xs))" using False by auto
    also have c5: "... = ({#Min (set (x # xs))#} + mset (remove1 (Min (set (x # xs))) (xs))) + {#x#}" using False by auto
    also have c6: "... = mset (xs) + {#x#}" using  IH add.right_neutral c2 c4 insert_DiffM min_membership mset.simps(2) mset_remove1 set_mset_mset union_mset_add_mset_right  by metis
    also have c7: "... = mset (x # xs)" by simp
    finally show "mset (selection_sort (x # xs)) = mset (x # xs)" by this
  qed
qed                                                                                                                                 

lemma kkkk: "\<lbrakk>minimum \<in># mset (y # ys); minimum = Min (set (y # ys)); rest = remove1 minimum (y # ys) \<rbrakk>\<Longrightarrow>   mset(rest) \<subseteq># (mset (y # ys))"  by simp

lemma sorted4: "\<lbrakk>minimum \<in># mset (y # ys); mset(rest) \<subseteq># (mset (y # ys)); minimum = Min (set (y # ys)); rest = remove1 minimum (y # ys); mset(selection_sort(rest)) \<subseteq># mset(y # ys)\<rbrakk> \<Longrightarrow> sorted(minimum#selection_sort(rest)) = (minimum  \<le> y \<and> sorted (selection_sort(rest)))"  by (metis List.finite_set Min_le list.set_intros(1) notin_set_remove1 selection_sort_is_permutation_of_input set_mset_mset sorted.simps(2))


theorem selection_sort_output_sorted: "sorted (selection_sort(xs))"
proof(induct xs rule:selection_sort.induct)
  case 1
  then show ?case by simp
next
  case (2 x xs)
  let ?minimum = "Min (set (x # xs))"
  let ?rest = "remove1 ?minimum (x # xs)"
  show "sorted (selection_sort (x # xs))"
  proof(simp only:selection_sort_Cons Let_def)
    have "?minimum \<in># mset (x # xs)" using min_membership by auto
    moreover have "mset(?rest) \<subseteq># (mset (x # xs))" by auto
    moreover have "?minimum = Min (set (x # xs))" by simp
    moreover have "?rest = remove1 ?minimum (x # xs)" by simp
    moreover have "mset(selection_sort(?rest)) \<subseteq># mset(x # xs)" using selection_sort_is_permutation_of_input by simp
    ultimately show "sorted (?minimum # selection_sort (?rest))"
    proof (simp only:sorted4)
      have "?minimum  \<le> x" by simp
      moreover have "sorted(selection_sort(?rest))" using "2.hyps" by simp
      ultimately show "?minimum  \<le> x \<and> sorted(selection_sort(?rest))" by blast
    qed 
  qed
qed



(*tail-recursive version*)

lemma max_membership: "m = Max(set (x#xs)) \<Longrightarrow> m \<in> set (x#xs)"
proof(induct xs arbitrary: x m)
  case Nil
  then show ?case by simp
next
  case (Cons a xs)
  then show "m \<in> set (x # a # xs)"
  proof(cases "m = Max (set (a#xs))")
    case True
    have "m \<in> set (a# xs)" using Cons.hyps True by simp
    moreover have "m \<in> set (x # a # xs)" using calculation by auto
    then show "m \<in> set (x # a # xs)" by assumption
  next
    case False
    have "m \<in> {Max ({x} \<union> set (a # xs))}" by (metis Cons.prems insertCI insert_is_Un list.simps(15))
    moreover have "m \<notin> set (a # xs)" by (metis Cons.prems False List.finite_set Max.in_idem Max.union insert_is_Un list.distinct(1) list.simps(15) set_empty sup.right_idem)
    moreover have "m \<in> {Max ({x})}" by (metis (mono_tags, lifting) Cons.prems List.finite_set Max_in calculation(2) insert_iff list.simps(15) set_empty singleton_iff)
    moreover have "m \<in> {x}"  using Max_singleton calculation(3) by blast
    moreover have  "m \<in> set (x # a # xs)" using calculation by simp
    then show "m \<in> set (x # a # xs)" by assumption
  qed
qed

function tr_selection_sort:: "nat list \<Rightarrow> nat list \<Rightarrow> nat list" where
"tr_selection_sort [] accum = accum" |
"tr_selection_sort (x#xs) accum = (let max = Max (set(x#xs)); rest =remove1 max (x#xs) in tr_selection_sort(rest) (max#accum))"
by pat_completeness auto
termination
apply(relation "measure (\<lambda>(xs,accum). size xs)")
apply simp
by (metis case_prod_conv in_measure max_membership remove_member)

value "tr_selection_sort [2,4,10,0,0] []"

theorem tr_selection_sort_output_sorted: "\<lbrakk>sorted (ACCUM);  \<forall>A e. A \<in> (set ACCUM) \<and> e \<in> set xs \<and> e \<le> A\<rbrakk>\<Longrightarrow> sorted (tr_selection_sort xs ACCUM)"
proof(induct xs arbitrary: ACCUM rule:tr_selection_sort.induct)
  case (1 zs)
  then show ?case  by (simp add: sorted01)
next
  case (2 v va zs)
  let ?max = "Max (set (v # va))"
  let ?rest = "remove1 ?max (v # va)"
  have "sorted (ACCUM)" using "2.prems"(1) by simp
  moreover have " \<forall>A e. A \<in> set ACCUM \<and> e \<in> set (?max # zs) \<and> e \<le> A" using "2.prems"(2) by simp
  moreover have "sorted (tr_selection_sort (?max # zs) ACCUM)" using 2(1) calculation by simp
  moreover have "sorted (tr_selection_sort (zs) (?max#ACCUM))"  using calculation by blast
  moreover have "sorted (tr_selection_sort (zs) (ACCUM))" using calculation by blast
  then show "sorted (tr_selection_sort zs ACCUM)"  by assumption
qed

theorem tr_selection_sort_is_permutation_of_input: "\<lbrakk>sorted (ACCUM); \<forall>A e. A \<in> (set ACCUM) \<and> e \<in> set xs \<and> e \<le> A\<rbrakk>  \<Longrightarrow> mset (tr_selection_sort xs ACCUM) = mset xs + mset ACCUM"
proof(induct xs arbitrary: ACCUM)
  case Nil
  then show ?case by simp
next
  case (Cons a xs)
  moreover have  "mset xs + {#a#} + mset ACCUM = mset xs + {#a#} + mset ACCUM" by simp
  moreover have  "mset xs + {#a#} + mset ACCUM = mset (a # xs) + mset ACCUM" by simp
  moreover have  "(mset xs + mset ACCUM) + {#a#} = mset (a # xs) + mset ACCUM" by simp
  moreover have  "(mset (tr_selection_sort xs ACCUM)) + {#a#} = mset (a # xs) + mset ACCUM" using calculation by blast
  moreover have  "(mset (tr_selection_sort (a#xs) ACCUM)) = mset (a # xs) + mset ACCUM" using calculation by blast
  then show "mset (tr_selection_sort (a # xs) ACCUM) = mset (a # xs) + mset ACCUM" by assumption
qed

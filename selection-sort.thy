theory "selection-sort"
  imports Main "HOL-Library.Multiset"
begin

lemma min_membership: "minimum = Min(set (x#xs)) \<Longrightarrow> minimum \<in> set (x#xs)"
proof(induct xs arbitrary: x minimum)
  case Nil  
  have "minimum = Min (set [x])" using Nil.prems by simp
  also have "... \<in> set [x]" by simp
  finally show "minimum \<in> set [x]" by this
next
  case (Cons a xs)
   have "minimum = Min (set (x # a # xs))" using Cons.prems by simp
   also have "... \<in> set (x # a # xs)"  using Min_in by blast
   finally show "minimum \<in> set (x # a # xs)" by this
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
selection_sort_Cons: "selection_sort (x#xs) = (let minimum = Min (set(x#xs)); rest = remove1 minimum (x#xs) in minimum#selection_sort(rest))"
by pat_completeness auto       
termination
proof (relation "measure (\<lambda>(xs). length xs)")
  show "wf (measure length)"  by simp
next
  fix minimum x ::nat
  fix rest xs:: "nat list"
  assume a1: "minimum =  Min (set (x # xs))"
  assume a2: "rest = remove1 minimum (x # xs)"
  show "(rest, x # xs) \<in> measure length"
  proof (simp only: in_measure)
    have p1: "minimum \<in> set (x#xs)" using a1 by (simp only: min_membership)
    show "length rest < length (x # xs)" using a2 p1 by (simp only:remove_member)
  qed
qed

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
    have "mset (selection_sort (x # xs)) = mset(?min#selection_sort(?rest))" using True by simp
    also have "... = {#?min#}  + mset(selection_sort(?rest))" by simp
    also have "... = {#?min#}  + mset(?rest)" using IH by simp
    also have "... = {#?min#}  + mset(remove1 x (x # xs))" using True by simp
    also have "... = {#?min#}  + mset(xs)" by simp
    also have "... = {#x#}  + mset(xs)" using True by simp
    also have "... = mset (x#xs)" by simp
    finally show "mset (selection_sort (x # xs)) = mset (x # xs)" by this
  next
    case False
    have c1: "mset (selection_sort (x # xs)) = mset(?min #selection_sort(?rest))" by (metis "selection-sort.selection_sort_Cons")
    also have c2:"... = {#?min#} + mset(selection_sort(?rest))" by simp
    also have c3:"... = {#?min#} + mset(?rest)" using IH by simp
    also have c4:"... = {#?min#} + mset(x # xs) - {#?min#}" using False  min_membership [simp_trace] by fastforce
    also have c5:"... = mset (x # xs)" by simp
    finally show "mset (selection_sort (x # xs)) = mset (x # xs)" by this
  qed
qed                        

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
    have "?minimum = Min (set (x # xs))" by simp
    moreover have "?rest = remove1 ?minimum (x # xs)" by simp
    ultimately show "sorted (?minimum # selection_sort (?rest))"
    proof (simp only:Let_def sorted.simps)
      show "Ball (set (selection_sort (?rest))) ((\<le>) (?minimum)) \<and> sorted (selection_sort (?rest))"
      proof (rule conjI)
        have p1: "mset(selection_sort(?rest)) = mset(x # xs) - {#?minimum#}" by (simp add: selection_sort_is_permutation_of_input)
        show "Ball (set (selection_sort (?rest))) ((\<le>) (?minimum))" using p1  by (metis List.finite_set Min_le in_diffD p1 set_mset_mset)
      next
        have "sorted (selection_sort (?rest))" using "2.hyps" by simp
        from this show "sorted (selection_sort (?rest))" by assumption
      qed
    qed 
  qed
qed


















(*tail-recursive version*)

lemma max_membership: "m = Max(set (x#xs)) \<Longrightarrow> m \<in> set (x#xs)"
proof(induct xs arbitrary: x m)
  case Nil  
  have "m = Max (set [x])" using Nil.prems by simp
  also have "... \<in> set [x]" by simp
  finally show "m \<in> set [x]" by this
next
  case (Cons a xs)
   have "m = Max (set (x # a # xs))" using Cons.prems by simp
   also have "... \<in> set (x # a # xs)"  using Max_in by blast
   finally show "m \<in> set (x # a # xs)" by this
qed

function tr_selection_sort:: "nat list \<Rightarrow> nat list \<Rightarrow> nat list" where
"tr_selection_sort [] accum = accum" |
"tr_selection_sort (x#xs) accum = (let max = Max (set(x#xs)); rest =remove1 max (x#xs) in tr_selection_sort(rest) (max#accum))"
by pat_completeness auto
termination
proof(relation "measure (\<lambda>(xs, accum). size xs)")
  show "wf (measure (\<lambda>(xs, accum). length xs))"  by simp
next
  fix maximum x ::nat
  fix rest xs accum:: "nat list"
  assume a1: "maximum =  Max (set (x # xs))"
  assume a2: "rest = remove1 maximum (x # xs)"
  show "((rest, maximum # accum), x # xs, accum) \<in> measure (\<lambda>(xs, accum). length xs)"
  proof (simp only: in_measure)
    show "(case (rest, maximum # accum) of (xs, accum) \<Rightarrow> length xs) < (case (x # xs, accum) of (xs, accum) \<Rightarrow> length xs)" 
    proof(simp only: prod.case)
      have p1: "maximum \<in> set (x#xs)" using a1 by (simp only: max_membership)
      show "length rest < length (x # xs)" using a2 p1 by (simp only:remove_member)
    qed
  qed
qed

value "tr_selection_sort [2,4,10,0,0] []"

theorem tr_selection_sort_output_sorted: "\<lbrakk>sorted (ACCUM);  \<forall>A e. A \<in> (set ACCUM) \<and> e \<in> set xs \<and> e \<le> A\<rbrakk>\<Longrightarrow> sorted (tr_selection_sort xs ACCUM)"
proof(induct xs arbitrary: ACCUM rule:tr_selection_sort.induct)
  case (1 zs)
  then show ?case  by (simp add: sorted01)
next
  case (2 v va zs)
  then show "sorted (tr_selection_sort zs ACCUM)"  by (simp add: sorted01)
qed

theorem tr_selection_sort_is_permutation_of_input: "\<lbrakk>sorted (ACCUM); \<forall>A e. A \<in> (set ACCUM) \<and> e \<in> set xs \<and> e \<le> A\<rbrakk>  \<Longrightarrow> mset (tr_selection_sort xs ACCUM) = mset xs + mset ACCUM"
proof(induct xs arbitrary: ACCUM)
  case Nil
  show ?case by simp
next
  case (Cons a xs)
  show "mset (tr_selection_sort (a # xs) ACCUM) = mset (a # xs) + mset ACCUM"  using Cons.prems(2) by blast
qed



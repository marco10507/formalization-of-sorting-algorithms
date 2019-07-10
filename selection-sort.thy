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
  finally have "length (remove1 y [x]) < length [x]" by this
  then show "length (remove1 y [x]) < length [x]" by assumption
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
    also have "length (remove1 x (x # a # xs)) = length (a # xs)" by simp
    also have "length (a # xs) < length (x # a # xs)" by simp
    finally have "length (remove1 y (x # a # xs)) < length (x # a # xs)" by this
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

lemma remove1_min: "\<lbrakk>e \<in> set (xs); rest = remove1 e xs\<rbrakk> \<Longrightarrow> mset xs = mset rest + {#e#}"
proof(induct xs arbitrary: e rest)
  case Nil
  then show ?case by simp
next
  case (Cons a xs)
  then show "mset (a # xs) = mset rest + {#e#}"
  proof (cases "e = a")
    case True
    have "rest = xs" using Cons.prems(2) True  by simp
    moreover have "mset xs = mset xs " by simp
    moreover have "mset xs + {#a#} = mset xs + {#a#}" by simp
    moreover have "mset xs + {#a#} = mset xs + {#e#}" using True  by simp
    moreover have "mset (a # xs) = mset rest + {#e#}" using True calculation(1) by simp
    then show "mset (a # xs) = mset rest + {#e#}" by assumption
  next
    case False
    have "e \<in> set xs" using Cons.prems(1) False by simp
    moreover have "rest = a # remove1 e xs" using Cons.prems(2) False  by simp
    moreover have "mset (remove1 e xs) = mset xs - {#e#}"  by simp
    moreover have " {#a#} +  mset xs - {#e#} = mset (a # remove1 e xs)"  using calculation(1) by simp
    moreover have " {#a#} +  mset xs - {#e#} + {#e#} = mset (a # remove1 e xs) + {#e#}" using calculation by simp
    moreover have " {#a#} +  mset xs = mset (a # remove1 e xs) + {#e#}" using calculation by simp
    moreover have " mset (a # xs) = mset (a # remove1 e xs) + {#e#}" using calculation by simp
    moreover have " mset (a # xs) = mset (rest) + {#e#}" using calculation(2) calculation(7) by simp
    then show "mset (a # xs) = mset rest + {#e#}" by assumption
  qed
qed

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
    have "?rest = xs" using True by simp
    moreover have "mset (selection_sort ?rest) = mset ?rest" using IH by simp
    moreover have "mset (selection_sort ?rest) + {#?min#} = mset ?rest + {#?min#}" using True calculation by simp
    moreover have "mset (?min#selection_sort ?rest) = mset ?rest + {#?min#}" using True calculation by simp
    moreover have "mset (x#selection_sort xs) = mset ?rest + {#?min#}" using True calculation by simp
    moreover have "mset (selection_sort (x#xs)) = mset ?rest + {#?min#}" using True calculation by simp
    moreover have "mset (selection_sort (x#xs)) = mset xs + {#x#}" using True calculation by simp
    moreover have "mset (selection_sort (x#xs)) = mset (x#xs)" using True calculation by simp
    then show "mset (selection_sort (x # xs)) = mset (x # xs)" by assumption
  next
    case False
    have min: "?min = Min (set (xs))" by (metis False List.finite_set Min_eqI Min_le list.set_intros(2) min_membership set_ConsD) 
    moreover have rest:"?rest = x#remove1 ?min xs" using False by simp
    moreover have remove1_simp: "mset xs = mset (remove1 ?min xs) + {#?min#}" by (meson False min_membership remove1_min set_ConsD)

    moreover{
      have "mset ?rest = mset ?rest"  by simp
      moreover have "mset ?rest + {#?min#} = mset ?rest + {#?min#}"  by simp 
      moreover have "mset ?rest + {#?min#} = mset (x#remove1 ?min xs) + {#?min#}" using rest by simp
      moreover have "mset ?rest + {#?min#} = (mset (remove1 ?min xs) + {#?min#}) + {#x#}" using calculation by simp
      moreover have "mset ?rest + {#?min#} = (mset (xs)) + {#x#}" using remove1_simp by simp
      moreover have "mset ?rest + {#?min#} = mset (x # xs)" using calculation by simp
      moreover have "mset (selection_sort ?rest) + {#?min#} = mset (x # xs)" using IH calculation by simp
      moreover have "mset (?min#selection_sort ?rest) = mset (x # xs)" using calculation by simp
      moreover have "mset (selection_sort (x # xs)) = mset (x # xs)" using calculation selection_sort.simps(2) by metis
    }
    then show "mset (selection_sort (x # xs)) = mset (x # xs)" by assumption
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
theory "selection-sort"
  imports Main "HOL-Library.Multiset"
begin

lemma min_membership: "m = Min(set (x#xs)) \<Longrightarrow> m \<in> set (x#xs)"
proof(induct xs arbitrary: x m)
  case Nil
  then show ?case by simp
next
  case (Cons a xs)
  then show "m \<in> set (x # a # xs)"
  proof(cases "m = Min (set (a#xs))")
    case True
    have "m \<in> set (a# xs)" using Cons.hyps True by simp
    moreover have "m \<in> set (x # a # xs)" using calculation by auto
    then show "m \<in> set (x # a # xs)" by assumption
  next
    case False
    have "m \<in> {Min ({x} \<union> set (a # xs))}" by (metis Cons.prems insertCI insert_is_Un list.simps(15))
    moreover have "m \<notin> set (a # xs)" by (metis Cons.prems False List.finite_set Min_eqI Min_le insertI2 list.simps(15))
    moreover have "m \<in> {Min ({x})}" by (metis (mono_tags, lifting) List.finite_set Min_in calculation(1) calculation(2) insert_iff insert_is_Un list.simps(15) set_empty singleton_iff)
    moreover have "m \<in> {x}" using Min_singleton calculation(3) by simp
    moreover have  "m \<in> set (x # a # xs)"  using calculation(4) by auto
    then show "m \<in> set (x # a # xs)" by assumption
  qed
qed

lemma p_3 [simp]: "y \<in> set (x#xs) \<Longrightarrow> length (remove1 y (x#xs)) = length (x#xs) - 1"
  apply(induct xs)
  apply(auto)
done

lemma p_30 [simp]: "xs \<noteq> [] \<Longrightarrow> y \<in> set (xs) \<Longrightarrow> length (remove1 y (xs)) = length (xs) - 1"
  apply(induct xs)
  apply simp
  apply (meson length_remove1)
done

lemma p_5 [simp]: "y \<in> set (x#xs) \<Longrightarrow> length (remove1 y (x#xs)) < length (x#xs)"
  apply(induct xs)
  apply(auto)
done

(*important to proof this makes lemma p_7 to work, which also help to termiante the execution*)
(*not tail-recursive*)
function selection_sort:: "nat list \<Rightarrow> nat list" where
"selection_sort [] = []" |
"selection_sort (x#xs) = (let m = Min (set(x#xs)) in m#selection_sort(remove1 m (x#xs)))"
by pat_completeness auto
termination by (meson "termination" in_measure min_membership p_5 wf_measure)

value "selection_sort [2,4,10,0,0]"
(*
Note that this rule (.cases) does not mention the function at all, but only describes 
the cases used for defining selection_sort.
*)
thm selection_sort.cases 
(*
In contrast, the rule selection_sort.elims also
tell us what the function value will be in each case:
*)
thm selection_sort.elims
thm selection_sort.induct

lemma p_13 [simp]: "m = Min(set xs)  \<Longrightarrow> e \<in> set(xs) \<Longrightarrow>  m \<le> e"
proof(induct xs)
  case Nil
  then show ?case by simp
next
  case (Cons x1 x2)
  then show ?case using Min_le by blast
qed

lemma p_10 [simp]: "m = Min(set (x#xs)) \<Longrightarrow> rest = remove1 m (x#xs) \<Longrightarrow> e \<in> set(rest) \<Longrightarrow>  m \<le> e"
proof(induct xs)
case Nil
then show ?case by simp
next
  case (Cons a xs)
  then show ?case by (meson list.discI notin_set_remove1 p_13)
qed

lemma p_11 [simp]: "m = Min(set xs) \<Longrightarrow> sorted (m#selection_sort(remove1 m (xs)))"
proof(induct xs arbitrary:m rule:selection_sort.induct)
  case 1
  then show ?case by simp
next
  case (2 x xs)
  then show ?case using [[simp_trace_new]] by (smt One_nat_def eq_iff length_Cons list.size(3) not_Cons_self2 p_10 remove1_idem selection_sort.elims sorted01 sorted2)
qed

theorem ss_s: "sorted (selection_sort(xs))"
proof(induct xs rule:selection_sort.induct)
  case 1
  then show ?case by simp
next
  case (2 x xs)
  then show ?case by (metis p_11 selection_sort.simps(2))
qed

lemma 100: "e \<in> set xs \<Longrightarrow> rest = remove1 e xs \<Longrightarrow> mset xs = mset rest + {#e#}"
proof(induct xs)
  case Nil
  then show ?case by simp
next
  case (Cons a xs)
  then show ?case by (metis add.right_neutral insert_DiffM mset_remove1 set_mset_mset union_mset_add_mset_right)
qed

theorem "mset (selection_sort(xs)) = mset xs"
proof(induct xs rule: selection_sort.induct)
case 1
then show ?case by simp
next
  case (2 x xs)
  then show ?case by (metis "100" add.right_neutral min_membership mset.simps(2) selection_sort.simps(2) union_mset_add_mset_right)
qed


(*tail-recursive version*)

lemma p_200 [simp]: "m = Max(set (x#xs)) \<Longrightarrow> m \<in> set (x#xs)"
proof(induct xs)
  case Nil
  then show ?case by simp
next
  case (Cons a xs)
  then show ?case using eq_Max_iff by blast
qed

function (sequential) tr_selection_sort:: "nat list \<Rightarrow> nat list \<Rightarrow> nat list" where
"tr_selection_sort [] accum = accum" |
"tr_selection_sort (xs) accum = (let m = Max (set(xs)) in tr_selection_sort(remove1 m (xs)) (m#accum))"
by pat_completeness auto
termination
apply(relation "measure (\<lambda>(xs,accum). size xs)")
apply simp
by (metis case_prod_conv in_measure p_200 p_5)

value "tr_selection_sort [2,4,10,0,0] []"

theorem tr_ss_s: "sorted (ACCUM) \<Longrightarrow> \<forall>A e. A \<in> (set ACCUM) \<and> e \<in> set xs \<and> A \<le> e  \<Longrightarrow> sorted (tr_selection_sort xs ACCUM)"
proof(induct xs rule:tr_selection_sort.induct)
case (1 accum)
then show ?case by blast
next
case (2 v va accum)
  then show ?case by (simp add: sorted01)
qed

theorem tr_ss_permutation: "sorted (ACCUM) \<Longrightarrow> \<forall>A e. A \<in> (set ACCUM) \<and> e \<in> set xs \<and> A \<le> e  \<Longrightarrow> mset (tr_selection_sort xs ACCUM) = mset xs + mset ACCUM"
proof(induct xs arbitrary: ACCUM)
  case Nil
  then show ?case by simp
next
  case (Cons a xs)
  then show ?case by blast
qed


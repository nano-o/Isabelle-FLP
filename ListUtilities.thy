section {* ListUtilities*}

text {*
  \file{ListUtilities} defines a (proper) prefix relation for lists, and proves some
  additional lemmata, mostly about lists.
*}

theory ListUtilities
imports Main
begin

context begin

subsection {* List Prefixes *}

inductive prefixList ::
  "'a list \<Rightarrow> 'a list \<Rightarrow> bool"
where
  "prefixList [] (x # xs)"
| "prefixList xa xb \<Longrightarrow> prefixList (x # xa) (x # xb)"

lemma PrefixListHasTail:
fixes 
  l1 :: "'a list" and
  l2 :: "'a list"
assumes
  "prefixList l1 l2"
shows
  "\<exists> l . l2 = l1 @ l \<and> l \<noteq> []"
  using assms by (induct rule: prefixList.induct, auto)

lemma PrefixListMonotonicity:
fixes 
  l1 :: "'a list" and
  l2 :: "'a list"
assumes
  "prefixList l1 l2"
shows
  "length l1 < length l2"
using assms by (induct rule: prefixList.induct, auto)

lemma TailIsPrefixList : 
fixes 
  l1 :: "'a list" and
  tail :: "'a list"
assumes "tail \<noteq> []"
shows "prefixList l1 (l1 @ tail)"
using assms
proof (induct l1, auto)
  have "\<exists> x xs . tail = x # xs"
    using assms by (metis neq_Nil_conv)
  thus "prefixList [] tail"
    using assms  by (metis prefixList.intros(1))
next
  fix a l1
  assume "prefixList l1 (l1 @ tail)"
  thus "prefixList (a # l1) (a # l1 @ tail)"
    by (metis prefixList.intros(2))
qed

lemma PrefixListTransitive:
fixes 
  l1 :: "'a list" and
  l2 :: "'a list" and
  l3 :: "'a list"
assumes
  "prefixList l1 l2"
  "prefixList l2 l3"
shows
  "prefixList l1 l3"
using assms
proof -
  from assms(1) have "\<exists> l12 . l2 = l1 @ l12 \<and> l12 \<noteq> []" 
    using PrefixListHasTail by auto
  then obtain l12 where Extend1: "l2 = l1 @ l12 \<and> l12 \<noteq> []" by blast
  from assms(2) have Extend2: "\<exists> l23 . l3 = l2 @ l23 \<and> l23 \<noteq> []" 
    using PrefixListHasTail by auto
  then obtain l23 where Extend2: "l3 = l2 @ l23 \<and> l23 \<noteq> []" by blast
  have "l3 = l1 @ (l12 @ l23) \<and> (l12 @ l23) \<noteq> []" 
    using Extend1 Extend2 by simp
  hence "\<exists> l . l3 = l1 @ l \<and> l \<noteq> []" by blast
  thus "prefixList l1 l3" using TailIsPrefixList by auto  
qed

subsection {* Lemmas for lists and nat predicates *}

lemma NatPredicateTippingPoint:
  assumes
    P0: "P 0" and NotPN2: "\<not>P n2"
  shows
    "\<exists>n<n2. P n \<and> \<not>P (Suc n)"
  by (metis NotPN2 P0 dec_induct zero_le)

lemma MinPredicate:
fixes 
  P::"nat \<Rightarrow> bool"
assumes
  "\<exists> n . P n"
shows 
  "(\<exists> n0 . (P n0) \<and> (\<forall> n' . (P n') \<longrightarrow> (n' \<ge> n0)))"
using assms
by (metis LeastI2_wellorder Suc_n_not_le_n)

text {*
  The lemma \isb{MinPredicate2} describes one case of \isb{MinPredicate}
  where the aforementioned smallest element is zero.
*}

lemma MinPredicate2:
fixes
  P::"nat \<Rightarrow> bool"
assumes
 "\<exists> n . P n"
shows
  "\<exists> n0 . (P n0) \<and> (n0 = 0 \<or> \<not> P (n0 - 1))"
using assms MinPredicate
by (metis add_diff_cancel_right' diff_is_0_eq diff_mult_distrib mult_eq_if)

text {*
  \isb{PredicatePairFunction} allows to obtain functions mapping two arguments
  to pairs from 4-ary predicates which are left-total on their first
  two arguments.
*}

private
lemma PredicatePairFunction: 
fixes
  P::"'a \<Rightarrow> 'b \<Rightarrow> 'c \<Rightarrow> 'd \<Rightarrow> bool"
assumes
  A1: "\<forall>x1 x2 . \<exists>y1 y2 . (P x1 x2 y1 y2)"
shows 
  "\<exists>f . \<forall>x1 x2 . \<exists>y1 y2 .
    (f x1 x2) = (y1, y2) 
    \<and> (P x1 x2 (fst (f x1 x2)) (snd (f x1 x2)))"
proof -
  def A2:  P'=="\<lambda>x y . P (fst x) (snd x) (fst y) (snd y)"
  hence "\<forall>x . \<exists>y . (P' x  y)" using A1 by auto
  hence A3: "\<exists>f . \<forall>x . P' x (f x)" by metis
  then obtain f where "\<forall>x . P' x (f x)" by blast
  moreover def f'=="\<lambda>x1 x2. f (x1, x2)"
  ultimately have "\<forall>x . P' x (f' (fst x) (snd x))" by auto
  hence "\<exists>f' . \<forall>x . P' x (f' (fst x) (snd x))" by blast
  thus ?thesis using A2 by auto
qed           

lemma PredicatePairFunctions2: 
fixes
  P::"'a \<Rightarrow> 'b \<Rightarrow> 'c \<Rightarrow> 'd \<Rightarrow> bool"
assumes
  A1: "\<forall>x1 x2 . \<exists>y1 y2 . (P x1 x2 y1 y2)"
obtains f1 f2  where
  "\<forall>x1 x2 . \<exists>y1 y2 .
    (f1 x1 x2) = y1 \<and> (f2 x1 x2) = y2 
    \<and> (P x1 x2 (f1 x1 x2) (f2 x1 x2))"
proof (cases thesis, auto)
  assume ass: "\<And>f1 f2. \<forall>x1 x2. P x1 x2 (f1 x1 x2) (f2 x1 x2) \<Longrightarrow> False"
  obtain f where F: "\<forall>x1 x2. \<exists>y1 y2. f x1 x2 = (y1, y2) \<and> P x1 x2 (fst (f x1 x2)) (snd (f x1 x2))"
    using PredicatePairFunction[OF A1] by blast
  def f1 == "\<lambda>x1 x2 . fst (f x1 x2)"
  def f2 == "\<lambda>x1 x2 . snd (f x1 x2)"
  show False
    using ass[of f1 f2] F unfolding f1_def f2_def by auto
qed

lemma PredicatePairFunctions2Inv: 
fixes
  P::"'a \<Rightarrow> 'b \<Rightarrow> 'c \<Rightarrow> 'd \<Rightarrow> bool"
assumes
  A1: "\<forall>x1 x2 . \<exists>y1 y2 . (P x1 x2 y1 y2)"
obtains f1 f2  where
  "\<forall>x1 x2 . (P x1 x2 (f1 x1 x2) (f2 x1 x2))"
using PredicatePairFunctions2[OF A1] by auto

lemma SmallerMultipleStepsWithLimit:
fixes
  k A limit
assumes
  "\<forall> n \<ge> limit . (A (Suc n)) < (A n)"
shows
  "\<forall> n \<ge> limit . (A (n + k)) \<le> (A n) - k"
proof(induct k,auto)
  fix n k
  assume IH: "\<forall>n\<ge>limit. A (n + k) \<le> A n - k" "limit \<le> n"
  hence "A (Suc (n + k)) < A (n + k)" using assms by simp 
  hence "A (Suc (n + k)) < A n - k" using IH by auto
  thus "A (Suc (n + k)) \<le> A n - Suc k" 
    by (metis Suc_lessI add_Suc_right add_diff_cancel_left' 
       less_diff_conv less_or_eq_imp_le add.commute)
qed

lemma PrefixSameOnLow:
fixes
  l1 l2
assumes
  "prefixList l1 l2"
shows
  "\<forall> index < length l1 . l1 ! index = l2 ! index"
using assms
proof(induct rule: prefixList.induct, auto)
  fix xa xb ::"'a list" and x index
  assume AssumpProof: "prefixList xa xb" 
        "\<forall>index < length xa. xa ! index = xb ! index"
        "prefixList l1 l2" "index < Suc (length xa)"
  show "(x # xa) ! index = (x # xb) ! index" using AssumpProof
  proof(cases "index = 0", auto)
  qed
qed

lemma KeepProperty:
fixes
  P Q low
assumes
  "\<forall> i \<ge> low . P i \<longrightarrow> (P (Suc i) \<and> Q i)" "P low"
shows
  "\<forall> i \<ge> low . Q i"
using assms
proof(clarify)
  fix i
  assume Assump:
    "\<forall>i\<ge>low. P i \<longrightarrow> P (Suc i) \<and> Q i"
    "P low"
    "low \<le> i"
  hence "\<forall>i\<ge>low. P i \<longrightarrow> P (Suc i)" by blast
  hence "\<forall> i \<ge> low . P i" using Assump(2) by (metis dec_induct)
  hence "P i" using Assump(3) by blast
  thus "Q i" using Assump by blast
qed

lemma ListLenDrop:
fixes
  i la lb
assumes
  "i < length lb"
  "i \<ge> la"
shows
  "lb ! i \<in> set (drop la lb)"
using assms
by (metis Cons_nth_drop_Suc in_set_member member_rec(1)
       set_drop_subset_set_drop set_rev_mp)

private
lemma DropToShift:
fixes
  l i list
assumes
  "l + i < length list"
shows
  "(drop l list) ! i = list ! (l + i)"
using assms
by (induct l, auto)

lemma SetToIndex:
fixes
  a and liste::"'a list"
assumes
  AssumpSetToIndex: "a \<in> set liste"
shows
  "\<exists> index < length liste . a = liste ! index"
  by (metis assms in_set_conv_nth)

private
lemma DropToIndex:
fixes
  a::"'a" and l liste 
assumes
  AssumpDropToIndex: "a \<in> set (drop l liste)"
shows
  "\<exists> i \<ge> l . i < length liste \<and> a = liste ! i"
proof-
  have "\<exists> index < length (drop l liste) . a = (drop l liste) ! index"
    using AssumpDropToIndex SetToIndex[of "a" "drop l liste"] by blast
  then obtain index where Index: "index < length (drop l liste)" 
    "a = (drop l liste) ! index" by blast
  have "l + index < length liste" using Index(1) 
    by (metis length_drop less_diff_conv add.commute)
  hence "a = liste ! (l + index)" 
    using DropToShift[of "l" "index"] Index(2) by blast
  thus "\<exists>i\<ge>l. i < length liste \<and> a = liste ! i" 
    by (metis `l + index < length liste` le_add1)
qed

end

end
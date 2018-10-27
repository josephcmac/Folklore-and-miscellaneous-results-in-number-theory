(*
Title: From Schroeder paths to Dyck paths
Author: Jose Manuel Rodriguez Caballero

We prove the following result.

theorem SchroederToDyckPath : \<open>SchroederPath w \<Longrightarrow> DyckPath (removeAll 0 w)\<close>


(This code  was verified in Isabelle2018)
*)

theory SchroederToDyck 

imports Complex_Main DyckPathsDef DyckPathsCharacterization1 SchroederPathsDef

begin


lemma DyckLettersQ : \<open> \<forall> j. j < length w \<longrightarrow> w!j = 1 \<or> w!j = -1 \<Longrightarrow> DyckLetters w\<close>
proof(induction w)
  case Nil
  thus ?case 
    using DyckLetters.simps(1) by blast
next
  case (Cons a w)
  thus ?case 
    by (metis DyckLetters.simps(2) Suc_mono add_diff_cancel_left' length_Cons nth_Cons_0 nth_non_equal_first_eq plus_1_eq_Suc zero_less_Suc)
qed

lemma SchroederLettersQ : \<open>SchroederLetters w \<Longrightarrow> \<forall> j. j < length w \<longrightarrow> w!j = 1 \<or> w!j = -1 \<or> w!j = 0\<close>
proof(induction w)
  case Nil
  thus ?case 
    by simp
next
  case (Cons a w)
  thus ?case 
    by (smt One_nat_def SchroederLetters.simps(2) Suc_less_eq Suc_pred length_Cons less_Suc_eq nth_Cons' zero_less_Suc)
qed

lemma preSchroederToDyckLetters:
  assumes \<open>SchroederLetters w\<close> and \<open>\<forall> j. j < length w \<longrightarrow> w!j \<noteq> 0\<close>
  shows \<open>DyckLetters w\<close>
proof-
  have \<open>\<forall> j. j < length w \<longrightarrow> w!j = 1 \<or> w!j = -1 \<or> w!j = 0\<close> 
    by (simp add: SchroederLettersQ assms(1))
  hence  \<open>\<forall> j. j < length w \<longrightarrow> w!j = 1 \<or> w!j = -1\<close> 
    using \<open>\<forall> j. j < length w \<longrightarrow> w!j \<noteq> 0\<close> 
    by blast
  thus ?thesis 
    using DyckLettersQ by blast
qed



lemma IgnoreNonZero:
  \<open>(removeAll x w ) \<noteq> [] \<Longrightarrow> (removeAll x w)!0 \<noteq> x\<close>
  by (metis (mono_tags, lifting) length_greater_0_conv length_removeAll_less less_irrefl_nat nth_mem removeAll_filter_not removeAll_filter_not_eq)


lemma IgnoreFirst:  \<open>removeAll t (x#w) = x#w \<Longrightarrow> removeAll t w = w\<close>
  by (metis dual_order.irrefl   length_Cons length_removeAll_less list.set(2) list.set_intros(2)  removeAll_id)

lemma IgnoreQRec:
  assumes \<open>removeAll 0 w = w \<longrightarrow> (\<forall> j. j < length w \<longrightarrow> w!j \<noteq> 0)\<close> 
    and \<open>removeAll 0 (x#w) = x#w\<close> and \<open>j < length (x#w)\<close>
  shows \<open>(x#w)!j \<noteq> 0\<close>
proof(cases \<open>j = 0\<close>)
  case True
  thus ?thesis 
    by (metis IgnoreNonZero assms(2) assms(3) less_numeral_extra(3) list.size(3))
next
  case False
  obtain i where \<open>Suc i = j\<close> 
    using False gr0_implies_Suc by auto 
  have \<open>(x#w)!j = w!i\<close> 
    using \<open>Suc i = j\<close> by auto
  from \<open>j < length (x#w)\<close>  \<open>Suc i = j\<close> have \<open>i < length w\<close>
    by auto
  from \<open>removeAll 0 (x#w) = x#w\<close> have \<open>removeAll 0 w = w\<close>
    by (meson IgnoreFirst)
  hence \<open>w ! i \<noteq> 0\<close> 
    using \<open>i < length w\<close> assms(1) by blast
  hence \<open>(x#w)!j \<noteq> 0\<close> 
    by (simp add: \<open>(x # w) ! j = w ! i\<close>)
  thus ?thesis 
    by blast
qed


lemma IgnoreQ: \<open>removeAll 0 w = w \<Longrightarrow> \<forall> j. j < length w \<longrightarrow> w!j \<noteq> 0\<close> 
proof(induction w)
  case Nil
  thus ?case 
    by simp
next
  case (Cons a w)
  thus ?case using IgnoreQRec by blast
qed

lemma IgnoreNot: \<open>removeAll x L \<noteq> L \<Longrightarrow> \<exists> U V. L = U @ [x] @ V \<close>
  by (metis append.left_neutral append_Cons removeAll_id  split_list)

lemma SchroederLettersFactorV: \<open>SchroederLetters (u@v) \<Longrightarrow> SchroederLetters v\<close> 
proof(induction u)
  case Nil
  thus ?case 
    by auto
next
  case (Cons a u)
  thus ?case 
    by (metis SchroederLetters.elims(2) append_Cons list.sel(2) list.sel(3))
qed

lemma SchroederLettersFactorU: \<open>SchroederLetters (u@v) \<Longrightarrow> SchroederLetters u\<close> 
proof(induction u)
  case Nil
  thus ?case 
    by simp
next
  case (Cons a u)
  thus ?case 
    by (metis SchroederLetters.simps(2) append_Cons)
qed


lemma SchroederLettersFactor: \<open>SchroederLetters (u@v@w) \<Longrightarrow> SchroederLetters v\<close> 
  using SchroederLettersFactorU SchroederLettersFactorV 
  by blast

lemma ConcatIgnore: \<open>removeAll x (U@V) = (removeAll x U) @ (removeAll x V)\<close>
  by simp


lemma ConcatDyckLetters: \<open>DyckLetters (U@V) \<longleftrightarrow> (DyckLetters U) \<and> (DyckLetters V)\<close>
proof(induction U)
  case Nil
  thus ?case 
    by simp
next
  case (Cons a U)
  thus ?case 
    by simp
qed

lemma SchroederToDyckLettersEq:
  \<open>\<forall> w.  SchroederLetters w \<and> removeAll 0 w = w \<longrightarrow> DyckLetters (removeAll 0 w)\<close>
  by (simp add: IgnoreQ preSchroederToDyckLetters)

lemma SchroederToDyckLettersNeqIndRec:
  assumes \<open>\<forall> w. length w \<le> n \<and> SchroederLetters w \<and> removeAll 0 w \<noteq> w \<longrightarrow> DyckLetters (removeAll 0 w)\<close>
    and \<open>length w \<le> Suc n\<close> and \<open>SchroederLetters w\<close> and \<open>removeAll 0 w \<noteq> w\<close>
  shows \<open>DyckLetters (removeAll 0 w)\<close>
proof-
  obtain U V where \<open>w = U @ [0] @ V\<close> 
    by (meson IgnoreNot assms(4))
  have \<open>length U \<le> n\<close> 
    using \<open>w = U @ [0] @ V\<close> assms(2) by auto
  have \<open>length V \<le> n\<close> 
    using \<open>w = U @ [0] @ V\<close> assms(2) by auto
  have \<open>SchroederLetters U\<close> using SchroederLettersFactor 
    by (metis \<open>w = U @ [0] @ V\<close> append_Nil assms(3))
  have \<open>SchroederLetters V\<close> using SchroederLettersFactor 
    by (metis (full_types) \<open>w = U @ [0] @ V\<close> assms(3) self_append_conv)
  have \<open>DyckLetters (removeAll 0 U)\<close> 
    using SchroederToDyckLettersEq \<open>SchroederLetters U\<close> \<open>length U \<le> n\<close> assms(1) by blast
  have \<open>DyckLetters (removeAll 0 V)\<close>
    using SchroederToDyckLettersEq \<open>SchroederLetters V\<close> \<open>length V \<le> n\<close> assms(1) by blast
  have \<open>DyckLetters (removeAll 0 (U@V))\<close> 
    by (simp add: ConcatDyckLetters \<open>DyckLetters (removeAll 0 U)\<close> \<open>DyckLetters (removeAll 0 V)\<close>)
  have \<open>removeAll 0 w = removeAll 0 (U @ [0] @ V)\<close>
    by (simp add: \<open>w = U @ [0] @ V\<close>)
  hence \<open>removeAll 0 w = (removeAll 0 U) @  (removeAll 0 [0]) @  (removeAll 0 V)\<close> 
    by auto
  hence \<open>removeAll 0 w = (removeAll 0 U) @  [] @  (removeAll 0 V)\<close> 
    by simp
  hence \<open>removeAll 0 w = (removeAll 0 U) @  (removeAll 0 V)\<close> 
    by simp
  hence \<open>removeAll 0 w = removeAll 0 (U@V)\<close> 
    by simp
  show ?thesis 
    using \<open>DyckLetters (removeAll 0 (U @ V))\<close> \<open>removeAll 0 w = removeAll 0 (U @ V)\<close> by auto
qed

lemma SchroederToDyckLettersNeqInd:
  \<open>\<forall> w. length w \<le> n \<and> SchroederLetters w \<and> removeAll 0 w \<noteq> w \<longrightarrow> DyckLetters (removeAll 0 w)\<close>
proof(induction n)
  case 0
  thus ?case 
    by simp
next
  case (Suc n)
  thus ?case 
    using SchroederToDyckLettersNeqIndRec by blast
qed

lemma SchroederToDyckLettersNeq:
  assumes \<open>SchroederLetters w\<close> \<open>removeAll 0 w \<noteq> w\<close>
  shows \<open>DyckLetters (removeAll 0 w)\<close>
  using SchroederToDyckLettersNeqInd assms(1) assms(2) by blast

lemma SchroederToDyckLetters:
  assumes \<open>SchroederLetters w\<close>
  shows \<open>DyckLetters (removeAll 0 w)\<close>
  using SchroederToDyckLettersEq SchroederToDyckLettersNeq assms by blast

lemma NonNegCharac : \<open>NonNeg w \<longleftrightarrow> (\<forall> j. j < length w \<longrightarrow> w!j \<ge> 0)\<close>
proof(induction w)
  case Nil
  thus ?case 
    by simp
next
  case (Cons a w)
  thus ?case 
    by (metis NonNeg.simps(2) One_nat_def Suc_less_eq Suc_pred length_Cons nth_Cons' nth_Cons_Suc nth_non_equal_first_eq zero_less_Suc)
qed

lemma HeightListRecE :
  \<open>\<forall> x. \<exists> v. HeightList (x#w) = x#(HeightList v) \<and> length (HeightList w) = length (HeightList v)\<close>
proof(induction w)
  case Nil
  thus ?case 
    by (metis HeightList.simps(1) HeightList.simps(2) length_0_conv list.size(3))
next
  case (Cons a w)
  thus ?case 
    by (metis HeightList.simps(3) length_Cons)
qed

lemma LengthHeightList : \<open>length w = length (HeightList w)\<close>
proof(induction w)
  case Nil
  thus ?case 
    by simp
next
  case (Cons a w)
  obtain v where \<open>HeightList (a#w) = a#(HeightList v)\<close> and \<open>length (HeightList w) = length (HeightList v)\<close>
    using HeightListRecE 
    by blast
  assume \<open>length w = length (HeightList w)\<close>
  hence \<open>1+length w = 1+length (HeightList w)\<close>
    by simp
  hence \<open>length (a#w) = 1+length (HeightList w)\<close>
    by simp
  hence \<open>length (a#w) = length (a#(HeightList w))\<close>
    by simp
  have \<open>length (HeightList w) = length w\<close> 
    by (simp add: Cons.IH)
  thus ?case 
    by (simp add: \<open>HeightList (a # w) = a # HeightList v\<close> \<open>length (HeightList w) = length (HeightList v)\<close>)
qed

lemma NonNegPathQ : \<open>NonNegPath w \<longleftrightarrow> (\<forall> j. j < length w \<longrightarrow> (HeightList w)!j \<ge> 0)\<close>
  using NonNegCharac LengthHeightList 
  by auto

lemma HeightListprefix: 
  fixes j :: nat
  assumes \<open>j < length U\<close> 
  shows \<open>(HeightList (U@V))!j = (HeightList U)!j\<close>
proof(cases \<open>U = []\<close>)
  case True
  thus ?thesis 
    using assms by auto
next
  case False
  hence \<open>(HeightList (U@V)) = (HeightList U) @ (incr (HeightList V) (last (HeightList U)))\<close>
    by (simp add: ConcatHeight)
  thus ?thesis 
    by (metis LengthHeightList assms nth_append)
qed


lemma preSchroederToDyckNonNegPathRedA : \<open>\<forall> j. j < length w \<longrightarrow> (HeightList w)!j \<ge> 0
\<Longrightarrow> w = U @ [0] @ V \<Longrightarrow>  j < length U \<Longrightarrow> (HeightList (U@V))!j \<ge> 0\<close>
  by (metis HeightListprefix append.left_neutral append_Cons le_iff_add length_append less_le_trans)

lemma HeightListbeginwithzero: \<open>HeightList (0#w) = 0 # (HeightList w)\<close>
proof(induction w)
  case Nil
  thus ?case 
    by simp
next
  case (Cons a w)
  thus ?case 
    by simp
qed

lemma preSchroederToDyckNonNegPathRedBempty : \<open>\<forall> j. j < length w \<longrightarrow> (HeightList w)!j \<ge> 0
\<Longrightarrow> w =  [0] @ V \<Longrightarrow>  j < length V \<Longrightarrow> (HeightList V)!j \<ge> 0\<close>
  using HeightListbeginwithzero 
  by auto

lemma preSchroederToDyckNonNegPathRedB : \<open>\<forall> j. j < length w \<longrightarrow> (HeightList w)!j \<ge> 0
\<Longrightarrow> w = U @ [0] @ V \<Longrightarrow>  j < length (U@V) \<Longrightarrow> length U \<le> j  \<Longrightarrow> (HeightList (U@V))!j \<ge> 0\<close>
proof(cases \<open>U = []\<close>)
  case True
  assume \<open>\<forall> j. j < length w \<longrightarrow> (HeightList w)!j \<ge> 0\<close>
  assume \<open>w = U @ [0] @ V\<close>
  assume \<open>j < length (U@V)\<close>
  assume \<open>length U \<le> j\<close>
  thus ?thesis using preSchroederToDyckNonNegPathRedBempty 
    by (metis True \<open>\<forall>j<length w. 0 \<le> HeightList w ! j\<close> \<open>j < length (U @ V)\<close> \<open>w = U @ [0] @ V\<close> append_Cons append_Nil)
next
  case False
  assume \<open>\<forall> j. j < length w \<longrightarrow> (HeightList w)!j \<ge> 0\<close>
  assume \<open>w = U @ [0] @ V\<close>
  assume \<open>j < length (U@V)\<close>
  assume \<open>length U \<le> j\<close>
  have \<open>HeightList w = HeightList ((U @ [0]) @ V)\<close> using \<open>w = U @ [0] @ V\<close> by simp
  hence  \<open>HeightList w = (HeightList (U@[0])) @ (incr ((HeightList  V)) (last (HeightList (U@[0]))))\<close>
    by (metis ConcatHeight Nil_is_append_conv list.discI)    
  have \<open>HeightList (U@[0]) = (HeightList U) @ (incr [0] (last (HeightList U)))\<close>
    by (simp add: ConcatHeight False)
  hence \<open>HeightList (U@[0]) = (HeightList U) @ [last (HeightList U)]\<close>
    by simp
  have \<open>last (HeightList (U@[0])) = last (HeightList U)\<close> 
    by (simp add: \<open>HeightList (U @ [0]) = HeightList U @ [last (HeightList U)]\<close>)
  hence  \<open>HeightList w = (HeightList U) @ [last (HeightList U)] @ (incr ((HeightList  V)) (last (HeightList U)))\<close>
    using \<open>HeightList (U @ [0]) = HeightList U @ [last (HeightList U)]\<close> \<open>HeightList w = HeightList (U @ [0]) @ incr (HeightList V) (last (HeightList (U @ [0])))\<close> by auto
  obtain i where \<open>j = (length U) + i\<close> 
    using \<open>length U \<le> j\<close> le_Suc_ex by auto
  have \<open>(HeightList w)!(j+1) =  (incr ((HeightList  V)) (last (HeightList U)))!i\<close>
    by (metis LengthHeightList \<open>HeightList w = HeightList (U @ [0]) @ incr (HeightList V) (last (HeightList (U @ [0])))\<close> \<open>j = length U + i\<close> \<open>last (HeightList (U @ [0])) = last (HeightList U)\<close> add.commute length_append_singleton nth_append_length_plus plus_1_eq_Suc plus_nat.simps(2))
  have \<open>(HeightList w)!(j+1) = (HeightList (U@V))!j\<close> 
    by (metis ConcatHeight False LengthHeightList \<open>HeightList w ! (j + 1) = incr (HeightList V) (last (HeightList U)) ! i\<close> \<open>j = length U + i\<close> nth_append_length_plus)
  have \<open>(HeightList (U@V))!j =  (incr ((HeightList  V)) (last (HeightList U)))!i\<close>
    using \<open>HeightList w ! (j + 1) = HeightList (U @ V) ! j\<close> \<open>HeightList w ! (j + 1) = incr (HeightList V) (last (HeightList U)) ! i\<close> by auto
  thus ?thesis 
    using \<open>HeightList w ! (j + 1) = incr (HeightList V) (last (HeightList U)) ! i\<close> \<open>\<forall>j<length w. 0 \<le> HeightList w ! j\<close> \<open>j < length (U @ V)\<close> \<open>w = U @ [0] @ V\<close> by auto
qed





lemma preSchroederToDyckNonNegPathRedS : \<open>\<forall> j. j < length w \<longrightarrow> (HeightList w)!j \<ge> 0
\<Longrightarrow> w = U @ [0] @ V \<Longrightarrow>  j < length (U@V) \<Longrightarrow> (HeightList (U@V))!j \<ge> 0\<close>
  using preSchroederToDyckNonNegPathRedA preSchroederToDyckNonNegPathRedB
  by (metis leI)

lemma preSchroederToDyckNonNegPathRed : \<open>\<forall> j. j < length w \<longrightarrow> (HeightList w)!j \<ge> 0
\<Longrightarrow> w = U @ [0] @ V \<Longrightarrow> \<forall> j. j < length (U@V) \<longrightarrow> (HeightList (U@V))!j \<ge> 0\<close>
  using preSchroederToDyckNonNegPathRedS by blast

lemma preSchroederToDyckNonNegPathIndRec :
  assumes \<open>\<forall> w. length w = n + length(removeAll 0 w) \<and> (\<forall> j. j < length w \<longrightarrow> (HeightList w)!j \<ge> 0)
 \<longrightarrow> (\<forall> j. j < length (removeAll 0 w) \<longrightarrow> (HeightList (removeAll 0 w))!j \<ge> 0)\<close>
    and \<open>length w = (Suc n) + length(removeAll 0 w)\<close> \<open>\<forall> j. j < length w \<longrightarrow> (HeightList w)!j \<ge> 0\<close>
  shows \<open>\<forall> j. j < length (removeAll 0 w) \<longrightarrow> (HeightList (removeAll 0 w))!j \<ge> 0\<close>
proof-
  have  \<open>w \<noteq> removeAll 0 w\<close> 
    using assms(2) by auto
  then obtain U V where \<open>w = U @ [0] @ V\<close> 
    by (metis IgnoreNot)
  have \<open>removeAll 0 (U @ [0] @ V) = removeAll 0 (U @ V)\<close> 
    by simp
  hence \<open>removeAll 0 w = removeAll 0 (U @ V)\<close> 
    using \<open>w = U @ [0] @ V\<close> by blast
  hence \<open>length (U@V) = n + length(removeAll 0 (U@V))\<close>
    using \<open>w = U @ [0] @ V\<close> assms(2) by auto
  have \<open>\<forall> j. j < length (U@V) \<longrightarrow> (HeightList (U@V))!j \<ge> 0\<close>
    using \<open>\<forall>j<length w. 0 \<le> HeightList w ! j\<close> \<open>w = U @ [0] @ V\<close> preSchroederToDyckNonNegPathRed by blast
  have  \<open>\<forall> j. j < length (removeAll 0 (U@V)) \<longrightarrow> (HeightList (removeAll 0 (U@V)))!j \<ge> 0\<close>
    using  \<open>\<forall> j. j < length (U@V) \<longrightarrow> (HeightList (U@V))!j \<ge> 0\<close>  \<open>length (U@V) = n + length(removeAll 0 (U@V))\<close>
      \<open>\<forall> w. length w = n + length(removeAll 0 w) \<and> (\<forall> j. j < length w \<longrightarrow> (HeightList w)!j \<ge> 0)
 \<longrightarrow> (\<forall> j. j < length (removeAll 0 w) \<longrightarrow> (HeightList (removeAll 0 w))!j \<ge> 0)\<close>
    by blast
  thus ?thesis 
    by (simp add: \<open>removeAll 0 w = removeAll 0 (U @ V)\<close>)
qed


lemma preSchroederToDyckNonNegPathInd : \<open>\<forall> w. length w = n + length(removeAll 0 w) \<and> (\<forall> j. j < length w \<longrightarrow> (HeightList w)!j \<ge> 0)
 \<longrightarrow> (\<forall> j. j < length (removeAll 0 w) \<longrightarrow> (HeightList (removeAll 0 w))!j \<ge> 0)\<close>
proof(induction n)
  case 0
  thus ?case 
    by (metis add.left_neutral length_removeAll_less not_add_less2 removeAll_id)
next
  case (Suc n)
  thus ?case using preSchroederToDyckNonNegPathIndRec 
    by blast
qed


lemma preSchroederToDyckNonNegPath : \<open>\<forall> j. j < length w \<longrightarrow> (HeightList w)!j \<ge> 0
 \<Longrightarrow> \<forall> j. j < length (removeAll 0 w) \<longrightarrow> (HeightList (removeAll 0 w))!j \<ge> 0\<close>
  using preSchroederToDyckNonNegPathInd 
  by (metis add.commute le_iff_add length_removeAll_less_eq)


lemma SchroederToDyckNonNegPath : \<open>NonNegPath w \<Longrightarrow> NonNegPath (removeAll 0 w)\<close>
proof-
  assume \<open>NonNegPath w\<close>
  hence \<open>\<forall> j. j < length w \<longrightarrow> (HeightList w)!j \<ge> 0\<close> 
    using NonNegPathQ by blast
  hence \<open>\<forall> j. j < length (removeAll 0 w) \<longrightarrow> (HeightList (removeAll 0 w))!j \<ge> 0\<close> 
    by (simp add: preSchroederToDyckNonNegPath)
  thus ?thesis 
    using NonNegPathQ by blast
qed

lemma preSchroederToDycklastHeightListXY:
  assumes \<open>\<forall> w. length w = n + length (removeAll 0 w) \<and> (removeAll 0 w) \<noteq> [] \<longrightarrow> last (HeightList w) = last (HeightList (removeAll 0 w))\<close>
    and \<open>length w = Suc n + length (removeAll 0 w)\<close> and \<open>(removeAll 0 w) \<noteq> []\<close>
  shows \<open>last (HeightList w) = last (HeightList (removeAll 0 w))\<close>
proof-
  from \<open>length w = Suc n + length (removeAll 0 w)\<close> 
  have \<open>w \<noteq> removeAll 0 w\<close> 
    by auto
  obtain U V where \<open>w = U @ [0] @ V\<close> 
    by (metis IgnoreNot \<open>w \<noteq> removeAll 0 w\<close>)
  have \<open>length (U@V) =  n + length (removeAll 0 (U@V))\<close>
    using \<open>w = U @ [0] @ V\<close> assms(2) by auto
  have \<open>(removeAll 0 w) = (removeAll 0 (U@V))\<close>
    by (simp add: \<open>w = U @ [0] @ V\<close>)
  have \<open>(removeAll 0 (U@V)) \<noteq> []\<close> 
    using \<open>removeAll 0 w = removeAll 0 (U @ V)\<close> assms(3) by auto
  have \<open>last (HeightList  (U @ V)) = last (HeightList (removeAll 0  (U @ V)))\<close>
    using \<open>length (U @ V) = n + length (removeAll 0 (U @ V))\<close> \<open>removeAll 0 (U @ V) \<noteq> []\<close> assms(1) by blast
  have \<open>last (HeightList w) = last (HeightList (U@V))\<close> 
    by (smt ConcatHeightSum HeightList.simps(2) \<open>length (U @ V) = n + length (removeAll 0 (U @ V))\<close> \<open>removeAll 0 (U @ V) \<noteq> []\<close> \<open>w = U @ [0] @ V\<close> append.right_neutral append_is_Nil_conv append_self_conv2 last.simps length_0_conv zero_eq_add_iff_both_eq_0)
  show ?thesis 
    by (simp add: \<open>last (HeightList (U @ V)) = last (HeightList (removeAll 0 (U @ V)))\<close> \<open>last (HeightList w) = last (HeightList (U @ V))\<close> \<open>removeAll 0 w = removeAll 0 (U @ V)\<close>)
qed


lemma preSchroederToDycklastHeightListX: \<open>\<forall> w. length w = n + length (removeAll 0 w) \<and> (removeAll 0 w) \<noteq> [] \<longrightarrow> last (HeightList w) = last (HeightList (removeAll 0 w))\<close>
proof(induction n)
  case 0
  thus ?case 
    by (metis add.left_neutral length_removeAll_less not_add_less2 removeAll_id)
next
  case (Suc n)
  thus ?case using preSchroederToDycklastHeightListXY 
    by blast
qed

lemma SchroederToDycklastHeightListX: \<open>(removeAll 0 w) \<noteq> [] \<Longrightarrow> last (HeightList w) = last (HeightList (removeAll 0 w))\<close>
  using preSchroederToDycklastHeightListX 
  by (metis add.commute le_Suc_ex length_removeAll_less_eq)

lemma SchroederToDycklastHeightList: \<open>w \<noteq> [] \<longrightarrow> last (HeightList w) = 0 \<Longrightarrow> (removeAll 0 w) \<noteq> [] \<longrightarrow> last (HeightList (removeAll 0 w)) = 0\<close>
  using SchroederToDycklastHeightListX 
  by (metis removeAll.simps(1))

theorem SchroederToDyckPath : \<open>SchroederPath w \<Longrightarrow> DyckPath (removeAll 0 w)\<close>
  using SchroederToDyckLetters SchroederToDyckNonNegPath SchroederToDycklastHeightList
  by simp



end

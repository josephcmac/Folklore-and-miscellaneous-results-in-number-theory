(*
Title: The frequency of a letter in a Dyck word
Author: Jose Manuel Rodriguez Caballero

We shall prove the following result.

theorem DyckListDCHRLengthAbstr:
 \<open>DyckPath w \<Longrightarrow> 2*length (DyckListDCHR c w) = length w \<close>


(This code  was verified in Isabelle2018)

*)

theory DyckPathHalfLength

imports Complex_Main ErdosNicolasOdd DyckPathHeight

begin
 
lemma DyckListDCHRLengthAbstrEqDyckPHeight0Set:
 \<open>DyckPHeight w = 0 \<Longrightarrow> (card (DyckSetDCHR up w)) = (card (DyckSetDCHR down w)) \<close>
  using DyckListDCHRLengthAbstrEqDyckPHeight0SetForm 
  by simp

lemma DyckListDCHRLengthAbstrEqDyckPHeight0:
 \<open>DyckPHeight w = 0 \<Longrightarrow> (length (DyckListDCHR up w)) = (length (DyckListDCHR down w)) \<close>
proof-
  assume \<open>DyckPHeight w = 0\<close>
  then have \<open>(card (DyckSetDCHR up w)) = (card (DyckSetDCHR down w))\<close> using DyckListDCHRLengthAbstrEqDyckPHeight0Set
    by blast
  have \<open>(length (DyckListDCHR up w)) = (card (DyckSetDCHR up w))\<close> 
    by (simp add: DyckListDCHR_def DyckSetDCHR_def FinSetToListCard)
  have \<open>(length (DyckListDCHR down w)) = (card (DyckSetDCHR down w))\<close> 
    by (simp add: DyckListDCHR_def DyckSetDCHR_def FinSetToListCard)
  show ?thesis 
    by (simp add: \<open>card (DyckSetDCHR up w) = card (DyckSetDCHR down w)\<close> \<open>length (DyckListDCHR down w) = card (DyckSetDCHR down w)\<close> \<open>length (DyckListDCHR up w) = card (DyckSetDCHR up w)\<close>)
qed

lemma DyckListDCHRLengthAbstrEq:
 \<open>DyckPath w \<Longrightarrow> (length (DyckListDCHR up w)) = (length (DyckListDCHR down w)) \<close>
proof-
  assume \<open>DyckPath w\<close>
  then have \<open>DyckPHeight w = 0\<close>
    by (simp add: AbstractPath_def DyckPath_def)
  then show ?thesis using DyckListDCHRLengthAbstrEqDyckPHeight0 
    by simp
qed

lemma DyckListDCHRLengthAbstrUnion:
 \<open>  (DyckSetDCHR up w)\<union>(DyckSetDCHR down w) = {j | j :: nat. j < length w} \<close>
proof-
  have \<open> (DyckSetDCHR up w)\<union>(DyckSetDCHR down w) = {j | j :: nat. (j < length w \<and> w ! j = up) \<or>  (j < length w \<and> w ! j = down) }\<close>
    by (smt Collect_cong DyckSetDCHR_def Un_def mem_Collect_eq)
  then have  \<open> (DyckSetDCHR up w)\<union>(DyckSetDCHR down w) = {j | j :: nat. (j < length w \<and> (w ! j = up \<or> w ! j = down) )}\<close>
    by auto
  then show ?thesis 
    by (smt Collect_cong DCHR.exhaust)
qed

lemma DyckListDCHRLengthAbstrInter:
 \<open>  (DyckSetDCHR up w)\<inter>(DyckSetDCHR down w) = {} \<close>
  by (metis (mono_tags, lifting) DCHR.distinct(1) DyckSetDCHR_def Int_emptyI mem_Collect_eq)


lemma DyckListDCHRLengthAbstrCardSum:
 \<open>  card (DyckSetDCHR up w) + card (DyckSetDCHR down w) = length w \<close>
proof-
  have \<open>card  {j | j::nat. j < length w} = length w\<close> 
    by auto
  then have \<open>finite {j | j :: nat. j < length w}\<close> by simp
  have  \<open> (DyckSetDCHR up w)\<union>(DyckSetDCHR down w) = {j | j :: nat. j < length w} \<close>
    using DyckListDCHRLengthAbstrUnion by auto
  then have \<open>finite (DyckSetDCHR up w)\<close> 
    by (simp add: DyckSetDCHR_def)
  then have \<open>finite (DyckSetDCHR down w)\<close> 
    by (simp add: DyckSetDCHR_def)
  have  \<open>  (DyckSetDCHR up w)\<inter>(DyckSetDCHR down w) = {} \<close> 
    by (simp add: DyckListDCHRLengthAbstrInter)
  show ?thesis 
    by (metis \<open>DyckSetDCHR up w \<inter> DyckSetDCHR down w = {}\<close> \<open>DyckSetDCHR up w \<union> DyckSetDCHR down w = {j |j. j < length w}\<close> \<open>card {j |j. j < length w} = length w\<close> \<open>finite (DyckSetDCHR down w)\<close> \<open>finite (DyckSetDCHR up w)\<close> card_Un_disjoint)
qed

lemma DyckListDCHRLengthAbstrSum:
 \<open> (length (DyckListDCHR up w))+(length (DyckListDCHR down w)) = length w \<close>
proof-
 have \<open>card  {j | j::nat. j < length w} = length w\<close> 
    by auto
  then have \<open>finite {j | j :: nat. j < length w}\<close> by simp
  have  \<open> (DyckSetDCHR up w)\<union>(DyckSetDCHR down w) = {j | j :: nat. j < length w} \<close>
    using DyckListDCHRLengthAbstrUnion by auto
  then have \<open>finite (DyckSetDCHR up w)\<close> 
    by (simp add: DyckSetDCHR_def)
  then have \<open>finite (DyckSetDCHR down w)\<close> 
    by (simp add: DyckSetDCHR_def)

  from  \<open>finite (DyckSetDCHR up w)\<close>
  have \<open>(length (DyckListDCHR up w)) = card (DyckSetDCHR up w)\<close> 
    by (simp add: DyckListDCHR_def FinSetToListCard)

  from  \<open>finite (DyckSetDCHR down w)\<close>
  have \<open>(length (DyckListDCHR down w)) = card (DyckSetDCHR down w)\<close> 
    by (simp add: DyckListDCHR_def FinSetToListCard)

  have  \<open>  card (DyckSetDCHR up w) + card (DyckSetDCHR down w) = length w \<close>
    by (simp add: DyckListDCHRLengthAbstrCardSum)
  then show ?thesis 
    by (simp add: \<open>length (DyckListDCHR down w) = card (DyckSetDCHR down w)\<close> \<open>length (DyckListDCHR up w) = card (DyckSetDCHR up w)\<close>)
qed

theorem DyckListDCHRLengthAbstr:
 \<open>DyckPath w \<Longrightarrow> 2*length (DyckListDCHR c w) = length w \<close>
  by (metis (full_types) DCHR.exhaust DyckListDCHRLengthAbstrEq DyckListDCHRLengthAbstrSum mult_2)



end
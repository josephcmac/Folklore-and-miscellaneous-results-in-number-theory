(*
Title: The height of a Dyck path
Author: Jose Manuel Rodriguez Caballero

We define the height of a Dyck path as the maximum of all partial heights.


definition DyckHeight :: \<open>DCHR list \<Rightarrow> int\<close> where
\<open>DyckHeight \<equiv> \<lambda> w. Max {DyckPHeight v | v. prefix v w}\<close>

We provide the following characterization for the height of a Dyck path.


theorem DyckHeightCharacterization1:
 \<open>DyckHeight w = Max {((card (DyckSetDCHR up v))::int) - ((card (DyckSetDCHR down v))::int) | v. prefix v w}\<close>


Reference:

@article{caballero2017symmetric,
  title={Symmetric Dyck Paths and Hooley’s ∆-function},
  author={Caballero, Jos{\'e} Manuel Rodr{\i}guez},
  journal={Combinatorics on Words. Springer International Publishing AG},
  year={2017}
}


(This code  was verified in Isabelle2018)

*)


theory DyckPathHeight

imports Complex_Main  DyckTypeLengthDiv

begin
definition DyckSetDCHR :: \<open> DCHR \<Rightarrow> DCHR list \<Rightarrow> nat set \<close> where
\<open>DyckSetDCHR \<equiv> \<lambda> c :: DCHR. \<lambda> w :: DCHR list. {j | j::nat. j < length w \<and> w ! j = c}\<close>

definition DyckListDCHR :: \<open> DCHR \<Rightarrow> DCHR list \<Rightarrow> nat list \<close> where
\<open>DyckListDCHR \<equiv> \<lambda> c :: DCHR.  \<lambda> w :: DCHR list. sorted_list_of_set (DyckSetDCHR c w)\<close>

definition DyckHeight :: \<open>DCHR list \<Rightarrow> int\<close> where
\<open>DyckHeight \<equiv> \<lambda> w. Max {DyckPHeight v | v. prefix v w}\<close>

section {* Auxiliary Results *}

lemma FinSetToListCard3:
\<open> L = sorted_list_of_set (set L) \<Longrightarrow> length L = card (set L)\<close>
  by (metis distinct_card distinct_sorted_list_of_set)

lemma FinSetToListCard2:
\<open>finite S \<Longrightarrow> set (sorted_list_of_set S) =  S \<Longrightarrow>  length (sorted_list_of_set S) = card S\<close>
  by (simp add: FinSetToListCard3)

lemma FinSetToListCard1:
\<open>finite S \<Longrightarrow> set (sorted_list_of_set S) =  S\<close>
  by simp

lemma FinSetToListCard:
\<open>finite S \<Longrightarrow> length (sorted_list_of_set S) = card S\<close>
  by (simp add: FinSetToListCard2)

lemma DyckSetDCHRFIN:
\<open>finite (DyckSetDCHR c w)\<close>
  by (metis (no_types, lifting) CollectD DyckSetDCHR_def  finite_lessThan finite_nat_set_iff_bounded_le lessThan_iff )

lemma DyckSetDCHRDyckSetDCHRDyckSetDCHREqNonZero:
\<open>{0} \<inter> {Suc j | j. j \<in> (S :: nat set)} = {}\<close>
  by blast

lemma DyckSetDCHRDyckSetDCHRDyckSetDCHREqSet:
\<open>c = d \<Longrightarrow> (DyckSetDCHR c (d # w)) = {0} \<union> {Suc j | j. j \<in> (DyckSetDCHR c w)}\<close>
proof-
  assume \<open>c = d\<close>
  have \<open>(DyckSetDCHR c (d # w)) = {j | j. j < length (d # w) \<and> (d # w) ! j = c}\<close>
    using DyckSetDCHR_def by presburger
  then have \<open>(DyckSetDCHR c (d # w)) = {j | j. j < Suc (length w) \<and> (d # w) ! j = c}\<close>
    by simp
  then have \<open>(DyckSetDCHR c (d # w)) = {j | j. (j = 0 \<and> j < Suc (length w) \<and> (d # w) ! j = c)\<or>(j \<noteq> 0 \<and> j < Suc (length w) \<and> (d # w) ! j = c)}\<close>
    by blast
  then have \<open>(DyckSetDCHR c (d # w)) = {j | j. (j = 0 \<and> j < Suc (length w) \<and> (d # w) ! j = c)} \<union> {j | j. (j \<noteq> 0 \<and> j < Suc (length w) \<and> (d # w) ! j = c)}\<close>
    by blast
  then have \<open>(DyckSetDCHR c (d # w)) = {0} \<union> {j | j. (j \<noteq> 0 \<and> j < Suc (length w) \<and> (d # w) ! j = c)}\<close>
    using \<open>c = d\<close> by force

  then have \<open>(DyckSetDCHR c (d # w)) = {0} \<union> {Suc j | j. ( Suc j < Suc (length w) \<and> (d # w) ! (Suc j) = c)}\<close>
    using less_Suc_eq_0_disj by fastforce
  then have \<open>(DyckSetDCHR c (d # w)) = {0} \<union> {Suc j | j. (  j <  (length w) \<and> (d # w) ! (Suc j) = c)}\<close>
    by auto
  then have \<open>(DyckSetDCHR c (d # w)) = {0} \<union> {Suc j | j. (  j <  (length w) \<and>  w ! j = c)}\<close>
    by auto
  then show ?thesis 
    by (smt Collect_cong DyckSetDCHR_def mem_Collect_eq)
qed


lemma DyckSetDCHRDyckSetDCHRDyckSetDCHRNoneqSet:
\<open>c \<noteq> d \<Longrightarrow> (DyckSetDCHR c (d # w)) =  {Suc j | j. j \<in> (DyckSetDCHR c w)}\<close>
proof-
  assume \<open>c \<noteq> d\<close>
  have \<open>(DyckSetDCHR c (d # w)) = {j | j. j < length (d # w) \<and> (d # w) ! j = c}\<close>
    using DyckSetDCHR_def by presburger
  then have \<open>(DyckSetDCHR c (d # w)) = {j | j. j < Suc (length w) \<and> (d # w) ! j = c}\<close>
    by simp
  then have \<open>(DyckSetDCHR c (d # w)) = {j | j. (j = 0 \<and> j < Suc (length w) \<and> (d # w) ! j = c)\<or>(j \<noteq> 0 \<and> j < Suc (length w) \<and> (d # w) ! j = c)}\<close>
    by blast
  then have \<open>(DyckSetDCHR c (d # w)) = {j | j. (j = 0 \<and> j < Suc (length w) \<and> (d # w) ! j = c)} \<union> {j | j. (j \<noteq> 0 \<and> j < Suc (length w) \<and> (d # w) ! j = c)}\<close>
    by blast
  then have \<open>(DyckSetDCHR c (d # w)) = {} \<union> {j | j. (j \<noteq> 0 \<and> j < Suc (length w) \<and> (d # w) ! j = c)}\<close>
    using \<open>c \<noteq> d\<close> by force
  then have \<open>(DyckSetDCHR c (d # w)) = {j | j. (j \<noteq> 0 \<and> j < Suc (length w) \<and> (d # w) ! j = c)}\<close>
    by simp
  then have \<open>(DyckSetDCHR c (d # w)) = {Suc j | j. ( Suc j < Suc (length w) \<and> (d # w) ! (Suc j) = c)}\<close>
    using less_Suc_eq_0_disj by fastforce
  then have \<open>(DyckSetDCHR c (d # w)) = {Suc j | j. (  j <  (length w) \<and> (d # w) ! (Suc j) = c)}\<close>
    by auto
  then have \<open>(DyckSetDCHR c (d # w)) = {Suc j | j. (  j <  (length w) \<and>  w ! j = c)}\<close>
    by auto
  then show ?thesis 
    by (smt Collect_cong DyckSetDCHR_def mem_Collect_eq)
qed

lemma DyckSetDCHRDyckSetDCHRDyckSetDCHREq:
\<open>c = d \<Longrightarrow> card (DyckSetDCHR c (d # w)) = 1 + card (DyckSetDCHR c w)\<close>
proof-
  assume \<open>c = d\<close>
  then have  \<open>(DyckSetDCHR c (d # w)) = {0} \<union> {Suc j | j. j \<in> (DyckSetDCHR c w)}\<close>
    using DyckSetDCHRDyckSetDCHRDyckSetDCHREqSet by auto
  have \<open>{0} \<inter> {Suc j | j. j \<in> (DyckSetDCHR c w)} = {}\<close> 
    by simp
  have \<open>finite ((DyckSetDCHR c (d # w)))\<close> 
    by (simp add: DyckSetDCHRFIN)
  have \<open> card (DyckSetDCHR c (d # w)) = 1 + card  {Suc j | j. j \<in> (DyckSetDCHR c w)}\<close>
    using \<open>DyckSetDCHR c (d # w) = {0} \<union> {Suc j |j. j \<in> DyckSetDCHR c w}\<close> \<open>finite (DyckSetDCHR c (d # w))\<close> by auto
  have \<open>inj Suc\<close> by auto
  have \<open> Suc ` {j | j. j \<in> (DyckSetDCHR c w)} = {Suc j | j. j \<in> (DyckSetDCHR c w)}\<close>
    by (simp add: setcompr_eq_image)
  have \<open>bij_betw Suc  {j | j. j \<in> (DyckSetDCHR c w)} {Suc j | j. j \<in> (DyckSetDCHR c w)}\<close>
    by auto
  have  \<open>card  {j | j. j \<in> (DyckSetDCHR c w)} = card  {Suc j | j. j \<in> (DyckSetDCHR c w)}\<close>
    using \<open>bij_betw Suc {j |j. j \<in> DyckSetDCHR c w} {Suc j |j. j \<in> DyckSetDCHR c w}\<close> bij_betw_same_card by blast
  then have \<open>card  (DyckSetDCHR c w) = card  {Suc j | j. j \<in> (DyckSetDCHR c w)}\<close>
    by auto
    show ?thesis 
      by (simp add: \<open>card (DyckSetDCHR c (d # w)) = 1 + card {Suc j |j. j \<in> DyckSetDCHR c w}\<close> \<open>card (DyckSetDCHR c w) = card {Suc j |j. j \<in> DyckSetDCHR c w}\<close>)
  qed

lemma DyckSetDCHRDyckSetDCHRDyckSetDCHRNeq:
\<open>c \<noteq> d \<Longrightarrow> card (DyckSetDCHR c (d # w)) =  card (DyckSetDCHR c w)\<close>
proof-
  assume \<open>c \<noteq> d\<close>
  then have  \<open>(DyckSetDCHR c (d # w)) = {Suc j | j. j \<in> (DyckSetDCHR c w)}\<close>
    using DyckSetDCHRDyckSetDCHRDyckSetDCHRNoneqSet by auto
  have \<open>inj Suc\<close> by auto
  have \<open> Suc ` {j | j. j \<in> (DyckSetDCHR c w)} = {Suc j | j. j \<in> (DyckSetDCHR c w)}\<close>
    by (simp add: setcompr_eq_image)
  have \<open>bij_betw Suc  {j | j. j \<in> (DyckSetDCHR c w)} {Suc j | j. j \<in> (DyckSetDCHR c w)}\<close>
    by auto
  have  \<open>card  {j | j. j \<in> (DyckSetDCHR c w)} = card  {Suc j | j. j \<in> (DyckSetDCHR c w)}\<close>
    using \<open>bij_betw Suc {j |j. j \<in> DyckSetDCHR c w} {Suc j |j. j \<in> DyckSetDCHR c w}\<close> bij_betw_same_card by blast
  then have \<open>card  (DyckSetDCHR c w) = card  {Suc j | j. j \<in> (DyckSetDCHR c w)}\<close>
    by auto
    show ?thesis 
      by (simp add: \<open>DyckSetDCHR c (d # w) = {Suc j |j. j \<in> DyckSetDCHR c w}\<close> \<open>card (DyckSetDCHR c w) = card {Suc j |j. j \<in> DyckSetDCHR c w}\<close>)
  qed

lemma DyckListDCHRLengthAbstrEqDyckPHeight0SetFormRecUp:
  assumes \<open>DyckPHeight w = ((card (DyckSetDCHR up w))::int) - ((card (DyckSetDCHR down w))::int) \<close>
  shows  \<open>DyckPHeight (up # w) = ((card (DyckSetDCHR up (up # w)))::int) - ((card (DyckSetDCHR down (up # w)))::int) \<close>
  using assms DyckSetDCHRDyckSetDCHRDyckSetDCHREq DyckSetDCHRDyckSetDCHRDyckSetDCHRNeq
  by (simp add: DyckPHeight_def)

lemma DyckListDCHRLengthAbstrEqDyckPHeight0SetFormRecDown:
  assumes \<open>DyckPHeight w = ((card (DyckSetDCHR up w))::int) - ((card (DyckSetDCHR down w))::int) \<close>
  shows  \<open>DyckPHeight (down # w) = ((card (DyckSetDCHR up (down # w)))::int) - ((card (DyckSetDCHR down (down # w)))::int) \<close>
  using assms DyckSetDCHRDyckSetDCHRDyckSetDCHREq DyckSetDCHRDyckSetDCHRDyckSetDCHRNeq
  by (simp add: DyckPHeight_def)

lemma DyckListDCHRLengthAbstrEqDyckPHeight0SetFormRec:
  assumes \<open>DyckPHeight w = ((card (DyckSetDCHR up w))::int) - ((card (DyckSetDCHR down w))::int) \<close>
  shows  \<open>DyckPHeight (a # w) = ((card (DyckSetDCHR up (a # w)))::int) - ((card (DyckSetDCHR down (a # w)))::int) \<close>
  using DyckListDCHRLengthAbstrEqDyckPHeight0SetFormRecUp DyckListDCHRLengthAbstrEqDyckPHeight0SetFormRecDown
  by (metis (full_types) DCHR.exhaust assms)

lemma DyckListDCHRLengthAbstrEqDyckPHeight0SetForm:
 \<open>DyckPHeight w = ((card (DyckSetDCHR up w))::int) - ((card (DyckSetDCHR down w))::int) \<close>
proof(induction w)
  case Nil
  have \<open>DyckPHeight [] = 0\<close> 
    by (simp add: DyckPHeight_def)
  have \<open>DyckSetDCHR up [] = {}\<close> 
    by (simp add: DyckSetDCHR_def)
  then have \<open>((card (DyckSetDCHR up []))::int) = 0\<close> 
    by simp
  have \<open>DyckSetDCHR down [] = {}\<close> 
    by (simp add: DyckSetDCHR_def)
  then have \<open>((card (DyckSetDCHR down []))::int) = 0\<close> 
    by simp    
  then show ?case 
    by (simp add: \<open>DyckPHeight [] = 0\<close> \<open>int (card (DyckSetDCHR up [])) = 0\<close>)
next
  case (Cons a w)
  then show ?case 
    using DyckListDCHRLengthAbstrEqDyckPHeight0SetFormRec by blast 
qed

section {* Main Result *}

theorem DyckHeightCharacterization1:
 \<open>DyckHeight w = Max {((card (DyckSetDCHR up v))::int) - ((card (DyckSetDCHR down v))::int) | v. prefix v w}\<close>
  using DyckHeight_def  DyckListDCHRLengthAbstrEqDyckPHeight0SetForm by presburger



end


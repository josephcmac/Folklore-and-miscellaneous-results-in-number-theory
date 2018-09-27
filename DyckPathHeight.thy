(*
Title: The height of a Dyck path
Author: Jose Manuel Rodriguez Caballero

We define the height of a Dyck path as the maximum of all partial heights.


definition DyckHeight :: \<open>DCHR list \<Rightarrow> int\<close> where
\<open>DyckHeight \<equiv> \<lambda> w. Max {DyckPHeight v | v. prefix v w}\<close>

We provide the following characterization for the height of a Dyck path.

theorem DyckHeightCharacterization:
 \<open> DyckPath w \<Longrightarrow> w \<noteq> [] \<Longrightarrow> DyckHeight w = Max {((card (DyckSetDCHR up v))::int) - ((card (DyckSetDCHR down v))::int) | v. prefix v w \<and> last v = up \<and> v \<noteq> []}\<close>


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


lemma preDyckHeightCharacterization:
 \<open>DyckHeight w = Max {((card (DyckSetDCHR up v))::int) - ((card (DyckSetDCHR down v))::int) | v. prefix v w}\<close>
  using DyckHeight_def  DyckListDCHRLengthAbstrEqDyckPHeight0SetForm by presburger

lemma lastcharlist:
 \<open>v \<noteq> [] \<Longrightarrow> last (v :: DCHR list) = down \<Longrightarrow> \<exists> u. v = u @ [down]\<close>
  by (metis last_snoc rev_exhaust)

lemma DyckSetDCHRup:
 \<open> ((card (DyckSetDCHR up (u @ [down])))::int) = ((card (DyckSetDCHR up u))::int) \<close>
proof-
  have \<open>(DyckSetDCHR up (u @ [down])) = {j | j::nat. j < length (u @ [down]) \<and> (u @ [down]) ! j = up}\<close>
    using DyckSetDCHR_def 
    by presburger
  then have \<open>(DyckSetDCHR up (u @ [down])) = {j | j::nat. j < length u \<and> (u @ [down]) ! j = up}\<close>
    by (smt Collect_cong DCHR.distinct(1) Suc_leI length_append_singleton lessI less_le_trans not_le not_less_iff_gr_or_eq nth_append_length)
  then have \<open>(DyckSetDCHR up (u @ [down])) = {j | j::nat. j < length u \<and> u ! j = up}\<close>
    by (metis (no_types, lifting) Collect_cong butlast_snoc nth_butlast)
  then show ?thesis 
    using DyckSetDCHR_def by metis
qed


lemma DyckSetDCHRdown:
 \<open> ((card (DyckSetDCHR down (u @ [down])))::int) = ((card (DyckSetDCHR down u))::int) + (1::int)\<close>
proof-
  have  \<open>{j | j::nat. (j = length u \<and> (u @ [down]) ! j = down)} = {length u}\<close>
    by auto  
  have \<open>{j | j::nat. (j < length u \<and> (u @ [down]) ! j = down) } \<inter> {length u} = {}\<close>
    by blast
  have \<open>finite {j | j::nat. (j = length u \<and> (u @ [down]) ! j = down)}\<close>
    by simp
  have \<open>DyckSetDCHR down u = {j | j::nat. j < length u  \<and> u ! j = down}\<close>
    using DyckSetDCHR_def by presburger
  have \<open>DyckSetDCHR down (u @ [down]) = {j | j::nat. j < length (u @ [down]) \<and> (u @ [down]) ! j = down}\<close>
    using DyckSetDCHR_def by presburger
  then have  \<open>DyckSetDCHR down (u @ [down]) = {j | j::nat. (j < length u \<and> (u @ [down]) ! j = down)\<or>(j = length u \<and> (u @ [down]) ! j = down)  }\<close>
    using less_Suc_eq by auto
  then have  \<open>DyckSetDCHR down (u @ [down]) = {j | j::nat. (j < length u \<and> (u @ [down]) ! j = down) } \<union> {j | j::nat. (j = length u \<and> (u @ [down]) ! j = down)}\<close>
    by (simp add: Un_def)
  then have  \<open>DyckSetDCHR down (u @ [down]) = {j | j::nat. (j < length u \<and> (u @ [down]) ! j = down) } \<union> {length u}\<close>
    using \<open>{j | j::nat. (j = length u \<and> (u @ [down]) ! j = down)} = {length u}\<close>
    by simp
  then have  \<open>card (DyckSetDCHR down (u @ [down])) = (card {j | j::nat. (j < length u \<and> (u @ [down]) ! j = down) }) + (card {length u})\<close>
    by simp
  then have  \<open>(card (DyckSetDCHR down (u @ [down]))::int) = ((card {j | j::nat. (j < length u \<and> (u @ [down]) ! j = down) })::int) + (1::int)\<close>
    by simp
  then have  \<open>(card (DyckSetDCHR down (u @ [down]))::int) = ((card {j | j::nat. (j < length u \<and> u ! j = down) })::int) + (1::int)\<close>
    by (metis (no_types, lifting) Collect_cong butlast_snoc nth_butlast)
  then have  \<open>(card (DyckSetDCHR down (u @ [down]))::int) = ((card (DyckSetDCHR down u))::int) + (1::int)\<close>
    using  \<open>DyckSetDCHR down u = {j | j::nat. j < length u  \<and> u ! j = down}\<close>
    by simp
  then show ?thesis by blast
qed


lemma DyckFirstLetterPrefix:
\<open>w \<noteq> [] \<Longrightarrow> prefix [w!0] w\<close>
  by (simp add: Suc_leI prefix_def)


lemma DyckFirstLetter:
 \<open> w \<noteq> [] \<Longrightarrow> DyckPath w \<Longrightarrow> w ! 0 = up\<close>
proof-
  assume \<open>DyckPath w\<close>
  assume \<open>w \<noteq> []\<close>
  have \<open>prefix [w ! 0] w\<close> 
    by (simp add: DyckFirstLetterPrefix \<open>w \<noteq> []\<close>)
  then have \<open>DyckPHeight [w ! 0] \<ge> 0\<close> using DyckPath_def AbstractPath_def
    by (metis \<open>DyckPath w\<close>)
  then have  \<open>w ! 0 = up\<close> using DyckPHeight_def 
    by (smt DCHR.exhaust DyckListDCHRLengthAbstrEqDyckPHeight0SetForm DyckSetDCHRDyckSetDCHRDyckSetDCHREq DyckSetDCHRDyckSetDCHRDyckSetDCHRNeq PHeightLetterwise.simps(1) of_nat_1 of_nat_add)
  then show ?thesis by blast
qed

lemma DyckUpPrefix:
\<open>DyckPath w \<Longrightarrow> w \<noteq> [] \<Longrightarrow> prefix [up] w\<close>
  using DyckFirstLetterPrefix DyckFirstLetter
  by fastforce

lemma prefixConcat:
\<open>w = u @ v \<Longrightarrow> prefix u w\<close> 
  using prefix_def 
  using DyckFirstLetterPrefix prefixL2 prefixZ1 by fastforce

lemma prefixTrans:
\<open>prefix u v \<Longrightarrow> prefix v w \<Longrightarrow> prefix u w\<close> 
  using prefix_def 
  using prefixLX prefixYY by blast


lemma MaxDyckHeightCharacterizationPropwithoutxylastRedLength:
  assumes \<open>DyckPath w\<close> and \<open>prefix v w\<close> and \<open>last v = down\<close> and \<open>v \<noteq> []\<close>
  shows \<open> \<exists> u. ((card (DyckSetDCHR up v))::int) - ((card (DyckSetDCHR down v))::int) \<le> ((card (DyckSetDCHR up u))::int) - ((card (DyckSetDCHR down u))::int) \<and> prefix u w \<and> length u = (length v)-1 \<and> u \<noteq> []\<close>
proof-
  from \<open>last v = down\<close> obtain u where \<open>v = u @ [down]\<close> 
    using  \<open>v \<noteq> []\<close> lastcharlist by blast
  have \<open>w ! 0 = up\<close> 
    using DyckUpPrefix assms(1) assms(2) assms(4) prefixYY by fastforce 
  then have \<open>u \<noteq> []\<close> 
    using \<open>v = u @ [down]\<close> assms(2) prefixYY by fastforce
  have \<open> ((card (DyckSetDCHR up v))::int) = ((card (DyckSetDCHR up u))::int) \<close>
    using  \<open>v = u @ [down]\<close> 
    using DyckSetDCHRup by blast
  have  \<open> ((card (DyckSetDCHR down (u @ [down])))::int) = ((card (DyckSetDCHR down u))::int) + (1::int)\<close>
    using  \<open>v = u @ [down]\<close> 
    using DyckSetDCHRdown by blast
  have \<open>((card (DyckSetDCHR up v))::int) - ((card (DyckSetDCHR down v))::int) \<le> ((card (DyckSetDCHR up u))::int) - ((card (DyckSetDCHR down u))::int)\<close>
    using \<open>int (card (DyckSetDCHR down (u @ [down]))) = int (card (DyckSetDCHR down u)) + 1\<close> \<open>int (card (DyckSetDCHR up v)) = int (card (DyckSetDCHR up u))\<close> \<open>v = u @ [down]\<close> by auto
  have \<open> length u = (length v)-1 \<close> using  \<open>v = u @ [down]\<close>
    by simp
  from \<open>v = u @ [down]\<close> have \<open>prefix u v\<close> 
    by (simp add: prefixConcat)
  from  \<open>prefix u v\<close>  \<open>prefix v w\<close> have \<open>prefix u w\<close>
    using prefixTrans by blast
    show ?thesis
    using \<open>int (card (DyckSetDCHR up v)) - int (card (DyckSetDCHR down v)) \<le> int (card (DyckSetDCHR up u)) - int (card (DyckSetDCHR down u))\<close> \<open>length u = length v - 1\<close> \<open>prefix u w\<close> \<open>u \<noteq> []\<close> by blast
  qed

lemma MaxDyckHeightCharacterizationPropwithoutxylastInd:
  fixes n :: nat and w :: \<open>DCHR list\<close>
  assumes  \<open>DyckPath w\<close>
  shows \<open>\<forall> v. \<exists> u. length v \<le> n \<and> prefix v w \<and> last v = down \<and> v \<noteq> [] \<longrightarrow> ( ((card (DyckSetDCHR up v))::int) - ((card (DyckSetDCHR down v))::int) \<le> ((card (DyckSetDCHR up u))::int) - ((card (DyckSetDCHR down u))::int) \<and> prefix u w \<and> last u = up \<and>  u \<noteq> [] )\<close>
proof(induction n)
case 0
  then show ?case 
    using lastcharlist by blast
next
  case (Suc n)
  then show ?case using MaxDyckHeightCharacterizationPropwithoutxylastRedLength
    by (smt DCHR.exhaust add_diff_cancel_left' assms le_SucE not_less_eq_eq plus_1_eq_Suc)
  qed

lemma MaxDyckHeightCharacterizationPropwithoutxylast:
  assumes  \<open>DyckPath w\<close> and \<open>prefix v w\<close> and \<open>last v = down\<close> and \<open>v \<noteq> []\<close>
  shows \<open> \<exists> u. ((card (DyckSetDCHR up v))::int) - ((card (DyckSetDCHR down v))::int) \<le> ((card (DyckSetDCHR up u))::int) - ((card (DyckSetDCHR down u))::int) \<and> prefix u w \<and> last u = up \<and> u \<noteq> []\<close>
  using assms MaxDyckHeightCharacterizationPropwithoutxylastInd
  by blast

lemma MaxDyckHeightCharacterizationPropwithoutxy:
  assumes  \<open>DyckPath w\<close> and \<open>prefix v w\<close> and \<open>v \<noteq> []\<close>
  shows \<open> \<exists> u. ((card (DyckSetDCHR up v))::int) - ((card (DyckSetDCHR down v))::int) \<le> ((card (DyckSetDCHR up u))::int) - ((card (DyckSetDCHR down u))::int) \<and> prefix u w \<and> last u = up \<and> u \<noteq> []\<close>
  using assms MaxDyckHeightCharacterizationPropwithoutxylast  DyckPHeightLetter.cases by blast

lemma MaxDyckHeightCharacterizationProp:
  assumes  \<open>DyckPath w\<close> and \<open>x = ((card (DyckSetDCHR up v))::int) - ((card (DyckSetDCHR down v))::int)\<close> and \<open>prefix v w\<close> and \<open>v \<noteq> []\<close>
  shows \<open>\<exists> y. \<exists> u. y = ((card (DyckSetDCHR up u))::int) - ((card (DyckSetDCHR down u))::int) \<and> prefix u w \<and> last u = up \<and> u \<noteq> [] \<and> x \<le> y\<close>
  using MaxDyckHeightCharacterizationPropwithoutxy assms by auto

lemma MaxDyckHeightCharacterization:
  assumes  \<open>DyckPath w\<close> and \<open>w \<noteq> []\<close> and \<open>x \<in> {((card (DyckSetDCHR up v))::int) - ((card (DyckSetDCHR down v))::int) | v. prefix v w \<and> v \<noteq> []}\<close> 
  shows \<open>\<exists> y. y \<in> {((card (DyckSetDCHR up v))::int) - ((card (DyckSetDCHR down v))::int) | v. prefix v w \<and> last v = up \<and> v \<noteq> []} \<and> x \<le> y\<close>
  using assms MaxDyckHeightCharacterizationProp 
  by fastforce


lemma FiniteNumberOfBoundedLengthRecUnionR:
  fixes n :: nat
  shows \<open> {[]} \<union> {up # v | v :: DCHR list. length v \<le> n} \<union> {down # v | v :: DCHR list. length v \<le> n} \<subseteq> {v | v :: DCHR list. length v \<le> Suc n}\<close>
  by auto

lemma preFiniteNumberOfBoundedLengthRecUnionL:
  fixes n :: nat and v :: \<open> DCHR list\<close>
  assumes \<open> length v \<le> Suc n \<close>
  shows \<open>v = [] \<or> (\<exists> u :: DCHR list. \<exists> c :: DCHR. length u \<le> n \<and> v = c # u)\<close>
proof(cases \<open>v = []\<close>)
  case True
  then show ?thesis 
    by simp
next
  case False
  then show ?thesis 
    using assms id_take_nth_drop by force
qed


lemma FiniteNumberOfBoundedLengthRecUnionL:
  fixes n :: nat
  shows \<open> {v | v :: DCHR list. length v \<le> Suc n} \<subseteq> {[]} \<union> {up # v | v :: DCHR list. length v \<le> n} \<union> {down # v | v :: DCHR list. length v \<le> n}\<close>
  using preFiniteNumberOfBoundedLengthRecUnionL 
  using DCHR.exhaust insertCI by blast


lemma FiniteNumberOfBoundedLengthRecUnion:
  fixes n :: nat
  shows \<open> {v | v :: DCHR list. length v \<le> Suc n} = {([]:: DCHR list)} \<union> {up # v | v :: DCHR list. length v \<le> n} \<union> {down # v | v :: DCHR list. length v \<le> n}\<close>
  using FiniteNumberOfBoundedLengthRecUnionL FiniteNumberOfBoundedLengthRecUnionR by auto

lemma preCFiniteNumberOfBoundedLengthRecinj:
\<open>inj (\<lambda> w ::'a list. c # w)\<close>
  by simp


lemma preCFiniteNumberOfBoundedLengthRecFun:
  fixes n :: nat
  shows \<open> (\<lambda> w :: DCHR list. c # w) ` {v | v :: DCHR list. length v \<le> n} = {c # v | v :: DCHR list. length v \<le> n} \<close>
  by blast


lemma bijpreCFiniteNumberOfBoundedLengthRecEq:
  fixes n :: nat
  shows \<open> bij_betw (\<lambda> w :: DCHR list. c # w) {v | v :: DCHR list. length v \<le> n} {c # v | v :: DCHR list. length v \<le> n} \<close>
  using preCFiniteNumberOfBoundedLengthRecinj preCFiniteNumberOfBoundedLengthRecFun
    bij_betw_def by fastforce

lemma preCFiniteNumberOfBoundedLengthRec:
  fixes n :: nat
  assumes \<open> finite {v | v :: DCHR list. length v \<le> n} \<close>
  shows \<open> finite {c # v | v :: DCHR list. length v \<le> n} \<close>
  using assms bijpreCFiniteNumberOfBoundedLengthRecEq by auto

lemma preUPFiniteNumberOfBoundedLengthRec:
  fixes n :: nat
  assumes \<open> finite {v | v :: DCHR list. length v \<le> n} \<close>
  shows \<open> finite {up # v | v :: DCHR list. length v \<le> n} \<close>
  using assms preCFiniteNumberOfBoundedLengthRec by auto

lemma preDOWNFiniteNumberOfBoundedLengthRec:
  fixes n :: nat
  assumes \<open> finite {v | v :: DCHR list. length v \<le> n} \<close>
  shows \<open> finite {down # v | v :: DCHR list. length v \<le> n} \<close>
  using assms preCFiniteNumberOfBoundedLengthRec by auto

lemma FiniteNumberOfBoundedLengthRec:
  fixes n :: nat
  assumes \<open> finite {v | v :: DCHR list. length v \<le> n} \<close>
  shows \<open> finite {v | v :: DCHR list. length v \<le> Suc n} \<close>
  using FiniteNumberOfBoundedLengthRecUnion preUPFiniteNumberOfBoundedLengthRec preDOWNFiniteNumberOfBoundedLengthRec
proof-
  have  \<open> {v | v :: DCHR list. length v \<le> Suc n} = {([]:: DCHR list)} \<union> {up # v | v :: DCHR list. length v \<le> n} \<union> {down # v | v :: DCHR list. length v \<le> n}\<close>
    using  \<open> finite {v | v :: DCHR list. length v \<le> n} \<close> FiniteNumberOfBoundedLengthRecUnion
    by auto
  have  \<open> finite {up # v | v :: DCHR list. length v \<le> n} \<close> 
    using  \<open> finite {v | v :: DCHR list. length v \<le> n} \<close> preUPFiniteNumberOfBoundedLengthRec
    by auto
  have  \<open> finite {down # v | v :: DCHR list. length v \<le> n} \<close> 
    using  \<open> finite {v | v :: DCHR list. length v \<le> n} \<close> preUPFiniteNumberOfBoundedLengthRec
    by auto
  have \<open>finite {([]:: DCHR list)}\<close> 
    by simp
  show ?thesis 
    using \<open>finite {down # v |v. length v \<le> n}\<close> \<open>finite {up # v |v. length v \<le> n}\<close> \<open>{v |v. length v \<le> Suc n} = {[]} \<union> {up # v |v. length v \<le> n} \<union> {down # v |v. length v \<le> n}\<close> by auto
qed

lemma FiniteNumberOfBoundedLength:
  fixes n :: nat
  shows \<open> finite {v | v :: DCHR list. length v \<le> n} \<close>
proof(induction n)
  case 0
  have \<open>{v | v :: DCHR list. length v \<le> 0} = {[]}\<close> 
    by simp
  then show ?case 
    by simp
next
  case (Suc n)
  then show ?case using  FiniteNumberOfBoundedLengthRec by blast
qed

lemma FiniteNumberOfPrefixes:
  fixes w :: \<open>DCHR list\<close>
  shows \<open> finite {v | v :: DCHR list. prefix v w} \<close>
proof-
  have \<open> finite {v | v :: DCHR list. length v \<le> length w} \<close> 
    using FiniteNumberOfBoundedLength by auto
  have \<open>\<forall> v w. prefix v w \<longrightarrow> length v \<le> length w\<close> using prefix_def 
    by (simp add: prefix_def)
  then have \<open>{v | v :: DCHR list. prefix v w} \<subseteq>  {v | v :: DCHR list. length v \<le> length w}\<close>
    by auto
then show ?thesis using \<open> finite {v | v :: DCHR list. length v \<le> length w} \<close> 
  by (simp add: finite_subset)
qed

lemma DyckSetDCHRcardempty:
 \<open>((card (DyckSetDCHR up []))::int) - ((card (DyckSetDCHR down []))::int) = 0\<close>
  by (simp add: DyckSetDCHR_def)

lemma preDyckHeightCharacterizationDyckNonZeroLthanOrEq1:
 \<open>DyckPath w \<Longrightarrow> w \<noteq> [] \<Longrightarrow> Max {((card (DyckSetDCHR up v))::int) - ((card (DyckSetDCHR down v))::int) | v. prefix v w} \<noteq> 0\<close>
proof-
  assume \<open>DyckPath w\<close>
  assume \<open>w \<noteq> []\<close>
 have \<open>{((card (DyckSetDCHR up v))::int) - ((card (DyckSetDCHR down v))::int) | v. prefix v w \<and> last v = up} \<subseteq> {((card (DyckSetDCHR up v))::int) - ((card (DyckSetDCHR down v))::int) | v. prefix v w}\<close>
    by blast
  have \<open>prefix [up] w\<close> using  \<open>DyckPath w\<close> \<open>w \<noteq> []\<close> DyckFirstLetter  
    by (simp add: prefix_def Suc_leI)
  have \<open>[up] \<noteq> []\<close> by blast
  have \<open>{((card (DyckSetDCHR up v))::int) - ((card (DyckSetDCHR down v))::int) | v. prefix v w \<and> last v = up } \<noteq> {}\<close>
    using \<open>prefix [up] w\<close> \<open>[up] \<noteq> []\<close> 
    by force
  have \<open>{((card (DyckSetDCHR up v))::int) - ((card (DyckSetDCHR down v))::int) | v. prefix v w } \<noteq> {}\<close> 
    using \<open>prefix [up] w\<close> by blast
  have \<open>finite {v | v. prefix v w}\<close>
    using FiniteNumberOfPrefixes by blast
  then have \<open>finite {v | v. prefix v w}\<close>
    by auto
  then have \<open>finite  ( (\<lambda> v. ((card (DyckSetDCHR up v))::int) - ((card (DyckSetDCHR down v))::int)) ` {v | v. prefix v w } )\<close>
    by blast    
  have \<open>( (\<lambda> v. ((card (DyckSetDCHR up v))::int) - ((card (DyckSetDCHR down v))::int)) ` {v | v. prefix v w } ) = {((card (DyckSetDCHR up v))::int) - ((card (DyckSetDCHR down v))::int) | v. prefix v w}\<close>
    by blast
  then have \<open>finite {((card (DyckSetDCHR up v))::int) - ((card (DyckSetDCHR down v))::int) | v. prefix v w}\<close>
    using \<open>finite ((\<lambda>v. int (card (DyckSetDCHR up v)) - int (card (DyckSetDCHR down v))) ` {v |v. prefix v w})\<close> by auto
  then have \<open>finite {((card (DyckSetDCHR up v))::int) - ((card (DyckSetDCHR down v))::int) | v. prefix v w \<and> last v = up}\<close>
    using \<open>{int (card (DyckSetDCHR up v)) - int (card (DyckSetDCHR down v)) |v. prefix v w \<and> last v = up} \<subseteq> {int (card (DyckSetDCHR up v)) - int (card (DyckSetDCHR down v)) | v. prefix v w}\<close> rev_finite_subset by blast
  have \<open>((card (DyckSetDCHR up [up]))::int) - ((card (DyckSetDCHR down [up]))::int)  \<in> {((card (DyckSetDCHR up v))::int) - ((card (DyckSetDCHR down v))::int) | v. prefix v w}\<close>
    using \<open>prefix [up] w\<close> by blast
  then have \<open>Max {((card (DyckSetDCHR up v))::int) - ((card (DyckSetDCHR down v))::int) | v. prefix v w} \<ge> ((card (DyckSetDCHR up [up]))::int) - ((card (DyckSetDCHR down [up]))::int) \<close>
    using Max_ge \<open>finite {int (card (DyckSetDCHR up v)) - int (card (DyckSetDCHR down v)) |v. prefix v w}\<close> by blast
  have \<open> ((card (DyckSetDCHR up [up]))::int) - ((card (DyckSetDCHR down [up]))::int) = (1::int)\<close>
    by (simp add: DyckSetDCHRDyckSetDCHRDyckSetDCHREq DyckSetDCHRDyckSetDCHRDyckSetDCHRNeq DyckSetDCHRcardempty)
  then show ?thesis 
    using \<open>int (card (DyckSetDCHR up [up])) - int (card (DyckSetDCHR down [up])) \<le> Max {int (card (DyckSetDCHR up v)) - int (card (DyckSetDCHR down v)) | v. prefix v w}\<close> by linarith
qed

lemma preDyckHeightCharacterizationDyckNonZero:
  fixes w :: \<open>DCHR list\<close>
  shows \<open>DyckPath w \<Longrightarrow> w \<noteq> [] \<Longrightarrow> DyckHeight w = Max {((card (DyckSetDCHR up v))::int) - ((card (DyckSetDCHR down v))::int) | v. prefix v w \<and> v \<noteq> []}\<close>
proof-
  assume \<open>DyckPath w\<close>
  assume \<open>w \<noteq> []\<close>
 have \<open>{((card (DyckSetDCHR up v))::int) - ((card (DyckSetDCHR down v))::int) | v. prefix v w \<and> last v = up} \<subseteq> {((card (DyckSetDCHR up v))::int) - ((card (DyckSetDCHR down v))::int) | v. prefix v w}\<close>
    by blast
  have \<open>prefix [up] w\<close> using  \<open>DyckPath w\<close> \<open>w \<noteq> []\<close> DyckFirstLetter  
    by (simp add: prefix_def Suc_leI)
  have \<open>[up] \<noteq> []\<close> by blast
  have \<open>{((card (DyckSetDCHR up v))::int) - ((card (DyckSetDCHR down v))::int) | v. prefix v w \<and> last v = up } \<noteq> {}\<close>
    using \<open>prefix [up] w\<close> \<open>[up] \<noteq> []\<close> 
    by force
  have \<open>{((card (DyckSetDCHR up v))::int) - ((card (DyckSetDCHR down v))::int) | v. prefix v w } \<noteq> {}\<close> 
    using \<open>prefix [up] w\<close> by blast
  have \<open>finite {v | v. prefix v w}\<close>
    using FiniteNumberOfPrefixes by blast
  then have \<open>finite {v | v. prefix v w}\<close>
    by auto
  then have \<open>finite  ( (\<lambda> v. ((card (DyckSetDCHR up v))::int) - ((card (DyckSetDCHR down v))::int)) ` {v | v. prefix v w } )\<close>
    by blast    
  have \<open>( (\<lambda> v. ((card (DyckSetDCHR up v))::int) - ((card (DyckSetDCHR down v))::int)) ` {v | v. prefix v w } ) = {((card (DyckSetDCHR up v))::int) - ((card (DyckSetDCHR down v))::int) | v. prefix v w}\<close>
    by blast
  then have \<open>finite {((card (DyckSetDCHR up v))::int) - ((card (DyckSetDCHR down v))::int) | v. prefix v w}\<close>
    using \<open>finite ((\<lambda>v. int (card (DyckSetDCHR up v)) - int (card (DyckSetDCHR down v))) ` {v |v. prefix v w})\<close> by auto
  then have \<open>finite {((card (DyckSetDCHR up v))::int) - ((card (DyckSetDCHR down v))::int) | v. prefix v w \<and> last v = up}\<close>
    using \<open>{int (card (DyckSetDCHR up v)) - int (card (DyckSetDCHR down v)) |v. prefix v w \<and> last v = up} \<subseteq> {int (card (DyckSetDCHR up v)) - int (card (DyckSetDCHR down v)) | v. prefix v w}\<close> rev_finite_subset by blast

  have \<open>DyckHeight w = Max {((card (DyckSetDCHR up v))::int) - ((card (DyckSetDCHR down v))::int) | v. prefix v w}\<close>
    using preDyckHeightCharacterization by auto
  then obtain v where \<open>DyckHeight w = ((card (DyckSetDCHR up v))::int) - ((card (DyckSetDCHR down v))::int)\<close> and \<open>prefix v w\<close>
    by (smt CollectD Max_in \<open>finite {int (card (DyckSetDCHR up v)) - int (card (DyckSetDCHR down v)) |v. prefix v w}\<close> \<open>{int (card (DyckSetDCHR up v)) - int (card (DyckSetDCHR down v)) |v. prefix v w} \<noteq> {}\<close>)
  have \<open>Max {((card (DyckSetDCHR up v))::int) - ((card (DyckSetDCHR down v))::int) | v. prefix v w} \<noteq> 0\<close> 
    using preDyckHeightCharacterizationDyckNonZeroLthanOrEq1  \<open>DyckPath w\<close>  \<open>w \<noteq> []\<close>
    by blast
  then have \<open>DyckHeight w \<noteq> 0\<close> using \<open>DyckHeight w = Max {((card (DyckSetDCHR up v))::int) - ((card (DyckSetDCHR down v))::int) | v. prefix v w}\<close>
    by simp
  then have \<open>v \<noteq> []\<close> using \<open>DyckHeight w = ((card (DyckSetDCHR up v))::int) - ((card (DyckSetDCHR down v))::int)\<close> DyckSetDCHRcardempty
    by auto
  then have \<open>v \<in> {v | v. prefix v w \<and> v \<noteq> []}\<close> 
    using \<open>prefix v w\<close> by blast
  have \<open>{((card (DyckSetDCHR up v))::int) - ((card (DyckSetDCHR down v))::int) | v. prefix v w \<and> v \<noteq> []} \<subseteq> {((card (DyckSetDCHR up v))::int) - ((card (DyckSetDCHR down v))::int) | v. prefix v w}\<close>
    by auto
  then have \<open>Max {((card (DyckSetDCHR up v))::int) - ((card (DyckSetDCHR down v))::int) | v. prefix v w \<and> v \<noteq> []} \<le> Max {((card (DyckSetDCHR up v))::int) - ((card (DyckSetDCHR down v))::int) | v. prefix v w}\<close>
    using Max.subset_imp \<open>finite {int (card (DyckSetDCHR up v)) - int (card (DyckSetDCHR down v)) |v. prefix v w}\<close> \<open>prefix v w\<close> \<open>v \<noteq> []\<close>
    by blast
  have \<open>DyckHeight w \<in> {((card (DyckSetDCHR up v))::int) - ((card (DyckSetDCHR down v))::int) | v. prefix v w \<and> v \<noteq> []}\<close>
    using \<open>DyckHeight w = int (card (DyckSetDCHR up v)) - int (card (DyckSetDCHR down v))\<close> \<open>prefix v w\<close> \<open>v \<noteq> []\<close> by blast
  then have \<open>DyckHeight w \<le> Max {((card (DyckSetDCHR up v))::int) - ((card (DyckSetDCHR down v))::int) | v. prefix v w \<and> v \<noteq> []}\<close>
    by (metis (mono_tags, lifting) Max_ge \<open>finite {int (card (DyckSetDCHR up v)) - int (card (DyckSetDCHR down v)) |v. prefix v w}\<close> \<open>{int (card (DyckSetDCHR up v)) - int (card (DyckSetDCHR down v)) |v. prefix v w \<and> v \<noteq> []} \<subseteq> {int (card (DyckSetDCHR up v)) - int (card (DyckSetDCHR down v)) | v. prefix v w}\<close> rev_finite_subset)
  then show ?thesis 
    using \<open>DyckHeight w = Max {int (card (DyckSetDCHR up v)) - int (card (DyckSetDCHR down v)) |v. prefix v w}\<close> \<open>Max {int (card (DyckSetDCHR up v)) - int (card (DyckSetDCHR down v)) |v. prefix v w \<and> v \<noteq> []} \<le> Max {int (card (DyckSetDCHR up v)) - int (card (DyckSetDCHR down v)) | v. prefix v w}\<close> by linarith
qed


section {* Main Result *}

theorem DyckHeightCharacterization:
 \<open> DyckPath w \<Longrightarrow> w \<noteq> [] \<Longrightarrow> DyckHeight w = Max {((card (DyckSetDCHR up v))::int) - ((card (DyckSetDCHR down v))::int) | v. prefix v w \<and> last v = up \<and> v \<noteq> []}\<close>
proof-
  assume \<open>w \<noteq> []\<close>
  assume \<open>DyckPath w\<close>
  have \<open>DyckHeight w = Max {((card (DyckSetDCHR up v))::int) - ((card (DyckSetDCHR down v))::int) | v. prefix v w \<and> v \<noteq> []}\<close>
    using  \<open>w \<noteq> []\<close>  \<open>DyckPath w\<close> preDyckHeightCharacterizationDyckNonZero by blast
  have \<open>{((card (DyckSetDCHR up v))::int) - ((card (DyckSetDCHR down v))::int) | v. prefix v w \<and> last v = up} \<subseteq> {((card (DyckSetDCHR up v))::int) - ((card (DyckSetDCHR down v))::int) | v. prefix v w}\<close>
    by blast
  have \<open>prefix [up] w\<close> using  \<open>DyckPath w\<close> \<open>w \<noteq> []\<close> DyckFirstLetter  
    by (simp add: prefix_def Suc_leI)
  have \<open>[up] \<noteq> []\<close> by blast
  have \<open>{((card (DyckSetDCHR up v))::int) - ((card (DyckSetDCHR down v))::int) | v. prefix v w \<and> last v = up \<and> v \<noteq> []} \<noteq> {}\<close>
    using \<open>prefix [up] w\<close> \<open>[up] \<noteq> []\<close> 
    by force
  have \<open>{((card (DyckSetDCHR up v))::int) - ((card (DyckSetDCHR down v))::int) | v. prefix v w \<and> v \<noteq> []} \<noteq> {}\<close> 
    using \<open>prefix [up] w\<close> by blast
  have \<open>finite {v | v. prefix v w}\<close>
    using FiniteNumberOfPrefixes by blast
  then have \<open>finite {v | v. prefix v w \<and> v \<noteq> []}\<close>
    by auto
  then have \<open>finite  ( (\<lambda> v. ((card (DyckSetDCHR up v))::int) - ((card (DyckSetDCHR down v))::int)) ` {v | v. prefix v w \<and> v \<noteq> []} )\<close>
    by blast    
  have \<open>( (\<lambda> v. ((card (DyckSetDCHR up v))::int) - ((card (DyckSetDCHR down v))::int)) ` {v | v. prefix v w \<and> v \<noteq> []} ) = {((card (DyckSetDCHR up v))::int) - ((card (DyckSetDCHR down v))::int) | v. prefix v w \<and> v \<noteq> []}\<close>
    by blast
  then have \<open>finite {((card (DyckSetDCHR up v))::int) - ((card (DyckSetDCHR down v))::int) | v. prefix v w \<and> v \<noteq> []}\<close>
    using \<open>finite ((\<lambda>v. int (card (DyckSetDCHR up v)) - int (card (DyckSetDCHR down v))) ` {v |v. prefix v w \<and> v \<noteq> []})\<close> by auto
  then have \<open>finite {((card (DyckSetDCHR up v))::int) - ((card (DyckSetDCHR down v))::int) | v. prefix v w \<and> last v = up \<and> v \<noteq> []}\<close>
  proof -
    have "{int (card (DyckSetDCHR up ds)) - int (card (DyckSetDCHR down ds)) |ds. prefix ds w \<and> last ds = up \<and> ds \<noteq> []} \<subseteq> {int (card (DyckSetDCHR up ds)) - int (card (DyckSetDCHR down ds)) | ds. prefix ds w \<and> ds \<noteq> []}"
      by blast
    then show ?thesis
      using \<open>finite {int (card (DyckSetDCHR up v)) - int (card (DyckSetDCHR down v)) |v. prefix v w \<and> v \<noteq> []}\<close> rev_finite_subset by blast
  qed
  
    have \<open>Max{((card (DyckSetDCHR up v))::int) - ((card (DyckSetDCHR down v))::int) | v. prefix v w \<and> last v = up \<and> v \<noteq> []} \<le> Max {((card (DyckSetDCHR up v))::int) - ((card (DyckSetDCHR down v))::int) | v. prefix v w \<and> v \<noteq> []}\<close>
proof -
  obtain dds :: "int \<Rightarrow> DCHR list" where
    f1: "\<forall>i. ((\<exists>ds. i = int (card (DyckSetDCHR up ds)) - int (card (DyckSetDCHR down ds)) \<and> prefix ds w \<and> last ds = up \<and> ds \<noteq> []) \<or> (\<forall>ds. [] = ds \<or> up \<noteq> last ds \<or> \<not> prefix ds w \<or> int (card (DyckSetDCHR up ds)) - int (card (DyckSetDCHR down ds)) \<noteq> i)) \<and> ([] \<noteq> dds i \<and> up = last (dds i) \<and> prefix (dds i) w \<and> int (card (DyckSetDCHR up (dds i))) - int (card (DyckSetDCHR down (dds i))) = i \<or> (\<forall>ds. i \<noteq> int (card (DyckSetDCHR up ds)) - int (card (DyckSetDCHR down ds)) \<or> \<not> prefix ds w \<or> last ds \<noteq> up \<or> ds = []))"
by moura
  { assume "\<forall>ds. sK9 (\<lambda>i. \<exists>ds. i = int (card (DyckSetDCHR up ds)) - int (card (DyckSetDCHR down ds)) \<and> prefix ds w \<and> ds \<noteq> []) (\<lambda>i. \<exists>ds. i = int (card (DyckSetDCHR up ds)) - int (card (DyckSetDCHR down ds)) \<and> prefix ds w \<and> last ds = up \<and> ds \<noteq> []) \<noteq> int (card (DyckSetDCHR up ds)) - int (card (DyckSetDCHR down ds)) \<or> \<not> prefix ds w \<or> ds = []"
    { assume "\<forall>ds. int (card (DyckSetDCHR up (dds (sK9 (\<lambda>i. \<exists>ds. i = int (card (DyckSetDCHR up ds)) - int (card (DyckSetDCHR down ds)) \<and> prefix ds w \<and> ds \<noteq> []) (\<lambda>i. \<exists>ds. i = int (card (DyckSetDCHR up ds)) - int (card (DyckSetDCHR down ds)) \<and> prefix ds w \<and> last ds = up \<and> ds \<noteq> []))))) - int (card (DyckSetDCHR down (dds (sK9 (\<lambda>i. \<exists>ds. i = int (card (DyckSetDCHR up ds)) - int (card (DyckSetDCHR down ds)) \<and> prefix ds w \<and> ds \<noteq> []) (\<lambda>i. \<exists>ds. i = int (card (DyckSetDCHR up ds)) - int (card (DyckSetDCHR down ds)) \<and> prefix ds w \<and> last ds = up \<and> ds \<noteq> []))))) \<noteq> int (card (DyckSetDCHR up ds)) - int (card (DyckSetDCHR down ds)) \<or> \<not> prefix ds w \<or> ds = []"
      then have "prefix (dds (sK9 (\<lambda>i. \<exists>ds. i = int (card (DyckSetDCHR up ds)) - int (card (DyckSetDCHR down ds)) \<and> prefix ds w \<and> ds \<noteq> []) (\<lambda>i. \<exists>ds. i = int (card (DyckSetDCHR up ds)) - int (card (DyckSetDCHR down ds)) \<and> prefix ds w \<and> last ds = up \<and> ds \<noteq> []))) w \<longrightarrow> [] = dds (sK9 (\<lambda>i. \<exists>ds. i = int (card (DyckSetDCHR up ds)) - int (card (DyckSetDCHR down ds)) \<and> prefix ds w \<and> ds \<noteq> []) (\<lambda>i. \<exists>ds. i = int (card (DyckSetDCHR up ds)) - int (card (DyckSetDCHR down ds)) \<and> prefix ds w \<and> last ds = up \<and> ds \<noteq> []))"
        by (metis (lifting))
      then have "\<forall>ds. sK9 (\<lambda>i. \<exists>ds. i = int (card (DyckSetDCHR up ds)) - int (card (DyckSetDCHR down ds)) \<and> prefix ds w \<and> ds \<noteq> []) (\<lambda>i. \<exists>ds. i = int (card (DyckSetDCHR up ds)) - int (card (DyckSetDCHR down ds)) \<and> prefix ds w \<and> last ds = up \<and> ds \<noteq> []) \<noteq> int (card (DyckSetDCHR up ds)) - int (card (DyckSetDCHR down ds)) \<or> \<not> prefix ds w \<or> last ds \<noteq> up \<or> ds = []"
        using f1 by blast }
    then have "{int (card (DyckSetDCHR up ds)) - int (card (DyckSetDCHR down ds)) |ds. prefix ds w \<and> last ds = up \<and> ds \<noteq> []} \<subseteq> {int (card (DyckSetDCHR up ds)) - int (card (DyckSetDCHR down ds)) | ds. prefix ds w \<and> ds \<noteq> []}"
      by blast }
  then have "{int (card (DyckSetDCHR up ds)) - int (card (DyckSetDCHR down ds)) |ds. prefix ds w \<and> last ds = up \<and> ds \<noteq> []} \<subseteq> {int (card (DyckSetDCHR up ds)) - int (card (DyckSetDCHR down ds)) | ds. prefix ds w \<and> ds \<noteq> []}"
by blast
then show ?thesis
  by (metis (lifting) Max_mono \<open>finite {int (card (DyckSetDCHR up v)) - int (card (DyckSetDCHR down v)) |v. prefix v w \<and> v \<noteq> []}\<close> \<open>{int (card (DyckSetDCHR up v)) - int (card (DyckSetDCHR down v)) |v. prefix v w \<and> last v = up \<and> v \<noteq> []} \<noteq> {}\<close>)
qed

  have \<open>DyckHeight w \<in> {((card (DyckSetDCHR up v))::int) - ((card (DyckSetDCHR down v))::int) | v. prefix v w \<and> v \<noteq> []}\<close>
    using Max_in \<open>DyckHeight w = Max {int (card (DyckSetDCHR up v)) - int (card (DyckSetDCHR down v)) |v. prefix v w \<and> v \<noteq> []}\<close> \<open>finite {int (card (DyckSetDCHR up v)) - int (card (DyckSetDCHR down v)) |v. prefix v w \<and> v \<noteq> []}\<close> \<open>{int (card (DyckSetDCHR up v)) - int (card (DyckSetDCHR down v)) |v. prefix v w \<and> v \<noteq> []} \<noteq> {}\<close> by auto
  then obtain y where \<open>y \<in> {((card (DyckSetDCHR up v))::int) - ((card (DyckSetDCHR down v))::int) | v. prefix v w \<and> last v = up \<and> v \<noteq> []}\<close>
    and \<open>DyckHeight w \<le> y\<close> using \<open>w \<noteq> []\<close> \<open>DyckPath w\<close> MaxDyckHeightCharacterization
     \<open>DyckHeight w = Max {((card (DyckSetDCHR up v))::int) - ((card (DyckSetDCHR down v))::int) | v. prefix v w \<and> v \<noteq> []}\<close>
    by blast    
    have \<open>Max{((card (DyckSetDCHR up v))::int) - ((card (DyckSetDCHR down v))::int) | v. prefix v w \<and> last v = up \<and> v \<noteq> []} \<ge> Max {((card (DyckSetDCHR up v))::int) - ((card (DyckSetDCHR down v))::int) | v. prefix v w \<and> v \<noteq> []}\<close>
      using Max_ge_iff \<open>DyckHeight w = Max {int (card (DyckSetDCHR up v)) - int (card (DyckSetDCHR down v)) |v. prefix v w \<and> v \<noteq> []}\<close> \<open>DyckHeight w \<le> y\<close> \<open>finite {int (card (DyckSetDCHR up v)) - int (card (DyckSetDCHR down v)) |v. prefix v w \<and> last v = up \<and> v \<noteq> []}\<close> \<open>y \<in> {int (card (DyckSetDCHR up v)) - int (card (DyckSetDCHR down v)) |v. prefix v w \<and> last v = up \<and> v \<noteq> []}\<close> by auto
  have \<open>Max{((card (DyckSetDCHR up v))::int) - ((card (DyckSetDCHR down v))::int) | v. prefix v w \<and> last v = up \<and> v \<noteq> []} = Max {((card (DyckSetDCHR up v))::int) - ((card (DyckSetDCHR down v))::int) | v. prefix v w \<and> v \<noteq> []}\<close>
    using \<open>Max {int (card (DyckSetDCHR up v)) - int (card (DyckSetDCHR down v)) |v. prefix v w \<and> last v = up \<and> v \<noteq> []} \<le> Max {int (card (DyckSetDCHR up v)) - int (card (DyckSetDCHR down v)) | v. prefix v w \<and> v \<noteq> []}\<close> \<open>Max {int (card (DyckSetDCHR up v)) - int (card (DyckSetDCHR down v)) |v. prefix v w \<and> v \<noteq> []} \<le> Max {int (card (DyckSetDCHR up v)) - int (card (DyckSetDCHR down v)) | v. prefix v w \<and> last v = up \<and> v \<noteq> []}\<close> by linarith
  then show ?thesis
    using \<open>DyckHeight w = Max {int (card (DyckSetDCHR up v)) - int (card (DyckSetDCHR down v)) |v. prefix v w \<and> v \<noteq> []}\<close> by linarith
qed


end


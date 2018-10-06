(*
Title: The frequency of a letter in a Dyck paths and the odd divisors 
Author: Jose Manuel Rodriguez Caballero

We prove the following result:

proposition cardDyckSetDCHRup:
  fixes n :: nat and v :: \<open>DCHR list\<close>
  assumes \<open>n \<ge> 1\<close> and \<open>v \<in> DyckTypeP n\<close>  
  shows \<open>card (DyckSetDCHR up v) = card {e | e::nat. e \<in> ODiv n \<and> e \<le> (DyckDiv n) v}\<close>

Reference:

@article{caballero2017symmetric,
  title={Symmetric Dyck Paths and Hooley’s ∆-function},
  author={Caballero, Jos{\'e} Manuel Rodr{\i}guez},
  journal={Combinatorics on Words. Springer International Publishing AG},
  year={2017}
}

@article{caballero2018function,
  title={On a function introduced by Erd{\"o}s and Nicolas},
  author={Caballero, Jos{\'e} Manuel Rodr{\'i}guez},
  journal={Journal of Number Theory},
  year={2018},
  publisher={Elsevier}
}


(This code  was verified in Isabelle2018)

*)


theory DyckDivPHeight 

imports Complex_Main DyckDiv

begin

lemma PrefixExistLength:
  \<open>\<forall> v. (k::nat) \<le> length v \<longrightarrow> (\<exists> u. prefix u v \<and> length u = k)\<close>
proof(induction k)
  case 0
  then show ?case 
    by (simp add: prefixConcat)
next
  case (Suc k)
  then show ?case
    by (metis Suc_le_lessD Suc_le_mono id_take_nth_drop length_take less_Suc_eq min.absorb2 prefixConcat prefix_def)
qed

lemma RecDyckTypeP:
  \<open> n \<ge> 1 \<Longrightarrow> v \<in> DyckTypeP n \<Longrightarrow> length v > 1 
\<Longrightarrow> \<exists> u t::DCHR list. u \<in> DyckTypeP n \<and> v = u @ t @ [up]
 \<and> (\<forall> j. j < length t \<longrightarrow> t!j = down)\<close>
proof-
  assume \<open>n \<ge> 1\<close>
  assume \<open>v \<in> DyckTypeP n\<close>
  assume \<open>length v > 1\<close>
  from \<open>v \<in> DyckTypeP n\<close> have \<open>last v = up\<close> 
    using CollectD DyckTypeP_def by fastforce
  then have \<open>v ! (length v - 1) = up\<close> 
    by (metis \<open>1 < length v\<close> last_conv_nth less_imp_le_nat list.size(3) not_one_le_zero)
  from \<open>v \<in> DyckTypeP n\<close> have \<open>prefix v (DyckType n)\<close> 
    using CollectD DyckTypeP_def by fastforce
  have \<open>(DyckType n)!0 = up\<close> 
    using DyckFirstLetter DyckType2 DyckType4 \<open>1 \<le> n\<close> by auto
  then have \<open>v!0 = up\<close> 
    by (metis \<open>1 < length v\<close> \<open>prefix v (DyckType n)\<close> less_numeral_extra(1) less_trans prefix_def)
  then have \<open>0 \<in> {j | j::nat. j < length v - 1 \<and> v!j = up}\<close> 
    using \<open>1 < length v\<close> by auto
  then have \<open>{j | j::nat. j < length v - 1 \<and> v!j = up} \<noteq> {}\<close> 
    by blast
  have \<open>finite {j | j::nat. j < length v - 1 \<and> v!j = up}\<close> 
    by simp
  have \<open>Max {j | j::nat. j < length v - 1 \<and> v!j = up} < length v\<close>
    using \<open>{j |j. j < length v - 1 \<and> v ! j = up} \<noteq> {}\<close> by force
  then obtain u where \<open>prefix u v\<close> and \<open>length u = 1 + Max {j | j::nat. j < length v - 1 \<and> v!j = up}\<close>
    by (smt PrefixExistLength Suc_leI le_antisym le_eq_less_or_eq nat_le_linear plus_1_eq_Suc)
  from \<open>prefix u v\<close> \<open>prefix v (DyckType n)\<close> 
  have \<open>prefix u (DyckType n)\<close> 
    using prefixTrans by blast
  have \<open>u \<noteq> []\<close> 
    using \<open>length u = 1 + Max {j |j. j < length v - 1 \<and> v ! j = up}\<close> by auto
  have \<open>\<forall> j. j \<in> {j |j. j < length v - 1 \<and> v ! j = up} \<longrightarrow> v ! j = up\<close>
    by blast
  have \<open>Max {j |j. j < length v - 1 \<and> v ! j = up} \<in>  {j |j. j < length v - 1 \<and> v ! j = up}\<close>
    using Max_in \<open>finite {j |j. j < length v - 1 \<and> v ! j = up}\<close> \<open>{j |j. j < length v - 1 \<and> v ! j = up} \<noteq> {}\<close> by blast
  from  \<open>\<forall> j. j \<in> {j |j. j < length v - 1 \<and> v ! j = up} \<longrightarrow> v ! j = up\<close>
    \<open>Max {j |j. j < length v - 1 \<and> v ! j = up} \<in>  {j |j. j < length v - 1 \<and> v ! j = up}\<close>
  have \<open>v ! (Max {j |j. j < length v - 1 \<and> v ! j = up}) = up\<close>
    by blast 
  then have \<open>last u = up\<close> 
    by (metis (no_types, lifting) \<open>length u = 1 + Max {j |j. j < length v - 1 \<and> v ! j = up}\<close> \<open>prefix u v\<close> \<open>u \<noteq> []\<close> add_diff_cancel_left' last_conv_nth lessI nth_append plus_1_eq_Suc prefixYY)
  have \<open>u \<in> DyckTypeP n\<close> 
    by (simp add: DyckTypeP_def \<open>last u = up\<close> \<open>prefix u (DyckType n)\<close> \<open>u \<noteq> []\<close>)
  obtain w where \<open>v = u @ w\<close> 
    using \<open>prefix u v\<close> prefixYY by blast
  have \<open>w \<noteq> []\<close> 
    using \<open>Max {j |j. j < length v - 1 \<and> v ! j = up} \<in> {j |j. j < length v - 1 \<and> v ! j = up}\<close> \<open>length u = 1 + Max {j |j. j < length v - 1 \<and> v ! j = up}\<close> \<open>v = u @ w\<close> by force
  have \<open>last v = last w\<close> 
    by (metis (no_types, lifting) CollectD \<open>Max {j |j. j < length v - 1 \<and> v ! j = up} \<in> {j |j. j < length v - 1 \<and> v ! j = up}\<close> \<open>length u = 1 + Max {j |j. j < length v - 1 \<and> v ! j = up}\<close> \<open>v = u @ w\<close> add_diff_cancel_left' last_appendR less_irrefl self_append_conv)
  obtain t where \<open>w = t @ [up]\<close> 
    by (metis \<open>last v = last w\<close> \<open>last v = up\<close> \<open>w \<noteq> []\<close> append_butlast_last_id)
  have \<open>v = u @ t @ [up]\<close> 
    by (simp add: \<open>v = u @ w\<close> \<open>w = t @ [up]\<close>)
  have \<open>\<forall> j. j < length v-1 \<and> j > Max {j |j. j < length v - 1 \<and> v ! j = up} \<longrightarrow> v ! j = down\<close>
  proof -
    { assume "\<exists>n. sK0 = n \<and> n < length v - 1 \<and> v ! n = up"
      then have "sK0 \<in> {n |n. n < length v - 1 \<and> v ! n = up}"
        by blast
      then have "down = v ! sK0 \<or> \<not> Max {n |n. n < length v - 1 \<and> v ! n = up} < sK0 \<or> \<not> sK0 < length v - 1"
        by (metis (lifting) Max_gr_iff \<open>finite {j |j. j < length v - 1 \<and> v ! j = up}\<close> \<open>{j |j. j < length v - 1 \<and> v ! j = up} \<noteq> {}\<close> less_not_refl2) }
    then have f1: "down = v ! sK0 \<or> \<not> Max {n |n. n < length v - 1 \<and> v ! n = up} < sK0 \<or> \<not> sK0 < length v - 1"
      by (metis DCHR.exhaust)
    have "(\<exists>X0. down \<noteq> v ! X0 \<and> Max {j |j. j < length v - 1 \<and> v ! j = up} < X0 \<and> X0 < length v - 1) \<longrightarrow> down \<noteq> v ! sK0 \<and> Max {j |j. j < length v - 1 \<and> v ! j = up} < sK0 \<and> sK0 < length v - 1"
      by (smt DCHR.exhaust Max_less_iff \<open>finite {j |j. j < length v - 1 \<and> v ! j = up}\<close> \<open>{j |j. j < length v - 1 \<and> v ! j = up} \<noteq> {}\<close> less_not_refl2 mem_Collect_eq)
    then show ?thesis
      using f1 by (metis (lifting))
  qed
  then have \<open>\<forall> j. j < length v-1 \<and> j \<ge> length u \<longrightarrow> (u @ t @ [up]) ! j = down\<close>
    by (metis (no_types, lifting) \<open>length u = 1 + Max {j |j. j < length v - 1 \<and> v ! j = up}\<close> \<open>v = u @ t @ [up]\<close> le_neq_implies_less lessI less_trans plus_1_eq_Suc)
  then have \<open>\<forall> j. j < length v-1-length u  \<longrightarrow> (u @ t @ [up]) ! (length u + j) = down\<close>
    by (simp add: add.commute)
  then have \<open>\<forall> j. j < length v-1-length u  \<longrightarrow> (t @ [up]) ! j = down\<close>
    by auto
  then have \<open>\<forall> j. j < length v-1-length u  \<longrightarrow> t ! j = down\<close>
    by (metis \<open>v = u @ t @ [up]\<close> add_diff_cancel_left' butlast_snoc diff_commute length_append length_append_singleton nth_butlast plus_1_eq_Suc)
  then have \<open>\<forall> j. j < length t  \<longrightarrow> t ! j = down\<close>
    by (simp add: \<open>v = u @ t @ [up]\<close>)
  show ?thesis 
    using \<open>\<forall>j<length t. t ! j = down\<close> \<open>u \<in> DyckTypeP n\<close> \<open>v = u @ t @ [up]\<close> by blast
qed

lemma DyckTypePlengthDichotomy:
  \<open> n \<ge> 1 \<Longrightarrow> v \<in> DyckTypeP n \<Longrightarrow> v \<noteq> [up] \<Longrightarrow> length v > 1\<close>
proof-
  assume \<open>n \<ge> 1\<close>
  assume \<open>v \<in> DyckTypeP n\<close>
  assume \<open>v \<noteq> [up]\<close>
  from \<open>v \<in> DyckTypeP n\<close> have \<open>prefix v (DyckType n)\<close> 
    using CollectD DyckTypeP_def by fastforce
  have \<open>prefix [up] (DyckType n)\<close> 
    using DyckType2 DyckType4 DyckUpPrefix \<open>1 \<le> n\<close> by blast
  from  \<open>prefix [up] (DyckType n)\<close> \<open>prefix v (DyckType n)\<close> \<open>v \<noteq> [up]\<close>
  show ?thesis
    by (smt CollectD DyckTypeP_def Groups.add_ac(2) One_nat_def \<open>v \<in> DyckTypeP n\<close> add_less_cancel_left append_eq_append_conv length_greater_0_conv less_Suc_eq list.size(3) list.size(4) plus_1_eq_Suc prefixYY)
qed

lemma DyckDivIncrA:
  \<open>n \<ge> 1 \<Longrightarrow> u \<in> DyckTypeP n \<Longrightarrow> v \<in> DyckTypeP n \<Longrightarrow> DyckDiv n u \<le> DyckDiv n v \<Longrightarrow> length u \<le> length v\<close>
proof(rule classical)
  assume \<open>n \<ge> 1\<close>
  assume \<open>u \<in> DyckTypeP n\<close>
  assume \<open>v \<in> DyckTypeP n\<close>
  assume \<open>DyckDiv n u \<le> DyckDiv n v\<close>
  assume \<open>\<not> (length u \<le> length v)\<close>
  then have \<open>length v < length u\<close> by auto
  then have  \<open>DyckDiv n v < DyckDiv n u\<close> 
    using DyckDiv2 \<open>1 \<le> n\<close> \<open>u \<in> DyckTypeP n\<close> \<open>v \<in> DyckTypeP n\<close> by blast
  show ?thesis using  \<open>DyckDiv n u \<le> DyckDiv n v\<close> \<open>DyckDiv n v < DyckDiv n u\<close> by auto
qed 

lemma DyckDivIncr:
  \<open>n \<ge> 1 \<Longrightarrow> u \<in> DyckTypeP n \<Longrightarrow> v \<in> DyckTypeP n \<Longrightarrow> DyckDiv n u < DyckDiv n v \<Longrightarrow> length u < length v\<close>
proof(rule classical)
  assume \<open>n \<ge> 1\<close>
  assume \<open>u \<in> DyckTypeP n\<close>
  assume \<open>v \<in> DyckTypeP n\<close>
  assume \<open>DyckDiv n u < DyckDiv n v\<close>
  assume \<open>\<not> (length u < length v)\<close>
  then have \<open>length v \<le> length u\<close>
    using not_le by blast
  from \<open>DyckDiv n u < DyckDiv n v\<close> have \<open>DyckDiv n u \<le> DyckDiv n v\<close> 
    by simp
  then have \<open>length u \<le> length v\<close> 
    using DyckDivIncrA \<open>1 \<le> n\<close> \<open>u \<in> DyckTypeP n\<close> \<open>v \<in> DyckTypeP n\<close> by blast
  then have \<open>length u = length v\<close> 
    using \<open>\<not> length u < length v\<close> order.not_eq_order_implies_strict by blast
  from  \<open>u \<in> DyckTypeP n\<close> 
  have \<open>prefix u (DyckType n)\<close> 
    using CollectD DyckTypeP_def by fastforce
  from  \<open>v \<in> DyckTypeP n\<close> 
  have \<open>prefix v (DyckType n)\<close> 
    using CollectD DyckTypeP_def by fastforce
  from \<open>prefix u (DyckType n)\<close> \<open>prefix v (DyckType n)\<close> \<open>length u = length v\<close> have \<open>u = v\<close> 
    by (metis append_eq_append_conv prefixYY)
  then have \<open>DyckDiv n u = DyckDiv n v\<close> by simp
  show ?thesis using \<open>DyckDiv n u = DyckDiv n v\<close> \<open>DyckDiv n u < DyckDiv n v\<close>
    by auto
qed

lemma addcardDyckSetDCHR:
  \<open>\<forall> v. card (DyckSetDCHR c (u @ v)) = card (DyckSetDCHR c u) + card (DyckSetDCHR c v)\<close>
proof(induction u)
  case Nil
  then show ?case 
    by (simp add: DyckSetDCHR_def)
next
  case (Cons a u)
  then show ?case 
    by (metis DyckSetDCHRDyckSetDCHRDyckSetDCHREq DyckSetDCHRDyckSetDCHRDyckSetDCHRNeq add.commute add.left_commute append_Cons)
qed

lemma DyckDivup:
  \<open>n \<ge> 1 \<Longrightarrow> (DyckDiv n) [up] = 1\<close>
proof(rule classical)
  assume \<open>\<not>((DyckDiv n) [up] = 1)\<close>
  assume \<open>n \<ge> 1\<close>
  then have \<open>DyckPath (DyckType n)\<close> 
    using DyckType2 by blast
  then have \<open>(DyckType n)!0 = up\<close> 
    using DyckFirstLetter DyckType4 \<open>1 \<le> n\<close> by blast
  then have \<open>[up] \<in> DyckTypeP n\<close> 
    by (smt CollectI DyckType4 DyckTypeP_def DyckUpPrefix \<open>1 \<le> n\<close> \<open>DyckPath (DyckType n)\<close> last.simps list.discI)
  then have \<open>\<forall> v::DCHR list. v \<in> DyckTypeP n \<and> length [up] < length v \<longrightarrow> (DyckDiv n) [up] < (DyckDiv n) v\<close>
    using  \<open>n \<ge> 1\<close> DyckDiv2 by blast
  then have \<open>\<forall> v::DCHR list. v \<in> DyckTypeP n \<and> 1 < length v \<longrightarrow> (DyckDiv n) [up] < (DyckDiv n) v\<close>
    by auto    
  from \<open>n \<ge> 1\<close> have \<open>1 \<in> ODiv n\<close> 
    by (simp add: ODiv_def)
  then obtain u where \<open>(DyckDiv n) u = 1\<close> and \<open>u \<in> DyckTypeP n\<close>
    by (metis DyckDiv1  \<open>1 \<le> n\<close> image_iff)
  from  \<open>\<not>((DyckDiv n) [up] = 1)\<close> have  \<open>(DyckDiv n) [up] > 1 \<or> (DyckDiv n) [up] = 0\<close>
    by linarith
  have \<open> (DyckDiv n) [up] \<in> ODiv n \<close> 
    using DyckDiv1 \<open>1 \<le> n\<close> \<open>[up] \<in> DyckTypeP n\<close> by blast
  have \<open>\<forall> d::nat. d \<in> ODiv n \<longrightarrow> d \<noteq> 0\<close> 
    by (metis CollectD ODiv_def One_nat_def even_Suc odd_one)
  then have \<open> (DyckDiv n) [up] \<noteq> 0 \<close> using  \<open> (DyckDiv n) [up] \<in> ODiv n \<close> by blast
  then have \<open>(DyckDiv n) [up] > 1\<close> using  \<open>(DyckDiv n) [up] > 1 \<or> (DyckDiv n) [up] = 0\<close>
    by auto
  then have \<open>\<forall> v::DCHR list. v \<in> DyckTypeP n \<and> 1 < length v \<longrightarrow> 1 < (DyckDiv n) v\<close>
    using  \<open>\<forall> v::DCHR list. v \<in> DyckTypeP n \<and> 1 < length v \<longrightarrow> (DyckDiv n) [up] < (DyckDiv n) v\<close>
    using order.strict_trans by blast
  then have \<open>length u = 1\<close> 
    by (metis DyckTypePlengthDichotomy \<open>1 \<le> n\<close> \<open>DyckDiv n [up] \<noteq> 1\<close> \<open>\<And>thesis. (\<And>u. \<lbrakk>DyckDiv n u = 1; u \<in> DyckTypeP n\<rbrakk> \<Longrightarrow> thesis) \<Longrightarrow> thesis\<close> less_numeral_extra(4))
  then have \<open>u = [up]\<close> using \<open>u \<in> DyckTypeP n\<close> 
    using DyckTypePlengthDichotomy \<open>1 \<le> n\<close> by fastforce
  then have \<open>DyckDiv n [up] = 1\<close> using \<open>DyckDiv n u = 1\<close> 
    by blast
  show ?thesis using  \<open>DyckDiv n [up] = 1\<close>  \<open>DyckDiv n [up] \<noteq> 1\<close> by blast
qed

lemma prefixofprefix:
  \<open>prefix v w \<Longrightarrow> prefix u w \<Longrightarrow> length u \<le> length v \<Longrightarrow> prefix u v\<close> 
  by (simp add: prefix_def)

lemma ODivDyckDivDyckTypePQS:
  \<open>n \<ge> 1 \<Longrightarrow> v \<in> DyckTypeP n \<Longrightarrow> u \<in> DyckTypeP n \<Longrightarrow> v = u @ t @ [up]
  \<Longrightarrow> \<forall> j. j < length t \<longrightarrow> t!j = down \<Longrightarrow> DyckDiv n u < e \<Longrightarrow> e < DyckDiv n v
  \<Longrightarrow> e \<notin> ODiv n\<close>
proof(rule classical)
  assume \<open>n \<ge> 1\<close>
  assume \<open>v \<in> DyckTypeP n\<close>
  assume \<open>u \<in> DyckTypeP n\<close>
  assume \<open>v = u @ t @ [up]\<close>
  assume \<open>\<forall> j. j < length t \<longrightarrow> t!j = down\<close>
  assume \<open>DyckDiv n u < e\<close>
  assume \<open>e < DyckDiv n v\<close>
  assume \<open>\<not> (e \<notin> ODiv n)\<close>
  then have  \<open>e \<in> ODiv n\<close> by blast
  then obtain w where \<open>DyckDiv n w = e\<close> and \<open>w \<in> DyckTypeP n\<close>
    by (metis (no_types, hide_lams) DyckDiv1  \<open>1 \<le> n\<close> imageE)
  have \<open>length w < length v\<close> 
    using DyckDivIncr \<open>1 \<le> n\<close> \<open>DyckDiv n w = e\<close> \<open>e < DyckDiv n v\<close> \<open>v \<in> DyckTypeP n\<close> \<open>w \<in> DyckTypeP n\<close> by blast
  have \<open>length u < length v\<close> 
    using DyckDivIncr \<open>1 \<le> n\<close> \<open>DyckDiv n u < e\<close> \<open>e < DyckDiv n v\<close> \<open>u \<in> DyckTypeP n\<close> \<open>v \<in> DyckTypeP n\<close> order.strict_trans by blast
  from  \<open>w \<in> DyckTypeP n\<close> have \<open>prefix w (DyckType n)\<close> 
    using CollectD DyckTypeP_def by fastforce
  from  \<open>v \<in> DyckTypeP n\<close> have \<open>prefix v (DyckType n)\<close> 
    using CollectD DyckTypeP_def by fastforce
  from  \<open>u \<in> DyckTypeP n\<close> have \<open>prefix u (DyckType n)\<close> 
    using CollectD DyckTypeP_def by fastforce
  have \<open>prefix w v\<close> 
    using prefixofprefix \<open>length w < length v\<close> \<open>prefix v (DyckType n)\<close> \<open>prefix w (DyckType n)\<close> less_imp_le_nat 
    by blast
  then have \<open>w ! (length w - 1) = v ! (length w - 1)\<close> 
    by (smt CollectD DyckTypeP_def \<open>w \<in> DyckTypeP n\<close> diff_less length_greater_0_conv less_numeral_extra(1) nth_append prefixYY)
  then have \<open>last w = v ! (length w - 1)\<close> 
    by (metis DyckTypePlengthDichotomy \<open>1 \<le> n\<close> \<open>w \<in> DyckTypeP n\<close> last_conv_nth list.discI list.size(3) not_less_zero)
  then have  \<open>up = v ! (length w - 1)\<close>
    using DyckTypePlengthDichotomy RecDyckTypeP \<open>1 \<le> n\<close> \<open>w \<in> DyckTypeP n\<close> by fastforce
  obtain k where \<open>length u + k = length w\<close> 
    using DyckDivIncr \<open>1 \<le> n\<close> \<open>DyckDiv n u < e\<close> \<open>DyckDiv n w = e\<close> \<open>u \<in> DyckTypeP n\<close> \<open>w \<in> DyckTypeP n\<close> less_imp_add_positive by blast
  have \<open>k \<ge> 1\<close> 
    using \<open>DyckDiv n u < e\<close> \<open>DyckDiv n w = e\<close> \<open>length u + k = length w\<close> \<open>prefix w v\<close> \<open>v = u @ t @ [up]\<close> neq_iff prefixYY by fastforce
  have \<open>v ! (length w - 1) = (u @ t @ [up]) ! (length w - 1)\<close> 
    using \<open>v = u @ t @ [up]\<close> by blast
  have \<open>v ! (length w - 1) = (u @ t @ [up]) ! (length u - 1 + k)\<close> 
    by (metis DyckTypePlengthDichotomy Nat.diff_add_assoc2 \<open>1 \<le> n\<close> \<open>length u + k = length w\<close> \<open>u \<in> DyckTypeP n\<close> \<open>v = u @ t @ [up]\<close> add.commute add_diff_cancel_left' add_eq_if less_imp_le_nat list.size(3) list.size(4) plus_1_eq_Suc)
  have \<open>(u @ (t @ [up])) ! (length u - 1 + k) = (t @ [up]) !  k\<close> 
  proof -
    have f1: "length v - length u = length (t @ [up])"
      by (simp add: \<open>v = u @ t @ [up]\<close>)
    have f2: "Suc (k - 1) = k"
      using \<open>1 \<le> k\<close> by fastforce
    have "k < length v - length u"
      using \<open>length u + k = length w\<close> \<open>length w < length v\<close> by force
    then have "k - 1 < length t"
      using f2 f1 by (simp add: add.commute)
    then show ?thesis
      by (metis (no_types) DCHR.distinct(1) Nat.add_diff_assoc2 \<open>1 \<le> k\<close> \<open>\<forall>j<length t. t ! j = down\<close> \<open>length u + k = length w\<close> \<open>up = v ! (length w - 1)\<close> \<open>v = u @ t @ [up]\<close> add.commute length_butlast nth_append nth_append_length_plus)
  qed
  have \<open>(t @ [up]) !  k = down\<close> 
    by (smt Nat.add_diff_assoc Nitpick.size_list_simp(2) \<open>(u @ t @ [up]) ! (length u - 1 + k) = (t @ [up]) ! k\<close> \<open>1 \<le> k\<close> \<open>\<forall>j<length t. t ! j = down\<close> \<open>length u + k = length w\<close> \<open>length w < length v\<close> \<open>v ! (length w - 1) = (u @ t @ [up]) ! (length u - 1 + k)\<close> \<open>v = u @ t @ [up]\<close> add_less_cancel_left append_is_Nil_conv butlast_snoc le_add_diff_inverse length_append length_butlast length_tl nth_append_length_plus nth_butlast plus_1_eq_Suc)
  then have  \<open>v ! (length w - 1) = down\<close> 
    using \<open>(u @ t @ [up]) ! (length u - 1 + k) = (t @ [up]) ! k\<close> \<open>v ! (length w - 1) = (u @ t @ [up]) ! (length u - 1 + k)\<close> by auto
  show ?thesis using  \<open>up = v ! (length w - 1)\<close> \<open>v ! (length w - 1) = down\<close> 
    by auto
qed

lemma ODivDyckDivDyckTypePQR:
  \<open>n \<ge> 1 \<Longrightarrow> v \<in> DyckTypeP n \<Longrightarrow>  u \<in> DyckTypeP n \<Longrightarrow> v = u @ t @ [up]
 \<Longrightarrow> \<forall> j. j < length t \<longrightarrow> t!j = down \<Longrightarrow>
  {e |e. e \<in> ODiv n \<and> DyckDiv n u < e \<and> e < DyckDiv n v} = {}\<close>
  using ODivDyckDivDyckTypePQS by blast

lemma ODivDyckDivDyckTypePQ:
  \<open>n \<ge> 1 \<Longrightarrow> v \<in> DyckTypeP n \<Longrightarrow>  u \<in> DyckTypeP n \<Longrightarrow> v = u @ t @ [up]
 \<Longrightarrow> \<forall> j. j < length t \<longrightarrow> t!j = down \<Longrightarrow>
  {e |e. e \<in> ODiv n \<and> DyckDiv n u < e \<and> e \<le> DyckDiv n v} = {DyckDiv n v}\<close>
proof-
  assume \<open>n \<ge> 1\<close>
  assume \<open>v \<in> DyckTypeP n\<close>
  assume \<open>u \<in> DyckTypeP n\<close>
  assume \<open>v = u @ t @ [up]\<close>
  assume \<open>\<forall> j. j < length t \<longrightarrow> t!j = down\<close>
  have \<open>{e |e. e \<in> ODiv n \<and> DyckDiv n u < e \<and> e \<le> DyckDiv n v} = {e |e. (e \<in> ODiv n \<and> DyckDiv n u < e \<and> e < DyckDiv n v)\<or>(e \<in> ODiv n \<and> DyckDiv n u < e \<and> e = DyckDiv n v)}\<close>
    by auto
  then  have \<open>{e |e. e \<in> ODiv n \<and> DyckDiv n u < e \<and> e \<le> DyckDiv n v} = {e |e. e \<in> ODiv n \<and> DyckDiv n u < e \<and> e < DyckDiv n v} \<union> {e |e. e \<in> ODiv n \<and> DyckDiv n u < e \<and> e = DyckDiv n v}\<close>
    by auto
  have \<open> DyckDiv n v \<in> ODiv n\<close> 
    using DyckDiv1 \<open>1 \<le> n\<close> \<open>v \<in> DyckTypeP n\<close> by blast
  have \<open>{e |e. e \<in> ODiv n \<and> DyckDiv n u < e \<and> e = DyckDiv n v} = {e |e. e \<in> ODiv n \<and> e = DyckDiv n v}\<close>
    using DyckDiv2 \<open>1 \<le> n\<close> \<open>u \<in> DyckTypeP n\<close> \<open>v = u @ t @ [up]\<close> \<open>v \<in> DyckTypeP n\<close> by auto
  have \<open>{e |e. e \<in> ODiv n \<and> e = DyckDiv n v} = { DyckDiv n v}\<close>
    using  \<open> DyckDiv n v \<in> ODiv n\<close> 
    by blast
  have \<open> {e |e. e \<in> ODiv n \<and> DyckDiv n u < e \<and> e < DyckDiv n v} = {}\<close>
    using ODivDyckDivDyckTypePQR  \<open>n \<ge> 1\<close> \<open>v \<in> DyckTypeP n\<close> \<open>u \<in> DyckTypeP n\<close> \<open>v = u @ t @ [up]\<close> \<open>\<forall> j. j < length t \<longrightarrow> t!j = down\<close>
    by blast
  show ?thesis 
    using \<open>{e |e. e \<in> ODiv n \<and> DyckDiv n u < e \<and> e < DyckDiv n v} = {}\<close> \<open>{e |e. e \<in> ODiv n \<and> DyckDiv n u < e \<and> e = DyckDiv n v} = {e |e. e \<in> ODiv n \<and> e = DyckDiv n v}\<close> \<open>{e |e. e \<in> ODiv n \<and> DyckDiv n u < e \<and> e \<le> DyckDiv n v} = {e |e. e \<in> ODiv n \<and> DyckDiv n u < e \<and> e < DyckDiv n v} \<union> {e |e. e \<in> ODiv n \<and> DyckDiv n u < e \<and> e = DyckDiv n v}\<close> \<open>{e |e. e \<in> ODiv n \<and> e = DyckDiv n v} = {DyckDiv n v}\<close> by auto
qed

lemma ODivDyckDivDyckTypeP:
  \<open>n \<ge> 1 \<Longrightarrow> v \<in> DyckTypeP n \<Longrightarrow>  u \<in> DyckTypeP n \<Longrightarrow> v = u @ t @ [up]
 \<Longrightarrow> \<forall> j. j < length t \<longrightarrow> t!j = down \<Longrightarrow>
  card {e |e. e \<in> ODiv n \<and> e \<le> DyckDiv n v} = card {e |e. e \<in> ODiv n \<and> e \<le> DyckDiv n u} + 1\<close>
proof-
  assume \<open>n \<ge> 1\<close>
  assume \<open>v \<in> DyckTypeP n\<close>
  assume \<open>u \<in> DyckTypeP n\<close>
  assume \<open>v = u @ t @ [up]\<close>
  assume \<open>\<forall> j. j < length t \<longrightarrow> t!j = down\<close>
  have \<open>\<forall> e. e \<le> DyckDiv n v \<longleftrightarrow> ( e \<le> DyckDiv n u)\<or>(DyckDiv n u < e \<and> e \<le> DyckDiv n v)\<close>
    by (smt DyckDiv2 \<open>1 \<le> n\<close> \<open>u \<in> DyckTypeP n\<close> \<open>v = u @ t @ [up]\<close> \<open>v \<in> DyckTypeP n\<close> add_diff_cancel_right' append_is_Nil_conv diff_less length_append length_greater_0_conv less_le_trans linorder_not_le list.discI not_less_iff_gr_or_eq)
  then have \<open>{e |e. e \<in> ODiv n \<and> e \<le> DyckDiv n v} = {e |e. (e \<in> ODiv n \<and> e \<le> DyckDiv n u)\<or>(e \<in> ODiv n \<and> DyckDiv n u < e \<and> e \<le> DyckDiv n v) }\<close>
    by blast  
  have \<open>finite {e |e. e \<in> ODiv n \<and> e \<le> DyckDiv n u}\<close> 
    using finite_nat_set_iff_bounded_le by blast
  have \<open>finite {e |e. e \<in> ODiv n \<and> DyckDiv n u < e \<and> e \<le> DyckDiv n v}\<close>
    using finite_nat_set_iff_bounded_le by blast
  have \<open>{e |e. (e \<in> ODiv n \<and> e \<le> DyckDiv n u)\<or>(e \<in> ODiv n \<and> DyckDiv n u < e \<and> e \<le> DyckDiv n v) } = {e |e. e \<in> ODiv n \<and> e \<le> DyckDiv n u} \<union> {e |e. e \<in> ODiv n \<and> DyckDiv n u < e \<and> e \<le> DyckDiv n v}\<close>
    by auto
  then have \<open>{e |e. e \<in> ODiv n \<and> e \<le> DyckDiv n v} = {e |e. e \<in> ODiv n \<and> e \<le> DyckDiv n u} \<union> {e |e. e \<in> ODiv n \<and> DyckDiv n u < e \<and> e \<le> DyckDiv n v}\<close>
    using \<open>{e |e. e \<in> ODiv n \<and> e \<le> DyckDiv n v} = {e |e. e \<in> ODiv n \<and> e \<le> DyckDiv n u \<or> e \<in> ODiv n \<and> DyckDiv n u < e \<and> e \<le> DyckDiv n v}\<close> by auto
  have \<open>{e |e. e \<in> ODiv n \<and> DyckDiv n u < e \<and> e \<le> DyckDiv n v} = {DyckDiv n v}\<close>
    using ODivDyckDivDyckTypePQ \<open>n \<ge> 1\<close> \<open>v \<in> DyckTypeP n\<close> \<open>u \<in> DyckTypeP n\<close> \<open>v = u @ t @ [up]\<close> \<open>\<forall> j. j < length t \<longrightarrow> t!j = down\<close>
    by blast
  then have  \<open>{e |e. e \<in> ODiv n \<and> e \<le> DyckDiv n v} = {e |e. e \<in> ODiv n \<and> e \<le> DyckDiv n u} \<union> {DyckDiv n v}\<close> 
    using \<open>{e |e. e \<in> ODiv n \<and> e \<le> DyckDiv n v} = {e |e. e \<in> ODiv n \<and> e \<le> DyckDiv n u} \<union> {e |e. e \<in> ODiv n \<and> DyckDiv n u < e \<and> e \<le> DyckDiv n v}\<close> by auto
  have \<open>length u < length v\<close> 
    by (simp add: \<open>v = u @ t @ [up]\<close>)
  then have \<open>DyckDiv n u < DyckDiv n v\<close> 
    using DyckDiv2 \<open>1 \<le> n\<close> \<open>u \<in> DyckTypeP n\<close> \<open>v \<in> DyckTypeP n\<close> by blast
  then have \<open>{e |e. e \<in> ODiv n \<and> e \<le> DyckDiv n u} \<inter> {DyckDiv n v} = {}\<close> 
    by auto
  show ?thesis 
    using \<open>{e |e. e \<in> ODiv n \<and> DyckDiv n u < e \<and> e \<le> DyckDiv n v} = {DyckDiv n v}\<close> \<open>{e |e. e \<in> ODiv n \<and> e \<le> DyckDiv n u \<or> e \<in> ODiv n \<and> DyckDiv n u < e \<and> e \<le> DyckDiv n v} = {e |e. e \<in> ODiv n \<and> e \<le> DyckDiv n u} \<union> {e |e. e \<in> ODiv n \<and> DyckDiv n u < e \<and> e \<le> DyckDiv n v}\<close> \<open>{e |e. e \<in> ODiv n \<and> e \<le> DyckDiv n u} \<inter> {DyckDiv n v} = {}\<close> \<open>{e |e. e \<in> ODiv n \<and> e \<le> DyckDiv n v} = {e |e. e \<in> ODiv n \<and> e \<le> DyckDiv n u \<or> e \<in> ODiv n \<and> DyckDiv n u < e \<and> e \<le> DyckDiv n v}\<close> by auto
qed

lemma cardDyckSetDCHRupIndRecS:
  fixes n k :: nat and v::\<open>DCHR list\<close>
  assumes \<open>n \<ge> 1\<close>
    and \<open> \<forall>v. card {e |e. e \<in> ODiv n \<and> e \<le> DyckDiv n v} \<le> k 
              \<and> v \<in> DyckTypeP n \<longrightarrow>
             card (DyckSetDCHR up v) =
             card {e |e. e \<in> ODiv n \<and> e \<le> DyckDiv n v} \<close>
    and \<open>card {e |e. e \<in> ODiv n \<and> e \<le> DyckDiv n v} \<le> Suc k\<close>
    and \<open> v \<in> DyckTypeP n \<close>
  shows \<open> card (DyckSetDCHR up v) = card {e |e. e \<in> ODiv n \<and> e \<le> DyckDiv n v} \<close>
proof(cases \<open>v = [up]\<close>)
  case True
  then have \<open>v = [up]\<close> by blast
  have \<open>DyckSetDCHR up v = {0}\<close> 
    by (smt Collect_empty_eq DyckListDCHRLengthAbstrCardSum DyckSetDCHRDyckSetDCHRDyckSetDCHREqSet DyckSetDCHRFIN DyckSetDCHRcardempty True Un_insert_left card_0_eq empty_iff list.size(3) of_nat_add of_nat_eq_iff semiring_1_class.of_nat_simps(1) sup_bot.left_neutral)
  have \<open>(DyckDiv n) v = 1\<close> 
    using DyckDivup assms(1)  \<open>v = [up]\<close>  by blast
  have \<open>\<forall> e::nat. e \<in> ODiv n \<and> e \<le> 1 \<longleftrightarrow> e = 1 \<close>
    by (metis (no_types, lifting) CollectD DyckDiv1 ODiv_def One_nat_def Suc_leI \<open>DyckDiv n v = 1\<close> assms(1) assms(4) even_Suc image_eqI le_neq_implies_less neq0_conv not_le)
  then have \<open>{e |e. e \<in> ODiv n \<and> e \<le> 1} = {1}\<close>
    by blast
  then show ?thesis using \<open>DyckSetDCHR up v = {0}\<close>  \<open>{e |e. e \<in> ODiv n \<and> e \<le> 1} = {1}\<close>
    using \<open>DyckDiv n v = 1\<close> by auto
next
  case False
  then have \<open>length v > 1\<close> 
    using DyckTypePlengthDichotomy assms(1) assms(4) by blast
  then obtain u t where \<open>u \<in> DyckTypeP n\<close> and \<open>v = u @ t @ [up]\<close>
    and \<open>\<forall> j. j < length t \<longrightarrow> t!j = down\<close> 
    using RecDyckTypeP assms(1) assms(4) by blast
  from \<open>\<forall> j. j < length t \<longrightarrow> t!j = down\<close>
  have \<open>card (DyckSetDCHR up t) = 0\<close> 
    by (simp add: DyckSetDCHR_def)
  have \<open>card (DyckSetDCHR up (u @ t @ [up])) = card (DyckSetDCHR up u)+card (DyckSetDCHR up t) + 1\<close>
    by (metis DyckListDCHRLengthAbstrCardSum DyckSetDCHRDyckSetDCHRDyckSetDCHREq One_nat_def add_is_0 addcardDyckSetDCHR append.assoc list.size(3) plus_1_eq_Suc)  
  then have  \<open>card (DyckSetDCHR up (u @ t @ [up])) = card (DyckSetDCHR up u) + 1\<close>
    using  \<open>\<forall> j. j < length t \<longrightarrow> t!j = down\<close> \<open>card (DyckSetDCHR up t) = 0\<close> by linarith
  have \<open>card {e |e. e \<in> ODiv n \<and> e \<le> DyckDiv n v} = card {e |e. e \<in> ODiv n \<and> e \<le> DyckDiv n u} + 1\<close>
    using ODivDyckDivDyckTypeP \<open>n \<ge> 1\<close> \<open>u \<in> DyckTypeP n\<close> \<open>v = u @ t @ [up]\<close>
      \<open>\<forall> j. j < length t \<longrightarrow> t!j = down\<close> \<open>v \<in> DyckTypeP n\<close>
    by blast
  have \<open>card {e |e. e \<in> ODiv n \<and> e \<le> DyckDiv n u} \<le> k\<close>
    using \<open>card {e |e. e \<in> ODiv n \<and> e \<le> DyckDiv n v} = card {e |e. e \<in> ODiv n \<and> e \<le> DyckDiv n u} + 1\<close> assms(3) by linarith
  from  \<open> \<forall>v. card {e |e. e \<in> ODiv n \<and> e \<le> DyckDiv n v} \<le> k 
              \<and> v \<in> DyckTypeP n \<longrightarrow>
             card (DyckSetDCHR up v) =
             card {e |e. e \<in> ODiv n \<and> e \<le> DyckDiv n v} \<close>
  have \<open>card (DyckSetDCHR up u) =
             card {e |e. e \<in> ODiv n \<and> e \<le> DyckDiv n u}\<close>
    using \<open>card {e |e. e \<in> ODiv n \<and> e \<le> DyckDiv n u} \<le> k\<close> \<open>u \<in> DyckTypeP n\<close> by blast
  then show ?thesis 
    using \<open>card (DyckSetDCHR up (u @ t @ [up])) = card (DyckSetDCHR up u) + 1\<close> \<open>card {e |e. e \<in> ODiv n \<and> e \<le> DyckDiv n v} = card {e |e. e \<in> ODiv n \<and> e \<le> DyckDiv n u} + 1\<close> \<open>v = u @ t @ [up]\<close> by auto
qed


lemma cardDyckSetDCHRupIndRec:
  fixes n k :: nat
  assumes \<open>n \<ge> 1\<close>
    and \<open> \<forall>v. card {e |e. e \<in> ODiv n \<and> e \<le> DyckDiv n v}
             \<le> k \<and>
             v \<in> DyckTypeP n \<longrightarrow>
             card (DyckSetDCHR up v) =
             card
              {e |e. e \<in> ODiv n \<and> e \<le> DyckDiv n v}\<close>
  shows \<open> \<forall>v. card {e |e. e \<in> ODiv n \<and> e \<le> DyckDiv n v}
             \<le> Suc k \<and>
             v \<in> DyckTypeP n \<longrightarrow>
             card (DyckSetDCHR up v) =
             card {e |e. e \<in> ODiv n \<and> e \<le> DyckDiv n v}\<close>
  using assms cardDyckSetDCHRupIndRecS by blast

lemma cardDyckSetDCHRupInd:
  fixes n k :: nat 
  assumes \<open>n \<ge> 1\<close>
  shows \<open>\<forall> v::DCHR list.
  card {e | e::nat. e \<in> ODiv n \<and> e \<le> (DyckDiv n) v} \<le> k
  \<and> v \<in> DyckTypeP n  \<longrightarrow> card (DyckSetDCHR up v) = card {e | e::nat. e \<in> ODiv n \<and> e \<le> (DyckDiv n) v}\<close>
proof(induction k)
  case 0
  have \<open>\<forall> v. v \<in> DyckTypeP n  \<longrightarrow> {e | e::nat. e \<in> ODiv n \<and> e \<le> (DyckDiv n) v} \<noteq> {}\<close>
    using \<open>n \<ge> 1\<close> DyckDiv1 by fastforce
  then have \<open>\<forall> v. v \<in> DyckTypeP n  \<longrightarrow> card {e | e::nat. e \<in> ODiv n \<and> e \<le> (DyckDiv n) v} \<noteq> 0\<close>
    by fastforce
  then show ?case 
    by blast
next
  case (Suc k)
  then show ?case using \<open>n\<ge>1\<close> cardDyckSetDCHRupIndRec
    by blast
qed

proposition cardDyckSetDCHRup:
  fixes n :: nat and v :: \<open>DCHR list\<close>
  assumes \<open>n \<ge> 1\<close> and \<open>v \<in> DyckTypeP n\<close>  
  shows \<open>card (DyckSetDCHR up v) = card {e | e::nat. e \<in> ODiv n \<and> e \<le> (DyckDiv n) v}\<close>
proof-
  have \<open>finite {e | e::nat. e \<in> ODiv n \<and> e \<le> (DyckDiv n) v}\<close> 
    using finite_nat_set_iff_bounded_le by blast
  then have \<open>card {e | e::nat. e \<in> ODiv n \<and> e \<le> (DyckDiv n) v} \<le> card {e | e::nat. e \<in> ODiv n \<and> e \<le> (DyckDiv n) v}\<close> 
    by blast
  then have \<open>card (DyckSetDCHR up v) = card {e | e::nat. e \<in> ODiv n \<and> e \<le> (DyckDiv n) v}\<close>
    using  \<open>v \<in> DyckTypeP n\<close>  \<open>n \<ge> 1\<close>  cardDyckSetDCHRupInd
    by blast
  then show ?thesis 
    by blast
qed

end


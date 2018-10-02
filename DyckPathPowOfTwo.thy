(*
Title: Dyck path and powers of 2
Author: Jose Manuel Rodriguez Caballero

(This code  was verified in Isabelle2018)
*)

theory DyckPathPowOfTwo

imports Complex_Main PowOfTwo fromNumberTheoryToLanguageTheory DyckTypeLengthDiv

begin



lemma DyckTypeDivLengthWA: 
  \<open>n \<ge> 1 \<Longrightarrow> length (DyckType n) = 2 \<Longrightarrow>  d dvd n \<Longrightarrow> odd d \<Longrightarrow> d = 1\<close>
proof(rule classical)
  assume \<open>n \<ge> 1\<close>
  assume \<open>length (DyckType n) = 2\<close>
  assume \<open>d dvd n\<close>
  assume \<open>odd d\<close>
  assume \<open>\<not> (d = 1)\<close>
  then have \<open>d \<noteq> 1\<close> by blast
  from  \<open>odd d\<close> have \<open>card {d | d :: nat. d dvd n \<and> odd d} = 1\<close>
    using DyckTypeDivLength \<open>1 \<le> n\<close> \<open>length (DyckType n) = 2\<close> by auto
  have \<open>1 \<in> {d | d :: nat. d dvd n \<and> odd d}\<close>
    by simp
  have \<open>d \<in> {d | d :: nat. d dvd n \<and> odd d}\<close> 
    by (simp add: \<open>d dvd n\<close> \<open>odd d\<close>)
  from  \<open>1 \<in> {d | d :: nat. d dvd n \<and> odd d}\<close> \<open>d \<in> {d | d :: nat. d dvd n \<and> odd d}\<close> \<open>d \<noteq> 1\<close>
  have \<open>card {1, d} \<ge> 2\<close>
    by simp
  from \<open>1 \<in> {d | d :: nat. d dvd n \<and> odd d}\<close> \<open>d \<in> {d | d :: nat. d dvd n \<and> odd d}\<close>
  have \<open>{1, d} \<subseteq> {d | d :: nat. d dvd n \<and> odd d}\<close> 
    by blast
  then have \<open>2 \<le> card {d | d :: nat. d dvd n \<and> odd d}\<close> using  \<open>card {1, d} \<ge> 2\<close>
    by (metis \<open>card {d |d::nat. d dvd n \<and> odd d} = 1\<close> card_1_singletonE insert_not_empty subset_singletonD)
  show ?thesis 
    using \<open>2 \<le> card {d |d::nat. d dvd n \<and> odd d}\<close> \<open>card {d |d::nat. d dvd n \<and> odd d} = 1\<close> by linarith
qed


lemma DyckTypeDivLengthWB: 
  \<open>n \<ge> 1 \<Longrightarrow> (\<forall> d. d dvd n \<and> odd d \<longrightarrow> d = 1) \<Longrightarrow> length (DyckType n) = 2\<close>
proof(rule classical)
  assume \<open>n \<ge> 1\<close>
  assume \<open>\<forall> d. d dvd n \<and> odd d \<longrightarrow> d = 1\<close>
  assume \<open>\<not> (length (DyckType n) = 2)\<close>
  then have \<open>card {d |d::nat. d dvd n \<and> odd d} \<noteq> 1\<close>
    using DyckTypeDivLength \<open>1 \<le> n\<close> by auto
  have \<open>1 \<in> {d |d::nat. d dvd n \<and> odd d}\<close>
    by simp
  have \<open>{1} \<subseteq> {d |d::nat. d dvd n \<and> odd d}\<close> by simp
  then have \<open>1 \<le> card {d |d::nat. d dvd n \<and> odd d}\<close> 
    by (smt Collect_conv_if Collect_mono_iff \<open>\<forall>d. d dvd n \<and> odd d \<longrightarrow> d = 1\<close> is_singletonI is_singleton_altdef le_numeral_extra(4) subset_antisym)
  then have \<open>2 \<le> card {d |d::nat. d dvd n \<and> odd d}\<close> using \<open>card {d |d::nat. d dvd n \<and> odd d} \<noteq> 1\<close>
    by linarith
  then obtain d :: nat where  \<open>d \<in> {d |d::nat. d dvd n \<and> odd d}\<close> and \<open>d \<noteq> 1\<close>
    by (metis (mono_tags, lifting) \<open>card {d |d. d dvd n \<and> odd d} \<noteq> 1\<close> \<open>{1} \<subseteq> {d |d. d dvd n \<and> odd d}\<close> equalityI insertCI is_singletonI is_singleton_altdef subsetI)
  have  \<open>d dvd n \<and> odd d\<close> using  \<open>d \<in> {d |d::nat. d dvd n \<and> odd d}\<close>
    by blast
  from  \<open>d dvd n \<and> odd d\<close> \<open>d \<noteq> 1\<close> \<open>\<forall> d. d dvd n \<and> odd d \<longrightarrow> d = 1\<close>
  show ?thesis 
    by blast
qed

lemma DyckTypeDivLengthW: 
  \<open>length (DyckType n) = 2 \<longleftrightarrow> (\<forall> d. d dvd n \<and> odd d \<longrightarrow> d = 1)\<close>
  using DyckTypeDivLengthWA DyckTypeDivLengthWB 
  by (metis (no_types, lifting) DyckType0 Nitpick.size_list_simp(2) One_nat_def  add.commute add_left_imp_eq dvd_0_right dvd_add_triv_right_iff less_one linorder_not_le  odd_one odd_two_times_div_two_succ plus_1_eq_Suc zero_neq_numeral)


lemma DyckTypeLength2A:
  \<open>DyckPath w \<Longrightarrow> length w = 2 \<Longrightarrow> w = [up, down]\<close>
proof-
  assume \<open>DyckPath w\<close>
  assume \<open>length w = 2\<close>
  then have \<open>w = [w!0, w!1]\<close> 
    by (metis Cons_nth_drop_Suc One_nat_def Suc_1 add_diff_cancel_left' append.simps(1) id_take_nth_drop length_0_conv length_tl lessI list.sel(3) plus_1_eq_Suc pos2 take0)
  have \<open>prefix [w ! 0] w\<close> 
    by (simp add: \<open>length w = 2\<close> prefix_def) 
  then have  \<open>DyckPHeight [w ! 0] \<ge> 0\<close> using \<open>DyckPath w\<close>
    by (simp add: AbstractPath_def DyckPath_def)
  then have \<open>w ! 0 = up\<close> 
    by (smt DCHR.exhaust DyckPHeightLetter.simps(2) DyckPHeight_def PHeightLetterwise.simps(1) PHeightLetterwise.simps(2))
  have \<open>DyckPHeight w = 0\<close> using \<open>DyckPath w\<close>
    by (simp add: AbstractPath_def DyckPath_def)
  then have \<open>w ! 1 = down\<close> using \<open>w ! 0 = up\<close> \<open>w = [w!0, w!1]\<close> 
    by (smt DCHR.exhaust DyckPHeightLetter.simps(1) DyckPHeight_def PHeightLetterwise.simps(2) \<open>0 \<le> DyckPHeight [w ! 0]\<close>)
  show ?thesis 
    using \<open>w ! 0 = up\<close> \<open>w ! 1 = down\<close> \<open>w = [w ! 0, w ! 1]\<close> by auto
qed

lemma DyckTypeLength2B:
  \<open>DyckPath w  \<Longrightarrow> w = [up, down] \<Longrightarrow> length w = 2\<close>
  by simp

lemma DyckTypeLength2:
  \<open>DyckPath w \<Longrightarrow> (length w = 2 \<longleftrightarrow> w = [up, down])\<close>
  using DyckTypeLength2A DyckTypeLength2B by blast

lemma preArithmFunPow2: 
  \<open>n \<ge> 1 \<Longrightarrow> (length (DyckType n) = 2 \<longleftrightarrow> (\<exists> k. n = 2^k))\<close>
  by (meson DyckTypeDivLengthW OddDivPow2)


lemma preArithmFunPow2C: 
  \<open>n \<ge> 1 \<Longrightarrow> ( DyckType n = [up, down] \<longleftrightarrow> (\<exists> k. n = 2^k))\<close>
  using DyckTypeLength2 preArithmFunPow2 
  by (simp add: DyckType2)


proposition ArithmFunPow2 : 
  \<open>ArithmFun (\<lambda> w. w = [up, down]) \<doteq> (\<lambda> n. (\<exists> k. n = 2^k ))\<close>
  using preArithmFunPow2  preArithmFunPow2C
  by (simp add: DyckTypeToArithmFunB)


end

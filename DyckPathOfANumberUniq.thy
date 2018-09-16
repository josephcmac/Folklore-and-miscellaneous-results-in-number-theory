(*
Title: Uniqueness of the Dyck path which represent a DyckClass
Author: Jose Manuel Rodriguez Caballero

Our main result will be the following theorem.

theorem DyckUniq :
  fixes  v w :: \<open>DCHR list\<close>
  assumes \<open>(DyckClass v) \<inter> (DyckClass w) \<noteq> {}\<close>
  shows \<open>v = w\<close>
  sorry


Reference 1:
@article{caballero2017symmetric,
  title={Symmetric Dyck Paths and Hooley’s Delta-function},
  author={Caballero, Jos{\'e} Manuel Rodr{\i}guez},
  journal={Combinatorics on Words. Springer International Publishing AG},
  year={2017}
}

Reference 2:
Höft, H.F.W.: On the symmetric spectrum of odd divisors of a number.
Link: https://oeis.org/A241561/a241561.pdf


(This code  was verified in Isabelle2018)
*)

theory DyckPathOfANumberUniq 

imports Complex_Main DyckPathOfANumberDefs DyckPathOfANumberExistence

begin

section {* Auxiliary Results *}

lemma WordToFunlength :
  fixes  v w :: \<open>SCHR list\<close> and j :: nat
  assumes \<open>WordToFun v = WordToFun w\<close> and \<open>length v \<le> length w\<close>
and \<open>j < length v\<close>
  shows \<open>v ! j = w ! j\<close>
proof-
  from  \<open>WordToFun v = WordToFun w\<close>
  have  \<open>(WordToFun v) j = (WordToFun w) j\<close> 
    by simp
  then show ?thesis 
    by (smt SCHR.exhaust SchroederCode_def WordToFun_def assms(2) assms(3) less_le_trans)
qed

lemma preWordToFunSchroederToDyck :
  fixes  v w :: \<open>SCHR list\<close>
  assumes \<open>WordToFun v = WordToFun w\<close> and \<open>length v \<le> length w\<close>
  shows \<open>\<exists> x. v @ x = w \<and> (\<forall> j. j < length x \<longrightarrow> x ! j = STRANGE)\<close>
proof(rule classical)
  assume  \<open>\<not>(\<exists> x. v @ x = w \<and> (\<forall> j. j < length x \<longrightarrow> x ! j = STRANGE))\<close>
  then have  \<open>\<forall> x. v @ x = w \<longrightarrow> (\<exists> j. j < length x \<and> x ! j \<noteq> STRANGE)\<close>
    by auto
  from  \<open>length v \<le> length w\<close> have \<open>\<forall> j. j < length v \<longrightarrow> v ! j = w ! j\<close>
    using WordToFunlength assms(1) by blast
  then have \<open>prefix v w\<close> using  \<open>length v \<le> length w\<close> 
    by (simp add: prefix_def)
  then obtain x where \<open>v @ x = w\<close> 
    using prefixYY by blast
  from  \<open>v @ x = w\<close> obtain j 
    where \<open> j < length x\<close> and \<open> x ! j \<noteq> STRANGE\<close> 
    using   \<open>\<forall> x. v @ x = w \<longrightarrow> (\<exists> j. j < length x \<and> x ! j \<noteq> STRANGE)\<close>
    by blast
  from  \<open> x ! j \<noteq> STRANGE\<close>
  have   \<open> (v @ x) ! ((length v)+j) \<noteq> STRANGE\<close>
    by auto
  then have  \<open> w ! ((length v)+j) \<noteq> STRANGE\<close> 
    using \<open>v @ x = w\<close> by blast
  then have \<open>(WordToFun w) ((length v)+j) \<noteq> 0\<close> 
    by (smt SCHR.exhaust SchroederCode_def WordToFun_def \<open>j < length x\<close> \<open>v @ x = w\<close> add_less_cancel_left length_append)
  have \<open>(WordToFun v) ((length v)+j) = 0\<close> 
    by (simp add: WordToFun_def)
  show ?thesis 
    using \<open>WordToFun v (length v + j) = 0\<close> \<open>WordToFun w (length v + j) \<noteq> 0\<close> assms(1) by auto
qed

lemma SchroederToDyckStrange :
  fixes  w :: \<open>SCHR list\<close>
  shows \<open>(\<forall> j. j < length w \<longrightarrow> w ! j = STRANGE)\<longrightarrow>(SchroederToDyck w = [])\<close>
  proof(induction w)
    case Nil
    then show ?case 
      by simp
  next
    case (Cons a w)
    then show ?case 
      by (metis One_nat_def SCHR.distinct(3) SCHR.distinct(5) SchroederToDyck.simps(2) SchroederToDyckCode_def Suc_less_eq append_is_Nil_conv diff_Suc_Suc diff_zero length_Cons nth_Cons_0 nth_Cons_pos zero_less_Suc)
  qed

lemma WordToFunSchroederToDyckOrder :
  fixes  v w :: \<open>SCHR list\<close>
  assumes \<open>WordToFun v = WordToFun w\<close> and \<open>length v \<le> length w\<close>
  shows \<open>SchroederToDyck v = SchroederToDyck w\<close>
  by (metis SchroederToDyckConcat SchroederToDyckStrange append_Nil2 assms(1) assms(2) preWordToFunSchroederToDyck)

lemma WordToFunSchroederToDyck :
  fixes  v w :: \<open>SCHR list\<close>
  assumes \<open>WordToFun v = WordToFun w\<close>
  shows \<open>SchroederToDyck v = SchroederToDyck w\<close>
  using assms WordToFunSchroederToDyckOrder 
  by (metis le_cases)

section {* Main Result *}

theorem DyckUniq :
  fixes  v w :: \<open>DCHR list\<close>
  assumes \<open>(DyckClass v) \<inter> (DyckClass w) \<noteq> {}\<close>
  shows \<open>v = w\<close>
proof-
  from \<open>(DyckClass v) \<inter> (DyckClass w) \<noteq> {}\<close> obtain n where \<open>n \<in> (DyckClass v) \<inter> (DyckClass w)\<close>
    by blast
  from  \<open>n \<in> (DyckClass v) \<inter> (DyckClass w)\<close> have  \<open>n \<in> (DyckClass v)\<close> by blast
  then obtain vv where \<open>WordToFun vv = Jsigns n\<close> and \<open>SchroederToDyck vv = v\<close> 
    by (smt Collect_mono_iff DyckClass_def Int_lower1 \<open>n \<in> DyckClass v \<inter> DyckClass w\<close> inf_Int_eq inf_set_def)
  from  \<open>n \<in> (DyckClass v) \<inter> (DyckClass w)\<close> have  \<open>n \<in> (DyckClass w)\<close> by blast
  then obtain ww where \<open>WordToFun ww = Jsigns n\<close> and \<open>SchroederToDyck ww = w\<close>
    by (smt Collect_mono_iff DyckClass_def Int_lower2 \<open>n \<in> DyckClass v \<inter> DyckClass w\<close> inf_Int_eq inf_set_def)
  have \<open>WordToFun vv = WordToFun ww\<close> 
    by (simp add: \<open>WordToFun vv = Jsigns n\<close> \<open>WordToFun ww = Jsigns n\<close>)
  then have \<open>SchroederToDyck vv = SchroederToDyck ww\<close> 
    using WordToFunSchroederToDyck by blast
  then show ?thesis 
    using \<open>SchroederToDyck vv = v\<close> \<open>SchroederToDyck ww = w\<close> by blast
qed

end


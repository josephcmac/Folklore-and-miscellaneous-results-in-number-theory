(*
Title: Parity of the numerator and the denominator of harmonic numbers 
Author: Jose Manuel Rodriguez Caballero

The n-th harmonic number is the result of the finite sum

H(n) = 1 + 1/2 + 1/3 + 1/4 + ... + 1/n.

Suppose that n \<ge> 2.  we will prove that H(n) is not an integer (this result is due to Taeisinger).

We use some results from the file TrapezoidalNumbers.thy in the same repertory.


(This code  was verified in Isabelle2018-RC4/HOL)

*)

theory HarmonicAreNotIntegers

imports Complex_Main TrapezoidalNumbers

begin

section {* Generalization *}

definition depth :: \<open>rat \<Rightarrow> nat \<Rightarrow> bool\<close> where
\<open>depth \<equiv> \<lambda> t::rat. \<lambda> k::nat. (\<exists> r s::int. odd r \<and> odd s \<and> Fract r (2^k*s) = t)\<close>

lemma FundLemTwoDeno1:
  fixes r rr s ss :: int and k kk :: nat
  assumes \<open>k < kk\<close> and \<open>odd r\<close> and \<open>odd s\<close> and \<open>odd rr\<close> and \<open>odd ss\<close>
  shows \<open>\<exists> j::nat.   Fract r (2^k*s) + Fract rr (2^kk*ss) = Fract (r*2^(j+1)*ss + rr*s) (2^kk*(s*ss))\<close>
proof-
  from \<open>k < kk\<close> obtain j::nat where \<open>k + j + 1 = kk\<close> 
    by (metis Suc_eq_plus1 less_imp_Suc_add)
  have \<open> Fract r (2^k*s) + Fract rr (2^kk*ss) = Fract (r*(2^kk*ss) + rr*(2^k*s)) ((2^k*s)*(2^kk*ss))\<close>
    by (smt add_rat assms(3) assms(5) dvd_0_right mult_eq_0_iff power_eq_0_iff)
  then have \<open> Fract r (2^k*s) + Fract rr (2^kk*ss) = Fract (r*(2^(k+j+1)*ss) + rr*(2^k*s)) ((2^k*s)*(2^kk*ss))\<close>
    using \<open>k + j + 1 = kk\<close> by blast
  then have \<open> Fract r (2^k*s) + Fract rr (2^kk*ss) = Fract (r*(2^k*2^(j+1)*ss) + rr*(2^k*s)) ((2^k*s)*(2^kk*ss))\<close>
    by (metis Suc_eq_plus1 add_Suc_right power_add)
  then have \<open> Fract r (2^k*s) + Fract rr (2^kk*ss) = Fract (2^k*(r*2^(j+1)*ss) + 2^k*(rr*s)) ((2^k*s)*(2^kk*ss))\<close>
    by (simp add: mult.assoc semiring_normalization_rules(19))
  then have \<open> Fract r (2^k*s) + Fract rr (2^kk*ss) = Fract (2^k*(r*2^(j+1)*ss + rr*s)) ((2^k*s)*(2^kk*ss))\<close>
    by (metis (mono_tags, hide_lams)  Suc_eq_plus1  linordered_field_class.sign_simps(2)  linordered_field_class.sign_simps(5) linordered_field_class.sign_simps(6)   ring_class.ring_distribs(1) semiring_normalization_rules(26))
  then have \<open> Fract r (2^k*s) + Fract rr (2^kk*ss) = Fract (2^k*(r*2^(j+1)*ss + rr*s)) (2^k*(s*2^kk*ss))\<close>    
    by (simp add: mult.assoc)
  then have \<open> Fract r (2^k*s) + Fract rr (2^kk*ss) = Fract (r*2^(j+1)*ss + rr*s) (s*2^kk*ss)\<close>    
    by (simp add: mult_rat_cancel)
  then show ?thesis   
    by (smt mult.commute semiring_normalization_rules(16))
qed

lemma FundLemTwoDeno:
  fixes r rr s ss :: int and k kk :: nat
  assumes \<open>k < kk\<close> and \<open>odd r\<close> and \<open>odd s\<close> and \<open>odd rr\<close> and \<open>odd ss\<close>
  shows \<open>\<exists> rrr sss::int. odd rrr \<and> odd sss \<and> Fract r (2^k*s) + Fract rr (2^kk*ss) = Fract rrr (2^kk*sss)\<close>
proof-
  obtain j :: nat where \<open> Fract r (2^k*s) + Fract rr (2^kk*ss) =  Fract (r*2^(j+1)*ss + rr*s) (2^kk*(s*ss))\<close>
    using FundLemTwoDeno1 assms(1) assms(2) assms(3) assms(4) assms(5) by blast
  have \<open>odd (s*ss)\<close> 
    by (simp add: assms(3) assms(5))
  have \<open>odd (rr*s)\<close> 
    by (simp add: assms(3) assms(4))
  have \<open>odd (r*2^(j+1)*ss + rr*s)\<close> 
    using \<open>odd (rr * s)\<close> by auto

  obtain rrr sss :: int where \<open>rrr = r*2^(j+1)*ss + rr*s\<close> and \<open>sss = s*ss\<close>
    by blast
  from \<open>rrr = r*2^(j+1)*ss + rr*s\<close> \<open>sss = s*ss\<close> \<open> Fract r (2^k*s) + Fract rr (2^kk*ss) =  Fract (r*2^(j+1)*ss + rr*s) (2^kk*(s*ss))\<close>
    have \<open>Fract r (2^k*s) + Fract rr (2^kk*ss) = Fract rrr (2^kk*sss)\<close> 
      by blast
  from  \<open>odd (r*2^(j+1)*ss + rr*s)\<close>  \<open>rrr = r*2^(j+1)*ss + rr*s\<close> have \<open>odd rrr\<close> by blast
  from \<open>odd (s*ss)\<close>  \<open>sss = s*ss\<close> have \<open>odd sss\<close> by blast
  show ?thesis 
    using \<open>Fract r (2 ^ k * s) + Fract rr (2 ^ kk * ss) = Fract rrr (2 ^ kk * sss)\<close> \<open>odd rrr\<close> \<open>odd sss\<close> by blast
qed   



lemma FundLemTwoDenoDepth:
  fixes u uu :: rat  and k kk :: nat
  assumes \<open>k < kk\<close> and \<open>depth u k\<close> and \<open>depth uu kk\<close>
  shows \<open>depth (u+uu) kk\<close>
proof-
  from \<open>depth u k\<close> obtain r s :: int 
    where \<open>odd r\<close> and \<open>odd s\<close> and \<open>Fract r (2^k*s) = u\<close>
    by (meson depth_def)
  from \<open>depth uu kk\<close> obtain rr ss :: int 
    where \<open>odd rr\<close> and \<open>odd ss\<close> and \<open>Fract rr (2^kk*ss) = uu\<close>
    by (meson depth_def)
  from \<open>Fract r (2^k*s) = u\<close>  \<open>Fract rr (2^kk*ss) = uu\<close>
  have \<open>u + uu = Fract r (2^k*s) + Fract rr (2^kk*ss)\<close>
    by blast
  then obtain rrr sss::int  where \<open>odd rrr\<close> and \<open>odd sss\<close> and  \<open>u+uu = Fract rrr (2^kk*sss) \<close>
    using FundLemTwoDeno
    by (metis \<open>odd r\<close> \<open>odd rr\<close> \<open>odd s\<close> \<open>odd ss\<close> assms(1))
  then show ?thesis 
    by (metis depth_def)
qed


lemma FundLemTwoDenoDepthGen:
  fixes uu :: rat  and n kk :: nat
    and u :: \<open>nat \<Rightarrow> rat\<close> and k :: \<open>nat \<Rightarrow> nat\<close>
  assumes \<open>\<forall> i. k i < kk\<close> and \<open>\<forall> i. depth (u i) (k i)\<close> and \<open>depth uu kk\<close>
  shows \<open>depth ((\<Sum>i=0..n. u i)+uu) kk\<close>
proof (induction n)
  case 0
  from  \<open>\<forall> i. k i < kk\<close> have \<open>k 0 < kk\<close>
    by simp
  from \<open>\<forall> i. depth (u i) (k i)\<close> have \<open>depth (u 0) (k 0)\<close>
    by simp
  from \<open>k 0 < kk\<close> \<open>depth (u 0) (k 0)\<close> have  \<open>depth ((u 0)+uu) kk\<close>
    using FundLemTwoDenoDepth assms(3) by blast
  then have \<open>depth ((\<Sum>i=0..0. u i)+uu) kk\<close> 
    by simp
  then show ?case 
    by blast
next
  case (Suc n)
  have \<open>sum u {0..Suc n} = (sum u {0..n}) + u (Suc n)\<close> 
    using sum.atLeast0_atMost_Suc by blast
  then have \<open>sum u {0..Suc n} + uu = ((sum u {0..n}) + uu) + u (Suc n)\<close>
    by linarith
  then show ?case 
    by (metis FundLemTwoDenoDepth Groups.add_ac(2) Suc assms(1) assms(2))
qed

lemma FundLemTwoDenoDepthGenRestr:
  fixes uu :: rat  and n kk :: nat
    and u :: \<open>nat \<Rightarrow> rat\<close> and k :: \<open>nat \<Rightarrow> nat\<close>
  assumes \<open>\<forall> i. (i \<le> n \<longrightarrow> k i < kk)\<close> and \<open>\<forall> i. (i \<le> n \<longrightarrow> depth (u i) (k i))\<close> and \<open>depth uu kk\<close>
  shows \<open>depth ((\<Sum>i=0..n. u i)+uu) kk\<close>
proof-
  obtain v :: \<open>nat \<Rightarrow> rat\<close> 
    where \<open>v \<equiv> \<lambda> i. ( if i \<le> n then u i else u n )\<close>
    by simp
  obtain kappa :: \<open>nat \<Rightarrow> nat\<close> 
    where \<open>kappa \<equiv> \<lambda> i. ( if i \<le> n then k i else k n )\<close>
    by simp
  have \<open>\<forall> i. i \<le> n \<longrightarrow> u i = v i\<close> 
    by (simp add: \<open>v \<equiv> \<lambda>i. if i \<le> n then u i else u n\<close>)
  then have \<open>(\<Sum>i=0..n. u i) = (\<Sum>i=0..n. v i)\<close> 
    by auto
  have \<open>\<forall> i. ( \<not>(i \<le> n) \<longrightarrow> v i = u n)\<close>
    by (simp add: \<open>v \<equiv> \<lambda>i. if i \<le> n then u i else u n\<close>)
  have \<open>\<forall> i. i \<le> n \<longrightarrow> k i = kappa i\<close> 
    by (simp add: \<open>kappa \<equiv> \<lambda>i. if i \<le> n then k i else k n\<close>)
  have \<open>\<forall> i. \<not>(i \<le> n) \<longrightarrow> k n = kappa i\<close> 
    by (simp add: \<open>kappa \<equiv> \<lambda>i. if i \<le> n then k i else k n\<close>)
  have \<open>\<forall> i. kappa i < kk\<close> 
    by (simp add: \<open>kappa \<equiv> \<lambda>i. if i \<le> n then k i else k n\<close> assms(1))
  have \<open>\<forall> i. depth (v i) (kappa i)\<close> 
    by (simp add: \<open>kappa \<equiv> \<lambda>i. if i \<le> n then k i else k n\<close> \<open>v \<equiv> \<lambda>i. if i \<le> n then u i else u n\<close> assms(2))
  have \<open>depth ((\<Sum>i=0..n. v i)+uu) kk\<close> 
    using FundLemTwoDenoDepthGen \<open>\<forall>i. depth (v i) (kappa i)\<close> \<open>\<forall>i. kappa i < kk\<close> assms(3) by blast
  then show ?thesis 
    by (simp add: \<open>sum u {0..n} = sum v {0..n}\<close>)
qed

lemma ErdosLemmaHarmonicEnd:
  fixes n i0 :: nat and u :: \<open>nat \<Rightarrow> rat\<close> and k :: \<open>nat \<Rightarrow> nat\<close>
  assumes \<open>\<forall> i. (i \<noteq> i0 \<longrightarrow>  k i < k i0)\<close> and \<open>\<forall> i.  depth (u i) (k i)\<close>
and \<open>i0 = n\<close>
  shows \<open>depth (\<Sum>i=0..n. u i) (k i0)\<close>
proof (cases n)
case 0
  then show ?thesis 
    by (simp add: assms(2) assms(3))
  next
  case (Suc nat)
  then obtain t :: nat where \<open>n = Suc t\<close> 
    by blast
  have \<open>(\<Sum>i=0..n. u i) = (\<Sum>i=0..t. u i) + (u i0)\<close> 
    by (simp add: \<open>n = Suc t\<close> assms(3))
  have \<open>\<forall> i. i \<le> t \<longrightarrow> depth (u i) (k i)\<close>
    using assms(2) assms(3) by auto
  from  \<open>\<forall> i. (i \<noteq> i0 \<longrightarrow>  k i < k i0)\<close> have  \<open>\<forall> i. (i < i0 \<longrightarrow>  k i < k i0)\<close>
    by simp
  then have \<open>\<forall> i. (i \<le> t \<longrightarrow>  k i < k i0)\<close> 
    by (simp add: \<open>n = Suc t\<close> assms(3))
    have \<open>depth (u i0) (k i0)\<close> 
      by (simp add: assms(2))
      have  \<open>depth ( (\<Sum>i=0..t. u i)+(u i0) ) (k i0)\<close>
        using FundLemTwoDenoDepthGenRestr \<open>\<forall>i\<le>t. k i < k i0\<close> assms(2) by blast
  then show ?thesis
    by (simp add: \<open>sum u {0..n} = sum u {0..t} + u i0\<close>)
qed

lemma ErdosLemmaHarmonicBegin:
  fixes n i0 :: nat and u :: \<open>nat \<Rightarrow> rat\<close> and k :: \<open>nat \<Rightarrow> nat\<close>
  assumes \<open>\<forall> i. (i \<noteq> i0 \<longrightarrow>  k i < k i0)\<close> and \<open>\<forall> i.  depth (u i) (k i)\<close>
and \<open>0 = i0\<close>
  shows \<open>depth (\<Sum>i=0..n. u i) (k i0)\<close>
proof(cases n )
  case 0
  then show ?thesis 
    by (simp add: assms(2) assms(3))
  next
  case (Suc nat)
  then obtain t :: nat where \<open>n = Suc t\<close> 
    by blast
  obtain v :: \<open>nat \<Rightarrow> rat\<close> where 
\<open>v \<equiv> \<lambda> i. (if i = 0 then (u n) else 
(if i = n then (u 0) else u i))\<close> 
    by auto
  have \<open>(\<Sum>i=0..n. u i) = (u 0) + (\<Sum>i=1..n. u i)\<close> 
    by (simp add: sum_head_Suc)
  then have \<open>(\<Sum>i=0..n. u i) = (v n) + (\<Sum>i=1..n. u i)\<close>
    by (simp add: \<open>v \<equiv> \<lambda>i. if i = 0 then u n else if i = n then u 0 else u i\<close>)
  then have \<open>(\<Sum>i=0..n. u i) = (v n) + (\<Sum>i=1..Suc t. u i)\<close> 
    using \<open>n = Suc t\<close> by blast
  then have \<open>(\<Sum>i=0..n. u i) = (v n) + (\<Sum>i=1..t. u i) + (u (Suc t))\<close>
    by simp
  then have \<open>(\<Sum>i=0..n. u i) = (v n) + (\<Sum>i=1..t. u i) + (u n)\<close>
    using \<open>n = Suc t\<close> by blast
  then have \<open>(\<Sum>i=0..n. u i) = (v n) + (\<Sum>i=1..t. u i) + (v 0)\<close>
    by (simp add: \<open>sum u {0..n} = v n + sum u {1..t} + u n\<close> \<open>v \<equiv> \<lambda>i. if i = 0 then u n else if i = n then u 0 else u i\<close>)
  then have \<open>(\<Sum>i=0..n. u i) = (v n) + (\<Sum>i=1..t. v i) + (v 0)\<close>
    using \<open>n = Suc t\<close> \<open>v \<equiv> \<lambda>i. if i = 0 then u n else if i = n then u 0 else u i\<close> by auto
  then  have \<open>(\<Sum>i=0..n. u i) = (\<Sum>i=0..n. v i)\<close> 
    by (simp add: \<open>n = Suc t\<close> sum_head_Suc)

  obtain kappa :: \<open>nat \<Rightarrow> nat\<close> where 
\<open>kappa \<equiv> \<lambda> i. (if i = 0 then (k n) else 
(if i = n then (k 0) else k i))\<close> 
    by auto
  from \<open>\<forall> i. (i \<noteq> i0 \<longrightarrow>  k i < k i0)\<close> have \<open>\<forall> i. (i \<noteq> n \<longrightarrow>  kappa i < kappa n)\<close>
    using \<open>kappa \<equiv> \<lambda>i. if i = 0 then k n else if i = n then k 0 else k i\<close> assms(3) by auto
  from \<open>\<forall> i.  depth (u i) (k i)\<close> have  \<open>\<forall> i.  depth (v i) (kappa i)\<close>
    by (simp add: \<open>kappa \<equiv> \<lambda>i. if i = 0 then k n else if i = n then k 0 else k i\<close> \<open>v \<equiv> \<lambda>i. if i = 0 then u n else if i = n then u 0 else u i\<close> assms(2))
  have \<open>depth (u i0) (k i0)\<close> 
    by (simp add: assms(2))
  from \<open>depth (u i0) (k i0)\<close> have \<open>depth (v i0) (kappa i0)\<close>
      by (simp add: \<open>\<forall>i. depth (v i) (kappa i)\<close>)
      
      have \<open>depth (\<Sum>i=0..n. v i) (kappa n)\<close>
        using ErdosLemmaHarmonicEnd \<open>\<forall>i. depth (v i) (kappa i)\<close> \<open>\<forall>i. i \<noteq> n \<longrightarrow> kappa i < kappa n\<close> by blast
  then have \<open>depth (\<Sum>i=0..n. u i) (k i0)\<close>
    by (metis \<open>kappa \<equiv> \<lambda>i. if i = 0 then k n else if i = n then k 0 else k i\<close> \<open>sum u {0..n} = sum v {0..n}\<close> assms(3))
    show ?thesis 
    using \<open>depth (sum u {0..n}) (k i0)\<close> by blast
qed


lemma SumChangeVariableQQ:
   fixes m :: nat and  u :: \<open>nat \<Rightarrow> rat\<close>
  shows  \<open>\<forall> a :: nat.  (\<Sum>i=a..a+m. u i) = (\<Sum>i=0..m. u (a+i))\<close>
proof(induction m)
  case 0
  then show ?case 
    by simp
next
  case (Suc m)
  then show ?case 
    by simp
qed

lemma SumChangeVariableQ:
   fixes m :: nat and  u :: \<open>nat \<Rightarrow> rat\<close>
  shows  \<open>\<forall> a n :: nat. a + m = n \<longrightarrow> (\<Sum>i=a..n. u i) = (\<Sum>i=0..m. u (a+i))\<close>
  using SumChangeVariableQQ by blast


lemma SumChangeVariable:
   fixes n m a :: nat and u :: \<open>nat \<Rightarrow> rat\<close>
  assumes \<open>a + m = n\<close>
  shows \<open>(\<Sum>i=a..n. u i) = (\<Sum>i=0..m. u (a+i))\<close>
  using SumChangeVariableQ assms by blast

lemma ErdosLemmaHarmonicMiddle:
  fixes n i0 :: nat and u :: \<open>nat \<Rightarrow> rat\<close> and k :: \<open>nat \<Rightarrow> nat\<close>
  assumes \<open>\<forall> i. (i \<noteq> i0 \<longrightarrow>  k i < k i0)\<close> and \<open>\<forall> i.  depth (u i) (k i)\<close>
and \<open>0 < i0\<close> and \<open>i0 < n\<close>
  shows \<open>depth (\<Sum>i=0..n. u i) (k i0)\<close>
proof-
  have \<open>(\<Sum>i=0..n. u i) = (\<Sum>i=0..i0. u i) + (\<Sum>i=i0+1..n. u i) \<close>
    using assms(4) atLeast0AtMost less_imp_add_positive sum_up_index_split by fastforce
  have \<open>depth (\<Sum>i=0..i0. u i) (k i0)\<close> 
    using ErdosLemmaHarmonicEnd assms(1) assms(2) assms(3) by blast

  obtain a :: nat where \<open>a = i0+1\<close> 
    by blast

  obtain m :: nat where \<open>a + m = n\<close> 
    by (metis (full_types) Suc_eq_plus1 Suc_le_mono \<open>a = i0 + 1\<close> add.comm_neutral  assms(4) le_add1 le_antisym le_simps(3)  less_imp_add_positive nat_neq_iff )
  from  \<open>a + m = n\<close>  have \<open>(\<Sum>i=a..n. u i) = (\<Sum>i=0..m. u (a+i))\<close> 
    using SumChangeVariable by blast

  obtain v :: \<open>nat \<Rightarrow> rat\<close> where \<open>v \<equiv> \<lambda> i. (u (a + i))\<close> 
    by simp

  from \<open>(\<Sum>i=a..n. u i) = (\<Sum>i=0..m. u (a+i))\<close> have  \<open>(\<Sum>i=a..n. u i) = (\<Sum>i=0..m. v i)\<close>
    using \<open>v \<equiv> \<lambda>i. u (a + i)\<close> by blast

  obtain kappa :: \<open>nat \<Rightarrow> nat\<close> where \<open>kappa \<equiv> \<lambda> i. (k (a + i))\<close> 
    by simp

  from \<open>\<forall> i. (i \<noteq> i0 \<longrightarrow>  k i < k i0)\<close> have \<open>\<forall> i. (kappa i < k i0)\<close> 
    by (simp add: \<open>a = i0 + 1\<close> \<open>kappa \<equiv> \<lambda>i. k (a + i)\<close>)

  from  \<open>\<forall> i. depth (u i) (k i)\<close> have  \<open>\<forall> i. depth (v i) (kappa i)\<close>
    by (simp add: \<open>kappa \<equiv> \<lambda>i. k (a + i)\<close> \<open>v \<equiv> \<lambda>i. u (a + i)\<close>)

  from  \<open>\<forall> i. depth (v i) (kappa i)\<close>  \<open>\<forall> i. (kappa i < k i0)\<close> \<open>depth (\<Sum>i=0..i0. u i) (k i0)\<close> 
  have \<open>depth ( (\<Sum>i=0..m. v i)+(\<Sum>i=0..i0. u i) ) (k i0)\<close> 
    using FundLemTwoDenoDepthGen by blast
  then show ?thesis 
    by (metis \<open>a = i0 + 1\<close> \<open>sum u {0..n} = sum u {0..i0} + sum u {i0 + 1..n}\<close> \<open>sum u {a..n} = sum v {0..m}\<close> add.commute)
qed

lemma ErdosLemmaHarmonic:
  fixes n i0 :: nat and u :: \<open>nat \<Rightarrow> rat\<close> and k :: \<open>nat \<Rightarrow> nat\<close>
  assumes \<open>\<forall> i. (i \<noteq> i0 \<longrightarrow>  k i < k i0)\<close> and \<open>\<forall> i. depth (u i) (k i)\<close>
    and \<open>i0 \<le> n\<close>
  shows \<open>depth (\<Sum>i=0..n. u i) (k i0)\<close>
  by (metis ErdosLemmaHarmonicBegin ErdosLemmaHarmonicEnd ErdosLemmaHarmonicMiddle assms(1) assms(2) assms(3) gr0I order.not_eq_order_implies_strict)

lemma ErdosLemmaHarmonicBounded:
  fixes n i0 :: nat and u :: \<open>nat \<Rightarrow> rat\<close> and k :: \<open>nat \<Rightarrow> nat\<close>
  assumes \<open>\<forall> i. (i \<noteq> i0 \<and> i \<le> n \<longrightarrow>  k i < k i0)\<close> and \<open>\<forall> i. (i \<le> n \<longrightarrow> depth (u i) (k i))\<close>
    and \<open>i0 \<le> n\<close> and \<open>n \<noteq> 0\<close>
  shows \<open>depth (\<Sum>i=0..n. u i) (k i0)\<close>
proof-
  from \<open>n \<noteq> 0\<close> obtain j0 :: nat where \<open>j0 \<noteq> i0\<close> and \<open>j0 \<le> n\<close> 
    by (metis le_simps(3) nat_le_linear neq0_conv)

  obtain v :: \<open>nat \<Rightarrow> rat\<close> where
\<open>v \<equiv> \<lambda> i. (if i \<le> n then u i else u j0)\<close> 
    by simp

  obtain kappa :: \<open>nat \<Rightarrow> nat\<close> where
\<open>kappa \<equiv> \<lambda> i. (if i \<le> n then k i else k j0)\<close>
    by simp

    have \<open>(\<Sum>i=0..n. u i) = (\<Sum>i=0..n. v i) \<close> 
      using \<open>v \<equiv> \<lambda>i. if i \<le> n then u i else u j0\<close> by auto

    from \<open>\<forall> i. (i \<le> n \<longrightarrow> depth (u i) (k i))\<close>
      have \<open>\<forall> i. (i \<noteq> i0 \<and> i \<le> n \<longrightarrow> depth (v i) (kappa i))\<close>
        by (simp add: \<open>kappa \<equiv> \<lambda>i. if i \<le> n then k i else k j0\<close> \<open>v \<equiv> \<lambda>i. if i \<le> n then u i else u j0\<close>)

      have  \<open>depth (v j0) (k j0)\<close> 
        using \<open>j0 \<le> n\<close> \<open>j0 \<noteq> i0\<close> \<open>v \<equiv> \<lambda>i. if i \<le> n then u i else u j0\<close> assms(2) by auto

      then have \<open>\<forall> i. (\<not>(i \<le> n) \<longrightarrow> depth (v i) (kappa i))\<close> 
        using \<open>kappa \<equiv> \<lambda>i. if i \<le> n then k i else k j0\<close> \<open>v \<equiv> \<lambda>i. if i \<le> n then u i else u j0\<close> by auto

      have \<open>depth (\<Sum>i=0..n. v i) (k i0)\<close> 
        by (metis ErdosLemmaHarmonic \<open>j0 \<le> n\<close> \<open>j0 \<noteq> i0\<close> \<open>kappa \<equiv> \<lambda>i. if i \<le> n then k i else k j0\<close> \<open>v \<equiv> \<lambda>i. if i \<le> n then u i else u j0\<close> assms(1) assms(2) assms(3))

      then show ?thesis 
        by (simp add: \<open>sum u {0..n} = sum v {0..n}\<close>)
    qed


lemma ErdosLemmaHarmonicBoundedGen:
  fixes n i0 a :: nat and u :: \<open>nat \<Rightarrow> rat\<close> and k :: \<open>nat \<Rightarrow> nat\<close>
  assumes \<open>\<forall> i. (i \<noteq> i0 \<and> a \<le> i \<and> i \<le> n \<longrightarrow>  k i < k i0)\<close>
    and \<open>\<forall> i. (a \<le> i \<and> i \<le> n \<longrightarrow> depth (u i) (k i))\<close>
    and \<open>a \<le> i0\<close> and  \<open>i0 \<le> n\<close> and \<open>a < n\<close>
  shows \<open>depth (\<Sum>i=a..n. u i) (k i0)\<close>
proof-
  obtain v :: \<open>nat \<Rightarrow> rat\<close> where 
    \<open>v \<equiv> \<lambda> i. (u (a + i))\<close> 
    by simp

  obtain kappa :: \<open>nat \<Rightarrow> nat\<close> where
    \<open>kappa \<equiv> \<lambda> i. (k  (a + i))\<close> 
    by simp

  obtain j0 :: nat where \<open>a + j0 = i0\<close> 
    using assms(3) nat_le_iff_add by auto

  obtain m :: nat where \<open>a + m = n\<close> 
    using assms(5) less_imp_add_positive by auto

  from \<open>\<forall> i. (i \<noteq> i0 \<and> a \<le> i \<and> i \<le> n \<longrightarrow>  k i < k i0)\<close>
  have \<open>\<forall> i. (i \<noteq> a+j0 \<and> a \<le> i \<and> i \<le> a+m \<longrightarrow>  k i < k (a+j0))\<close> 
    using \<open>a + j0 = i0\<close> \<open>a + m = n\<close> by blast
  then have   \<open>\<forall> i. (a+i \<noteq> a+j0 \<and> a \<le> a+i \<and> a+i \<le> a+m \<longrightarrow>  k (a+i) < k (a+j0))\<close> 
    by (simp add: le_add1)
  then have   \<open>\<forall> i. (i \<noteq> j0 \<and> 0 \<le> i \<and> i \<le> m \<longrightarrow>  k (a+i) < k (a+j0))\<close> 
    by auto
  then have   \<open>\<forall> i. (i \<noteq> j0 \<and> i \<le> m \<longrightarrow>  k (a+i) < k (a+j0))\<close> 
    by simp
  then  have  \<open>\<forall> i. (i \<noteq> j0 \<and> i \<le> m \<longrightarrow>  kappa i < kappa j0)\<close>  
    using \<open>kappa \<equiv> \<lambda>i. k (a + i)\<close> by blast

  from \<open>\<forall> i. (a \<le> i \<and> i \<le> n \<longrightarrow> depth (u i) (k i))\<close>
    have  \<open>\<forall> i. ( a+i \<le> a+m \<longrightarrow> depth (u (a+i)) (k (a+i)))\<close>
      by (simp add: \<open>a + m = n\<close>)
    then  have  \<open>\<forall> i. ( i \<le> m \<longrightarrow> depth (u (a+i)) (k (a+i)))\<close>
      by simp
      then have  \<open>\<forall> i. ( i \<le> m \<longrightarrow> depth (u (a+i)) (kappa i))\<close>
        using \<open>kappa \<equiv> \<lambda>i. k (a + i)\<close> by blast
      then have  \<open>\<forall> i. ( i \<le> m \<longrightarrow> depth (v i) (kappa i))\<close>
        using \<open>v \<equiv> \<lambda>i. u (a + i)\<close> by blast

      have \<open>depth (\<Sum>i=0..m. v i) (kappa j0)\<close> 
        using ErdosLemmaHarmonicBounded \<open>\<forall>i. i \<noteq> j0 \<and> i \<le> m \<longrightarrow> kappa i < kappa j0\<close> \<open>\<forall>i\<le>m. depth (v i) (kappa i)\<close> \<open>a + j0 = i0\<close> \<open>a + m = n\<close> assms(4) assms(5) by auto
      then have  \<open>depth (\<Sum>i=0..m. u (a + i)) (k (a + j0))\<close> 
        using \<open>kappa \<equiv> \<lambda>i. k (a + i)\<close> \<open>v \<equiv> \<lambda>i. u (a + i)\<close> by blast
      then have  \<open>depth (\<Sum>i=a..a+m. (u i)) (k i0)\<close> 
        by (metis SumChangeVariable \<open>a + j0 = i0\<close> \<open>a + m = n\<close>) 
      then show ?thesis 
        using \<open>a + m = n\<close> by blast
    qed


section {* Application to Harmonic Numbers *}

subsection {* Trivial Auxiliary Results *}


lemma ParityDescomposition:
  fixes n::nat
  assumes \<open>n \<ge> 1\<close>
  shows \<open>\<exists> k t :: nat. n = (2::nat)^k*t \<and> odd t\<close>
  by (metis TrapezoidalNumbersSuf_1C assms   less_one linorder_not_le     )



lemma Pow2inj:
  fixes n m::nat
  assumes \<open> (2::nat)^n = (2::nat)^m\<close>
  shows \<open>n = m\<close>
  using assms by auto

lemma oneovernlem:
  fixes n k:: nat
  assumes \<open>n \<noteq> 0\<close> \<open>depth (Fract 1 n) k \<close>
  shows \<open>\<exists> t :: nat. n = (2::nat)^k*t \<and> odd t \<close>
  proof-
    obtain r s :: int where \<open>odd r\<close> and \<open>odd s\<close> and \<open>Fract 1 n = Fract r ((2::int)^k * s)\<close>
      by (metis assms(2) depth_def)
    have \<open>(2::int)^k * s = n * r\<close>
      by (smt \<open>Fract 1 (int n) = Fract r (2 ^ k * s)\<close> \<open>odd s\<close> assms(1) eq_rat(1) even_zero mult.assoc mult.commute mult_cancel_left of_nat_eq_0_iff one_power2 power2_eq_square power_eq_0_iff)    
    then have \<open>r dvd ((2::int)^k * s)\<close>
      by simp
    have \<open>coprime r ((2::int)^k)\<close> 
      by (simp add: \<open>odd r\<close>)
    then have \<open>r dvd s\<close> 
      using \<open>r dvd 2 ^ k * s\<close> coprime_dvd_mult_right_iff by blast
    then obtain e :: int where \<open>r * e = s\<close> 
      by blast
    then have \<open>(2::int)^k * r * e = n * r\<close> 
      by (simp add: \<open>2 ^ k * s = int n * r\<close> mult.assoc)
    then have \<open>(2::int)^k * e = n\<close> 
      using \<open>odd r\<close> by auto
    have \<open>odd e\<close> 
      using \<open>odd s\<close> \<open>r * e = s\<close> even_mult_iff by blast
    have \<open>e \<ge> 0\<close> 
      by (smt One_nat_def Suc_nat_eq_nat_zadd1 \<open>2 ^ k * e = int n\<close> add.right_neutral add_Suc_right arith_special(3) assms(1) mult_zero_right nat_1 nat_int nat_le_0 nat_mult_distrib nat_power_eq power_eq_0_iff rel_simps(76))
    from \<open>e \<ge> 0\<close> \<open>odd e\<close> \<open>(2::int)^k * e = n\<close>  show ?thesis 
      by (smt One_nat_def Suc_eq_plus1 Suc_nat_eq_nat_zadd1 arith_special(3) even_nat_iff nat_1 nat_int nat_mult_distrib nat_power_eq zero_le_power)
  qed

subsection {* Auxiliary Results V *}

lemma ErdosFSDFDSFSDFSWEFDEW:
  assumes \<open>\<exists> t::nat. (2::nat)^(a+1) = (2::nat)^(k (2^(a+1) ))*t \<and> odd t\<close>
shows \<open>a+1 = k ((2::nat)^(a+1))\<close> 
proof-
  obtain t::nat where \<open>(2::nat)^(a+1) = (2::nat)^(k (2^(a+1) ))*t\<close> and \<open>odd t\<close> 
    using assms by blast
  from \<open>2^(a+1) = 2^(k (2^(a+1) ))*t\<close> 
  have \<open>t \<noteq> 0\<close> 
    using \<open>odd t\<close> by presburger
  have \<open> t dvd ((2::nat)^(a+1)) \<close>
    by (metis \<open>2 ^ (a + 1) = 2 ^ k (2 ^ (a + 1)) * t\<close> dvd_triv_right)
    then have \<open>t = 1\<close> using \<open>odd t\<close>  \<open>t \<noteq> 0\<close> 
      by (metis TrapezoidalNumbersNec2_5recA \<open>2 ^ (a + 1) = 2 ^ k (2 ^ (a + 1)) * t\<close>)
      then have \<open>(2::nat)^(a+1) = (2::nat)^(k (2^(a+1) ))\<close> using \<open>(2::nat)^(a+1) = (2::nat)^(k (2^(a+1) ))*t\<close>
      by simp
    then show ?thesis 
      using Pow2inj by blast
  qed

lemma WeakEuclidPow2A:
  fixes n::nat
  shows \<open>\<exists> a b :: nat. n+2 = 2^(a+1) + b \<and> b < 2^(a+1)\<close>
proof(induction n)
  case 0
  then show ?case 
    by (metis add.right_neutral  plus_nat.add_0 pos2 power_one_right )
next
  case (Suc n)
  then show ?case 
    by (smt Suc_leI add.right_neutral add_Suc_right arith_simps(1) arith_simps(45) le_eq_less_or_eq mult_2 numeral_code(1) plus_1_eq_Suc power.simps(1) power.simps(2) power_add semiring_normalization_rules(23) zero_less_Suc)
qed


lemma WeakEuclidPow2:
  fixes n::nat
  assumes \<open>n \<ge> 2\<close>
  shows \<open>\<exists> a b :: nat. n = 2^(a+1) + b \<and> b < 2^(a+1)\<close>
  by (metis WeakEuclidPow2A add.commute assms le_Suc_ex)

lemma FractPropor:
  fixes a b c d :: int
  assumes \<open>Fract a b = Fract c d\<close> and \<open>b \<noteq> 0\<close> and  \<open>d \<noteq> 0\<close> and \<open>coprime a b\<close>
  shows \<open>\<exists> k :: int. a*k = c \<and> b*k = d\<close>
proof-
  from \<open>Fract a b = Fract c d\<close> and \<open>b \<noteq> 0\<close> and  \<open>d \<noteq> 0\<close>
  have \<open>a*d = b*c\<close> 
    using eq_rat(1) by auto
  from \<open>a*d = b*c\<close> have \<open>b dvd (a*d)\<close> 
    by (metis dvd_triv_left)
  then have \<open>b dvd d\<close> 
    using assms(4) coprime_commute coprime_dvd_mult_right_iff by blast
  then obtain k :: int where \<open>b*k = d\<close> 
    by blast
  have \<open>a*k = c\<close> 
    using \<open>a * d = b * c\<close> \<open>b * k = d\<close> assms(2) by auto
  show ?thesis 
    using \<open>a * k = c\<close> \<open>b * k = d\<close> by blast
qed

subsection  {* Auxiliary Results IV *}


lemma ErdosLemmaHarmonicBoundedGenCaseA5trivial1:
  fixes n k t::nat
  assumes \<open>n \<ge> 1\<close> \<open>n = 2^k*t\<close> \<open>odd t\<close>
  shows \<open>depth (Fract 1 n) k\<close>
proof-
    have \<open>Fract (of_nat 1) (of_nat n) = Fract (of_nat 1) (2^k*(of_nat t))\<close>
     by (simp add: \<open>n = 2 ^ k * t\<close>)
   have \<open>odd (of_nat 1)\<close> by simp
   have \<open>odd (of_nat t)\<close> 
     by (simp add: assms(3))
  from \<open>odd (of_nat 1)\<close> \<open>odd (of_nat t)\<close> \<open>Fract (of_nat 1) (of_nat n) = Fract (of_nat 1) (2^k*(of_nat t))\<close> 
    have \<open>depth (Fract (of_nat 1) (of_nat n)) k\<close> 
      by (smt depth_def)
  then show ?thesis 
    by simp
qed

lemma ErdosLemmaHarmonicBoundedGenCaseA5trivial1A:
  fixes n ::nat
  assumes \<open>n \<ge> 1\<close> 
  shows \<open>\<exists> k t. n = 2^k*t \<and> odd t \<and> depth (Fract 1 n) k\<close>
  using ErdosLemmaHarmonicBoundedGenCaseA5trivial1 ParityDescomposition assms by blast

lemma ErdosLemmaHarmonicBoundedGenCaseA5trivial1B:
 \<open>\<forall> n :: nat. \<exists> k:: nat. (\<exists> t::nat. (n \<ge> 1 \<longrightarrow> (n = 2^k*t \<and> odd t \<and> depth (Fract 1 n) k) ) )\<close>
proof -
  obtain nn :: "nat \<Rightarrow> nat" and nna :: "nat \<Rightarrow> nat" where
    f1: "\<forall>n. depth (Fract 1 (int n)) (nn n) \<and> odd (nna n) \<and> 2 ^ nn n * nna n = n \<or> \<not> 1 \<le> n"
    using ErdosLemmaHarmonicBoundedGenCaseA5trivial1A by moura
  then have "\<forall>n. odd (int (nna n)) \<or> \<not> 1 \<le> n"
    by auto
  then show ?thesis
    using f1 by (metis (no_types) of_nat_1 of_nat_eq_of_nat_power_cancel_iff of_nat_le_of_nat_power_cancel_iff of_nat_mult power_one real_of_nat_eq_numeral_power_cancel_iff)
qed


lemma ErdosLemmaHarmonicBoundedGenCaseA5trivial1Choice:
  \<open>\<forall> n :: nat. \<exists> k:: nat. (\<exists> t::nat. (n \<ge> 1 \<longrightarrow> (n = 2^k*t \<and> odd t \<and> depth (Fract 1 n) k) ) ) \<Longrightarrow> \<exists> k:: nat\<Rightarrow>nat. \<forall> n :: nat. (\<exists> t::nat. (n \<ge> 1 \<longrightarrow> (n = 2^(k n)*t \<and> odd t \<and> depth (Fract 1 n) (k n)) ) )\<close>
   by (rule Hilbert_Choice.choice) 

lemma ErdosLemmaHarmonicBoundedGenCaseA5trivial1C:
 \<open>\<exists> k:: nat\<Rightarrow>nat. \<forall> n :: nat. (\<exists> t::nat. (n \<ge> 1 \<longrightarrow> (n = 2^(k n)*t \<and> odd t \<and> depth (Fract 1 n) (k n)) ) )\<close>
  using ErdosLemmaHarmonicBoundedGenCaseA5trivial1A ErdosLemmaHarmonicBoundedGenCaseA5trivial1Choice by auto


lemma ErdosLemmaHarmonicBoundedGenCaseA5trivialZ:
  fixes n :: nat 
  shows \<open>\<exists>  k :: nat \<Rightarrow> nat. ( \<forall> i. (1 \<le> i \<and> i \<le> n  \<longrightarrow> ((depth (Fract 1 i) (k i))\<and> (\<exists> t::nat. i = 2^(k i)*t \<and> odd t )) )) \<close>
  using ErdosLemmaHarmonicBoundedGenCaseA5trivial1C by blast

lemma ErdosLemmaHarmonicBoundedGenCaseA5trivialY:
  fixes a b :: nat 
  shows \<open>\<exists>  k :: nat \<Rightarrow> nat. ( \<forall> i. (1 \<le> i \<and> i \<le> 2^(a+1)+b  \<longrightarrow> ((depth (Fract 1 i) (k i))\<and> (\<exists> t::nat. i = 2^(k i)*t \<and> odd t )) )) \<close>
  by (meson ErdosLemmaHarmonicBoundedGenCaseA5trivial1C)

lemma ErdosLemmaHarmonicBoundedGenCaseA5trivialX:
  fixes a b :: nat 
  shows \<open>\<exists>  k :: nat \<Rightarrow> nat. ( \<forall> i. (1 \<le> i \<and> i \<le> 2^(a+1)+b  \<longrightarrow> ((depth (Fract 1 i) (k i))\<and> (\<exists> t::nat. 2^(a+1) = 2^(k (2^(a+1) ))*t \<and> odd t )) )) \<close>
  using ErdosLemmaHarmonicBoundedGenCaseA5trivial1C one_le_numeral one_le_power by blast

lemma ErdosLemmaHarmonicBoundedGenCaseA5trivialXZ:
  fixes a b :: nat 
  shows \<open>\<exists>  k :: nat \<Rightarrow> nat. (\<exists> t::nat. 2^(a+1) = 2^(k (2^(a+1) ))*t \<and> odd t ) \<and>( \<forall> i. (1 \<le> i \<and> i \<le> 2^(a+1)+b  \<longrightarrow> ((depth (Fract 1 i) (k i))) )) \<close>
  using ErdosLemmaHarmonicBoundedGenCaseA5trivial1C one_le_numeral one_le_power by blast


lemma ErdosLemmaHarmonicBoundedGenCaseA5trivialXY:
  fixes a b :: nat 
  shows \<open>\<exists>  k :: nat \<Rightarrow> nat. ( a+1 = k (2^(a+1)) ) \<and>( \<forall> i. (1 \<le> i \<and> i \<le> 2^(a+1)+b  \<longrightarrow> ((depth (Fract 1 i) (k i))) )) \<close>
  using ErdosFSDFDSFSDFSWEFDEW ErdosLemmaHarmonicBoundedGenCaseA5trivialXZ by blast



lemma ErdosLemmaHarmonicBoundedGenCaseA5trivial:
  fixes a b :: nat 
  assumes \<open>b < 2^(a+1)\<close> 
  shows \<open>\<exists>  k :: nat \<Rightarrow> nat. ( \<forall> i. (1 \<le> i \<and> i \<le> 2^(a+1)+b  \<longrightarrow> depth (Fract 1 i) (k i))) \<and> (k (2^(a+1)) = a+1 )\<close>
  using ErdosLemmaHarmonicBoundedGenCaseA5trivialXY by fastforce

subsection  {* Auxiliary Results III *}

lemma HarmonicNumbersParityNumeratorDenominator3X1Zeq:
  fixes a b :: nat and  k :: \<open>nat \<Rightarrow> nat\<close>
  assumes \<open>b < 2^(a+1)\<close> and \<open>\<forall> i. (1 \<le> i \<and> i \<le> 2^(a+1)+b  \<longrightarrow> depth (Fract 1 i) (k i))\<close>
  shows \<open>\<forall> i. (i = 2^(a+1)  \<and> i \<noteq> 2^(a+1)  \<and> 1 \<le> i \<and> i \<le> 2^(a+1)+b \<longrightarrow>  k i < k (2^(a+1) ))\<close>
  by blast


lemma LemTrivialFSWRWER:
  fixes a b i :: nat and  k :: \<open>nat \<Rightarrow> nat\<close>
  assumes \<open>b < 2^(a+1)\<close> and \<open>\<forall> i. (1 \<le> i \<and> i \<le> 2^(a+1)+b  \<longrightarrow> depth (Fract 1 i) (k i))\<close>
  shows \<open>k (2^(a+1) ) = a+1\<close>
proof-
  have \<open>depth (Fract 1 ((2::nat)^(a+1))) (k ( (2::nat)^(a+1) ))\<close> 
    using assms(2) le_add1 one_le_numeral one_le_power by blast
  then obtain t::nat where \<open>odd t\<close> and \<open>(2::nat)^(a+1) = 2^(k ( (2::nat)^(a+1) ))*t \<close> 
    by (metis oneovernlem power_eq_0_iff zero_neq_numeral)
  from  \<open>(2::nat)^(a+1) = 2^(k ( (2::nat)^(a+1) ))*t \<close> 
  have \<open>t dvd (2::nat)^(a+1)\<close> 
    by (metis dvd_triv_right)
  then have \<open>t = 1\<close> 
    by (metis TrapezoidalNumbersNec2_5recA \<open>2 ^ (a + 1) = 2 ^ k (2 ^ (a + 1)) * t\<close> \<open>odd t\<close>)
  then have \<open>(2::nat)^(a+1) = 2^(k ( (2::nat)^(a+1) )) \<close>
    using \<open>2 ^ (a + 1) = 2 ^ k (2 ^ (a + 1)) * t\<close> by auto
  then have \<open>a+1 = k ( (2::nat)^(a+1) )\<close> 
    using Pow2inj by blast
  then show ?thesis 
    by linarith
qed

lemma HarmonicNumbersParityNumeratorDenominator3X1ZlessSimp:
  fixes a b i :: nat and  k :: \<open>nat \<Rightarrow> nat\<close>
  assumes \<open>b < 2^(a+1)\<close> and \<open>\<forall> i. (1 \<le> i \<and> i \<le> 2^(a+1)+b  \<longrightarrow> depth (Fract 1 i) (k i))\<close>
and \<open>i < 2^(a+1)\<close> and \<open>1 \<le> i\<close> and \<open>i \<le> 2^(a+1)+b\<close> 
  shows \<open>k i < k (2^(a+1) )\<close>
proof-
  have \<open>k (2^(a+1) ) = a+1\<close> 
     using LemTrivialFSWRWER assms(1) assms(2) by blast
  have \<open>depth (Fract 1 i) (k i)\<close> 
    using assms(2) assms(4) assms(5) by blast
  then obtain r s :: int where \<open>odd r\<close> and \<open>odd s\<close> and \<open>Fract 1 i = Fract r (2^(k i) * s)\<close> 
    by (metis depth_def)
  obtain t::nat where \<open>i = 2^(k i) * t\<close> and \<open>odd t\<close>  
    by (metis \<open>depth (Fract 1 (int i)) (k i)\<close> assms(4) less_one linorder_not_le oneovernlem)
  from \<open>i = 2^(k i) * t\<close> have \<open>2^(k i) \<le> i\<close> 
    by (metis One_nat_def assms(4) mult_le_mono mult_numeral_1_right numeral_One one_le_mult_iff order_refl)
  from \<open>2^(k i) \<le> i\<close>  \<open>i < 2^(a+1)\<close>   have \<open>(2::nat)^(k i) <  (2::nat)^(a+1)\<close> 
    by linarith
  then have \<open>k i < a+1\<close> 
    using one_less_numeral_iff power_less_imp_less_exp semiring_norm(76) by blast
  then show ?thesis 
    using \<open>k (2 ^ (a + 1)) = a + 1\<close> by linarith
qed


lemma HarmonicNumbersParityNumeratorDenominator3X1ZmoreSimpbnon0:
  fixes a b i :: nat and  k :: \<open>nat \<Rightarrow> nat\<close>
  assumes \<open>b < 2^(a+1)\<close> and \<open>\<forall> i. (1 \<le> i \<and> i \<le> 2^(a+1)+b  \<longrightarrow> depth (Fract 1 i) (k i))\<close>
and \<open>i > 2^(a+1)\<close> and \<open>1 \<le> i\<close> and \<open>i \<le> 2^(a+1)+b\<close> and \<open>b \<noteq> 0\<close>
  shows \<open> k i < k (2^(a+1))\<close>
proof (rule classical)
  assume \<open>\<not> (k i < k (2^(a+1)))\<close>
  then have \<open>k i \<ge>  k (2^(a+1))\<close> 
    using not_le by blast
 have \<open>k (2^(a+1) ) = a+1\<close> 
   using LemTrivialFSWRWER assms(1) assms(2) by blast
  then have \<open>k i \<ge> a+1\<close> using \<open>k i \<ge>  k (2^(a+1))\<close> 
    by linarith 
  have \<open>depth (Fract 1 i) (k i)\<close> 
    using assms(2) assms(4) assms(5) by blast
  then obtain r s :: int where \<open>odd r\<close> and \<open>odd s\<close> and \<open>Fract 1 i = Fract r (2^(k i) * s)\<close> 
    by (metis depth_def)
  obtain t::nat where \<open>i = 2^(k i) * t\<close> and \<open>odd t\<close>  
    by (metis \<open>depth (Fract 1 (int i)) (k i)\<close> assms(4) less_one linorder_not_le oneovernlem)

  obtain j :: nat where \<open>2^(a+1) + j = i\<close> 
    using assms(3) less_imp_add_positive by blast
  have \<open>j \<le> b\<close> 
    using \<open>2 ^ (a + 1) + j = i\<close> add_le_cancel_left assms(5) by blast

  then have \<open>j < 2^(a+1)\<close> 
    using assms(1) by linarith

  have \<open>2^(a+1) dvd i\<close> 
    by (metis \<open>i = 2 ^ k i * t\<close> \<open>k (2 ^ (a + 1)) = a + 1\<close> \<open>k (2 ^ (a + 1)) \<le> k i\<close> dvd_mult2 le_imp_power_dvd)

  have \<open>2^(a+1) dvd j\<close> 
    using \<open>2 ^ (a + 1) + j = i\<close> \<open>2 ^ (a + 1) dvd i\<close> dvd_add_triv_left_iff by blast

  from \<open>j < (2::nat)^(a+1)\<close>  \<open>(2::nat)^(a+1) dvd j\<close>  have \<open>j = 0\<close> 
    using dvd_imp_le linorder_not_le by auto

  have \<open>i = 2^(a+1) \<close> 
    using \<open>2 ^ (a + 1) + j = i\<close> \<open>j = 0\<close> add.right_neutral by blast
  have False 
    using \<open>i = 2 ^ (a + 1)\<close> assms(3) by blast
  then show ?thesis 
    by blast
qed


lemma HarmonicNumbersParityNumeratorDenominator3X1ZmoreSimpb0:
  fixes a b i :: nat and  k :: \<open>nat \<Rightarrow> nat\<close>
  assumes \<open>b < 2^(a+1)\<close> and \<open>\<forall> i. (1 \<le> i \<and> i \<le> 2^(a+1)+b  \<longrightarrow> depth (Fract 1 i) (k i))\<close>
and \<open>i > 2^(a+1)\<close> and \<open>1 \<le> i\<close> and \<open>i \<le> 2^(a+1)+b\<close> and \<open>b = 0\<close>
  shows \<open> k i < k (2^(a+1) )\<close>
  using assms(3) assms(5) assms(6) by linarith

lemma HarmonicNumbersParityNumeratorDenominator3X1ZmoreSimp:
  fixes a b i :: nat and  k :: \<open>nat \<Rightarrow> nat\<close>
  assumes \<open>b < 2^(a+1)\<close> and \<open>\<forall> i. (1 \<le> i \<and> i \<le> 2^(a+1)+b  \<longrightarrow> depth (Fract 1 i) (k i))\<close>
and \<open>i > 2^(a+1)\<close> and \<open>1 \<le> i\<close> and \<open>i \<le> 2^(a+1)+b\<close> 
  shows \<open> k i < k (2^(a+1) )\<close>
  using HarmonicNumbersParityNumeratorDenominator3X1ZmoreSimpbnon0 assms(1) assms(2) assms(3) assms(5) by auto

lemma HarmonicNumbersParityNumeratorDenominator3X1Zmore:
  fixes a b :: nat and  k :: \<open>nat \<Rightarrow> nat\<close>
  assumes \<open>b < 2^(a+1)\<close> and \<open>\<forall> i. (1 \<le> i \<and> i \<le> 2^(a+1)+b  \<longrightarrow> depth (Fract 1 i) (k i))\<close>
  shows \<open>\<forall> i. (i > 2^(a+1)  \<and> i \<noteq> 2^(a+1)  \<and> 1 \<le> i \<and> i \<le> 2^(a+1)+b \<longrightarrow>  k i < k (2^(a+1) ))\<close>
  using HarmonicNumbersParityNumeratorDenominator3X1ZmoreSimp assms(1) assms(2) by blast

lemma HarmonicNumbersParityNumeratorDenominator3X1Zless:
  fixes a b :: nat and  k :: \<open>nat \<Rightarrow> nat\<close>
  assumes \<open>b < 2^(a+1)\<close> and \<open>\<forall> i. (1 \<le> i \<and> i \<le> 2^(a+1)+b  \<longrightarrow> depth (Fract 1 i) (k i))\<close>
  shows \<open>\<forall> i. (i < 2^(a+1)  \<and> i \<noteq> 2^(a+1)  \<and> 1 \<le> i \<and> i \<le> 2^(a+1)+b \<longrightarrow>  k i < k (2^(a+1) ))\<close>
  using HarmonicNumbersParityNumeratorDenominator3X1ZlessSimp assms(1) assms(2) by blast

lemma trico:
  fixes a i::nat
  shows \<open> i < 2^(a+1) \<or> i > 2^(a+1) \<or> i = 2^(a+1)\<close>
  using linorder_neqE_nat by blast

lemma HarmonicNumbersParityNumeratorDenominator3X1:
  fixes a b :: nat and  k :: \<open>nat \<Rightarrow> nat\<close>
  assumes \<open>b < 2^(a+1)\<close> and \<open>\<forall> i. (1 \<le> i \<and> i \<le> 2^(a+1)+b  \<longrightarrow> depth (Fract 1 i) (k i))\<close>
  shows \<open>\<forall> i. (i \<noteq> 2^(a+1)  \<and> 1 \<le> i \<and> i \<le> 2^(a+1)+b \<longrightarrow>  k i < k (2^(a+1) ))\<close>
  using trico HarmonicNumbersParityNumeratorDenominator3X1Zless 
    HarmonicNumbersParityNumeratorDenominator3X1Zmore
    HarmonicNumbersParityNumeratorDenominator3X1Zeq
    assms(1) assms(2) by blast  

subsection  {* Auxiliary Results II *}

lemma ErdosLemmaHarmonicBoundedGenCaseA2:
  fixes n i0 :: nat  and k :: \<open>nat \<Rightarrow> nat\<close>
  assumes \<open>\<forall> i. (i \<noteq> i0 \<and> 1 \<le> i \<and> i \<le> n \<longrightarrow>  k i < k i0)\<close>
    and \<open>\<forall> i. (1 \<le> i \<and> i \<le> n \<longrightarrow> depth (Fract 1 i) (k i))\<close>
    and \<open>1 \<le> i0\<close> and  \<open>i0 \<le> n\<close> and \<open>1 < n\<close>
  shows \<open>depth (\<Sum>i=1..n. Fract 1 i) (k i0)\<close>
  using ErdosLemmaHarmonicBoundedGen assms(1) assms(2) assms(3) assms(4) assms(5) by auto

lemma ErdosLemmaHarmonicBoundedGenCaseA3:
  fixes a b :: nat  and k :: \<open>nat \<Rightarrow> nat\<close>
  assumes  \<open>\<forall> i. (i \<noteq> 2^(a+1)  \<and> 1 \<le> i \<and> i \<le> 2^(a+1)+b \<longrightarrow>  k i < k (2^(a+1) ))\<close>
    and \<open>\<forall> i. (1 \<le> i \<and> i \<le> 2^(a+1)+b  \<longrightarrow> depth (Fract 1 i) (k i))\<close>
    and \<open>1 \<le> 2^(a+1) \<close> and  \<open>2^(a+1) \<le> 2^(a+1)+b\<close> and \<open>1 < 2^(a+1) + b \<close>
  shows \<open>depth (\<Sum>i=1..2^(a+1) + b . Fract 1 i) (k (2^(a+1) ))\<close>
  using ErdosLemmaHarmonicBoundedGenCaseA2 assms(1) assms(2) assms(5) by auto


lemma ErdosLemmaHarmonicBoundedGenCaseA4trivial:
  fixes a b :: nat
shows  \<open>1 \<le> (2::nat)^(a+1) \<and> (2::nat)^(a+1) \<le> 2^(a+1)+b \<and> 1 < (2::nat)^(a+1) + b \<close>
  by (metis (no_types, lifting) One_nat_def le_add1 le_add2 le_eq_less_or_eq less_le_trans nat_power_eq_Suc_0_iff num.distinct(1) numeral_One numeral_eq_iff one_le_numeral one_le_power zero_less_one)


lemma ErdosLemmaHarmonicBoundedGenCaseA4:
  fixes a b :: nat  and k :: \<open>nat \<Rightarrow> nat\<close>
  assumes  \<open>\<forall> i. (i \<noteq> 2^(a+1)  \<and> 1 \<le> i \<and> i \<le> 2^(a+1)+b \<longrightarrow>  k i < k (2^(a+1) ))\<close>
    and \<open>\<forall> i. (1 \<le> i \<and> i \<le> 2^(a+1)+b  \<longrightarrow> depth (Fract 1 i) (k i))\<close>
  shows \<open>depth (\<Sum>i=1..2^(a+1) + b . Fract 1 i) (k (2^(a+1) ))\<close>
  using ErdosLemmaHarmonicBoundedGenCaseA2 ErdosLemmaHarmonicBoundedGenCaseA4trivial assms(1) assms(2) by blast


lemma ErdosLemmaHarmonicBoundedGenCaseA5:
  fixes a b :: nat  and k :: \<open>nat \<Rightarrow> nat\<close>
  assumes \<open>b < 2^(a+1)\<close> \<open>\<forall> i. (1 \<le> i \<and> i \<le> 2^(a+1)+b  \<longrightarrow> depth (Fract 1 i) (k i))\<close>
  shows \<open>depth (\<Sum>i=1..2^(a+1) + b . Fract 1 i) (k (2^(a+1) ))\<close>
  using ErdosLemmaHarmonicBoundedGenCaseA3 ErdosLemmaHarmonicBoundedGenCaseA4trivial HarmonicNumbersParityNumeratorDenominator3X1 assms(1) assms(2) by blast


lemma HarmonicNumbersParityNumeratorDenominator3:
  fixes a b :: nat 
  assumes \<open>b < 2^(a+1)\<close>
  shows \<open>depth (\<Sum> i = 1..2^(a+1) + b. (Fract 1 i) ) (a+1)\<close>
proof-
  from  \<open>b < 2^(a+1)\<close> obtain  k :: \<open>nat \<Rightarrow> nat\<close> where 
    \<open>\<forall> i. (1 \<le> i \<and> i \<le> 2^(a+1)+b  \<longrightarrow> depth (Fract 1 i) (k i))\<close> and  \<open>k (2^(a+1)) = a+1\<close>
    using ErdosLemmaHarmonicBoundedGenCaseA5trivial by blast
  then have  \<open>depth (\<Sum>i=1..2^(a+1) + b . Fract 1 i) (k (2^(a+1) ))\<close> 
    using ErdosLemmaHarmonicBoundedGenCaseA5 assms by blast
  then show ?thesis using \<open>k (2^(a+1)) = a+1\<close>
    by simp
qed

lemma HarmonicNumbersParityNumeratorDenominator2:
  fixes a b :: nat and r s :: int
  assumes \<open>b < 2^(a+1)\<close> and \<open> (\<Sum> k = 1..2^(a+1) + b. (Fract 1 k) ) = Fract r s \<close>
    and \<open>coprime r s\<close>
  shows \<open>odd r \<and> (\<exists> ss ::int. s = 2^(a+1)*ss \<and> odd ss)\<close>
proof-
  have \<open>depth (\<Sum> k = 1..2^(a+1) + b. (Fract 1 k) ) (a+1)\<close> 
    using HarmonicNumbersParityNumeratorDenominator3 assms(1) by blast
  then obtain r0 s0::int where \<open>odd r0\<close> and \<open>odd s0\<close> and \<open>Fract r0 (2^(a+1)*s0) = (\<Sum> k = 1..2^(a+1) + b. (Fract 1 k))\<close> 
    by (meson depth_def)
  from  \<open> (\<Sum> k = 1..2^(a+1) + b. (Fract 1 k) ) = Fract r s \<close> \<open>Fract r0 (2^(a+1)*s0) = (\<Sum> k = 1..2^(a+1) + b. (Fract 1 k))\<close> 
  have \<open>Fract r s = Fract r0 (2^(a+1)*s0)\<close> 
    by linarith
  have \<open>s \<noteq> 0\<close> 
    by (smt \<open>Fract r s = Fract r0 (2 ^ (a + 1) * s0)\<close> \<open>odd r0\<close> \<open>odd s0\<close> dvd_0_right minus_rat mult_eq_0_iff mult_minus_left positive_rat power_eq_0_iff)
    have  \<open>2^(a+1)*s0 \<noteq> 0\<close> 
    using \<open>odd s0\<close> by auto
  from \<open>Fract r s = Fract r0 (2^(a+1)*s0)\<close> \<open>s \<noteq> 0\<close> \<open>2^(a+1)*s0 \<noteq> 0\<close> \<open>coprime r s\<close>
    obtain d :: int where \<open>r*d = r0\<close> and \<open>s*d = 2^(a+1)*s0\<close> 
      using FractPropor by blast
    have \<open>odd d\<close> 
      using \<open>odd r0\<close> \<open>r * d = r0\<close> even_mult_iff by blast
    have \<open>odd r\<close> 
      using \<open>odd r0\<close> \<open>r * d = r0\<close> even_mult_iff by blast
    from \<open>odd d\<close>  \<open>s*d = 2^(a+1)*s0\<close> have \<open>coprime d (2^(a+1))\<close> 
      using coprime_power_right_iff coprime_right_2_iff_odd by blast
    from  \<open>s*d = 2^(a+1)*s0\<close> have \<open>d dvd (2^(a+1)*s0)\<close> 
      by (metis dvd_triv_right)
    from  \<open>coprime d (2^(a+1))\<close> \<open>d dvd (2^(a+1)*s0)\<close> have \<open>d dvd s0\<close> 
      using coprime_dvd_mult_right_iff by blast
    then  obtain e :: int where \<open>s0 = d*e\<close> 
      by blast
    have \<open>odd e\<close> 
      using \<open>odd s0\<close> \<open>s0 = d * e\<close> even_mult_iff by blast
    have \<open>s = 2^(a+1)*e\<close> 
      using \<open>odd d\<close> \<open>s * d = 2 ^ (a+1) * s0\<close> \<open>s0 = d * e\<close> by auto
  show ?thesis 
    using \<open>odd e\<close> \<open>odd r\<close> \<open>s = 2 ^ (a + 1) * e\<close> by blast
qed


lemma HarmonicNumbersParityNumeratorDenominator:
  fixes n :: nat and r s :: int
  assumes \<open>n \<ge> 2\<close> and \<open> (\<Sum> k = 1..n. (Fract 1 k) ) = Fract r s \<close> and \<open>coprime r s\<close>
  shows \<open>odd r \<and> even s\<close>
proof-
  from \<open>n \<ge> 2\<close> obtain a b :: nat where \<open>n = 2^(a+1) + b\<close> and \<open>b < 2^(a+1)\<close>
    using WeakEuclidPow2 by blast
  have \<open>odd r \<and> (\<exists> ss ::int. s = 2^(a+1)*ss \<and> odd ss)\<close> 
    using HarmonicNumbersParityNumeratorDenominator2 \<open>b < 2 ^ (a + 1)\<close> \<open>n = 2 ^ (a + 1) + b\<close> assms(2) assms(3) by blast
  from  \<open>odd r \<and> (\<exists> ss ::int. s = 2^(a+1)*ss \<and> odd ss)\<close> have \<open>odd r\<close> by blast
  from  \<open>odd r \<and> (\<exists> ss ::int. s = 2^(a+1)*ss \<and> odd ss)\<close> have  \<open>\<exists> ss ::int. s = 2^(a+1)*ss \<and> odd ss\<close>
    by blast
  then obtain ss :: int where \<open>s = 2^(a+1)*ss\<close> and \<open>odd ss\<close> 
    by blast
  from  \<open>s = 2^(a+1)*ss\<close> have \<open>even s\<close> 
    by simp
  show ?thesis 
    by (simp add: \<open>even s\<close> \<open>odd r\<close>)
qed


subsection  {* Auxiliary Results I *}

lemma HarmNumAreRat1:
  fixes  n :: nat
  shows \<open>(\<Sum> k = 1..n+1. (Fract 1 (of_nat k)) ) \<in> \<rat>\<close>
proof (induction n)
  case 0
   have \<open> (\<Sum> k = 1..0+1. (Fract 1 k) ) = (\<Sum> k = 1..1. (Fract 1 k) ) \<close> 
     by simp
   then have  \<open> (\<Sum> k = 1..0+1. (Fract 1 k) ) =  (Fract 1 1) \<close> 
     by simp
   then have  \<open> (\<Sum> k = 1..0+1. (Fract 1 k) ) \<in> \<rat> \<close> 
     using One_rat_def by auto
  then show ?case 
    by simp
next
  case (Suc n)
  then have \<open>(\<Sum> k = 1..n+1. (Fract 1 (of_nat k)) ) \<in> \<rat>\<close> 
    by blast
  have \<open> Fract 1 (of_nat ((Suc n) + 1)) \<in> \<rat>\<close> 
    by (simp add: Fract_of_int_quotient) 
  then have \<open>(\<Sum> k = 1..n+1. (Fract 1 (of_nat k)) ) + Fract 1 (of_nat ((Suc n) + 1)) \<in> \<rat>\<close>
    using Rats_add Suc.IH by blast
  have \<open> (\<Sum> k = 1..(Suc n)+1. (Fract 1 (of_nat k)) ) = (\<Sum> k = 1..n+1. (Fract 1 (of_nat k)) ) + Fract 1 (of_nat ((Suc n) + 1)) \<close>
    by simp
    then show ?case 
      using \<open>(\<Sum>k = 1..n + 1. Fract 1 (int k)) + Fract 1 (int (Suc n + 1)) \<in> \<rat>\<close> by auto
qed

lemma HarmNumAreRat:
  fixes  n :: nat
  assumes \<open>n \<ge> 1\<close>
  shows \<open>(\<Sum> k = 1..n. (Fract 1 k) ) \<in> \<rat>\<close>
  by (metis HarmNumAreRat1 One_nat_def Suc_le_D add.commute assms plus_1_eq_Suc)

lemma FractOddNumEvenDen:
  fixes r s :: int
  assumes \<open>odd r\<close> and  \<open>even s\<close> and \<open>s \<noteq> 0\<close>
  shows  \<open> Fract r s \<notin> \<int> \<close>
proof (rule classical)
  assume \<open>\<not> (Fract r s \<notin> \<int>)\<close>
  then have \<open>Fract r s \<in> \<int>\<close> 
    by blast 
  then obtain t :: int where \<open>r = t*s\<close> 
    by (metis Ints_cases \<open>\<not> Fract r s \<notin> \<int>\<close> assms(3) eq_rat(1) mult.commute mult.right_neutral of_int_rat semiring_normalization_rules(10))
  from  \<open>r = t*s\<close> \<open>even s\<close> have \<open>even r\<close> 
    by simp
  from  \<open>even r\<close> \<open>odd r\<close> have False by simp
  then show ?thesis by simp
qed

subsection {* Main Result *}

theorem HarmonicNumbersAreNotIntegers:
  fixes n :: nat
  assumes \<open>n \<ge> 2\<close>
  shows \<open> (\<Sum> k = 1..n. (Fract 1 (of_nat k)) ) \<notin> \<int> \<close>
proof (rule classical) 
  from  \<open>n \<ge> 2\<close> have \<open> (\<Sum> k = 1..n. (Fract 1 (of_nat k)) ) \<in> \<rat> \<close>  
    using HarmNumAreRat by auto
  then obtain r s :: int where \<open> (\<Sum> k = 1..n. (Fract 1 (of_nat k)) ) = (Fract r s) \<close> and \<open>coprime r s\<close> 
    using Rat_cases by blast  
  assume \<open> \<not>( (\<Sum> k = 1..n. (Fract 1 k) ) \<notin> \<int>) \<close>
  then have \<open> (\<Sum> k = 1..n. (Fract 1 k) ) \<in> \<int>  \<close>
    by blast
  then have \<open> Fract r s \<in> \<int> \<close>
    using \<open>(\<Sum>k = 1..n. Fract 1 (int k)) = Fract r s\<close> by auto
  from  \<open>n \<ge> 2\<close> \<open> (\<Sum> k = 1..n. (Fract 1 (of_nat k)) ) = (Fract r s) \<close> \<open>coprime r s\<close>
  have \<open>odd r\<close> 
    using HarmonicNumbersParityNumeratorDenominator by blast
  from  \<open>n \<ge> 2\<close> \<open> (\<Sum> k = 1..n. (Fract 1 (of_nat k)) ) = (Fract r s) \<close> \<open>coprime r s\<close>
  have \<open>even s\<close> 
    using HarmonicNumbersParityNumeratorDenominator by blast
  have \<open>s \<noteq> 0\<close> 
    by (metis HarmonicNumbersParityNumeratorDenominator \<open>(\<Sum>k = 1..n. Fract 1 (int k)) = Fract r s\<close> \<open>coprime r s\<close> assms coprime_commute eq_rat(3) rat_number_collapse(6))
    from  \<open>odd r\<close>  \<open>even s\<close> \<open>s \<noteq> 0\<close>  \<open> Fract r s \<in> \<int> \<close> have False
    using FractOddNumEvenDen by blast
  then show ?thesis 
    by blast 
qed


end


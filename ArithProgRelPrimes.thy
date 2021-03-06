(*

Problem (ARITHMETIC PROGRESSIONS): 9/13/2002: For which integers n>1 does the set of positive
 integers less than and relatively prime to n constitute an arithmetic progression?
                                                                              
Link: https://www.ocf.berkeley.edu/~wwu/riddles/putnam.shtml


Solution by: Jose Manuel Rodriguez Caballero

text{* Solution of the Problem *}
theorem SolutionOfTheProblem:
  \<open>(n::nat) > 1 \<Longrightarrow>
 prime n \<or> (\<exists> k. n = 2^k) \<or> n = 6
 \<longleftrightarrow>  
(\<exists> a b m. m \<noteq> 0 \<and> {x | x :: nat. x < n \<and> coprime x n} = {a+j*b| j::nat. j < m})\<close>


Date: November 3, 2018

*)

theory ArithProgRelPrimes

imports
  Complex_Main PowOfTwo  "HOL-Number_Theory.Number_Theory"

begin

lemma preACasePrimeA1:
  \<open>(n::nat) > 1 \<Longrightarrow>  coprime x n \<Longrightarrow> x \<noteq> 0\<close>
  by (meson coprime_0_left_iff less_numeral_extra(1) nat_dvd_not_less)

lemma preACasePrimeA2:
  \<open>(n::nat) > 1 \<Longrightarrow> prime n \<Longrightarrow>  x < n \<Longrightarrow> x \<noteq> 0 \<Longrightarrow>  coprime x n\<close>
  by (simp add: coprime_commute nat_dvd_not_less prime_imp_coprime_nat)

lemma preACasePrimeA:
  \<open>(n::nat) > 1 \<Longrightarrow> prime n \<Longrightarrow> {x | x :: nat. x < n \<and> coprime x n} = {x | x :: nat. x \<noteq> 0 \<and> x < n}\<close>
  using preACasePrimeA1 preACasePrimeA2 by auto

lemma preBCasePrimeA:
  \<open>{1+j| j::nat. j < (m::nat)} =  {x | x :: nat. x \<noteq> 0 \<and> x < m+1}\<close>
proof(induction m)
  case 0
  thus ?case 
    by auto
next
  case (Suc m)
  thus ?case
    by (metis Suc_eq_plus1   less_Suc_eq_0_disj  nat.discI  plus_1_eq_Suc)
qed

lemma CasePrimeA:
  \<open>(n::nat) > 1 \<Longrightarrow>
 prime n 
 \<Longrightarrow>
 (\<exists> m.  m \<noteq> 0 \<and> {x | x :: nat. x < n \<and> coprime x n} = {1+j| j::nat. j < m})\<close>
proof-
  assume \<open>n > 1\<close>
  assume \<open>prime n\<close>
  have \<open>{x | x :: nat. x < n \<and> coprime x n} =  {x | x :: nat. x \<noteq> 0 \<and> x < n}\<close> 
    using \<open>1 < n\<close> \<open>prime n\<close> preACasePrimeA by auto
  obtain m where \<open>m+1 = n\<close> 
    using \<open>1 < n\<close> less_imp_add_positive linordered_field_class.sign_simps(2) by blast
  have \<open>{1+j| j::nat. j < (m::nat)} =  {x | x :: nat. x \<noteq> 0 \<and> x < m+1}\<close> 
    by (metis Suc_eq_plus1   \<open>m + 1 = n\<close> gr0_implies_Suc le_simps(3)   less_nat_zero_code   linorder_not_less nat.simps(3) nat_neq_iff  plus_1_eq_Suc )
  hence  \<open>{x | x :: nat. x < n \<and> coprime x n} = {1+j| j::nat. j < (m::nat)}\<close>
    using \<open>{x | x :: nat. x < n \<and> coprime x n} =  {x | x :: nat. x \<noteq> 0 \<and> x < n}\<close>  \<open>m+1 = n\<close> 
    by auto
  from \<open>n > 1\<close> have \<open>m \<noteq> 0\<close> 
    using \<open>m + 1 = n\<close> by linarith
  have \<open>{x | x :: nat. x < n \<and> coprime x n} = {1+j| j::nat. j < m}\<close> 
    using Suc_eq_plus1 \<open>1 < n\<close> \<open>{x |x. x < n \<and> coprime x n} = {1 + j |j. j < m}\<close> by auto
  hence \<open>(\<exists> m.  m \<noteq> 0 \<and> {x | x :: nat. x < n \<and> coprime x n} = {1+j| j::nat. j < m})\<close>
    using \<open>m \<noteq> 0\<close> by blast
  thus ?thesis by blast
qed

lemma preDSFSDf:
  \<open>(n::nat) > 1
 \<Longrightarrow>
 m \<noteq> 0
 \<Longrightarrow> 
{x | x :: nat. x < n \<and> coprime x n} = {1+j| j::nat. j < m}
\<Longrightarrow>
 x < n 
\<Longrightarrow> 
 x \<noteq> 0
 \<Longrightarrow> coprime x n\<close>
proof-
  assume \<open>n > 1\<close>
  assume \<open>m \<noteq> 0\<close>
  assume \<open>{x | x :: nat. x < n \<and> coprime x n} = {1+j| j::nat. j < m}\<close>
  assume \<open>x < n\<close>
  assume \<open>x \<noteq> 0\<close>
  have \<open>{1+j| j::nat. j < m} = {x | x :: nat. x < m+1 \<and> x \<noteq> 0}\<close> 
    by (metis (full_types) Suc_eq_plus1  add_mono1 less_Suc_eq_0_disj  nat.simps(3) plus_1_eq_Suc )
  hence \<open>{x | x :: nat. x < n \<and> coprime x n} = {x | x :: nat. x < m+1 \<and> x \<noteq> 0}\<close>
    using \<open>{x |x. x < n \<and> coprime x n} = {1 + j |j. j < m}\<close> by auto
  have \<open>coprime (n-1) n\<close> 
    using \<open>1 < n\<close> coprime_diff_one_left_nat by auto
  have \<open>n-1 < n\<close> 
    using \<open>1 < n\<close> by auto
  have \<open>n-1 \<in> {x |x. x < n \<and> coprime x n}\<close> 
    using \<open>coprime (n - 1) n\<close> \<open>n - 1 < n\<close> by blast
  have \<open>n-1 \<le> m\<close> 
    by (metis (no_types, lifting) CollectD Suc_eq_plus1 Suc_less_eq2 \<open>n - 1 \<in> {x |x. x < n \<and> coprime x n}\<close> \<open>{x |x. x < n \<and> coprime x n} = {x |x. x < m + 1 \<and> x \<noteq> 0}\<close>   leD  le_less_linear not_less_eq_eq )
  have \<open>m \<in>  {x | x :: nat. x < m+1 \<and> x \<noteq> 0}\<close> 
    using \<open>m \<noteq> 0\<close> by auto
  have \<open>m \<in> {x |x. x < n \<and> coprime x n} \<close> 
    using \<open>m \<in> {x |x. x < m + 1 \<and> x \<noteq> 0}\<close> \<open>{x |x. x < n \<and> coprime x n} = {x |x. x < m + 1 \<and> x \<noteq> 0}\<close> by blast
  have \<open>m < n\<close> 
    using \<open>m \<in> {x |x. x < n \<and> coprime x n}\<close> by blast
  have \<open>m+1 = n\<close> 
    using \<open>m < n\<close> \<open>n - 1 \<le> m\<close> by linarith
  have \<open>x \<in>  {x | x :: nat. x < m+1 \<and> x \<noteq> 0}\<close> 
    using \<open>m + 1 = n\<close> \<open>x < n\<close> \<open>x \<noteq> 0\<close> by blast
  hence \<open>x \<in> {x |x. x < n \<and> coprime x n}\<close> 
    using \<open>{x |x. x < n \<and> coprime x n} = {x |x. x < m + 1 \<and> x \<noteq> 0}\<close> by blast
  thus ?thesis 
    by blast
qed

lemma DSFSDf:
  \<open>(n::nat) > 1
 \<Longrightarrow>
\<exists>  m. m \<noteq> 0 \<and> {x | x :: nat. x < n \<and> coprime x n} = {1+j| j::nat. j < m}
\<Longrightarrow>
\<forall> x::nat. x < n \<and> x \<noteq> 0 \<longrightarrow> coprime x n\<close>
  using preDSFSDf by blast

lemma DSFSDF:
  \<open>(n::nat) > 1
 \<Longrightarrow>
\<forall> x::nat. x < n \<and> x \<noteq> 0 \<longrightarrow> coprime x n
\<Longrightarrow>
prime n\<close>
  using coprime_commute nat_neq_iff prime_nat_iff'' by auto

lemma CasePrimeB:
  \<open>(n::nat) > 1
 \<Longrightarrow>
 (\<exists>  m. m \<noteq> 0 \<and> {x | x :: nat. x < n \<and> coprime x n} = {1+j| j::nat. j < m})
\<Longrightarrow> 
 prime n\<close>
  using DSFSDf DSFSDF 
  by (metis (no_types, lifting) )


lemma preCasePrime:
  \<open>(n::nat) > 1 \<Longrightarrow>
 prime n 
 \<longleftrightarrow>
 (\<exists>  m.   m \<noteq> 0 \<and> {x | x :: nat. x < n \<and> coprime x n} = {1+j| j::nat. j < m})\<close>
  using CasePrimeA CasePrimeB by blast

lemma preCasePrimeT1:
  \<open>(n::nat) > 1 \<Longrightarrow>
 prime n 
 \<longleftrightarrow>
 (\<exists>  m.   m \<noteq> 0 \<and> {x | x :: nat. x < n \<and> coprime x n} = {1+j*1| j::nat. j < m})\<close>
  using preCasePrime by auto

lemma CasePrime:
  \<open>(n::nat) > 1 \<Longrightarrow>
 prime n 
 \<longleftrightarrow>
 (\<exists>  b m. b = 1 \<and>  m \<noteq> 0 \<and> {x | x :: nat. x < n \<and> coprime x n} = {1+j*b| j::nat. j < m})\<close>
  using preCasePrimeT1 by blast


lemma preCasePow2A2X:
  fixes x :: nat
  assumes \<open>x < 2^(Suc k)\<close> and \<open>coprime x (2^(Suc k))\<close>
  shows \<open>\<exists> j. x = 1+j*2 \<and> j < 2^k\<close>
proof-
  from \<open>coprime x (2^(Suc k))\<close>
  have \<open>odd x\<close> 
    by simp
  then obtain j where \<open>x = 1+j*2\<close> 
    by (metis add.commute add.left_commute left_add_twice mult_2_right oddE)
  from  \<open>x < 2^(Suc k)\<close> \<open>x = 1+j*2\<close> have \<open>j < 2^k\<close> 
    by auto 
  show ?thesis 
    using \<open>j < 2 ^ k\<close> \<open>x = 1 + j * 2\<close> by blast
qed


lemma preCasePow2A2YU:
  fixes x :: nat
  assumes  \<open> x = 1+j*2\<close> and \<open>j < 2^k\<close>
  shows  \<open>x < 2^(Suc k)\<close>
  using assms(1) assms(2) by auto

lemma preCasePow2A2V:
  fixes x :: nat
  assumes  \<open> x = 1+j*2\<close> and \<open>j < 2^k\<close>
  shows  \<open>coprime x (2^(Suc k))\<close>
  by (simp add: assms(1))

lemma preCasePow2A2Y:
  fixes x :: nat
  assumes  \<open> x = 1+j*2\<close> and \<open>j < 2^k\<close>
  shows  \<open>x < 2^(Suc k) \<and> coprime x (2^(Suc k))\<close>
  using preCasePow2A2YU preCasePow2A2V 
  using assms(1) assms(2) by auto

lemma preCasePow2A2:
  \<open>{x | x :: nat. x < 2^(Suc k) \<and> coprime x (2^(Suc k))} = {1+j*2| j::nat. j < 2^k}\<close>
  using preCasePow2A2X preCasePow2A2Y by blast

lemma preCasePow2A1:
  \<open>n = 2^(Suc k)
 \<Longrightarrow>
 {x | x :: nat. x < n \<and> coprime x n} = {1+j*2| j::nat. j < 2^k}\<close>
  using preCasePow2A2 by blast

lemma preCasePow2A:
  \<open>(n::nat) > 1
 \<Longrightarrow>
  n = 2^k
 \<Longrightarrow>
 \<exists>  m. m \<noteq> 0 \<and> {x | x :: nat. x < n \<and> coprime x n} = {1+j*2| j::nat. j < m}\<close>
proof-
  assume \<open>n > 1\<close>
  assume \<open>n = 2^k\<close>
  have \<open>k \<noteq> 0\<close> 
    by (metis \<open>1 < n\<close> \<open>n = 2 ^ k\<close> nat_less_le power.simps(1))
  obtain t where \<open>Suc t = k\<close> 
    by (metis \<open>k \<noteq> 0\<close> fib.cases)
  have \<open>n = 2^(Suc t)\<close> 
    by (simp add: \<open>Suc t = k\<close> \<open>n = 2 ^ k\<close>)
  have \<open>{x | x :: nat. x < n \<and> coprime x n} = {1+j*2| j::nat. j < 2^t}\<close>
    using \<open>Suc t = k\<close> \<open>n = 2 ^ k\<close> preCasePow2A1 by force
  have \<open>(2::nat)^(t::nat) \<noteq> 0\<close> 
    by simp
  obtain m where \<open>m = (2::nat)^t\<close> by blast
  have \<open>m \<noteq> 0\<close> 
    using \<open>m = 2 ^ t\<close> by auto
  have \<open>{x | x :: nat. x < n \<and> coprime x n} = {1+j*2| j::nat. j < m}\<close>
    using \<open>m = 2 ^ t\<close> \<open>{x |x. x < n \<and> coprime x n} = {1 + j * 2 |j. j < 2 ^ t}\<close> by auto
  from  \<open>m \<noteq> 0\<close>  \<open>{x | x :: nat. x < n \<and> coprime x n} = {1+j*2| j::nat. j < m}\<close>
  show ?thesis by blast
qed
lemma preCasePow2B5:
  \<open>(n::nat) > 1
\<Longrightarrow>
\<forall> x :: nat. x dvd n \<and> odd x \<longrightarrow> x = 1
\<Longrightarrow>
\<exists> k. n = (2::nat)^k\<close>
  using OddDivPow2 by auto

lemma preCasePow2B4:
  \<open>(n::nat) > 1
\<Longrightarrow>
\<forall> x :: nat. x < n \<longrightarrow> (coprime x n \<longleftrightarrow> odd x)
\<Longrightarrow>
\<forall> x :: nat. x dvd n \<and> odd x \<longrightarrow> x = 1\<close>
  by (metis Suc_1 comm_monoid_add_class.add_0 coprime_Suc_right_nat coprime_absorb_left dvd_imp_le even_Suc even_Suc_Suc_iff gr0_conv_Suc le_eq_less_or_eq lessI less_iff_Suc_add less_imp_add_positive nat_dvd_1_iff_1 plus_1_eq_Suc zero_less_Suc)

lemma preCasePow2B3:
  \<open>(n::nat) > 1
\<Longrightarrow>
\<forall> x :: nat. x < n \<longrightarrow> (coprime x n \<longleftrightarrow> odd x)
\<Longrightarrow>
\<exists> k. n = (2::nat)^k\<close>
  using preCasePow2B5 preCasePow2B4 by blast

lemma preCasePow2B2A:
  \<open>(n::nat) > 1
 \<Longrightarrow>
  m \<noteq> 0 
\<Longrightarrow>
 {x | x :: nat. x < n \<and> coprime x n} = {1+j*2| j::nat. j < m}
\<Longrightarrow>
 x < n 
\<Longrightarrow> coprime x n 
\<Longrightarrow> odd x\<close>
proof-
  assume \<open>n > 1\<close>
  assume \<open>m \<noteq> 0\<close>
  assume \<open>{x | x :: nat. x < n \<and> coprime x n} = {1+j*2| j::nat. j < m}\<close>
  assume \<open>x < n\<close>
  assume \<open>coprime x n\<close>
  have \<open>x \<in> {x | x :: nat. x < n \<and> coprime x n}\<close> 
    by (simp add: \<open>coprime x n\<close> \<open>x < n\<close>)
  hence \<open>x \<in> {1+j*2| j::nat. j < m}\<close> 
    using \<open>{x |x. x < n \<and> coprime x n} = {1 + j * 2 |j. j < m}\<close> by blast
  then obtain j where \<open>x = 1+j*2\<close> 
    by blast
  thus ?thesis
    by simp
qed

lemma SDFsfrwrGen:
  \<open>(n::nat) > 1
 \<Longrightarrow>
  m \<noteq> 0 
\<Longrightarrow>
 {x | x :: nat. x < n \<and> coprime x n} = {1+j*(b::nat)| j::nat. j < m}
\<Longrightarrow>
b \<noteq> 0
\<Longrightarrow>
n = 2+(m-1)*b\<close>
proof-
  assume \<open>n > 1\<close>
  assume \<open>m \<noteq> 0\<close>
  assume \<open>b \<noteq> 0\<close>
  assume \<open>{x | x :: nat. x < n \<and> coprime x n} = {1+j*b| j::nat. j < m}\<close>
  have \<open>n-1 \<in> {x | x :: nat. x < n \<and> coprime x n}\<close> 
    using \<open>1 < n\<close> coprime_diff_one_left_nat by auto
  have \<open>n-1 \<in> {1+j*b| j::nat. j < m}\<close> 
    using \<open>n - 1 \<in> {x |x. x < n \<and> coprime x n}\<close> \<open>{x |x. x < n \<and> coprime x n} = {1 + j * b |j. j < m}\<close> by blast
  then obtain i::nat where \<open>n-1 = 1+i*b\<close> and \<open>i < m\<close> 
    by blast
  have \<open>i \<le> m-1\<close> 
    using \<open>i < m\<close> by linarith
  have \<open>1 + (m-1)*b \<in> {1+j*b| j::nat. j < m}\<close> 
    using \<open>m \<noteq> 0\<close> by auto
  hence \<open>1 + (m-1)*b \<in> {x | x :: nat. x < n \<and> coprime x n}\<close> 
    using \<open>{x |x. x < n \<and> coprime x n} = {1 + j * b |j. j < m}\<close> by blast
  hence \<open>1 + (m-1)*b < n\<close> 
    by blast
  hence \<open>1 + (m-1)*b \<le> n-1\<close> 
    by linarith
  hence \<open>1 + (m-1)*b \<le> 1+i*b\<close> 
    using \<open>n - 1 = 1 + i * b\<close> by linarith
  hence \<open>(m-1)*b \<le> i*b\<close> 
    by linarith
  hence \<open>m-1 \<le> i\<close> using \<open>b \<noteq> 0\<close> 
    by auto
  hence \<open>m-1 = i\<close> 
    using \<open>i \<le> m - 1\<close> le_antisym by blast
  thus ?thesis 
    using \<open>m \<noteq> 0\<close> \<open>n - 1 = 1 + i * b\<close> by auto
qed



lemma SDFsfrwr:
  \<open>(n::nat) > 1
 \<Longrightarrow>
  m \<noteq> 0 
\<Longrightarrow>
 {x | x :: nat. x < n \<and> coprime x n} = {1+j*(2::nat)| j::nat. j < m}
\<Longrightarrow>
n = 2*m\<close>
proof-
  assume \<open>n > 1\<close>
  assume \<open>m \<noteq> 0\<close>
  assume \<open>{x | x :: nat. x < n \<and> coprime x n} = {1+j*(2::nat)| j::nat. j < m}\<close>
  have  \<open>(2::nat) \<noteq> 0\<close> by auto
  from  \<open>n > 1\<close>  \<open>m \<noteq> 0\<close> \<open>{x | x :: nat. x < n \<and> coprime x n} = {1+j*(2::nat)| j::nat. j < m}\<close> \<open>(2::nat) \<noteq> 0\<close>
  have \<open>n = 2+(m-1)*2\<close> 
    using SDFsfrwrGen
    by blast
  thus  ?thesis 
    by (simp add: \<open>m \<noteq> 0\<close> \<open>n = 2 + (m - 1) * 2\<close> mult.commute mult_eq_if)
qed

lemma preCasePow2B2B:
  \<open>(n::nat) > 1
 \<Longrightarrow>
  m \<noteq> 0 
\<Longrightarrow>
 {x | x :: nat. x < n \<and> coprime x n} = {1+j*2| j::nat. j < m}
\<Longrightarrow>
 x < n 
\<Longrightarrow>  odd x 
\<Longrightarrow>  coprime x n\<close>
proof-
  assume \<open>n > 1\<close>
  assume \<open>m \<noteq> 0\<close>
  assume \<open>{x | x :: nat. x < n \<and> coprime x n} = {1+j*2| j::nat. j < m}\<close>
  assume \<open>x < n\<close>
  assume \<open>odd x\<close>
  obtain j::nat where \<open>x = 1+j*2\<close> 
    by (metis \<open>odd x\<close> add.commute mult_2_right odd_two_times_div_two_succ one_add_one semiring_normalization_rules(16)) 
  have \<open>j < (n-1)/2\<close> 
    using \<open>x < n\<close> \<open>x = 1 + j * 2\<close> by linarith
  from \<open>n > 1\<close> \<open>m \<noteq> 0\<close>  \<open>{x | x :: nat. x < n \<and> coprime x n} = {1+j*2| j::nat. j < m}\<close>
  have \<open>n = 2*m\<close> using SDFsfrwr by blast
  hence \<open>j < m\<close> 
    using \<open>x < n\<close> \<open>x = 1 + j * 2\<close> by linarith
  hence \<open>x \<in> {1+j*2| j::nat. j < m}\<close> 
    using \<open>x = 1 + j * 2\<close> by blast
  hence \<open>x \<in> {x | x :: nat. x < n \<and> coprime x n}\<close> 
    using \<open>{x |x. x < n \<and> coprime x n} = {1 + j * 2 |j. j < m}\<close> by blast
  thus ?thesis 
    by blast
qed



lemma preCasePow2B2:
  \<open>(n::nat) > 1
 \<Longrightarrow>
  m \<noteq> 0 
\<Longrightarrow>
 {x | x :: nat. x < n \<and> coprime x n} = {1+j*2| j::nat. j < m}
\<Longrightarrow>
\<forall> x :: nat. x < n \<longrightarrow> (coprime x n \<longleftrightarrow> odd x)\<close>
  using preCasePow2B2A preCasePow2B2B by blast

lemma preCasePow2B1:
  \<open>(n::nat) > 1
 \<Longrightarrow>
  m \<noteq> 0 
\<Longrightarrow>
 {x | x :: nat. x < n \<and> coprime x n} = {1+j*2| j::nat. j < m}
\<Longrightarrow>
\<exists> k. n = 2^k\<close>
  using preCasePow2B3 preCasePow2B2 
  by blast

lemma preCasePow2B:
  \<open>(n::nat) > 1
 \<Longrightarrow>
 \<exists>  m. m \<noteq> 0 \<and> {x | x :: nat. x < n \<and> coprime x n} = {1+j*2| j::nat. j < m}
\<Longrightarrow>
\<exists> k. n = 2^k\<close>
  using preCasePow2B1 by blast

lemma preCasePow2:
  \<open>(n::nat) > 1 \<Longrightarrow>
 (\<exists> k. n = 2^k)
 \<longleftrightarrow>
( \<exists>  m. m \<noteq> 0 \<and> {x | x :: nat. x < n \<and> coprime x n} = {1+j*2| j::nat. j < m})\<close>
  using preCasePow2A preCasePow2B by blast

lemma CasePow2:
  \<open>(n::nat) > 1 \<Longrightarrow>
 (\<exists> k. n = 2^k)
 \<longleftrightarrow>
 (\<exists> b  m. b = 2 \<and> m \<noteq> 0 \<and> {x | x :: nat. x < n \<and> coprime x n} = {1+j*b| j::nat. j < m})\<close>
  using preCasePow2 by blast

lemma preCaseN6AAA1P:
  \<open>{1, 5} \<subseteq> {x | x :: nat. x < 6 \<and> coprime x 6}\<close>
  by (metis (mono_tags, lifting) coprime_1_left coprime_Suc_right_nat insert_iff lessI less_linear mem_Collect_eq   not_numeral_less_one   numeral_nat(2)   semiring_norm(28)  singleton_iff subsetI )

lemma preCaseN6AAA1QX:
  fixes x :: nat
  assumes \<open>x < 6\<close> and \<open>coprime x 6\<close>
  shows \<open>x = 1 \<or> x = 5\<close>
proof-
  from \<open>x < 6\<close> 
  have \<open>x = 0 \<or> x = 1 \<or> x = 2 \<or> x = 3 \<or> x = 4 \<or> x = 5\<close>
    by auto
  have  \<open>\<not> (coprime (0::nat) (6::nat))\<close>
    by auto
  have  \<open>\<not> (coprime (2::nat) (6::nat))\<close>
    by auto
  have  \<open>gcd (3::nat) (6::nat) = (3::nat)\<close>
    by auto
  hence  \<open>\<not> (coprime (3::nat) (6::nat))\<close>
    by presburger
  have  \<open>gcd (4::nat) (6::nat) = (2::nat)\<close>
    by (metis (no_types, lifting) add_numeral_left gcd_add1 gcd_add2 gcd_idem_nat numeral_Bit0 numeral_One one_plus_numeral semiring_norm(3))
  hence  \<open>\<not> (coprime (4::nat) (6::nat))\<close>
    by auto
  show ?thesis 
    using \<open>\<not> coprime 0 6\<close> \<open>\<not> coprime 2 6\<close> \<open>\<not> coprime 3 6\<close> \<open>\<not> coprime 4 6\<close> \<open>x = 0 \<or> x = 1 \<or> x = 2 \<or> x = 3 \<or> x = 4 \<or> x = 5\<close> assms(2) by blast
qed


lemma preCaseN6AAA1Q:
  \<open>{x | x :: nat. x < 6 \<and> coprime x 6} \<subseteq> {1, 5}\<close>
  using preCaseN6AAA1QX by blast

lemma preCaseN6AAA1:
  \<open>{x | x :: nat. x < 6 \<and> coprime x 6} = {1, 5}\<close>
  using preCaseN6AAA1P preCaseN6AAA1Q by blast

lemma preCaseN6AAA2:
  \<open>{1+j*4| j::nat. j < 2} = {1, 5}\<close>
  by force

lemma preCaseN6AAA:
  \<open>{x | x :: nat. x < 6 \<and> coprime x 6} = {1+j*4| j::nat. j < 2}\<close>
  using preCaseN6AAA1 preCaseN6AAA2 by blast

lemma preCaseN6AA:
  \<open> (2::nat) \<noteq> (0::nat) \<and> {x | x :: nat. x < 6 \<and> coprime x 6} = {1+j*4| j::nat. j < 2}\<close>
  using preCaseN6AAA by auto

lemma preCaseN6A:
  \<open>\<exists> m.  m \<noteq> 0 \<and> {x | x :: nat. x < 6 \<and> coprime x 6} = {1+j*4| j::nat. j < m}\<close>
  using preCaseN6AA by blast


lemma AXXXpreCaseN6X2:
  \<open>{x | x :: nat. x < 2 \<and> coprime x 2} = {1}\<close>
proof-
  have \<open>{x | x :: nat. x < 2 \<and> coprime x 2} = {x | x :: nat. x < 2 \<and> x \<noteq> 0}\<close>
    using less_2_cases by fastforce
  have \<open>{x | x :: nat. x < 2 \<and> x \<noteq> 0} = {1}\<close> by fastforce
  thus ?thesis using  \<open>{x | x :: nat. x < 2 \<and> coprime x 2} = {x | x :: nat. x < 2 \<and> x \<noteq> 0}\<close>
    by auto
qed

lemma BXXXpreCaseN6X2:
  \<open>{1+j*4| j::nat. j < 1} = {1}\<close>
  by fastforce

lemma XXXpreCaseN6X2:
  \<open>{x | x :: nat. x < 2 \<and> coprime x 2} = {1+j*4| j::nat. j < 1}\<close>
  using AXXXpreCaseN6X2 BXXXpreCaseN6X2 by blast

lemma XXpreCaseN6X2:
  \<open> (1::nat) \<noteq> 0 \<and> {x | x :: nat. x < 2 \<and> coprime x 2} = {1+j*4| j::nat. j < 1}\<close>
proof-
  have \<open>{x | x :: nat. x < 2 \<and> coprime x 2} = {1+j*4| j::nat. j < 1}\<close>
    using XXXpreCaseN6X2 by blast
  have \<open>(1::nat) \<noteq> 0\<close> by auto
  thus ?thesis using  \<open>{x | x :: nat. x < 2 \<and> coprime x 2} = {1+j*4| j::nat. j < 1}\<close>
    by blast
qed

lemma XpreCaseN6X2:
  \<open>\<exists> m.  m \<noteq> 0 \<and> {x | x :: nat. x < 2 \<and> coprime x 2} = {1+j*4| j::nat. j < m}\<close>
  using XXpreCaseN6X2 by blast

lemma preCaseN6X2:
  \<open>n = 2 \<Longrightarrow> \<exists> m.  m \<noteq> 0 \<and> {x | x :: nat. x < n \<and> coprime x n} = {1+j*4| j::nat. j < m}\<close>
  using XpreCaseN6X2 by blast


lemma preCaseN6Aand2:
  \<open>n = 2 \<or> n = 6 \<Longrightarrow> \<exists> m.  m \<noteq> 0 \<and> {x | x :: nat. x < n \<and> coprime x n} = {1+j*4| j::nat. j < m}\<close>
  using preCaseN6X2 preCaseN6A by blast

lemma XpreCaseN6B:
  \<open>(n::nat) > 1
\<Longrightarrow>
 m \<noteq> 0 
\<Longrightarrow>
 {x | x :: nat. x < n \<and> coprime x n} = {1+j*4| j::nat. j < m}
\<Longrightarrow>
 n = 2 \<or> n = 6\<close>
proof(rule classical)
  assume \<open>n > 1\<close>
  assume \<open>m \<noteq> 0\<close>
  assume \<open>{x | x :: nat. x < n \<and> coprime x n} = {1+j*4| j::nat. j < m}\<close>
  assume \<open>\<not> ( n = 2 \<or> n = 6 )\<close>
  have  \<open>(4::nat) \<noteq> 0\<close> by auto
  from \<open>n > 1\<close>  \<open>m \<noteq> 0\<close>  \<open>{x | x :: nat. x < n \<and> coprime x n} = {1+j*4| j::nat. j < m}\<close> \<open>(4::nat) \<noteq> 0\<close>
  have \<open>n =  2+(m-1)*4\<close> using SDFsfrwrGen by blast
  hence \<open>n = 4*m - 2\<close> 
    by (simp add: \<open>m \<noteq> 0\<close> mult.commute mult_eq_if)
  have \<open>m \<ge> 3\<close> 
    using \<open>\<not> (n = 2 \<or> n = 6)\<close> \<open>n = 2 + (m - 1) * 4\<close> by auto
  hence \<open> {1+j*4| j::nat. j < 3} \<subseteq> {1+j*4| j::nat. j < m}\<close>
    by force
  hence \<open>9 \<in> {1+j*4| j::nat. j < 3}\<close> by force
  hence \<open>9 \<in> {1+j*4| j::nat. j < m}\<close> 
    using  \<open> {1+j*4| j::nat. j < 3} \<subseteq> {1+j*4| j::nat. j < m}\<close> by blast
  hence \<open>9 \<in> {x | x :: nat. x < n \<and> coprime x n}\<close> using \<open>{x | x :: nat. x < n \<and> coprime x n} = {1+j*4| j::nat. j < m}\<close>
    by blast
  hence \<open>coprime (9::nat) n\<close> 
    by blast
  have \<open>(3::nat) dvd 9\<close> by auto
  have  \<open>coprime (3::nat) n\<close> using  \<open>coprime (9::nat) n\<close> \<open>(3::nat) dvd 9\<close>
    by (metis coprime_commute coprime_mult_right_iff dvd_def)
  have \<open>(3::nat) < n\<close> 
    by (metis One_nat_def Suc_lessI \<open>1 < n\<close> \<open>\<not> (n = 2 \<or> n = 6)\<close> \<open>coprime 3 n\<close> coprime_0_left_iff coprime_self numeral_2_eq_2 numeral_3_eq_3 preACasePrimeA1)
  have \<open>(3::nat) \<in>  {x | x :: nat. x < n \<and> coprime x n}\<close> 
    using \<open>3 < n\<close> \<open>coprime 3 n\<close> by blast
  hence  \<open>(3::nat) \<in> {1+j*4| j::nat. j < m}\<close> 
    using \<open>{x |x. x < n \<and> coprime x n} = {1 + j * 4 |j. j < m}\<close> by blast
  then obtain j::nat where \<open>(3::nat) = 1 + j*4\<close> 
    by blast
  from  \<open>(3::nat) = 1 + j*4\<close>  have \<open>2 = j*4\<close> 
    using numeral_3_eq_3 by linarith
  hence \<open>1 = j*2\<close> 
    by linarith
  hence \<open>even 1\<close> 
    by simp
  thus ?thesis 
    using odd_one by blast
qed


lemma preCaseN6B:
  \<open>(n::nat) > 1
\<Longrightarrow>
 \<exists> m.  m \<noteq> 0 \<and> {x | x :: nat. x < n \<and> coprime x n} = {1+j*4| j::nat. j < m}
\<Longrightarrow>
n = 2 \<or> n = 6\<close>
  using XpreCaseN6B by blast

lemma preCaseN6:
  \<open>(n::nat) > 1
 \<Longrightarrow>
 (n = 2 \<or> n = 6) 
 \<longleftrightarrow>
 (\<exists> m.  m \<noteq> 0 \<and> {x | x :: nat. x < n \<and> coprime x n} = {1+j*4| j::nat. j < m})\<close>
  using  preCaseN6B preCaseN6Aand2  by blast

lemma CaseN6:
  \<open>(n::nat) > 1 \<Longrightarrow>
 (n = 2 \<or> n = 6)
 \<longleftrightarrow>
 (\<exists> b  m. b = 4 \<and> m \<noteq> 0 \<and> {x | x :: nat. x < n \<and> coprime x n} = {1+j*b| j::nat. j < m})\<close>
  using preCaseN6 by blast  


lemma Caseb0AX:
  \<open> \<exists>  m. m \<noteq> 0 \<and> {x | x :: nat. x < 2 \<and> coprime x 2} = {1+j*0| j::nat. j < m}\<close>
proof-
  have \<open>{x | x :: nat. x < 2 \<and> coprime x 2} = {1}\<close> 
    using AXXXpreCaseN6X2 by blast
  have \<open>{1+j*0| j::nat. j < 1} = {1}\<close> by auto
  thus ?thesis using  \<open>{x | x :: nat. x < 2 \<and> coprime x 2} = {1}\<close>  by blast
qed

lemma Caseb0A:
  \<open>(n::nat) > 1 \<Longrightarrow>
 n = 2
\<Longrightarrow>
 \<exists> b  m. b = 0 \<and> m \<noteq> 0 \<and> {x | x :: nat. x < n \<and> coprime x n} = {1+j*b| j::nat. j < m}\<close>
  using Caseb0AX by blast

lemma preCaseb0B:
  \<open>(n::nat) > 1 
\<Longrightarrow>
  b = 0
\<Longrightarrow> 
 m \<noteq> 0 
\<Longrightarrow>
 {x | x :: nat. x < n \<and> coprime x n} = {1+j*b| j::nat. j < m}
\<Longrightarrow>
 n = 2\<close>
proof-
  assume \<open>n > 1\<close>
  assume \<open>b = 0\<close>
  assume \<open>m \<noteq> 0\<close>
  assume \<open> {x | x :: nat. x < n \<and> coprime x n} = {1+j*b| j::nat. j < m}\<close>
  have \<open> {1+j*b| j::nat. j < m} =  {1}\<close> using \<open>b = 0\<close> \<open>m \<noteq> 0\<close> by force
  hence \<open> {x | x :: nat. x < n \<and> coprime x n} = {1}\<close> 
    using \<open>{x |x. x < n \<and> coprime x n} = {1 + j * b |j. j < m}\<close> by auto
  have \<open>n-1 \<in>  {x | x :: nat. x < n \<and> coprime x n}\<close> 
    using \<open>1 < n\<close> coprime_diff_one_left_nat by auto
  have \<open>n-1 \<in> {1}\<close> 
    using \<open>n - 1 \<in> {x |x. x < n \<and> coprime x n}\<close> \<open>{x |x. x < n \<and> coprime x n} = {1}\<close> by blast
  hence \<open>n-1 = 1\<close> 
    by blast
  hence \<open>n = 2\<close> by simp
  thus ?thesis by blast
qed

lemma Caseb0B:
  \<open>(n::nat) > 1 
\<Longrightarrow>
 \<exists> b  m. b = 0 \<and> m \<noteq> 0 \<and> {x | x :: nat. x < n \<and> coprime x n} = {1+j*b| j::nat. j < m}
\<Longrightarrow>
 n = 2\<close>
  using preCaseb0B by blast

lemma Caseb0:
  \<open>(n::nat) > 1 \<Longrightarrow>
 n = 2
 \<longleftrightarrow>
 (\<exists> b  m. b = 0 \<and> m \<noteq> 0 \<and> {x | x :: nat. x < n \<and> coprime x n} = {1+j*b| j::nat. j < m})\<close>
  using Caseb0A Caseb0B by blast


lemma CaseOthersNonb3:
  \<open>(n::nat) > 1 \<Longrightarrow>
 \<exists> m.  m \<noteq> 0 \<and> {x | x :: nat. x < n \<and> coprime x n} = {1+j*(b::nat)| j::nat. j < m}
\<Longrightarrow> n \<noteq> 2 \<Longrightarrow> b \<noteq> 3\<close>
proof (rule classical)
  assume \<open>n > 1\<close>
  assume \<open>\<exists> m.  m \<noteq> 0 \<and> {x | x :: nat. x < n \<and> coprime x n} = {1+j*(b::nat)| j::nat. j < m}\<close>
  assume \<open>n \<noteq> 2\<close>
  assume \<open>\<not> (b \<noteq> 3)\<close>
  hence \<open>b = 3\<close> by blast
  from  \<open>\<exists> m.  m \<noteq> 0 \<and> {x | x :: nat. x < n \<and> coprime x n} = {1+j*(b::nat)| j::nat. j < m}\<close>
  obtain m where  \<open>m \<noteq> 0\<close> and 
    \<open>{x | x :: nat. x < n \<and> coprime x n} = {1+j*(b::nat)| j::nat. j < m}\<close>
    by blast
  have \<open>b \<noteq> 0\<close> 
    by (simp add: \<open>b = 3\<close>)
  from \<open>n > 1\<close> \<open>m \<noteq> 0\<close>  \<open>{x | x :: nat. x < n \<and> coprime x n} = {1+j*(b::nat)| j::nat. j < m}\<close>
    \<open>b \<noteq> 0\<close> 
  have \<open>n = 2 + (m-1)*b\<close> using SDFsfrwrGen by blast
  have \<open>n > 2\<close> 
    using \<open>1 < n\<close> \<open>n \<noteq> 2\<close> by linarith
  hence \<open> m \<ge> 2 \<close> using  \<open>n = 2 + (m-1)*b\<close> \<open>b = 3\<close> 
    by simp
  have \<open>(4::nat) \<in> {1+j*(b::nat)| j::nat. j < m}\<close> 
    using \<open>2 \<le> m\<close> \<open>b = 3\<close> by force
  hence \<open>(4::nat) \<in>  {x | x :: nat. x < n \<and> coprime x n}\<close> 
    using \<open>{x |x. x < n \<and> coprime x n} = {1 + j * b |j. j < m}\<close> by auto
  hence \<open>coprime (4::nat) n\<close> 
    by blast
  have \<open>(2::nat) dvd 4\<close> by auto
  hence \<open>coprime (2::nat) n\<close> using  \<open>coprime (4::nat) n\<close> 
    using coprime_divisors dvd_refl by blast
  have \<open>(4::nat) < n\<close> 
    using \<open>4 \<in> {x |x. x < n \<and> coprime x n}\<close> by blast
  have \<open>(2::nat) < (4::nat)\<close> by auto
  have  \<open>(2::nat) < n\<close> 
    by (simp add: \<open>2 < n\<close>)
  hence \<open>(2::nat) \<in>  {x | x :: nat. x < n \<and> coprime x n}\<close> using  \<open>coprime (2::nat) n\<close> by blast
  hence  \<open>(2::nat) \<in> {1+j*(b::nat)| j::nat. j < m}\<close> 
    using \<open>{x |x. x < n \<and> coprime x n} = {1 + j * b |j. j < m}\<close> by blast
  then obtain j::nat where \<open>(2::nat) = 1+j*(3::nat)\<close> using \<open>b = 3\<close> by blast
  from  \<open>(2::nat) = 1+j*(3::nat)\<close>
  have  \<open>(1::nat) = j*(3::nat)\<close> by auto
  hence \<open>3 dvd 1\<close> by auto
  thus ?thesis 
    by (smt One_nat_def add_left_imp_eq nat_dvd_1_iff_1 numeral_2_eq_2 numeral_3_eq_3 plus_1_eq_Suc preCaseN6AA)
qed


lemma CaseOthersNonbG4oddb:
  \<open>(n::nat) > 1 \<Longrightarrow>
 \<exists> m.  m \<noteq> 0 \<and> {x | x :: nat. x < n \<and> coprime x n} = {1+j*(b::nat)| j::nat. j < m} \<Longrightarrow>
n \<noteq> 2 \<Longrightarrow> odd b
\<Longrightarrow> b \<le> 4\<close>
proof(rule classical)
  assume \<open>n > 1\<close>
  assume \<open>\<exists> m.  m \<noteq> 0 \<and> {x | x :: nat. x < n \<and> coprime x n} = {1+j*(b::nat)| j::nat. j < m}\<close>
  assume \<open>n \<noteq> 2\<close>
  assume \<open>odd b\<close>
  assume \<open>\<not>(b \<le> 4)\<close>
  hence \<open>b > 4\<close> 
    using le_less_linear by blast
  from  \<open>\<exists> m.  m \<noteq> 0 \<and> {x | x :: nat. x < n \<and> coprime x n} = {1+j*(b::nat)| j::nat. j < m}\<close>
  obtain m where  \<open> m \<noteq> 0\<close> and \<open>{x | x :: nat. x < n \<and> coprime x n} = {1+j*(b::nat)| j::nat. j < m}\<close>
    by blast
  have \<open>b \<noteq> 0\<close> 
    using \<open>4 < b\<close> by linarith
  from \<open>n > 1\<close> \<open>m \<noteq> 0\<close>  \<open>{x | x :: nat. x < n \<and> coprime x n} = {1+j*(b::nat)| j::nat. j < m}\<close>
    \<open>b \<noteq> 0\<close> 
  have \<open>n = 2 + (m-1)*b\<close> using SDFsfrwrGen by blast
  have \<open>m \<ge> 2\<close> 
    using \<open>n = 2 + (m - 1)*b\<close> \<open>n \<noteq> 2\<close> by auto
  hence \<open>1+b \<in> {1+j*(b::nat)| j::nat. j < m}\<close> 
    by fastforce
  hence  \<open>1+b \<in> {x | x :: nat. x < n \<and> coprime x n}\<close>
    using \<open>{x |x. x < n \<and> coprime x n} = {1 + j * b |j. j < m}\<close> by blast
  hence \<open>coprime (1+b) n\<close> 
    by blast
  have \<open>(2::nat) dvd (1+b)\<close> using \<open>odd b\<close> 
    by simp
  hence \<open>coprime (2::nat) n\<close> 
    using \<open>coprime (1 + b) n\<close> coprime_common_divisor coprime_left_2_iff_odd odd_one by blast
  have \<open>(2::nat) < n\<close> 
    using \<open>1 < n\<close> \<open>n \<noteq> 2\<close> by linarith
  have \<open>(2::nat) \<in>  {x | x :: nat. x < n \<and> coprime x n}\<close> 
    using \<open>2 < n\<close> \<open>coprime 2 n\<close> by blast 
  hence  \<open>(2::nat) \<in>  {1+j*(b::nat)| j::nat. j < m}\<close> 
    using \<open>{x |x. x < n \<and> coprime x n} = {1 + j * b |j. j < m}\<close> by blast
  then obtain j::nat where \<open>(2::nat) = 1+j*b\<close> by blast
  from  \<open>(2::nat) = 1+j*b\<close> have  \<open>1 = j*b\<close> 
    by linarith
  thus ?thesis 
    by simp
qed

lemma CaseOthersNonbG4even:
  \<open>(n::nat) > 1 \<Longrightarrow>
 \<exists> m.  m \<noteq> 0 \<and> {x | x :: nat. x < n \<and> coprime x n} = {1+j*(b::nat)| j::nat. j < m} \<Longrightarrow>
n \<noteq> 2 \<Longrightarrow> even b 
\<Longrightarrow> b \<le> 4\<close>
proof(rule classical)
  assume \<open>n > 1\<close>
  assume \<open>\<exists> m.  m \<noteq> 0 \<and> {x | x :: nat. x < n \<and> coprime x n} = {1+j*(b::nat)| j::nat. j < m}\<close>
  assume \<open>n \<noteq> 2\<close>
  assume \<open>even b\<close>
  assume \<open>\<not>(b \<le> 4)\<close>
  hence \<open>b > 4\<close> 
    using le_less_linear by blast
  from  \<open>\<exists> m.  m \<noteq> 0 \<and> {x | x :: nat. x < n \<and> coprime x n} = {1+j*(b::nat)| j::nat. j < m}\<close>
  obtain m where  \<open> m \<noteq> 0\<close> and \<open>{x | x :: nat. x < n \<and> coprime x n} = {1+j*(b::nat)| j::nat. j < m}\<close>
    by blast
  have \<open>b \<noteq> 0\<close> 
    using \<open>4 < b\<close> by linarith
  from \<open>n > 1\<close> \<open>m \<noteq> 0\<close>  \<open>{x | x :: nat. x < n \<and> coprime x n} = {1+j*(b::nat)| j::nat. j < m}\<close>
    \<open>b \<noteq> 0\<close> 
  have \<open>n = 2 + (m-1)*b\<close> using SDFsfrwrGen by blast
  obtain k :: nat where \<open>b = 2*k\<close> 
    using \<open>even b\<close> by blast
  from \<open>n = 2 + (m-1)*b\<close>  \<open>b = 2*k\<close> 
  have \<open>n = 2*(1 + (m-1)*k)\<close> by simp
  show ?thesis
  proof (cases \<open>odd m\<close>)
    case True
    hence \<open>odd m\<close> by blast
    then obtain t::nat where \<open>m-1 = 2*t\<close> 
      by (metis odd_two_times_div_two_nat)
    have  \<open>n = 2*(1 + b*t)\<close> 
      using \<open>m - 1 = 2 * t\<close> \<open>n = 2 + (m - 1) * b\<close> by auto
    have \<open>t < m\<close> 
      using \<open>m - 1 = 2 * t\<close> \<open>m \<noteq> 0\<close> by linarith
    have \<open>1 + b*t \<in> {1+j*(b::nat)| j::nat. j < m}\<close> 
      using \<open>t < m\<close> by auto 
    hence \<open>1 + b*t \<in> {x | x :: nat. x < n \<and> coprime x n}\<close> 
      using \<open>{x |x. x < n \<and> coprime x n} = {1 + j * b |j. j < m}\<close> by blast 
    hence \<open> coprime (1 + b*t) n\<close> by auto
    thus ?thesis 
      by (metis (no_types, lifting) \<open>b = 2 * k\<close> \<open>n = 2 * (1 + (m - 1) * k)\<close> \<open>n = 2 * (1 + b * t)\<close> \<open>n = 2 + (m - 1) * b\<close> \<open>n \<noteq> 2\<close> add_cancel_right_right coprime_mult_right_iff coprime_self mult_cancel_left mult_is_0 nat_dvd_1_iff_1)
  next
    case False
    thus ?thesis
    proof(cases \<open>odd k\<close>)
      case True
      hence \<open>odd k\<close> by blast
      have \<open>even (1 + (m - 1) * k)\<close> 
        by (simp add: False True \<open>m \<noteq> 0\<close>)
      have \<open>coprime (2 + (m - 1) * k) (1 + (m - 1) * k)\<close> 
        by simp
      have \<open>coprime (2 + (m - 1) * k) n\<close> 
        using \<open>coprime (2 + (m - 1) * k) (1 + (m - 1) * k)\<close> \<open>even (1 + (m - 1) * k)\<close> \<open>n = 2 * (1 + (m - 1) * k)\<close> coprime_common_divisor coprime_mult_right_iff coprime_right_2_iff_odd odd_one by blast
      have \<open>2 + (m - 1) * k < n\<close> 
        by (metis (no_types, lifting) \<open>even (1 + (m - 1) * k)\<close> \<open>n = 2 * (1 + (m - 1) * k)\<close> add_gr_0 add_mono_thms_linordered_semiring(1) dvd_add_left_iff dvd_add_triv_left_iff dvd_imp_le le_add2 le_neq_implies_less less_numeral_extra(1) mult_2 odd_one)
      have \<open>2 + (m - 1) * k  \<in> {x | x :: nat. x < n \<and> coprime x n}\<close> 
        using \<open>2 + (m - 1) * k < n\<close> \<open>coprime (2 + (m - 1) * k) n\<close> by blast
      hence \<open>2 + (m - 1) * k  \<in> {1 + j * b |j. j < m}\<close> 
        using \<open>{x |x. x < n \<and> coprime x n} = {1 + j * b |j. j < m}\<close> by blast
      then obtain j::nat where  \<open>2 + (m - 1) * k  = 1 + j * b\<close> and \<open>j < m\<close>
        by blast
      from  \<open>2 + (m - 1) * k  = 1 + j * b\<close>
      have  \<open>1 + (m - 1) * k  = j * b\<close> by simp
      hence  \<open>1 + (m - 1) * k  = j * (2*k)\<close> 
        using \<open>b = 2 * k\<close> by blast
      thus ?thesis 
        by (metis \<open>b = 2 * k\<close> \<open>even b\<close> \<open>n = 2 * (1 + (m - 1) * k)\<close> \<open>n = 2 + (m - 1) * b\<close> dvd_add_times_triv_right_iff dvd_antisym dvd_imp_le dvd_triv_right even_numeral mult_2 zero_less_numeral)
    next
      case False
      hence \<open>even k\<close> by auto
      have \<open>odd (1 + (m - 1) * k)\<close> 
        by (simp add: \<open>even k\<close> )
      hence \<open>coprime (3 + (m - 1) * k) (1 + (m - 1) * k)\<close> 
        by (smt add_numeral_left coprime_common_divisor coprime_right_2_iff_odd dvd_add_left_iff not_coprimeE numeral_Bit1 numeral_One numeral_plus_one one_add_one)
      hence \<open>coprime (3 + (m - 1) * k) n\<close> 
        by (metis \<open>even k\<close> \<open>n = 2 * (1 + (m - 1) * k)\<close> coprime_mult_right_iff coprime_right_2_iff_odd even_add even_mult_iff odd_numeral)
      have \<open>3 + (m - 1) * k < n\<close> 
        by (smt Groups.add_ac(2) \<open>even k\<close> \<open>n = 2 * (1 + (m - 1) * k)\<close> \<open>n = 2 + (m - 1) * b\<close> \<open>n \<noteq> 2\<close> add_Suc_right add_cancel_right_right add_mono_thms_linordered_semiring(1) dvd_imp_le even_add even_mult_iff le_add2 le_neq_implies_less left_add_twice mult_2 neq0_conv numeral_Bit1 numeral_One odd_numeral one_add_one plus_1_eq_Suc)
      have \<open>3 + (m - 1) * k \<in> {x |x. x < n \<and> coprime x n}\<close> 
        using \<open>3 + (m - 1) * k < n\<close> \<open>coprime (3 + (m - 1) * k) n\<close> by blast
      hence \<open>3 + (m - 1) * k \<in> {1 + j * b |j. j < m}\<close> 
        using \<open>{x |x. x < n \<and> coprime x n} = {1 + j * b |j. j < m}\<close> by blast 
      then obtain j::nat where \<open>3 + (m - 1) * k = 1 + j * b\<close> 
        by blast
      from \<open>3 + (m - 1) * k = 1 + j * b\<close>  have \<open>2 + (m - 1) * k = j * b\<close> by simp
      hence  \<open>2 + (m - 1) * k = j * 2*k\<close> 
        by (simp add: \<open>b = 2 * k\<close>)
      thus ?thesis 
        by (metis \<open>4 < b\<close> \<open>b = 2 * k\<close> \<open>even k\<close> dvd_add_times_triv_right_iff dvd_antisym dvd_triv_right mult_2 nat_neq_iff numeral_Bit0)
    qed
  qed
qed

lemma CaseOthersNonbG4:
  \<open>(n::nat) > 1 \<Longrightarrow>
 (\<exists> m.  m \<noteq> 0 \<and> {x | x :: nat. x < n \<and> coprime x n} = {1+j*(b::nat)| j::nat. j < m}) \<Longrightarrow>
n \<noteq> 2 
\<Longrightarrow> b \<le> 4\<close>
  using CaseOthersNonbG4oddb CaseOthersNonbG4even by blast

lemma WCaseOthers:
  \<open>(n::nat) > 1 \<Longrightarrow>
 \<exists> m.  m \<noteq> 0 \<and> {x | x :: nat. x < n \<and> coprime x n} = {1+j*(b::nat)| j::nat. j < m}
\<Longrightarrow> n \<noteq> 2 \<Longrightarrow> b \<le> 4 \<and> b \<noteq> 3\<close>
  using CaseOthersNonb3 CaseOthersNonbG4
  by blast

lemma obviowhr3uhr: \<open> (b::nat) \<le> 4 \<and> b \<noteq> 3 \<Longrightarrow>  b = 0 \<or> b = 1 \<or> b = 2 \<or> b = 4\<close>
  by linarith

lemma CaseOthers:
  \<open>(n::nat) > 1 \<Longrightarrow>
 \<exists> m.  m \<noteq> 0 \<and> {x | x :: nat. x < n \<and> coprime x n} = {1+j*(b::nat)| j::nat. j < m}
\<Longrightarrow> n \<noteq> 2 \<Longrightarrow> b = 0 \<or> b = 1 \<or> b = 2 \<or> b = 4\<close>
  using WCaseOthers obviowhr3uhr by auto

lemma TSolutionOfTheProblemRed:
  \<open>(n::nat) > 1 \<Longrightarrow>
 prime n \<or> (\<exists> k. n = 2^k) \<or>  (n = 2 \<or> n = 6) \<or> n = 2
 \<longleftrightarrow>
 (\<exists> b m. m \<noteq> 0 \<and> {x | x :: nat. x < n \<and> coprime x n} = {1+j*b| j::nat. j < m})\<close>
  using CaseN6 CaseOthers CasePow2 CasePrime Caseb0B Collect_cong
  sorry
(*  by smt *)

lemma SolutionOfTheProblemRed:
  \<open>(n::nat) > 1 \<Longrightarrow>
(prime n \<or> (\<exists> k. n = 2^k) \<or>  n = 6)
 \<longleftrightarrow>
 (\<exists> b m. m \<noteq> 0 \<and> {x | x :: nat. x < n \<and> coprime x n} = {1+j*b| j::nat. j < m})\<close>
proof-
  assume \<open>n > 1\<close>
  hence \<open> prime n \<or> (\<exists> k. n = 2^k) \<or>  (n = 2 \<or> n = 6) \<or> n = 2
 \<longleftrightarrow>
 (\<exists> b m. m \<noteq> 0 \<and> {x | x :: nat. x < n \<and> coprime x n} = {1+j*b| j::nat. j < m})\<close>
    using TSolutionOfTheProblemRed by blast
  have \<open>n = 2 \<longrightarrow> (\<exists> k. n = 2^k)\<close> 
    by (metis power_one_right)
  thus ?thesis using \<open>prime n \<or> (\<exists> k. n = 2^k) \<or>  (n = 2 \<or> n = 6) \<or> n = 2
 \<longleftrightarrow>
 (\<exists> b m. m \<noteq> 0 \<and> {x | x :: nat. x < n \<and> coprime x n} = {1+j*b| j::nat. j < m})\<close>
    by blast
qed

lemma FSDFDWFMin:
  \<open>(n::nat) > 1 \<Longrightarrow> Min {x | x :: nat. x < n \<and> coprime x n} = 1\<close>
proof-
  assume \<open>n > 1\<close>
  have \<open>finite {x | x :: nat. x < n \<and> coprime x n}\<close>
    by auto
  have \<open>{x | x :: nat. x < n \<and> coprime x n} \<noteq> {}\<close> 
    using \<open>1 < n\<close> by auto
  have \<open>1 \<in> {x | x :: nat. x < n \<and> coprime x n}\<close> 
    using \<open>1 < n\<close> by auto
  have \<open>\<forall> x. coprime x n \<longrightarrow> x \<ge> 1\<close> 
    using \<open>1 < n\<close> le_less_linear by fastforce
  hence \<open>\<forall> x.  x < n \<and> coprime x n \<longrightarrow> x \<ge> 1\<close> 
    by blast
  hence \<open>\<forall> x \<in> {x | x :: nat. x < n \<and> coprime x n}. x \<ge> 1\<close> 
    by blast
  hence \<open>Min {x | x :: nat. x < n \<and> coprime x n} \<ge> 1\<close> 
    using  \<open>finite {x | x :: nat. x < n \<and> coprime x n}\<close> 
      \<open>{x |x. x < n \<and> coprime x n} \<noteq> {}\<close> by auto
  thus ?thesis 
    using Min_le \<open>1 \<in> {x |x. x < n \<and> coprime x n}\<close> \<open>finite {x |x. x < n \<and> coprime x n}\<close> antisym by blast
qed

lemma FSDFDWFMinProg:
  \<open>(n::nat) > 1 \<Longrightarrow> (m::nat) \<noteq> 0 \<Longrightarrow> Min {a+j*b| j::nat. j < m} = a\<close>
proof-
  assume \<open>n > 1\<close>
  assume \<open>m \<noteq> 0\<close>
  have \<open>{a+j*b| j::nat. j < m} \<noteq> {}\<close> 
    using \<open>m \<noteq> 0\<close> by blast
  have \<open>finite {j| j::nat. j < m}\<close> 
    by auto
  hence  \<open>finite ( (\<lambda> j. a+j*b) ` {j| j::nat. j < m} )\<close> 
    by blast
  hence  \<open>finite {a+j*b| j::nat. j < m}\<close> 
    by auto
  have \<open>\<forall> j. a+b*j \<ge> a\<close> 
    using le_add1 by blast
  hence \<open>\<forall> x \<in> {a+j*b| j::nat. j < m}. x \<ge> a\<close>
    by auto
  hence \<open>Min {a+j*b| j::nat. j < m} \<ge> a\<close>
    using \<open>{a + j * b |j. j < m} \<noteq> {}\<close> by auto
  have  \<open>a \<in> {a+j*b| j::nat. j < m}\<close>
    using \<open>m \<noteq> 0\<close> by auto
  thus ?thesis using  \<open>Min {a+j*b| j::nat. j < m} \<ge> a\<close> 
    using Min_le \<open>finite {a + j * b |j. j < m}\<close> antisym by blast
qed

lemma FSDFd:
  \<open>(n::nat) > 1 \<Longrightarrow> (m::nat) \<noteq> 0 \<Longrightarrow> {x | x :: nat. x < n \<and> coprime x n} = {(a::nat)+j*(b::nat)| j::nat. j < m} \<Longrightarrow> a = 1\<close>
proof-
  assume \<open>n > 1\<close>
  assume \<open>m \<noteq> 0\<close>
  assume \<open>{x | x :: nat. x < n \<and> coprime x n} = {a+j*b| j::nat. j < m}\<close>
  hence \<open>Min {x | x :: nat. x < n \<and> coprime x n} = Min {a+j*b| j::nat. j < m}\<close> by auto
  from \<open>n > 1\<close>
  have \<open>Min {x | x :: nat. x < n \<and> coprime x n} = 1\<close>
    using FSDFDWFMin 
    by blast
  from \<open>n > 1\<close> \<open>m \<noteq> 0\<close> have \<open>Min  {a+j*b| j::nat. j < m} = a\<close>
    using FSDFDWFMinProg by blast
  hence \<open>Min  {a+j*b| j::nat. j < m} = a\<close> by blast
  thus ?thesis using \<open>Min {x | x :: nat. x < n \<and> coprime x n} = 1\<close> \<open>Min {x | x :: nat. x < n \<and> coprime x n} = Min {a+j*b| j::nat. j < m}\<close>
    by linarith
qed

lemma FSDFDA:
  \<open>(n::nat) > 1
 \<Longrightarrow>
(\<exists> a b m::nat. m \<noteq> 0 \<and> {x | x :: nat. x < n \<and> coprime x n} = {a+j*b| j::nat. j < m})
\<Longrightarrow>
 (\<exists> b m::nat. m \<noteq> 0 \<and> {x | x :: nat. x < n \<and> coprime x n} = {1+j*b| j::nat. j < m})\<close>
proof-
  assume \<open>n > 1\<close>
  assume \<open>\<exists> a b m::nat. m \<noteq> 0 \<and> {x | x :: nat. x < n \<and> coprime x n} = {a+j*b| j::nat. j < m}\<close>
  then obtain a b m::nat where \<open>m \<noteq> 0\<close> and \<open>{x | x :: nat. x < n \<and> coprime x n} = {a+j*b| j::nat. j < m}\<close>
    by auto
  from \<open>n > 1\<close>  \<open>m \<noteq> 0\<close> \<open>{x | x :: nat. x < n \<and> coprime x n} = {a+j*b| j::nat. j < m}\<close>
  have \<open>a = 1\<close> using FSDFd
    by blast
  thus ?thesis using  \<open>m \<noteq> 0\<close> \<open>{x | x :: nat. x < n \<and> coprime x n} = {a+j*b| j::nat. j < m}\<close> 
    by auto
qed

lemma FSDFDB:
  \<open>(n::nat) > 1
 \<Longrightarrow>
(\<exists> b m. m \<noteq> 0 \<and> {x | x :: nat. x < n \<and> coprime x n} = {1+j*b| j::nat. j < m})
\<Longrightarrow>
 (\<exists> a b m. m \<noteq> 0 \<and> {x | x :: nat. x < n \<and> coprime x n} = {a+j*b| j::nat. j < m})\<close>
  by blast

lemma FSDFDC:
  \<open>(n::nat) > 1
 \<Longrightarrow>
(\<exists> b m. m \<noteq> 0 \<and> {x | x :: nat. x < n \<and> coprime x n} = {1+j*b| j::nat. j < m})
\<longleftrightarrow>
 (\<exists> a b m. m \<noteq> 0 \<and> {x | x :: nat. x < n \<and> coprime x n} = {a+j*b| j::nat. j < m})\<close>
  by (smt Collect_cong FSDFDA FSDFDB)

text{* Solution of the Problem *}
theorem SolutionOfTheProblem:
  \<open>(n::nat) > 1 \<Longrightarrow>
 prime n \<or> (\<exists> k. n = 2^k) \<or> n = 6
 \<longleftrightarrow>  
(\<exists> a b m. m \<noteq> 0 \<and> {x | x :: nat. x < n \<and> coprime x n} = {a+j*b| j::nat. j < m})\<close>
  using FSDFDC SolutionOfTheProblemRed 
  by auto

  

end

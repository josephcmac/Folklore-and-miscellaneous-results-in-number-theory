(*
Title: Trapezoidal numbers
Author: Jose Manuel Rodriguez Caballero

We formally verify the main result from the paper [gamer1985trapezoidal]:

Definition. A natural number is trapezoidal if it is the sum of 2 or more consecutive
non-zero natural numbers.

Theorem. For any natural number  n \<noteq> 0, we have that n is a trapezoidal number if 
and only if n is not a power of 2 (including 1).

References:

@article{gamer1985trapezoidal,
  title={Trapezoidal numbers},
  author={Gamer, Carlton and Roeder, David W and Watkins, John J},
  journal={Mathematics Magazine},
  volume={58},
  number={2},
  pages={108--110},
  year={1985},
  publisher={Taylor \& Francis}
}

(This code  was verified in Isabelle2018)

*)

theory TrapezoidalNumbers

imports Complex_Main PowOfTwo

begin

section {* Necessary Condition *}

primrec TSum :: "nat \<Rightarrow> nat  \<Rightarrow> nat" where
  "TSum a 0 = 0" 
| "TSum a (Suc k) = (TSum a k) + (a + k)"



lemma TrapezoidalNumbersNec2_1: "(k::nat) \<ge> 1 \<Longrightarrow> odd k \<or> odd ((k::nat)+2*a-1)"
  by (meson dvd_diffD1 dvd_triv_left even_add le_add1 le_trans odd_one)

lemma TrapezoidalNumbersNec2A: "a \<ge> 1 \<and> (k::nat) \<ge> 2 \<and> odd k \<Longrightarrow> \<not> (\<exists> r. k*(k+2*a-1) = 2^r)"
  using TrapezoidalNumbersNec2_2 dvd_triv_left by blast

lemma TrapezoidalNumbersNec2B: "a \<ge> 1 \<and> (k::nat) \<ge> 2 \<and> odd (k+2*a-1) \<Longrightarrow> \<not> (\<exists> r. k*(k+2*a-1) = 2^r)"
  by (metis Nat.add_diff_assoc TrapezoidalNumbersNec2_2 dvd_triv_right mult_2 trans_le_add1)

lemma TrapezoidalNumbersNec2: "a \<ge> 1 \<and> (k::nat) \<ge> 2 \<Longrightarrow> \<not> (\<exists> r. k*(k+2*a-1) = 2^r)"
  by (metis TrapezoidalNumbersNec2A TrapezoidalNumbersNec2B TrapezoidalNumbersNec2_1 add_leD2 one_add_one)

lemma HDGFHFreal: "(k::real)*(k+2*a-1) + 2*(a + k) = (k+1)*((k+1)+2*a-1)"
  by (smt mult.commute semiring_normalization_rules(3))

lemma HDGFHF: "a \<ge> 1 \<Longrightarrow> (k::nat)*(k+2*a-1) + 2*(a + k) = (Suc k)*((Suc k)+2*a-1)"
proof (rule classical)
  obtain kk where "kk = real k" by simp
  obtain aa where "aa = real a" by simp
  assume "a \<ge> 1"
  assume "\<not> (k*(k+2*a-1) + 2*(a + k) = (Suc k)*((Suc k)+2*a-1))"
  then have "(k*(k+2*a-1) + 2*(a + k) \<noteq> (k+1)*((k+1)+2*a-1))" by simp
  then have "real  (k*(k+2*a-1) + 2*(a + k)) \<noteq> real ((k+1)*((k+1)+2*a-1))"
    using of_nat_eq_iff by blast
  then have  "(kk*(kk+2*aa-1) + 2*(aa + kk)) \<noteq> ((kk+1)*((kk+1)+2*aa-1))"
    using diff_mult_distrib2 by auto
  then have False
    using \<open>k * (k + 2 * a - 1) + 2 * (a + k) \<noteq> (k + 1) * (k + 1 + 2 * a - 1)\<close> diff_mult_distrib2 by auto
  then show ?thesis by blast
qed

lemma TrapezoidalNumbersNec1: "a \<ge> 1 \<Longrightarrow> 2*TSum a k =  k*(k+2*a-1)"
proof (induction k)
  case 0
  then show ?case by auto
next
  case (Suc k)
  then have "2*TSum a k + 2*(a + k) =  k*(k+2*a-1) + 2*(a + k)" by auto
  then have "2*(TSum a k + (a + k)) =  k*(k+2*a-1) + 2*(a + k)" 
    by simp
  then have  "2*(TSum a (Suc k)) =  k*(k+2*a-1) + 2*(a + k)" by simp
  then have "2*(TSum a (Suc k)) =  (Suc k)*((Suc k)+2*a-1)"
    using HDGFHF \<open>a \<ge> 1\<close> by auto
  then show ?case
    by blast
qed

theorem TrapezoidalNumbersNec: "( \<exists> a k. a \<ge> 1 \<and> k \<ge> 2 \<and> n = (TSum a k) ) \<Longrightarrow> \<not> (\<exists> r. n = 2^r)"
proof-
  assume "\<exists> a k. a \<ge> 1 \<and> k \<ge> 2 \<and> n = (TSum a k)"
  then obtain a k where "a \<ge> 1" and "k \<ge> 2" and "n = (TSum a k)" by auto
  from \<open>n = (TSum a k)\<close> have \<open>2*n = k*(k+2*a-1)\<close> 
    using TrapezoidalNumbersNec1 \<open>a \<ge> 1\<close> by blast
  have "\<not> (\<exists> r. 2*n = 2^r)" 
    using TrapezoidalNumbersNec2 \<open>1 \<le> a\<close> \<open>2 * n = k * (k + 2 * a - 1)\<close> \<open>2 \<le> k\<close> by auto
  then have "\<not> (\<exists> r. n = 2^r)"  by (rule TrapezoidalNumbersNec3)
  then show ?thesis by blast
qed

section {* Sufficient Condition *}


lemma TrapezoidalNumbersSuf_1C_BOUNDED: "\<forall> N  n. (n \<le> (N::nat) \<longrightarrow> (n \<noteq> 0 \<longrightarrow>  ( \<exists> r t.  n = 2^r*t \<and> odd t ) ))"
  using TrapezoidalNumbersSuf_1C_BOUNDEDNonQ by blast

lemma TrapezoidalNumbersSuf_1C: "(n::nat) \<noteq> 0 \<longrightarrow> ( \<exists> r t.  n = 2^r*t \<and> odd t )"
  using TrapezoidalNumbersSuf_1C_BOUNDED by blast 

lemma TrapezoidalNumbersSuf_1B: "n \<noteq> 0 \<Longrightarrow>  ( \<forall> d.  d dvd (n::nat) \<and> odd d \<longrightarrow> d = 1 )  \<Longrightarrow> (\<exists> r. n = 2^r)"
proof-
  assume \<open>n \<noteq> 0\<close>
  assume \<open>  \<forall> d.  d dvd (n::nat) \<and> odd d \<longrightarrow> d = 1 \<close>
  from \<open>n \<noteq> 0\<close> have \<open> \<exists> r t.  n = 2^r*t \<and> odd t \<close> 
    using TrapezoidalNumbersSuf_1C by blast
  then obtain r t where \<open> n = 2^r*t \<close> and \<open>odd t\<close> by blast
  from \<open> n = 2^r*t \<close>  have \<open>t dvd n\<close> 
    by simp 
  from \<open> \<forall> d.  d dvd (n::nat) \<and> odd d \<longrightarrow> d = 1\<close> \<open>odd t\<close> \<open>t dvd n\<close>  have \<open>t = 1\<close> 
    by blast
  from \<open> n = 2^r*t \<close> this have \<open>n = 2^r\<close> 
    using nat_mult_1_right by blast
  then have \<open>\<exists> r. n = 2^r\<close> by blast
  then show ?thesis by blast
qed


lemma TrapezoidalNumbersSuf_1A: "n \<noteq> 0 \<Longrightarrow> (\<not> ( \<exists> d. d \<ge> 2 \<and> d dvd (n::nat) \<and> odd d ) \<longrightarrow> (\<exists> r. n = 2^r))"
  by (metis One_nat_def Suc_leI TrapezoidalNumbersSuf_1B dvd_1_left dvd_pos_nat gr0I linorder_neqE_nat  nat_dvd_not_less numeral_2_eq_2)

lemma TrapezoidalNumbersSuf_1: "n \<noteq> 0 \<Longrightarrow> (\<not> (\<exists> r. n = 2^r) \<longrightarrow> ( \<exists> d. d \<ge> 2 \<and> d dvd (n::nat) \<and> odd d) )"
  using TrapezoidalNumbersSuf_1A by blast

lemma TrapezoidalNumbersSuf_2A2: "n \<noteq> 0 \<Longrightarrow> \<exists> d. d \<ge> 2 \<and> d dvd (n::nat) \<and> odd d \<and> d^2 \<ge> 2*n \<Longrightarrow> ( \<exists> a k. a \<ge> 1 \<and> k \<ge> 2 \<and> 2*n = k*(k+2*a-1) )"
proof -
  assume \<open>n \<noteq> 0\<close>
  assume \<open>\<exists> d. d \<ge> 2 \<and> d dvd (n::nat) \<and> odd d \<and> d^2 \<ge> 2*n\<close>
  obtain d where \<open>d \<ge> 2\<close> and \<open>d dvd n\<close> and \<open>odd d\<close> and \<open>d^2 \<ge> 2*n\<close>
    using \<open>\<exists>d\<ge>2. d dvd n \<and> odd d \<and> 2 * n \<le> d\<^sup>2\<close> by blast
  obtain e where \<open>d*e = n\<close> 
    using \<open>d dvd n\<close> dvd_mult_div_cancel by blast
  obtain k where \<open>k = 2*e\<close> by simp
  have \<open>d \<ge> k\<close> 
    by (metis \<open>2 * n \<le> d\<^sup>2\<close> \<open>2 \<le> d\<close> \<open>d * e = n\<close> \<open>k = 2 * e\<close> less_le_trans mult.left_commute nat_mult_le_cancel_disj pos2 power2_eq_square)
  have \<open>even (d - k + 1)\<close> 
    using \<open>k = 2 * e\<close> \<open>k \<le> d\<close> \<open>odd d\<close> by auto
  then   obtain a::nat where \<open> 2*a  = d - k + 1\<close>  
    using  \<open>odd d\<close>  by (metis evenE)
  from \<open> 2*a  = d - k + 1\<close> \<open>k = 2 * e\<close>  \<open>d * e = n\<close> have \<open>k * (k + 2*a - 1) = 2*n\<close>
    by auto
  have \<open>a \<ge> 1\<close> 
    using \<open>2 * a = d - k + 1\<close> by auto
  have \<open>e \<ge> 1\<close> 
    using \<open>d * e = n\<close> \<open>n \<noteq> 0\<close> by auto
  from \<open>k = 2 * e\<close> have \<open>k \<ge> 2\<close> 
    using \<open>1 \<le> e\<close> by linarith
  show ?thesis 
    using \<open>1 \<le> a\<close> \<open>2 \<le> k\<close> \<open>k * (k + 2 * a - 1) = 2 * n\<close> by fastforce 
qed

lemma TrapezoidalNumbersSuf_2A1: "n \<noteq> 0 \<Longrightarrow> \<exists> d. d \<ge> 2 \<and> d dvd (n::nat) \<and> odd d \<and> d^2 \<le> 2*n \<Longrightarrow> ( \<exists> a k. a \<ge> 1 \<and> k \<ge> 2 \<and> 2*n = k*(k+2*a-1) )"
proof -
  assume \<open>n \<noteq> 0\<close>
  assume \<open>\<exists> d. d \<ge> 2 \<and> d dvd (n::nat) \<and> odd d \<and> d^2 \<le> 2*n\<close>
  obtain d where \<open>d \<ge> 2\<close> and \<open>d dvd n\<close> and \<open>odd d\<close> and \<open>d^2 \<le> 2*n\<close>
    using \<open>\<exists>d\<ge>2. d dvd n \<and> odd d \<and> 2 * n \<ge> d\<^sup>2\<close> by blast
  obtain e where \<open>d*e = n\<close> 
    using \<open>d dvd n\<close> dvd_mult_div_cancel by blast
  have \<open>d*(2*e) = 2*n\<close> 
    using \<open>d * e = n\<close> mult.left_commute by blast
  from \<open>d*(2*e) = 2*n\<close> \<open>d^2 \<le> 2*n\<close>  have \<open>2*e \<ge> d\<close> 
    by (metis \<open>2 \<le> d\<close> less_le_trans nat_mult_le_cancel_disj pos2 power2_eq_square)  
  obtain k where \<open>k = d\<close>
    by simp
  have \<open>2*e  \<ge> k - 1 \<close> 
    using \<open>d \<le> 2 * e\<close> \<open>k = d\<close> by linarith
  have \<open>even (2*e - k - 1)\<close> 
    by (simp add: \<open>k = d\<close> \<open>odd d\<close>)
  obtain a where \<open>2*a = 2*e - k + 1\<close>  
    by (metis One_nat_def Suc_leI \<open>d \<le> 2 * e\<close> \<open>even (2 * e - k - 1)\<close> \<open>k = d\<close> \<open>odd d\<close> dvdE dvd_triv_left even_diff_nat le_neq_implies_less linorder_not_le zero_less_diff)
  have \<open>k \<ge> 2\<close> 
    by (simp add: \<open>2 \<le> d\<close> \<open>k = d\<close>)
  have \<open>a \<ge> 1\<close> 
    using \<open>2 * a = 2 * e - k + 1\<close> by auto
  have \<open>k * (k + 2*a - 1) = 2*n\<close> 
    by (simp add: \<open>2 * a = 2 * e - k + 1\<close> \<open>d * (2 * e) = 2 * n\<close> \<open>d \<le> 2 * e\<close> \<open>k = d\<close>)
  show ?thesis 
    using \<open>1 \<le> a\<close> \<open>2 \<le> d\<close> \<open>k * (k + 2 * a - 1) = 2 * n\<close> \<open>k = d\<close> by fastforce
qed


lemma TrapezoidalNumbersSuf_2A: "n \<noteq> 0 \<Longrightarrow> \<exists> d. d \<ge> 2 \<and> d dvd (n::nat) \<and> odd d \<Longrightarrow> ( \<exists> a k. a \<ge> 1 \<and> k \<ge> 2 \<and> 2*n = k*(k+2*a-1) )"
  by (metis TrapezoidalNumbersSuf_2A1 TrapezoidalNumbersSuf_2A2 nat_le_linear)

lemma TrapezoidalNumbersSuf_2: "n \<noteq> 0 \<Longrightarrow> \<exists> d. d \<ge> 2 \<and> d dvd (n::nat) \<and> odd d \<Longrightarrow> ( \<exists> a k. a \<ge> 1 \<and> k \<ge> 2 \<and> n = (TSum a k) )"
  by (metis Suc_mult_cancel1 TrapezoidalNumbersNec1 TrapezoidalNumbersSuf_2A numeral_2_eq_2)

theorem TrapezoidalNumbersSuf: "n \<noteq> 0 \<Longrightarrow>  \<not> (\<exists> r. n = 2^r) \<Longrightarrow> ( \<exists> a k. a \<ge> 1 \<and> k \<ge> 2 \<and> n = (TSum a k) )"
  using TrapezoidalNumbersSuf_1 TrapezoidalNumbersSuf_2 by blast

section {* Main result *}

theorem TrapezoidalNumbers: "n \<noteq> 0 \<Longrightarrow>  ( \<exists> a k. a \<ge> 1 \<and> k \<ge> 2 \<and> n = (TSum a k) ) \<longleftrightarrow>  \<not> (\<exists> r. n = 2^r)"
  using TrapezoidalNumbersNec TrapezoidalNumbersSuf by blast

end
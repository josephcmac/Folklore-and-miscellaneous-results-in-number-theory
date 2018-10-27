(*
Title: 2-densely divisible numbers
Author: Jose Manuel Rodriguez Caballero

The so-called 2-densely divisible numbers were introduced by the group
DHJ Polymath [castryck2014new].

Definition. An integer n \<ge> 1 is 2-densely divisible if and only if for any pair 
of consecutive divisors d and e, we have d < e \<le> 2d.

We will prove that an integer n \<ge> 1 is a power of 2 if and only if n is 
2-densely divisible and n is not the semi-perimeter of a Pythagorean
triangle. This theorem is due to the author (Jose M. Rodriguez Caballero).

Reference.

@article{castryck2014new,
  title={New equidistribution estimates of Zhang type},
  author={Castryck, Wouter and Fouvry, {\'E}tienne and Harcos, Gergely and Kowalski, Emmanuel and Michel, Philippe and Nelson, Paul and Paldi, Eytan and Pintz, J{\'a}nos and Sutherland, Andrew and Tao, Terence and others},
  journal={Algebra \& Number Theory},
  volume={8},
  number={9},
  pages={2067--2199},
  year={2014},
  publisher={Mathematical Sciences Publishers}
}


(This code  was verified in Isabelle2018)

*)

theory TwoDenselyDivisible

imports Complex_Main PowOfTwo PeriPythTriang

begin

text {* u and v are consecutive divisors of n *}
definition ConsecDiv :: \<open>nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool\<close> where
  \<open>ConsecDiv \<equiv> \<lambda> n u v::nat. (u dvd n \<and> v dvd n \<and> u < v \<and> (\<forall> d:: nat. d dvd n \<longrightarrow> d \<le> u \<or> v \<le> d ))\<close>

text {* n is a 2-densely divisible number *}
definition TwoDD :: \<open>nat \<Rightarrow> bool\<close> where
  \<open>TwoDD \<equiv> \<lambda> n. ( \<forall> u v. ConsecDiv n u v \<longrightarrow> v \<le> 2*u )\<close>

text {* n is the semiperimeter of a Pythagorean triangle  *}
definition SemiPeriPytha :: "nat \<Rightarrow> bool" where
  \<open>SemiPeriPytha \<equiv> \<lambda> n. (\<exists> a b c :: nat. a*b*c \<noteq> 0 \<and> a^2 + b^2 = c^2 \<and> a + b + c = 2*n )\<close>

section {* Auxiliary results *}

subsection {* Powers of 2 *}

text {* Tendency A *}

lemma TribPow24234qweaBBBOddTRIVIALQT:
  fixes k :: nat
  assumes \<open>d dvd ((2::nat)^(Suc k))\<close> and \<open>odd d\<close> and \<open>\<forall> d::nat. d dvd ((2::nat)^k) \<and> odd d \<longrightarrow> d = 1\<close>
  shows \<open>d = 1\<close>
proof-
  from \<open>d dvd ((2::nat)^(Suc k))\<close> have \<open>d dvd 2*((2::nat)^k)\<close> 
    by simp
  from \<open>odd d\<close> have \<open>gcd d 2 = 1\<close> 
    by (metis dvd_antisym dvd_mult_cancel2 dvd_mult_div_cancel dvd_refl even_mult_iff gcd_dvd2 gcd_nat.absorb_iff2 nat_0_less_mult_iff pos2)
  hence  \<open>d dvd ((2::nat)^k)\<close> using \<open>d dvd 2*((2::nat)^k)\<close> 
    using coprime_dvd_mult_right_iff by blast
  then  show ?thesis 
    using assms(2) assms(3) by blast
qed

lemma TribPow24234qweaBBBOddTRIVIALQ:
  fixes k :: nat
  shows \<open>\<forall> d::nat. d dvd ((2::nat)^k) \<and> odd d \<longrightarrow> d = 1\<close>
proof (induction k)
  case 0
  thus ?case 
    by simp
next
  case (Suc k)
  thus ?case 
    using TribPow24234qweaBBBOddTRIVIALQT by blast
qed

lemma TribPow24234qweaBBBOddTRIVIAL:
  fixes d k :: nat
  assumes \<open>d dvd (2^k)\<close> and \<open>odd d\<close>
  shows \<open>d = 1\<close>
  using TribPow24234qweaBBBOddTRIVIALQ assms(1) assms(2) by blast

lemma TribPow24234qweaBBBEven:
  fixes d k e:: nat
  assumes  \<open>even e\<close> and \<open>d*e = (2::nat)^(Suc k)\<close> and \<open>d \<noteq> 2^(Suc k)\<close>
  shows \<open>d dvd ((2::nat)^k)\<close>
proof-
  obtain ee :: nat where \<open>2*ee = e\<close> 
    using assms(1) by blast
  from  \<open>d*e = (2::nat)^(Suc k)\<close> have  \<open>d*e = 2*(2::nat)^k\<close>
    by simp
  from  \<open>d*e = 2*(2::nat)^k\<close> \<open>2*ee = e\<close> have \<open>d*ee = (2::nat)^k\<close> 
    by (metis Suc_mult_cancel1 numeral_2_eq_2 semiring_normalization_rules(19))
  thus ?thesis 
    by (metis dvd_triv_left)
qed

lemma TribPow24234qwea:
  fixes d k :: nat
  assumes \<open>d dvd (2::nat)^(Suc k)\<close> and  \<open>d \<noteq> 2^(Suc k)\<close>
  shows \<open>d dvd ((2::nat)^k)\<close>
  by (metis TribPow24234qweaBBBEven TribPow24234qweaBBBOddTRIVIAL assms(1) assms(2) dvd_mult_div_cancel dvd_triv_right mult_numeral_1_right numeral_One)

lemma Pow2DivLQRec:
  fixes k  d :: nat
  assumes \<open>d dvd ((2::nat)^(Suc k))\<close> and \<open>\<forall> d::nat. d dvd ((2::nat)^k) \<longrightarrow> (\<exists> j :: nat. d = (2::nat)^j)\<close>
  shows \<open>\<exists> j :: nat. d = (2::nat)^j\<close> 
proof(cases \<open>d = (2::nat)^(Suc k)\<close>)
  case True
  thus ?thesis 
    by blast
next
  case False
  hence \<open>d dvd ((2::nat)^k)\<close> using \<open>d dvd ((2::nat)^(Suc k))\<close> 
    using TribPow24234qwea by blast
  thus ?thesis 
    by (simp add: assms(2))
qed

lemma Pow2DivLQ:
  fixes k  :: nat
  shows \<open>\<forall> d::nat. d dvd ((2::nat)^k) \<longrightarrow> (\<exists> j :: nat. d = (2::nat)^j)\<close>
proof (induction k)
  case 0
  thus ?case 
    by (metis nat_dvd_1_iff_1 power_0)
next
  case (Suc k)
  thus ?case 
    using Pow2DivLQRec by blast
qed

lemma Pow2DivL:
  fixes k d :: nat
  assumes \<open>d dvd ((2::nat)^k)\<close>
  shows \<open>\<exists> j :: nat. d = (2::nat)^j\<close>
  using Pow2DivLQ assms by blast


lemma Pow2DivIndRecSTrivial:
  fixes k u :: nat
  assumes  \<open>ConsecDiv (2^(Suc k)) u (2^(Suc k))\<close>
  shows \<open>u = 2^k\<close>
  by (metis ConsecDiv_def Pow2DivL add_cancel_left_left antisym_conv assms dvd_imp_le dvd_triv_right le_imp_power_dvd mult_2 nat_dvd_not_less not_less_eq_eq pos2 power.simps(2) zero_less_power)


lemma Pow2DivIndRecSTrivial2:
  fixes k u :: nat
  assumes  \<open>ConsecDiv (2^(Suc k)) u v\<close> and \<open>\<not> (v = (2^(Suc k)))\<close>
  shows \<open>ConsecDiv (2^k) u v\<close>
proof-
  from \<open>ConsecDiv (2^(Suc k)) u v\<close> have \<open>u dvd (2^(Suc k))\<close> 
    by (simp add: ConsecDiv_def)
  from \<open>ConsecDiv (2^(Suc k)) u v\<close> have \<open>ConsecDiv (2^(Suc k)) u v\<close> 
    by blast
  from \<open>ConsecDiv (2^(Suc k)) u v\<close> have  \<open>v dvd (2^(Suc k))\<close> 
    by (simp add: ConsecDiv_def)
  from \<open>ConsecDiv (2^(Suc k)) u v\<close> have  \<open>u < v\<close> 
    by (simp add: ConsecDiv_def)
  from \<open>ConsecDiv (2^(Suc k)) u v\<close> have \<open>\<forall> d:: nat. d dvd (2^(Suc k)) \<longrightarrow> d \<le> u \<or> v \<le> d \<close>
    by (simp add: ConsecDiv_def)
  then   have \<open>\<forall> d:: nat. d dvd (2^(Suc k)) \<and> (d \<noteq> 2^(Suc k) ) \<longrightarrow> d \<le> u \<or> v \<le> d \<close>
    by blast
  hence \<open>\<forall> d:: nat. d dvd (2^k) \<longrightarrow> d \<le> u \<or> v \<le> d \<close> 
    by (simp add: \<open>\<forall>d. d dvd 2 ^ Suc k \<longrightarrow> d \<le> u \<or> v \<le> d\<close>)
  have \<open>u dvd (2^( k))\<close> 
    by (metis Pow2DivL \<open>u < v\<close> \<open>u dvd 2 ^ Suc k\<close> \<open>v dvd 2 ^ Suc k\<close> dvd_antisym dvd_power_le even_numeral  nat_dvd_not_less not_less_eq_eq zero_less_numeral zero_less_power)
  have \<open>v dvd (2^( k))\<close> 
    by (metis Pow2DivL \<open>v dvd 2 ^ Suc k\<close> assms(2) dvd_antisym le_imp_power_dvd not_less_eq_eq)
  show ?thesis 
    by (simp add: ConsecDiv_def \<open>\<forall>d. d dvd 2 ^ k \<longrightarrow> d \<le> u \<or> v \<le> d\<close> \<open>u < v\<close> \<open>u dvd 2 ^ k\<close> \<open>v dvd 2 ^ k\<close>)
qed


lemma Pow2DivIndRecS:
  fixes k :: nat
  assumes \<open>( \<forall> u v. ConsecDiv (2^k) u v \<longrightarrow> v = 2*u)\<close> 
    and \<open>ConsecDiv (2^(Suc k)) u v\<close>
  shows \<open>v = 2*u\<close>
proof (cases \<open>v = 2^(Suc k)\<close>)
  case True
  thus ?thesis 
    using Pow2DivIndRecSTrivial assms(2) power_Suc by blast
next
  case False
  thus ?thesis 
    using Pow2DivIndRecSTrivial2 assms(1) assms(2) by blast
qed

lemma Pow2DivInd:
  fixes k :: nat
  shows \<open>( \<forall> u v. ConsecDiv (2^k) u v \<longrightarrow> v = 2*u)\<close>
proof(induction k)
  case 0
  thus ?case 
    by (simp add: ConsecDiv_def)
next
  case (Suc k)
  thus ?case 
    using Pow2DivIndRecS by blast
qed

lemma Pow2DivS:
  fixes k :: nat
  shows \<open>( \<forall> u v. ConsecDiv (2^k) u v \<longrightarrow> v = 2*u)\<close>
  by (simp add: Pow2DivInd)

lemma Pow2Div:
  fixes n :: nat
  assumes \<open>n \<ge> 1\<close> and \<open>\<exists> k :: nat. n = 2^k\<close>
  shows \<open>( \<forall> u v. ConsecDiv n u v \<longrightarrow> v = 2*u)\<close>
  using Pow2DivS assms(2) by blast

text {* Tendency B *}

fun powOP :: \<open>(nat \<Rightarrow> nat) \<Rightarrow> nat \<Rightarrow> nat\<close> where
  \<open>powOP f 0 = 1\<close>
| \<open>powOP f (Suc n) = f (powOP f n)\<close>


lemma Pow2DivConvOddTRGenY1:
  fixes j n :: nat and  x f :: \<open>nat \<Rightarrow> nat\<close>
  assumes \<open>x \<equiv> powOP f\<close> \<open>v \<ge> 2\<close> \<open>v dvd n\<close> \<open>\<forall> d :: nat.  ( d dvd n \<and> d < v \<longrightarrow> ( (f d) dvd n \<and> d < (f d) \<and> (f d) < v ) )\<close>
  shows \<open> (x j) dvd n \<and> x j < v\<close>
proof(induction j)
  case 0
  thus ?case 
    using assms(1) assms(2) by auto
next
  case (Suc j)
  have \<open>x (Suc j) = f (x j)\<close> 
    by (simp add: assms(1))
  have \<open>(x j) dvd n\<close> 
    by (simp add: Suc.IH)
  have \<open>(x j) < v\<close> 
    by (simp add: Suc.IH)
  have \<open>(f (x j)) dvd n\<close> 
    using Suc.IH assms(4) by blast
  have \<open>f (x j) < v\<close> 
    by (simp add: Suc.IH assms(4)) 
  show ?case 
    by (simp add: \<open>f (x j) < v\<close> \<open>f (x j) dvd n\<close> \<open>x (Suc j) = f (x j)\<close>)
qed

lemma Pow2DivConvOddTRGenX1:
  fixes j n :: nat and  x f :: \<open>nat \<Rightarrow> nat\<close>
  assumes \<open>x \<equiv> powOP f\<close> \<open>v \<ge> 2\<close> \<open>v dvd n\<close> \<open>\<forall> d :: nat.  ( d dvd n \<and> d < v \<longrightarrow> ( (f d) dvd n \<and> d < (f d) \<and> (f d) < v ) )\<close>
  shows \<open> x j > j\<close>
proof(induction j)
  case 0
  thus ?case 
    by (simp add: assms(1))
next
  case (Suc j)
  thus ?case 
    using Pow2DivConvOddTRGenY1 assms(1) assms(2) assms(3) assms(4) less_trans_Suc powOP.simps(2) by presburger
qed

lemma Pow2DivConvOddTRGenX:
  fixes n :: nat and  x f :: \<open>nat \<Rightarrow> nat\<close>
  assumes \<open>x \<equiv> powOP f\<close> \<open>v \<ge> 2\<close> \<open>v dvd n\<close> \<open>\<forall> d :: nat.  ( d dvd n \<and> d < v \<longrightarrow> ( (f d) dvd n \<and> d < (f d) \<and> (f d) < v ) )\<close>
  shows \<open>\<forall> j :: nat. x j > j\<close>
  using Pow2DivConvOddTRGenX1 assms(1) assms(2) assms(3) assms(4) by blast

lemma Pow2DivConvOddTRGenY:
  fixes n :: nat and  x f :: \<open>nat \<Rightarrow> nat\<close>
  assumes \<open>x \<equiv> powOP f\<close> \<open>v \<ge> 2\<close> \<open>v dvd n\<close> \<open>\<forall> d :: nat.  ( d dvd n \<and> d < v \<longrightarrow> ( (f d) dvd n \<and> d < (f d) \<and> (f d) < v ) )\<close>
  shows \<open>\<forall> j :: nat. (x j) dvd n\<close>
  using Pow2DivConvOddTRGenY1 assms(1) assms(2) assms(3) assms(4) by blast

lemma Pow2DivConvOddTRGen:
  fixes n :: nat
  assumes \<open>v \<ge> 2\<close> \<open>v dvd n\<close>
  shows \<open>\<exists> u :: nat. ConsecDiv n u v\<close>
proof (rule classical)
  assume \<open>\<not> ( \<exists> u :: nat. ConsecDiv n u v )\<close>
  hence \<open>\<forall> u :: nat. \<not> (ConsecDiv n u v)\<close> 
    by auto
  hence \<open>\<forall> d :: nat. d dvd n \<and> d < v \<longrightarrow> (\<exists> e :: nat. e dvd n \<and> d < e \<and> e < v )\<close>
    by (meson ConsecDiv_def assms(2) not_less)
  hence \<open>\<forall> d :: nat. \<exists> e :: nat. ( d dvd n \<and> d < v \<longrightarrow> ( e dvd n \<and> d < e \<and> e < v ) )\<close>
    by blast
  from \<open>\<forall> d :: nat. \<exists> e :: nat. ( d dvd n \<and> d < v \<longrightarrow> ( e dvd n \<and> d < e \<and> e < v ) )\<close>
  obtain f :: \<open>nat \<Rightarrow> nat\<close> where \<open>\<forall> d :: nat.  ( d dvd n \<and> d < v \<longrightarrow> ( (f d) dvd n \<and> d < (f d) \<and> (f d) < v ) )\<close>
    by metis
  obtain x :: \<open>nat \<Rightarrow> nat\<close> where  \<open>x \<equiv> powOP f\<close> 
    by simp
  have \<open>x n > n\<close> using Pow2DivConvOddTRGenX 
    using \<open>\<forall>d. d dvd n \<and> d < v \<longrightarrow> f d dvd n \<and> d < f d \<and> f d < v\<close> \<open>x \<equiv> powOP f\<close> assms(1) assms(2) by blast
  hence \<open>(x n) dvd n\<close> 
    using Pow2DivConvOddTRGenY \<open>\<forall>d. d dvd n \<and> d < v \<longrightarrow> f d dvd n \<and> d < f d \<and> f d < v\<close> \<open>x \<equiv> powOP f\<close> assms(1) assms(2) by auto
  have False 
    by (metis  Suc_leI  \<open>\<forall>d. d dvd n \<and> d < v \<longrightarrow> (\<exists>e. e dvd n \<and> d < e \<and> e < v)\<close> \<open>n < x n\<close> \<open>x n dvd n\<close> assms(1) dvd_triv_left gr0I      less_or_eq_imp_le less_trans_Suc  mult_is_0 nat_dvd_not_less  not_le not_less_eq_eq numerals(2) old.nat.exhaust)
  thus ?thesis 
    by blast
qed


lemma Pow2DivConv:
  fixes n :: nat
  assumes \<open>n \<ge> 1\<close> and \<open>( \<forall> u v. ConsecDiv n u v \<longrightarrow> v = 2*u)\<close>
  shows  \<open>\<exists> k :: nat. n = 2^k\<close>
  by (metis Pow2DivConvOddTRGen Pow2Odd assms(1) assms(2) dvd_def)


subsection {* Divisor-repulsion *}

lemma DivisorRepulsionPyth1:
  fixes n :: nat
  assumes \<open>n \<ge> 1\<close> and \<open>\<exists> u v. ConsecDiv n u v \<and> v < 2*u\<close> 
  shows \<open>SemiPeriPytha n\<close>
proof-
  obtain u v :: nat where \<open>ConsecDiv n u v\<close> and \<open>v < 2*u\<close> 
    using assms(2) by blast
  from \<open>ConsecDiv n u v\<close> have \<open>u dvd n\<close> 
    by (simp add: ConsecDiv_def)
  from \<open>ConsecDiv n u v\<close> have \<open>v dvd n\<close> 
    by (simp add: ConsecDiv_def)
  from \<open>ConsecDiv n u v\<close> have \<open>u < v\<close> 
    by (simp add: ConsecDiv_def)
  from  \<open>u dvd n\<close>  \<open>v dvd n\<close>  \<open>u < v\<close> \<open>v < 2*u\<close> show ?thesis 
    using ShortDivToPeriPyth 
    by (smt SemiPeriPytha_def add_gr_0 assms(1) le_numeral_extra(2) mult_is_0 neq0_conv power_eq_0_iff)
qed

lemma DivisorRepulsionPyth:
  fixes n :: nat
  assumes \<open>n \<ge> 1\<close> and \<open>\<not>(SemiPeriPytha n)\<close>
  shows \<open>( \<forall> u v. ConsecDiv n u v \<longrightarrow> v \<ge> 2*u)\<close>
  by (meson DivisorRepulsionPyth1 assms(1) assms(2) not_less)


lemma DivisorRepulsionPythConverse1:
  fixes n :: nat
  assumes \<open>n \<ge> 1\<close> and \<open>SemiPeriPytha n\<close>
  shows \<open> \<exists> u v. ConsecDiv n u v \<and> v < 2*u\<close>
proof-
  from \<open>SemiPeriPytha n\<close> obtain a b c :: nat where
    \<open>a * b * c \<noteq> 0\<close> and \<open>a^2 + b^2 = c^2\<close> and \<open>2*n = a + b + c\<close>
    by (metis SemiPeriPytha_def)
  from \<open>a * b * c \<noteq> 0\<close> have  \<open>a \<noteq> 0\<close> by simp
  from \<open>a * b * c \<noteq> 0\<close> have  \<open>b \<noteq> 0\<close> by simp
  from \<open>a * b * c \<noteq> 0\<close> have  \<open>c \<noteq> 0\<close> by simp
  from \<open>n \<ge> 1\<close> and  \<open>a \<noteq> 0\<close> and  \<open>b \<noteq> 0\<close> and  \<open>c \<noteq> 0\<close> and \<open>a^2 + b^2 = c^2\<close> and \<open>2*n = a + b + c\<close>
  have \<open>\<exists> d e. d dvd n \<and> e dvd n \<and> d < e \<and> e < 2*d\<close>
    using PeriPythToShortDiv 
    by (metis le_numeral_extra(2))
  then obtain d e :: nat where \<open>d dvd n\<close> and \<open>e dvd n\<close> 
    and \<open>d < e\<close> and \<open>e < 2*d\<close> 
    by blast
  from \<open>d dvd n\<close>  \<open>e dvd n\<close>  \<open>d < e\<close> 
  obtain u :: nat where \<open>ConsecDiv n u e\<close>
    by (metis Pow2DivConvOddTRGen Suc_leI assms(1) dvd_pos_nat less_le_trans not_less_eq numerals(2) zero_less_one)
  from \<open>ConsecDiv n u e\<close> \<open>d < e\<close> \<open>d dvd n\<close> have \<open>d \<le> u\<close> 
    by (meson ConsecDiv_def leD)
  hence \<open>e < 2*u\<close> using \<open>e < 2*d\<close> 
    by linarith
  show ?thesis 
    using \<open>ConsecDiv n u e\<close> \<open>e < 2 * u\<close> by blast
qed


lemma DivisorRepulsionPythConverse:
  fixes n :: nat
  assumes \<open>n \<ge> 1\<close> and \<open>( \<forall> u v. ConsecDiv n u v \<longrightarrow> v \<ge> 2*u)\<close> 
  shows \<open>\<not>(SemiPeriPytha n)\<close>
  using DivisorRepulsionPythConverse1 assms(1) assms(2) le_less_trans by blast



subsection {* Analysis of the original statement *}

lemma twoDNotDSemiPeriPythaPow2:
  fixes n :: nat
  assumes \<open>n \<ge> 1\<close> and \<open>\<not>(SemiPeriPytha n)\<close> and \<open>TwoDD n\<close>
  shows \<open>\<exists> k :: nat. n = 2^k\<close>
  by (meson DivisorRepulsionPyth Pow2DivConv TwoDD_def assms(1) assms(2) assms(3) dual_order.antisym)

lemma Pow2twoDNotDSemiPeriPytha:
  fixes n :: nat
  assumes \<open>n \<ge> 1\<close> \<open>\<exists> k :: nat. n = 2^k\<close>
  shows  \<open>\<not>(SemiPeriPytha n) \<and> TwoDD n\<close> 
  by (metis DivisorRepulsionPythConverse Pow2Div TwoDD_def assms(1) assms(2) order_refl)

lemma Pow2CharacterizationONLYIF:
  \<open>\<forall> n::nat. n \<ge> 1 \<longrightarrow>((\<exists> k :: nat. n = 2^k) \<longrightarrow> TwoDD n \<and> \<not>(SemiPeriPytha n)) \<close>
  using Pow2twoDNotDSemiPeriPytha by blast

lemma Pow2CharacterizationIF:
  \<open>\<forall> n::nat. n \<ge> 1 \<longrightarrow> (TwoDD n \<and> \<not>(SemiPeriPytha n) \<longrightarrow> (\<exists> k :: nat. n = 2^k))\<close>
  by (simp add: twoDNotDSemiPeriPythaPow2)

section {* Main results *}

theorem Pow2Characterization:
  \<open>\<forall> n::nat. n \<ge> 1 \<longrightarrow> ( (\<exists> k :: nat. n = 2^k) \<longleftrightarrow> TwoDD n \<and> \<not>(SemiPeriPytha n) ) \<close>
  using Pow2CharacterizationIF Pow2CharacterizationONLYIF by blast

end
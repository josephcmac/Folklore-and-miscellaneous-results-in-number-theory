(*
Title: Perfect Powers
Author: Jose Manuel Rodriguez Caballero

A perfect power is a natural number of the form u^v, with u \<ge> 2 and v \<ge> 2.

We will prove that any natural number n \<ge> 2 can be expressed as n = u^v, 
where u \<ge> 2, v \<ge> 1 and u is not perfect power. Furthermore, we will prove that such
a representation is unique.This result belongs to the mathematical folklore.

(This code  was verified in Isabelle2018-RC4/HOL)

*)

theory PerfectPowers

imports Complex_Main


begin

text {* Definition of perfect powers *}
definition PerfectPower :: "nat \<Rightarrow> bool" where
"PerfectPower \<equiv> \<lambda> n. (\<exists> u v::nat. n = u^v \<and> u \<ge> 2 \<and> v \<ge> 2)"



section {* Existence of the representation *}


lemma PPRepresentationBaseAux :
  shows \<open> \<not>(PerfectPower 2)\<close>
  by (metis (mono_tags, hide_lams) One_nat_def PerfectPower_def lessI less_le_trans linorder_not_le numerals(2) power_le_imp_le_exp power_one_right)

lemma PPRepresentationBase :
  shows \<open>\<exists> u v::nat. 2 = u^v \<and> u \<ge> 2 \<and> v \<ge> 1 \<and> \<not>(PerfectPower u)\<close>
  using PPRepresentationBaseAux by force

lemma PPRepresentationRefKInd :
  fixes K :: nat
  shows \<open>(\<forall> k.  (k < K \<longrightarrow> ( \<exists> u v::nat. k+2 = u^v \<and> u \<ge> 2 \<and> v \<ge> 1 \<and> \<not>(PerfectPower u)) )) \<Longrightarrow> ( \<exists> u v::nat. K+2 = u^v \<and> u \<ge> 2 \<and> v \<ge> 1 \<and> \<not>(PerfectPower u)) \<close>
proof (cases \<open>PerfectPower (K+2)\<close>)
  case True
then obtain u v :: nat where \<open>K+2 = u^v\<close> and \<open>u \<ge> 2\<close> and \<open>v \<ge> 2\<close> 
  by (meson PerfectPower_def)
  from  \<open>K+2 = u^v\<close> and \<open>u \<ge> 2\<close> and \<open>v \<ge> 2\<close> have \<open>u < K+2\<close> 
    by (metis add_leD2 le_neq_implies_less numeral_le_one_iff one_add_one power_increasing_iff power_one_right semiring_norm(69))
  from \<open>u \<ge> 2\<close> obtain j :: nat where \<open>u = j + 2\<close> 
    by (metis add_2_eq_Suc add_2_eq_Suc'  le_Suc_ex )
  assume \<open>(\<forall> k.  (k < K \<longrightarrow> ( \<exists> u v::nat. k+2 = u^v \<and> u \<ge> 2 \<and> v \<ge> 1 \<and> \<not>(PerfectPower u)))) \<close>
  then obtain p q :: nat  where \<open>u = p^q\<close> and \<open>p \<ge> 2\<close> and \<open>q \<ge> 1\<close> and \<open> \<not>(PerfectPower p)\<close> 
    using \<open>u < K + 2\<close> \<open>u = j + 2\<close> by auto
  obtain s ::nat where \<open>s = q * v\<close> by auto
  from  \<open>K+2 = u^v\<close> and \<open>u = p^q\<close> have  \<open>K+2 = (p^q)^v\<close> 
    by blast
   then have \<open>K+2 = p^s\<close> using  \<open>s = q * v\<close>
  by (simp add: semiring_normalization_rules(31))
  have \<open>( \<exists> u v::nat. K+2 = u^v \<and> u \<ge> 2 \<and> v \<ge> 1 \<and> \<not>(PerfectPower u))\<close> 
    using \<open>1 \<le> q\<close> \<open>2 \<le> p\<close> \<open>2 \<le> v\<close> \<open>K + 2 = p ^ s\<close> \<open>\<not> PerfectPower p\<close> \<open>s = q * v\<close> by fastforce
  show ?thesis 
    using \<open>\<exists>u v. K + 2 = u ^ v \<and> 2 \<le> u \<and> 1 \<le> v \<and> \<not> PerfectPower u\<close> by blast
next
  case False
  then show ?thesis 
    by (metis le_add2 le_numeral_extra(4) power_one_right)
qed

lemma PPRepresentationRefK :
  fixes K :: nat
  shows \<open>\<forall> k. (k < K \<longrightarrow> ( \<exists> u v::nat. k+2 = u^v \<and> u \<ge> 2 \<and> v \<ge> 1 \<and> \<not>(PerfectPower u)) )\<close>
  proof (induction K)
case 0
  then show ?case 
    using PPRepresentationBase by force
next
  case (Suc K)
  then show ?case 
    using PPRepresentationRefKInd by auto
  qed

lemma PPRepresentationRef :
  fixes k :: nat
  shows \<open>\<exists> u v::nat. k+2 = u^v \<and> u \<ge> 2 \<and> v \<ge> 1 \<and> \<not>(PerfectPower u)\<close>
  using PPRepresentationRefK by blast

theorem PPRepresentation :
  fixes n :: nat
  assumes \<open>n \<ge> 2\<close>
  shows \<open>\<exists> u v::nat. n = u^v \<and> u \<ge> 2 \<and> v \<ge> 1 \<and> \<not>(PerfectPower u)\<close>
proof-
  from  \<open>n \<ge> 2\<close> obtain k::nat where \<open>n = 2 + k\<close> 
    using le_Suc_ex by blast
  from \<open>n = 2 + k\<close> show ?thesis 
    using PPRepresentationRef by auto
qed

section {* Uniqueness of the representation *}


lemma PowReg1:
  fixes a b c p :: nat
  assumes \<open> a \<ge> 2\<close> and \<open>b \<ge> 2\<close> and \<open>c \<ge> 2\<close> and \<open>p \<ge> 1\<close> and \<open>a^p = b^p * c\<close>
  shows \<open>b dvd a\<close>
  by (metis assms(4) assms(5) dvd_triv_left gr0I  le_zero_eq  less_numeral_extra(1) pow_divides_pow_iff)

lemma PowReg:
  fixes a b c p :: nat
  assumes \<open> a \<ge> 2\<close> and \<open>b \<ge> 2\<close> and \<open>c \<ge> 2\<close> and \<open>p \<ge> 1\<close> and \<open>a^p = b^p * c\<close>
  shows \<open>\<exists> k::nat. c = k^p\<close>
proof-
  have \<open>b dvd a\<close> 
    using PowReg1 assms(1) assms(2) assms(3) assms(4) assms(5) by blast
  obtain k :: nat where \<open>b*k = a\<close> 
    using \<open>b dvd a\<close> dvdE by blast
  from  \<open>a^p = b^p * c\<close> have  \<open>b^p*k^p = b^p * c\<close> 
    by (metis \<open>b * k = a\<close> power_mult_distrib)
  then show ?thesis
    using assms(2) by auto
qed

lemma nonPerfectPowerChar : \<open>(n::nat) \<ge> 2 \<Longrightarrow> \<not>(PerfectPower n) \<Longrightarrow>  n = u^v \<Longrightarrow> v = 1 \<close>
proof-
  assume \<open>n \<ge> 2\<close>
  assume \<open>\<not>(PerfectPower n)\<close>
  then have \<open>\<not> (\<exists> u v::nat. n = u^v \<and> u \<ge> 2 \<and> v \<ge> 2)\<close> 
    by (meson PerfectPower_def)
  then have \<open>\<forall> u v::nat. n \<noteq> u^v \<or> u \<le> 1 \<or> v \<le> 1\<close> 
    by (simp add: not_less_eq_eq)
  assume \<open> n = u^v \<close>
  from  \<open> n = u^v \<close>  \<open>\<forall> u v::nat. n \<noteq> u^v \<or> u \<le> 1 \<or> v \<le> 1\<close>  have \<open> u \<le> 1 \<or> v \<le> 1\<close> 
    by blast
  from  \<open> n = u^v \<close> \<open>n \<ge> 2\<close> have \<open>u > 1\<close> 
    by (metis One_nat_def Suc_leI add_leD2 dual_order.strict_trans1 le_neq_implies_less less_numeral_extra(4) nat_zero_less_power_iff one_add_one one_less_numeral_iff power_0 power_one semiring_norm(76))
  from  \<open> u \<le> 1 \<or> v \<le> 1\<close>   \<open>u > 1\<close> have \<open>v \<le> 1\<close> 
    using not_le by blast
  from  \<open> n = u^v \<close> \<open>n \<ge> 2\<close> have \<open>v \<noteq> 0 \<close> 
    by (metis One_nat_def nat_power_eq_Suc_0_iff numeral_le_one_iff semiring_norm(69))
  from \<open>v \<noteq> 0 \<close>   \<open>v \<le> 1\<close>  have \<open>v = 1\<close> 
    using le_neq_implies_less by blast
  then show ?thesis 
    by blast
qed


lemma BezoutNat:
  fixes x y:: nat
  assumes \<open>x > y\<close> and \<open>gcd x y = 1\<close>
  shows \<open>\<exists> a b::nat. a*x = b*y + 1\<close>
  by (metis assms(1) assms(2) bezout_nat gr_implies_not0 semiring_normalization_rules(7))

lemma PPUniquenessRelPrimesRedEqOne :
  fixes n u v p q :: nat
  assumes \<open>n \<ge> 2\<close> and \<open>n = u^v\<close> and \<open>u \<ge> 2\<close> and \<open>v \<ge> 1\<close> and \<open>\<not>(PerfectPower u)\<close>
and  \<open>n = p^q\<close> and \<open>p \<ge> 2\<close> and \<open>q \<ge> 1\<close> and \<open>\<not>(PerfectPower p)\<close> and \<open>gcd q v = 1\<close> and \<open>q > v\<close>
  shows \<open> v = 1\<close>
proof-
  from \<open>gcd q v = 1\<close> obtain a b :: nat where \<open>a*q = b*v + 1\<close>
    using BezoutNat assms(11) by presburger
  from \<open>n = u^v\<close>  \<open>n = p^q\<close> have \<open>u^v = p^q\<close>
    by blast
  then have \<open>u^(a*v) = p^(a*q)\<close> 
    by (metis mult.commute semiring_normalization_rules(31))
  then have \<open>u^(a*v) = p^(b*v + 1)\<close> 
    by (simp add: \<open>a * q = b * v + 1\<close>)
  then have  \<open>(u^a)^v = (p^b)^v * p\<close> 
    by (simp add: semiring_normalization_rules(31))
  then obtain X Y :: nat where  \<open>X = u^a\<close> and  \<open>Y = p^b\<close> 
    by simp
  from  \<open>X = u^a\<close> \<open>Y = p^b\<close>  \<open>(u^a)^v = (p^b)^v * p\<close>   have \<open>X^v = Y^v * p\<close> 
    by blast
  have \<open>X \<ge> 2\<close> 
    by (metis One_nat_def Suc_leI \<open>(u ^ a) ^ v = (p ^ b) ^ v * p\<close> \<open>X = u ^ a\<close> add_leD2 assms(3) assms(7) le_neq_implies_less nat_1_eq_mult_iff nat_one_le_power numerals(2) one_add_one power_one)
  have \<open>Y \<ge> 2\<close>
    by (metis Groups.mult_ac(2) One_nat_def PerfectPower_def Suc_leI \<open>(u ^ a) ^ v = (p ^ b) ^ v * p\<close> \<open>2 \<le> X\<close> \<open>X = u ^ a\<close> \<open>Y = p ^ b\<close> add_leD2 assms(11) assms(2) assms(4) assms(5) assms(6) assms(7) assms(9) mult_1_right nat_less_le nat_one_le_power numerals(2) one_add_one power_one power_one_right)
  from \<open>X \<ge> 2\<close>  \<open>Y \<ge> 2\<close> \<open>v \<ge> 1\<close> \<open>X^v = Y^v * p\<close> obtain k::nat where \<open>p = k^v\<close> 
    using PowReg assms(7) by blast
  from  \<open>p \<ge> 2\<close> \<open>p = k^v\<close> show ?thesis 
    using assms(9) nonPerfectPowerChar by blast
qed

lemma PPUniquenessRelPrimesRed :
  fixes n u v p q :: nat
  assumes \<open>n \<ge> 2\<close> and \<open>n = u^v\<close> and \<open>u \<ge> 2\<close> and \<open>v \<ge> 1\<close> and \<open>\<not>(PerfectPower u)\<close>
and  \<open>n = p^q\<close> and \<open>p \<ge> 2\<close> and \<open>q \<ge> 1\<close> and \<open>\<not>(PerfectPower p)\<close> and \<open>gcd q v = 1\<close> and \<open>q > v\<close>
  shows \<open>u = p \<and> v = q\<close>
  by (metis PPUniquenessRelPrimesRedEqOne assms(1) assms(10) assms(11) assms(2) assms(3) assms(4) assms(5) assms(6) assms(7) assms(8) assms(9) nonPerfectPowerChar power_one_right)

lemma PPUniquenessRelPrimes :
  fixes n u v p q :: nat
  assumes \<open>n \<ge> 2\<close> and \<open>n = u^v\<close> and \<open>u \<ge> 2\<close> and \<open>v \<ge> 1\<close> and \<open>\<not>(PerfectPower u)\<close>
and  \<open>n = p^q\<close> and \<open>p \<ge> 2\<close> and \<open>q \<ge> 1\<close> and \<open>\<not>(PerfectPower p)\<close> and \<open>gcd q v = 1\<close>
  shows \<open>u = p \<and> v = q\<close>
  by (metis PPUniquenessRelPrimesRed assms(1) assms(10) assms(2) assms(3) assms(4) assms(5) assms(6) assms(7) assms(8) assms(9) gcd.commute gcd_nat.idem nat_neq_iff power_one_right)

theorem PPUniqueness :
  fixes n u v p q :: nat
  assumes \<open>n \<ge> 2\<close> and \<open>n = u^v\<close> and \<open>u \<ge> 2\<close> and \<open>v \<ge> 1\<close> and \<open>\<not>(PerfectPower u)\<close>
and  \<open>n = p^q\<close> and \<open>p \<ge> 2\<close> and \<open>q \<ge> 1\<close> and \<open>\<not>(PerfectPower p)\<close>
  shows \<open>u = p \<and> v = q\<close>
proof-
  obtain d :: nat where \<open>gcd q v = d\<close> by auto
  from  \<open>gcd q v = d\<close> obtain qq :: nat where \<open> qq * d = q \<close> 
    by (metis assms(8) gcd_coprime_exists gcd_eq_0_iff le_numeral_extra(2))
  from  \<open>gcd q v = d\<close> obtain vv :: nat where \<open> vv * d = v \<close> 
    by (metis assms(4) gcd_coprime_exists gcd_eq_0_iff less_le_trans less_numeral_extra(3) zero_less_one)
  from  \<open>gcd q v = d\<close> and  \<open> qq * d = q \<close>  and  \<open> vv * d = v \<close>  have \<open>gcd qq vv = 1\<close>
  proof -
    have "d * gcd qq vv dvd d"
      by (metis (no_types) \<open>gcd q v = d\<close> \<open>qq * d = q\<close> \<open>vv * d = v\<close> dvd_refl gcd_mult_distrib_nat semiring_normalization_rules(7))
    then show ?thesis
      by (metis (no_types) \<open>qq * d = q\<close> assms(8) dvd_mult_cancel2 gcd.bottom_left_bottom le_less_trans nat_0_less_mult_iff nat_mult_eq_1_iff order.not_eq_order_implies_strict semiring_normalization_rules(7) zero_le)
  qed

  from \<open>n = p^q\<close> and \<open>n = u^v\<close> have \<open>p^q = u^v\<close>
    by blast
  from \<open>p^q = u^v\<close> and  \<open> qq * d = q \<close> and  \<open> vv * d = v \<close> have \<open>p^qq = u^vv\<close> 
    by (smt assms(4) dual_order.strict_implies_order dual_order.strict_trans1 less_numeral_extra(1) nat_0_less_mult_iff not_gr_zero power_eq_0_iff power_eq_iff_eq_base semiring_normalization_rules(31))
  have  \<open>vv \<ge> 1\<close> 
    using \<open>vv * d = v\<close> assms(4) by auto
  have  \<open>qq \<ge> 1\<close> 
    using \<open>qq * d = q\<close> assms(8) by auto
  obtain nn where \<open>nn = u^vv\<close> 
    by simp
  have  \<open>nn = p^qq\<close> 
    by (simp add: \<open>nn = u ^ vv\<close> \<open>p ^ qq = u ^ vv\<close>)
  have  \<open>nn \<ge> 2\<close> 
    by (metis One_nat_def \<open>nn = p ^ qq\<close> \<open>qq * d = q\<close> add_leD2 antisym_conv assms(1) assms(6) assms(7) nat_one_le_power not_less_eq_eq numerals(2) one_add_one power_one semiring_normalization_rules(31))
  from  \<open>nn \<ge> 2\<close> and \<open>nn = u^vv\<close> and \<open>u \<ge> 2\<close> and \<open>vv \<ge> 1\<close> and \<open>\<not>(PerfectPower u)\<close>
and  \<open>nn = p^qq\<close> and \<open>p \<ge> 2\<close> and \<open>qq \<ge> 1\<close> and \<open>\<not>(PerfectPower p)\<close> and \<open>gcd qq vv = 1\<close>
  have  \<open>u = p \<and> vv = qq\<close> 
    by (meson PPUniquenessRelPrimes)
  show ?thesis
    using \<open>qq * d = q\<close> \<open>u = p \<and> vv = qq\<close> \<open>vv * d = v\<close> by blast
qed

end


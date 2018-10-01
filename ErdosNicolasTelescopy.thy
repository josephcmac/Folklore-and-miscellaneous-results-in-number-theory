(*
Title: The Erdos-Nicolas function as a difference of two counting functions
Author: Jose Manuel Rodriguez Caballero

We define the function 


definition OddDivBound :: \<open>nat \<Rightarrow> real \<Rightarrow> nat\<close> where
\<open>OddDivBound \<equiv> \<lambda> n::nat. \<lambda> x::real. (card {d | d :: nat. d dvd n \<and> odd d \<and> (d::real) \<le> x })\<close>

and we prove the identity

theorem ErdosNicolasSetOddDivBound:
  fixes n k m d :: nat
  assumes \<open>n = (2::nat)^k*m\<close> and \<open>odd m\<close> and \<open>d dvd n\<close> and \<open>odd d\<close> 
  shows \<open>card (ErdosNicolasSet n d) = (card (OddDivBound n (d::real))) - (card (OddDivBound n ((d::real)/(2::real)^(k+1))))\<close>


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

@article{erdos1976methodes,
  title={M{\'e}thodes probabilistes et combinatoires en th{\'e}orie des nombres},
  author={Erdos, Paul and Nicolas, Jean-Louis},
  journal={Bull. Sci. Math},
  volume={2},
  number={100},
  pages={301--320},
  year={1976}
}

(This code  was verified in Isabelle2018)

*)


theory ErdosNicolasTelescopy

imports Complex_Main ErdosNicolasOdd PowOfTwo

begin


definition OddDivBound :: \<open>nat \<Rightarrow> real \<Rightarrow> nat set\<close> where
\<open>OddDivBound \<equiv> \<lambda> n::nat. \<lambda> x::real.  {d | d :: nat. d dvd n \<and> odd d \<and> d \<le> x }\<close>

section {* Minimum of a set of natural numbers *}

section {* Auxiliary Results *}

lemma ErdosNicolasSetOddDivBoundLInter:
  fixes n k m d :: nat
  assumes \<open>n = (2::nat)^k*m\<close> and \<open>odd m\<close> and \<open>d dvd n\<close> and \<open>odd d\<close> 
  shows \<open> (ErdosNicolasSet n d) \<inter> (OddDivBound n ((d::real)/(2::real)^(k+1))) = {}\<close>
proof(rule classical)
  assume \<open>\<not> (  (ErdosNicolasSet n d) \<inter> (OddDivBound n ((d::real)/(2::real)^(k+1))) = {} )\<close>
  then have  \<open>(ErdosNicolasSet n d) \<inter> (OddDivBound n ((d::real)/(2::real)^(k+1))) \<noteq> {}\<close>
    by simp
  then obtain x where \<open>x \<in> (ErdosNicolasSet n d) \<inter> (OddDivBound n ((d::real)/(2::real)^(k+1)))\<close>
    by blast
  then have \<open>x \<in> ErdosNicolasSet n d\<close>
    by blast
  from  \<open>x \<in> (ErdosNicolasSet n d) \<inter> (OddDivBound n ((d::real)/(2::real)^(k+1)))\<close>
  have \<open>x \<in> OddDivBound n ((d::real)/(2::real)^(k+1))\<close> 
    by blast
  from  \<open>x \<in> ErdosNicolasSet n d\<close> have \<open>(d::real)/(2::real) < x\<close> 
    using CollectD ErdosNicolasSet_def by fastforce
  from \<open>x \<in> (OddDivBound n ((d::real)/(2::real)^(k+1)))\<close> have \<open>x \<le> (d::real)/(2::real)^(k+1)\<close>
    using CollectD OddDivBound_def by fastforce
  have \<open>(2::real)^1 \<le> (2::real)^(k+1)\<close> 
    by simp
  then have \<open> (d::real)/(2::real)^(k+1) \<le>  (d::real)/(2::real)\<close>  
    by (smt frac_le neq0_conv of_nat_0_less_iff power_one_right semiring_1_class.of_nat_simps(1))
  then have \<open>x < x\<close> using \<open>(d::real)/(2::real) < x\<close>  \<open>x \<le> (d::real)/(2::real)^(k+1)\<close>
    by linarith
  then show ?thesis 
    by blast
qed


lemma WLGOddPartShortIntervalX:
  fixes x y i j :: nat
  assumes \<open>OddPart x = OddPart y\<close> and \<open>y < 2*x\<close> and \<open>x \<le> y\<close>
and \<open>x = (2::nat)^i*(OddPart x)\<close> and \<open>y = (2::nat)^j*(OddPart y)\<close>
and \<open>i \<le> j\<close>
shows \<open>x = y\<close>
proof-
  have \<open>OddPart x > 0\<close> 
    using Exp2OddPartChar assms(4) by fastforce
  then have \<open>(OddPart x)/(OddPart x) = 1\<close>
    by simp
  have \<open>(2::nat)^j*(OddPart y) < (2::nat)*((2::nat)^i*(OddPart x))\<close>
    using \<open>y < (2::nat)*x\<close>  \<open>x = (2::nat)^i*(OddPart x)\<close>  \<open>y = (2::nat)^j*(OddPart y)\<close>
    by auto
  then have \<open>(2::nat)^j*(OddPart y) < (2::nat)^(i+1)*(OddPart x)\<close>
    by simp
  then have \<open>(2::nat)^j*(OddPart x) < (2::nat)^(i+1)*(OddPart x)\<close>
    using  \<open>OddPart x = OddPart y\<close> by simp
   then have  \<open>(2::nat)^j < (2::nat)^(i+1)\<close>
    using  \<open>(OddPart x)/(OddPart x) = 1\<close> 
    by simp   
  then have \<open>j < i+1\<close> 
    using nat_power_less_imp_less pos2 by blast
  have \<open>j = i\<close> 
    using \<open>j < i + 1\<close> assms(6) by linarith
  show ?thesis 
    using \<open>j = i\<close> assms(1) assms(4) assms(5) by auto
qed

lemma OddPartShortIntervalX:
  fixes x y :: nat
  assumes \<open>OddPart x = OddPart y\<close> and \<open>y < 2*x\<close> and \<open>x \<le> y\<close>
and \<open>x = 2^i*(OddPart x)\<close> and \<open>y = 2^j*(OddPart y)\<close>
shows \<open>x = y\<close>
  by (metis WLGOddPartShortIntervalX antisym assms(1) assms(2) assms(3) assms(4) assms(5) linear mult_le_mono1 one_less_numeral_iff power_increasing_iff semiring_norm(76))

lemma OddPartShortInterval:
  fixes x y :: nat
  assumes \<open>OddPart x = OddPart y\<close> and \<open>y < 2*x\<close> and \<open>x \<le> y\<close>
shows \<open>x = y\<close>
proof-
  obtain i where \<open>x = 2^i*(OddPart x)\<close> 
    by (metis One_nat_def Suc_leI assms(2) assms(3) mult_0_right neq0_conv not_le preExp2OddPartChar2)
  obtain j where \<open>y = 2^j*(OddPart y)\<close> 
    by (metis One_nat_def Suc_leI \<open>x = 2 ^ i * OddPart x\<close> assms(3) linorder_not_le neq0_conv preExp2OddPartChar2)
  show ?thesis 
    using OddPartShortIntervalX \<open>x = 2 ^ i * OddPart x\<close> \<open>y = 2 ^ j * OddPart y\<close> assms(1) assms(2) assms(3) by blast
qed

lemma WLOGErdosNicolasSetOddDivBoundInjOnSCaseA:
  fixes n k m d x y :: nat
  assumes \<open>n = (2::nat)^k*m\<close> and \<open>odd m\<close> and \<open>d dvd n\<close> and \<open>odd d\<close>
 and  \<open>x \<in>  (ErdosNicolasSet n d)\<close>
 and  \<open>y \<in>  (ErdosNicolasSet n d)\<close>
and \<open>OddPart x = OddPart y\<close> and \<open>x \<le> y\<close>
shows \<open>x = y\<close>
proof-
  from  \<open>x \<in>  (ErdosNicolasSet n d)\<close>
  have \<open>d < 2*x\<close> 
    using CollectD ErdosNicolasSet_def by fastforce
  from  \<open>y \<in>  (ErdosNicolasSet n d)\<close>
  have \<open>y \<le> d\<close> 
    by (simp add: ErdosNicolasSet_def)
  have \<open>y < 2*x\<close> 
    using \<open>d < 2 * x\<close> \<open>y \<le> d\<close> le_less_trans by blast
  show ?thesis using OddPartShortInterval \<open>x \<le> y\<close> \<open>y < 2*x\<close>  \<open>OddPart x = OddPart y\<close> 
    by simp
qed


lemma ErdosNicolasSetOddDivBoundInjOnSCaseA:
  fixes n k m d x y :: nat
  assumes \<open>n = (2::nat)^k*m\<close> and \<open>odd m\<close> and \<open>d dvd n\<close> and \<open>odd d\<close>
 and  \<open>x \<in>  (ErdosNicolasSet n d)\<close>
 and  \<open>y \<in>  (ErdosNicolasSet n d)\<close>
and \<open>OddPart x = OddPart y\<close>
shows \<open>x = y\<close>
  using WLOGErdosNicolasSetOddDivBoundInjOnSCaseA assms 
  by (metis nat_le_linear)

lemma OddPartBoundDiv:
  fixes n k m d :: nat
  assumes \<open>n = (2::nat)^k*m\<close> and \<open>odd m\<close> and \<open>d dvd n\<close>
  shows \<open>OddPart d \<ge> d/(2::real)^k\<close>
proof-
  obtain j where \<open>(2::nat)^j*(OddPart d) = d\<close>
    by (metis assms(1) assms(2) assms(3) dvd_0_left_iff even_mult_iff even_numeral less_one linorder_not_le   mult_eq_0_iff  preExp2OddPartChar2X2)
  from  \<open>(2::nat)^j*(OddPart d) = d\<close> \<open>d dvd n\<close> 
  have \<open>(2::nat)^j dvd n\<close> 
    by (metis dvd_mult_left)
  then have \<open>(2::nat)^j dvd (2::nat)^k*m\<close>  
    using  \<open>n = (2::nat)^k*m\<close> 
    by blast
  have \<open>gcd ((2::nat)^j) m = 1\<close> 
    by (meson OddDivPow2 assms(2) dvd_trans gcd_unique_nat one_le_numeral one_le_power)
  then have  \<open>(2::nat)^j dvd (2::nat)^k\<close>
    using \<open>(2::nat)^j dvd (2::nat)^k*m\<close>
    by (metis dvd_triv_right gcd_greatest gcd_mult_distrib_nat semiring_normalization_rules(12))
  then have \<open>(2::nat)^j \<le> (2::nat)^k\<close>
    by (simp add: dvd_imp_le)
  then have \<open>(2::nat)^k*(OddPart d) \<ge> d\<close> using  \<open>(2::nat)^j*(OddPart d) = d\<close> 
    by (metis mult_le_mono1)
  then have \<open>(2::real)^k*(OddPart d) \<ge> d\<close> 
    by (metis  numeral_power_eq_of_nat_cancel_iff of_nat_le_iff of_nat_mult )
  have \<open>(2::real)^k > 0\<close> 
    by simp
  then  show ?thesis using  \<open>(2::real)^k*(OddPart d) \<ge> d\<close>
    by (smt divide_strict_right_mono nonzero_mult_div_cancel_left)
qed


lemma ImpoErdosNicolasSetOddDivBoundInjOnSCaseB:
  fixes n k m d :: nat
  assumes \<open>n = (2::nat)^k*m\<close> and \<open>odd m\<close> and \<open>d dvd n\<close> and \<open>odd d\<close>
 and  \<open>x \<in>  (ErdosNicolasSet n d)\<close>
 and  \<open>y \<in> (OddDivBound n ((d::real)/(2::real)^(k+1)))\<close>
shows \<open>OddPart x \<noteq> OddPart y\<close>
proof-
  have \<open>odd y\<close> 
    using CollectD OddDivBound_def assms(6) by fastforce
  then have \<open>OddPart y = y\<close> 
    by (metis One_nat_def Suc_leI odd_pos preExp2OddPartChar1 preExp2OddPartChar2 preUniqnessOddEven_OddPartOneSide)
  have \<open>y \<le> ((d::real)/(2::real)^(k+1))\<close> 
    using CollectD OddDivBound_def assms(6) by fastforce
  have \<open>x dvd n\<close> 
    using CollectD ErdosNicolasSet_def assms(5) by fastforce
  then have \<open>OddPart x \<ge> x / (2::real)^k\<close> 
    using OddPartBoundDiv assms(1) assms(2) by blast
  from  \<open>x \<in>  (ErdosNicolasSet n d)\<close> 
  have \<open>2*x > d\<close> 
    using CollectD ErdosNicolasSet_def by fastforce 
  then have \<open>x > (d::real)/(2::real)\<close>
    by linarith
  then have \<open> x / (2::real)^k  > ((d::real)/(2::real))/(2::real)^k\<close>
    by (smt divide_strict_right_mono zero_less_power)
  then have \<open> x / (2::real)^k  > (d::real)/((2::real)*(2::real)^k)\<close>
    by simp
  then have \<open> x / (2::real)^k  > (d::real)/((2::real)^(k+1))\<close>
    by simp
  then have \<open>OddPart x > (d::real)/((2::real)^(k+1))\<close> 
    using \<open>real x / 2 ^ k \<le> real (OddPart x)\<close> by linarith
  then have \<open>OddPart x > y\<close> 
    using \<open>real y \<le> real d / 2 ^ (k + 1)\<close> by linarith 
  then show ?thesis 
    using \<open>OddPart y = y\<close> by linarith
qed

lemma ErdosNicolasSetOddDivBoundInjOnSCaseB:
  fixes n k m d :: nat
  assumes \<open>n = (2::nat)^k*m\<close> and \<open>odd m\<close> and \<open>d dvd n\<close> and \<open>odd d\<close>
 and  \<open>x \<in>  (ErdosNicolasSet n d)\<close>
 and  \<open> y \<in> (OddDivBound n ((d::real)/(2::real)^(k+1)))\<close>
and \<open>OddPart x = OddPart y\<close>
shows \<open>x = y\<close>
  using assms ImpoErdosNicolasSetOddDivBoundInjOnSCaseB 
  by blast


lemma ErdosNicolasSetOddDivBoundInjOnSCaseC:
  fixes n k m d :: nat
  assumes \<open>n = (2::nat)^k*m\<close> and \<open>odd m\<close> and \<open>d dvd n\<close> and \<open>odd d\<close>
 and  \<open> x \<in> (OddDivBound n ((d::real)/(2::real)^(k+1)))\<close>
 and  \<open>y \<in> (OddDivBound n ((d::real)/(2::real)^(k+1)))\<close>
and \<open>OddPart x = OddPart y\<close>
shows \<open>x = y\<close>
proof-
  have \<open>odd x\<close> 
    by (metis (no_types, lifting) OddDivBound_def One_nat_def add.right_neutral add_Suc_right assms(5) mem_Collect_eq)
  then have \<open>OddPart x = x\<close> 
    by (metis One_nat_def Suc_leI odd_pos preExp2OddPartChar1 preExp2OddPartChar2 preUniqnessOddEven_OddPartOneSide)
  have \<open>odd y\<close> 
    using CollectD OddDivBound_def assms(6) by fastforce
    then have \<open>OddPart y = y\<close>
    by (metis One_nat_def Suc_leI odd_pos preExp2OddPartChar1 preExp2OddPartChar2 preUniqnessOddEven_OddPartOneSide)
  show ?thesis 
    using \<open>OddPart x = x\<close> \<open>OddPart y = y\<close> assms(7) by linarith
qed


lemma ErdosNicolasSetOddDivBoundInjOnS:
  fixes n k m d :: nat
  assumes \<open>n = (2::nat)^k*m\<close> and \<open>odd m\<close> and \<open>d dvd n\<close> and \<open>odd d\<close>
 and  \<open>x \<in>  (ErdosNicolasSet n d) \<or> x \<in> (OddDivBound n ((d::real)/(2::real)^(k+1)))\<close>
 and  \<open>y \<in>  (ErdosNicolasSet n d) \<or> y \<in> (OddDivBound n ((d::real)/(2::real)^(k+1)))\<close>
and \<open>OddPart x = OddPart y\<close>
shows \<open>x = y\<close>
  using assms ErdosNicolasSetOddDivBoundInjOnSCaseA ErdosNicolasSetOddDivBoundInjOnSCaseB
ErdosNicolasSetOddDivBoundInjOnSCaseC 
  by metis

lemma ErdosNicolasSetOddDivBoundInjOn:
  fixes n k m d :: nat
  assumes \<open>n = (2::nat)^k*m\<close> and \<open>odd m\<close> and \<open>d dvd n\<close> and \<open>odd d\<close> 
  shows \<open> inj_on OddPart ((ErdosNicolasSet n d) \<union> (OddDivBound n ((d::real)/(2::real)^(k+1))))\<close>
  using ErdosNicolasSetOddDivBoundInjOnS inj_on_def assms 
  by (smt UnE)

lemma OddPartErdosNicolasSet:
\<open> OddPart ` ((ErdosNicolasSet n d) \<union> (OddDivBound n ((d::real)/(2::real)^(k+1)))) = (OddPart ` ((ErdosNicolasSet n d))) \<union> (OddPart ` (OddDivBound n ((d::real)/(2::real)^(k+1))))\<close>
  by (simp add: image_Un)

lemma ErdosNicolasSetOddDivBoundSurjAIS:
  fixes n k m d :: nat
  assumes \<open>n = (2::nat)^k*m\<close> and \<open>odd m\<close> and \<open>d dvd n\<close> and \<open>odd d\<close> 
and \<open>x \<in> ((ErdosNicolasSet n d))\<close> 
shows \<open>OddPart x \<in> (OddDivBound n (d::real))\<close>
proof-
  from  \<open>x \<in> ((ErdosNicolasSet n d))\<close> 
  have \<open>x dvd n\<close> 
    using CollectD ErdosNicolasSet_def by fastforce
  from  \<open>x \<in> ((ErdosNicolasSet n d))\<close> 
  have \<open>x \<le> d\<close> 
    using CollectD ErdosNicolasSet_def by fastforce
  have \<open>OddPart x dvd n\<close> 
    by (metis OddPartL1 \<open>x dvd n\<close> dvd_0_right dvd_imp_le gcd_nat.trans one_dvd order.order_iff_strict zero_order(1)) 
  have \<open>OddPart x \<le> d\<close> 
    by (metis OddPartL1 One_nat_def Suc_leI \<open>x \<le> d\<close> \<open>x dvd n\<close> assms(1) assms(2) dual_order.trans dvd_imp_le dvd_pos_nat nat_0_less_mult_iff odd_pos pos2 zero_less_power)
  have \<open>OddPart x \<ge> 1\<close> 
    by (metis One_nat_def Suc_leI \<open>OddPart x dvd n\<close> assms(1) assms(2) dvd_pos_nat nat_0_less_mult_iff odd_pos pos2 zero_less_power)
  then have \<open>odd (OddPart x)\<close>
    by (metis One_nat_def Suc_leI \<open>x dvd n\<close> assms(1) assms(2) dvd_pos_nat nat_0_less_mult_iff odd_pos pos2 preExp2OddPartChar1 zero_less_power)
  show ?thesis 
    by (simp add: OddDivBound_def \<open>OddPart x \<le> d\<close> \<open>OddPart x dvd n\<close> \<open>odd (OddPart x)\<close>)
qed


lemma ErdosNicolasSetOddDivBoundSurjAI:
  fixes n k m d :: nat
  assumes \<open>n = (2::nat)^k*m\<close> and \<open>odd m\<close> and \<open>d dvd n\<close> and \<open>odd d\<close> 
  shows \<open>  (OddPart ` ((ErdosNicolasSet n d))) \<subseteq> (OddDivBound n (d::real))\<close>
  using ErdosNicolasSetOddDivBoundSurjAIS assms(1) assms(2) assms(3) assms(4) by blast

lemma ErdosNicolasSetOddDivBoundSurjAIIX:
  fixes n k m d :: nat
  assumes \<open>n = (2::nat)^k*m\<close> and \<open>odd m\<close> and \<open>d dvd n\<close> and \<open>odd d\<close> 
and \<open>x \<in> (OddPart ` (OddDivBound n ((d::real)/(2::real)^(k+1))))\<close>
shows \<open> x \<in> (OddDivBound n (d::real))\<close>
proof-
  obtain y::nat where \<open>x = OddPart y\<close> and \<open>y \<in> (OddDivBound n ((d::real)/(2::real)^(k+1)))\<close>
    using assms(5) by blast
  from  \<open>y \<in> (OddDivBound n ((d::real)/(2::real)^(k+1)))\<close>
  have \<open>odd y\<close> 
    by (metis (mono_tags, lifting) CollectD OddDivBound_def One_nat_def add.right_neutral add_Suc_right  one_add_one)
  then have \<open>y \<ge> 1\<close> 
    by (simp add: dvd_imp_le odd_pos)
  then have \<open>y = OddPart y\<close> using  \<open>odd y\<close>
    by (meson OddPartL1 OddPartL1X1 antisym dvd_refl linorder_neqE_nat nat_dvd_not_less odd_pos order_less_imp_le)
  have \<open>y \<le> ((d::real)/(2::real)^(k+1))\<close> 
    using CollectD OddDivBound_def \<open>y \<in> OddDivBound n (real d / 2 ^ (k + 1))\<close> by fastforce
  have \<open>(1::real) \<le> (2::real)^(k+1)\<close> 
    using two_realpow_ge_one by blast 
  have \<open> ((d::real)/(2::real)^(k+1)) \<le> (d::real)/(1::real)\<close> 
    by (smt \<open>1 \<le> 2 ^ (k + 1)\<close> frac_le neq0_conv of_nat_0 of_nat_0_less_iff)    
  then  have \<open> ((d::real)/(2::real)^(k+1)) \<le> (d::real)\<close> 
    by linarith
  then  have \<open>y \<le> (d::real)\<close> 
    using \<open>real y \<le> real d / 2 ^ (k + 1)\<close> by linarith
  then have \<open>x \<le> d\<close> 
    using \<open>x = OddPart y\<close> \<open>y = OddPart y\<close> by linarith
  have \<open>odd x\<close> 
    using \<open>odd y\<close> \<open>x = OddPart y\<close> \<open>y = OddPart y\<close> by auto
  have \<open>x dvd n\<close> 
    using CollectD OddDivBound_def \<open>x = OddPart y\<close> \<open>y = OddPart y\<close> \<open>y \<in> OddDivBound n (real d / 2 ^ (k + 1))\<close> by fastforce
  show ?thesis 
    by (simp add: OddDivBound_def \<open>odd x\<close> \<open>x \<le> d\<close> \<open>x dvd n\<close>)
qed


lemma ErdosNicolasSetOddDivBoundSurjAII:
  fixes n k m d :: nat
  assumes \<open>n = (2::nat)^k*m\<close> and \<open>odd m\<close> and \<open>d dvd n\<close> and \<open>odd d\<close> 
  shows \<open>  (OddPart ` (OddDivBound n ((d::real)/(2::real)^(k+1)))) \<subseteq> (OddDivBound n (d::real))\<close>
  using assms ErdosNicolasSetOddDivBoundSurjAIIX by blast

lemma ErdosNicolasSetOddDivBoundSurjA:
  fixes n k m d :: nat
  assumes \<open>n = (2::nat)^k*m\<close> and \<open>odd m\<close> and \<open>d dvd n\<close> and \<open>odd d\<close> 
  shows \<open>  (OddPart ` ((ErdosNicolasSet n d))) \<union> (OddPart ` (OddDivBound n ((d::real)/(2::real)^(k+1)))) \<subseteq> (OddDivBound n (d::real))\<close>
  using assms ErdosNicolasSetOddDivBoundSurjAI ErdosNicolasSetOddDivBoundSurjAII 
  by simp

lemma ErdosNicolasSetOddDivBoundSurjBI:
  fixes n k m d :: nat
  assumes \<open>n = (2::nat)^k*m\<close> and \<open>odd m\<close> and \<open>d dvd n\<close> and \<open>odd d\<close> 
and \<open>x \<in> (OddDivBound n (d::real))\<close>
and \<open>x \<le> ((d::real)/(2::real)^(k+1))\<close>
shows \<open>x \<in> (OddPart ` (OddDivBound n ((d::real)/(2::real)^(k+1))))\<close>
proof-
  from \<open>x \<in> (OddDivBound n (d::real))\<close>
  have \<open>x dvd n\<close> 
    using CollectD OddDivBound_def by fastforce
  from  \<open>x \<in> (OddDivBound n (d::real))\<close>
  have \<open>odd x\<close> using OddDivBound_def 
    using CollectD by fastforce
  have \<open>x \<ge> 1\<close> 
    by (simp add: Suc_leI \<open>odd x\<close> odd_pos)
  have \<open>x = OddPart x\<close> 
    using \<open>1 \<le> x\<close> \<open>odd x\<close> preExp2OddPartChar1 preExp2OddPartChar2 preUniqnessOddEven_OddPartOneSide by blast
  have \<open>x \<in> (OddDivBound n ((d::real)/(2::real)^(k+1)))\<close>
    by (metis (mono_tags) OddDivBound_def Suc_eq_plus1 \<open>odd x\<close> \<open>x dvd n\<close> assms(6) mem_Collect_eq )
  then show ?thesis 
    using \<open>x = OddPart x\<close> by blast
qed


lemma ErdosNicolasSetOddDivBoundSurjBII:
  fixes n k m d :: nat
  assumes \<open>n = (2::nat)^k*m\<close> and \<open>odd m\<close> and \<open>d dvd n\<close> and \<open>odd d\<close> 
and \<open>x \<in> (OddDivBound n (d::real))\<close>
and \<open>x > ((d::real)/(2::real)^(k+1))\<close>
shows \<open>x \<in> (OddPart ` ((ErdosNicolasSet n d)))\<close>
proof-
  from  \<open>x \<in> (OddDivBound n (d::real))\<close>
  have \<open>x dvd n\<close> 
    using CollectD OddDivBound_def by fastforce
  from  \<open>x \<in> (OddDivBound n (d::real))\<close>
  have \<open>odd x\<close> 
    using CollectD OddDivBound_def by fastforce
  then have \<open>x \<ge> 1\<close> 
    by (simp add: dvd_imp_le odd_pos)
  then have \<open>OddPart x = x\<close>
    using  \<open>odd x\<close> 
    by (meson OddPartL1 OddPartL1X1 antisym dvd_refl linorder_neqE_nat nat_dvd_not_less odd_pos order_less_imp_le)
  from \<open>x > ((d::real)/(2::real)^(k+1))\<close>
  have \<open>2^k*x > 2^k*((d::real)/(2::real)^(k+1))\<close>
    by (smt mult_le_cancel_left_pos of_nat_1 of_nat_add of_nat_mult of_nat_power one_add_one zero_less_power)
  then have \<open>2^k*x > (d::real)/(2::real)\<close>
    by simp
  then have \<open>k \<in> {i | i :: nat. 2^i*x > (d::real)/(2::real)}\<close>
    by blast
  then have \<open>{i | i :: nat. 2^i*x > (d::real)/(2::real)} \<noteq> {}\<close>
    by blast
  then obtain j::nat where \<open>j = Inf {i | i :: nat. 2^i*x > (d::real)/(2::real)}\<close>
    by blast
  from \<open>k \<in> {i | i :: nat. 2^i*x > (d::real)/(2::real)}\<close> 
  have \<open>k \<ge> Inf {i | i :: nat. 2^i*x > (d::real)/(2::real)}\<close>
    using cInf_lower
    by (metis \<open>j = Inf {i |i. real d / 2 < real (2 ^ i * x)}\<close> bdd_above_bot)
  then have \<open>k \<ge> j\<close> 
    using \<open>j = Inf {i |i. real d / 2 < real (2 ^ i * x)}\<close> by blast
  then have \<open>2^j dvd n\<close> 
    using assms(1) dvd_triv_left power_le_dvd by blast
  then have \<open>gcd x (2^j) = 1\<close> 
    by (meson OddDivPow2 \<open>odd x\<close> dvd_trans gcd_unique_nat one_le_numeral one_le_power)
  then have \<open>2^j*x dvd n\<close> using  \<open>2^j dvd n\<close> \<open>x dvd n\<close> 
    by (smt TrapezoidalNumbersNec2_5 \<open>j \<le> k\<close> \<open>odd x\<close> assms(1) division_decomp dvd_mult le_imp_power_dvd mult_dvd_mono preUniqnessOddEven_OddPartOneSide)
  from  \<open>j = Inf {i | i :: nat. 2^i*x > (d::real)/(2::real)}\<close> \<open> {i | i :: nat. 2^i*x > (d::real)/(2::real)} \<noteq> {}\<close>
  have \<open>j \<in> {i | i :: nat. 2^i*x > (d::real)/(2::real)}\<close>
    using Inf_nat_def1
    by presburger
  then have \<open>2^j*x > (d::real)/(2::real)\<close>
    by blast
  have \<open>d \<ge> x\<close> 
    by (metis (no_types, lifting) CollectD OddDivBound_def assms(5) of_nat_le_iff)
  have \<open>d \<ge> 2^j*x\<close>
    proof(cases \<open>j = 0\<close>)
        case True
          then show ?thesis using \<open>d \<ge> x\<close> \<open>j = 0\<close> by simp
        next
          case False
          then have \<open>j \<noteq> 0\<close> by blast
          then obtain p::nat where \<open>Suc p = j\<close> 
            by (metis lessI less_Suc_eq_0_disj)
            have \<open>d \<ge> 2^j*x\<close>
            proof(rule classical)
              assume \<open>\<not>(d \<ge> 2^j*x)\<close>
              then have \<open>2^(Suc p)*x > d\<close> using \<open>Suc p = j\<close> by auto
              then have \<open>2*(2^p*x) > d\<close> 
                by auto
              then have \<open>2^p*x > (d::real)/(2::real)\<close> 
                by linarith
              then have \<open>p \<in> {i | i :: nat. 2^i*x > (d::real)/(2::real)}\<close>
                by blast
              have \<open>p < j\<close> 
                using \<open>Suc p = j\<close> by blast
              have \<open>p \<ge> j\<close> 
                by (metis \<open>j = Inf {i |i. real d / 2 < real (2 ^ i * x)}\<close> \<open>p \<in> {i |i. real d / 2 < real (2 ^ i * x)}\<close> bdd_above_bot cInf_lower)
              show ?thesis using  \<open>p < j\<close> \<open>p \<ge> j\<close>  by auto
            qed
        then show ?thesis by blast
      qed
      from \<open>2^j*x > (d::real)/(2::real)\<close>
      have \<open>2^j*x > d/2\<close>
        by simp
      then have \<open>2*(2^j*x) > 2*(d/2)\<close> by simp
      then have  \<open>2*(2^j*x) > d*((2::nat)/2)\<close> by simp
      then have  \<open>2*(2^j*x) > d*(1::nat)\<close> 
        by (simp add: of_nat_less_imp_less)
      then have  \<open>2*(2^j*x) > d\<close> 
        by linarith 
    have \<open>2^j*x \<in> ((ErdosNicolasSet n d))\<close>
      using \<open>d \<ge> 2^j*x\<close> \<open>2*(2^j*x) > d\<close>  \<open>x dvd n\<close> ErdosNicolasSet_def 
      by (simp add: \<open>ErdosNicolasSet \<equiv> \<lambda>n d. {e |e. e dvd n \<and> e \<le> d \<and> d < 2 * e}\<close> \<open>2 ^ j * x dvd n\<close>)
    have \<open>OddPart (2^j*x) = x\<close> using \<open>odd x\<close> \<open>x \<ge> 1\<close> UniqnessOddEven
      by (smt dvd_mult_unit_iff' le_eq_less_or_eq less_1_mult nat_dvd_1_iff_1 one_le_numeral one_le_power preExp2OddPartChar1 preExp2OddPartChar2 preUniqnessOddEven_OddPartOneSide semiring_normalization_rules(12))
    from  \<open>2^j*x \<in> (ErdosNicolasSet n d)\<close> \<open>OddPart (2^j*x) = x\<close>
    have \<open>x \<in> OddPart ` (ErdosNicolasSet n d)\<close> 
      by (metis image_eqI)
    then show ?thesis by blast
qed

lemma ErdosNicolasSetOddDivBoundSurjB:
  fixes n k m d :: nat
  assumes \<open>n = (2::nat)^k*m\<close> and \<open>odd m\<close> and \<open>d dvd n\<close> and \<open>odd d\<close> 
  shows \<open>(OddDivBound n (d::real)) \<subseteq>  (OddPart ` ((ErdosNicolasSet n d))) \<union> (OddPart ` (OddDivBound n ((d::real)/(2::real)^(k+1))))\<close>
  by (smt ErdosNicolasSetOddDivBoundSurjBI ErdosNicolasSetOddDivBoundSurjBII UnCI assms(1) assms(2) assms(3) assms(4) subsetI)

lemma ErdosNicolasSetOddDivBoundSurj:
  fixes n k m d :: nat
  assumes \<open>n = (2::nat)^k*m\<close> and \<open>odd m\<close> and \<open>d dvd n\<close> and \<open>odd d\<close> 
  shows \<open> OddPart ` ((ErdosNicolasSet n d) \<union> (OddDivBound n ((d::real)/(2::real)^(k+1)))) = (OddDivBound n (d::real))\<close>
  using assms ErdosNicolasSetOddDivBoundSurjA ErdosNicolasSetOddDivBoundSurjB OddPartErdosNicolasSet
  by (simp add: subset_antisym)


lemma ErdosNicolasSetOddDivBoundBij:
  fixes n k m d :: nat
  assumes \<open>n = (2::nat)^k*m\<close> and \<open>odd m\<close> and \<open>d dvd n\<close> and \<open>odd d\<close> 
  shows \<open> bij_betw OddPart ((ErdosNicolasSet n d) \<union> (OddDivBound n ((d::real)/(2::real)^(k+1)))) (OddDivBound n (d::real))\<close>
  using assms ErdosNicolasSetOddDivBoundInjOn ErdosNicolasSetOddDivBoundSurj 
  by (simp add: bij_betw_def)

lemma ErdosNicolasSetOddDivBoundL:
  fixes n k m d :: nat
  assumes \<open>n = (2::nat)^k*m\<close> and \<open>odd m\<close> and \<open>d dvd n\<close> and \<open>odd d\<close> 
  shows \<open>card (ErdosNicolasSet n d) + (card (OddDivBound n ((d::real)/(2::real)^(k+1)))) = (card (OddDivBound n (d::real)))\<close>
proof-
  have \<open>finite (ErdosNicolasSet n d)\<close> 
    by (metis (no_types, lifting) CollectD ErdosNicolasSet_def finite_nat_set_iff_bounded_le )

  have \<open>finite (OddDivBound n (d::real))\<close> using OddDivBound_def 
    by (metis (no_types, lifting) assms(1) assms(2) dvd_0_right dvd_imp_le finite_nat_set_iff_bounded_le mem_Collect_eq mult_eq_0_iff neq0_conv pos2 zero_less_power)

  have \<open>finite (OddDivBound n ((d::real)/(2::real)^(k+1)))\<close> using OddDivBound_def
    by (metis (no_types, lifting) assms(1) assms(2) dvd_0_right dvd_imp_le finite_nat_set_iff_bounded_le mem_Collect_eq mult_eq_0_iff neq0_conv pos2 zero_less_power)

  have \<open>card ((ErdosNicolasSet n d) \<union> (OddDivBound n ((d::real)/(2::real)^(k+1)))) = card (OddDivBound n (d::real))\<close>
    using ErdosNicolasSetOddDivBoundBij 
    by (meson assms(1) assms(2) assms(3) assms(4) bij_betw_same_card)

  have \<open> (ErdosNicolasSet n d) \<inter> (OddDivBound n ((d::real)/(2::real)^(k+1))) = {}\<close>
    using ErdosNicolasSetOddDivBoundLInter 
    using assms(1) assms(2) assms(3) assms(4) by blast
  show ?thesis 
    using \<open>ErdosNicolasSet n d \<inter> OddDivBound n (real d / 2 ^ (k + 1)) = {}\<close> \<open>card (ErdosNicolasSet n d \<union> OddDivBound n (real d / 2 ^ (k + 1))) = card (OddDivBound n (real d))\<close> \<open>finite (ErdosNicolasSet n d)\<close> \<open>finite (OddDivBound n (real d / 2 ^ (k + 1)))\<close> card_Un_disjoint by fastforce
qed


section {* Main Result *}

theorem ErdosNicolasSetOddDivBound:
  fixes n k m d :: nat
  assumes \<open>n = (2::nat)^k*m\<close> and \<open>odd m\<close> and \<open>d dvd n\<close> and \<open>odd d\<close> 
  shows \<open>card (ErdosNicolasSet n d) = (card (OddDivBound n (d::real))) - (card (OddDivBound n ((d::real)/(2::real)^(k+1))))\<close>
  using ErdosNicolasSetOddDivBoundL assms 
  by (metis diff_add_inverse2)

end


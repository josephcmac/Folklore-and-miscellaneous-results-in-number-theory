(*
Title: A relationship between the Erdos-Nicolas function and the odd divisors
Author: Jose Manuel Rodriguez Caballero

The Erdos-Nicolas function is defined as follows:

definition ErdosNicolasSet :: \<open> nat \<Rightarrow> nat \<Rightarrow> nat set \<close> 
  where \<open>ErdosNicolasSet \<equiv> \<lambda> n :: nat. \<lambda> d :: nat.
 {e | e :: nat. e dvd n \<and> e \<le> d \<and> d < 2*e}\<close>

definition ErdosNicolas :: \<open>nat \<Rightarrow> nat\<close>
  where \<open>ErdosNicolas \<equiv> \<lambda> n :: nat. Max { card (ErdosNicolasSet n d) | d :: nat. d dvd n}\<close>

We prove the following characterization of this function, involving only odd divisors:

theorem ErdosNicolasOddDivSetOdd:
  fixes n k m :: nat
  assumes \<open>n = (2::nat)^k*m\<close> and \<open>odd m\<close> 
  shows \<open>ErdosNicolas n = Max { card (ErdosNicolasSetOdd n k d) | d :: nat. d dvd n \<and> odd d}\<close>

where 

definition ErdosNicolasSetOdd :: \<open> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat set \<close> 
  where \<open>ErdosNicolasSetOdd \<equiv> \<lambda> n :: nat. \<lambda> k::nat. \<lambda> d :: nat.
 {e | e :: nat. e dvd n \<and> odd e \<and> e \<le> d \<and> d < 2^(k+1)*e}\<close>


References:

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


theory ErdosNicolasOdd

imports Complex_Main  PowOfTwo


begin

definition ErdosNicolasSet :: \<open> nat \<Rightarrow> nat \<Rightarrow> nat set \<close> 
  where \<open>ErdosNicolasSet \<equiv> \<lambda> n :: nat. \<lambda> d :: nat.
 {e | e :: nat. e dvd n \<and> e \<le> d \<and> d < 2*e}\<close>

definition ErdosNicolas :: \<open>nat \<Rightarrow> nat\<close>
  where \<open>ErdosNicolas \<equiv> \<lambda> n :: nat. Max { card (ErdosNicolasSet n d) | d :: nat. d dvd n}\<close>

definition ErdosNicolasSetOdd :: \<open> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat set \<close> 
  where \<open>ErdosNicolasSetOdd \<equiv> \<lambda> n :: nat. \<lambda> k::nat. \<lambda> d :: nat.
 {e | e :: nat. e dvd n \<and> odd e \<and> e \<le> d \<and> d < 2^(k+1)*e}\<close>


section {* Auxiliary Results *}


definition OddDivSet :: \<open>nat \<Rightarrow> real \<Rightarrow> nat set\<close> where
  \<open>OddDivSet \<equiv> \<lambda> n::nat. \<lambda> x::real.  {d | d :: nat. d dvd n \<and> odd d \<and> d \<le> x }\<close>




lemma ErdosNicolasOdd7AXAL:
  fixes n d:: nat
  assumes \<open>n \<ge> 1\<close> and \<open>d dvd n\<close>
  shows \<open> \<exists> e :: nat. e dvd n \<and> e \<le> d \<and> d < 2*e \<close>
  by (metis One_nat_def arith_special(3) assms(1) assms(2) dvd_pos_nat lessI less_le_trans n_less_m_mult_n nat_le_linear plus_1_eq_Suc)

lemma ErdosNicolasOdd7AXA:
  fixes n d:: nat
  assumes \<open>n \<ge> 1\<close> and \<open>d dvd n\<close>
  shows \<open> d \<in> (ErdosNicolasSet n d)\<close>
  using assms ErdosNicolasOdd7AXAL 
  by (smt ErdosNicolasSet_def dvd_def dvd_refl le_neq_implies_less mem_Collect_eq mult.commute mult_le_mono nat_le_linear not_le)

lemma ErdosNicolasOdd7AXB:
  fixes n d e :: nat
  assumes \<open>n \<ge> 1\<close> and \<open>d dvd n\<close> and \<open>even d\<close> and \<open>e dvd n\<close> and \<open>e < d\<close>
    and \<open>\<forall> ee. ee dvd n \<and> ee < d \<longrightarrow> ee \<le> e\<close>
  shows \<open> d \<notin> (ErdosNicolasSet n e)\<close>
proof-
  have \<open>\<forall> j. j \<in> (ErdosNicolasSet n e) \<longrightarrow> j \<le> e\<close> 
    by (simp add: ErdosNicolasSet_def)
  hence  \<open>\<forall> j. j \<in> (ErdosNicolasSet n e) \<longrightarrow> j \<noteq> d\<close> 
    using  \<open>e < d\<close> 
      less_le_trans by blast
  thus ?thesis 
    by blast
qed

lemma ErdosNicolasOdd7AX:
  fixes n d e :: nat
  assumes \<open>n \<ge> 1\<close> and \<open>d dvd n\<close> and \<open>even d\<close> and \<open>e dvd n\<close> and \<open>e < d\<close>
    and \<open>\<forall> ee. ee dvd n \<and> ee < d \<longrightarrow> ee \<le> e\<close>
  shows \<open> d \<in> (ErdosNicolasSet n d) - (ErdosNicolasSet n e)\<close>
  using  assms ErdosNicolasOdd7AXA ErdosNicolasOdd7AXB
  by blast

lemma ErdosNicolasOdd7AY:
  fixes n d dd e :: nat
  assumes \<open>n \<ge> 1\<close> and \<open>d dvd n\<close> and \<open>even d\<close> and \<open>e dvd n\<close> and \<open>e < d\<close>
    and \<open>\<forall> ee. ee dvd n \<and> ee < d \<longrightarrow> ee \<le> e\<close>
    and \<open> d \<in> (ErdosNicolasSet n d) - (ErdosNicolasSet n e)\<close>
    and \<open> dd \<in> (ErdosNicolasSet n d) - (ErdosNicolasSet n e)\<close>
  shows \<open>d = dd\<close> 
  by (metis (no_types, lifting) CollectD CollectI DiffE ErdosNicolasSet_def assms(5) assms(6) assms(8) dual_order.strict_iff_order less_le_trans)

lemma singletonSplit:
  assumes \<open>x \<in> S\<close> and \<open>\<forall> y. (y \<in> S \<longrightarrow> x = y)\<close>
  shows \<open>{x} = S\<close>
  using assms(1) assms(2) by fastforce

lemma ErdosNicolasOdd7A:
  fixes n d e :: nat
  assumes \<open>n \<ge> 1\<close> and \<open>d dvd n\<close> and \<open>even d\<close> and \<open>e dvd n\<close> and \<open>e < d\<close>
    and \<open>\<forall> ee. ee dvd n \<and> ee < d \<longrightarrow> ee \<le> e\<close>
  shows \<open> (ErdosNicolasSet n d) - (ErdosNicolasSet n e) = {d}\<close>
  using assms ErdosNicolasOdd7AX ErdosNicolasOdd7AY singletonSplit
  by metis

lemma ErdosNicolasOdd7BXAL:
  fixes n d e:: nat
  assumes \<open>n \<ge> 1\<close> and \<open>d dvd n\<close> and \<open>even d\<close> and \<open>e dvd n\<close> and \<open>e < d\<close>
    and \<open>\<forall> ee. ee dvd n \<and> ee < d \<longrightarrow> ee \<le> e\<close>
  shows \<open> (d div 2) dvd n \<and> (d div 2) \<le> e \<and> e < 2*(d div 2)\<close>
  using Suc_le_lessD assms(1) assms(2) assms(3) assms(5) assms(6) by fastforce

lemma ErdosNicolasOdd7BX:
  fixes n d e :: nat
  assumes \<open>n \<ge> 1\<close> and \<open>d dvd n\<close> and \<open>even d\<close> and \<open>e dvd n\<close> and \<open>e < d\<close>
    and \<open>\<forall> ee. ee dvd n \<and> ee < d \<longrightarrow> ee \<le> e\<close>
  shows \<open>d div 2 \<in> (ErdosNicolasSet n e)\<close>
  using assms ErdosNicolasOdd7BXAL 
  by (metis (no_types, lifting) CollectI ErdosNicolasSet_def dvd_mult_div_cancel)


lemma ErdosNicolasOdd7BY:
  fixes n d e :: nat
  assumes \<open>n \<ge> 1\<close> and \<open>d dvd n\<close> and \<open>even d\<close> and \<open>e dvd n\<close> and \<open>e < d\<close>
    and \<open>\<forall> ee. ee dvd n \<and> ee < d \<longrightarrow> ee \<le> e\<close>
  shows \<open>d div 2 \<notin> (ErdosNicolasSet n d)\<close>
  by (simp add: ErdosNicolasSet_def leD)


lemma ErdosNicolasOdd7BXYFusion:
  fixes n d e :: nat
  assumes \<open>n \<ge> 1\<close> and \<open>d dvd n\<close> and \<open>even d\<close> and \<open>e dvd n\<close> and \<open>e < d\<close>
    and \<open>\<forall> ee. ee dvd n \<and> ee < d \<longrightarrow> ee \<le> e\<close>
  shows \<open>d div 2 \<in> (ErdosNicolasSet n e) - (ErdosNicolasSet n d)\<close>
  using ErdosNicolasOdd7BX ErdosNicolasOdd7BY assms(1) assms(2) assms(3) assms(4) assms(5) assms(6) by auto


lemma ErdosNicolasOdd7B:
  fixes n d e :: nat
  assumes \<open>n \<ge> 1\<close> and \<open>d dvd n\<close> and \<open>even d\<close> and \<open>e dvd n\<close> and \<open>e < d\<close>
    and \<open>\<forall> ee. ee dvd n \<and> ee < d \<longrightarrow> ee \<le> e\<close>
  shows \<open>card((ErdosNicolasSet n e) - (ErdosNicolasSet n d)) \<ge> 1\<close>
proof-
  have \<open>finite (ErdosNicolasSet n e)\<close> 
    by (metis (mono_tags, lifting) CollectD ErdosNicolasSet_def assms(5)  finite_nat_set_iff_bounded less_le_trans  not_le)
  hence \<open>finite((ErdosNicolasSet n e) - (ErdosNicolasSet n d))\<close>
    by blast
  have \<open>d div 2 \<in> (ErdosNicolasSet n e) - (ErdosNicolasSet n d)\<close> 
    using ErdosNicolasOdd7BXYFusion assms(1) assms(2) assms(3) assms(4) assms(5) assms(6) by blast
  thus ?thesis 
    using \<open>finite (ErdosNicolasSet n e - ErdosNicolasSet n d)\<close> card_Suc_Diff1 by fastforce  
qed

lemma SymDiffThisProblem:
  fixes n d e :: nat
  assumes \<open>n \<ge> 1\<close> and \<open>d dvd n\<close> and \<open>even d\<close> and \<open>e dvd n\<close> and \<open>e < d\<close>
    and \<open>\<forall> ee. ee dvd n \<and> ee < d \<longrightarrow> ee \<le> e\<close>
  shows \<open>card((ErdosNicolasSet n d) - (ErdosNicolasSet n e)) \<le> card((ErdosNicolasSet n e) - (ErdosNicolasSet n d)) \<close>
  by (metis ErdosNicolasOdd7A ErdosNicolasOdd7B One_nat_def assms(1) assms(2) assms(3) assms(4) assms(5) assms(6) card.empty card_insert_if empty_iff finite.emptyI)

lemma SymDiff:
  assumes \<open>finite A\<close> and \<open>finite B\<close> and \<open>card (A - B) \<le> card (B - A)\<close>
  shows \<open>card A \<le> card B\<close>
proof-
  have \<open>card A = card (A - B) + card (A \<inter> B)\<close> 
    by (metis Diff_Diff_Int Diff_disjoint Un_Diff_Int assms(1) card_Un_disjoint finite_Diff)
  have \<open>card B = card (B - A) + card (A \<inter> B)\<close> 
    by (metis Diff_Diff_Int Diff_disjoint Un_Diff_Int assms(2) card_Un_disjoint finite_Diff inf_commute)
  show ?thesis 
    by (simp add: \<open>card A = card (A - B) + card (A \<inter> B)\<close> \<open>card B = card (B - A) + card (A \<inter> B)\<close> assms(3))
qed

lemma ErdosNicolasOdd6:
  fixes n d e :: nat
  assumes \<open>n \<ge> 1\<close> and \<open>d dvd n\<close> and \<open>even d\<close> and \<open>e dvd n\<close> and \<open>e < d\<close>
    and \<open>\<forall> ee. ee dvd n \<and> ee < d \<longrightarrow> ee \<le> e\<close>
  shows \<open> card (ErdosNicolasSet n d) \<le> card (ErdosNicolasSet n e)\<close>
proof-
  have \<open>finite (ErdosNicolasSet n d)\<close> 
    by (metis (no_types, lifting) CollectD ErdosNicolasSet_def  finite_nat_set_iff_bounded_le  )
  have \<open>finite (ErdosNicolasSet n e)\<close> 
    by (metis (no_types, lifting) CollectD ErdosNicolasSet_def bounded_nat_set_is_finite  less_le_trans  not_less)
  hence \<open>card((ErdosNicolasSet n d) - (ErdosNicolasSet n e)) \<le> card((ErdosNicolasSet n e) - (ErdosNicolasSet n d)) \<close>
    using SymDiffThisProblem assms(1) assms(2) assms(3) assms(4) assms(5) assms(6) by blast
  show ?thesis 
    by (simp add: SymDiff \<open>card (ErdosNicolasSet n d - ErdosNicolasSet n e) \<le> card (ErdosNicolasSet n e - ErdosNicolasSet n d)\<close> \<open>finite (ErdosNicolasSet n d)\<close> \<open>finite (ErdosNicolasSet n e)\<close>)
qed

lemma ErdosNicolasOdd5:
  fixes n d :: nat
  assumes \<open>n \<ge> 1\<close> and \<open>d dvd n\<close> and \<open>even d\<close>
  shows \<open> \<exists> e. e dvd n \<and> e < d \<and> (\<forall> ee. ee dvd n \<and> ee < d \<longrightarrow> ee \<le> e)\<close>
proof-
  obtain k::nat where \<open>d = 2*k\<close> using \<open>even d\<close> 
    by blast
  have \<open>k \<in> {e | e :: nat.  e dvd n \<and> e < d }\<close> 
    by (metis CollectI Groups.mult_ac(2) One_nat_def Suc_le_lessD \<open>d = 2 * k\<close> assms(1) assms(2) dual_order.strict_iff_order dvd_imp_le dvd_pos_nat dvd_triv_right gcd_nat.trans nat_mult_1 nonzero_mult_div_cancel_left odd_one)
  have \<open>finite {e | e :: nat.  e dvd n \<and> e < d }\<close> 
    using finite_nat_set_iff_bounded by blast
  obtain e ::nat where \<open>e = Max  {e | e :: nat.  e dvd n \<and> e < d }\<close>
    by simp
  from  \<open>e = Max  {e | e :: nat.  e dvd n \<and> e < d }\<close> 
  have \<open>e dvd n\<close> 
    using Max_in \<open>finite {e |e. e dvd n \<and> e < d}\<close> \<open>k \<in> {e |e. e dvd n \<and> e < d}\<close> mem_Collect_eq by blast
  from  \<open>e = Max  {e | e :: nat.  e dvd n \<and> e < d }\<close> 
  have \<open>e < d\<close> 
    using Max_in \<open>finite {e |e. e dvd n \<and> e < d}\<close> \<open>k \<in> {e |e. e dvd n \<and> e < d}\<close> mem_Collect_eq by blast
  from  \<open>e = Max  {e | e :: nat.  e dvd n \<and> e < d }\<close> 
  have \<open>\<forall> ee. ee dvd n \<and> ee < d \<longrightarrow> ee \<le> e\<close> 
    by simp
  show ?thesis 
    using \<open>\<forall>ee. ee dvd n \<and> ee < d \<longrightarrow> ee \<le> e\<close> \<open>e < d\<close> \<open>e dvd n\<close> by blast
qed

lemma ErdosNicolasOdd4:
  assumes  \<open>n \<ge> 1\<close> and \<open>d \<le> Suc k\<close> and \<open>d dvd n\<close> and \<open>even d\<close>
  shows \<open>\<exists> e. e dvd n \<and> e \<le> k \<and> card (ErdosNicolasSet n d) \<le> card (ErdosNicolasSet n e)\<close>
proof-
  obtain k where \<open>2*k = d\<close> 
    using assms(4) by blast
  obtain e where \<open>e dvd n\<close> and \<open>e < d\<close> and \<open>\<forall> ee. ee dvd n \<and> ee < d \<longrightarrow> ee \<le> e\<close>
    using ErdosNicolasOdd5 assms(1) assms(3) \<open>even d\<close> by blast
  have \<open>card (ErdosNicolasSet n d) \<le> card (ErdosNicolasSet n e)\<close> 
    using ErdosNicolasOdd6 \<open>\<forall>ee. ee dvd n \<and> ee < d \<longrightarrow> ee \<le> e\<close> \<open>e < d\<close> \<open>e dvd n\<close> assms(1) assms(3) assms(4) by blast
  thus ?thesis 
    using \<open>e < d\<close> \<open>e dvd n\<close> assms(2) less_le_trans by auto
qed

lemma ErdosNicolasOdd3:
  assumes \<open>\<forall> n d.  n \<ge> 1 \<and> d \<le> k  \<and> d dvd n  \<longrightarrow> ( \<exists> e. e dvd n \<and> odd e \<and> card (ErdosNicolasSet n d) \<le> card (ErdosNicolasSet n e) )\<close>
    and \<open>n \<ge> 1\<close> and \<open>d \<le> Suc k\<close>  and \<open>d dvd n\<close>
  shows \<open>\<exists> e. e dvd n \<and> odd e \<and> card (ErdosNicolasSet n d) \<le> card (ErdosNicolasSet n e)\<close>
proof(induction k)
  case 0
  thus ?case 
    by (smt ErdosNicolasOdd4 assms(1) assms(2) assms(3) assms(4) order_refl order_trans)
next
  case (Suc k)
  thus ?case using ErdosNicolasOdd4 
    by blast
qed


lemma ErdosNicolasOdd2:
  \<open>\<forall> n d.  n \<ge> 1 \<and> d \<le> k  \<and> d dvd n  \<longrightarrow> ( \<exists> e. e dvd n \<and> odd e \<and> card (ErdosNicolasSet n d) \<le> card (ErdosNicolasSet n e) )\<close>
proof(induction k)
  case 0
  thus ?case 
    by auto
next
  case (Suc k)
  thus ?case using ErdosNicolasOdd3 by blast
qed

lemma ErdosNicolasOdd1:
  \<open>n \<ge> 1 \<Longrightarrow> d dvd n  \<Longrightarrow> \<exists> e. e dvd n \<and> odd e \<and> card (ErdosNicolasSet n d) \<le> card (ErdosNicolasSet n e) \<close>
  using ErdosNicolasOdd2 
  by (metis   Suc_n_not_le_n dual_order.trans    nat_le_linear  )


proposition ErdosNicolasOdd:
  \<open>n \<ge> 1 \<Longrightarrow> ErdosNicolas n = Max { card (ErdosNicolasSet n d) | d :: nat. d dvd n \<and> odd d}\<close>
proof-
  assume \<open>n \<ge> 1\<close>
  have \<open>{ card (ErdosNicolasSet n d) | d :: nat. d dvd n} \<noteq> {}\<close>
    by blast
  have \<open>\<forall> d. d dvd n \<longrightarrow> d \<le> n\<close> 
    using \<open>1 \<le> n\<close> by auto
  hence \<open>{ card (ErdosNicolasSet n d) | d :: nat. d dvd n} = { card (ErdosNicolasSet n d) | d :: nat. d dvd n \<and> d \<le> n}\<close>
    by blast
  have \<open>finite { d | d :: nat. d dvd n \<and> d \<le> n}\<close>
    using finite_nat_set_iff_bounded_le by blast
  hence \<open>finite { card (ErdosNicolasSet n d) | d :: nat. d dvd n \<and> d \<le> n}\<close>
    by auto
  hence \<open>finite { card (ErdosNicolasSet n d) | d :: nat. d dvd n}\<close>
    using  \<open>{ card (ErdosNicolasSet n d) | d :: nat. d dvd n} = { card (ErdosNicolasSet n d) | d :: nat. d dvd n \<and> d \<le> n}\<close>
    by auto
  have \<open>{ card (ErdosNicolasSet n d) | d :: nat. d dvd n \<and> odd d} \<subseteq> { card (ErdosNicolasSet n d) | d :: nat. d dvd n}\<close>
    by blast
  hence  \<open>Max { card (ErdosNicolasSet n d) | d :: nat. d dvd n \<and> odd d} \<le> Max { card (ErdosNicolasSet n d) | d :: nat. d dvd n}\<close>
  proof -
    have "\<exists>na nb. na = card (ErdosNicolasSet n nb) \<and> nb dvd n \<and> odd nb"
      by (meson odd_one one_dvd)
    thus ?thesis
      by (simp add: Max.subset_imp \<open>finite {card (ErdosNicolasSet n d) |d. d dvd n}\<close> \<open>{card (ErdosNicolasSet n d) |d. d dvd n \<and> odd d} \<subseteq> {card (ErdosNicolasSet n d) |d. d dvd n}\<close>)
  qed

  obtain d::nat where \<open>card (ErdosNicolasSet n d)  = Max { card (ErdosNicolasSet n d) | d :: nat. d dvd n}\<close>
  proof -
    assume a1: "\<And>d. card (ErdosNicolasSet n d) = Max {card (ErdosNicolasSet n d) |d. d dvd n} \<Longrightarrow> thesis"
    have "\<exists>na. Max {card (ErdosNicolasSet n na) |na. na dvd n} = card (ErdosNicolasSet n na)"
      using Max_in \<open>finite {card (ErdosNicolasSet n d) |d. d dvd n}\<close> by auto
    thus ?thesis
      using a1 by force
  qed

  obtain e :: nat where \<open>card (ErdosNicolasSet n d) \<le> card (ErdosNicolasSet n e)\<close> and \<open>e dvd n\<close> and \<open>odd e\<close>
    by (smt CollectD ErdosNicolasOdd1 Max_in \<open>1 \<le> n\<close> \<open>card (ErdosNicolasSet n d) = Max {card (ErdosNicolasSet n d) |d. d dvd n}\<close> \<open>finite {card (ErdosNicolasSet n d) |d. d dvd n}\<close> \<open>{card (ErdosNicolasSet n d) |d. d dvd n} \<noteq> {}\<close>)

  have \<open>card (ErdosNicolasSet n e) \<in> {card (ErdosNicolasSet n d) |d. d dvd n \<and> odd d}\<close>
    using \<open>e dvd n\<close> \<open>odd e\<close> by blast
  hence \<open>card (ErdosNicolasSet n e) \<le> Max {card (ErdosNicolasSet n d) |d. d dvd n \<and> odd d}\<close>
    by (metis (mono_tags, lifting) Max_ge \<open>finite {card (ErdosNicolasSet n d) |d. d dvd n}\<close> \<open>{card (ErdosNicolasSet n d) |d. d dvd n \<and> odd d} \<subseteq> {card (ErdosNicolasSet n d) |d. d dvd n}\<close> finite_subset)
  hence  \<open> Max { card (ErdosNicolasSet n d) | d :: nat. d dvd n} \<le> Max { card (ErdosNicolasSet n d) | d :: nat. d dvd n \<and> odd d}\<close>
    using \<open>card (ErdosNicolasSet n d) = Max {card (ErdosNicolasSet n d) |d. d dvd n}\<close> \<open>card (ErdosNicolasSet n d) \<le> card (ErdosNicolasSet n e)\<close> le_trans subset_refl by linarith
  hence \<open>Max { card (ErdosNicolasSet n d) | d :: nat. d dvd n} = Max { card (ErdosNicolasSet n d) | d :: nat. d dvd n \<and> odd d}\<close>
    using \<open>Max {card (ErdosNicolasSet n d) |d. d dvd n \<and> odd d} \<le> Max {card (ErdosNicolasSet n d) |d. d dvd n}\<close> le_antisym by blast
  show ?thesis 
    using ErdosNicolas_def \<open>Max {card (ErdosNicolasSet n d) |d. d dvd n} = Max {card (ErdosNicolasSet n d) |d. d dvd n \<and> odd d}\<close> by presburger
qed




lemma ErdosNicolasSetOddDivSetLInter:
  fixes n k m d :: nat
  assumes \<open>n = (2::nat)^k*m\<close> and \<open>odd m\<close> and \<open>d dvd n\<close> and \<open>odd d\<close> 
  shows \<open> (ErdosNicolasSet n d) \<inter> (OddDivSet n ((d::real)/(2::real)^(k+1))) = {}\<close>
proof(rule classical)
  assume \<open>\<not> (  (ErdosNicolasSet n d) \<inter> (OddDivSet n ((d::real)/(2::real)^(k+1))) = {} )\<close>
  hence  \<open>(ErdosNicolasSet n d) \<inter> (OddDivSet n ((d::real)/(2::real)^(k+1))) \<noteq> {}\<close>
    by simp
  then obtain x where \<open>x \<in> (ErdosNicolasSet n d) \<inter> (OddDivSet n ((d::real)/(2::real)^(k+1)))\<close>
    by blast
  hence \<open>x \<in> ErdosNicolasSet n d\<close>
    by blast
  from  \<open>x \<in> (ErdosNicolasSet n d) \<inter> (OddDivSet n ((d::real)/(2::real)^(k+1)))\<close>
  have \<open>x \<in> OddDivSet n ((d::real)/(2::real)^(k+1))\<close> 
    by blast
  from  \<open>x \<in> ErdosNicolasSet n d\<close> have \<open>(d::real)/(2::real) < x\<close> 
    using CollectD ErdosNicolasSet_def by fastforce
  from \<open>x \<in> (OddDivSet n ((d::real)/(2::real)^(k+1)))\<close> have \<open>x \<le> (d::real)/(2::real)^(k+1)\<close>
    using CollectD OddDivSet_def by fastforce
  have \<open>(2::real)^1 \<le> (2::real)^(k+1)\<close> 
    by simp
  hence \<open> (d::real)/(2::real)^(k+1) \<le>  (d::real)/(2::real)\<close>  
    by (smt frac_le neq0_conv of_nat_0_less_iff power_one_right semiring_1_class.of_nat_simps(1))
  hence \<open>x < x\<close> using \<open>(d::real)/(2::real) < x\<close>  \<open>x \<le> (d::real)/(2::real)^(k+1)\<close>
    by linarith
  thus ?thesis 
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
  hence \<open>(OddPart x)/(OddPart x) = 1\<close>
    by simp
  have \<open>(2::nat)^j*(OddPart y) < (2::nat)*((2::nat)^i*(OddPart x))\<close>
    using \<open>y < (2::nat)*x\<close>  \<open>x = (2::nat)^i*(OddPart x)\<close>  \<open>y = (2::nat)^j*(OddPart y)\<close>
    by auto
  hence \<open>(2::nat)^j*(OddPart y) < (2::nat)^(i+1)*(OddPart x)\<close>
    by simp
  hence \<open>(2::nat)^j*(OddPart x) < (2::nat)^(i+1)*(OddPart x)\<close>
    using  \<open>OddPart x = OddPart y\<close> by simp
  hence  \<open>(2::nat)^j < (2::nat)^(i+1)\<close>
    using  \<open>(OddPart x)/(OddPart x) = 1\<close> 
    by simp   
  hence \<open>j < i+1\<close> 
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

lemma WLOGErdosNicolasSetOddDivSetInjOnSCaseA:
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


lemma ErdosNicolasSetOddDivSetInjOnSCaseA:
  fixes n k m d x y :: nat
  assumes \<open>n = (2::nat)^k*m\<close> and \<open>odd m\<close> and \<open>d dvd n\<close> and \<open>odd d\<close>
    and  \<open>x \<in>  (ErdosNicolasSet n d)\<close>
    and  \<open>y \<in>  (ErdosNicolasSet n d)\<close>
    and \<open>OddPart x = OddPart y\<close>
  shows \<open>x = y\<close>
  using WLOGErdosNicolasSetOddDivSetInjOnSCaseA assms 
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
  hence \<open>(2::nat)^j dvd (2::nat)^k*m\<close>  
    using  \<open>n = (2::nat)^k*m\<close> 
    by blast
  have \<open>gcd ((2::nat)^j) m = 1\<close> 
    by (meson OddDivPow2 assms(2) dvd_trans gcd_unique_nat one_le_numeral one_le_power)
  hence  \<open>(2::nat)^j dvd (2::nat)^k\<close>
    using \<open>(2::nat)^j dvd (2::nat)^k*m\<close>
    by (metis dvd_triv_right gcd_greatest gcd_mult_distrib_nat semiring_normalization_rules(12))
  hence \<open>(2::nat)^j \<le> (2::nat)^k\<close>
    by (simp add: dvd_imp_le)
  hence \<open>(2::nat)^k*(OddPart d) \<ge> d\<close> using  \<open>(2::nat)^j*(OddPart d) = d\<close> 
    by (metis mult_le_mono1)
  hence \<open>(2::real)^k*(OddPart d) \<ge> d\<close> 
    by (metis  numeral_power_eq_of_nat_cancel_iff of_nat_le_iff of_nat_mult )
  have \<open>(2::real)^k > 0\<close> 
    by simp
  then  show ?thesis using  \<open>(2::real)^k*(OddPart d) \<ge> d\<close>
    by (smt divide_strict_right_mono nonzero_mult_div_cancel_left)
qed


lemma ImpoErdosNicolasSetOddDivSetInjOnSCaseB:
  fixes n k m d :: nat
  assumes \<open>n = (2::nat)^k*m\<close> and \<open>odd m\<close> and \<open>d dvd n\<close> and \<open>odd d\<close>
    and  \<open>x \<in>  (ErdosNicolasSet n d)\<close>
    and  \<open>y \<in> (OddDivSet n ((d::real)/(2::real)^(k+1)))\<close>
  shows \<open>OddPart x \<noteq> OddPart y\<close>
proof-
  have \<open>odd y\<close> 
    using CollectD OddDivSet_def assms(6) by fastforce
  hence \<open>OddPart y = y\<close> 
    by (metis One_nat_def Suc_leI odd_pos preExp2OddPartChar1 preExp2OddPartChar2 preUniqnessOddEven_OddPartOneSide)
  have \<open>y \<le> ((d::real)/(2::real)^(k+1))\<close> 
    using CollectD OddDivSet_def assms(6) by fastforce
  have \<open>x dvd n\<close> 
    using CollectD ErdosNicolasSet_def assms(5) by fastforce
  hence \<open>OddPart x \<ge> x / (2::real)^k\<close> 
    using OddPartBoundDiv assms(1) assms(2) by blast
  from  \<open>x \<in>  (ErdosNicolasSet n d)\<close> 
  have \<open>2*x > d\<close> 
    using CollectD ErdosNicolasSet_def by fastforce 
  hence \<open>x > (d::real)/(2::real)\<close>
    by linarith
  hence \<open> x / (2::real)^k  > ((d::real)/(2::real))/(2::real)^k\<close>
    by (smt divide_strict_right_mono zero_less_power)
  hence \<open> x / (2::real)^k  > (d::real)/((2::real)*(2::real)^k)\<close>
    by simp
  hence \<open> x / (2::real)^k  > (d::real)/((2::real)^(k+1))\<close>
    by simp
  hence \<open>OddPart x > (d::real)/((2::real)^(k+1))\<close> 
    using \<open>real x / 2 ^ k \<le> real (OddPart x)\<close> by linarith
  hence \<open>OddPart x > y\<close> 
    using \<open>real y \<le> real d / 2 ^ (k + 1)\<close> by linarith 
  thus ?thesis 
    using \<open>OddPart y = y\<close> by linarith
qed

lemma ErdosNicolasSetOddDivSetInjOnSCaseB:
  fixes n k m d :: nat
  assumes \<open>n = (2::nat)^k*m\<close> and \<open>odd m\<close> and \<open>d dvd n\<close> and \<open>odd d\<close>
    and  \<open>x \<in>  (ErdosNicolasSet n d)\<close>
    and  \<open> y \<in> (OddDivSet n ((d::real)/(2::real)^(k+1)))\<close>
    and \<open>OddPart x = OddPart y\<close>
  shows \<open>x = y\<close>
  using assms ImpoErdosNicolasSetOddDivSetInjOnSCaseB 
  by blast


lemma ErdosNicolasSetOddDivSetInjOnSCaseC:
  fixes n k m d :: nat
  assumes \<open>n = (2::nat)^k*m\<close> and \<open>odd m\<close> and \<open>d dvd n\<close> and \<open>odd d\<close>
    and  \<open> x \<in> (OddDivSet n ((d::real)/(2::real)^(k+1)))\<close>
    and  \<open>y \<in> (OddDivSet n ((d::real)/(2::real)^(k+1)))\<close>
    and \<open>OddPart x = OddPart y\<close>
  shows \<open>x = y\<close>
proof-
  have \<open>odd x\<close> 
    by (metis (no_types, lifting) OddDivSet_def One_nat_def add.right_neutral add_Suc_right assms(5) mem_Collect_eq)
  hence \<open>OddPart x = x\<close> 
    by (metis One_nat_def Suc_leI odd_pos preExp2OddPartChar1 preExp2OddPartChar2 preUniqnessOddEven_OddPartOneSide)
  have \<open>odd y\<close> 
    using CollectD OddDivSet_def assms(6) by fastforce
  hence \<open>OddPart y = y\<close>
    by (metis One_nat_def Suc_leI odd_pos preExp2OddPartChar1 preExp2OddPartChar2 preUniqnessOddEven_OddPartOneSide)
  show ?thesis 
    using \<open>OddPart x = x\<close> \<open>OddPart y = y\<close> assms(7) by linarith
qed


lemma ErdosNicolasSetOddDivSetInjOnS:
  fixes n k m d :: nat
  assumes \<open>n = (2::nat)^k*m\<close> and \<open>odd m\<close> and \<open>d dvd n\<close> and \<open>odd d\<close>
    and  \<open>x \<in>  (ErdosNicolasSet n d) \<or> x \<in> (OddDivSet n ((d::real)/(2::real)^(k+1)))\<close>
    and  \<open>y \<in>  (ErdosNicolasSet n d) \<or> y \<in> (OddDivSet n ((d::real)/(2::real)^(k+1)))\<close>
    and \<open>OddPart x = OddPart y\<close>
  shows \<open>x = y\<close>
  using assms ErdosNicolasSetOddDivSetInjOnSCaseA ErdosNicolasSetOddDivSetInjOnSCaseB
    ErdosNicolasSetOddDivSetInjOnSCaseC 
  by metis

lemma ErdosNicolasSetOddDivSetInjOn:
  fixes n k m d :: nat
  assumes \<open>n = (2::nat)^k*m\<close> and \<open>odd m\<close> and \<open>d dvd n\<close> and \<open>odd d\<close> 
  shows \<open> inj_on OddPart ((ErdosNicolasSet n d) \<union> (OddDivSet n ((d::real)/(2::real)^(k+1))))\<close>
  using ErdosNicolasSetOddDivSetInjOnS inj_on_def assms 
  by (smt UnE)

lemma OddPartErdosNicolasSet:
  \<open> OddPart ` ((ErdosNicolasSet n d) \<union> (OddDivSet n ((d::real)/(2::real)^(k+1)))) = (OddPart ` ((ErdosNicolasSet n d))) \<union> (OddPart ` (OddDivSet n ((d::real)/(2::real)^(k+1))))\<close>
  by (simp add: image_Un)

lemma ErdosNicolasSetOddDivSetSurjAIS:
  fixes n k m d :: nat
  assumes \<open>n = (2::nat)^k*m\<close> and \<open>odd m\<close> and \<open>d dvd n\<close> and \<open>odd d\<close> 
    and \<open>x \<in> ((ErdosNicolasSet n d))\<close> 
  shows \<open>OddPart x \<in> (OddDivSet n (d::real))\<close>
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
  hence \<open>odd (OddPart x)\<close>
    by (metis One_nat_def Suc_leI \<open>x dvd n\<close> assms(1) assms(2) dvd_pos_nat nat_0_less_mult_iff odd_pos pos2 preExp2OddPartChar1 zero_less_power)
  show ?thesis 
    by (simp add: OddDivSet_def \<open>OddPart x \<le> d\<close> \<open>OddPart x dvd n\<close> \<open>odd (OddPart x)\<close>)
qed


lemma ErdosNicolasSetOddDivSetSurjAI:
  fixes n k m d :: nat
  assumes \<open>n = (2::nat)^k*m\<close> and \<open>odd m\<close> and \<open>d dvd n\<close> and \<open>odd d\<close> 
  shows \<open>  (OddPart ` ((ErdosNicolasSet n d))) \<subseteq> (OddDivSet n (d::real))\<close>
  using ErdosNicolasSetOddDivSetSurjAIS assms(1) assms(2) assms(3) assms(4) by blast

lemma ErdosNicolasSetOddDivSetSurjAIIX:
  fixes n k m d :: nat
  assumes \<open>n = (2::nat)^k*m\<close> and \<open>odd m\<close> and \<open>d dvd n\<close> and \<open>odd d\<close> 
    and \<open>x \<in> (OddPart ` (OddDivSet n ((d::real)/(2::real)^(k+1))))\<close>
  shows \<open> x \<in> (OddDivSet n (d::real))\<close>
proof-
  obtain y::nat where \<open>x = OddPart y\<close> and \<open>y \<in> (OddDivSet n ((d::real)/(2::real)^(k+1)))\<close>
    using assms(5) by blast
  from  \<open>y \<in> (OddDivSet n ((d::real)/(2::real)^(k+1)))\<close>
  have \<open>odd y\<close> 
    by (metis (mono_tags, lifting) CollectD OddDivSet_def One_nat_def add.right_neutral add_Suc_right  one_add_one)
  hence \<open>y \<ge> 1\<close> 
    by (simp add: dvd_imp_le odd_pos)
  hence \<open>y = OddPart y\<close> using  \<open>odd y\<close>
    by (meson OddPartL1 OddPartL1X1 antisym dvd_refl linorder_neqE_nat nat_dvd_not_less odd_pos order_less_imp_le)
  have \<open>y \<le> ((d::real)/(2::real)^(k+1))\<close> 
    using CollectD OddDivSet_def \<open>y \<in> OddDivSet n (real d / 2 ^ (k + 1))\<close> by fastforce
  have \<open>(1::real) \<le> (2::real)^(k+1)\<close> 
    using two_realpow_ge_one by blast 
  have \<open> ((d::real)/(2::real)^(k+1)) \<le> (d::real)/(1::real)\<close> 
    by (smt \<open>1 \<le> 2 ^ (k + 1)\<close> frac_le neq0_conv of_nat_0 of_nat_0_less_iff)    
  then  have \<open> ((d::real)/(2::real)^(k+1)) \<le> (d::real)\<close> 
    by linarith
  then  have \<open>y \<le> (d::real)\<close> 
    using \<open>real y \<le> real d / 2 ^ (k + 1)\<close> by linarith
  hence \<open>x \<le> d\<close> 
    using \<open>x = OddPart y\<close> \<open>y = OddPart y\<close> by linarith
  have \<open>odd x\<close> 
    using \<open>odd y\<close> \<open>x = OddPart y\<close> \<open>y = OddPart y\<close> by auto
  have \<open>x dvd n\<close> 
    using CollectD OddDivSet_def \<open>x = OddPart y\<close> \<open>y = OddPart y\<close> \<open>y \<in> OddDivSet n (real d / 2 ^ (k + 1))\<close> by fastforce
  show ?thesis 
    by (simp add: OddDivSet_def \<open>odd x\<close> \<open>x \<le> d\<close> \<open>x dvd n\<close>)
qed


lemma ErdosNicolasSetOddDivSetSurjAII:
  fixes n k m d :: nat
  assumes \<open>n = (2::nat)^k*m\<close> and \<open>odd m\<close> and \<open>d dvd n\<close> and \<open>odd d\<close> 
  shows \<open>  (OddPart ` (OddDivSet n ((d::real)/(2::real)^(k+1)))) \<subseteq> (OddDivSet n (d::real))\<close>
  using assms ErdosNicolasSetOddDivSetSurjAIIX by blast

lemma ErdosNicolasSetOddDivSetSurjA:
  fixes n k m d :: nat
  assumes \<open>n = (2::nat)^k*m\<close> and \<open>odd m\<close> and \<open>d dvd n\<close> and \<open>odd d\<close> 
  shows \<open>  (OddPart ` ((ErdosNicolasSet n d))) \<union> (OddPart ` (OddDivSet n ((d::real)/(2::real)^(k+1)))) \<subseteq> (OddDivSet n (d::real))\<close>
  using assms ErdosNicolasSetOddDivSetSurjAI ErdosNicolasSetOddDivSetSurjAII 
  by simp

lemma ErdosNicolasSetOddDivSetSurjBI:
  fixes n k m d :: nat
  assumes \<open>n = (2::nat)^k*m\<close> and \<open>odd m\<close> and \<open>d dvd n\<close> and \<open>odd d\<close> 
    and \<open>x \<in> (OddDivSet n (d::real))\<close>
    and \<open>x \<le> ((d::real)/(2::real)^(k+1))\<close>
  shows \<open>x \<in> (OddPart ` (OddDivSet n ((d::real)/(2::real)^(k+1))))\<close>
proof-
  from \<open>x \<in> (OddDivSet n (d::real))\<close>
  have \<open>x dvd n\<close> 
    using CollectD OddDivSet_def by fastforce
  from  \<open>x \<in> (OddDivSet n (d::real))\<close>
  have \<open>odd x\<close> using OddDivSet_def 
    using CollectD by fastforce
  have \<open>x \<ge> 1\<close> 
    by (simp add: Suc_leI \<open>odd x\<close> odd_pos)
  have \<open>x = OddPart x\<close> 
    using \<open>1 \<le> x\<close> \<open>odd x\<close> preExp2OddPartChar1 preExp2OddPartChar2 preUniqnessOddEven_OddPartOneSide by blast
  have \<open>x \<in> (OddDivSet n ((d::real)/(2::real)^(k+1)))\<close>
    by (metis (mono_tags) OddDivSet_def Suc_eq_plus1 \<open>odd x\<close> \<open>x dvd n\<close> assms(6) mem_Collect_eq )
  thus ?thesis 
    using \<open>x = OddPart x\<close> by blast
qed


lemma ErdosNicolasSetOddDivSetSurjBII:
  fixes n k m d :: nat
  assumes \<open>n = (2::nat)^k*m\<close> and \<open>odd m\<close> and \<open>d dvd n\<close> and \<open>odd d\<close> 
    and \<open>x \<in> (OddDivSet n (d::real))\<close>
    and \<open>x > ((d::real)/(2::real)^(k+1))\<close>
  shows \<open>x \<in> (OddPart ` ((ErdosNicolasSet n d)))\<close>
proof-
  from  \<open>x \<in> (OddDivSet n (d::real))\<close>
  have \<open>x dvd n\<close> 
    using CollectD OddDivSet_def by fastforce
  from  \<open>x \<in> (OddDivSet n (d::real))\<close>
  have \<open>odd x\<close> 
    using CollectD OddDivSet_def by fastforce
  hence \<open>x \<ge> 1\<close> 
    by (simp add: dvd_imp_le odd_pos)
  hence \<open>OddPart x = x\<close>
    using  \<open>odd x\<close> 
    by (meson OddPartL1 OddPartL1X1 antisym dvd_refl linorder_neqE_nat nat_dvd_not_less odd_pos order_less_imp_le)
  from \<open>x > ((d::real)/(2::real)^(k+1))\<close>
  have \<open>2^k*x > 2^k*((d::real)/(2::real)^(k+1))\<close>
    by (smt mult_le_cancel_left_pos of_nat_1 of_nat_add of_nat_mult of_nat_power one_add_one zero_less_power)
  hence \<open>2^k*x > (d::real)/(2::real)\<close>
    by simp
  hence \<open>k \<in> {i | i :: nat. 2^i*x > (d::real)/(2::real)}\<close>
    by blast
  hence \<open>{i | i :: nat. 2^i*x > (d::real)/(2::real)} \<noteq> {}\<close>
    by blast
  then obtain j::nat where \<open>j = Inf {i | i :: nat. 2^i*x > (d::real)/(2::real)}\<close>
    by blast
  from \<open>k \<in> {i | i :: nat. 2^i*x > (d::real)/(2::real)}\<close> 
  have \<open>k \<ge> Inf {i | i :: nat. 2^i*x > (d::real)/(2::real)}\<close>
    using cInf_lower
    by (metis \<open>j = Inf {i |i. real d / 2 < real (2 ^ i * x)}\<close> bdd_above_bot)
  hence \<open>k \<ge> j\<close> 
    using \<open>j = Inf {i |i. real d / 2 < real (2 ^ i * x)}\<close> by blast
  hence \<open>2^j dvd n\<close> 
    using assms(1) dvd_triv_left power_le_dvd by blast
  hence \<open>gcd x (2^j) = 1\<close> 
    by (meson OddDivPow2 \<open>odd x\<close> dvd_trans gcd_unique_nat one_le_numeral one_le_power)
  hence \<open>2^j*x dvd n\<close> using  \<open>2^j dvd n\<close> \<open>x dvd n\<close> 
    by (smt TrapezoidalNumbersNec2_5 \<open>j \<le> k\<close> \<open>odd x\<close> assms(1) division_decomp dvd_mult le_imp_power_dvd mult_dvd_mono preUniqnessOddEven_OddPartOneSide)
  from  \<open>j = Inf {i | i :: nat. 2^i*x > (d::real)/(2::real)}\<close> \<open> {i | i :: nat. 2^i*x > (d::real)/(2::real)} \<noteq> {}\<close>
  have \<open>j \<in> {i | i :: nat. 2^i*x > (d::real)/(2::real)}\<close>
    using Inf_nat_def1
    by presburger
  hence \<open>2^j*x > (d::real)/(2::real)\<close>
    by blast
  have \<open>d \<ge> x\<close> 
    by (metis (no_types, lifting) CollectD OddDivSet_def assms(5) of_nat_le_iff)
  have \<open>d \<ge> 2^j*x\<close>
  proof(cases \<open>j = 0\<close>)
    case True
    thus ?thesis using \<open>d \<ge> x\<close> \<open>j = 0\<close> by simp
  next
    case False
    hence \<open>j \<noteq> 0\<close> by blast
    then obtain p::nat where \<open>Suc p = j\<close> 
      by (metis lessI less_Suc_eq_0_disj)
    have \<open>d \<ge> 2^j*x\<close>
    proof(rule classical)
      assume \<open>\<not>(d \<ge> 2^j*x)\<close>
      hence \<open>2^(Suc p)*x > d\<close> using \<open>Suc p = j\<close> by auto
      hence \<open>2*(2^p*x) > d\<close> 
        by auto
      hence \<open>2^p*x > (d::real)/(2::real)\<close> 
        by linarith
      hence \<open>p \<in> {i | i :: nat. 2^i*x > (d::real)/(2::real)}\<close>
        by blast
      have \<open>p < j\<close> 
        using \<open>Suc p = j\<close> by blast
      have \<open>p \<ge> j\<close> 
        by (metis \<open>j = Inf {i |i. real d / 2 < real (2 ^ i * x)}\<close> \<open>p \<in> {i |i. real d / 2 < real (2 ^ i * x)}\<close> bdd_above_bot cInf_lower)
      show ?thesis using  \<open>p < j\<close> \<open>p \<ge> j\<close>  by auto
    qed
    thus ?thesis by blast
  qed
  from \<open>2^j*x > (d::real)/(2::real)\<close>
  have \<open>2^j*x > d/2\<close>
    by simp
  hence \<open>2*(2^j*x) > 2*(d/2)\<close> by simp
  hence  \<open>2*(2^j*x) > d*((2::nat)/2)\<close> by simp
  hence  \<open>2*(2^j*x) > d*(1::nat)\<close> 
    by (simp add: of_nat_less_imp_less)
  hence  \<open>2*(2^j*x) > d\<close> 
    by linarith 
  have \<open>2^j*x \<in> ((ErdosNicolasSet n d))\<close>
    using \<open>d \<ge> 2^j*x\<close> \<open>2*(2^j*x) > d\<close>  \<open>x dvd n\<close> ErdosNicolasSet_def 
    by (simp add: \<open>ErdosNicolasSet \<equiv> \<lambda>n d. {e |e. e dvd n \<and> e \<le> d \<and> d < 2 * e}\<close> \<open>2 ^ j * x dvd n\<close>)
  have \<open>OddPart (2^j*x) = x\<close> using \<open>odd x\<close> \<open>x \<ge> 1\<close> UniqnessOddEven
    by (smt dvd_mult_unit_iff' le_eq_less_or_eq less_1_mult nat_dvd_1_iff_1 one_le_numeral one_le_power preExp2OddPartChar1 preExp2OddPartChar2 preUniqnessOddEven_OddPartOneSide semiring_normalization_rules(12))
  from  \<open>2^j*x \<in> (ErdosNicolasSet n d)\<close> \<open>OddPart (2^j*x) = x\<close>
  have \<open>x \<in> OddPart ` (ErdosNicolasSet n d)\<close> 
    by (metis image_eqI)
  thus ?thesis by blast
qed

lemma ErdosNicolasSetOddDivSetSurjB:
  fixes n k m d :: nat
  assumes \<open>n = (2::nat)^k*m\<close> and \<open>odd m\<close> and \<open>d dvd n\<close> and \<open>odd d\<close> 
  shows \<open>(OddDivSet n (d::real)) \<subseteq>  (OddPart ` ((ErdosNicolasSet n d))) \<union> (OddPart ` (OddDivSet n ((d::real)/(2::real)^(k+1))))\<close>
  by (smt ErdosNicolasSetOddDivSetSurjBI ErdosNicolasSetOddDivSetSurjBII UnCI assms(1) assms(2) assms(3) assms(4) subsetI)

lemma ErdosNicolasSetOddDivSetSurj:
  fixes n k m d :: nat
  assumes \<open>n = (2::nat)^k*m\<close> and \<open>odd m\<close> and \<open>d dvd n\<close> and \<open>odd d\<close> 
  shows \<open> OddPart ` ((ErdosNicolasSet n d) \<union> (OddDivSet n ((d::real)/(2::real)^(k+1)))) = (OddDivSet n (d::real))\<close>
  using assms ErdosNicolasSetOddDivSetSurjA ErdosNicolasSetOddDivSetSurjB OddPartErdosNicolasSet
  by (simp add: subset_antisym)


lemma ErdosNicolasSetOddDivSetBij:
  fixes n k m d :: nat
  assumes \<open>n = (2::nat)^k*m\<close> and \<open>odd m\<close> and \<open>d dvd n\<close> and \<open>odd d\<close> 
  shows \<open> bij_betw OddPart ((ErdosNicolasSet n d) \<union> (OddDivSet n ((d::real)/(2::real)^(k+1)))) (OddDivSet n (d::real))\<close>
  using assms ErdosNicolasSetOddDivSetInjOn ErdosNicolasSetOddDivSetSurj 
  by (simp add: bij_betw_def)

lemma ErdosNicolasSetOddDivSetL:
  fixes n k m d :: nat
  assumes \<open>n = (2::nat)^k*m\<close> and \<open>odd m\<close> and \<open>d dvd n\<close> and \<open>odd d\<close> 
  shows \<open>card (ErdosNicolasSet n d) + (card (OddDivSet n ((d::real)/(2::real)^(k+1)))) = (card (OddDivSet n (d::real)))\<close>
proof-
  have \<open>finite (ErdosNicolasSet n d)\<close> 
    by (metis (no_types, lifting) CollectD ErdosNicolasSet_def finite_nat_set_iff_bounded_le )

  have \<open>finite (OddDivSet n (d::real))\<close> using OddDivSet_def 
    by (metis (no_types, lifting) assms(1) assms(2) dvd_0_right dvd_imp_le finite_nat_set_iff_bounded_le mem_Collect_eq mult_eq_0_iff neq0_conv pos2 zero_less_power)

  have \<open>finite (OddDivSet n ((d::real)/(2::real)^(k+1)))\<close> using OddDivSet_def
    by (metis (no_types, lifting) assms(1) assms(2) dvd_0_right dvd_imp_le finite_nat_set_iff_bounded_le mem_Collect_eq mult_eq_0_iff neq0_conv pos2 zero_less_power)

  have \<open>card ((ErdosNicolasSet n d) \<union> (OddDivSet n ((d::real)/(2::real)^(k+1)))) = card (OddDivSet n (d::real))\<close>
    using ErdosNicolasSetOddDivSetBij 
    by (meson assms(1) assms(2) assms(3) assms(4) bij_betw_same_card)

  have \<open> (ErdosNicolasSet n d) \<inter> (OddDivSet n ((d::real)/(2::real)^(k+1))) = {}\<close>
    using ErdosNicolasSetOddDivSetLInter 
    using assms(1) assms(2) assms(3) assms(4) by blast
  show ?thesis 
    using \<open>ErdosNicolasSet n d \<inter> OddDivSet n (real d / 2 ^ (k + 1)) = {}\<close> \<open>card (ErdosNicolasSet n d \<union> OddDivSet n (real d / 2 ^ (k + 1))) = card (OddDivSet n (real d))\<close> \<open>finite (ErdosNicolasSet n d)\<close> \<open>finite (OddDivSet n (real d / 2 ^ (k + 1)))\<close> card_Un_disjoint by fastforce
qed

lemma ErdosNicolasSetOddDivSetLL:
  fixes n k m d :: nat
  assumes \<open>n = (2::nat)^k*m\<close> and \<open>odd m\<close> and \<open>d dvd n\<close> and \<open>odd d\<close> 
  shows \<open>card (ErdosNicolasSet n d) = (card (OddDivSet n (d::real))) - (card (OddDivSet n ((d::real)/(2::real)^(k+1))))\<close>
  using ErdosNicolasSetOddDivSetL assms 
  by (metis diff_add_inverse2)


proposition ErdosNicolasOddDivSet:
  fixes n k m :: nat
  assumes \<open>n = (2::nat)^k*m\<close> and \<open>odd m\<close> 
  shows \<open>ErdosNicolas n
   = Max{ (card (OddDivSet n (real d))) - (card (OddDivSet n ((real d)/(2::real)^(k+1)))) 
          |d :: nat. d dvd n \<and> odd d}\<close>
proof-
  have \<open>n \<ge> 1\<close> 
    by (simp add: Suc_leI assms(1) assms(2) odd_pos)
  hence \<open>ErdosNicolas n = Max { card (ErdosNicolasSet n d) | d :: nat. d dvd n \<and> odd d}\<close>
    using ErdosNicolasOdd by auto
  have \<open>\<forall> d::nat. d dvd n \<and> odd d \<longrightarrow> card (ErdosNicolasSet n d) = (card (OddDivSet n (d::real))) - (card (OddDivSet n ((d::real)/(2::real)^(k+1))))\<close>
    using ErdosNicolasSetOddDivSetLL assms(1) assms(2) by blast
  thus ?thesis using  \<open>ErdosNicolas n = Max { card (ErdosNicolasSet n d) | d :: nat. d dvd n \<and> odd d}\<close>
    by (smt Collect_cong)
qed



lemma preErdosNicolasSetDiffIncl:
  fixes n k m :: nat
  assumes \<open>n = (2::nat)^k*m\<close> and \<open>odd m\<close> and \<open>d dvd n\<close> and \<open>odd d\<close> 
  shows \<open>(OddDivSet n ((real d)/(2::real)^(k+1))) \<subseteq> (OddDivSet n (real d))\<close>
proof-
  have \<open>(OddDivSet n (real d)) = {e | e::nat. e dvd n \<and> odd e \<and> e \<le> (real d)}\<close> 
    using OddDivSet_def by presburger
  have \<open>(OddDivSet n ((real d)/(2::real)^(k+1))) = {e | e::nat. e dvd n \<and> odd e \<and> e \<le> (real d)/(2::real)^(k+1)}\<close> 
    using OddDivSet_def by presburger
  have \<open>(real d)/(2::real)^(k+1) \<le> (real d)\<close> 
    by (smt assms(4) div_by_1 frac_le odd_pos of_nat_0_less_iff one_le_power)
  hence \<open>\<forall> e :: nat. e \<le> (real d)/(2::real)^(k+1) \<longrightarrow> e \<le> (real d)\<close> 
    using order_trans by blast
  show ?thesis using  \<open>\<forall> e :: nat. e \<le> (real d)/(2::real)^(k+1) \<longrightarrow> e \<le> (real d)\<close>
      \<open>(OddDivSet n (real d)) = {e | e::nat. e dvd n \<and> odd e \<and> e \<le> (real d)}\<close> 
      \<open>(OddDivSet n ((real d)/(2::real)^(k+1))) = {e | e::nat. e dvd n \<and> odd e \<and> e \<le> (real d)/(2::real)^(k+1)}\<close> 
    by blast
qed


lemma preErdosNicolasSetDiff:
  fixes n k m :: nat
  assumes \<open>n = (2::nat)^k*m\<close> and \<open>odd m\<close> and \<open>d dvd n\<close> and \<open>odd d\<close> 
  shows \<open>ErdosNicolasSetOdd n k d  = (OddDivSet n (real d)) - (OddDivSet n ((real d)/(2::real)^(k+1)))\<close>
proof-
  have \<open>(OddDivSet n (real d)) = {e | e::nat. e dvd n \<and> odd e \<and> e \<le> (real d)}\<close> 
    using OddDivSet_def by presburger
  hence \<open>(OddDivSet n (real d)) = {e | e::nat. e dvd n \<and> odd e \<and> e \<le>  d}\<close> 
    by auto
  have \<open>(2::nat)^(k+1) > 0\<close> 
    by simp
  have \<open>\<forall> e :: nat.  e \<le> (real d)/(2::real)^(k+1) \<longleftrightarrow> e \<le> d/(2::nat)^(k+1)\<close>
    by simp
  hence \<open>\<forall> e :: nat.  e \<le> (real d)/(2::real)^(k+1) \<longleftrightarrow> e*(2::nat)^(k+1) \<le> (d/(2::nat)^(k+1))*(2::nat)^(k+1)\<close>
    using  \<open>(2::nat)^(k+1) > 0\<close>  
    by (smt of_nat_0_less_iff of_nat_mult real_mult_less_iff1)
  hence \<open>\<forall> e :: nat.  e \<le> (real d)/(2::real)^(k+1) \<longleftrightarrow> e*(2::nat)^(k+1) \<le> d*((2::nat)^(k+1)/(2::nat)^(k+1))\<close>
    by simp
  hence  \<open>\<forall> e :: nat.  e \<le> (real d)/(2::real)^(k+1) \<longleftrightarrow> e*(2::nat)^(k+1) \<le> d*1\<close>
    by simp
  hence  \<open>\<forall> e :: nat.  e \<le> (real d)/(2::real)^(k+1) \<longleftrightarrow> e*(2::nat)^(k+1) \<le> d\<close>
    by simp
  have \<open>(OddDivSet n ((real d)/(2::real)^(k+1))) = {e | e::nat. e dvd n \<and> odd e \<and> e \<le> (real d)/(2::real)^(k+1)}\<close>
    using OddDivSet_def by presburger
  hence  \<open>(OddDivSet n ((real d)/(2::real)^(k+1))) = {e | e::nat. e dvd n \<and> odd e \<and> e*(2::nat)^(k+1) \<le> d }\<close>
    using  \<open>\<forall> e :: nat.  e \<le> (real d)/(2::real)^(k+1) \<longleftrightarrow> e*(2::nat)^(k+1) \<le> d\<close> 
    by (smt Collect_cong of_nat_le_iff of_nat_mult) 
  from  \<open>(OddDivSet n ((real d)/(2::real)^(k+1))) = {e | e::nat. e dvd n \<and> odd e \<and> e*(2::nat)^(k+1) \<le> d }\<close>
  have \<open> - (OddDivSet n ((real d)/(2::real)^(k+1))) = {e | e::nat. \<not>(e dvd n \<and> odd e \<and> e*(2::nat)^(k+1) \<le> d) }\<close>
    by auto
  from  \<open>(OddDivSet n (real d)) = {e | e::nat. e dvd n \<and> odd e \<and> e \<le> d}\<close>
    \<open> - (OddDivSet n ((real d)/(2::real)^(k+1))) = {e | e::nat. \<not>(e dvd n \<and> odd e \<and> e*(2::nat)^(k+1) \<le> d) }\<close>
  have \<open>(OddDivSet n (real d)) - (OddDivSet n ((real d)/(2::real)^(k+1)))
        = {e | e::nat. e dvd n \<and> odd e \<and> e \<le> d} \<inter> {e | e::nat. \<not>(e dvd n \<and> odd e \<and> e*(2::nat)^(k+1) \<le> d) }\<close>
    by auto    
  hence  \<open>(OddDivSet n (real d)) - (OddDivSet n ((real d)/(2::real)^(k+1)))
        = {e | e::nat. (e dvd n \<and> odd e \<and> e \<le> d) \<and>  \<not>(e dvd n \<and> odd e \<and> e*(2::nat)^(k+1) \<le> d) }\<close>
    by blast
  hence   \<open>(OddDivSet n (real d)) - (OddDivSet n ((real d)/(2::real)^(k+1)))
        = {e | e::nat. e dvd n \<and> odd e \<and> e \<le> d \<and>  \<not>( e*(2::nat)^(k+1) \<le> d) }\<close>
    by auto
  hence   \<open>(OddDivSet n (real d)) - (OddDivSet n ((real d)/(2::real)^(k+1)))
        = {e | e::nat. e dvd n \<and> odd e \<and> e \<le> d \<and>  d < 2^(k+1)*e }\<close>
    by (smt Collect_cong Groups.mult_ac(2) linorder_not_le)
  have \<open>ErdosNicolasSetOdd n k d = {e | e::nat. e dvd n \<and> odd e \<and>  e \<le> d \<and> d < 2^(k+1)*e}\<close>
    using ErdosNicolasSetOdd_def by presburger
  show ?thesis 
    using \<open>ErdosNicolasSetOdd n k d = {e |e. e dvd n \<and> odd e \<and> e \<le> d \<and> d < 2 ^ (k + 1) * e}\<close> \<open>OddDivSet n (real d) - OddDivSet n (real d / 2 ^ (k + 1)) = {e |e. e dvd n \<and> odd e \<and> e \<le> d \<and> d < 2 ^ (k + 1) * e}\<close> by auto
qed

lemma ErdosNicolasSetDiff:
  fixes n k m :: nat
  assumes \<open>n = (2::nat)^k*m\<close> and \<open>odd m\<close> and \<open>d dvd n\<close> and \<open>odd d\<close> 
  shows \<open>card (ErdosNicolasSetOdd n k d) = (card (OddDivSet n (real d))) - (card (OddDivSet n ((real d)/(2::real)^(k+1))))\<close>
proof-
  have \<open>finite (ErdosNicolasSetOdd n k d)\<close> 
    by (metis (no_types, lifting) CollectD ErdosNicolasSetOdd_def finite_nat_set_iff_bounded_le   )
  have \<open>finite (OddDivSet n (real d))\<close> 
    by (metis (no_types, lifting) CollectD OddDivSet_def finite_nat_set_iff_bounded_le of_nat_le_iff) 
  have \<open>(OddDivSet n ((real d)/(2::real)^(k+1))) \<subseteq> (OddDivSet n (real d))\<close> 
    using assms(1) assms(2) assms(3) assms(4) preErdosNicolasSetDiffIncl by blast
  hence \<open>finite (OddDivSet n ((real d)/(2::real)^(k+1)))\<close> using \<open>finite (OddDivSet n (real d))\<close> 
    by (meson finite_nat_set_iff_bounded_le subsetCE)
  have  \<open>ErdosNicolasSetOdd n k d  = (OddDivSet n (real d)) - (OddDivSet n ((real d)/(2::real)^(k+1)))\<close>
    using assms(1) assms(2) assms(3) assms(4) preErdosNicolasSetDiff by blast
  show ?thesis 
    using \<open>ErdosNicolasSetOdd n k d = OddDivSet n (real d) - OddDivSet n (real d / 2 ^ (k + 1))\<close> \<open>OddDivSet n (real d / 2 ^ (k + 1)) \<subseteq> OddDivSet n (real d)\<close> \<open>finite (OddDivSet n (real d / 2 ^ (k + 1)))\<close> card_Diff_subset by auto
qed

section {* Main Result *}

theorem ErdosNicolasOddDivSetOdd:
  fixes n k m :: nat
  assumes \<open>n = (2::nat)^k*m\<close> and \<open>odd m\<close> 
  shows \<open>ErdosNicolas n = Max { card (ErdosNicolasSetOdd n k d) | d :: nat. d dvd n \<and> odd d}\<close>
proof-
  have \<open>ErdosNicolas n
   = Max{ (card (OddDivSet n (real d))) - (card (OddDivSet n ((real d)/(2::real)^(k+1)))) 
          |d :: nat. d dvd n \<and> odd d}\<close> 
    using ErdosNicolasOddDivSet assms(1) assms(2) by auto
  have \<open>\<forall> d :: nat. d dvd n \<and> odd d \<longrightarrow> card (ErdosNicolasSetOdd n k d)  = (card (OddDivSet n (real d))) - (card (OddDivSet n ((real d)/(2::real)^(k+1))))\<close>
    using ErdosNicolasSetDiff assms(1) assms(2) by blast
  show ?thesis  using  \<open>ErdosNicolas n
   = Max{ (card (OddDivSet n (real d))) - (card (OddDivSet n ((real d)/(2::real)^(k+1)))) 
          |d :: nat. d dvd n \<and> odd d}\<close> 
      \<open>\<forall> d :: nat. d dvd n \<and> odd d \<longrightarrow> card (ErdosNicolasSetOdd n k d)  = (card (OddDivSet n (real d))) - (card (OddDivSet n ((real d)/(2::real)^(k+1))))\<close>
    by (smt Collect_cong)
qed

end


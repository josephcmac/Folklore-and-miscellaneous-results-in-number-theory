(*
Title: The Erdos-Nicolas function and the odd divisors
Author: Jose Manuel Rodriguez Caballero

The Erdos-Nicolas function is defined as follows:

definition ErdosNicolasSet :: \<open> nat \<Rightarrow> nat \<Rightarrow> nat set \<close> 
  where \<open>ErdosNicolasSet \<equiv> \<lambda> n :: nat. \<lambda> d :: nat.
 {e | e :: nat. e dvd n \<and> e \<le> d \<and> d < 2*e}\<close>

definition ErdosNicolas :: \<open>nat \<Rightarrow> nat\<close>
  where \<open>ErdosNicolas \<equiv> \<lambda> n :: nat. Max { card (ErdosNicolasSet n d) | d :: nat. d dvd n}\<close>


We will prove that we can restrict ourselves to the odd divisors in
the definition of ErdosNicolas:

theorem ErdosNicolasOdd:
\<open>n \<ge> 1 \<Longrightarrow> ErdosNicolas n = Max { card (ErdosNicolasSet n d) | d :: nat. d dvd n \<and> odd d}\<close>


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


theory ErdosNicolasOdd

imports Complex_Main 


begin

definition ErdosNicolasSet :: \<open> nat \<Rightarrow> nat \<Rightarrow> nat set \<close> 
  where \<open>ErdosNicolasSet \<equiv> \<lambda> n :: nat. \<lambda> d :: nat.
 {e | e :: nat. e dvd n \<and> e \<le> d \<and> d < 2*e}\<close>

definition ErdosNicolas :: \<open>nat \<Rightarrow> nat\<close>
  where \<open>ErdosNicolas \<equiv> \<lambda> n :: nat. Max { card (ErdosNicolasSet n d) | d :: nat. d dvd n}\<close>




section {* Auxiliary Results *}


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
  then have  \<open>\<forall> j. j \<in> (ErdosNicolasSet n e) \<longrightarrow> j \<noteq> d\<close> 
    using  \<open>e < d\<close> 
     less_le_trans by blast
  then show ?thesis 
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
  then have \<open>finite((ErdosNicolasSet n e) - (ErdosNicolasSet n d))\<close>
    by blast
  have \<open>d div 2 \<in> (ErdosNicolasSet n e) - (ErdosNicolasSet n d)\<close> 
    using ErdosNicolasOdd7BXYFusion assms(1) assms(2) assms(3) assms(4) assms(5) assms(6) by blast
  then show ?thesis 
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
  then have \<open>card((ErdosNicolasSet n d) - (ErdosNicolasSet n e)) \<le> card((ErdosNicolasSet n e) - (ErdosNicolasSet n d)) \<close>
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
  then show ?thesis 
    using \<open>e < d\<close> \<open>e dvd n\<close> assms(2) less_le_trans by auto
qed

lemma ErdosNicolasOdd3:
  assumes \<open>\<forall> n d.  n \<ge> 1 \<and> d \<le> k  \<and> d dvd n  \<longrightarrow> ( \<exists> e. e dvd n \<and> odd e \<and> card (ErdosNicolasSet n d) \<le> card (ErdosNicolasSet n e) )\<close>
and \<open>n \<ge> 1\<close> and \<open>d \<le> Suc k\<close>  and \<open>d dvd n\<close>
shows \<open>\<exists> e. e dvd n \<and> odd e \<and> card (ErdosNicolasSet n d) \<le> card (ErdosNicolasSet n e)\<close>
proof(induction k)
case 0
then show ?case 
  by (smt ErdosNicolasOdd4 assms(1) assms(2) assms(3) assms(4) order_refl order_trans)
next
  case (Suc k)
  then show ?case using ErdosNicolasOdd4 
    by blast
qed


lemma ErdosNicolasOdd2:
\<open>\<forall> n d.  n \<ge> 1 \<and> d \<le> k  \<and> d dvd n  \<longrightarrow> ( \<exists> e. e dvd n \<and> odd e \<and> card (ErdosNicolasSet n d) \<le> card (ErdosNicolasSet n e) )\<close>
proof(induction k)
  case 0
  then show ?case 
    by auto
next
  case (Suc k)
  then show ?case using ErdosNicolasOdd3 by blast
qed

lemma ErdosNicolasOdd1:
\<open>n \<ge> 1 \<Longrightarrow> d dvd n  \<Longrightarrow> \<exists> e. e dvd n \<and> odd e \<and> card (ErdosNicolasSet n d) \<le> card (ErdosNicolasSet n e) \<close>
  using ErdosNicolasOdd2 
  by (metis   Suc_n_not_le_n dual_order.trans    nat_le_linear  )


theorem ErdosNicolasOdd:
\<open>n \<ge> 1 \<Longrightarrow> ErdosNicolas n = Max { card (ErdosNicolasSet n d) | d :: nat. d dvd n \<and> odd d}\<close>
proof-
  assume \<open>n \<ge> 1\<close>
  have \<open>{ card (ErdosNicolasSet n d) | d :: nat. d dvd n} \<noteq> {}\<close>
    by blast
  have \<open>\<forall> d. d dvd n \<longrightarrow> d \<le> n\<close> 
    using \<open>1 \<le> n\<close> by auto
  then have \<open>{ card (ErdosNicolasSet n d) | d :: nat. d dvd n} = { card (ErdosNicolasSet n d) | d :: nat. d dvd n \<and> d \<le> n}\<close>
    by blast
    have \<open>finite { d | d :: nat. d dvd n \<and> d \<le> n}\<close>
      using finite_nat_set_iff_bounded_le by blast
    then have \<open>finite { card (ErdosNicolasSet n d) | d :: nat. d dvd n \<and> d \<le> n}\<close>
      by auto
  then have \<open>finite { card (ErdosNicolasSet n d) | d :: nat. d dvd n}\<close>
    using  \<open>{ card (ErdosNicolasSet n d) | d :: nat. d dvd n} = { card (ErdosNicolasSet n d) | d :: nat. d dvd n \<and> d \<le> n}\<close>
    by auto
  have \<open>{ card (ErdosNicolasSet n d) | d :: nat. d dvd n \<and> odd d} \<subseteq> { card (ErdosNicolasSet n d) | d :: nat. d dvd n}\<close>
    by blast
  then have  \<open>Max { card (ErdosNicolasSet n d) | d :: nat. d dvd n \<and> odd d} \<le> Max { card (ErdosNicolasSet n d) | d :: nat. d dvd n}\<close>
proof -
have "\<exists>na nb. na = card (ErdosNicolasSet n nb) \<and> nb dvd n \<and> odd nb"
  by (meson odd_one one_dvd)
  then show ?thesis
    by (simp add: Max.subset_imp \<open>finite {card (ErdosNicolasSet n d) |d. d dvd n}\<close> \<open>{card (ErdosNicolasSet n d) |d. d dvd n \<and> odd d} \<subseteq> {card (ErdosNicolasSet n d) |d. d dvd n}\<close>)
qed

  obtain d::nat where \<open>card (ErdosNicolasSet n d)  = Max { card (ErdosNicolasSet n d) | d :: nat. d dvd n}\<close>
      proof -
          assume a1: "\<And>d. card (ErdosNicolasSet n d) = Max {card (ErdosNicolasSet n d) |d. d dvd n} \<Longrightarrow> thesis"
            have "\<exists>na. Max {card (ErdosNicolasSet n na) |na. na dvd n} = card (ErdosNicolasSet n na)"
                using Max_in \<open>finite {card (ErdosNicolasSet n d) |d. d dvd n}\<close> by auto
                then show ?thesis
                    using a1 by force
     qed

  obtain e :: nat where \<open>card (ErdosNicolasSet n d) \<le> card (ErdosNicolasSet n e)\<close> and \<open>e dvd n\<close> and \<open>odd e\<close>
    by (smt CollectD ErdosNicolasOdd1 Max_in \<open>1 \<le> n\<close> \<open>card (ErdosNicolasSet n d) = Max {card (ErdosNicolasSet n d) |d. d dvd n}\<close> \<open>finite {card (ErdosNicolasSet n d) |d. d dvd n}\<close> \<open>{card (ErdosNicolasSet n d) |d. d dvd n} \<noteq> {}\<close>)

  have \<open>card (ErdosNicolasSet n e) \<in> {card (ErdosNicolasSet n d) |d. d dvd n \<and> odd d}\<close>
    using \<open>e dvd n\<close> \<open>odd e\<close> by blast
  then have \<open>card (ErdosNicolasSet n e) \<le> Max {card (ErdosNicolasSet n d) |d. d dvd n \<and> odd d}\<close>
    by (metis (mono_tags, lifting) Max_ge \<open>finite {card (ErdosNicolasSet n d) |d. d dvd n}\<close> \<open>{card (ErdosNicolasSet n d) |d. d dvd n \<and> odd d} \<subseteq> {card (ErdosNicolasSet n d) |d. d dvd n}\<close> finite_subset)
  then have  \<open> Max { card (ErdosNicolasSet n d) | d :: nat. d dvd n} \<le> Max { card (ErdosNicolasSet n d) | d :: nat. d dvd n \<and> odd d}\<close>
    using \<open>card (ErdosNicolasSet n d) = Max {card (ErdosNicolasSet n d) |d. d dvd n}\<close> \<open>card (ErdosNicolasSet n d) \<le> card (ErdosNicolasSet n e)\<close> le_trans subset_refl by linarith
  then have \<open>Max { card (ErdosNicolasSet n d) | d :: nat. d dvd n} = Max { card (ErdosNicolasSet n d) | d :: nat. d dvd n \<and> odd d}\<close>
    using \<open>Max {card (ErdosNicolasSet n d) |d. d dvd n \<and> odd d} \<le> Max {card (ErdosNicolasSet n d) |d. d dvd n}\<close> le_antisym by blast
  show ?thesis 
    using ErdosNicolas_def \<open>Max {card (ErdosNicolasSet n d) |d. d dvd n} = Max {card (ErdosNicolasSet n d) |d. d dvd n \<and> odd d}\<close> by presburger
qed

end


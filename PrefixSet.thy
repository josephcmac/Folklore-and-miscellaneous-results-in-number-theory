(*
Title: Properties of PrefixSet
Author: Jose Manuel Rodriguez Caballero

We introduce the function

definition DyckJdvd :: \<open>nat\<Rightarrow>((DCHR list)\<Rightarrow>nat)\<close> where
  \<open>DyckJdvd \<equiv> SOME F :: nat\<Rightarrow>((DCHR list)\<Rightarrow>nat). \<forall> n::nat. n \<ge> 1 \<longrightarrow> (F n) ` (PrefixSet n) = (JDiv n) \<and> (\<forall> x y. length x < length y \<and> x \<in> (PrefixSet n) \<and> y \<in> (PrefixSet n) \<longrightarrow> (F n) x < (F n) y) \<close>


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


(This code  was verified in Isabelle2018)

*)


theory PrefixSet

imports Complex_Main DyckDivPHeightUP

begin

definition PrefixSet :: \<open>nat \<Rightarrow> (DCHR list) set\<close> where
\<open>PrefixSet \<equiv> \<lambda> n. {v | v. prefix v (DyckType n) \<and> v \<noteq> []}\<close>

definition JDiv :: \<open>nat \<Rightarrow> nat set\<close> where
\<open>JDiv \<equiv> \<lambda> n. {d | d::nat. Jdvd d n}\<close>

lemma preDyckJdvdBijIncr1:
  fixes n :: nat
  assumes \<open>n \<ge> 1\<close>
  shows \<open>\<forall> v. v \<in> (PrefixSet n) \<longrightarrow> prefix v (DyckType n)\<close>
  using CollectD PrefixSet_def by fastforce

lemma preDyckJdvdBijIncr3:
  fixes n :: nat
  assumes \<open>n \<ge> 1\<close>
  shows \<open> finite (JDiv n) \<close>
  using JDiv_def assms fromJdvdToDvdF1 by presburger

lemma prefixDSFsfA:
  fixes u v ::\<open>DCHR list\<close> and a::DCHR
  assumes \<open>prefix u (v@[a])\<close>
shows \<open>prefix u v \<or> u = v@[a]\<close>
  by (metis append_self_conv assms butlast_append butlast_snoc prefixConcat prefixYY)

lemma prefixDSFsfB:
  fixes u v ::\<open>DCHR list\<close> and a::DCHR
  assumes  \<open>prefix u v \<or> u = v@[a]\<close> 
shows \<open>prefix u (v@[a])\<close>
  using DyckFirstLetterPrefix assms prefixLX prefixZ1 by fastforce

lemma prefixDSFsf:
  fixes v ::\<open>DCHR list\<close> and a::DCHR
  shows \<open>\<forall> u. prefix u (v@[a]) \<longleftrightarrow> prefix u v \<or> u = v@[a]\<close>
  using prefixDSFsfA prefixDSFsfB 
  by blast

lemma preDyckJdvdBijIncr2A1AbsIndX:
  fixes v ::\<open>DCHR list\<close> and a::DCHR
  shows \<open>(card {u | u::DCHR list. prefix u (v@[a])  \<and> u \<noteq> [] }) = (card {u | u::DCHR list. prefix u v  \<and> u \<noteq> [] })+1\<close>
proof-
  have \<open>{u | u::DCHR list. prefix u (v@[a])  \<and> u \<noteq> [] } = {u | u::DCHR list. (prefix u v \<or> u = v@[a])  \<and> u \<noteq> [] }\<close>
    by (simp add: prefixDSFsf)
  then have \<open>{u | u::DCHR list. prefix u (v@[a])  \<and> u \<noteq> [] } = {u | u::DCHR list. (prefix u v \<and> u \<noteq> []) \<or> (u = v@[a] \<and> u \<noteq> []) }\<close>
    by auto
  then have \<open>{u | u::DCHR list. prefix u (v@[a])  \<and> u \<noteq> [] }
       =   {u | u::DCHR list. prefix u v \<and> u \<noteq> [] }
        \<union> {u | u::DCHR list. u = v@[a] \<and> u \<noteq> [] } \<close>
    by auto
  then have \<open>{u | u::DCHR list. prefix u (v@[a])  \<and> u \<noteq> [] }
       =   {u | u::DCHR list. prefix u v \<and> u \<noteq> [] }
        \<union> { v@[a] } \<close>
    by auto
  have \<open>  {u | u::DCHR list. prefix u v \<and> u \<noteq> [] }
        \<inter> { v@[a] } = {}\<close>
    by (simp add: prefix_def)
  have \<open>finite {u | u::DCHR list. prefix u (v@[a]) }\<close> 
    using PrefixLength by force
  have \<open>finite {u | u::DCHR list. prefix u v \<and> u \<noteq> [] }\<close>
    using CollectD PrefixLength by force
  have \<open>finite { v@[a] }\<close> 
    by simp
  have \<open>card {u | u::DCHR list. prefix u (v@[a])  \<and> u \<noteq> [] }
       =  card  {u | u::DCHR list. prefix u v \<and> u \<noteq> [] }
        + card { v@[a] } \<close>
    using  \<open>{u | u::DCHR list. prefix u (v@[a])  \<and> u \<noteq> [] }
       =   {u | u::DCHR list. prefix u v \<and> u \<noteq> [] }
        \<union> { v@[a] } \<close>
     \<open>  {u | u::DCHR list. prefix u v \<and> u \<noteq> [] }
        \<inter> { v@[a] } = {}\<close>
   \<open>finite {u | u::DCHR list. prefix u (v@[a]) }\<close> 
   \<open>finite {u | u::DCHR list. prefix u v \<and> u \<noteq> [] }\<close>
   \<open>finite { v@[a] }\<close> 
    by auto    
  then show ?thesis 
    by simp
qed

lemma preDyckJdvdBijIncr2A1AbsIndq:
  fixes  n::nat and w::\<open>DCHR list\<close>
  assumes \<open>\<forall> w::DCHR list. length w = n \<longrightarrow> card {v | v::DCHR list. prefix v w \<and> v \<noteq> [] } = length w\<close>
    and \<open>length w = Suc n\<close>
  shows \<open>card {v | v::DCHR list. prefix v w  \<and> v \<noteq> [] } = length w\<close>
proof-
  from \<open>length w = Suc n\<close> obtain v
    where \<open>w = v @ [last w]\<close> 
    by (metis append_butlast_last_id length_Suc_conv list.discI)
  from \<open>w = v @ [last w]\<close>  \<open>length w = Suc n\<close>
  have \<open>length v = n\<close> 
    by (metis add_diff_cancel_left' length_append_singleton plus_1_eq_Suc)
  then have \<open>card {u | u::DCHR list. prefix u v \<and> u \<noteq> [] } = length v\<close>
    using \<open>\<forall> w::DCHR list. length w = n \<longrightarrow> card {v | v::DCHR list. prefix v w  \<and> v \<noteq> [] } = length w\<close>
    by blast
  have \<open>card {u | u::DCHR list. prefix u (v @ [last w]) \<and> u \<noteq> [] } = (card {u | u::DCHR list. prefix u v \<and> u \<noteq> [] } ) + 1\<close>
    using preDyckJdvdBijIncr2A1AbsIndX by auto
    have \<open>length w = length v + 1\<close> 
      by (simp add: \<open>length v = n\<close> assms(2))
   show ?thesis
     using \<open>card {u |u. prefix u v \<and> u \<noteq> []} = length v\<close> \<open>length w = length v + 1\<close>
 \<open>w = v @ [last w]\<close>  \<open>card {u | u::DCHR list. prefix u (v @ [last w]) \<and> u \<noteq> [] } = (card {u | u::DCHR list. prefix u v \<and> u \<noteq> [] } ) + 1\<close>
     by auto
qed
      
lemma preDyckJdvdBijIncr2A1AbsInd:
  fixes  n::nat
  shows \<open>\<forall> w::DCHR list. length w = n \<longrightarrow> card {v | v::DCHR list. prefix v w \<and> v \<noteq> [] } = length w\<close>
proof(induction n)
  case 0
  have \<open>{v | v::DCHR list. prefix v []  \<and> v \<noteq> [] } = {}\<close>
    using prefixYYBase by auto
    then show ?case 
      by (metis card_0_eq card_infinite length_0_conv)
next
  case (Suc n)
  then show ?case using preDyckJdvdBijIncr2A1AbsIndq 
    by blast
qed

lemma preDyckJdvdBijIncr2A1Abs:
  fixes  w::\<open>DCHR list\<close>
  shows \<open>card {v | v::DCHR list. prefix v w \<and> v \<noteq> [] } = length w\<close>
  using preDyckJdvdBijIncr2A1AbsInd by auto

lemma preDyckJdvdBijIncr2A1:
  fixes n :: nat
  assumes \<open>n \<ge> 1\<close>
  shows \<open>card (PrefixSet n) = length (DyckType n)\<close>
  using preDyckJdvdBijIncr2A1Abs PrefixSet_def
  by (metis (no_types, lifting) Collect_cong)

lemma preDyckJdvdBijIncr2A:
  fixes n :: nat
  assumes \<open>n \<ge> 1\<close>
  shows \<open>card (PrefixSet n) = 2*(sigmaOdd n)\<close>
  using assms DyckTypeDivLengthsigmaOdd preDyckJdvdBijIncr2A1 PrefixSet_def 
  by simp

lemma preDyckJdvdBijIncr2B:
  fixes n :: nat
  assumes \<open>n \<ge> 1\<close>
  shows \<open>card (JDiv n) = 2*(sigmaOdd n)\<close>
  using DyckTypeDivLength DyckTypeDivLengthsigmaOdd JDiv_def assms fromJdvdToDvd by presburger

lemma preDyckJdvdBijIncr2:
  fixes n :: nat
  assumes \<open>n \<ge> 1\<close>
  shows \<open> card (PrefixSet n) = card (JDiv n) \<close>
  using preDyckJdvdBijIncr2A preDyckJdvdBijIncr2B assms by auto

lemma DyckJdvdBijIncr:
  \<open>\<forall> n::nat. \<exists> f::(DCHR list)\<Rightarrow>nat. n \<ge> 1 \<longrightarrow>  f ` (PrefixSet n) = (JDiv n) \<and> (\<forall> x y. length x < length y \<and> x \<in> (PrefixSet n) \<and> y \<in> (PrefixSet n) \<longrightarrow> f x < f y) \<close>
  using preDyckJdvdBijIncr1 preDyckJdvdBijIncr2 preDyckJdvdBijIncr3 ListEqCardPrefix
  by metis

theorem DyckJdvdBijIncrFun:
  \<open>\<exists> F :: nat\<Rightarrow>((DCHR list)\<Rightarrow>nat). \<forall> n::nat. n \<ge> 1 \<longrightarrow> (F n) ` (PrefixSet n) = (JDiv n) \<and> (\<forall> x y. length x < length y \<and> x \<in> (PrefixSet n) \<and> y \<in> (PrefixSet n) \<longrightarrow> (F n) x < (F n) y)\<close>
  using DyckJdvdBijIncr  by metis


definition DyckJdvd :: \<open>nat\<Rightarrow>((DCHR list)\<Rightarrow>nat)\<close> where
  \<open>DyckJdvd \<equiv> SOME F :: nat\<Rightarrow>((DCHR list)\<Rightarrow>nat). \<forall> n::nat. n \<ge> 1 \<longrightarrow> (F n) ` (PrefixSet n) = (JDiv n) \<and> (\<forall> x y. length x < length y \<and> x \<in> (PrefixSet n) \<and> y \<in> (PrefixSet n) \<longrightarrow> (F n) x < (F n) y) \<close>

lemma DyckJdvd1:
  fixes n::nat
  assumes \<open>n \<ge> 1\<close>
  shows \<open>(DyckJdvd n) ` (PrefixSet n) = (JDiv n)\<close>
  using DyckJdvd_def  DyckJdvdBijIncrFun PrefixSet_def
  by (smt JDiv_def assms someI_ex)

lemma DyckJdvd2:
  fixes n::nat
  assumes \<open>n \<ge> 1\<close>
  shows \<open>\<forall> x y. length x < length y \<and> x \<in> (PrefixSet n) \<and> y \<in> (PrefixSet n) \<longrightarrow> (DyckJdvd n) x < (DyckJdvd n) y\<close>
  using DyckJdvd_def  DyckJdvdBijIncrFun assms dual_order.refl order.trans someI_ex
  by smt



end


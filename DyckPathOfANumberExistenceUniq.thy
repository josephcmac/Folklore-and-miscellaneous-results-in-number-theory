(*
Title: Existence and Uniqueness of the Dyck path of a number
Author: Jose Manuel Rodriguez Caballero

We associate to any 2-letter word w, a set of positive 
natural numbers, denoted DyckClass w. We prove the following result:

theorem DyckExistsUniq :
 \<open>\<exists>! f :: nat \<Rightarrow> DCHR list.  (f 0 = [])\<and>(\<forall> n. n \<ge> 1 \<longrightarrow> n \<in> DyckClass (f n) \<and> DyckPath (f n))\<close>
 

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

theory DyckPathOfANumberExistenceUniq

imports Complex_Main PowOfTwo DyckPathOfANumberDefs

begin

section {* Schroeder Paths *}


subsection {* Auxiliary Results *}

subsubsection {* Polymophic Results *}

lemma JsignsSumToDiffCardLebesgueGRec1Plus:
  fixes f :: \<open>nat \<Rightarrow> int\<close> and k :: nat
  assumes \<open>f k = 1\<close>
  and  \<open>(\<Sum>j < k. f j) = 
          ((card {j | j :: nat. f j = 1 \<and> j < k})::int)
        - ((card {j | j :: nat. f j = -1 \<and> j < k})::int)\<close>
shows \<open>(\<Sum>j < Suc k. f j) = 
          ((card {j | j :: nat. f j = 1 \<and> j < Suc k})::int)
        - ((card {j | j :: nat. f j = -1 \<and> j < Suc k})::int)\<close>
proof-
  have \<open> {j | j :: nat. f j = 1 \<and> j <  k} \<inter>  {j | j :: nat. f j = 1 \<and> j =  k} = {}\<close> 
    by blast
 have \<open> ( {j | j :: nat. (f j = 1 \<and> j <  k) \<or> (f j = 1 \<and> j = k)}) =  {j | j :: nat. f j = 1 \<and> j < Suc k}\<close>
   using less_Suc_eq by blast
  then have \<open> {j | j :: nat. (f j = 1 \<and> j <  k)} \<union> {j | j :: nat. (f j = 1 \<and> j = k)} =  {j | j :: nat. f j = 1 \<and> j < Suc k}\<close>
    by blast
  have \<open>finite {j | j :: nat. f j = 1 \<and> j <  k}\<close> 
    by (metis (no_types, lifting) finite_nat_set_iff_bounded_le less_not_sym linorder_not_less mem_Collect_eq)
  have \<open>finite {j | j :: nat. f j = 1 \<and> j = k}\<close>
    by auto
  have \<open>card ({j | j :: nat. (f j = 1 \<and> j <  k)} \<union> {j | j :: nat. (f j = 1 \<and> j = k)}) =  (card {j | j :: nat. f j = 1 \<and> j <  k}) +  (card {j | j :: nat. f j = 1 \<and> j =  k})\<close>
    using  \<open> {j | j :: nat. f j = 1 \<and> j <  k} \<inter>  {j | j :: nat. f j = 1 \<and> j =  k} = {}\<close>
     \<open>finite {j | j :: nat. f j = 1 \<and> j <  k}\<close> 
 \<open>finite {j | j :: nat. f j = 1 \<and> j = k}\<close>
    by (simp add: card_Un_disjoint)
  then  have \<open> (card {j | j :: nat. f j = 1 \<and> j <  k}) +  (card {j | j :: nat. f j = 1 \<and> j =  k}) = card {j | j :: nat. f j = 1 \<and> j < Suc k}\<close>
    using \<open>{j |j. f j = 1 \<and> j < k} \<union> {j |j. f j = 1 \<and> j = k} = {j |j. f j = 1 \<and> j < Suc k}\<close> by auto
  have \<open>{j | j :: nat. f j = 1 \<and> j =  k} = {k}\<close> 
    using   \<open>f k = 1\<close> 
    by blast
  then  have \<open>(card {j | j :: nat. f j = 1 \<and> j <  k}) +1 = card {j | j :: nat. f j = 1 \<and> j < Suc k}\<close>
    using \<open>card {j |j. f j = 1 \<and> j < k} + card {j |j. f j = 1 \<and> j = k} = card {j |j. f j = 1 \<and> j < Suc k}\<close> by auto    
  from  \<open>f k = 1\<close> have \<open>card {j | j :: nat. f j = -1 \<and> j <  k} = card {j | j :: nat. f j = -1 \<and> j < Suc k}\<close>
    by (metis less_SucI less_Suc_eq one_neq_neg_one)
  from \<open>(\<Sum>j < k. f j) = 
          ((card {j | j :: nat. f j = 1 \<and> j < k})::int)
        - ((card {j | j :: nat. f j = -1 \<and> j < k})::int)\<close> 
  have \<open>(f k) + (\<Sum>j < k. f j) = 
          (f k) + (((card {j | j :: nat. f j = 1 \<and> j < k})::int)
        - ((card {j | j :: nat. f j = -1 \<and> j < k})::int))\<close> 
    by simp
  then have \<open>(\<Sum>j < Suc k. f j) = 
          (f k) + (((card {j | j :: nat. f j = 1 \<and> j < k})::int)
        - ((card {j | j :: nat. f j = -1 \<and> j < k})::int))\<close> 
    by simp
  then have \<open>(\<Sum>j < Suc k. f j) = 
          (1::int) + (((card {j | j :: nat. f j = 1 \<and> j < k})::int)
        - ((card {j | j :: nat. f j = -1 \<and> j < k})::int))\<close> 
    using \<open>f k = 1\<close> by auto
  then have \<open>(\<Sum>j < Suc k. f j) = 
          ((1::int) + ((card {j | j :: nat. f j = 1 \<and> j < k})::int))
        -((card {j | j :: nat. f j = -1 \<and> j < k})::int)\<close> 
    by simp
  then have \<open>(\<Sum>j < Suc k. f j) = 
          ((card {j | j :: nat. f j = 1 \<and> j < Suc k})::int)
        - ((card {j | j :: nat. f j = -1 \<and> j < Suc k})::int) \<close>
  using \<open>card {j |j. f j = - 1 \<and> j < k} = card {j |j. f j = - 1 \<and> j < Suc k}\<close> \<open>card {j |j. f j = 1 \<and> j < k} + 1 = card {j |j. f j = 1 \<and> j < Suc k}\<close> by linarith
  then show ?thesis  by blast
qed


lemma JsignsSumToDiffCardLebesgueGRec1Zero:
  fixes f :: \<open>nat \<Rightarrow> int\<close> and k :: nat
  assumes \<open>f k = 0\<close>  
  and  \<open>(\<Sum>j < k. f j) = 
          ((card {j | j :: nat. f j = 1 \<and> j < k})::int)
        - ((card {j | j :: nat. f j = -1 \<and> j < k})::int)\<close>
shows \<open>(\<Sum>j < Suc k. f j) = 
          ((card {j | j :: nat. f j = 1 \<and> j < Suc k})::int)
        - ((card {j | j :: nat. f j = -1 \<and> j < Suc k})::int)\<close>
proof-
  from  \<open>f k = 0\<close> have \<open>card {j | j :: nat. f j = 1 \<and> j <  k} = card {j | j :: nat. f j = 1 \<and> j < Suc k}\<close>
    by (metis less_SucI less_Suc_eq zero_neq_one)
  from  \<open>f k = 0\<close> have \<open>card {j | j :: nat. f j = -1 \<and> j <  k} = card {j | j :: nat. f j = -1 \<and> j < Suc k}\<close>
    by (metis less_SucI less_Suc_eq zero_neq_neg_one)
  from \<open>(\<Sum>j < k. f j) =
          ((card {j | j :: nat. f j = 1 \<and> j < k})::int)
        - ((card {j | j :: nat. f j = -1 \<and> j < k})::int)\<close> 
  have \<open>(f k) + (\<Sum>j < k. f j) = 
          (f k) + (((card {j | j :: nat. f j = 1 \<and> j < k})::int)
        - ((card {j | j :: nat. f j = -1 \<and> j < k})::int))\<close> 
    by simp
  then have \<open>(\<Sum>j < Suc k. f j) = 
          (f k) + (((card {j | j :: nat. f j = 1 \<and> j < k})::int)
        - ((card {j | j :: nat. f j = -1 \<and> j < k})::int))\<close> 
    by simp
  then have \<open>(\<Sum>j < Suc k. f j) = 
          (((card {j | j :: nat. f j = 1 \<and> j < k})::int)
        - ((card {j | j :: nat. f j = -1 \<and> j < k})::int))\<close> 
    using \<open>f k = 0\<close> by auto
  then have \<open>(\<Sum>j < Suc k. f j) = 
          ((card {j | j :: nat. f j = 1 \<and> j < Suc k})::int)
        - ((card {j | j :: nat. f j = -1 \<and> j < Suc k})::int) \<close>
    using \<open>card {j |j. f j = 1 \<and> j < k} = card {j |j. f j =  1 \<and> j < Suc k}\<close> \<open>card {j |j. f j = -1 \<and> j < k} = card {j |j. f j = -1 \<and> j < Suc k}\<close> by linarith
  then show ?thesis  by blast
qed


lemma JsignsSumToDiffCardLebesgueGRec1Minus:
  fixes f :: \<open>nat \<Rightarrow> int\<close> and k :: nat
  assumes \<open>f k = -1\<close> 
  and  \<open>(\<Sum>j < k. f j) = 
          ((card {j | j :: nat. f j = 1 \<and> j < k})::int)
        - ((card {j | j :: nat. f j = -1 \<and> j < k})::int)\<close>
shows \<open>(\<Sum>j < Suc k. f j) = 
          ((card {j | j :: nat. f j = 1 \<and> j < Suc k})::int)
        - ((card {j | j :: nat. f j = -1 \<and> j < Suc k})::int)\<close>
proof-
  have \<open> {j | j :: nat. f j = -1 \<and> j <  k} \<inter>  {j | j :: nat. f j = -1 \<and> j =  k} = {}\<close> 
    by blast
 have \<open> ( {j | j :: nat. (f j = -1 \<and> j <  k) \<or> (f j = -1 \<and> j = k)}) =  {j | j :: nat. f j = -1 \<and> j < Suc k}\<close>
   using less_Suc_eq by blast
  then have \<open> {j | j :: nat. (f j = -1 \<and> j <  k)} \<union> {j | j :: nat. (f j = -1 \<and> j = k)} =  {j | j :: nat. f j = -1 \<and> j < Suc k}\<close>
    by blast
  have \<open>finite {j | j :: nat. f j = -1 \<and> j <  k}\<close> 
    by (metis (no_types, lifting) finite_nat_set_iff_bounded_le less_not_sym linorder_not_less mem_Collect_eq)
  have \<open>finite {j | j :: nat. f j = -1 \<and> j = k}\<close>
    by auto
  have \<open>card ({j | j :: nat. (f j = -1 \<and> j <  k)} \<union> {j | j :: nat. (f j = -1 \<and> j = k)}) =  (card {j | j :: nat. f j = -1 \<and> j <  k}) +  (card {j | j :: nat. f j = -1 \<and> j =  k})\<close>
    using  \<open> {j | j :: nat. f j = -1 \<and> j <  k} \<inter>  {j | j :: nat. f j = -1 \<and> j =  k} = {}\<close>
     \<open>finite {j | j :: nat. f j = -1 \<and> j <  k}\<close> 
 \<open>finite {j | j :: nat. f j = -1 \<and> j = k}\<close>
    by (simp add: card_Un_disjoint)
  then  have \<open> (card {j | j :: nat. f j = -1 \<and> j <  k}) +  (card {j | j :: nat. f j = -1 \<and> j =  k}) = card {j | j :: nat. f j = -1 \<and> j < Suc k}\<close>
    using \<open>{j |j. f j = -1 \<and> j < k} \<union> {j |j. f j = -1 \<and> j = k} = {j |j. f j = -1 \<and> j < Suc k}\<close> by auto
  have \<open>{j | j :: nat. f j = -1 \<and> j =  k} = {k}\<close> 
    using   \<open>f k = -1\<close> 
    by blast
  then  have \<open>(card {j | j :: nat. f j = -1 \<and> j <  k}) +1 = card {j | j :: nat. f j = -1 \<and> j < Suc k}\<close>
    using \<open>card {j |j. f j = -1 \<and> j < k} + card {j |j. f j = -1 \<and> j = k} = card {j |j. f j = -1 \<and> j < Suc k}\<close> by auto    
  from  \<open>f k = -1\<close> have \<open>card {j | j :: nat. f j = 1 \<and> j <  k} = card {j | j :: nat. f j = 1 \<and> j < Suc k}\<close>
    by (metis less_SucI less_Suc_eq one_neq_neg_one)
  from \<open>(\<Sum>j < k. f j) = 
          ((card {j | j :: nat. f j = 1 \<and> j < k})::int)
        - ((card {j | j :: nat. f j = -1 \<and> j < k})::int)\<close> 
  have \<open>(f k) + (\<Sum>j < k. f j) = 
          (f k) + (((card {j | j :: nat. f j = 1 \<and> j < k})::int)
        - ((card {j | j :: nat. f j = -1 \<and> j < k})::int))\<close> 
    by simp
  then have \<open>(\<Sum>j < Suc k. f j) = 
          (f k) + (((card {j | j :: nat. f j = 1 \<and> j < k})::int)
        - ((card {j | j :: nat. f j = -1 \<and> j < k})::int))\<close> 
    by simp
  then have \<open>(\<Sum>j < Suc k. f j) = 
          (-1::int) + (((card {j | j :: nat. f j = 1 \<and> j < k})::int)
        - ((card {j | j :: nat. f j = -1 \<and> j < k})::int))\<close> 
    using \<open>f k = -1\<close> by auto
  then have \<open>(\<Sum>j < Suc k. f j) = 
           ((card {j | j :: nat. f j = 1 \<and> j < k})::int)
       -( (1::int) +((card {j | j :: nat. f j = -1 \<and> j < k})::int))\<close> 
    by simp
  then have \<open>(\<Sum>j < Suc k. f j) = 
          ((card {j | j :: nat. f j = 1 \<and> j < Suc k})::int)
        - ((card {j | j :: nat. f j = -1 \<and> j < Suc k})::int) \<close>
    using \<open>card {j |j. f j = 1 \<and> j < k} = card {j |j. f j =  1 \<and> j < Suc k}\<close> \<open>card {j |j. f j = -1 \<and> j < k} + 1 = card {j |j. f j = -1 \<and> j < Suc k}\<close> by linarith
  then show ?thesis  by blast
qed

lemma JsignsSumToDiffCardLebesgueGRec1:
  fixes f :: \<open>nat \<Rightarrow> int\<close> and k :: nat
  assumes  \<open>f k = -1 \<or> f k = 0 \<or> f k = 1\<close>
  and  \<open>(\<Sum>j < k. f j) = 
          ((card {j | j :: nat. f j = 1 \<and> j < k})::int)
        - ((card {j | j :: nat. f j = -1 \<and> j < k})::int)\<close>
shows \<open>(\<Sum>j < Suc k. f j) = 
          ((card {j | j :: nat. f j = 1 \<and> j < Suc k})::int)
        - ((card {j | j :: nat. f j = -1 \<and> j < Suc k})::int)\<close>
  using JsignsSumToDiffCardLebesgueGRec1Plus JsignsSumToDiffCardLebesgueGRec1Zero JsignsSumToDiffCardLebesgueGRec1Minus assms
  by blast

lemma JsignsSumToDiffCardLebesgueG:
  fixes f :: \<open>nat \<Rightarrow> int\<close> and k :: nat
  assumes \<open>\<forall> j. f j = -1 \<or> f j = 0 \<or> f j = 1\<close>
  shows  \<open>(\<Sum>j < k. f j) = 
          ((card {j | j :: nat. f j = 1 \<and> j < k})::int)
        - ((card {j | j :: nat. f j = -1 \<and> j < k})::int)\<close>
proof(induction k)
  case 0
  then show ?case 
    by simp
next
  case (Suc k)
  then have \<open>sum f {..<k} = int (card {j |j. f j = 1 \<and> j < k}) - int (card {j |j. f j = - 1 \<and> j < k})\<close> by blast
  have  \<open>f k = -1 \<or> f k = 0 \<or> f k = 1\<close> using  \<open>\<forall> j. f j = -1 \<or> f j = 0 \<or> f j = 1\<close> by blast
  show ?case using JsignsSumToDiffCardLebesgueGRec1  \<open>sum f {..<k} = int (card {j |j. f j = 1 \<and> j < k}) - int (card {j |j. f j = - 1 \<and> j < k})\<close>  \<open>f k = -1 \<or> f k = 0 \<or> f k = 1\<close> 
    by blast
qed

lemma CantorBernsteinSchroeder:
  fixes A :: \<open>'a set\<close> and B :: \<open>'b set\<close> and f :: \<open>'a \<Rightarrow> 'b\<close> and g :: \<open>'b \<Rightarrow> 'a\<close>
  assumes  \<open>f ` A \<subseteq> B\<close> and \<open> g ` B \<subseteq> A\<close> and \<open>inj_on f A\<close> and \<open>inj_on g B\<close>
      and \<open>finite A\<close> and \<open>finite B\<close>
  shows \<open>card A = card B\<close>
  by (meson Schroeder_Bernstein assms(1) assms(2) assms(3) assms(4) assms(5) assms(6) bij_betw_iff_card)

lemma CantorBernsteinSchroederfeqg:
  fixes A :: \<open>'a set\<close> and B :: \<open>'a set\<close> and f :: \<open>'a \<Rightarrow> 'a\<close>
  assumes \<open>f ` A \<subseteq> B\<close> and \<open>f ` B \<subseteq>  A\<close> and \<open>inj_on f A\<close> and \<open>inj_on f B\<close>
      and \<open>finite A\<close> and \<open>finite B\<close>
  shows \<open>card A = card B\<close>
  using CantorBernsteinSchroeder assms(1) assms(2) assms(3) assms(4) assms(5) assms(6) by blast

lemma InjIneqCard:
  fixes A :: \<open>'a set\<close> and B :: \<open>'a set\<close> and f :: \<open>'a \<Rightarrow> 'a\<close>
  assumes \<open>f ` A \<subseteq> B\<close> \<open>inj_on f A\<close> 
      and \<open>finite A\<close> and \<open>finite B\<close>
  shows \<open>card A \<le> card B\<close>
  using assms(1) assms(2) assms(4) card_inj_on_le by blast

lemma biCardSetSucA:
  fixes P :: \<open>nat \<Rightarrow> bool\<close>
  shows \<open>inj_on Suc {n | n :: nat. P (Suc n)}\<close>
  by simp


lemma biCardSetSucBQS:
  fixes P :: \<open>nat \<Rightarrow> bool\<close> and x :: nat
  assumes \<open>x \<in> {n | n :: nat. P (Suc n)}\<close>
  shows \<open>Suc x \<in> {n | n :: nat. n \<ge> 1 \<and> P n} \<close>
proof-
  have \<open>P (Suc x)\<close> 
    using assms by auto
  then show ?thesis 
    by simp
qed

lemma biCardSetSucBQ:
  fixes P :: \<open>nat \<Rightarrow> bool\<close>
  shows \<open>\<forall> x \<in> {n | n :: nat. P (Suc n)}.  Suc x \<in> {n | n :: nat. n \<ge> 1 \<and> P n} \<close>
  using biCardSetSucBQS by blast

lemma biCardSetSucB:
  fixes P :: \<open>nat \<Rightarrow> bool\<close>
  shows \<open> Suc ` {n | n :: nat. P (Suc n)}  \<subseteq> {n | n :: nat. n \<ge> 1 \<and> P n} \<close>
  using biCardSetSucBQ by blast

lemma CardSetSucC:
  fixes P :: \<open>nat \<Rightarrow> bool\<close>
  assumes \<open>finite {n | n :: nat. n \<ge> 1 \<and> P n}\<close> and \<open>finite {n | n :: nat. P (Suc n)}\<close>
  shows \<open>  card  {n | n :: nat. P (Suc n)} \<le> card {n | n :: nat. n \<ge> 1 \<and> P n}\<close>
proof-
  have  \<open>inj_on Suc {n | n :: nat. P (Suc n)}\<close> 
    using inj_Suc by blast
  have  \<open> Suc ` {n | n :: nat. P (Suc n)}  \<subseteq> {n | n :: nat. n \<ge> 1 \<and> P n} \<close> 
    by auto
  then show ?thesis using InjIneqCard 
    using assms(1) by fastforce
qed

lemma biCardSetSucOPA:
  fixes P :: \<open>nat \<Rightarrow> bool\<close>
  shows \<open>inj_on (\<lambda> q. q - 1) {n | n :: nat. n \<ge> 1 \<and> P n}\<close>
  using inj_on_diff_nat by fastforce

lemma biCardSetSucOPBQS:
  fixes P :: \<open>nat \<Rightarrow> bool\<close> and x :: nat
  assumes \<open>x \<in> {n | n :: nat. n \<ge> 1 \<and> P n}\<close>
  shows \<open> (\<lambda> q. q - 1) x \<in> {n | n :: nat. P (Suc n)}\<close>
  using assms by auto

lemma biCardSetSucOPBQ:
  fixes P :: \<open>nat \<Rightarrow> bool\<close>
  shows \<open>\<forall> x \<in> {n | n :: nat. n \<ge> 1 \<and> P n}. (\<lambda> q. q - 1) x \<in> {n | n :: nat. P (Suc n)} \<close>
  using biCardSetSucOPBQS by blast

lemma biCardSetSucOPB:
  fixes P :: \<open>nat \<Rightarrow> bool\<close>
  shows \<open> (\<lambda> q. q - 1) ` {n | n :: nat. n \<ge> 1 \<and> P n}  \<subseteq> {n | n :: nat. P (Suc n)} \<close>
  using  biCardSetSucOPBQ by blast

lemma CardSetSucOPC:
  fixes P :: \<open>nat \<Rightarrow> bool\<close>
  assumes \<open>finite {n | n :: nat. n \<ge> 1 \<and> P n}\<close> and \<open>finite {n | n :: nat. P (Suc n)}\<close>
  shows \<open>  card {n | n :: nat. n \<ge> 1 \<and> P n} \<le> card  {n | n :: nat. P (Suc n)}\<close>
proof-
  have \<open>inj_on (\<lambda> q. q - 1) {n | n :: nat. n \<ge> 1 \<and> P n}\<close> 
    using biCardSetSucOPA by auto
  have \<open> (\<lambda> q. q - 1) ` {n | n :: nat. n \<ge> 1 \<and> P n}  \<subseteq> {n | n :: nat. P (Suc n)} \<close> 
    by (simp add: image_subset_iff)
  then show ?thesis 
    using InjIneqCard \<open>inj_on (\<lambda>q. q - 1) {n |n. 1 \<le> n \<and> P n}\<close> assms(2) by fastforce
qed

lemma CardSetSuc:
  fixes P :: \<open>nat \<Rightarrow> bool\<close>
  assumes \<open>finite {n | n :: nat. n \<ge> 1 \<and> P n}\<close> and \<open>finite {n | n :: nat. P (Suc n)}\<close>
  shows \<open> card {n | n :: nat. n \<ge> 1 \<and> P n} = card  {n | n :: nat. P (Suc n)} \<close>
  using assms CardSetSucC CardSetSucOPC by fastforce

subsubsection {* Number Theoretic Results *}

definition JCompl::\<open>nat \<Rightarrow> (nat \<Rightarrow> nat)\<close> where
\<open>JCompl \<equiv> \<lambda> n. (\<lambda> d. (2*n) div d)\<close>

lemma preJsignsCardEq1AQ:
 fixes n k x y :: nat 
 assumes \<open>n \<ge> 1\<close> and \<open>A = {d | d :: nat. odd d \<and> Jdvd d n \<and> d \<le> k}\<close> 
   and \<open>x \<in> A\<close> and \<open>y \<in> A\<close> and \<open>(JCompl n) x = (JCompl n) y\<close>
 shows \<open>x = y\<close>
proof-
  have \<open>odd x\<close> using  \<open>x \<in> A\<close> \<open>A = {d | d :: nat. odd d \<and> Jdvd d n \<and> d \<le> k}\<close> 
    by blast
  have \<open>Jdvd x n\<close> using  \<open>x \<in> A\<close> \<open>A = {d | d :: nat. odd d \<and> Jdvd d n \<and> d \<le> k}\<close> 
    by blast
  have \<open>x \<le> k\<close> using  \<open>x \<in> A\<close> \<open>A = {d | d :: nat. odd d \<and> Jdvd d n \<and> d \<le> k}\<close> 
    by blast
  from \<open>Jdvd x n\<close> obtain t :: nat where \<open>x * t = 2*n\<close> 
    by (meson Jdvd_def)
  have \<open>t = (JCompl n) x\<close> 
    by (metis Groups.mult_ac(2) JCompl_def One_nat_def Suc_leI \<open>x * t = 2 * n\<close> assms(1) dvd_div_mult_self dvd_triv_left mult_compare_simps(13) not_one_le_zero pos2)
  have \<open>odd y\<close> using  \<open>y \<in> A\<close> \<open>A = {d | d :: nat. odd d \<and> Jdvd d n \<and> d \<le> k}\<close> 
    by blast
  have \<open>Jdvd y n\<close> using  \<open>y \<in> A\<close> \<open>A = {d | d :: nat. odd d \<and> Jdvd d n \<and> d \<le> k}\<close> 
    by blast
  have \<open>y \<le> k\<close> using  \<open>y \<in> A\<close> \<open>A = {d | d :: nat. odd d \<and> Jdvd d n \<and> d \<le> k}\<close> 
    by blast
  from \<open>Jdvd y n\<close> obtain s :: nat where \<open>y * s = 2*n\<close> 
    by (meson Jdvd_def)
  have \<open>s = (JCompl n) y\<close> 
    by (metis JCompl_def One_nat_def Suc_leI \<open>y * s = 2 * n\<close> assms(1) dvd_div_mult_self dvd_triv_left mult.commute mult_cancel_right not_one_le_zero pos2) 
  have \<open>x * t = y * t\<close> 
    using \<open>s = JCompl n y\<close> \<open>t = JCompl n x\<close> \<open>x * t = 2 * n\<close> \<open>y * s = 2 * n\<close> assms(5) by auto
  have \<open>t \<noteq> 0\<close> 
    using One_nat_def \<open>x * t = 2 * n\<close> assms(1) not_one_le_zero by fastforce
  from  \<open>x * t = y * t\<close> \<open>t \<noteq> 0\<close> have \<open>x = y\<close> 
    using mult_right_cancel by blast
  then show ?thesis by blast
qed

lemma preJsignsCardEq1A:
 fixes n k :: nat 
 assumes \<open>n \<ge> 1\<close> and \<open>A = {d | d :: nat. odd d \<and> Jdvd d n \<and> d \<le> k}\<close> 
 shows \<open>\<forall> x\<in>A. \<forall> y\<in>A. (JCompl n) x = (JCompl n) y \<longrightarrow> x = y\<close>
  using assms preJsignsCardEq1AQ by blast

lemma preJsignsCardEq1:
 fixes n k :: nat 
 assumes \<open>n \<ge> 1\<close> and \<open>A = {d | d :: nat. odd d \<and> Jdvd d n \<and> d \<le> k}\<close> 
 shows \<open>inj_on (JCompl n) A\<close>
proof-
  have  \<open>\<forall> x\<in>A. \<forall> y\<in>A. (JCompl n) x = (JCompl n) y \<longrightarrow> x = y\<close> using assms preJsignsCardEq1A by blast
  then show ?thesis using inj_on_def 
    by (simp add: inj_on_def)
qed

lemma preJsignsCardEq2AQ:
 fixes n k x y :: nat 
 assumes \<open>x \<in> B\<close> and \<open>y \<in> B\<close> and \<open>n \<ge> 1\<close> and  \<open>B = {d | d :: nat. even d \<and> Jdvd d n \<and> d \<le> k}\<close>
   and \<open>(JCompl n) x = (JCompl n) y\<close>
 shows \<open> x = y \<close>
proof-
  have \<open>even x\<close> 
    using assms(1) assms(4) by auto
  have \<open>Jdvd x n\<close> 
    using assms(1) assms(4) by blast
  have \<open>x \<le> k\<close> 
    using assms(1) assms(4) by blast
  from \<open>Jdvd x n\<close> obtain t :: nat where \<open>x * t = 2*n\<close>
    by (meson Jdvd_def)
  have \<open>t = (JCompl n) x\<close> 
    by (metis JCompl_def One_nat_def Suc_leI \<open>x * t = 2 * n\<close> assms(3) dvd_div_mult_self dvd_triv_left less_one linorder_not_le mult.commute mult_cancel_right pos2)
  have \<open>even y\<close> 
    using assms(2) assms(4) by blast
  have \<open>Jdvd y n\<close> 
    using assms(2) assms(4) by blast
    have \<open>y \<le> k\<close>
      using assms(2) assms(4) by blast
      from \<open>Jdvd y n\<close> obtain s :: nat where \<open>y * s = 2*n\<close> 
    by (meson Jdvd_def)
  have \<open>t \<noteq> 0\<close>
    using \<open>x * t = 2 * n\<close> assms(3) not_one_le_zero by fastforce
  have \<open>t = s\<close> 
    by (metis JCompl_def One_nat_def Suc_leI \<open>t = JCompl n x\<close> \<open>y * s = 2 * n\<close> assms(3) assms(5) mult_eq_0_iff nonzero_mult_div_cancel_left not_one_le_zero pos2)
  have \<open>x*t = y*s\<close> 
    by (simp add: \<open>x * t = 2 * n\<close> \<open>y * s = 2 * n\<close>)
  then have \<open>x*t = y*t\<close> 
    using \<open>t = s\<close> by blast
  then have \<open>x = y\<close> 
    using \<open>t \<noteq> 0\<close> mult_right_cancel by blast
  then show ?thesis by blast
qed

lemma preJsignsCardEq2A:
 fixes n k :: nat 
 assumes \<open>n \<ge> 1\<close> and  \<open>B = {d | d :: nat. even d \<and> Jdvd d n \<and> d \<le> k}\<close>
 shows \<open>\<forall> x \<in> B. \<forall> y \<in> B. (JCompl n) x = (JCompl n) y \<longrightarrow> x = y \<close>
  using assms(1) assms(2) preJsignsCardEq2AQ by auto

lemma preJsignsCardEq2:
 fixes n k :: nat 
 assumes \<open>n \<ge> 1\<close> and  \<open>B = {d | d :: nat. even d \<and> Jdvd d n \<and> d \<le> k}\<close>
 shows \<open>inj_on (JCompl n) B\<close>
  by (smt Groups.mult_ac(2) JCompl_def Jdvd_def assms(1) assms(2) dvd_div_mult_self dvd_triv_left inj_on_def less_one linorder_not_le mem_Collect_eq mult_compare_simps(13))

lemma preJsignsCardEq3AS:
 fixes n k x:: nat 
 assumes \<open>n \<ge> 1\<close> and \<open>A = {d | d :: nat. odd d \<and> Jdvd d n \<and> d \<le> k}\<close>  and \<open>B = {d | d :: nat. even d \<and> Jdvd d n \<and> d \<le> k}\<close> 
and \<open>k \<ge> 2*n\<close> and \<open>x \<in> A\<close>
  shows \<open>(JCompl n) x \<in> B\<close>
proof-
  obtain y where \<open>y = (JCompl n) x\<close> by blast
  have \<open>x * y = 2*n\<close> 
    by (metis (no_types, lifting) JCompl_def Jdvd_def \<open>y = JCompl n x\<close> assms(2) assms(5) dvd_mult_div_cancel dvd_triv_left mem_Collect_eq)
  have \<open>odd x\<close> 
    using assms(2) assms(5) by blast
  have \<open>even y\<close> 
    using \<open>odd x\<close> \<open>x * y = 2 * n\<close> even_mult_iff by fastforce
  have \<open>Jdvd y n\<close> 
    by (metis Jdvd_def \<open>odd x\<close> \<open>x * y = 2 * n\<close> semiring_normalization_rules(7))
  have \<open>y \<le> k\<close> 
    by (metis One_nat_def Suc_le_lessD \<open>x * y = 2 * n\<close> assms(1) assms(4) dual_order.trans dvd_imp_le dvd_triv_right nat_0_less_mult_iff pos2)
  have \<open>y \<in> B\<close> 
    by (simp add: \<open>Jdvd y n\<close> \<open>even y\<close> \<open>y \<le> k\<close> assms(3))
  then show ?thesis 
    using \<open>y = JCompl n x\<close> by blast
qed

lemma preJsignsCardEq3A:
 fixes n k :: nat 
 assumes \<open>n \<ge> 1\<close> and \<open>A = {d | d :: nat. odd d \<and> Jdvd d n \<and> d \<le> k}\<close>  and \<open>B = {d | d :: nat. even d \<and> Jdvd d n \<and> d \<le> k}\<close> 
and \<open>k \<ge> 2*n\<close>
  shows \<open>\<forall>x \<in> A.(JCompl n) x \<in> B\<close>
  using assms preJsignsCardEq3AS by blast

lemma preJsignsCardEq3:
 fixes n k :: nat 
 assumes \<open>n \<ge> 1\<close> and \<open>A = {d | d :: nat. odd d \<and> Jdvd d n \<and> d \<le> k}\<close>  and \<open>B = {d | d :: nat. even d \<and> Jdvd d n \<and> d \<le> k}\<close> 
and \<open>k \<ge> 2*n\<close>
  shows \<open>(JCompl n) ` A \<subseteq> B\<close>
  using preJsignsCardEq3A assms by blast

lemma preJsignsCardEq4AS:
 fixes n k x :: nat 
 assumes \<open>n \<ge> 1\<close> and \<open>A = {d | d :: nat. odd d \<and> Jdvd d n \<and> d \<le> k}\<close> and \<open>B = {d | d :: nat. even d \<and> Jdvd d n \<and> d \<le> k}\<close> 
   and \<open>x \<in> B\<close> and \<open>k \<ge> 2*n\<close>
 shows \<open>(JCompl n) x \<in>  A\<close>
proof-
  obtain y where \<open>y = (JCompl n) x\<close> by blast
  have \<open>x*y = 2*n\<close> 
    by (metis (no_types, lifting) JCompl_def Jdvd_def \<open>y = JCompl n x\<close> assms(3) assms(4) dvd_div_mult_self dvd_triv_left mem_Collect_eq mult.commute)
  have \<open>Jdvd x n\<close> 
    using assms(3) assms(4) by blast 
  have \<open>even x\<close> 
    using assms(3) assms(4) by blast
  have \<open>odd y\<close> 
    by (metis Jdvd_def Suc_1 \<open>Jdvd x n\<close> \<open>even x\<close> \<open>x * y = 2 * n\<close> assms(1) le_simps(3) less_one nat_mult_eq_cancel_disj no_zero_divisors  not_less_eq_eq power.simps(1) power.simps(2) zero_power2)
  have \<open>x \<le> k\<close> 
    using assms(3) assms(4) by blast
  have \<open>y \<le> k\<close> 
    by (metis One_nat_def Suc_le_lessD \<open>x * y = 2 * n\<close> assms(1) assms(5) dual_order.trans dvd_imp_le dvd_triv_right nat_0_less_mult_iff pos2)   
  have \<open>y \<in> A\<close> 
    by (metis (no_types, lifting) Jdvd_def \<open>odd y\<close> \<open>x * y = 2 * n\<close> \<open>y \<le> k\<close> assms(2) mem_Collect_eq mult.commute)
  then show ?thesis using  \<open>y = (JCompl n) x\<close> by auto
qed

lemma preJsignsCardEq4A:
 fixes n k :: nat 
 assumes \<open>n \<ge> 1\<close> and \<open>A = {d | d :: nat. odd d \<and> Jdvd d n \<and> d \<le> k}\<close> and \<open>B = {d | d :: nat. even d \<and> Jdvd d n \<and> d \<le> k}\<close> 
   and \<open>k \<ge> 2*n\<close>
  shows \<open>\<forall> x \<in> B. (JCompl n) x \<in>  A\<close>
  using preJsignsCardEq4AS assms by blast

lemma preJsignsCardEq4:
 fixes n k :: nat 
 assumes \<open>n \<ge> 1\<close> and \<open>A = {d | d :: nat. odd d \<and> Jdvd d n \<and> d \<le> k}\<close> and \<open>B = {d | d :: nat. even d \<and> Jdvd d n \<and> d \<le> k}\<close> 
   and \<open>k \<ge> 2*n\<close>
 shows \<open>(JCompl n) ` B \<subseteq> A\<close>
  using assms preJsignsCardEq4A by blast

lemma JsignsCardEq:
  fixes n k :: nat
  assumes \<open>n \<ge> 1\<close> and \<open>k \<ge> 2*n\<close>
  shows \<open>(card {d | d :: nat. odd d \<and> Jdvd d n \<and> d \<le> k}) = (card {d | d :: nat. even d \<and> Jdvd d n \<and> d \<le> k})\<close>
proof-
  obtain A where \<open>A = {d | d :: nat. odd d \<and> Jdvd d n \<and> d \<le> k}\<close> by blast
  obtain B where \<open>B = {d | d :: nat. even d \<and> Jdvd d n \<and> d \<le> k}\<close> by blast
  have \<open>finite A\<close> 
    using \<open>A = {d |d. odd d \<and> Jdvd d n \<and> d \<le> k}\<close> finite_nat_set_iff_bounded_le by blast
  have \<open>finite B\<close>
    using \<open>B = {d |d. even d \<and> Jdvd d n \<and> d \<le> k}\<close> finite_nat_set_iff_bounded_le by blast
  have \<open>inj_on (JCompl n) A\<close> 
    using \<open>A = {d |d. odd d \<and> Jdvd d n \<and> d \<le> k}\<close> assms(1) inj_on_def preJsignsCardEq1A by fastforce
  have \<open>inj_on (JCompl n) B\<close>
    using \<open>B = {d |d. even d \<and> Jdvd d n \<and> d \<le> k}\<close> assms(1) preJsignsCardEq2 by auto
  have  \<open>(JCompl n) ` A \<subseteq> B\<close>
    using \<open>A = {d |d. odd d \<and> Jdvd d n \<and> d \<le> k}\<close> \<open>B = {d |d. even d \<and> Jdvd d n \<and> d \<le> k}\<close> assms(1) assms(2) preJsignsCardEq3 by auto
  have  \<open>(JCompl n) ` B \<subseteq> A\<close>
    using \<open>k \<ge> 2*n\<close> \<open>A = {d |d. odd d \<and> Jdvd d n \<and> d \<le> k}\<close> \<open>B = {d |d. even d \<and> Jdvd d n \<and> d \<le> k}\<close> assms(1) preJsignsCardEq4 by auto
  have \<open>card A = card B\<close>
    using CantorBernsteinSchroederfeqg \<open>JCompl n ` A \<subseteq> B\<close> \<open>JCompl n ` B \<subseteq> A\<close> \<open>finite A\<close> \<open>finite B\<close> \<open>inj_on (JCompl n) A\<close> \<open>inj_on (JCompl n) B\<close> by blast
  then show ?thesis 
    using \<open>A = {d |d. odd d \<and> Jdvd d n \<and> d \<le> k}\<close> \<open>B = {d |d. even d \<and> Jdvd d n \<and> d \<le> k}\<close> by blast
qed

lemma OddPartfromAtoBinjQS:
 fixes n k x y:: nat 
 assumes \<open>n \<ge> 1\<close> and \<open>A = {d | d :: nat. odd d \<and> Jdvd d n \<and> d \<le> k}\<close> and \<open>B = {d | d :: nat. even d \<and> Jdvd d n \<and> d \<le> k}\<close> 
and \<open>x \<in> B\<close> and \<open>y \<in> B\<close> and \<open>OddPart x = OddPart y\<close>
shows \<open>x = y\<close>
proof-
  have \<open>even x\<close> 
    using assms(3) assms(4) by blast
  have \<open>even  y\<close>
    using assms(3) assms(5) by blast
  obtain t where \<open>x * t = 2*n\<close> and \<open>odd t\<close> 
    by (metis (no_types, lifting) Jdvd_def assms(3) assms(4) mem_Collect_eq)
  obtain s where \<open>y * s = 2*n\<close> and \<open>odd s\<close>   
    by (metis (no_types, lifting) Jdvd_def \<open>even y\<close> \<open>x * t = 2 * n\<close> assms(3) assms(5) mem_Collect_eq)
  have \<open>x \<ge> 1\<close> 
    by (metis One_nat_def Suc_leI \<open>x * t = 2 * n\<close> assms(1) one_le_mult_iff pos2)
  have \<open>y \<ge> 1\<close> 
    by (metis One_nat_def Suc_leI \<open>y * s = 2 * n\<close> assms(1) less_le_trans less_numeral_extra(1) nat_0_less_mult_iff pos2)
  from \<open>x \<ge> 1\<close> have \<open>x = (2^(Exp2 x))*(OddPart x) \<and> odd (OddPart x)\<close> 
    using Exp2OddPartChar by blast
  then have \<open>x = (2^(Exp2 x))*(OddPart x)\<close> by blast
  have \<open>odd (OddPart x)\<close> using \<open>x = (2^(Exp2 x))*(OddPart x) \<and> odd (OddPart x)\<close> by blast
  from \<open>y \<ge> 1\<close> have \<open>y = (2^(Exp2 y))*(OddPart y) \<and> odd (OddPart y)\<close> 
    using Exp2OddPartChar by blast
 then have \<open>y = (2^(Exp2 y))*(OddPart y)\<close> by blast
  have \<open>odd (OddPart y)\<close> using \<open>y = (2^(Exp2 y))*(OddPart y) \<and> odd (OddPart y)\<close> by blast
  have \<open>odd (t*(OddPart x))\<close> 
    by (simp add: \<open>odd (OddPart x)\<close> \<open>odd t\<close>)
  have \<open>odd (s*(OddPart y))\<close> 
    by (simp add: \<open>odd (OddPart y)\<close> \<open>odd s\<close>)
  have \<open>(2^(Exp2 x))*(t*(OddPart x)) = 2*n\<close> 
    by (metis \<open>x * t = 2 * n\<close> \<open>x = 2 ^ Exp2 x * OddPart x \<and> odd (OddPart x)\<close> mult.assoc semiring_normalization_rules(16))
  have \<open>(2^(Exp2 y))*(s*(OddPart y)) = 2*n\<close> 
    by (metis \<open>y * s = 2 * n\<close> \<open>y = 2 ^ Exp2 y * OddPart y\<close> mult.assoc semiring_normalization_rules(16))    
  from \<open>(2^(Exp2 x))*(t*(OddPart x)) = 2*n\<close>  \<open>odd (t*(OddPart x))\<close> 
    have \<open>OddPart (2*n) = t*(OddPart x)\<close>
      using  Exp2OddPartChar Exp2ValueAt1 OddPartValueAt1 UniqnessOddEven_EvenPart UniqnessOddEven_OddPart 
      by (metis One_nat_def Suc_leI assms(1) one_le_mult_iff pos2)
    from \<open>(2^(Exp2 y))*(s*(OddPart y)) = 2*n\<close>  \<open>odd (s*(OddPart y))\<close>
    have  \<open>OddPart (2*n) = s*(OddPart y)\<close>
      using  Exp2OddPartChar Exp2ValueAt1 OddPartValueAt1 UniqnessOddEven_EvenPart UniqnessOddEven_OddPart 
      by (metis \<open>2 ^ Exp2 x * (t * OddPart x) = 2 * n\<close> \<open>OddPart (2 * n) = t * OddPart x\<close> \<open>odd (t * OddPart x)\<close>)
    from  \<open>OddPart (2*n) = t*(OddPart x)\<close> \<open>OddPart (2*n) = s*(OddPart y)\<close> 
    have \<open>t*(OddPart x) = s*(OddPart y)\<close> by simp
    then have \<open>t = s\<close> using  \<open>OddPart x = OddPart y\<close> 
      by (metis UniqnessOddEven \<open>1 \<le> x\<close> \<open>2 ^ Exp2 x * (t * OddPart x) = 2 * n\<close> \<open>2 ^ Exp2 y * (s * OddPart y) = 2 * n\<close> \<open>odd (t * OddPart x)\<close> \<open>x * t = 2 * n\<close> \<open>x = 2 ^ Exp2 x * OddPart x \<and> odd (OddPart x)\<close> \<open>y * s = 2 * n\<close> \<open>y = 2 ^ Exp2 y * OddPart y\<close> nat_mult_eq_cancel_disj not_one_le_zero)
    then have \<open>x = y\<close> 
      by (metis UniqnessOddEven \<open>2 ^ Exp2 x * (t * OddPart x) = 2 * n\<close> \<open>2 ^ Exp2 y * (s * OddPart y) = 2 * n\<close> \<open>odd (t * OddPart x)\<close> \<open>x = 2 ^ Exp2 x * OddPart x \<and> odd (OddPart x)\<close> \<open>y = 2 ^ Exp2 y * OddPart y\<close> assms(6))
    then show ?thesis by blast
  qed

lemma OddPartfromAtoBinjQ:
 fixes n k :: nat 
 assumes \<open>n \<ge> 1\<close> and \<open>A = {d | d :: nat. odd d \<and> Jdvd d n \<and> d \<le> k}\<close> and \<open>B = {d | d :: nat. even d \<and> Jdvd d n \<and> d \<le> k}\<close> 
 shows \<open>\<forall> x \<in> B. \<forall> y \<in> B. OddPart x = OddPart y \<longrightarrow> x = y\<close>
  using assms OddPartfromAtoBinjQS by blast

lemma OddPartfromAtoBinj:
 fixes n k :: nat 
 assumes \<open>n \<ge> 1\<close> and \<open>A = {d | d :: nat. odd d \<and> Jdvd d n \<and> d \<le> k}\<close> and \<open>B = {d | d :: nat. even d \<and> Jdvd d n \<and> d \<le> k}\<close> 
 shows \<open>inj_on OddPart B\<close>
  using assms OddPartfromAtoBinjQ  inj_on_def 
  by (metis (mono_tags, lifting) inj_onI)

lemma OddPartfromAtoB1:
 fixes n k x :: nat 
 assumes \<open>n \<ge> 1\<close> and \<open>A = {d | d :: nat. odd d \<and> Jdvd d n \<and> d \<le> k}\<close> and \<open>B = {d | d :: nat. even d \<and> Jdvd d n \<and> d \<le> k}\<close> 
and \<open>x \<in> B\<close> 
shows \<open>OddPart x \<in> A\<close>
proof-
  have \<open>x \<ge> 1\<close> 
    by (metis (no_types, lifting) Jdvd_def assms(1) assms(3) assms(4) less_one mem_Collect_eq mult_eq_0_iff neq0_conv not_le pos2)
  then have \<open>x = 2^(Exp2 x)* (OddPart x) \<and> odd (OddPart x)\<close> 
    using preExp2OddPartChar by blast
  then have \<open>odd (OddPart x)\<close> by blast
  then obtain y where \<open>x * y = 2*n\<close> and \<open>odd y\<close> 
    by (metis (no_types, lifting) Jdvd_def assms(3) assms(4) mem_Collect_eq)
  from  \<open>x * y = 2*n\<close> have \<open>(OddPart x)*(2^(Exp2 x)*y) = 2*n\<close> 
    by (metis \<open>x = 2 ^ Exp2 x * OddPart x \<and> odd (OddPart x)\<close> semiring_normalization_rules(16) semiring_normalization_rules(7))
  then have \<open>Jdvd (OddPart x) n\<close> 
    by (meson Jdvd_def \<open>x = 2 ^ Exp2 x * OddPart x \<and> odd (OddPart x)\<close>)
  have \<open>OddPart x \<le> k\<close> 
    by (metis (no_types, lifting) OddPartL1 \<open>1 \<le> x\<close> assms(3) assms(4) dual_order.trans dvd_imp_le less_le_trans less_numeral_extra(1) mem_Collect_eq)
  from  \<open>odd (OddPart x)\<close>  \<open>Jdvd (OddPart x) n\<close>   \<open>OddPart x \<le> k\<close> 
   have \<open>OddPart x \<in> A\<close> using  \<open>A = {d | d :: nat. odd d \<and> Jdvd d n \<and> d \<le> k}\<close>
     by blast
   then show ?thesis by blast
 qed

lemma OddPartfromAtoB:
 fixes n k :: nat 
 assumes \<open>n \<ge> 1\<close> and \<open>A = {d | d :: nat. odd d \<and> Jdvd d n \<and> d \<le> k}\<close> and \<open>B = {d | d :: nat. even d \<and> Jdvd d n \<and> d \<le> k}\<close> 
 shows \<open>OddPart ` B \<subseteq> A\<close>
  using OddPartfromAtoB1  assms(1) assms(2) assms(3) image_subsetI by blast

lemma JsignsCardIneq:
  fixes n k :: nat
  assumes \<open>n \<ge> 1\<close>
  shows \<open>(card {d | d :: nat. odd d \<and> Jdvd d n \<and> d \<le> k}) \<ge> (card {d | d :: nat. even d \<and> Jdvd d n \<and> d \<le> k})\<close>
proof-
  obtain A where \<open>A = {d | d :: nat. odd d \<and> Jdvd d n \<and> d \<le> k}\<close> by blast
  obtain B where \<open>B = {d | d :: nat. even d \<and> Jdvd d n \<and> d \<le> k}\<close> by blast
  have \<open>finite A\<close> 
    using \<open>A = {d |d. odd d \<and> Jdvd d n \<and> d \<le> k}\<close> finite_nat_set_iff_bounded_le by blast
  have \<open>finite B\<close>
    using \<open>B = {d |d. even d \<and> Jdvd d n \<and> d \<le> k}\<close> finite_nat_set_iff_bounded_le by blast
  have \<open>inj_on OddPart B\<close> 
    using  OddPartfromAtoBinj \<open>B = {d |d. even d \<and> Jdvd d n \<and> d \<le> k}\<close> assms by blast    
  have  \<open>OddPart ` B \<subseteq> A\<close>
    using OddPartfromAtoB  \<open>A = {d | d :: nat. odd d \<and> Jdvd d n \<and> d \<le> k}\<close> \<open>B = {d | d :: nat. even d \<and> Jdvd d n \<and> d \<le> k}\<close>  \<open>n \<ge> 1\<close>
    by blast
  have \<open> card B \<le> card A\<close> using InjIneqCard  \<open>OddPart ` B \<subseteq> A\<close> \<open>inj_on OddPart B\<close> 
      \<open>finite A\<close>  \<open>finite B\<close> by blast
  then show ?thesis 
    using \<open>A = {d |d. odd d \<and> Jdvd d n \<and> d \<le> k}\<close> \<open>B = {d |d. even d \<and> Jdvd d n \<and> d \<le> k}\<close> by blast
qed

subsubsection {* Miscellany Results *}

lemma SchroederArithmL2X1 :
  fixes n :: nat
  assumes \<open>n \<ge> 1\<close>
  shows \<open> \<forall> k. (Jsigns n) k \<in> {-1, 0, 1} \<close>
  by (simp add: Jsigns_def)

lemma JdvdL1 :
  fixes n k :: nat
  assumes \<open>n \<ge> 1\<close> and \<open>k \<ge> 2*n\<close>
  shows \<open>\<not> Jdvd (Suc k) n\<close> 
  using assms Jdvd_def 
  by (metis (no_types, lifting) One_nat_def Suc_1 le_SucI  mult_numeral_1_right nat_mult_le_cancel_disj not_less_eq_eq numeral_One one_le_mult_iff)

lemma SchroederArithmL2X2Y2 :
  fixes n k :: nat
  assumes \<open>n \<ge> 1\<close> and  \<open>\<not> Jdvd (Suc k) n\<close> 
  shows \<open> (Jsigns n) k = 0 \<close>
  by (simp add: Jsigns_def assms(2))

lemma SchroederArithmL2X2Y1 :
  fixes n k :: nat
  assumes \<open>n \<ge> 1\<close> and \<open>k \<ge> 2*n\<close>
  shows \<open> (Jsigns n) k = 0 \<close>
  using JdvdL1 SchroederArithmL2X2Y2 assms by blast

lemma SchroederArithmL2X2 :
  fixes n :: nat
  assumes \<open>n \<ge> 1\<close>
  shows \<open> PolyFun (Jsigns n) \<close>
  using assms SchroederArithmL2X2Y1 PolyFun_def 
  by (metis (mono_tags, lifting) LARGE_def)

lemma SchroederArithmL2 :
  fixes n :: nat
  assumes \<open>n \<ge> 1\<close>
  shows \<open> ThreeWord  (Jsigns n) \<close>
  using SchroederArithmL2X1 SchroederArithmL2X2 ThreeWord_def assms  by metis


lemma JsignsSumToDiffCardLebesgue:
  fixes n k :: nat
  assumes \<open>n \<ge> 1\<close>
  shows \<open>(\<Sum>j < k. (Jsigns n) j) = 
          ((card {j | j :: nat. (Jsigns n) j = 1 \<and> j < k})::int)
        - ((card {j | j :: nat. (Jsigns n) j = -1 \<and> j < k})::int)\<close>
  using JsignsSumToDiffCardLebesgueG Jsigns_def by presburger

lemma preJsignsSumToDiffCardPlus:
  fixes n j :: nat
  assumes \<open>n \<ge> 1\<close> 
  shows \<open>(Jdvd (Suc j) n)\<and>(odd (Suc j))  \<longleftrightarrow>  Jsigns n j = 1\<close>
  by (simp add: Jsigns_def)

lemma preSJsignsSumToDiffCardPlus:
  fixes n k :: nat
  assumes \<open>n \<ge> 1\<close>
  shows \<open> {j | j :: nat. odd (Suc j) \<and> Jdvd (Suc j) n \<and> j < k}
       =  {j | j :: nat. (Jsigns n) j = 1 \<and> j < k} \<close>
  using preJsignsSumToDiffCardPlus assms by blast

lemma JsignsSumToDiffCardPlus:
  fixes n k :: nat
  assumes \<open>n \<ge> 1\<close>
  shows \<open>(card {d | d :: nat. odd d \<and> Jdvd d n \<and> d \<le> k})
       = (card {j | j :: nat. (Jsigns n) j = 1 \<and> j < k}) \<close>
proof-
  from \<open>n \<ge> 1\<close> have  \<open> {j | j :: nat. odd (Suc j) \<and> Jdvd (Suc j) n \<and> j < k}
       =  {j | j :: nat. (Jsigns n) j = 1 \<and> j < k} \<close> using preSJsignsSumToDiffCardPlus by blast
  then have \<open> {j | j :: nat. odd (Suc j) \<and> Jdvd (Suc j) n \<and> Suc j \<le> k}
       =  {j | j :: nat. (Jsigns n) j = 1 \<and> j < k} \<close> 
    by (simp add: Suc_le_eq)
  then have \<open>card {j | j :: nat. (odd (Suc j) \<and> Jdvd (Suc j) n \<and> Suc j \<le> k)}
       = card {j | j :: nat. (Jsigns n) j = 1 \<and> j < k} \<close> by auto
  have \<open>finite {j | j :: nat. j \<ge> 1  \<and> (odd j \<and> Jdvd j n \<and> j \<le> k)}\<close> 
    using finite_nat_set_iff_bounded_le by blast
  have \<open>finite {j | j :: nat. (odd (Suc j) \<and> Jdvd (Suc j) n \<and> Suc j \<le> k)}\<close> 
    using \<open>{j |j. odd (Suc j) \<and> Jdvd (Suc j) n \<and> Suc j \<le> k} = {j |j. Jsigns n j = 1 \<and> j < k}\<close> by auto
  have \<open>card {j | j :: nat. j \<ge> 1  \<and> (odd j \<and> Jdvd j n \<and> j \<le> k)} = card {j | j :: nat. (odd (Suc j) \<and> Jdvd (Suc j) n \<and> Suc j \<le> k)}\<close>
    using CardSetSuc  \<open>finite {j | j :: nat. j \<ge> 1  \<and> (odd j \<and> Jdvd j n \<and> j \<le> k)}\<close> \<open>finite {j | j :: nat. (odd (Suc j) \<and> Jdvd (Suc j) n \<and> Suc j \<le> k)}\<close> 
    by auto
  then  have \<open>card {d | d :: nat. d \<ge> 1  \<and> (odd d \<and> Jdvd d n \<and> d \<le> k)}
       = card {j | j :: nat. (Jsigns n) j = 1 \<and> j < k} \<close> 
    using \<open>card {j |j. odd (Suc j) \<and> Jdvd (Suc j) n \<and> Suc j \<le> k} = card {j |j. Jsigns n j = 1 \<and> j < k}\<close> by linarith
  have \<open>\<forall> d. Jdvd d n \<longrightarrow> d \<ge> 1\<close> 
    by (metis (full_types)  Jdvd_def  assms   le_numeral_extra(4) less_imp_le less_one linorder_cases mult_zero_left  no_zero_divisors   power_0  zero_power2)
  then have  \<open>{d | d :: nat. d \<ge> 1  \<and> (odd d \<and> Jdvd d n \<and> d \<le> k)} = {d | d :: nat. (odd d \<and> Jdvd d n \<and> d \<le> k)}  \<close>
    by blast
  then have \<open>card {d | d :: nat. (odd d \<and> Jdvd d n \<and> d \<le> k)} =  card {j | j :: nat. (Jsigns n) j = 1 \<and> j < k}\<close>
    using \<open>card {d |d. 1 \<le> d \<and> odd d \<and> Jdvd d n \<and> d \<le> k} = card {j |j. Jsigns n j = 1 \<and> j < k}\<close> by auto
  then show ?thesis 
    by blast
qed

lemma preJsignsSumToDiffCardMinus:
  fixes n j :: nat
  assumes \<open>n \<ge> 1\<close> 
  shows \<open>(Jdvd (Suc j) n)\<and>(even (Suc j))  \<longleftrightarrow>  Jsigns n j = -1\<close>
  by (simp add: Jsigns_def)

lemma preSJsignsSumToDiffCardMinus:
  fixes n k :: nat
  assumes \<open>n \<ge> 1\<close>
  shows \<open> {j | j :: nat. even (Suc j) \<and> Jdvd (Suc j) n \<and> j < k}
       =  {j | j :: nat. (Jsigns n) j = -1 \<and> j < k} \<close>
  using preJsignsSumToDiffCardMinus assms by blast

lemma JsignsSumToDiffCardMinus:
  fixes n k :: nat
  assumes \<open>n \<ge> 1\<close>
  shows \<open>(card {d | d :: nat. even d \<and> Jdvd d n \<and> d \<le> k})
       = (card {j | j :: nat. (Jsigns n) j = -1 \<and> j < k}) \<close>
  proof-
  from \<open>n \<ge> 1\<close> have  \<open> {j | j :: nat. even (Suc j) \<and> Jdvd (Suc j) n \<and> j < k}
       =  {j | j :: nat. (Jsigns n) j = -1 \<and> j < k} \<close> using preSJsignsSumToDiffCardMinus by blast
  then have \<open> {j | j :: nat. even (Suc j) \<and> Jdvd (Suc j) n \<and> Suc j \<le> k}
       =  {j | j :: nat. (Jsigns n) j = -1 \<and> j < k} \<close> 
    by (simp add: Suc_le_eq)
  then have \<open>card {j | j :: nat. (even (Suc j) \<and> Jdvd (Suc j) n \<and> Suc j \<le> k)}
       = card {j | j :: nat. (Jsigns n) j = -1 \<and> j < k} \<close> by auto
  have \<open>finite  {j | j :: nat. j \<ge> 1  \<and> (even j \<and> Jdvd j n \<and> j \<le> k)}\<close> 
    using finite_nat_set_iff_bounded_le by blast
  have \<open>finite {j | j :: nat. (even (Suc j) \<and> Jdvd (Suc j) n \<and> Suc j \<le> k)}\<close> 
    by (metis (no_types, lifting) \<open>{j |j. even (Suc j) \<and> Jdvd (Suc j) n \<and> Suc j \<le> k} = {j |j. Jsigns n j = - 1 \<and> j < k}\<close> finite_nat_set_iff_bounded_le mem_Collect_eq order_less_imp_le)
  have \<open>card {j | j :: nat. j \<ge> 1  \<and> (even j \<and> Jdvd j n \<and> j \<le> k)} = card {j | j :: nat. (even (Suc j) \<and> Jdvd (Suc j) n \<and> Suc j \<le> k)}\<close>
    using CardSetSuc \<open>finite  {j | j :: nat. j \<ge> 1  \<and> (even j \<and> Jdvd j n \<and> j \<le> k)}\<close>  \<open>finite {j | j :: nat. (even (Suc j) \<and> Jdvd (Suc j) n \<and> Suc j \<le> k)}\<close> 
    by auto
  then  have \<open>card {d | d :: nat. d \<ge> 1  \<and> (even d \<and> Jdvd d n \<and> d \<le> k)}
       = card {j | j :: nat. (Jsigns n) j = -1 \<and> j < k} \<close> 
    using \<open>card {j |j. even (Suc j) \<and> Jdvd (Suc j) n \<and> Suc j \<le> k} = card {j |j. Jsigns n j = -1 \<and> j < k}\<close> by linarith
  have \<open>\<forall> d. Jdvd d n \<longrightarrow> d \<ge> 1\<close> 
    by (metis (full_types)  Jdvd_def  assms   le_numeral_extra(4) less_imp_le less_one linorder_cases mult_zero_left  no_zero_divisors   power_0  zero_power2)
  then have  \<open>{d | d :: nat. d \<ge> 1  \<and> (even d \<and> Jdvd d n \<and> d \<le> k)} = {d | d :: nat. (even d \<and> Jdvd d n \<and> d \<le> k)}  \<close>
    by blast
  then have \<open>card {d | d :: nat. (even d \<and> Jdvd d n \<and> d \<le> k)} =  card {j | j :: nat. (Jsigns n) j = -1 \<and> j < k}\<close>
    using \<open>card {d |d. 1 \<le> d \<and> even d \<and> Jdvd d n \<and> d \<le> k} = card {j |j. Jsigns n j = -1 \<and> j < k}\<close> by auto
  then show ?thesis 
    by blast
qed

lemma JsignsSumToDiffCard:
  fixes n k :: nat
  assumes \<open>n \<ge> 1\<close>
  shows \<open>(\<Sum>j < k. (Jsigns n) j) = 
          ((card {d | d :: nat. odd d \<and> Jdvd d n \<and> d \<le> k})::int)
        - ((card {d | d :: nat. even d \<and> Jdvd d n \<and> d \<le> k})::int)\<close>
  using assms JsignsSumToDiffCardLebesgue JsignsSumToDiffCardPlus JsignsSumToDiffCardMinus
  by auto

lemma preJsignsWordToFunId :
  fixes n j :: nat and w :: \<open>SCHR list\<close> 
  assumes \<open>n \<ge> 1\<close> and \<open> WordToFun w = Jsigns n \<close> and \<open>j < length w\<close>
  shows \<open>SchroederCode (w ! j) = (Jsigns n) j \<close>
  by (metis WordToFun_def assms(2) assms(3))

lemma SchroederPHeightSumRec:
  fixes  w :: \<open>SCHR list\<close> and a :: SCHR 
  assumes \<open>SchroederPHeight w = (\<Sum>j < length w. SchroederCode( w ! j ))\<close>
  shows \<open>SchroederPHeight (a # w) = (\<Sum>j < length (a # w). SchroederCode( (a # w) ! j ))\<close>
proof-
  have \<open>SchroederPHeight (a # w) = (SchroederCode a) + (SchroederPHeight w)\<close> 
    using SchroederCode_def SchroederPHeight_def  PHeightLetterwise.simps(1)  PHeightLetterwise.simps(2)
    by (smt SCHR.exhaust SchroederPHeightLetter.simps(1) SchroederPHeightLetter.simps(2) SchroederPHeightLetter.simps(3))
    have \<open>(a # w) ! 0 = a\<close>
    by simp
  have \<open>length (a # w) = Suc (length w)\<close> 
    by simp
  have \<open>\<forall> j. j < length w \<longrightarrow> (a # w) ! (Suc j) = w ! j\<close> 
    by simp
  have \<open>(\<Sum>j < length w. SchroederCode( w ! j ) ) = (\<Sum>j < length w. SchroederCode( (a # w) ! (Suc j) ) )\<close>
    by simp
  then have  \<open>(\<Sum>j < length w. SchroederCode( w ! j ) )+(SchroederCode a) = (\<Sum>j < length w. SchroederCode( (a # w) ! (Suc j) ) )+ SchroederCode( (a # w) ! 0)\<close>
   using \<open>(a # w) ! 0 = a\<close> by presburger
  then have \<open>SchroederPHeight (a # w) = (\<Sum>j < length w. SchroederCode( (a # w) ! (Suc j) ) )+ SchroederCode( (a # w) ! 0)\<close>
    using \<open>SchroederPHeight (a # w) = SchroederCode a + SchroederPHeight w\<close> assms by linarith
  then show ?thesis 
    by (smt \<open>length (a # w) = Suc (length w)\<close> sum.cong sum_lessThan_Suc_shift)
qed

lemma SchroederPHeightSum:
  fixes  w :: \<open>SCHR list\<close> 
  shows \<open>SchroederPHeight w = (\<Sum>j < length w. SchroederCode( w ! j ))\<close>
proof(induction w)
  case Nil
  then show ?case 
        by (simp add: SchroederPHeight_def)
next
  case (Cons a w)
  then show ?case 
    using SchroederPHeightSumRec by blast
qed

lemma JsignsWordToFunId :
  fixes n :: nat and w :: \<open>SCHR list\<close> 
  assumes \<open>n \<ge> 1\<close> and \<open> WordToFun w = Jsigns n \<close>
  shows \<open>SchroederPHeight w = (\<Sum>j < length w. (Jsigns n) j) \<close>
  by (metis (no_types, lifting) SchroederPHeightSum WordToFun_def assms(2) lessThan_iff sum.cong)

lemma JsignsWordToFunIdprefix :
  fixes n :: nat and v w :: \<open>SCHR list\<close> 
  assumes \<open>n \<ge> 1\<close> and \<open> WordToFun w = Jsigns n \<close> and \<open>prefix v w\<close>
  shows \<open>SchroederPHeight v = (\<Sum>j < length v. (Jsigns n) j) \<close>
  by (smt SchroederPHeightSum WordToFun_def assms(2) assms(3) lessThan_iff less_le_trans prefix_def sum.cong)

lemma preJsignsWordToFunPSgeq0prefix :
  fixes n k :: nat 
  assumes \<open>n \<ge> 1\<close>
  shows \<open>(\<Sum>j < k. (Jsigns n) j) \<ge> 0\<close>
  using JsignsSumToDiffCard JsignsCardIneq assms by auto

lemma JsignsWordToFunPSgeq0prefix :
  fixes n :: nat and v w :: \<open>SCHR list\<close> 
  assumes \<open>n \<ge> 1\<close> and \<open> WordToFun w = Jsigns n \<close> and \<open>prefix v w\<close>
  shows \<open>(\<Sum>j < length v. (Jsigns n) j) \<ge> 0\<close>
  using  preJsignsWordToFunPSgeq0prefix assms by auto

lemma preJsignsWordToFunPSeq0 :
  fixes n :: nat and w :: \<open>SCHR list\<close> 
  assumes \<open>n \<ge> 1\<close> and \<open> WordToFun w = Jsigns n \<close>
  shows \<open>length w \<ge> 2*n\<close>
proof (rule classical)
  assume \<open>\<not>(length w \<ge> 2*n)\<close>
  then have \<open>length w < 2*n\<close> by simp
  have \<open>\<forall> j. j > length w \<longrightarrow> (Jsigns n) j = 0\<close> 
    by (metis WordToFun_def assms(2) order.asym)
  then have \<open>(Jsigns n) ((2*n)-1) = 0\<close> using  \<open>length w < 2*n\<close> 
    by (metis One_nat_def Suc_leI Suc_pred WordToFun_def \<open>\<not> 2 * n \<le> length w\<close> assms(1) assms(2) less_le_trans less_numeral_extra(1) nat_0_less_mult_iff pos2)
  have \<open>Jdvd (2*n) n\<close> 
    by (metis Jdvd_def One_nat_def even_Suc mult.right_neutral nat.simps(3) odd_Suc_minus_one semiring_normalization_rules(7))
  then have  \<open>(Jsigns n) ((2*n)-1) \<noteq> 0\<close> using Jsigns_def 
    by (smt One_nat_def Suc_1 Suc_pred assms(1) less_le_trans nat_0_less_mult_iff zero_less_Suc)
  show ?thesis 
    using \<open>Jsigns n (2 * n - 1) = 0\<close> \<open>Jsigns n (2 * n - 1) \<noteq> 0\<close> by blast
qed 

lemma JsignsWordToFunPSeq0 :
  fixes n :: nat and w :: \<open>SCHR list\<close> 
  assumes \<open>n \<ge> 1\<close> and \<open> WordToFun w = Jsigns n \<close>
  shows \<open>(\<Sum>j < length w. (Jsigns n) j) = 0\<close>
proof-
  have \<open>length w \<ge> 2*n\<close> 
    using assms(1) assms(2) preJsignsWordToFunPSeq0 by blast
  have  \<open>(\<Sum>j < length w. (Jsigns n) j) = ((card {d | d :: nat. odd d \<and> Jdvd d n \<and> d \<le> length w})::int)
        - ((card {d | d :: nat. even d \<and> Jdvd d n \<and> d \<le> length w})::int)\<close>
    using JsignsSumToDiffCard assms(1) by auto
  have \<open>(card {d | d :: nat. odd d \<and> Jdvd d n \<and> d \<le> length w})
        = (card {d | d :: nat. even d \<and> Jdvd d n \<and> d \<le> length w})\<close> 
  using JsignsCardEq \<open>2 * n \<le> length w\<close> assms(1) by auto
  show ?thesis 
    using \<open>card {d |d. odd d \<and> Jdvd d n \<and> d \<le> length w} = card {d |d. even d \<and> Jdvd d n \<and> d \<le> length w}\<close> \<open>sum (Jsigns n) {..<length w} = int (card {d |d. odd d \<and> Jdvd d n \<and> d \<le> length w}) - int (card {d |d. even d \<and> Jdvd d n \<and> d \<le> length w})\<close> by linarith
  qed

lemma SchroederArithmL3A :
  fixes n :: nat and w :: \<open>SCHR list\<close> 
  assumes \<open>n \<ge> 1\<close> and \<open> WordToFun w = Jsigns n \<close> and \<open>length w = 2*n\<close>
  shows \<open>SchroederPHeight w = 0\<close>
  using assms JsignsWordToFunId JsignsWordToFunPSeq0 
  by simp

lemma SchroederArithmL3B :
  fixes n :: nat and v w :: \<open>SCHR list\<close> 
  assumes \<open>n \<ge> 1\<close> and \<open> WordToFun w = Jsigns n \<close> and \<open>prefix v w\<close>  
  shows \<open>SchroederPHeight v \<ge> 0\<close>
  using assms JsignsWordToFunIdprefix JsignsWordToFunPSgeq0prefix by simp

lemma SchroederArithmL3 :
  fixes n :: nat and w :: \<open>SCHR list\<close> 
  assumes \<open>n \<ge> 1\<close> and \<open> WordToFun w = Jsigns n \<close>
  shows \<open>SchroederPath w\<close>
  using  AbstractPath_def  JsignsWordToFunId JsignsWordToFunPSeq0 SchroederArithmL3B SchroederPath_def assms(1) assms(2) 
  by (metis (full_types)  )

lemma FromFunToThreeWordE1QRec:
  fixes  K :: nat and f :: \<open>nat\<Rightarrow>int\<close>
  assumes \<open>\<forall> f :: nat\<Rightarrow>int. (\<forall> n. f n \<in> {-1, 0, 1})\<and>(\<forall> k. k \<ge> K \<longrightarrow> f k = 0)\<longrightarrow> (\<exists> w:: SCHR list. f = WordToFun w \<and> length w = K) \<close>
    and \<open>\<forall> n. f n \<in> {-1, 0, 1}\<close> and \<open>\<forall> k. k \<ge> Suc K \<longrightarrow> f k = 0\<close>
  shows \<open>\<exists> w:: SCHR list. f = WordToFun w \<and> length w = Suc K\<close>
proof-
  obtain g :: \<open>nat \<Rightarrow> int\<close> where \<open>g \<equiv> \<lambda> n. (if n < K then f n else 0)\<close>
    by blast
  from  \<open>g \<equiv> \<lambda> n. (if n < K then f n else 0)\<close> \<open>\<forall> n. f n \<in> {-1, 0, 1}\<close> have \<open>\<forall> n. g n \<in> {-1, 0, 1}\<close>
    by auto
  from  \<open>g \<equiv> \<lambda> n. (if n < K then f n else 0)\<close>  \<open>\<forall> k. k \<ge> Suc K \<longrightarrow> f k = 0\<close> have  \<open>\<forall> k. k \<ge> K \<longrightarrow> g k = 0\<close>
    by simp
  then obtain w :: \<open>SCHR list\<close> where \<open>WordToFun w = g\<close>  and \<open>length w = K\<close>
    using \<open>\<forall>n. g n \<in> {- 1, 0, 1}\<close> assms(1) by blast
  have \<open>f K = 0 \<or> f K = 1 \<or> f K = -1\<close> 
    using assms(2) by blast
  then obtain q :: SCHR where \<open>SchroederCode q = f K\<close> 
    by (metis SCHR.distinct(1) SCHR.distinct(5) SCHR.simps(4) SchroederCode_def  )
  then obtain ww :: \<open>SCHR list\<close> where \<open>ww = w @ [q]\<close> 
    by blast
  have \<open>\<forall> j. j < length w \<longrightarrow> (ww ! j) =  (w ! j)\<close> 
    by (simp add: \<open>ww = w @ [q]\<close> nth_append)
  then have \<open>\<forall> j. j < length w \<longrightarrow> (WordToFun ww)  j =  (WordToFun w)  j\<close> 
    by (simp add: WordToFun_def \<open>ww = w @ [q]\<close>)
  then have  \<open>\<forall> j. j < length w \<longrightarrow> (WordToFun ww)  j = g  j\<close> 
    using \<open>WordToFun w = g\<close> by blast
  have \<open>length ww = Suc K\<close> 
    by (simp add: \<open>length w = K\<close> \<open>ww = w @ [q]\<close>)
   have  \<open>\<forall> j. j \<le> K \<longrightarrow> (WordToFun ww)  j = f  j\<close> 
     by (metis WordToFun_def \<open>SchroederCode q = f K\<close> \<open>\<forall>j<length w. WordToFun ww j = g j\<close> \<open>g \<equiv> \<lambda>n. if n < K then f n else 0\<close> \<open>length w = K\<close> \<open>length ww = Suc K\<close> \<open>ww = w @ [q]\<close> le_imp_less_Suc le_less nth_append_length)
   have  \<open>\<forall> j. j \<ge> Suc K \<longrightarrow> (WordToFun ww)  j = f  j\<close> 
     by (simp add: WordToFun_def \<open>length ww = Suc K\<close> assms(3))
   have  \<open>\<forall> j. (WordToFun ww)  j = f  j\<close> 
     using \<open>\<forall>j\<ge>Suc K. WordToFun ww j = f j\<close> \<open>\<forall>j\<le>K. WordToFun ww j = f j\<close> not_less_eq_eq by blast
   then    have  \<open>(WordToFun ww)  = f \<close> by blast
   show ?thesis 
     using \<open>WordToFun ww = f\<close> \<open>length ww = Suc K\<close> by auto
 qed

lemma FromFunToThreeWordE1Qbase:
  fixes  f :: \<open>nat\<Rightarrow>int\<close>
  assumes \<open>\<forall> n. f n \<in> {-1, 0, 1}\<close> and \<open>\<forall> k. k \<ge> 0 \<longrightarrow> f k = 0\<close>
  shows \<open>\<exists> w:: SCHR list. f = WordToFun w \<and> length w = 0\<close>
proof-
  have \<open>length Nil = 0\<close> 
    by blast
  from \<open>\<forall> k. k \<ge> 0 \<longrightarrow> f k = 0\<close> have \<open>\<forall> k. f k = 0\<close> 
    by blast
  have \<open>\<forall> k. (WordToFun Nil) k = 0\<close> 
    by (simp add: WordToFun_def)
  then have \<open>\<forall> k. f k = (WordToFun Nil) k\<close> using  \<open>\<forall> k. f k = 0\<close> 
    by simp
  then have \<open>f = WordToFun Nil\<close> by blast
  show ?thesis 
    by (simp add: \<open>f = WordToFun []\<close>)
qed

lemma FromFunToThreeWordE1Q:
  fixes  K :: nat
  shows \<open>\<forall> f :: nat\<Rightarrow>int. (\<forall> n. f n \<in> {-1, 0, 1})\<and>(\<forall> k. k \<ge> K \<longrightarrow> f k = 0)\<longrightarrow> (\<exists> w:: SCHR list. f = WordToFun w \<and> length w = K) \<close>
proof(induction K)
  case 0
  then show ?case 
    using FromFunToThreeWordE1Qbase by auto
next
  case (Suc K)
  then show ?case  
    by (simp add: FromFunToThreeWordE1QRec)
qed

lemma FromFunToThreeWordE:
  fixes f :: \<open>nat \<Rightarrow> int\<close>
  assumes \<open>ThreeWord f\<close>
  shows \<open>\<exists> w:: SCHR list. f = WordToFun w \<close>
  by (metis (mono_tags, lifting) FromFunToThreeWordE1Q LARGE_def PolyFun_def ThreeWord_def assms)

lemma SchroederArithmL1 :
  fixes n :: nat
  assumes \<open>n \<ge> 1\<close>
  shows \<open>\<exists> w :: SCHR list.  WordToFun w = Jsigns n \<and> SchroederPath w \<close>
  using FromFunToThreeWordE SchroederArithmL2 SchroederArithmL3 assms by fastforce


proposition SchroederArithmA :
  fixes n :: nat
  assumes \<open>n \<ge> 1\<close>
  shows \<open>\<exists> w :: SCHR list. n \<in> SchroederClass w \<and> SchroederPath w \<close>
  by (metis (mono_tags, lifting) SchroederArithmL1 SchroederClass_def assms mem_Collect_eq)

section {* Dyck Paths *}

definition STRANGEL :: \<open>SCHR list \<Rightarrow> int\<close> where 
\<open>STRANGEL \<equiv> (PHeightLetterwise (\<lambda> c::SCHR. (if c = STRANGE then (1::int) else (0::int)))) \<close>

lemma STRANGELCHAR:
  fixes w :: \<open>SCHR list\<close> and a :: SCHR
  shows \<open>STRANGEL (a # w) = (if a = STRANGE then (STRANGEL w) + 1 else  (STRANGEL w)) \<close>
  by (simp add: STRANGEL_def)

lemma STRANGELCHARGE0:
  fixes w :: \<open>SCHR list\<close>
  shows \<open>STRANGEL w \<ge> 0 \<close>
proof(induction w)
  case Nil
  then show ?case 
    by (simp add: STRANGEL_def)
next
  case (Cons a w)
  then show ?case
    by (simp add: STRANGELCHAR)
qed

lemma STRANGELCHAR1:
  fixes w :: \<open>SCHR list\<close> and a :: SCHR
  assumes  \<open>STRANGEL (a # w) = 0\<close> 
  shows \<open>STRANGEL w = 0\<close>
  using assms STRANGELCHARGE0 STRANGELCHAR 
  by smt

lemma STRANGELCHAR2:
  fixes w :: \<open>SCHR list\<close> and a :: SCHR
  assumes  \<open>STRANGEL (a # w) = 0\<close> 
  shows \<open>a \<noteq> STRANGE\<close>
  using STRANGELCHAR STRANGELCHAR1 assms by fastforce

lemma DyckToSchroederSchroederToDyckRec:
  fixes w :: \<open>SCHR list\<close>
  assumes \<open>STRANGEL w = 0 \<longrightarrow> DyckToSchroeder (SchroederToDyck w) = w\<close>
  and \<open>STRANGEL (a # w) = 0\<close>
shows \<open>DyckToSchroeder (SchroederToDyck (a # w)) = a # w\<close>
  using assms STRANGELCHAR1 STRANGELCHAR2 SchroederToDyckCode_def
  by (metis (full_types) DCHR.distinct(1) DyckToSchroeder.simps(2) DyckToSchroederCode_def SCHR.distinct(1)   SCHR.exhaust   SchroederToDyck.simps(2) append_Cons append_Nil)

lemma DyckToSchroederSchroederToDyck:
  fixes w :: \<open>SCHR list\<close>
  shows \<open>STRANGEL w = 0 \<longrightarrow> DyckToSchroeder (SchroederToDyck w) = w\<close>
proof(induction w)
  case Nil
  then show ?case 
    by simp
next
  case (Cons a w)
  then show ?case 
    using DyckToSchroederSchroederToDyckRec by blast
qed

lemma PHeightZeroStrange:
  fixes w :: \<open>DCHR list\<close>
shows \<open>SchroederPHeight (DyckToSchroeder w) = DyckPHeight w\<close>
proof(induction w)
  case Nil
  then show ?case 
    by (simp add: DyckPHeight_def SchroederPHeight_def)
next
  case (Cons a w)
  then show ?case 
    by (metis (full_types) DCHR.exhaust DyckPHeightLetter.simps(1) DyckPHeightLetter.simps(2) DyckPHeight_def DyckToSchroeder.simps(2) DyckToSchroederCode_def PHeightLetterwise.simps(2) SchroederPHeightLetter.simps(1) SchroederPHeightLetter.simps(2) SchroederPHeight_def)
qed

lemma DyckIsSchroederH0:
  fixes w :: \<open>DCHR list\<close>
  shows \<open>SchroederPHeight (DyckToSchroeder w) = 0 \<longrightarrow> DyckPHeight w = 0\<close>
  using PHeightZeroStrange by auto

lemma prefixL1:
  fixes u w :: \<open>'b list\<close> 
  assumes \<open>prefix u (a # w)\<close> and \<open>u \<noteq> []\<close>
  shows \<open>\<exists> uu. u = a # uu\<close>
proof -
obtain bb :: "'b list \<Rightarrow> 'b" and bbs :: "'b list \<Rightarrow> 'b list" where
  f1: "\<forall>bs. ([] \<noteq> bs \<or> (\<forall>b bsa. b # bsa \<noteq> bs)) \<and> (bb bs # bbs bs = bs \<or> [] = bs)"
  by (metis (no_types) neq_Nil_conv)
  { assume "a # bbs u \<noteq> u"
    then have "\<exists>bs. bs @ u = bs"
      using f1 by (metis append_Nil assms(1) length_greater_0_conv nth_Cons_0 prefix_def)
then have ?thesis
using assms(2) by force }
  then show ?thesis
    by (metis (full_types))
qed

lemma prefixL2:
  fixes u w :: \<open>'b list\<close> 
  assumes \<open>prefix (a # u) (a # w)\<close>
  shows \<open>prefix u w\<close>
  by (metis (no_types, lifting) Suc_le_mono Suc_less_eq assms length_Cons nth_Cons_Suc prefix_def)

lemma prefixL3:
  fixes u w :: \<open>'b list\<close>
  assumes \<open>prefix u w\<close>
  shows \<open>prefix (x # u) (x # w) \<close>
proof-
  from \<open>prefix u w\<close> have \<open>( (length u \<le> length w)
 \<and> (\<forall> j. j < length u \<longrightarrow>  u ! j =  w ! j ) )\<close> by (simp add: prefix_def)
  then have \<open>length u \<le> length w\<close> by blast
  then have \<open>length (x # u) \<le> length (x # w)\<close> 
    by simp
  from  \<open>( (length u \<le> length w)
 \<and> (\<forall> j. j < length u \<longrightarrow>  u ! j =  w ! j ) )\<close>
  have  \<open>(\<forall> j. j < length u \<longrightarrow>  u ! j =  w ! j )\<close> by blast
  then have \<open>(\<forall> j. Suc j < length (x # u) \<longrightarrow>  (x # u) ! (Suc j) =  (x # w) ! (Suc j) )\<close>
    by simp
  then have \<open>(\<forall> j. j < length (x # u) \<longrightarrow>  (x # u) ! j =  (x # w) ! j )\<close> 
    by (simp add: nth_Cons')
  then show ?thesis using  \<open>length (x # u) \<le> length (x # w)\<close> 
    by (simp add: prefix_def)
qed

lemma DyckIsSchroederPrefixOntoRec:
  fixes w u :: \<open>DCHR list\<close> 
  assumes \<open>\<forall> u. (prefix u w \<longrightarrow> prefix (DyckToSchroeder u) (DyckToSchroeder w))\<close>
  and \<open>prefix u (a # w)\<close>
  shows  \<open> prefix (DyckToSchroeder u) (DyckToSchroeder (a # w))\<close>
proof(cases \<open>u = []\<close>)
  case True
  then show ?thesis 
    by (simp add: prefix_def)
next
  case False
  then obtain uu where \<open>u = a # uu\<close> 
    by (meson assms(2) prefixL1)
  have \<open>prefix uu w\<close> 
    using \<open>u = a # uu\<close> assms(2) prefixL2 by fastforce
  have \<open>prefix (DyckToSchroeder uu) (DyckToSchroeder w)\<close>
    by (simp add: \<open>prefix uu w\<close> assms(1))
  obtain x where \<open>(DyckToSchroeder u) = x # (DyckToSchroeder uu)\<close> 
    by (simp add: \<open>u = a # uu\<close>)
  have \<open>(DyckToSchroeder (a # w)) = x # (DyckToSchroeder w)\<close> 
    using \<open>DyckToSchroeder u = x # DyckToSchroeder uu\<close> \<open>u = a # uu\<close> by auto
  have \<open>prefix (DyckToSchroeder uu) (DyckToSchroeder w)\<close> 
    by (simp add: \<open>prefix (DyckToSchroeder uu) (DyckToSchroeder w)\<close>)
  show ?thesis 
    using \<open>DyckToSchroeder (a # w) = x # DyckToSchroeder w\<close> \<open>DyckToSchroeder u = x # DyckToSchroeder uu\<close> \<open>prefix (DyckToSchroeder uu) (DyckToSchroeder w)\<close> prefixL3 by force
  qed

lemma DyckIsSchroederPrefixOnto:
  fixes w :: \<open>DCHR list\<close> 
  shows \<open>\<forall> u. (prefix u w \<longrightarrow> prefix (DyckToSchroeder u) (DyckToSchroeder w))\<close>
proof (induction w)
case Nil
  then show ?case 
    by (simp add: prefix_def)
next
  case (Cons a w)
  then show ?case using DyckIsSchroederPrefixOntoRec by blast
qed

lemma DyckIsSchroederPrefix:
  fixes w :: \<open>DCHR list\<close>
  shows \<open>(\<forall> v::SCHR list. (prefix v (DyckToSchroeder w) \<longrightarrow> SchroederPHeight v \<ge> 0)) \<longrightarrow> (\<forall> u::DCHR list. (prefix u w \<longrightarrow> DyckPHeight u \<ge> 0))\<close>
  using PHeightZeroStrange DyckIsSchroederPrefixOnto
  by fastforce

lemma DyckIsSchroeder:
  fixes w :: \<open>DCHR list\<close>
  shows \<open>SchroederPath (DyckToSchroeder w) \<longrightarrow> DyckPath w\<close>
  using DyckIsSchroederH0 DyckIsSchroederPrefix SchroederPath_def 
  by (metis AbstractPath_def DyckPath_def)

lemma SchroederTransIntoDyckStranger0:
  fixes w :: \<open>SCHR list\<close>
  assumes \<open>SchroederPath w\<close> and \<open>STRANGEL w = 0\<close>
  shows \<open>DyckPath (SchroederToDyck w)\<close>
  by (simp add: DyckIsSchroeder DyckToSchroederSchroederToDyck assms(1) assms(2))

lemma STRANGELAdd:
  fixes u v :: \<open>SCHR list\<close>
  shows \<open>STRANGEL (u @ v) = (STRANGEL u) + (STRANGEL v)\<close>
proof(induction u)
  case Nil
  then show ?case 
    by (simp add: STRANGEL_def)
next
  case (Cons a u)
  then show ?case 
    by (simp add: STRANGEL_def)
qed

lemma ZPreSchroederStrangeRedPara_nRED:
  fixes w :: \<open>SCHR list\<close>
  shows \<open>(\<forall> u v. w \<noteq> u @ [STRANGE] @ v) \<longrightarrow> STRANGEL w = 0\<close>
proof(induction w)
  case Nil
  then show ?case 
    by (simp add: STRANGEL_def)
next
  case (Cons a w)
  then show ?case 
    by (metis (no_types, hide_lams)  STRANGELCHAR  append_Cons  self_append_conv2)
qed

lemma PreSchroederStrangeRedPara_nRED:
  fixes w :: \<open>SCHR list\<close>
  assumes \<open>STRANGEL w \<noteq> 0\<close>
  shows \<open>\<exists> u v. w = u @ [STRANGE] @ v\<close>
  using ZPreSchroederStrangeRedPara_nRED assms by blast

lemma SchroederToDyckConcat:
  fixes u v :: \<open>SCHR list\<close>
  shows \<open>SchroederToDyck (u @ v) = (SchroederToDyck u) @ (SchroederToDyck v)\<close>
proof(induction u)
case Nil
  then show ?case 
    by simp
next
  case (Cons a u)
  then show ?case 
    by simp
qed

lemma SchroederPHeightAdd:
  fixes u :: \<open>SCHR list\<close>
  shows \<open>\<forall> v. SchroederPHeight (u @ v) = (SchroederPHeight u)+(SchroederPHeight v)\<close>
proof(induction u)
  case Nil
have \<open> (SchroederPHeight Nil) = 0\<close> 
  by (metis DyckPHeight_def DyckToSchroeder.simps(1) PHeightLetterwise.simps(1) PHeightZeroStrange) 
  then show ?case 
    by simp
next
  case (Cons a u)
  then show ?case 
    by (smt Cons_eq_appendI PHeightLetterwise.simps(2) SchroederPHeight_def)
qed

lemma SchroederPHeightSTRANGE:
  \<open>SchroederPHeight [STRANGE] = 0\<close>
  by (simp add: SchroederPHeight_def)

lemma SchroederPathIsNotStrangePHeightZero:
  fixes u v :: \<open>SCHR list\<close>
  assumes \<open>SchroederPHeight (u @ [STRANGE] @ v) = 0\<close>
  shows \<open>SchroederPHeight (u @ v) = 0\<close>
  using SchroederPHeightAdd SchroederPHeightSTRANGE assms by presburger

lemma prefixLX:
  fixes p u v :: \<open>'a list\<close>
  assumes \<open>prefix p u\<close>
  shows  \<open>prefix p (u @ v)\<close>
proof-
  from \<open>prefix p u\<close> have \<open>length p \<le> length u\<close> using prefix_def by metis
  then have \<open>length p \<le> length (u @ v)\<close> 
    by auto
  from \<open>prefix p u\<close> have \<open>\<forall> j. j < length p \<longrightarrow> p ! j = u ! j\<close> using prefix_def by metis
  then have  \<open>\<forall> j. j < length p \<longrightarrow> p ! j = (u @ v) ! j\<close> 
    by (simp add: \<open>length p \<le> length u\<close> less_le_trans nth_append)
  from \<open>length p \<le> length (u @ v)\<close>   \<open>\<forall> j. j < length p \<longrightarrow> p ! j = (u @ v) ! j\<close>  show ?thesis
    by (simp add: prefix_def)
qed

lemma prefixYYBase:
  assumes \<open>prefix u Nil\<close>
  shows  \<open>\<exists> q.  Nil = u @ q\<close>
proof-
  from  \<open>prefix u Nil\<close> prefix_def have \<open>length u \<le> length Nil\<close>
    by (simp add: assms prefix_def)
  then have \<open>u = Nil\<close> 
    by simp
  then show ?thesis 
    by simp
qed

lemma prefixYYRec:
  assumes \<open>prefix u (a # p)\<close> and  \<open>\<forall> u.  prefix u p \<longrightarrow> (\<exists> q.  p = u @ q)\<close>
  shows  \<open>\<exists> q.  a # p = u @ q\<close>
proof(cases \<open>u = Nil\<close>)
  case True
  then show ?thesis 
    by simp
next
  case False
  then have \<open>length u > 0\<close> 
    by blast 
  from  \<open>prefix u (a # p)\<close> have \<open>length u \<le> length (a # p)\<close> by (simp add:  prefix_def)
  from  \<open>prefix u (a # p)\<close> have \<open>\<forall> j. j < length u \<longrightarrow> u ! j = (a # p) ! j\<close> by (simp add:  prefix_def)
  then have \<open>u ! 0 = a\<close> using  \<open>length u > 0\<close> 
    by simp
  then  obtain uu where \<open>u = a # uu\<close> 
    using False assms(1) prefixL1 by fastforce
  have  \<open>length (a # uu) \<le> length (a # p)\<close>  
    using \<open>length u \<le> length (a # p)\<close> \<open>u = a # uu\<close> by blast
  then have \<open>length uu \<le> length  p\<close> 
    by auto  
  have \<open>\<forall> j. j < length (a # uu) \<longrightarrow> (a # uu) ! j = (a # p) ! j\<close>
    using \<open>\<forall>j<length u. u ! j = (a # p) ! j\<close> \<open>u = a # uu\<close> by blast
  then  have \<open>\<forall> j. j < length  uu \<longrightarrow>  uu ! j =  p ! j\<close>
    using assms(2) by auto
  then have \<open>prefix uu p\<close> using  \<open>length uu \<le> length  p\<close>
    by (simp add : prefix_def)
  obtain q where \<open>p = uu @ q\<close> 
    using \<open>prefix uu p\<close> assms(2) by blast
  from \<open>p = uu @ q\<close> have \<open>a # p = a # (uu @ q)\<close> 
    by simp
  then have \<open>a # p = (a # uu) @ q\<close> 
    by simp
  then show ?thesis using \<open>u = a # uu\<close> 
    by blast
qed

lemma prefixYY:
  fixes p :: \<open>'a list\<close>
  shows  \<open>\<forall> u.  prefix u p \<longrightarrow> (\<exists> q.  p = u @ q)\<close>
proof(induction p)
  case Nil
  then show ?case  
    using prefixYYBase by blast
next
  case (Cons a p)
  then show ?case 
    by (simp add: prefixYYRec)
qed

lemma prefixY:
  fixes u v p :: \<open>'a list\<close>
  assumes  \<open>prefix p (u @ v)\<close> and \<open>\<not> (prefix p u)\<close>
  shows \<open>\<exists> q. prefix q v \<and> p = u @ q\<close>
proof-
  from \<open>prefix p (u @ v)\<close> 
  have \<open>length p \<le> length (u @ v)\<close> by (simp add: prefix_def)
  from \<open>prefix p (u @ v)\<close> 
  have \<open>\<forall> j. j < length p \<longrightarrow> p ! j = (u @ v) ! j\<close> 
    by (simp add: prefix_def)
  then have \<open>\<forall> j. j < length p \<and>  j < length u  \<longrightarrow> p ! j = u ! j\<close> 
    by (simp add: nth_append)
  then have \<open>length p > length u\<close> using  \<open>\<not> (prefix p u)\<close> prefix_def
    by (metis (no_types, lifting) dual_order.strict_trans leI linorder_neqE_nat)
  from  \<open>\<forall> j. j < length p \<and>  j < length u  \<longrightarrow> p ! j = u ! j\<close>  and \<open>length p > length u\<close>
  have  \<open>\<forall> j. j < length u  \<longrightarrow> p ! j = u ! j\<close> 
    by auto
  then have \<open>prefix u p\<close> using  \<open>length p > length u\<close> by (simp add: prefix_def)
  then obtain q where \<open>p = u @ q\<close> 
    using prefixYY by blast
  from  \<open>p = u @ q\<close>  \<open>length p \<le> length (u @ v)\<close>
  have  \<open>length  (u @ q) \<le> length (u @ v)\<close>
    by blast
  have \<open>length  (u @ q) = length u + length  q\<close>
    by simp
  have \<open>length  (u @ v) = length u + length  v\<close>
    by simp
  have \<open>length u + length q \<le>  length u + length v\<close> 
    using \<open>length (u @ q) \<le> length (u @ v)\<close> by auto
  then have \<open> length q \<le> length v \<close> 
    using add_le_cancel_left by blast
  have  \<open>\<forall> j. j < length q  \<longrightarrow> q ! j = v ! j\<close> 
    by (metis  \<open>\<forall>j<length p. p ! j = (u @ v) ! j\<close> \<open>length (u @ q) = length u + length q\<close> \<open>p = u @ q\<close> add_less_cancel_left  nth_append_length_plus)
  have \<open>prefix q v\<close> using  \<open>\<forall> j. j < length q  \<longrightarrow> q ! j = v ! j\<close>  \<open> length q \<le> length v \<close> 
    by (simp add: prefix_def)
  then show ?thesis using  \<open>p = u @ q\<close> 
    by blast
qed

lemma prefixZ1:
  fixes u v p :: \<open>'a list\<close>
  assumes \<open>prefix u w\<close> 
  shows \<open>prefix (p @ u) (p @ w)\<close> 
proof(induction p)
  case Nil
  then show ?case 
    by (simp add: assms)
next
  case (Cons a p)
  then show ?case 
    by (simp add: prefixL3)
qed

lemma prefixZ2:
  fixes u v p :: \<open>'a list\<close>
  assumes \<open>prefix (p @ u) (p @ w)\<close>  
  shows  \<open>prefix u w\<close>
proof-
  from  \<open>prefix (p @ u) (p @ w)\<close> 
  have \<open>length (p @ u) \<le> length (p @ w)\<close> 
    by (simp add: prefix_def)
  then have \<open>length u \<le> length w\<close> 
    by simp
  from  \<open>prefix (p @ u) (p @ w)\<close> 
  have \<open>\<forall> j. j < length (p @ u) \<longrightarrow> (p @ u) ! j = (p @ w) ! j\<close>
    by (simp add: prefix_def)
  then have \<open>\<forall> j. j < length  u \<longrightarrow>  u ! j = w ! j\<close>
    by (metis add_less_cancel_left length_append nth_append_length_plus)
  from  \<open>length u \<le> length w\<close>  \<open>\<forall> j. j < length  u \<longrightarrow>  u ! j = w ! j\<close>
  have \<open>prefix u w\<close> by (simp add: prefix_def)
  then show ?thesis by blast
qed

lemma prefixZ:
  fixes u v q x:: \<open>'a list\<close>
  assumes \<open>prefix (u @ q) (u @ v)\<close> 
  shows \<open>prefix (u @ x @ q) (u @ x @ v)\<close> 
  using assms prefixZ1 prefixZ2 by blast

lemma SchroederPathIsNotStrangePHeightREC:
  fixes u v p :: \<open>SCHR list\<close>
  assumes \<open>\<forall> p :: SCHR list. prefix p (u @ [STRANGE] @ v) \<longrightarrow> SchroederPHeight p \<ge> 0\<close>
    and \<open>prefix p (u @ v)\<close>
  shows  \<open>SchroederPHeight p \<ge> 0\<close>
proof(cases \<open>prefix p u\<close>)
  case True
  then have \<open> prefix p (u @ [STRANGE] @ v) \<close> 
    by (simp add: prefixLX)
  then have  \<open>SchroederPHeight p \<ge> 0\<close> 
    using assms(1) by blast
  then show ?thesis by blast
next
  case False
  then obtain q where \<open>prefix q v\<close> and \<open>p = u @ q\<close>
    using assms(2) prefixY by blast
  have \<open>prefix (u @ [STRANGE] @ q) (u @ [STRANGE] @ v)\<close> 
    using \<open>p = u @ q\<close> assms(2) prefixZ by blast
then have \<open>SchroederPHeight (u @ [STRANGE] @ q) \<ge> 0\<close> 
  using assms(1) by blast
  then have  \<open>SchroederPHeight (u @  q) \<ge> 0\<close> 
    using SchroederPHeightAdd SchroederPHeightSTRANGE by smt
  then show ?thesis 
    using \<open>p = u @ q\<close> by blast
qed

lemma SchroederPathIsNotStrange:
  fixes u v :: \<open>SCHR list\<close>
  assumes \<open>SchroederPath (u @ [STRANGE] @ v)\<close>
  shows \<open>SchroederPath (u @ v)\<close>
proof-
  from \<open>SchroederPath (u @ [STRANGE] @ v)\<close>
  have \<open>SchroederPHeight (u @ [STRANGE] @ v) = 0\<close> using AbstractPath_def SchroederPath_def SchroederPHeight_def
    by (metis (full_types) )
  then have  \<open>SchroederPHeight (u @ v) = 0\<close> using SchroederPathIsNotStrangePHeightZero 
    by blast
  from \<open>SchroederPath (u @ [STRANGE] @ v)\<close>
  have  \<open>\<forall> p :: SCHR list. prefix p (u @ [STRANGE] @ v) \<longrightarrow> SchroederPHeight p \<ge> 0\<close>
 using AbstractPath_def SchroederPath_def SchroederPHeight_def
  by (metis (full_types) )
  then have   \<open>\<forall> p :: SCHR list. prefix p (u @ v) \<longrightarrow> SchroederPHeight p \<ge> 0\<close>
    using SchroederPathIsNotStrangePHeightREC by blast
  show ?thesis using  \<open>SchroederPHeight (u @ v) = 0\<close>  \<open>\<forall> p :: SCHR list. prefix p (u @ v) \<longrightarrow> SchroederPHeight p \<ge> 0\<close>
  AbstractPath_def SchroederPath_def SchroederPHeight_def
    by (metis (full_types) )
qed

lemma SchroederStrangeRedPara_nRED:
  fixes v w :: \<open>SCHR list\<close> and n :: nat
  assumes \<open>STRANGEL v = Suc n\<close> and \<open>(SchroederToDyck v) = (SchroederToDyck w)\<close> and \<open>(SchroederPath w \<longrightarrow> SchroederPath v)\<close>
  shows   \<open>\<exists> v :: SCHR list. STRANGEL v =     n \<and> (SchroederToDyck v) = (SchroederToDyck w) \<and> (SchroederPath w \<longrightarrow> SchroederPath v)\<close>
proof-
  from \<open>STRANGEL v = Suc n\<close> have \<open>STRANGEL v \<noteq> 0\<close> 
    by linarith
  then obtain p q  where \<open>v = p @ [STRANGE] @ q\<close> 
    using PreSchroederStrangeRedPara_nRED by blast  
  obtain vv where \<open>vv = p @ q\<close> by blast
  have \<open>STRANGEL vv = n\<close> 
    using STRANGELAdd STRANGELCHAR \<open>v = p @ [STRANGE] @ q\<close> \<open>vv = p @ q\<close> assms(1) by auto
  from \<open>(SchroederToDyck v) = (SchroederToDyck w)\<close> 
    have \<open>(SchroederToDyck vv) = (SchroederToDyck w)\<close> 
      by (simp add: SchroederToDyckCode_def SchroederToDyckConcat \<open>v = p @ [STRANGE] @ q\<close> \<open>vv = p @ q\<close>)
  from \<open>(SchroederPath w \<longrightarrow> SchroederPath v)\<close>
    have \<open>(SchroederPath w \<longrightarrow> SchroederPath vv)\<close> 
      using SchroederPathIsNotStrange \<open>v = p @ [STRANGE] @ q\<close> \<open>vv = p @ q\<close> by blast
    show ?thesis 
      using \<open>STRANGEL vv = int n\<close> \<open>SchroederPath w \<longrightarrow> SchroederPath vv\<close> \<open>SchroederToDyck vv = SchroederToDyck w\<close> by blast
  qed

lemma SchroederStrangeRedPara_n:
  fixes w :: \<open>SCHR list\<close> and n :: nat
  shows   \<open>(\<exists> v :: SCHR list. STRANGEL v =  n \<and> (SchroederToDyck v) = (SchroederToDyck w) \<and> (SchroederPath w \<longrightarrow> SchroederPath v)) \<longrightarrow> (\<exists> v :: SCHR list. STRANGEL v = 0  \<and> (SchroederToDyck v) = (SchroederToDyck w) \<and> (SchroederPath w \<longrightarrow> SchroederPath v))\<close>
  proof(induction n)
case 0
then show ?case 
  by simp
next
  case (Suc n)
  then show ?case 
    using SchroederStrangeRedPara_nRED by blast
qed

lemma SchroederStrangeRed:
  fixes w :: \<open>SCHR list\<close>
  shows \<open>\<exists> v :: SCHR list. STRANGEL v = 0 \<and> (SchroederToDyck v) = (SchroederToDyck w) \<and> (SchroederPath w \<longrightarrow> SchroederPath v)\<close>
proof-
obtain n::nat where  \<open>STRANGEL w =  n\<close> 
  using STRANGELCHARGE0 zero_le_imp_eq_int by blast
  have  \<open>(SchroederToDyck w) = (SchroederToDyck w)\<close> by simp
  have \<open> (SchroederPath w \<longrightarrow> SchroederPath w)\<close> by blast
  then show ?thesis using SchroederStrangeRedPara_n 
    by (metis \<open>\<And>thesis. (\<And>n. STRANGEL w = int n \<Longrightarrow> thesis) \<Longrightarrow> thesis\<close>)
qed

lemma SchroederTransIntoDyck:
  fixes w :: \<open>SCHR list\<close>
  assumes \<open>SchroederPath w\<close>
  shows \<open>DyckPath (SchroederToDyck w)\<close>
proof-
  obtain v where \<open>STRANGEL v = 0\<close> and \<open>(SchroederToDyck v) = (SchroederToDyck w)\<close> and \<open>SchroederPath w \<longrightarrow> SchroederPath v\<close>
    using assms SchroederStrangeRed 
    by blast
  have \<open>DyckPath (SchroederToDyck v)\<close> 
    by (simp add: SchroederTransIntoDyckStranger0 \<open>STRANGEL v = 0\<close> \<open>SchroederPath w \<longrightarrow> SchroederPath v\<close> assms)
  then show ?thesis 
    by (simp add: \<open>SchroederToDyck v = SchroederToDyck w\<close>)
qed

lemma DyckArithmA :
  fixes n :: nat
  assumes \<open>n \<ge> 1\<close>
  shows \<open>\<exists> w :: DCHR list. n \<in> DyckClass w \<and> DyckPath w \<close>
  using SchroederArithmA SchroederTransIntoDyck assms 
  by (metis (mono_tags, lifting) DyckClass_def SchroederArithmL1 mem_Collect_eq)

section {* Dyck path uniqueness *}

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

proposition DyckUniq :
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

lemma prezDyckExistsS :
  fixes n :: nat
assumes \<open>n \<ge> 1\<close>
  shows \<open>\<exists>! w :: DCHR list.  n \<in> DyckClass w \<and> DyckPath w\<close>
  using assms DyckArithmA  DyckUniq 
  by blast

lemma zDyckExistsS :
  fixes n :: nat
  shows \<open>\<exists>! w :: DCHR list. (n = 0 \<longrightarrow> w = [])\<and>(n \<ge> 1 \<longrightarrow> n \<in> DyckClass w \<and> DyckPath w)\<close>
proof(cases \<open>n \<ge> 1\<close>)
  case True
  then show ?thesis 
    using prezDyckExistsS by auto
next
  case False
  then show ?thesis 
    by simp
qed

lemma zDyckExists :
 \<open>\<forall> n. \<exists>! w :: DCHR list. (n = 0 \<longrightarrow> w = [])\<and>(n \<ge> 1 \<longrightarrow> n \<in> DyckClass w \<and> DyckPath w)\<close>
  using zDyckExistsS by blast

lemma qDyckExists :
 \<open>\<exists> f :: nat \<Rightarrow> DCHR list.  (f 0 = [])\<and>(\<forall> n. n \<ge> 1 \<longrightarrow> n \<in> DyckClass (f n) \<and> DyckPath (f n))\<close>
  using zDyckExists by metis

lemma ADyckExistsUniqExt :
  fixes f g :: \<open>nat \<Rightarrow> DCHR list\<close> and n :: nat
  assumes \<open>f 0 = []\<close> and \<open> n \<ge> 1 \<longrightarrow> n \<in> DyckClass (f n) \<and> DyckPath (f n)\<close>
and \<open>g 0 = []\<close> and \<open> n \<ge> 1 \<longrightarrow> n \<in> DyckClass (g n) \<and> DyckPath (g n)\<close>
shows \<open>f n = g n\<close>
proof(cases \<open>n = 0\<close>)
  case True
  then show ?thesis 
    by (simp add: assms(1) assms(3))
next
  case False
  have \<open> n \<in> DyckClass (f n) \<and> DyckPath (f n) \<close> 
    using False assms(2) by linarith
  have \<open> n \<in> DyckClass (g n) \<and> DyckPath (g n)\<close> 
    using False assms(4) by linarith
  then show ?thesis 
    using DyckUniq \<open>n \<in> DyckClass (f n) \<and> DyckPath (f n)\<close> by blast
qed

lemma ADyckExistsUniq :
 \<open>\<forall> f g :: nat \<Rightarrow> DCHR list.  (f 0 = [])\<and>(\<forall> n. n \<ge> 1 \<longrightarrow> n \<in> DyckClass (f n) \<and> DyckPath (f n)) \<and> (g 0 = [])\<and>(\<forall> n. n \<ge> 1 \<longrightarrow> n \<in> DyckClass (g n) \<and> DyckPath (g n)) \<longrightarrow> f = g\<close>
  using ADyckExistsUniqExt ext by auto

section {* Main Result *}

theorem DyckExistsUniq :
 \<open>\<exists>! f :: nat \<Rightarrow> DCHR list.  (f 0 = [])\<and>(\<forall> n. n \<ge> 1 \<longrightarrow> n \<in> DyckClass (f n) \<and> DyckPath (f n))\<close>
  using qDyckExists ADyckExistsUniqExt ADyckExistsUniq 
  by auto 



end

(*
Title: Reduction from number theory to language theory
Author: Jose Manuel Rodriguez Caballero

We define a homomorphism ArithmFun from the Boolean algebra of
functions (DCHR list \<Rightarrow> bool) to the Boolean algebra of functions
(nat \<Rightarrow> bool).

(This code  was verified in Isabelle2018)
*)

theory fromNumberTheoryToLanguageTheory

imports Complex_Main DyckPathOfANumberExistenceUniq

begin

text {* ArithmFun transforms a language theoretic function into an arithmetical function *}

definition ArithmFun :: \<open>(DCHR list \<Rightarrow> 'a) \<Rightarrow> (nat \<Rightarrow> 'a)\<close> where
\<open>ArithmFun \<equiv> \<lambda> g. (g \<circ> DyckType)\<close>

section {* Pointwise Boolean operations *}


subsection {* AND *}
definition AND_op :: \<open>('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> bool)\<close> where
\<open>AND_op \<equiv> \<lambda> f g. (\<lambda> x. (f x)\<and>(g x))\<close> 

abbreviation AND_abb :: \<open>('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> bool)\<close>
(infixr "AND" 65)
where
\<open>f AND g \<equiv> AND_op f g\<close>

lemma ANDQ : 
  shows  \<open>\<forall> x. (f AND g) x \<longleftrightarrow> f x \<and> g x\<close>
  by (simp add: AND_op_def)

lemma AND_funt_ext: \<open>\<forall>x. ((f \<circ> h) AND (g \<circ> h)) x = ((f AND g) \<circ> h) x\<close>
  by (simp add: ANDQ)

lemma AND_funt: \<open>(f \<circ> h) AND (g \<circ> h) = (f AND g) \<circ> h\<close>
  by (simp add: AND_funt_ext ext)

proposition RepFunAND : 
 \<open>ArithmFun (F AND G) = (ArithmFun F) AND (ArithmFun G) \<close>
  by (simp add: AND_funt ArithmFun_def)


subsection {* OR *}

definition OR_op :: \<open>('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> bool)\<close> where
\<open>OR_op \<equiv> \<lambda> f g. (\<lambda> x. (f x)\<or>(g x))\<close>

abbreviation OR_abb :: \<open>('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> bool)\<close>
(infixr "OR" 65)
where
\<open>f OR g \<equiv> OR_op f g\<close>


lemma ORQ : 
  shows  \<open>\<forall> x. (f OR g) x \<longleftrightarrow> f x \<or> g x\<close>
  by (simp add: OR_op_def)

lemma OR_funt_ext: \<open>\<forall>x. ((f \<circ> h) OR (g \<circ> h)) x = ((f OR g) \<circ> h) x\<close>
  by (simp add: ORQ)

lemma OR_funt: \<open>(f \<circ> h) OR (g \<circ> h) = (f OR g) \<circ> h\<close>
  by (simp add: OR_funt_ext ext)

proposition RepFunOR : 
 \<open>ArithmFun (F OR G) = (ArithmFun F) OR (ArithmFun G) \<close>
  by (simp add: ArithmFun_def OR_funt)

subsection {* NOT *}

definition NOT :: \<open>('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> bool)\<close> where
\<open>NOT \<equiv> \<lambda> f. (\<lambda> x. \<not>(f x))\<close>


lemma NOTQ : 
shows  \<open>\<forall> x. (NOT f) x \<longleftrightarrow> \<not> (f x)\<close>
  by (simp add: NOT_def)

lemma NOT_funt_ext: \<open>\<forall>x. ((NOT f) \<circ> h) x =  (NOT (f \<circ> h)) x\<close>
  by (simp add: NOTQ)

lemma NOT_funt: \<open>(NOT f) \<circ> h  = NOT (f \<circ> h)\<close>
  using NOT_funt_ext ext by fastforce

proposition RepFunNOT : 
 \<open>ArithmFun (NOT F) = NOT (ArithmFun F) \<close>
  by (simp add: ArithmFun_def NOT_funt)


end
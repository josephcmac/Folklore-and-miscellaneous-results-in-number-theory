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

section {* Equality *}

text {* Equality ignoring the value of the functions at zero *}
abbreviation eqSuc_abb :: \<open>(nat \<Rightarrow> 'a) \<Rightarrow> (nat \<Rightarrow> 'a) \<Rightarrow> bool\<close>
  (infixr "\<doteq>" 65)
  where
    \<open>f \<doteq> g \<equiv>  f \<circ> Suc = g \<circ> Suc\<close>

section {* DyckType *}

definition DyckType :: \<open>nat \<Rightarrow> DCHR list\<close> where
  \<open>DyckType \<equiv> (SOME f :: nat \<Rightarrow> DCHR list. ((f 0 = [])\<and>(\<forall> n. n \<ge> 1 \<longrightarrow> n \<in> DyckClass (f n) \<and> DyckPath (f n)) ))\<close>

proposition DyckType0: \<open>(DyckType 0 = [])\<close>
  by (smt qDyckExists DyckType_def someI_ex)

proposition DyckType1: \<open>n \<ge> 1 \<Longrightarrow>  n \<in> DyckClass (DyckType n)\<close>
  by (smt qDyckExists DyckType_def someI_ex)

proposition DyckType2: \<open>n \<ge> 1 \<Longrightarrow>  DyckPath (DyckType n)\<close>
  by (smt qDyckExists DyckType_def someI_ex)

proposition DyckType3: \<open>n \<ge> 1 \<Longrightarrow>  n \<in> DyckClass w  \<Longrightarrow> w = DyckType n\<close>
  using DyckType1 DyckUniq by blast

proposition DyckType4: \<open>n \<ge> 1 \<Longrightarrow>  DyckType n \<noteq> []\<close>
proof-
  assume \<open>n \<ge> 1\<close>
  obtain w where \<open>n \<in> DyckClass w\<close> 
    using DyckType1 \<open>1 \<le> n\<close> by blast
  from  \<open>n \<in> DyckClass w\<close> obtain v where \<open>WordToFun v = Jsigns n\<close> and \<open>SchroederToDyck v = w\<close>
    by (smt CollectD DyckClass_def)
  from \<open>n \<ge> 1\<close> have \<open>(Jsigns n) 0 = 1\<close> 
    by (metis Jdvd_def add.right_neutral dvd_0_right even_Suc preJsignsSumToDiffCardPlus times_nat.simps(1) times_nat.simps(2))
  from  \<open>WordToFun v = Jsigns n\<close>  \<open>(Jsigns n) 0 = 1\<close>  have \<open>v ! 0 = UP\<close> 
    by (smt SchroederCode_def WordToFun_def)
  from  \<open>v ! 0 = UP\<close>  \<open>SchroederToDyck v = w\<close> have \<open>w ! 0 = up\<close>
    by (metis Groups.add_ac(2) One_nat_def SchroederToDyck.elims SchroederToDyckCode_def WordToFun_def \<open>Jsigns n 0 = 1\<close> \<open>WordToFun v = Jsigns n\<close> less_numeral_extra(1) less_numeral_extra(3) list.size(3) list.size(4) nth_Cons_0 nth_append plus_1_eq_Suc)
  show ?thesis 
    by (metis (no_types, hide_lams) DyckType3 Nil_is_append_conv SchroederToDyck.elims SchroederToDyckCode_def WordToFun_def \<open>1 \<le> n\<close> \<open>Jsigns n 0 = 1\<close> \<open>SchroederToDyck v = w\<close> \<open>WordToFun v = Jsigns n\<close> \<open>n \<in> DyckClass w\<close> \<open>v ! 0 = UP\<close>  list.discI  list.size(3) nth_Cons_0 rel_simps(93) zero_order(3))
qed

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

proposition RepFunANDdot : 
  \<open>ArithmFun (F AND G) \<doteq> (ArithmFun F) AND (ArithmFun G) \<close>
  using RepFunAND by auto


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

proposition RepFunORdot : 
  \<open>ArithmFun (F OR G) \<doteq> (ArithmFun F) OR (ArithmFun G) \<close>
  by (simp add: RepFunOR)

subsection {* NOT *}

definition NOT :: \<open>('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> bool)\<close> where
  \<open>NOT \<equiv> \<lambda> f. (\<lambda> x. \<not>(f x))\<close>


lemma NOTQ : 
  shows  \<open>\<forall> x. (NOT f) x \<longleftrightarrow> \<not> (f x)\<close>
  by (simp add: NOT_def)

lemma NOT_funt_ext: \<open>\<forall>x. ((NOT f) \<circ> h) x =  (NOT (f \<circ> h)) x\<close>
  by (simp add: NOTQ)

lemma NOT_funt: \<open>(NOT f) \<circ> h = NOT (f \<circ> h)\<close>
  using NOT_funt_ext ext by fastforce

proposition RepFunNOT : 
  \<open>ArithmFun (NOT F) = NOT (ArithmFun F) \<close>
  by (simp add: ArithmFun_def NOT_funt)

proposition RepFunNOTdot : 
  \<open>ArithmFun (NOT F) \<doteq> NOT (ArithmFun F) \<close>
  using RepFunNOT by auto

section {* Split *}

text {* We assume that both the empty word and the number zero 
does not satisfy the properties *}

proposition DyckTypeToArithmFun:
  fixes f :: \<open>nat \<Rightarrow> bool\<close> and g :: \<open>DCHR list \<Rightarrow> bool\<close>
  assumes  \<open>\<forall> n. n \<ge> 1 \<longrightarrow> ((g (DyckType n) \<longrightarrow> f n))\<close> and  \<open>\<forall> n. n \<ge> 1 \<longrightarrow> (f n \<longrightarrow> g (DyckType n))\<close>
  shows \<open>(ArithmFun g) \<doteq> f \<close>
proof-
  from \<open>\<forall> n. n \<ge> 1 \<longrightarrow> (g (DyckType n) \<longrightarrow> f n)\<close> 
  have \<open>\<forall> n. n \<ge> 1 \<longrightarrow>((ArithmFun g) n \<longrightarrow> f n)\<close> 
    by (simp add: ArithmFun_def)
  from \<open>\<forall> n. n \<ge> 1 \<longrightarrow> (g (DyckType n) \<longrightarrow> f n)\<close> 
  have  \<open>\<forall> n. n \<ge> 1 \<longrightarrow> (f n \<longrightarrow> (ArithmFun g) n )\<close> 
    by (metis ArithmFun_def assms(2) o_apply)
  have \<open>\<forall> n. n \<ge> 1 \<longrightarrow>((ArithmFun g) n \<longleftrightarrow> f n)\<close>
    using \<open>\<forall>n\<ge>1. ArithmFun g n \<longrightarrow> f n\<close> \<open>\<forall>n\<ge>1. f n \<longrightarrow> ArithmFun g n\<close> by blast
  then show ?thesis using ext by auto
qed


corollary DyckTypeToArithmFunB:
  fixes f :: \<open>nat \<Rightarrow> bool\<close> and g :: \<open>DCHR list \<Rightarrow> bool\<close>
  assumes  \<open>\<forall> n. n \<ge> 1 \<longrightarrow> ((g (DyckType n) \<longleftrightarrow> f n))\<close>
  shows \<open>(ArithmFun g) \<doteq> f \<close>
  by (simp add: DyckTypeToArithmFun assms)

proposition DyckTypeToArithmFunC:
  fixes f :: \<open>nat \<Rightarrow> 'a\<close> and g :: \<open>DCHR list \<Rightarrow> 'a\<close>
  assumes  \<open>\<forall> n. n \<ge> 1 \<longrightarrow> ((g (DyckType n) = f n))\<close>
  shows \<open>(ArithmFun g) \<doteq> f \<close>
proof-
  from  \<open>\<forall> n. n \<ge> 1 \<longrightarrow> ((g (DyckType n) = f n))\<close>
  have \<open>\<forall> n.((g (DyckType (Suc n)) = f (Suc n)))\<close>
    by simp
  then have \<open>g \<circ> DyckType \<circ> Suc = f \<circ> Suc \<close> 
    by auto
  then show ?thesis 
    by (simp add: ArithmFun_def)
qed

end
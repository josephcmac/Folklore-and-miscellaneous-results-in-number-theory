(*
Title: Reduction from number theory to language theory
Author: Jose Manuel Rodriguez Caballero

(This code  was verified in Isabelle2018)
*)

theory fromNumberTheoryToLanguageTheory

imports Complex_Main DyckPathOfANumberExistenceUniq

begin

definition RepFun :: \<open>(nat \<Rightarrow> 'a) \<Rightarrow> (DCHR list \<Rightarrow> 'a) \<Rightarrow> bool\<close> where
\<open>RepFun \<equiv> \<lambda> f. \<lambda> g. (f = g \<circ> DyckType)\<close>

definition AND_op :: \<open>('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> bool)\<close> where
\<open>AND_op \<equiv> \<lambda> f g. (\<lambda> x. (f x)\<and>(g x))\<close> 

abbreviation AND_abb :: \<open>('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> bool)\<close>
(infixr "AND" 65)
where
\<open>f AND g \<equiv> AND_op f g\<close>

definition OR_op :: \<open>('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> bool)\<close> where
\<open>OR_op \<equiv> \<lambda> f g. (\<lambda> x. (f x)\<or>(g x))\<close>

abbreviation OR_abb :: \<open>('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> bool)\<close>
(infixr "OR" 65)
where
\<open>f OR g \<equiv> OR_op f g\<close>


definition NOT :: \<open>('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> bool)\<close> where
\<open>NOT \<equiv> \<lambda> f. (\<lambda> x. \<not>(f x))\<close>


lemma RepFunInj : \<open>RepFun f h \<Longrightarrow> RepFun g h \<Longrightarrow>  f = g\<close>
  by (simp add: RepFun_def)

lemma ANDQ : 
  shows  \<open>\<forall> x. (f AND g) x \<longleftrightarrow> f x \<and> g x\<close>
  by (simp add: AND_op_def)

lemma AND_funt_ext: \<open>\<forall>x. ((f \<circ> h) AND (g \<circ> h)) x = ((f AND g) \<circ> h) x\<close>
  by (simp add: ANDQ)

lemma AND_funt: \<open>(f \<circ> h) AND (g \<circ> h) = (f AND g) \<circ> h\<close>
  by (simp add: AND_funt_ext ext)

proposition RepFunAND : 
 \<open>RepFun f F \<Longrightarrow> RepFun g G \<Longrightarrow> RepFun (f AND g) (F AND G)\<close>
proof-
  assume \<open>RepFun f F\<close>
  assume \<open>RepFun g G\<close>
  from \<open>RepFun f F\<close> have \<open>f = F \<circ> DyckType\<close> 
    by (simp add: RepFun_def)
  from \<open>RepFun g G\<close> have \<open>g = G \<circ> DyckType\<close> 
    by (simp add: RepFun_def)
  from  \<open>f = F \<circ> DyckType\<close> \<open>g = G \<circ> DyckType\<close> 
  have \<open>f AND g = (F \<circ> DyckType) AND (G \<circ> DyckType)\<close>
    by blast
  then  have \<open>f AND g =  ((F AND G) \<circ> DyckType)\<close>
    using AND_funt by auto
  then show ?thesis 
    by (simp add: RepFun_def)
qed

lemma ORQ : 
  shows  \<open>\<forall> x. (f OR g) x \<longleftrightarrow> f x \<or> g x\<close>
  by (simp add: OR_op_def)

lemma OR_funt_ext: \<open>\<forall>x. ((f \<circ> h) OR (g \<circ> h)) x = ((f OR g) \<circ> h) x\<close>
  by (simp add: ORQ)

lemma OR_funt: \<open>(f \<circ> h) OR (g \<circ> h) = (f OR g) \<circ> h\<close>
  by (simp add: OR_funt_ext ext)

proposition RepFunOR : 
 \<open>RepFun f F \<Longrightarrow> RepFun g G \<Longrightarrow> RepFun (f OR g) (F OR G)\<close>
proof-
  assume \<open>RepFun f F\<close>
  assume \<open>RepFun g G\<close>
  from \<open>RepFun f F\<close> have \<open>f = F \<circ> DyckType\<close> 
    by (simp add: RepFun_def)
  from \<open>RepFun g G\<close> have \<open>g = G \<circ> DyckType\<close> 
    by (simp add: RepFun_def)
  from  \<open>f = F \<circ> DyckType\<close> \<open>g = G \<circ> DyckType\<close> 
  have \<open>f OR g = (F \<circ> DyckType) OR (G \<circ> DyckType)\<close>
    by blast
  then  have \<open>f OR g =  ((F OR G) \<circ> DyckType)\<close>
    using OR_funt by auto
  then show ?thesis 
    by (simp add: RepFun_def)
qed


lemma NOTQ : 
shows  \<open>\<forall> x. (NOT f) x \<longleftrightarrow> \<not> (f x)\<close>
  by (simp add: NOT_def)

lemma NOT_funt_ext: \<open>\<forall>x. ((NOT f) \<circ> h) x =  (NOT (f \<circ> h)) x\<close>
  by (simp add: NOTQ)

lemma NOT_funt: \<open>(NOT f) \<circ> h  = NOT (f \<circ> h)\<close>
  using NOT_funt_ext ext by fastforce

proposition RepFunNOT : 
 \<open>RepFun f F \<Longrightarrow> RepFun (NOT f) (NOT F)\<close>
proof-
  assume \<open>RepFun f F\<close>
  from \<open>RepFun f F\<close> have \<open>f = F \<circ> DyckType\<close> 
    by (simp add: RepFun_def)
  then have \<open>NOT f  = (NOT F) \<circ> DyckType\<close>
    by (simp add: NOT_funt)
  then show ?thesis 
    by (simp add: RepFun_def)
qed

end
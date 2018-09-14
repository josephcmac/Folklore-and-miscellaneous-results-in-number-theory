(*
Title: Definitions concerning abstract paths
Author: Jose Manuel Rodriguez Caballero


(This code  was verified in Isabelle2018)
*)

theory AbstractPathsDef

imports Complex_Main

begin
text {* The property P(n) holds for all n large enough *}
definition LARGE :: \<open>(nat \<Rightarrow> bool) \<Rightarrow> bool \<close> where
\<open>LARGE \<equiv> \<lambda> P. (\<exists> K. \<forall> k. k \<ge> K \<longrightarrow> P k)\<close>

text {* Polynomial function *}
definition PolyFun :: \<open>(nat \<Rightarrow> int) \<Rightarrow> bool\<close> where 
\<open>PolyFun \<equiv> \<lambda> f. LARGE (\<lambda> n. f n = 0)\<close>


definition prefix :: \<open>'a list \<Rightarrow> 'a list \<Rightarrow> bool\<close> where
\<open>prefix \<equiv> \<lambda> v w. ( (length v \<le> length w)
 \<and> (\<forall> j. j < length v \<longrightarrow>  v ! j =  w ! j ) )\<close>

fun HeightLetterwise :: \<open>('a \<Rightarrow> int) \<Rightarrow> ('a list \<Rightarrow> int)\<close> where
  \<open>HeightLetterwise h []  = 0\<close>
|  \<open> HeightLetterwise h (a # x) = (HeightLetterwise h x) + (h a) \<close>

definition AbstractPath :: \<open>('a list \<Rightarrow> int) \<Rightarrow> ('a list \<Rightarrow>  bool)\<close> where
  \<open>AbstractPath \<equiv> \<lambda> h.  \<lambda> w.
(\<forall> v :: 'a list.  prefix v w \<longrightarrow>  h v \<ge> 0 ) 
\<and> ( h w = 0)\<close>


end 
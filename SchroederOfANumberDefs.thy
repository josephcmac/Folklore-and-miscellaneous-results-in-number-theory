(*
Title: Definitions concerning Schroeder paths and number theory
Author: Jose Manuel Rodriguez Caballero


(This code  was verified in Isabelle2018)
*)

theory SchroederOfANumberDefs

imports Complex_Main 

begin


datatype SCHR = UP | DOWN | STRANGE 

text {* The property P(n) holds for all n large enough *}
definition LARGE :: \<open>(nat \<Rightarrow> bool) \<Rightarrow> bool \<close> where
\<open>LARGE \<equiv> \<lambda> P. (\<exists> K. \<forall> k. k \<ge> K \<longrightarrow> P k)\<close>

text {* Polynomial function *}
definition PolyFun :: \<open>(nat \<Rightarrow> int) \<Rightarrow> bool\<close> where 
\<open>PolyFun \<equiv> \<lambda> f. LARGE (\<lambda> n. f n = 0)\<close>

text {* 3-letter word  *}
definition ThreeWord :: \<open>(nat \<Rightarrow> int) \<Rightarrow> bool\<close> where 
\<open>ThreeWord \<equiv> \<lambda> f. (\<forall> n. f n \<in> {-1, 0, 1}) \<and> PolyFun f\<close>

text {* Schroeder's code in symbols UP, DOWN, STRANGE *}
definition SchroederCode :: \<open>SCHR \<Rightarrow> int\<close> where
\<open>SchroederCode \<equiv> \<lambda> c::SCHR. (if c = UP then (1::int) else 
(if c = DOWN then (-1::int) else (0::int) ) )\<close>

definition WordToFun :: \<open>(SCHR list) \<Rightarrow> (nat \<Rightarrow> int)\<close> where
\<open>WordToFun \<equiv> \<lambda> w::(SCHR list). (\<lambda> n::nat. (if n < (length w) then SchroederCode ((!) w n) else 0))\<close>


fun SchroederHeight :: \<open>(SCHR list) \<Rightarrow> int\<close> where
  \<open>SchroederHeight ('''') = 0\<close>
|  \<open> SchroederHeight (STRANGE # x) = (SchroederHeight x) \<close>
|  \<open> SchroederHeight (UP # x) = (SchroederHeight x)+1 \<close>
|  \<open> SchroederHeight (DOWN # x) = (SchroederHeight x)-1 \<close>

definition prefix :: \<open>SCHR list \<Rightarrow> SCHR list \<Rightarrow> bool\<close> where
\<open>prefix \<equiv> \<lambda> v w. ( (length v \<le> length w)
 \<and> (\<forall> j. j < length v \<longrightarrow> (!) v j = (!) w j ) )\<close>

definition SchroederPath :: \<open>(SCHR list) \<Rightarrow> bool\<close> where
  \<open>SchroederPath \<equiv> \<lambda> w. 
(\<forall> v :: SCHR list.  prefix v w \<longrightarrow> SchroederHeight v \<ge> 0 ) 
\<and> (SchroederHeight w = 0)\<close>

text {* Jordan's divisors of n *}
definition Jdvd :: \<open>nat \<Rightarrow> nat \<Rightarrow> bool\<close> where
\<open>Jdvd \<equiv> \<lambda> d n. (\<exists> k :: nat. d*k = 2*n \<and> ((odd d)\<or>(odd k)))\<close>

text {* Jordan's sequence of signs of n *}
definition Jsigns :: \<open>nat \<Rightarrow> (nat \<Rightarrow> int)\<close> where
\<open>Jsigns \<equiv> \<lambda> n. ( \<lambda> d. (if Jdvd (Suc d) n then 
  (if odd (Suc d) then 1 else -1) 
else 0 ) )\<close>

text {* Schroeder class of n *}
definition  SchroederClass :: \<open> SCHR list \<Rightarrow> nat set\<close> where
\<open>SchroederClass \<equiv> \<lambda> w. {n | n :: nat. n \<ge> 1 \<and> WordToFun w = Jsigns n} \<close>


end
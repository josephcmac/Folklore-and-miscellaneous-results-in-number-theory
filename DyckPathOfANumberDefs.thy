(*
Title: Definitions concerning the Dyck path approach to number theory
Author: Jose Manuel Rodriguez Caballero

(This code  was verified in Isabelle2018)
*)

theory DyckPathOfANumberDefs

imports Complex_Main 

begin

section {* Large numbers *}
text {* The property P(n) holds for all n large enough *}
definition LARGE :: \<open>(nat \<Rightarrow> bool) \<Rightarrow> bool \<close> where
\<open>LARGE \<equiv> \<lambda> P. (\<exists> K. \<forall> k. k \<ge> K \<longrightarrow> P k)\<close>

text {* Polynomial function *}
definition PolyFun :: \<open>(nat \<Rightarrow> int) \<Rightarrow> bool\<close> where 
\<open>PolyFun \<equiv> \<lambda> f. LARGE (\<lambda> n. f n = 0)\<close>

section {* Abstract Paths *}

definition prefix :: \<open>'a list \<Rightarrow> 'a list \<Rightarrow> bool\<close> where
\<open>prefix \<equiv> \<lambda> v w. ( (length v \<le> length w)
 \<and> (\<forall> j. j < length v \<longrightarrow>  v ! j =  w ! j ) )\<close>

fun PHeightLetterwise :: \<open>('a \<Rightarrow> int) \<Rightarrow> ('a list \<Rightarrow> int)\<close> where
  \<open>PHeightLetterwise h [] = 0\<close>
|  \<open> PHeightLetterwise h (a # x) = (PHeightLetterwise h x) + (h a) \<close>

definition AbstractPath :: \<open>('a list \<Rightarrow> int) \<Rightarrow> ('a list \<Rightarrow>  bool)\<close> where
  \<open>AbstractPath \<equiv> \<lambda> h.  \<lambda> w.
(\<forall> v :: 'a list.  prefix v w \<longrightarrow>  h v \<ge> 0 ) 
\<and> ( h w = 0)\<close>

section {* Schroeder Paths *}

datatype SCHR = UP | DOWN | STRANGE 

fun SchroederPHeightLetter ::\<open>SCHR \<Rightarrow> int\<close> where 
\<open>SchroederPHeightLetter UP = 1\<close>
| \<open>SchroederPHeightLetter DOWN = -1\<close>
| \<open>SchroederPHeightLetter STRANGE = 0\<close>

definition SchroederPHeight :: \<open>(SCHR list) \<Rightarrow> int\<close> where
\<open> SchroederPHeight \<equiv> (PHeightLetterwise SchroederPHeightLetter)  \<close>

definition SchroederPath :: \<open>(SCHR list) \<Rightarrow> bool\<close> where
  \<open>SchroederPath \<equiv> AbstractPath SchroederPHeight \<close>

text {* 3-letter word  *}
definition ThreeWord :: \<open>(nat \<Rightarrow> int) \<Rightarrow> bool\<close> where 
\<open>ThreeWord \<equiv> \<lambda> f. (\<forall> n. f n \<in> {-1, 0, 1}) \<and> PolyFun f\<close>

text {* Schroeder's code in symbols UP, DOWN, STRANGE *}
definition SchroederCode :: \<open>SCHR \<Rightarrow> int\<close> where
\<open>SchroederCode \<equiv> \<lambda> c::SCHR. (if c = UP then (1::int) else 
(if c = DOWN then (-1::int) else (0::int) ) )\<close>

definition WordToFun :: \<open>(SCHR list) \<Rightarrow> (nat \<Rightarrow> int)\<close> where
\<open>WordToFun \<equiv> \<lambda> w::(SCHR list). (\<lambda> n::nat. (if n < (length w) then SchroederCode ( w ! n) else 0))\<close>

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

section {* Dyck Paths *}

datatype DCHR = up | down

fun DyckPHeightLetter ::\<open>DCHR \<Rightarrow> int\<close> where 
\<open>DyckPHeightLetter up = 1\<close>
| \<open>DyckPHeightLetter down = -1\<close>

definition DyckPHeight :: \<open>(DCHR list) \<Rightarrow> int\<close> where
\<open> DyckPHeight \<equiv> (PHeightLetterwise DyckPHeightLetter)  \<close>

definition DyckPath :: \<open>(DCHR list) \<Rightarrow> bool\<close> where
  \<open>DyckPath \<equiv> AbstractPath DyckPHeight \<close>

definition DyckToSchroederCode :: \<open>DCHR \<Rightarrow> SCHR\<close> where
\<open>DyckToSchroederCode \<equiv> \<lambda> c. (if c = up then  UP
 else DOWN )\<close>

fun DyckToSchroeder :: \<open>DCHR list \<Rightarrow> SCHR list\<close> where
 \<open>DyckToSchroeder [] = []\<close>
| \<open>DyckToSchroeder (a # x) = (DyckToSchroederCode a) # (DyckToSchroeder x)\<close>

definition SchroederToDyckCode :: \<open>SCHR \<Rightarrow> DCHR list\<close> where
\<open>SchroederToDyckCode \<equiv> \<lambda> c. (if c = UP then  [up]
 else (if c = DOWN then [down] else []) )\<close>

fun SchroederToDyck :: \<open>SCHR list \<Rightarrow> DCHR list\<close> where 
 \<open>SchroederToDyck [] = []\<close>
| \<open>SchroederToDyck (a # x) =  (SchroederToDyckCode a) @ (SchroederToDyck x)\<close>

text {* Dyck class of n *}
definition  DyckClass :: \<open> DCHR list \<Rightarrow> nat set\<close> where
\<open>DyckClass \<equiv> \<lambda> w. {n | n :: nat. n \<ge> 1 \<and> (\<exists> v::SCHR list. SchroederToDyck v = w \<and> WordToFun v = Jsigns n)} \<close>

end

(*
Title: Definitions concerning Dyck paths and number theory
Author: Jose Manuel Rodriguez Caballero


(This code  was verified in Isabelle2018)
*)

theory DyckPathOfANumberDefs

imports Complex_Main SchroederOfANumberDefs

begin

datatype DCHR = up | down

fun DyckHeightLetter ::\<open>DCHR \<Rightarrow> int\<close> where 
\<open>DyckHeightLetter up = 1\<close>
| \<open>DyckHeightLetter down = -1\<close>

definition DyckHeight :: \<open>(DCHR list) \<Rightarrow> int\<close> where
\<open> DyckHeight \<equiv> (HeightLetterwise DyckHeightLetter)  \<close>

definition DyckPath :: \<open>(DCHR list) \<Rightarrow> bool\<close> where
  \<open>DyckPath \<equiv> AbstractPath DyckHeight \<close>




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

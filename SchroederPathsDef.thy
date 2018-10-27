(*
Title: Definition of Schroeder Paths
Author: Jose Manuel Rodriguez Caballero

We define the Schroeder paths.


(This code  was verified in Isabelle2018)
*)

theory SchroederPathsDef

imports Complex_Main DyckPathsDef 

begin

fun SchroederLetters  :: \<open>int list \<Rightarrow> bool\<close> where
  \<open>SchroederLetters [] = True\<close>|
  \<open>SchroederLetters (x#w) = (if x = -1 \<or> x = 1 \<or> x = 0 then SchroederLetters w else False)\<close>

fun SchroederPath :: \<open>int list \<Rightarrow> bool\<close> where
  \<open>SchroederPath w = (NonNegPath w  \<and> SchroederLetters w \<and> (w \<noteq> [] \<longrightarrow> last (HeightList w) = 0))\<close>


end

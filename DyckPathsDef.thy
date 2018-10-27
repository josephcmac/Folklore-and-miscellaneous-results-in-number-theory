(*
Title: Definition of Dyck Paths
Author: Jose Manuel Rodriguez Caballero

We define the Dyck paths.


(This code  was verified in Isabelle2018)
*)

theory DyckPathsDef

imports Complex_Main

begin

fun DyckLetters  :: \<open>int list \<Rightarrow> bool\<close> where
  \<open>DyckLetters [] = True\<close>|
  \<open>DyckLetters (x#w) = (if x = -1 \<or> x = 1 then DyckLetters w else False)\<close>

fun NonNeg  :: \<open>int list \<Rightarrow> bool\<close> where
  \<open>NonNeg [] = True\<close>|
  \<open>NonNeg (x#w) = (if x \<ge> 0 then NonNeg w else False)\<close>

fun HeightList :: \<open>int list \<Rightarrow> int list\<close> where
  \<open>HeightList [] = []\<close>  |
  \<open>HeightList [x] = [x]\<close> | 
  \<open>HeightList (x#y#w) = x#(HeightList ((x+y)#w))\<close>


fun NonNegPath :: \<open>int list \<Rightarrow> bool\<close> where
  \<open>NonNegPath w =  NonNeg (HeightList w) \<close>

fun DyckPath :: \<open>int list \<Rightarrow> bool\<close> where
  \<open>DyckPath w = (NonNegPath w \<and> DyckLetters w \<and> (w \<noteq> [] \<longrightarrow> last (HeightList w) = 0))\<close>

end

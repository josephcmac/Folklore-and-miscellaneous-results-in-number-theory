(*
Title: Constructive definition of the Dyck type of a number
Author: Jose Manuel Rodriguez Caballero

We define Dyck n to be the Dyck type of n.

References

@inproceedings{caballero2017symmetric,
  title={Symmetric Dyck Paths and Hooley’s $$$\backslash$varDelta $$ $\Delta$-Function},
  author={Caballero, Jos{\'e} Manuel Rodr{\'\i}guez},
  booktitle={International Conference on Combinatorics on Words},
  pages={252--261},
  year={2017},
  organization={Springer}
}

(This code  was verified in Isabelle2018)
*)

theory DyckTypeConstrDef

imports 
  Complex_Main 

begin

fun SchroederCHR :: \<open>nat \<Rightarrow> nat \<Rightarrow> int\<close> where
  \<open>SchroederCHR n k = 
      (if k dvd (2*n) \<and> (odd k) then 1 
 else (if k dvd (2*n) \<and> odd ((2*n)div k) then -1 
else 0 ))\<close>

fun preSchroeder :: \<open>nat \<Rightarrow> nat \<Rightarrow> int list\<close> where
  \<open>preSchroeder n 0 = []\<close> |
  \<open>preSchroeder n (Suc k) = (preSchroeder n k) @ [SchroederCHR n (Suc k)]\<close> 

fun Schroeder :: \<open>nat  \<Rightarrow> int list\<close> where
  \<open>Schroeder n = preSchroeder n (2*n)\<close> 


text {* Dyck n is the Dyck type of n *}
fun Dyck :: \<open>nat  \<Rightarrow> int list\<close> where
  \<open>Dyck n = removeAll 0 (Schroeder n)\<close> 


end

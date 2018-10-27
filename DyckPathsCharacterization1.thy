(*
Title: Characterization of Dyck Paths (Part 1)
Author: Jose Manuel Rodriguez Caballero


We prove that DyckPath (defined in DyckPathsDef) satisfies the following properties.

proposition DyckA: \<open>DyckPath [] = True\<close>

proposition DyckB: \<open>DyckPath w \<Longrightarrow> DyckPath ([1] @ w @ [-1])\<close>

proposition DyckC: \<open>DyckPath v \<Longrightarrow> DyckPath w \<Longrightarrow> DyckPath (v @ w)\<close>



(This code  was verified in Isabelle2018)
*)

theory DyckPathsCharacterization1

imports Complex_Main DyckPathsDef

begin

section {* Proposition DyckA *}

proposition DyckA: \<open>DyckPath [] = True\<close>
  by simp

section {* Proposition DyckB *}

lemma DyckBDyckLetters: \<open>DyckLetters w \<Longrightarrow> DyckLetters ([1] @ w @ [-1])\<close>
proof(induction w)
  case Nil
  then show ?case 
    by simp
next
  case (Cons a w)
  then show ?case 
    by (metis DyckLetters.simps(2) append.left_neutral append_Cons)
qed

fun incr :: \<open>int list \<Rightarrow> int \<Rightarrow> int list\<close> where
  \<open>incr [] c = []\<close> |
  \<open>incr (x#w) c = (x+c)#(incr w c)\<close>

lemma CocatIncr: \<open> incr (v @ w) c = (incr v c) @ (incr w c)\<close> 
proof(induction v)
  case Nil
  then show ?case 
    by simp
next
  case (Cons a v)
  then show ?case 
    by simp
qed

lemma IteractionIncr: \<open> incr (incr w c) d = incr w (c+d) \<close> 
proof(induction w)
  case Nil
  then show ?case 
    by simp
next
  case (Cons a w)
  then show ?case 
    by simp
qed

lemma ConcatHeightSumUS1:
  assumes \<open>w \<noteq> [] \<longrightarrow> (\<forall> x. x + last (HeightList w) = last (HeightList (x#w)) )\<close>
  shows \<open>x + last (HeightList (y#w)) = last (HeightList (x#(y#w)))\<close>
proof(cases \<open>w = []\<close>)
  case True
  then show ?thesis 
    by simp
next
  case False
  then have \<open>w \<noteq> []\<close> by blast
  then have \<open>y + last (HeightList w) = last (HeightList (y#w))\<close>
    by (simp add: assms)
  then have \<open>x + y + last (HeightList w) = x + last (HeightList (y#w))\<close>
    by simp
  then have \<open>(x + y) + last (HeightList w) = x + last (HeightList (y#w))\<close>
    by simp
  then have \<open>last (HeightList ( (x + y) # w) ) = x + last (HeightList (y#w))\<close>
    by (simp add: False assms)
  then show ?thesis 
    using HeightList.elims by auto
qed

lemma ConcatHeightSumUS: \<open>w \<noteq> [] \<Longrightarrow> (\<forall> x. x + last (HeightList w) = last (HeightList (x#w)) )\<close>
proof(induction w)
  case Nil
  then show ?case 
    by simp
next
  case (Cons a w)
  then show ?case using ConcatHeightSumUS1 by blast
qed


lemma ConcatHeightSumU: \<open>w \<noteq> [] \<Longrightarrow> (\<forall> x. last (HeightList [x]) + last (HeightList w) = last (HeightList ([x]@w)) )\<close>
  using ConcatHeightSumUS by auto

lemma ConcatHeightSumQRec: 
  assumes \<open> \<forall> w. v \<noteq> [] \<and> w \<noteq> [] \<longrightarrow> last (HeightList v) + last (HeightList w) = last (HeightList (v@w)) \<close> 
    and \<open>w \<noteq> []\<close>
  shows \<open>last (HeightList (x#v)) + last (HeightList w) = last (HeightList ((x#v)@w))\<close>
proof(cases \<open>v = []\<close>)
  case True
  then show ?thesis 
    using ConcatHeightSumU assms(2) by blast
next
  case False
  then have \<open>v \<noteq> []\<close> by blast
  have \<open>last (HeightList v) + last (HeightList w) = last (HeightList (v@w))\<close>
    by (simp add: False assms(1) assms(2))
  then have \<open>last (HeightList [x]) + last (HeightList v) + last (HeightList w) = last (HeightList [x]) + last (HeightList (v@w))\<close>
    by simp
  then have \<open>last (HeightList ([x]@v)) + last (HeightList w) = last (HeightList [x]) + last (HeightList (v@w))\<close>
    using ConcatHeightSumU  \<open>v \<noteq> []\<close> 
    by metis
  then have \<open>last (HeightList ([x]@v)) + last (HeightList w) =  last (HeightList ([x]@(v@w)))\<close>
    using ConcatHeightSumU  \<open>v \<noteq> []\<close> 
    by auto
  then show ?thesis by auto
qed

lemma ConcatHeightSumQ: \<open> \<forall> w. v \<noteq> [] \<and> w \<noteq> [] \<longrightarrow> last (HeightList v) + last (HeightList w) = last (HeightList (v@w)) \<close> 
proof(induction v)
  case Nil
  then show ?case 
    by simp
next
  case (Cons a v)
  then show ?case using ConcatHeightSumQRec 
    by blast 
qed

lemma ConcatHeightSum: \<open>v \<noteq> [] \<Longrightarrow> w \<noteq> [] \<Longrightarrow> last (HeightList v) + last (HeightList w) = last (HeightList (v@w)) \<close> 
  using ConcatHeightSumQ by blast

lemma ConcatHeightComm: \<open>v \<noteq> [] \<Longrightarrow> w \<noteq> [] \<Longrightarrow> last (HeightList (v@w)) =  last (HeightList (w@v)) \<close> 
  using ConcatHeightSum 
  by smt

lemma Lastsumchar: \<open>last (HeightList ((a+b)#v)) = last (HeightList (a#b#v))\<close>
  using HeightList.elims by auto

lemma ConcatHeightLX2Rec:
  assumes \<open>\<forall> a.  HeightList ((a#v)@[x]) = (HeightList (a#v)) @ [x+(last (HeightList (a#v)))] \<close> 
  shows \<open>HeightList ((a#(b#v))@[x]) = (HeightList (a#(b#v))) @ [x+(last (HeightList (a#(b#v))))] \<close>
proof-
  have \<open>HeightList ((a#(b#v))@[x]) = HeightList (a#b#v@[x])\<close>
    by simp
  then have \<open>HeightList ((a#(b#v))@[x]) = a#HeightList ((a+b)#v@[x])\<close>
    by auto
  then have \<open>HeightList ((a#(b#v))@[x]) = a# (HeightList ((a+b)#v)) @ [x+(last (HeightList ((a+b)#v)))]\<close>
    using assms by auto
  have \<open>last (HeightList ((a+b)#v)) = last (HeightList (a#b#v))\<close>
    by (simp add: Lastsumchar)
  then have \<open>HeightList ((a#(b#v))@[x]) = a# (HeightList ((a+b)#v)) @ [x+(last (HeightList (a#b#v)))]\<close>
    using  \<open>HeightList ((a#(b#v))@[x]) = a# (HeightList ((a+b)#v)) @ [x+(last (HeightList ((a+b)#v)))]\<close>
    by auto
  have \<open>a# (HeightList ((a+b)#v)) = (HeightList (a#b#v))\<close>
    by simp
  then have \<open>HeightList ((a#(b#v))@[x]) = (HeightList (a#b#v)) @ [x+(last (HeightList (a#b#v)))]\<close>
    using  \<open>HeightList ((a#(b#v))@[x]) = a# (HeightList ((a+b)#v)) @ [x+(last (HeightList (a#b#v)))]\<close>
    by simp
  then show ?thesis 
    by blast
qed

lemma ConcatHeightLX2: \<open>\<forall> a.  HeightList ((a#v)@[x]) = (HeightList (a#v)) @ [x+(last (HeightList (a#v)))] \<close>
proof(induction v)
  case Nil
  then show ?case by simp
next
  case (Cons a v)
  then show ?case using ConcatHeightLX2Rec by auto
qed

lemma ConcatHeightLX1: \<open>v \<noteq> [] \<Longrightarrow>
 HeightList (v@[x]) = (HeightList v) @ [x+(last (HeightList v))] \<close> 
  using ConcatHeightLX2 
  by (metis neq_Nil_conv)

lemma ConcatHeightLX: \<open>v \<noteq> [] \<Longrightarrow>
 HeightList (v@[x]) = (HeightList v)@( incr (HeightList [x]) (last (HeightList v)) )\<close> 
  using ConcatHeightLX1 
  by simp

lemma  IncreHeight: \<open>v \<noteq> [] \<Longrightarrow>
    ( (HeightList v)@( incr (HeightList u) (last (HeightList v)) )  )
 @ ( incr (HeightList [x]) (last (HeightList (v@u))) )
 = (HeightList v)@( incr (HeightList (u @ [x])) (last (HeightList v)) )\<close>
proof(cases \<open>u = []\<close>)
  case True
  then show ?thesis 
    by simp
next
  case False
  then have \<open>u \<noteq> []\<close> by blast
  assume \<open>v \<noteq> []\<close>
  then have \<open>HeightList (u @ [x]) = (HeightList u)@( incr (HeightList [x]) (last (HeightList u)) )\<close>
    using ConcatHeightLX  \<open>u \<noteq> []\<close> by blast
  then have \<open>incr (HeightList (u @ [x])) (last (HeightList v)) = incr ((HeightList u)@( incr (HeightList [x]) (last (HeightList u)) )) (last (HeightList v))\<close>
    by simp
  then have  \<open>incr (HeightList (u @ [x])) (last (HeightList v)) = (incr (HeightList u) (last (HeightList v)) )  @ (incr ( incr (HeightList [x]) (last (HeightList u)) )  (last (HeightList v)))\<close>
    by (simp add: CocatIncr)
  then have  \<open>incr (HeightList (u @ [x])) (last (HeightList v)) = (incr (HeightList u) (last (HeightList v)) )  @  ( incr (HeightList [x]) (last (HeightList u)+last (HeightList v)) )  \<close>
    by auto
  then have  \<open>incr (HeightList (u @ [x])) (last (HeightList v)) = (incr (HeightList u) (last (HeightList v)) )  @  ( incr (HeightList [x]) (last (HeightList (u@v))) )  \<close>
    using  \<open>u \<noteq> []\<close>  \<open>v \<noteq> []\<close>
    by (simp add: ConcatHeightSum ) 
  then have  \<open>(HeightList v)@( incr (HeightList (u @ [x])) (last (HeightList v)) ) = (HeightList v)@ ((incr (HeightList u) (last (HeightList v)) )  @  ( incr (HeightList [x]) (last (HeightList (u@v))) ) ) \<close>
    by simp
  then have \<open>(HeightList v)@( incr (HeightList (u @ [x])) (last (HeightList v)) ) = ( (HeightList v)@( incr (HeightList u) (last (HeightList v)) )  ) @ ( incr (HeightList [x]) (last (HeightList (v@u))) )\<close>
    using ConcatHeightComm 
    by (simp add: False \<open>v \<noteq> []\<close>)
  then show ?thesis
    by auto
qed

lemma ConcatHeightQRec:
  assumes  \<open>\<forall> v w. v \<noteq> [] \<and> length w = n \<longrightarrow> HeightList (v@w) = (HeightList v)@( incr (HeightList w) (last (HeightList v)) )\<close>
    and \<open>v \<noteq> []\<close> and \<open>length w = Suc n\<close>
  shows \<open>HeightList (v@w) = (HeightList v)@( incr (HeightList w) (last (HeightList v)) )\<close>  
proof-
  from  \<open>length w = Suc n\<close> obtain u x where \<open>w = u @ [x]\<close> 
    by (metis append_butlast_last_id length_0_conv nat.simps(3))
  have \<open>length u = n\<close> 
    using \<open>w = u @ [x]\<close> assms(3) by auto
  have \<open>HeightList (v@u) = (HeightList v)@( incr (HeightList u) (last (HeightList v)) )\<close>
    by (simp add: \<open>length u = n\<close> assms(1) assms(2))
  have \<open>HeightList ((v@u)@[x]) = (HeightList (v@u)) @ ( incr (HeightList [x]) (last (HeightList (v@u))) )\<close>
    using ConcatHeightLX assms(2) by blast
  then have \<open>HeightList ((v@u)@[x]) = ( (HeightList v)@( incr (HeightList u) (last (HeightList v)) )  ) @ ( incr (HeightList [x]) (last (HeightList (v@u))) )\<close>
    using \<open>HeightList (v @ u) = HeightList v @ incr (HeightList u) (last (HeightList v))\<close> by auto
  then have \<open>HeightList (v @ w) = ( (HeightList v)@( incr (HeightList u) (last (HeightList v)) )  ) @ ( incr (HeightList [x]) (last (HeightList (v@u))) )\<close>
    using \<open>w = u @ [x]\<close> by auto
  then have \<open>HeightList (v @ w) = (HeightList v)@( incr (HeightList (u @ [x])) (last (HeightList v)) )\<close>
    using IncreHeight assms(2) by auto
  then show ?thesis 
    using \<open>w = u @ [x]\<close> by blast
qed

lemma ConcatHeightQ: \<open>\<forall> v w. v \<noteq> [] \<and> length w = n \<longrightarrow> HeightList (v@w) = (HeightList v)@( incr (HeightList w) (last (HeightList v)) )\<close>
proof(induction n)
  case 0
  then show ?case 
    by simp
next
  case (Suc n)
  then show ?case using ConcatHeightQRec 
    by blast
qed


lemma ConcatHeight: \<open>v \<noteq> [] \<Longrightarrow> HeightList (v@w) = (HeightList v)@( incr (HeightList w) (last (HeightList v)) )\<close>
  using ConcatHeightQ by blast

lemma lastHeightListPrefix: \<open>w \<noteq> [] \<Longrightarrow> last (HeightList (x#w)) = x+(last (HeightList w))\<close>
  by (simp add: ConcatHeightSumUS)

lemma HeightListPar: \<open>w \<noteq> [] \<Longrightarrow> HeightList ([1] @ w @ [-1]) = [1] @ (incr (HeightList w) 1) @ [last (HeightList w)]\<close>
proof-
  assume \<open>w \<noteq> []\<close>
  have \<open>[1] \<noteq> []\<close> by simp
  have \<open>HeightList ([1] @ w) = [1] @ (incr (HeightList w) 1)\<close> 
    by (metis ConcatHeight HeightList.simps(2) \<open>[1] \<noteq> []\<close> last.simps)
  have \<open>[1] @ w \<noteq> []\<close> 
    by simp
  have \<open>HeightList ([1] @ w @ [-1]) = (HeightList ([1] @ w)) @ (incr [-1] (last (HeightList ([1] @ w))))\<close>
    by (metis ConcatHeight HeightList.simps(2) \<open>[1] @ w \<noteq> []\<close> append.assoc)   
  then have \<open>HeightList ([1] @ w @ [-1]) = [1] @ (incr (HeightList w) 1) @ (incr [-1] (last (HeightList ([1] @ w))))\<close>
    using \<open>HeightList ([1] @ w) = [1] @ incr (HeightList w) 1\<close> by auto
  then have \<open>HeightList ([1] @ w @ [-1]) = [1] @ (incr (HeightList w) 1) @ (incr [-1] (last (HeightList w)+1))\<close>
    by (simp add: \<open>w \<noteq> []\<close> lastHeightListPrefix)
  then have \<open>HeightList ([1] @ w @ [-1]) = [1] @ (incr (HeightList w) 1) @ [-1+(last (HeightList w)+1)]\<close>
    by auto
  then have \<open>HeightList ([1] @ w @ [-1]) = [1] @ (incr (HeightList w) 1) @ [last (HeightList w)]\<close>
    by simp
  then show ?thesis by blast
qed

lemma NonNegPathincr: \<open>NonNeg w \<Longrightarrow> c \<ge> 0 \<Longrightarrow> NonNeg (incr w c)\<close> 
proof(induction w)
  case Nil
  then show ?case 
    by simp
next
  case (Cons a w)
  then show ?case 
    by (smt NonNeg.simps(2) incr.simps(2))
qed

lemma ConcatNonNeg: \<open>NonNeg v \<Longrightarrow> NonNeg w \<Longrightarrow> NonNeg (v@w)\<close> 
proof(induction v)
  case Nil
  then show ?case 
    by simp
next
  case (Cons a v)
  then show ?case 
    by (metis Cons_eq_appendI NonNeg.simps(2))
qed


lemma NonNegRecLast: \<open>NonNeg (w@[x]) = (if x \<ge> 0 then NonNeg w else False)\<close>
proof(induction w)
  case Nil
  then show ?case 
    by simp
next
  case (Cons a w)
  then show ?case 
    by auto
qed

lemma NonNegPathlast: \<open>w \<noteq> [] \<Longrightarrow> NonNegPath w \<Longrightarrow> last (HeightList w) \<ge> 0\<close> 
  using NonNegRecLast 
  by (metis HeightList.elims NonNegPath.elims(2) list.discI snoc_eq_iff_butlast)

lemma DyckBNonNegPath: \<open>NonNegPath w \<Longrightarrow> NonNegPath ([1] @ w @ [-1])\<close>
proof(cases \<open>w = []\<close>)
  case True
  then show ?thesis 
    by simp
next
  case False
  then have \<open>w \<noteq> []\<close> by blast
  assume \<open>NonNegPath w\<close>
  then have \<open>NonNeg (HeightList w)\<close> 
    by simp
  then have \<open>NonNeg (incr (HeightList w) 1)\<close> 
    by (simp add: NonNegPathincr) 
  have \<open>HeightList ([1] @ w @ [-1]) = [1] @ (incr (HeightList w) 1) @ [last (HeightList w)]\<close>
    using HeightListPar \<open>w \<noteq> []\<close> by blast
  have \<open>last (HeightList w) \<ge> 0\<close> 
    using NonNegPathlast \<open>NonNegPath w\<close> \<open>w \<noteq> []\<close> by blast
  have \<open>(1::int) \<ge> (0::int)\<close> 
    by simp
  have \<open>NonNeg ([1] @ (incr (HeightList w) 1))\<close> 
    by (simp add: \<open>NonNeg (incr (HeightList w) 1)\<close>)
  have \<open>NonNeg [last (HeightList w)]\<close> 
    by (simp add: \<open>0 \<le> last (HeightList w)\<close>)
  have \<open>NonNeg ( ([1] @ (incr (HeightList w) 1)) @ [last (HeightList w)] )\<close>
    using ConcatNonNeg  \<open>NonNeg ([1] @ (incr (HeightList w) 1))\<close> \<open>NonNeg [last (HeightList w)]\<close> 
    by blast
  then show ?thesis 
    using \<open>HeightList ([1] @ w @ [- 1]) = [1] @ incr (HeightList w) 1 @ [last (HeightList w)]\<close> by auto
qed

lemma DyckBlast: \<open>(w \<noteq> [] \<longrightarrow> last (HeightList w) = 0) \<Longrightarrow> (([1] @ w @ [-1]) \<noteq> [] \<longrightarrow> last (HeightList ([1] @ w @ [-1])) = 0)\<close>
  by (metis (no_types, hide_lams) ConcatHeightComm   ConcatHeightSumUS  HeightList.simps(2) HeightList.simps(3) Nil_is_append_conv  add_cancel_right_right  append.left_neutral append_eq_Cons_conv eq_neg_iff_add_eq_0 last.simps last_ConsL  not_Cons_self)

proposition DyckB: \<open>DyckPath w \<Longrightarrow> DyckPath ([1] @ w @ [-1])\<close>
  using DyckBDyckLetters DyckBNonNegPath DyckBlast by auto

section {* Proposition DyckC *}

lemma DyckCNonNegPath: \<open>NonNegPath v \<Longrightarrow> NonNegPath w \<Longrightarrow> NonNegPath (v @ w)\<close>
  by (metis ConcatHeightQ ConcatNonNeg NonNegPath.elims(2) NonNegPath.elims(3) NonNegPathincr NonNegPathlast append.left_neutral)

lemma DyckCDyckLetters: \<open>DyckLetters v \<Longrightarrow> DyckLetters w \<Longrightarrow> DyckLetters (v @ w)\<close>
proof(induction v)
  case Nil
  then show ?case 
    by simp
next
  case (Cons a v)
  then show ?case 
    by (metis DyckLetters.simps(2) append_Cons)
qed

lemma DyckCDyckLetterslastHeightList: \<open>(v \<noteq> [] \<longrightarrow> last (HeightList v) = 0) \<Longrightarrow> (w \<noteq> [] \<longrightarrow> last (HeightList w) = 0) \<Longrightarrow> (v@w \<noteq> [] \<longrightarrow> last (HeightList (v@w)) = 0)\<close>
  by (metis ConcatHeightSumQ add_cancel_left_right  append_self_conv2  self_append_conv)

proposition DyckC: \<open>DyckPath v \<Longrightarrow> DyckPath w \<Longrightarrow> DyckPath (v @ w)\<close>
  using DyckCNonNegPath DyckCDyckLetters DyckCDyckLetterslastHeightList by auto


end

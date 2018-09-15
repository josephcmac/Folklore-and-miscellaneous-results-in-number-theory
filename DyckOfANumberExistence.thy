(*
Title: Existence of a Dyck path for each number
Author: Jose Manuel Rodriguez Caballero

Reference:

@article{caballero2017symmetric,
  title={Symmetric Dyck Paths and Hooley’s Delta-function},
  author={Caballero, Jos{\'e} Manuel Rodr{\i}guez},
  journal={Combinatorics on Words. Springer International Publishing AG},
  year={2017}
}

(This code  was verified in Isabelle2018)
*)

theory DyckOfANumberExistence

imports Complex_Main  SchroederOfANumberDefs PowOfTwo SchroederOfANumberExistence DyckPathOfANumberDefs

begin

section {*Auxiliary Results *}

definition STRANGEL :: \<open>SCHR list \<Rightarrow> int\<close> where 
\<open>STRANGEL \<equiv> (HeightLetterwise (\<lambda> c::SCHR. (if c = STRANGE then (1::int) else (0::int)))) \<close>


lemma STRANGELCHAR:
  fixes w :: \<open>SCHR list\<close> and a :: SCHR
  shows \<open>STRANGEL (a # w) = (if a = STRANGE then (STRANGEL w) + 1 else  (STRANGEL w)) \<close>
  by (simp add: STRANGEL_def)

lemma STRANGELCHARGE0:
  fixes w :: \<open>SCHR list\<close>
  shows \<open>STRANGEL w \<ge> 0 \<close>
proof(induction w)
  case Nil
  then show ?case 
    by (simp add: STRANGEL_def)
next
  case (Cons a w)
  then show ?case
    by (simp add: STRANGELCHAR)
qed


lemma STRANGELCHAR1:
  fixes w :: \<open>SCHR list\<close> and a :: SCHR
  assumes  \<open>STRANGEL (a # w) = 0\<close> 
  shows \<open>STRANGEL w = 0\<close>
  using assms STRANGELCHARGE0 STRANGELCHAR 
  by smt

lemma STRANGELCHAR2:
  fixes w :: \<open>SCHR list\<close> and a :: SCHR
  assumes  \<open>STRANGEL (a # w) = 0\<close> 
  shows \<open>a \<noteq> STRANGE\<close>
  using STRANGELCHAR STRANGELCHAR1 assms by fastforce


lemma DyckToSchroederSchroederToDyckRec:
  fixes w :: \<open>SCHR list\<close>
  assumes \<open>STRANGEL w = 0 \<longrightarrow> DyckToSchroeder (SchroederToDyck w) = w\<close>
  and \<open>STRANGEL (a # w) = 0\<close>
shows \<open>DyckToSchroeder (SchroederToDyck (a # w)) = a # w\<close>
  using assms STRANGELCHAR1 STRANGELCHAR2 SchroederToDyckCode_def
  by (metis (full_types) DCHR.distinct(1) DyckToSchroeder.simps(2) DyckToSchroederCode_def SCHR.distinct(1)   SCHR.exhaust   SchroederToDyck.simps(2) append_Cons append_Nil)

lemma DyckToSchroederSchroederToDyck:
  fixes w :: \<open>SCHR list\<close>
  shows \<open>STRANGEL w = 0 \<longrightarrow> DyckToSchroeder (SchroederToDyck w) = w\<close>
proof(induction w)
  case Nil
  then show ?case 
    by simp
next
  case (Cons a w)
  then show ?case 
    using DyckToSchroederSchroederToDyckRec by blast
qed

lemma HeightZeroStrange:
  fixes w :: \<open>DCHR list\<close>
shows \<open>SchroederHeight (DyckToSchroeder w) = DyckHeight w\<close>
proof(induction w)
  case Nil
  then show ?case 
    by (simp add: DyckHeight_def SchroederHeight_def)
next
  case (Cons a w)
  then show ?case 
    by (metis (full_types) DCHR.exhaust DyckHeightLetter.simps(1) DyckHeightLetter.simps(2) DyckHeight_def DyckToSchroeder.simps(2) DyckToSchroederCode_def HeightLetterwise.simps(2) SchroederHeightLetter.simps(1) SchroederHeightLetter.simps(2) SchroederHeight_def)
qed

lemma DyckIsSchroederH0:
  fixes w :: \<open>DCHR list\<close>
  shows \<open>SchroederHeight (DyckToSchroeder w) = 0 \<longrightarrow> DyckHeight w = 0\<close>
  using HeightZeroStrange by auto

lemma prefixL1:
  fixes u w :: \<open>'b list\<close> 
  assumes \<open>prefix u (a # w)\<close> and \<open>u \<noteq> []\<close>
  shows \<open>\<exists> uu. u = a # uu\<close>
proof -
obtain bb :: "'b list \<Rightarrow> 'b" and bbs :: "'b list \<Rightarrow> 'b list" where
  f1: "\<forall>bs. ([] \<noteq> bs \<or> (\<forall>b bsa. b # bsa \<noteq> bs)) \<and> (bb bs # bbs bs = bs \<or> [] = bs)"
  by (metis (no_types) neq_Nil_conv)
  { assume "a # bbs u \<noteq> u"
    then have "\<exists>bs. bs @ u = bs"
      using f1 by (metis append_Nil assms(1) length_greater_0_conv nth_Cons_0 prefix_def)
then have ?thesis
using assms(2) by force }
  then show ?thesis
    by (metis (full_types))
qed


lemma prefixL2:
  fixes u w :: \<open>'b list\<close> 
  assumes \<open>prefix (a # u) (a # w)\<close>
  shows \<open>prefix u w\<close>
  by (metis (no_types, lifting) Suc_le_mono Suc_less_eq assms length_Cons nth_Cons_Suc prefix_def)

lemma prefixL3:
  fixes u w :: \<open>'b list\<close>
  assumes \<open>prefix u w\<close>
  shows \<open>prefix (x # u) (x # w) \<close>
proof-
  from \<open>prefix u w\<close> have \<open>( (length u \<le> length w)
 \<and> (\<forall> j. j < length u \<longrightarrow>  u ! j =  w ! j ) )\<close> by (simp add: prefix_def)
  then have \<open>length u \<le> length w\<close> by blast
  then have \<open>length (x # u) \<le> length (x # w)\<close> 
    by simp
  from  \<open>( (length u \<le> length w)
 \<and> (\<forall> j. j < length u \<longrightarrow>  u ! j =  w ! j ) )\<close>
  have  \<open>(\<forall> j. j < length u \<longrightarrow>  u ! j =  w ! j )\<close> by blast
  then have \<open>(\<forall> j. Suc j < length (x # u) \<longrightarrow>  (x # u) ! (Suc j) =  (x # w) ! (Suc j) )\<close>
    by simp
  then have \<open>(\<forall> j. j < length (x # u) \<longrightarrow>  (x # u) ! j =  (x # w) ! j )\<close> 
    by (simp add: nth_Cons')
  then show ?thesis using  \<open>length (x # u) \<le> length (x # w)\<close> 
    by (simp add: prefix_def)
qed

lemma DyckIsSchroederPrefixOntoRec:
  fixes w u :: \<open>DCHR list\<close> 
  assumes \<open>\<forall> u. (prefix u w \<longrightarrow> prefix (DyckToSchroeder u) (DyckToSchroeder w))\<close>
  and \<open>prefix u (a # w)\<close>
  shows  \<open> prefix (DyckToSchroeder u) (DyckToSchroeder (a # w))\<close>
proof(cases \<open>u = []\<close>)
  case True
  then show ?thesis 
    by (simp add: prefix_def)
next
  case False
  then obtain uu where \<open>u = a # uu\<close> 
    by (meson assms(2) prefixL1)
  have \<open>prefix uu w\<close> 
    using \<open>u = a # uu\<close> assms(2) prefixL2 by fastforce
  have \<open>prefix (DyckToSchroeder uu) (DyckToSchroeder w)\<close>
    by (simp add: \<open>prefix uu w\<close> assms(1))
  obtain x where \<open>(DyckToSchroeder u) = x # (DyckToSchroeder uu)\<close> 
    by (simp add: \<open>u = a # uu\<close>)
  have \<open>(DyckToSchroeder (a # w)) = x # (DyckToSchroeder w)\<close> 
    using \<open>DyckToSchroeder u = x # DyckToSchroeder uu\<close> \<open>u = a # uu\<close> by auto
  have \<open>prefix (DyckToSchroeder uu) (DyckToSchroeder w)\<close> 
    by (simp add: \<open>prefix (DyckToSchroeder uu) (DyckToSchroeder w)\<close>)
  show ?thesis 
    using \<open>DyckToSchroeder (a # w) = x # DyckToSchroeder w\<close> \<open>DyckToSchroeder u = x # DyckToSchroeder uu\<close> \<open>prefix (DyckToSchroeder uu) (DyckToSchroeder w)\<close> prefixL3 by force
  qed

lemma DyckIsSchroederPrefixOnto:
  fixes w :: \<open>DCHR list\<close> 
  shows \<open>\<forall> u. (prefix u w \<longrightarrow> prefix (DyckToSchroeder u) (DyckToSchroeder w))\<close>
proof (induction w)
case Nil
  then show ?case 
    by (simp add: prefix_def)
next
  case (Cons a w)
  then show ?case using DyckIsSchroederPrefixOntoRec by blast
qed

lemma DyckIsSchroederPrefix:
  fixes w :: \<open>DCHR list\<close>
  shows \<open>(\<forall> v::SCHR list. (prefix v (DyckToSchroeder w) \<longrightarrow> SchroederHeight v \<ge> 0)) \<longrightarrow> (\<forall> u::DCHR list. (prefix u w \<longrightarrow> DyckHeight u \<ge> 0))\<close>
  using HeightZeroStrange DyckIsSchroederPrefixOnto
  by fastforce

lemma DyckIsSchroeder:
  fixes w :: \<open>DCHR list\<close>
  shows \<open>SchroederPath (DyckToSchroeder w) \<longrightarrow> DyckPath w\<close>
  using DyckIsSchroederH0 DyckIsSchroederPrefix SchroederPath_def 
  by (metis AbstractPath_def DyckPath_def)

lemma SchroederTransIntoDyckStranger0:
  fixes w :: \<open>SCHR list\<close>
  assumes \<open>SchroederPath w\<close> and \<open>STRANGEL w = 0\<close>
  shows \<open>DyckPath (SchroederToDyck w)\<close>
  by (simp add: DyckIsSchroeder DyckToSchroederSchroederToDyck assms(1) assms(2))


lemma STRANGELAdd:
  fixes u v :: \<open>SCHR list\<close>
  shows \<open>STRANGEL (u @ v) = (STRANGEL u) + (STRANGEL v)\<close>
proof(induction u)
  case Nil
  then show ?case 
    by (simp add: STRANGEL_def)
next
  case (Cons a u)
  then show ?case 
    by (simp add: STRANGEL_def)
qed

lemma ZPreSchroederStrangeRedPara_nRED:
  fixes w :: \<open>SCHR list\<close>
  shows \<open>(\<forall> u v. w \<noteq> u @ [STRANGE] @ v) \<longrightarrow> STRANGEL w = 0\<close>
proof(induction w)
  case Nil
  then show ?case 
    by (simp add: STRANGEL_def)
next
  case (Cons a w)
  then show ?case 
    by (metis (no_types, hide_lams)  STRANGELCHAR  append_Cons  self_append_conv2)
qed

lemma PreSchroederStrangeRedPara_nRED:
  fixes w :: \<open>SCHR list\<close>
  assumes \<open>STRANGEL w \<noteq> 0\<close>
  shows \<open>\<exists> u v. w = u @ [STRANGE] @ v\<close>
  using ZPreSchroederStrangeRedPara_nRED assms by blast

lemma SchroederToDyckConcat:
  fixes u v :: \<open>SCHR list\<close>
  shows \<open>SchroederToDyck (u @ v) = (SchroederToDyck u) @ (SchroederToDyck v)\<close>
proof(induction u)
case Nil
  then show ?case 
    by simp
next
  case (Cons a u)
  then show ?case 
    by simp
qed



lemma SchroederHeightAdd:
  fixes u :: \<open>SCHR list\<close>
  shows \<open>\<forall> v. SchroederHeight (u @ v) = (SchroederHeight u)+(SchroederHeight v)\<close>
proof(induction u)
  case Nil
have \<open> (SchroederHeight Nil) = 0\<close> 
  by (metis DyckHeight_def DyckToSchroeder.simps(1) HeightLetterwise.simps(1) HeightZeroStrange) 
  then show ?case 
    by simp
next
  case (Cons a u)
  then show ?case 
    by (smt Cons_eq_appendI HeightLetterwise.simps(2) SchroederHeight_def)
qed

lemma SchroederHeightSTRANGE:
  \<open>SchroederHeight [STRANGE] = 0\<close>
  by (simp add: SchroederHeight_def)


lemma SchroederPathIsNotStrangeHeightZero:
  fixes u v :: \<open>SCHR list\<close>
  assumes \<open>SchroederHeight (u @ [STRANGE] @ v) = 0\<close>
  shows \<open>SchroederHeight (u @ v) = 0\<close>
  using SchroederHeightAdd SchroederHeightSTRANGE assms by presburger

lemma prefixLX:
  fixes p u v :: \<open>'a list\<close>
  assumes \<open>prefix p u\<close>
  shows  \<open>prefix p (u @ v)\<close>
proof-
  from \<open>prefix p u\<close> have \<open>length p \<le> length u\<close> using prefix_def by metis
  then have \<open>length p \<le> length (u @ v)\<close> 
    by auto
  from \<open>prefix p u\<close> have \<open>\<forall> j. j < length p \<longrightarrow> p ! j = u ! j\<close> using prefix_def by metis
  then have  \<open>\<forall> j. j < length p \<longrightarrow> p ! j = (u @ v) ! j\<close> 
    by (simp add: \<open>length p \<le> length u\<close> less_le_trans nth_append)
  from \<open>length p \<le> length (u @ v)\<close>   \<open>\<forall> j. j < length p \<longrightarrow> p ! j = (u @ v) ! j\<close>  show ?thesis
    by (simp add: prefix_def)
qed

lemma prefixYYBase:
  assumes \<open>prefix u Nil\<close>
  shows  \<open>\<exists> q.  Nil = u @ q\<close>
proof-
  from  \<open>prefix u Nil\<close> prefix_def have \<open>length u \<le> length Nil\<close>
    by (simp add: assms prefix_def)
  then have \<open>u = Nil\<close> 
    by simp
  then show ?thesis 
    by simp
qed

lemma prefixYYRec:
  assumes \<open>prefix u (a # p)\<close> and  \<open>\<forall> u.  prefix u p \<longrightarrow> (\<exists> q.  p = u @ q)\<close>
  shows  \<open>\<exists> q.  a # p = u @ q\<close>
proof(cases \<open>u = Nil\<close>)
  case True
  then show ?thesis 
    by simp
next
  case False
  then have \<open>length u > 0\<close> 
    by blast 
  from  \<open>prefix u (a # p)\<close> have \<open>length u \<le> length (a # p)\<close> by (simp add:  prefix_def)
  from  \<open>prefix u (a # p)\<close> have \<open>\<forall> j. j < length u \<longrightarrow> u ! j = (a # p) ! j\<close> by (simp add:  prefix_def)
  then have \<open>u ! 0 = a\<close> using  \<open>length u > 0\<close> 
    by simp
  then  obtain uu where \<open>u = a # uu\<close> 
    using False assms(1) prefixL1 by fastforce
  have  \<open>length (a # uu) \<le> length (a # p)\<close>  
    using \<open>length u \<le> length (a # p)\<close> \<open>u = a # uu\<close> by blast
  then have \<open>length uu \<le> length  p\<close> 
    by auto  
  have \<open>\<forall> j. j < length (a # uu) \<longrightarrow> (a # uu) ! j = (a # p) ! j\<close>
    using \<open>\<forall>j<length u. u ! j = (a # p) ! j\<close> \<open>u = a # uu\<close> by blast
  then  have \<open>\<forall> j. j < length  uu \<longrightarrow>  uu ! j =  p ! j\<close>
    using assms(2) by auto
  then have \<open>prefix uu p\<close> using  \<open>length uu \<le> length  p\<close>
    by (simp add : prefix_def)
  obtain q where \<open>p = uu @ q\<close> 
    using \<open>prefix uu p\<close> assms(2) by blast
  from \<open>p = uu @ q\<close> have \<open>a # p = a # (uu @ q)\<close> 
    by simp
  then have \<open>a # p = (a # uu) @ q\<close> 
    by simp
  then show ?thesis using \<open>u = a # uu\<close> 
    by blast
qed


lemma prefixYY:
  fixes p :: \<open>'a list\<close>
  shows  \<open>\<forall> u.  prefix u p \<longrightarrow> (\<exists> q.  p = u @ q)\<close>
proof(induction p)
  case Nil
  then show ?case  
    using prefixYYBase by blast
next
  case (Cons a p)
  then show ?case 
    by (simp add: prefixYYRec)
qed

lemma prefixY:
  fixes u v p :: \<open>'a list\<close>
  assumes  \<open>prefix p (u @ v)\<close> and \<open>\<not> (prefix p u)\<close>
  shows \<open>\<exists> q. prefix q v \<and> p = u @ q\<close>
proof-
  from \<open>prefix p (u @ v)\<close> 
  have \<open>length p \<le> length (u @ v)\<close> by (simp add: prefix_def)
  from \<open>prefix p (u @ v)\<close> 
  have \<open>\<forall> j. j < length p \<longrightarrow> p ! j = (u @ v) ! j\<close> 
    by (simp add: prefix_def)
  then have \<open>\<forall> j. j < length p \<and>  j < length u  \<longrightarrow> p ! j = u ! j\<close> 
    by (simp add: nth_append)
  then have \<open>length p > length u\<close> using  \<open>\<not> (prefix p u)\<close> prefix_def
    by (metis (no_types, lifting) dual_order.strict_trans leI linorder_neqE_nat)
  from  \<open>\<forall> j. j < length p \<and>  j < length u  \<longrightarrow> p ! j = u ! j\<close>  and \<open>length p > length u\<close>
  have  \<open>\<forall> j. j < length u  \<longrightarrow> p ! j = u ! j\<close> 
    by auto
  then have \<open>prefix u p\<close> using  \<open>length p > length u\<close> by (simp add: prefix_def)
  then obtain q where \<open>p = u @ q\<close> 
    using prefixYY by blast
  from  \<open>p = u @ q\<close>  \<open>length p \<le> length (u @ v)\<close>
  have  \<open>length  (u @ q) \<le> length (u @ v)\<close>
    by blast
  have \<open>length  (u @ q) = length u + length  q\<close>
    by simp
  have \<open>length  (u @ v) = length u + length  v\<close>
    by simp
  have \<open>length u + length q \<le>  length u + length v\<close> 
    using \<open>length (u @ q) \<le> length (u @ v)\<close> by auto
  then have \<open> length q \<le> length v \<close> 
    using add_le_cancel_left by blast
  have  \<open>\<forall> j. j < length q  \<longrightarrow> q ! j = v ! j\<close> 
    by (metis  \<open>\<forall>j<length p. p ! j = (u @ v) ! j\<close> \<open>length (u @ q) = length u + length q\<close> \<open>p = u @ q\<close> add_less_cancel_left  nth_append_length_plus)
  have \<open>prefix q v\<close> using  \<open>\<forall> j. j < length q  \<longrightarrow> q ! j = v ! j\<close>  \<open> length q \<le> length v \<close> 
    by (simp add: prefix_def)
  then show ?thesis using  \<open>p = u @ q\<close> 
    by blast
qed

lemma prefixZ1:
  fixes u v p :: \<open>'a list\<close>
  assumes \<open>prefix u w\<close> 
  shows \<open>prefix (p @ u) (p @ w)\<close> 
proof(induction p)
  case Nil
  then show ?case 
    by (simp add: assms)
next
  case (Cons a p)
  then show ?case 
    by (simp add: prefixL3)
qed

lemma prefixZ2:
  fixes u v p :: \<open>'a list\<close>
  assumes \<open>prefix (p @ u) (p @ w)\<close>  
  shows  \<open>prefix u w\<close>
proof-
  from  \<open>prefix (p @ u) (p @ w)\<close> 
  have \<open>length (p @ u) \<le> length (p @ w)\<close> 
    by (simp add: prefix_def)
  then have \<open>length u \<le> length w\<close> 
    by simp
  from  \<open>prefix (p @ u) (p @ w)\<close> 
  have \<open>\<forall> j. j < length (p @ u) \<longrightarrow> (p @ u) ! j = (p @ w) ! j\<close>
    by (simp add: prefix_def)
  then have \<open>\<forall> j. j < length  u \<longrightarrow>  u ! j = w ! j\<close>
    by (metis add_less_cancel_left length_append nth_append_length_plus)
  from  \<open>length u \<le> length w\<close>  \<open>\<forall> j. j < length  u \<longrightarrow>  u ! j = w ! j\<close>
  have \<open>prefix u w\<close> by (simp add: prefix_def)
  then show ?thesis by blast
qed

lemma prefixZ:
  fixes u v q x:: \<open>'a list\<close>
  assumes \<open>prefix (u @ q) (u @ v)\<close> 
  shows \<open>prefix (u @ x @ q) (u @ x @ v)\<close> 
  using assms prefixZ1 prefixZ2 by blast

lemma SchroederPathIsNotStrangeHeightREC:
  fixes u v p :: \<open>SCHR list\<close>
  assumes \<open>\<forall> p :: SCHR list. prefix p (u @ [STRANGE] @ v) \<longrightarrow> SchroederHeight p \<ge> 0\<close>
    and \<open>prefix p (u @ v)\<close>
  shows  \<open>SchroederHeight p \<ge> 0\<close>
proof(cases \<open>prefix p u\<close>)
  case True
  then have \<open> prefix p (u @ [STRANGE] @ v) \<close> 
    by (simp add: prefixLX)
  then have  \<open>SchroederHeight p \<ge> 0\<close> 
    using assms(1) by blast
  then show ?thesis by blast
next
  case False
  then obtain q where \<open>prefix q v\<close> and \<open>p = u @ q\<close>
    using assms(2) prefixY by blast
  have \<open>prefix (u @ [STRANGE] @ q) (u @ [STRANGE] @ v)\<close> 
    using \<open>p = u @ q\<close> assms(2) prefixZ by blast
then have \<open>SchroederHeight (u @ [STRANGE] @ q) \<ge> 0\<close> 
  using assms(1) by blast
  then have  \<open>SchroederHeight (u @  q) \<ge> 0\<close> 
    using SchroederHeightAdd SchroederHeightSTRANGE by smt
  then show ?thesis 
    using \<open>p = u @ q\<close> by blast
qed

lemma SchroederPathIsNotStrange:
  fixes u v :: \<open>SCHR list\<close>
  assumes \<open>SchroederPath (u @ [STRANGE] @ v)\<close>
  shows \<open>SchroederPath (u @ v)\<close>
proof-
  from \<open>SchroederPath (u @ [STRANGE] @ v)\<close>
  have \<open>SchroederHeight (u @ [STRANGE] @ v) = 0\<close> using AbstractPath_def SchroederPath_def SchroederHeight_def
    by (metis (full_types) )
  then have  \<open>SchroederHeight (u @ v) = 0\<close> using SchroederPathIsNotStrangeHeightZero 
    by blast
  from \<open>SchroederPath (u @ [STRANGE] @ v)\<close>
  have  \<open>\<forall> p :: SCHR list. prefix p (u @ [STRANGE] @ v) \<longrightarrow> SchroederHeight p \<ge> 0\<close>
 using AbstractPath_def SchroederPath_def SchroederHeight_def
  by (metis (full_types) )
  then have   \<open>\<forall> p :: SCHR list. prefix p (u @ v) \<longrightarrow> SchroederHeight p \<ge> 0\<close>
    using SchroederPathIsNotStrangeHeightREC by blast
  show ?thesis using  \<open>SchroederHeight (u @ v) = 0\<close>  \<open>\<forall> p :: SCHR list. prefix p (u @ v) \<longrightarrow> SchroederHeight p \<ge> 0\<close>
  AbstractPath_def SchroederPath_def SchroederHeight_def
    by (metis (full_types) )
qed

lemma SchroederStrangeRedPara_nRED:
  fixes v w :: \<open>SCHR list\<close> and n :: nat
  assumes \<open>STRANGEL v = Suc n\<close> and \<open>(SchroederToDyck v) = (SchroederToDyck w)\<close> and \<open>(SchroederPath w \<longrightarrow> SchroederPath v)\<close>
  shows   \<open>\<exists> v :: SCHR list. STRANGEL v =     n \<and> (SchroederToDyck v) = (SchroederToDyck w) \<and> (SchroederPath w \<longrightarrow> SchroederPath v)\<close>
proof-
  from \<open>STRANGEL v = Suc n\<close> have \<open>STRANGEL v \<noteq> 0\<close> 
    by linarith
  then obtain p q  where \<open>v = p @ [STRANGE] @ q\<close> 
    using PreSchroederStrangeRedPara_nRED by blast  
  obtain vv where \<open>vv = p @ q\<close> by blast
  have \<open>STRANGEL vv = n\<close> 
    using STRANGELAdd STRANGELCHAR \<open>v = p @ [STRANGE] @ q\<close> \<open>vv = p @ q\<close> assms(1) by auto
  from \<open>(SchroederToDyck v) = (SchroederToDyck w)\<close> 
    have \<open>(SchroederToDyck vv) = (SchroederToDyck w)\<close> 
      by (simp add: SchroederToDyckCode_def SchroederToDyckConcat \<open>v = p @ [STRANGE] @ q\<close> \<open>vv = p @ q\<close>)
  from \<open>(SchroederPath w \<longrightarrow> SchroederPath v)\<close>
    have \<open>(SchroederPath w \<longrightarrow> SchroederPath vv)\<close> 
      using SchroederPathIsNotStrange \<open>v = p @ [STRANGE] @ q\<close> \<open>vv = p @ q\<close> by blast
    show ?thesis 
      using \<open>STRANGEL vv = int n\<close> \<open>SchroederPath w \<longrightarrow> SchroederPath vv\<close> \<open>SchroederToDyck vv = SchroederToDyck w\<close> by blast
  qed

lemma SchroederStrangeRedPara_n:
  fixes w :: \<open>SCHR list\<close> and n :: nat
  shows   \<open>(\<exists> v :: SCHR list. STRANGEL v =  n \<and> (SchroederToDyck v) = (SchroederToDyck w) \<and> (SchroederPath w \<longrightarrow> SchroederPath v)) \<longrightarrow> (\<exists> v :: SCHR list. STRANGEL v = 0  \<and> (SchroederToDyck v) = (SchroederToDyck w) \<and> (SchroederPath w \<longrightarrow> SchroederPath v))\<close>
  proof(induction n)
case 0
then show ?case 
  by simp
next
  case (Suc n)
  then show ?case 
    using SchroederStrangeRedPara_nRED by blast
qed


lemma SchroederStrangeRed:
  fixes w :: \<open>SCHR list\<close>
  shows \<open>\<exists> v :: SCHR list. STRANGEL v = 0 \<and> (SchroederToDyck v) = (SchroederToDyck w) \<and> (SchroederPath w \<longrightarrow> SchroederPath v)\<close>
proof-
obtain n::nat where  \<open>STRANGEL w =  n\<close> 
  using STRANGELCHARGE0 zero_le_imp_eq_int by blast
  have  \<open>(SchroederToDyck w) = (SchroederToDyck w)\<close> by simp
  have \<open> (SchroederPath w \<longrightarrow> SchroederPath w)\<close> by blast
  then show ?thesis using SchroederStrangeRedPara_n 
    by (metis \<open>\<And>thesis. (\<And>n. STRANGEL w = int n \<Longrightarrow> thesis) \<Longrightarrow> thesis\<close>)
qed

lemma SchroederTransIntoDyck:
  fixes w :: \<open>SCHR list\<close>
  assumes \<open>SchroederPath w\<close>
  shows \<open>DyckPath (SchroederToDyck w)\<close>
proof-
  obtain v where \<open>STRANGEL v = 0\<close> and \<open>(SchroederToDyck v) = (SchroederToDyck w)\<close> and \<open>SchroederPath w \<longrightarrow> SchroederPath v\<close>
    using assms SchroederStrangeRed 
    by blast
  have \<open>DyckPath (SchroederToDyck v)\<close> 
    by (simp add: SchroederTransIntoDyckStranger0 \<open>STRANGEL v = 0\<close> \<open>SchroederPath w \<longrightarrow> SchroederPath v\<close> assms)
  then show ?thesis 
    by (simp add: \<open>SchroederToDyck v = SchroederToDyck w\<close>)
qed

section {* Main Result *}

theorem DyckArithmA :
  fixes n :: nat
  assumes \<open>n \<ge> 1\<close>
  shows \<open>\<exists> w :: DCHR list. n \<in> DyckClass w \<and> DyckPath w \<close>
  using SchroederArithmA SchroederTransIntoDyck assms 
  by (metis (mono_tags, lifting) DyckClass_def SchroederArithmL1 mem_Collect_eq)

end
(*
Title: The Erdos-Nicolas function and the height of Dyck paths
Author: Jose Manuel Rodriguez Caballero


We will prove the following result:

theorem ListEqCardPrefixDyckFun:
  \<open>\<exists> F :: nat\<Rightarrow>((DCHR list)\<Rightarrow>nat). \<forall> n::nat. n \<ge> 1 \<longrightarrow> (F n) ` (DyckTypeP n) = (ODiv n) \<and> (\<forall> x y. length x < length y \<and> x \<in> (DyckTypeP n) \<and> y \<in> (DyckTypeP n) \<longrightarrow> (F n) x < (F n) y)\<close>



Reference:

@article{caballero2017symmetric,
  title={Symmetric Dyck Paths and Hooley’s ∆-function},
  author={Caballero, Jos{\'e} Manuel Rodr{\i}guez},
  journal={Combinatorics on Words. Springer International Publishing AG},
  year={2017}
}

@article{caballero2018function,
  title={On a function introduced by Erd{\"o}s and Nicolas},
  author={Caballero, Jos{\'e} Manuel Rodr{\'i}guez},
  journal={Journal of Number Theory},
  year={2018},
  publisher={Elsevier}
}

@article{erdos1976methodes,
  title={M{\'e}thodes probabilistes et combinatoires en th{\'e}orie des nombres},
  author={Erdos, Paul and Nicolas, Jean-Louis},
  journal={Bull. Sci. Math},
  volume={2},
  number={100},
  pages={301--320},
  year={1976}
}

(This code  was verified in Isabelle2018)

*)


theory ErdosNicolasHeight

imports Complex_Main DyckPathHeight DyckTypeLengthDiv DyckPathHalfLength

begin

section {* Definitions *}

definition DyckTypeP :: \<open>nat \<Rightarrow> (DCHR list) set\<close> where
  \<open>DyckTypeP \<equiv> \<lambda> n. {v | v. prefix v (DyckType n) \<and> last v = up \<and> v \<noteq> []}\<close>



section {* Auxiliary Results *}

lemma ListEqCardIndX:
  fixes n :: nat and A B :: \<open>nat set\<close>
  assumes \<open>\<forall> A B :: nat set. finite A \<and> finite B \<and> card A = card B \<and> card A = n \<longrightarrow> (\<exists> f::nat\<Rightarrow>nat. f ` A = B \<and> (\<forall> x y. x < y \<and> x \<in> A \<and> y \<in> A \<longrightarrow> f x < f y))\<close>
    and \<open>finite A\<close> and \<open>finite B\<close> and \<open>card A = card B\<close> and \<open>card A = Suc n\<close>
  shows \<open>\<exists> f::nat\<Rightarrow>nat. f ` A = B \<and> (\<forall> x y. x < y \<and> x \<in> A \<and> y \<in> A \<longrightarrow> f x < f y)\<close>
proof-
  obtain X where \<open>X = A - {Max A}\<close> 
    by blast
  from \<open>X = A - {Max A}\<close> \<open>finite A\<close>  \<open>card A = Suc n\<close>
  have \<open>card X = n\<close> 
    using Max_in by fastforce
  have \<open>card B = Suc n\<close> 
    using assms(4) assms(5) by auto
  obtain Y where \<open>Y = B - {Max B}\<close> 
    by blast
  from \<open>Y = B - {Max B}\<close> \<open>finite B\<close>  \<open>card B = Suc n\<close>
  have \<open>card Y = n\<close> 
    using Max_in by fastforce
  have \<open>finite X\<close> 
    using \<open>X = A - {Max A}\<close> assms(2) by blast
  have \<open>finite Y\<close> 
    using \<open>Y = B - {Max B}\<close> assms(3) by blast
  have \<open>card X = card Y\<close> 
    by (simp add: \<open>card X = n\<close> \<open>card Y = n\<close>)
  obtain g::\<open>nat\<Rightarrow>nat\<close> where \<open>g ` X = Y\<close> and \<open>\<forall> x y. x < y \<and> x \<in> X \<and> y \<in> X \<longrightarrow> g x < g y\<close> 
    using \<open>card X = card Y\<close> \<open>card X = n\<close> \<open>finite X\<close> \<open>finite Y\<close> assms(1) by blast
  obtain f::\<open>nat\<Rightarrow>nat\<close> where 
    \<open>f \<equiv> \<lambda> n::nat. (if n = Max A then Max B else g n )\<close>
    by blast
  have \<open>f ` X = Y \<close> 
    using \<open>X = A - {Max A}\<close> \<open>f \<equiv> \<lambda>n. if n = Max A then Max B else g n\<close> \<open>finite X\<close> \<open>g ` X = Y\<close> assms(2) by fastforce 
  have \<open>f ` {Max A} = {Max B}\<close> 
    by (simp add: \<open>f \<equiv> \<lambda>n. if n = Max A then Max B else g n\<close>)
  from  \<open>f ` X = Y \<close>  \<open>f ` {Max A} = {Max B}\<close> \<open>X = A - {Max A}\<close> \<open>Y = B - {Max B}\<close>
  have \<open>f ` A = B \<close>
    by (metis Max_in Max_singleton assms(2) assms(3) assms(4) card_eq_0_iff image_empty image_insert insert_Diff)
  from \<open>\<forall> x y. x < y \<and> x \<in> X \<and> y \<in> X \<longrightarrow> g x < g y\<close> 
  have \<open>\<forall> x y. x < y \<and> x \<in> X \<and> y \<in> X \<longrightarrow> f x < f y\<close>
    by (simp add: \<open>X = A - {Max A}\<close> \<open>f \<equiv> \<lambda>n. if n = Max A then Max B else g n\<close>)
  have \<open>\<forall> x y. x < y \<and> x \<in> A \<and> y \<in> A \<longrightarrow> f x < f y\<close>
    by (metis (no_types, lifting) Max_ge Max_in Max_singleton \<open>X = A - {Max A}\<close> \<open>Y = B - {Max B}\<close> \<open>\<forall>x y. x < y \<and> x \<in> X \<and> y \<in> X \<longrightarrow> f x < f y\<close> \<open>f ` A = B\<close> \<open>f ` X = Y\<close> assms(2) assms(3) card.insert_remove image_insert insert_Diff insert_Diff_single insert_iff le_neq_trans linorder_not_le n_not_Suc_n)
  show ?thesis 
    using \<open>\<forall>x y. x < y \<and> x \<in> A \<and> y \<in> A \<longrightarrow> f x < f y\<close> \<open>f ` A = B\<close> by blast
qed


lemma ListEqCardInd:
  fixes n :: nat
  shows \<open>\<forall> A B :: nat set. finite A \<and> finite B \<and> card A = card B \<and> card A = n \<longrightarrow> (\<exists> f::nat\<Rightarrow>nat. f ` A = B \<and> (\<forall> x y. x < y \<and> x \<in> A \<and> y \<in> A \<longrightarrow> f x < f y))\<close>
proof(induction n)
  case 0
  then show ?case
    by auto
next
  case (Suc n)
  then show ?case  
    using ListEqCardIndX by auto
qed

lemma ListEqCard:
  fixes A B :: \<open>nat set\<close>
  assumes \<open>finite A\<close> and \<open>finite B\<close> and \<open>card A = card B\<close>
  shows \<open>\<exists> f::nat\<Rightarrow>nat. f ` A = B \<and> (\<forall> x y. x < y \<and> x \<in> A \<and> y \<in> A \<longrightarrow> f x < f y)\<close>
  using ListEqCardInd assms by blast


lemma PrefixLength:
  fixes A::\<open>(DCHR list) set\<close> and w::\<open>DCHR list\<close>
  assumes \<open>\<forall> v. v \<in> A \<longrightarrow> prefix v w\<close>
  shows \<open>finite A\<close> 
proof-
  have \<open> finite {v | v :: DCHR list. length v \<le> ((length w)::nat)} \<close>
    using FiniteNumberOfBoundedLength 
    by blast
  from  \<open>\<forall> v. v \<in> A \<longrightarrow> prefix v w\<close>
  have \<open>A \<subseteq> {v | v :: DCHR list. length v \<le> ((length w)::nat)}\<close>
    by (simp add: prefix_def subsetI)
  then have \<open>finite A\<close> 
    using \<open>finite {v |v. length v \<le> length w}\<close> finite_subset by blast
  then show ?thesis by blast
qed

lemma PrefixInjOnY:
  fixes A::\<open>(DCHR list) set\<close> and w::\<open>DCHR list\<close>
  assumes  \<open>\<forall> w. \<forall> A. (\<forall> v. v \<in> A \<longrightarrow> prefix v w) \<and> (\<forall> y. length x = length y \<and> x \<in> A \<and> y \<in> A \<longrightarrow> x = y)\<close> 
    and \<open>\<forall> v. v \<in> A \<longrightarrow> prefix v w\<close> and \<open>length (a#xx) = length y\<close> and \<open>(a#xx) \<in> A\<close> and \<open>y \<in> A\<close>
  shows \<open>a#xx = y\<close>
proof-
  have \<open>length (a#xx) \<noteq> 0\<close>
    by simp
  then have \<open>length y \<noteq> 0\<close> 
    using assms(3) by auto
  have \<open>w ! 0 = a\<close> 
    by (metis assms(2) assms(4) length_greater_0_conv list.discI nth_Cons_0 prefix_def)
  obtain b and yy where \<open>y = b # yy\<close>
    by (metis append.left_neutral append_eq_append_conv assms(3) map_tailrec_rev.elims)
  from \<open>y \<in> A\<close> have \<open>prefix y w\<close> 
    using assms(2) by blast
  then have \<open>y ! 0 = w ! 0\<close> 
    by (metis \<open>length y \<noteq> 0\<close> length_0_conv length_greater_0_conv prefix_def)
  then have \<open>b = a\<close> 
    by (simp add: \<open>w ! 0 = a\<close> \<open>y = b # yy\<close>)
  have \<open>length xx = length yy\<close> 
    using \<open>y = b # yy\<close> assms(3) by auto
  obtain ww where \<open>w = a#ww\<close> 
    using \<open>prefix y w\<close> \<open>w ! 0 = a\<close> \<open>y = b # yy\<close> prefixYY by fastforce
  obtain AA where \<open>AA = { tt | tt :: DCHR list. a#tt \<in> A}\<close> by blast
  have \<open>\<forall> v. v \<in> AA \<longrightarrow> prefix v ww\<close> 
    using \<open>AA = {tt |tt. a # tt \<in> A}\<close> \<open>w = a # ww\<close> assms(2) prefixL2 by fastforce
  have \<open>length xx = length yy\<close> 
    by (simp add: \<open>length xx = length yy\<close>)
  have \<open>xx \<in> AA\<close> 
    by (simp add: \<open>AA = {tt |tt. a # tt \<in> A}\<close> assms(4))
  have \<open>yy \<in> AA\<close> 
    using \<open>AA = {tt |tt. a # tt \<in> A}\<close> \<open>b = a\<close> \<open>y = b # yy\<close> assms(5) by blast
  have \<open>xx = yy\<close> 
    by (metis \<open>prefix y w\<close> \<open>y = b # yy\<close> append_eq_append_conv assms(2) assms(3) assms(4) list.inject prefixYY)
  show ?thesis 
    by (simp add: \<open>b = a\<close> \<open>xx = yy\<close> \<open>y = b # yy\<close>)
qed

lemma PrefixInjOnX:
  fixes A::\<open>(DCHR list) set\<close> and w::\<open>DCHR list\<close>
  assumes \<open>\<forall> v. v \<in> A \<longrightarrow> prefix v w\<close>
  shows \<open>\<forall> y. length x = length y \<and> x \<in> A \<and> y \<in> A \<longrightarrow> x = y\<close> 
proof(induction x)
  case Nil
  then show ?case 
    by simp
next
  case (Cons a x)
  then show ?case 
    by (metis append_eq_append_conv assms prefixYY)
qed  


lemma PrefixInjOn:
  fixes A::\<open>(DCHR list) set\<close> and w::\<open>DCHR list\<close>
  assumes \<open>\<forall> v. v \<in> A \<longrightarrow> prefix v w\<close>
  shows \<open>inj_on length A\<close> 
  using PrefixInjOnX
  by (meson assms inj_onI)


lemma ListEqCardPrefix:
  fixes A::\<open>(DCHR list) set\<close> and B::\<open>nat set\<close> and w::\<open>DCHR list\<close>
  assumes \<open>\<forall> v. v \<in> A \<longrightarrow> prefix v w\<close> and \<open>card A = card B\<close> and \<open>finite B\<close>
  shows \<open>\<exists> f::(DCHR list)\<Rightarrow>nat. f ` A = B \<and> (\<forall> x y. length x < length y \<and> x \<in> A \<and> y \<in> A \<longrightarrow> f x < f y)\<close>
proof-
  obtain AA::\<open>nat set\<close> where \<open>AA = length ` A\<close> by blast
  have \<open>inj_on length A\<close> 
    using PrefixInjOn assms(1) by blast
  then have \<open>card AA = card A\<close> 
    using \<open>AA = length ` A\<close> card_image by blast
  then have \<open>card AA = card B\<close> 
    by (simp add: assms(2))
  have \<open>finite A\<close> 
    using PrefixLength assms(1) by blast  
  have \<open>finite AA\<close> 
    by (simp add: \<open>AA = length ` A\<close> \<open>finite A\<close>)
  from \<open>finite A\<close> \<open>finite B\<close> \<open>card A = card B\<close> 
  obtain g::\<open>nat\<Rightarrow>nat\<close> where  \<open>g ` AA = B\<close> and \<open>\<forall> x y. x < y \<and> x \<in> AA \<and> y \<in> AA \<longrightarrow> g x < g y\<close>
    using ListEqCard \<open>card AA = card B\<close> \<open>finite AA\<close> by blast
  obtain f::\<open>DCHR list\<Rightarrow>nat\<close> where \<open>f = g \<circ> length\<close> by blast
  have \<open>f ` A = B\<close> 
    using \<open>AA = length ` A\<close> \<open>f = g \<circ> length\<close> \<open>g ` AA = B\<close> by auto
  have \<open>\<forall> x y. length x < length y \<and> x \<in> A \<and> y \<in> A \<longrightarrow> f x < f y\<close>
    by (simp add: \<open>AA = length ` A\<close> \<open>\<forall>x y. x < y \<and> x \<in> AA \<and> y \<in> AA \<longrightarrow> g x < g y\<close> \<open>f = g \<circ> length\<close>)
  show ?thesis 
    using \<open>\<forall>x y. length x < length y \<and> x \<in> A \<and> y \<in> A \<longrightarrow> f x < f y\<close> \<open>f ` A = B\<close> by blast
qed

lemma DyckListDCHRlenght:
  \<open>(n::nat) \<ge> 1 \<Longrightarrow> length (DyckListDCHR c (DyckType n)) = sigmaOdd n\<close>
proof-
  assume \<open>(n::nat) \<ge> 1\<close>
  have \<open>DyckPath (DyckType n)\<close> 
    using DyckType2 \<open>1 \<le> n\<close> by auto
  then obtain  \<open>2*length (DyckListDCHR c (DyckType n)) = length (DyckType n)\<close>
    using DyckListDCHRLengthAbstr 
    by simp
  have \<open>length (DyckType n) = 2*(sigmaOdd n)\<close>
    using DyckTypeDivLengthsigmaOdd  \<open>n \<ge> 1\<close> 
    by blast
  then have \<open>2*length (DyckListDCHR c (DyckType n)) = 2*(sigmaOdd n)\<close>
    by (simp add: \<open>2 * length (DyckListDCHR c (DyckType n)) = length (DyckType n)\<close>)
  then have  \<open>length (DyckListDCHR c (DyckType n)) = sigmaOdd n\<close>
    by simp
  then show ?thesis by blast
qed

lemma PrefixInjOnNonEmptyX:
  fixes A::\<open>(DCHR list) set\<close> and w::\<open>DCHR list\<close>
  assumes \<open>\<forall> v. v \<in> A \<longrightarrow> prefix v w \<and> v \<noteq> []\<close> and \<open>w \<noteq> []\<close>
    and \<open>(\<lambda> w. (length w - 1)) a = (\<lambda> w. (length w - 1)) b\<close> 
    and \<open>a \<in> A\<close> and \<open>b \<in> A\<close>
  shows \<open>a = b\<close>
proof-
  from \<open>\<forall> v. v \<in> A \<longrightarrow> prefix v w \<and> v \<noteq> []\<close>
  have \<open>\<forall> v. v \<in> A \<longrightarrow> prefix v w\<close> by blast
  from \<open>\<forall> v. v \<in> A \<longrightarrow> prefix v w \<and> v \<noteq> []\<close>
  have \<open>\<forall> v. v \<in> A \<longrightarrow> v \<noteq> []\<close> by blast
  then have  \<open>\<forall> v. \<exists> u. v \<in> A \<longrightarrow> v = (v!0) # u\<close>
    by (metis assms(1) hd_conv_nth list.discI list.expand list.sel(1) list.sel(3))
  then obtain B where \<open>B = {u | u. \<exists> v. v \<in> A \<and> (v!0)#u = v}\<close>
    by blast
  from  \<open>w \<noteq> []\<close> obtain t where \<open>w = (w!0)#t\<close> 
    by (metis hd_conv_nth list.discI list.expand list.sel(1) list.sel(3))
  from  \<open>w = (w!0)#t\<close>  \<open>B = {u | u. \<exists> v. v \<in> A \<and> (v!0)#u = v}\<close>
  have \<open>\<forall> v. v \<in> B \<longrightarrow> prefix v t\<close>
    by (smt CollectD assms(1) length_greater_0_conv prefixL2 prefix_def)
  then have  \<open>inj_on length B\<close> 
    using PrefixInjOn by blast 
  have \<open>\<forall> v. \<exists> u. v \<in> A \<longrightarrow> length v = length ((v!0)#u)\<close> 
    by (metis \<open>\<forall>v. \<exists>u. v \<in> A \<longrightarrow> v = v ! 0 # u\<close>)
  then have  \<open>\<forall> v. \<exists> u. v \<in> A \<longrightarrow> length v = (length u)+1\<close>
    by (metis Ex_list_of_length Suc_eq_plus1 length_Cons)
  then have  \<open>\<forall> v. \<exists> u. v \<in> A \<longrightarrow> (length v)-1 = length u\<close>
    by (metis add_diff_cancel_right')
  from \<open>(\<lambda> w. (length w - 1)) a = (\<lambda> w. (length w - 1)) b\<close> 
  have \<open>length a - 1 = length b - 1\<close> 
    by blast
  from \<open>a \<in> A\<close> obtain aa where \<open>a = (w!0)#aa\<close> 
    by (metis \<open>w = w ! 0 # t\<close> assms(1) prefixL1)
  from \<open>b \<in> A\<close> obtain bb where \<open>b= (w!0)#bb\<close> 
    by (metis \<open>w = w ! 0 # t\<close> assms(1) prefixL1)
  from  \<open>length a - 1 = length b - 1\<close>  \<open>a = (w!0)#aa\<close>  \<open>b= (w!0)#bb\<close>
  have \<open>length aa = length bb\<close> 
    by simp
  from \<open>a \<in> A\<close>  \<open>a = (w!0)#aa\<close> have \<open>aa \<in> B\<close> 
    using \<open>B = {u |u. \<exists>v. v \<in> A \<and> v ! 0 # u = v}\<close> by fastforce
  from \<open>b \<in> A\<close>  \<open>b = (w!0)#bb\<close> have \<open>bb \<in> B\<close> 
    using \<open>B = {u |u. \<exists>v. v \<in> A \<and> v ! 0 # u = v}\<close> by fastforce
  have \<open>aa = bb\<close> 
    by (meson \<open>aa \<in> B\<close> \<open>bb \<in> B\<close> \<open>inj_on length B\<close> \<open>length aa = length bb\<close> inj_on_def)
  from \<open>aa = bb\<close>  \<open>a = (w!0)#aa\<close>  \<open>b = (w!0)#bb\<close> 
  have \<open>a = b\<close> 
    by blast
  then show ?thesis by blast
qed



lemma PrefixInjOnNonEmpty:
  fixes A::\<open>(DCHR list) set\<close> and w::\<open>DCHR list\<close>
  assumes \<open>\<forall> v. v \<in> A \<longrightarrow> prefix v w \<and> v \<noteq> []\<close> and \<open>w \<noteq> []\<close>
  shows \<open>inj_on (\<lambda> w. (length w - 1)) A\<close> 
  by (metis (no_types, lifting) Nitpick.size_list_simp(2) append_eq_append_conv assms(1) inj_onI length_tl prefixYY)


lemma lengthDyckListDCHRDyckTypeInj:
  \<open>(n::nat) \<ge> 1 \<Longrightarrow> inj_on (\<lambda> w. (length w) - 1 ) (DyckTypeP n)\<close>
  using PrefixInjOnNonEmpty 
  by (smt CollectD DyckTypeP_def Nitpick.size_list_simp(2) append_eq_append_conv inj_onI length_tl prefixYY)

lemma lengthDyckListDCHRDyckTypeSurjAX:
  fixes n :: nat
  assumes \<open>n \<ge> 1\<close> and \<open>w \<in> DyckTypeP n\<close>
  shows \<open>length w - 1 \<in> DyckSetDCHR up (DyckType n)\<close>
  by (smt CollectD CollectI DyckSetDCHR_def DyckTypeP_def assms(2) diff_less last_conv_nth length_greater_0_conv less_le_trans less_numeral_extra(1) prefix_def)


lemma lengthDyckListDCHRDyckTypeSurjBX:
  fixes n k :: nat
  assumes \<open>n \<ge> 1\<close> and \<open>k \<in> DyckSetDCHR up (DyckType n)\<close> 
  shows \<open>\<exists> w. w \<in> DyckTypeP n \<and> length w - 1 = k \<close>
proof-
  have \<open>k+1 \<le> length (DyckType n)\<close> 
    using CollectD DyckSetDCHR_def assms(2) by fastforce
  then obtain w v where \<open>length w = k + 1\<close> and \<open>DyckType n = w @ v\<close>
    by (metis append_Nil2 id_take_nth_drop le_eq_less_or_eq length_take min.absorb2)
  from  \<open>length w = k + 1\<close>
  have  \<open>length w - 1 = k\<close> 
    by simp
  have \<open>length w \<le> length (DyckType n)\<close>
    using \<open>k + 1 \<le> length (DyckType n)\<close> \<open>length w = k + 1\<close> by linarith
  have \<open>\<forall> j. j < length w \<longrightarrow> w!j = (DyckType n)!j\<close>
    by (simp add: \<open>DyckType n = w @ v\<close> nth_append)
  then have \<open>prefix w (DyckType n)\<close> using  \<open>length w \<le> length (DyckType n)\<close> 
    by (simp add: \<open>DyckType n = w @ v\<close> prefixConcat)
  have \<open>w \<noteq> []\<close> 
    using \<open>length w = k + 1\<close> by auto
  have \<open>last w = up\<close> 
    by (metis (mono_tags, lifting) CollectD DyckSetDCHR_def \<open>\<forall>j<length w. w ! j = DyckType n ! j\<close> \<open>length w - 1 = k\<close> \<open>w \<noteq> []\<close> assms(2) diff_less last_conv_nth length_greater_0_conv less_numeral_extra(1))
  have \<open>w \<in> DyckTypeP n\<close> 
    by (simp add: DyckTypeP_def \<open>last w = up\<close> \<open>prefix w (DyckType n)\<close> \<open>w \<noteq> []\<close>)
  show ?thesis 
    using \<open>length w - 1 = k\<close> \<open>w \<in> DyckTypeP n\<close> by blast
qed


lemma lengthDyckListDCHRDyckTypeSurjA:
  \<open>(n::nat) \<ge> 1 \<Longrightarrow> (\<lambda> w. (length w) - 1 ) ` (DyckTypeP n) \<subseteq> (DyckSetDCHR up (DyckType n))\<close>
  using lengthDyckListDCHRDyckTypeSurjAX 
  by blast


lemma lengthDyckListDCHRDyckTypeSurjB:
  \<open>(n::nat) \<ge> 1 \<Longrightarrow> (DyckSetDCHR up (DyckType n)) \<subseteq> (\<lambda> w. (length w) - 1 ) ` (DyckTypeP n)\<close>
  using lengthDyckListDCHRDyckTypeSurjBX 
  by blast


lemma lengthDyckListDCHRDyckTypeSurj:
  \<open>(n::nat) \<ge> 1 \<Longrightarrow> (\<lambda> w. (length w) - 1 ) ` (DyckTypeP n) = (DyckSetDCHR up (DyckType n))\<close>
  using lengthDyckListDCHRDyckTypeSurjA lengthDyckListDCHRDyckTypeSurjB
  by (simp add: set_eq_subset)

lemma lengthDyckListDCHRDyckTypeBij:
  \<open>(n::nat) \<ge> 1 \<Longrightarrow> bij_betw (\<lambda> w. (length w) - 1 ) (DyckTypeP n) (DyckSetDCHR up (DyckType n))\<close>
  using lengthDyckListDCHRDyckTypeInj lengthDyckListDCHRDyckTypeSurj 
  by (simp add: bij_betw_def)

lemma lengthDyckListDCHRDyckType:
  \<open>(n::nat) \<ge> 1 \<Longrightarrow> card (DyckSetDCHR up (DyckType n)) = card (DyckTypeP n)\<close>
proof-
  assume \<open>(n::nat) \<ge> 1\<close>
  have \<open>finite (DyckSetDCHR up (DyckType n))\<close>
    by (simp add: DyckSetDCHRFIN)
  have \<open>finite (DyckTypeP n)\<close>
    by (metis (no_types, lifting) DyckTypeP_def PrefixLength mem_Collect_eq)
  from \<open>n \<ge> 1\<close> have \<open>bij_betw (\<lambda> w. (length w) - 1 ) (DyckTypeP n) (DyckSetDCHR up (DyckType n))\<close>
    using lengthDyckListDCHRDyckTypeBij by blast
  then show ?thesis using \<open>finite (DyckTypeP n)\<close> \<open>finite (DyckSetDCHR up (DyckType n))\<close>
    by (simp add: bij_betw_same_card)
qed


lemma cardDyckTypeP:
  \<open>(n::nat) \<ge> 1 \<Longrightarrow> card (DyckTypeP n) = sigmaOdd n\<close>
proof-
  assume \<open>(n::nat) \<ge> 1\<close>
  then have \<open>length (DyckListDCHR up (DyckType n)) = sigmaOdd n\<close>
    using DyckListDCHRlenght by blast
  then have  \<open>card (DyckSetDCHR up (DyckType n)) = sigmaOdd n\<close>
    by (simp add: DyckListDCHR_def DyckSetDCHR_def FinSetToListCard)
  then show ?thesis using lengthDyckListDCHRDyckType \<open>n \<ge> 1\<close>
    by auto
qed

lemma ListEqCardPrefixDyckQ:
  fixes n::nat  
  assumes \<open>n \<ge> 1\<close>
  shows  \<open>\<exists> f::(DCHR list)\<Rightarrow>nat. f ` (DyckTypeP n) = (ODiv n) \<and> (\<forall> x y. length x < length y \<and> x \<in> (DyckTypeP n) \<and> y \<in> (DyckTypeP n) \<longrightarrow> f x < f y)\<close>
proof-
  have \<open>\<forall> d::nat. d dvd n \<longrightarrow> d \<le> n\<close> using \<open>n \<ge> 1\<close> 
    by auto
  then have \<open>ODiv n  \<subseteq> {d | d :: nat. d \<le> n}\<close>
    by (simp add: Collect_mono ODiv_def)
  then have \<open>finite (ODiv n)\<close> 
    by (simp add: finite_subset)
  have \<open>\<forall> v. v \<in> DyckTypeP n \<longrightarrow> prefix v (DyckType n)\<close>
    using CollectD DyckTypeP_def by fastforce
  have \<open>card (DyckTypeP n) = card (ODiv n)\<close> 
    using assms cardDyckTypeP sigmaOdd_def by presburger
  obtain f where \<open>f ` (DyckTypeP n) = (ODiv n)\<close> and \<open>\<forall> x y. length x < length y \<and> x \<in> (DyckTypeP n) \<and> y \<in> (DyckTypeP n) \<longrightarrow> f x < f y\<close>
    using ListEqCardPrefix 
    by (metis \<open>\<forall>v. v \<in> DyckTypeP n \<longrightarrow> prefix v (DyckType n)\<close> \<open>card (DyckTypeP n) = card (ODiv n)\<close> \<open>finite (ODiv n)\<close>)
  from  \<open>f ` (DyckTypeP n) = (ODiv n)\<close>  \<open>\<forall> x y. length x < length y \<and> x \<in> (DyckTypeP n) \<and> y \<in> (DyckTypeP n) \<longrightarrow> f x < f y\<close>
  show ?thesis 
    by blast
qed

lemma ListEqCardPrefixDyck:
  \<open>\<forall> n::nat. \<exists> f::(DCHR list)\<Rightarrow>nat. n \<ge> 1 \<longrightarrow>  f ` (DyckTypeP n) = (ODiv n) \<and> (\<forall> x y. length x < length y \<and> x \<in> (DyckTypeP n) \<and> y \<in> (DyckTypeP n) \<longrightarrow> f x < f y) \<close>
  using ListEqCardPrefixDyckQ by blast

theorem ListEqCardPrefixDyckFun:
  \<open>\<exists> F :: nat\<Rightarrow>((DCHR list)\<Rightarrow>nat). \<forall> n::nat. n \<ge> 1 \<longrightarrow> (F n) ` (DyckTypeP n) = (ODiv n) \<and> (\<forall> x y. length x < length y \<and> x \<in> (DyckTypeP n) \<and> y \<in> (DyckTypeP n) \<longrightarrow> (F n) x < (F n) y)\<close>
  using ListEqCardPrefixDyck  by metis


end


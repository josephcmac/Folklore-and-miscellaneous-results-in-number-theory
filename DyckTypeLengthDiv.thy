(*
Title: Number theoretic interpretation of the length of the Dyck path
Author: Jose Manuel Rodriguez Caballero

We prove the following result.

proposition DyckTypeDivLengthArithmFun : 
\<open>ArithmFun (\<lambda> w. length w) \<doteq> (\<lambda> n. 2*(card {d | d :: nat. d dvd n \<and> odd d}))\<close>

(This code  was verified in Isabelle2018)
*)


theory DyckTypeLengthDiv

imports Complex_Main fromNumberTheoryToLanguageTheory

begin

lemma DyckTypeDivLengthJsignsARec: 
  assumes \<open> length ( SchroederToDyck w ) = (card {j | j :: nat. j < length w \<and> w ! j \<noteq> STRANGE})\<close>
  shows \<open> length ( SchroederToDyck (a # w) ) = (card {j | j :: nat. j < length (a # w) \<and> (a # w) ! j \<noteq> STRANGE})\<close>
proof(cases \<open>a = STRANGE\<close>)
  case True
  have \<open> SchroederToDyck (a # w)  =  SchroederToDyck w \<close> 
    by (simp add: SchroederToDyckCode_def True)
  have \<open> {j | j :: nat. j < length (a # w) \<and> (a # w) ! j \<noteq> STRANGE} =  {j | j :: nat. j \<noteq> 0 \<and> j < length (a # w) \<and> (a # w) ! j \<noteq> STRANGE}\<close>
    by (metis True nth_Cons_0)
  then have \<open> {j | j :: nat. j < length (a # w) \<and> (a # w) ! j \<noteq> STRANGE} =  {j | j :: nat. j \<noteq> 0 \<and> j < Suc (length  w) \<and> (a # w) ! j \<noteq> STRANGE}\<close>
    by simp
  then have \<open> {j | j :: nat. j < length (a # w) \<and> (a # w) ! j \<noteq> STRANGE} =  {Suc j | j :: nat. Suc j < Suc (length  w) \<and> (a # w) ! (Suc j) \<noteq> STRANGE}\<close>
    using True less_Suc_eq_0_disj less_irrefl by fastforce
  then have \<open> {j | j :: nat. j < length (a # w) \<and> (a # w) ! j \<noteq> STRANGE} =  {Suc j | j :: nat.  j <  (length  w) \<and> (a # w) ! (Suc j) \<noteq> STRANGE}\<close>
    by simp
  have \<open>inj Suc\<close> 
    by simp
  have \<open>Suc ` { j | j :: nat.  j <  (length  w) \<and>  w ! j \<noteq> STRANGE} = { Suc j | j :: nat.  j <  (length  w) \<and>  w ! j \<noteq> STRANGE}\<close>
    by blast
  have \<open>bij_betw Suc { j | j :: nat.  j <  (length  w) \<and>  w ! j \<noteq> STRANGE} { Suc j | j :: nat.  j <  (length  w) \<and>  w ! j \<noteq> STRANGE}\<close>
    by auto
  then have \<open>card { j | j :: nat.  j <  (length  w) \<and>  w ! j \<noteq> STRANGE} = card { Suc j | j :: nat.  j <  (length  w) \<and>  w ! j \<noteq> STRANGE}\<close>
    using bij_betw_same_card by blast
  then have \<open>card {j | j :: nat. j < length (a # w) \<and> (a # w) ! j \<noteq> STRANGE} =  card { j | j :: nat.  j <  (length  w) \<and>  w ! j \<noteq> STRANGE}\<close>
    using \<open>{j |j. j < length (a # w) \<and> (a # w) ! j \<noteq> STRANGE} = {Suc j |j. j < length w \<and> (a # w) ! Suc j \<noteq> STRANGE}\<close> nth_Cons_Suc by auto
  then show ?thesis 
    using \<open>SchroederToDyck (a # w) = SchroederToDyck w\<close> assms by auto
next
  case False
  obtain b where  \<open> SchroederToDyck (a # w)  =  b # SchroederToDyck w \<close>
    using False SchroederToDyckCode_def
    by (metis (full_types) SCHR.exhaust SchroederToDyck.simps(2) append.left_neutral append_Cons)
  have \<open> {j | j :: nat. j < length (a # w) \<and> (a # w) ! j \<noteq> STRANGE} =  {j | j :: nat. j = 0 \<and> j < length (a # w) \<and> (a # w) ! j \<noteq> STRANGE} \<union> {j | j :: nat. j \<noteq> 0 \<and> j < length (a # w) \<and> (a # w) ! j \<noteq> STRANGE}\<close>
    by force
  then have  \<open> {j | j :: nat. j < length (a # w) \<and> (a # w) ! j \<noteq> STRANGE} =  {(0::nat)} \<union> {j | j :: nat. j \<noteq> 0 \<and> j < length (a # w) \<and> (a # w) ! j \<noteq> STRANGE}\<close>
    using False by force
  have \<open> {(0::nat)} \<inter> {j | j :: nat. j \<noteq> 0 \<and> j < length (a # w) \<and> (a # w) ! j \<noteq> STRANGE} = {}\<close> 
    by blast
  have \<open>finite {j | j :: nat. j \<noteq> 0 \<and> j < length (a # w) \<and> (a # w) ! j \<noteq> STRANGE}\<close>
    by simp
  have \<open>finite {(0::nat)}\<close> by simp
  have  \<open>card ({(0::nat)} \<union> {j | j :: nat. j \<noteq> 0 \<and> j < length (a # w) \<and> (a # w) ! j \<noteq> STRANGE}) =  (card {(0::nat)}) + (card {j | j :: nat. j \<noteq> 0 \<and> j < length (a # w) \<and> (a # w) ! j \<noteq> STRANGE})\<close>
    using  \<open> {(0::nat)} \<inter> {j | j :: nat. j \<noteq> 0 \<and> j < length (a # w) \<and> (a # w) ! j \<noteq> STRANGE} = {}\<close> 
    by auto
  have  \<open>card {j | j :: nat. j < length (a # w) \<and> (a # w) ! j \<noteq> STRANGE} =  card {(0::nat)} + card {j | j :: nat. j \<noteq> 0 \<and> j < length (a # w) \<and> (a # w) ! j \<noteq> STRANGE}\<close>
    using \<open>card ({0} \<union> {j |j. j \<noteq> 0 \<and> j < length (a # w) \<and> (a # w) ! j \<noteq> STRANGE}) = card {0} + card {j |j. j \<noteq> 0 \<and> j < length (a # w) \<and> (a # w) ! j \<noteq> STRANGE}\<close> \<open>{j |j. j < length (a # w) \<and> (a # w) ! j \<noteq> STRANGE} = {0} \<union> {j |j. j \<noteq> 0 \<and> j < length (a # w) \<and> (a # w) ! j \<noteq> STRANGE}\<close> by presburger
  then have \<open>card {j | j :: nat. j < length (a # w) \<and> (a # w) ! j \<noteq> STRANGE} =  1 + card {j | j :: nat. j \<noteq> 0 \<and> j < length (a # w) \<and> (a # w) ! j \<noteq> STRANGE}\<close>
    by simp

  have \<open> {j | j :: nat. j \<noteq> 0 \<and> j < length (a # w) \<and> (a # w) ! j \<noteq> STRANGE} =  {Suc j | j :: nat. Suc j < Suc (length  w) \<and> (a # w) ! (Suc j) \<noteq> STRANGE}\<close>
    using  less_Suc_eq_0_disj less_irrefl by fastforce
  then have \<open> {j | j :: nat. j \<noteq> 0 \<and>  j < length (a # w) \<and> (a # w) ! j \<noteq> STRANGE} =  {Suc j | j :: nat.  j <  (length  w) \<and> (a # w) ! (Suc j) \<noteq> STRANGE}\<close>
    by simp
  have \<open>inj Suc\<close> 
    by simp
  have \<open>Suc ` { j | j :: nat. j \<noteq> 0 \<and>  j <  (length  w) \<and>  w ! j \<noteq> STRANGE} = { Suc j | j :: nat.  j \<noteq> 0 \<and> j <  (length  w) \<and>  w ! j \<noteq> STRANGE}\<close>
    by blast
  have \<open>bij_betw Suc { j | j :: nat.  j <  (length  w) \<and>  w ! j \<noteq> STRANGE} { Suc j | j :: nat.  j <  (length  w) \<and>  w ! j \<noteq> STRANGE}\<close>
    by auto
  then have \<open>card { j | j :: nat.  j <  (length  w) \<and>  w ! j \<noteq> STRANGE} = card { Suc j | j :: nat.  j <  (length  w) \<and>  w ! j \<noteq> STRANGE}\<close>
    using bij_betw_same_card by blast
  then have \<open>card {j | j :: nat. j < length (a # w) \<and> (a # w) ! j \<noteq> STRANGE} =  1+card { j | j :: nat.  j <  (length  w) \<and>  w ! j \<noteq> STRANGE}\<close>
    by (smt Collect_cong \<open>card {j |j. j < length (a # w) \<and> (a # w) ! j \<noteq> STRANGE} = 1 + card {j |j. j \<noteq> 0 \<and> j < length (a # w) \<and> (a # w) ! j \<noteq> STRANGE}\<close> length_Cons less_Suc_eq_0_disj nth_Cons_Suc order_less_irrefl)
  then show ?thesis 
    using \<open>SchroederToDyck (a # w) = b # SchroederToDyck w\<close> assms by auto
qed

lemma DyckTypeDivLengthJsignsA: 
  \<open> length ( SchroederToDyck w ) = (card {j | j :: nat. j < length w \<and> w ! j \<noteq> STRANGE})\<close>
proof(induction w)
  case Nil
  then show ?case 
    by simp
next
  case (Cons a w)
  then show ?case 
    using DyckTypeDivLengthJsignsARec by auto
qed

lemma DyckTypeDivLengthJsignsB: 
  \<open>n \<ge> 1 \<Longrightarrow>  WordToFun w = Jsigns n  \<Longrightarrow> (card {j | j :: nat. j < length w \<and> w ! j \<noteq> STRANGE}) = (card {j | j :: nat. (Jsigns n) j \<noteq> 0})\<close>
proof-
  assume \<open>n \<ge> 1\<close>
  assume \<open>WordToFun w = Jsigns n\<close>
  have \<open>\<forall> j. j < length w \<longrightarrow> (w ! j \<noteq> STRANGE \<longleftrightarrow> (WordToFun w) j \<noteq> 0)\<close> 
    by (smt SCHR.distinct(3) SCHR.distinct(5) SCHR.exhaust SchroederCode_def WordToFun_def)
  then have \<open>\<forall> j. j < length w \<longrightarrow> (w ! j \<noteq> STRANGE \<longleftrightarrow> (Jsigns n) j \<noteq> 0)\<close>
    using \<open>WordToFun w = Jsigns n\<close> 
    by simp
  have \<open>\<forall> j. j \<ge>  length w \<longrightarrow> ((Jsigns n) j = 0)\<close> using \<open>WordToFun w = Jsigns n\<close>
    by (metis WordToFun_def leD)
  have \<open>{j | j :: nat. j < length w \<and> w ! j \<noteq> STRANGE} = {j | j :: nat. (Jsigns n) j \<noteq> 0}\<close>
    using  \<open>\<forall> j. j < length w \<longrightarrow> (w ! j \<noteq> STRANGE \<longleftrightarrow> (Jsigns n) j \<noteq> 0)\<close>
      \<open>\<forall> j. j \<ge>  length w \<longrightarrow> ((Jsigns n) j = 0)\<close>
    by (metis WordToFun_def \<open>WordToFun w = Jsigns n\<close>)   
  show ?thesis 
    using \<open>{j |j. j < length w \<and> w ! j \<noteq> STRANGE} = {j |j. Jsigns n j \<noteq> 0}\<close> by auto
qed

lemma DyckTypeDivLengthJsigns: 
  \<open>n \<ge> 1 \<Longrightarrow> length (DyckType n) = (card {j | j :: nat. (Jsigns n) j \<noteq> 0})\<close>
proof-
  assume \<open>n \<ge> 1\<close>
  obtain w where \<open> DyckType n = SchroederToDyck w\<close> and \<open>WordToFun w = Jsigns n \<close>
    by (smt DyckClass_def DyckType1 \<open>1 \<le> n\<close> mem_Collect_eq)
  from  \<open>n \<ge> 1\<close> \<open> DyckType n = SchroederToDyck w\<close>  \<open>WordToFun w = Jsigns n \<close>
  have \<open> length (DyckType n) = (card {j | j :: nat. j < length w \<and> w ! j \<noteq> STRANGE}) \<close>
    using DyckTypeDivLengthJsignsA by auto
  then show ?thesis 
    using DyckTypeDivLengthJsignsB \<open>1 \<le> n\<close> \<open>WordToFun w = Jsigns n\<close> by auto
qed

lemma fromJsignsToJdvdBijXAL:
  \<open>n \<ge> 1 \<Longrightarrow>  (Jsigns n) j \<noteq> 0 \<Longrightarrow>  Jdvd (Suc j) n\<close>
  using SchroederArithmL2X2Y2 by blast

lemma fromJsignsToJdvdBijXA:
  \<open>n \<ge> 1 \<Longrightarrow>  Suc ` {j | j :: nat. (Jsigns n) j \<noteq> 0} \<subseteq> {d | d :: nat. Jdvd d n}\<close>
  using fromJsignsToJdvdBijXAL 
  by blast

lemma fromJsignsToJdvdBijXBL:
  \<open>n \<ge> 1 \<Longrightarrow>  Jdvd d n \<Longrightarrow> \<exists> j. (Jsigns n) j \<noteq> 0 \<and> d = Suc j\<close>
  by (smt Jdvd_def Jsigns_def Suc_1 less_Suc_eq_0_disj linorder_cases mult_eq_0_iff nat_0_less_mult_iff no_zero_divisors not_gr_zero not_le not_less_eq_eq not_one_le_zero old.nat.distinct(2) old.nat.exhaust order_class.order.antisym times_nat.simps(1) zero_less_Suc zero_neq_neg_one zero_neq_one)

lemma fromJsignsToJdvdBijXB:
  \<open>n \<ge> 1 \<Longrightarrow>  {d | d :: nat. Jdvd d n} \<subseteq>  Suc ` {j | j :: nat. (Jsigns n) j \<noteq> 0}\<close>
  using fromJsignsToJdvdBijXBL 
  by auto

lemma fromJsignsToJdvdBijX:
  \<open>n \<ge> 1 \<Longrightarrow>  Suc ` {j | j :: nat. (Jsigns n) j \<noteq> 0} = {d | d :: nat. Jdvd d n}\<close>
  using fromJsignsToJdvdBijXA fromJsignsToJdvdBijXB by fastforce

lemma fromJsignsToJdvdBijY:
  \<open>inj Suc\<close>
  by simp

lemma fromJsignsToJdvdBij:
  \<open>n \<ge> 1 \<Longrightarrow> bij_betw Suc {j | j :: nat. (Jsigns n) j \<noteq> 0} {d | d :: nat. Jdvd d n}\<close>
  using fromJsignsToJdvdBijX by auto

lemma fromJsignsToJdvd:
  \<open>n \<ge> 1 \<Longrightarrow> (card {j | j :: nat. (Jsigns n) j \<noteq> 0}) = (card {d | d :: nat. Jdvd d n})\<close>
  using fromJsignsToJdvdBij 
  by (meson bij_betw_same_card)


lemma fromJdvdToDvdX1A:
  \<open>n \<ge> 1 \<Longrightarrow>  {d | d :: nat. Jdvd d n} \<subseteq> {d | d :: nat. \<exists> e. d*e = 2*n \<and> odd d} \<union> {d | d :: nat. \<exists> e. d*e = 2*n \<and> odd e}\<close>
  by (smt Jdvd_def UnCI mem_Collect_eq subsetI)

lemma prefromJdvdToDvdX1B:
  \<open>n \<ge> 1 \<Longrightarrow> {d | d :: nat. (\<exists> e. d*e = 2*n \<and> (odd d \<or> odd e)) } \<subseteq>  {d | d :: nat. Jdvd d n}\<close>
  by (simp add: Jdvd_def)


lemma fromJdvdToDvdX1B:
  \<open>n \<ge> 1 \<Longrightarrow> {d | d :: nat. \<exists> e. d*e = 2*n \<and> odd d} \<union> {d | d :: nat. \<exists> e. d*e = 2*n \<and> odd e} \<subseteq>  {d | d :: nat. Jdvd d n}\<close>
  using prefromJdvdToDvdX1B Un_iff by blast


lemma fromJdvdToDvdX1:
  \<open>n \<ge> 1 \<Longrightarrow>  {d | d :: nat. Jdvd d n} = {d | d :: nat. \<exists> e. d*e = 2*n \<and> odd d} \<union> {d | d :: nat. \<exists> e. d*e = 2*n \<and> odd e}\<close>
proof-
  assume \<open>n \<ge> 1\<close>
  then have \<open> {d | d :: nat. \<exists> e. d*e = 2*n \<and> odd d} \<union> {d | d :: nat. \<exists> e. d*e = 2*n \<and> odd e} \<subseteq>  {d | d :: nat. Jdvd d n}\<close>
    using fromJdvdToDvdX1B by blast
  from \<open>n \<ge> 1\<close> 
  have \<open>{d | d :: nat. Jdvd d n} \<subseteq> {d | d :: nat. \<exists> e. d*e = 2*n \<and> odd d} \<union> {d | d :: nat. \<exists> e. d*e = 2*n \<and> odd e}\<close>
    using fromJdvdToDvdX1A by blast
  from  \<open> {d | d :: nat. \<exists> e. d*e = 2*n \<and> odd d} \<union> {d | d :: nat. \<exists> e. d*e = 2*n \<and> odd e} \<subseteq>  {d | d :: nat. Jdvd d n}\<close>
    \<open>{d | d :: nat. Jdvd d n} \<subseteq> {d | d :: nat. \<exists> e. d*e = 2*n \<and> odd d} \<union> {d | d :: nat. \<exists> e. d*e = 2*n \<and> odd e}\<close>
  show ?thesis 
    by blast
qed

lemma fromJdvdToDvdX2:
  \<open>n \<ge> 1 \<Longrightarrow>   {d | d :: nat. \<exists> e. d*e = 2*n \<and> odd d} \<inter> {d | d :: nat. \<exists> e. d*e = 2*n \<and> odd e} = {}\<close>
  by (smt Int_emptyI dvd_triv_left even_mult_iff mem_Collect_eq) 

definition DivEx :: \<open>nat \<Rightarrow> (nat \<Rightarrow> nat)\<close> where
  \<open>DivEx \<equiv> \<lambda> n. (\<lambda> d. ((2*n) div d))\<close>

lemma prefromJdvdToDvdX3Inj:
  \<open>n \<ge> 1 \<Longrightarrow> x \<in> {d | d :: nat. \<exists> e. d*e = 2*n \<and> odd d}
 \<Longrightarrow>  y \<in> {d | d :: nat. \<exists> e. d*e = 2*n \<and> odd d}
\<Longrightarrow> (DivEx n) x = (DivEx n) y \<Longrightarrow> x = y\<close>
proof-
  assume \<open>n \<ge> 1\<close>
  assume \<open>x \<in> {d | d :: nat. \<exists> e. d*e = 2*n \<and> odd d}\<close>
  assume \<open>y \<in> {d | d :: nat. \<exists> e. d*e = 2*n \<and> odd d}\<close>
  assume \<open>(DivEx n) x = (DivEx n) y\<close>
  obtain ex where \<open>x*ex = 2*n\<close> and \<open>odd x\<close> using  \<open>x \<in> {d | d :: nat. \<exists> e. d*e = 2*n \<and> odd d}\<close> by blast
  obtain ey where \<open>y*ey = 2*n\<close> and \<open>odd y\<close> using  \<open>y \<in> {d | d :: nat. \<exists> e. d*e = 2*n \<and> odd d}\<close> by blast
  from \<open>(DivEx n) x = (DivEx n) y\<close> have \<open>ex = ey\<close> 
    by (metis DivEx_def One_nat_def \<open>\<And>thesis. (\<And>ex. \<lbrakk>x * ex = 2 * n; odd x\<rbrakk> \<Longrightarrow> thesis) \<Longrightarrow> thesis\<close> \<open>\<And>thesis. (\<And>ey. \<lbrakk>y * ey = 2 * n; odd y\<rbrakk> \<Longrightarrow> thesis) \<Longrightarrow> thesis\<close> \<open>x * ex = 2 * n\<close> \<open>y * ey = 2 * n\<close> even_Suc nonzero_mult_div_cancel_left odd_one)
  have \<open>ex \<noteq> 0\<close> using  \<open>x*ex = 2*n\<close> \<open>n \<ge> 1\<close>
    using not_one_le_zero by fastforce
  have \<open>ey \<noteq> 0\<close> using  \<open>y*ey = 2*n\<close> \<open>n \<ge> 1\<close>
    using not_one_le_zero by fastforce
  have \<open>x = y\<close> using \<open>ex \<noteq> 0\<close> \<open>ey \<noteq> 0\<close>  \<open>x*ex = 2*n\<close>  \<open>y*ey = 2*n\<close>
    by (metis \<open>ex = ey\<close> mult_cancel_right)
  then show ?thesis by blast
qed

lemma fromJdvdToDvdX3Inj:
  \<open>n \<ge> 1 \<Longrightarrow> inj_on  (DivEx n)  {d | d :: nat. \<exists> e. d*e = 2*n \<and> odd d}\<close>
proof-
  assume \<open>n \<ge> 1\<close>
  then have \<open> \<forall> x \<in> {d | d :: nat. \<exists> e. d*e = 2*n \<and> odd d}. 
\<forall> y \<in> {d | d :: nat. \<exists> e. d*e = 2*n \<and> odd d}. 
(DivEx n) x = (DivEx n) y \<longrightarrow> x = y \<close>
    by (metis (mono_tags, lifting)  prefromJdvdToDvdX3Inj)
  then show ?thesis 
    by (meson inj_onI)
qed

lemma prefromJdvdToDvdX3OntoXSL:
  \<open>n \<ge> 1 \<Longrightarrow>  \<exists> e. d*e = 2*n \<and> odd d \<Longrightarrow>  \<exists> e.  e*( (DivEx n) d ) = 2*n \<and> odd e\<close>
proof-
  assume \<open>n \<ge> 1\<close>
  assume \<open> \<exists> e. d*e = 2*n \<and> odd d \<close>
  then obtain e where  \<open>d*e = 2*n\<close> and \<open>odd d\<close>
    by blast
  from  \<open>d*e = 2*n\<close> have \<open>(DivEx n) d = e\<close> 
    by (metis DivEx_def One_nat_def \<open>\<exists>e. d * e = 2 * n \<and> odd d\<close> even_Suc nonzero_mult_div_cancel_left odd_one)
  then show ?thesis 
    using \<open>d * e = 2 * n\<close> \<open>odd d\<close> by blast
qed

lemma prefromJdvdToDvdX3OntoXS:
  \<open>n \<ge> 1 \<Longrightarrow>  d \<in>  {d | d :: nat. \<exists> e. d*e = 2*n \<and> odd d} \<Longrightarrow> (DivEx n) d \<in> {d | d :: nat. \<exists> e. d*e = 2*n \<and> odd e}\<close>
  using prefromJdvdToDvdX3OntoXSL 
  by (smt mem_Collect_eq mult.commute)

lemma prefromJdvdToDvdX3OntoX:
  \<open>n \<ge> 1 \<Longrightarrow>  (DivEx n) `  {d | d :: nat. \<exists> e. d*e = 2*n \<and> odd d} \<subseteq> {d | d :: nat. \<exists> e. d*e = 2*n \<and> odd e}\<close>
  using prefromJdvdToDvdX3OntoXS by blast


lemma prefromJdvdToDvdX3OntoYSL:
  \<open>n \<ge> 1 \<Longrightarrow>  \<exists> e. d*e = 2*n \<and> odd e \<Longrightarrow>  \<exists> dd::nat. d = (DivEx n) dd \<and>  (\<exists> e. dd*e = 2*n) \<and> odd dd\<close>
proof-
  assume \<open>n \<ge> 1\<close>
  assume \<open> \<exists> e. d*e = 2*n \<and> odd e\<close>
  then obtain dd where \<open>d*dd = 2*n\<close> and \<open>odd dd\<close> by blast
  have \<open>d = (DivEx n) dd\<close> 
    by (metis DivEx_def \<open>1 \<le> n\<close> \<open>d * dd = 2 * n\<close> linorder_not_le mult.commute mult_eq_0_iff nonzero_mult_div_cancel_left rel_simps(68) rel_simps(76))
  have \<open>odd dd\<close> 
    by (simp add: \<open>odd dd\<close>)
  have \<open>(\<exists> e. dd*e = 2*n)\<close> 
    by (metis \<open>d * dd = 2 * n\<close> semiring_normalization_rules(7))
  have \<open> d = (DivEx n) dd \<and>  (\<exists> e. dd*e = 2*n) \<and> odd dd \<close> using \<open>d = (DivEx n) dd\<close> \<open>(\<exists> e. dd*e = 2*n)\<close> \<open>odd dd\<close> 
    by blast
  then show ?thesis by blast
qed

lemma prefromJdvdToDvdX3OntoYSXXX:
  \<open>n \<ge> 1 \<Longrightarrow>  \<exists> e. d*e = 2*n \<and> odd e \<Longrightarrow> \<exists> dd. d =  (DivEx n) dd \<and> (\<exists> e. dd*e = 2*n) \<and> odd dd \<close>
  using prefromJdvdToDvdX3OntoYSL by blast

lemma prefromJdvdToDvdX3OntoYSXX:
  \<open>n \<ge> 1 \<Longrightarrow>  \<exists> e. d*e = 2*n \<and> odd e \<Longrightarrow> \<exists> dd. d =  (DivEx n) dd \<and> dd \<in>  {d | d :: nat. \<exists> e. d*e = 2*n \<and> odd d}\<close>
  using prefromJdvdToDvdX3OntoYSXXX by auto

lemma prefromJdvdToDvdX3OntoYSX:
  \<open>n \<ge> 1 \<Longrightarrow>  \<exists> e. d*e = 2*n \<and> odd e \<Longrightarrow> d \<in>  (DivEx n) `  {d | d :: nat. \<exists> e. d*e = 2*n \<and> odd d}\<close>
  using prefromJdvdToDvdX3OntoYSXX 
  by fastforce

lemma prefromJdvdToDvdX3OntoYS:
  \<open>n \<ge> 1 \<Longrightarrow> d \<in> {d | d :: nat. \<exists> e. d*e = 2*n \<and> odd e} \<Longrightarrow> d \<in>  (DivEx n) `  {d | d :: nat. \<exists> e. d*e = 2*n \<and> odd d}\<close>
  using prefromJdvdToDvdX3OntoYSX by blast


lemma prefromJdvdToDvdX3OntoY:
  \<open>n \<ge> 1 \<Longrightarrow> {d | d :: nat. \<exists> e. d*e = 2*n \<and> odd e} \<subseteq>  (DivEx n) `  {d | d :: nat. \<exists> e. d*e = 2*n \<and> odd d}\<close>
  using prefromJdvdToDvdX3OntoYS by blast

lemma fromJdvdToDvdX3Onto:
  \<open>n \<ge> 1 \<Longrightarrow>  (DivEx n) `  {d | d :: nat. \<exists> e. d*e = 2*n \<and> odd d} = {d | d :: nat. \<exists> e. d*e = 2*n \<and> odd e}\<close>
  using prefromJdvdToDvdX3OntoX prefromJdvdToDvdX3OntoY 
  by (meson subset_antisym)


lemma fromJdvdToDvdX3:
  \<open>n \<ge> 1 \<Longrightarrow> bij_betw  (DivEx n)  {d | d :: nat. \<exists> e. d*e = 2*n \<and> odd d} {d | d :: nat. \<exists> e. d*e = 2*n \<and> odd e}\<close>
  using  fromJdvdToDvdX3Inj fromJdvdToDvdX3Onto 
  using inj_on_imp_bij_betw by fastforce

lemma fromJdvdToDvdX4:
  \<open>n \<ge> 1 \<Longrightarrow> card {d | d :: nat. \<exists> e. d*e = 2*n \<and> odd d} = card {d | d :: nat. \<exists> e. d*e = 2*n \<and> odd e}\<close>
  using fromJdvdToDvdX3  by (meson bij_betw_same_card)


lemma fromJdvdToDvdX5AX:
  \<open>n \<ge> 1 \<Longrightarrow> (d dvd 2*n \<and> odd d) \<Longrightarrow> (d dvd n \<and> odd d)\<close>
  by (smt dvd_div_mult dvd_div_mult_self dvd_triv_left dvd_triv_right even_mult_iff nonzero_mult_div_cancel_left rel_simps(76))

lemma fromJdvdToDvdX5AY:
  \<open>n \<ge> 1\<Longrightarrow> (d dvd n \<and> odd d) \<Longrightarrow> (d dvd 2*n \<and> odd d) \<close>
  by simp

lemma fromJdvdToDvdX5A:
  \<open>n \<ge> 1 \<Longrightarrow> (\<exists> e. d*e = 2*n \<and> odd d) \<longleftrightarrow> (d dvd n \<and> odd d)\<close>
  using fromJdvdToDvdX5AX fromJdvdToDvdX5AY 
  by (metis dvd_def  dvd_triv_left )

lemma fromJdvdToDvdX5:
  \<open>n \<ge> 1 \<Longrightarrow> card {d | d :: nat. \<exists> e. d*e = 2*n \<and> odd d} = card {d | d :: nat. d dvd n \<and> odd d}\<close>
  by (meson fromJdvdToDvdX5A)

lemma JdvdBound: 
  \<open>n \<ge> 1 \<Longrightarrow>  Jdvd d n \<Longrightarrow> d \<le> 2*n\<close>
  by (metis Jdvd_def dvd_imp_le dvd_triv_left less_le_trans nat_0_less_mult_iff pos2 rel_simps(68))

lemma fromJdvdToDvdF1: 
  \<open>n \<ge> 1 \<Longrightarrow>  finite {d | d :: nat. Jdvd d n}\<close>
  using JdvdBound 
  by (metis (no_types, lifting)    finite_nat_set_iff_bounded_le  mem_Collect_eq )

lemma fromJdvdToDvd:
  \<open>n \<ge> 1 \<Longrightarrow> (card {d | d :: nat. Jdvd d n}) = 2*(card {d | d :: nat. d dvd n \<and> odd d})\<close>
proof-
  assume \<open>n \<ge> 1\<close>
  have  \<open>finite {d | d :: nat. Jdvd d n}\<close> 
    using \<open>1 \<le> n\<close> fromJdvdToDvdF1 by auto
  have \<open>{d | d :: nat. \<exists> e. d*e = 2*n \<and> odd d} \<inter> {d | d :: nat. \<exists> e. d*e = 2*n \<and> odd e} = {}\<close>
    by (smt disjoint_iff_not_equal dvd_triv_left even_mult_iff mem_Collect_eq)
  have \<open> {d | d :: nat. Jdvd d n} = {d | d :: nat. \<exists> e. d*e = 2*n \<and> odd d} \<union> {d | d :: nat. \<exists> e. d*e = 2*n \<and> odd e}\<close>
    using \<open>1 \<le> n\<close> fromJdvdToDvdX1 by auto
  then have  \<open>card {d | d :: nat. Jdvd d n} = card {d | d :: nat. \<exists> e. d*e = 2*n \<and> odd d} + card {d | d :: nat. \<exists> e. d*e = 2*n \<and> odd e}\<close>
    using \<open>{d | d :: nat. \<exists> e. d*e = 2*n \<and> odd d} \<inter> {d | d :: nat. \<exists> e. d*e = 2*n \<and> odd e} = {}\<close> \<open>finite {d | d :: nat. Jdvd d n}\<close> 
    by (simp add: card_Un_disjoint)
  have \<open>card {d | d :: nat. \<exists> e. d*e = 2*n \<and> odd d} = card {d | d :: nat. \<exists> e. d*e = 2*n \<and> odd e}\<close>
    using fromJdvdToDvdX4 \<open>n \<ge> 1\<close> by blast
  then have  \<open>card {d | d :: nat. Jdvd d n} = 2*card {d | d :: nat. \<exists> e. d*e = 2*n \<and> odd d}\<close> using  \<open>card {d | d :: nat. Jdvd d n} = card {d | d :: nat. \<exists> e. d*e = 2*n \<and> odd d} + card {d | d :: nat. \<exists> e. d*e = 2*n \<and> odd e}\<close>
    by linarith
  then show ?thesis 
    by (smt Collect_cong \<open>1 \<le> n\<close> fromJdvdToDvdX5)
qed

lemma DyckTypeDivLength: 
  \<open>n \<ge> 1 \<Longrightarrow> length (DyckType n) = 2*(card {d | d :: nat. d dvd n \<and> odd d})\<close>
  using fromJdvdToDvd fromJsignsToJdvd DyckTypeDivLengthJsigns
  by auto

definition sigmaOdd :: \<open>nat \<Rightarrow> nat\<close>
  where \<open>sigmaOdd \<equiv> \<lambda> n. card {d | d :: nat. d dvd n \<and> odd d}\<close>

proposition DyckTypeDivLengthArithmFun : 
  \<open>ArithmFun length \<doteq> ( \<lambda> n. 2*(sigmaOdd n) )\<close>
  using DyckTypeDivLength sigmaOdd_def
  by (simp add: sigmaOdd_def DyckTypeToArithmFunC)

end
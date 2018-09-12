(*
Title: Essential uniqueness of the paths associated to a number
Author: Jose Manuel Rodriguez Caballero

We will prove the following result.

theorem SchroederArithmB :
  fixes  v w :: \<open>SCHR list\<close>
  assumes \<open>(SchroederClass v) \<inter> (SchroederClass w) \<noteq> {}\<close>
    and \<open>length v = length w\<close>
  shows \<open>v = w\<close>


(This code  was verified in Isabelle2018)
*)

theory SchroederOfANumberUniq

imports Complex_Main PowOfTwo SchroederOfANumberDefs

begin


section {* Auxiliary Results  *}


lemma WordToFunINJEqLengthQIndReclastEqAssming:
  fixes n :: nat  and u v :: \<open>SCHR list\<close>
  assumes  \<open>\<forall>  u v :: SCHR list. WordToFun u = WordToFun v \<and> length u = n \<and> length v = n  \<longrightarrow>  u = v\<close>
    and \<open>WordToFun u = WordToFun v\<close> and \<open>length u = Suc n\<close> and \<open>length v = Suc n \<close> 
  and \<open> u ! n = v ! n\<close>
shows \<open>u = v\<close>
proof-
  from \<open>length u = Suc n\<close> have \<open>length u > 0\<close> 
    by simp
  then have \<open>u \<noteq> []\<close> 
    by blast
  then obtain uu :: \<open>SCHR list\<close> and qu :: SCHR where \<open>u = uu @ [qu]\<close> 
    by (metis append_butlast_last_id)
  from \<open>length v = Suc n\<close> have \<open>length v > 0\<close> 
    by simp
  then have \<open>v \<noteq> []\<close> 
    by blast
  then obtain vv :: \<open>SCHR list\<close> and qv :: SCHR where \<open>v = vv @ [qv]\<close> 
    by (metis append_butlast_last_id)
  from  \<open> u ! n = v ! n\<close> have \<open>qu = qv\<close> 
    by (metis Suc_inject \<open>u = uu @ [qu]\<close> \<open>v = vv @ [qv]\<close> assms(3) assms(4) length_append_singleton nth_append_length)
  have \<open>length uu = n\<close> 
    using \<open>u = uu @ [qu]\<close> assms(3) by auto
  have \<open>length vv = n\<close> 
    using \<open>v = vv @ [qv]\<close> assms(4) by auto 
  have \<open>\<forall> j. j < n \<longrightarrow> uu ! j = u ! j\<close> 
    by (simp add: \<open>length uu = n\<close> \<open>u = uu @ [qu]\<close> nth_append)
  then have \<open>\<forall> j. j < n \<longrightarrow> (WordToFun uu) j = (WordToFun u) j \<close>  
    by (simp add: WordToFun_def \<open>length uu = n\<close> assms(3))
  have \<open>\<forall> j. j < n \<longrightarrow> vv ! j = v ! j\<close> 
    by (simp add: \<open>length vv = n\<close> \<open>v = vv @ [qv]\<close> nth_append)
   then have \<open>\<forall> j. j < n \<longrightarrow> (WordToFun vv) j = (WordToFun v) j \<close>  
     by (simp add: WordToFun_def \<open>length vv = n\<close> assms(4))
   from \<open>WordToFun u = WordToFun v\<close> have  \<open>\<forall> j. j < n \<longrightarrow> (WordToFun u) j = (WordToFun v) j\<close>
     by simp
    have \<open>\<forall> j. j < n \<longrightarrow> (WordToFun uu) j = (WordToFun vv) j\<close> 
      by (simp add: \<open>\<forall>j<n. WordToFun uu j = WordToFun u j\<close> \<open>\<forall>j<n. WordToFun vv j = WordToFun v j\<close> assms(2))
    from \<open>length uu = n\<close> have  \<open>\<forall> j. j \<ge> n \<longrightarrow> (WordToFun uu) j = 0\<close> 
      by (simp add: WordToFun_def) 
    from \<open>length vv = n\<close> have  \<open>\<forall> j. j \<ge> n \<longrightarrow> (WordToFun vv) j = 0\<close> 
      by (simp add: WordToFun_def) 
     have \<open>\<forall> j. j \<ge> n \<longrightarrow> (WordToFun uu) j = (WordToFun vv) j\<close> 
       by (simp add: \<open>\<forall>j\<ge>n. WordToFun uu j = 0\<close> \<open>\<forall>j\<ge>n. WordToFun vv j = 0\<close>)
     have \<open>\<forall> j. (WordToFun uu) j = (WordToFun vv) j\<close> 
       using \<open>\<forall>j<n. WordToFun uu j = WordToFun vv j\<close> \<open>\<forall>j\<ge>n. WordToFun uu j = WordToFun vv j\<close> not_le by auto
     then have \<open>WordToFun uu = WordToFun vv\<close> by blast
     have \<open>uu = vv\<close> 
       by (simp add: \<open>WordToFun uu = WordToFun vv\<close> \<open>length uu = n\<close> \<open>length vv = n\<close> assms(1))
     show ?thesis 
       by (simp add: \<open>qu = qv\<close> \<open>u = uu @ [qu]\<close> \<open>uu = vv\<close> \<open>v = vv @ [qv]\<close>)
   qed

lemma WordToFunINJEqLengthQIndReclastEqProving:
  fixes n :: nat and u v :: \<open>SCHR list\<close>
  assumes  \<open>\<forall>  u v :: SCHR list. WordToFun u = WordToFun v \<and> length u = n \<and> length v = n  \<longrightarrow>  u = v\<close>
    and \<open>WordToFun u = WordToFun v\<close> and \<open>length u = Suc n\<close> and \<open>length v = Suc n \<close> 
shows  \<open>(!) u n = (!) v n\<close>
proof-
  from \<open>WordToFun u = WordToFun v\<close> have \<open>(WordToFun u) n = (WordToFun v) n\<close> 
    by simp
  then show ?thesis
    by (smt SCHR.exhaust SchroederCode_def WordToFun_def assms(3) assms(4) lessI)
qed

lemma WordToFunINJEqLengthQIndRec:
  fixes n :: nat
  assumes  \<open>\<forall>  u v :: SCHR list. WordToFun u = WordToFun v \<and> length u = n \<and> length v = n  \<longrightarrow>  u = v\<close>
    and \<open>WordToFun u = WordToFun v\<close> and \<open>length u = Suc n\<close> and \<open>length v = Suc n \<close> 
shows \<open>u = v\<close>
  using WordToFunINJEqLengthQIndReclastEqAssming WordToFunINJEqLengthQIndReclastEqProving
   assms(1) assms(2) assms(3) assms(4) by blast

lemma WordToFunINJEqLengthQInd:
  fixes n :: nat
  shows  \<open>\<forall>  u v :: SCHR list. WordToFun u = WordToFun v \<and> length u = n \<and> length v = n  \<longrightarrow>  u = v\<close>
proof (induction n)
  case 0
  then show ?case 
    by simp
next
  case (Suc n)
  then show ?case using WordToFunINJEqLengthQIndRec 
    by blast
qed

lemma WordToFunINJEqLengthQ:
  \<open>\<forall>  u v :: SCHR list. WordToFun u = WordToFun v \<and> length u = length v  \<longrightarrow>  u = v\<close>
  using WordToFunINJEqLengthQInd by blast

lemma WordToFunINJEqLength:
  fixes u v :: \<open>SCHR list\<close>
  assumes \<open> WordToFun u =  WordToFun v\<close> and \<open>length u = length v\<close>
  shows \<open>u = v\<close>
  using WordToFunINJEqLengthQ  assms(1) assms(2) by blast

section {* Main result *}

theorem SchroederArithmB :
  fixes  v w :: \<open>SCHR list\<close>
  assumes \<open>(SchroederClass v) \<inter> (SchroederClass w) \<noteq> {}\<close>
    and \<open>length v = length w\<close>
  shows \<open>v = w\<close>
proof-
  obtain n :: nat where \<open>n \<in> (SchroederClass v) \<inter> (SchroederClass w)\<close> using  \<open>(SchroederClass v) \<inter> (SchroederClass w) \<noteq> {}\<close>
    by blast
  have \<open>n \<in> SchroederClass v\<close> using  \<open>n \<in> (SchroederClass v) \<inter> (SchroederClass w)\<close> by blast
  then have \<open>n \<ge> 1\<close> 
    by (simp add: SchroederClass_def)
  from  \<open>n \<in> SchroederClass v\<close> have \<open>WordToFun v = (Jsigns n)\<close> 
    by (simp add: SchroederClass_def)
  have \<open>n \<in> SchroederClass w\<close> using  \<open>n \<in> (SchroederClass v) \<inter> (SchroederClass w)\<close> by blast
  then  have \<open>WordToFun w = (Jsigns n)\<close> 
    by (simp add: SchroederClass_def)
  show ?thesis 
    by (simp add: WordToFunINJEqLengthQInd \<open>WordToFun v = Jsigns n\<close> \<open>WordToFun w = Jsigns n\<close> assms(2))
qed


end
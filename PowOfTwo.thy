(*
Title: Powers of 2
Author: Jose Manuel Rodriguez Caballero

Miscellany about powers of 2. Our main result will be the following theorem:

\<exists>! f :: nat \<Rightarrow> nat. \<exists>! g :: nat \<Rightarrow> nat. (\<forall> n. (f 0 = 0 \<and> g 0 = 1 \<and> ( n \<ge> 1 \<longrightarrow> n = 2^(f n)*(g n) \<and> odd (g n) )) )

(This code  was verified in Isabelle2018-RC4/HOL)

*)

theory PowOfTwo

imports Complex_Main

begin

lemma TrapezoidalNumbersNec3: "\<not>(\<exists> r. 2*(n::nat) = 2^r) \<Longrightarrow> \<not>(\<exists> r. n = 2^r)"
  by (metis power_commutes semiring_normalization_rules(28))

lemma TrapezoidalNumbersNec2_5base: 
  fixes d r :: nat
  shows "d dvd 2 ^ 0 \<Longrightarrow> \<exists>k. d = 2 ^ k"
  by (metis One_nat_def Suc_leI dvd_imp_le dvd_pos_nat le_antisym less_numeral_extra(1) nat_power_eq_Suc_0_iff)


lemma TrapezoidalNumbersNec2_5recA1729:
  fixes t d r :: nat
  assumes \<open>\<forall>d. odd t \<and> d * t = 2 ^ r \<longrightarrow> t = 1\<close>
    and \<open>odd t\<close> and \<open> d * t = 2 ^ Suc r \<close>
shows \<open>t = 1\<close>
proof-
  have \<open>even d\<close> 
    by (metis \<open>d * t = 2 ^ Suc r\<close> \<open>odd t\<close> even_mult_iff even_numeral even_power zero_less_Suc)
  then obtain e :: nat where \<open>2*e = d\<close> 
    by blast
  have \<open> e * t = 2 ^ r\<close>
    using \<open>2 * e = d\<close> \<open>d * t = 2 ^ Suc r\<close> by auto
  have \<open> t = 1 \<close> 
    using \<open>e * t = 2 ^ r\<close> assms(1) assms(2) by blast
    show ?thesis 
      by (simp add: \<open>t = 1\<close>)
  qed

lemma TrapezoidalNumbersNec2_5recA:
  "\<forall> d::nat. (odd t \<and> d*(t::nat) = 2^(r::nat) \<longrightarrow> t = 1)"
proof (induction r)
  case 0
  then show ?case 
    by simp
next
  case (Suc r)
  then show ?case 
    using TrapezoidalNumbersNec2_5recA1729 by blast
  qed

lemma TrapezoidalNumbersNec2_5rec: 
  fixes d r :: nat
  shows "(d dvd 2 ^ r \<Longrightarrow> \<exists>k. d = 2 ^ k) \<Longrightarrow> ( d dvd 2 ^ Suc r \<Longrightarrow> \<exists>k. d = 2 ^ k)"
proof (cases "d = 2^(Suc r)")
  case True
  then show ?thesis by blast
next
  case False
  assume "d dvd 2 ^ r \<Longrightarrow> \<exists>k. d = 2 ^ k"
  assume "d dvd 2 ^ Suc r"
  from \<open>d dvd 2 ^ Suc r\<close> obtain t::nat where \<open>d*t = 2 ^ Suc r\<close> 
    by (metis dvdE) 
  then have \<open>t \<ge> 2\<close> 
    by (metis False One_nat_def Suc_leI le_antisym mult_1_right nat_one_le_power not_less_eq_eq numeral_2_eq_2 one_le_mult_iff pos2)
   have \<open>t dvd  2 ^ Suc r\<close> 
     by (metis \<open>d * t = 2 ^ Suc r\<close> dvd_triv_right)
   from  \<open>d*t = 2 ^ Suc r\<close> have "even t \<or> even d" 
     by (metis False One_nat_def TrapezoidalNumbersNec2_5recA mult.right_neutral)
   then show ?thesis
   proof (cases "even t")
     case True
     then show ?thesis 
     proof -
       obtain nn :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
         "t = Suc (Suc 0) * nn t (Suc (Suc 0))"
         by (metis True dvd_def numeral_2_eq_2)
then have "Suc (Suc 0) * 2 ^ r = d * (Suc (Suc 0) * nn t (Suc (Suc 0)))"
by (simp add: \<open>d * t = 2 ^ Suc r\<close>)
  then have "\<exists>n. 2 ^ r = d * n"
by (metis Suc_neq_Zero mult_left_cancel semiring_normalization_rules(19))
  then show ?thesis
    using \<open>d dvd 2 ^ r \<Longrightarrow> \<exists>k. d = 2 ^ k\<close> dvd_def by blast
qed
   next
     case False
     then have \<open>odd t\<close> by simp
     then show ?thesis 
       by (metis TrapezoidalNumbersNec2_5recA \<open>d * t = 2 ^ Suc r\<close> mult_1_right)
     qed
qed

lemma TrapezoidalNumbersNec2_5: 
  fixes d r :: nat
  shows "d dvd 2^r \<Longrightarrow> \<exists> k. d = 2^k"
proof (induction r)
case 0
then show ?case 
  using TrapezoidalNumbersNec2_5base by blast
next
  case (Suc r)
  then show ?case 
    using TrapezoidalNumbersNec2_5rec by blast
qed
  
lemma TrapezoidalNumbersNec2_4: 
  fixes d r :: nat
  assumes "d dvd 2^r"  and "d \<noteq> 2^r"
  shows "\<exists> k. d = 2^k \<and> k < r"
  by (metis TrapezoidalNumbersNec2_5 antisym_conv3 assms(1) assms(2) nat_dvd_not_less nat_power_less_imp_less pos2 zero_less_power)

lemma TrapezoidalNumbersNec2_3: 
  fixes d r :: nat
  assumes "d dvd 2^r" and "d \<ge> 2" 
  shows "even d"
proof (cases "d = 2^r")
  case True
  show ?thesis 
    by (metis True assms(2) even_power gcd_nat.order_iff_strict le_add1 le_antisym not_gr0 one_add_one power_0)
next
  case False
  then obtain k where "d = 2^k" and "k < r" 
    using TrapezoidalNumbersNec2_4 assms(1) by blast
  from \<open>d = 2^k\<close> \<open>k < r\<close> \<open>d \<ge> 2\<close> have "k \<ge> 1" 
    by (metis one_less_numeral_iff power_increasing_iff power_one_right semiring_norm(76))
  from \<open>k \<ge> 1\<close> \<open>d = 2^k\<close> show ?thesis by auto
qed

lemma TrapezoidalNumbersNec2_2: "\<exists> d. d \<ge> 2 \<and> d dvd (n::nat) \<and> odd d \<Longrightarrow>  \<not> (\<exists> r. n = 2^r)"
proof (rule classical)
  assume "\<not> (\<not> (\<exists> r. n = 2^r))"
  then have "\<exists> r. n = 2^r" by simp
  then obtain r :: nat where "n = 2^r" by blast
  assume "\<exists> d. d \<ge> 2 \<and> d dvd (n::nat) \<and> odd d"
  then obtain d::nat where "d \<ge> 2" and "d dvd n" and "odd d" by blast
  have "d dvd 2^r" 
    using \<open>d dvd n\<close> \<open>n = 2 ^ r\<close> by blast
  have "even d" 
    using TrapezoidalNumbersNec2_3 \<open>2 \<le> d\<close> \<open>d dvd 2 ^ r\<close> by blast
  from \<open>even d\<close> \<open>odd d\<close> show ?thesis by blast
qed

lemma TrapezoidalNumbersSuf_1C_base: "n \<noteq> 0 \<Longrightarrow> odd n \<Longrightarrow> ( \<exists> r t.  n = 2^r*t \<and> odd t )"
proof-
  assume \<open>n \<noteq> 0\<close>
  assume \<open>odd n\<close>
  have \<open>n = 2^0 * n\<close>
    by simp
  show ?thesis 
    using \<open>n = 2 ^ 0 * n\<close> \<open>odd n\<close> by blast
qed

lemma TrapezoidalNumbersSuf_1C_BOUNDEDNonQ: "\<forall>  n. (n \<le> (N::nat) \<longrightarrow> (n \<noteq> 0 \<longrightarrow>  ( \<exists> r t.  n = 2^r*t \<and> odd t ) ))"
proof (induction N)
  case 0
  then show ?case
    by blast
next
  case (Suc N)
  have \<open>\<exists> r t.  Suc N = 2^r*t \<and> odd t\<close>
  proof (cases \<open>odd (Suc N)\<close>)
    case True
    then show ?thesis 
      using TrapezoidalNumbersSuf_1C_base by blast
  next
    case False
  then have \<open>even (Suc N)\<close> 
    by auto
  obtain m where \<open>2*m = Suc N\<close> 
    by (metis \<open>even (Suc N)\<close> dvdE)
  from \<open>2*m = Suc N\<close> have \<open>m \<le> N\<close> 
    by linarith
  then have \<open> \<exists> r t.  m = 2^r*t \<and> odd t \<close> 
    using Suc.IH \<open>2 * m = Suc N\<close> by auto
    then show ?thesis 
      by (metis \<open>2 * m = Suc N\<close> power_commutes semiring_normalization_rules(18) semiring_normalization_rules(28))
  qed
  then show ?case 
    by (simp add: Suc.IH le_Suc_eq)
qed


lemma ParityDescomposition:
  fixes n::nat
  assumes \<open>n \<ge> 1\<close>
  shows \<open>\<exists> k t :: nat. n = (2::nat)^k*t \<and> odd t\<close>
  using TrapezoidalNumbersSuf_1C_BOUNDEDNonQ assms le_eq_less_or_eq by auto


lemma Pow2Odd:
  fixes n :: nat
  assumes \<open>n \<ge> 1\<close> and \<open>\<forall> d. d \<ge> 2 \<and> d dvd n \<longrightarrow> even d\<close>
  shows \<open>\<exists> k :: nat. n = 2^k\<close>
proof-
  obtain u v :: nat where \<open>n = 2^u * v\<close> and \<open>odd v\<close> 
    using ParityDescomposition assms(1) by blast
  from \<open>n = 2^u * v\<close> have \<open>v dvd n\<close> 
    by simp
  from  \<open>v dvd n\<close> \<open>odd v\<close>  \<open>\<forall> d. d \<ge> 2 \<and> d dvd n \<longrightarrow> even d\<close> 
  have \<open>v = 1\<close> 
    by (metis One_nat_def Suc_leI add.commute add.right_neutral add_right_mono neq0_conv odd_two_times_div_two_succ one_add_one)
  then show ?thesis 
    by (simp add: \<open>n = 2 ^ u * v\<close>)
qed

(* ---  *)

lemma preExistenceUniquenessEvenPart:
\<open>\<forall> n::nat. \<exists> u v :: nat. ( n \<ge> 1 \<longrightarrow> n = 2^u*v \<and> odd v )\<close>
  by (simp add: ParityDescomposition) 

lemma preExistenceEvenPart:
\<open>\<exists> f g :: nat \<Rightarrow> nat. \<forall> n::nat. ( n \<ge> 1 \<longrightarrow> n = 2^(f n)*(g n) \<and> odd (g n) )\<close>
  using preExistenceUniquenessEvenPart by metis

lemma ExistenceEvenPart:
\<open>\<exists> f :: nat \<Rightarrow> nat. \<exists> g :: nat \<Rightarrow> nat. \<forall> n::nat. (f 0 = 0) \<and> (g 0 = 1) \<and> ( n \<ge> 1 \<longrightarrow> n = 2^(f n)*(g n) \<and> odd (g n) )\<close>
proof-
  obtain f g :: \<open>nat \<Rightarrow> nat\<close> where 
\<open> \<forall> n::nat. ( n \<ge> 1 \<longrightarrow> n = 2^(f n)*(g n) \<and> odd (g n) )\<close>
    using preExistenceEvenPart by blast

  obtain ff :: \<open>nat \<Rightarrow> nat\<close> where 
\<open>ff \<equiv> \<lambda> n. (if n = 0 then 0 else f n)\<close>
    by simp

  obtain gg :: \<open>nat \<Rightarrow> nat\<close> where 
\<open>gg \<equiv> \<lambda> n. (if n = 0 then 1 else g n)\<close>
    by simp

  from \<open> \<forall> n::nat. ( n \<ge> 1 \<longrightarrow> n = 2^(f n)*(g n) \<and> odd (g n) )\<close>
\<open>ff \<equiv> \<lambda> n. (if n = 0 then 0 else f n)\<close> \<open>gg \<equiv> \<lambda> n. (if n = 0 then 1 else g n)\<close>
  show ?thesis 
    by (smt \<open>\<And>thesis. (\<And>ff. ff \<equiv> \<lambda>n. if n = 0 then 0 else f n \<Longrightarrow> thesis) \<Longrightarrow> thesis\<close> \<open>\<And>thesis. (\<And>gg. gg \<equiv> \<lambda>n. if n = 0 then 1 else g n \<Longrightarrow> thesis) \<Longrightarrow> thesis\<close> not_one_le_zero)
qed


lemma preUniqEvenPartS0:
  fixes f ff  g gg  :: \<open>nat \<Rightarrow> nat\<close> and n :: nat
  assumes \<open>n = 0\<close> and  \<open>f 0 = 0\<close> and \<open>g 0 = 1\<close> and \<open> n \<ge> 1 \<longrightarrow> n = 2^(f n)*(g n) \<and> odd (g n) \<close>
    and \<open>ff 0 = 0\<close> and \<open>gg 0 = 1\<close> and \<open> n \<ge> 1 \<longrightarrow> n = 2^(ff n)*(gg n) \<and> odd (gg n)\<close>
  shows \<open>f n = ff n \<and> g n = gg n\<close>
  by (simp add: assms(1) assms(2) assms(3) assms(5) assms(6))


lemma preUniqnessOddEven_OddPartOneSide :
 fixes uu v vv :: nat
 assumes  \<open>odd v\<close> and \<open>odd vv\<close> and \<open>v = 2^uu*vv\<close>
 shows \<open>v = vv\<close>
  using assms(1) assms(3) by auto

lemma preUniqnessOddEven_OddPart :
 fixes u uu v vv :: nat
 assumes \<open>u \<le> uu\<close> and \<open>odd v\<close> and \<open>odd vv\<close> and \<open>2^u*v = 2^uu*vv\<close>
 shows \<open>v = vv\<close>
proof-
  from  \<open>u \<le> uu\<close> obtain k :: nat where \<open>u + k = uu\<close> 
    using le_Suc_ex by blast
  from \<open>2^u*v = 2^uu*vv\<close> \<open>u + k = uu\<close> 
    have \<open>v = 2^k*vv\<close> 
      by (smt Groups.mult_ac(1) nonzero_mult_div_cancel_left power_add power_eq_0_iff rel_simps(76))
    then show ?thesis using \<open>odd v\<close> \<open>odd vv\<close> 
      using preUniqnessOddEven_OddPartOneSide by blast
qed

lemma UniqnessOddEven_OddPart :
 fixes u uu v vv :: nat
 assumes \<open>odd v\<close> and \<open>odd vv\<close> and \<open>2^u*v = 2^uu*vv\<close>
 shows \<open>v = vv\<close>
  by (metis assms(1) assms(2) assms(3) nat_le_linear preUniqnessOddEven_OddPart)


lemma UniqnessOddEven_EvenPart :
 fixes u uu v vv :: nat
 assumes \<open>odd v\<close> and \<open>odd vv\<close> and \<open>2^u*v = 2^uu*vv\<close>
 shows \<open>u = uu\<close>
  by (metis One_nat_def UniqnessOddEven_OddPart assms(1) assms(2) assms(3) even_zero lessI mult_cancel_right numeral_2_eq_2 power_inject_exp)

lemma UniqnessOddEven :
 fixes u uu v vv :: nat
 assumes \<open>odd v\<close> and \<open>odd vv\<close> and \<open>2^u*v = 2^uu*vv\<close>
 shows \<open>u = uu \<and> v = vv\<close>
  using UniqnessOddEven_EvenPart UniqnessOddEven_OddPart assms(1) assms(2) assms(3) by blast

lemma preUniqEvenPartS1:
  fixes f ff  g gg  :: \<open>nat \<Rightarrow> nat\<close> and n :: nat
  assumes \<open>n \<ge> 1\<close> and  \<open>f 0 = 0\<close> and \<open>g 0 = 1\<close> and \<open> n \<ge> 1 \<longrightarrow> n = 2^(f n)*(g n) \<and> odd (g n) \<close>
    and \<open>ff 0 = 0\<close> and \<open>gg 0 = 1\<close> and \<open> n \<ge> 1 \<longrightarrow> n = 2^(ff n)*(gg n) \<and> odd (gg n)\<close>
  shows \<open>f n = ff n \<and> g n = gg n\<close>
  by (metis UniqnessOddEven assms(1) assms(4) assms(7))


lemma preUniqEvenPartS:
  fixes f ff  g gg  :: \<open>nat \<Rightarrow> nat\<close> and n :: nat
  assumes \<open>f 0 = 0\<close> and \<open>g 0 = 1\<close> and \<open> n \<ge> 1 \<longrightarrow> n = 2^(f n)*(g n) \<and> odd (g n) \<close>
    and \<open>ff 0 = 0\<close> and \<open>gg 0 = 1\<close> and \<open> n \<ge> 1 \<longrightarrow> n = 2^(ff n)*(gg n) \<and> odd (gg n)\<close>
  shows \<open>f n = ff n \<and> g n = gg n\<close>
  by (metis assms(1) assms(2) assms(3) assms(4) assms(5) assms(6) dvd_imp_le neq0_conv one_dvd preUniqEvenPartS1)

lemma preUniqEvenPartSQE:
  fixes f ff  g gg  :: \<open>nat \<Rightarrow> nat\<close>
  shows \<open>(\<forall> n. (f 0 = 0 \<and> g 0 = 1 \<and> ( n \<ge> 1 \<longrightarrow> n = 2^(f n)*(g n) \<and> odd (g n) )) 
\<and> (ff 0 = 0 \<and> gg 0 = 1 \<and> (n \<ge> 1 \<longrightarrow> n = 2^(ff n)*(gg n) \<and> odd (gg n) )) ) \<Longrightarrow> (f  = ff ) \<and> (g  = gg ) \<close>
  using preUniqEvenPartS by blast

lemma preUniqEvenPartSQEG:
  fixes f ff  :: \<open>nat \<Rightarrow> nat\<close>
  shows \<open>\<exists>! g :: nat \<Rightarrow> nat. (\<forall> n. (f 0 = 0 \<and> g 0 = 1 \<and> ( n \<ge> 1 \<longrightarrow> n = 2^(f n)*(g n) \<and> odd (g n) )) 
\<and> (ff 0 = 0 \<and> g 0 = 1 \<and> (n \<ge> 1 \<longrightarrow> n = 2^(ff n)*(g n) \<and> odd (g n) )) ) \<Longrightarrow> (f = ff ) \<close>
  using preUniqEvenPartSQE by blast

lemma preUniqEvenPartSQEGD:
  fixes f ff  :: \<open>nat \<Rightarrow> nat\<close>
  assumes \<open>\<exists>! g :: nat \<Rightarrow> nat. (\<forall> n. (f 0 = 0 \<and> g 0 = 1 \<and> ( n \<ge> 1 \<longrightarrow> n = 2^(f n)*(g n) \<and> odd (g n) )) )
\<and> (\<forall> n. (ff 0 = 0 \<and> g 0 = 1 \<and> (n \<ge> 1 \<longrightarrow> n = 2^(ff n)*(g n) \<and> odd (g n) )) )\<close>
  shows \<open>f = ff\<close>
  by (metis assms preUniqEvenPartSQE)

lemma preUniqEvenPartSQEGX:
   \<open>\<exists> f :: nat \<Rightarrow> nat. \<exists>! g :: nat \<Rightarrow> nat. (\<forall> n. (f 0 = 0 \<and> g 0 = 1 \<and> ( n \<ge> 1 \<longrightarrow> n = 2^(f n)*(g n) \<and> odd (g n) )) ) \<close>
  by (smt ExistenceEvenPart preUniqEvenPartSQE)

lemma UniqEvenPartXrferew4:
 \<open>\<exists>f. \<exists>!g. f 0 = 0 \<and>
             g 0 = Suc 0 \<and>
             (\<forall>n\<ge>Suc 0. n = 2 ^ f n * g n \<and> odd (g n))\<close>
  using preUniqEvenPartSQEGX by auto

lemma preUniqEvenPartXr43ur93n: 
  fixes f y g ga :: \<open>nat \<Rightarrow> nat\<close> and n :: nat
  assumes
\<open> \<forall>y y'.
          y 0 = Suc 0 \<and>
          (\<forall>n\<ge>Suc 0. n = 2 ^ f n * y n \<and> odd (y n)) \<and>
          y' 0 = Suc 0 \<and>
          (\<forall>n\<ge>Suc 0. n = 2 ^ f n * y' n \<and> odd (y' n)) \<longrightarrow>
          y = y'\<close> 
and
      \<open> \<forall>ya y'.
          ya 0 = Suc 0 \<and>
          (\<forall>n\<ge>Suc 0. n = 2 ^ y n * ya n \<and> odd (ya n)) \<and>
          y' 0 = Suc 0 \<and>
          (\<forall>n\<ge>Suc 0. n = 2 ^ y n * y' n \<and> odd (y' n)) \<longrightarrow>
          ya = y'\<close>and
      \<open>f 0 = 0\<close> and
      \<open>y 0 = 0\<close> and
      \<open>g 0 = Suc 0\<close> and
      \<open> \<forall>n\<ge>Suc 0. n = 2 ^ f n * g n \<and> odd (g n)\<close> and
      \<open> ga 0 = Suc 0\<close> and
      \<open> \<forall>n\<ge>Suc 0. n = 2 ^ y n * ga n \<and> odd (ga n)\<close> 
    shows \<open> f n = y n\<close>
proof(cases \<open>n = 0\<close>)
case True
  then show ?thesis 
    by (simp add: assms(3) assms(4))
next
  case False
  then have \<open>n \<ge> Suc 0\<close> 
    using not_less_eq_eq by blast
  then show ?thesis 
    using One_nat_def assms(3) assms(4) assms(5) assms(6) assms(7) assms(8) preUniqEvenPartS by presburger
qed

lemma preUniqEvenPartXr43ur93: 
  fixes f y g ga :: \<open>nat \<Rightarrow> nat\<close>
  assumes
\<open> \<forall>y y'.
          y 0 = Suc 0 \<and>
          (\<forall>n\<ge>Suc 0. n = 2 ^ f n * y n \<and> odd (y n)) \<and>
          y' 0 = Suc 0 \<and>
          (\<forall>n\<ge>Suc 0. n = 2 ^ f n * y' n \<and> odd (y' n)) \<longrightarrow>
          y = y'\<close> 
and
      \<open> \<forall>ya y'.
          ya 0 = Suc 0 \<and>
          (\<forall>n\<ge>Suc 0. n = 2 ^ y n * ya n \<and> odd (ya n)) \<and>
          y' 0 = Suc 0 \<and>
          (\<forall>n\<ge>Suc 0. n = 2 ^ y n * y' n \<and> odd (y' n)) \<longrightarrow>
          ya = y'\<close>and
      \<open>f 0 = 0\<close> and
      \<open>y 0 = 0\<close> and
      \<open>g 0 = Suc 0\<close> and
      \<open> \<forall>n\<ge>Suc 0. n = 2 ^ f n * g n \<and> odd (g n)\<close> and
      \<open> ga 0 = Suc 0\<close> and
      \<open> \<forall>n\<ge>Suc 0. n = 2 ^ y n * ga n \<and> odd (ga n)\<close> 
    shows \<open> f = y\<close>
proof (rule classical)
  assume \<open>\<not>(f = y)\<close>
  then obtain n where \<open>f n \<noteq> y n \<close> 
    by (meson ext)
  from preUniqEvenPartXr43ur93n have \<open>f n = y n\<close> 
    using One_nat_def assms(3) assms(4) assms(5) assms(6) assms(7) assms(8) preUniqEvenPartS by presburger
  from  \<open>f n \<noteq> y n \<close>  \<open>f n = y n\<close>  have False 
    by blast
  then show ?thesis by blast
qed

lemma UniqEvenPartXr43ur93: \<open>\<And>f y g ga.
       \<forall>y y'.
          y 0 = Suc 0 \<and>
          (\<forall>n\<ge>Suc 0. n = 2 ^ f n * y n \<and> odd (y n)) \<and>
          y' 0 = Suc 0 \<and>
          (\<forall>n\<ge>Suc 0. n = 2 ^ f n * y' n \<and> odd (y' n)) \<longrightarrow>
          y = y' \<Longrightarrow>
       \<forall>ya y'.
          ya 0 = Suc 0 \<and>
          (\<forall>n\<ge>Suc 0. n = 2 ^ y n * ya n \<and> odd (ya n)) \<and>
          y' 0 = Suc 0 \<and>
          (\<forall>n\<ge>Suc 0. n = 2 ^ y n * y' n \<and> odd (y' n)) \<longrightarrow>
          ya = y' \<Longrightarrow>
       f 0 = 0 \<Longrightarrow>
       y 0 = 0 \<Longrightarrow>
       g 0 = Suc 0 \<Longrightarrow>
       \<forall>n\<ge>Suc 0. n = 2 ^ f n * g n \<and> odd (g n) \<Longrightarrow>
       ga 0 = Suc 0 \<Longrightarrow>
       \<forall>n\<ge>Suc 0. n = 2 ^ y n * ga n \<and> odd (ga n) \<Longrightarrow> f = y\<close>
  using preUniqEvenPartXr43ur93 by auto

theorem UniqEvenPart:
   \<open>\<exists>! f :: nat \<Rightarrow> nat. \<exists>! g :: nat \<Rightarrow> nat. (\<forall> n. (f 0 = 0 \<and> g 0 = 1 \<and> ( n \<ge> 1 \<longrightarrow> n = 2^(f n)*(g n) \<and> odd (g n) )) ) \<close>
  apply (auto)
  using UniqEvenPartXrferew4 apply blast
  using UniqEvenPartXr43ur93 apply auto
  done

end

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

(* --- *)

definition OddPart :: \<open>nat \<Rightarrow> nat\<close> where
\<open>OddPart \<equiv> \<lambda> n. (if n = 0 then 1 else  Max {d |d :: nat.  d dvd n \<and> odd d} )\<close>

definition Exp2 :: \<open>nat \<Rightarrow> nat\<close> where
\<open>Exp2 \<equiv> \<lambda> n. (if n = 0 then 0 else Max {k |k :: nat.  (2^k) dvd n})\<close>

lemma preExp2OddPartChar1:
  fixes n :: nat
  assumes \<open>n \<ge> 1\<close>
  shows \<open> odd (OddPart n) \<close>
proof-
  from \<open>n \<ge> 1\<close> have \<open>\<not> (n = 0)\<close> by simp
  then obtain S :: \<open>nat set\<close> where \<open>S = {d |d :: nat.  d dvd n \<and> odd d}\<close> 
    by blast
  from  \<open>S = {d |d :: nat.  d dvd n \<and> odd d}\<close>  \<open>n \<ge> 1\<close> have \<open>S \<noteq> {}\<close> by auto
  from  \<open>S = {d |d :: nat.  d dvd n \<and> odd d}\<close>  \<open>n \<ge> 1\<close> have \<open>finite S\<close> by auto
  from \<open>S \<noteq> {}\<close> \<open>finite S\<close> obtain d :: nat where \<open>d = Max S\<close>  
    by blast
  from \<open>S = {d |d :: nat.  d dvd n \<and> odd d}\<close> \<open>d = Max S\<close>  have \<open>d = OddPart n\<close> 
    using OddPart_def 
    using \<open>n \<noteq> 0\<close> by presburger
  from \<open>S \<noteq> {}\<close> \<open>finite S\<close> \<open>d = Max S\<close> have \<open> d dvd n \<and> odd d \<close>
    using Max_in \<open>S = {d |d. d dvd n \<and> odd d}\<close> by auto
  then have \<open>odd d\<close> by blast 
  from \<open>odd d\<close>  \<open>d = OddPart n\<close> show ?thesis 
    by blast
qed

lemma Exp2L1QQ:
\<open>(n :: nat) \<ge> 1 \<Longrightarrow> {e |e :: nat.  2^e dvd n} \<noteq> {}\<close>
  by (metis One_nat_def ParityDescomposition dvd_triv_left empty_Collect_eq)

lemma Exp2L1QQQ:
\<open>(n :: nat) \<ge> 1 \<Longrightarrow> finite {e |e :: nat.  2^e dvd n}\<close>
proof(rule classical)
  assume \<open>n \<ge> 1\<close>
  assume \<open>\<not> (finite {e |e :: nat.  2^e dvd n})\<close>
  then have \<open>infinite {e |e :: nat.  2^e dvd n}\<close> 
    by blast
  obtain e :: nat where \<open>e \<in> {e |e :: nat.  2^e dvd n}\<close> and \<open>e > n\<close>
    by (metis \<open>infinite {e |e. 2 ^ e dvd n}\<close> finite_nat_set_iff_bounded_le not_le)
  from \<open>e \<in> {e |e :: nat.  2^e dvd n}\<close> have \<open>2^e dvd n\<close> 
    by simp
  from \<open>e > n\<close> have \<open>2^e > n \<close> 
    using less_trans of_nat_less_two_power by auto
  from \<open>n \<ge> 1\<close> \<open>2^e dvd n\<close> \<open>2^e > n \<close>  have False 
    by auto
  then show ?thesis 
    by simp
qed


lemma Exp2L1:
  fixes n :: nat
  assumes \<open>n \<ge> 1\<close>
  shows \<open> 2^(Exp2 n) dvd n \<close>
proof-
   from \<open>n \<ge> 1\<close> have \<open>\<not> (n = 0)\<close> by simp
  then obtain S :: \<open>nat set\<close> where \<open>S = {e |e :: nat.  2^e dvd n}\<close> 
    by blast
  from  \<open>S = {e |e :: nat.  2^e dvd n}\<close> \<open>n \<ge> 1\<close> have \<open>S \<noteq> {}\<close> 
    by (metis empty_Collect_eq one_dvd power_0)
  from  \<open>S = {e |e :: nat.  2^e dvd n}\<close> \<open>n \<ge> 1\<close> have \<open>finite S\<close>
    using Exp2L1QQQ by auto
  from \<open>S \<noteq> {}\<close> \<open>finite S\<close> obtain e :: nat where \<open>e = Max S\<close>  
    by blast
  have \<open>2^e dvd n\<close> 
    using Max_in \<open>S = {e |e. 2 ^ e dvd n}\<close> \<open>S \<noteq> {}\<close> \<open>e = Max S\<close> \<open>finite S\<close> by auto
  then show ?thesis 
    by (metis  Exp2_def \<open>S = {e |e. 2 ^ e dvd n}\<close> \<open>e = Max S\<close> \<open>n \<noteq> 0\<close>)
qed

lemma Exp2L2:
  fixes n e :: nat
  assumes \<open>n \<ge> 1\<close> \<open> 2^e dvd n\<close>
  shows \<open> e \<le> Exp2 n \<close>
proof-
   from \<open>n \<ge> 1\<close> have \<open>\<not> (n = 0)\<close> by simp
  then obtain S :: \<open>nat set\<close> where \<open>S = {e |e :: nat.  2^e dvd n}\<close> 
    by blast
  from  \<open>S = {e |e :: nat.  2^e dvd n}\<close> \<open>n \<ge> 1\<close> have \<open>S \<noteq> {}\<close> 
    by (metis empty_Collect_eq one_dvd power_0)
  from  \<open>S = {e |e :: nat.  2^e dvd n}\<close> \<open>n \<ge> 1\<close> have \<open>finite S\<close>
    using Exp2L1QQQ by auto
  from \<open>S \<noteq> {}\<close> \<open>finite S\<close> obtain ee :: nat where \<open>ee = Max S\<close>  
    by blast
  have \<open>ee = Exp2 n\<close> 
    using Exp2_def \<open>S = {e |e. 2 ^ e dvd n}\<close> \<open>ee = Max S\<close> \<open>n \<noteq> 0\<close> by presburger
  have \<open>e \<in> S\<close> 
    using \<open>S = {e |e. 2 ^ e dvd n}\<close> assms(2) by blast 
  have \<open>e \<le> ee\<close> 
    by (simp add: \<open>e \<in> S\<close> \<open>ee = Max S\<close> \<open>finite S\<close>)
  then have \<open>e \<le> Exp2 n\<close> using \<open>ee = Exp2 n\<close> 
    by blast
  then show ?thesis by blast
qed

lemma preExp2OddPartChar2XA:
  fixes n k :: nat
  assumes \<open>n \<ge> 1\<close> and \<open>n = 2^(Exp2 n)*k\<close>
  shows \<open> odd k  \<close>
proof (rule classical)
  assume \<open>\<not> (odd k)\<close>
  then have \<open>even k\<close> by blast
  then obtain t :: nat where \<open>k = 2*t\<close> by blast
  then have \<open>n = 2^((Exp2 n)+1)*t\<close> 
    using assms(2) by auto
  then have \<open>2^((Exp2 n)+1) dvd n\<close> 
    by (metis dvd_triv_left)
  then have \<open>(Exp2 n)+1 \<le> Exp2 n\<close> 
    using Exp2L2 assms(1) by blast
  then have False 
    by simp
  then show ?thesis 
    by simp
qed

lemma preExp2OddPartChar2X1:
  fixes n :: nat
  assumes \<open>n \<ge> 1\<close>
  shows \<open>\<exists> k :: nat.  n = 2^(Exp2 n)*k \<and> odd k \<close>
  by (meson Exp2L1 assms dvdE preExp2OddPartChar2XA) 


lemma OddPartL1:
  fixes n :: nat
  assumes \<open>n \<ge> 1\<close>
  shows \<open> (OddPart n) dvd n \<close>
proof-
  from \<open>n \<ge> 1\<close> have \<open>\<not> (n = 0)\<close> by simp
  then obtain S :: \<open>nat set\<close> where \<open>S = {d |d :: nat.  d dvd n \<and> odd d}\<close> 
    by blast
  from  \<open>S = {d |d :: nat.  d dvd n \<and> odd d}\<close>  \<open>n \<ge> 1\<close> have \<open>S \<noteq> {}\<close> by auto
  from  \<open>S = {d |d :: nat.  d dvd n \<and> odd d}\<close>  \<open>n \<ge> 1\<close> have \<open>finite S\<close> by auto
  from \<open>S \<noteq> {}\<close> \<open>finite S\<close> obtain d :: nat where \<open>d = Max S\<close>  
    by blast
  from \<open>S = {d |d :: nat.  d dvd n \<and> odd d}\<close> \<open>d = Max S\<close>  have \<open>d = OddPart n\<close> 
    using OddPart_def 
    using \<open>n \<noteq> 0\<close> by presburger
  from \<open>S \<noteq> {}\<close> \<open>finite S\<close> \<open>d = Max S\<close> have \<open> d dvd n \<and> odd d \<close>
    using Max_in \<open>S = {d |d. d dvd n \<and> odd d}\<close> by auto
    then have \<open>d dvd n\<close> by blast
    then show ?thesis using \<open>d = Max S\<close> 
      using \<open>d = OddPart n\<close> by auto
  qed

lemma OddPartL1X1:
  fixes n k :: nat
  assumes \<open>n \<ge> 1\<close> and \<open>odd k\<close> and \<open>k dvd n\<close>
  shows \<open>k \<le> (OddPart n)\<close>
proof-
  from \<open>n \<ge> 1\<close> have \<open>\<not> (n = 0)\<close> by simp
  then obtain S :: \<open>nat set\<close> where \<open>S = {d |d :: nat.  d dvd n \<and> odd d}\<close> 
    by blast
  from  \<open>S = {d |d :: nat.  d dvd n \<and> odd d}\<close>  \<open>n \<ge> 1\<close> have \<open>S \<noteq> {}\<close> by auto
  from  \<open>S = {d |d :: nat.  d dvd n \<and> odd d}\<close>  \<open>n \<ge> 1\<close> have \<open>finite S\<close> by auto
  from \<open>S \<noteq> {}\<close> \<open>finite S\<close> obtain d :: nat where \<open>d = Max S\<close>  
    by blast
  from \<open>S = {d |d :: nat.  d dvd n \<and> odd d}\<close> \<open>d = Max S\<close>  have \<open>d = OddPart n\<close> 
    using OddPart_def 
    using \<open>n \<noteq> 0\<close> by presburger
  from \<open>S \<noteq> {}\<close> \<open>finite S\<close> \<open>d = Max S\<close> have \<open> d dvd n \<and> odd d \<close>
    using Max_in \<open>S = {d |d. d dvd n \<and> odd d}\<close> by auto
  then have \<open>odd d\<close> by blast 
    have \<open>k \<le> d\<close> 
      using Max_ge \<open>S = {d |d. d dvd n \<and> odd d}\<close> \<open>d = Max S\<close> \<open>finite S\<close> assms(2) assms(3) by blast
    then show ?thesis 
      by (simp add: \<open>d = OddPart n\<close>)
  qed

lemma OddPartL2S:
  fixes n d k :: nat
  assumes \<open>n \<ge> 1\<close> and \<open>n = d * (OddPart n)\<close> and \<open>k dvd d\<close> and \<open>odd k\<close>
  shows \<open>k = 1\<close>
proof(rule classical)
  assume \<open>\<not>(k = 1)\<close>
  then have \<open>k = 0 \<or> k \<ge> 2\<close> 
    by linarith
have \<open>k \<noteq> 0\<close> 
  using assms(4) by presburger
  then have \<open>k \<ge> 2\<close> 
    using \<open>k = 0 \<or> 2 \<le> k\<close> by blast
  obtain w :: nat where \<open>w = k * (OddPart n)\<close> 
    by blast
  have \<open>w dvd n\<close> 
    by (metis \<open>w = k * OddPart n\<close> assms(2) assms(3) dvd_times_right_cancel_iff gcd_nat.order_iff_strict mult_cancel_right)
  have \<open>odd w\<close> 
    using \<open>w = k * OddPart n\<close> assms(1) assms(4) even_mult_iff preExp2OddPartChar1 by blast
  have \<open>w > OddPart n\<close> 
    by (metis OddPart_def \<open>k \<noteq> 0\<close> \<open>k \<noteq> 1\<close> \<open>w = k * OddPart n\<close> \<open>w dvd n\<close> dvd_div_mult_self less_one  mult_cancel_right mult_is_0 mult_le_mono1 nat_mult_1 nat_neq_iff not_le semiring_normalization_rules(11))
  have \<open>w \<le> OddPart n\<close> 
    using OddPartL1X1 \<open>odd w\<close> \<open>w dvd n\<close> assms(1) by blast
  from  \<open>w > OddPart n\<close> \<open>w \<le> OddPart n\<close>  have False by simp
  then show ?thesis by blast
qed


lemma OddPartL2:
  fixes n d :: nat
  assumes \<open>n \<ge> 1\<close> and \<open>n = d * (OddPart n)\<close>
  shows \<open>\<forall> k :: nat. k dvd d \<and> odd k \<longrightarrow> k = 1\<close>
  using OddPartL2S assms(1) assms(2) by blast

lemma DFSFSfre34:
  fixes n :: nat
  assumes \<open>n \<ge> 1\<close> \<open>\<forall> k :: nat. k dvd n \<and> odd k \<longrightarrow> k = 1\<close>
  shows \<open> \<exists> e::nat. n = 2^e\<close>
  using Pow2Odd 
  using assms(1) assms(2) numeral_le_one_iff semiring_norm(69) by blast

lemma OddPartL3:
  fixes n d :: nat
  assumes \<open>n \<ge> 1\<close> and \<open>n = d * (OddPart n)\<close>
  shows \<open> \<exists> e::nat. d = 2^e\<close>
proof-
  from  \<open>n \<ge> 1\<close>  \<open>n = d * (OddPart n)\<close>
  have \<open>\<forall> k :: nat. k dvd d \<and> odd k \<longrightarrow> k = 1\<close> 
    using OddPartL2 by blast
  then show ?thesis using DFSFSfre34 \<open>n \<ge> 1\<close> 
    by (metis assms(2) dvd_imp_le mult_is_0 neq0_conv one_dvd)
qed


lemma preExp2OddPartChar2X2:
  fixes n :: nat
  assumes \<open>n \<ge> 1\<close>
  shows \<open>\<exists> e :: nat.  n = 2^e*(OddPart n) \<close>
proof-
  have \<open>(OddPart n) dvd n\<close> 
    using OddPartL1 assms by blast
  then obtain d :: nat where \<open>n = d * (OddPart n)\<close> 
    by (metis dvd_div_mult_self)
  then obtain e :: nat where \<open>d = 2^e\<close> 
    using OddPartL3 assms by blast
  then show ?thesis 
    using \<open>n = d * OddPart n\<close> by blast
qed

lemma preExp2OddPartChar2:
  fixes n :: nat
  assumes \<open>n \<ge> 1\<close>
  shows \<open> n = 2^(Exp2 n)*(OddPart n) \<close>
proof-
  obtain k :: nat where \<open>n = 2^(Exp2 n)*k\<close> and \<open>odd k\<close> 
    using assms preExp2OddPartChar2X1 by blast
  obtain e :: nat where \<open>n = 2^e*(OddPart n)\<close> and \<open>odd (OddPart n)\<close> 
    using assms preExp2OddPartChar2X2 preExp2OddPartChar1 by presburger
  from  \<open>n = 2^(Exp2 n)*k\<close> \<open>n = 2^e*(OddPart n)\<close> \<open>odd k\<close> \<open>odd (OddPart n)\<close> 
  have \<open>(OddPart n) = k\<close> 
    by (metis UniqnessOddEven)
  then have \<open>2^(Exp2 n) = 2^e\<close> 
    by (metis UniqnessOddEven \<open>n = 2 ^ Exp2 n * k\<close> \<open>n = 2 ^ e * OddPart n\<close> \<open>odd (OddPart n)\<close>)
  then show ?thesis 
    by (smt \<open>n = 2 ^ e * OddPart n\<close>)
qed

lemma preExp2OddPartChar:
  fixes n :: nat
  assumes \<open>n \<ge> 1\<close>
  shows \<open> n = 2^(Exp2 n)*(OddPart n) \<and> odd (OddPart n)  \<close>
  using assms preExp2OddPartChar1 preExp2OddPartChar2 by blast

corollary Exp2OddPartChar:
   \<open> (\<forall> n. (Exp2 0 = 0 \<and> OddPart 0 = 1 \<and> ( n \<ge> 1 \<longrightarrow> n = 2^(Exp2 n)*(OddPart n) \<and> odd (OddPart n) )) ) \<close>
  using  preExp2OddPartChar 
  by (simp add: Exp2_def OddPart_def)

corollary CoroUniqEvenPart:
  fixes f g :: \<open>nat \<Rightarrow> nat\<close>
  assumes \<open>(\<forall> n. (f 0 = 0 \<and> g 0 = 1 \<and> ( n \<ge> 1 \<longrightarrow> n = 2^(f n)*(g n) \<and> odd (g n) )) ) \<close>
  shows \<open>f = Exp2 \<and> g = OddPart\<close>
  using UniqEvenPart Exp2OddPartChar
  by (metis (no_types, hide_lams) Exp2_def OddPart_def assms preUniqEvenPartSQE)

lemma Exp2ValueAt1: \<open>Exp2 (1::nat) = 0\<close>
proof-
  have \<open>(1::nat) = 2^(Exp2 (1::nat))*OddPart (1::nat)\<close> 
    using preExp2OddPartChar by blast
  then show ?thesis 
    by simp
qed

lemma OddPartValueAt1: \<open>OddPart (1::nat) = 1\<close>
proof-
  have \<open>(1::nat) = 2^(Exp2 (1::nat))*OddPart (1::nat)\<close> 
    using preExp2OddPartChar by blast
  then show ?thesis 
    by simp
qed

end

(*
Title: Uniqueness of the representation of a prime as a sum of two squares
Author: Jose Manuel Rodriguez Caballero

Roelof Oosterhuis [SumSquares-AFP] mechanized the so-called Fermat's Christmas Theorem: 
any prime number having the form p = 4k+1 can be represented as a sum of two squares of natural
numbers. In the present development, we contribute to the subject of representation of integers
as a sum of two squares by means of the following uniqueness result: the representation of
a prime p = 4k+1 as a sum of two squares of natural numbers is unique up a to permutation of the
squares. 

Our approach will be like in the proof of Theorem 13.4 in [nathanson2008elementary]. The original
proof involves subtractions, but we attained the same goal using additions and cancellations.


References.

@book{nathanson2008elementary,
  title={Elementary methods in number theory},
  author={Nathanson, Melvyn B},
  volume={195},
  year={2008},
  publisher={Springer Science & Business Media}
}

@article{SumSquares-AFP,
  author  = {Roelof Oosterhuis},
  title   = {Sums of Two and Four Squares},
  journal = {Archive of Formal Proofs},
  month   = aug,
  year    = 2007,
  note    = {\url{http://isa-afp.org/entries/SumSquares.html},
            Formal proof development},
  ISSN    = {2150-914x},
}

(This code was verified in Isabelle2018-RC4/HOL)

*)

theory SumOfSquaresUniqueness

imports Complex_Main "HOL-Number_Theory.Number_Theory"

begin

lemma DiophantusIdentityNat : 
  fixes a b c d :: nat
  assumes kdef: "k + b*d = a*c"
  shows "(a^2 + b^2)*(c^2 + d^2) = k^2 + (a*d + b*c)^2"
proof -
  from kdef have "a^2*c^2 = k^2 + 2*k*b*d + b^2*d^2" by (metis (mono_tags, lifting) power2_sum semiring_normalization_rules(18) semiring_normalization_rules(23) semiring_normalization_rules(30))
  then have "a^2*(c^2 + d^2) = k^2 + 2*k*b*d + b^2*d^2 + a^2*d^2" by (simp add: distrib_left)
  then have "a^2*(c^2 + d^2)+b^2*(c^2 + d^2) = k^2 + 2*k*b*d + b^2*d^2 + a^2*d^2 + b^2*c^2 + b^2*d^2" by (simp add: distrib_left)
  then have "(a^2 + b^2)*(c^2 + d^2) = k^2 + 2*k*b*d + a^2*d^2 + b^2*c^2 + 2* b^2*d^2" by (simp add: semiring_normalization_rules(1))
  then have  "(a^2 + b^2)*(c^2 + d^2) = k^2 + 2*b*d* (k + b*d) + a^2*d^2 + b^2*c^2" by (smt add_mult_distrib2 mult.commute power2_eq_square semiring_normalization_rules(16) semiring_normalization_rules(23) semiring_normalization_rules(25))
  then have  "(a^2 + b^2)*(c^2 + d^2) = k^2 + 2*b*d*a*c + a^2*d^2 + b^2*c^2" using kdef by simp
  thus ?thesis by (simp add: power2_sum power_mult_distrib)
qed


lemma  FermatChristmasUniquenessLem :
  fixes p a\<^sub>1 b\<^sub>1 a\<^sub>2 b\<^sub>2 :: nat
  assumes a1la2: "a\<^sub>1 < a\<^sub>2"
    and podd: "odd p"
    and sumofsq1: "p = a\<^sub>1^2 + b\<^sub>1^2"
    and a1odd: "odd a\<^sub>1"
    and sumofsq2: "p = a\<^sub>2^2 + b\<^sub>2^2"
    and a2odd: "odd a\<^sub>2"
  shows "\<not>  prime p"
proof -
  have  b1lb2: "b\<^sub>1 > b\<^sub>2"
    proof-  
      from a1la2 have a1la2sq: "a\<^sub>1^2 < a\<^sub>2^2" by (simp add: power_strict_mono)
      from sumofsq1 sumofsq2 have "a\<^sub>1^2 + b\<^sub>1^2 =a\<^sub>2^2 + b\<^sub>2^2" by simp
      then   have "b\<^sub>1^2 > b\<^sub>2^2" using  a1la2sq by linarith
      then show ?thesis using power_less_imp_less_base by blast
    qed

    from podd sumofsq1 a1odd have b1eveb: "even b\<^sub>1" by simp
    from podd sumofsq2 a1odd have b2eveb: "even b\<^sub>2" by (simp add: a2odd )

    have "\<exists> x::nat. a\<^sub>2 = a\<^sub>1 + 2*x" 
       proof -
         from a1la2 obtain U::nat where a2eqa1plusU: "a\<^sub>2 = a\<^sub>1 + U" using less_imp_add_positive by blast
         from a2eqa1plusU a1odd a2odd have "even U" using even_add by blast
         then obtain u::nat where Ux: "U = 2*u" using evenE by blast
         from Ux a2eqa1plusU show ?thesis  by blast
       qed
     then obtain x :: nat where xdef: "a\<^sub>2 = a\<^sub>1 + 2*x"  by blast

     have "\<exists> y::nat. b\<^sub>1 = b\<^sub>2 + 2*y"
       proof -
         from b1lb2 obtain V::nat where b1eqb2plusV: "b\<^sub>1 = b\<^sub>2 + V" using less_imp_add_positive by blast
         from b1eqb2plusV have "even V" using even_add  using b1eveb b2eveb by blast
         then obtain v::nat where Vy: "V = 2*v" using evenE by blast
         from Vy b1eqb2plusV show ?thesis  by blast
       qed
       then obtain y::nat where ydef: "b\<^sub>1 = b\<^sub>2 + 2*y" by blast

       obtain d::nat where ddef: "d = gcd x y" by simp
       from a1la2 xdef have x0: "x \<noteq> 0"  by simp 
       from b1lb2 ydef have y0: "y \<noteq> 0"  by simp 
       from ddef have d0: "d \<noteq> 0"  using x0  by auto
       from ddef obtain X::nat where Xdef: "x = d*X" using dvdE by blast
       from ddef obtain Y::nat where Ydef: "y = d*Y" using dvdE by blast
       from x0 Xdef d0 have X0: "X \<noteq> 0" by simp 
       from y0 Ydef d0 have Y0: "Y \<noteq> 0" by simp 
       from ddef d0 Xdef Ydef have gcdXY: "gcd X Y = 1" by (metis gcd_mult_distrib_nat mult_eq_self_implies_10)


       have b1y: "b\<^sub>1*Y = (a\<^sub>1 + x)*X + y*Y"
       proof -
         from xdef have xsq: "a\<^sub>2^2 = a\<^sub>1^2 + 4*x*a\<^sub>1 + 4*x^2" 
          proof -
              show ?thesis
                by (simp add: power2_sum xdef)
            qed
         from ydef have ysq: "b\<^sub>2^2 + 4*y*b\<^sub>2 + 4*y^2 = b\<^sub>1^2"
            proof -
                show ?thesis
                    by (simp add: power2_sum ydef)
                qed
       from xsq ysq  have  "(a\<^sub>2^2 + b\<^sub>2^2) + 4*y*b\<^sub>2 + 4*y^2 = (a\<^sub>1^2 + b\<^sub>1^2) + 4*x*a\<^sub>1 + 4*x^2"  by (simp add: semiring_normalization_rules(21))
       then have "p + 4*y*b\<^sub>2 + 4*y^2 = p + 4*x*a\<^sub>1 + 4*x^2" using sumofsq1 sumofsq2 by simp
       then have "y*b\<^sub>2 + y^2 = x*a\<^sub>1 + x^2" by simp
       then have "y*(b\<^sub>2 + 2*y) = x*a\<^sub>1 + x^2 + y^2"  by (smt add.commute add_mult_distrib2 left_add_mult_distrib mult_2 power2_eq_square semiring_normalization_rules(1))      
       then have "b\<^sub>1*y = a\<^sub>1*x + x^2 + y^2" using ydef by (simp add: semiring_normalization_rules(7))
       then have "d*b\<^sub>1*Y = d*a\<^sub>1*X + d*x*X + d*y*Y" using Xdef Ydef by (metis mult.left_commute power2_eq_square semiring_normalization_rules(18))
       then have "d*b\<^sub>1*Y = d*(a\<^sub>1*X + x*X + y*Y)" by (simp add: distrib_left)
       then have "b\<^sub>1*Y = a\<^sub>1*X + x*X + y*Y" using d0 by simp
       then show ?thesis by (simp add: add_mult_distrib)
     qed

     have  rdef: "\<exists> r::nat. r*Y = a\<^sub>1 + d*X"
       proof -
         from b1y have "Y dvd (a\<^sub>1 + x)*X"  by (metis dvd_add_times_triv_right_iff dvd_triv_right)
         then have "Y dvd (a\<^sub>1 + x)" using gcdXY 
           by (metis (no_types, lifting) division_decomp dvd_triv_right  gcd_greatest_iff mult.right_neutral mult_dvd_mono)

         then show ?thesis by (metis Xdef dvdE semiring_normalization_rules(7))
       qed

     from rdef obtain r::nat where rdef: "r*Y = a\<^sub>1 + d*X" by auto

     from  rdef b1y Xdef Ydef Y0  have  randb1: "b\<^sub>1 = r*X + d*Y"  by (metis add_mult_distrib mult_cancel_right semiring_normalization_rules(16))

     have rd2: "r^2 + d^2 \<ge> 2" by (smt One_nat_def Suc_1 Suc_leI Y0 Ydef add_cancel_left_left add_gr_0 d0 le_add1 le_add2 le_add_same_cancel1 le_antisym le_less mult.commute mult_2_right mult_eq_0_iff power_eq_0_iff randb1 ydef)
     have XY2: "X^2 + Y^2 \<ge> 2" by (metis One_nat_def Suc_leI X0 Y0 add_mono neq0_conv numeral_Bit0 numeral_code(1) power_not_zero)

     from rdef randb1  have "(r^2 + d^2)*(X^2 + Y^2) = a\<^sub>1^2 + b\<^sub>1^2"  by (metis DiophantusIdentityNat add.commute) 
     then have prod2sq: "(r^2 + d^2)*(X^2 + Y^2) = p" using sumofsq1 by blast
     from prod2sq rd2 XY2 show ?thesis by (metis add_diff_cancel_left' diff_is_0_eq' dvd_triv_left mult.right_neutral mult_eq_0_iff nat_mult_eq_cancel_disj numeral_Bit0 numeral_One prime_nat_iff prime_prime_factor_sqrt)
qed

lemma  FermatChristmasUniquenessUpPermOneIsOdd :
  fixes p a\<^sub>1 b\<^sub>1 :: nat
  assumes
   sumofsq1: "p = a\<^sub>1^2 + b\<^sub>1^2"
    and podd: "odd p"
  shows \<open>odd a\<^sub>1 \<or> odd b\<^sub>1\<close>
  using podd sumofsq1 by auto


theorem  FermatChristmasUniqueness:
  fixes p a\<^sub>1 b\<^sub>1 a\<^sub>2 b\<^sub>2 :: nat
  assumes pprime: "prime p"
    and podd: "odd p"
    and sumofsq1: "p = a\<^sub>1^2 + b\<^sub>1^2"
    and a1odd: "odd a\<^sub>1"
    and sumofsq2: "p = a\<^sub>2^2 + b\<^sub>2^2"
    and a2odd: "odd a\<^sub>2"
  shows "a\<^sub>1 = a\<^sub>2 \<and> b\<^sub>1 = b\<^sub>2"
proof-
  from pprime podd sumofsq1 a1odd sumofsq2 a2odd  have a12: "a\<^sub>1 \<ge> a\<^sub>2" 
    using FermatChristmasUniquenessLem leI by blast

  from pprime podd sumofsq1 a1odd sumofsq2 a2odd  have a21: "a\<^sub>2 \<ge> a\<^sub>1"
    using FermatChristmasUniquenessLem leI by blast

  from a12 a21 have a1eqa2: "a\<^sub>1 = a\<^sub>2" using le_antisym by blast 

  from sumofsq1 sumofsq2 a1eqa2 have b1eqb2: "b\<^sub>1 = b\<^sub>2" by auto

  from a1eqa2 b1eqb2 show ?thesis by simp
qed


corollary  FermatChristmasUniquenessUpPermPOdd :
  fixes p a\<^sub>1 b\<^sub>1 a\<^sub>2 b\<^sub>2 :: nat
  assumes pprime: "prime p"
and podd: "odd p"
    and sumofsq1: "p = a\<^sub>1^2 + b\<^sub>1^2"
    and sumofsq2: "p = a\<^sub>2^2 + b\<^sub>2^2"
  shows "(a\<^sub>1 = a\<^sub>2 \<and> b\<^sub>1 = b\<^sub>2) \<or> (a\<^sub>1 = b\<^sub>2 \<and> b\<^sub>1 = a\<^sub>2)"
  by (metis FermatChristmasUniqueness FermatChristmasUniquenessUpPermOneIsOdd add.commute podd pprime sumofsq1 sumofsq2)


end
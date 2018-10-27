(*
Title: The perimeters of Pythagorean triangles
Author: José Manuel Rodriguez Caballero

We present two theorems belonging to the mathematical folklore. Both theorems can be
putted together into the following statement: For any nonzero natural number n, we have
that 2*n is the perimeter of a Pythagorean triangle if and only if n has a pair of
divisors d and e satisfying d < e < 2*d. Notice that the perimeter of a Pythagorean triangle is
always even.


The systematic research about the numbers n having a pair of divisors d and e satisfying
satisfying d < e < 2*d began with Erdos' conjecture [erdos1948density] that the asymptotic
density of this set is exactly 1. The proof of this conjecture, due to  
Maier and Tenenbaum [maier1984set], was a major achievement of Probabilistic Number Theory.

References.

@article{erdos1948density,
  title={On the density of some sequences of integers},
  author={Erd{\"o}s, Paul},
  journal={Bulletin of the American Mathematical Society},
  volume={54},
  number={8},
  pages={685--692},
  year={1948}
}

@article{maier1984set,
  title={On the set of divisors of an integer},
  author={Maier, Helmut and Tenenbaum, G{\'e}rald},
  journal={Inventiones mathematicae},
  volume={76},
  number={1},
  pages={121--128},
  year={1984},
  publisher={Springer}
}

(This code was verified in Isabelle2018)


*)

theory PeriPythTriang

imports Complex_Main "HOL-Number_Theory.Number_Theory"

begin

text {*
the perimeter of a Pythagorean triangle is always even.
*}

proposition PerPythEven: "a^2 + b^2 = (c::nat)^2 \<Longrightarrow> 2 dvd (a+b+c)"
  by (metis even_power odd_add)


text {* 
Given a nonzero natural number n, if n has a pair of divisors d and e
 satisfying d < e < 2*d, then 2*n is the perimeter of a Pythagorean triangle.
*}

theorem ShortDivToPeriPyth:
  fixes n :: nat
  assumes n0: "n \<noteq> 0"
    and Edivshotint: "\<exists> d e. d dvd n \<and> e dvd n \<and> d < e \<and> e < 2*d"
  shows "\<exists> a b c::nat. a \<noteq> 0 \<and> b \<noteq> 0 \<and> a^2 + b^2 = c^2 \<and> a + b + c = 2*n"
proof -
  from Edivshotint obtain d e where ddvdn: "d dvd n" and edvdn: "e dvd n" and dle: "d < e" and eltwod: "e < 2*d" by auto 
  obtain dd::nat where dddef: "d = (gcd d e)*dd" using dvdE by blast
  obtain ee::nat where eedef: "e = (gcd d e)*ee" using dvdE by blast
  from dle dddef eedef have sdle: "dd < ee"  by (metis nat_mult_less_cancel_disj)
  from eltwod dddef eedef  have eeltwod: "ee < 2*dd" by (metis mult.left_commute nat_mult_less_cancel_disj)
  obtain r::nat where rdef: "r = ee" using real_of_nat_div by blast
  obtain s::nat where sdef: "s = 2*dd - ee"  by blast
  from rdef sdef sdle have sler: "s < r" by linarith
  hence sler2: "s^2 < r^2" using pos2 power_strict_mono by blast
  from sler have rsqminusssq: "r^2 - s^2 \<noteq> 0" by (simp add: linorder_not_le power2_nat_le_eq_le)
  from rdef sdef  have rcongs: "2 dvd (r - s)" by (simp add: eeltwod order_less_imp_le)
  from rcongs sler  have twodivdifsq: "2 dvd (r^2 - s^2)" by simp
  from rcongs sler  have twodivsumsq: "2 dvd (r^2 + s^2)" by simp
  from rcongs twodivdifsq twodivsumsq sler obtain x y z ::nat where xdef: "x = r*s" and ydef: "y = (r^2 - s^2)/2" and zdef: "z = (r^2 + s^2)/2"  by  (smt Suc_1 of_nat_1 real_of_nat_div semiring_1_class.of_nat_simps(2))
  from ydef have twoy: "2*y = r^2-s^2" by linarith
  from zdef  have "(r^2 + 2*s^2 - s^2)/2 = z" by simp
  from this sler2 ydef have "s^2 + y = z" by linarith
  hence "(s^2 + y)^2 = z^2" by simp
  hence "(s^2)^2 + 2*(s^2)*y + y^2 = z^2" by (simp add: power2_sum)
  hence "(2*y + s^2)*s^2 + y^2 = z^2" by (simp add: add.commute power2_eq_square semiring_normalization_rules(1) semiring_normalization_rules(16))
  from this twoy have "(r^2-s^2 + s^2)*s^2 + y^2 = z^2" by simp
  hence "r^2*s^2 + y^2 = z^2" by (simp add: less_or_eq_imp_le sler2)
  from this xdef have Pythxyz: "x^2 + y^2 = z^2" by (simp add: power_mult_distrib)
  from xdef ydef zdef have "x+y+z = r*s + (r^2-s^2)/2 + (r^2+s^2)/2"  by (simp add: zdef)
  hence "x+y+z = r*s + ((r^2-s^2) + (r^2+s^2))/2" by simp
  hence "x+y+z = r*s + (2*r^2)/2"  using sler2 by auto
  hence "x+y+z = r*s + r^2" by linarith
  hence "x+y+z = r*(s + r)" by (simp add: distrib_left power2_eq_square)
  from this rdef sdef have "x+y+z = ee*(2*dd-ee + ee)" by blast
  hence sumxyz: "x+y+z = 2*dd*ee" using eeltwod by auto
  from ddvdn dddef have dddvdn: "dd dvd n" by (metis dvd_mult_right)
  from edvdn eedef have eeevdn: "ee dvd n" by (metis dvd_mult_right)
  from dddef eedef have gcdgcd: "gcd dd ee = 1"  by (metis dle gcd_eq_0_iff gcd_mult_distrib_nat gr_implies_not0 mult_eq_self_implies_10)
  from dddvdn eeevdn gcdgcd have "(dd*ee) dvd n" using divides_mult by blast 
  then obtain k::nat where kdef: "n = k*(dd*ee)" by (metis dvd_mult_div_cancel mult.commute)
  obtain a b c::nat where adef: "a = k*x" and bdef: "b = k*y" and cdef: "c = k*z" by simp
  from sumxyz adef bdef cdef kdef have sumabc: "a+b+c = 2*n" by (metis Groups.mult_ac(3) ab_semigroup_mult_class.mult_ac(1) distrib_left)
  from Pythxyz adef bdef cdef have Pythabc: "a^2 + b^2 = c^2" by (metis add_mult_distrib2 semiring_normalization_rules(30))
  from adef have a0: "a \<noteq> 0" using eeltwod kdef n0 sdef sler xdef by auto
  from bdef  have b0: "b \<noteq> 0" using kdef n0 sler2 twoy by auto 
  from a0 b0 Pythabc sumabc show ?thesis  by blast
qed


lemma factorizationinprimes2:  "(k::nat) \<noteq> 0  \<Longrightarrow> (\<Prod>x\<in>prime_factors k. x ^ (2*multiplicity x k)) = k^2"
proof-
  assume "k \<noteq> 0"
  hence "k^2 \<noteq> 0" by simp
  hence  "(\<Prod>x\<in>prime_factors (k^2). x ^ multiplicity x (k^2)) = k^2" using prime_factorization_nat by auto
  hence "(\<Prod>x\<in>prime_factors (k^2). x ^ ( 2*multiplicity x k )) = k^2" by (metis (no_types, lifting) ASSUMPTION_I \<open>k \<noteq> 0\<close> in_prime_factors_imp_prime prime_elem_multiplicity_power_distrib prime_imp_prime_elem' prod.cong)
  thus ?thesis by (simp add: prime_factors_power)
qed

lemma MultSq:
  fixes n k :: nat
  assumes n0: "n \<noteq> 0" 
    and Sq: "n = k^2"
  shows "\<forall> p. p \<in> prime_factors n \<longrightarrow> even (multiplicity p n)"
proof-
  from n0 have k0: "k \<noteq> 0"  by (simp add: Sq)
  hence "(\<Prod>x\<in>prime_factors k. x ^ (2*multiplicity x k)) = n" using factorizationinprimes2 Sq by blast
  thus ?thesis by (simp add: ASSUMPTION_I Sq in_prime_factors_imp_prime k0 prime_elem_multiplicity_power_distrib)
qed


lemma MultSqConverse:
  fixes n :: nat
  assumes n0: "n \<noteq> 0" and
    PrimePowSq: "\<forall> p. p \<in> prime_factors n \<longrightarrow> even (multiplicity p n)"
  shows "\<exists> k. n = k^2"
proof-
  have "\<forall> p. p \<in> prime_factors n \<longrightarrow> 2*((multiplicity p n) div 2) = multiplicity p n" using PrimePowSq dvd_mult_div_cancel by blast
  obtain k where Hk: "(\<Prod>x\<in>prime_factors n. x ^ ((multiplicity x n)div 2)) = k" by auto
  from Hk have "(\<Prod>x\<in>prime_factors n. x ^ ((multiplicity x n)div 2))^2 = k^2" by simp
  hence "(\<Prod>x\<in>prime_factors n. ( x ^ ((multiplicity x n)div 2) )^2 ) = k^2" by (metis (full_types) prod_power_distrib)
  hence "(\<Prod>x\<in>prime_factors n. x ^ (2*((multiplicity x n)div 2)) ) = k^2" by (simp add: \<open>(\<Prod>x\<in>prime_factors n. (x ^ (multiplicity x n div 2))\<^sup>2) = k\<^sup>2\<close> power_even_eq)
  hence "(\<Prod>x\<in>prime_factors n. x ^ (multiplicity x n) ) = k^2" using \<open>\<forall>p. p \<in># prime_factorization n \<longrightarrow> 2 * (multiplicity p n div 2) = multiplicity p n\<close> by auto
  thus ?thesis  using n0 prime_factorization_nat by auto
qed


lemma MultRelPrimes: 
  fixes a b p :: nat
  assumes relprimes: "gcd a b = 1"
    and "prime p"
  shows "multiplicity p a = 0 \<or> multiplicity p b = 0"
  by (metis gcd_greatest_iff multiplicity_unit_left not_dvd_imp_multiplicity_0 relprimes)

lemma MultRelPrimes2: 
  fixes a b p :: nat
  assumes relprimes: "gcd a b = 1"
    and "prime p"
  shows "multiplicity p a = multiplicity p (a*b) \<or> multiplicity p b =  multiplicity p (a*b)"
  by (smt ASSUMPTION_I MultRelPrimes One_nat_def assms(2) gcd.commute gcd_0_nat gcd_greatest_iff mult.right_neutral mult_is_0 multiplicity_normalize_left multiplicity_one_nat multiplicity_prime_elem_times_other multiplicity_unit_left multiplicity_zero not_dvd_imp_multiplicity_0 prime_elem_multiplicity_mult_distrib prime_imp_prime_elem' relprimes zero_neq_one zero_power2)

lemma EvenMultRelPrimes: 
  fixes a b p :: nat
  assumes relprimes: "gcd a b = 1"
    and pprime: "prime p"
    and evenmultab:  "even (multiplicity p (a*b))"
  shows "even (multiplicity p a)"
  by (metis ASSUMPTION_I add.right_neutral assms(2) assms(3) dvd_0_right gcd_greatest_iff multiplicity_unit_left multiplicity_zero not_dvd_imp_multiplicity_0 prime_elem_multiplicity_mult_distrib prime_imp_prime_elem' relprimes)

lemma primeincl: "b \<noteq> 0 \<Longrightarrow> (a::nat) dvd b \<Longrightarrow>  p \<in> prime_factors a \<Longrightarrow> p \<in> prime_factors b" 
proof-
  assume b0: "b \<noteq> 0"
  assume advdb:" a dvd b"
  assume "p \<in> prime_factors a"
  hence pprime: "prime p" and pdvda: "p dvd a" by auto
  have pdvdb: "p dvd b" using \<open>a dvd b\<close> gcd_nat.trans pdvda by blast
  from pprime pdvdb show ?thesis using b0 in_prime_factors_iff by blast
qed

lemma sqProdnatAsym: "b \<noteq> 0 \<Longrightarrow> gcd a b = 1 \<Longrightarrow> k^2 = (a::nat) * b \<Longrightarrow> (\<exists> r. r^2 = a)"
proof -
  assume b0: "b \<noteq> 0"
  assume GCDab1: "gcd a b = 1"
  assume ksqeqab: "k^2 = a*b"
  have "\<forall> p. p \<in> prime_factors (k^2) \<longrightarrow> even (multiplicity p (k^2))" by (metis MultSq even_zero multiplicity_zero)
  hence "\<forall> p. p \<in> prime_factors (k^2) \<longrightarrow> even (multiplicity p (a*b))"  by (simp add: ksqeqab)
  hence "\<forall> p. p \<in> prime_factors (k^2) \<longrightarrow> even (multiplicity p a)" 
    using EvenMultRelPrimes GCDab1 in_prime_factors_imp_prime 
    by metis
  hence "\<forall> p. p \<in> prime_factors a \<longrightarrow> even (multiplicity p a)" by (metis b0 dvdI ksqeqab no_zero_divisors primeincl)
  thus ?thesis by (metis MultSqConverse zero_power2) 
qed

lemma sqProdnat: "k \<noteq> 0 \<Longrightarrow> gcd a b = 1 \<Longrightarrow> k^2 = (a::nat) * b \<Longrightarrow> (\<exists> r s. r^2 = a \<and> s^2 = b)"
  by (metis gcd.commute mult.commute mult_not_zero power_not_zero sqProdnatAsym)

lemma preatleastoneisoddPyth: " (a::nat)^2 + b^2 = c^2 \<Longrightarrow> \<not> ( odd a \<or> odd b)  \<Longrightarrow> \<not>( Gcd {a, b, c} = 1 )"
proof -
  assume Pyth:  "a^2 + b^2 = c^2"
  assume "\<not> ( odd a \<or> odd b)"
  hence evena: "even a" and evenb: "even b" by auto
  hence "even (a^2)" and "even (b^2)" by auto
  hence "even (a^2 + b^2)" by simp
  hence "even (c^2)" using Pyth by simp
  hence evenc: "even c" by simp
  from evena evenb evenc obtain aa bb cc :: nat where "a = 2*aa" and "b = 2*bb" and "c = 2*cc" by (meson evenE)
  hence "Gcd { 2*aa,  2*bb,  2*cc} = Gcd {a, b, c}" by simp
  hence "2*(Gcd { aa,  bb,  cc}) =  Gcd {a, b, c}" by (simp add: gcd_mult_distrib_nat)
  thus ?thesis by auto
qed

lemma atleastoneisoddPyth: " (a::nat)^2 + b^2 = c^2 \<Longrightarrow> Gcd {a, b, c} = 1  \<Longrightarrow>  odd a \<or> odd b"
  using preatleastoneisoddPyth by blast

lemma odddiv: "(n::nat) \<noteq> 0 \<Longrightarrow> d dvd (2*n) \<Longrightarrow> odd d \<Longrightarrow> d dvd n"
proof -
  assume a1: "d dvd 2 * n"
  assume a2: "odd d"
  have f3: "d dvd n * 2"
    using a1 by (simp add: mult.commute)
  have "gcd d 2 = 1"
    using a2 by (meson coprime_imp_gcd_eq_1 coprime_right_2_iff_odd)
  hence "d dvd n * 1"
    using f3 by (metis (no_types) dvd_triv_right  gcd_greatest_iff gcd_mult_distrib_nat)
  thus ?thesis
    by simp
qed

lemma PeriPythToShortDivRelPrimaodd:
  fixes n :: nat
  assumes  n0: "n \<noteq> 0"
    and aodd:  "odd a"
    and b0: " b \<noteq> 0"
    and Pythabc: "a^2 + b^2 = c^2"
    and sumabc: "a + b + c = 2*n"
    and Gcdabc1: " Gcd {a, b, c} = 1"
  shows "\<exists> d e. d dvd n \<and> e dvd n \<and> d < e \<and> e < 2*d"
proof-
  from aodd have a0: "a \<noteq> 0" by (meson even_zero)
  from Pythabc a0 have "b^2 < c^2" by (metis add_diff_cancel_right' aodd odd_pos zero_less_diff zero_less_power) 
  hence blc: "b < c" using power_less_imp_less_base by blast
  then obtain v::nat where vdef: "b + v = c" using less_imp_add_positive by blast
  then obtain u::nat where udef: "u = c + b" by simp
  from Pythabc  have  "a^2+b^2 = (b+v)^2" using vdef by simp
  hence "a^2 + b^2 = 2*b*v + v^2 + b^2"  by (simp add: power2_sum)
  hence "a^2  = 2*b*v + v^2 " by simp
  hence "a^2  = (2*b + v)*v " by (simp add: power2_eq_square semiring_normalization_rules(1))
  hence auv: "a^2 = u*v" by (simp add: udef vdef)
  from auv aodd have uodd: "odd u" 
    by (metis even_mult_iff even_power)
  from auv aodd have vodd: "odd v" 
    using udef uodd vdef by auto
  from uodd vodd have gcduvodd: "odd (gcd u v)" using gcd_nat.bounded_iff by blast
  from udef vdef have "u + v = 2*c" by simp
  hence "(gcd u v) dvd (2*c)" by (metis dvd_add gcd_dvd1 gcd_dvd2)
  from this gcduvodd have gcduvdvdc: "(gcd u v) dvd c"  using blc gr_implies_not0 odddiv by blast
  from udef vdef have bdef: "u - v = 2*b" by simp
  hence "(gcd u v) dvd (2*b)"  by (metis dvd_diff_nat gcd_nat.cobounded1 gcd_nat.cobounded2)
  from this gcduvodd have gcduvdvdb: "(gcd u v) dvd b" using b0 odddiv by blast
  from auv have  "(gcd u v)^2 dvd (a^2)"  by (simp add: mult_dvd_mono power2_eq_square)
  hence gcduvdvda: "(gcd u v) dvd a" by simp
  from gcduvdvda gcduvdvdb gcduvdvdc have "(gcd u v) dvd (Gcd {a, b, c})" by simp
  from Gcdabc1 this  have gcduv1: "gcd u v = 1" by simp
  from gcduv1 auv obtain r s::nat where rdef: "r^2 = u" and sdef: "s^2 = v"  
    by (meson a0 sqProdnat)
  from rdef sdef auv  have "a^2 = (r*s)^2"  by (simp add: power_mult_distrib)
  hence ars: "a = r*s" by simp
  from rdef have rodd: "odd r"  using even_power pos2 uodd by blast
  from sdef have sodd: "odd s"  using even_power pos2 vodd by blast
  obtain e::nat where edef: "e = r" by simp
  from rodd sodd obtain d::nat where ddef: "2*d = r+s" by (metis evenE odd_even_add)
  have slr: "s < r" by (metis \<open>u + v = 2 * c\<close> add_eq_self_zero b0 linorder_neqE_nat mult_2 nat_mult_eq_cancel_disj not_add_less2 odd_pos order_less_imp_le pos2 power_strict_mono rdef rodd sdef semiring_normalization_rules(23) udef vdef) 
  from slr ddef edef have dle: "d < e"  by linarith
  from ddef edef have dltwoe: "e < 2*d" by (simp add: odd_pos sodd)
  from sumabc rdef sdef have "a + u = 2*n" using udef by auto
  hence "a + r^2 = 2*n"  using rdef by blast
  from this ars  have "r*s + r^2 = 2*n" by simp
  hence  "(s + r)*r = 2*n" by (metis power2_eq_square semiring_normalization_rules(1) semiring_normalization_rules(7))
  hence "2*d*e = 2*n" using ddef edef by (simp add: semiring_normalization_rules(24))
  hence den: "d*e = n" by simp
  from den have ddvdn: "d dvd n" using dvdI by blast
  from den have edvdn: "e dvd n" using dvd_triv_right by blast
  show ?thesis  using ddvdn dle dltwoe edvdn by blast
qed

lemma PeriPythToShortDivRelPrim:
  fixes n :: nat
  assumes  n0: "n \<noteq> 0"
    and a0:  "a \<noteq> 0"
    and b0: " b \<noteq> 0"
    and Pythabc: "a^2 + b^2 = c^2"
    and sumabc: "a + b + c = 2*n"
    and Gcdabc1: " Gcd {a, b, c} = 1" 
  shows "\<exists> d e. d dvd n \<and> e dvd n \<and> d < e \<and> e < 2*d"
proof (cases "odd a")
  case True
  hence aodd: "odd a" by simp
  from n0 aodd b0 Pythabc sumabc Gcdabc1  show ?thesis  using PeriPythToShortDivRelPrimaodd  by blast
next
  case False
  hence bodd: "odd b" using Gcdabc1 Pythabc atleastoneisoddPyth by blast
  from Pythabc have Pythbac: "b^2 + a^2 = c^2" by simp
  from sumabc have sumbac: "b + a + c = 2*n" by simp
  from Gcdabc1 have Gcdbac1: "Gcd {b, a, c} = 1"  by (simp add: insert_commute)
  from n0 bodd a0 Pythbac sumbac Gcdbac1  show ?thesis  using PeriPythToShortDivRelPrimaodd by blast
qed

text {* 
Given a nonzero natural number n, if 2*n is the perimeter of a
Pythagorean triangle then n has a pair of divisors d and e satisfying d < e < 2*d.
*}

theorem PeriPythToShortDiv:
  fixes n :: nat
  assumes  n0: "n \<noteq> 0"
    and peripyth: "\<exists> a b c.  a \<noteq> 0 \<and> b \<noteq> 0 \<and> a^2 + b^2 = c^2 \<and> a + b + c = 2*n"
  shows "\<exists> d e. d dvd n \<and> e dvd n \<and> d < e \<and> e < 2*d"
proof-
  from peripyth obtain a b c :: nat where a0: "a \<noteq> 0" and b0: "b \<noteq> 0" and Pythabc: "a^2 + b^2 = c^2" and sumabc: "a + b + c = 2*n" by auto
  have "(Gcd {a, b, c}) dvd a" by simp
  then obtain x :: nat where xdef: "a = (Gcd {a, b, c})*x" using dvdE by blast
  have "(Gcd {a, b, c}) dvd b" by (meson Gcd_dvd_nat insertCI)
  then obtain y :: nat where ydef: "b = (Gcd {a, b, c})*y" using dvdE by blast
  have "(Gcd {a, b, c}) dvd c" by (meson Gcd_dvd_nat insertCI)
  then obtain z :: nat where zdef: "c = (Gcd {a, b, c})*z" using dvdE by blast
  from a0 xdef have x0: "x \<noteq> 0"  using mult_not_zero by fastforce
  from b0 ydef have y0: "y \<noteq> 0"  using mult_not_zero by fastforce 
  from a0 have Gcdabc0: "Gcd {a, b, c} \<noteq> 0" by auto
  from  Gcdabc0 Pythabc xdef ydef zdef have Pythxyz: "x^2 + y^2 = z^2" by (smt add_mult_distrib2 nat_mult_eq_cancel_disj power_eq_0_iff power_mult_distrib)
  from Gcdabc0 xdef ydef zdef have "Gcd {a, b, c} = Gcd {(Gcd {a, b, c})*x, (Gcd {a, b, c})*y, (Gcd {a, b, c})*z}" by simp
  hence "Gcd {a, b, c} = (Gcd {a, b, c})*Gcd {x, y, z}" by (simp add: gcd_mult_distrib_nat)
  hence Gcdxyz1: "Gcd {x, y, z} = 1" using Gcdabc0 by auto
  from xdef ydef zdef  sumabc have gcdxyz2n:  "(Gcd {a, b, c})*(x + y + z) = 2*n"  by (metis distrib_left)
  from this Pythxyz obtain  nn:: nat where nndef: "x+y+z = 2*nn" using PerPythEven dvdE by blast
  from  gcdxyz2n  nndef  have Gcdnn: "(Gcd {a, b, c})*nn = n" by auto
  from this n0 have nn0: "nn \<noteq> 0" using mult_not_zero by blast
  from nn0 x0 y0 Pythxyz nndef Gcdxyz1  have "\<exists> d e. d dvd nn \<and> e dvd nn \<and> d < e \<and> e < 2*d" using PeriPythToShortDivRelPrim by blast
  then obtain dd ee::nat where dddvdn: "dd dvd nn" and eedvdn :"ee dvd nn" and ddlee: "dd < ee" and eeltwodd: "ee < 2*dd" by auto
  then obtain d e:: nat where ddef: "d = (Gcd {a, b, c})*dd" and edef: "e = (Gcd {a, b, c})*ee" by simp
  from ddef edef ddlee have dle: "d < e"  using Gcdabc0 mult_less_mono2 by blast
  from ddef edef eeltwodd have eltwod: "e < 2*d" using Gcdabc0 by auto
  from ddef dddvdn have ddvdn: "d dvd n" using Gcdnn nat_mult_dvd_cancel_disj by blast
  from edef eedvdn have edvdn: "e dvd n" using Gcdnn nat_mult_dvd_cancel_disj by blast
  from ddvdn edvdn show ?thesis using dle eltwod by blast
qed


end
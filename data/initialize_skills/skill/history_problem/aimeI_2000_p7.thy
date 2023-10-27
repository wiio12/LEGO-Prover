theory aimeI_2000_p7
  imports HOL.HOL Complex_Main "HOL-Computational_Algebra.Computational_Algebra" "HOL-Number_Theory.Number_Theory"
begin

lemma cancle_div:
  fixes x a b c:: real
  assumes "x > 0" "a + b / x = c"
  shows "a * x + b = c * x"
proof -
  have "x * (a + b / x) = c * x"
    using assms(2) by auto
  then have "x * a + x * (b / x) = c * x"
    by (simp add: distrib_left)
  then show ?thesis
    using assms(1) by (simp add: mult.commute)
qed


theorem
  fixes x y z :: real
    and p :: rat
  assumes "0 < x ∧ 0 < y ∧ 0 < z"
    and "x * y * z = 1"
    and "x + 1 / z = 5"
    and "y + 1 / x = 29"
    and "z + 1 / y = p"
    and "0 < p" 
  shows "let (m,n) = quotient_of p in m + n = 5"
proof -
  (* We can rewrite $xyz=1$ as $\frac{1}{z}=xy$. *)
  have c0: "z = 1 / (x*y)"
    using assms(1) assms(2)
    by (smt (verit, ccfv_threshold) mult_eq_0_iff nonzero_mult_div_cancel_left)
  
  (* Substituting into one of the given equations, we have
  $x+xy=5$
  $x(1+y)=5$
  $\frac{1}{x}=\frac{1+y}{5}.$ *)
  have "x + x * y = 5" 
    using c0 assms(3) by simp
  then have "x * (1 + y) = 5"
    by (simp add: distrib_left)
  (*add*) then have "x = 5 / (1 + y)" using assms(1) 
    by (smt (verit, best) nonzero_divide_eq_eq)
  then have c1:"1 / x = (1 + y) / 5"
    by simp

  (* We can substitute back into $y+\frac{1}{x}=29$ to obtain
  $y+\frac{1+y}{5}=29$
  $5y+1+y=145$
  $y=24.$ *)
  have "y + (1+y)/5 = 29" 
    using assms(4) c1 by auto
  then have "5*y + (1 + y) = 145" 
    using cancle_div[of 5 "y" "1+y" 29] by auto
  then have c2:"y = 24" by simp

  (* We can then substitute once again to get
  $x=\frac15$
  $z=\frac{5}{24}.$ *)
  have c3:"x = 1 / 5" 
    by (simp add: ‹x = 5 / (1 + y)› c2)
  have c4: "z = 5 / 24"
    using c0 c2 c3 by simp
  
  (* Thus, $z+\frac1y=\frac{5}{24}+\frac{1}{24}=\frac{1}{4}$, so $m+n=005$. *)
  have "p = z + 1/y" using assms(5) by simp
  also have "... = 5/24 + 1/24" unfolding c2 c4 by simp
  also have "... = 1/4" by simp
  finally have c5: "p = 1/4"
    by (metis (mono_tags, lifting) of_rat_1 of_rat_divide of_rat_eq_iff of_rat_numeral_eq)
  have "quotient_of p = (1, 4)" unfolding c5 by eval
  then show ?thesis by simp
qed

end
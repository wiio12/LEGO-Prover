theory algebra_amgm_faxinrrp2msqrt2geq2mxm1div2x
  imports Complex_Main "HOL-Library.Sum_of_Squares"
begin

lemma a_times_vera:
  fixes a :: real
  assumes "a ≠ 0"
  shows " a * (1 / a) = 1"
  by (simp add: assms)
  


theorem
  fixes x :: real
  assumes "x > 0"
  shows "2 - sqrt 2 ≥ 2 - x - 1/ (2 * x)"
proof -
  (* First notice that $2x$ is positive. *)
  have c0: "2 * x > 0" using assms
    by simp
  (* It suffices to show $\sqrt{2} \leq x + \frac{1}{2x}$. *)
  have "sqrt 2 ≤ x + 1 / (2 * x)"
  proof -
    (* Let $y = \sqrt{2}$. $y*y = 2$. *)
    define y where "y = sqrt 2"
    have c1: "2 = y * y"
      by (simp add: y_def)


    (* Then $2x*x + 1 - 2x * \sqrt{2} = y*y * x*x + 1 - 2xy = (xy - 1)^2 \geq 0$. *)
    have c2: "2 * x * x + 1 - 2 * x * (sqrt 2) = (y * y * x * x) + 1 - 2 * x * y"
      using c1 y_def by simp
    then have "... = (y*x) * (y*x) - 2 * (y*x) + 1" by simp
    also have "... = (y*x - 1) * (y*x - 1)" by sos
    also have "... ≥ 0" by simp
    ultimately have c3: "2 * x * x + 1 - 2 * x * (sqrt 2) ≥ 0" 
      by (simp add: c2)


    (* Also notice that $2x*x + 1 - 2x * \sqrt{2} = 2x * (x + \frac{1}{2x} - \sqrt{2})$. *)
    have "(2*x) * (x + 1/(2*x) - sqrt 2) = (2 * x) * x + 1 - (2*x) * sqrt 2"
      by (smt (verit) a_times_vera c0 right_diff_distrib)
    also have "... ≥ 0" using c3
      by simp

    (* Therefore $x + \frac{1}{2x} - \sqrt{2} \geq 0$, given $2x > 0$. *)
    ultimately have "(2*x) * (x + 1/(2*x) - sqrt 2) ≥ 0" 
      by auto
    hence "x + 1/(2*x) - sqrt 2 ≥ 0" using c0
      by (simp add: zero_le_mult_iff)

    (* Rearranging terms, we see that the required inequality holds. *)
    then show ?thesis
      by simp
  qed
  then show ?thesis
    by simp
qed

end
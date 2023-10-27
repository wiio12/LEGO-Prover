theory aime_1984_p5
  imports Complex_Main "HOL-Library.Sum_of_Squares"
begin


lemma cal_log_exp_value:
  fixes a :: real
  assumes "a > 0" "a ≠ 1" "n > 0"
  shows "log a (a^n) = n"
proof -
  have c0: "log a a = 1"
    by (simp add: assms(1) assms(2))
  have "log a (a^n) = n * (log a a)"
    using log_nat_power[of a a n] by (simp add: assms(1))
  then have c1: "log a (a^n) = n"
    using c0 by simp
  then show ?thesis 
    by (simp add: c1)
qed


lemma cal_log_value:
  assumes "a > 0" and "a ≠ 1" and "b > 0" and "log a b = c"
  shows "b = a ^ c"
  by (metis assms(1) assms(2) assms(3) assms(4) powr_log_cancel powr_realpow)


theorem
  fixes a b ::real
  assumes 
    "a > 0"
    "b > 0"
    "(log 2 a) / (log 2 8) + (log 2 (b^2)) / (log 2 4) = 5"
    "(log 2 b) / (log 2 8) + (log 2 (a^2)) / (log 2 4) = 7"
  shows "a * b = 512"
proof -

  (* We first calculate that $\log_2=1$ and $\log_8=3$. *)
  have c1: "log 2 8 = 3"
    using cal_log_exp_value[of 2 3] by simp
  have c2: "log 2 4 = 2"
    using cal_log_exp_value[of 2 2] by simp

  (* Then let $c=\log_a$ and $d=\log_b$. We can write the equations as $\frac{c}{3} + 2*\frac{d}{2}=5$ and $\frac{d}{3} + 2*\frac{c}{2}=7$. *)
  define c where "c = log 2 a"
  define d where "d = log 2 b"
  have c3: "c / 3 + 2 * d / 2 = 5"
    using c_def d_def assms(3) c1 c2 log_nat_power 
    by (simp add: assms(2) log_mult)

  have c4: "d / 3 + c = 7"
    using c_def d_def assms(4) c1 c2 log_nat_power
    by (simp add: assms(1) log_mult)
  
  (* Solving the equations and we get $c=6$ and $d=3$. 
  Hence $a=2^6=64$ and $b=2^3=8$. Multiply them together and $ab=512$. *)
  have "d = 3" using c3 c4 
    by simp
  then have c5:"b = 2^3" using d_def cal_log_value[of 2 b 3]
    by (simp add: assms(2))

  have "c = 6" using c3 c4
    by simp
  then have c6:"a = 2^6" using c_def cal_log_value[of 2 a 6]
    by (simp add: assms(1))

  show ?thesis unfolding c5 c6 by simp
qed

end
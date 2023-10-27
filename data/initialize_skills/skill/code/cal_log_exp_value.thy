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
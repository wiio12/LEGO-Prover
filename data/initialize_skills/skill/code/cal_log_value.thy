lemma cal_log_value:
  assumes "a > 0" and "a ≠ 1" and "b > 0" and "log a b = c"
  shows "b = a ^ c"
by (metis assms(1) assms(2) assms(3) assms(4) powr_log_cancel powr_realpow)
lemma a_times_vera:
  fixes a :: real
  assumes "a ≠ 0"
  shows " a * (1 / a) = 1"
  by (simp add: assms)
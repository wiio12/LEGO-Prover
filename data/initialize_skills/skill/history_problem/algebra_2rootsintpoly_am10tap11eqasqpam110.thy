theory algebra_2rootsintpoly_am10tap11eqasqpam110
  imports Complex_Main "HOL-Library.Sum_of_Squares"
begin

lemma multi_distrib_complex:
  fixes a b c d :: complex
  shows "(a + b) * (c + d) = a * c + a * d + b * c + b * d"
  by (simp add: distrib_left distrib_right)


theorem
  fixes a :: complex
  shows "(a-10) * (a+11) = a^2 + a -110"
proof -
  
  (* We first expand all terms of the left hand side to get $a^2 - 10a + 11a - 10*11$. *)
  have "(a-10) * (a+11) = a^2 - 10*a + 11*a - 10 *11"
    using multi_distrib_complex[of a "-10" a 11] by (simp add: power2_eq_square)
  (* This equals $a^2 + a - 10*11 = a^2 + a - 110$. *)
  then show ?thesis
    by simp
qed

end
theorem
  fixes a b c d :: complex
  shows "(a-d) * (a-c) * (a-b) = -(((a^2 - (b+c) * a) + c * b) * d) + (a^2 - (b+c) * a + c * b) * a"
proof -
  (* We first see that $a^2 = a * a$ trivially. *)
  have t0: "a^2 = a * a"
    using power2_eq_square
      sledgehammer
  (* Unfolding this, the main equation holds true when terms are rearranged. *)
  show ?thesis unfolding t0
    sledgehammer
qed
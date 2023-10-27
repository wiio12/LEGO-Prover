theorem
  fixes a b :: nat
  assumes h0 : "1\<le>a \<and> a \<le>9 \<and> b \<le>9"
    and h1 : "10 * a + b = 2 * (a+b)"
  shows "10 * a + b = 18"
proof -
  (* We simplify $10a + b = 2(a+b)$ to get $8a = b$. *)
  have c0: "8 * a = b" using h1 sledgehammer
  (* Since $a$ is at least 1, $b$ is at least 8. *)
  hence "b \<ge> 8" using h0 sledgehammer
  (* We know $b$ is 8 since $8a = b$ and $a$ is a natural number. *)
  hence c1:"b = 8" using h0 c0
    sledgehammer
  (* Hence $a$ is 1. *)
  hence "a = 1" using c0 sledgehammer
  (* The two-digit integer is hence $18$. *)
  then show ?thesis using c1 sledgehammer
qed
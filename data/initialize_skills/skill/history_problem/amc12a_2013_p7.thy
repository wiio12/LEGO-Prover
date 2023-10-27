theorem
  fixes s :: "nat \<Rightarrow> real"
  assumes h0 : "\<And>n. s (n+2) = s (n+1) + s n"
    and h1 : "s 9 = 110"
    and h2 : "s 7 = 42"
  shows "s 4 = 10"
proof -
  (* $S_9 = 110$, $S_7 = 42$

  $S_8 = S_9 - S_ 7 = 110 - 42 = 68$ *)
  have "s 8 = 68" using h1 h2 h0[of 7] sledgehammer
  (* $S_6 = S_8 - S_7 = 68 - 42 = 26$ *)
  hence h3: "s 6 = 26" using h2 h0[of 6] sledgehammer
  (* $S_5 = S_7 - S_6 = 42 - 26 = 16$ *)
  hence "s 5 = 16" using h2 h0[of 5] sledgehammer
  (* $S_4 = S_6 - S_5 = 26 - 16 = 10$ *)
  then show ?thesis using h3 h0[of 4] sledgehammer
qed
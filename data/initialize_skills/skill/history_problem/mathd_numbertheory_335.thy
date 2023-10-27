theorem
  fixes n :: nat
  assumes h0 : "n mod 7 = 5"
  shows "(5 * n) mod 7 = 4"
proof -
  (* Then $n \equiv 5 \pmod{7}$, so $5n \equiv 5 \cdot 5 \equiv 25 \equiv 4 \pmod{7}$. *)
  have c0:"(5 * n) mod 7 = (5 * 5) mod 7" using h0
    sledgehammer
  then have "\<dots> = 4" sledgehammer
  then have "(5 * n) mod 7 = 4" using c0 sledgehammer
  then show ?thesis sledgehammer
qed
theorem
  fixes a :: int
  shows "a^2 mod 3 = 0 \<or> a^2 mod 3 = 1"
proof -
  (* Let $b = a mod 3$. *)
  obtain b::int where c0: "b = a mod 3" sledgehammer
  (* We know that b can only be 0, 1, or 2. *)
  have c1: "b \<ge> 0 \<and> b \<le> 2"
    sledgehammer
  (* Also, $a^2 mod 3 = b^2 mod 3$. *)
  hence c2: "a^2 mod 3 = b^2 mod 3" using c0
    sledgehammer
  then show ?thesis
  (* If $b=0$, $a^2 mod 3 = 0^2 mod 3 = 0$;
  If $b=1$, $a^2 mod 3 = 1^2 mod 3 = 1$;
  If $b=2$, $a^2 mod 3 = 2^2 mod 3 = 1$.*)
  proof (cases "b=0")
    case True
    have "a^2 mod 3 = 0" using True c0 sledgehammer
    then show ?thesis sledgehammer
  next
    case c3: False
    then show ?thesis
    proof (cases "b=1")
      case True
      have "a^2 mod 3 = 1" using True c0
        sledgehammer
      then show ?thesis sledgehammer
    next
      case False
      have "b = 2" using c1 c3 False sledgehammer
      hence "a^2 mod 3 = 2^2 mod 3" using c2 sledgehammer
      also have "... = 1" sledgehammer
      finally have "a^2 mod 3 = 1" sledgehammer
      then show ?thesis sledgehammer
    qed
  qed
qed
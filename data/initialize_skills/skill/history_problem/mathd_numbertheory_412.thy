theory mathd_numbertheory_412
imports Complex_Main 
begin

lemma mod_add_power:
  fixes x n a b c :: nat
  assumes "n > 0" "b > 0" "c > 0" "x mod n = a"
  shows "((x + b)^c) mod n = ((a + b)^c) mod n"
proof -
  have "(x + b)^c mod n = ((x mod n) + b)^c mod n"
    by (smt (verit) mod_add_left_eq power_mod)
  also have "... = (a + b)^c mod n"
    using assms(4) by auto
  finally show ?thesis by auto
qed


theorem
  fixes x y :: nat
  assumes h0 : "x mod 19 = (4:: nat)"
    and h1 : "y mod 19 = (7:: nat)"
  shows "(x+1)^2 * (y+5)^3 mod 19 = (13:: nat)"
proof -
  (* (x + 1)^2 (y + 5)^3 &\equiv 5^2 \cdot 12^3 
  &\equiv 6 \cdot 18 *)
  have c0: "(x+1)^2 mod 19 = 5^2 mod 19"
    using mod_add_power[where x="x" and n=19 and b=1 and a=4 and c=2] h0 by simp
  have c1: "(y+5)^3 mod 19 = 12^3 mod 19"
    using mod_add_power[where x="y" and n=19 and b=5 and a=7 and c=3] h1 by simp
  have "(x+1)^2 * (y+5)^3 mod 19 = ((x+1)^2 mod 19) * ((y+5)^3 mod 19) mod 19"
    by (metis mod_mult_eq)
  also have "... = 6 * 18 mod 19" unfolding c0 c1 by auto
  (* &\equiv 13 *)
  also have "... = 13" by auto
  finally show ?thesis by auto
qed

end
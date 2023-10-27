theory algebra_binomnegdiscrineq_10alt28asqp1
  imports Complex_Main "HOL-Library.Sum_of_Squares"
begin

theorem
  fixes a :: real
  shows "10 * a \<le> 28 * a^2 + 1"
proof -
(* it suffices to show $0\leq 28a^2 - 10a + 1$ *)
    
  have c0: "0 \<le> 28*a^2 - 10*a + 1"
  proof -
    (* observe that $(a - \frac{5}{28})^2 = a^2 - \frac{10}{28}a + (5/28)^2$ *)
    have c1: "(a - (5/28))^2 = a^2 - 10/28*a + (5/28)^2"
      by sos
    (* we have $0\leq a^2 - \frac{10}{28}a + (5/28)^2$ *)
    then have c2: "0 \<le> a^2 - 10/28*a + (5/28)^2" using c1
      by sos
    (* Multiplying by 28 and simplifying terms gives $0\leq 28*a^2 - 10*a + (25/28)$ *)
    then have c3: "0 \<le> 28*a^2 - 10*a + (25/28)" using c2
      by sos
    (* Since $25/28 < 1$, the result follows. *)
    then show ?thesis using c3
      by auto
  qed
  then show ?thesis
    by auto
qed

end
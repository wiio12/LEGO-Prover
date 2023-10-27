theorem
  fixes n ::nat
  assumes "n>0"
    and prime:"prime (n^2+2-3*n)"
  shows "n=3"
proof -
  have "n>2" 
  proof (rule ccontr)
    assume "\<not> 2 < n"
    then have "n=1 \<or> n=2" using \<open>n>0\<close> sledgehammer
    then show False using prime[THEN prime_gt_1_nat]
      sledgehammer
  qed
  (* Factoring, we get $n^2 - 3n + 2 = (n-2)(n-1)$. *)
  then have "n^2+2-3*n  = (n-1) * (n-2)"
    unfolding power2_eq_square
    sledgehammer
  (* Either $n-1$ or $n-2$ is odd, and the other is even.  
  Their product must yield an even number.  
  The only prime that is even is $2$, which is when $n$ is $3$ or $0$. 
  Since $0$ is not a positive number, the answer is $\mathrm{(B)}\ \text{one}$.*)
  then have "prime ((n-1) * (n-2))"
    using prime sledgehammer
  then have "n-1=1 \<or> n-2 = 1"
    using prime_product sledgehammer
  with \<open>n>2\<close>
  show "n=3" sledgehammer
qed
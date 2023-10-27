theory mathd_numbertheory_48
  imports Complex_Main "HOL-Library.Sum_of_Squares"
begin

theorem
  fixes b :: real
  assumes h0 : "0 < b"
    and h1 : "3 * b^2 + 2 * b + 1 = 57"
  shows "b=4"
proof -
  (* Converting $321_{b}$ to base 10 and setting it equal to 57, we find that egin{align*} 3(b^2)+2(b^1)+1(b^0)&=57
  \ 3b^2+2b+1&=57
  \\Rightarrow\qquad 3b^2+2b-56&=0
  \\Rightarrow\qquad (3b+14)(b-4)&=0
  \end{align*} *)
  have "0 = 3 * b^2 + 2 * b -56" using h1
    by auto
  also have "... = (3*b+14)*(b-4)" 
    by sos
  finally have "0 = (3*b+14)*(b-4)" 
    by auto
  (* This tells us that $b$ is either $-
                                        rac{14}{3}$ or $4$. *)
  then have "b = -14/3 \<or> b=4" 
    by auto
  (* We know that $b>0$, so $b=4$. *)
  then show ?thesis using h0 
    by auto
qed

end
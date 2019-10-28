theory tutorial_3
imports
Main

begin

locale group =
  fixes on :: "'p ⇒ 'l ⇒ bool" 
  assumes line_on_two_pts: "a ≠ b ⟹ ∃l. on a l ∧ on b l"
   and line_on_two_pts_unique: "⟦ a ≠ b; on a l; on b l; on a m; on b m ⟧ ⟹ l = m"
  and two_points_on_line: "∃a b. a ≠ b ∧ on a l ∧ on b l"
  and three_points_not_on_line: "∃a b c. a ≠ b ∧ a ≠ c ∧ b ≠ c ∧ 
                                    ¬ (∃l. on a l ∧ on b l ∧ on c l)" 

(* PROOFS START *) 

begin

(* not all points lie on the same line. *) 
lemma exists_a_point_not_on_line: "∃x. ¬ on x l"
proof - 
  obtain a b c where lines: "¬ (on a l ∧ on b l ∧ on c l)" 
    using three_points_not_on_line by blast
  then show ?thesis by blast
qed

(* there exist at least two lines through each point. *) 
lemma two_lines_through_each_point: "∃l k. on x l ∧ on x k ∧ l ≠ k"
proof - 
  have "∃z. z ≠ x" 
  proof (rule ccontr)
    from two_points_on_line obtain a b where ab: "(a::'p) ≠ b" by blast
    assume "∄z. z ≠ x"
    then have univ: "∀z. z = x" by blast 
    then have "a = x" and "b = x" by auto 
    then show False
      using ab by simp
  qed
  then obtain z where "z ≠ x" by blast
  then obtain l where xl: "on x l" and zl: "on z l" using line_on_two_pts by blast
  obtain w where n_wl: "¬ on w l" using exists_a_point_not_on_line by blast
  obtain m where wm: "on x m" and zm: "on w m" using line_on_two_pts xl by force
  then have "l ≠ m" using n_wl by blast
  thus ?thesis using wm xl by blast
qed

(* two lines cannot intersect in more than one point.
   proof method: prove that they are the same line if they do. *)
lemma two_lines_unique_intersect_pt: 
  assumes lm: "l ≠ m" and "on x l" and "on x m" and "on y l" and "on y m"
  shows "x = y"
  proof (rule ccontr)
    assume "x ≠ y"
    then have "l = m"
      using assms(2) assms(3) assms(4) assms(5) line_on_two_pts_unique by simp
    thus False
      using lm by simp
  qed

end

(* PROOFS END *) 


end

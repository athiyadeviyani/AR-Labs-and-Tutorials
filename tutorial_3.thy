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
begin


lemma exists_a_point_not_on_line: "∃x. ¬ on x l"
proof - 
  obtain a b c where lines: "¬ (on a l ∧ on b l ∧ on c l)" 
    using three_points_not_on_line by blast
  then show ?thesis by blast
qed


lemma two_lines_through_each_point: "∃l m. on x l ∧ on x m ∧ l ≠ m"
  oops

lemma two_lines_unique_intersect_pt: 
  oops


end

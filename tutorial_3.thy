theory tutorial_3
imports
Main

begin

locale Geom =
  fixes on :: "'p \<Rightarrow> 'l \<Rightarrow> bool" 
  assumes line_on_two_pts: "a \<noteq> b \<Longrightarrow> \<exists>l. on a l \<and> on b l"
   and line_on_two_pts_unique: "\<lbrakk> a \<noteq> b; on a l; on b l; on a m; on b m \<rbrakk> \<Longrightarrow> l = m"
  and two_points_on_line: "\<exists>a b. a \<noteq> b \<and> on a l \<and> on b l"
  and three_points_not_on_line: "\<exists>a b c. a \<noteq> b \<and> a \<noteq> c \<and> b \<noteq> c \<and> 
                                    \<not> (\<exists>l. on a l \<and> on b l \<and> on c l)"
begin


lemma exists_pt_not_on_line: "\<exists>x. \<not> on x l"
proof - 
  obtain a b c where l3: "\<not> (on a l \<and> on b l \<and> on c l)" using three_points_not_on_line by blast
  thus ?thesis by blast
qed


lemma two_lines_through_each_point: "\<exists>l m. on x l \<and> on x m \<and> l \<noteq> m"
  oops

lemma two_lines_unique_intersect_pt: 
  oops


end

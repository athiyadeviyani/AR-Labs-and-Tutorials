theory tutorial_4
imports Main

begin

lemma 1: "(P ⟶(Q⟶R))⟶((P⟶Q)⟶(P⟶R))"
proof (rule impI)+
  assume 1: "(P ⟶(Q⟶R))" and 2: "P⟶Q" and 3: "P"
  from 2 and 3
  have 4: "Q" by (rule mp)
  from 1 and 3
  have 5: "Q⟶R" by (rule mp)
  from 5 and 4
  show "R" by (rule mp) (* replace with blast *)
qed


lemma 2: "(∀x. P x ⟶ Q) ⟶ (∃x. P x ⟶ Q)"
proof 
  assume "(∀x. P x ⟶ Q)" then have "P a ⟶ Q" by blast
  then show "(∃x. P x ⟶ Q)" by blast
qed


lemma 3: assumes ex: "\<not>(\<exists>x. P x)" shows all: "\<forall>x. \<not>P x"
  oops

lemma 4: assumes n_all: "\<not>(\<forall>x. P x)" shows "\<exists>x. \<not>P x"
  oops

lemma "(R \<longrightarrow> P) \<longrightarrow> (((\<not>R \<or> P) \<longrightarrow> (Q \<longrightarrow> S)) \<longrightarrow> (Q \<longrightarrow> S))"
  oops

end

theory tutorial_4
imports Main

begin

lemma 1: "(P \<longrightarrow>(Q\<longrightarrow>R))\<longrightarrow>((P\<longrightarrow>Q)\<longrightarrow>(P\<longrightarrow>R))"
proof (rule impI, rule impI, rule impI)
  assume "P" "P \<longrightarrow> Q \<longrightarrow> R" 
    then have qr: "Q \<longrightarrow> R" by fast
    assume "P" "P \<longrightarrow> Q" 
    then have "Q" by blast
    then show "R" using qr by blast
qed

lemma 2: "(\<forall>x. P x \<longrightarrow> Q)\<longrightarrow>(\<exists>x. P x\<longrightarrow>Q)"
proof 
  assume "\<forall>x. P x \<longrightarrow> Q" then have "P a \<longrightarrow> Q" ..
  then show "(\<exists>x. P x\<longrightarrow>Q)" ..
qed

lemma 3: assumes ex: "\<not>(\<exists>x. P x)" shows all: "\<forall>x. \<not>P x"
  oops

lemma 4: assumes n_all: "\<not>(\<forall>x. P x)" shows "\<exists>x. \<not>P x"
  oops

lemma "(R \<longrightarrow> P) \<longrightarrow> (((\<not>R \<or> P) \<longrightarrow> (Q \<longrightarrow> S)) \<longrightarrow> (Q \<longrightarrow> S))"
  oops

end
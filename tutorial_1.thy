theory tutorial_1
imports Main
begin

lemma 1: "(P \<longrightarrow> (Q \<longrightarrow> R)) \<longrightarrow> ((P \<longrightarrow> Q) \<longrightarrow> (P \<longrightarrow> R))"
  apply (rule impI)+
  apply (erule impE)
   apply assumption
  apply (erule mp)
  apply (erule impE)
   apply assumption
  apply assumption

lemma 2: "\<not>\<not>P \<longrightarrow> P"
  apply (rule impI)+
  apply (rule classical)
  apply (erule notE)
  apply assumption

lemma 3: "(P \<longrightarrow> Q \<and> R) \<longrightarrow> ((P \<longrightarrow> Q) \<and> (P \<longrightarrow> R))"
  apply (rule impI)
  apply (rule conjI)
   apply (rule impI)
   apply (erule impE)
  apply assumption
   apply (erule conjE)
   apply assumption
  apply (rule impI)
  apply (erule impE)
   apply assumption
  apply (erule conjE)
  apply assumption

lemma 4: "(\<not>P \<longrightarrow> Q) \<longrightarrow> (\<not>Q \<longrightarrow> P)"
  apply (rule impI)+
  apply (rule classical)
  apply (erule notE)
  apply (erule impE)
   apply assumption
  apply assumption

lemma 5: "P \<or> \<not>P"
  apply (rule classical)
  apply (rule disjI1)
  apply (rule classical)
  apply (erule notE)
  apply (rule disjI2)
  apply assumption



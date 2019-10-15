theory tutorial_2 imports Main

begin

lemma 1: "(\<forall> x. P x \<longrightarrow> Q) \<longrightarrow> (\<exists> x. P x \<longrightarrow> Q)" 
  apply (rule impI)
  apply (rule exI)
  apply (rule allE)
   apply assumption+


lemma 2: "\<not>(\<exists> x. P x) \<Longrightarrow> \<forall> x. \<not>P x" 
  apply (rule allI)
  apply (rule notI)
  apply (erule notE)
  apply (rule exI)
  apply assumption

lemma 3: "\<not>(\<forall> x. P x) \<Longrightarrow> \<exists> x. \<not>P x"
  apply (rule ccontr)
  apply (erule notE)
  apply (rule allI)
  apply (rule ccontr)
  apply (erule notE)
  apply (rule exI)
  by assumption
  

end

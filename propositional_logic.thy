(*
    ex.thy,v 1.1 2016/09/29 17:37:37 jdf Exp
    Original Author: Tjark Weber
    Updated to Isabelle 2016 and additions by Jacques Fleuriot

    File completed and renamed to: propositional_logic.thy
    Name: Athiya Deviyani
    UUN: S1709906
*)

section {* Propositional Logic *}

theory propositional_logic imports Main begin 

text {* In this exercise, we will prove some lemmas of propositional
logic with the aid of a calculus of natural deduction.

For the proofs, you may only use

notI: (?P \<Longrightarrow> False) \<Longrightarrow> \<not> ?P
notE: \<lbrakk>\<not> ?P; ?P\<rbrakk> \<Longrightarrow> ?R
conjI: \<lbrakk>?P; ?Q\<rbrakk> \<Longrightarrow> ?P \<and> ?Q
conjE: \<lbrakk>?P \<and> ?Q; \<lbrakk>?P; ?Q\<rbrakk> \<Longrightarrow> ?R\<rbrakk> \<Longrightarrow> ?R
disjI1:?P \<Longrightarrow> ?P \<or> ?Q
disjI2: ?Q \<Longrightarrow> ?P \<or> ?Q
disjE: \<lbrakk>?P \<or> ?Q; ?P \<Longrightarrow> ?R; ?Q \<Longrightarrow> ?R\<rbrakk> \<Longrightarrow> ?R
impI: (?P \<Longrightarrow> ?Q) \<Longrightarrow> ?P \<longrightarrow> ?Q
impE:\<lbrakk>?P \<longrightarrow> ?Q; ?P; ?Q \<Longrightarrow> ?R\<rbrakk> \<Longrightarrow> ?R
mp: \<lbrakk>?P \<longrightarrow> ?Q; ?P\<rbrakk> \<Longrightarrow> ?Q
iffI:\<lbrakk>?P \<Longrightarrow> ?Q; ?Q \<Longrightarrow> ?P\<rbrakk> \<Longrightarrow> ?P = ?Q
iffE:\<lbrakk>?P = ?Q; \<lbrakk>?P \<longrightarrow> ?Q; ?Q \<longrightarrow> ?P\<rbrakk> \<Longrightarrow> ?R\<rbrakk> \<Longrightarrow> ?R
classical: (\<not> ?P \<Longrightarrow> ?P) \<Longrightarrow> ?P


and the proof methods rule, erule and assumption.
\end{itemize}

Prove:
*}
  

lemma I: "A \<longrightarrow> A"
  apply (rule impI)
  apply assumption
  done


lemma "A \<and> B \<longrightarrow> B \<and> A"
  apply (rule impI)
  apply (erule conjE)
  apply (rule conjI)
   apply assumption
  apply assumption

lemma "(A \<and> B) \<longrightarrow> (A \<or> B)"
  apply (rule impI)
  apply (erule conjE)
  apply (rule disjI1)
  apply assumption


lemma "((A \<or> B) \<or> C) \<longrightarrow> A \<or> (B \<or> C)"
  apply (rule impI)
  apply (erule disjE)
   apply (erule disjE)
    apply (rule disjI1)
    apply assumption
   apply (rule disjI2)
   apply (rule disjI1)
  apply assumption
  apply(rule disjI2)
  apply (rule disjI2)
  apply assumption 

lemma K: "A \<longrightarrow> B \<longrightarrow> A"
  apply (rule impI)
  apply (rule impI)
  apply assumption

lemma "(A \<or> A) = (A \<and> A)"
  apply (rule iffI)
   apply (erule disjE)
    apply (rule conjI)
     apply assumption
    apply assumption
   apply (rule conjI)
    apply assumption
  apply assumption
  apply (erule conjE)
  apply (rule disjI1)
  apply assumption

lemma S: "(A \<longrightarrow> B \<longrightarrow> C) \<longrightarrow> (A \<longrightarrow> B) \<longrightarrow> A \<longrightarrow> C"
  apply (rule impI)+
  apply (erule impE)
   apply assumption
  apply (erule impE)
    apply assumption
  apply (erule impE)
   apply assumption
  apply assumption

lemma "(A \<longrightarrow> B) \<longrightarrow> (B \<longrightarrow> C) \<longrightarrow> A \<longrightarrow> C"
  apply (rule impI)+
  apply (erule impE)
   apply assumption
  apply (erule impE)
   apply assumption
  apply assumption

lemma "\<not> \<not> A \<longrightarrow> A"
  apply (rule impI)
  apply (rule classical)
  apply (erule notE)
  apply assumption

lemma "A \<longrightarrow> \<not> \<not> A"
  apply (rule impI)
  apply (rule notI)
  apply (erule notE)
  apply assumption


lemma "(\<not> A \<longrightarrow> B) \<longrightarrow> (\<not> B \<longrightarrow> A)"
  apply (rule impI)+
  apply (rule classical)
  apply (erule notE)
  apply (erule impE)
   apply assumption
  apply assumption

lemma "((A \<longrightarrow> B) \<longrightarrow> A) \<longrightarrow> A"  
  apply (rule impI)
  apply (rule classical)
  apply (erule impE)
  apply (rule impI)
  apply (erule notE)
   apply (assumption)
  apply (erule notE)
  apply assumption

lemma "A \<or> \<not> A"
  apply (rule classical)
  apply (rule disjI2)
  apply (rule notI)
  apply (erule notE)
  apply (rule disjI1)      
  apply assumption        

                                             
lemma "(\<not> (A \<and> B)) = (\<not> A \<or> \<not> B)"
  apply (rule iffI)
   apply (rule classical)
   apply (erule notE)
   apply (rule conjI)
    apply (rule classical)
    apply (erule notE)
    apply (rule disjI1)
    apply assumption
   apply (rule classical)
   apply (erule notE)
   apply (rule disjI2)
   apply assumption
  apply (rule classical)
  apply (erule notE)
  apply (erule disjE)
   apply (rule notI)
  apply (erule notE)
   apply (erule conjE)
   apply assumption
  apply (rule notI)
  apply (erule conjE)
  apply (erule notE)
  apply assumption

end 


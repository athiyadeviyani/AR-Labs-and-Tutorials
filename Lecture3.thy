theory Lecture3
imports Main
begin

section{* Natural Deduction Rules for Propositional Logic *}

text{* You can lookup the statement of a theorem/lemma using the "thm" command. You would not leave 
       these as part of your theory file usually. *}

(* Conjunction *)

thm conjunct1
thm conjunct2 
thm conjI

(* Disjunction *)


(* Implication *)

thm impI
thm mp
thm impE

(* If and only if *)

thm iffI
thm iffD1
thm iffD2

(* Not *)
thm FalseE
thm notI
thm notE

(* Classical *)

thm excluded_middle
thm ccontr

theorem K: "A \<longrightarrow> B \<longrightarrow> A"
oops  


lemma "\<lbrakk>A; B \<rbrakk> \<Longrightarrow> A"
apply assumption
done


lemma "\<lbrakk> A; B; C \<rbrakk> \<Longrightarrow> (A \<and> B) \<or> D"
apply (rule disjI1)
apply (rule conjI)
apply assumption+
done 


(* This is not such a nice Isabelle proof: it's mostly for illustrating some of the basic ND rules in action *)
lemma "((Sunny \<or> Rainy) \<and> \<not> Sunny) \<longrightarrow> Rainy" 
apply (rule impI)
apply (frule conjunct1)
apply (erule disjE)
apply (drule conjunct2)
apply (erule notE)
apply assumption
apply assumption 
done

(* A "nicer" one using ConjE *)
lemma "((Sunny \<or> Rainy) \<and> \<not> Sunny) \<longrightarrow> Rainy" 
apply (rule impI)
apply (erule conjE)
apply (erule disjE)
apply (erule notE)
apply assumption
apply assumption
done


(* A structured proof -- note the naming of the assumption. More on this style of proof later in the course *)
lemma "((Sunny \<or> Rainy) \<and> \<not> Sunny) \<longrightarrow> Rainy" 
proof (rule impI)
  assume SRS: "(Sunny \<or> Rainy) \<and> \<not> Sunny"
  from SRS have "Sunny \<or> Rainy" by (rule conjunct1)
  then show "Rainy"
  proof 
    assume S: "Sunny" 
    from SRS have "\<not> Sunny" by (rule conjunct2)
    then show "Rainy" using S by (rule notE)
  next 
    assume "Rainy"
    then show "Rainy" .
  qed
qed

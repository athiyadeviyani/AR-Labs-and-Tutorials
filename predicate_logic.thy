(*
    ex.thy,v 1.1 2016/09/29 17:37:37 jdf Exp
    Original Author: Tjark Weber
    Updated to Isabelle 2016 by Jacques Fleuriot
*)

section {* Predicate Logic *}

 theory predicate_logic imports Main begin 

text {*
We are again talking about proofs in the calculus of Natural Deduction.  In
addition to the rules given in the exercise "Propositional Logic", you may
now also use

exI: ?P ?x ⟹ ∃x. ?P x
exE:⟦∃x. ?P x; ⋀x. ?P x ⟹ ?Q⟧ ⟹ ?Q
allI: (⋀x. ?P x) ⟹ ∀x. ?P x
allE: ⟦∀x. ?P x; ?P ?x ⟹ ?R⟧ ⟹ ?R

Give a proof of the f collowing propositions or an argument why the formula is
not valid:
*}
 
  
lemma "(∃x. ∀y. P x y) ⟶ (∀y. ∃x. P x y)"
  apply (rule impI)
  apply (erule exE)
  apply (rule allI)
  apply (erule allE)
  apply (rule exI)
  apply assumption
  done

lemma "(∀x. P x ⟶ Q) = ((∃x. P x) ⟶ Q)"
  apply (rule iffI)
  apply (rule impI)
   apply (erule exE)
   apply (erule allE)
   apply (erule impE)
    apply assumption
   apply assumption
  apply (rule allI)
  apply (rule impI)
  apply (erule impE)
   apply (rule exI)
   apply assumption
  apply assumption
  done 

lemma "((∀ x. P x) ∧ (∀ x. Q x)) = (∀ x. (P x ∧ Q x))"
  apply (rule iffI)
   apply (erule conjE)
   apply (rule allI)
   apply (erule allE)
   apply (erule allE)
   apply (rule conjI)
    apply assumption
   apply assumption
  apply (rule conjI)
   apply (rule allI, erule allE, erule conjE, assumption)+


lemma "((∀ x. P x) ∨ (∀ x. Q x)) = (∀ x. (P x ∨ Q x))"
  oops 
  text {*
    Auto Quickcheck found a counterexample:
      P = {a⇩1}
      Q = {a⇩2}
    Evaluated terms:
      ∀x xa. P x ∨ Q xa = False
      ∀x. P x ∨ Q x = True 
  *}



lemma "((∃ x. P x) ∨ (∃ x. Q x)) = (∃ x. (P x ∨ Q x))"
  apply (rule iffI)
   apply (erule disjE)
    apply (erule exE)
    apply (rule exI)
    apply (rule disjI1)
    apply assumption
   apply (erule exE)
   apply (rule exI)
   apply (rule disjI2)
   apply assumption
  apply (erule exE)
  apply (erule disjE)
   apply (rule disjI1)
   apply (rule exI)
   apply assumption
  apply (rule disjI2)
  apply (rule exI)
  apply assumption

lemma "(∀x. ∃y. P x y) ⟶ (∃y. ∀x. P x y)"
  oops
  text {* 
  Auto Quickcheck found a counterexample:
     P = (λx. undefined)(a⇩1 := {a⇩2}, a⇩2 := {a⇩1}) 
  *}


lemma "(¬ (∀ x. P x)) = (∃ x. ¬ P x)"
  apply (rule iffI)
   apply (rule classical)
   apply (erule notE)
   apply (rule allI)
   apply (rule classical)
   apply (erule notE)
   apply (rule exI)
   apply assumption
  apply (erule exE)
  apply (rule notI)
  apply (erule allE)
  apply (erule notE)
  apply assumption

end 

theory tutorial_1
imports Main
begin

lemma 1: "(P ⟶ (Q ⟶ R)) ⟶ ((P ⟶ Q) ⟶ (P ⟶ R))"
  apply (rule impI)+
  apply (erule impE)
   apply assumption
  apply (erule mp)
  apply (erule impE)
   apply assumption
  apply assumption
  done

lemma 2: "¬¬P ⟶ P"
  apply (rule impI)+
  apply (rule classical)
  apply (erule notE)
  apply assumption
  done

lemma 3: "(P ⟶ Q ∧ R) ⟶ ((P ⟶ Q) ∧ (P ⟶ R))"
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
  done

lemma 4: "(¬P ⟶ Q) ⟶ (¬Q ⟶ P)"
  apply (rule impI)+
  apply (rule classical)
  apply (erule notE)
  apply (erule impE)
   apply assumption
  apply assumption
  done

lemma excluded_middle: "P ∨ ¬P"
  apply (rule classical)
  apply (rule disjI1)
  apply (rule classical)
  apply (erule notE)
  apply (rule disjI2  apply (erule notE)
  apply (erule impE)
   apply assumption
  apply assumption
  done

lemma excluded_middle: "P ∨ ¬P"
  apply (rule classical)
  apply (rule disjI1)
  apply (rule classical)
  apply (erule notE)
  apply (rule disjI2)
  apply assumption
  done


lemma 6: "(R ⟶ P) ⟶ (((¬R ∨ P) ⟶ (Q ⟶ S)) ⟶ (Q ⟶ S))"
  apply (rule impI)
  apply (rule impI)
  apply (rule impI)
  apply (rule ccontr)
  apply (erule impE)
  apply (rule ccontr)
  apply (erule impE)
  apply (rule disjI1)
  apply assumption
  apply (erule impE)
  apply assumption
  apply (rule notE)
  apply assumption
  apply assumption
  apply (erule impE)
  apply (rule disjI2)
  apply assumption
  apply (erule impE)
  apply assumption
  apply (erule notE)
  apply assumption
  done


lemma 6: "(R ⟶ P) ⟶ (((¬R ∨ P) ⟶ (Q ⟶ S)) ⟶ (Q ⟶ S))"
  apply (rule impI)
  apply (rule impI)
  apply (rule impI)
  apply (rule ccontr)
  apply (erule impE)
  apply (rule ccontr)
  apply (erule impE)
  apply (rule disjI1)
  apply assumption
  apply (erule impE)
  apply assumption
  apply (rule notE)
  apply assumption
  apply assumption
  apply (erule impE)
  apply (rule disjI2)
  apply assumption
  apply (erule impE)
  apply assumption
  apply (erule notE)
  apply assumption
  done

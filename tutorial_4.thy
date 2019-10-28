theory tut4 imports Main
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
  assume "(∀x. P x ⟶ Q)" then have "P a ⟶ Q"
    by (simp add: ‹∀x. P x ⟶ Q›)
  then show "(∃x. P x ⟶ Q)"
    by simp
qed

lemma three_try: "¬(∃x. P x) ⟹ (∀x.¬P x)"
  apply (rule allI)
  apply (rule notI)
  apply (erule notE)
  apply (rule exI)
  apply assumption
  done

lemma 3: "¬(∃x. P x) ⟹ (∀x.¬P x)"
proof (rule allI, rule notI)
  fix x
  assume forContra: "P x"
  have 0: "∃x. P x"
    using forContra by (rule exI)
  assume notExist: "∄x. P x"
  then show "False"
    using forContra by auto
qed

lemma 31: "¬(∃x. P x) ⟹ (∀x.¬P x)"
proof (safe)
  fix x
  assume "P x" then have "(∃x. P x)" ..
  assume ex: "¬(∃x. P x)"
  then show False using ex
    using ‹P x› by auto
qed

(* safe is a method that will not make any provable goal become unprovable.
It does not do any exI or spec/allE steps. You can use other methods instead. *)

lemma assumes n_all: "¬(∀x. P x)" shows "∃x. ¬P x"
proof (rule ccontr)
  assume n_ex: "∄x. ¬ P x"
  { fix x
    have "P x"
    proof (rule ccontr)
      assume "¬P x" then have "∃x. ¬P x" ..
      then show False using n_ex by simp
    qed
  }
  then have "∀x. P x" .. 
  then show False using n_all by simp
qed

lemma 5: "(R⟶P)⟶(((¬R ∨ P)⟶(Q⟶S))⟶(Q⟶S))"
proof (rule impI)+ 
  assume "R ⟶ P" and "¬R ∨ P ⟶ Q ⟶ S" and "Q" 
  show "S"
  (* show the possible cases: 
      1. R  
      2. ¬R 
  *)
  proof (cases)
    assume "R"
    then have "P"
      using ‹R ⟶ P› by blast
    then have "¬R ∨ P"
      by simp
    then have "Q ⟶ S"
      using ‹¬ R ∨ P ⟶ Q ⟶ S› by blast
    then show "S"
      using ‹Q› by simp
  next
    assume "¬R"
    then have "¬R ∨ P"
      by simp
    then have "Q ⟶ S"
      using ‹¬ R ∨ P ⟶ Q ⟶ S› by blast
    then show "S"
      using ‹Q› by simp
  qed
qed

end

theory tia_learns_lsar
  imports Main

begin

(* ------------------- PROPOSITIONAL LOGIC in sematicscholar.org ------------------- *)
lemma "A ⟶ A"
proof (rule impI)
  assume a: "A"
  show "A" by (rule a)
qed

lemma "A ⟶ A ∧ A"
proof 
  assume "A"
  show "A ∧ A"
    by (simp add: ‹A›)
qed

lemma "A ∧ B ⟶ B ∧ A"
proof 
  assume AB: "A ∧ B"
  show "B ∧ A"
  proof (rule conjE[OF AB]) (* conjE[OF AB]: ([A; B] ⟹ ?R) ⟹ ?R *)
    assume "A" and "B"
    show ?thesis (* ?thesis stands for current goal, i.e. the enclosing show (or have) statement *)
      by (simp add: AB) 
  qed
qed

lemma "A ∧ B ⟶ B ∧ A"
proof 
  assume AB: "A ∧ B"
  from AB show "B ∧ A"
  proof
    assume "A" and "B"
    show ?thesis
      by (simp add: AB)
  qed
qed

(* forward reasoning *) 
lemma "A ∧ B ⟶ B ∧ A"
proof
  assume ab: "A ∧ B" 
  from ab have a: "A" ..
  from ab have b: "B" ..
  from b a show "B ∧ A" ..
qed



(* ------------------- PREDICATE LOGIC in sematicscholar.org ------------------- *)

(* 
The command fix introduces new local variables into a proof. 
The pair fix-show corresponds to ⋀ (the universal quantifier at the meta-level)
  just like assume-show corresponds to ⟹.
*) 

lemma assumes P: "∀x. P x" shows "∀x. P(f x)"
proof  (* allI: (⋀x. ?P x) ⟹ ∀x. ?P x *)
  fix a 
  from P show "P(f a)"  (* allE: ⟦∀x. ?P x; ?P ?x ⟹ ?R⟧ ⟹ ?R *)
    by simp
qed

lemma assumes Pf: "∃x. P(f x)" shows "∃y. P y"
proof -
  from Pf show ?thesis 
  proof  (* exE: [∃x. ?P x; ⋀x. ?P x ⟹ ?Q] ⟹ ?Q *)
    fix x
    assume "P(f x)"
    show ?thesis
      using ‹P (f x)› by auto  (* exI: ?P ?x ⟹ ∃x. ?P x *)
  qed
qed

lemma assumes Pf: "∃x. P(f x)" shows "∃y. P y"
proof -
  from Pf obtain x where "P(f x)" .. 
      (* obtain provides a more appealing form of generalised existence reasoning *)
  thus "∃y. P y" .. 
qed

lemma assumes ex: "∃x. ∀y. P x y" shows "∀y. ∃x. P x y" 
proof 
  fix y 
  from ex obtain x where "∀y. P x y" ..
  hence "P x y" .. 
  thus "∃x. P x y" .. 
qed



(* ------------------- CANTOR'S THEOREM in sematicscholar.org ------------------- *)

(* CANTOR'S THEOREM: there is no surjective function from a set to its powerset. *) 
theorem Cantor: "∃S. S ∉ range (f :: 'a ⇒ 'a set)"
proof 
  let ?S = "{x. x ∉ f x}"  (* let introduces an abbreviation of a term *)
  show "?S ∉ range f"
  proof
    assume "?S ∈ range f"
    then obtain y where "?S = f y" .. 
    show False
    proof cases
      assume "y ∈ S"
      with `?S = f y` show False by blast
    next
      assume "y ∉ S"
      with `?S = f y` show False by blast
    qed
  qed
qed

(* detailed version without blasting *)
theorem Cantor_Long: "∃S. S ∉ range (f :: 'a ⇒ 'a set)"
proof 
  let ?S = "{x. x ∉ f x}"  (* let introduces an abbreviation of a term *)
  show "?S ∉ range f"
  proof
    assume "?S ∈ range f"
    then obtain y where "?S = f y" .. 
    show False
    proof cases
      assume "y ∈ ?S"
      hence "y ∉ f y" by simp
      hence "y ∉ ?S"
        by (simp add: `?S = f y`)
      thus False
        using ‹y ∈ {x. x ∉ f x}› by auto
    next 
      assume "y ∉ ?S"
      hence "y ∈ f y" by simp
      hence "y ∈ ?S" 
        by (simp add: `?S = f y`)
      thus False
        using ‹y ∉ {x. x ∉ f x}› by auto 
    qed
  qed
qed






end

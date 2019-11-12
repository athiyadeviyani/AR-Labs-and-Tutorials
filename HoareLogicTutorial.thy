theory HoareLogicTutorial
imports Main "~~/src/HOL/Hoare/Hoare_Logic"
begin

(* The minimum of two integers x and y: *)
lemma Min: "VARS (z :: int)
 {True}
 IF x \<le> y THEN z := x ELSE z := y FI
 { z = min x y }"
  apply vcg
  apply (simp add: min_def)
  done




(* Iteratively copy an integer variable x to y: *)
lemma Copy: "VARS (a :: int) y
 {0 \<le> x}
 a := x; y := 0;
 WHILE a \<noteq> 0
 INV { x=y+a } 
 DO y := y + 1 ; a := a - 1 OD
 {x = y}"
apply vcg_simp
done

(* Multiplication *) 
lemma Multipl: "VARS (z :: int) i
{0 \<le> y}
i := y;
z := 0;
WHILE i \<noteq> 0 
INV { z = (y - i) * x }
DO
  z := z + x;
  i := i - 1
OD
{z = x * y}"
  apply vcg
  apply (auto simp add: algebra_simps)
  done


(* Iterative multiplication through addition: *)
lemma Multi: "VARS (a :: int) z
 {0 \<le> y}
 a := 0; z := 0;
 WHILE a \<noteq> y
 INV {z = x * a}
 DO 
   z := z + x ; 
   a := a + 1 
 OD
 {z = x * y}"
(* "Replace Inv with your invariant." *)
  apply vcg_simp
  apply (erule conjE)
  apply (simp add: distrib_left) 
  done



(* A factorial algorithm: *)
lemma DownFact: "VARS (z :: nat) (y::nat)
 {True}
 z := x; y := 1;
 WHILE z > 0
 INV { Inv }
 DO 
   y := y * z; 
   z := z - 1 
 OD
 {y = fact x}"
(* "Replace Inv with your invariant." *)
oops


(* Integer division of x by y: *)
lemma Div: "VARS (r :: int) d 
 {y \<noteq> 0}
 r := x; d := 0;
 WHILE y \<le> r
 INV { Inv }
 DO 
  r := r - y;
  d := d + 1
 OD
 { Postcondition }"
(* "Replace Inv with your invariant." *)
(* "Replace Postcondition with your postcondition." *)
oops


end
theory HoareLogicLecture
imports Main "HOL-Hoare.Hoare_Logic"
begin

lemma "VARS (z :: nat) (y::nat)
 {True}
 y := 1; z := 0;
 WHILE z \<noteq> x
 INV { y = fact z }
 DO 
   z := z + 1;
   y := y * z 
 OD
 {y = fact x}"
by vcg_simp


lemma "VARS (z :: int) i
 {True}
 i := y;
 z := 0;
 WHILE i \<noteq> 0
 INV { z = (y - i) * x }
 DO 
   z := z + x; 
   i := i - 1 
 OD
 {z = x * y}"
apply vcg_simp
by (simp add: algebra_simps)


lemma "VARS j R
  { True }
  j:= 0; R := [];
  WHILE j < length A
  INV { R = rev (take j A) }
  DO 
    R := (A!j) # R;
    j := j + 1
  OD
  { R = rev A }"
proof (vcg_simp)
  show "\<And>j R. R = rev (take j A) \<and> j < length A \<Longrightarrow> A ! j # rev (take j A) = rev (take (Suc j) A)"
  proof (induct A)
    case Nil thus ?case by simp
  next
    case (Cons a A') thus ?case by (cases "j", auto)    
  qed
qed

lemma "VARS j R
  { True }
  j:= 0; R := [];
  WHILE j < length A
  INV { R = rev (take j A) }
  DO 
    R := (A!j) # R;
    j := j + 1
  OD
  { R = rev A }"
proof (vcg_simp, simp add: take_Suc_conv_app_nth)
qed


end



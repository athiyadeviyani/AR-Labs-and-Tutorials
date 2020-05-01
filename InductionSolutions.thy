theory InductionSolutions
imports Main
begin

datatype 'a TREE = LEAF 'a | NODE 'a "'a TREE" "'a TREE"

thm TREE.induct
  
(* Appropriate induction rule: 
   \<lbrakk>\<And>x. ?P (LEAF x); \<And>x1a x2 x3. \<lbrakk>?P x2; ?P x3\<rbrakk> \<Longrightarrow> ?P (NODE x1a x2 x3)\<rbrakk> \<Longrightarrow> ?P ?TREE *)
  
  
primrec MIRROR :: "'a TREE \<Rightarrow> 'a TREE" where
  "MIRROR (LEAF x) = LEAF x" 
| "MIRROR (NODE x l r) = NODE x (MIRROR r) (MIRROR l)"

lemma mirror_mirror: "MIRROR(MIRROR t) = t"
proof(induct t)
 case (LEAF x) then show ?case by simp
next
 case(NODE x l r) then show ?case by simp
qed

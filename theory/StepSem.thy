theory StepSem
  imports Main
begin

inductive star::"('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" for r where
refl:"star r x x"|
step: "r x y \<Longrightarrow> star r y z \<Longrightarrow> star r x z"


lemma star_left:
  "r s1 s2 \<Longrightarrow> star r s2 s3 \<Longrightarrow> star r s1 s3"
  apply (rule star.step; simp)
  done

(*
lemma star_right:
  "star r s1 s2 \<Longrightarrow> r s2 s3 \<Longrightarrow> star r s1 s3"
  apply (rule star.step [of _ _ s2])
  done *)

end
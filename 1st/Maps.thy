theory Maps
  imports HOL.String
begin

section {* Identifiers *}

definition beq_string :: "string \<Rightarrow> string \<Rightarrow> bool" where
  "beq_string x y = (if x = y then True else False)"

theorem beq_string_refl: "\<forall> s. True = beq_string s s"
  unfolding beq_string_def
  apply (simp)
  done

end

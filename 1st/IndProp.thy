theory IndProp
  imports Logic
begin

section {* IndProp *}

subsection {* Inductively defined propositions *}

inductive ev :: "nat \<Rightarrow> HOL.bool" where
  ev_0: "ev 0"
| ev_SS: " ev n \<Longrightarrow> ev (Suc (Suc n))"

theorem ev_4: "ev (Suc (Suc (Suc (Suc 0))))"
  apply (rule ev_SS)
  apply (rule ev_SS)
  apply (rule ev_0)
  done

end
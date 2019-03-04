theory IndProp
  imports Logic
begin

section {* IndProp *}

subsection {* Inductively defined propositions *}

inductive ev :: "nat \<Rightarrow> HOL.bool" where
  ev_0: "ev 0"
| ev_SS: "ev n \<Longrightarrow> ev (Suc (Suc n))"

theorem ev_4: "ev (Suc (Suc (Suc (Suc 0))))"
  apply (rule ev_SS)
  apply (rule ev_SS)
  apply (rule ev_0)
  done

subsection {* Using Evidence in Proofs *}

subsubsection {* Inversion on Evidence *}

(*
inductive_set even :: "nat set" where
  zero[intro!]: "0 \<in> even"
| step[intro!]: "n \<in> even \<Longrightarrow> Suc (Suc n) \<in> even"

inductive_cases Suc_Suc_cases [elim!]: "Suc (Suc n) \<in> even"
*)

(* theorem ev_minus2: "\<forall> n. n \<in> even \<longrightarrow> (pred (pred n)) \<in> even" *)

end
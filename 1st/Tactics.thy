theory Tactics
  imports Poly
begin

section {* Tactics *}

(* theorem silly1: "\<forall> n m p q::nat. n = m \<longrightarrow> [n, p] = [n, q] \<longrightarrow> [n, p] = [m, q]" *)
theorem silly1: "n = m \<longrightarrow> [n, p] = [n, q] \<longrightarrow> [n, p] = [m, q]"
  apply (simp)
  done

subsection {* The apply ... with ... Tactic *}

lemma trans_eq_example: "[a, b] = [c, d] \<longrightarrow> [c, d] = [e, f] \<longrightarrow> [a, b] = [e, f]"
  apply (simp)
  done

lemma trans_eq: "n = m \<longrightarrow> m = p \<longrightarrow> n = p"
  apply (simp)
  done

subsection {* The inversion tactic *}

theorem S_inversion: "\<forall> n m::nat. Suc n = Suc m \<longrightarrow> n = m"
  apply (simp)
  done

subsection {* Using tactic on Hypotheses *}

(* theorem S_inj: "\<forall> n m::nat. beq_nat (Suc n) (Suc m) = b \<longrightarrow> beq_nat n m = b" *)

subsection {* Varying the induction Hypotheses *}

subsection {* Unfolding Definition *}

definition square ::"nat \<Rightarrow> nat" where
  "square n = n * n"

lemma square_multi: "square (n * m) = (square n) * (square m)"
  unfolding Tactics.square_def
  apply (simp)
  done

definition foo ::"nat \<Rightarrow> nat" where "foo _ = 5"

theorem silly_fact_1: "foo m + 1 = foo (m + 1) + 1"
  unfolding Tactics.foo_def
  apply (simp)
  done

fun bar ::"nat \<Rightarrow> nat" where
  "bar 0 = 5"
| "bar (Suc n) = 5"

theorem silly_fact_2: "bar m + 1 = bar (m + 1) + 1"
  apply (induction m)
   apply (simp_all)
  done

subsection {* Using destruct on Compound Expressions *}

end

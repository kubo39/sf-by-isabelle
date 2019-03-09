theory Tactics
  imports Poly
begin

section {* Tactics *}

(* theorem silly1: "\<forall> n m p q::nat. n = m \<longrightarrow> [n, p] = [n, q] \<longrightarrow> [n, p] = [m, q]" *)
theorem silly1: "n = m \<longrightarrow> [n, p] = [n, q] \<longrightarrow> [n, p] = [m, q]"
  apply (simp)
  done

theorem silly_ex: "evenb n = True \<longrightarrow> oddb (Suc n) = True \<longrightarrow> evenb (Suc (Suc 1)) = True \<longrightarrow> oddb 4 = True"
  apply (simp)
  done

theorem rev_exercise1: "xs = rev ys \<longrightarrow> ys = rev xs"
  apply (simp add: rev_involutive)
  done

subsection {* The apply ... with ... Tactic *}

lemma trans_eq_example: "[a, b] = [c, d] \<longrightarrow> [c, d] = [e, f] \<longrightarrow> [a, b] = [e, f]"
  apply (simp)
  done

lemma trans_eq: "n = m \<longrightarrow> m = p \<longrightarrow> n = p"
  apply (simp)
  done

lemma trans_eq_exercise: "m = minustwo p \<longrightarrow> n + q = m \<longrightarrow> n + q = minustwo p"
  apply (simp)
  done

subsection {* The inversion tactic *}

theorem S_inversion: "\<forall> n m::nat. Suc n = Suc m \<longrightarrow> n = m"
  apply (simp)
  done

theorem inversion_ex1: "\<forall> n m p::nat. (n # m # []) = (p # p # []) \<longrightarrow> (n # []) = (m # [])"
  apply (simp)
  done

theorem inversion_ex2: "\<forall> n m::nat. (n # []) = (m # []) \<longrightarrow> n = m"
  apply (simp)
  done

theorem inversion_ex3: "x # y # l = z # j \<longrightarrow> y # l = x # j \<longrightarrow> x = y"
  apply (auto)
  done

theorem inversion_ex6: "x # y # l = [] \<longrightarrow> y # l = z # j \<longrightarrow> x = z"
  apply (simp)
  done

theorem f_equal: "x = y \<longrightarrow> f x = f y"
  apply (simp)
  done

subsection {* Using tactic on Hypotheses *}

theorem S_inj: "\<forall> n m::nat. beq_nat (Suc n) (Suc m) = b \<longrightarrow> beq_nat n m = b"
  apply (simp)
  done

theorem plus_n_n_injective: "\<forall> n m::nat. n + n = m + m \<longrightarrow> n = m"
  apply (simp)
  done

subsection {* Varying the induction Hypotheses *}

(*
theorem beq_nat_true: "beq_nat n m = True \<longrightarrow> n = m"
  apply (induction n)
   apply (induction m)
    apply (simp)
   apply (simp)
  apply (induction m)
   apply (simp)
*)

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

definition sillyfun :: "nat \<Rightarrow> bool" where
  "sillyfun n = (if n = 3 then False else (if n = 5 then False else False))"

theorem sillyfun_false: "sillyfun n = False"
  unfolding sillyfun_def
  apply (simp)
  done

(*
theorem combine_split: "split xs = (ys, zs) \<longrightarrow> combine ys zs = xs"
  apply (induction xs)
   apply (simp)
  apply (induction ys)
   apply (simp)
*)

end

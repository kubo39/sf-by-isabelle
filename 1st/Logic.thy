theory Logic
  imports Tactics
begin

section {* Logic *}

(* definition plus_fact where "2 + 2 = 4" *)

subsection {* Logical Connectives *}

value "(mult 2 2)"

subsubsection {* Conjunction *}

lemma and_example: "3 + 4 = 7 \<and> (2::nat) * 2 = 4"
  apply (simp)
  done

lemma and_intro: "A \<longrightarrow> B \<longrightarrow> A \<and> B"
  apply (simp)
  done

lemma and_exercise: "\<forall> n m::nat. n + m = 0 \<longrightarrow> n = 0 \<and> m = 0"
  apply (simp)
  done

lemma and_example2: "\<forall> n m::nat. n = 0 \<and> m = 0 \<longrightarrow> n + m = 0"
  apply (simp)
  done

lemma and_example3: "\<forall> n m::nat. n + m = 0 \<longrightarrow> n * m = 0"
  apply (simp)
  done

lemma proj1: "P \<and> Q \<longrightarrow> P"
  apply (simp)
  done

lemma proj2: "P \<and> Q \<longrightarrow> Q"
  apply (simp)
  done

theorem and_commut: "P \<and> Q \<longrightarrow> Q \<and> P"
  apply (simp)
  done

subsubsection {* Disjunction *}

lemma or_example: "\<forall> n m :: nat. n = 0 \<or> m = 0 \<longrightarrow> n * m = 0"
  apply (simp)
  done

lemma or_intro: "A \<longrightarrow> A \<or> B"
  apply (simp)
  done

lemma zero_or_succ: "n = 0 \<or> n = Suc (pred n)"
  apply (induction n)
   apply (simp_all)
  done

lemma mult_eq_0: "\<forall> n m::nat. n * m = 0 \<longrightarrow> n = 0 \<or> m = 0"
  apply (simp)
  done

theorem or_commut: "P \<or> Q \<longrightarrow> Q \<or> P"
  apply (simp)
  done

subsubsection {* Falsehood and Negation *}

(* theorem ex_falso_quodlibet: "False \<rightarrow> P" *)

(* theorem zero_not_one: "\<not> (0 = 1)" *)

theorem not_False: "\<not> HOL.False"
  apply (simp)
  done

end

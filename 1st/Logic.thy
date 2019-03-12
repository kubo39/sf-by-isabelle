theory Logic
  imports Tactics
begin

section {* Logic *}

(* definition plus_fact where "2 + 2 = 4" *)

subsection {* Logical Connectives *}

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

theorem and_assoc: "P \<and> (Q \<and> R) \<longrightarrow> (P \<and> Q) \<and> R"
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

theorem ex_falso_quodlibet: "HOL.False \<longrightarrow> P"
  apply (simp)
  done

theorem not_implies_our_not: "\<forall> P. \<not>P \<longrightarrow> (\<forall> Q. P \<longrightarrow> Q)"
  apply (simp)
  done

(* theorem zero_not_one: "\<not> (0 = 1)" *)

(* theorem zero_not_one': "0 \<noteq> 1" *)

theorem not_False: "\<not> HOL.False"
  apply (simp)
  done

theorem contradiction_implies_anything: "(P \<and> \<not>P) \<longrightarrow> Q"
  apply (simp)
  done

theorem double_neg: "P \<longrightarrow> \<not>\<not>P"
  apply (simp)
  done

theorem contrapositive: "(P \<longrightarrow> Q) \<longrightarrow> (\<not>Q \<longrightarrow> \<not>P)"
  apply (auto)
  done

theorem not_both_true_and_false: "\<not>(P \<and> \<not>P)"
  apply (simp)
  done

theorem not_true_is_false: "b \<noteq> True \<longrightarrow> b = False"
  apply (case_tac b)
   apply (simp_all)
  done

subsubsection {* Truth *}

(* True is true. *)
theorem True_is_true: "HOL.True"
  apply (simp)
  done

subsubsection {* Logical Equivalance *}

definition iff :: "HOL.bool \<Rightarrow> HOL.bool \<Rightarrow> HOL.bool" where
   "iff P Q \<equiv> (P \<longrightarrow> Q) \<and> (Q \<longrightarrow> P)"

theorem iff_sym: "\<forall> P Q. iff P Q \<longrightarrow> iff Q P"
  unfolding iff_def
  apply (simp)
  done

lemma not_true_iff_false: "b \<noteq> bool.True \<longleftrightarrow> b = bool.False"
  apply (case_tac b)
   apply (simp_all)
  done

theorem iff_refl: "\<forall> P. P \<longleftrightarrow> P"
  apply (simp)
  done

theorem iff_trans: "\<forall> P Q R. (P \<longleftrightarrow> Q) \<longrightarrow> (Q \<longleftrightarrow> R) \<longrightarrow> (P \<longleftrightarrow> R)"
  apply (simp)
  done

theorem or_distributes_over_and: "\<forall> P Q R. P \<or> (Q \<and> R) \<longleftrightarrow> (P \<or> Q) \<and> (P \<or> R)"
  using [[simp_trace]]
  apply (auto)
  done

lemma mult_0: "\<forall> n m::nat. n * m = 0 \<longleftrightarrow> n = 0 \<or> m = 0"
  apply (simp)
  done

lemma or_assoc: "\<forall> P Q R. P \<or> (Q \<or> R) \<longleftrightarrow> (P \<or> Q) \<or> R"
  apply (simp)
  done

subsubsection {* Existential Quantification*}

lemma four_is_even: "\<exists> n::nat. 4 = n + n"
  sorry

subsubsection {* Programming with Propisition *}

fun In :: "'a \<Rightarrow> 'a list \<Rightarrow> HOL.bool" where
  "In _ [] = HOL.False"
| "In a (x # xs) = (x = a \<or> In a xs)"

lemma In_example_1: "In 4 (1 # 2 # 3 # 4 # 5 # [])"
  apply (simp)
  done

lemma In_example_2: "\<forall> n. In n (2 # 4 # []) \<longrightarrow> (\<exists> n'. n = 2 * n')"
  sorry

lemma In_map: "In a xs \<longrightarrow> In (f a) (map f xs)"
  apply (induction xs)
   apply (simp_all)
  done

lemma In_map_iff: "In y (map f xs) \<longleftrightarrow> exists x f x = y \<and> In a xs"
  apply (induction xs)
   apply (simp)
  sorry

lemma In_app_iff: "In a (xs @ ys) \<longrightarrow> In a xs \<or> In a ys"
  apply (induction xs)
   apply (simp_all)
  done

end

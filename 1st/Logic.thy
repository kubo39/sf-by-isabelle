theory Logic
  imports Tactics
begin

section {* Logic *}

(* definition plus_fact where "2 + 2 = 4" *)

subsection {* Logical Connectives *}

value "(mult 2 2)"

lemma and_example: "3 + 4 = 7 \<and> (2::nat) * 2 = 4"
  apply (simp)
  done

lemma and_intro: "A \<longrightarrow> B \<longrightarrow> A \<and> B"
  apply (simp)
  done

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

end

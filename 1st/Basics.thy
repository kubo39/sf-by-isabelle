theory Basics
  imports Main
begin

section {* Basics *}

datatype day = monday | tuesday | wednesday |
  thursday | friday | saturday | sunday

fun next_weekday :: "day \<Rightarrow> day" where
  "next_weekday monday = tuesday"
| "next_weekday tuesday = wednesday"
| "next_weekday wednesday = thursday"
| "next_weekday thursday = friday"
| "next_weekday friday = monday"
| "next_weekday saturday = monday"
| "next_weekday sunday = monday"

value "next_weekday friday" (* "monday" :: "day" *)
value "next_weekday (next_weekday saturday)" (* "tuesday" :: "day" *)

lemma test_next_weekday: "next_weekday (next_weekday saturday) = tuesday" by simp

datatype bool = True | False

fun negb :: "bool \<Rightarrow> bool" where
  "negb True = False"
| "negb False = True"

fun andb :: "bool \<Rightarrow> bool \<Rightarrow> bool" (infixr "&&" 65)
  where
  "andb True b2 = b2"
| "andb False _ = False"

fun orb :: "bool \<Rightarrow> bool \<Rightarrow> bool" (infixr "||" 65)
  where
  "orb True _ = True"
| "orb False b2 = b2"

lemma test_orb1: "orb True False = True" by simp
lemma test_orb2: "orb False False = False" by simp
lemma test_orb3: "orb False True = True" by simp
lemma test_orb4: "orb True True = True" by simp

lemma test_orb5: "False || False || True = True"
  apply (simp)
  done

fun pred :: "nat \<Rightarrow> nat" where
  "pred 0 = 0"
| "pred (Suc n') = n'"

value "Suc (Suc (Suc (Suc 0)))" (* "4" :: "nat" *)

fun minustwo :: "nat \<Rightarrow> nat" where
  "minustwo 0 = 0"
| "minustwo (Suc 0) = 0"
| "minustwo (Suc (Suc n')) = n'"

value "minustwo 4" (* "2" :: "nat" *)

fun evenb :: "nat \<Rightarrow> bool" where
  "evenb 0 = True"
| "evenb (Suc 0) = False"
| "evenb (Suc (Suc n')) = evenb n'"

fun oddb :: "nat \<Rightarrow> bool" where
  "oddb n = negb (evenb n)"

lemma test_oddb1: "oddb 1 = True" by simp
lemma test_oddb2: "oddb (Suc (Suc (Suc 1))) = False" by simp

fun plus :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "plus 0 m = m"
| "plus (Suc n') m = Suc (plus n' m)"

value "plus 3 2" (* "5" :: "nat" *)

fun mult :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "mult 0 _ = 0"
| "mult (Suc n') m = plus m (mult n' m)"

lemma test_plus1: "plus 1 1 = 2" by simp
lemma test_plus2: "plus (Suc (Suc 1)) 3 = 6" by simp
lemma test_mult1: "mult (Suc (Suc 1)) (Suc (Suc 1)) = 9" by simp

fun minus :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "minus 0 _ = 0"
| "minus n 0 = n"
| "minus (Suc n') (Suc m') = minus n' m'"

(*
fun exp :: "nat \<Rightarrow> nat" where
  "exp power 0 = Suc 0"
| "exp base (Suc p) = mult base (exp base p)"
*)

theorem plus_0_n: "\<forall> n::nat. 0 + n = n" by simp
theorem plus_1_l: "\<forall> n::nat. 1 + n = Suc n" by simp
theorem mult_0_l: "\<forall> n::nat. 0 * n = 0" by simp

theorem plus_id_example: "\<forall> n m::nat. n = m \<longrightarrow> n + n = m + m" by simp
theorem mult_0_plus: "\<forall> n m::nat. (0 + n) * m = n * m" by simp

end
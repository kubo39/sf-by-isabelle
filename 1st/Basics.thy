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

fun nandb :: "bool \<Rightarrow> bool \<Rightarrow> bool" where
  "nandb False _ = True"
| "nandb True b2 = negb b2"

lemma test_nandb1: "nandb True False = True" by simp
lemma test_nandb2: "nandb False False = True" by simp
lemma test_nandb3: "nandb False True = True" by simp
lemma test_nandb4: "nandb True True = False" by simp

fun andb3 :: "bool \<Rightarrow> bool \<Rightarrow> bool \<Rightarrow> bool" where
  "andb3 False _ _ = False"
| "andb3 True False _ = False"
| "andb3 True True b3 = b3"

lemma test_andb31: "andb3 True True True = True" by simp
lemma test_andb32: "andb3 False True True = False" by simp
lemma test_andb33: "andb3 True False True = False" by simp
lemma test_andb34: "andb3 True True False = False" by simp


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

fun factorial :: "nat \<Rightarrow> nat" where
  "factorial 0 = 1"
| "factorial (Suc n') = mult (Suc n') (factorial n')"

(* lemma test_factorial1: "factorial 3 = 6" *)
lemma test_factorial1: "factorial (Suc (Suc 1)) = 6" by simp

(* n = m *)
fun beq_nat :: "nat \<Rightarrow> nat \<Rightarrow> bool" where
  "beq_nat 0 0 = True"
| "beq_nat 0 (Suc m') = False"
| "beq_nat (Suc n') 0 = False"
| "beq_nat (Suc n') (Suc m') = beq_nat n' m'"

(* n \<le> m *)
fun leb :: "nat \<Rightarrow> nat \<Rightarrow> bool" where
  "leb 0 _ = True"
| "leb (Suc n') 0 = False"
| "leb (Suc n') (Suc m') = leb n' m'"

(* lemma test_leb1: "leb 2 2 = True" *)
lemma test_leb1: "leb (Suc 1) (Suc 1) = True" by simp

(* n < m \<longrightarrow> !(n \<ge> m) *)
definition blt_nat :: "nat \<Rightarrow> nat \<Rightarrow> bool" where
  "blt_nat n m = negb (leb m n)"

lemma test_blt_nat1: "blt_nat (Suc 1) (Suc 1) = False"
  unfolding blt_nat_def
  apply (simp)
  done

lemma test_blt_nat2: "blt_nat (Suc 1) (Suc (Suc (Suc 1))) = True"
  unfolding blt_nat_def
  apply (simp)
  done

lemma test_blt_nat3: "blt_nat (Suc (Suc (Suc 1))) (Suc 1) = False"
  unfolding blt_nat_def
  apply (simp)
  done

theorem plus_0_n: "\<forall> n::nat. 0 + n = n" by simp
theorem plus_1_l: "\<forall> n::nat. 1 + n = Suc n" by simp
theorem mult_0_l: "\<forall> n::nat. 0 * n = 0" by simp

theorem plus_id_example: "\<forall> n m::nat. n = m \<longrightarrow> n + n = m + m" by simp
theorem plus_id_exercise: "\<forall> n m p::nat. n = m \<longrightarrow> m = p \<longrightarrow> n + m = m + p"
  apply (simp)
  done

theorem mult_0_plus: "\<forall> n m::nat. (0 + n) * m = n * m" by simp
theorem mult_S_1: "\<forall> n m::nat. m = Suc n \<longrightarrow> m * (1 + n) = m * m"
  apply (simp)
  done

theorem plus_1_neq_0: "\<forall> n::nat. beq_nat (n + 1) 0 = False"
  apply (simp)
  done

(* theorem negb_involutive: "\<forall> b::bool. negb (negb b) = b" *)
theorem negb_involutive: "negb (negb b) = b"
  apply (induction b)
   apply (simp_all)
  done

theorem andb_commutative: "andb b c = andb c b"
  apply (induction b)
   apply (induction c)
    apply (simp_all)
  apply (induction c)
   apply (simp_all)
  done

theorem plus_1_neq_0': "\<forall> n::nat. beq_nat (n + 1) 0 = False"
  apply (simp)
  done

theorem andb_true_elim2: "\<forall> b c::bool. andb b c = True \<longrightarrow> c = True"
  using andb.elims
  apply (auto)
  done

theorem zero_nbeq_plus_1: "\<forall> n::nat. beq_nat 0 (n + 1) = False"
  apply (simp)
  done

end

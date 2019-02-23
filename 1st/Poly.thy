theory Poly
  imports Lists
begin 

section {* Poly *}

no_notation Nil ("[]") and Cons (infixr "#" 65) and app (infixr "@" 65)

datatype 'a list = Nil ("[]")
  | Cons 'a "'a list" (infixr "#" 65)

fun repeat :: "'a \<Rightarrow> nat \<Rightarrow> 'a list" where
  "repeat _ 0 = []"
| "repeat n (Suc count') = Cons n (repeat n count')"

value "repeat (4::nat) 2" (* Cons (4::nat) (Cons (4::nat) Nil)" *)
(* value "repeat (4::nat) 2 = Cons (4::nat) (Cons (4::nat) Nil)" *)
(* lemma test_repeat1: "repeat (4::nat) 2 = Cons (4::nat) (Cons (4::nat) Nil)" *)

fun app :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list" (infixr "@" 65)
  where
  "app [] ys = ys"
| "app (x # xs) ys = x # (app xs ys)"

fun rev :: "'a list \<Rightarrow> 'a list" where
  "rev [] = []"
| "rev (x # xs) = app (rev xs) (x # [])"

fun length :: "'a list \<Rightarrow> nat" where
  "length [] = 0"
| "length (x # xs) = Suc (length xs)"

lemma test_rev1: "rev (1 # 2 # []) = 2 #1 # []" by simp
lemma test_rev2: "rev (True # []) = True # []" by simp
lemma test_length1: "length (1 # 2 # 3 # []) = 3" by simp

fun fst :: "'X * 'Y \<Rightarrow> 'X" where "fst (x, y) = x"
lemma test_fst1: "fst (3, 4) = 3" by simp

fun snd :: "'X * 'Y \<Rightarrow> 'Y" where "snd (x, y) = y"
lemma test_snd1: "snd (3, 4) = 4" by simp

fun combine :: "'a list \<Rightarrow> 'b list \<Rightarrow> ('a * 'b) list" where
  "combine [] _ = []"
| "combine _ [] = []"
| "combine (x # xs) (y # ys) = (x, y) # (combine xs ys)"

value "combine ((1::nat) # (2::nat) # Nil) ((True::bool) # (False::bool) # Nil)"


fun do3times :: "('X \<Rightarrow> 'X) \<Rightarrow> 'X \<Rightarrow> 'X" where
  "do3times f n = f (f (f n))"

value "do3times minustwo 9" (* "3" :: "nat" *)
(* lemma test_do3times: "do3times minustwo 9 = 3" *)

end
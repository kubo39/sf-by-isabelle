theory Poly
  imports Lists
begin 

section {* Poly *}

datatype 'a list = Nil | Cons 'a "'a list"

fun repeat :: "'a \<Rightarrow> nat \<Rightarrow> 'a list" where
  "repeat _ 0 = Nil"
| "repeat n (Suc count') = Cons n (repeat n count')"

value "repeat (4::nat) 2" (* Cons (4::nat) (Cons (4::nat) Nil)" *)
(* value "repeat (4::nat) 2 = Cons (4::nat) (Cons (4::nat) Nil)" *)
(* lemma test_repeat1: "repeat (4::nat) 2 = Cons (4::nat) (Cons (4::nat) Nil)" *)

fun app :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "app Nil ys = ys"
| "app (Cons x xs) ys = Cons x (app xs ys)"

fun rev :: "'a list \<Rightarrow> 'a list" where
  "rev Nil = Nil"
| "rev (Cons x xs) = app (rev xs) (Cons x Nil)"

fun length :: "'a list \<Rightarrow> nat" where
  "length Nil = 0"
| "length (Cons x xs) = Suc (length xs)"

lemma test_rev1: "rev (Cons 1 (Cons 2 Nil)) = Cons 2 (Cons 1 Nil)" by simp
lemma test_rev2: "rev (Cons True Nil) = Cons True Nil" by simp
lemma test_length1: "length (Cons 1 (Cons 2 (Cons 3 Nil))) = 3" by simp

fun fst :: "'X * 'Y \<Rightarrow> 'X" where "fst (x, y) = x"
lemma test_fst1: "fst (3, 4) = 3" by simp

fun snd :: "'X * 'Y \<Rightarrow> 'Y" where "snd (x, y) = y"
lemma test_snd1: "snd (3, 4) = 4" by simp

fun combine :: "'a list \<Rightarrow> 'b list \<Rightarrow> ('a * 'b) list" where
  "combine Nil _ = Nil"
| "combine _ Nil = Nil"
| "combine (Cons x xs) (Cons y ys) = Cons (x, y) (combine xs ys)"

value "combine (Cons (1::nat) (Cons (2::nat) Nil)) (Cons (True::bool) (Cons (False::bool) Nil))"


fun do3times :: "('X \<Rightarrow> 'X) \<Rightarrow> 'X \<Rightarrow> 'X" where
  "do3times f n = f (f (f n))"

value "do3times minustwo 9" (* "3" :: "nat" *)
(* lemma test_do3times: "do3times minustwo 9 = 3" *)

end
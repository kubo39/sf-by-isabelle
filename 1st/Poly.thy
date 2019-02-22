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

fun fst :: "'X * 'Y \<Rightarrow> 'X" where "fst (x, y) = x"
lemma test_fst1: "fst (3::nat, 4::nat) = 3" by simp

fun snd :: "'X * 'Y \<Rightarrow> 'Y" where "snd (x, y) = y"
lemma test_snd1: "snd (3::nat, 4::nat) = 4" by simp

fun combine :: "'a list \<Rightarrow> 'b list \<Rightarrow> ('a * 'b) list" where
  "combine Nil _ = Nil"
| "combine _ Nil = Nil"
| "combine (Cons x xs) (Cons y ys) = Cons (x, y) (combine xs ys)"

value "combine (Cons (1::nat) (Cons (2::nat) Nil)) (Cons (True::bool) (Cons (False::bool) Nil))"

end
theory Lists
  imports Basics
begin

section {* Lists *}

datatype natprod = pair "nat * nat"

fun fst :: "natprod \<Rightarrow> nat" where
  "fst (pair (x, y)) = x"

value "fst (pair (3, 5))"

fun snd :: "natprod \<Rightarrow> nat" where
  "snd (pair (x, y)) = y"

fun fst' :: "nat * nat \<Rightarrow> nat" where
  "fst' (x, y) = x"

value "fst' (3, 5)"

fun snd' :: "nat * nat \<Rightarrow> nat" where
  "snd' (x, y) = y"

fun swap_pair :: "nat * nat \<Rightarrow> nat * nat" where
  "swap_pair (x, y) = (y, x)"

theorem subjective_pairing': "\<forall> n m::nat. (n, m) = (fst'(n, m), snd'(n, m))"
  apply simp
  done

(* theorem subjective_pairing: "\<forall> p::natprod. p = pair (fst p, snd p)" *)


no_notation Nil ("[]") and Cons (infixr "#" 65) and append (infixr "@" 65)

datatype natlist = Nil ("[]")
  | Cons nat "natlist" (infixr "#" 65)
hide_type list

fun repeat :: "nat \<Rightarrow> nat \<Rightarrow> natlist" where
  "repeat _ 0 = []"
| "repeat n (Suc count') = n # (repeat n count')"

fun length :: "natlist \<Rightarrow> nat" where
  "length [] = 0"
| "length (x # xs) = Suc (length xs)"

primrec app :: "natlist \<Rightarrow> natlist \<Rightarrow> natlist" (infixr "@" 65)
  where
  "[] @ ys = ys"
| "(x # xs) @ ys = x # (xs @ ys)"

lemma test_app1: "(1 # (2 # (3 # []))) @ (4 # (5 # [])) = 1 # 2 # 3 # 4 # 5 # []" by simp

fun hd :: "nat \<Rightarrow> natlist \<Rightarrow> nat" where
  "hd init [] = init"
| "hd _ (x # xs) = x"

fun tl :: "natlist \<Rightarrow> natlist" where
  "tl [] = []"
| "tl (x # xs) = xs"

lemma test_hd1: "hd 0 (1 # 2 # 3 # []) = 1" by simp
lemma test_hd2: "hd 0 [] = 0" by simp
lemma test_tl: "tl (1 # 2 # 3 # []) = 2 # 3 # []" by simp

end
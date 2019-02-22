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

end
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

fun swap_pair :: "natprod \<Rightarrow> natprod" where
  "swap_pair (pair (x, y)) = pair (y, x)"

fun swap_pair' :: "nat * nat \<Rightarrow> nat * nat" where
  "swap_pair' (x, y) = (y, x)"

theorem subjective_pairing': "\<forall> n m::nat. (n, m) = (fst'(n, m), snd'(n, m))" by simp

(* theorem subjective_pairing: "\<forall> p::natprod. p = pair (fst p, snd p)" *)
theorem subjective_pairing: "p = pair (fst p, snd p)"
  apply (induction p)
  apply (auto)
  done

theorem snd_fst_is_swap: "(snd' p, fst' p) = swap_pair' p"
  apply (induction p)
  apply (simp)
  done

theorem fst_swap_is_snd: "fst' (swap_pair' p) = snd' p"
  apply (induction p)
  apply (simp)
  done

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

fun nonzeros :: "natlist \<Rightarrow> natlist" where
  "nonzeros [] = []"
| "nonzeros (x # xs) = (if x = 0 then nonzeros xs else x # (nonzeros xs))"

lemma test_nonzeros: "nonzeros (0 # 1 # 0 # 2 # 3 # 0 # 0 # []) = 1 # 2 # 3 # []"
  apply (simp)
  done

fun oddmembers :: "natlist \<Rightarrow> natlist" where
  "oddmembers [] = []"
| "oddmembers (x # xs) = (if odd x then x # oddmembers xs else oddmembers xs)"

lemma test_oddmembers: "oddmembers (0 # 1 # 0 # 2 # 3 # 0 # 0 # []) = 1 # 3 # []"
  apply (simp)
  done

definition countoddmembers :: "natlist \<Rightarrow> nat" where
  "countoddmembers xs = length (oddmembers xs)"

lemma test_countoddmembers1: "countoddmembers (1 # 0 # 3 # 1 # 4 # 5 # []) = 4"
  unfolding countoddmembers_def
  apply (simp)
  done

lemma test_countoddmembers2: "countoddmembers (0 # 2 # 4 # []) = 0"
  unfolding countoddmembers_def
  apply (simp)
  done

lemma test_countoddmembers3: "countoddmembers [] = 0"
  unfolding countoddmembers_def
  apply (simp)
  done

subsection {* inferences *}

theorem nil_app: "\<forall> xs::natlist. [] @ xs = xs" by simp

(* theorem tl_length_pred: "\<forall> xs::natlist. pred (length xs) = length (tl xs)" *)
theorem tl_length_pred: "pred (length xs) = length (tl xs)"
  apply (induction xs)
   apply (simp_all)
  done

(* theorem app_assoc: "\<forall> xs ys::natlist. (xs @ ys) @zs = xs @ (ys @ zs)" *)
theorem app_assoc: "(xs @ ys) @zs = xs @ (ys @ zs)"
  apply (induction xs)
   apply (simp_all)
  done

fun rev :: "natlist \<Rightarrow> natlist" where
  "rev [] = []"
| "rev (x # xs) = (rev xs) @ (x # [])"

lemma test_rev1: "rev (1 # 2 # 3 # []) = 3 # 2 # 1 # []" by simp
lemma test_rev2: "rev [] = []" by simp

(* theorem app_length: "\<forall> xs ys::natlist. length (xs @ ys) = (length xs) + (length ys)" *)
theorem app_length: "length (xs @ ys) = (length xs) + (length ys)"
  apply (induct xs)
   apply (simp_all)
  done

(* theorem rev_length: "\<forall> xs::natlist. length (rev xs) = length xs" *)
theorem rev_length: "length (rev xs) = length xs"
  apply (induct xs)
   apply (simp)
  apply (simp add: app_length)
  done

(* theorem app_nil_r: "\<forall> xs::natlist. xs @ [] = xs" *)
theorem app_nil_r: "xs @ [] = xs"
  apply (induction xs)
   apply (simp_all)
  done

(*
theorem rev_app_distr: "rev (xs @ ys) = (rev xs) @ (rev ys)"
  apply (induction xs)
   apply (simp)
*)

end
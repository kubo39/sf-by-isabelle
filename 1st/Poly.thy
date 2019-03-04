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

value "repeat (4::nat) 2" (* "4 # 4 # []" :: "nat list" *)
lemma test_repeat2 [simp]: "repeat 1 0 = []" by auto
(* lemma test_repeat1: "repeat 4 2 = 4 # 4 # []" *)

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

theorem app_nil_r: "xs @ [] = xs"
  apply (induction xs)
   apply (auto)
  done

theorem app_assoc: "xs @ m @ n = (xs @ m) @ n"
  apply (induction xs)
   apply (auto)
  done

theorem app_length: "length (xs @ ys) = length xs + length ys"
  apply (induction xs)
   apply (auto)
  done

theorem rev_app_distr: "rev (xs @ ys) = rev ys @ rev xs"
  apply (induction xs)
   apply (simp add: app_nil_r)
  apply (simp add: app_assoc)
  done

theorem rev_involutive: "rev (rev xs) = xs"
  apply (induction xs)
   apply (auto)
  apply (simp add: rev_app_distr)
  done


fun fst :: "'X * 'Y \<Rightarrow> 'X" where "fst (x, y) = x"
lemma test_fst1: "fst (3, 4) = 3" by simp

fun snd :: "'X * 'Y \<Rightarrow> 'Y" where "snd (x, y) = y"
lemma test_snd1: "snd (3, 4) = 4" by simp

fun combine :: "'a list \<Rightarrow> 'b list \<Rightarrow> ('a * 'b) list" where
  "combine [] _ = []"
| "combine _ [] = []"
| "combine (x # xs) (y # ys) = (x, y) # (combine xs ys)"

value "combine ((1::nat) # 2 # []) ((True::bool) # False # [])"

fun split :: "('a * 'b) list \<Rightarrow> ('a list) * ('b list)" where
  "split [] = ([], [])"
| "split (x # xs) = (fst x # fst (split xs), snd x # snd (split xs))"

lemma test_split: "split ((1, False) # (2, False) # []) = (1 # 2 # [], False # False # [])"
  apply (simp)
  done

datatype 'a option = None | Some 'a

fun nth_error :: "'a list \<Rightarrow> nat \<Rightarrow> 'a option" where
  "nth_error [] _ = None"
| "nth_error (x # xs) n = (if n = 0 then Some x else nth_error xs (pred n))"

lemma test_nth_error2: "nth_error ((1 # []) # ((Suc 1) # []) # []) 1 = Some ((Suc 1) # [])"
  apply (simp)
  done

lemma test_nth_error3: "nth_error (True # []) (Suc 1) = None"
  apply (simp)
  done

fun do3times :: "('X \<Rightarrow> 'X) \<Rightarrow> 'X \<Rightarrow> 'X" where
  "do3times f n = f (f (f n))"

value "do3times minustwo 9" (* "3" :: "nat" *)
(* lemma test_do3times: "do3times minustwo 9 = 3" *)


fun filter :: "('a \<Rightarrow> bool) \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "filter _ [] = []"
| "filter f (x # xs) = (case f x of True \<Rightarrow> x # (filter f xs) | False \<Rightarrow> filter f xs)"

lemma test_filter1: "filter evenb (1 # (Suc 1) # (Suc (Suc 1)) # (Suc (Suc (Suc 1))) # []) = 2 # 4 # []"
  apply (simp)
  done

fun countoddmembers' :: "nat list \<Rightarrow> nat" where
  "countoddmembers' xs = length (filter oddb xs)"

(* lemma test_countoddmembers: "countoddmembers' (1 # 0 # (Suc (Suc 1)) # 1 # 4 # 5 # []) = 4" *)

fun map :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a list \<Rightarrow> 'b list" where
  "map _ [] = []"
| "map f (x # xs) = (f x) # (map f xs)"

value "map (plus 3) (1 # 2 # [])"

lemma test_map2: "map oddb (Suc 1 # 1 # Suc 1 # (Suc (Suc (Suc (Suc 1)))) # []) = (False # True # False # True # [])"
  apply (simp)
  done

(*
theorem map_rev: "map f (rev xs) = rev (map f xs)"
  apply (induction xs)
   apply (auto)
*)

fun fold :: "('a \<Rightarrow> 'b \<Rightarrow> 'b) \<Rightarrow> 'a list \<Rightarrow> 'b \<Rightarrow> 'b" where
  "fold _ [] b = b"
| "fold f (x # xs) b = f x (fold f xs b)"

value "fold plus (1 # 2 # 3 # 4 # []) 0"

end

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

fun hd_error :: "'a list \<Rightarrow> 'a option" where
  "hd_error [] = None"
| "hd_error (x # xs) = Some x"

lemma test_hd_error1: "hd_error (1 # 2 # []) = Some 1"
  apply (simp)
  done

lemma test_hd_error2: "hd_error ((1 # []) # (2 # []) # []) = Some (1 # [])"
  apply (simp)
  done

fun doit3times :: "('X \<Rightarrow> 'X) \<Rightarrow> 'X \<Rightarrow> 'X" where
  "doit3times f n = f (f (f n))"

value "doit3times minustwo 9" (* "3" :: "nat" *)
(* lemma test_doit3times: "doit3times minustwo 9 = 3" *)

lemma test_doit3times': "doit3times negb True = False"
  apply (simp)
  done

fun filter :: "('a \<Rightarrow> bool) \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "filter _ [] = []"
| "filter f (x # xs) = (case f x of True \<Rightarrow> x # (filter f xs) | False \<Rightarrow> filter f xs)"

lemma test_filter1: "filter evenb (1 # (Suc 1) # (Suc (Suc 1)) # (Suc (Suc (Suc 1))) # []) = 2 # 4 # []"
  apply (simp)
  done

fun countoddmembers' :: "nat list \<Rightarrow> nat" where
  "countoddmembers' xs = length (filter oddb xs)"

(* lemma test_countoddmembers: "countoddmembers' (1 # 0 # (Suc (Suc 1)) # 1 # 4 # 5 # []) = 4" *)

lemma test_anon_fun': "doit3times (\<lambda> n. n * n) (2::nat) = 256"
  apply (simp)
  done

definition filter_even_gt7 :: "nat list \<Rightarrow> nat list" where
  "filter_even_gt7 xs = filter (\<lambda> n. if n > 7 then evenb n else False) xs"

value "filter_even_gt7 (1 # 2 # 6 # 9 # 10 # 3 # 12 # 8 # []) = (10 # 12 # 8 # [])"
(*
lemma test_filter_even_gt7_1: "filter_even_gt7 (1 # 2 # 6 # 9 # 10 # 3 # 12 # 8 # []) = (10 # 12 # 8 # [])"
  apply (simp)
*)

fun map :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a list \<Rightarrow> 'b list" where
  "map _ [] = []"
| "map f (x # xs) = (f x) # (map f xs)"

value "map (plus 3) (1 # 2 # [])"

(* lemma test_map1: "map (\<lambda> x. plus 3 x) ((Suc 1) # 0 # (Suc 1) # []) = (5 # 3 # 5 # [])" *)

lemma test_map2: "map oddb (Suc 1 # 1 # Suc 1 # (Suc (Suc (Suc (Suc 1)))) # []) = (False # True # False # True # [])"
  apply (simp)
  done

(*
theorem map_rev: "map f (rev xs) = rev (map f xs)"
  apply (induction xs)
   apply (auto)
*)

fun flat_map :: "('a \<Rightarrow> 'b list) \<Rightarrow> 'a list \<Rightarrow> 'b list" where
  "flat_map _ [] = []"
| "flat_map f (x # xs) = (f x) @ (flat_map f xs)"

lemma test_flat_map1: "flat_map (\<lambda> n. n # (n + 1) # (n + 2) # []) (1 # []) = (1 # 2 # 3 # [])"
  apply (simp)
  done

fun option_map :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a option \<Rightarrow> 'b option" where
  "option_map _ None = None"
| "option_map f (Some x) = Some (f x)"


fun fold :: "('a \<Rightarrow> 'b \<Rightarrow> 'b) \<Rightarrow> 'a list \<Rightarrow> 'b \<Rightarrow> 'b" where
  "fold _ [] b = b"
| "fold f (x # xs) b = f x (fold f xs b)"

value "fold plus (1 # 2 # 3 # 4 # []) 0"

lemma fold_example1: "fold mult (1 # (Suc 1) # (Suc (Suc 1)) # (Suc (Suc (Suc 1))) # []) 1 = 24"
  apply (simp)
  done

lemma fold_example2: "fold andb (True # True # False # True # []) True = False"
  apply (simp)
  done

definition constfun :: "'a \<Rightarrow> nat \<Rightarrow> 'a" where
  "constfun x = (\<lambda> n. x)"

definition ftrue where "ftrue = constfun True"

lemma constfun_example1: "ftrue 0 = True"
  unfolding ftrue_def
  unfolding constfun_def
  apply (simp)
  done

lemma constfun_example2: "(constfun 5) 99 = 5"
  unfolding constfun_def
  apply (simp)
  done

definition plus3 :: "nat \<Rightarrow> nat" where
  "plus3 = plus 3"

(*
lemma test_plus3: "plus3 4 = 7"
  apply (simp add: plus3_def)
*)

definition fold_length :: "'a list \<Rightarrow> nat" where
  "fold_length xs = fold (\<lambda> _ n. Suc n) xs 0"

lemma test_fold_length: "fold_length (4 # 7 # 0 # []) = 3"
  unfolding fold_length_def
  apply (simp)
  done

theorem fold_length_correct: "fold_length xs = length xs"
  unfolding fold_length_def
  apply (induction xs)
   apply (simp)
  apply (simp)
  done

end

theory Imp
  imports Basics
begin

datatype aexp = ANum nat |
                APlus aexp aexp |
                AMinus aexp aexp |
                AMult aexp aexp

datatype bexp = BTrue |
                BFalse |
                BEq aexp aexp |
                BLe aexp aexp |
                BNot bexp |
                BAnd bexp bexp

section {* Evaluation *}

fun aeval :: "aexp \<Rightarrow> nat" where
  "aeval (ANum n) = n"
| "aeval (APlus a1 a2) = (aeval a1) + (aeval a2)"
| "aeval (AMinus a1 a2) = (aeval a1) - (aeval a2)"
| "aeval (AMult a1 a2) = (aeval a1) * (aeval a2)"

lemma test_aeval: "aeval (APlus (ANum 2) (ANum 2)) = 4"
  apply (simp)
  done

fun beval :: "bexp \<Rightarrow> bool" where
  "beval BTrue = True"
| "beval BFalse = False"
| "beval (BEq a1 a2) = beq_nat (aeval a1) (aeval a2)"
| "beval (BLe a1 a2) = leb (aeval a1) (aeval a2)"
| "beval (BNot b1) = negb (beval b1)"
| "beval (BAnd b1 b2) = andb (beval b1) (beval b2)"

section {* Optimization *}

fun optimize_0plus :: "aexp \<Rightarrow> aexp" where
  "optimize_0plus (ANum n) = ANum n"
| "optimize_0plus (APlus (ANum 0) e2) = e2"
| "optimize_0plus (APlus e1 e2) = APlus (optimize_0plus e1) (optimize_0plus e2)"
| "optimize_0plus (AMinus e1 e2) = AMinus (optimize_0plus e1) (optimize_0plus e2)"
| "optimize_0plus (AMult e1 e2) = AMult (optimize_0plus e1) (optimize_0plus e2)"

lemma test_optimize_0plus:
  "(beval (BEq (optimize_0plus (APlus (ANum (Suc 1)) (APlus (ANum 0) (APlus (ANum 0) (ANum 1)))))
           (APlus (ANum (Suc 1)) (ANum 1)))) = True"
  apply (simp)
  done

theorem optimize_0plus_sound: "aeval (optimize_0plus a) = aeval a"
  apply (induct a)
     apply (simp) (* ANum *)
    apply (case_tac a) (* APlus *)
       apply (case_tac a1) (* a1 = ANum n *)
          apply (simp)
  oops

section {* Expression with variables *}

hide_type aexp
hide_type bexp

datatype aexpr = ANum nat |
                 AId string |
                 APlus aexpr aexpr |
                 AMinus aexpr aexpr |
                AMult aexpr aexpr

datatype bexpr = BTrue |
                BFalse |
                BEq aexpr aexpr |
                BLe aexpr aexpr |
                BNot bexpr |
                BAnd bexpr bexpr

type_synonym state = "string \<Rightarrow> nat"

fun aval :: "state \<Rightarrow> aexpr \<Rightarrow> nat" where
  "aval _ (ANum n) = n"
| "aval st (AId x) = st x"
| "aval st (APlus a1 a2) = (aval st a1) + (aval st a2)"
| "aval st (AMinus a1 a2) = (aval st a1) - (aval st a2)"
| "aval st (AMult a1 a2) = (aval st a1) * (aval st a2)"

fun bval :: "state \<Rightarrow> bexpr \<Rightarrow> bool" where
  "bval _ BTrue = True"
| "bval _ BFalse = False"
| "bval st (BEq a1 a2) = beq_nat (aval st a1) (aval st a2)"
| "bval st (BLe a1 a2) = leb (aval st a1) (aval st a2)"
| "bval st (BNot b1) = negb (bval st b1)"
| "bval st (BAnd b1 b2) = andb (bval st b1) (bval st b2)"

end
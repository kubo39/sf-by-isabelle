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

end
theory Basics
  imports Main
begin

section {* Basics *}

datatype day = monday | tuesday | wednesday |
  thursday | friday | saturday | sunday

fun next_weekday :: "day \<Rightarrow> day" where
  "next_weekday monday = tuesday"
  | "next_weekday tuesday = wednesday"
  | "next_weekday wednesday = thursday"
  | "next_weekday thursday = friday"
  | "next_weekday friday = monday"
  | "next_weekday saturday = monday"
  | "next_weekday sunday = monday"

value "next_weekday friday" (* "monday" :: "day" *)
value "next_weekday (next_weekday saturday)" (* "tuesday" :: "day" *)

lemma test_next_weekday: "next_weekday (next_weekday saturday) = tuesday" by simp

datatype bool = true | false

fun negb :: "bool \<Rightarrow> bool" where
  "negb true = false"
  | "negb false = true"

fun andb :: "bool \<Rightarrow> bool \<Rightarrow> bool" where
  "andb true b2 = b2"
  | "andb false _ = false"

fun orb :: "bool \<Rightarrow> bool \<Rightarrow> bool" where
  "orb true _ = true"
  | "orb false b2 = b2"

lemma test_orb1: "orb true false = true" by simp
lemma test_orb2: "orb false false = false" by simp
lemma test_orb3: "orb false true = true" by simp
lemma test_orb4: "orb true true = true" by simp

end


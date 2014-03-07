theory Monolith
imports Main
        Rat
begin

(* exercise 2.22 *)
(* Between every two rational numbers there is a third *)
lemma DensityOfRationals1:
  fixes a b :: rat
  shows "\<exists>(x::rat). a < x \<and> x < b"
sorry

lemma DensityOfRationals2:
  fixes a b :: rat
  obtains x where "a < x \<and> x < b"
sorry

lemma exercise_4_10:
  shows "{a}={b} \<longleftrightarrow> a=b"
sorry

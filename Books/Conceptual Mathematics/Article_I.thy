theory Article_I
imports "~~/src/HOL/Library/FuncSet"
begin

datatype_new person = John | Mary | Sam
definition "people = (UNIV :: person set)"
datatype_new food = coffee | eggs
definition "breakfasts = (UNIV :: food set)"

lemma "card (UNIV :: (person \<Rightarrow> food) set) = 8"
  oops

lemma
  assumes "card A = 3" and "card B = 2"
  shows "card {F. \<forall>a\<in>A. \<exists>!b\<in>B. (a,b) \<in> F} = 8"
  (* quickcheck finds a counterexample, but I don't know what to make of it... *)
  oops

lemma
  assumes "card A = 3" and "card B = 2"
  shows "card (A \<rightarrow> B) = 8"
  oops
value "({}::(person set)) \<rightarrow> ({}::(person set))"
lemma
  assumes "finite A" and "finite B"
  shows "card (A \<rightarrow> B) = (card B) ^ (card A)"

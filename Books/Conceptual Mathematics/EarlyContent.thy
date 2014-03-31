theory EarlyContent
imports "~~/src/HOL/Library/FuncSet"
begin

text {* let's explore some different ways of representing the content from Article I *}

lemma tmp:
  assumes "finite A"
  shows "card (A \<rightarrow>\<^sub>E B) = card B ^ card A"
  thm card_PiE
  thm card_PiE[OF `finite A`]
  apply (unfold card_PiE[OF `finite A`])
  thm setprod_constant
  thm setprod_constant[OF `finite A`]
  apply (unfold setprod_constant[OF `finite A`])
  apply (rule refl)
  done

lemma "\<lbrakk>finite A; card A = 0\<rbrakk> \<Longrightarrow> card {f \<in> A\<rightarrow>\<^sub>EA. compose A f f = f} = 1" oops
lemma "\<lbrakk>finite A; card A = 1\<rbrakk> \<Longrightarrow> card {f \<in> A\<rightarrow>\<^sub>EA. compose A f f = f} = 1" oops
lemma "\<lbrakk>finite A; card A = 2\<rbrakk> \<Longrightarrow> card {f \<in> A\<rightarrow>\<^sub>EA. compose A f f = f} = 3"
  apply (unfold compose_def)
  apply (simp add: extensional_funcset_def)
thm ext
  apply auto
oops
lemma "\<lbrakk>finite A; card A = 3\<rbrakk> \<Longrightarrow> card {f \<in> A\<rightarrow>\<^sub>EA. compose A f f = f} = 10" oops
lemma "\<lbrakk>finite A; card A = 4\<rbrakk> \<Longrightarrow> card {f \<in> A\<rightarrow>\<^sub>EA. compose A f f = f} = 0"
  


lemma exercise_two_point_six:
  assumes "finite A" and "card A = 3"
  shows "card {f. f \<in> (A \<rightarrow>\<^sub>E A) \<and> f\<circ>f = f} = 10"
oops



datatype PeopleType = John | Mary | Sam
print_theorems
term PeopleType_rep_set
thm PeopleType_rep_set_def
term PeopleType_rec_set
thm PeopleType_rec_set_def

datatype breakfastType = eggs | oatmeal | toast | coffee

primrec favorite_breakfast where
  "favorite_breakfast John = eggs"
| "favorite_breakfast Mary = coffee"
| "favorite_breakfast Sam = coffee"

primrec favorite_person where
  "favorite_person John = Mary"
| "favorite_person Mary = John"
| "favorite_person Sam = Mary"

text {* I'm not sure how to say "I don't care what John/Mary/Sam are, I just want them to be distinct elements of a set" *}
definition PeopleSet where
  "PeopleSet \<equiv> {1, 2, 3}"
definition FoodSet where
  "FoodSet \<equiv> {1, 2, 3, 4}"
definition FavBreakfastRel where
  "FavBreakfastRel \<equiv> {(1, 1), (2, 4), (3, 4)}"
definition FavPersonRel where
  "FavPersonRel \<equiv> {(1, 2), (2, 1), (3, 2)}"

definition FavBreakfast where
  "FavBreakfast \<equiv> {(John, eggs), (Mary, coffee), (Sam, coffee)}"
definition FavPerson where
  "FavPerson \<equiv> {(John, Mary), (Mary, John), (Sam, Mary)}"

lemma "single_valued FavPerson" oops

text {* For `FavBreakfast` to be viable, I think I would need to be able to *apply* it and *compose* it. *}



lemma "{John, Mary, Sam} = {x :: PeopleType . True}" oops



lemma two: "card {f :: PeopleType \<Rightarrow> breakfastType. True} = 8" oops
lemma seven: "card {g :: breakfastType \<Rightarrow> breakfastType. g \<circ> g = g} = 3" oops


locale Two_through_Nine =
  fixes A :: "'a set"
    and (* B :: "('b::{equal,enum}) set" *)
        B :: "'b set"
  assumes A_three: "card A = 3"
      and B_two: "card B = 2"
begin

lemma two: "card (A \<rightarrow> B) = 8"
  using A_three and B_two apply auto
lemma seven: "card {g\<in>B\<rightarrow>B. g\<circ>g = g} = 3" oops

end

definition total_on :: "'a set \<Rightarrow> ('a * 'b) set \<Rightarrow> bool"
where
  "total_on A r \<longleftrightarrow> (\<forall>x\<in>A. \<exists>y\<in>(Range r). (x, y) \<in> r)"

abbreviation "total \<equiv> total_on UNIV"

lemma total_on_empty [simp]: "total_on {} r"
  by (simp add: total_on_def)


subsubsection {* Single valued relations *}

definition single_valued :: "('a \<times> 'b) set \<Rightarrow> bool"
where
  "single_valued r \<longleftrightarrow> (\<forall>x y. (x, y) \<in> r \<longrightarrow> (\<forall>z. (x, z) \<in> r \<longrightarrow> y = z))"

abbreviation single_valuedP :: "('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> bool" where
  "single_valuedP r \<equiv> single_valued {(x, y). r x y}"

lemma single_valuedI:
  "ALL x y. (x,y):r --> (ALL z. (x,z):r --> y=z) ==> single_valued r"
  by (unfold single_valued_def)

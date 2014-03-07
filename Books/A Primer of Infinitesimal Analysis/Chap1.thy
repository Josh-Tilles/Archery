theory Chap1
imports HOL
begin

(* Groups *)
subsection {* Abstract structures *}
locale semigroup =
  fixes f :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" (infixl "*" 70)
  assumes assoc: "(a * b) * c = a * (b * c)"

locale abel_semigroup = semigroup +
  assumes commute: "a * b = b * a"

locale monoid = semigroup +
  fixes z :: 'a ("1")
  assumes left_neutral [simp]: "1 * a = a"
  assumes right_neutral [simp]: "a * 1 = a"

locale comm_monoid = abel_semigroup +
  fixes z :: 'a ("1")
  assumes comm_neutral: "a * 1 = a"

sublocale comm_monoid < monoid
  apply default
  defer
  apply (rule comm_neutral)
  apply (subst commute)
  apply (rule comm_neutral)
done

locale zero =
  fixes zero :: 'a  ("0")

locale one =
  fixes one  :: 'a  ("1")

locale plus =
  fixes plus :: "'a \<Rightarrow> 'a \<Rightarrow> 'a"  (infixl "+" 65)

locale minus =
  fixes minus :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" (infixl "-" 65)

locale uminus =
  fixes uminus :: "'a \<Rightarrow> 'a" ("- _" [81] 80)

locale times =
  fixes times :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" (infixl "*" 70)

subsection {* Semigroups and Monoids *}

locale semigroup_add = plus +
  assumes add_assoc: "(a + b) + c = a + (b + c)"

sublocale semigroup_add < add!: semigroup plus
  by default (fact add_assoc)

locale ab_semigroup_add = semigroup_add +
  assumes add_commute: "a + b = b + a"

sublocale ab_semigroup_add < add!: abel_semigroup plus
  by default (fact add_commute)

locale semigroup_mult = times +
  assumes mult_assoc: "(a * b) * c = a * (b * c)"

sublocale semigroup_mult < mult!: semigroup times
  by default (fact mult_assoc)

locale ab_semigroup_mult = semigroup_mult +
  assumes mult_commute: "a * b = b * a"

sublocale ab_semigroup_mult < mult!: abel_semigroup times
  by default (fact mult_commute)

locale monoid_add = zero + semigroup_add +
  assumes add_0_left: "0 + a = a"
    and add_0_right: "a + 0 = a"

sublocale monoid_add < add!: monoid plus 0
  by default (fact add_0_left add_0_right)+

lemma (in zero) zero_reorient: "0 = x \<longleftrightarrow> x = 0"
  by (rule eq_commute)

locale comm_monoid_add = zero + ab_semigroup_add +
  assumes add_0: "0 + a = a"

sublocale comm_monoid_add < add!: comm_monoid plus 0
  apply default
  apply (subst add_commute)
  apply (rule add_0)
done

sublocale comm_monoid_add < monoid_add
  apply default
  apply (rule add_0)
  apply (subst add_commute)
  apply (rule add_0)
done

locale comm_monoid_diff = comm_monoid_add + minus +
  assumes diff_zero: "a - 0 = a"
    and zero_diff: "0 - a = 0"
    and add_diff_cancel_left: "(c + a) - (c + b) = a - b"
    and diff_diff_add: "a - b - c = a - (b + c)"

locale monoid_mult = one + semigroup_mult +
  assumes mult_1_left: "1 * a  = a"
    and mult_1_right: "a * 1 = a"

sublocale monoid_mult < mult!: monoid times 1
  by default (fact mult_1_left mult_1_right)+

lemma (in monoid) one_reorient: "1 = x \<longleftrightarrow> x = 1"
  by (rule eq_commute)

locale comm_monoid_mult = one + ab_semigroup_mult +
  assumes mult_1: "1 * a = a"

sublocale comm_monoid_mult < mult!: comm_monoid times 1
  apply default
(*
  apply (rule mult_commute)

  WHY WON'T IT WORK??
  ...
  oh, right.
*)
  apply (subst mult_commute)
  apply (rule mult_1)
done

sublocale comm_monoid_mult < monoid_mult
  by default (fact mult.left_neutral mult.right_neutral)+

locale cancel_semigroup_add = semigroup_add +
  assumes add_left_imp_eq: "a + b = a + c \<Longrightarrow> b = c"
  assumes add_right_imp_eq: "b + a = c + a \<Longrightarrow> b = c"

locale cancel_ab_semigroup_add = ab_semigroup_add +
  assumes add_imp_eq: "a + b = a + c \<Longrightarrow> b = c"
begin
  sublocale cancel_semigroup_add
  proof
    fix a b c :: 'a
    assume "a + b = a + c" 
    then show "b = c" by (rule add_imp_eq)
  next
    fix a b c :: 'a
    assume "b + a = c + a"
    then have "a + b = a + c"
apply (simp only: add_commute)
done
    then show "b = c" by (rule add_imp_eq)
  qed
end

locale cancel_comm_monoid_add = cancel_ab_semigroup_add + comm_monoid_add

locale group_add = minus + uminus + monoid_add +
  assumes left_minus (*[simp]*): "(- a) + a = 0"
  assumes diff_minus: "a - b = a + (- b)"

(* subclass *)
sublocale cancel_semigroup_add < group_add
sorry

locale ab_group_add = minus + uminus + comm_monoid_add +
  assumes ab_left_minus: "(- a) + a = 0"
  assumes ab_diff_minus: "a - b = a + (- b)"
begin
  sublocale group_add
  sorry

  sublocale cancel_comm_monoid_add
  sorry
end



(* Rings *)
locale semiring = ab_semigroup_add + semigroup_mult +
  assumes distrib_right: "(a + b) * c = a * c + b * c"
  assumes distrib_left: "a * (b + c) = a * b + a * c"

locale mult_zero = times + zero +
  assumes mult_zero_left [simp]: "0 * a = 0"
  assumes mult_zero_right [simp]: "a * 0 = 0"

locale semiring_0 = semiring + comm_monoid_add + mult_zero

locale semiring_0_cancel = semiring + cancel_comm_monoid_add
begin
  sublocale semiring_0 sorry
end

locale comm_semiring = ab_semigroup_add + ab_semigroup_mult +
  assumes distrib: "(a + b) * c = a * c + b * c"
begin
  sublocale semiring sorry
end

locale comm_semiring_0 = comm_semiring + comm_monoid_add + mult_zero
begin
  sublocale semiring_0 sorry
end

locale comm_semiring_0_cancel = comm_semiring + cancel_comm_monoid_add
begin
  sublocale semiring_0_cancel sorry
  sublocale comm_semiring_0 sorry
end

locale zero_neq_one = zero + one +
  assumes zero_neq_one [simp]: "0 \<noteq> 1"
begin
  lemma one_neq_zero [simp]: "1 \<noteq> 0"
    by (rule not_sym) (rule zero_neq_one)
end

locale semiring_1 = zero_neq_one + semiring_0 + monoid_mult

text {* Abstract divisibility *}

locale dvd = times
begin

definition dvd :: "'a \<Rightarrow> 'a \<Rightarrow> bool" (infix "dvd" 50) where
  "b dvd a \<longleftrightarrow> (\<exists>k. a = b * k)"

lemma dvdI [intro?]: "a = b * k \<Longrightarrow> b dvd a"
  unfolding dvd_def ..

lemma dvdE [elim?]: "b dvd a \<Longrightarrow> (\<And>k. a = b * k \<Longrightarrow> P) \<Longrightarrow> P"
  unfolding dvd_def by blast 

end

locale comm_semiring_1 = zero_neq_one + comm_semiring_0 + comm_monoid_mult + dvd
  (*previously almost_semiring*)
begin
  sublocale semiring_1 sorry
end

locale no_zero_divisors = zero + times +
  assumes no_zero_divisors: "a \<noteq> 0 \<Longrightarrow> b \<noteq> 0 \<Longrightarrow> a * b \<noteq> 0"

locale semiring_1_cancel = semiring + cancel_comm_monoid_add
  + zero_neq_one + monoid_mult
begin
  sublocale semiring_0_cancel sorry
  sublocale semiring_1 sorry
end

locale comm_semiring_1_cancel = comm_semiring + cancel_comm_monoid_add
  + zero_neq_one + comm_monoid_mult
begin
  sublocale semiring_1_cancel sorry
  sublocale comm_semiring_0_cancel sorry
  sublocale comm_semiring_1 sorry
end

locale ring = semiring + ab_group_add
begin
  sublocale semiring_0_cancel sorry
end

locale comm_ring = comm_semiring + ab_group_add
begin
  sublocale ring sorry
  sublocale comm_semiring_0_cancel sorry
end

locale ring_1 = ring + zero_neq_one + monoid_mult
begin
  sublocale semiring_1_cancel sorry
end

locale comm_ring_1 = comm_ring + zero_neq_one + comm_monoid_mult
  (*previously ring*)
begin
  sublocale ring_1 sorry
  sublocale comm_semiring_1_cancel sorry
end

locale ring_no_zero_divisors = ring + no_zero_divisors

locale ring_1_no_zero_divisors = ring_1 + ring_no_zero_divisors

locale idom = comm_ring_1 + no_zero_divisors
begin
  sublocale ring_1_no_zero_divisors sorry
end

subsection {* Division rings *}

text {*
  A division ring is like a field, but without the commutativity requirement.
*}

locale inverse =
  fixes inverse :: "'a \<Rightarrow> 'a"
    and divide :: "'a \<Rightarrow> 'a \<Rightarrow> 'a"  (infixl "'/" 70)

locale division_ring = ring_1 + inverse +
  assumes left_inverse [simp]:  "a \<noteq> 0 \<Longrightarrow> inverse a * a = 1"
  assumes right_inverse [simp]: "a \<noteq> 0 \<Longrightarrow> a * inverse a = 1"
  assumes divide_inverse: "a / b = a * inverse b"
begin
  sublocale ring_1_no_zero_divisors sorry
end

locale division_ring_inverse_zero = division_ring +
  assumes inverse_zero [simp]: "inverse 0 = 0"

subsection {* Fields *}

locale field = comm_ring_1 + inverse +
  assumes field_inverse: "a \<noteq> 0 \<Longrightarrow> inverse a * a = 1"
  assumes field_divide_inverse: "a / b = a * inverse b"
begin
  sublocale division_ring sorry
  sublocale idom sorry
end

locale field_inverse_zero = field +
  assumes field_inverse_zero: "inverse 0 = 0"
begin
  sublocale division_ring_inverse_zero sorry
end




subsection {* Abstract ordering *}

(*
locale ordering =
  fixes less_eq :: "'a \<Rightarrow> 'a \<Rightarrow> bool" (infix "\<preceq>" 50)
   and less :: "'a \<Rightarrow> 'a \<Rightarrow> bool" (infix "\<prec>" 50)
  assumes strict_iff_order: "a \<preceq> b \<longleftrightarrow> a \<preceq> b \<and> a \<noteq> b"
  assumes refl: "a \<preceq> a" -- {* not @{text iff}: makes problems due to multiple (dual) interpretations *}
    and antisym: "a \<preceq> b \<Longrightarrow> b \<preceq> a \<Longrightarrow> a = b"
    and trans: "a \<preceq> b \<Longrightarrow> b \<preceq> c \<Longrightarrow> a \<preceq> c"
*)
locale ordering =
  fixes less :: "'a \<Rightarrow> 'a \<Rightarrow> bool" (infix "\<prec>" 50)
  assumes trans: "\<lbrakk>a \<prec> b; b \<prec> c\<rbrakk> \<Longrightarrow> a \<prec> c"
    and strict: "\<not>(a \<prec> a)"
begin
  definition less_eq :: "'a \<Rightarrow> 'a \<Rightarrow> bool" (infix "\<preceq>" 50) where
    "a \<preceq> b \<longleftrightarrow> \<not>(b \<prec> a)"

  notation
    less_eq  ("op <=") and
    less_eq  ("(_/ <= _)" [51, 51] 50) and
    less  ("op <") and
    less  ("(_/ < _)"  [51, 51] 50)
  
  notation (xsymbols)
    less_eq  ("op \<le>") and
    less_eq  ("(_/ \<le> _)"  [51, 51] 50)
end

locale linorder = ordering +
  assumes linear: "x \<le> y \<or> y \<le> x"

locale ordered_ab_semigroup_add = ordering + ab_semigroup_add +
  assumes add_left_mono: "a < b \<Longrightarrow> a + c < b + c"

locale ordered_cancel_ab_semigroup_add =
  ordered_ab_semigroup_add + cancel_ab_semigroup_add

locale ordered_ab_semigroup_add_imp_le =
  ordered_cancel_ab_semigroup_add +
  assumes add_le_imp_le_left: "c + a < c + b \<Longrightarrow> a < b"

locale ordered_cancel_comm_monoid_diff = comm_monoid_diff + ordered_ab_semigroup_add_imp_le +
  assumes le_iff_add: "a \<le> b \<longleftrightarrow> (\<exists>c. b = a + c)"

subsection {* Support for reasoning about signs *}

locale ordered_comm_monoid_add =
  ordered_cancel_ab_semigroup_add + comm_monoid_add

locale ordered_ab_group_add =
  ab_group_add + ordered_ab_semigroup_add
begin
  sublocale ordered_cancel_ab_semigroup_add sorry
  sublocale ordered_ab_semigroup_add_imp_le sorry
  sublocale ordered_comm_monoid_add sorry
end

locale linordered_ab_semigroup_add =
  linorder + ordered_ab_semigroup_add

locale linordered_cancel_ab_semigroup_add =
  linorder + ordered_cancel_ab_semigroup_add
begin
  sublocale linordered_ab_semigroup_add sorry
  sublocale ordered_ab_semigroup_add_imp_le sorry
end

locale linordered_ab_group_add = linorder + ordered_ab_group_add
begin
  sublocale linordered_cancel_ab_semigroup_add sorry
end

locale abs =
  fixes abs :: "'a \<Rightarrow> 'a"
begin

  notation (xsymbols)
    abs  ("\<bar>_\<bar>")

  notation (HTML output)
    abs  ("\<bar>_\<bar>")

end

locale sgn =
  fixes sgn :: "'a \<Rightarrow> 'a"

locale abs_if = minus + uminus + ord + zero + abs +
  assumes abs_if: "\<bar>a\<bar> = (if a < 0 then - a else a)"

locale sgn_if = minus + uminus + zero + one + ord + sgn +
  assumes sgn_if: "sgn x = (if x = 0 then 0 else if 0 < x then 1 else - 1)"
begin

lemma sgn0 [simp]: "sgn 0 = 0"
  by (simp add:sgn_if)

end



class ordered_ab_group_add_abs = ordered_ab_group_add + abs +
  assumes abs_ge_zero [simp]: "\<bar>a\<bar> \<ge> 0"
    and abs_ge_self: "a \<le> \<bar>a\<bar>"
    and abs_leI: "a \<le> b \<Longrightarrow> - a \<le> b \<Longrightarrow> \<bar>a\<bar> \<le> b"
    and abs_minus_cancel [simp]: "\<bar>-a\<bar> = \<bar>a\<bar>"
    and abs_triangle_ineq: "\<bar>a + b\<bar> \<le> \<bar>a\<bar> + \<bar>b\<bar>"

locale ordering_top = ordering +
  fixes top :: "'a"
  assumes extremum (*[simp]*): "a \<preceq> top"

class ord =
  fixes less_eq :: "'a \<Rightarrow> 'a \<Rightarrow> bool"
    and less :: "'a \<Rightarrow> 'a \<Rightarrow> bool"
begin

notation
  less_eq  ("op <=") and
  less_eq  ("(_/ <= _)" [51, 51] 50) and
  less  ("op <") and
  less  ("(_/ < _)"  [51, 51] 50)
  
notation (xsymbols)
  less_eq  ("op \<le>") and
  less_eq  ("(_/ \<le> _)"  [51, 51] 50)

notation (HTML output)
  less_eq  ("op \<le>") and
  less_eq  ("(_/ \<le> _)"  [51, 51] 50)

abbreviation (input)
  greater_eq  (infix ">=" 50) where
  "x >= y \<equiv> y <= x"

notation (input)
  greater_eq  (infix "\<ge>" 50)

abbreviation (input)
  greater  (infix ">" 50) where
  "x > y \<equiv> y < x"

end


subsection {* Quasi orders *}

class preorder = ord +
  assumes less_le_not_le: "x < y \<longleftrightarrow> x \<le> y \<and> \<not> (y \<le> x)"
  and order_refl [iff]: "x \<le> x"
  and order_trans: "x \<le> y \<Longrightarrow> y \<le> z \<Longrightarrow> x \<le> z"

subsection {* Partial orders *}

class order = preorder +
  assumes antisym: "x \<le> y \<Longrightarrow> y \<le> x \<Longrightarrow> x = y"

sublocale order < order!: ordering less_eq less +  dual_order!: ordering greater_eq greater
  by default (auto intro: antisym order_trans simp add: less_le)

subsection {* Linear (total) orders *}

class linorder = order +
  assumes linear: "x \<le> y \<or> y \<le> x"

subsection {* (Unique) top and bottom elements *}

class bot =
  fixes bot :: 'a ("\<bottom>")

class order_bot = order + bot +
  assumes bot_least: "\<bottom> \<le> a"

sublocale order_bot < bot!: ordering_top greater_eq greater bot
  by default (fact bot_least)

class top =
  fixes top :: 'a ("\<top>")

class order_top = order + top +
  assumes top_greatest: "a \<le> \<top>"

sublocale order_top < top!: ordering_top less_eq less top
  by default (fact top_greatest)

subsection {* Dense orders *}

class dense_order = order +
  assumes dense: "x < y \<Longrightarrow> (\<exists>z. x < z \<and> z < y)"

class dense_linorder = linorder + dense_order

class no_top = order + 
  assumes gt_ex: "\<exists>y. x < y"

class no_bot = order + 
  assumes lt_ex: "\<exists>y. y < x"

class unbounded_dense_linorder = dense_linorder + no_top + no_bot

subsection {* Wellorders *}

class wellorder = linorder +
  assumes less_induct [case_names less]: "(\<And>x. (\<And>y. y < x \<Longrightarrow> P y) \<Longrightarrow> P x) \<Longrightarrow> P a"


locale linordered_field = field + linordered_idom
begin
  sublocale unbounded_dense_linorder
end

locale linordered_field_inverse_zero = linordered_field + field_inverse_zero

locale SmoothWorld =
  assumes add_0_left: "0 + a = a"
    and add_0_right: "a + 0 = a"
  assumes add_0: "0 + a = a"

(*
- (- a) = a
- 0 = 0

0 + a = a
a - b \<equiv> a + (- b)
a - a = 0
a + b = b + a
a + (b + c) = (a + b) + c

if a \<noteq> 0, then can obtain a^-1
@TODO sexy inverse syntax

a / b = a * b^-1

0 * a = 0
1 * a = a
a * b = b * a
a*(b*c) = (a*b)*c

a * (b + c) = a*b + a*c

a \<noteq> 0 \<longrightarrow> a/a = 1 ( i.e., a * a^-1 = 1 )

*)

(* Orderings *)
locale ordering =
  fixes less_eq :: "'a \<Rightarrow> 'a \<Rightarrow> bool" (infix "\<preceq>" 50)
   and less :: "'a \<Rightarrow> 'a \<Rightarrow> bool" (infix "\<prec>" 50)
  assumes strict_iff_order: "a \<preceq> b \<longleftrightarrow> a \<preceq> b \<and> a \<noteq> b"
  assumes refl: "a \<preceq> a" -- {* not @{text iff}: makes problems due to multiple (dual) interpretations *}
    and antisym: "a \<preceq> b \<Longrightarrow> b \<preceq> a \<Longrightarrow> a = b"
    and trans: "a \<preceq> b \<Longrightarrow> b \<preceq> c \<Longrightarrow> a \<preceq> c"


subsection {* Syntactic orders *}

class ord =
  fixes less_eq :: "'a \<Rightarrow> 'a \<Rightarrow> bool"
    and less :: "'a \<Rightarrow> 'a \<Rightarrow> bool"
begin

notation
  less_eq  ("op <=") and
  less_eq  ("(_/ <= _)" [51, 51] 50) and
  less  ("op <") and
  less  ("(_/ < _)"  [51, 51] 50)
  
notation (xsymbols)
  less_eq  ("op \<le>") and
  less_eq  ("(_/ \<le> _)"  [51, 51] 50)

notation (HTML output)
  less_eq  ("op \<le>") and
  less_eq  ("(_/ \<le> _)"  [51, 51] 50)

abbreviation (input)
  greater_eq  (infix ">=" 50) where
  "x >= y \<equiv> y <= x"

notation (input)
  greater_eq  (infix "\<ge>" 50)

abbreviation (input)
  greater  (infix ">" 50) where
  "x > y \<equiv> y < x"

end


subsection {* Quasi orders *}

class preorder = ord +
  assumes less_le_not_le: "x < y \<longleftrightarrow> x \<le> y \<and> \<not> (y \<le> x)"
  and order_refl [iff]: "x \<le> x"
  and order_trans: "x \<le> y \<Longrightarrow> y \<le> z \<Longrightarrow> x \<le> z"
begin

text {* Reflexivity. *}

lemma eq_refl: "x = y \<Longrightarrow> x \<le> y"
    -- {* This form is useful with the classical reasoner. *}
by (erule ssubst) (rule order_refl)
end

subsection {* Partial orders *}

class order = preorder +
  assumes antisym: "x \<le> y \<Longrightarrow> y \<le> x \<Longrightarrow> x = y"



class ordered_semiring = semiring + comm_monoid_add + ordered_ab_semigroup_add +
  assumes mult_left_mono: "a \<le> b \<Longrightarrow> 0 \<le> c \<Longrightarrow> c * a \<le> c * b"
  assumes mult_right_mono: "a \<le> b \<Longrightarrow> 0 \<le> c \<Longrightarrow> a * c \<le> b * c"

locale ordered_cancel_semiring = ordered_semiring + cancel_comm_monoid_add
begin
  sublocale semiring_0_cancel sorry
end

class linordered_semiring = ordered_semiring + linordered_cancel_ab_semigroup_add
begin
  sublocale ordered_cancel_semiring sorry
  sublocale ordered_comm_monoid_add sorry
end

class linordered_semiring_1 = linordered_semiring + semiring_1

class linordered_semiring_strict = semiring + comm_monoid_add + linordered_cancel_ab_semigroup_add +
  assumes mult_strict_left_mono: "a < b \<Longrightarrow> 0 < c \<Longrightarrow> c * a < c * b"
  assumes mult_strict_right_mono: "a < b \<Longrightarrow> 0 < c \<Longrightarrow> a * c < b * c"
begin
  sublocale semiring_0_cancel sorry
  sublocale linordered_semiring sorry
end

class linordered_semiring_1_strict = linordered_semiring_strict + semiring_1
begin
  sublocale linordered_semiring_1 sorry
end

class ordered_comm_semiring = comm_semiring_0 + ordered_ab_semigroup_add + 
  assumes comm_mult_left_mono: "a \<le> b \<Longrightarrow> 0 \<le> c \<Longrightarrow> c * a \<le> c * b"
begin
  sublocale oredered_semiring
end

class ordered_cancel_comm_semiring = ordered_comm_semiring + cancel_comm_monoid_add
begin
  sublocale comm_semiring_0_cancel sorry
  sublocale ordered_comm_semiring sorry
  sublocale ordered_cancel_semiring sorry
end

class linordered_comm_semiring_strict = comm_semiring_0 + linordered_cancel_ab_semigroup_add +
  assumes comm_mult_strict_left_mono: "a < b \<Longrightarrow> 0 < c \<Longrightarrow> c * a < c * b"
begin
  sublocale linordered_semiring_strict sorry
  sublocale ordered_cancel_comm_semiring sorry
end

class ordered_ring = ring + ordered_cancel_semiring
begin
  sublocale ordered_ab_group_add sorry
end

class linordered_ring = ring + linordered_semiring + linordered_ab_group_add + abs_if
begin
  sublocale ordered_ring sorry
  sublocale ordered_ab_group_add_abs sorry
end

(* The "strict" suffix can be seen as describing the combination of linordered_ring and no_zero_divisors.
   Basically, linordered_ring + no_zero_divisors = linordered_ring_strict.
 *)
class linordered_ring_strict = ring + linordered_semiring_strict
  + ordered_ab_group_add + abs_if
begin
  sublocale linordered_ring sorry
  sublocale ring_no_zero_divisors sorry
end

class ordered_comm_ring = comm_ring + ordered_comm_semiring
begin
  sublocale ordered_ring sorry
  sublocale ordered_cancel_comm_semiring sorry
end

class linordered_semidom = comm_semiring_1_cancel + linordered_comm_semiring_strict +
  (*previously linordered_semiring*)
  assumes zero_less_one [simp]: "0 < 1"

class linordered_idom = comm_ring_1 +
  linordered_comm_semiring_strict + ordered_ab_group_add +
  abs_if + sgn_if
  (*previously linordered_ring*)
begin
  sublocale linordered_semiring_1_strict sorry
  sublocale linordered_ring_strict sorry
  sublocale ordered_comm_ring sorry
  sublocale idom sorry
  sublocale linordered_semidom sorry
end

class ordered_ring_abs = ordered_ring + ordered_ab_group_add_abs +
  assumes abs_eq_mult:
    "(0 \<le> a \<or> a \<le> 0) \<and> (0 \<le> b \<or> b \<le> 0) \<Longrightarrow> \<bar>a * b\<bar> = \<bar>a\<bar> * \<bar>b\<bar>"

sublocale ordered_ring_abs < linordered_idom sorry

(* Fields *)

subsection {* Ordered fields *}

class linordered_field = field + linordered_idom

class linordered_field_inverse_zero = linordered_field + field_inverse_zero


locale SmoothWorld =
(*
- (- a) = a
- 0 = 0

0 + a = a
a - b \<equiv> a + (- b)
a - a = 0
a + b = b + a
a + (b + c) = (a + b) + c

if a \<noteq> 0, then can obtain a^-1
@TODO sexy inverse syntax

a / b = a * b^-1

0 * a = 0
1 * a = a
a * b = b * a
a*(b*c) = (a*b)*c

a * (b + c) = a*b + a*c

a \<noteq> 0 \<longrightarrow> a/a = 1 ( i.e., a * a^-1 = 1 )

*)

class ordered_ab_group_add =
  ab_group_add + ordered_ab_semigroup_add
begin

subclass ordered_cancel_ab_semigroup_add ..

subclass ordered_ab_semigroup_add_imp_le
proof
  fix a b c :: 'a
  assume "c + a \<le> c + b"
  hence "(-c) + (c + a) \<le> (-c) + (c + b)" by (rule add_left_mono)
  hence "((-c) + c) + a \<le> ((-c) + c) + b" by (simp only: add_assoc)
  thus "a \<le> b" by simp
qed

subclass ordered_comm_monoid_add ..

end

class ab_group_add = minus + uminus + comm_monoid_add +
  assumes ab_left_minus: "- a + a = 0"
  assumes ab_diff_minus: "a - b = a + (- b)"
begin

subclass group_add
  proof qed (simp_all add: ab_left_minus ab_diff_minus)

subclass cancel_comm_monoid_add
proof
  fix a b c :: 'a
  assume "a + b = a + c"
  then have "- a + a + b = - a + a + c"
    unfolding add_assoc by simp
  then show "b = c" by simp
qed

locale ab_semigroup_mult = semigroup_mult +
  assumes mult_commute: "a * b = b * a"

sublocale ab_semigroup_mult < mult!: abel_semigroup times
  by default (fact mult_commute)









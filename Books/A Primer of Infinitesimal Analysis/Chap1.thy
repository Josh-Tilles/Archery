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
  fixes uminus :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" ("- _" [81] 80)

locale times =
  fixes times :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" (infixl "*" 70)

locale semigroup_add = plus +
  assumes add_assoc: "(a + b) + c = a + (b + c)"

sublocale semigroup_add < add!: semigroup plus
  by default (fact add_assoc)

locale ab_semigroup_add = semigroup_add +
  assumes add_commute: "a + b = b + a"

sublocale ab_semigroup_add < add!: abel_semigroup plus
  by default (fact add_commute)

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

locale semigroup_mult = times +
  assumes mult_assoc: "(a * b) * c = a * (b * c)"

sublocale semigroup_mult < mult!: semigroup times
  by default (fact mult_assoc)


locale monoid_mult = one + semigroup_mult +
  assumes mult_1_left: "1 * a  = a"
    and mult_1_right: "a * 1 = a"

sublocale monoid_mult < mult!: monoid times 1
  by default (fact mult_1_left mult_1_right)+

lemma (in monoid) one_reorient: "1 = x \<longleftrightarrow> x = 1"
by (rule eq_commute)

locale ab_semigroup_mult = semigroup_mult +
  assumes mult_commute: "a * b = b * a"

sublocale ab_semigroup_mult < mult!: abel_semigroup times
  by default (fact mult_commute)

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

class ab_group_add = minus + uminus + comm_monoid_add +
  assumes ab_left_minus: "- a + a = 0"
  assumes ab_diff_minus: "a - b = a + (- b)"

class ordered_ab_semigroup_add = order + ab_semigroup_add +
  assumes add_left_mono: "a \<le> b \<Longrightarrow> c + a \<le> c + b"

class ordered_cancel_ab_semigroup_add =
  ordered_ab_semigroup_add + cancel_ab_semigroup_add

class ordered_ab_semigroup_add_imp_le =
  ordered_cancel_ab_semigroup_add +
  assumes add_le_imp_le_left: "c + a \<le> c + b \<Longrightarrow> a \<le> b"

class ordered_cancel_comm_monoid_diff = comm_monoid_diff + ordered_ab_semigroup_add_imp_le +
  assumes le_iff_add: "a \<le> b \<longleftrightarrow> (\<exists>c. b = a + c)"

subsection {* Support for reasoning about signs *}

class ordered_comm_monoid_add =
  ordered_cancel_ab_semigroup_add + comm_monoid_add

class ordered_ab_group_add =
  ab_group_add + ordered_ab_semigroup_add

class linordered_ab_semigroup_add =
  linorder + ordered_ab_semigroup_add

class linordered_cancel_ab_semigroup_add =
  linorder + ordered_cancel_ab_semigroup_add

class linordered_ab_group_add = linorder + ordered_ab_group_add

class abs =
  fixes abs :: "'a \<Rightarrow> 'a"
begin

notation (xsymbols)
  abs  ("\<bar>_\<bar>")

notation (HTML output)
  abs  ("\<bar>_\<bar>")

end

class sgn =
  fixes sgn :: "'a \<Rightarrow> 'a"

class abs_if = minus + uminus + ord + zero + abs +
  assumes abs_if: "\<bar>a\<bar> = (if a < 0 then - a else a)"

class sgn_if = minus + uminus + zero + one + ord + sgn +
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

(* Rings *)
class semiring = ab_semigroup_add + semigroup_mult +
  assumes distrib_right[algebra_simps, field_simps]: "(a + b) * c = a * c + b * c"
  assumes distrib_left[algebra_simps, field_simps]: "a * (b + c) = a * b + a * c"

class mult_zero = times + zero +
  assumes mult_zero_left [simp]: "0 * a = 0"
  assumes mult_zero_right [simp]: "a * 0 = 0"

class semiring_0 = semiring + comm_monoid_add + mult_zero

class semiring_0_cancel = semiring + cancel_comm_monoid_add

class comm_semiring = ab_semigroup_add + ab_semigroup_mult +
  assumes distrib: "(a + b) * c = a * c + b * c"

class comm_semiring_0 = comm_semiring + comm_monoid_add + mult_zero

class comm_semiring_0_cancel = comm_semiring + cancel_comm_monoid_add

class zero_neq_one = zero + one +
  assumes zero_neq_one [simp]: "0 \<noteq> 1"

class semiring_1 = zero_neq_one + semiring_0 + monoid_mult

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





subsection {* Generic operations *}

class zero = 
  fixes zero :: 'a  ("0")

class one =
  fixes one  :: 'a  ("1")

class plus =
  fixes plus :: "'a \<Rightarrow> 'a \<Rightarrow> 'a"  (infixl "+" 65)

class minus =
  fixes minus :: "'a \<Rightarrow> 'a \<Rightarrow> 'a"  (infixl "-" 65)

class uminus =
  fixes uminus :: "'a \<Rightarrow> 'a"  ("- _" [81] 80)

class times =
  fixes times :: "'a \<Rightarrow> 'a \<Rightarrow> 'a"  (infixl "*" 70)

subsection {* Semigroups and Monoids *}

class semigroup_add = plus +
  assumes add_assoc: "(a + b) + c = a + (b + c)"

sublocale semigroup_add < add!: semigroup plus
  by default (fact add_assoc)

class ab_semigroup_add = semigroup_add +
  assumes add_commute: "a + b = b + a"

sublocale ab_semigroup_add < add!: abel_semigroup plus
  by default (fact add_commute)

class monoid_add = zero + semigroup_add +
  assumes add_0_left: "0 + a = a"
    and add_0_right: "a + 0 = a"

sublocale monoid_add < add!: monoid plus 0
  by default (fact add_0_left add_0_right)+

lemma zero_reorient: "0 = x \<longleftrightarrow> x = 0"
by (rule eq_commute)

class comm_monoid_add = zero + ab_semigroup_add +
  assumes add_0: "0 + a = a"

sublocale comm_monoid_add < add!: comm_monoid plus 0
  by default (insert add_0, simp add: ac_simps)

subclass (in comm_monoid_add) monoid_add
  by default (fact add.left_neutral add.right_neutral)+

class comm_monoid_diff = comm_monoid_add + minus +
  assumes diff_zero [simp]: "a - 0 = a"
    and zero_diff [simp]: "0 - a = 0"
    and add_diff_cancel_left [simp]: "(c + a) - (c + b) = a - b"
    and diff_diff_add: "a - b - c = a - (b + c)"

class monoid_mult = one + semigroup_mult +
  assumes mult_1_left: "1 * a  = a"
    and mult_1_right: "a * 1 = a"

sublocale monoid_mult < mult!: monoid times 1
  by default (fact mult_1_left mult_1_right)+

lemma one_reorient: "1 = x \<longleftrightarrow> x = 1"
by (rule eq_commute)

class comm_monoid_mult = one + ab_semigroup_mult +
  assumes mult_1: "1 * a = a"

sublocale comm_monoid_mult < mult!: comm_monoid times 1
  by default (insert mult_1, simp add: ac_simps)

subclass (in comm_monoid_mult) monoid_mult
  by default (fact mult.left_neutral mult.right_neutral)+

class cancel_semigroup_add = semigroup_add +
  assumes add_left_imp_eq: "a + b = a + c \<Longrightarrow> b = c"
  assumes add_right_imp_eq: "b + a = c + a \<Longrightarrow> b = c"

class cancel_ab_semigroup_add = ab_semigroup_add +
  assumes add_imp_eq: "a + b = a + c \<Longrightarrow> b = c"
begin

subclass cancel_semigroup_add
proof
  fix a b c :: 'a
  assume "a + b = a + c" 
  then show "b = c" by (rule add_imp_eq)
next
  fix a b c :: 'a
  assume "b + a = c + a"
  then have "a + b = a + c" by (simp only: add_commute)
  then show "b = c" by (rule add_imp_eq)
qed

end

class cancel_comm_monoid_add = cancel_ab_semigroup_add + comm_monoid_add

class group_add = minus + uminus + monoid_add +
  assumes left_minus [simp]: "- a + a = 0"
  assumes diff_minus: "a - b = a + (- b)"

class ab_group_add = minus + uminus + comm_monoid_add +
  assumes ab_left_minus: "- a + a = 0"
  assumes ab_diff_minus: "a - b = a + (- b)"

class ordered_ab_semigroup_add = order + ab_semigroup_add +
  assumes add_left_mono: "a \<le> b \<Longrightarrow> c + a \<le> c + b"

class ordered_cancel_ab_semigroup_add =
  ordered_ab_semigroup_add + cancel_ab_semigroup_add

class ordered_ab_semigroup_add_imp_le =
  ordered_cancel_ab_semigroup_add +
  assumes add_le_imp_le_left: "c + a \<le> c + b \<Longrightarrow> a \<le> b"

class ordered_cancel_comm_monoid_diff = comm_monoid_diff + ordered_ab_semigroup_add_imp_le +
  assumes le_iff_add: "a \<le> b \<longleftrightarrow> (\<exists>c. b = a + c)"

subsection {* Support for reasoning about signs *}

class ordered_comm_monoid_add =
  ordered_cancel_ab_semigroup_add + comm_monoid_add

class ordered_ab_group_add =
  ab_group_add + ordered_ab_semigroup_add

class linordered_ab_semigroup_add =
  linorder + ordered_ab_semigroup_add

class linordered_cancel_ab_semigroup_add =
  linorder + ordered_cancel_ab_semigroup_add

class linordered_ab_group_add = linorder + ordered_ab_group_add

class abs =
  fixes abs :: "'a \<Rightarrow> 'a"
begin

notation (xsymbols)
  abs  ("\<bar>_\<bar>")

notation (HTML output)
  abs  ("\<bar>_\<bar>")

end

class sgn =
  fixes sgn :: "'a \<Rightarrow> 'a"

class abs_if = minus + uminus + ord + zero + abs +
  assumes abs_if: "\<bar>a\<bar> = (if a < 0 then - a else a)"

class sgn_if = minus + uminus + zero + one + ord + sgn +
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

class linordered_ab_semigroup_add =
  linorder + ordered_ab_semigroup_add

class linordered_cancel_ab_semigroup_add =
  linorder + ordered_cancel_ab_semigroup_add
begin

subclass linordered_ab_semigroup_add ..

subclass ordered_ab_semigroup_add_imp_le
proof
  fix a b c :: 'a
  assume le: "c + a <= c + b"  
  show "a <= b"
  proof (rule ccontr)
    assume w: "~ a \<le> b"
    hence "b <= a" by (simp add: linorder_not_le)
    hence le2: "c + b <= c + a" by (rule add_left_mono)
    have "a = b" 
      apply (insert le)
      apply (insert le2)
      apply (drule antisym, simp_all)
      done
    with w show False 
      by (simp add: linorder_not_le [symmetric])
  qed
qed

end

class linordered_ab_group_add = linorder + ordered_ab_group_add
begin

subclass linordered_cancel_ab_semigroup_add ..

(* Rings *)
class semiring = ab_semigroup_add + semigroup_mult +
  assumes distrib_right[algebra_simps, field_simps]: "(a + b) * c = a * c + b * c"
  assumes distrib_left[algebra_simps, field_simps]: "a * (b + c) = a * b + a * c"

class mult_zero = times + zero +
  assumes mult_zero_left [simp]: "0 * a = 0"
  assumes mult_zero_right [simp]: "a * 0 = 0"

class semiring_0 = semiring + comm_monoid_add + mult_zero

class semiring_0_cancel = semiring + cancel_comm_monoid_add

class comm_semiring = ab_semigroup_add + ab_semigroup_mult +
  assumes distrib: "(a + b) * c = a * c + b * c"

class comm_semiring_0 = comm_semiring + comm_monoid_add + mult_zero

class comm_semiring_0_cancel = comm_semiring + cancel_comm_monoid_add

class zero_neq_one = zero + one +
  assumes zero_neq_one [simp]: "0 \<noteq> 1"

class semiring_1 = zero_neq_one + semiring_0 + monoid_mult

text {* Abstract divisibility *}

class dvd = times
begin

definition dvd :: "'a \<Rightarrow> 'a \<Rightarrow> bool" (infix "dvd" 50) where
  "b dvd a \<longleftrightarrow> (\<exists>k. a = b * k)"

lemma dvdI [intro?]: "a = b * k \<Longrightarrow> b dvd a"
  unfolding dvd_def ..

lemma dvdE [elim?]: "b dvd a \<Longrightarrow> (\<And>k. a = b * k \<Longrightarrow> P) \<Longrightarrow> P"
  unfolding dvd_def by blast 

end

class comm_semiring_1 = zero_neq_one + comm_semiring_0 + comm_monoid_mult + dvd
  (*previously almost_semiring*)

class no_zero_divisors = zero + times +
  assumes no_zero_divisors: "a \<noteq> 0 \<Longrightarrow> b \<noteq> 0 \<Longrightarrow> a * b \<noteq> 0"

class semiring_1_cancel = semiring + cancel_comm_monoid_add
  + zero_neq_one + monoid_mult

class comm_semiring_1_cancel = comm_semiring + cancel_comm_monoid_add
  + zero_neq_one + comm_monoid_mult

class ring = semiring + ab_group_add

class comm_ring = comm_semiring + ab_group_add

class ring_1 = ring + zero_neq_one + monoid_mult

class comm_ring_1 = comm_ring + zero_neq_one + comm_monoid_mult
  (*previously ring*)

class ring_no_zero_divisors = ring + no_zero_divisors

class ring_1_no_zero_divisors = ring_1 + ring_no_zero_divisors

class idom = comm_ring_1 + no_zero_divisors

class ordered_semiring = semiring + comm_monoid_add + ordered_ab_semigroup_add +
  assumes mult_left_mono: "a \<le> b \<Longrightarrow> 0 \<le> c \<Longrightarrow> c * a \<le> c * b"
  assumes mult_right_mono: "a \<le> b \<Longrightarrow> 0 \<le> c \<Longrightarrow> a * c \<le> b * c"

class ordered_cancel_semiring = ordered_semiring + cancel_comm_monoid_add

class linordered_semiring = ordered_semiring + linordered_cancel_ab_semigroup_add

class linordered_semiring_1 = linordered_semiring + semiring_1

class linordered_semiring_strict = semiring + comm_monoid_add + linordered_cancel_ab_semigroup_add +
  assumes mult_strict_left_mono: "a < b \<Longrightarrow> 0 < c \<Longrightarrow> c * a < c * b"
  assumes mult_strict_right_mono: "a < b \<Longrightarrow> 0 < c \<Longrightarrow> a * c < b * c"

class linordered_semiring_1_strict = linordered_semiring_strict + semiring_1

class ordered_comm_semiring = comm_semiring_0 + ordered_ab_semigroup_add + 
  assumes comm_mult_left_mono: "a \<le> b \<Longrightarrow> 0 \<le> c \<Longrightarrow> c * a \<le> c * b"

class ordered_cancel_comm_semiring = ordered_comm_semiring + cancel_comm_monoid_add

class linordered_comm_semiring_strict = comm_semiring_0 + linordered_cancel_ab_semigroup_add +
  assumes comm_mult_strict_left_mono: "a < b \<Longrightarrow> 0 < c \<Longrightarrow> c * a < c * b"

class ordered_ring = ring + ordered_cancel_semiring 

class linordered_ring = ring + linordered_semiring + linordered_ab_group_add + abs_if

(* The "strict" suffix can be seen as describing the combination of linordered_ring and no_zero_divisors.
   Basically, linordered_ring + no_zero_divisors = linordered_ring_strict.
 *)
class linordered_ring_strict = ring + linordered_semiring_strict
  + ordered_ab_group_add + abs_if

class ordered_comm_ring = comm_ring + ordered_comm_semiring

class linordered_semidom = comm_semiring_1_cancel + linordered_comm_semiring_strict +
  (*previously linordered_semiring*)
  assumes zero_less_one [simp]: "0 < 1"

class linordered_idom = comm_ring_1 +
  linordered_comm_semiring_strict + ordered_ab_group_add +
  abs_if + sgn_if
  (*previously linordered_ring*)

class ordered_ring_abs = ordered_ring + ordered_ab_group_add_abs +
  assumes abs_eq_mult:
    "(0 \<le> a \<or> a \<le> 0) \<and> (0 \<le> b \<or> b \<le> 0) \<Longrightarrow> \<bar>a * b\<bar> = \<bar>a\<bar> * \<bar>b\<bar>"

(* Fields *)
subsection {* Division rings *}

text {*
  A division ring is like a field, but without the commutativity requirement.
*}

class inverse =
  fixes inverse :: "'a \<Rightarrow> 'a"
    and divide :: "'a \<Rightarrow> 'a \<Rightarrow> 'a"  (infixl "'/" 70)

class division_ring = ring_1 + inverse +
  assumes left_inverse [simp]:  "a \<noteq> 0 \<Longrightarrow> inverse a * a = 1"
  assumes right_inverse [simp]: "a \<noteq> 0 \<Longrightarrow> a * inverse a = 1"
  assumes divide_inverse: "a / b = a * inverse b"

class division_ring_inverse_zero = division_ring +
  assumes inverse_zero [simp]: "inverse 0 = 0"

subsection {* Fields *}

class field = comm_ring_1 + inverse +
  assumes field_inverse: "a \<noteq> 0 \<Longrightarrow> inverse a * a = 1"
  assumes field_divide_inverse: "a / b = a * inverse b"

class field_inverse_zero = field +
  assumes field_inverse_zero: "inverse 0 = 0"

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



theory ChapZeroExers
imports Main (* Complex_Main for exercise 1.6 *)
begin

(* @TODO Chap0 I.2.2 *)
(* from Fun.thy *)
lemma the_inv_into_f_f: "\<lbrakk>inj_on f A; x \<in> A\<rbrakk> \<Longrightarrow> the_inv_into A f (f x) = x"
  unfolding the_inv_into_def inj_on_def

  assumes "inj_on f A"
    and "x \<in> A" (* an important part of the proof is that A is non-empty *)
  shows "the_inv_into A f (f x) = x"

find_theorems "card (Pow _)"
thm Finite_Set.card_partition
thm insert_partition
(* rewrite Finite_Set.eq_card_imp_in_on
           Finite_Set.card_inj_on_le
           Fun.the_inv_into_comp
           Fun.the_inv_into_f_eq
           Fun.the_inv_into_into
           Fun.f_the_inv_into_f
           Fun.the_inv_into_f_f
           Fun.fun_upd_idem_iff
           Fun.bij_image_Compl_eq
           Fun.bij_image_INT
           Fun.image_INT
           Fun.inj_on_image_set_diff
           Fun.inj_on_image_Int
           Fun.vimage_subset_eq*)
lemma card_Pow2: "finite A ==> card (Pow A) = 2 ^ card A"
apply (induct rule: finite_induct)
 apply (simp_all add: Pow_insert)
apply (subst card_Un_disjoint, blast)
  apply (blast, blast)
apply (subgoal_tac "inj_on (insert x) (Pow F)")
 apply (subst mult_2)
 apply (simp add: card_image Pow_insert)
apply (unfold inj_on_def)
apply (blast elim!: equalityE)
done
(* "F" for "Family (of sets)". Also, look up to see if there's a way to express disjointness. *)
definition partition_of :: "'a set set \<Rightarrow> 'a set \<Rightarrow> bool" where
  "partition_of F s \<equiv> (\<Union>x\<in>F. x) = s
                      \<and> (\<forall>x1\<in>F. \<forall>x2\<in>F. x1 \<noteq> x2 \<longrightarrow> x1 \<inter> x2 = {})
                      \<and> (\<forall>x\<in>F. x \<noteq> {})" (* @TODO find a nicer way to say "all are non_empty *)
                      
subsubsection "Exercise 1.2"
lemma fixes A :: "'a set"
        and r :: "('a \<times> 'a) set"
      (* assumes "(x,y)\<in>r \<Longrightarrow> x\<in>A"
          and "(x,y)\<in>r \<Longrightarrow> y\<in>A" *)
      shows "partition_of (A // r) A"
oops

subsection "Exercise 1.3"
lemma assumes "partition_of F s"
      shows "\<exists>r. s//r = F"
oops

subsubsection "Exercise 1.4"
lemma "card {er. equiv {1, 2, 3} er} = 3"
  unfolding equiv_def card_def finite_def fold_image_def Finite_Set.fold_def sym_def trans_def refl_on_def insert_def lfp_def fold_graph_def
  apply simp
  oops
value "refl_on ({1, 2, 3} :: nat set) {(1, 1), (2, 2), (3, 3)}"
value "sym {(1, 1), (2, 2), (3, 3)}"
value "trans ({(1, 1), (2, 2), (3, 3)} :: (nat \<times> nat) set)"
  
subsubsection "Exercise 2.3"
lemma assumes "bij f"
      shows "bij (inv f)"
  apply (simp only: bij_def inj_on_def surj_def)
  apply auto
  apply (simp only: inv_def)
  defer
  apply (rule exI)
  apply (unfold inv_def)
   try0
  oops

  
definition epimorphism :: "('a \<Rightarrow> 'b) \<Rightarrow> bool" where
  "epimorphism f \<equiv> \<forall> g h. g \<circ> f = h \<circ> f \<longrightarrow> g = h"
definition monomorphism :: "('a \<Rightarrow> 'b) \<Rightarrow> bool" where
  "monomorphism f \<equiv> \<forall> g h. f \<circ> g = f \<circ> h \<longrightarrow> g = h"
definition isomorphism :: "('a \<Rightarrow> 'b) \<Rightarrow> bool" where
  "isomorphism f \<equiv> \<exists>g. f \<circ> g = id \<and> g \<circ> f = id"
lemma
  assumes "monomorphism TYPE('x) f"
      and "epimorphism TYPE('x) f"
  shows "isomorphism f"
  apply (unfold isomorphism_def)
  oops
  
lemma bij_betw_trans:
  "bij_betw f A B \<Longrightarrow> bij_betw g B C \<Longrightarrow> bij_betw (g o f) A C"
by(auto simp add:bij_betw_def comp_inj_on)

lemma bij_comp: "bij f \<Longrightarrow> bij g \<Longrightarrow> bij (g o f)"
  by (rule bij_betw_trans)

lemma bij_betw_comp_iff:
  "bij_betw f A A' \<Longrightarrow> bij_betw f' A' A'' \<longleftrightarrow> bij_betw (f' o f) A A''"
by(auto simp add: bij_betw_def inj_on_def)

lemma bij_betw_comp_iff2:
  assumes BIJ: "bij_betw f' A' A''" and IM: "f ` A \<le> A'"
  shows "bij_betw f A A' \<longleftrightarrow> bij_betw (f' o f) A A''"
using assms
proof(auto simp add: bij_betw_comp_iff)
  assume *: "bij_betw (f' \<circ> f) A A''"
  thus "bij_betw f A A'"
  using IM
  proof(auto simp add: bij_betw_def)
    assume "inj_on (f' \<circ> f) A"
    thus "inj_on f A" using inj_on_imageI2 by blast
  next
    fix a' assume **: "a' \<in> A'"
    hence "f' a' \<in> A''" using BIJ unfolding bij_betw_def by auto
    then obtain a where 1: "a \<in> A \<and> f'(f a) = f' a'" using *
    unfolding bij_betw_def by force
    hence "f a \<in> A'" using IM by auto
    hence "f a = a'" using BIJ ** 1 unfolding bij_betw_def inj_on_def by auto
    thus "a' \<in> f ` A" using 1 by auto
  qed
qed

lemma bij_betw_inv: assumes "bij_betw f A B" shows "EX g. bij_betw g B A"
proof -
  have i: "inj_on f A" and s: "f ` A = B"
    using assms by(auto simp:bij_betw_def)
  let ?P = "%b a. a:A \<and> f a = b" let ?g = "%b. The (?P b)"
  { fix a b assume P: "?P b a"
    hence ex1: "\<exists>a. ?P b a" using s unfolding image_def by blast
    hence uex1: "\<exists>!a. ?P b a" by(blast dest:inj_onD[OF i])
    hence " ?g b = a" using the1_equality[OF uex1, OF P] P by simp
  } note g = this
  have "inj_on ?g B"
  proof(rule inj_onI)
    fix x y assume "x:B" "y:B" "?g x = ?g y"
    from s `x:B` obtain a1 where a1: "?P x a1" unfolding image_def by blast
    from s `y:B` obtain a2 where a2: "?P y a2" unfolding image_def by blast
    from g[OF a1] a1 g[OF a2] a2 `?g x = ?g y` show "x=y" by simp
  qed
  moreover have "?g ` B = A"
  proof(auto simp:image_def)
    fix b assume "b:B"
    with s obtain a where P: "?P b a" unfolding image_def by blast
    thus "?g b \<in> A" using g[OF P] by auto
  next
    fix a assume "a:A"
    then obtain b where P: "?P b a" using s unfolding image_def by blast
    then have "b:B" using s unfolding image_def by blast
    with g[OF P] show "\<exists>b\<in>B. a = ?g b" by blast
  qed
  ultimately show ?thesis by(auto simp:bij_betw_def)
qed

lemma bij_betw_cong:
  "(\<And> a. a \<in> A \<Longrightarrow> f a = g a) \<Longrightarrow> bij_betw f A A' = bij_betw g A A'"
unfolding bij_betw_def inj_on_def by force

lemma bij_betw_id[intro, simp]:
  "bij_betw id A A"
unfolding bij_betw_def id_def by auto

subsubsection "Exercise 2.10"
lemma
  assumes "finite A"
      and "finite B"
  shows "card {r . r \<subseteq> A\<times>B \<and> single_valued r} = (card B ^ card A)"

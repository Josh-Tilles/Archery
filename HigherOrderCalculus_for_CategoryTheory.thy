theory HigherOrderCalculus_for_CategoryTheory
imports Pure
begin

subsection {* Pure Logic *}

class type
default_sort type

typedecl o
instance o :: type ..
instance "fun" :: (type, type) type ..


subsubsection {* Basic logical connectives *}

judgment
  Trueprop :: "o \<Rightarrow> prop"    ("_" 5)

axiomatization
  imp :: "o \<Rightarrow> o \<Rightarrow> o"    (infixr "\<longrightarrow>" 25) and
  All :: "('a \<Rightarrow> o) \<Rightarrow> o"    (binder "\<forall>" 10)
where
  impI [intro]: "(A \<Longrightarrow> B) \<Longrightarrow> A \<longrightarrow> B" and
  impE [dest, trans]: "A \<longrightarrow> B \<Longrightarrow> A \<Longrightarrow> B" and
  allI [intro]: "(\<And>x. P x) \<Longrightarrow> \<forall>x. P x" and
  allE [dest]: "\<forall>x. P x \<Longrightarrow> P a"

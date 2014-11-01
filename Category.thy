theory Category
imports "~~/src/HOL/Library/FuncSet"
begin

(* Records are defined surprisingly late in HOL. Would it be possible to define categories using more-foundational Isabelle mechanisms? *)
locale category' =
  fixes obj :: "'o set"
    and mor :: "'m set"
    and src :: "'m \<Rightarrow> 'o"
    and trg :: "'m \<Rightarrow> 'o"
    and id  :: "'o \<Rightarrow> 'm"
    and composition :: "'m \<Rightarrow> 'm \<Rightarrow> 'm" (* (infixl ";;" 70) *) (* @TODO safe to keep around? *)
  assumes src_object: "f \<in> mor \<Longrightarrow> src f \<in> obj"
      and trg_object: "f \<in> mor \<Longrightarrow> trg f \<in> obj"
  (* etc. *)

(* (choosing lower-case record-name to match the conventions of the rest of the Isabelle codebase) *)
record ('o, 'm) category =
  Obj  :: "'o set" ("obj\<index>" 70)
  Mor  :: "'m set" ("mor\<index>" 70)
  Dom  :: "'m \<Rightarrow> 'o" ("dom\<index> _" [80] 70)
  Cod  :: "'m \<Rightarrow> 'o" ("cod\<index> _" [80] 70)
  Id   :: "'o \<Rightarrow> 'm" ("id\<index> _"  [80] 75)
  Comp :: "'m \<Rightarrow> 'm \<Rightarrow> 'm" (infixl ";;\<index>" 70)

(* Keep Greg O'Keefe's composition-notation around as an option. *)
notation
  category.Comp (infixl "\<bullet>\<index>" 60)

definition
  MapsTo :: "('o, 'm, 'a) category_scheme \<Rightarrow> 'm \<Rightarrow> 'o \<Rightarrow> 'o \<Rightarrow> bool" ("_ maps\<index> _ to _" [60, 60, 60] 65) where
  "f maps\<^bsub>\<C>\<^esub> X to Y \<longleftrightarrow> f \<in> mor\<^bsub>\<C>\<^esub> \<and> dom\<^bsub>\<C>\<^esub> f = X \<and> cod\<^bsub>\<C>\<^esub> f = Y"

inductive MapsTo' :: "('o, 'm, 'a) category_scheme \<Rightarrow> 'm \<Rightarrow> 'o \<Rightarrow> 'o \<Rightarrow> bool" (* ("_ maps\<index> _ to _" [60, 60, 60] 65) *) where
  "\<lbrakk>f \<in> mor\<^bsub>\<C>\<^esub>; dom\<^bsub>C\<^esub> f = X; cod\<^bsub>\<C>\<^esub> f = Y\<rbrakk> \<Longrightarrow> MapsTo' \<C> f X Y"

(* @TODO create a shortcut for <bsub> and <esub> (cf. C-e up and C-e down) *)
definition
  CompDefined :: "('o, 'm, 'a) category_scheme \<Rightarrow> 'm \<Rightarrow> 'm \<Rightarrow> bool" (infixl "\<approx>>\<index>" 65) where
  "f \<approx>>\<^bsub>\<C>\<^esub> g \<longleftrightarrow> f \<in> mor\<^bsub>\<C>\<^esub> \<and> g \<in> mor\<^bsub>\<C>\<^esub> \<and> cod\<^bsub>\<C>\<^esub> f = dom\<^bsub>\<C>\<^esub> g"

inductive CompDefined' :: "('o, 'm, 'a) category_scheme \<Rightarrow> 'm \<Rightarrow> 'm \<Rightarrow> bool" (*  (infixl "\<approx>>\<index>" 65) *) where
  "\<lbrakk>f \<in> mor\<^bsub>\<C>\<^esub>; g \<in> mor\<^bsub>\<C>\<^esub>; cod\<^bsub>\<C>\<^esub> f = dom\<^bsub>\<C>\<^esub> g\<rbrakk> \<Longrightarrow> CompDefined' \<C> f g"

locale category =
  fixes \<C> :: "('o, 'm, 'a) category_scheme" (structure)
  assumes dom_object: "f \<in> mor \<Longrightarrow> dom f \<in> obj"
      and cod_object: "f \<in> mor \<Longrightarrow> cod f \<in> obj"
      and id_mor:     "X \<in> obj \<Longrightarrow> (id X) maps X to X"
(*    and id_left:    "f maps X to Y \<Longrightarrow> id X ;; f = f" *)
      and id_left:    "f \<in> mor \<Longrightarrow> id (dom f) ;; f = f"
(*    and id_right:   "f maps X to Y \<Longrightarrow> f ;; id Y = f" *)
      and id_right:   "f \<in> mor \<Longrightarrow> f ;; id (cod f) = f"
      and comp_types: "\<lbrakk>f maps X to Y; g maps Y to Z\<rbrakk> \<Longrightarrow> (f ;; g) maps X to Z"
(*     and comp_types': "f \<approx>> g \<Longrightarrow> (f ;; g) maps (dom f) to (cod g)" *)
      and comp_associative:
        "\<lbrakk>f \<approx>> g; g \<approx>> h\<rbrakk> \<Longrightarrow> (f ;; g) ;; h = f ;; (g ;; h)"
(*    and comp_associative: "associative category.Comp" *)

(*
declare category.dom_object[intro]
declare category.cod_object[intro]
declare category.id_mor[dest]
declare category.id_left[simp]
declare category.id_right[simp]
declare category.comp_types[intro]
declare category.comp_associative[simp]
*)

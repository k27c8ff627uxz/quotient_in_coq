Require Import Coq.Relations.Relation_Definitions.
Require Export Coq.Classes.SetoidClass.
Require Import Coq.Classes.Equivalence.

Open Scope equiv_scope.

Definition f_comp {A B C : Type} (f : B -> C) (g : A -> B) : A -> C := fun a => f (g a).
Definition mono {A B : Type} (f : A -> B) := forall (X : Type) (u1 u2 : X -> A), f_comp f u1 === f_comp f u2 -> u1 === u2.
Definition epi {A B : Type} (f : A -> B) := forall (X : Type) (u1 u2 : B -> X), f_comp u1 f === f_comp u2 f -> u1 === u2.

Polymorphic Record quotient@{i j} (A : Type@{i}) (setoid : Setoid A) :=
  {
    q_type :  Type@{i};
    q_proj : A -> q_type;

    (* conditions *)
    quotient_comp : forall (x y : A), x === y -> q_proj x = q_proj y;
    quotient_proj_epi : epi q_proj;
    quotient_factor : forall {B : Type@{j}} (f : A -> B), Proper ( (fun a b => a === b) ==> (fun a b => a = b) ) f -> { f' : q_type -> B | f === f_comp f' q_proj }

  }.

Polymorphic Definition quotient_exists := forall (A : Type) (setoid : Setoid A), quotient A setoid.

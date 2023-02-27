Require Import Coq.Relations.Relation_Definitions.
Require Export Coq.Classes.SetoidClass.
Require Import Coq.Classes.Equivalence.

Require Import Quotient.function_util.

Open Scope equiv_scope.

Record quotient@{i j} (A : Type@{i}) (setoid : Setoid A) :=
  {
    q_type :  Type@{i};
    q_proj : A -> q_type;

    (* conditions *)
    quotient_comp : forall (x y : A), x === y -> q_proj x = q_proj y;
    quotient_proj_epi : epi q_proj;
    quotient_factor : forall {B : Type@{j}} (f : A -> B), Proper ( (fun a b => a === b) ==> (fun a b => a = b) ) f -> { f' : q_type -> B | f === f_comp f' q_proj }

  }.

Definition quotient_exists := forall (A : Type) (setoid : Setoid A), quotient A setoid.

Require Export UniMath.Foundations.All.


Definition apD {X:Type} {Y : X -> Type} (s : ∏ x, Y x) {x x':X} (p : x = x') :
  transportf Y p (s x) = s x'.
Proof.
  now induction p.
Defined.

Inductive Two : Set :=
  | On : Two
  | Tw : Two.

Module Export Suspension.

Private Inductive Suspension (A : Type) : Set :=
  | North : Suspension A
  | South : Suspension A.


Axiom merid : forall {A : Type} (x : A), North A = South A.

Definition Suspension_ind {A : Type} (P : Suspension A -> Type) (n : P (North A)) (s : P (South A)) (m : forall x, transportf P (merid x) n = s)
  : forall x : Suspension A, P x :=
  fun x =>
    match x with
    | North _ => n
    | South _ => s
    end.

Axiom Suspension_ind_merid : forall {A : Type} {x : A} (P : Suspension A -> Type) (n : P (North A)) (s : P (South A)) (m : forall x, transportf P (merid x) n = s),
  apD (Suspension_ind P n s m) (merid x) = m x.

Definition Suspension_recur {A : Type} (P : Type) (n : P) (s : P) (m : A -> n = s) : Suspension A -> P :=
  fun x =>
    match x with
    | North _ => n
    | South _ => s
    end.

Axiom Suspension_recur_merid : forall {A : Type} {x : A} (P : Type) (n : P) (s : P) (p : A -> n = s),
  maponpaths (Suspension_recur P n s p) (merid x) = p x.

End Suspension.


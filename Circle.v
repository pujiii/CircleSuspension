Require Export UniMath.Foundations.All.

Definition apD {X:Type} {Y : X -> Type} (s : ∏ x, Y x) {x x':X} (p : x = x') :
  transportf Y p (s x) = s x'.
Proof.
  now induction p.
Defined.

Module Export S1.

Private Inductive S1 : Set :=
  | base : S1.

Axiom loop : base = base.

Definition S1_ind (P : S1 -> Type) (b : P base) (l : transportf P loop b = b)
  : forall x : S1, P x :=
  fun x =>
    match x with
    | base => b
    end.

Axiom S1_ind_loop : forall (P : S1 -> Type) (b : P base) (l : transportf P loop b = b),
  apD (S1_ind P b l) loop = l.

Definition S1_recur (A : Type) (a : A) (l : a = a) : S1 -> A :=
  fun x =>
    match x with
    | base => a
    end.

Axiom S1_recur_loop : forall (A : Type) (a : A) (l : a = a) ,
  maponpaths (S1_recur A a l) loop = l.

End S1.

Module Export S1'.

Private Inductive S1' : Set :=
  | north_pole : S1'
  | south_pole : S1'.

Axiom p1 : north_pole = south_pole.
Axiom p2 : south_pole = north_pole.

Definition S1'_ind (P : S1' -> Type) (n : P north_pole) (s : P south_pole) (p1' : transportf P p1 n = s) (p2' : transportf P p2 s = n)
  : forall x : S1', P x :=
  fun x =>
    match x with
    | north_pole => n
    | south_pole => s
    end.

Axiom S1'_ind_p1 : forall (P : S1' -> Type) (n : P north_pole) (s : P south_pole) (p1' : transportf P p1 n = s) (p2' : transportf P p2 s = n),
  apD (S1'_ind P n s p1' p2') p1 = p1'.

Axiom S1'_ind_p2 : forall (P : S1' -> Type) (n : P north_pole) (s : P south_pole) (p1' : transportf P p1 n = s) (p2' : transportf P p2 s = n),
  apD (S1'_ind P n s p1' p2') p2 = p2'.

Definition S1'_recur (A : Type) (n : A) (s : A) (p1' : n = s) (p2' : s = n ) : S1' -> A :=
  fun x =>
    match x with
    | north_pole => n
    | south_pole => s
    end.

Axiom S1'_recur_p1 : forall (A : Type) (n : A) (s : A) (p1' : n = s) (p2' : s = n) ,
  maponpaths (S1'_recur A n s p1' p2') p1 = p1'.

Axiom S1'_recur_p2 : forall (A : Type) (n : A) (s : A) (p1' : n = s) (p2' : s = n) ,
  maponpaths (S1'_recur A n s p1' p2') p2 = p2'.

End S1'.

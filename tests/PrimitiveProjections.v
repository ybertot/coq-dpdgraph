Set Primitive Projections.
Set Implicit Arguments.

Record sigT {A} (P : A -> Type) := existT { projT1 : A ; projT2 : P projT1 }.

Definition bar := @projT1.
Definition baz A P (x : @sigT A P) := projT1 x.

Definition foo (A: Type) (B: A -> Type) (C: A -> Type)
   (c: sigT (A := A) (fun x : A => sigT (A := B x) (fun _ =>  C x))) :
   sigT (A := A) (fun x : A => sigT (A := C x) (fun _ => B x)).
Proof.
  exists (projT1 c).
  exists (projT2 (projT2 c)).
  destruct c as [a [b c]].
  exact b.
Defined.

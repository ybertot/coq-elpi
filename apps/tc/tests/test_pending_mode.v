From elpi Require Import tc.

Module m1.
  Elpi TC.Pending_mode +.
  Class C (i : nat).
  Instance C0 : C 0. Qed.
  Goal exists x, C x. eexists. Fail apply _. Abort.
  Class C' (i : nat).
  Instance C0' : C' 0. Qed.
  Goal exists x, C' x. eexists. apply _. Abort.

  Elpi TC.Pending_mode +.
  Fail Elpi TC.Pending_mode +.

  Class C'' (i : nat).
  Instance C0'' : C'' 0. Qed.
  Goal exists x, C'' x. eexists. Fail apply _. Abort.
End m1.

Module ground.
  Elpi TC.Pending_mode +.
  Class C (i : Type).
  Instance i : C (list nat). Qed.

  Goal exists (x : Type), C (list x). 
    eexists. 
    Fail apply _.
  Abort.
End ground.

Module ground1.
  Elpi TC.Pending_mode +.
  Class C (i : Type).
  Instance i x: C x. Qed.

  Goal exists (x : Type), C (list x). 
    eexists.
    apply _.
  Abort.
End ground1.

Module ground2.
  Elpi TC.Pending_mode +.
  Class C (i : Type).
  Instance i (x: Type): C (list x). Qed.

  Goal exists (x : Type), C (list x). 
    eexists. 
    apply _.
  Abort.
End ground2.

Module ground3.
  Elpi TC.Pending_mode + +.
  Class C {i : Type} (f : i -> i -> Prop).
  Instance i {X : Type}: C (@eq X). Qed.
  Hint Mode C ! ! : typeclass_instances.

  Goal exists (X : Type), C (@eq X). 
    eexists.
    Fail apply _.
  Abort.
End ground3.

Module ground4.
  Elpi TC.Pending_mode - +.
  Class C {i : Type} (f : i -> i -> Prop).
  Instance i {X : Type}: C (@eq X). Qed.
  Hint Mode C ! ! : typeclass_instances.

  Goal exists (X : Type), @C (list X) eq. 
    eexists.
     apply _.
  Abort.
End ground4.

Module rigid_head1.
  Elpi TC.Pending_mode !.
  Class C (i : Type).
  Instance i: C (list nat). Qed.
  Hint Mode C ! : typeclass_instances.

  Goal exists (x : Type), C (list x). 
    eexists.
    apply _.
  Qed.

  Goal exists (x : Type), C x. 
    eexists.
    Fail apply _.
  Abort.
End rigid_head1.

Module rigid_head2.
  Elpi TC.Pending_mode ! !.
  Class C {i : Type} (f : i -> i -> Prop).
  Instance i {X : Type}: C (@eq X). Qed.
  Hint Mode C ! ! : typeclass_instances.

  Goal exists (X : Type), C (@eq X). 
    eexists.
    Fail apply _.
  Abort.
End rigid_head2.
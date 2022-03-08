From Coq Require Import ssreflect ssrfun ssrbool Eqdep_dec.
From elpi Require Import elpi.
From elpi.apps.derive Require Import induction param1_functor param1_trivial eqb_core_defs tag fields eqb.

Export ssreflect ssrbool eqb_core_defs. (* go ask the ltac gurus... *)
Ltac do_one_arg x :=
  let t := type of x in
  match reverse goal with 
  | View : @eqb_correct_on _ _ _ |- _ =>
      move=> /=/View{View} ?;
      subst x
  | x' : t |- Datatypes.is_true true -> _ =>
      move=> _;
      rewrite (@Eqdep_dec.UIP_dec bool Bool.bool_dec _ _ x x')
  end.

Ltac eqb_correct_on__solver :=
  by match goal with
  | f : _ |- _ => move: f
  end;
  repeat (
    let f := fresh "f" in
    let x := fresh "x" in
    move=> f;
    ((case/andP; case: f => x f; do_one_arg x; move: f)
    || (do_one_arg f))).

Ltac eqb_refl_on__solver :=
  by rewrite /eqb_fields_refl_on /=;
  repeat ((apply /andP; split) || reflexivity || assumption).
      
Elpi Command derive.eqbcorrect.
Elpi Accumulate Db derive.tag.db.
Elpi Accumulate Db derive.eqb.db.
Elpi Accumulate Db derive.fields.db.
Elpi Accumulate Db derive.eqbcorrect.db.
Elpi Accumulate Db derive.induction.db.
Elpi Accumulate Db derive.param1.trivial.db.
Elpi Accumulate Db derive.param1.functor.db. 
Elpi Accumulate File "eqbcorrect.elpi" From elpi.apps.derive.
Elpi Accumulate File "paramX-lib.elpi" From elpi.apps.derive. 
Elpi Accumulate File "param1.elpi" From elpi.apps.derive.
Elpi Accumulate Db derive.param1.db.

Elpi Accumulate lp:{{
  main [str I, str O] :- !, 
    coq.locate I (indt GR), 
    Prefix is O ^ "_",
    derive.eqbcorrect.main GR Prefix _.

  main [str I] :- !, 
    coq.locate I (indt GR),
    coq.gref->id (indt GR) Tname,
    Prefix is Tname ^ "_",
    derive.eqbcorrect.main GR Prefix _.

  main _ :- usage.
   
  usage :- coq.error "Usage: derive.eqbcorrect <inductive name> [<prefix>]".

}}.
Elpi Typecheck.

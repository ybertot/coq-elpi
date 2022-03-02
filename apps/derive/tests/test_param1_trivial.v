From elpi.apps Require Import derive.param1_trivial.

From elpi.apps Require Import test_derive_stdlib test_param1 test_param1_congr.
Import test_derive_stdlib.Coverage.
Import test_param1.Coverage.
Import test_param1_congr.Coverage.

Module Coverage.

Elpi derive.param1.trivial is_empty.
Elpi derive.param1.trivial is_unit.
Elpi derive.param1.trivial is_peano.
(*
Print congr_is_Succ.
Print is_peano_witness.
Print is_peano_trivial.
Definition is_peano_trivial2 : forall x : peano, {u : is_peano x & forall v : is_peano x, u = v}.
refine (fun x : peano => contracts peano is_peano x (is_peano_witness x) _).
revert x. fix rec 2.
intros x px. case px.
  reflexivity.
  intros n pn.
  simpl.
fun x : peano =>
contracts peano is_peano x (is_peano_witness x)
  ((fix IH (x0 : peano) (y : is_peano x0) {struct y} :
	    is_peano_witness x0 = y :=
      match y as i in (is_peano s1) return (is_peano_witness s1 = i) with
      | is_Zero => eq_refl
      | is_Succ n Pn => 
           congr_is_Succ n (is_peano_witness n) Pn
           (trivial_uniq peano is_peano
              (fun x1 : peano =>
               contracts peano is_peano x1 (is_peano_witness x1) (IH x1)) n
              Pn)
      (*eq_refl*) (*
          match
            trivial_uniq peano is_peano
              (fun x1 : peano =>
               contracts peano is_peano x1 (is_peano_witness x1) (IH x1)) n
              Pn in (_ = H)
            return
              (is_Succ n
                 (trivial_full peano is_peano
                    (fun x1 : peano =>
                     contracts peano is_peano x1 (is_peano_witness x1)
                       (IH x1)) n) = is_Succ n H)
          with
          | eq_refl => eq_refl
          end*)
      end) x).
*)
Elpi derive.param1.trivial is_option.
Elpi derive.param1.trivial is_pair.
Elpi derive.param1.trivial is_seq.
Elpi derive.param1.trivial is_box_peano.
Fail Elpi derive.param1.trivial is_nest.
Elpi derive.param1.trivial is_rose.
Elpi derive.param1.trivial is_rose_p.
Elpi derive.param1.trivial is_rose_o.
Fail Elpi derive.param1.trivial is_w.
(*
Lemma is_vect_witness A (PA : A -> Type) (HA : full A PA) (i : peano) (pi: is_peano i) :
  forall (v : vect A i), is_vect A PA i pi v.
(*rewrite <- (trivial_uniq _ _ is_peano_trivial i pi). clear pi.*)
revert i pi.
fix rec 3.
intros i pi v.
  rewrite <- (trivial_uniq _ _ is_peano_trivial2 i pi). clear pi.
  case v.
  constructor 1.
intros x j xs.
  constructor 2.
  apply HA.
  apply rec.
Defined.

Lemma is_vect_trivial A (PA : A -> Type) (HA : trivial A PA) :
forall (i : peano) (pi: is_peano i), trivial (vect A i) (is_vect A PA i pi).
Proof.
    intros i pi v.
    apply (contracts _ (is_vect A PA i pi) v (is_vect_witness A PA (trivial_full _ _ HA) i pi v)). 
    (*rewrite <- (trivial_uniq _ _ is_peano_trivial i pi). clear pi.*)
    revert i pi v.
    fix rec 4.
    intros i is_i v is_v.
    case is_v.
      reflexivity.
    intros a is_a j is_j t is_t.
    case (rec j is_j t is_t).
    rewrite <- (trivial_uniq _ _ is_peano_trivial2 j is_j).
    rewrite <- (trivial_uniq _ _ HA a is_a).
    simpl.
    assert (forall x, x = 
    (trivial_uniq peano is_peano is_peano_trivial2 (Succ j)
     (is_Succ j (trivial_full peano is_peano is_peano_trivial2 j)))
    ).

intro.
unfold trivial_uniq, trivial_full, is_peano_trivial2. simpl.

    unfold is_peano_trivial.
    case (trivial_uniq peano is_peano is_peano_trivial (Succ j) (is_Succ j (trivial_full peano is_peano is_peano_trivial j))).
    reflexivity.



    unfold is_vect_witness. unfold trivial_uniq. unfold is_peano_trivial. simpl.
    reflexivity.
    case

    Check (contracts _ _ (is_vect_witness A PA (trivial_full _ _ HA))).



*)
Fail Elpi derive.param1.trivial is_vect.
Fail Elpi derive.param1.trivial is_dyn.
Elpi derive.param1.trivial is_zeta.
Elpi derive.param1.trivial is_beta.
Fail Elpi derive.param1.trivial is_iota.
Fail Elpi derive.param1.trivial is_large.
Elpi derive.param1.trivial is_prim_int.
Elpi derive.param1.trivial is_prim_float.
Elpi derive.param1.trivial is_fo_record.
Elpi derive.param1.trivial is_pa_record.
Elpi derive.param1.trivial is_pr_record.
Fail Elpi derive.param1.trivial is_dep_record.
Elpi derive.param1.trivial is_enum.
Elpi derive.param1.trivial is_bool.
(*
Elpi derive.param1.trivial is_eq. (* ad-hoc *)
*)
Elpi derive.param1.trivial is_sigma_bool.
Elpi derive.param1.trivial is_ord.
Elpi derive.param1.trivial is_val.


End Coverage.

Import Coverage.

Check is_empty_trivial : trivial empty is_empty.
Check is_unit_trivial : trivial unit is_unit.
Check is_peano_trivial : trivial peano is_peano.
Check is_option_trivial : forall A P, trivial A P -> trivial (option A) (is_option A P).
Check is_pair_trivial : forall A P, trivial A P -> forall B Q, trivial B Q -> trivial (pair A B) (is_pair A P B Q).
Check is_seq_trivial : forall A P, trivial A P -> trivial (seq A) (is_seq A P).
Check is_rose_trivial : forall A P, trivial A P -> trivial (rose A) (is_rose A P).
Fail Check is_nest_trivial.
Fail Check is_w_trivial : forall A P, trivial A P -> trivial (w A) (is_w A P).
Fail Check is_vect_trivial : forall A P, trivial A P -> forall i pi, trivial (vect A i) (is_vect A P i pi).
Fail Check is_dyn_trivial.
Check is_zeta_trivial : forall A P, trivial A P -> trivial (zeta A) (is_zeta A P).
Check is_beta_trivial : forall A P, trivial A P -> trivial (beta A) (is_beta A P).
Fail Check is_iota_trivial.
Fail Check is_large_trivial : trivial large is_large.
Check is_prim_int_trivial : trivial prim_int is_prim_int.
Check is_prim_float_trivial : trivial prim_float is_prim_float.

Check is_fo_record_trivial : trivial fo_record is_fo_record.
Check is_pa_record_trivial : forall A P, trivial A P -> trivial (pa_record A) (is_pa_record A P).
Check is_pr_record_trivial : forall A P, trivial A P -> trivial (pr_record A) (is_pr_record A P).
Check is_enum_trivial : trivial enum is_enum.
Check is_sigma_bool_trivial : trivial sigma_bool is_sigma_bool.
Check is_val_trivial : trivial val is_val.
Check is_ord_trivial : forall p px, trivial (ord p) (is_ord p px).




Check is_empty_witness : full empty is_empty.
Check is_unit_witness : full unit is_unit.
Check is_peano_witness : full peano is_peano.
Check is_option_witness : forall A P, full A P -> full (option A) (is_option A P).
Check is_pair_witness : forall A P, full A P -> forall B Q, full B Q -> full (pair A B) (is_pair A P B Q).
Check is_seq_witness : forall A P, full A P -> full (seq A) (is_seq A P).
Check is_rose_witness : forall A P, full A P -> full (rose A) (is_rose A P).
Fail Check is_nest_witness.
Fail Check is_w_witness : forall A P, full A P -> full (w A) (is_w A P).
Fail Check is_vect_witness : forall A P, full A P -> forall i pi, full (vect A i) (is_vect A P i pi).
Fail Check is_dyn_witness.
Check is_zeta_witness : forall A P, full A P -> full (zeta A) (is_zeta A P).
Check is_beta_witness : forall A P, full A P -> full (beta A) (is_beta A P).
Fail Check is_iota_witness.
Fail Check is_large_witness : full large is_large.
Check is_prim_int_witness : full prim_int is_prim_int.
Check is_prim_float_witness : full prim_float is_prim_float.

Check is_fo_record_witness : full fo_record is_fo_record.
Check is_pa_record_witness : forall A P, full A P -> full (pa_record A) (is_pa_record A P).
Check is_pr_record_witness : forall A P, full A P -> full (pr_record A) (is_pr_record A P).
Check is_enum_witness : full enum is_enum.

Check is_sigma_bool_witness : full sigma_bool is_sigma_bool.
Check is_val_witness : full val is_val.
Check is_ord_witness : forall p px, full (ord p) (is_ord p px).

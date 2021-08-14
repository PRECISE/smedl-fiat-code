(*Coq definition of parseCC*)
(*Proof of wellformedness of parseCC*)

Require Import Coq.Lists.List.

Require Export smedlDef.SmedlAST_submission.
Require Export smedlDef.semantic_rules.
Require Export wellFormScenario.
Require Export wellForm.
Require Export deter_definition.
Require Export smedlDef.smedl_common_lemmas.
Require Export aux_monitor.
Require Export well_decision_proc. 
Require Import Coq.omega.Omega.
Require Export Refinement.
Require Import Fiat.ADT Fiat.ADTNotation.
Require Import Coq.QArith.QArith_base.
Require Import
        Coq.Strings.String.






(*object parseclass2
    state
        int in_class = 0;

    events
        imported inClass();//go into class
        imported outClass();//go out of class
        imported state_to_start();//state is set to CCS_START
        imported state_to_value();//state is set to CCS_VALUE
        imported state_to_range();//state is set to CCS_RANGE
        imported state_to_complete();//state is set to CCS_COMPLETE
        exported error(int);

    scenarios

       main:
          
           CCS_START -> state_to_value() when (in_class != 1) -> CCS_VALUE
           CCS_START -> state_to_value() when (in_class == 1) {raise error();} -> CCS_START
           CCS_START -> state_to_start() {raise error(0);}  -> CCS_START
           CCS_START -> state_to_range() {raise error(0);}  -> CCS_START
           CCS_START -> state_to_complete() {raise error(0);}  -> CCS_START


           CCS_VALUE -> state_to_value() -> CCS_VALUE
           CCS_VALUE -> state_to_complete() {raise error(1);} -> CCS_VALUE
           CCS_VALUE -> state_to_range() -> CCS_RANGE
           CCS_VALUE -> state_to_start() -> CCS_START


           CCS_RANGE -> state_to_value() -> CCS_VALUE
           CCS_RANGE -> state_to_complete() -> CCS_COMPLETE
           CCS_RANGE -> state_to_range() {raise error(2);}  -> CCS_RANGE
           CCS_RANGE -> state_to_start() {raise error(2);} -> CCS_RANGE


           CCS_COMPLETE -> state_to_value()  -> CCS_VALUE
           CCS_COMPLETE -> state_to_complete() {raise error(3);}  -> CCS_COMPLETE
           CCS_COMPLETE -> state_to_range() {raise error(3);}  -> CCS_COMPLETE
           CCS_COMPLETE -> state_to_start() {raise error(3);}   -> CCS_COMPLETE

       
       check_class:
          start -> in_class() when (in_class == 0)  {in_class = 1;} -> start
          start -> out_class() when (in_class == 1) {in_class = 0;} -> start
 *)



Definition imports_str := ""%string.
Definition objName:= "oni"%string.
Definition objId : list (atom * typ) := [].
 
Definition objstvar :=  [(AIdent "in_class"%string, Int)].


(*

events
        imported inClass();//go into class
        imported outClass();//go out of class
        imported state_to_start();//state is set to CCS_START
        imported state_to_value();//state is set to CCS_VALUE
        imported state_to_range();//state is set to CCS_RANGE
        imported state_to_complete();//state is set to CCS_COMPLETE
        exported error(int);


 *)

Check Build_event_definition. 
Definition e_inClass := (Build_event_definition Imported "inClass"%string []). 
Definition e_outClass := (Build_event_definition Imported "outClass"%string []).
Definition e_s2s := (Build_event_definition Imported "state_to_start"%string []).
Definition e_s2v := (Build_event_definition Imported "state_to_value"%string []).
Definition e_s2r := (Build_event_definition Imported "state_to_range"%string []).
Definition e_s2c := (Build_event_definition Imported "state_to_complete"%string []).
Definition e_error := (Build_event_definition Exported "error"%string [Int]).

Definition objev := [e_inClass;e_outClass;e_s2s;e_s2v;e_s2r;e_s2c;e_error].

(*
 main:
          
           CCS_START -> state_to_value() when (in_class != 1) -> CCS_VALUE
           CCS_START -> state_to_value() when (in_class == 1) {raise error();} -> CCS_START
           CCS_START -> state_to_start() {raise error(0);}  -> CCS_START
           CCS_START -> state_to_range() {raise error(0);}  -> CCS_START
           CCS_START -> state_to_complete() {raise error(0);}  -> CCS_START


           CCS_VALUE -> state_to_value() -> CCS_VALUE
           CCS_VALUE -> state_to_complete() {raise error(1);} -> CCS_VALUE
           CCS_VALUE -> state_to_range() -> CCS_RANGE
           CCS_VALUE -> state_to_start() -> CCS_START


           CCS_RANGE -> state_to_value() -> CCS_VALUE
           CCS_RANGE -> state_to_complete() -> CCS_COMPLETE
           CCS_RANGE -> state_to_range() {raise error(2);}  -> CCS_RANGE
           CCS_RANGE -> state_to_start() {raise error(2);} -> CCS_RANGE


           CCS_COMPLETE -> state_to_value()  -> CCS_VALUE
           CCS_COMPLETE -> state_to_complete() {raise error(3);}  -> CCS_VALUE
           CCS_COMPLETE -> state_to_range() {raise error(3);}  -> CCS_VALUE
           CCS_COMPLETE -> state_to_start() {raise error(3);}   -> CCS_VALUE
 *)

Print expr.

Definition guard1 := ENot (EEq (EAtom (AIdent "in_class"%string)) (EAtom (AInt 1%Z))).
Definition truth := (EAtom (ABool true)).


Definition eis2v := (Build_event_instance e_s2v [] guard1).
Definition eis2v_rev := (Build_event_instance e_s2v [] (ENot guard1)).

Definition eis2vng := (Build_event_instance e_s2v [] truth).
Definition eis2vng_rev := (Build_event_instance e_s2v [] (ENot truth)).

Definition eis2sng := (Build_event_instance e_s2s [] truth).
Definition eis2sng_rev := (Build_event_instance e_s2s [] (ENot truth)).

Definition eis2rng := (Build_event_instance e_s2r [] truth).
Definition eis2rng_rev := (Build_event_instance e_s2r [] (ENot truth)).

Definition eis2cng := (Build_event_instance e_s2c [] truth).
Definition eis2cng_rev := (Build_event_instance e_s2c [] (ENot truth)).


Print action.

(*states in Main*)
Definition cs := "CCS_START"%string.
Definition cv := "CCS_VALUE"%string.
Definition cr := "CCS_RANGE"%string.
Definition cc := "CCS_COMPLETE"%string.

Definition eact0 :=RaiseStmt "error"%string [(EAtom (AInt 0%Z))].
Definition eact1 :=RaiseStmt "error"%string [(EAtom (AInt 1%Z))].
Definition eact2 :=RaiseStmt "error"%string [(EAtom (AInt 2%Z))].
Definition eact3 :=RaiseStmt "error"%string [(EAtom (AInt 3%Z))].


(*steps in main*)

(*CCS_START -> state_to_value() when (in_class != 1) -> CCS_VALUE*)
Definition csv1 := Build_step cs eis2v Skip cv.

(* CCS_START -> state_to_value() when (in_class == 1) {raise error();} -> CCS_START*)
Definition csv1' := Build_step cs eis2v_rev eact0 cs.



(*CCS_START -> state_to_start() {raise error(0);}  -> CCS_START*)
Definition css1 := Build_step cs eis2sng eact0 cs.
Definition css1' := Build_step cs eis2sng_rev Skip cs.

(*CCS_START -> state_to_range() {raise error(0);}  -> CCS_START*)
Definition csr1 := Build_step cs eis2rng eact0 cs.
Definition csr1' := Build_step cs eis2rng_rev Skip cs.

(*CCS_START -> state_to_complete() {raise error(0);}  -> CCS_START*)
Definition csc1 := Build_step cs eis2cng eact0 cs.
Definition csc1' := Build_step cs eis2cng_rev Skip cs.


(* CCS_VALUE -> state_to_value() -> CCS_VALUE
           CCS_VALUE -> state_to_complete() {raise error(1);} -> CCS_VALUE
           CCS_VALUE -> state_to_range() -> CCS_RANGE
           CCS_VALUE -> state_to_start() -> CCS_START
 *)


(* CCS_VALUE -> state_to_value() -> CCS_VALUE*)
Definition cvv1 := Build_step cv eis2vng Skip cv.
Definition cvv1' := Build_step cv eis2vng_rev Skip cv.


(*CCS_VALUE -> state_to_complete() {raise error(1);} -> CCS_VALUE*)
Definition cvc1 := Build_step cv eis2cng eact1 cv.
Definition cvc1' := Build_step cv eis2cng_rev Skip cv.

(* CCS_VALUE -> state_to_range() -> CCS_RANGE*)
Definition cvr1 := Build_step cv eis2rng Skip cr.
Definition cvr1' := Build_step cv eis2rng_rev Skip cv.

(* CCS_VALUE -> state_to_start() -> CCS_START*)
Definition cvs1 := Build_step cv eis2sng Skip cs.
Definition cvs1' := Build_step cv eis2sng_rev Skip cs.



(*
          CCS_RANGE -> state_to_value() -> CCS_VALUE
           CCS_RANGE -> state_to_complete() -> CCS_COMPLETE
           CCS_RANGE -> state_to_range() {raise error(2);}  -> CCS_RANGE
           CCS_RANGE -> state_to_start() {raise error(2);} -> CCS_RANGE
 *)


(*CCS_RANGE -> state_to_value() -> CCS_VALUE*)
Definition crv1 := Build_step cr eis2vng Skip cv.
Definition crv1' := Build_step cr eis2vng_rev Skip cv.


(*CCS_RANGE -> state_to_complete() -> CCS_COMPLETE*)
Definition crc1 := Build_step cr eis2cng Skip cc.
Definition crc1' := Build_step cr eis2cng_rev Skip cc.

(*CCS_RANGE -> state_to_range() {raise error(2);}  -> CCS_RANGE*)
Definition crr1 := Build_step cr eis2rng eact2 cr.
Definition crr1' := Build_step cr eis2rng_rev Skip cr.

(*CCS_RANGE -> state_to_start() {raise error(2);} -> CCS_RANGE*)
Definition crs1 := Build_step cr eis2sng eact2 cr.
Definition crs1' := Build_step cr eis2sng_rev Skip cr.


(*CCS_COMPLETE -> state_to_value()  -> CCS_VALUE
           CCS_COMPLETE -> state_to_complete() {raise error(3);}  -> CCS_COMPLETE
           CCS_COMPLETE -> state_to_range() {raise error(3);}  -> CCS_COMPLETE
           CCS_COMPLETE -> state_to_start() {raise error(3);}   -> CCS_COMPLETE*)



(*CCS_COMPLETE -> state_to_value()  -> CCS_VALUE*)
Definition ccv1 := Build_step cc eis2vng Skip cv.
Definition ccv1' := Build_step cc eis2vng_rev Skip cv.


(* CCS_COMPLETE -> state_to_complete() {raise error(3);}  -> CCS_COMPLETE*)
Definition ccc1 := Build_step cc eis2cng eact3 cc.
Definition ccc1' := Build_step cc eis2cng_rev Skip cc.

(* CCS_COMPLETE -> state_to_range() {raise error(3);}  -> CCS_COMPLETE*)
Definition ccr1 := Build_step cc eis2rng eact3 cc.
Definition ccr1' := Build_step cc eis2rng_rev Skip cc.

(*CCS_COMPLETE -> state_to_start() {raise error(3);}   -> CCS_COMPLETE*)
Definition ccs1 := Build_step cc eis2sng eact3 cc.
Definition ccs1' := Build_step cc eis2sng_rev Skip cc.


Definition mainS := Build_scenario "main"%string (csv1::csv1'::css1::css1'::csr1::csr1'::csc1::csc1'::cvv1::cvv1'::cvs1::cvs1'::cvr1::cvr1'::cvc1::cvc1'::crv1::crv1'::crs1::crs1'::crr1::crr1'::crc1::crc1'::ccv1::ccv1'::ccs1::ccs1'::ccr1::ccr1'::ccc1::[ccc1']) [e_s2s;e_s2v;e_s2r;e_s2c].

Print action. 

(*       check_class:
          start -> in_class() when (in_class == 0)  {in_class = 1;} -> start
          start -> out_class() when (in_class == 1) {in_class = 0;} -> start*)

(*state in check_class*)
Definition start := "start"%string.


Definition chk_act1 := (StateUpdate (LExp ( (AIdent "in_class"%string ))) (EAtom (AInt 1%Z))).

Definition chk_act2 := (StateUpdate (LExp ( (AIdent "in_class"%string ))) (EAtom (AInt 0%Z))).

(* check_class:
          start -> in_class() when (in_class != 1)  {in_class = 1;} -> start
          start -> out_class() when (in_class == 1) {in_class = 0;} -> start*)

Definition eiinClass := (Build_event_instance e_inClass [] guard1).
Definition eiinClass_rev := (Build_event_instance e_inClass [] (ENot guard1)).

Definition eioutClass := (Build_event_instance e_outClass [] (ENot guard1)).
Definition eioutClass_rev := (Build_event_instance e_outClass [] (ENot (ENot guard1))).


Definition check_inc := Build_step start eiinClass chk_act1 start.
Definition check_inc' := Build_step start eiinClass_rev Skip start.

Definition check_outc := Build_step start eioutClass chk_act2 start.
Definition check_outc' := Build_step start eioutClass_rev Skip start.


Definition checkS := Build_scenario "check_class"%string (check_inc::check_inc'::check_outc::[check_outc']) [e_inClass;e_outClass].

Definition sces := [mainS;checkS]. 

Definition stpSceMap := (mainS, csv1) :: (mainS, csv1') :: (mainS, css1) :: (mainS, css1') :: (mainS, csr1) :: (mainS, csr1') :: (mainS, csc1) :: (mainS, csc1') :: (mainS, cvv1) :: (mainS, cvv1') ::(mainS, cvs1) :: (mainS, cvs1') :: (mainS, cvr1) :: (mainS, cvr1') :: (mainS, cvc1) :: (mainS, cvc1') :: (mainS, crv1) :: (mainS, crv1') :: (mainS, crs1) :: (mainS, crs1') :: (mainS, crr1) :: (mainS, crr1') :: (mainS, crc1) :: (mainS, crc1') :: (mainS, ccv1) :: (mainS, ccv1') ::  (mainS, ccs1) :: (mainS, ccs1') ::  (mainS, ccr1) :: (mainS, ccr1') ::  (mainS, ccc1) :: (mainS, ccc1') :: (checkS, check_inc) :: (checkS, check_inc') :: (checkS, check_outc) :: [(checkS, check_outc')].


Definition stSceMap := [(mainS,cs);(mainS,cv);(mainS,cr);(mainS,cc);
                        (checkS,start)].


Definition stEvStpMap := ((cs, eis2v), Some csv1) :: ((cs, eis2v_rev), Some csv1') :: ((cs, eis2sng), Some css1)  :: ((cs, eis2sng_rev), Some css1')  :: ((cs, eis2rng), Some csr1)  :: ((cs, eis2rng_rev), Some csr1')  :: ((cs, eis2cng), Some csc1)  :: ((cs, eis2cng_rev), Some csc1')  ::
 ((cv, eis2vng), Some cvv1)  :: ((cv, eis2vng_rev), Some cvv1') ::
((cv, eis2sng), Some cvs1)  :: ((cv, eis2sng_rev), Some cvs1') ::                                                             
((cv, eis2rng), Some cvr1)  :: ((cv, eis2rng_rev), Some cvr1') ::
((cv, eis2cng), Some cvc1)  :: ((cv, eis2cng_rev), Some cvc1') ::
 ((cr, eis2vng), Some crv1)  :: ((cv, eis2vng_rev), Some crv1') ::
((cr, eis2sng), Some crs1)  :: ((cr, eis2sng_rev), Some crs1') ::                                                             
((cr, eis2rng), Some crr1)  :: ((cv, eis2rng_rev), Some crr1') ::
((cr, eis2cng), Some crc1')  :: ((cv, eis2cng_rev), Some crc1') ::

 ((cc, eis2vng), Some ccv1)  :: ((cc, eis2vng_rev), Some ccv1') ::
((cc, eis2sng), Some ccs1)  :: ((cc, eis2sng_rev), Some ccs1') ::                                                             
((cc, eis2rng), Some ccr1)  :: ((cc, eis2rng_rev), Some ccr1') ::
((cc, eis2cng), Some ccc1)  :: ((cc, eis2cng_rev), Some ccc1') ::

((start,eiinClass),Some check_inc) :: ((start,eiinClass_rev),Some check_inc') ::
((start,eioutClass),Some check_outc) :: [((start,eioutClass_rev),Some check_outc')].

Definition stEvStpMap' := (((cs, eis2v),mainS), Some csv1) :: (((cs, eis2v_rev),mainS), Some csv1') :: (((cs, eis2sng),mainS), Some css1)  :: (((cs, eis2sng_rev),mainS), Some css1')  :: (((cs, eis2rng),mainS), Some csr1)  :: (((cs, eis2rng_rev),mainS), Some csr1')  :: (((cs, eis2cng),mainS), Some csc1)  :: (((cs, eis2cng_rev),mainS), Some csc1')  ::
 (((cv, eis2vng),mainS), Some cvv1)  :: (((cv, eis2vng_rev),mainS), Some cvv1') ::
(((cv, eis2sng),mainS), Some cvs1)  :: (((cv, eis2sng_rev),mainS), Some cvs1') ::                                                             
(((cv, eis2rng),mainS), Some cvr1)  :: (((cv, eis2rng_rev),mainS), Some cvr1') ::
(((cv, eis2cng),mainS), Some cvc1)  :: (((cv, eis2cng_rev),mainS), Some cvc1') ::
 (((cr, eis2vng),mainS), Some crv1)  :: (((cr, eis2vng_rev),mainS), Some crv1') ::
(((cr, eis2sng),mainS), Some crs1)  :: (((cr, eis2sng_rev),mainS), Some crs1') ::                                                             
(((cr, eis2rng),mainS), Some crr1)  :: (((cr, eis2rng_rev),mainS), Some crr1') ::
(((cr, eis2cng),mainS), Some crc1)  :: (((cr, eis2cng_rev),mainS), Some crc1') ::

 (((cc, eis2vng),mainS), Some ccv1)  :: (((cc, eis2vng_rev),mainS), Some ccv1') ::
(((cc, eis2sng),mainS), Some ccs1)  :: (((cc, eis2sng_rev),mainS), Some ccs1') ::                                                             
(((cc, eis2rng),mainS), Some ccr1)  :: (((cc, eis2rng_rev),mainS), Some ccr1') ::
(((cc, eis2cng),mainS), Some ccc1)  :: (((cc, eis2cng_rev),mainS), Some ccc1') ::

(((start,eiinClass),checkS),Some check_inc) :: (((start,eiinClass_rev),checkS),Some check_inc') ::
(((start,eioutClass),checkS),Some check_outc) :: [(((start,eioutClass_rev),checkS),Some check_outc')].



Definition stEvDefInMap := ((Some cs, Some e_s2v), (eis2v::[eis2v_rev])) ::  ((Some cs, Some e_s2s), (eis2sng::[eis2sng_rev])) :: ((Some cs, Some e_s2r), (eis2rng::[eis2rng_rev])) :: ((Some cs, Some e_s2c), (eis2cng::[eis2cng_rev])) :: ((Some cv, Some e_s2v), (eis2vng::[eis2vng_rev])) :: ((Some cv, Some e_s2s), (eis2sng::[eis2sng_rev])) :: ((Some cv, Some e_s2r), (eis2rng::[eis2rng_rev])) ::
((Some cv, Some e_s2c), (eis2cng::[eis2cng_rev])) ::                                               ((Some cr, Some e_s2v), (eis2vng::[eis2vng_rev])) :: ((Some cr, Some e_s2s), (eis2sng::[eis2sng_rev])) :: ((Some cr, Some e_s2r), (eis2rng::[eis2rng_rev])) ::
((Some cr, Some e_s2c), (eis2cng::[eis2cng_rev])) ::
((Some cc, Some e_s2v), (eis2vng::[eis2vng_rev])) :: ((Some cc, Some e_s2s), (eis2sng::[eis2sng_rev])) :: ((Some cc, Some e_s2r), (eis2rng::[eis2rng_rev])) ::
((Some cc, Some e_s2c), (eis2cng::[eis2cng_rev])) ::
((Some start, Some e_inClass), (eiinClass::[eiinClass_rev])) ::
[((Some start, Some e_outClass), (eioutClass::[eioutClass_rev]))].





Definition parseCC := Build_object [imports_str] objName objId objstvar objev sces stEvStpMap stEvStpMap' stEvDefInMap stpSceMap stSceMap.



Ltac crush' :=    repeat match goal with
         | [ |- ?a = ?a \/ _] => left                 
         | [ H: _ \/ _ |- _] => destruct H
         | [ |- _ <> []] => unfold not;intros
         | [ H: _ |- _ /\ _] => split;auto;simpl;constructor
        | [ H: _ |- exists e1 e2, [?a3;?a4] = [e1;e2] /\ _ ] => exists a3;exists a4
                                          
          | [  |- _ /\ _] => split                                         
         | [ H: _ |- ~ In _ _] => unfold not;intros
         | [ H: ?a = ?b |- _] => inversion H;subst;clear H
         | [ H: _ |- ?a = ?b] => simpl;auto
         | [ H: _ |- uniqList _ ] => constructor
         | [ H: In ?a [] |- _] => inversion H
         | [ H: In ?a _ |- _] => inversion H;clear H
         | [ H: _ |-  typeCheckInstance _ _] => constructor;simpl                                  
         | [ H: (_,_,_) = _ |-_] => inversion H;clear H;subst                               
         | [ H: False |- _] => inversion H
         | [ H: _ |- if ?a then _ else _] => destruct a;simpl in *;auto
        
                        end.



Print stateEvDefInstanceMapEquivEListProp.
Print stateEvDefInstanceMap. 
Print object.

Lemma stateEvDefInstanceCor: stateEvDefInstanceMapEquivEListProp parseCC. 
Proof.

  
  unfold stateEvDefInstanceMapEquivEListProp;intros;simpl in *;
  
 crush';simpl;try (inversion H1);try (inversion H);
  (*; 
   | [H:_|- HasTy _ (EEq _ (EAtom (AString _))) _] => apply HasTy_Op2_Eq with (t:=Str);auto;constructor;simpl;auto
   | [H:_|- HasTy _ (EEq _ (EAtom (AInt _))) _] => apply HasTy_Op2_Eq with (t:=Int);auto;constructor;simpl;auto;auto                                                                                                     *)
   repeat (match goal with
            | [H:_|- HasTy _ (EEq _ (EAtom (AString _))) _] => apply HasTy_Op2_Eq with (t:=Str);auto;constructor;simpl;auto
            | [H:_|- HasTy _ (EEq _ (EAtom (AInt _))) _] => apply HasTy_Op2_Eq with (t:=Int);auto;constructor;simpl;auto;auto
            | [H:_|- HasTy _ (ELt _ (EAtom (AInt _))) _] => apply HasTy_Op2_Lt1;auto;constructor;simpl;auto
            | [H:_|- HasTy _ (ELe _ (EAtom (AInt _))) _] => apply HasTy_Op2_Le1;auto;constructor;simpl;auto
          | [H:_|- HasTy [_;(AIdent ?a, Float);_] (ELe _ (EAtom (AIdent ?a))) _] => apply HasTy_Op2_Le2;auto;constructor;simpl;auto                                                                                                    
          | [H:_|- HasTy _ (EAnd _ _) _] => constructor;simpl;auto
          | [H:_|- HasTy _ (EOr _ _) _] => constructor;simpl;auto
           | [H:_|- HasTy _ (ENot _) _] => constructor;simpl;auto                                  
          | [H:_|- HasTy _ (EAtom _) _] => constructor;simpl;auto                 
     | [H:_|- HasTy _ ?a _] => unfold a;simpl;auto
                                                  
  end)
   ;auto. 
Qed.                                                                           








Lemma typeCheckCor: typeCheck parseCC. 
Proof.
  unfold typeCheck;intros;unfold typeCheckScenario;intros;unfold  typeCheckStep;simpl in *;
    crush';split;simpl;try(constructor);simpl;auto;try(constructor);simpl;
      repeat match goal with
            | [|- HasTy _ ?a _] => unfold a;simpl;auto

             | [|- HasTy _ (EEq _ (EAtom (AString _))) _] => apply HasTy_Op2_Eq with (t:=Str);auto;constructor;simpl;auto
            | [|- HasTy _ (EEq _ (EAtom (AInt _))) _] => apply HasTy_Op2_Eq with (t:=Int);auto;constructor;simpl;auto;auto
            | [|- HasTy _ (ELt _ (EAtom (AInt _))) _] => apply HasTy_Op2_Lt1;auto;constructor;simpl;auto
            | [|- HasTy _ (ELe _ (EAtom (AInt _))) _] => apply HasTy_Op2_Le1;auto;constructor;simpl;auto
          | [|- HasTy [_;(AIdent ?a, Float);_] (ELe _ (EAtom (AIdent ?a))) _] => apply HasTy_Op2_Le2;auto;constructor;simpl;auto                                                                                                    
          | [|- HasTy _ (EAnd _ _) _] => constructor;simpl;auto
          | [|- HasTy _ (EOr _ _) _] => constructor;simpl;auto
           | [|- HasTy _ (ENot _) _] => constructor;simpl;auto                                  
          | [|- HasTy _ (EAtom _) _] => constructor;simpl;auto                 
             | [ H:_ |- HasTy_action _ _ ?a] => unfold a
            | [ H:_ |- HasTy_action _ _ (StateUpdate _ _ _)] => eapply HasTy_action_Assign;simpl                                  
          | [ |- uniqList _ ] => constructor
         | [ H: In ?a [] |- _] => inversion H
         | [ H: In ?a _ |- _] => inversion H;clear H
         | [ |- ~ In _ _] => unfold not;intros;simpl
         | [ H: ?a = ?b |- False] => inversion H;clear H                                        
             end.
  exists e_error;split;simpl in *;repeat(constructor;auto).
  exists e_error;split;simpl in *;repeat(constructor;auto).
 exists e_error;split;simpl in *;repeat(constructor;auto).
 exists e_error;split;simpl in *;repeat(constructor;auto).
 exists e_error;split;simpl in *;repeat(constructor;auto).
 exists e_error;split;simpl in *;repeat(constructor;auto).
 exists e_error;split;simpl in *;repeat(constructor;auto).
 exists e_error;split;simpl in *;repeat(constructor;auto).
 exists e_error;split;simpl in *;repeat(constructor;auto).
 exists e_error;split;simpl in *;repeat(constructor;auto).
 
   unfold chk_act1. 
   apply HasTy_action_Assign with (ty:=Int);auto;constructor;constructor;simpl;auto.

    unfold chk_act2. 
  apply HasTy_action_Assign with (ty:=Int);auto;constructor;constructor;simpl;auto.

  

Qed.


Lemma e_exists_basic:  forall ev2 a, a = e_inClass \/ a = e_outClass \/ a = e_error->
  ~ (exists sce : scenario,
                             In sce (scenarios parseCC) /\
                             (exists (tr : step) (act : action) (exprs : list expr),
                                In tr (getTransitionsOfScenario sce) /\
                                In act (transitionIntoBasicActionList (stepActions tr)) /\
                                act = RaiseStmt (eventId ev2) exprs /\ a = event (stepEvent tr))).
Proof.
  intros. destruct H; subst; unfold not; intros;simpl in *;
repeat match goal with
         | [ H: exists x, _ |- _ ] => destruct H
         | [ H: _ /\ _ |- _] => destruct H                                   
         | [ H: _ \/ _ |- _] => destruct H
         | [ H: False |- _] => inversion H
         | [ H: In _ _ |- _] => simpl in *;subst                 
           end;inversion H;(try (inversion H3));(try (inversion H4)). 
Qed.



Lemma e_exists_basic_rev: forall ev2 a, a = e_inClass \/ a = e_outClass \/ a = e_s2v \/ a = e_s2s \/ a = e_s2r \/ a = e_s2c ->
  ~ (exists sce : scenario,
                             In sce (scenarios parseCC) /\
                             (exists (tr : step) (act : action) (exprs : list expr),
                                In tr (getTransitionsOfScenario sce) /\
                                In act (transitionIntoBasicActionList (stepActions tr)) /\
                                act = RaiseStmt (eventId a) exprs /\ ev2 = event (stepEvent tr))).
Proof.
  intros. destruct H;subst;unfold not;intros; simpl in *;
repeat match goal with
         | [ H: exists x, _ |- _ ] => destruct H
         | [ H: _ /\ _ |- _] => destruct H                                   
         | [ H: _ \/ _ |- _] => destruct H
         | [ H: False |- _] => inversion H
         | [ H: In _ _ |- _] => simpl in *;subst                 
           end;inversion H;(try (inversion H3)). 
Qed.

Lemma no_lead_in: forall ev1 ev2,  staticEventLeadTo parseCC ev1 ev2 ->
                                In ev2 (events parseCC) /\ In ev1 (events parseCC).
Proof.
  pose proof EventEquivalence.
intros;split;induction H0;repeat match goal with
         | [ H: "error"%string = eventId ?a, H': forall ev1 ev2 : event_definition, eventId ev1 = eventId ev2 <-> ev1 = ev2  |- _] =>  assert (a = e_error);rewrite <- H';auto;subst                                                                                     
         | [ H: exists x, _ |- _ ] => destruct H
         | [ H: _ /\ _ |- _] => destruct H                                   
         | [ H: _ \/ _ |- _] => destruct H
         | [ H: ?a |- ?a \/ _] => left;auto
          | [ H: ?a |- _ \/ ?a ] => intuition                             
         | [ H: False |- _] => inversion H
         | [ H: In _ _ |- _] => simpl in *;subst
         | [ H: StateUpdate _ _ = RaiseStmt _ _ |- _] => inversion H                                        | [ H: RaiseStmt _ _ = RaiseStmt _ _ |- _] => inversion H;clear H
         | [ H: Skip = RaiseStmt _ _ |- _] => inversion H;clear H
         | [ H: Skip = StateUpdate _ _ |- _] => inversion H;clear H                                              
                             end;intuition.

Qed.

Lemma e_no_lead': forall a, a = e_inClass \/ a = e_outClass \/ a = e_error-> ~ (exists ev, staticEventLeadTo parseCC a ev).
Proof.
  intros. destruct H;subst;    
  unfold not;intros; 
    destruct H;subst;(try (destruct H0));
      pose proof no_lead_case; apply H0 in H;
  destruct H; pose proof e_exists_basic;
  unfold not in H1. 
  apply H1 with (ev2:=x) (a:=e_inClass);auto.
  destruct H. destruct H. 
  
   apply H1 with (ev2:=x0) (a:=e_inClass);auto. 
   apply H1 with (ev2:=x) (a:=e_outClass);auto.
   (destruct H). destruct H. apply H1 with (ev2:=x0) (a:=e_outClass);auto. 
   apply H1 with (ev2:=x) (a:=e_error);auto.
   (destruct H). destruct H. apply H1 with (ev2:=x0) (a:=e_error);auto.
 
Qed.
    


Lemma e_no_lead_to': forall a, (a = e_inClass \/ a = e_outClass \/ a = e_s2v \/ a = e_s2s \/ a = e_s2r \/ a = e_s2c) -> ~ (exists ev, staticEventLeadTo parseCC ev a).
Proof.
  intros; destruct H;subst;unfold not;intros;
  destruct H;subst;
  pose proof no_lead_case_rev. 
 
  apply H0 in H;
  destruct H;
  pose proof e_exists_basic_rev;
  unfold not in H1.
  
  apply H1 with (ev2:=x) (a:=e_inClass);auto.
  destruct H. destruct H. 
  apply H1 with (ev2:=x0) (a:=e_inClass);auto.

  destruct H0. 
   apply H in H0;
  destruct H0;
  pose proof e_exists_basic_rev;
  unfold not in H1.
  
  
  
   apply H1 with (ev2:=x) (a:=e_outClass);auto.
  destruct H0.   destruct H0.
  apply H1 with (ev2:=x0) (a:=e_outClass);auto.

  
  destruct H.  subst. destruct H0.  
  apply H1 in H;
  destruct H;
  pose proof e_exists_basic_rev;
  unfold not in H0.
  
  
  
   apply H0 with (ev2:=x) (a:=e_s2v);auto.
  destruct H.   destruct H.
  apply H0 with (ev2:=x0) (a:=e_s2v);auto.

   
  destruct H.  subst. destruct H0.  
  apply H1 in H;
  destruct H;
  pose proof e_exists_basic_rev;
  unfold not in H0.
  
  
  
   apply H0 with (ev2:=x) (a:=e_s2s);auto.
  destruct H.   destruct H.
  apply H0 with (ev2:=x0) (a:=e_s2s);auto.


   
  destruct H.  subst. destruct H0.  
  apply H1 in H;
  destruct H;
  pose proof e_exists_basic_rev;
  unfold not in H0.
  
  
  
   apply H0 with (ev2:=x) (a:=e_s2r);auto.
intuition.   destruct H.   destruct H.
  apply H0 with (ev2:=x0) (a:=e_s2r);auto.
intuition.   

 subst. destruct H0.  
  apply H1 in H;
  destruct H;
  pose proof e_exists_basic_rev;
  unfold not in H0.
  
  
  
   apply H0 with (ev2:=x) (a:=e_s2c);auto.
intuition.   destruct H.   destruct H.
  apply H0 with (ev2:=x0) (a:=e_s2c);auto.
intuition.   

  
Qed.



(*Lemma e_exists_basic:  forall ev2 a, a = e_inClass \/ a = e_outClass ->
  ~ (exists sce : scenario,
                             In sce (scenarios parseCC) /\
                             (exists (tr : step) (act : action) (exprs : list expr),
                                In tr (getTransitionsOfScenario sce) /\
                                In act (transitionIntoBasicActionList (stepActions tr)) /\
                                act = RaiseStmt (eventId ev2) exprs /\ a = event (stepEvent tr))).
Proof.
  intros. destruct H; subst; unfold not; intros;simpl in *;
repeat match goal with
         | [ H: exists x, _ |- _ ] => destruct H
         | [ H: _ /\ _ |- _] => destruct H                                   
         | [ H: _ \/ _ |- _] => destruct H
         | [ H: False |- _] => inversion H
         | [ H: In _ _ |- _] => simpl in *;subst                 
           end;inversion H;(try (inversion H3));(try (inversion H4)). 
Qed.



Lemma e_exists_basic_rev: forall ev2 a, a = e_inClass \/ a = e_outClass \/ a = e_s2v \/ a = e_s2s \/ a = e_s2r \/ a = e_s2c ->
  ~ (exists sce : scenario,
                             In sce (scenarios parseCC) /\
                             (exists (tr : step) (act : action) (exprs : list expr),
                                In tr (getTransitionsOfScenario sce) /\
                                In act (transitionIntoBasicActionList (stepActions tr)) /\
                                act = RaiseStmt (eventId a) exprs /\ ev2 = event (stepEvent tr))).
Proof.
  intros. destruct H;subst;unfold not;intros; simpl in *;
repeat match goal with
         | [ H: exists x, _ |- _ ] => destruct H
         | [ H: _ /\ _ |- _] => destruct H                                   
         | [ H: _ \/ _ |- _] => destruct H
         | [ H: False |- _] => inversion H
         | [ H: In _ _ |- _] => simpl in *;subst                 
           end;inversion H;(try (inversion H3)). 
Qed.*)

Lemma noRaiseAction : forall  a,  a = e_inClass \/ a = e_outClass ->
                                    ~ (exists e ev2, raiseAction parseCC e a ev2).
Proof.
     intros. destruct H; subst; unfold not; unfold raiseAction in *; intros;simpl in *;
repeat match goal with
         | [ H: exists x, _ |- _ ] => destruct H
         | [ H: _ /\ _ |- _] => destruct H                                   
         | [ H: _ \/ _ |- _] => destruct H
         | [ H: False |- _] => inversion H
         | [ H: In _ _ |- _] => simpl in *;subst                 
           end;(try (inversion H0)); (try (inversion H2)); (try (inversion H4)).  
Qed.

Lemma noRaiseAction_rev: forall  a, a = e_inClass \/ a = e_outClass \/ a = e_s2v \/ a = e_s2s \/ a = e_s2r \/ a = e_s2c ->
  ~ (exists e ev1 , raiseAction parseCC e ev1 a)
                            .
Proof.
  intros. destruct H;subst;unfold not;unfold raiseAction in *;intros; simpl in *;
repeat match goal with
         | [ H: exists x, _ |- _ ] => destruct H
         | [ H: _ /\ _ |- _] => destruct H                                   
         | [ H: _ \/ _ |- _] => destruct H
         | [ H: False |- _] => inversion H
         | [ H: In _ _ |- _] => simpl in *;subst                 
           end; (try (inversion H0)); (try (inversion H)). 
Qed.

Print staticEventLeadTo'.

Lemma no_lead_case': forall e ev1 ev2 mon, staticEventLeadTo' mon e ev1 ev2 ->
                                           raiseAction mon e ev1 ev2 \/
                                           (exists ev3,
                                               staticEventLeadTo' mon e ev1 ev3 /\
                                               raiseAction mon e ev3 ev2). 
Proof.
  intros. induction H.
  - left;auto.
  -  destruct IHstaticEventLeadTo'.
     right. exists ev2. split;auto.
     destruct H1. destruct H1. right.
     exists ev2. split;auto. 
Qed.

Lemma no_lead_case_rev': forall e ev1 ev2 mon, staticEventLeadTo' mon e ev1 ev2 ->
                                           raiseAction mon e ev1 ev2 \/
                                           (exists ev3,
                                               raiseAction mon e ev1 ev3 /\
                                               staticEventLeadTo' mon e ev3 ev2).
Proof.
  intros. induction H.
  - left;auto.
  -  destruct IHstaticEventLeadTo'.
     right. exists ev2. split;auto. apply staticLeadBasicCase';auto. 
     destruct H1. destruct H1. right.
     exists x. split;auto. apply staticLeadTransit' with (ev2:=ev2);auto. 
Qed.


Check EventEquivalence. 

Lemma no_lead'_in: forall e ev1 ev2,  staticEventLeadTo' parseCC e ev1 ev2 ->
                                In ev2 (events parseCC) /\ In ev1 (events parseCC).
Proof.
  pose proof EventEquivalence.
intros;split;induction H0;unfold raiseAction in *;repeat match goal with
         | [ H: "error"%string = eventId ?a, H': forall ev1 ev2 : event_definition, eventId ev1 = eventId ev2 <-> ev1 = ev2  |- _] =>  assert (a = e_error);rewrite <- H';auto;subst                                                                                     
         | [ H: exists x, _ |- _ ] => destruct H
         | [ H: _ /\ _ |- _] => destruct H                                   
         | [ H: _ \/ _ |- _] => destruct H
         | [ H: ?a |- ?a \/ _] => left;auto
          | [ H: ?a |- _ \/ ?a ] => intuition                             
         | [ H: False |- _] => inversion H
         | [ H: In _ _ |- _] => simpl in *;subst
         | [ H: StateUpdate _ _ = RaiseStmt _ _ |- _] => inversion H                                        | [ H: RaiseStmt _ _ = RaiseStmt _ _ |- _] => inversion H;clear H
         | [ H: Skip = RaiseStmt _ _ |- _] => inversion H;clear H
         | [ H: Skip = StateUpdate _ _ |- _] => inversion H;clear H                                              
                             end;intuition.

Qed.

Lemma no_lead': forall e a, a = e_inClass \/ a = e_outClass -> ~ (exists ev, staticEventLeadTo'  parseCC e a ev).
Proof.
  intros. destruct H;subst;
  unfold not;intros;
    destruct H.
  apply no_lead_case_rev' in H. destruct H.
  pose proof noRaiseAction. 

  unfold not in H0. 
  apply H0 with  (a:=e_inClass);auto.
  exists e;exists x;auto.

  destruct H.
  destruct H.

   pose proof noRaiseAction. 

     unfold not in H1. 
  apply H1 with  (a:=e_inClass);auto.
  exists e;exists x0;auto.

   apply no_lead_case_rev' in H. destruct H.
  pose proof noRaiseAction. 

  unfold not in H0. 
  apply H0 with  (a:=e_outClass);auto.
  exists e;exists x;auto.

  destruct H.
  destruct H.

   pose proof noRaiseAction. 

     unfold not in H1. 
  apply H1 with  (a:=e_outClass);auto.
  exists e;exists x0;auto.
  
Qed. 
   
    


Lemma no_lead'_to: forall e a, (a = e_inClass \/ a = e_outClass \/ a = e_s2v \/ a = e_s2s \/ a = e_s2r \/ a = e_s2c) -> ~ (exists ev, staticEventLeadTo' parseCC e ev a).
Proof.
  intros; destruct H;subst;unfold not;intros;
  destruct H;subst;
  pose proof no_lead_case'. 
 
  apply H0 in H;
  destruct H;
  pose proof noRaiseAction_rev;
  unfold not in H1.
  
  apply H1 with (a:=e_inClass);auto.
  exists e;exists x;auto.
  destruct H. destruct H. 
  apply H1 with  (a:=e_inClass);auto.

  exists e;exists x0;auto.

  destruct H0. 
   apply H in H0;
  destruct H0;
  pose proof noRaiseAction_rev;
  unfold not in H1.

   
  apply H1 with (a:=e_outClass);auto.
  exists e;exists x;auto.
  destruct H0. destruct H0. 
  apply H1 with  (a:=e_outClass);auto.

  exists e;exists x0;auto.

  destruct H. 
  subst. 
    
  
   destruct H0. 
   apply H1 in H;
  destruct H;
  pose proof noRaiseAction_rev. 
  unfold not in H0.

  apply H0 with (a:=e_s2v);auto.
  exists e;exists x;auto.
  destruct H. destruct H. 
  apply H0 with  (a:=e_s2v);auto.

  exists e;exists x0;auto.

  
  destruct H.
  subst.
  
   destruct H0. 
   apply H1 in H;
  destruct H;
  pose proof noRaiseAction_rev. 
  unfold not in H0.

  apply H0 with (a:=e_s2s);auto.
  exists e;exists x;auto.
  destruct H. destruct H. 
  apply H0 with  (a:=e_s2s);auto.

  exists e;exists x0;auto.

   destruct H.
  subst.
  
   destruct H0. 
   apply H1 in H;
  destruct H;
  pose proof noRaiseAction_rev. 
  unfold not in H0.

  apply H0 with (a:=e_s2r);auto.
  intuition;auto.   exists e;exists x;auto.
  destruct H. destruct H. 
  apply H0 with  (a:=e_s2r);intuition;auto.

  exists e;exists x0;auto.

subst.  

 
  
   destruct H0. 
   apply H1 in H;
  destruct H;
  pose proof noRaiseAction_rev. 
  unfold not in H0.

  apply H0 with (a:=e_s2c);auto.
  intuition;auto.   exists e;exists x;auto.
  destruct H. destruct H. 
  apply H0 with  (a:=e_s2c);intuition;auto.

  exists e;exists x0;auto.

Qed.




(*proof of determinism for parseCC*)
(*usually take >20 mins*)
(*execution time could be reduced if better tactics are used*)
(*commmented it to save time*)

Lemma deter_oni: deterProp_final' parseCC.
Proof.
 
    unfold deterProp_final'.
    split.
    +  intros. 
       
       simpl in *.
      
       pose proof no_lead'_to. 
       repeat match goal with
              | [H: updateVarEv _ _ _ |- _] => unfold updateVarEv in H
              | [H: ?a , H': ~?a |- _] => contradiction
              | [H: forall e a : event_definition,
       a = e_inClass \/ a = e_outClass \/ a = e_s2v \/ a = e_s2s \/ a = e_s2r \/ a = e_s2c ->
       ~ (exists ev : event_definition, staticEventLeadTo' parseCC e ev a),
         H1: staticEventLeadTo' parseCC ?c ?b e_inClass |- _] =>
       apply H with (e:=c) (a:=e_inClass); intuition; exists b;auto                                              | [H: forall e a : event_definition,
       a = e_inClass \/ a = e_outClass \/ a = e_s2v \/ a = e_s2s \/ a = e_s2r \/ a = e_s2c ->
       ~ (exists ev : event_definition, staticEventLeadTo' parseCC e ev a),
         H1: staticEventLeadTo' parseCC ?c ?b e_outClass |- _] =>
       apply H with (e:=c) (a:=e_outClass); intuition; exists b;auto  
               | [H: forall e a : event_definition,
       a = e_inClass \/ a = e_outClass \/ a = e_s2v \/ a = e_s2s \/ a = e_s2r \/ a = e_s2c ->
       ~ (exists ev : event_definition, staticEventLeadTo' parseCC e ev a),
         H1: staticEventLeadTo' parseCC ?c ?b e_s2v |- _] =>
       apply H with (e:=c) (a:=e_s2v); intuition; exists b;auto                                                  | [H: forall e a : event_definition,
       a = e_inClass \/ a = e_outClass \/ a = e_s2v \/ a = e_s2s \/ a = e_s2r \/ a = e_s2c ->
       ~ (exists ev : event_definition, staticEventLeadTo' parseCC e ev a),
         H1: staticEventLeadTo' parseCC ?c ?b e_s2s |- _] =>
       apply H with (e:=c) (a:=e_s2s); intuition; exists b;auto                                                  | [H: forall e a : event_definition,
       a = e_inClass \/ a = e_outClass \/ a = e_s2v \/ a = e_s2s \/ a = e_s2r \/ a = e_s2c ->
       ~ (exists ev : event_definition, staticEventLeadTo' parseCC e ev a),
         H1: staticEventLeadTo' parseCC ?c ?b e_s2r |- _] =>
       apply H with (e:=c) (a:=e_s2r); intuition; exists b;auto                                                  | [H: forall e a : event_definition,
       a = e_inClass \/ a = e_outClass \/ a = e_s2v \/ a = e_s2s \/ a = e_s2r \/ a = e_s2c ->
       ~ (exists ev : event_definition, staticEventLeadTo' parseCC e ev a),
         H1: staticEventLeadTo' parseCC ?c ?b e_s2c |- _] =>
       apply H with (e:=c) (a:=e_s2c); intuition; exists b;auto                                                 
              | [H: exists _, _|- _] => destruct H
              | [H:  In _ (scenarioUpdateVar _ _) |- _] => simpl in H                                            | [ H: _ |- ?a <> ?a] => unfold not;intros
              | [H: _ /\ _ |- _] => destruct H                                   
              | [H: _ \/ _ |- _] => destruct H;subst
              | [H: False |- _] => inversion H
              | [H: ?a <> ?a |- _] => contradiction

                                                            end.
  + split. 
       intros.        simpl in *.
        pose proof no_lead'_to.  
 repeat match goal with
              | [H: ?a , H': ~?a |- _] => contradiction
              | [H: _ \/ _ |- _] => destruct H;subst                                               
              | [H: exists _, _|- _] => destruct H
              | [H: _ /\ _ |- _] => destruct H                                        
              | [ H: _ |- ?a <> ?a] => unfold not;intros                                           
              | [H: False |- _] => inversion H
              | [H: ?a <> ?a |- _] => contradiction
                                      
        end;
   repeat match goal with
               | [H: forall e a : event_definition,
       a = e_inClass \/ a = e_outClass \/ a = e_s2v \/ a = e_s2s \/ a = e_s2r \/ a = e_s2c ->
       ~ (exists ev : event_definition, staticEventLeadTo' parseCC e ev a),
         H1: staticEventLeadTo' parseCC ?c ?b e_inClass |- _] =>
       apply H with (e:=c) (a:=e_inClass); intuition; exists b;auto                                              | [H: forall e a : event_definition,
       a = e_inClass \/ a = e_outClass \/ a = e_s2v \/ a = e_s2s \/ a = e_s2r \/ a = e_s2c ->
       ~ (exists ev : event_definition, staticEventLeadTo' parseCC e ev a),
         H1: staticEventLeadTo' parseCC ?c ?b e_outClass |- _] =>
       apply H with (e:=c) (a:=e_outClass); intuition; exists b;auto  
               | [H: forall e a : event_definition,
       a = e_inClass \/ a = e_outClass \/ a = e_s2v \/ a = e_s2s \/ a = e_s2r \/ a = e_s2c ->
       ~ (exists ev : event_definition, staticEventLeadTo' parseCC e ev a),
         H1: staticEventLeadTo' parseCC ?c ?b e_s2v |- _] =>
       apply H with (e:=c) (a:=e_s2v); intuition; exists b;auto                                                  | [H: forall e a : event_definition,
       a = e_inClass \/ a = e_outClass \/ a = e_s2v \/ a = e_s2s \/ a = e_s2r \/ a = e_s2c ->
       ~ (exists ev : event_definition, staticEventLeadTo' parseCC e ev a),
         H1: staticEventLeadTo' parseCC ?c ?b e_s2s |- _] =>
       apply H with (e:=c) (a:=e_s2s); intuition; exists b;auto                                                  | [H: forall e a : event_definition,
       a = e_inClass \/ a = e_outClass \/ a = e_s2v \/ a = e_s2s \/ a = e_s2r \/ a = e_s2c ->
       ~ (exists ev : event_definition, staticEventLeadTo' parseCC e ev a),
         H1: staticEventLeadTo' parseCC ?c ?b e_s2r |- _] =>
       apply H with (e:=c) (a:=e_s2r); intuition; exists b;auto                                                  | [H: forall e a : event_definition,
       a = e_inClass \/ a = e_outClass \/ a = e_s2v \/ a = e_s2s \/ a = e_s2r \/ a = e_s2c ->
       ~ (exists ev : event_definition, staticEventLeadTo' parseCC e ev a),
         H1: staticEventLeadTo' parseCC ?c ?b e_s2c |- _] =>
       apply H with (e:=c) (a:=e_s2c); intuition; exists b;auto    
                                             
               | [H:  In _ (scenarioUpdateVar _ _) |- _] => simpl in H
               | [H:  In _ (scenarioUsedVar _ _) |- _] => simpl in H
               | [H: _ /\ _ |- _] => destruct H
               | [H: _ \/ _ |- _] => destruct H;subst                               
        end. 

       intros.        simpl in *.
        pose proof no_lead'_to.  
 repeat match goal with
              | [H: ?a , H': ~?a |- _] => contradiction
              | [H: _ \/ _ |- _] => destruct H;subst                                               
              | [H: exists _, _|- _] => destruct H
              | [H: _ /\ _ |- _] => destruct H                                        
              | [ H: _ |- ?a <> ?a] => unfold not;intros                                           
              | [H: False |- _] => inversion H
              | [H: ?a <> ?a |- _] => contradiction
                                      
        end;
   repeat match goal with
               | [H: forall e a : event_definition,
       a = e_inClass \/ a = e_outClass \/ a = e_s2v \/ a = e_s2s \/ a = e_s2r \/ a = e_s2c ->
       ~ (exists ev : event_definition, staticEventLeadTo' parseCC e ev a),
         H1: staticEventLeadTo' parseCC ?c ?b e_inClass |- _] =>
       apply H with (e:=c) (a:=e_inClass); intuition; exists b;auto                                              | [H: forall e a : event_definition,
       a = e_inClass \/ a = e_outClass \/ a = e_s2v \/ a = e_s2s \/ a = e_s2r \/ a = e_s2c ->
       ~ (exists ev : event_definition, staticEventLeadTo' parseCC e ev a),
         H1: staticEventLeadTo' parseCC ?c ?b e_outClass |- _] =>
       apply H with (e:=c) (a:=e_outClass); intuition; exists b;auto  
               | [H: forall e a : event_definition,
       a = e_inClass \/ a = e_outClass \/ a = e_s2v \/ a = e_s2s \/ a = e_s2r \/ a = e_s2c ->
       ~ (exists ev : event_definition, staticEventLeadTo' parseCC e ev a),
         H1: staticEventLeadTo' parseCC ?c ?b e_s2v |- _] =>
       apply H with (e:=c) (a:=e_s2v); intuition; exists b;auto                                                  | [H: forall e a : event_definition,
       a = e_inClass \/ a = e_outClass \/ a = e_s2v \/ a = e_s2s \/ a = e_s2r \/ a = e_s2c ->
       ~ (exists ev : event_definition, staticEventLeadTo' parseCC e ev a),
         H1: staticEventLeadTo' parseCC ?c ?b e_s2s |- _] =>
       apply H with (e:=c) (a:=e_s2s); intuition; exists b;auto                                                  | [H: forall e a : event_definition,
       a = e_inClass \/ a = e_outClass \/ a = e_s2v \/ a = e_s2s \/ a = e_s2r \/ a = e_s2c ->
       ~ (exists ev : event_definition, staticEventLeadTo' parseCC e ev a),
         H1: staticEventLeadTo' parseCC ?c ?b e_s2r |- _] =>
       apply H with (e:=c) (a:=e_s2r); intuition; exists b;auto                                                  | [H: forall e a : event_definition,
       a = e_inClass \/ a = e_outClass \/ a = e_s2v \/ a = e_s2s \/ a = e_s2r \/ a = e_s2c ->
       ~ (exists ev : event_definition, staticEventLeadTo' parseCC e ev a),
         H1: staticEventLeadTo' parseCC ?c ?b e_s2c |- _] =>
       apply H with (e:=c) (a:=e_s2c); intuition; exists b;auto    
                                             
               | [H:  In _ (scenarioUpdateVar _ _) |- _] => simpl in H
               | [H:  In _ (scenarioUsedVar _ _) |- _] => simpl in H
               | [H: _ /\ _ |- _] => destruct H
               | [H: _ \/ _ |- _] => destruct H;subst                               
        end. 
Qed.  


Lemma traceAlphabetL: traceAlphabetIn parseCC. 
Proof. 
    unfold  traceAlphabetIn;intros.
    simpl in *.
    repeat match goal with
              | [H: ?a , H': ~?a |- _] => contradiction
              | [H: _ \/ _ |- _] => destruct H;subst;simpl in *                                    
              | [H: exists _, _|- _] => destruct H
              | [H: _ /\ _ |- _] => destruct H                                        
              | [H: False |- _] => inversion H
              | [H: ?a <> ?a |- _] => contradiction    
           end;intuition. 
Qed.     

Lemma raiseIntL: raiseInternal parseCC.
Proof. 
  unfold raiseInternal;intros.
    simpl in *.     
  
    repeat match goal with
              | [H: ?a , H': ~?a |- _] => contradiction
              | [H: _ \/ _ |- _] => destruct H;subst;simpl in *                                    
              | [H: exists _, _|- _] => destruct H
              | [H: _ /\ _ |- _] => destruct H                                        
              | [H: False |- _] => inversion H
              | [H: ?a <> ?a |- _] => contradiction
              | [H: Skip = RaiseStmt _ _|- _] => inversion H                         
           end;intuition;inversion H0. 
  
    
Qed. 

       
Lemma Well_oni: WellFormed parseCC.
Proof.
  split.
  (*noMergeError*)
  apply noMergeCheck_cor_all;auto.
  split.
  Focus 2.   
  split.
  Focus 2. split.
   Focus 2.
 split.    unfold noDupRaise''.
   intros. split.
   Focus 2. 
   apply  checkNoDup_cor_dec_all_left;auto.
   intros. 
simpl in H;repeat match goal with
                             | [H: _ \/ _ |- _] => destruct H;subst
                                                        end;simpl in H0;inversion H0.  
inversion H. split.   apply checkAlphabetRaise_cor_dec;auto.    
  split. 
  apply    deter_oni. 

  split. apply traceAlphabetL.
  apply raiseIntL. 
  
  split.
   apply typeCheckCor;auto.

   
   split.
   apply stateEvDefInstanceMapEquiv_cor_all;auto.  simpl.
   unfold checkStateEvDefInstanceMap.
   destruct (ListDec.NoDup_dec op_string_ev_dec);auto.
  
   simpl in *. 
   exfalso.     apply n;
   repeat match goal with 
     | [  |- NoDup _ ] =>  constructor 
    | [|- ~ In _ _] => unfold not;intros                                        
    | [ H: In _ []  |- _] => inversion H
   | [ H: In _ _  |- _] => inversion H; clear H                                
    | [ H: ?a = ?b |- _] => inversion H;clear H
                               end. 
   split.
   
   apply findEvInStateEvDefList_cor_all;auto. 
   split.
 
   apply transEvMapEventInstanceProp_cor_all;auto.
    split.

    (*stpStMapEquiv'*)
    Print stpStMapEquiv'.
    Print stateEvStepMap'. 
unfold stpStMapEquiv';simpl;  repeat match goal with
         | [  |- ~ In _ _] => unfold not;intros;simpl 
         | [ H: ?a = ?b |- _] => inversion H;inversion H;auto
         | [  |- uniqList _ ] => constructor
         | [ H: In ?a [] |- _] => inversion H
         | [ H: In ?a _ |- _] => inversion H;clear H
         | [ H: _ \/ _ |- _] => destruct H
         | [ H: False |- _] => inversion H
                                     end.



split.
apply stepExistsMon_all_cor_all;auto. 
split.
Print correctStateEvStepMap'.
(*correctStateEvStepMap' = 
fun mon : object =>
forall (st : scenario_state) (ei : event_instance) (stp : step) (sce : scenario),
In (st, ei, sce, Some stp) (stateEvStepMap' mon) ->
In stp (traces sce) /\ stepEvent stp = ei /\ pre_state stp = st*)




apply checklegalStateEvStpMap_cor_dec_all;simpl;auto. 

split. 
apply stateEvDefInstanceCor;auto. 
split.
(*alphabetScenario*)
apply alphabetScenario_dec_all;auto.
split.
apply stateSceProp_dec;auto. 

(*stateSceIn*)


apply stateSceIn_dec_all;auto.

  pose proof e_no_lead_to'.
  unfold importedNoCommonAlphabet''.

   intros. 
  
    simpl in *.

     pose proof no_lead_in.
    assert (In e2 (events parseCC) /\ In e1 (events parseCC)).
    apply H4;auto.
   
    destruct H5.
    clear H4. simpl in *. 
                  
    repeat match goal with
    | [H: _ \/ _ |- _] => destruct H;subst         
    | [H: _ /\ _ |- _] => destruct H;simpl in *;subst
    | [H: In _ _ |- _] =>simpl in *;subst                                                     
    | [H: exists _, _ |- _] => destruct H
    | [ H: False |- _] => inversion H                                    
    | [H: ?a <> ?a|- _] => contradiction
     | [H: forall a : event_definition,
      a = e_inClass \/ a = e_outClass \/ a = e_s2v \/ a = e_s2s \/ a = e_s2r \/ a = e_s2c ->
      ~ (exists ev : event_definition, staticEventLeadTo parseCC ev a),
         H1: staticEventLeadTo parseCC ?b e_s2s |- _] =>
      apply H with (a:=e_s2s); intuition; exists b;auto
     | [H: forall a : event_definition,
      a = e_inClass \/ a = e_outClass \/ a = e_s2v \/ a = e_s2s \/ a = e_s2r \/ a = e_s2c ->
      ~ (exists ev : event_definition, staticEventLeadTo parseCC ev a),
         H1: staticEventLeadTo parseCC ?b e_s2v |- _] =>
       apply H with (a:=e_s2v); intuition; exists b;auto
     | [H: forall a : event_definition,
      a = e_inClass \/ a = e_outClass \/ a = e_s2v \/ a = e_s2s \/ a = e_s2r \/ a = e_s2c ->
      ~ (exists ev : event_definition, staticEventLeadTo parseCC ev a),
         H1: staticEventLeadTo parseCC ?b e_s2r |- _] =>
       apply H with (a:=e_s2r); intuition; exists b;auto
     | [H: forall a : event_definition,
      a = e_inClass \/ a = e_outClass \/ a = e_s2v \/ a = e_s2s \/ a = e_s2r \/ a = e_s2c ->
      ~ (exists ev : event_definition, staticEventLeadTo parseCC ev a),
          H1: staticEventLeadTo parseCC ?b e_s2c |- _] =>
      apply H with (a:=e_s2c); intuition; exists b;auto                                                 | [H: forall a : event_definition,
      a = e_inClass \/ a = e_outClass \/ a = e_s2v \/ a = e_s2s \/ a = e_s2r \/ a = e_s2c ->
      ~ (exists ev : event_definition, staticEventLeadTo parseCC ev a),
         H1: staticEventLeadTo parseCC ?b e_inClass |- _] =>
                                                                                                          apply H with (a:=e_inClass); intuition; exists b;auto
     | [H: forall a : event_definition,
      a = e_inClass \/ a = e_outClass \/ a = e_s2v \/ a = e_s2s \/ a = e_s2r \/ a = e_s2c ->
      ~ (exists ev : event_definition, staticEventLeadTo parseCC ev a),
         H1: staticEventLeadTo parseCC ?b e_outClass |- _] =>
      apply H with (a:=e_outClass); intuition; exists b;auto                 
    | [ H: _ |- ~ (exists _, _) 
      ] =>   unfold not;intros
           end;(try (inversion H));inversion H0; repeat match goal with
       | [H: exists _, _ |- _] => destruct H                    
       | [H: _ \/ _ |- _] => destruct H;subst;simpl in *
      | [H: _ /\ _ |- _] => destruct H;simpl in *;subst                                                 
      
      | [ H: False |- _] => inversion H                                                                     end;
    pose proof   e_no_lead'; repeat match goal with
         | [H: triggerSce _ e_error _ |- _] => apply triggerSceLemma in H
         | [H: exists _, _ |- _] => destruct H
         | [H: _ /\ _ |- _] => destruct H;simpl in *;subst   
         | [H: _ \/ _ |- _] => destruct H;subst;simpl in *
         | [H: ?a = ?b |- _] => inversion H;clear H
         | [ H: False |- _] => inversion H
         | [ H:  forall a : event_definition,
       a = e_inClass \/ a = e_outClass \/ a = e_error ->
       ~ (exists ev : event_definition, staticEventLeadTo parseCC a ev),
               H1: staticEventLeadTo parseCC e_error ?b |- _] =>
          apply H with (a:=e_error); intuition; exists b;auto  
                                    end.

      


    unfold noMultAlphabet''. intros.
    unfold not;intros.
    destruct H3. 
    simpl in *.

     pose proof e_no_lead_to'.
     pose proof no_lead_in.
    assert (In e1 (events parseCC) /\ In e (events parseCC)).
    apply H5;auto.
    assert (In e2 (events parseCC) /\ In e (events parseCC)).
    apply H5;auto. 
    destruct H6.  destruct H7.
    clear H9.
    clear H5. simpl in *. 
    repeat match goal with
    | [H: _ \/ _ |- _] => destruct H;subst         
    | [H: _ /\ _ |- _] => destruct H;simpl in *;subst
    | [H: In _ _ |- _] =>simpl in *;subst                                                     
    | [H: exists _, _ |- _] => destruct H
    | [ H: False |- _] => inversion H                                    
    | [H: ?a <> ?a|- _] => contradiction
    | [H: forall a : event_definition,
      a = e_inClass \/ a = e_outClass \/ a = e_s2v \/ a = e_s2s \/ a = e_s2r \/ a = e_s2c ->
      ~ (exists ev : event_definition, staticEventLeadTo parseCC ev a),
         H1: staticEventLeadTo parseCC ?b e_s2s |- _] =>
      apply H with (a:=e_s2s); intuition; exists b;auto
     | [H: forall a : event_definition,
      a = e_inClass \/ a = e_outClass \/ a = e_s2v \/ a = e_s2s \/ a = e_s2r \/ a = e_s2c ->
      ~ (exists ev : event_definition, staticEventLeadTo parseCC ev a),
         H1: staticEventLeadTo parseCC ?b e_s2v |- _] =>
       apply H with (a:=e_s2v); intuition; exists b;auto
     | [H: forall a : event_definition,
      a = e_inClass \/ a = e_outClass \/ a = e_s2v \/ a = e_s2s \/ a = e_s2r \/ a = e_s2c ->
      ~ (exists ev : event_definition, staticEventLeadTo parseCC ev a),
         H1: staticEventLeadTo parseCC ?b e_s2r |- _] =>
       apply H with (a:=e_s2r); intuition; exists b;auto
     | [H: forall a : event_definition,
      a = e_inClass \/ a = e_outClass \/ a = e_s2v \/ a = e_s2s \/ a = e_s2r \/ a = e_s2c ->
      ~ (exists ev : event_definition, staticEventLeadTo parseCC ev a),
          H1: staticEventLeadTo parseCC ?b e_s2c |- _] =>
      apply H with (a:=e_s2c); intuition; exists b;auto                                                 | [H: forall a : event_definition,
      a = e_inClass \/ a = e_outClass \/ a = e_s2v \/ a = e_s2s \/ a = e_s2r \/ a = e_s2c ->
      ~ (exists ev : event_definition, staticEventLeadTo parseCC ev a),
         H1: staticEventLeadTo parseCC ?b e_inClass |- _] =>
                                                                                                          apply H with (a:=e_inClass); intuition; exists b;auto
     | [H: forall a : event_definition,
      a = e_inClass \/ a = e_outClass \/ a = e_s2v \/ a = e_s2s \/ a = e_s2r \/ a = e_s2c ->
      ~ (exists ev : event_definition, staticEventLeadTo parseCC ev a),
         H1: staticEventLeadTo parseCC ?b e_outClass |- _] =>
      apply H with (a:=e_outClass); intuition; exists b;auto                                               
    | [ H: _ |- ~ (exists _, _) 
    ] =>   unfold not;intros                           
           end.

   

    

Qed.



Definition configuration1 : configuration parseCC :=
  Build_configuration parseCC
    ([(AIdent "in_class"%string, (Int, (inl (inl (inl (inl 0%Z)))) ))]) [(mainS,cs);(checkS,start)] nil nil nil nil. 


Lemma configuration1_correct: correct_configuration configuration1.
Proof.
  
split;intros;simpl in *;
    repeat match goal with
    | [H: False |- _] => inversion H            
    | [ |- ?a <> []] => unfold not;intros
    | [ H: ?a = [] |- _] =>  inversion H;clear H                                   
    | [ H: ?a = ?b |- _] => inversion H
  | [ H: In _ _ |- _] =>  inversion H;clear H                                   
  | [ |- uniqList _ ] => constructor
  | [ |- ~ In _ _ ] => unfold not;intros                                 
                          
         end.
   repeat match goal with
         | [H: _ \/ _ |- _] => destruct H;subst;simpl                
                                                                       
     | [ H: ?a = [] |- _] =>  inversion H;clear
    | [ H: Some ?a = None |- False] =>  inversion H;clear                                         
    | [ H: _ |- (if ?a then _ else _) <> None] => destruct a
    | [ |- ?a <> ?b] => unfold not;intros
    | [H: ?a <> ?b |- _] => simpl in *; inversion H;clear
    | [H: ?a <> ?a |- _] => contradiction                                         
         end;
  destruct H;subst;simpl in *;(try contradiction);
    destruct H;subst;simpl in *;(try contradiction).
   
   unfold scenarioInclusion; 
  unfold incl. intros. simpl in H. inversion H. 
  split;simpl;unfold objev;try(apply Forall_cons;split;auto || omega);auto; 
  repeat match goal with 
    | [|- Forall _ _] =>  apply Forall_cons;auto
    | [|- correct_event_definition _] => split;auto
 (*   | [|- Exists importedEvent [e_track; _; _; _]] => apply Exists_cons_tl                             | [|- Exists importedEvent [e_hb; _; _]] => apply Exists_cons_hd*)
    | [|- importedEvent _ ] => unfold importedEvent; simpl; auto
    | [|-  correct_scenario _] => split;simpl;auto                                                     | [ |- uniqList _ ] => constructor
    | [ H: In _ _ |- _] =>  inversion H;clear H
    | [ |- ~ In _ _ ] => unfold not;intros
    | [ H: False |-_] => inversion H
    | [ H: ?a = ?b |- False] => inversion H;clear H                               
         end.
  
  repeat(constructor);simpl;auto.

  
  omega.
  repeat(constructor).
  unfold sces.  auto. unfold parseCC.  unfold objId. unfold objstvar.
  unfold dsmon.  simpl. auto. unfold dsmon;simpl. unfold objstvar. constructor.
  constructor.   destruct H;subst. inversion H;subst. intuition.
  destruct H;inversion H. subst. intuition. auto. 
Qed.



Lemma configuration1_ready : readyConfig configuration1.
 Proof.
   split;simpl in *;auto.
   apply configuration1_correct;auto. 
Qed.

Definition mon_oni_impl := program Well_oni configuration1_ready.

Definition mon_oni_new := monitor_new Well_oni configuration1_ready.

Definition parseCC_processEvent (r : ComputationalADT.cRep mon_oni_impl)
           (e: raisedEvent | raisedAsImported  parseCC e) :=
  monitor_processEvent r e.


Extraction Language Haskell.

Unset Extraction KeepSingleton.
Set Extraction AutoInline.
Set Extraction Optimize.
Set Extraction AccessOpaque.

(*Extraction "mon_oni.hs" mon_oni_new mon_oni_processEvent.*)

Locate createRaised. 

Require Import Coq.Lists.List.

Require Export smedlDef.SmedlAST_submission.
Require Export smedlDef.semantic_rules.
Require Export wellFormScenario.
Require Export wellForm.
Require Export smedlDef.smedl_common_lemmas.
Require Import Coq.omega.Omega.
Require Export Refinement.
Require Import Fiat.ADT Fiat.ADTNotation.


Require Import
        Coq.Strings.String.

Ltac crush :=    repeat match goal with
         | [ |- ?a = ?a \/ _] => left                 
         | [ H: _ \/ _ |- _] => destruct H
         | [ |- _ <> []] => unfold not;intros
         | [ H: _ |- exists e1 e2, [?a3;?a4] = [e1;e2] /\ _ ] => exists a3;exists a4
         | [ H: _ |- _ /\ _] => split;auto;simpl;constructor
          | [  |- _ /\ _] => split                                         
         | [ H: _ |- ~ In _ _] => unfold not;intros
         | [ H: ?a = ?b |- _] => inversion H;subst;clear H
         | [ H: _ |- ?a = ?b] => simpl;auto
         | [ H: _ |- uniqList _ ] => constructor
         | [ H: In ?a [] |- _] => inversion H
         | [ H: In ?a _ |- _] => inversion H;clear H
         | [ H: _ |-  typeCheckInstance _ _] => constructor;simpl
         | [ H: _ |-  HasTy _ _ _] => constructor;simpl
         | [ H: (_,_,_) = _ |-_] => inversion H;clear H;subst                               
         | [ H: False |- _] => inversion H
         | [ H: _ |- if ?a then _ else _] => destruct a;simpl in *;auto
        
                        end.

Lemma no_lead_case: forall ev1 ev2 mon,  staticEventLeadTo mon ev1 ev2 ->
                          (exists sce : scenario,
                             In sce (scenarios mon) /\
                             (exists (tr : step) (act : action) (exprs : list expr),
                                In tr (getTransitionsOfScenario sce) /\
                                In act (transitionIntoBasicActionList (stepActions tr)) /\
                                act = RaiseStmt (eventId ev2) exprs /\ ev1 = event (stepEvent tr))) \/ (exists ev3, (exists sce : scenario,
                             In sce (scenarios mon) /\
                             (exists (tr : step) (act : action) (exprs : list expr),
                                In tr (getTransitionsOfScenario sce) /\
                                In act (transitionIntoBasicActionList (stepActions tr)) /\
                                act = RaiseStmt (eventId ev3) exprs /\ ev1 = event (stepEvent tr)))/\ staticEventLeadTo mon ev3 ev2).
Proof.
  intros;induction H.
  left;auto.
  right.
  destruct  IHstaticEventLeadTo1.
  destruct  IHstaticEventLeadTo2.
  exists ev2. split;auto.
  exists ev2. split;auto.
  destruct (IHstaticEventLeadTo2).
  destruct H1.
  exists x. split;auto. destruct H1;auto.
  destruct H1.
  eapply staticLeadTransit. apply H3.  auto.
 
  destruct H1;destruct H1.
  exists x. split;auto.
  eapply staticLeadTransit. apply H3.  auto.
Qed.

(*Inductive
staticEventLeadTo' (mon : object) (e : event_definition)
  : event_definition -> event_definition -> Prop :=
    staticLeadBasicCase' : forall ev1 ev2 : event_definition,
                           raiseAction mon e ev1 ev2 -> staticEventLeadTo' mon e ev1 ev2
  | staticLeadTransit' : forall ev1 ev2 ev3 : event_definition,
                         staticEventLeadTo' mon e ev1 ev2 ->
                         raiseAction mon e ev2 ev3 -> staticEventLeadTo' mon e ev1 ev3*)


  

  
Lemma no_lead_case_rev: forall ev1 ev2 mon,  staticEventLeadTo mon ev1 ev2 ->
                          (exists sce : scenario,
                             In sce (scenarios mon) /\
                             (exists (tr : step) (act : action) (exprs : list expr),
                                In tr (getTransitionsOfScenario sce) /\
                                In act (transitionIntoBasicActionList (stepActions tr)) /\
                                act = RaiseStmt (eventId ev2) exprs /\ ev1 = event (stepEvent tr))) \/ (exists ev3, (exists sce : scenario,
                             In sce (scenarios mon) /\
                             (exists (tr : step) (act : action) (exprs : list expr),
                                In tr (getTransitionsOfScenario sce) /\
                                In act (transitionIntoBasicActionList (stepActions tr)) /\
                                act = RaiseStmt (eventId ev2) exprs /\ ev3 = event (stepEvent tr)))/\ staticEventLeadTo mon ev1 ev3).
Proof.
  intros;induction H.
  left;auto.
  right.
  destruct  IHstaticEventLeadTo1.
  destruct  IHstaticEventLeadTo2.
  exists ev2. split;auto.
  destruct H2. 
  exists x. destruct H2.  split;auto.
  eapply staticLeadTransit. apply H.  auto.
  destruct (IHstaticEventLeadTo2).
 
  exists ev2. split;auto.
  destruct H2. destruct H2.
  exists x. split;auto. 
  eapply staticLeadTransit. apply H.  auto.
Qed.

Lemma triggerSceLemma: forall M e sce,
    triggerSce M e sce ->
    (In e (alphabet sce) \/ (exists e', staticEventLeadTo M e e' /\ triggerSce M e' sce )).
Proof.
  intros.
  induction H.
  left;auto.
  destruct IHtriggerSce.
  right. exists e2. intuition.
  right. exists e2. intuition.
Qed.

(*{re | raisedAsImported M re }*)

Check exist. 



 Definition createRaisedEvent (M:object) (id: string) (ek: EventKind) (lk: list typ)
           (lkt: list range_typ) : option raisedEvent:=
  let evDef := Build_event_definition ek id lk in
  let re := Build_raisedEvent evDef lkt in
  let checkRaiseCompute := raisedAsImported_computation  M re in
  if checkRaiseCompute then
     Some re
  else
    None.


  

Lemma raisedRight: forall M id ek lk lkt re,
    Some re = createRaisedEvent M id ek lk lkt ->
    raisedAsImported  M re. 
Proof.                           
  intros. 
  SearchAbout  raisedAsImported. 
  apply raisedAsImported_computation_correct;auto.
  unfold createRaisedEvent in H. 
  
  remember (raisedAsImported_computation  M
          {|
          eventDefinition := {| eventKind := ek; eventId := id; eventParams := lk |};
          eventArguments := lkt |}). 
  destruct b. Focus 2.   inversion H.
  inversion H. inversion H.  auto.
Qed.


Program Definition createRaised (M:object) (id: string) (ek: EventKind) (lk: list typ)
           (lkt: list range_typ): option {re| raisedAsImported M re} :=
  match createRaisedEvent M id ek lk lkt with
  | Some re =>
    Some (exist _ re (_ : raisedAsImported M re))
  | None => None
  end. 
Obligation 1. 
 apply raisedAsImported_computation_correct;auto.
  unfold createRaisedEvent in  Heq_anonymous. 
  
  remember (raisedAsImported_computation  M
          {|
          eventDefinition := {| eventKind := ek; eventId := id; eventParams := lk |};
          eventArguments := lkt |}). 
  destruct b. Focus 2.   inversion   Heq_anonymous.
  inversion Heq_anonymous. inversion Heq_anonymous.  auto.
Defined.

(*Definition createRaisedEvent' (M:object) (id: string) (ek: EventKind) (lk: list typ)
           (lkt: list range_typ) : option {re | raisedAsImported M re} :=
  match createRaisedEvent M id ek lk lkt with
  | Some re => exist (raisedAsImported M) re raisedRight
  | None => None
  end. 
*)
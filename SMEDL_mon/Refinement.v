Require Import Coq.Lists.List.
Require Export smedlDef.SmedlAST_submission.
Require Export smedlDef.semantic_rules.
Require Export wellFormScenario.
Require Export wellForm.
Require Export smedlDef.smedl_common_lemmas.
Require Export deter_definition.
Require Import Coq.omega.Omega.
Require Import Fiat.ADT Fiat.ADTNotation.

(** * Basic definitions

    These definitions are just outlines. *)

(** A configuration is defined by the user in his or her .smedl file. *)


(** The state of a monitor is initialized when the monitor is instantiated,
    and changes as events are received. *)



(** A configuration is well-formed if it behaves correctly for any valid
    input state and any input event accepted by that configuration. *)

Definition WellFormed (M : monitor) : Prop :=
    noMergeError' M /\
    noMultAlphabet'' M /\
    importedNoCommonAlphabet'' M /\
    basicPreconditionMon M /\
    noDupRaise'' M /\
    alphabetRaisingObject M /\
    deterProp_final' M /\  traceAlphabetIn M /\
    raiseInternal M.


Definition trySync {M} conf lst : option (configuration M) :=
  match lst with
  | nil => None
  | e::lst' =>
    match combineFunc e conf with (*find the first one that can trigger execution*)
    | Some conf' => Some conf'
    | None  => None
    end
  end.

Definition syncStep `(conf: configuration M) : option (configuration M) :=
  trySync conf (raisedevents conf).


Lemma synchronyStep : forall l M (conf : configuration M) c ,
    correct_configuration conf
      -> incl l (raisedevents conf)
      -> Some c = trySync conf l
      -> (exists e, synchrony conf c e).
Proof.
  intro l. induction l.
  - intros. simpl in H1. inversion H1.
  - intros. simpl in H1.
    unfold synchrony.
    remember (combineFunc a conf).
    destruct o. inversion H1;subst.
    exists a.
    split. unfold incl in H0. apply H0. left;auto. auto.
    inversion H1.
Qed.

Lemma synchronyStep': forall M (conf : configuration M) c ,
    correct_configuration conf
      -> Some c = syncStep conf
      -> (exists e, synchrony conf c e).
Proof.
  pose proof synchronyStep.
  intros.
  unfold syncStep in H1.
  apply H with (l:=raisedevents conf);auto.
  unfold incl. intros;auto.
Qed.



Lemma wellFormedNoErrorNotFinal: forall M (conf : configuration M) ,
    WellFormed M ->
    syncProgress conf ->
    correct_configuration conf ->
    ~ (finalConfig conf) ->
    (exists c, Some c = syncStep conf).
Proof.
  intros.
  unfold syncStep. unfold trySync.
  pose proof combineNoErr.
  remember (raisedevents conf).
  destruct l.
  exfalso;apply H2. unfold finalConfig. left. rewrite <- Heql. auto.

  unfold WellFormed in H.
              repeat match goal with
            | [ H: _ /\ _ |- _ ] => destruct H

                     end.

  assert (exists conf' : configuration M, combineFunc r conf = Some conf');auto.
  apply H3;auto. destruct H6;auto.

  repeat match goal with
            | [ H: _ /\ _ |- _ ] => destruct H

                     end.
    split;auto.   split;auto. split. rewrite <- Heql.
  left;auto. repeat(split;auto). 
  destruct H12. rewrite H12. exists x. auto.

Qed.

Fixpoint macroNStep `(conf: configuration M) (n: nat) (p: {finalConfig conf} + {~(finalConfig conf)}): option (configuration M) :=
  if p then
     Some conf
  else
    match n with
    |  O => Some conf
    |  S n' => let conf' := syncStep conf in (*need to consider error info to see if the execution has finished*)
            match conf' with
            | Some conf'' => @macroNStep M conf'' n' (finalConfig_dec conf'')
            | None => None
            end
    end.

Lemma syncStepCorrect: forall M (conf conf' : configuration M),
    correct_configuration conf ->
    WellFormed M ->
    Some conf' = syncStep conf ->
    correct_configuration conf'.
Proof.
  intros.
  pose proof synchronyStep'.
  apply H2 in H1. destruct H1.
  unfold WellFormed in H0.

           repeat match goal with
            | [ H: _ /\ _ |- _ ] => destruct H

                  end.
  destruct H5.
           repeat match goal with
            | [ H: _ /\ _ |- _ ] => destruct H

                  end.
  apply termL5 with (conf:=conf) (e:=x);auto.

  remember H1. clear Heqs. unfold synchrony in s.
  destruct s.
  apply raised_wellform with (conf:=conf);auto. auto.
Qed.

Check ConnectedRefl. 


Local Close Scope N.

Lemma ConnectedStep': forall n M (conf conf' : configuration M) p, correct_configuration conf -> Some conf' = @macroNStep M conf n p ->  WellFormed M -> (exists e, Connected conf conf' e).
Proof.
  intro n;induction n.
  - intros. rename H1 into WellFormedC. simpl in H0. destruct p. inversion H0;subst.
    unfold finalConfig in f.
    exists (Build_raisedEvent (Build_event_definition Imported "" nil) nil ).
   apply ConnectedRefl.
    inversion H0;subst.
     exists (Build_raisedEvent (Build_event_definition Imported "" nil) nil ).  apply ConnectedRefl.
- intros. rename H1 into WellFormedC.
  simpl in H0.
  destruct p. inversion H0;auto.
  exists (Build_raisedEvent (Build_event_definition Imported "" nil) nil ).
  apply ConnectedRefl.
   remember (syncStep conf).
   destruct o. Focus 2. inversion H0.
   apply IHn in H0. destruct H0.
   pose proof synchronyStep'.
   apply H1 in Heqo;auto. destruct Heqo.
   exists x0. eapply ConnectedTrans. apply H2. apply H0.
   apply syncStepCorrect with (conf:=conf);auto.
   auto.
Qed.



Inductive ConnectedRanking (M : monitor) : nat -> configuration M -> configuration M -> raisedEvent -> Prop :=
  | ConnectedReflRanking : forall (a : configuration M) (e : raisedEvent), ConnectedRanking O a a e
  | ConnectedTransRanking : forall n (a1 a2 a3 : configuration M) (e e' : raisedEvent),
      synchrony a1 a2 e -> ConnectedRanking n a2 a3 e' -> ConnectedRanking (S n) a1 a3 e.

Lemma ConnectedStep''': forall n M (conf conf' : configuration M) e p, initialConfig conf -> Some conf' = @macroNStep M conf n p ->   In e (raisedevents conf) -> WellFormed M ->  Connected conf conf' e.
Proof.
  intro n;induction n.
  - intros. rename H2 into WellFormedC. rename H1 into inconf. simpl in H0. destruct p. inversion H0;subst.

    apply ConnectedRefl.

    inversion H0;subst.
     apply ConnectedRefl.
  - intros. rename H2 into WellFormedC. rename H1 into inconf.
  simpl in H0.
  destruct p. inversion H0;auto.
subst.     apply ConnectedRefl.
  remember (syncStep conf).
  destruct o. Focus 2. inversion H0.
   pose proof synchronyStep'. remember Heqo. clear Heqe0.
   apply H1 in Heqo;auto. destruct Heqo. Focus 2. destruct H;auto.

   remember H2. clear Heqs.
    pose proof ConnectedStep'.
        apply H3 in H0;auto. destruct H0.

   eapply ConnectedTrans.
   assert (x = e).
   unfold synchrony in s.
   destruct s.
   remember H. clear Heqi. destruct i.
      repeat match goal with
            | [ H: _ /\ _ |- _ ] => destruct H

             end.
        apply initialConfigOneRaisedEvent with (conf:=conf);auto.
        subst.     apply H2.
        apply H0.

   apply syncStepCorrect with (conf:=conf);auto. destruct H;auto.
Qed.

Lemma chainMergeStep': forall n M (conf conf' : configuration M) e p, initialConfig conf -> In e (raisedevents conf) -> Some conf' = @macroNStep M conf n p ->  WellFormed M -> (conf = conf' \/ chainMerge conf conf' e).
Proof.
   pose proof  ConnectedStep'''.
   pose proof   Connected_chainmerge.
   intros.

   apply H0;auto.
   apply H with (n:=n) (p:=p);auto.
Qed.





Lemma wellFormedNoError': forall n M (conf : configuration M) ,
    WellFormed M ->
    correct_configuration conf ->
    (initialConfig conf \/ (exists conf' e, chainMerge conf' conf e)) ->
    syncProgress conf ->
    (exists conf', Some conf' = macroNStep n (finalConfig_dec conf)).
Proof. intro n;induction n.
       - intros. simpl. destruct (finalConfig_dec conf). exists conf;auto. exists conf;auto.
       -
         intros.
         simpl.
         destruct (finalConfig_dec conf). exists conf;auto.
         remember (syncStep conf). destruct o.
         assert ((finalConfig c) \/ ~ (finalConfig c)).
         apply excluded_middle. destruct H3.
         destruct n. simpl.
         destruct (finalConfig_dec c). exists c;auto. contradiction.
         simpl.
         destruct (finalConfig_dec c).
         exists c;auto. contradiction.
         apply IHn;auto.

         apply syncStepCorrect with (conf:=conf);auto.
         Focus 3.
         pose proof wellFormedNoErrorNotFinal.
         apply H3 in n0;auto. destruct n0. rewrite <- H4 in Heqo;inversion Heqo.
         destruct H1.

         right. exists conf.

         apply synchronyStep' in Heqo;auto.
         destruct Heqo. exists x;auto.

         apply basic';auto.

         apply synchronyStep' in Heqo;auto.
         destruct Heqo.
         right.
         destruct H1. destruct H1.
         exists x0;exists x1.
         eapply chain'. apply H1. apply H4.
         destruct H1.
         apply synchronyStep' in Heqo;auto.
         destruct Heqo.
         assert (chainMerge conf c x).
         apply basic';auto.
         Focus 2.
         destruct H1. destruct H1.
         apply synchronyStep' in Heqo;auto.
         destruct Heqo.
         assert (chainMerge x c x0).
         eapply chain'. apply H1. apply H4.
         destruct H.
            repeat match goal with
            | [ H: _ /\ _ |- _ ] => destruct H

                   end.
            remember H8. clear Heqb.
            destruct H8.
             repeat match goal with
            | [ H: _ /\ _ |- _ ] => destruct H

                    end.

         apply preserveSync with (conf:=x) (re:=x0);auto.
         split.
          apply noMultIn;auto.  apply noMultImportedIn;auto.       
          destruct H.
            repeat match goal with
            | [ H: _ /\ _ |- _ ] => destruct H

                   end.
            remember H8. clear Heqb.
            destruct H8.
             repeat match goal with
            | [ H: _ /\ _ |- _ ] => destruct H

                    end.

             apply preserveSync with (conf:=conf) (re:=x);auto.
             split.
          apply noMultIn;auto.  apply noMultImportedIn;auto.    
        Qed.






Locate inListLemma. 

Lemma wellFormedNoError: forall n M (conf : configuration M) ,
    WellFormed M ->
    initialConfig conf ->
  ~ (None = macroNStep n (finalConfig_dec conf)).
Proof.
   pose proof wellFormedNoError'.
       intros.
       remember H1. clear Heqi.
       destruct i.
       destruct H3.
       remember ((raisedevents conf)).
       destruct l. inversion H3.
       apply H with (n:=n)  (conf:=conf) in H0;auto. destruct H0. rewrite <- H0. unfold not. intros. inversion H5. apply initialImplyProgress in H1;auto.
Defined.



(*transform ready to initial*)
Definition configTransitionFunc {M : monitor} (conf: configuration M) (e: raisedEvent) : configuration M :=
  Build_configuration M (datastate conf) (controlstate conf)
                      (e::(raisedevents conf)) (exportedevents conf)
                      (finishedscenarios conf)
                      (sceEventMap conf).

Definition toReadyFunc {M : monitor} (conf: configuration M) : configuration M * (list raisedEvent) :=
  (Build_configuration M (datastate conf) (controlstate conf)
                      nil nil
                      nil
                      nil ,exportedevents conf).

Definition raisedAsImported (mon: object) (e: raisedEvent)  : Prop :=
  wellFormedRaisedEvent e /\
  importedEvent (eventDefinition e) /\
  (exists sce : scenario,
      In sce (scenarios mon) /\ In (eventDefinition e) (alphabet sce))
  /\ In (eventDefinition e) (events mon).



Lemma configTransInitial: forall M (conf conf' : configuration M) e,
    readyConfig conf ->
    raisedAsImported M e ->
    conf' = configTransitionFunc conf e ->
    configTrans conf conf'.
Proof.
  intros.
  split;auto.
  split.
  split.
  destruct H.
  destruct H.
  unfold configTransitionFunc in H1.
  unfold raisedAsImported in H0.
  subst.
    repeat match goal with
            | [ H: _ /\ _ |- _ ] => destruct H

           end.

  split;subst;simpl;auto.
  intros. rewrite H2 in H7. destruct H7. Focus 2. inversion H7.
  subst. auto.
   intros. rewrite H2 in H7. destruct H7. Focus 2. inversion H7.
   subst. auto.
    intros. rewrite H2 in H7. destruct H7. Focus 2. inversion H7.
    subst. right. unfold importedEvent in H0.
   destruct (eventKind (eventDefinition re) );inversion H0.  auto.
split.
   unfold configTransitionFunc in H1.
   unfold raisedAsImported in H0.
    destruct H.
    destruct H.
  repeat match goal with
            | [ H: _ /\ _ |- _ ] => destruct H

         end.
  rewrite H1;simpl.
rewrite H2;simpl;auto.
split.
intros.
 unfold configTransitionFunc in H1.
   unfold raisedAsImported in H0.
    destruct H.
    destruct H.
  repeat match goal with
            | [ H: _ /\ _ |- _ ] => destruct H

         end.
  rewrite H1 in H2.
  simpl in H2.
  rewrite H3 in H2.
 destruct H2;inversion H2.
 subst.
 split;auto.
 simpl.
 destruct H4. exists x;auto.
 rewrite cs_consist;auto.
 unfold configTransitionFunc in H1.
   unfold raisedAsImported in H0.
    destruct H.
    destruct H.
  repeat match goal with
            | [ H: _ /\ _ |- _ ] => destruct H

         end.
rewrite H1;auto.
unfold configStEq.
unfold configTransitionFunc in H1.
rewrite H1;auto.
Qed.



Lemma toReady: forall M (conf conf' : configuration M) reList,
    correct_configuration conf ->
    toReadyFunc conf = (conf', reList) ->
    configTransRev conf conf'.
Proof.
  intros.
  unfold configTransRev.
  unfold toReadyFunc in H0.
  inversion H0;subst;simpl.
  split.
  unfold    configStEq. simpl.
  split;auto.
  unfold readyConfig.
  split;auto. destruct H.
    split;auto.
    simpl;auto. constructor.
    unfold scenarioInclusion.  simpl. unfold incl;intros. inversion H.
    simpl. intros. inversion H.
   simpl.  intros.  inversion H.
   simpl. intros. inversion H. intros. inversion H.
   simpl. 
intros. inversion H. intros. simpl in *. inversion H. 
Qed.




Definition macroStepReadyFinal' M (conf: configuration M) (e: raisedEvent)
           (n:nat): option (configuration M*list raisedEvent) :=
  let conf' := configTransitionFunc conf e in
   match @macroNStep M conf' n (finalConfig_dec conf') with
  | Some conf'' => Some (toReadyFunc conf'')
  | None => None
  end.

Program Definition macroStepReadyFinal M (conf: configuration M)
        (e: raisedEvent) (W: WellFormed M) (C: readyConfig conf)
        (P: raisedAsImported M e) (n:nat) :
  configuration M * list raisedEvent :=
  match @macroStepReadyFinal' M conf e n with
  | Some (conf''', eList) => (conf''', eList)
  | None => False_rect _ _
  end.

Obligation 1.
unfold  macroStepReadyFinal' in Heq_anonymous.
remember (macroNStep n (finalConfig_dec (configTransitionFunc conf e))).
destruct o. inversion  Heq_anonymous.
pose proof wellFormedNoError.
remember (configTransitionFunc conf e).
pose proof configTransInitial.
apply H0 with (e:=e) (conf':=c) in C;auto.
unfold configTrans in C.
  repeat match goal with
            | [ H: _ /\ _ |- _ ] => destruct H

         end.
  apply H with (n:=n) in H2;auto.
Defined.




Lemma macroStepReadyFinalLemma: forall M (C : configuration M) e W Cor P   ,
    @macroStepReadyFinal' M C e (length (dom (controlstate C)))
      = Some (@macroStepReadyFinal M C e W Cor P (length (dom (controlstate C)))).
Proof.

  intros.
  unfold  macroStepReadyFinal.
  refine (
    (fun H => _) (_ :
    (forall (x : option (configuration M * list raisedEvent))
            (e0 : x =  macroStepReadyFinal' C e (length (dom (controlstate C))) ),
     macroStepReadyFinal' C e (length (dom (controlstate C))) =
     Some
    (match
       x as o return

         (o = macroStepReadyFinal' C e (length (dom (controlstate C))) ->
          (configuration M * list raisedEvent))
     with
     | Some p =>
         let
           (conf''', eList) as p2
            return
              (Some p2 =
               macroStepReadyFinal' C e (length (dom (controlstate C))) ->
               (configuration M * list raisedEvent)) := p in
         fun
           _ : Some (conf''', eList) =
               macroStepReadyFinal' C e(length (dom (controlstate C))) =>
         (conf''', eList)
     | None =>
         fun Heq_anonymous : None = macroStepReadyFinal' C e(length (dom (controlstate C)))
         => !
     end e0)))).


  - apply H.
  - intros. destruct x.

    +  destruct p.  rewrite <- e0. auto.


    + exfalso.
      pose proof wellFormedNoError.
      unfold macroStepReadyFinal' in e0.
      remember (macroNStep (length (dom (controlstate C))) (finalConfig_dec (configTransitionFunc C e))).
      destruct o;inversion e0.
      remember ((configTransitionFunc C e)).
      remember Heqc. clear Heqe1.
      apply configTransInitial in Heqc;auto.
      unfold configTrans in Heqc.
       repeat match goal with
            | [ H: _ /\ _ |- _ ] => destruct H

              end.
       unfold configTransitionFunc in e1.
      assert ( (controlstate C) = (controlstate c)).
      rewrite e1;auto. rewrite H3 in Heqo.
      apply H with (n:=(length (dom (controlstate c)))) (conf:=c) in W;auto.

Qed.




(** The non-deterministic specification above likely leaves out a lot of
    details, like what to actually do in certain situations. We now define
    a deterministic implementation that fills in those details, and makes
    those choices, even if they are not the best for every possible
    environment. *)

Lemma ConnectedFinishedScenariosLength : forall M (conf conf' : configuration M) x,
    Connected conf conf' x ->
    length (finishedscenarios conf) <= length (finishedscenarios conf').
Proof.
  intros.
  induction H.
   omega.
  pose proof termL4.
  apply H1 in H.
  omega.
Qed.

Lemma stepNoEqual:
  forall (n : nat) (M : monitor) (conf conf' : configuration M) (e : raisedEvent)
    (p : {finalConfig conf} + {~ finalConfig conf}),
  correct_configuration conf ->
  Some conf' = macroNStep n p -> WellFormed M -> n > 0  -> ~ finalConfig conf -> conf' <> conf.
Proof.
  intro n;induction n.
- intros. omega.
- intros. simpl in H0.
  destruct p. contradiction.
  remember (syncStep conf).
  destruct o. Focus 2. inversion H0.
  remember Heqo. clear Heqe0.
  apply synchronyStep' in Heqo;auto.
  destruct Heqo.

   apply ConnectedStep'  in H0;auto.
   destruct H0.
   pose proof termL4.
  assert (conf <> c).
  unfold not. intros.
  assert (length (finishedscenarios conf) < length (finishedscenarios c)).
  apply H5 with (e:=x);auto.

  destruct conf. destruct c.
  simpl in H7.   inversion H6.
  subst; intuition.
  assert (Connected conf conf' x).
  eapply ConnectedTrans. apply H4. apply H0.
  assert (conf' = conf \/ conf' <> conf).
  apply excluded_middle. destruct H8.
  Focus 2. auto.

  apply ConnectedFinishedScenariosLength in H0.
  apply termL4 in H4. assert (length (finishedscenarios conf) < length (finishedscenarios conf')).
  omega.
  rewrite H8 in H9. omega.
  destruct H1.
   repeat match goal with
            | [ H: _ /\ _ |- _ ] => destruct H

          end.
   destruct H7.
    repeat match goal with
            | [ H: _ /\ _ |- _ ] => destruct H

          end.
    apply termL5 with (conf:=conf) (e:=x);auto.
    apply raised_wellform with (conf:=conf);auto.
    unfold synchrony in H4. destruct H4;auto.
Qed.

Lemma marcoNStepFinish': forall n M (conf : configuration M) c  p ,
    ((exists a' e',  WellFormed M /\ chainMerge a' conf e') \/ (initialConfig conf)) ->
    WellFormed M ->
     Some c = @macroNStep M conf n  p  ->
    finalConfig c \/ (length (finishedscenarios c)  - length (finishedscenarios conf))>= n  .
Proof.
  intro n;induction n.
  - intros. simpl in H1.
    destruct p. inversion H1;subst. left;auto.
    inversion H1;subst. right. omega.
  - intros.
    simpl in H1.
   assert (correct_configuration conf).
 destruct H.   Focus 2. destruct H;auto.
    destruct H. destruct H. destruct H. destruct H.
 repeat match goal with
            | [ H: _ /\ _ |- _ ] => destruct H

        end.

 destruct H5.
  repeat match goal with
            | [ H: _ /\ _ |- _ ] => destruct H

        end.
 apply termL5' with (conf:=x) (e:=x0);auto.
     remember H2.  clear Heqc0.    apply chainMergeInitialEvent in c0;auto.
     apply chainMergeInitial in H2. destruct H2.
     destruct H2.
     apply raised_wellform';auto.



    destruct p. inversion H1;subst. left;auto.
    remember (syncStep conf).
    destruct o;inversion H1.
       remember Heqo. clear Heqe.
       apply synchronyStep' in Heqo;auto.
       destruct Heqo.
    remember H0.
    clear Heqw.

     destruct H0.

 repeat match goal with
            | [ H: _ /\ _ |- _ ] => destruct H

        end.

 destruct H7.
  repeat match goal with
            | [ H: _ /\ _ |- _ ] => destruct H

         end.
rename H21 into ssp;rename H22 into sin. 
    assert (exists e : raisedEvent, Connected c0 c e).
    pose proof ConnectedStep'.
    apply H21 with (n:=n) (p:= finalConfig_dec c0);auto.

    apply termL5 with (conf:=conf)(e:=x);auto.
    unfold synchrony in H3.
    destruct H3.
    destruct H2. apply raised_wellform' ;auto.
    destruct H21.
    apply ConnectedFinishedScenariosLength in H21.

    remember ((finalConfig_dec c0)).
     destruct s.
     destruct n. simpl in H1. inversion H1;subst;auto.
     simpl in H1.  inversion H1;subst;auto.
     apply IHn in H1.
     destruct H1. left;auto.
     right.
     apply termL4 in H3. omega.
     left.
     destruct H.
     Focus 2.
     exists conf. exists x.
     split;auto. apply basic';auto.
     destruct H. destruct H. destruct H.
     exists x1. exists x2. split;auto.
     eapply chain'. apply H22. apply H3.
     auto.
Qed.

Lemma marcoNStepFinish: forall M (conf : configuration M) c p ,
    initialConfig conf ->
    WellFormed M ->
    Some c = @macroNStep M conf (length (dom (controlstate conf))) p ->
    finalConfig c.
Proof.
  pose proof marcoNStepFinish'.

  intros.
  assert (finalConfig c \/ length (finishedscenarios c) - length (finishedscenarios conf) >= (length (dom (controlstate conf)))).
  apply H with (p:=p);auto.
  destruct H3;auto.
  remember H0. clear Heqi.
  destruct i.
   repeat match goal with
            | [ H: _ /\ _ |- _ ] => destruct H

          end.
   rewrite H7 in H3.    simpl in H3.

   rewrite <- minus_n_O in H3.
   destruct p.
   remember H0.  clear Heqi. apply InitialNotStuckNorError in i. contradiction.
  remember H0. clear Heqi.
  destruct i.
   repeat match goal with
            | [ H: _ /\ _ |- _ ] => destruct H

          end.

   pose proof (domControlSyncChain).
   pose proof chainMergeStep'. remember (raisedevents conf).
   destruct (l).  inversion H5.
   remember ( (UpperBound' (inr n))).
   unfold UpperBound' in Heqn0.
   rewrite H7 in Heqn0. simpl in Heqn0.  rewrite <- minus_n_O in Heqn0.
   assert (n0 > 0).
   rewrite Heqn0. destruct H9.
   destruct correct_mon. rewrite cs_consist. omega.
 remember H2.  clear Heqe. apply H15 with (e:=r) in H2;auto.
   Focus 2. rewrite <- Heql. left;auto. destruct H2.
   pose proof stepNoEqual.
   apply H17 in e;auto. rewrite H2 in e. contradiction.
   destruct H0. destruct H0. rewrite cs_consist. destruct correct_mon;auto.

   remember H2.   clear Heqc0. apply domControlSyncChain in c0.
   rewrite c0 in H3.

   destruct H1.
      repeat match goal with
            | [ H: _ /\ _ |- _ ] => destruct H

             end.
      destruct H19.
     repeat match goal with
            | [ H: _ /\ _ |- _ ] => destruct H

             end.
  rename H33 into ssp;rename H34 into sin. 
   assert (correct_configuration c).

   apply termL5' with (conf:=conf) (e:=r);auto.
   remember H2. clear Heqc1. apply chainMergeInitial in c1.
   apply chainMergeInitialEvent in H2.
   destruct c1.
   destruct H33.
   apply raised_wellform';auto.
   destruct H33.
   unfold scenarioInclusion in inclusion.
   unfold finalConfig. right.
   apply NoDup_length_incl;auto.
   apply uniqListNoDupEq;auto.
Qed.

Lemma marcoNStepFinishFinal: forall M (conf : configuration M) c p ,
    initialConfig conf ->
    WellFormed M ->
    Some c = @macroNStep M conf (length (dom (controlstate conf))) p ->
    finalConfig' c.
Proof.
  intros.
  assert ( finalConfig c).
  apply marcoNStepFinish with (conf:=conf) (p:=p);auto.
  pose proof preserveFinal.
  remember H0. clear Heqw. 
  unfold WellFormed in H0.
  repeat match goal with [ H: _ /\ _ |- _ ] => destruct H end.
  

  pose proof ConnectedStep'.
  assert (exists e : raisedEvent, Connected conf c e).
  apply H12 with (n:=(length (dom (controlstate conf)))) (p:=p);auto.
  destruct H;auto.
  destruct H13.
 
  assert (conf <> c).
 
  apply InitialNotStuckNorError in H.
  unfold not;intros.
  subst. contradiction.
 
  inversion H13.
  subst.   contradiction.
  subst.   unfold synchrony in H15. destruct H15.
  
  pose proof chainMergeStep'.
  
  assert (conf = c \/ chainMerge conf c x).
  apply H18 with (n:=(length (dom (controlstate conf)))) (p:=p);auto.
  destruct H19.  subst.  contradiction.
  
  
  apply H3 with (conf:=conf) (re:=x);auto.
  split.
  apply noMultIn;auto.   apply noMultImportedIn;auto. 
Qed.
(*preserveFinal*)  

Require Import
  Fiat.ADTRefinement
  Fiat.ADTRefinement.BuildADTRefinements.

Lemma ProcessEventRefinedLemma : forall M (C : configuration M) (W : WellFormed M) (Cor:readyConfig C) (e: raisedEvent) (P: raisedAsImported M e) rconf' reList,
  @macroStepReadyFinal' M C e (length (dom (controlstate C))) = Some (rconf',reList) ->
  exists rconf fconf, chainMergeTrans C rconf fconf e rconf' reList.
Proof.
  unfold chainMergeTrans, macroStepReadyFinal'; intros.
  remember (macroNStep (length (dom (controlstate C)))
                       (finalConfig_dec (configTransitionFunc C e))).
  destruct o; [|inversion H].
  inversion H; subst; clear H.
  rename c into fconf.
  eexists (configTransitionFunc C e), fconf.
  remember (configTransitionFunc C e) as c.
  assert (configTrans C c).
    apply configTransInitial with (e:=e);auto.
  split; auto.
  unfold configTrans in H.
  repeat match goal with [ H: _ /\ _ |- _ ] => destruct H end.
  pose proof chainMergeStep'.
  unfold configTransitionFunc in Heqc.
  assert (controlstate C = controlstate c).
    rewrite Heqc.
    simpl;auto.
  rewrite H3 in Heqo.
  remember Heqo.
  clear Heqe0.
  apply H2 with (e:=e) in Heqo;auto.
    destruct Heqo;auto.
      remember Cor.
      clear Heqr.
      unfold readyConfig in r.
      destruct r.
      destruct H5.
      destruct correct_mon.
      rewrite <- cs_consist in H9.
      unfold configTransitionFunc in Heqc.
      assert (controlstate C = controlstate c).
        rewrite Heqc.
        simpl;auto. 
      apply marcoNStepFinish in e0;auto.
      rewrite <- H4 in e0.
      apply InitialNotStuckNorError in H0;auto.
      contradiction.
    split;auto.
    apply marcoNStepFinish in e0;auto. split;auto.

    split;auto.
    unfold configTransRev.
    split.
    unfold configStEq.
    split;auto.
    unfold  readyConfig. split;auto.
    assert (correct_configuration fconf).
      unfold WellFormed in W.
       repeat match goal with
                | [ H: _ /\ _ |- _ ] => destruct H

              end.
       destruct H8.
         repeat match goal with
                | [ H: _ /\ _ |- _ ] => destruct H

              end.
      apply termL5' in H4;auto.
      unfold raisedAsImported in P. destruct P;auto.
    destruct H5.
    split;simpl;auto.
    - constructor.
    - unfold scenarioInclusion.
      unfold incl; simpl; intros.
      inversion H5.
    - intros; inversion H5.
    - intros; inversion H5.
    - intros; inversion H5.
    - intros;inversion H5. 
    - intros. inversion H5.
    - intros. inversion H5. 
    -rewrite Heqc; simpl.
      left; auto.
Qed.

Lemma ProcessEventRefined M (C : configuration M) (W : WellFormed M)
      (Cor:readyConfig C) (e: raisedEvent) (P : raisedAsImported M e) :
 refine { p : configuration M * list raisedEvent
        | exists conf' econf, chainMergeTrans C conf' econf e (fst p) (snd p) }
        (ret (macroStepReadyFinal W Cor P
                                   (length (dom (controlstate C))))).
Proof.
  refine pick val ((macroStepReadyFinal  W Cor P (length (dom (controlstate C))))).
  finish honing.
  remember ((macroStepReadyFinal  W Cor P (length (dom (controlstate C))))).

  pose proof macroStepReadyFinalLemma.
  assert (Some (macroStepReadyFinal W Cor P (length (dom (controlstate C)))) = @macroStepReadyFinal' M C e  (length (dom (controlstate C)))).
  symmetry;auto.

  destruct p. simpl.

  pose proof ProcessEventRefinedLemma.

  apply H1 ;auto.

  rewrite <- Heqp in H0.
  symmetry;auto.
Qed.

Lemma macroStepReadyFinal_yields_readyConfig
      M (C : configuration M) (W : WellFormed M)
      (Cor : readyConfig C) (e : raisedEvent)
      (P : raisedAsImported M e) :
  readyConfig (fst (macroStepReadyFinal W Cor P (length (dom (controlstate C))))).
Proof.
  remember (macroStepReadyFinal W Cor P (length (dom (controlstate C)))).
  pose proof macroStepReadyFinalLemma.
  assert (macroStepReadyFinal' C e (length (dom (controlstate C))) = Some p).
  rewrite  Heqp.
  apply H.
  destruct p.
  simpl.
  SearchAbout macroStepReadyFinal'.
  apply ProcessEventRefinedLemma in H0;auto.
  destruct H0. destruct H0.
  unfold chainMergeTrans in H0.
  repeat match goal with
                | [ H: _ /\ _ |- _ ] => destruct H

         end.
  unfold   configTransRev in H3. destruct H3;auto. 
Qed.                       

Require Import
  Coq.Strings.String
  Fiat.Computation.IfDec
  Fiat.Computation.Decidable
  Fiat.ADTInduction.

Section Specification.

Variable M : monitor.

Definition newS := "new"%string.
Definition processEventS := "processEvent"%string.

Definition confSpec : ADT _ := Def ADT {
  rep := configuration M,

  Def Constructor0 newS : rep := { c : configuration M | readyConfig c },,

  Def Method1 processEventS (r : rep) (e: raisedEvent | raisedAsImported  M e) :
      rep * list raisedEvent :=
    (* Processing an event means: taking a configuration and an event, and
       producing another configuration and list of events, such that every
       event that could result from the transition between those two
       configurations is present in that list. The [chainMerge] guarantees
       that the subsequent configuration is a ready one. *)
    { p : configuration M * list raisedEvent
    | exists conf' econf,
        chainMergeTrans r conf' econf (` e) (fst p) (snd p) }
}%ADTParsing.

Ltac destruct_computations :=
  repeat match goal with
  | [ H : computes_to (Bind _ _) _     |- _ ] =>
    let H0 := fresh "H0" in
    apply Bind_inv in H; destruct H as [? [? H0]]
  | [ H : computes_to (Pick _) _       |- _ ] =>
    apply Pick_inv in H
  | [ H : computes_to (Return _) _     |- _ ] =>
    apply Return_inv in H; subst
  | [ H : computes_to _ _ |- _ ] =>
    let H0 := fresh "H0" in
    first [ apply Bind_inv in H; destruct H as [? [? H0]]
          | apply Pick_inv in H
          | apply Return_inv in H; subst ]
  end.

Ltac inspect :=
  repeat (destruct_computations; simpl in *).

Ltac attack_ADT r :=
  pattern r; apply ADT_ind; try eassumption;
  intro midx;
  match goal with
  | [ cidx : ConstructorIndex _ |- _ ] => pattern cidx
  | [ midx : MethodIndex _ |- _ ] => pattern midx
  end;
  apply IterateBoundedIndex.Iterate_Ensemble_equiv';
  repeat apply IterateBoundedIndex.Build_prim_and;
  try solve [constructor];
  simpl in *; intros;
  simpl in *; destruct_ex; split_and;
  repeat inspect; injections; simpl in *;
  inspect; eauto; intros.

Lemma alwaysReady : forall (r : Rep confSpec), fromADT _ r ->
  readyConfig r.
Proof.
  intros.
  attack_ADT r.
  destruct x; simpl in *;
  destruct_computations; simpl in *.
  destruct_ex.
  inversion H0; subst.
  unfold chainMergeTrans in *.
  unfold configTransRev in *.
  repeat match goal with [ H: _ /\ _ |- _ ] => destruct H end.
  assumption.
Qed.

End Specification.

Section Implementation.

Variable M : object.
Hypothesis M_wf : WellFormed M.
Variable initial_conf : configuration M.
Variable initial_conf_ready : readyConfig initial_conf.

Fixpoint listInBool {A} (dec_A: (forall x y:A, {x = y} + {x <> y})) (la: list A) (a : A) : bool :=
  match la with
  | nil => false
  | a'::la' => if dec_A a' a then
                 true
               else
                 listInBool dec_A la' a
 end.


Lemma listInBool_correct: forall A dec_A la a,
    @listInBool A dec_A la a <->
    In a la.
Proof.
  intros.
  generalize dependent a.
  induction la;intros. split.
  intros.

  simpl in H.   inversion H.
  simpl. intros. inversion H.
  split.   intros. simpl in H.
  destruct ( dec_A a a0). left;auto.
  right;auto.
  destruct IHla with (a:=a0);auto.
  intros.
  inversion H. subst.
  destruct H.
  simpl. destruct (dec_A a0 a0). auto. contradiction.
  apply IHla in H.
  simpl.
  destruct (dec_A a0 a0). auto. contradiction.
  simpl.
  destruct (dec_A a a0). simpl in H. destruct H;auto.
  apply IHla;auto.
Qed.



Fixpoint sceCheckBool sceList e: bool :=
  match sceList with
  | nil => false
  | sce::sceList' => if listInBool event_definition_dec (alphabet sce) (eventDefinition e) then
                       true
                     else
                       sceCheckBool sceList' e
  end.


Lemma sceCheckBool_correct: forall sceList e,
    sceCheckBool sceList e ->
     (exists sce : scenario,
      In sce sceList /\ In (eventDefinition e) (alphabet sce)).
Proof.
  intro sceList;induction sceList.
  intros. simpl in H. inversion H.
  intros.
  simpl in H.

  remember (listInBool event_definition_dec (alphabet a) (eventDefinition e)).
  destruct b;inversion H.
  exists a. split. left;auto.
  symmetry in Heqb.
  apply listInBool_correct with (dec_A:=event_definition_dec);auto.
  apply IHsceList in H.
  destruct H. exists x.
  split. right;auto. destruct H;auto. destruct H;auto.

Qed.



Lemma sceCheckBool_correct_rev: forall sceList e,
     (exists sce : scenario,
         In sce sceList /\ In (eventDefinition e) (alphabet sce)) ->
      sceCheckBool sceList e.
Proof.

  intro sceList;induction sceList.
  intros. simpl in H. inversion H.
  inversion H0.   inversion H1. intros.
  simpl in H.
  simpl.

  remember (listInBool event_definition_dec (alphabet a) (eventDefinition e)).
  symmetry in Heqb.

  destruct b.   auto.

  apply IHsceList.
  destruct H. destruct H.
  destruct H. subst.
  assert (listInBool event_definition_dec (alphabet x) (eventDefinition e) = true).
  apply listInBool_correct. auto.  rewrite H in Heqb. inversion Heqb.
  exists x. split;auto.

Qed.

Lemma sceCheckBool_correct_all: forall sceList e,
     (exists sce : scenario,
         In sce sceList /\ In (eventDefinition e) (alphabet sce)) <->
      sceCheckBool sceList e.
Proof.
  intros.
  split.
  apply sceCheckBool_correct_rev.
  apply sceCheckBool_correct.
Qed.

Definition raisedAsImported_computation  (mon: object) (e: raisedEvent): bool := andb (andb (andb (parameterMatchFunc (eventArguments e) (eventParams (eventDefinition e)))
 (importEventBool (eventDefinition e))) (listInBool event_definition_dec (events mon) (eventDefinition e)))
                                                                                      (sceCheckBool (scenarios mon) e).

Lemma raisedAsImported_computation_correct: forall e mon,
    raisedAsImported_computation  mon e= true ->
    raisedAsImported mon e.
Proof.
  intros.
  unfold raisedAsImported_computation in H.
  remember ((parameterMatchFunc (eventArguments e) (eventParams (eventDefinition e)))).
  destruct b. Focus 2. simpl in H. inversion H.
  remember (importEventBool (eventDefinition e)).
  destruct b. Focus 2. simpl in H. inversion H.
  remember (listInBool event_definition_dec (events mon) (eventDefinition e) ).
  destruct b. Focus 2. simpl in H;inversion H.
  remember (sceCheckBool (scenarios mon) e).
  destruct b. Focus 2. simpl in H;inversion H.
  split.
  unfold  wellFormedRaisedEvent.
  rewrite parameterMatch_refl;auto.
  split.
  unfold   importedEvent.
  unfold importEventBool in Heqb0.
  destruct ((eventKind (eventDefinition e)));simpl in Heqb0. inversion Heqb0. auto. inversion Heqb0.
  Check sceCheckBool_correct. Check listInBool_correct. 
  Search  sceCheckBool.
  symmetry in Heqb2.   apply sceCheckBool_correct in Heqb2.
  destruct Heqb2. destruct H0.
  split;auto.  exists x;auto. 
  apply listInBool_correct with (dec_A := event_definition_dec);auto.
 
Qed.

Lemma raisedAsImported_computation_correct_rev: forall e mon,
    raisedAsImported mon e ->
 raisedAsImported_computation  mon e = true.
Proof.
  intros.
  unfold raisedAsImported in H.
   repeat match goal with
            | [ H: _ /\ _ |- _ ] => destruct H

          end.
   unfold    wellFormedRaisedEvent in H.
   rewrite parameterMatch_refl in H.
   unfold  raisedAsImported_computation.
   rewrite H.
   unfold importEventBool.
   unfold importedEvent in H0.

   remember (eventKind (eventDefinition e)).
   destruct e0; inversion H0.
   simpl.    destruct (eventKind_dec Imported Imported).
   Focus 2. contradiction.
   assert (listInBool event_definition_dec (events mon) (eventDefinition e) = true).

   apply   listInBool_correct;auto. rewrite H3.
   simpl. apply sceCheckBool_correct_rev;auto.

Qed.

Lemma raisedAsImported_computation_correct_all: forall e mon,
    raisedAsImported_computation  mon e= true
  <-> raisedAsImported mon e.

Proof.
  intros;split.
  apply raisedAsImported_computation_correct;auto.
  apply raisedAsImported_computation_correct_rev;auto.

Qed.


Program Instance raisedAsImported_Decidable d :
  Decidable.Decidable (raisedAsImported  M d).
Obligation 1.

apply (raisedAsImported_computation  M d).

Defined.
Obligation 2.
apply raisedAsImported_computation_correct_all.
Defined.


Lemma If_Then_Else_fst : forall p A B (a b : A * B),
  fst (If p Then a Else b) = If p Then (fst a) Else (fst b).
Proof. intros; destruct p; trivial. Qed.

Lemma If_Then_Else_snd : forall p A B (a b : A * B),
  snd (If p Then a Else b) = If p Then (snd a) Else (snd b).
Proof. intros; destruct p; trivial. Qed.

Lemma If_Then_Else_pair : forall p A (a b : A) B (c d : B),
  (If p Then a Else b, If p Then c Else d)
    = If p Then (a, c) Else (b, d).
Proof. intros; destruct p; trivial. Qed.

Lemma refine_IfDec_Then_Else_Bind {A B}
  : forall i (H : Decidable.Decidable i) (t e : Comp A) (b : A -> Comp B),
    refine (a <- IfDec i Then t Else e; b a)
           (IfDec i Then (a <- t;
                       b a)
               Else (a <- e;
                     b a)).
Proof.
  intros.
  rewrite !refine_IfDec_decides; simpl.
  destruct H.
  destruct Decidable_witness; simpl; reflexivity.
Qed.

Lemma refine_ifdec :
  forall (A : Type) (c : Comp A) (P : Prop) (H : Decidable.Decidable P)
         (ta ea : Comp A),
  (P -> refine ta c) ->
  (~ P -> refine ea c) -> refine (IfDec P Then ta Else ea) c.
Proof.
  intros.
  rewrite refine_IfDec_decides; simpl.
  destruct H.
  destruct Decidable_witness; simpl.
    apply H0, Decidable_spec; reflexivity.
  apply H1.
  intro.
  apply Decidable_spec in H.
  discriminate.
Defined.

Lemma refine_IfDec_Under_Bind {B} P (P_dec : Decidable P)
  : forall (tb eb : Comp B) tb' eb',
    (forall (p : P), refine tb (tb' p))
    -> refine eb eb'
    -> refine (IfDec P Then tb Else eb)
              ((if Decidable_witness as b return Decidable_witness = b -> _
                then fun H => tb' (Decidable_sound P _ H)
                else fun _ => eb') eq_refl).
Proof.
  unfold IfDec_Then_Else; intros.
  computes_to_econstructor.
  eapply PickComputes; apply Decidable_witness_decides.
  revert v H1;
    generalize (Decidable_sound P P_dec) (Decidable_complete_alt P P_dec).
  destruct Decidable_witness; intros; eauto.
  eapply H; eauto.
Qed.


Theorem sharpened_confSpec : FullySharpened (confSpec M).
Proof.
  start sharpening ADT.

  (* For now, simply use the same representation for monitors that was used in
     the specification, even though there may be more efficient choices. *)
  hone representation using
       (fun (or : configuration M)
            (nr : { r : configuration M | readyConfig r }) =>
          or = ` nr).

  {
    refine pick val initial_conf.
      simplify with monad laws; simpl.
      refine pick val (exist _ initial_conf initial_conf_ready).
        finish honing.
      reflexivity.
    exact initial_conf_ready.
  }

  {
    subst.

    
    rewrite ProcessEventRefined
      with (W:=M_wf) (Cor:=proj2_sig r_n) (e:=` d) (P:=proj2_sig d).
    simplify with monad laws; simpl.
    refine pick val
           (exist (fun r => readyConfig r)
                  (fst (macroStepReadyFinal
                          M_wf (proj2_sig r_n)
                          (proj2_sig d)
                          (List.length (dom (controlstate (` r_n))))))
                  (macroStepReadyFinal_yields_readyConfig
                     M_wf (proj2_sig r_n) (proj2_sig d)
                     (*(List.length (dom (controlstate (` r_n))))*))).
      simplify with monad laws; simpl.
      finish honing.
    reflexivity.
  }


  finish_SharpeningADT_WithoutDelegation.
Defined.

Check sharpened_confSpec.
Check FullySharpened. 
Check ComputationalADT.cRep. 

Definition program := Eval simpl in projT1 sharpened_confSpec.
Check program.
Check ComputationalADT.cRep. 
Print newS.
Print CallConstructor. 
Definition monitor_new : ComputationalADT.cRep program :=
  Eval vm_compute in CallConstructor program newS.
Check monitor_new. 
Definition monitor_processEvent (r : ComputationalADT.cRep program)
           (e: raisedEvent | raisedAsImported M e) :
  ComputationalADT.cRep program * list raisedEvent :=
  Eval simpl in CallMethod program processEventS r e.
Check monitor_processEvent.
Check program. 

End Implementation.

Extraction Language Haskell.

Unset Extraction KeepSingleton.
Set Extraction AutoInline.
Set Extraction Optimize.
Set Extraction AccessOpaque.

Extraction "SMEDL.hs" monitor_new monitor_processEvent.
Locate incl_dec. 
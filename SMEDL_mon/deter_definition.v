(*Definitions for determinism*)
(*check whether a monitor is deterministic*)
(*Predicate for determinism: deterProp_final'*)
Require Import Coq.Lists.List.

Require Export smedlDef.SmedlAST_submission.
Require Export smedlDef.semantic_rules.
Require Export wellFormScenario.
Require Export wellForm.
Require Import Coq.omega.Omega.
Require Import Fiat.ADT Fiat.ADTNotation.
Require Import
        Coq.Strings.String.
Require Import Coq.Sorting.Permutation.





(*relation between two configuration lists*)
(*similar to permutation, but use equivConf instead of equal*)
Inductive confEquivList M : list (configuration M) -> list (configuration M) -> Prop :=
| confEqBasic: confEquivList nil nil 
| confEqSkip: forall conf conf' l l', equivConf conf conf' -> confEquivList l l'
                -> confEquivList (conf::l) (conf'::l')
| confEqSwap: forall conf1 conf1' conf2 conf2' l l', equivConf conf1 conf1' -> equivConf conf2 conf2' -> confEquivList l l'
                     -> confEquivList (conf1::conf2::l) (conf2'::conf1'::l')
| confEqTrans: forall l1 l2 l3, confEquivList l1 l2 -> confEquivList l2 l3 -> confEquivList l1 l3.


Definition updateVarEv M e v : Prop :=
exists sce, In sce (scenarioUpdateVar (scenarios M) v) /\ triggerSce M e sce. 

Definition usedVarEv M e v : Prop :=
exists sce, In sce (scenarioUsedVar (scenarios M) v) /\ triggerSce M e sce. 

Definition raisedEv M e ev : Prop :=
exists sce, In sce (scenarioRaise (scenarios M) ev) /\ triggerSce M e sce. 



Definition raiseAction (mon: object) (e:event_definition) (ev1 ev2: event_definition) :=
    (exists (sce:scenario), triggerSce mon e sce /\ In sce (scenarios mon) /\                
                            (exists tr act exprs, In tr (getTransitionsOfScenario sce) /\ In act (transitionIntoBasicActionList (stepActions tr)) /\ act = RaiseStmt (eventId ev2) exprs /\  ev1 = (event (stepEvent tr)))).



Inductive staticEventLeadTo' (mon: object) (e: event_definition) : event_definition -> event_definition -> Prop :=
| staticLeadBasicCase' : forall ev1 ev2,
      raiseAction mon e ev1 ev2 ->
                staticEventLeadTo' mon e ev1 ev2
| staticLeadTransit' : forall ev1 ev2 ev3, staticEventLeadTo' mon e ev1 ev2 ->               
            raiseAction mon e ev2 ev3     -> staticEventLeadTo' mon e ev1 ev3.




(*e1 e2 may be raised by the same imported event e and e1 and e2 cannot trigger each other*)
Definition deterProp' (m: object): Prop :=
  (forall v1 v2 e1 e2 , (exists e, In e (events m) /\ eventKind e = Imported /\ staticEventLeadTo' m e e e1 /\ staticEventLeadTo' m e e e2 /\ ~ (staticEventLeadTo' m e e1 e2) /\  ~ (staticEventLeadTo' m e e2 e1)  ) ->  In e2 (events m) -> In e1 (events m) -> In v1 (dom (dsmon m)) -> In v2 (dom (dsmon m)) -> e1 <> e2 ->
                        updateVarEv m e1 v1 -> updateVarEv m e2 v2 -> v1 <> v2  )
  /\
  (forall v1 v2 e1 e2 , (exists e, In e (events m) /\ eventKind e = Imported /\ staticEventLeadTo' m e e e1 /\ staticEventLeadTo' m e e e2 /\ ~ (staticEventLeadTo' m e e1 e2) /\  ~ (staticEventLeadTo' m e e2 e1)  ) -> In e2 (events m) -> In e1 (events m) -> In v1 (dom (dsmon m)) -> In v2 (dom (dsmon m)) -> e1 <> e2 ->
                        updateVarEv m e1 v1 -> usedVarEv m e2 v2 -> v1 <> v2  )
  /\
  (forall v1 v2 e1 e2 , (exists e, In e (events m) /\ eventKind e = Imported /\ staticEventLeadTo' m e e e1 /\ staticEventLeadTo' m e e e2 /\ ~ (staticEventLeadTo' m e e1 e2) /\  ~ (staticEventLeadTo' m e e2 e1)  ) -> In e2 (events m) -> In e1 (events m) -> In v1 (dom (dsmon m)) -> In v2 (dom (dsmon m)) -> e1 <> e2 ->
                        usedVarEv m e1 v1 -> updateVarEv m e2 v2 -> v1 <> v2  )
  /\
  ( forall ev1 ev2 e1 e2: event_definition,
   (exists e, In e (events m) /\ eventKind e = Imported /\ staticEventLeadTo' m e e e1 /\ staticEventLeadTo' m e e e2 /\ ~ (staticEventLeadTo' m e e1 e2) /\  ~ (staticEventLeadTo' m e e2 e1)  ) ->
  In ev1 (events m) ->
  In ev2 (events m) ->
  In e2 (events m) -> In e1 (events m) ->
  e1 <> e2 -> raisedEv m e1 ev1 -> raisedEv m e2 ev2 -> eventKind ev1 = Internal -> eventKind ev2 = Internal -> ev1 <> ev2)
 /\
 (forall  (sce1 sce2 : scenario)  e1 e2,
  (exists e, In e (events m) /\ eventKind e = Imported /\ staticEventLeadTo' m e e e1 /\ staticEventLeadTo' m e e e2 /\ ~ (staticEventLeadTo' m e e1 e2) /\  ~ (staticEventLeadTo' m e e2 e1)  ) ->
  e1 <> e2 ->
  In sce1 (scenarios m) ->
  In sce2 (scenarios m) ->
  In e1 (alphabet sce1) ->
  In e2 (alphabet sce2) -> sce1 <> sce2)
.





(*triggering events of transitions are in the alphabet of the scenario*)
(*not stated in the paper*)
Definition traceAlphabetIn (M: monitor) : Prop :=
  forall sce stp,
    In sce (scenarios M) ->
    In stp (traces sce) ->
    In (event (stepEvent stp)) (alphabet sce). 

Print triggerSce.

(*(exprs : list expr),
          In (sce', ev) (sceEventMap conf') /\
          In tr (getTransitionsOfScenario sce') /\
          In act (transitionIntoBasicActionList (stepActions tr)) /\
          act = RaiseStmt (eventId x) exprs /\ ev = event (stepEvent tr))*)

(*events raised are either internal or exported events*)
(*not stated in the paper*)
Definition raiseInternal (M: monitor) : Prop :=
  forall sce  e tr exprs,
    In e (events M) ->
    In sce (scenarios M) ->
    In tr (traces sce) ->
    In (RaiseStmt (eventId e) exprs) (transitionIntoBasicActionList (stepActions tr)) ->
    (eventKind e = Internal \/ eventKind e = Exported).


(*enhanced version of noMultAlphabet' defined in WellFormed*)
(*In the paper, this predicate is used instead of noMultAlphabet' when defining WellFormed*)
Definition noMultAlphabet'' := 
fun mon : object =>
forall e e1 e2 : event_definition,
In e (events mon) ->
staticEventLeadTo mon e e1 ->
staticEventLeadTo mon e e2 ->
e1 <> e2 ->
~ (exists sce : scenario, In sce (scenarios mon) /\ triggerSce mon e1 sce /\ triggerSce mon e2 sce). 

Print noMultAlphabet.
Print importedNoCommonAlphabet'.

(*enhanced version of importedNoCommonAlphabet' defined in WellFormed*)
(*In the paper, this predicate is used instead of importedNoCommonAlphabet' when defining WellFormed*)
(*Definition importedNoCommonAlphabet'' := 
fun mon : object =>
forall e1 e2 : event_definition,
In e1 (events mon) ->
eventKind e1 = Imported ->
staticEventLeadTo mon e1 e2 ->
e1 <> e2 ->
~ (exists sce : scenario, In sce (scenarios mon) /\ triggerSce mon e1 sce /\ triggerSce mon e2 sce).*)


Definition importedNoCommonAlphabet'' := 
fun mon : object =>
forall e1 e2 : event_definition,
In e1 (events mon) ->
eventKind e1 = Imported ->
staticEventLeadTo mon e1 e2 ->
e1 <> e2 ->
~ (exists sce : scenario, In sce (scenarios mon) /\ In e1 (alphabet sce) /\ triggerSce mon e2 sce).


Lemma staticEventTwo: forall mon e e1 e2,
    staticEventLeadTo' mon e e1 e2 ->
    staticEventLeadTo mon  e1 e2.
Proof.
  intros.
  induction H.
  unfold raiseAction in H.
  destruct H.
  destruct H.
  Print staticEventLeadTo.
  apply   staticLeadBasicCase;auto.
  exists x;auto.
  Print  staticEventLeadTo.   
  apply staticLeadTransit with (ev2:=ev2);auto.
  apply   staticLeadBasicCase;auto.
  unfold raiseAction in H0.
  destruct H0.
  destruct H0.
  exists x;auto.
Qed.


Lemma triggerSceScenarios: forall m e x,
    triggerSce m e x ->
    In x (scenarios m).
Proof.
  intros.
  induction H.
  -  auto.
  -  auto. 
Qed.

Lemma deterRaiseNoDup: forall m,
    noMultAlphabet'' m ->
    noDupRaise'' m ->
    raiseInternal m ->
    (( forall ev1 ev2 e1 e2: event_definition,
   (exists e, In e (events m) /\ eventKind e = Imported /\ staticEventLeadTo' m e e e1 /\ staticEventLeadTo' m e e e2 /\ ~ (staticEventLeadTo' m e e1 e2) /\  ~ (staticEventLeadTo' m e e2 e1)  ) ->
  In ev1 (events m) ->
  In ev2 (events m) ->
  In e2 (events m) -> In e1 (events m) -> 
  e1 <> e2 -> eventKind ev1 = Internal -> eventKind ev2 = Internal -> raisedEv m e1 ev1 -> raisedEv m e2 ev2 -> ev1 <> ev2)).
Proof.
  intros m H H0 H1. rename H1 into rim. intros. 
  unfold noMultAlphabet'' in H. 
  unfold noDupRaise'' in H0.
   unfold raisedEv in *. 
   repeat match goal with
            | [ H: _ /\ _ |- _ ] => destruct H
            | [ H: exists _, _ |- _] => destruct H
                     end.  
   
   unfold not;intros.
   subst.    
   assert (x = x0 \/ x <> x0).
   apply excluded_middle.    
   destruct H18.
   subst.

   apply H with (e:=x1) (e1:=e1) (e2:=e2);auto.
     apply staticEventTwo with (e:=x1);auto.
   apply staticEventTwo with (e:=x1);auto.
   exists x0;split;auto.
   apply triggerSceScenarios with (e:=e1);auto.
   apply H0 in H2.
   destruct H2.

   unfold scenarioRaise in H9.
      

   apply H2 with (sce1:=x0) (sce2:=x) in H7;auto.
   apply H7.
   exists x1.  split;auto.
   split.
   apply induction_ts with (e2:=e1);auto.    
   apply staticEventTwo with (e:=x1);auto.
   apply induction_ts with (e2:=e2);auto.
   apply staticEventTwo with (e:=x1);auto.  
Qed.


    

Lemma deter_noMulti: forall m,
    noMultAlphabet'' m ->
    (forall  (sce1 sce2 : scenario)  e1 e2,
  (exists e, In e (events m) /\ eventKind e = Imported /\ staticEventLeadTo' m e e e1 /\ staticEventLeadTo' m e e e2 /\ ~ (staticEventLeadTo' m e e1 e2) /\  ~ (staticEventLeadTo' m e e2 e1)  ) ->
  e1 <> e2 ->
  In sce1 (scenarios m) ->
  In sce2 (scenarios m) ->
  In e1 (alphabet sce1) ->
  In e2 (alphabet sce2) -> sce1 <> sce2).
Proof.
  intros.
  unfold  noMultAlphabet'' in H.
    repeat match goal with
            | [ H: _ /\ _ |- _ ] => destruct H
            | [ H: exists _, _ |- _] => destruct H
                     end.    
    unfold not;intros.
   subst.     
   unfold not in H.
   apply H with (e:=x) (e1:=e1) (e2:=e2);auto.    
   Focus 3. 
   exists sce2.   split;auto.
   split;apply basic_ts;auto.
   apply staticEventTwo with (e:=x);auto.
   apply staticEventTwo with (e:=x);auto.
Qed.

   

Definition deter_prop (m: object): Prop := deterProp' m /\  traceAlphabetIn m /\
     noMultAlphabet'' m /\
     importedNoCommonAlphabet'' m /\
     raiseInternal m.

(*e1 e2 may be raised by the same imported event e and e1 and e2 cannot trigger each other*)
Definition deterProp_final' (m: object): Prop :=
  (forall v1 v2 e1 e2 , (exists e, In e (events m) /\ eventKind e = Imported /\ staticEventLeadTo' m e e e1 /\ staticEventLeadTo' m e e e2 /\ ~ (staticEventLeadTo' m e e1 e2) /\  ~ (staticEventLeadTo' m e e2 e1)  ) ->  In e2 (events m) -> In e1 (events m) -> In v1 (dom (dsmon m)) -> In v2 (dom (dsmon m)) -> e1 <> e2 ->
                        updateVarEv m e1 v1 -> updateVarEv m e2 v2 -> v1 <> v2  )
  /\
  (forall v1 v2 e1 e2 , (exists e, In e (events m) /\ eventKind e = Imported /\ staticEventLeadTo' m e e e1 /\ staticEventLeadTo' m e e e2 /\ ~ (staticEventLeadTo' m e e1 e2) /\  ~ (staticEventLeadTo' m e e2 e1)  ) -> In e2 (events m) -> In e1 (events m) -> In v1 (dom (dsmon m)) -> In v2 (dom (dsmon m)) -> e1 <> e2 ->
                        updateVarEv m e1 v1 -> usedVarEv m e2 v2 -> v1 <> v2  )
  /\
  (forall v1 v2 e1 e2 , (exists e, In e (events m) /\ eventKind e = Imported /\ staticEventLeadTo' m e e e1 /\ staticEventLeadTo' m e e e2 /\ ~ (staticEventLeadTo' m e e1 e2) /\  ~ (staticEventLeadTo' m e e2 e1)  ) -> In e2 (events m) -> In e1 (events m) -> In v1 (dom (dsmon m)) -> In v2 (dom (dsmon m)) -> e1 <> e2 ->
                        usedVarEv m e1 v1 -> updateVarEv m e2 v2 -> v1 <> v2  )
.



Definition deter_prop_final (m: object): Prop := deterProp_final' m /\  traceAlphabetIn m /\
     noMultAlphabet'' m /\
     importedNoCommonAlphabet'' m /\
     raiseInternal m.

Lemma deter_prop_final_impl: forall m,
     noDupRaise'' m -> 
    deter_prop_final m ->
    deter_prop m. 
Proof.
  intros.
  unfold  deter_prop_final in *;unfold deter_prop;split;intuition;auto.
 
  unfold deterProp_final' in H1.
      repeat match goal with
            | [ H: _ /\ _ |- _ ] => destruct H
            | [ H: exists _, _ |- _] => destruct H
             end.
      repeat(split;auto).
      pose proof deterRaiseNoDup.
      intros.
   apply H7 with (m:=m) (e1:=e1) (e2:=e2);auto.       
   intros.
   apply deter_noMulti with (m:=m) (e1:=e1) (e2:=e2);auto.    
Qed.


Lemma noMultIn: forall m,
    noMultAlphabet'' m -> noMultAlphabet' m.
Proof. 
  intros.
  unfold noMultAlphabet'' in H. unfold noMultAlphabet';intros.
  assert (~
            (exists sce : scenario, In sce (scenarios m) /\ triggerSce m e1 sce /\ triggerSce m e2 sce)).
  apply H with (e:=e);auto.
  unfold not;intros.
  unfold not in H4;apply H4.
   repeat match goal with
        | [ H: _ /\ _ |- _ ] => destruct H
        | [ H: exists _, _ |- _] => destruct H
          end. 
   exists x.
   split;auto.
   split;apply basic_ts;auto.
Qed.

Lemma noMultImportedIn: forall m,
    importedNoCommonAlphabet'' m -> importedNoCommonAlphabet' m.
Proof. 
  intros.
  unfold importedNoCommonAlphabet'' in H. unfold importedNoCommonAlphabet';intros.
  assert (~
            (exists sce : scenario, In sce (scenarios m) /\ In e1 (alphabet sce) /\ triggerSce m e2 sce)).
  apply H ;auto.
  unfold not;intros.
  unfold not in H4;apply H4.
   repeat match goal with
        | [ H: _ /\ _ |- _ ] => destruct H
        | [ H: exists _, _ |- _] => destruct H
          end. 
   exists x.
   split;auto.
  split.    auto. apply basic_ts;auto.
Qed.

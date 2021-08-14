(*Proof determinism*)
(*main theorem:  deterministicMacroStepChainMerge*)
Require Import Coq.Lists.List.

Require Export smedlDef.SmedlAST_submission.
Require Export smedlDef.semantic_rules.
Require Export wellFormScenario.
Require Export wellForm.
Require Export smedlDef.smedl_common_lemmas.
Require Export aux_monitor.
Require Export well_decision_proc. 
Require Import Coq.omega.Omega.
Require Export Refinement.
Require Export deter_definition.
Require Export Refinement. 
Require Import Fiat.ADT Fiat.ADTNotation.
Require Import
        Coq.Strings.String.
Require Import Coq.Sorting.Permutation.






Lemma confEquivList_length_eq: forall M  (l l' : list (configuration M)),
 confEquivList  l l' -> 
List.length l = List.length l'.
Proof.
intros. induction H.
- auto.
- Print confEquivList. simpl. f_equal. auto.
- intros. simpl. f_equal. f_equal. auto.
- rewrite  IHconfEquivList1. auto.
Qed.      

Lemma confEquivList_sym: forall M  (l l' : list (configuration M)),
confEquivList l l' ->
confEquivList l' l.
Proof. intros. 
induction H. 
- constructor. 
- Print confEquivList.  apply confEqSkip. apply equivConf_Sym. auto. auto.
-   Print confEquivList. apply  confEqSwap. apply equivConf_Sym. auto.
apply equivConf_Sym. auto. auto.
-Print confEquivList. eapply confEqTrans. apply IHconfEquivList2. auto.
Qed.       

Lemma confEquivList_refl: forall M (l: list (configuration M)),
confEquivList l l.
Proof. intros. 
induction l;constructor. 
- apply equivConf_Refl.  
- auto.  
Qed.  

Lemma confEquivList_cons_nil: forall M  x (l: list (configuration M)),
~ confEquivList nil (x::l) .
Proof.
intros. unfold not. intros. 
apply confEquivList_length_eq in H. inversion H. 
Qed.       

Lemma confEquivListTransitivity: forall M conf1 (x x0 : list (configuration M)),
confEquivList conf1 x ->
confEquivList x x0 ->
confEquivList conf1 x0. 
Proof.
intros. Print confEquivList.
eapply confEqTrans.
apply H. apply H0.   
Qed.

Check getStep'. 
     
Lemma getStepEquiv: forall M (conf conf':configuration M) sce e, 
equivConf conf conf' ->
getStep'  conf sce e = getStep' conf' sce e.
Proof.
intros. unfold getStep'. unfold equivConf in H. destruct H. destruct H0. 
rewrite H0. auto.
Qed.  


Lemma equivConfSyncBasic: forall M (conf conf' conf1 conf2: configuration M) e sce,
    equivConf conf conf' ->
    Result conf1 = constructConfig sce e conf ->
    Result conf2 = constructConfig sce e conf' ->
     conf1 = conf2.
Proof.
  intros.
  unfold constructConfig in H0.
  unfold constructConfig in H1.
  unfold equivConf in H.
     repeat match goal with
            | [ H: _ /\ _ |- _ ] => destruct H

                     end.
     rewrite <- H2 in H1.
     remember (getScenarioState sce (controlstate conf)).
     destruct o;inversion H1;inversion H0. clear H11.
     remember (transEvMapFunc (stateEvDefInstanceMap M) (Some s, Some (eventDefinition e))). 
     destruct o;inversion H0;inversion H1.  clear H11;clear H12.
     rewrite <- H in H1. clear H10.
     remember (findEventInstance e (datastate conf) l ).
     destruct o;inversion H0;inversion H1. clear H11. clear H10.
     remember ( createValueEnv (eventArgs e0) (eventParams (eventDefinition e)) (eventArguments e)). 
     destruct e1;inversion H0;inversion H1.
     clear H11;clear H10.
     pose proof getStepEquiv.
     assert (getStep' conf sce e0 = getStep' conf' sce e0). 
     apply H9;auto.  repeat(split;auto).  rewrite <- H10 in H1.
     remember (getStep' conf sce e0).
     destruct o;inversion H0;inversion H1;subst.
     clear H13;clear H12.
     unfold  configTransition in H0;
       unfold configTransition in H1.
     rewrite <- H in H1.
     rewrite <- H2 in H1.
     remember ( execAction (extendValEnv (datastate conf) v, []) (stepActions s0)
             (filter
                (fun e : event_definition =>
                 match eventKind e with
                 | Internal => true
                 | Imported => false
                 | Exported => true
                 end) (events M))).
     destruct e1;inversion H0;inversion H1.
     clear H13. clear H12.
     rewrite <- H0 in H1. inversion H1;subst. auto. 
Qed.

Lemma equivConfSyncBasic': forall M (conf conf' conf1 : configuration M) e sce,
    equivConf conf conf' ->
    Result conf1 = constructConfig sce e conf ->
    (exists conf2, Result conf2 = constructConfig sce e conf').
Proof.
  intros.
  unfold constructConfig in *.
  remember H. clear Heqe0.  
  unfold equivConf in H.
    repeat match goal with
            | [ H: _ /\ _ |- _ ] => destruct H

                     end. 
  rewrite <- H1. remember ( getScenarioState sce (controlstate conf) ). 
  destruct o;inversion H0.
  remember ( transEvMapFunc (stateEvDefInstanceMap M) (Some s, Some (eventDefinition e))).
  destruct o;inversion H0.
  rewrite <- H.
  remember (findEventInstance e (datastate conf) l).
  destruct o;inversion H0.
  remember (createValueEnv (eventArgs e1) (eventParams (eventDefinition e)) (eventArguments e)).
  destruct e2;inversion H11.
  pose proof getStepEquiv.
  assert ( getStep' conf sce e1 = getStep' conf' sce e1).
  apply H8;auto. 
  rewrite <- H13;auto. 
       
  remember (getStep' conf sce e1 ).
  destruct o;inversion H0.
  clear H15.
  unfold  configTransition in H0.
  unfold  configTransition.    
  remember (execAction (extendValEnv (datastate conf) v, []) (stepActions s0)
             (filter
                (fun e : event_definition =>
                 match eventKind e with
                 | Internal => true
                 | Imported => false
                 | Exported => true
                 end) (events M))).
  destruct e2;inversion Heqe0.
  destruct v0.
  Focus 2.   inversion H0. 
  exists ({|
      datastate := updateDataState v0 (dom (datastate conf'));
      controlstate := updateControlState (controlstate conf') sce s0;
      raisedevents := filter
                        (fun re : raisedEvent =>
                         EventKind_beq (eventKind (eventDefinition re)) Internal) l0;
      exportedevents := filter
                          (fun re : raisedEvent =>
                           EventKind_beq (eventKind (eventDefinition re)) Exported) l0;
      finishedscenarios := [sce];
      sceEventMap := [(sce, eventDefinition e)] |}
         ).  auto.
Qed.





Lemma synchronyFinishedUnchanged: forall M (conf conf1: configuration M) e1 e2,
    correct_configuration conf ->
    synchrony conf conf1 e1 ->
    (forall sce1 sce2, In sce1  (scenarios M) -> In sce2  (scenarios M) ->   In (eventDefinition e1) (alphabet sce1) -> In (eventDefinition e2) (alphabet sce2) -> sce1 <> sce2) ->
    (forall sce, In sce (scenarios M) -> In (eventDefinition e2) (alphabet sce) -> ~ In sce (finishedscenarios conf) -> ~ In sce (finishedscenarios conf1) /\ getScenarioState sce (controlstate conf) = getScenarioState sce (controlstate conf1)). 
Proof.
  intros.
  remember H0. clear Heqs.  
  unfold synchrony in H0.
  destruct H0.
  SearchAbout finishedscenarios.
  unfold combineFunc in H5.
  remember (constructConfigList (dom (controlstate conf)) e1 conf).
  destruct e;inversion H5.
  destruct v.   inversion H5. clear H7.
  unfold constructConfigList in Heqe.
  assert ( ~ In (eventDefinition e1) (alphabet sce)).
  unfold not;intros.
  apply H1 with (sce1:=sce) in H3;auto.   
  assert (~ In sce ((filter
              (fun x : scenario => inList event_definition_dec (eventDefinition e1) (alphabet x))
              (filterList (finishedscenarios conf) (dom (controlstate conf)) scenario_dec)))).
  unfold not;intros.
  apply filter_In in H7.
  destruct H7.
  apply H6. SearchAbout inList. apply reverseinListLemma in H8. auto. 
  remember (innerCombineFunc'''' conf (c :: v)).
  destruct o;inversion H5.
  unfold removeEventFromConf;simpl.
  SearchAbout finishedscenarios. 
  assert (forall conf, In conf (c::v) -> ~ In sce (finishedscenarios conf)).
  intros.
  unfold not;intros.
  pose proof termL2.
  assert (exists sce : scenario, In sce (filter
              (fun x : scenario => inList event_definition_dec (eventDefinition e1) (alphabet x))
              (filterList (finishedscenarios conf) (dom (controlstate conf)) scenario_dec)) /\ Result conf0 = constructConfig sce e1 conf).
 apply H11 with (lst:=(c::v));auto.   
 destruct H12.
 destruct H12.
 SearchAbout finishedscenarios.
 apply termL3 in H13.
 rewrite H13 in H10. 
 destruct H10. Focus 2. inversion H10.
 subst.
 contradiction.
 split.
 unfold not;intros.
 SearchAbout finishedscenarios.
 pose proof finishedscenarioIn.
 apply H11 with (i:= sce) (c:=c0) in Heqe;auto.   
 SearchAbout filter.
 apply filterUniq;auto.
 SearchAbout filterList.
 destruct H.
  repeat match goal with
        | [ H: _ /\ _ |- _ ] => destruct H
        | [ H: exists _, _ |- _] => destruct H
            end.
 apply uniqListFilter;auto.
unfold incl;intros.   
apply filter_In in H12.              
destruct H12.
apply filterL2 in H12;auto. 
SearchAbout getScenarioState.
pose proof innerCombineFuncVarScenarioStateNoChange.
apply H10 with (v0:=c::v) (re:=e1) (sceList:=(filter
              (fun x : scenario => inList event_definition_dec (eventDefinition e1) (alphabet x))
              (filterList (finishedscenarios conf) (dom (controlstate conf)) scenario_dec)) );auto. unfold incl;intros.   
apply filter_In in H11.              
destruct H11.
apply filterL2 in H11;auto. 
            
Qed.




Lemma innerCombineRaisedPreservation: forall  M lst (c conf : configuration M)  re,
    In re (raisedevents conf) ->
    Some c = innerCombineFunc'''' conf lst ->
    In re (raisedevents c).
Proof.
  intros M lst;induction lst.
-  
  intros.  simpl in H0.
  inversion H0.
-  intros.
   simpl in H0.
   destruct lst.
      
   remember (mergeConfigFunc' conf conf a).
   destruct e;inversion H0.
   subst.
   SearchAbout mergeConfigFunc'.
   unfold   mergeConfigFunc' in Heqe.
   destruct (mergeDataStateFunc (datastate conf) (datastate conf) (datastate a));inversion Heqe.
   clear H2.
   destruct (mergeControlStateFunc (controlstate conf) (controlstate conf) (controlstate a));inversion Heqe.
   clear H2.
   simpl.  apply in_app_iff.   left;auto.
   remember ( innerCombineFunc'''' conf (c0 :: lst) ).
   destruct o;inversion H0.
   remember (mergeConfigFunc' conf a c1).
   destruct e;inversion H0.
   subst.
   apply IHlst with (re:=re) in Heqo;auto.
    unfold   mergeConfigFunc' in Heqe.
   destruct (mergeDataStateFunc (datastate conf) (datastate a) (datastate c1));inversion Heqe.
   clear H3.
   destruct (mergeControlStateFunc (controlstate conf) (controlstate a) (controlstate c1));inversion Heqe.
   clear H3.
   simpl.  apply in_app_iff.  right;auto. 
Qed.


Lemma removeEventPreservation: forall l e1 e2,
    e1 <> e2 ->
    In e2 l ->
    In e2  (removeEvent' e1 l). 
Proof.
  intro l;induction l.
  - intros. inversion H0.
  - intros.
    simpl.     
    destruct H0.
    subst.
    destruct (raisedEvent_dec e1 e2 ).
    contradiction.
    left;auto.
    destruct (raisedEvent_dec e1 a ).
    subst.   apply IHl;auto.   
    right.
    apply IHl;auto.     
Qed.

Lemma raisedPreservation: forall M (conf conf1 conf2: configuration M)  e1 e2,
    WellFormed M ->
    correct_configuration conf -> synchrony conf conf1 e1 ->  synchrony conf conf2 e2 ->
     e1 <> e2 ->
In e2 (raisedevents conf1).
Proof.
  intros.
  unfold synchrony in *.
   repeat match goal with
        | [ H: _ /\ _ |- _ ] => destruct H
        | [ H: exists _, _ |- _] => destruct H
          end.
   unfold combineFunc in H5.
   remember (constructConfigList (dom (controlstate conf)) e1 conf).
   destruct e;inversion H5.
   clear H7.
   destruct v.
   inversion H5.
   remember (innerCombineFunc'''' conf (c :: v)).
   destruct o;inversion H4.
   unfold constructConfigList in Heqe.
   clear H7.      
   Focus 2. inversion H5.
   inversion H5.
   unfold  removeEventFromConf.
   simpl.
   SearchAbout removeEvent'.
   assert (In e2 (raisedevents c0)).
   eapply innerCombineRaisedPreservation;auto.
   apply H2. apply Heqo. 
   SearchAbout removeEventFromConf.           
   SearchAbout (In _ (raisedevents _)).
   apply removeEventPreservation;auto.
     
   
Qed.

Lemma diamondL2: forall M (conf conf1 conf2: configuration M)  e1 e2, 
(forall sce1 sce2, In sce1 (dom (controlstate conf)) -> In sce2 (dom (controlstate conf)) -> In (eventDefinition e1) (alphabet sce1) -> In (eventDefinition e2) (alphabet sce2) -> sce1 <> sce2) ->
WellFormed M ->
e1 <> e2 ->
correct_configuration conf -> synchrony conf conf1 e1 ->  synchrony conf conf2 e2 ->
 (exists conf1', 
     synchrony conf1 conf1' e2).
Proof.
  intros.
  remember H3. clear Heqs. remember H4. clear Heqs0. 
  unfold synchrony in H3;unfold synchrony in H4. unfold synchrony. 
  repeat match goal with
        | [ H: _ /\ _ |- _ ] => destruct H
        | [ H: exists _, _ |- _] => destruct H
            end.
  unfold combineFunc in *.
  
  remember (constructConfigList (dom (controlstate conf)) e1 conf).
  destruct e;inversion H6.  clear H8.
  remember (constructConfigList (dom (controlstate conf)) e2 conf).
  destruct e;inversion H5. clear H8. 
  destruct v0;inversion H5. 
  destruct v;inversion H6.
  unfold  constructConfigList in *.     
  assert (dom (controlstate conf) = dom (controlstate conf1)).
  apply domControlSync with (e:=e1);auto.
  rewrite <- H7.
  pose proof constructList'NotNil.
  assert ( exists lst : list (configuration M),
             Result lst = constructConfigList' (filter
           (fun x : scenario => inList event_definition_dec (eventDefinition e2) (alphabet x))
           (filterList (finishedscenarios conf1) (dom (controlstate conf)) scenario_dec)) e2 conf1 /\ lst <> []).
  remember H0.
  clear Heqw. 
  unfold WellFormed in H0.
   repeat match goal with
        | [ H: _ /\ _ |- _ ] => destruct H
        | [ H: exists _, _ |- _] => destruct H
          end.
   unfold basicPreconditionMon in H13.
 repeat match goal with
        | [ H: _ /\ _ |- _ ] => destruct H
        | [ H: exists _, _ |- _] => destruct H
          end.  
  apply H10.
  apply termL5 with (conf:=conf) (e:=e1);auto. 
  destruct H2.
  apply   raised_wellform';auto.
  split;auto.   
   apply termL5 with (conf:=conf) (e:=e1);auto. 
  destruct H2.
  apply   raised_wellform';auto.
  repeat(split;auto).
  apply raisedPreservation with (conf:=conf) (conf2:=conf2) (e1:=e1);auto. 
  
  
  unfold not;intros.
  assert ((filter
               (fun x : scenario => inList event_definition_dec (eventDefinition e2) (alphabet x))
               (filterList (finishedscenarios conf) (dom (controlstate conf)) scenario_dec)) <> []).
  unfold not;intros.
   destruct ((filter
               (fun x : scenario => inList event_definition_dec (eventDefinition e2) (alphabet x))
               (filterList (finishedscenarios conf) (dom (controlstate conf)) scenario_dec))).
   simpl in Heqe0.
   inversion Heqe0.
   inversion H30.
   remember (filter
          (fun x : scenario => inList event_definition_dec (eventDefinition e2) (alphabet x))
          (filterList (finishedscenarios conf) (dom (controlstate conf)) scenario_dec) ).
   destruct l.
   contradiction.
  assert (In s1  (filter
          (fun x : scenario => inList event_definition_dec (eventDefinition e2) (alphabet x))
          (filterList (finishedscenarios conf1) (dom (controlstate conf)) scenario_dec))).
  apply filter_In;auto.
  split.
  Focus 2.
 
 
 assert (In s1 ( filter
           (fun x : scenario => inList event_definition_dec (eventDefinition e2) (alphabet x))
           (filterList (finishedscenarios conf) (dom (controlstate conf)) scenario_dec))).
 rewrite <- Heql.  left;auto.
 apply filter_In in H31.
 destruct H31;auto.
 apply filterIn.
  assert (In s1 ( filter
           (fun x : scenario => inList event_definition_dec (eventDefinition e2) (alphabet x))
           (filterList (finishedscenarios conf) (dom (controlstate conf)) scenario_dec))).
  rewrite <- Heql.  left;auto.
 apply filter_In in H31.
 destruct H31;auto.
 apply filterL2 in H31;auto.
   assert (In s1 ( filter
           (fun x : scenario => inList event_definition_dec (eventDefinition e2) (alphabet x))
           (filterList (finishedscenarios conf) (dom (controlstate conf)) scenario_dec))).
   rewrite <- Heql.  left;auto.
  apply filter_In in H31.
 destruct H31;auto.
 apply filterL1 in H31;auto.
 unfold not;intros.
 assert (In (eventDefinition e1) (alphabet s1)).
 Check syncFinish. 
apply syncFinish with (M:=M) (conf:=conf) (conf':=conf1);auto.
assert (~ In (eventDefinition e2) (alphabet s1)).
unfold not;intros.

assert (In s1 (dom (controlstate conf))).
rewrite domControlSync with (conf':=conf1) (e:=e1);auto. 
assert (correct_configuration conf1).
apply termL5 with (conf:=conf) (e:=e1);auto.
destruct H2.
apply raised_wellform';auto.
destruct H36.
unfold scenarioInclusion in inclusion;unfold incl in inclusion;apply inclusion;auto. 


apply H with (sce2:=s1) in H34;auto.

 apply reverseinListLemma in H32.
contradiction.
rewrite H29 in H31. 
inversion H31.
unfold incl;intros.
apply filter_In in H29. 
destruct H29.
apply filterL2 in H29;auto.
rewrite <- H7;auto.
intros.
apply filter_In in H29.
destruct H29.
split.
apply filterL1 in H29;auto. 
apply reverseinListLemma in H30;auto.
destruct H11.
destruct H11.
rewrite <- H11.
destruct x.
contradiction.
pose proof innerCombineNoErr .
assert (exists conf' : configuration M, innerCombineFunc'''' conf1 (c1::x) = Some conf').
remember H0. clear Heqw.  
unfold WellFormed in H0.
 repeat match goal with
        | [ H: _ /\ _ |- _ ] => destruct H
        | [ H: exists _, _ |- _] => destruct H
        end.
 rename H19 into dpf; rename H20 into tai; rename H21 into rim. 
   unfold basicPreconditionMon in H16.
 repeat match goal with
        | [ H: _ /\ _ |- _ ] => destruct H
        | [ H: exists _, _ |- _] => destruct H
        end.
 
apply H13 with (sceList:=(filter
             (fun x : scenario => inList event_definition_dec (eventDefinition e2) (alphabet x))
             (filterList (finishedscenarios conf1) (dom (controlstate conf)) scenario_dec))) (re:=e2) ;auto.
apply termL5 with (conf:=conf) (e:=e1);auto. 
destruct H2.
apply raised_wellform';auto.
split;auto.
apply termL5 with (conf:=conf) (e:=e1);auto. 
destruct H2.
apply raised_wellform';auto.
repeat(split;auto).
apply raisedPreservation with (conf:=conf) (conf2:=conf2) (e1:=e1);auto.

unfold incl.
intros.
rewrite filter_In in H29.
destruct H29.
apply filterL2 in H29;auto.
rewrite <- H7;auto.

apply filterUniq;auto.
apply uniqListFilter;auto.
assert (correct_configuration conf1).
apply termL5 with (conf:=conf) (e:=e1);auto. 
destruct H2.
apply raised_wellform';auto.
destruct H29.
auto.
destruct H2;auto.
intros.
apply filter_In in H29.
apply filter_In in H30.
destruct H29.
destruct H30.
apply reverseinListLemma in H31.
apply reverseinListLemma in H32.


unfold noIntersection;intros.
unfold not;intros.
destruct H33.
apply H33 with (eventDefinition e2);auto.
destruct H14.
rewrite H14.
exists ((removeEventFromConf e2 x0)).
split;auto.
apply raisedPreservation with (conf:=conf) (conf2:=conf2) (e1:=e1);auto.


Qed.

Lemma diamondL3: forall M (conf conf1 conf2 conf1': configuration M)  e1 e2, 
(forall sce1 sce2, In sce1 (dom (controlstate conf)) -> In sce2 (dom (controlstate conf)) -> In (eventDefinition e1) (alphabet sce1) -> In (eventDefinition e2) (alphabet sce2) -> sce1 <> sce2) ->
WellFormed M ->
e1 <> e2 ->
correct_configuration conf -> synchrony conf conf1 e1 ->  synchrony conf conf2 e2 ->
 (exists conf2', 
     synchrony conf2 conf2' e1).
Proof.
    intros.
    apply diamondL2 with (conf:=conf) (conf2:=conf1) (e1:=e2);auto.
    intros.
    unfold not;intros.
    apply H with (sce1:=sce2) (sce2:=sce1);auto.
Qed.    
 

Lemma value_env_eq: forall (env1 env2: value_env),
    dom2 env1 = dom2 env2 ->
    uniqList (dom env1) ->
    (forall v, In v (dom env1) -> (exists s, AIdent s = v ) /\ getValue v env1 = getValue v env2) ->
    env1 = env2.
Proof.
  (*dom2dom*)
  intro env1;induction env1.
-
  intros.  destruct env2.
  auto.   simpl in H. inversion H.
- intros.
  destruct env2.
  simpl in H;inversion H.
  simpl in H.
  destruct a;destruct p;simpl in *.
  inversion H.
  subst.
  destruct p0;destruct p.
  simpl in H4;subst.
  clear H.
  destruct H1 with (v:=a0).
  left;auto.
  destruct H.   rewrite <- H in H2.
    destruct (atom_eq_dec (AIdent x) (AIdent x)).
    inversion H2;subst.
    f_equal.
    apply IHenv1;auto.
    inversion H0;subst;auto.
    intros.
    destruct H1 with (v:=v);auto.
  destruct H3.  rewrite <- H3 in H4.   split.  
 exists x0;auto.    subst. 
 destruct ( atom_eq_dec (AIdent x0) (AIdent x)).
 inversion H0;subst.
 rewrite  e0 in H.
 contradiction.
 auto.
contradiction.  
Qed.

Print correct_configuration.
Print evnConsist.




Lemma getValueNone': forall env v ,
    ~ In v (dom env) ->
    getValue v env = None.
Proof.
  intro env;induction env.
  - intros.
        simpl;auto. destruct v;auto. 
  - intros.
    simpl. destruct a;destruct p.
    destruct v;auto.     destruct (atom_eq_dec (AIdent s) a). subst.
    simpl in H. exfalso;apply H. left;auto.
    apply IHenv. unfold not. intros.
    apply H. simpl;right;auto. 
Qed.


Lemma diamondDSNoChange: forall M (conf conf1: configuration M)  e1 e2 v, 
WellFormed M ->
e1 <> e2 ->
correct_configuration conf -> synchrony conf conf1 e1 ->
~ updateVarEv M (eventDefinition e1) v ->
getValue v (datastate conf) = getValue v (datastate conf1).
Proof.
  SearchAbout getValue.
  (*innerCombineFuncVarNoChange*)
  intros.
  assert (dom2 (datastate conf) = dom2 (datastate conf1)).
  SearchAbout dom2.
  apply  syncDSDom2 with (e:=e1);auto.

  assert (dom (datastate conf) = dom (datastate conf1)).
  
  rewrite <- dom2dom'.
  SearchAbout dom2.
  rewrite  ds_dom_eq;auto.
  assert (correct_configuration conf1).
  unfold  WellFormed in H.
     repeat match goal with
        | [ H: _ /\ _ |- _ ] => destruct H
        | [ H: exists _, _ |- _] => destruct H
            end. assert (noMultAlphabet'' M /\ importedNoCommonAlphabet'' M). split;auto.
     rename H10 into dpf. rename H11 into tai; rename H12 into rim. 
     rename H5  into noMul. clear H6. rename H7 into H6. rename H8 into H7. rename H9 into H8. 
  destruct H6.
  repeat match goal with
        | [ H: _ /\ _ |- _ ] => destruct H
        | [ H: exists _, _ |- _] => destruct H
              end.
  apply termL5 with (conf:=conf) (e:=e1);auto.
  destruct H1.
  apply raised_wellform';auto.
  unfold synchrony in H2;intuition. 
  destruct H5.
  rewrite <- ds_dom_eq.
    rewrite <- dom2dom'. 
    auto.
    assert (In v (dom (datastate conf)) \/ ~ (In v (dom (datastate conf)))).
    apply excluded_middle.
    destruct H6.
    Focus 2.
    
 
    rewrite  getValueNone';auto.
    rewrite  getValueNone';auto.
 rewrite <- H5;auto.
 unfold synchrony in H2.
 destruct H2.
 unfold combineFunc in H7.
 remember (constructConfigList (dom (controlstate conf)) e1 conf).
 destruct e;inversion H7.
 clear H9.
 destruct v0;inversion H7.
 remember (innerCombineFunc'''' conf (c :: v0)).
 destruct o;inversion H7.
 pose proof innerCombineFuncVarNoChange.
 unfold removeEventFromConf ;simpl. 
 assert (exists s, AIdent s = v).
 SearchAbout AIdent.
 apply tyEnvVar with (env:=datastate conf);auto.
 destruct H1;auto.
 destruct H11.
 subst.
 unfold constructConfigList in Heqe.
  unfold  WellFormed in H.
     repeat match goal with
        | [ H: _ /\ _ |- _ ] => destruct H
        | [ H: exists _, _ |- _] => destruct H
            end. assert (noMultAlphabet'' M /\ importedNoCommonAlphabet'' M). split;auto.
      rename H15 into dpf. rename H16 into tai; rename H17 into rim. 

      
     rename H10  into noMul. clear H11. rename H12 into H11. rename H13 into H12. rename H14 into H13. 
  destruct H11.
  repeat match goal with
        | [ H: _ /\ _ |- _ ] => destruct H
        | [ H: exists _, _ |- _] => destruct H
              end.
 
 apply H8 with (sceList:=(filter
              (fun x : scenario => inList event_definition_dec (eventDefinition e1) (alphabet x))
              (filterList (finishedscenarios conf) (dom (controlstate conf)) scenario_dec)) )
              (v0:=c::v0) (re:=e1);auto.
 intros.
 apply filter_In in H25.
 destruct H25.
 SearchAbout inList.
 apply reverseinListLemma in H26.
 unfold not;intros.
 apply H3.
 unfold  updateVarEv. 
 exists sce.            
 split;auto.
 Print triggerSce.
 apply basic_ts;auto.
 apply filterL2 in H25.
 destruct H1.
 rewrite <- cs_consist;auto.
 
 
Qed.

  
Lemma filterEqual: forall A (l l1 l2: list A)  (decA : forall x y : A, {x = y} + {x <> y}) (f: A-> bool),
    incl l1 l2 ->
    (forall a, In a l2 -> ~ In a l1 -> f a = false) ->
    
(filter f  (filterList l1 l decA)) =
(filter f (filterList l2 l decA)).
Proof.
  intros A l;induction l.
  -  intros.
     simpl in *.
     auto.
  -  intros.
     simpl.
     remember (inList decA a l1).
     destruct b.
     remember (inList decA a l2 ).
     destruct b.
     apply IHl;auto.
     simpl.
     remember (f a).
     destruct b.
     symmetry in Heqb, Heqb0.
     
     SearchAbout inList.
     apply reverseinListLemma in Heqb.
     apply reverseinListFalse in Heqb0.
     unfold incl in H.
     apply H in Heqb.      
     contradiction.
     apply IHl;auto.
     remember (inList decA a l2).
     destruct b.
     simpl.
     remember (f a).
     destruct b.
     symmetry in Heqb, Heqb0.
     apply reverseinListLemma in Heqb0.
     apply reverseinListFalse in Heqb.
     assert (f a = false).
     apply H0;auto.
     rewrite H1 in Heqb1.      
     inversion Heqb1.
     apply IHl;auto.
     simpl.
     destruct (f a).
     f_equal.
     apply IHl;auto.  
     apply IHl;auto.       
Qed.





Lemma evalMonadEq: forall ex  env1 env2  ,
    (forall  v, filterStateUsedExpr ex v -> getValue v env1 = getValue v env2 ) ->
    evalMonad env1 ex = evalMonad env2 ex. 
Proof.
  intro ex;induction ex;
  intros.
     simpl in *;intros. 
     
     assert (evalMonad env1 ex1 = evalMonad env2 ex1).
     apply IHex1 ;auto. intros;apply H;auto. rewrite H0;auto. 
     assert (evalMonad env1 ex2 = evalMonad env2 ex2).
     apply IHex2;auto.  intros;apply H;auto. rewrite  H1;auto.
     destruct (filterStateUsedExpr ex1 v);auto.
          
     rewrite H0;rewrite H1.  
     auto.
     Focus 10.
  
     simpl.
     

    destruct a;auto.
    assert (getValue (AIdent s) env1 = getValue (AIdent s) env2).
    apply H;auto.
    Print filterStateUsedExpr.     simpl. destruct (atom_eq_dec (AIdent s) (AIdent s)).  auto.
    contradiction.     rewrite H0;auto.

    simpl in *;intros. 
     assert (evalMonad env1 ex1 = evalMonad env2 ex1).
     apply IHex1 ;auto. intros;apply H;auto. rewrite H0;auto. 
     assert (evalMonad env1 ex2 = evalMonad env2 ex2).
     apply IHex2;auto.  intros;apply H;auto. rewrite  H1;auto.
     destruct (filterStateUsedExpr ex1 v);auto.
          
     rewrite H0;rewrite H1.  
     auto.

       simpl in *;intros. 
     assert (evalMonad env1 ex1 = evalMonad env2 ex1).
     apply IHex1 ;auto. intros;apply H;auto. rewrite H0;auto. 
     assert (evalMonad env1 ex2 = evalMonad env2 ex2).
     apply IHex2;auto.  intros;apply H;auto. rewrite  H1;auto.
     destruct (filterStateUsedExpr ex1 v);auto.
          
     rewrite H0;rewrite H1.  
     auto.
       simpl in *;intros. 
     assert (evalMonad env1 ex1 = evalMonad env2 ex1).
     apply IHex1 ;auto. intros;apply H;auto. rewrite H0;auto. 
     assert (evalMonad env1 ex2 = evalMonad env2 ex2).
     apply IHex2;auto.  intros;apply H;auto. rewrite  H1;auto.
     destruct (filterStateUsedExpr ex1 v);auto.
          
     rewrite H0;rewrite H1.  
     auto.

       simpl in *;intros. 
     assert (evalMonad env1 ex1 = evalMonad env2 ex1).
     apply IHex1 ;auto. intros;apply H;auto. rewrite H0;auto. 
     assert (evalMonad env1 ex2 = evalMonad env2 ex2).
     apply IHex2;auto.  intros;apply H;auto. rewrite  H1;auto.
     destruct (filterStateUsedExpr ex1 v);auto.
          
     rewrite H0;rewrite H1.  
     auto.

       simpl in *;intros. 
     assert (evalMonad env1 ex1 = evalMonad env2 ex1).
     apply IHex1 ;auto. intros;apply H;auto. rewrite H0;auto. 
     assert (evalMonad env1 ex2 = evalMonad env2 ex2).
     apply IHex2;auto.  intros;apply H;auto. rewrite  H1;auto.
     destruct (filterStateUsedExpr ex1 v);auto.
          
     rewrite H0;rewrite H1.  
     auto.

       simpl in *;intros. 
     assert (evalMonad env1 ex1 = evalMonad env2 ex1).
     apply IHex1 ;auto. intros;apply H;auto. rewrite H0;auto. 
     assert (evalMonad env1 ex2 = evalMonad env2 ex2).
     apply IHex2;auto.  intros;apply H;auto. rewrite  H1;auto.
     destruct (filterStateUsedExpr ex1 v);auto.
          
     rewrite H0;rewrite H1.  
     auto.

       simpl in *;intros. 
     assert (evalMonad env1 ex1 = evalMonad env2 ex1).
     apply IHex1 ;auto. intros;apply H;auto. rewrite H0;auto. 
     assert (evalMonad env1 ex2 = evalMonad env2 ex2).
     apply IHex2;auto.  intros;apply H;auto. rewrite  H1;auto.
     destruct (filterStateUsedExpr ex1 v);auto.
          
     rewrite H0;rewrite H1.  
     auto.

       simpl in *;intros. 
     assert (evalMonad env1 ex1 = evalMonad env2 ex1).
     apply IHex1 ;auto. intros;apply H;auto. rewrite H0;auto. 
     assert (evalMonad env1 ex2 = evalMonad env2 ex2).
     apply IHex2;auto.  intros;apply H;auto. rewrite  H1;auto.
     destruct (filterStateUsedExpr ex1 v);auto.
          
     rewrite H0;rewrite H1.  
     auto.

     simpl in *;intros.

     assert (evalMonad env1 ex = evalMonad env2 ex).
     apply IHex;auto.
     rewrite H0;auto.      
 Qed.


Lemma getValueInNoUniq: forall env1 env2 s,
    In (AIdent s) (dom env1) ->
    getValue (AIdent s) (env1 ++ env2) = getValue (AIdent s) env1.
Proof. 
   intro env1;induction env1. 
   - intros.
     inversion H.
   - intros.
     simpl. destruct a;destruct p.
     destruct H. simpl in H. 
     destruct (atom_eq_dec (AIdent s) a). auto. rewrite H in n. contradiction.
     
     destruct (atom_eq_dec (AIdent s) a).
     auto.
     apply IHenv1;auto. 
Qed.

Lemma getValueNotInNoUniq: forall env1 env2 s,
    ~In (AIdent s) (dom env1) ->
    getValue (AIdent s) (env1 ++ env2) = getValue (AIdent s) env2.
Proof. 
   intro env1;induction env1. 
   - intros.
     simpl in *. auto. 
   - intros.
     simpl in *.  destruct a;destruct p.
     simpl in *.     
     destruct (atom_eq_dec (AIdent s) a). subst.
     exfalso;apply H;left;auto.
     apply IHenv1;auto.
Qed.


Lemma getValueNotInNoUniq': forall env1 env2 v,
    ~In v (dom env1) ->
    getValue v (env1 ++ env2) = getValue v env2.
Proof. 
   intro env1;induction env1. 
   - intros.
     simpl in *. auto. 
   - intros.
     simpl in *.
     destruct v.
     destruct env2;simpl;auto.
      destruct env2;simpl;auto.
     destruct a;destruct p.
     simpl in *.     
     destruct (atom_eq_dec (AIdent s) a). subst.
     exfalso;apply H;left;auto.
     apply IHenv1;auto.
      destruct env2;simpl;auto.
      destruct env2;simpl;auto.
       destruct env2;simpl;auto.
    
Qed.


Lemma findEventValueEq: forall  l env1 env2 e,
    (forall ei v, In ei l -> filterStateUsedExpr (eventWhenExpr ei) v -> getValue v env1 = getValue v env2 ) ->
    dom env1 = dom env2 ->
   (forall v, In v (dom env1) -> exists s, AIdent s = v) ->
  findEventInstance e env1 l =  findEventInstance e env2 l. 
Proof.
  intro l;induction l.
  - intros;simpl.
    auto.
  - intros;simpl in *.
    remember (createValueEnv (eventArgs a) (eventParams (eventDefinition e)) (eventArguments e)).
    destruct e0;auto.
   
    pose proof evalMonadEq.
        
    unfold extendValEnv. 
    Print usedVarEv.
    Print scenarioUsedVar.  
    assert (evalMonad (env1 ++ v) (eventWhenExpr a) = evalMonad (env2 ++ v) (eventWhenExpr a)).
    apply H2.
    intros.
    assert (In v0 (dom env1) \/ ~ In v0 (dom env1)).
    apply excluded_middle.
    destruct H4.
    assert (exists s : string, AIdent s = v0).
    apply H1;auto.  destruct H5.  subst.   
    rewrite getValueInNoUniq;auto.  rewrite getValueInNoUniq;auto.
    Focus 2. rewrite <- H0;auto.
    apply H with (ei:=a);auto.
    assert (~ In v0 (dom env2)).
    rewrite <- H0;auto.
   
    
    
    rewrite getValueNotInNoUniq';auto.
    rewrite getValueNotInNoUniq';auto.

    rewrite H3.
    destruct ( evalMonad (env2 ++ v) (eventWhenExpr a));auto.
    destruct v0;auto.
    destruct s;auto.
    destruct b;auto.
    apply IHl;auto.
    intros.
    apply H with (ei:=ei);auto.     
Qed.


Lemma scenarioUsedVarIn: forall l  sce stp v0,
    In sce l ->
    filterStateUsedExpr (eventWhenExpr (stepEvent stp)) v0 ->
    In stp (traces sce) ->
    In sce (scenarioUsedVar l v0). 
Proof.
  intro l;induction l.
  -   intros. inversion H.
  - intros.
    destruct H;subst.
    simpl.
    remember ( filter
        (fun stp0 : step =>
         (filterStateUsedAct (stepActions stp0) v0
          || filterStateUsedExpr (eventWhenExpr (stepEvent stp0)) v0)%bool)
        (getTransitionsOfScenario sce)).
    destruct l0.
    unfold getTransitionsOfScenario in Heql0.
    assert (In stp ( filter
            (fun stp0 : step =>
             (filterStateUsedAct (stepActions stp0) v0
              || filterStateUsedExpr (eventWhenExpr (stepEvent stp0)) v0)%bool) 
            (traces sce))).
    apply filter_In;auto.
    split;auto.
    rewrite H0.  destruct (filterStateUsedAct (stepActions stp) v0);auto. 
    rewrite <- Heql0 in H;inversion H.
    left;auto.
    simpl.
    destruct ( filter
        (fun stp0 : step =>
         (filterStateUsedAct (stepActions stp0) v0
          || filterStateUsedExpr (eventWhenExpr (stepEvent stp0)) v0)%bool)
        (getTransitionsOfScenario a)).
    apply IHl with (stp:=stp);auto.
    right.
     apply IHl with (stp:=stp);auto.
Qed.



Lemma getValueInNoUniq': forall env1 env2 a,
    In a (dom env1) ->
    getValue a (env1 ++ env2) = getValue a env1.
Proof. 
   intro env1;induction env1. 
   - intros.
     inversion H.
   - intros.
     simpl. destruct a;destruct p.
     destruct H. simpl in H. subst.
     destruct a0;auto.
     destruct (atom_eq_dec (AIdent s) (AIdent s));auto.
     apply IHenv1;auto.
     contradiction.
     destruct a0;auto.
     
     destruct (atom_eq_dec (AIdent s) a). auto. 
     apply IHenv1;auto. 
Qed.

Lemma updateValueInv: forall v v' s v3,
    In (AIdent s) (dom v) ->
    Some v' = updateValueEnvInv (AIdent s) v3 v ->
    getValue (AIdent s) v' = Some v3.
Proof.
  intro v;induction v;intros.
  -  inversion H.
  -  simpl in H0.
     destruct a;destruct p.
     simpl in H.
     destruct H.
     +  subst. destruct (atom_eq_dec (AIdent s) (AIdent s)).
        destruct (typeValMatch t v3). inversion H0;subst.  simpl.
        destruct (atom_eq_dec (AIdent s) (AIdent s));auto.
        contradiction.    inversion H0.      contradiction.
     +  destruct (atom_eq_dec (AIdent s) a).
        destruct (typeValMatch t v3 ). inversion H0;subst. simpl;auto.
        destruct (atom_eq_dec (AIdent s) (AIdent s));auto. contradiction.
        inversion H0.
        remember (updateValueEnvInv (AIdent s) v3 v).
       destruct o;inversion H0.
       subst.  simpl.
       destruct (atom_eq_dec (AIdent s) a ).
       contradiction.     apply IHv;auto .    
Qed.

Lemma execActionAppEqual': forall act eventList v v1  l1 l2 v' v'' l' l'' x,
    Result (v', l') = execAction (v, l1) act eventList ->
    Result (v'', l'') = execAction (v1, l2) act eventList ->
    getValue (AIdent x) v = getValue (AIdent x) v1 ->
     In (AIdent x) (dom v) ->
    (dom v = dom v1) ->
    (forall va, In va (dom v) -> filterStateUsedAct act va = true ->
                getValue va v = getValue va v1) ->
    (forall va, In va (dom v) -> exists s' : string, va = AIdent s') -> 
    getValue (AIdent x) v' = getValue (AIdent x) v''.
Proof.
  intro act;induction act.
  - intros. simpl in *.
     inversion H;inversion H0;subst.
     auto.

  - intros. rename H5 into ais. 
     simpl in *. 
     destruct l;inversion H.   clear H6.  destruct a;inversion H.
     clear H6.
     remember (evalMonad v e ).
     destruct e0;inversion H.
     clear H6.
     remember (evalMonad v1 e).
     destruct e0;inversion H0. clear H6. 
     remember (updateValueEnvInv (AIdent s) v0 (v)).
     destruct o;inversion H. subst. 
         
     remember ( updateValueEnvInv (AIdent s) v2 (v1)).
     destruct o;inversion H0.
     subst.
        assert  ( evalMonad (v) e = evalMonad (v1) e).
   apply evalMonadEq;auto. intros.  
   
    assert (In v5 (dom v) \/ ~ In v5 (dom v)).
   apply excluded_middle.
   destruct H6.
   assert (In v5 (dom v1)).
   rewrite <- H3;auto.
   apply H4;auto.  
   assert (~ In v5 (dom v1)).
   rewrite <- H3;auto. SearchAbout getValue. 
   rewrite getValueNone';auto.  rewrite getValueNone';auto. 
   
    assert (x = s \/ x <> s).
   apply excluded_middle.
   destruct H6.
   subst.
   
   Focus 2.
   pose proof valueNoChange. 
   apply H7 with (s':= x) in Heqo;auto.
  apply H7 with (s':= x) in Heqo0;auto. 
  rewrite <- Heqo.  rewrite <- Heqo0.  auto. 
   pose proof updateValueInv.
   apply H6 in Heqo;auto. apply H6 in Heqo0;auto. rewrite H5 in Heqe0.   rewrite <- Heqe1 in Heqe0.  inversion Heqe0;subst. rewrite Heqo;rewrite Heqo0. auto.
   rewrite <- H3;auto.
  -  intros. rename H5 into ais. 
  simpl in *.   
  remember (calculateExprList (v) exprs).
  destruct e;inversion H. clear H6.
  remember (calculateExprList (v1) exprs).
  destruct e;inversion H0.
  clear H6.
  remember (getEventByName ident eventList).
  destruct o;inversion H.
  clear H6.
  remember (parameterMatchFunc v0 (eventParams e)).
  destruct b;inversion H.
 subst. 
  remember (parameterMatchFunc v2 (eventParams e)).
  destruct b;inversion H0.
  subst.
  auto.
  - intros. rename H5 into ais. 
 
  simpl in H;simpl in H0.
  remember (execAction (v, l1) act1 eventList).
  destruct e;inversion H.
  remember (execAction (v1, l2) act1 eventList).
  destruct e;inversion H0.
  clear H6.
  clear H7.
  destruct v0.
  destruct v2.
  
  assert ( getValue (AIdent x) v0 = getValue (AIdent x) v2).
  eapply IHact1 with (v:=v) (v1:=v1);auto. apply Heqe. apply Heqe0. 
    intros.
  apply H4;auto. simpl. rewrite H6;auto.
  eapply IHact2 with (v:=v0) (v1:=v2) (l1:=l) (l2:=l0);auto.
   apply H.
 apply H0. 
  
  pose proof execActionUniqList. 
  apply H6 in Heqe. rewrite <- Heqe. auto. 
  pose proof execActionUniqList.
  apply H6 in Heqe. apply H6 in Heqe0. rewrite <- Heqe;rewrite <- Heqe0.
  auto.   intros.
  
  assert (exists s', va = AIdent s').
  apply ais;auto.    pose proof execActionUniqList.
  apply H8 in Heqe.
   rewrite Heqe;auto.   
  destruct H8.
  rewrite H8. apply IHact1 with (v:=v) (v1:=v1) (eventList:=eventList) (l1:=l1) (l2:=l2) (l':=l) (l'':=l0);auto.
  pose proof execActionUniqList.
  apply H9 in Heqe.
  rewrite Heqe in H4.  apply H4 in H6.  rewrite H8 in H6;auto. simpl. rewrite H7;intuition;auto.
  rewrite H8 in H6;auto.
   pose proof execActionUniqList.
  apply H9 in Heqe.
  rewrite Heqe;auto.
  intros.
  apply H4;auto. simpl. rewrite H10;intuition;auto.
  intros. apply ais;auto.
  pose proof execActionUniqList.
  apply H7 in Heqe.
  rewrite Heqe;auto.
  
Qed.

Lemma scenarioUsedVarIn': forall l  sce stp v0,
    In sce l ->
    filterStateUsedAct (stepActions stp) v0 ->
    In stp (traces sce) ->
    In sce (scenarioUsedVar l v0). 
Proof.
  intro l;induction l.
  -   intros. inversion H.
  - intros.
    destruct H;subst.
    simpl.
    remember ( filter
        (fun stp0 : step =>
         (filterStateUsedAct (stepActions stp0) v0
          || filterStateUsedExpr (eventWhenExpr (stepEvent stp0)) v0)%bool)
        (getTransitionsOfScenario sce)).
    destruct l0.
    unfold getTransitionsOfScenario in Heql0.
    assert (In stp ( filter
            (fun stp0 : step =>
             (filterStateUsedAct (stepActions stp0) v0
              || filterStateUsedExpr (eventWhenExpr (stepEvent stp0)) v0)%bool) 
            (traces sce))).
    apply filter_In;auto.
    split;auto.
    rewrite H0.  intuition. 
    rewrite <- Heql0 in H;inversion H.
    left;auto.
    simpl.
    destruct ( filter
        (fun stp0 : step =>
         (filterStateUsedAct (stepActions stp0) v0
          || filterStateUsedExpr (eventWhenExpr (stepEvent stp0)) v0)%bool)
        (getTransitionsOfScenario a)).
    apply IHl with (stp:=stp);auto.
    right.
     apply IHl with (stp:=stp);auto.
Qed.

   
(*stpStMapEquiv' M ->
    stateEvDefInstanceMapEquivEListProp M ->
    stateEvDefInstanceMapEquiv M ->
    transEvMapProp M ->
    correctStateEvStepMap' M ->*)
  
(* Heqo0 : Some l = transEvMapFunc (stateEvDefInstanceMap M) (Some s0, Some (eventDefinition re))
  e : event_instance
  Heqo1 : Some e = findEventInstance re (datastate conf) l*)

(*e0 : Some l = transEvMapFunc (stateEvDefInstanceMap M) (Some s0, Some (eventDefinition re))
  e1 : Some e = findEventInstance re (datastate conf) l*)

(* e2 : transEvMapFunc (stateEvDefInstanceMap M) (Some s0, Some (eventDefinition re)) = Some l*)

(* H14 : event e = eventDefinition re*)

(*  Heqe3 : Result v2 = createTypEnv (eventArgs x) (eventParams (event x))
  v3 : list (atom * typ)
  Heqe4 : Result v3 = createTypEnv (eventArgs x0) (eventParams (event x0))*)


Lemma constructConfigVarEqual: forall M (conf conf1 conf' conf'': configuration M) sce e1 e2 v,
    correct_configuration conf ->
    synchrony conf conf1 e1 ->
    e1 <> e2 ->
    stateEvDefInstanceMapEquiv M ->
    correctStateEvStepMap' M ->
    stepExistsMon' M sce ->
    In v (dom (datastate conf)) ->
    getValue v (datastate conf) = getValue v (datastate conf1) ->
    (forall v,  usedVarEv M (eventDefinition e2) v -> getValue v (datastate conf) = getValue v (datastate conf1)) ->
    In sce (scenarios M) ->
    In (eventDefinition e2) (alphabet sce) ->
    getScenarioState sce (controlstate conf) = getScenarioState sce (controlstate conf1) ->
    Result conf' = constructConfig sce e2 conf ->
    Result conf'' = constructConfig sce e2 conf1 ->
    In e2 (raisedevents conf) ->
    typeCheck M ->
    transEvMapEventInstanceProp M ->
    transEvMapProp M ->
    stpStMapEquiv' M ->
    stateEvDefInstanceMapEquivEListProp M ->
    stateSceIn M ->
    getValue v (datastate conf') = getValue v (datastate conf''). 
Proof.
  intros. rename H15 into transInProp.
  rename H16 into transProp.
  rename H17 into stpEquiv.
  rename H18 into stateMapEquivProp.
  rename H19 into stateIn.
  unfold constructConfig in *.
  rewrite <- H10 in H12.
  remember (getScenarioState sce (controlstate conf) ).
  destruct o;inversion H11.
  clear H16.
  remember (transEvMapFunc (stateEvDefInstanceMap M) (Some s, Some (eventDefinition e2)) ).
  destruct o;inversion H11.
  clear H16.
  assert (findEventInstance e2 (datastate conf) l = findEventInstance e2 (datastate conf1) l).
  apply findEventValueEq;auto.
  intros.
  apply H7;auto. Print filterStateUsedExpr.  unfold usedVarEv.
  exists sce. split.
  Focus 2.
 
  apply basic_ts;auto.
  
  unfold correctStateEvStepMap' in H3.
  unfold stepExistsMon' in H4.
  unfold stateEvDefInstanceMapEquiv in H2. 
  assert (exists stp : step, In (s, ei, sce, Some stp) (stateEvStepMap' M)).
  apply H4  with (e:=(eventDefinition e2)) (l:=l);auto.

  rewrite semantic_rules.stateEvDefInstanceMapEquiv'. symmetry;auto. 
  destruct H2;auto.
  destruct H17.   
  apply H3 in H17.
  destruct H17.
  destruct H18.
  apply scenarioUsedVarIn with (stp:=x);auto.
  subst;auto.   
  assert (dom2 (datastate conf) = dom2 (datastate conf1)).
  SearchAbout dom2.
  apply syncDSDom2 with (e:=e1) ;auto.
  SearchAbout dom2.
  rewrite <- dom2dom'. 
  rewrite <- dom2dom'.    rewrite H15;auto. 
  intros.
  SearchAbout tyEnv.  apply tyEnvVar with (env:=datastate conf);auto.  
  destruct H;auto.
  rewrite <- H15 in H12.
  remember (findEventInstance e2 (datastate conf) l).
  destruct o;inversion H11.
  clear H17.
  remember (createValueEnv (eventArgs e) (eventParams (eventDefinition e2)) (eventArguments e2)).
  destruct e0;inversion H11.
  clear H17.
  SearchAbout getStep'.
  assert (getStep' conf sce e = getStep' conf1 sce e).
  unfold getStep'.
  rewrite <- Heqo.
  rewrite <- H10.
  auto.
  rewrite <- H16 in H12.
  remember (getStep' conf sce e).
  destruct o;inversion H11.
  clear H18.
  remember (configTransition (extendValEnv (datastate conf) v0) e2 e sce s0 conf).
  destruct e0;inversion H11.
  subst.
  remember (configTransition (extendValEnv (datastate conf1) v0) e2 e sce s0 conf1).
  destruct e0;inversion H12.
  subst.
  unfold configTransition in Heqe1,Heqe2.
  remember (execAction (extendValEnv (datastate conf) v0, []) (stepActions s0)
              (filter
                 (fun e : event_definition =>
                  match eventKind e with
                  | Internal => true
                  | Imported => false
                  | Exported => true
                  end) (events M))).
  destruct e0;inversion Heqe1.
  clear H18.
  destruct v3.
  remember ( execAction (extendValEnv (datastate conf1) v0, []) (stepActions s0)
              (filter
                 (fun e : event_definition =>
                  match eventKind e with
                  | Internal => true
                  | Imported => false
                  | Exported => true
                  end) (events M))).
  destruct e0;inversion Heqe2.
  clear H18.
  destruct v4.
  inversion Heqe1;subst;simpl.
  inversion Heqe2;subst;simpl.
  unfold extendValEnv in Heqe3, Heqe4.
 
  (*getValueIn'*)
  SearchAbout execAction. 
  assert ( dom (datastate conf ++ v0) = dom v3 ).
  eapply execActionUniqList. 
  apply Heqe3.
  assert ( dom (datastate conf1 ++ v0) = dom v4).
  eapply execActionUniqList.   apply Heqe4.
  SearchAbout updateDataState.
  assert (exists s, AIdent s = v).
  SearchAbout tyEnv.
  apply tyEnvVar with (env:=datastate conf);auto.
  destruct H;auto.
  destruct H19. 
  subst.
  assert (correct_configuration conf1).
  apply termL5 with (conf:=conf) (e:=e1);auto.   destruct H.
  unfold synchrony in H0. destruct H0.  apply raised_wellform' in H;auto.
  assert (dom (datastate conf) = dom (datastate conf1)).
  destruct H;destruct H19.
  SearchAbout dom2.  rewrite <- dom2dom'.  rewrite <- dom2dom'.  rewrite ds_dom_eq0. rewrite ds_dom_eq. auto. 
  rewrite <- getValueIn' with (env2:=v0);auto.   
  rewrite <- getValueIn' with (env2:=v0);auto.
  pose proof execActionAppEqual'.
  eapply H21 with (v:=datastate conf ++ v0) (v1:=datastate conf1 ++ v0);auto.  apply Heqe3. 
  apply Heqe4.
 
  rewrite getValueInNoUniq'.
  rewrite getValueInNoUniq'.   auto. rewrite <- H20;auto. auto.
  rewrite domApp. rewrite in_app_iff. left;auto. rewrite domApp;rewrite domApp.
  rewrite H20;auto. intros. SearchAbout filterStateUsedAct.
  assert (usedVarEv M (eventDefinition e2) va).
  unfold usedVarEv.   exists sce.
  split.

  Focus 2.
 
  apply basic_ts;auto.
  
  unfold correctStateEvStepMap' in H3.
  unfold stepExistsMon' in H4.
  unfold stateEvDefInstanceMapEquiv in H2. SearchAbout getStep'.
  assert (Some s0 = stpStpMapFunc (stateEvStepMap' M) (s, e, sce)).
  apply getStepMap' with (conf:=conf);auto. SearchAbout stpStpMapFunc.
  symmetry in H24. rewrite <- stpStMapEquivLem in H24. 
  
  destruct H2;auto.
  apply H3 in H24. destruct H24. destruct H26.
  apply scenarioUsedVarIn' with (stp:=s0);auto. 
  unfold stpStMapEquiv' in stpEquiv;auto.
  apply H7 in H24;auto.
  SearchAbout v0.
  assert (In va (dom (datastate conf)) \/ ~ In va (dom (datastate conf))).
  apply excluded_middle.   destruct H25.
    rewrite getValueInNoUniq';auto. rewrite getValueInNoUniq';auto.
    rewrite <- H20;auto.
      
  rewrite domApp in H22. rewrite in_app_iff in H22.
  destruct H22. contradiction.
  SearchAbout getValue. 
  rewrite  getValueNotInNoUniq';auto. 
  rewrite getValueNotInNoUniq';auto.  rewrite <- H20;auto. 
  intros. SearchAbout (AIdent _). SearchAbout tyEnv.
  assert (tyEnv v0). eapply raisedTyEnv;auto. Focus 2. apply Heqe0.
  SearchAbout parameterMatch.
  destruct H. apply raised_wellform' in H13. unfold wellFormedRaisedEvent in H13. auto.
  rewrite domApp in H22. rewrite in_app_iff in H22.
  destruct H22. SearchAbout AIdent. assert (exists s': string,  AIdent s' = va ).
  apply tyEnvVar with (env:=(datastate conf)). destruct H;auto. auto. destruct H24. exists x0;auto. assert (exists s': string,  AIdent s' = va ). apply tyEnvVar with (env:=v0);auto. destruct H24. 
  exists x0;auto.
  
  rewrite <- H18.
  (*rewrite domApp.
  apply uniqApp';auto.
  Focus 2.*) 
  remember Heqo0.
  clear Heqe5. symmetry in e0. 
  rewrite <- semantic_rules.stateEvDefInstanceMapEquiv' in e0.
     
  assert (In e l).
  eapply findEventInstanceIn. apply Heqo1. 
  assert (exists t_env : typ_env, typeCheckInstance e t_env).
  eapply eventInstanceTypeCorrect;auto.
  apply e0.  auto. auto. auto. destruct H22.
  unfold  typeCheckInstance in H22.
  unfold typeCheck in H14.
  apply H14 in H8.  unfold   typeCheckScenario in H8.
  unfold getTransitionsOfScenario in H8. 
  (*getStepMap':
  forall (M : monitor) (conf : configuration M) (sce : scenario) (s0 : step)
    (e0 : event_instance) (s : scenario_state),
  Some s0 = getStep' conf sce e0 ->
  Some s = getScenarioState sce (controlstate conf) ->
  Some s0 = stpStpMapFunc (stateEvStepMap' M) (s, e0, sce)
stpStMapEquivLem:
  forall l : list (scenario_state * event_instance * scenario * option step),
  uniqList (dom l) ->
  forall (st : scenario_state) (ei : event_instance) (stp : step) (sce : scenario),
  In (st, ei, sce, Some stp) l <-> stpStpMapFunc l (st, ei, sce) = Some stp*)
  unfold correctStateEvStepMap' in H3.
  assert (Some s0 = stpStpMapFunc (stateEvStepMap' M) (s, e, sce)).
  apply getStepMap' with (conf:=conf);auto.
   symmetry in H23.
  rewrite <- stpStMapEquivLem in H23. 
  assert ( In s0 (traces sce) /\ stepEvent s0 = e /\ pre_state s0 = s).
  apply H3;auto.
  destruct H24.
  apply H8 in H24.
  unfold typeCheckStep in H24.
  remember (createTypEnv (eventArgs (stepEvent s0)) (eventParams (event (stepEvent s0))) ).
  destruct e3;inversion H24. SearchAbout x0. 
  clear H24.
 
  destruct H25.
  subst.
  assert (event (stepEvent s0) = eventDefinition e2).
  eapply findInstanceDefMon;auto. apply transProp;auto. apply e0. 
  apply Heqo1.  rewrite H24 in *. 
  assert (dom v = dom v0).
  eapply createEqual. apply Heqe5. apply Heqe0.  
  unfold typeCheckInstance in H26.
    repeat match goal with
            | [ H: _ /\ _ |- _ ] => destruct H

                     end. 
    rewrite domApp in H29. rewrite domApp.
    rewrite <- H25. destruct H19. destruct  correct_mon. SearchAbout dom2. rewrite <- dom2dom'.
    rewrite ds_dom_eq.  unfold dsmon.    auto. 
 
    unfold stpStMapEquiv' in stpEquiv. auto.
    unfold stateEvDefInstanceMapEquiv in H2;intuition;auto. 
 
(*to prove v0, need to add typeCheck, typeCheckStep and typeCheckInstance are used*)

    rewrite <- H20;auto.
   rewrite <- H17. rewrite domApp. rewrite  H20. 

   remember Heqo0.
  clear Heqe5. symmetry in e0. 
  rewrite <- semantic_rules.stateEvDefInstanceMapEquiv' in e0.
     
  assert (In e l).
  eapply findEventInstanceIn. apply Heqo1. 
  assert (exists t_env : typ_env, typeCheckInstance e t_env).
  eapply eventInstanceTypeCorrect;auto.
  apply e0.  auto. auto. auto. destruct H22.
  unfold  typeCheckInstance in H22.
  unfold typeCheck in H14.
  apply H14 in H8.  unfold   typeCheckScenario in H8.
  unfold getTransitionsOfScenario in H8. 
  unfold correctStateEvStepMap' in H3.
  assert (Some s0 = stpStpMapFunc (stateEvStepMap' M) (s, e, sce)).
  apply getStepMap' with (conf:=conf);auto.
   symmetry in H23.
  rewrite <- stpStMapEquivLem in H23. 
  assert ( In s0 (traces sce) /\ stepEvent s0 = e /\ pre_state s0 = s).
  apply H3;auto.
  destruct H24.
  apply H8 in H24.
  unfold typeCheckStep in H24.
  remember (createTypEnv (eventArgs (stepEvent s0)) (eventParams (event (stepEvent s0))) ).
  destruct e3;inversion H24. SearchAbout x0. 
  clear H24.
 
  destruct H25.
  subst.
  assert (event (stepEvent s0) = eventDefinition e2).
  eapply findInstanceDefMon;auto. apply transProp;auto. apply e0. 
  apply Heqo1.  rewrite H24 in *. 
  assert (dom v = dom v0).
  eapply createEqual. apply Heqe5. apply Heqe0.  
  unfold typeCheckInstance in H26.
    repeat match goal with
            | [ H: _ /\ _ |- _ ] => destruct H

                     end. 
    rewrite domApp in H29. 
    rewrite <- H25. destruct H19. destruct  correct_mon.  rewrite <- dom2dom'.
    rewrite ds_dom_eq.  unfold dsmon.    auto. 
 
    unfold stpStMapEquiv' in stpEquiv. auto.
    unfold stateEvDefInstanceMapEquiv in H2;intuition;auto.
    
   
   
Qed.  


Lemma constructConfigVarEqual': forall M (conf conf1 conf' conf'': configuration M) sce e1 e2 v,
    correct_configuration conf ->
    synchrony conf conf1 e1 ->
    e1 <> e2 ->
    stateEvDefInstanceMapEquiv M ->
    correctStateEvStepMap' M ->
    stepExistsMon' M sce ->
    In v (dom (datastate conf)) ->
    getValue v (datastate conf) = getValue v (datastate conf1) ->
    (forall v,  In v (dom (datastate conf)) -> usedVarEv M (eventDefinition e2) v -> getValue v (datastate conf) = getValue v (datastate conf1)) ->
    In sce (scenarios M) ->
    In (eventDefinition e2) (alphabet sce) ->
    getScenarioState sce (controlstate conf) = getScenarioState sce (controlstate conf1) ->
    Result conf' = constructConfig sce e2 conf ->
    Result conf'' = constructConfig sce e2 conf1 ->
    In e2 (raisedevents conf) ->
    typeCheck M ->
    transEvMapEventInstanceProp M ->
    transEvMapProp M ->
    stpStMapEquiv' M ->
    stateEvDefInstanceMapEquivEListProp M ->
    stateSceIn M ->
    getValue v (datastate conf') = getValue v (datastate conf''). 
Proof.
  intros. rename H15 into transInProp.
  rename H16 into transProp.
  rename H17 into stpEquiv.
  rename H18 into stateMapEquivProp.
  rename H19 into stateIn.
  unfold constructConfig in *.
  rewrite <- H10 in H12.
  remember (getScenarioState sce (controlstate conf) ).
  destruct o;inversion H11.
  clear H16.
  remember (transEvMapFunc (stateEvDefInstanceMap M) (Some s, Some (eventDefinition e2)) ).
  destruct o;inversion H11.
  clear H16.
  assert (findEventInstance e2 (datastate conf) l = findEventInstance e2 (datastate conf1) l).
  Check findEventValueEq.
  Print findEventInstance. 
  Check findEventValueEq. 
  Locate findEventValueEq.         
  apply findEventValueEq;auto.
  intros.

  assert (In v0 (dom (datastate conf)) \/ ~ In v0 (dom (datastate conf))). 
  apply excluded_middle.
  destruct H17.
    
  
  apply H7;auto.
 

  unfold usedVarEv.
  exists sce. split.
  Focus 2.
 
  apply basic_ts;auto.
  rename H17 into v0d.   
  unfold correctStateEvStepMap' in H3.
  unfold stepExistsMon' in H4.
  unfold stateEvDefInstanceMapEquiv in H2. 
  assert (exists stp : step, In (s, ei, sce, Some stp) (stateEvStepMap' M)).
  apply H4  with (e:=(eventDefinition e2)) (l:=l);auto.

  rewrite semantic_rules.stateEvDefInstanceMapEquiv'. symmetry;auto. 
  destruct H2;auto.
  destruct H17.   
  apply H3 in H17.
  destruct H17.
  destruct H18.
  apply scenarioUsedVarIn with (stp:=x);auto.
  subst;auto.   

  Print filterStateUsedExpr. 
  SearchAbout getValue.
  
  rewrite getValueNone';auto.
  rewrite getValueNone';auto.

    assert (dom2 (datastate conf) = dom2 (datastate conf1)).
 
  apply syncDSDom2 with (e:=e1) ;auto.
  assert (dom (datastate conf) = dom (datastate conf1)).
  rewrite <- dom2dom'. 
  rewrite <- dom2dom'. rewrite H18;auto. rewrite <- H19;auto. 
  
  assert (dom2 (datastate conf) = dom2 (datastate conf1)).
  SearchAbout dom2.
  apply syncDSDom2 with (e:=e1) ;auto.
  SearchAbout dom2.
  rewrite <- dom2dom'. 
  rewrite <- dom2dom'.    rewrite H15;auto. 
  intros.
  SearchAbout tyEnv.  apply tyEnvVar with (env:=datastate conf);auto.  
  destruct H;auto.
  rewrite <- H15 in H12.
  remember (findEventInstance e2 (datastate conf) l).
  destruct o;inversion H11.
  clear H17.
  remember (createValueEnv (eventArgs e) (eventParams (eventDefinition e2)) (eventArguments e2)).
  destruct e0;inversion H11.
  clear H17.
  SearchAbout getStep'.
  assert (getStep' conf sce e = getStep' conf1 sce e).
  unfold getStep'.
  rewrite <- Heqo.
  rewrite <- H10.
  auto.
  rewrite <- H16 in H12.
  remember (getStep' conf sce e).
  destruct o;inversion H11.
  clear H18.
  remember (configTransition (extendValEnv (datastate conf) v0) e2 e sce s0 conf).
  destruct e0;inversion H11.
  subst.
  remember (configTransition (extendValEnv (datastate conf1) v0) e2 e sce s0 conf1).
  destruct e0;inversion H12.
  subst.
  unfold configTransition in Heqe1,Heqe2.
  remember (execAction (extendValEnv (datastate conf) v0, []) (stepActions s0)
              (filter
                 (fun e : event_definition =>
                  match eventKind e with
                  | Internal => true
                  | Imported => false
                  | Exported => true
                  end) (events M))).
  destruct e0;inversion Heqe1.
  clear H18.
  destruct v3.
  remember ( execAction (extendValEnv (datastate conf1) v0, []) (stepActions s0)
              (filter
                 (fun e : event_definition =>
                  match eventKind e with
                  | Internal => true
                  | Imported => false
                  | Exported => true
                  end) (events M))).
  destruct e0;inversion Heqe2.
  clear H18.
  destruct v4.
  inversion Heqe1;subst;simpl.
  inversion Heqe2;subst;simpl.
  unfold extendValEnv in Heqe3, Heqe4.
 
  (*getValueIn'*)
  SearchAbout execAction. 
  assert ( dom (datastate conf ++ v0) = dom v3 ).
  eapply execActionUniqList. 
  apply Heqe3.
  assert ( dom (datastate conf1 ++ v0) = dom v4).
  eapply execActionUniqList.   apply Heqe4.
  SearchAbout updateDataState.
  assert (exists s, AIdent s = v).
  SearchAbout tyEnv.
  apply tyEnvVar with (env:=datastate conf);auto.
  destruct H;auto.
  destruct H19. 
  subst.
  assert (correct_configuration conf1).
  apply termL5 with (conf:=conf) (e:=e1);auto.   destruct H.
  unfold synchrony in H0. destruct H0.  apply raised_wellform' in H;auto.
  assert (dom (datastate conf) = dom (datastate conf1)).
  destruct H;destruct H19.
  SearchAbout dom2.  rewrite <- dom2dom'.  rewrite <- dom2dom'.  rewrite ds_dom_eq0. rewrite ds_dom_eq. auto. 
  rewrite <- getValueIn' with (env2:=v0);auto.   
  rewrite <- getValueIn' with (env2:=v0);auto.
  pose proof execActionAppEqual'.
  eapply H21 with (v:=datastate conf ++ v0) (v1:=datastate conf1 ++ v0);auto.  apply Heqe3. 
  apply Heqe4.
 
  rewrite getValueInNoUniq'.
  rewrite getValueInNoUniq'.   auto. rewrite <- H20;auto. auto.
  rewrite domApp. rewrite in_app_iff. left;auto. rewrite domApp;rewrite domApp.
  rewrite H20;auto. intros. SearchAbout filterStateUsedAct.
  assert (usedVarEv M (eventDefinition e2) va).
  unfold usedVarEv.   exists sce.
  split.

  Focus 2.
 
  apply basic_ts;auto.
  
  unfold correctStateEvStepMap' in H3.
  unfold stepExistsMon' in H4.
  unfold stateEvDefInstanceMapEquiv in H2. SearchAbout getStep'.
  assert (Some s0 = stpStpMapFunc (stateEvStepMap' M) (s, e, sce)).
  apply getStepMap' with (conf:=conf);auto. SearchAbout stpStpMapFunc.
  symmetry in H24. rewrite <- stpStMapEquivLem in H24. 
  
  destruct H2;auto.
  apply H3 in H24. destruct H24. destruct H26.
  apply scenarioUsedVarIn' with (stp:=s0);auto. 
  unfold stpStMapEquiv' in stpEquiv;auto.

   assert (In va (dom (datastate conf)) \/ ~ In va (dom (datastate conf))).
   apply excluded_middle.   destruct H25.

   
  
  apply H7 in H24;auto.
  SearchAbout getValue.  rewrite getValueInNoUniq';auto. 
  rewrite getValueInNoUniq'. auto. rewrite <- H20;auto. 
  SearchAbout getValue. 
  rewrite getValueNotInNoUniq';auto.
  rewrite getValueNotInNoUniq';auto.
  rewrite <- H20;auto.
  intros. 
  
 
  SearchAbout (AIdent _). SearchAbout tyEnv.
  assert (tyEnv v0). eapply raisedTyEnv;auto. Focus 2. apply Heqe0.
  SearchAbout parameterMatch.
  destruct H. apply raised_wellform' in H13. unfold wellFormedRaisedEvent in H13. auto.
  rewrite domApp in H22. rewrite in_app_iff in H22.
  destruct H22. SearchAbout AIdent. assert (exists s': string,  AIdent s' = va ).
  apply tyEnvVar with (env:=(datastate conf)). destruct H;auto. auto. destruct H24. exists x0;auto. assert (exists s': string,  AIdent s' = va ). apply tyEnvVar with (env:=v0);auto. destruct H24. 
  exists x0;auto.
  
  rewrite <- H18.
  (*rewrite domApp.
  apply uniqApp';auto.
  Focus 2.*) 
  remember Heqo0.
  clear Heqe5. symmetry in e0. 
  rewrite <- semantic_rules.stateEvDefInstanceMapEquiv' in e0.
     
  assert (In e l).
  eapply findEventInstanceIn. apply Heqo1. 
  assert (exists t_env : typ_env, typeCheckInstance e t_env).
  eapply eventInstanceTypeCorrect;auto.
  apply e0.  auto. auto. auto. destruct H22.
  unfold  typeCheckInstance in H22.
  unfold typeCheck in H14.
  apply H14 in H8.  unfold   typeCheckScenario in H8.
  unfold getTransitionsOfScenario in H8. 
  (*getStepMap':
  forall (M : monitor) (conf : configuration M) (sce : scenario) (s0 : step)
    (e0 : event_instance) (s : scenario_state),
  Some s0 = getStep' conf sce e0 ->
  Some s = getScenarioState sce (controlstate conf) ->
  Some s0 = stpStpMapFunc (stateEvStepMap' M) (s, e0, sce)
stpStMapEquivLem:
  forall l : list (scenario_state * event_instance * scenario * option step),
  uniqList (dom l) ->
  forall (st : scenario_state) (ei : event_instance) (stp : step) (sce : scenario),
  In (st, ei, sce, Some stp) l <-> stpStpMapFunc l (st, ei, sce) = Some stp*)
  unfold correctStateEvStepMap' in H3.
  assert (Some s0 = stpStpMapFunc (stateEvStepMap' M) (s, e, sce)).
  apply getStepMap' with (conf:=conf);auto.
   symmetry in H23.
  rewrite <- stpStMapEquivLem in H23. 
  assert ( In s0 (traces sce) /\ stepEvent s0 = e /\ pre_state s0 = s).
  apply H3;auto.
  destruct H24.
  apply H8 in H24.
  unfold typeCheckStep in H24.
  remember (createTypEnv (eventArgs (stepEvent s0)) (eventParams (event (stepEvent s0))) ).
  destruct e3;inversion H24. SearchAbout x0. 
  clear H24.
 
  destruct H25.
  subst.
  assert (event (stepEvent s0) = eventDefinition e2).
  eapply findInstanceDefMon;auto. apply transProp;auto. apply e0. 
  apply Heqo1.  rewrite H24 in *. 
  assert (dom v = dom v0).
  eapply createEqual. apply Heqe5. apply Heqe0.  
  unfold typeCheckInstance in H26.
    repeat match goal with
            | [ H: _ /\ _ |- _ ] => destruct H

                     end. 
    rewrite domApp in H29. rewrite domApp.
    rewrite <- H25. destruct H19. destruct  correct_mon. SearchAbout dom2. rewrite <- dom2dom'.
    rewrite ds_dom_eq.  unfold dsmon.    auto. 
 
    unfold stpStMapEquiv' in stpEquiv. auto.
    unfold stateEvDefInstanceMapEquiv in H2;intuition;auto. 
 
(*to prove v0, need to add typeCheck, typeCheckStep and typeCheckInstance are used*)

    rewrite <- H20;auto.
   rewrite <- H17. rewrite domApp. rewrite  H20. 

   remember Heqo0.
  clear Heqe5. symmetry in e0. 
  rewrite <- semantic_rules.stateEvDefInstanceMapEquiv' in e0.
     
  assert (In e l).
  eapply findEventInstanceIn. apply Heqo1. 
  assert (exists t_env : typ_env, typeCheckInstance e t_env).
  eapply eventInstanceTypeCorrect;auto.
  apply e0.  auto. auto. auto. destruct H22.
  unfold  typeCheckInstance in H22.
  unfold typeCheck in H14.
  apply H14 in H8.  unfold   typeCheckScenario in H8.
  unfold getTransitionsOfScenario in H8. 
  unfold correctStateEvStepMap' in H3.
  assert (Some s0 = stpStpMapFunc (stateEvStepMap' M) (s, e, sce)).
  apply getStepMap' with (conf:=conf);auto.
   symmetry in H23.
  rewrite <- stpStMapEquivLem in H23. 
  assert ( In s0 (traces sce) /\ stepEvent s0 = e /\ pre_state s0 = s).
  apply H3;auto.
  destruct H24.
  apply H8 in H24.
  unfold typeCheckStep in H24.
  remember (createTypEnv (eventArgs (stepEvent s0)) (eventParams (event (stepEvent s0))) ).
  destruct e3;inversion H24. SearchAbout x0. 
  clear H24.
 
  destruct H25.
  subst.
  assert (event (stepEvent s0) = eventDefinition e2).
  eapply findInstanceDefMon;auto. apply transProp;auto. apply e0. 
  apply Heqo1.  rewrite H24 in *. 
  assert (dom v = dom v0).
  eapply createEqual. apply Heqe5. apply Heqe0.  
  unfold typeCheckInstance in H26.
    repeat match goal with
            | [ H: _ /\ _ |- _ ] => destruct H

                     end. 
    rewrite domApp in H29. 
    rewrite <- H25. destruct H19. destruct  correct_mon.  rewrite <- dom2dom'.
    rewrite ds_dom_eq.  unfold dsmon.    auto. 
 
    unfold stpStMapEquiv' in stpEquiv. auto.
    unfold stateEvDefInstanceMapEquiv in H2;intuition;auto.
    
   
   
Qed.  




Lemma mergeDataFuncUpdateRev:
  forall (dso ds1 ds2 : value_env) (ds3 : list (atom * (typ * range_typ))) (a : atom),
  Result ds3 = mergeDataStateFunc dso ds1 ds2 ->
  getValue a ds3 = getValue a dso ->
  getValue a ds1 = getValue a ds2. 
Proof.
 intro dso. induction dso;intros;simpl.
       - destruct ds1.  destruct ds2.  simpl in H.  inversion H. simpl. auto.
         simpl in H. inversion H. simpl in H. inversion H. 
- simpl in H. destruct a. destruct p. 
destruct ds1. inversion H.
destruct p. destruct p. 
destruct ds2. inversion H. 
destruct p. destruct p.
destruct (atom_eq_dec a a1).
destruct (atom_eq_dec a a2).    
destruct (typ_eq_dec t t0).
destruct (typ_eq_dec t t1). 
 remember (mergeDataStateFunc dso ds1 ds2).
destruct e3.              
destruct (range_typ_dec r0 r1).
subst. 
inversion H;subst.
simpl.  
destruct a0;auto.   
destruct (atom_eq_dec (AIdent s) a2). auto.
apply IHdso with (ds3:=v);auto.
simpl in  H0.
destruct (atom_eq_dec (AIdent s) a2 ). contradiction. 
auto. 
subst. 
destruct (range_typ_dec r0 r).
subst. inversion H;subst. clear H.
simpl in *. destruct a0;auto.
destruct (atom_eq_dec (AIdent s) a2 );auto. 
apply IHdso with (ds3:=v);auto.
destruct (range_typ_dec r1 r).
subst.
inversion H;subst.
clear H.
simpl in *. destruct a0;auto.
destruct (atom_eq_dec (AIdent s) a2 );auto.
apply IHdso with (ds3:=v);auto. inversion H. inversion H. inversion H. inversion H. inversion H.
inversion H. 
Qed.


Lemma mergeDataFuncUpdateRev':
  forall (dso ds1 ds2 : value_env) (ds3 : list (atom * (typ * range_typ))) (a : atom),
  Result ds3 = mergeDataStateFunc dso ds1 ds2 ->
  getValue a ds3 = getValue a dso ->
  getValue a dso = getValue a ds1. 
Proof.
 intro dso. induction dso;intros;simpl.
       - destruct ds1.  destruct ds2.  simpl in H.  inversion H. simpl. auto.
         simpl in H. inversion H. simpl in H. inversion H. 
- simpl in H. destruct a. destruct p. 
destruct ds1. inversion H.
destruct p. destruct p. 
destruct ds2. inversion H. 
destruct p. destruct p.
destruct (atom_eq_dec a a1).
destruct (atom_eq_dec a a2).    
destruct (typ_eq_dec t t0).
destruct (typ_eq_dec t t1). 
 remember (mergeDataStateFunc dso ds1 ds2).
destruct e3.              
destruct (range_typ_dec r0 r1).
subst. 
inversion H;subst.
simpl.  
destruct a0;auto.   
destruct (atom_eq_dec (AIdent s) a2). subst.
simpl in H0.
destruct (atom_eq_dec (AIdent s) (AIdent s)).
auto.
contradiction. apply IHdso with (ds3:=v) (ds2:=ds2);auto.
simpl in  H0.
destruct (atom_eq_dec (AIdent s) a2 ). contradiction. 
auto. 
subst. 
destruct (range_typ_dec r0 r).
subst. inversion H;subst. clear H.
simpl in *. destruct a0;auto.
destruct (atom_eq_dec (AIdent s) a2 );auto. 
apply IHdso with (ds3:=v) (ds2:=ds2);auto.
destruct (range_typ_dec r1 r).
subst.
inversion H;subst.
clear H.
simpl in *. destruct a0;auto.
destruct (atom_eq_dec (AIdent s) a2 );auto.
apply IHdso with (ds3:=v) (ds2:=ds2);auto. inversion H. inversion H. inversion H. inversion H. inversion H.
inversion H. 
Qed.


Lemma innerCombineEq: forall M l (conf: configuration M) c v,
    Some c = innerCombineFunc'''' conf l ->
    uniqList (dom (datastate conf)) ->
    In v (dom (datastate conf)) ->
    getValue v (datastate c) = getValue v (datastate conf) ->
    (forall conf', In conf' l -> getValue v (datastate conf') = getValue v (datastate conf)).
Proof.

  intros M l.
  induction l.
  -
    intros. inversion H3.
  -  intros.
     simpl in H.
     destruct l.
     remember (mergeConfigFunc' conf conf a).
     destruct e;inversion H.
     subst.
     destruct H3. Focus 2. inversion H3. 
     subst.
     SearchAbout mergeConfigFunc'.
     unfold   mergeConfigFunc' in Heqe.
     remember (mergeDataStateFunc (datastate conf) (datastate conf) (datastate conf')).
     destruct e;inversion Heqe.
     clear H4.
     destruct ( mergeControlStateFunc (controlstate conf) (controlstate conf) (controlstate conf'));inversion Heqe.
     subst;simpl in *.   clear Heqe. clear H.
     symmetry. apply mergeDataFuncUpdateRev with (dso:=datastate conf) (ds3:=v1);auto. 
   
    remember (innerCombineFunc'''' conf (c0 :: l)).
    destruct o;inversion H.
    clear H5.
    destruct H3. subst.
    remember (mergeConfigFunc' conf conf' c1).
    destruct e;inversion H.    subst.
    unfold mergeConfigFunc' in Heqe.
    remember ( mergeDataStateFunc (datastate conf) (datastate conf') (datastate c1)).
    destruct e;inversion Heqe.
    clear H4.     
    symmetry. apply mergeDataFuncUpdateRev' with (ds2:=datastate c1) (ds3:=v1);auto.
    destruct (mergeControlStateFunc (controlstate conf) (controlstate conf') (controlstate c1));inversion Heqe. simpl in H4. rewrite H4 in H2;simpl in H2. auto. 
   
   apply IHl with (v:=v) (conf':=conf') in Heqo;auto.  
   remember (mergeConfigFunc' conf a c1).
   destruct e;inversion H.
   subst.
  unfold mergeConfigFunc' in Heqe.
    remember ( mergeDataStateFunc (datastate conf) (datastate a) (datastate c1)).
    destruct e;inversion Heqe.
    clear H5.
    destruct (mergeControlStateFunc (controlstate conf) (controlstate a) (controlstate c1));inversion Heqe.
    clear H5.     inversion Heqe. rewrite H5 in H2;simpl in H2.
    pose proof mergeDataFuncUpdateRev.
    pose proof mergeDataFuncUpdateRev'.
  rewrite <- H4 with (dso:=datastate conf) (ds1:=datastate a) (ds2:=datastate c1) (ds3:=v1);auto.     symmetry. 
      apply H6 with  (ds2:=datastate c1) (ds3:=v1);auto. 
    
Qed.


Lemma constructIn: forall M l e (conf conf':configuration M) cl x,
    Result cl = constructConfigList' l e conf ->
    In x l ->
    Result conf' = constructConfig x e conf ->
    In conf' cl.
Proof.
  intros M l;induction l.
  - intros. inversion H0.
  - intros. destruct H0.
    subst.
    simpl in H.
    remember (constructConfig x e conf).
    destruct e0;inversion H.
    clear H2.
    inversion H1;subst.
    remember (constructConfigList' l e conf).
    destruct e0;inversion H.
    left;auto.
    simpl in H.
    remember (constructConfig a e conf).
    destruct e0;inversion H.
    clear H3.
    remember (constructConfigList' l e conf).
    destruct e0;inversion H.
    subst.
    apply IHl with (conf':=conf') (x:=x) in Heqe1;auto. 
    right;auto. 
Qed. 


Lemma innerCombineEq': forall M l (conf: configuration M) c v,
    Some c = innerCombineFunc'''' conf l ->
    uniqList (dom (datastate conf)) ->
    In v (dom (datastate conf)) ->
    
    (forall conf', In conf' l -> getValue v (datastate conf') = getValue v (datastate conf)) ->
    (exists s, v = AIdent s) -> 
    getValue v (datastate c) = getValue v (datastate conf)
    .
Proof.
     intros M l.
  induction l.
  -
    intros. simpl in H. inversion H.
  -  intros. rename H3 into existName. 
     simpl in *.
     destruct l.
     remember (mergeConfigFunc' conf conf a).
     destruct e;inversion H.
     subst.
     assert (getValue v (datastate a) = getValue v (datastate conf)).
     apply H2;auto.
     SearchAbout mergeConfigFunc'.
     symmetry.
     destruct existName.  subst.
     SearchAbout mergeConfigFunc'.      
     
     apply mergeConfigFuncDSVarEqual with (conf1:=conf) (conf2:=a);auto.
     remember (innerCombineFunc'''' conf (c0 :: l)).
     destruct o;inversion H.
     clear H4.
     remember (mergeConfigFunc' conf a c1).
     destruct e;inversion H.
     subst.
     apply IHl with (v:=v) in Heqo;auto.
     assert (getValue v (datastate a) = getValue v (datastate conf)).
     apply H2;auto.
     symmetry. destruct existName;subst. 
      apply mergeConfigFuncDSVarEqual with (conf1:=a) (conf2:=c1);auto.    
    
Qed.


Lemma mergeDataFuncUpdate2:
  forall (dso ds1 ds2 : value_env) (ds3 : list (atom * (typ * range_typ))) (a : atom),
  Result ds3 = mergeDataStateFunc dso ds1 ds2 ->
  (getValue a ds3 = getValue a ds1 \/ getValue a ds3 = getValue a ds2). 
Proof.
 intro dso. induction dso;intros;simpl.
       - destruct ds1.  destruct ds2.  simpl in H.  inversion H. simpl. auto.
         simpl in H. inversion H. simpl in H. inversion H. 
- simpl in H. destruct a. destruct p. 
destruct ds1. inversion H.
destruct p. destruct p. 
destruct ds2. inversion H. 
destruct p. destruct p.
destruct (atom_eq_dec a a1).
destruct (atom_eq_dec a a2).    
destruct (typ_eq_dec t t0).
destruct (typ_eq_dec t t1). 
 remember (mergeDataStateFunc dso ds1 ds2).
destruct e3.              
destruct (range_typ_dec r0 r1).
subst. 
inversion H;subst.
simpl in *.  
destruct a0;auto.   
destruct (atom_eq_dec (AIdent s) a2). left;auto.
apply IHdso with (ds3:=v) (ds2:=ds2);auto.
subst. 
destruct (range_typ_dec r0 r).
subst. inversion H;subst. clear H.
simpl in *. destruct a0;auto.
destruct (atom_eq_dec (AIdent s) a2 );auto. 
destruct (range_typ_dec r1 r).
subst.
inversion H;subst.
clear H.
simpl in *. destruct a0;auto.
destruct (atom_eq_dec (AIdent s) a2 );auto.
inversion H.
inversion H. inversion H. inversion H. inversion H. inversion H. 
Qed.

Lemma innerCombineExistConf: forall M l (conf:configuration M) c v,
    Some c = innerCombineFunc'''' conf l ->
    getValue v (datastate conf) <> getValue v (datastate c) ->
     (exists s : string, v = AIdent s) ->
    (exists conf', In conf' l /\ getValue v (datastate c) = getValue v (datastate conf')).
Proof.
   intros M l.
  induction l.
  -
    intros. simpl in H. inversion H.
  -  intros.
     simpl in *.
     destruct l.
     remember (mergeConfigFunc' conf conf a).
     destruct e;inversion H.
     subst.
     SearchAbout mergeConfigFunc'. 
     
    
     unfold   mergeConfigFunc' in Heqe.
     remember (mergeDataStateFunc (datastate conf) (datastate conf) (datastate a)).
     destruct e;inversion Heqe.
     clear H3.
     destruct ( mergeControlStateFunc (controlstate conf) (controlstate conf) (controlstate a));inversion Heqe.
     subst;simpl in *.   clear Heqe. clear H.
     apply mergeDataFuncUpdate2 with (a:=v) in Heqe0;auto.
     destruct Heqe0. symmetry in H. contradiction. exists a. split;auto.
     remember (innerCombineFunc'''' conf (c0 :: l)).
     destruct o;inversion H. clear H3.
     remember (mergeConfigFunc' conf a c1).
     destruct e;inversion H.   subst.
     assert (getValue v (datastate v0) = getValue v (datastate a) \/ getValue v (datastate v0) <> getValue v (datastate a)).
     apply excluded_middle.
     destruct H2. exists a. split;auto.
     
     apply IHl with (v:=v) in Heqo;auto.
     destruct Heqo.  exists x. split. intuition;auto.
      unfold   mergeConfigFunc' in Heqe.
     remember (mergeDataStateFunc (datastate conf) (datastate a) (datastate c1)).
     destruct e;inversion Heqe.
     clear H5.
     destruct ( mergeControlStateFunc (controlstate conf) (controlstate a) (controlstate c1));inversion Heqe.
     subst;simpl.  clear Heqe. clear H. simpl in H2. simpl in H0.
     destruct H3.
     apply mergeDataFuncUpdate2 with (a:=v) in Heqe0;auto. destruct Heqe0. contradiction.
     rewrite <- H3;auto.
     unfold not;intros. 
     rewrite H3 in H0.
     
     unfold   mergeConfigFunc' in Heqe.
      remember (mergeDataStateFunc (datastate conf) (datastate a) (datastate c1)).
     destruct e;inversion Heqe.
     clear H5.
     destruct ( mergeControlStateFunc (controlstate conf) (controlstate a) (controlstate c1));inversion Heqe.
     subst;simpl.  clear Heqe. clear H. simpl in H2. simpl in H0.
     apply mergeDataFuncUpdate2 with (a:=v) in Heqe0;auto.
     destruct Heqe0. contradiction. apply H0. auto.
Qed.


Lemma mergeDataFuncUpdate3:
  forall (dso ds1 ds2 : value_env) (ds3 : list (atom * (typ * range_typ))) (a : atom),
    Result ds3 = mergeDataStateFunc dso ds1 ds2 ->
    getValue a ds3 = getValue a ds2 ->
    getValue a dso <> getValue a ds1 ->
  (getValue a ds1 = getValue a ds2). 
Proof.
 intro dso. induction dso;intros;simpl.
       - destruct ds1.  destruct ds2.  simpl in H.  inversion H. simpl. auto.
         simpl in H. inversion H. simpl in H. inversion H. 
- simpl in H. destruct a. destruct p. 
destruct ds1. inversion H.
destruct p. destruct p. 
destruct ds2. inversion H. 
destruct p. destruct p.
destruct (atom_eq_dec a a1).
destruct (atom_eq_dec a a2).    
destruct (typ_eq_dec t t0).
destruct (typ_eq_dec t t1). 
 remember (mergeDataStateFunc dso ds1 ds2).
destruct e3.              
destruct (range_typ_dec r0 r1).
subst. 
inversion H;subst.
simpl in *.  
destruct a0;auto.   
destruct (atom_eq_dec (AIdent s) a2). auto. 
apply IHdso with (ds3:=v) (ds2:=ds2);auto.
subst. 
destruct (range_typ_dec r0 r).
subst. inversion H;subst. clear H.
simpl in *. destruct a0;auto.
destruct (atom_eq_dec (AIdent s) a2 );auto. 
contradiction.
apply IHdso with (ds3:=v) (ds2:=ds2);auto.
destruct (range_typ_dec r1 r).
subst.
inversion H;subst.
clear H.
simpl in *. destruct a0;auto.
destruct (atom_eq_dec (AIdent s) a2 );auto.
apply IHdso with (ds3:=v) (ds2:=ds2);auto. inversion H.
inversion H. inversion H. inversion H. inversion H. inversion H. 
Qed.

Lemma mergeDataFuncUpdate3':
  forall (dso ds1 ds2 : value_env) (ds3 : list (atom * (typ * range_typ))) (a : atom),
    Result ds3 = mergeDataStateFunc dso ds1 ds2 ->
    getValue a dso <> getValue a ds2 ->
  (getValue a ds3 = getValue a ds2). 
Proof.
 intro dso. induction dso;intros;simpl.
       - destruct ds1.  destruct ds2.  simpl in H.  inversion H. simpl. auto.
         simpl in H. inversion H. simpl in H. inversion H. 
- simpl in H. destruct a. destruct p. 
destruct ds1. inversion H.
destruct p. destruct p. 
destruct ds2. inversion H. 
destruct p. destruct p.
destruct (atom_eq_dec a a1).
destruct (atom_eq_dec a a2).    
destruct (typ_eq_dec t t0).
destruct (typ_eq_dec t t1). 
 remember (mergeDataStateFunc dso ds1 ds2).
destruct e3.              
destruct (range_typ_dec r0 r1).
subst. 
inversion H;subst.
simpl in *.  
destruct a0;auto.   
destruct (atom_eq_dec (AIdent s) a2). auto. 
apply IHdso with (ds1:=ds1) (ds3:=v) (ds2:=ds2);auto.
subst. 
destruct (range_typ_dec r0 r).
subst. inversion H;subst. clear H.
simpl in *. destruct a0;auto.
destruct (atom_eq_dec (AIdent s) a2 );auto. 

apply IHdso with (ds1:=ds1) (ds3:=v) (ds2:=ds2);auto.
destruct (range_typ_dec r1 r).
subst.
inversion H;subst.
clear H.
simpl in *. destruct a0;auto.
destruct (atom_eq_dec (AIdent s) a2 );auto.
contradiction. apply IHdso with (ds1:=ds1) (ds3:=v) (ds2:=ds2);auto. inversion H.
inversion H. inversion H. inversion H. inversion H. inversion H. 
Qed.


Lemma innerCombineConfEq: forall M l (conf conf1:configuration M) c v ,
    Some c = innerCombineFunc'''' conf l ->
    In conf1 l ->    
    getValue v (datastate conf) <> getValue v (datastate conf1) ->
    getValue v (datastate c) = getValue v (datastate conf1).
Proof.
   intros M l.
  induction l.
  -
    intros.  inversion H0.
  -  intros.
     simpl in *.
     destruct l.
     remember (mergeConfigFunc' conf conf a).
     destruct e;inversion H.
     subst.
     destruct H0. 
     Focus 2.      
     inversion H0.
     subst.
     
     unfold   mergeConfigFunc' in Heqe.
     remember (mergeDataStateFunc (datastate conf) (datastate conf) (datastate conf1)).
     destruct e;inversion Heqe.
     clear H2.
     destruct ( mergeControlStateFunc (controlstate conf) (controlstate conf) (controlstate conf1));inversion Heqe.
     subst;simpl in *.   clear Heqe. clear H.
     SearchAbout mergeDataStateFunc.
     remember Heqe0. 
     clear Heqe.      
       
     apply mergeDataFuncUpdate2 with (a:=v) in Heqe0;auto.
     destruct Heqe0. symmetry in H.
     apply mergeDataFuncUpdateRev with (a:=v) in e;auto.    rewrite <- H;auto.
     auto.
   
     remember (innerCombineFunc'''' conf (c0 :: l)).
     destruct o;inversion H. clear H3.
     remember (mergeConfigFunc' conf a c1).
     destruct e;inversion H.   subst.
     destruct H0;subst.
     Check mergeDataFuncUpdateRev.
     unfold   mergeConfigFunc' in Heqe.
     remember (mergeDataStateFunc (datastate conf) (datastate conf1) (datastate c1)).
     destruct e;inversion Heqe.
     clear H2.
     destruct ( mergeControlStateFunc (controlstate conf) (controlstate conf1) (controlstate c1));inversion Heqe.
     subst;simpl.   clear Heqe. clear H.
     remember Heqe0.   clear Heqe.    apply mergeDataFuncUpdate2 with (a:=v) in Heqe0;auto.
     destruct Heqe0;auto.
     pose proof mergeDataFuncUpdate3.
     apply H0 with (a:=v) in e;auto.   rewrite <- H in e.    auto.
     apply IHl with (conf1:=conf1) (v:=v) in Heqo;auto.
     rewrite <- Heqo in H1.
      unfold   mergeConfigFunc' in Heqe.
     remember (mergeDataStateFunc (datastate conf) (datastate a) (datastate c1)).
     destruct e;inversion Heqe.
     clear H3.
     destruct ( mergeControlStateFunc (controlstate conf) (controlstate a) (controlstate c1));inversion Heqe.
     subst;simpl.   clear Heqe. clear H.
     pose proof mergeDataFuncUpdate3'. rewrite <- Heqo. 
     apply H with (dso:=datastate conf) (ds1:=datastate a) ;auto.      
    Qed.
  


Lemma diamondDS: forall M (conf conf1 conf2 conf1': configuration M)  e1 e2 v, 
(forall v1 v2 , In v1 (dom (datastate conf)) -> In v2 (dom (datastate conf)) ->
updateVarEv M (eventDefinition e1)  v1 -> updateVarEv M (eventDefinition e2) v2 -> v1 <> v2) -> 
(forall v1 v2 , In v1 (dom (datastate conf)) -> In v2 (dom (datastate conf)) ->
updateVarEv M (eventDefinition e1)  v1 -> usedVarEv M (eventDefinition e2) v2 -> v1 <> v2) ->
(forall v1 v2 , In v1 (dom (datastate conf)) -> In v2 (dom (datastate conf)) ->
updateVarEv M (eventDefinition e2)  v1 -> usedVarEv M (eventDefinition e1) v2 -> v1 <> v2)  ->
(forall ev1 ev2, In ev1 (events M) -> In ev2 (events M) -> raisedEv M (eventDefinition e1) ev1 -> 
       eventKind ev1 = Internal -> eventKind ev2 = Internal ->          raisedEv M (eventDefinition e2) ev2 -> ev1 <> ev2) ->
(forall sce1 sce2, In sce1 (dom (controlstate conf)) -> In sce2 (dom (controlstate conf)) ->  In (eventDefinition e1) (alphabet sce1) -> In (eventDefinition e2) (alphabet sce2) -> sce1 <> sce2) ->
WellFormed M ->
e1 <> e2 ->
correct_configuration conf -> synchrony conf conf1 e1 ->  synchrony conf conf2 e2 ->
synchrony conf1 conf1' e2 ->
In v (dom (datastate conf)) ->
~ updateVarEv M (eventDefinition e1) v ->
updateVarEv M (eventDefinition e2) v ->
 getValue v (datastate conf1') = getValue v (datastate conf2). 
Proof.
  intros. 
  pose proof diamondDSNoChange.
  assert ( getValue v (datastate conf) = getValue v (datastate conf1)).
 apply H13 with (e1:=e1) (e2:=e2);auto.   
 SearchAbout getValue.
 remember H7 as sync1. 
 clear Heqsync1.
 remember H8 as sync2.
 clear Heqsync2.
 remember H9 as sync3.
 clear Heqsync3.
 unfold synchrony in H7,H8,H9.
  repeat match goal with
        | [ H: _ /\ _ |- _ ] => destruct H
        | [ H: exists _, _ |- _] => destruct H
         end.
  unfold combineFunc in H15, H16.
  remember (constructConfigList (dom (controlstate conf)) e2 conf).
  destruct e;inversion H16.
  clear H19.
  remember (constructConfigList (dom (controlstate conf1)) e2 conf1).
  destruct e;inversion H15.
  clear H19.
  destruct v0;inversion H16.
  clear H19.
  destruct v1;inversion H15.
  clear H19.
  unfold constructConfigList in Heqe.
  unfold constructConfigList in Heqe0.
  remember ( innerCombineFunc'''' conf (c :: v0) ).
  destruct o;inversion H16.
  remember (innerCombineFunc'''' conf1 (c0 :: v1)).
   destruct o;inversion H15.
   unfold removeEventFromConf;simpl.
 
   assert (dom (controlstate conf) = dom (controlstate conf1)).
  apply domControlSync with (e:=e1);auto.
  rewrite <- H18 in Heqe0.
  Check filterEqual. 
  assert ((filter
              (fun x : scenario => inList event_definition_dec (eventDefinition e2) (alphabet x))
              (filterList (finishedscenarios conf) (dom (controlstate conf)) scenario_dec)) =
          (filter
               (fun x : scenario => inList event_definition_dec (eventDefinition e2) (alphabet x))
               (filterList (finishedscenarios conf1) (dom (controlstate conf)) scenario_dec))).
  apply   filterEqual;auto.
  unfold incl;intros.
  apply finishedInvariantSync with (conf:=conf) (e:=e1);auto.   
  intros.
  apply  inListFalse;auto.
  unfold not;intros.
  assert (correct_configuration conf1).
  destruct H4.
   repeat match goal with
        | [ H: _ /\ _ |- _ ] => destruct H
        | [ H: exists _, _ |- _] => destruct H
          end.
   destruct H26.
    repeat match goal with
        | [ H: _ /\ _ |- _ ] => destruct H
        | [ H: exists _, _ |- _] => destruct H
          end.

    apply termL5 with (conf:=conf) (e:=e1);auto.
  destruct H6;intuition. 
  rename H24 into corr.
  assert (In a (dom (controlstate conf))).
  rewrite domControlSync with (conf':=conf1) (e:=e1);auto.
  destruct corr.
  unfold  scenarioInclusion in inclusion.
  unfold incl in inclusion;apply inclusion;auto.
  rename H24 into inad.   
  apply H3 with (sce1:=a) in H23;auto.     
  
  apply syncFinish with (M:=M) (conf:=conf) (conf':=conf1);auto.
 
  rewrite H21 in Heqe.
  

  assert (forall sce c3 c4, In sce (filter
              (fun x : scenario => inList event_definition_dec (eventDefinition e2) (alphabet x))
              (filterList (finishedscenarios conf1) (dom (controlstate conf)) scenario_dec)) ->
                            Result c3 = constructConfig sce e2 conf ->
                            Result c4 = constructConfig sce e2 conf1 ->
                           getValue v (datastate c3) = getValue v (datastate c4)
         ).
  intros.
  remember H4. clear Heqw.  
  
  unfold  WellFormed in H4.

     repeat match goal with
            | [ H: _ /\ _ |- _ ] => destruct H

            end.
     destruct H27.
    repeat match goal with
            | [ H: _ /\ _ |- _ ] => destruct H

            end.    
    apply constructConfigVarEqual' with (conf:=conf) (conf1:=conf1) (sce:=sce) (e1:=e1) (e2:=e2);auto.  apply H37;auto.
     rewrite <- cs_consist with (conf0:=conf);auto.
    apply filter_In in H22.
    destruct H22.    apply filterL2 in H22. auto.
    intros.
   
    assert ( ~ updateVarEv M (eventDefinition e1) v2 ).
    unfold not;intros.
    unfold not in H0.
    apply H0 with (v1:=v2) (v2:=v2);auto.
    SearchAbout updateVarEv.
    apply H13 with (e1:=e1) (e2:=e2);auto.
     apply filter_In in H22. destruct H22. apply filterL2 in H22.
     destruct H6.   rewrite <-  cs_consist;auto.
     unfold stateSceProp in H41.
     SearchAbout stateScenarioMap.
     apply filter_In in H22. destruct H22. SearchAbout inList.
     eapply reverseinListLemma;auto. apply H43. 
     SearchAbout (getScenarioState _ _ = getScenarioState _ _).
     pose proof synchronyFinishedUnchanged. 
     assert ( forall sce : scenario,
        In sce (scenarios M) ->
        In (eventDefinition e2) (alphabet sce) ->
        ~ In sce (finishedscenarios conf) ->
        ~ In sce (finishedscenarios conf1) /\
        getScenarioState sce (controlstate conf) = getScenarioState sce (controlstate conf1)).
     apply H43 with (e1:=e1);auto.
     intros.
     assert (In sce1 (dom (controlstate conf))).
    destruct H6. rewrite cs_consist;auto. 
     apply H3;auto.
     destruct H6. rewrite cs_consist;auto. 
  
  
     assert (~ In sce (finishedscenarios conf1) /\
             getScenarioState sce (controlstate conf) = getScenarioState sce (controlstate conf1)).
     apply H44;auto.
     SearchAbout sce.
      apply filter_In in H22. destruct H22. apply filterL2 in H22. destruct H6. rewrite  cs_consist in H22;auto.  apply filter_In in H22. destruct H22. 
      eapply reverseinListLemma;auto. apply H45.
      rewrite <- H21 in H22. 
      apply filter_In in H22. destruct H22. apply filterL1 in H22.
auto.       destruct H45;auto. 
  


  
  assert ( getValue v (datastate conf) =  getValue v (datastate c1) \/ ~ (getValue v (datastate conf) =  getValue v (datastate c1))).
  apply excluded_middle.
  destruct H23.
  rewrite <- H23.
  rewrite H14.
  SearchAbout getValue.
  simpl in Heqo.
 
pose proof innerCombineEq. 
assert (    forall conf' : configuration M,
           In conf' (c :: v0)  -> getValue v (datastate conf') = getValue v (datastate conf)).
apply H24 with (c:=c1);auto. 
destruct H6.
 rewrite <- dom2dom'. rewrite  ds_dom_eq. destruct correct_mon.
auto.
assert (forall conf' : configuration M,
           In conf' (c0 :: v1) -> getValue v (datastate conf') = getValue v (datastate conf)).
intros.
symmetry.
assert (exists sce : scenario, In sce (filter
              (fun x : scenario => inList event_definition_dec (eventDefinition e2) (alphabet x))
              (filterList (finishedscenarios conf1) (dom (controlstate conf)) scenario_dec)) /\ Result conf' = constructConfig sce e2 conf1).
apply termL2 with (lst:=c0::v1);auto. 
destruct H27. destruct H27.
assert ( exists conf' : configuration M, Result conf' = constructConfig x e2 conf).
Check termL2'. 
apply termL2' with (scs:=(filter
              (fun x : scenario => inList event_definition_dec (eventDefinition e2) (alphabet x))
              (filterList (finishedscenarios conf1) (dom (controlstate conf)) scenario_dec))) (lst:=c::v0);auto. 
destruct H29.
assert (getValue v (datastate x0) = getValue v (datastate conf')).

apply H22 with (sce:=x);auto.
rewrite <- H30. symmetry in H25. apply H25;auto.
eapply constructIn;auto. 
apply Heqe. apply H27. auto.
pose proof innerCombineEq'.

apply H27 with (l:=c0::v1) ;auto. 
SearchAbout conf1.
assert (correct_configuration conf1).
destruct H4.
repeat match goal with
            | [ H: _ /\ _ |- _ ] => destruct H

       end.
destruct H30.
repeat match goal with
            | [ H: _ /\ _ |- _ ] => destruct H

       end.

apply termL5 with (e:=e1) (conf:=conf);auto. 
destruct H6. 
intuition.

destruct H28.
rewrite <- dom2dom'. 
destruct correct_mon.
rewrite  ds_dom_eq;auto. 
SearchAbout v.

assert (correct_configuration conf1).
destruct H4.
repeat match goal with
            | [ H: _ /\ _ |- _ ] => destruct H

       end.
destruct H30.
repeat match goal with
            | [ H: _ /\ _ |- _ ] => destruct H

       end.

apply termL5 with (e:=e1) (conf:=conf);auto. 
destruct H6. 
intuition.

destruct H28.
rewrite <- dom2dom'. 
rewrite  ds_dom_eq;auto.

destruct H6. 
rewrite <- ds_dom_eq0;auto.
SearchAbout dom2.
rewrite dom2dom';auto.

intros.

rewrite <-  H14. 
apply H26;auto. 
SearchAbout v. 
destruct H6.
SearchAbout tyEnv.
apply tyEnvVar with (a:=v) in ds_tyEnv;auto. 
destruct ds_tyEnv. 
exists x;auto.

pose proof innerCombineExistConf.
assert (exists conf' : configuration M,
           In conf' (c :: v0)  /\ getValue v (datastate c1) = getValue v (datastate conf')).
apply H24 with (conf:=conf);auto.
destruct H6.
 apply tyEnvVar with (a:=v) in ds_tyEnv;auto.
destruct ds_tyEnv. 
exists x;auto.
destruct H25.
destruct H25.
Check termL2.
assert (exists sce : scenario, In sce ( filter
          (fun x : scenario => inList event_definition_dec (eventDefinition e2) (alphabet x))
          (filterList (finishedscenarios conf1) (dom (controlstate conf)) scenario_dec)) /\ Result x = constructConfig sce e2 conf).
apply termL2 with (e:=e2) (lst:=(c :: v0));auto.
destruct H27.
destruct H27.
Check termL2'.
assert (exists conf' : configuration M, Result conf' = constructConfig x0 e2 conf1
       ).
apply termL2' with (scs:=(filter
              (fun x : scenario => inList event_definition_dec (eventDefinition e2) (alphabet x))
              (filterList (finishedscenarios conf1) (dom (controlstate conf)) scenario_dec))) (lst:=c0::v1);auto. 
destruct H29.
assert ( getValue v (datastate x) = getValue v (datastate x1)).
apply H22 with (sce:=x0);auto. 
rewrite H30 in H26. rewrite H26.
assert (In x1 (c0::v1)).
eapply constructIn;auto. 
apply Heqe0. apply H27. 
auto.
assert (getValue v (datastate x1) <> getValue v (datastate conf1)).
rewrite <- H26. auto. unfold not;intros. apply H23.  rewrite  H14. auto.
pose proof innerCombineConfEq.
apply H33 with (conf:=conf1) (l:=c0::v1);auto.
Qed.

Lemma diamondDS': forall M (conf conf1 conf2 conf2': configuration M)  e1 e2 v, 
(forall v1 v2 , In v1 (dom (datastate conf)) -> In v2 (dom (datastate conf)) ->
updateVarEv M (eventDefinition e1)  v1 -> updateVarEv M (eventDefinition e2) v2 -> v1 <> v2) -> 
(forall v1 v2 , In v1 (dom (datastate conf)) -> In v2 (dom (datastate conf)) ->
updateVarEv M (eventDefinition e1)  v1 -> usedVarEv M (eventDefinition e2) v2 -> v1 <> v2) ->
(forall v1 v2 , In v1 (dom (datastate conf)) -> In v2 (dom (datastate conf)) ->
updateVarEv M (eventDefinition e2)  v1 -> usedVarEv M (eventDefinition e1) v2 -> v1 <> v2)  ->
(forall ev1 ev2, In ev1 (events M) -> In ev2 (events M) -> raisedEv M (eventDefinition e1) ev1 -> 
           eventKind ev1 = Internal -> eventKind ev2 = Internal ->      raisedEv M (eventDefinition e2) ev2 -> ev1 <> ev2) ->
(forall sce1 sce2, In sce1 (dom (controlstate conf)) -> In sce2 (dom (controlstate conf)) -> In (eventDefinition e1) (alphabet sce1) -> In (eventDefinition e2) (alphabet sce2) -> sce1 <> sce2) ->
WellFormed M ->
e1 <> e2 ->
correct_configuration conf -> synchrony conf conf1 e1 ->  synchrony conf conf2 e2 ->
synchrony conf2 conf2' e1 ->
In v (dom (datastate conf)) ->
 updateVarEv M (eventDefinition e1) v ->
~updateVarEv M (eventDefinition e2) v ->
 getValue v (datastate conf2') = getValue v (datastate conf1).
Proof.
  pose proof diamondDS.
  intros.
  apply H with (conf:=conf) (conf1:=conf2) (e1:=e2) (e2:=e1);auto.
  intros.
  assert (v2 <> v1). 
  apply H0;auto. unfold not;intros. apply H18;auto.
  intros.
  assert (ev2 <> ev1).
  apply H3;auto.   unfold not;intros. apply H20;auto.
  intros.
  unfold not;intros.
  unfold not in H4.   apply H4 with (sce1:=sce2) (sce2:=sce1);auto.
  
Qed.

  
  
Lemma diamondDSAll: forall M (conf conf1 conf2 conf1' conf2': configuration M)  e1 e2 v, 
(forall v1 v2 , In v1 (dom (datastate conf)) -> In v2 (dom (datastate conf)) ->
updateVarEv M (eventDefinition e1)  v1 -> updateVarEv M (eventDefinition e2) v2 -> v1 <> v2) -> 
(forall v1 v2 , In v1 (dom (datastate conf)) -> In v2 (dom (datastate conf)) ->
updateVarEv M (eventDefinition e1)  v1 -> usedVarEv M (eventDefinition e2) v2 -> v1 <> v2) ->
(forall v1 v2 , In v1 (dom (datastate conf)) -> In v2 (dom (datastate conf)) ->
updateVarEv M (eventDefinition e2)  v1 -> usedVarEv M (eventDefinition e1) v2 -> v1 <> v2)  ->
(forall ev1 ev2, In ev1 (events M) -> In ev2 (events M) -> raisedEv M (eventDefinition e1) ev1 -> 
              eventKind ev1 = Internal -> eventKind ev2 = Internal ->   raisedEv M (eventDefinition e2) ev2 -> ev1 <> ev2) ->
(forall sce1 sce2, In sce1 (dom (controlstate conf)) -> In sce2 (dom (controlstate conf)) ->  In (eventDefinition e1) (alphabet sce1) -> In (eventDefinition e2) (alphabet sce2) -> sce1 <> sce2) ->
WellFormed M ->
e1 <> e2 ->
correct_configuration conf -> synchrony conf conf1 e1 ->  synchrony conf conf2 e2 ->
synchrony conf1 conf1' e2 -> synchrony conf2 conf2' e1 ->
In v (dom (datastate conf)) ->
 getValue v (datastate conf1') =  getValue v (datastate conf2'). 
Proof.
  intros.
  assert (updateVarEv M (eventDefinition e1)  v \/ ~ updateVarEv M (eventDefinition e1)  v).
  apply excluded_middle.
  destruct H12.
  assert (~ updateVarEv M (eventDefinition e2) v).
  unfold not;intros.
  unfold not in H.   apply H with (v1:=v) (v2:=v);auto.
  pose proof diamondDS'.
  assert (getValue v (datastate conf2') = getValue v (datastate conf1)).
  apply H14 with (conf:=conf) (conf2:=conf2) (e1:=e1) (e2:=e2);auto.
  rewrite H15.   
  SearchAbout updateVarEv. 
  symmetry.
  apply diamondDSNoChange with (e1:=e2) (e2:=e1);auto.
  unfold WellFormed in H4.
  repeat match goal with
            | [ H: _ /\ _ |- _ ] => destruct H

       end.
destruct H18.
repeat match goal with
            | [ H: _ /\ _ |- _ ] => destruct H

       end.
apply termL5 with (conf:=conf) (e:=e1);auto.
unfold synchrony in H7. destruct H6.
apply  raised_wellform' ;intuition;auto.
assert (updateVarEv M (eventDefinition e2)  v \/ ~ updateVarEv M (eventDefinition e2)  v).
 apply excluded_middle.
 destruct H13.

 pose proof diamondDS.
 assert (getValue v (datastate conf1') = getValue v (datastate conf2)).
  apply H14 with (conf:=conf) (conf1:=conf1) (e1:=e1) (e2:=e2);auto.
  rewrite H15.

  apply diamondDSNoChange with (e1:=e1) (e2:=e2);auto.
  unfold WellFormed in H4.
  repeat match goal with
            | [ H: _ /\ _ |- _ ] => destruct H

       end.
destruct H18.
repeat match goal with
            | [ H: _ /\ _ |- _ ] => destruct H

       end.
apply termL5 with (conf:=conf) (e:=e2);auto.

unfold synchrony in H8. destruct H6.
apply  raised_wellform' ;intuition;auto.
pose proof diamondDSNoChange.
assert ( getValue v (datastate conf) = getValue v (datastate conf1)).
apply H14 with (e1:=e1) (e2:=e2);auto.
assert ( getValue v (datastate conf) = getValue v (datastate conf2)).
apply H14 with (e1:=e2) (e2:=e1);auto.
assert ( getValue v (datastate conf1) = getValue v (datastate conf1')).
apply H14 with (e1:=e2) (e2:=e1);auto.
 unfold WellFormed in H4.
  repeat match goal with
            | [ H: _ /\ _ |- _ ] => destruct H

       end.
destruct H19.
repeat match goal with
            | [ H: _ /\ _ |- _ ] => destruct H

       end.
apply termL5 with (conf:=conf) (e:=e1);auto.

unfold synchrony in H7. destruct H6.
apply  raised_wellform' ;intuition;auto.

assert ( getValue v (datastate conf2) = getValue v (datastate conf2')).
apply H14 with (e1:=e1) (e2:=e2);auto.

 unfold WellFormed in H4.
  repeat match goal with
            | [ H: _ /\ _ |- _ ] => destruct H

       end.
destruct H20.
repeat match goal with
            | [ H: _ /\ _ |- _ ] => destruct H

       end.
apply termL5 with (conf:=conf) (e:=e2);auto.

unfold synchrony in H8. destruct H6.
apply  raised_wellform' ;intuition;auto.
rewrite <- H17;rewrite <- H18. 
rewrite <- H15;rewrite <- H16;auto. 
  
Qed.  

                                  
Lemma diamondCSNoChange
     : forall (M : monitor) (conf conf1 : configuration M) (e1  : raisedEvent) sce,
       WellFormed M ->
       correct_configuration conf ->
       synchrony conf conf1 e1 ->
       ~ In (eventDefinition e1) (alphabet sce) ->
       getScenarioState sce (controlstate conf) = getScenarioState sce (controlstate conf1). 
Proof.
  intros.
  remember H1.
  clear Heqs.
  unfold synchrony in s.
  destruct s.
  unfold combineFunc in H4.
  remember (constructConfigList (dom (controlstate conf)) e1 conf).
  destruct e;inversion Heqe.
  Focus 2.   inversion H4.
  unfold constructConfigList in Heqe.
  assert (~ In sce (filter
              (fun x : scenario => inList event_definition_dec (eventDefinition e1) (alphabet x))
              (filterList (finishedscenarios conf) (dom (controlstate conf)) scenario_dec))).
  unfold not;intros.
  apply filter_In in H5.
  destruct H5.
  SearchAbout inList.
  apply  reverseinListLemma in H7.
  contradiction.
  SearchAbout (getScenarioState _ (controlstate _) = getScenarioState _ (controlstate _)).
  pose proof innerCombineFuncVarScenarioStateNoChange.
  
  destruct v;inversion H4.
  clear H9.
  remember ( innerCombineFunc'''' conf (c :: v)).
  destruct o;inversion H4.
  simpl.
  apply H7 with (v0:=c::v) (re:=e1) (sceList:=(filter
              (fun x : scenario => inList event_definition_dec (eventDefinition e1) (alphabet x))
              (filterList (finishedscenarios conf) (dom (controlstate conf)) scenario_dec)) ) ;auto.
  unfold incl;intros.
  apply filter_In in H8.
  destruct H8.
  apply filterL2 in H8;auto.   
  
Qed.

Lemma syncFinishedNoChange: forall M (conf conf': configuration M) e sce,
    
    synchrony conf conf' e ->
    In sce (finishedscenarios conf) ->
    correct_configuration conf ->
    getScenarioState sce (controlstate conf) = getScenarioState sce (controlstate conf').
Proof.
  intros.
 rename H1 into correct. 
  remember H.
  clear Heqs.
  unfold synchrony in s.
  destruct s.
  unfold combineFunc in H2.
  remember (constructConfigList (dom (controlstate conf)) e conf).
  destruct e0;inversion H2.
  destruct v;inversion H2.
  clear H5.
  
  remember ( innerCombineFunc'''' conf (c :: v)).
  destruct o;inversion H2.
  simpl.
  unfold constructConfigList in Heqe0.
  assert (~ In sce (filter
               (fun x : scenario => inList event_definition_dec (eventDefinition e) (alphabet x))
               (filterList (finishedscenarios conf) (dom (controlstate conf)) scenario_dec)) ).
  unfold not;intros.
  apply filter_In in H3.
  destruct H3.
  apply filterL1 in H3.
  contradiction.
  pose proof innerCombineFuncVarScenarioStateNoChange.
  apply H6 with (v0:=c::v) (re:=e) (sceList:=(filter
               (fun x : scenario => inList event_definition_dec (eventDefinition e) (alphabet x))
               (filterList (finishedscenarios conf) (dom (controlstate conf)) scenario_dec))) ;auto.
  unfold incl;intros.
  apply filter_In in H7.
  destruct H7.
  apply filterL2 in H7;auto. 
Qed.


Lemma updateSceStateEq: forall (env env1: scenario_env) sce st,
    dom env = dom env1 ->
    In sce (dom env) ->
    getScenarioState sce (updateScenarioState' sce st env) =
    getScenarioState sce (updateScenarioState' sce st env1). 
Proof.
  intro env;induction env.
  -  intros.
     inversion H0.
  - intros.
    destruct env1.
    inversion H.
    simpl in *.
    destruct a.
    simpl in *.
    destruct H0;subst.
    destruct p;simpl in *.
    inversion H;subst.
    destruct (string_dec (scenarioId s) (scenarioId s)).
    simpl.
    destruct (string_dec (scenarioId s) (scenarioId s)).
    auto.
    contradiction.
    contradiction.
    destruct p;simpl in *.
    inversion H.
    subst.     
    apply IHenv with (env1:=env1) (st:=st) in H0;auto.
    destruct (string_dec (scenarioId s1) (scenarioId sce)).
    simpl.
    destruct (string_dec (scenarioId s1) (scenarioId sce)).
    subst.               
    destruct (string_dec (scenarioId sce) (scenarioId s1));auto.
    contradiction. 
    simpl.
    destruct (string_dec (scenarioId sce) (scenarioId s1)).
    symmetry in e.
    contradiction.
    auto.     
    
Qed.

Lemma constructConfigSceStateEqual: forall M (conf conf1 conf' conf'': configuration M) sce e1 e2 ,
    correct_configuration conf ->
    synchrony conf conf1 e1 ->
    e1 <> e2 ->
    stateEvDefInstanceMapEquiv M ->
    correctStateEvStepMap' M ->
    stepExistsMon' M sce ->   
    (forall v,  In v (dom (datastate conf)) -> usedVarEv M (eventDefinition e2) v -> getValue v (datastate conf) = getValue v (datastate conf1)) ->
    In sce (scenarios M) ->
    In (eventDefinition e2) (alphabet sce) ->
    getScenarioState sce (controlstate conf) = getScenarioState sce (controlstate conf1) ->
    Result conf' = constructConfig sce e2 conf ->
    Result conf'' = constructConfig sce e2 conf1 ->
    In e2 (raisedevents conf) ->
    typeCheck M ->
    transEvMapEventInstanceProp M ->
    transEvMapProp M ->
    stpStMapEquiv' M ->
    stateEvDefInstanceMapEquivEListProp M ->
    stateSceIn M ->
    getScenarioState sce (controlstate conf') = getScenarioState sce (controlstate conf''). 
Proof.
  intros. rename H13 into transInProp.
  rename H14 into transProp.
  rename H15 into stpEquiv.
  rename H16 into stateMapEquivProp.
  rename H17 into stateIn.
  unfold constructConfig in *.
  rewrite <- H8 in H10.
  remember (getScenarioState sce (controlstate conf) ).
  destruct o;inversion H9.
  clear H14.
  remember (transEvMapFunc (stateEvDefInstanceMap M) (Some s, Some (eventDefinition e2)) ).
  destruct o;inversion H10.
  clear H14.
  assert (findEventInstance e2 (datastate conf) l = findEventInstance e2 (datastate conf1) l).
  apply findEventValueEq;auto.

  
  intros.

  assert (In v (dom (datastate conf)) \/ ~ In v (dom (datastate conf))). 
  apply excluded_middle.
  destruct H15.
    
  
  apply H5;auto.
 

  unfold usedVarEv.
  exists sce. split.
  Focus 2.
 


 
  apply basic_ts;auto.
     rename H15 into vdd. 
  unfold correctStateEvStepMap' in H3.
  unfold stepExistsMon' in H4.
  unfold stateEvDefInstanceMapEquiv in H2. 
  assert (exists stp : step, In (s, ei, sce, Some stp) (stateEvStepMap' M)).
  apply H4  with (e:=(eventDefinition e2)) (l:=l);auto.

  rewrite semantic_rules.stateEvDefInstanceMapEquiv'. symmetry;auto. 
  destruct H2;auto.
  destruct H15.   
  apply H3 in H15.
  destruct H15.
  destruct H16.
  apply scenarioUsedVarIn with (stp:=x);auto.
  subst;auto.   

  SearchAbout getValue.
  rewrite getValueNone';auto.
  rewrite getValueNone';auto.
  
    
  assert (dom2 (datastate conf) = dom2 (datastate conf1)).
 
  apply syncDSDom2 with (e:=e1) ;auto.
  assert (dom (datastate conf) = dom (datastate conf1)).
  
  rewrite <- dom2dom'. 
  rewrite <- dom2dom'.
  rewrite H16;auto. 
  rewrite <- H17;auto.   
  
  assert (dom2 (datastate conf) = dom2 (datastate conf1)).
 
  apply syncDSDom2 with (e:=e1) ;auto.
  rewrite <- dom2dom'. 
  rewrite <- dom2dom'.    rewrite H13;auto. 
  intros.
    apply tyEnvVar with (env:=datastate conf);auto.  
  destruct H;auto.
  rewrite <- H13 in H10.
  remember (findEventInstance e2 (datastate conf) l).
  destruct o;inversion H9.
  clear H15.
  remember (createValueEnv (eventArgs e) (eventParams (eventDefinition e2)) (eventArguments e2)).
  destruct e0;inversion H9.
  clear H15.
  assert (getStep' conf sce e = getStep' conf1 sce e).
  unfold getStep'.
  rewrite <- Heqo.
  rewrite <- H8.
  auto.
  rewrite <- H14 in H10.
  remember (getStep' conf sce e).
           
  destruct o;inversion H9.
  clear H16.
        
  remember (configTransition (extendValEnv (datastate conf) v) e2 e sce s0 conf).
  destruct e0;inversion H9.
  subst.
  remember (configTransition (extendValEnv (datastate conf1) v) e2 e sce s0 conf1).
  destruct e0;inversion H10.
  subst.
  unfold configTransition in Heqe1,Heqe2.
  remember (execAction (extendValEnv (datastate conf) v, []) (stepActions s0)
              (filter
                 (fun e : event_definition =>
                  match eventKind e with
                  | Internal => true
                  | Imported => false
                  | Exported => true
                  end) (events M))).
  destruct e0;inversion Heqe1.
  clear H16.
  destruct v2.
  remember ( execAction (extendValEnv (datastate conf1) v, []) (stepActions s0)
              (filter
                 (fun e : event_definition =>
                  match eventKind e with
                  | Internal => true
                  | Imported => false
                  | Exported => true
                  end) (events M))).
  destruct e0;inversion Heqe2.
  clear H16.
  destruct v3.
  inversion Heqe1;subst;simpl.
  inversion Heqe2;subst;simpl.
  unfold extendValEnv in Heqe3, Heqe4.
  
  unfold updateControlState.
  pose proof updateSceStateEq.
  apply H15;auto.

  apply domControlSync with (e:=e1);auto.
  destruct H.
  rewrite cs_consist;auto.   
Qed.  



Lemma mergeCSEq1: forall  cso cs1 cs2 cs3 sce,
    In sce (dom cso) ->
    Result cs3 = mergeControlStateFunc cso cs1 cs2 ->
    getScenarioState sce cso = getScenarioState sce cs3 ->
    getScenarioState sce cs1 = getScenarioState sce cs2.
Proof.
  intro cso;induction cso;intros.
  - inversion H.
  -  simpl in *.
     destruct a.
     simpl in *.
     destruct H. subst.
     destruct (string_dec (scenarioId sce) (scenarioId sce)).
     Focus 2.  contradiction.
     destruct cs1.
     inversion H0.
     destruct cs2.
     destruct p. inversion H0.
     destruct p;destruct p0.
     destruct  (scenario_dec sce s).
     destruct (scenario_dec sce s2).
     subst.
     remember (mergeControlStateFunc cso cs1 cs2).
     destruct e0;inversion H0.
     clear H2.
     destruct (string_dec s1 s3).
     inversion H0;subst.
     simpl in *.
     destruct (string_dec (scenarioId s2) (scenarioId s2)).
     auto.
     contradiction.
     destruct (string_dec s1 s0).
     subst.
     inversion H0;subst.
     simpl in *.
     destruct (string_dec (scenarioId s2) (scenarioId s2)).
     auto.
     contradiction.
     destruct (string_dec s3 s0 ).
     subst.      
     inversion H0;subst.
     simpl in *.
     destruct (string_dec (scenarioId s2) (scenarioId s2)).
     auto.
     contradiction.
     inversion H0.      
     inversion H0.
     inversion H0.
        
     destruct cs1.
     inversion H0.
     destruct p.
     destruct cs2.      
     inversion H0.

       destruct p. 
     destruct  (scenario_dec s s1).
     destruct (scenario_dec s s3).
     subst.
     
     remember (mergeControlStateFunc cso cs1 cs2).
     destruct e;inversion H0.
     clear H3.
     destruct (string_dec s2 s4).
     inversion H0;subst.
     simpl in *.
     destruct (string_dec (scenarioId sce) (scenarioId s3)).
     auto.
     apply IHcso with (cs3:=v);auto.
           
     destruct (string_dec s2 s0).
     subst.
     inversion H0;subst.
     simpl in *.
     destruct (string_dec (scenarioId sce) (scenarioId s3)).
     auto.   apply IHcso with (cs3:=v);auto.
     destruct (string_dec s4 s0 ).
     subst.      
     inversion H0;subst.
     simpl in *.
     destruct (string_dec (scenarioId sce) (scenarioId s3)).
     auto.
     apply IHcso with (cs3:=v);auto.
     inversion H0.      
     inversion H0.
     inversion H0.
Qed.

Lemma mergeCSEq23: forall  cso cs1 cs2 cs3 sce,
    In sce (dom cso) ->
    Result cs3 = mergeControlStateFunc cso cs1 cs2 ->
    getScenarioState sce cs3 = getScenarioState sce cs1 \/
    getScenarioState sce cs3 = getScenarioState sce cs2.
Proof.
   intro cso;induction cso;intros.
  - inversion H.
  -  simpl in *.
     destruct a.
     simpl in *.
     destruct H. subst.
     destruct (string_dec (scenarioId sce) (scenarioId sce)).
     Focus 2.  contradiction.
     destruct cs1.
     inversion H0.
     destruct cs2.
     destruct p. inversion H0.
     destruct p;destruct p0.
     destruct  (scenario_dec sce s).
     subst. destruct (scenario_dec s s2).
     subst.
     remember (mergeControlStateFunc cso cs1 cs2).
     destruct e0;inversion H0.
     clear H1.
     destruct (string_dec s1 s3).
     inversion H0;subst.
     simpl in *.
     destruct (string_dec (scenarioId s2) (scenarioId s2)).
     auto.
     contradiction.
     destruct (string_dec s1 s0).
     subst.
     inversion H0;subst.
     simpl in *.
     destruct (string_dec (scenarioId s2) (scenarioId s2)).
     intuition;auto.  
     contradiction.
     destruct (string_dec s3 s0 ).
     subst.      
     inversion H0;subst.
     simpl in *.
     destruct (string_dec (scenarioId s2) (scenarioId s2)).
     auto.
     contradiction.
     inversion H0.      
     inversion H0.
     inversion H0.
        
     destruct cs1.
     inversion H0.
     destruct p.
     destruct cs2.      
     inversion H0.

       destruct p. 
     destruct  (scenario_dec s s1).
     destruct (scenario_dec s s3).
     subst.
     
     remember (mergeControlStateFunc cso cs1 cs2).
     destruct e;inversion H0.
     clear H2.
     destruct (string_dec s2 s4).
     inversion H0;subst.
     simpl in *.
     destruct (string_dec (scenarioId sce) (scenarioId s3)).
     auto.
     apply IHcso with (cs3:=v);auto.
           
     destruct (string_dec s2 s0).
     subst.
     inversion H0;subst.
     simpl in *.
     destruct (string_dec (scenarioId sce) (scenarioId s3)).
     auto.   apply IHcso with (cs3:=v);auto.
     destruct (string_dec s4 s0 ).
     subst.      
     inversion H0;subst.
     simpl in *.
     destruct (string_dec (scenarioId sce) (scenarioId s3)).
     auto.
     apply IHcso with (cs3:=v);auto.
     inversion H0.      
     inversion H0.
     inversion H0.
     
Qed.  

Lemma mergeCSEq4: forall  cso cs1 cs2 cs3 sce,
    In sce (dom cso) ->
    Result cs3 = mergeControlStateFunc cso cs1 cs2 ->
    getScenarioState sce cso <> getScenarioState sce cs3 ->
    getScenarioState sce cs1 <> getScenarioState sce cso \/
    getScenarioState sce cs2 <> getScenarioState sce cso.
Proof.

   intro cso;induction cso;intros.
  - inversion H.
  -  simpl in *.
     destruct a.
     simpl in *.
     destruct H. subst.
     destruct (string_dec (scenarioId sce) (scenarioId sce)).
     Focus 2.  contradiction.
     destruct cs1.
     inversion H0.
    
     destruct p. destruct cs2. inversion H0.
     destruct p. 
     destruct  (scenario_dec sce s).
     subst. destruct (scenario_dec s s2).
     subst.
     remember (mergeControlStateFunc cso cs1 cs2).
     destruct e0;inversion H0.
     destruct (string_dec s1 s3).
     subst.      inversion H0;subst.
     simpl in *.

       destruct (string_dec (scenarioId s2) (scenarioId s2)).
       auto.
       contradiction.
             
     destruct (string_dec s1 s0).
     subst.  inversion H0;subst. 
     simpl in  *.

      destruct (string_dec (scenarioId s2) (scenarioId s2)).
       auto.
       contradiction.

       
       destruct (string_dec s3 s0 ).
       subst.
      inversion H0;subst. 
      simpl in *.

          destruct (string_dec (scenarioId s2) (scenarioId s2)).
       auto.
       contradiction.


      inversion H0.      
     inversion H0.      inversion H0.

     destruct cs1.
     inversion H0.
     

     destruct p. destruct cs2. inversion H0.
     destruct p.

     destruct ( scenario_dec s s1).
     subst.
     destruct (scenario_dec s1 s3).
     subst.
          
   
      remember (mergeControlStateFunc cso cs1 cs2).
     destruct e;inversion H0.

     destruct (string_dec s2 s4).
     subst. inversion H0;subst.
     simpl in *.
     destruct ( string_dec (scenarioId sce) (scenarioId s3)).
    auto. 
    apply IHcso with (cs3:=v);auto.

     destruct (string_dec s2 s0).
     subst.
     inversion H0;subst.
     simpl in *. 
     destruct ( string_dec (scenarioId sce) (scenarioId s3)).
    auto. 
    apply IHcso with (cs3:=v);auto.
         
       destruct (string_dec s4 s0).
     subst. inversion H0;subst.
     simpl in *.
     destruct ( string_dec (scenarioId sce) (scenarioId s3)).
    auto. 
    apply IHcso with (cs3:=v);auto.

    
     inversion H0.      
     inversion H0.
     inversion H0.
        
Qed.


Lemma mergeCSEq4': forall  cso cs1 cs2 cs3 sce,
    In sce (dom cso) ->
    Result cs3 = mergeControlStateFunc cso cs1 cs2 ->
    getScenarioState sce cso <> getScenarioState sce cs2 ->
    getScenarioState sce cs2 = getScenarioState sce cs3.

Proof.
  
   intro cso;induction cso;intros.
  - inversion H.
  -  simpl in *.
     destruct a.
     simpl in *.
     destruct H. subst.
     destruct (string_dec (scenarioId sce) (scenarioId sce)).
     Focus 2.  contradiction.
     destruct cs1.
     inversion H0.
    
     destruct p. destruct cs2. inversion H0.
     destruct p. 
     destruct  (scenario_dec sce s).
     subst. destruct (scenario_dec s s2).
     subst.
     remember (mergeControlStateFunc cso cs1 cs2).
     destruct e0;inversion H0.
     destruct (string_dec s1 s3).
     subst.      inversion H0;subst.
     simpl in *.

       destruct (string_dec (scenarioId s2) (scenarioId s2)).
       auto.
       contradiction.
             
     destruct (string_dec s1 s0).
     subst.  inversion H0;subst. 
     simpl in  *.

      destruct (string_dec (scenarioId s2) (scenarioId s2)).
       auto.
       contradiction.

       
       destruct (string_dec s3 s0 ).
       subst.
      inversion H0;subst. 
      simpl in *.

          destruct (string_dec (scenarioId s2) (scenarioId s2)).
      
       contradiction.
       contradiction.
         

      inversion H0.      
     inversion H0.      inversion H0.

     destruct cs1.
     inversion H0.
     

     destruct p. destruct cs2. inversion H0.
     destruct p.

     destruct ( scenario_dec s s1).
     subst.
     destruct (scenario_dec s1 s3).
     subst.
          
   
      remember (mergeControlStateFunc cso cs1 cs2).
     destruct e;inversion H0.

     destruct (string_dec s2 s4).
     subst. inversion H0;subst.
     simpl in *.
     destruct ( string_dec (scenarioId sce) (scenarioId s3)).
    auto. 
    apply IHcso with (cs1:=cs1) (cs3:=v);auto.

     destruct (string_dec s2 s0).
     subst.
     inversion H0;subst.
     simpl in *. 
     destruct ( string_dec (scenarioId sce) (scenarioId s3)).
    auto. 
    apply IHcso with (cs1:=cs1)  (cs3:=v);auto.
         
       destruct (string_dec s4 s0).
     subst. inversion H0;subst.
     simpl in *.
     destruct ( string_dec (scenarioId sce) (scenarioId s3)).
 contradiction.     auto. 
   apply IHcso with (cs1:=cs1)  (cs3:=v);auto.
     inversion H0.      
     inversion H0.
     inversion H0.

Qed.


  
Lemma innerSceStateEq: forall M l sceList (conf: configuration M) e  c sce,
    
    Result l = constructConfigList' sceList e conf ->
    Some c = innerCombineFunc'''' conf l ->
    In sce sceList ->
    incl sceList (dom (controlstate conf)) ->
    uniqList sceList ->
    correct_configuration conf ->
    (exists x,
        In x l /\
        Result x = constructConfig sce e conf /\ getScenarioState sce (controlstate c) = getScenarioState sce (controlstate x)). 
Proof.
  intros M l;induction l.
  - intros. simpl in *.  inversion H0.
  -  intros. rename H4 into corr. 
     destruct sceList. inversion H1. 
     simpl in H.
     
     
     remember (constructConfig s e conf ).
     destruct e0;inversion H.
     clear H5.
     remember (constructConfigList' sceList e conf).
     destruct e0;inversion H.
     subst. destruct H1;subst. 
     clear H.
     exists v. split;intuition;auto. 
     simpl in H0.
     destruct v0;inversion H0.
     clear H1.
     remember (mergeConfigFunc' conf conf v).
     destruct e0;inversion H0.
     subst.
     clear H0.
     Focus 2. clear H1.
     remember (innerCombineFunc'''' conf (c0 :: v0) ).
     destruct o;inversion H0.
     clear H1.
     remember (mergeConfigFunc' conf v c1).
     destruct e0;inversion H0.
     subst.  clear H0.
     SearchAbout (getScenarioState _ (controlstate _) = getScenarioState _ (controlstate _)).
     pose proof innerCombineFuncVarScenarioStateNoChange.
     assert ( getScenarioState sce (controlstate conf) = getScenarioState sce (controlstate c1)).
     apply H with (v0:=c0::v0) (re:=e) (sceList:=sceList);auto.
     unfold incl;intros.
     unfold incl in H2.   apply H2;auto.
     right;auto.
     unfold not;intros.
       inversion H3;subst;contradiction.  
       assert ( getScenarioState sce (controlstate v1) = getScenarioState sce (controlstate c1) \/
                ~ (getScenarioState sce (controlstate v1) = getScenarioState sce (controlstate c1))).
       apply excluded_middle.
       destruct H1.
       rewrite <- H1 in H0.
       unfold mergeConfigFunc' in Heqe2.
       destruct (mergeDataStateFunc (datastate conf) (datastate v) (datastate c1) );inversion Heqe2.
       clear H5.
       remember (mergeControlStateFunc (controlstate conf) (controlstate v) (controlstate c1) ).
       destruct e0;inversion Heqe2.
       simpl. rewrite H5 in H1;rewrite H5 in H0;subst;simpl in H0. simpl in H1.
       clear Heqe2.
    
       apply mergeCSEq1 with (sce:=sce) in Heqe3;auto.
      rewrite Heqe3;auto.        
      unfold incl in H2.          apply H2.     left;auto.
      pose proof mergeCSEq23.

      unfold mergeConfigFunc' in Heqe2.
       destruct (mergeDataStateFunc (datastate conf) (datastate v) (datastate c1) );inversion Heqe2.
       clear H6.
       remember (mergeControlStateFunc (controlstate conf) (controlstate v) (controlstate c1) ).
       destruct e0;inversion Heqe2.
       simpl. rewrite H6 in H1. simpl in H1.
       clear Heqe2.
     apply H4 with (sce:=sce) in Heqe3;auto. 
    destruct Heqe3. 
    auto.       contradiction. unfold incl in H2.          apply H2.     left;auto.

     unfold mergeConfigFunc' in Heqe2.
       destruct (mergeDataStateFunc (datastate conf) (datastate conf) (datastate v) );inversion Heqe2.
       clear H0.
       remember (mergeControlStateFunc (controlstate conf) (controlstate conf) (controlstate v) ).
       destruct e0;inversion Heqe2.
       simpl. rewrite H0 in *;auto. clear Heqe2.
      assert ( getScenarioState sce ( v2) = getScenarioState sce (controlstate conf) \/
               ~ (getScenarioState sce ( v2) = getScenarioState sce (controlstate conf))).
      apply excluded_middle.
      destruct H.
      apply  mergeCSEq1 with (sce:=sce) in Heqe3;auto.
      rewrite <- Heqe3;auto. 
      unfold incl in H2.          apply H2.     left;auto.
    
          apply mergeCSEq23 with (sce:=sce) in Heqe3;auto. 
          destruct Heqe3.
          contradiction.   auto.      unfold incl in H2.          apply H2.     left;auto.
          clear H.
          simpl in H0.
          destruct v0.
          remember (mergeConfigFunc' conf conf v ).
          destruct e0;inversion H0.
     subst. destruct sceList.          
     inversion H1.   simpl in Heqe1.
     remember (constructConfig s0 e conf).
     destruct e0;inversion Heqe1.
     destruct (constructConfigList' sceList e conf );inversion Heqe1.
     remember (innerCombineFunc'''' conf (c0 :: v0)).
    destruct o;inversion H0.      
    clear H4.
       remember ( mergeConfigFunc' conf v c1).
   
          destruct e0;inversion H0.
          subst.
    apply IHl with (c:=c1) (sce:=sce) in Heqe1;auto. 
   Focus 2. 
   unfold incl in H2.       unfold incl;intros. apply H2.     right;auto.
   Focus 2.
   inversion H3;subst;auto.
   destruct Heqe1.
    exists x;intuition;auto.    
   clear H0. 
     unfold mergeConfigFunc' in Heqe2.
       destruct (mergeDataStateFunc (datastate conf) (datastate v) (datastate c1) );inversion Heqe2.
       clear H5.
       remember (mergeControlStateFunc (controlstate conf) (controlstate v) (controlstate c1) ).
       destruct e0;inversion Heqe2.
       simpl. rewrite H5 in *;auto. clear Heqe2.
      
       clear H5. 
    remember Heqe1.      
    clear Heqe2.
    apply mergeCSEq23 with (sce:=sce) in e0;auto.
    Focus 2.  unfold incl in H2.        apply H2.     right;auto.
    destruct e0.
    assert ( getScenarioState sce ( v3) = getScenarioState sce (controlstate conf) \/
             ~ (getScenarioState sce ( v3) = getScenarioState sce (controlstate conf))).
    apply excluded_middle.
    destruct H5.
    
      apply  mergeCSEq1 with (sce:=sce) in Heqe1;auto.
     Focus 2.  unfold incl in H2.        apply H2.     right;auto. 
    
     
     rewrite <- H6.  rewrite <- Heqe1;auto. 
    rewrite <- H6.
    pose proof mergeCSEq4.
    remember Heqe1. clear Heqe2.
    
  apply H7 with (sce:=sce) in Heqe1;auto. 
  destruct Heqe1.
  pose proof sceNoChange.
 symmetry in Heqe0.  apply H9 with (sce':=sce) in Heqe0;auto.   
 symmetry in Heqe0.
 contradiction.
 split;auto.
 unfold not;intros.
  subst.  
  inversion H3;subst.
  contradiction.
  unfold incl in H2.
  apply H2;auto.
  left;auto.
  remember e0.
  clear Heqe1.   
  apply mergeCSEq23 with (sce:=sce) in e0;auto.
  destruct e0.   
  pose proof mergeCSEq4'.
  apply H10 with (sce:=sce) in e1;auto.
  unfold incl in H2.        apply H2.     right;auto.
  auto. 
  unfold incl in H2.        apply H2.     right;auto.
  unfold incl in H2.        apply H2.     right;auto.

  rewrite H0.
auto.   
  
Qed.


Lemma diamondCS: forall M (conf conf1 conf2 conf1': configuration M)  e1 e2 sce, 
(forall v1 v2 , In v1 (dom (datastate conf)) -> In v2 (dom (datastate conf)) -> 
updateVarEv M (eventDefinition e1)  v1 -> updateVarEv M (eventDefinition e2) v2 -> v1 <> v2) -> 
(forall v1 v2 , In v1 (dom (datastate conf)) -> In v2 (dom (datastate conf)) -> 
updateVarEv M (eventDefinition e1)  v1 -> usedVarEv M (eventDefinition e2) v2 -> v1 <> v2) ->
(forall v1 v2 , In v1 (dom (datastate conf)) -> In v2 (dom (datastate conf)) -> 
updateVarEv M (eventDefinition e2)  v1 -> usedVarEv M (eventDefinition e1) v2 -> v1 <> v2)  ->
(forall ev1 ev2, In ev1 (events M) -> In ev2 (events M) -> raisedEv M (eventDefinition e1) ev1 -> 
          eventKind ev1 = Internal -> eventKind ev2 = Internal ->         raisedEv M (eventDefinition e2) ev2 -> ev1 <> ev2) ->
(forall sce1 sce2, In sce1 (dom (controlstate conf)) -> In sce2 (dom (controlstate conf)) ->  In (eventDefinition e1) (alphabet sce1) -> In (eventDefinition e2) (alphabet sce2) -> sce1 <> sce2) ->
WellFormed M ->
e1 <> e2 ->
correct_configuration conf -> synchrony conf conf1 e1 ->  synchrony conf conf2 e2 ->
synchrony conf1 conf1' e2 ->
In sce (dom (controlstate conf)) ->
~ In (eventDefinition e1) (alphabet sce) ->
In (eventDefinition e2) (alphabet sce) ->
getScenarioState sce (controlstate conf1') = getScenarioState sce (controlstate conf2).
Proof.
  intros.
  assert (getScenarioState sce (controlstate conf) = getScenarioState sce (controlstate conf1)).
  apply  diamondCSNoChange with (e1:=e1);auto.
  symmetry in H13.

  assert (correct_configuration conf1).
  remember H4. clear Heqw. 
  unfold   WellFormed in H4.

   repeat match goal with
            | [ H: _ /\ _ |- _ ] => destruct H

          end.
   destruct H16.
    repeat match goal with
            | [ H: _ /\ _ |- _ ] => destruct H

          end.

    apply termL5 with (conf:=conf) (e:=e1);auto.
    unfold synchrony in H7.
    destruct H6.
    apply  raised_wellform';intuition;auto.
   
     assert (correct_configuration conf2).
  unfold   WellFormed in H4.

   repeat match goal with
            | [ H: _ /\ _ |- _ ] => destruct H

          end.
   destruct H17.
    repeat match goal with
            | [ H: _ /\ _ |- _ ] => destruct H

          end.

    apply termL5 with (conf:=conf) (e:=e2);auto.
    unfold synchrony in H8.
    destruct H6.
    apply  raised_wellform';intuition;auto.
    

   assert (In sce (finishedscenarios conf) \/ ~ In sce (finishedscenarios conf)).
  apply excluded_middle.
  destruct H16.

  pose proof syncFinishedNoChange.
  assert (getScenarioState sce (controlstate conf) = getScenarioState sce (controlstate conf2)).
  apply H17 with (e:=e2);auto.
  rewrite H18 in H13. 
  assert (In sce (finishedscenarios conf1)).
 
  apply finishedInvariantSync with (e:=e1) (conf:=conf);auto.
  assert (In sce (finishedscenarios conf2)).
  apply finishedInvariantSync with (e:=e2) (conf:=conf);auto.  

   assert (getScenarioState sce (controlstate conf1) = getScenarioState sce (controlstate conf1')).
  apply H17 with (e:=e2);auto.

 rewrite <- H21;auto. 
  
  remember H8;remember H9. clear Heqs;clear Heqs0. 
  unfold synchrony in s.
  unfold synchrony in s0.
  repeat match goal with
            | [ H: _ /\ _ |- _ ] => destruct H

         end.
  unfold combineFunc in *.
  remember (constructConfigList (dom (controlstate conf)) e2 conf).
  destruct e;inversion H20.
  clear H22.
  remember (constructConfigList (dom (controlstate conf1)) e2 conf1).
  destruct e;inversion H18.
  clear H22.
  destruct v;inversion H20.
  clear H22.
  destruct v0;inversion H18.
  clear H22.
  remember ( innerCombineFunc'''' conf (c :: v)).
  destruct o;inversion H20.
  simpl.
  remember (innerCombineFunc'''' conf1 (c0 :: v0)).
  destruct o;inversion H18.
  simpl.
  unfold constructConfigList in *.

   assert (dom (controlstate conf) = dom (controlstate conf1)).
  apply domControlSync with (e:=e1);auto.
  rewrite <- H21 in Heqe0.

  assert ((filter
              (fun x : scenario => inList event_definition_dec (eventDefinition e2) (alphabet x))
              (filterList (finishedscenarios conf) (dom (controlstate conf)) scenario_dec)) =
          (filter
               (fun x : scenario => inList event_definition_dec (eventDefinition e2) (alphabet x))
               (filterList (finishedscenarios conf1) (dom (controlstate conf)) scenario_dec))).
  apply   filterEqual;auto.
  unfold incl;intros.
  apply finishedInvariantSync with (conf:=conf) (e:=e1);auto.   
  intros.
  apply  inListFalse;auto.
  unfold not;intros.

  assert (In a (dom (controlstate conf))).
  rewrite domControlSync with (conf':=conf1) (e:=e1);auto.   
  destruct  H14.
  unfold scenarioInclusion in inclusion.
  unfold incl in inclusion;apply inclusion;auto.   
  
  apply H3 with (sce1:=a) in H26;auto.    
  
  apply syncFinish with (M:=M) (conf:=conf) (conf':=conf1);auto.
  rewrite H24 in Heqe.
 assert (In sce (filter
              (fun x : scenario => inList event_definition_dec (eventDefinition e2) (alphabet x))
              (filterList (finishedscenarios conf1) (dom (controlstate conf)) scenario_dec))).
 apply filter_In.
 split;auto.
 apply filterIn;auto.
 unfold not;intros.
 SearchAbout (finishedscenarios).
 
 apply syncFinish with (sce:=sce) in H7;auto.
 SearchAbout inList.
 apply  inListLemma;auto.
  
 
 SearchAbout constructConfigList'.
 pose proof constructIn.
 Check termL2'.
 assert (exists conf' : configuration M, Result conf' = constructConfig sce e2 conf).
 apply termL2' with (scs:=(filter
              (fun x : scenario => inList event_definition_dec (eventDefinition e2) (alphabet x))
              (filterList (finishedscenarios conf1) (dom (controlstate conf)) scenario_dec))) (lst:=c::v);auto.
 destruct H27.
   assert (exists conf' : configuration M, Result conf' = constructConfig sce e2 conf1).
 apply termL2' with (scs:=(filter
              (fun x : scenario => inList event_definition_dec (eventDefinition e2) (alphabet x))
              (filterList (finishedscenarios conf1) (dom (controlstate conf)) scenario_dec))) (lst:=c0::v0);auto.
 destruct H28.
 assert (getScenarioState sce (controlstate x) = getScenarioState sce (controlstate x0)).
 remember H4.  clear Heqw. destruct H4.

  repeat match goal with
            | [ H: _ /\ _ |- _ ] => destruct H

         end.
  destruct H31.

  repeat match goal with
            | [ H: _ /\ _ |- _ ] => destruct H

         end.
 
  
 apply constructConfigSceStateEqual with (conf:=conf) (conf1:=conf1) (e1:=e1) (e2:=e2);auto. 
 apply H41;auto.
  auto.  
  destruct H6.
  rewrite <- cs_consist;auto.   
  intros.
  
  assert (~  updateVarEv M (eventDefinition e1) v1 ).
  unfold not;intros.
  unfold not in H0.
  apply H0 with (v1:=v1) (v2:=v1);auto.   
  apply  diamondDSNoChange with (e1:=e1) (e2:=e2);auto. 
  destruct H6.
  rewrite <- cs_consist;auto.
  assert (In x (c::v)).
  apply H26 with (l:=(filter
              (fun x : scenario => inList event_definition_dec (eventDefinition e2) (alphabet x))
              (filterList (finishedscenarios conf1) (dom (controlstate conf)) scenario_dec))) (e:=e2) (conf:=conf) (x:=sce);auto.

  assert (In x0 (c0::v0)).
  apply H26 with (l:=(filter
              (fun x : scenario => inList event_definition_dec (eventDefinition e2) (alphabet x))
              (filterList (finishedscenarios conf1) (dom (controlstate conf)) scenario_dec))) (e:=e2) (conf:=conf1) (x:=sce);auto.
  pose proof innerSceStateEq.
  assert (exists x : configuration M,
          In x (c::v) /\
          Result x = constructConfig sce e2 conf /\
          getScenarioState sce (controlstate c1) = getScenarioState sce (controlstate x)).
  apply H32 with (sceList:= (filter
             (fun x : scenario => inList event_definition_dec (eventDefinition e2) (alphabet x))
             (filterList (finishedscenarios conf1) (dom (controlstate conf)) scenario_dec)));auto.
  unfold incl;intros.
  apply filter_In in H33;auto.
  destruct H33.
  apply filterL2 in H33;auto.
  SearchAbout uniqList.
  apply filterUniq;auto.
  SearchAbout filterList.
  apply   uniqListFilter;auto.
  destruct H14.
  auto.
  destruct H6.
  auto.
  destruct H33.
  destruct H33.
  destruct H34.
  rewrite <- H34 in H27.
  inversion H27;subst;auto.

   
  assert (exists x : configuration M,
          In x (c0::v0) /\
          Result x = constructConfig sce e2 conf1 /\
          getScenarioState sce (controlstate c2) = getScenarioState sce (controlstate x)).
  
  
  apply H32 with (sceList:= (filter
             (fun x : scenario => inList event_definition_dec (eventDefinition e2) (alphabet x))
             (filterList (finishedscenarios conf1) (dom (controlstate conf)) scenario_dec)));auto.
  unfold incl;intros.
  apply filter_In in H22;auto.
  destruct H22.
  apply filterL2 in H22;auto. Check domControlSync.
  
  rewrite  domControlSync with (conf':=conf1) (e:=e1) in H22;auto.

  apply filterUniq;auto.
  apply   uniqListFilter;auto.
  destruct H14.
  auto.
  destruct H6.
  auto.
  destruct H22.
  destruct H22.
  destruct H23.
  rewrite <- H23 in H28.
  inversion H28;subst;auto.
  rewrite H35;rewrite H36;auto. 
  
  
Qed.

Lemma diamondCS': forall M (conf conf1 conf2 conf2': configuration M)  e1 e2 sce, 
(forall v1 v2 , In v1 (dom (datastate conf)) -> In v2 (dom (datastate conf)) -> 
updateVarEv M (eventDefinition e1)  v1 -> updateVarEv M (eventDefinition e2) v2 -> v1 <> v2) -> 
(forall v1 v2 , In v1 (dom (datastate conf)) -> In v2 (dom (datastate conf)) -> 
updateVarEv M (eventDefinition e1)  v1 -> usedVarEv M (eventDefinition e2) v2 -> v1 <> v2) ->
(forall v1 v2 , In v1 (dom (datastate conf)) -> In v2 (dom (datastate conf)) -> 
updateVarEv M (eventDefinition e2)  v1 -> usedVarEv M (eventDefinition e1) v2 -> v1 <> v2)  ->
(forall ev1 ev2, In ev1 (events M) -> In ev2 (events M) -> raisedEv M (eventDefinition e1) ev1 -> 
             eventKind ev1 = Internal -> eventKind ev2 = Internal ->      raisedEv M (eventDefinition e2) ev2 -> ev1 <> ev2) ->
(forall sce1 sce2, In sce1 (dom (controlstate conf)) -> In sce2 (dom (controlstate conf)) -> In (eventDefinition e1) (alphabet sce1) -> In (eventDefinition e2) (alphabet sce2) -> sce1 <> sce2) ->
WellFormed M ->
e1 <> e2 ->
correct_configuration conf -> synchrony conf conf1 e1 ->  synchrony conf conf2 e2 ->
synchrony conf2 conf2' e1 ->
In sce (dom (controlstate conf)) ->
~ In (eventDefinition e2) (alphabet sce) ->
In (eventDefinition e1) (alphabet sce) ->
getScenarioState sce (controlstate conf2') = getScenarioState sce (controlstate conf1).
Proof.
  intros.
  apply diamondCS with (conf:=conf) (conf1:=conf2) (e1:=e2) (e2:=e1);auto.
  intros.
  unfold not;intros.
  unfold not in H.   
  apply H with (v1:=v2) (v2:=v1);auto.
  intros.
   unfold not;intros.
  unfold not in H2.   
  apply H2 with (ev1:=ev2) (ev2:=ev1);auto.
  intros.
    unfold not;intros.
  unfold not in H3.   
  apply H3 with (sce1:=sce2) (sce2:=sce1);auto.  
Qed.


Lemma diamondCSAll: forall M (conf conf1 conf2 conf1' conf2': configuration M)  e1 e2  sce, 
(forall v1 v2 , In v1 (dom (datastate conf)) -> In v2 (dom (datastate conf)) -> 
updateVarEv M (eventDefinition e1)  v1 -> updateVarEv M (eventDefinition e2) v2 -> v1 <> v2) -> 
(forall v1 v2 , In v1 (dom (datastate conf)) -> In v2 (dom (datastate conf)) -> 
updateVarEv M (eventDefinition e1)  v1 -> usedVarEv M (eventDefinition e2) v2 -> v1 <> v2) ->
(forall v1 v2 , In v1 (dom (datastate conf)) -> In v2 (dom (datastate conf)) -> 
updateVarEv M (eventDefinition e2)  v1 -> usedVarEv M (eventDefinition e1) v2 -> v1 <> v2)  ->
(forall ev1 ev2, In ev1 (events M) -> In ev2 (events M) -> raisedEv M (eventDefinition e1) ev1 -> 
        eventKind ev1 = Internal -> eventKind ev2 = Internal ->           raisedEv M (eventDefinition e2) ev2 -> ev1 <> ev2) ->
(forall sce1 sce2, In sce1 (dom (controlstate conf)) -> In sce2 (dom (controlstate conf)) -> In (eventDefinition e1) (alphabet sce1) -> In (eventDefinition e2) (alphabet sce2) -> sce1 <> sce2) ->
WellFormed M ->
e1 <> e2 ->
correct_configuration conf -> synchrony conf conf1 e1 ->  synchrony conf conf2 e2 ->
synchrony conf1 conf1' e2 -> synchrony conf2 conf2' e1 ->
In sce (dom (controlstate conf)) ->
getScenarioState sce (controlstate conf1') =  getScenarioState sce (controlstate conf2').
Proof.
  intros.
  assert (correct_configuration conf1).
  destruct H4.
   repeat match goal with
            | [ H: _ /\ _ |- _ ] => destruct H

         end.
  destruct H14.

  repeat match goal with
            | [ H: _ /\ _ |- _ ] => destruct H

         end.
  apply termL5 with (conf:=conf) (e:=e1);auto.
  destruct H6.
  apply raised_wellform';auto.
  unfold synchrony in H7;intuition.
  assert (correct_configuration conf2).
  destruct H4.
   repeat match goal with
            | [ H: _ /\ _ |- _ ] => destruct H

         end.
  destruct H15.

  repeat match goal with
            | [ H: _ /\ _ |- _ ] => destruct H

         end.
  apply termL5 with (conf:=conf) (e:=e2);auto.
  destruct H6.
  apply raised_wellform';auto.
  unfold synchrony in H8;intuition.
  
  assert (In (eventDefinition e1) (alphabet sce) \/ ~ In (eventDefinition e1) (alphabet sce)).
  apply excluded_middle.
  destruct H14.
  assert (~ In (eventDefinition e2) (alphabet sce)).
  unfold not;intros.
  unfold not in H3.
  apply H3 with (sce1:=sce) (sce2:=sce);auto.
  pose proof diamondCS'.
  assert ( getScenarioState sce (controlstate conf2') = getScenarioState sce (controlstate conf1)).
  apply H16 with (conf:=conf) (conf2:=conf2) (e1:=e1) (e2:=e2);auto.
  rewrite H17.
  symmetry.
  apply diamondCSNoChange with (e1:=e2);auto.

  assert (In (eventDefinition e2) (alphabet sce) \/ ~ In (eventDefinition e2) (alphabet sce)).
  apply excluded_middle.
  destruct H15.

  pose proof diamondCS.
   assert ( getScenarioState sce (controlstate conf1') = getScenarioState sce (controlstate conf2)).
  apply H16 with (conf:=conf) (conf1:=conf1) (e1:=e1) (e2:=e2);auto.
  rewrite H17.

  apply diamondCSNoChange with (e1:=e1);auto.

  assert (getScenarioState sce (controlstate conf) = getScenarioState sce (controlstate conf1)).
    apply diamondCSNoChange with (e1:=e1);auto.

  assert (getScenarioState sce (controlstate conf) = getScenarioState sce (controlstate conf2)).
    apply diamondCSNoChange with (e1:=e2);auto.

  assert (getScenarioState sce (controlstate conf1) = getScenarioState sce (controlstate conf1')).
    apply diamondCSNoChange with (e1:=e2);auto.

  assert (getScenarioState sce (controlstate conf2) = getScenarioState sce (controlstate conf2')).
    apply diamondCSNoChange with (e1:=e1);auto.
    rewrite <- H18;rewrite <- H19.
  rewrite <- H16;auto.     

Qed.



Lemma finishedInList': forall (lst : list scenario) (e : raisedEvent) (M : monitor) (conf : configuration M)
    (v : list (configuration M)) (i : scenario) (c : configuration M),
  uniqList lst ->
  incl lst (dom (controlstate conf)) ->
  Result v = constructConfigList' lst e conf ->
  Some c = innerCombineFunc'''' conf v ->
  In i lst ->
   correct_configuration conf ->
       noMergeError' M ->
       basicPrecondition conf e ->
     
  In i (finishedscenarios c).
Proof.
  intro lst;induction lst.
  - intros. inversion H3.
  - intros. rename H4 into correct. rename H5 into noMerge. rename H6 into bp.
    destruct H3. subst.
    simpl in H1.
    remember (constructConfig i e conf).
    destruct e0;inversion H1.
    remember (constructConfigList' lst e conf ). 
    destruct e0;inversion H1.
    subst.
    simpl in H2.
    destruct v1.
    remember (mergeConfigFunc' conf conf v0). 
    destruct e0;inversion H2. subst.
    unfold mergeConfigFunc' in Heqe2.
    destruct (mergeDataStateFunc (datastate conf) (datastate conf) (datastate v0));inversion Heqe2.   clear H5. 
    destruct ( mergeControlStateFunc (controlstate conf) (controlstate conf) (controlstate v0));inversion Heqe2. simpl.
    rewrite in_app_iff. right.
    SearchAbout constructConfig. apply termL3 in Heqe0. rewrite Heqe0. left;auto.
    remember (innerCombineFunc'''' conf (c0 :: v1)).
    destruct o;inversion H2. clear H5.
    remember (mergeConfigFunc' conf v0 c1 ).
    destruct e0;inversion H2.
    subst.
    
    unfold mergeConfigFunc' in Heqe2.
    destruct ( mergeDataStateFunc (datastate conf) (datastate v0) (datastate c1));inversion Heqe2.
    destruct (mergeControlStateFunc (controlstate conf) (controlstate v0) (controlstate c1));inversion H5.
    simpl.
    clear H5. clear Heqe2.
    rewrite in_app_iff.
    left. 
    apply termL3 in Heqe0.
    rewrite Heqe0. left;auto.

    simpl in H1.
    
   
     remember (constructConfig a e conf).
     destruct e0;inversion H1.
     clear H1.
   remember (constructConfigList' lst e conf).      
   destruct e0;inversion H5.
   subst.
   simpl in H2.
   destruct v1.
   destruct lst. inversion H3.
   simpl in Heqe1.
   destruct (constructConfig s e conf);inversion Heqe1. 
   destruct (constructConfigList' lst e conf);inversion Heqe1. 
   
   remember (innerCombineFunc'''' conf (c0::v1)).
   destruct o;inversion H2. clear H4.
   remember (mergeConfigFunc' conf v0 c1 ).
   destruct e0;inversion H2.
   subst.
   unfold mergeConfigFunc' in Heqe2.
    destruct ( mergeDataStateFunc (datastate conf) (datastate v0) (datastate c1));inversion Heqe2.
    destruct (mergeControlStateFunc (controlstate conf) (controlstate v0) (controlstate c1));inversion H4.
    simpl.

    
        
    rewrite in_app_iff.
    right. clear H4. clear Heqe2.
    apply IHlst with (i:=i) (c:=c1) in Heqe1;auto.
    inversion H;auto.
    unfold incl;intros. unfold incl in H0;apply H0. right;auto.
   
Qed.


Lemma finishedInList'': forall (lst : list scenario) (e : raisedEvent) (M : monitor) (conf : configuration M)
    (v : list (configuration M)) (i : scenario) (c : configuration M),
  uniqList lst ->
  incl lst (dom (controlstate conf)) ->
  Result v = constructConfigList' lst e conf ->
  Some c = innerCombineFunc'''' conf v ->
  In i lst ->
  In i (finishedscenarios c).
Proof.
  intro lst;induction lst.
  - intros. inversion H3.
  - intros. 
    destruct H3. subst.
    simpl in H1.
    remember (constructConfig i e conf).
    destruct e0;inversion H1.
    remember (constructConfigList' lst e conf ). 
    destruct e0;inversion H1.
    subst.
    simpl in H2.
    destruct v1.
    remember (mergeConfigFunc' conf conf v0). 
    destruct e0;inversion H2. subst.
    unfold mergeConfigFunc' in Heqe2.
    destruct (mergeDataStateFunc (datastate conf) (datastate conf) (datastate v0));inversion Heqe2.   clear H5. 
    destruct ( mergeControlStateFunc (controlstate conf) (controlstate conf) (controlstate v0));inversion Heqe2. simpl.
    rewrite in_app_iff. right.
     apply termL3 in Heqe0. rewrite Heqe0. left;auto.
    remember (innerCombineFunc'''' conf (c0 :: v1)).
    destruct o;inversion H2. clear H5.
    remember (mergeConfigFunc' conf v0 c1 ).
    destruct e0;inversion H2.
    subst.
    
    unfold mergeConfigFunc' in Heqe2.
    destruct ( mergeDataStateFunc (datastate conf) (datastate v0) (datastate c1));inversion Heqe2.
    destruct (mergeControlStateFunc (controlstate conf) (controlstate v0) (controlstate c1));inversion H5.
    simpl.
    clear H5. clear Heqe2.
    rewrite in_app_iff.
    left. 
    apply termL3 in Heqe0.
    rewrite Heqe0. left;auto.

    simpl in H1.
    
   
     remember (constructConfig a e conf).
     destruct e0;inversion H1.
     clear H1.
   remember (constructConfigList' lst e conf).      
   destruct e0;inversion H5.
   subst.
   simpl in H2.
   destruct v1.
   destruct lst. inversion H3.
   simpl in Heqe1.
   destruct (constructConfig s e conf);inversion Heqe1. 
   destruct (constructConfigList' lst e conf);inversion Heqe1. 
   
   remember (innerCombineFunc'''' conf (c0::v1)).
   destruct o;inversion H2. clear H4.
   remember (mergeConfigFunc' conf v0 c1 ).
   destruct e0;inversion H2.
   subst.
   unfold mergeConfigFunc' in Heqe2.
    destruct ( mergeDataStateFunc (datastate conf) (datastate v0) (datastate c1));inversion Heqe2.
    destruct (mergeControlStateFunc (controlstate conf) (controlstate v0) (controlstate c1));inversion H4.
    simpl.

    
        
    rewrite in_app_iff.
    right. clear H4. clear Heqe2.
    apply IHlst with (i:=i) (c:=c1) in Heqe1;auto.
    inversion H;auto.
    unfold incl;intros. unfold incl in H0;apply H0. right;auto.
   
Qed.

Lemma diamondFinAux1: forall M (conf conf1 conf2 conf1': configuration M)  e1 e2 sce, 
(forall v1 v2 , In v1 (dom (datastate conf)) -> In v2 (dom (datastate conf)) -> 
updateVarEv M (eventDefinition e1)  v1 -> updateVarEv M (eventDefinition e2) v2 -> v1 <> v2) -> 
(forall v1 v2 , In v1 (dom (datastate conf)) -> In v2 (dom (datastate conf)) -> 
updateVarEv M (eventDefinition e1)  v1 -> usedVarEv M (eventDefinition e2) v2 -> v1 <> v2) ->
(forall v1 v2 , In v1 (dom (datastate conf)) -> In v2 (dom (datastate conf)) -> 
updateVarEv M (eventDefinition e2)  v1 -> usedVarEv M (eventDefinition e1) v2 -> v1 <> v2)  ->
(forall ev1 ev2, In ev1 (events M) -> In ev2 (events M) -> raisedEv M (eventDefinition e1) ev1 -> 
           eventKind ev1 = Internal -> eventKind ev2 = Internal ->        raisedEv M (eventDefinition e2) ev2 -> ev1 <> ev2) ->
(forall sce1 sce2, In sce1 (dom (controlstate conf)) -> In sce2 (dom (controlstate conf)) -> In (eventDefinition e1) (alphabet sce1) -> In (eventDefinition e2) (alphabet sce2) -> sce1 <> sce2) ->
WellFormed M ->
e1 <> e2 ->
correct_configuration conf -> synchrony conf conf1 e1 ->  synchrony conf conf2 e2 ->
synchrony conf1 conf1' e2 ->
In sce (dom (controlstate conf)) ->
~ In sce (finishedscenarios conf) ->
In (eventDefinition e2) (alphabet sce) ->
In sce (finishedscenarios conf2) /\ (~ In sce (finishedscenarios conf1) /\ In sce (finishedscenarios conf1')).
Proof.
  intros.
  split.
  SearchAbout finishedscenarios.
  (*finishedInList*)
  remember H8. 
  clear Heqs.
  unfold synchrony in H8.   
  destruct H8.
  unfold combineFunc in H13.
  remember (constructConfigList (dom (controlstate conf)) e2 conf).
  destruct e;inversion H13.
  clear H15.
  destruct v;inversion H13.
  clear H15.
  remember (innerCombineFunc'''' conf (c :: v) ).
  destruct o;inversion H13.
  simpl.
  unfold  constructConfigList  in Heqe.
  assert (In sce (filter
              (fun x : scenario => inList event_definition_dec (eventDefinition e2) (alphabet x))
              (filterList (finishedscenarios conf) (dom (controlstate conf)) scenario_dec))).
  apply filter_In;split;auto.
  SearchAbout filterList .
  apply filterIn;auto.
  SearchAbout inList.
  apply   inListLemma;auto.
  pose proof finishedInList'.
  destruct H4.
   repeat match goal with
            | [ H: _ /\ _ |- _ ] => destruct H

         end. 

 apply H16 with (lst:=(filter
              (fun x : scenario => inList event_definition_dec (eventDefinition e2) (alphabet x))
              (filterList (finishedscenarios conf) (dom (controlstate conf)) scenario_dec))) (e:=e2) (conf:=conf) (v:=c::v);auto.
 apply filterUniq;auto.
 apply  uniqListFilter;destruct H6;auto.
 unfold incl;intros.
 apply filter_In in H25.
 destruct H25.
 apply filterL2 in H25;auto.
 destruct H19;auto.
  repeat match goal with
            | [ H: _ /\ _ |- _ ] => destruct H

         end.
  repeat(split;auto).
  split.
  unfold not;intros.
  SearchAbout finishedscenarios.
  apply syncFinish with (sce:=sce) in H7;auto.
  unfold not in H3.
  apply H3 with (sce1:=sce) (sce2:=sce);auto.


  assert (correct_configuration conf1).
   destruct H4.
   repeat match goal with
            | [ H: _ /\ _ |- _ ] => destruct H

          end.
   destruct H15.
   repeat match goal with
            | [ H: _ /\ _ |- _ ] => destruct H

          end.
   apply termL5 with (conf:=conf) (e:=e1);auto. 
     destruct H6.
     apply raised_wellform';auto.
     unfold synchrony in H7;intuition.
     rename H13 into corr.
     
   
  assert (~In sce (finishedscenarios conf1)).

  unfold not;intros.
  SearchAbout finishedscenarios.
  apply syncFinish with (sce:=sce) in H7;auto.
  unfold not in H3.
  apply H3 with (sce1:=sce) (sce2:=sce);auto.
        
  remember H9. 
  clear Heqs.
  unfold synchrony in H9.   
  destruct H9.
  unfold combineFunc in H14.
  remember (constructConfigList (dom (controlstate conf1)) e2 conf1).
  destruct e;inversion H14.
  clear H16.
  destruct v;inversion H14.
  clear H16.
  remember (innerCombineFunc'''' conf1 (c :: v) ).
  destruct o;inversion H14.
  simpl.
  unfold  constructConfigList  in Heqe.
  assert (In sce (filter
              (fun x : scenario => inList event_definition_dec (eventDefinition e2) (alphabet x))
              (filterList (finishedscenarios conf1) (dom (controlstate conf1)) scenario_dec))).
  apply filter_In;split;auto.
  apply filterIn;auto. rewrite <- domControlSync with (conf:=conf) (e:=e1);auto.
  
  apply   inListLemma;auto.
  pose proof finishedInList'.
  destruct H4.
   repeat match goal with
            | [ H: _ /\ _ |- _ ] => destruct H

         end. 

 apply H17 with (lst:=(filter
              (fun x : scenario => inList event_definition_dec (eventDefinition e2) (alphabet x))
              (filterList (finishedscenarios conf1) (dom (controlstate conf1)) scenario_dec))) (e:=e2) (conf:=conf1) (v:=c::v);auto.
 apply filterUniq;auto.
 
 apply  uniqListFilter;destruct corr;auto.
 

 unfold incl;intros.
 apply filter_In in H26.
 destruct H26.
 apply filterL2 in H26;auto.
 destruct H20;auto.
  repeat match goal with
            | [ H: _ /\ _ |- _ ] => destruct H

         end.
  repeat(split;auto).

  
Qed.


Lemma diamondFinAux2: forall M (conf conf1 conf2 conf1': configuration M)  e1 e2 sce, 
(forall v1 v2 , In v1 (dom (datastate conf)) -> In v2 (dom (datastate conf)) -> 
updateVarEv M (eventDefinition e1)  v1 -> updateVarEv M (eventDefinition e2) v2 -> v1 <> v2) -> 
(forall v1 v2 , In v1 (dom (datastate conf)) -> In v2 (dom (datastate conf)) -> 
updateVarEv M (eventDefinition e1)  v1 -> usedVarEv M (eventDefinition e2) v2 -> v1 <> v2) ->
(forall v1 v2 , In v1 (dom (datastate conf)) -> In v2 (dom (datastate conf)) -> 
updateVarEv M (eventDefinition e2)  v1 -> usedVarEv M (eventDefinition e1) v2 -> v1 <> v2)  ->
(forall ev1 ev2, In ev1 (events M) -> In ev2 (events M) -> raisedEv M (eventDefinition e1) ev1 -> 
           eventKind ev1 = Internal -> eventKind ev2 = Internal ->        raisedEv M (eventDefinition e2) ev2 -> ev1 <> ev2) ->
(forall sce1 sce2, In sce1 (dom (controlstate conf)) -> In sce2 (dom (controlstate conf)) -> In (eventDefinition e1) (alphabet sce1) -> In (eventDefinition e2) (alphabet sce2) -> sce1 <> sce2) ->
WellFormed M ->
e1 <> e2 ->
correct_configuration conf -> synchrony conf conf1 e1 ->  synchrony conf conf2 e2 ->
synchrony conf1 conf1' e2 ->
In sce (dom (controlstate conf)) ->
~ In sce (finishedscenarios conf) ->
~ In sce (finishedscenarios conf1) ->
~ In (eventDefinition e2) (alphabet sce) ->
~ In sce (finishedscenarios conf2) /\ ~ In sce (finishedscenarios conf1').
Proof.
  intros.
  assert (correct_configuration conf1).
 destruct H4.
   repeat match goal with
            | [ H: _ /\ _ |- _ ] => destruct H

         end. 
   destruct H16.
     repeat match goal with
            | [ H: _ /\ _ |- _ ] => destruct H

         end. 
    apply termL5 with (conf:=conf) (e:=e1);auto. 
     destruct H6.
     apply raised_wellform';auto.
     unfold synchrony in H7;intuition;auto.
       
   assert (correct_configuration conf2).
 destruct H4.
   repeat match goal with
            | [ H: _ /\ _ |- _ ] => destruct H

         end. 
   destruct H17.
     repeat match goal with
            | [ H: _ /\ _ |- _ ] => destruct H

         end. 
    apply termL5 with (conf:=conf) (e:=e2);auto. 
     destruct H6.
     apply raised_wellform';auto.
     unfold synchrony in H8;intuition;auto.
   
  split.
  unfold not;intros.
  apply syncFinish with (sce:=sce) in H8;auto. 
  unfold not;intros.
  apply syncFinish with (sce:=sce) in H9;auto.    
   
Qed.


Lemma diamondFinAux3: forall M (conf conf1 conf2 conf1': configuration M)  e1 e2, 
(forall v1 v2 , In v1 (dom (datastate conf)) -> In v2 (dom (datastate conf)) -> 
updateVarEv M (eventDefinition e1)  v1 -> updateVarEv M (eventDefinition e2) v2 -> v1 <> v2) -> 
(forall v1 v2 , In v1 (dom (datastate conf)) -> In v2 (dom (datastate conf)) -> 
updateVarEv M (eventDefinition e1)  v1 -> usedVarEv M (eventDefinition e2) v2 -> v1 <> v2) ->
(forall v1 v2 , In v1 (dom (datastate conf)) -> In v2 (dom (datastate conf)) -> 
updateVarEv M (eventDefinition e2)  v1 -> usedVarEv M (eventDefinition e1) v2 -> v1 <> v2)  ->
(forall ev1 ev2, In ev1 (events M) -> In ev2 (events M) -> raisedEv M (eventDefinition e1) ev1 -> 
            eventKind ev1 = Internal -> eventKind ev2 = Internal ->       raisedEv M (eventDefinition e2) ev2 -> ev1 <> ev2) ->
(forall sce1 sce2, In sce1 (dom (controlstate conf)) -> In sce2 (dom (controlstate conf)) -> In (eventDefinition e1) (alphabet sce1) -> In (eventDefinition e2) (alphabet sce2) -> sce1 <> sce2) ->
WellFormed M ->
e1 <> e2 ->
correct_configuration conf -> synchrony conf conf1 e1 ->  synchrony conf conf2 e2 ->
synchrony conf1 conf1' e2 ->
incl  (filterList (finishedscenarios conf1) (finishedscenarios conf1') scenario_dec)
      (filterList (finishedscenarios conf) (finishedscenarios conf2) scenario_dec)
      /\
incl  (filterList (finishedscenarios conf) (finishedscenarios conf2) scenario_dec)
      (filterList (finishedscenarios conf1) (finishedscenarios conf1') scenario_dec)
      . 
Proof.
  intros.
  split.
  - unfold incl;intros.
    remember H10. clear Heqi.
    apply filterL1 in H10.
    apply filterL2 in i.
    SearchAbout filterList.
    apply filterIn.
        
    Check syncFinish.
    remember H9.
    clear Heqs.    
   apply syncFinish with (sce:=a) in H9;auto.
   Focus 2.
   destruct H4.
   repeat match goal with
            | [ H: _ /\ _ |- _ ] => destruct H

         end. 
   destruct H13.
     repeat match goal with
            | [ H: _ /\ _ |- _ ] => destruct H

         end. 
     apply termL5 with (conf:=conf) (e:=e1);auto.
     destruct H6.
     apply raised_wellform';auto.
     unfold synchrony in H7;intuition;auto.
     assert (~ In a (finishedscenarios conf)).
     unfold not;intros.
     SearchAbout finishedscenarios.
     apply finishedInvariantSync with (sce:=a) in H7;auto.      

    pose proof finishedInList'.

    remember H8.  clear Heqs0. unfold synchrony in H8.
    destruct H8.
    unfold combineFunc in H13.
    remember (constructConfigList (dom (controlstate conf)) e2 conf).
    destruct e;inversion H13.
    clear H15.
    unfold constructConfigList in Heqe.
    destruct v;inversion H13.
    clear H15.
    remember (innerCombineFunc'''' conf (c :: v) ).
    destruct o;inversion H13.
    simpl.     
    assert (In a (filter
              (fun x : scenario => inList event_definition_dec (eventDefinition e2) (alphabet x))
              (filterList (finishedscenarios conf) (dom (controlstate conf)) scenario_dec))).
    apply filter_In;auto.
    split.
    apply filterIn;auto.
    assert (correct_configuration conf1').
    destruct H4.
     repeat match goal with
            | [ H: _ /\ _ |- _ ] => destruct H

            end.
     destruct H17.
      repeat match goal with
            | [ H: _ /\ _ |- _ ] => destruct H

             end.
      apply termL5 with (conf:=conf1) (e:=e2);auto.
      apply termL5 with (conf:=conf) (e:=e1);auto.
      destruct H6.
      apply  raised_wellform';auto.
      unfold synchrony in H7;intuition;auto.
      auto.
      destruct H6.
      apply  raised_wellform' ;auto.
        
    assert (In a (dom (controlstate conf1'))).
    destruct H14.
    unfold  scenarioInclusion in inclusion.
    unfold incl in inclusion.
    apply inclusion;auto.
    assert (In a (dom (controlstate conf1))).
    rewrite  domControlSync with (conf':=conf1') (e:=e2);auto.
    auto. Check domControlSync.
        rewrite  domControlSync with (conf':=conf1) (e:=e1);auto.
        SearchAbout inList.
        apply  inListLemma;auto.
        destruct H4.
     repeat match goal with
            | [ H: _ /\ _ |- _ ] => destruct H

            end.
     
        apply H12 with (lst:=(filter
             (fun x : scenario => inList event_definition_dec (eventDefinition e2) (alphabet x))
             (filterList (finishedscenarios conf) (dom (controlstate conf)) scenario_dec))) (e:=e2) (conf:=conf) (v:=c::v) ;auto.
        SearchAbout uniqList.
        apply filterUniq;auto.
        SearchAbout uniqList.
    apply  uniqListFilter;destruct H6;auto.     
    unfold incl;intros.
    apply filter_In in H24.
    destruct H24.
   apply filterL2 in H24;auto.     
   destruct H18.
   repeat match goal with
            | [ H: _ /\ _ |- _ ] => destruct H

          end.
   repeat(split;auto).
       
   unfold not;intros.
    apply finishedInvariantSync with (sce:=a) in H7;auto.          
  -


    unfold incl;intros.
    remember H10. clear Heqi.
    apply filterL1 in H10.
    apply filterL2 in i.
    assert (In (eventDefinition e2) (alphabet a)).
    apply syncFinish with (sce:=a) in H8;auto.
    assert (~(In (eventDefinition e1) (alphabet a))).
    unfold not;intros.
    unfold not in H3.

    assert (correct_configuration conf2).
     destruct H4.
   repeat match goal with
            | [ H: _ /\ _ |- _ ] => destruct H

         end. 
   destruct H15.
     repeat match goal with
            | [ H: _ /\ _ |- _ ] => destruct H

         end. 
     apply termL5 with (conf:=conf) (e:=e2);auto.
     destruct H6.
     apply raised_wellform';auto.
     unfold synchrony in H8;intuition;auto.

     assert (In a (dom (controlstate conf))).
   rewrite domControlSync with (conf':=conf2) (e:=e2);auto.      
   destruct H13.
   unfold scenarioInclusion in inclusion.
   unfold incl in inclusion;apply inclusion;auto.    
   
    apply H3 with (sce1:=a) (sce2:=a);auto.
   


    assert (correct_configuration conf1).
     destruct H4.
   repeat match goal with
            | [ H: _ /\ _ |- _ ] => destruct H

         end. 
   destruct H15.
     repeat match goal with
            | [ H: _ /\ _ |- _ ] => destruct H

         end. 
     apply termL5 with (conf:=conf) (e:=e1);auto.
     destruct H6.
     apply raised_wellform';auto.
     unfold synchrony in H7;intuition;auto.
     assert (correct_configuration conf2).
     destruct H4.
   repeat match goal with
            | [ H: _ /\ _ |- _ ] => destruct H

         end. 
   destruct H16.
     repeat match goal with
            | [ H: _ /\ _ |- _ ] => destruct H

         end. 
     apply termL5 with (conf:=conf) (e:=e2);auto.
     destruct H6.
     apply raised_wellform';auto.
     unfold synchrony in H8;intuition;auto.
     assert (correct_configuration conf1').
      destruct H4.
   repeat match goal with
            | [ H: _ /\ _ |- _ ] => destruct H

         end. 
   destruct H17.
     repeat match goal with
            | [ H: _ /\ _ |- _ ] => destruct H

         end. 
     apply termL5 with (conf:=conf1) (e:=e2);auto.
     destruct H13.
     apply raised_wellform';auto.
     unfold synchrony in H9;intuition;auto.
     assert (~ In a (finishedscenarios conf1)).
     unfold not;intros.
     apply syncFinish with (sce:=a) in H7;auto.

     
     apply filterIn;auto.    
    remember H9.
    clear Heqs.    
    unfold synchrony in H9.
    destruct H9.
      
  
    unfold combineFunc in H17.
    remember (constructConfigList (dom (controlstate conf1)) e2 conf1).
    destruct e;inversion H17.
    clear H19.
    unfold constructConfigList in Heqe.
    destruct v;inversion H17.
    clear H19.
    remember (innerCombineFunc'''' conf1 (c :: v) ).
    destruct o;inversion H17.
    simpl.     
    assert (In a (filter
              (fun x : scenario => inList event_definition_dec (eventDefinition e2) (alphabet x))
              (filterList (finishedscenarios conf1) (dom (controlstate conf1)) scenario_dec))).
    apply filter_In;auto.
    split.
    apply filterIn;auto.
  
     
    assert (In a (dom (controlstate conf2))).
    destruct H14.
    unfold  scenarioInclusion in inclusion.
    unfold incl in inclusion.
    apply inclusion;auto.
    assert (In a (dom (controlstate conf))).
       
    rewrite  domControlSync with (conf':=conf2) (e:=e2);auto.
      rewrite  <- domControlSync with (conf:=conf) (e:=e1);auto.  
        apply  inListLemma;auto.
        pose proof finishedInList'.

        destruct H4.
     repeat match goal with
            | [ H: _ /\ _ |- _ ] => destruct H

         end.       
        
        apply H20 with (lst:=(filter
             (fun x : scenario => inList event_definition_dec (eventDefinition e2) (alphabet x))
             (filterList (finishedscenarios conf1) (dom (controlstate conf1)) scenario_dec))) (e:=e2) (conf:=conf1) (v:=c::v) ;auto.
        apply filterUniq;auto.
        apply  uniqListFilter;
        destruct H13;auto.     
    unfold incl;intros.
    apply filter_In in H29.
    destruct H29.
   apply filterL2 in H29;auto.     
   destruct H23.
   repeat match goal with
            | [ H: _ /\ _ |- _ ] => destruct H

          end.
   repeat(split;auto).
       
Qed.

SearchAbout incl. 


(*NoDup_Permutation_bis*)

Lemma diamondFin: forall M (conf conf1 conf2 conf1': configuration M)  e1 e2, 
(forall v1 v2 , In v1 (dom (datastate conf)) -> In v2 (dom (datastate conf)) -> 
updateVarEv M (eventDefinition e1)  v1 -> updateVarEv M (eventDefinition e2) v2 -> v1 <> v2) -> 
(forall v1 v2 , In v1 (dom (datastate conf)) -> In v2 (dom (datastate conf)) -> 
updateVarEv M (eventDefinition e1)  v1 -> usedVarEv M (eventDefinition e2) v2 -> v1 <> v2) ->
(forall v1 v2 , In v1 (dom (datastate conf)) -> In v2 (dom (datastate conf)) -> 
updateVarEv M (eventDefinition e2)  v1 -> usedVarEv M (eventDefinition e1) v2 -> v1 <> v2)  ->
(forall ev1 ev2, In ev1 (events M) -> In ev2 (events M) -> raisedEv M (eventDefinition e1) ev1 -> 
           eventKind ev1 = Internal -> eventKind ev2 = Internal ->        raisedEv M (eventDefinition e2) ev2 -> ev1 <> ev2) ->
(forall sce1 sce2, In sce1 (dom (controlstate conf)) -> In sce2 (dom (controlstate conf)) -> In (eventDefinition e1) (alphabet sce1) -> In (eventDefinition e2) (alphabet sce2) -> sce1 <> sce2) ->
WellFormed M ->
e1 <> e2 ->
correct_configuration conf -> synchrony conf conf1 e1 ->  synchrony conf conf2 e2 ->
synchrony conf1 conf1' e2 ->
Permutation  (filterList (finishedscenarios conf1) (finishedscenarios conf1') scenario_dec)
             (filterList (finishedscenarios conf) (finishedscenarios conf2) scenario_dec). 
Proof.
  intros.
  assert (incl  (filterList (finishedscenarios conf1) (finishedscenarios conf1') scenario_dec)
      (filterList (finishedscenarios conf) (finishedscenarios conf2) scenario_dec)
      /\
incl  (filterList (finishedscenarios conf) (finishedscenarios conf2) scenario_dec)
      (filterList (finishedscenarios conf1) (finishedscenarios conf1') scenario_dec)).
  
  apply diamondFinAux3 with (e1:=e1) (e2:=e2);auto.
  destruct H10.
  pose proof NoDup_Permutation_bis.
  assert (correct_configuration conf1).
  destruct H4. 
   repeat match goal with
            | [ H: _ /\ _ |- _ ] => destruct H

         end. 
   destruct H15.
     repeat match goal with
            | [ H: _ /\ _ |- _ ] => destruct H

         end. 
     apply termL5 with (conf:=conf) (e:=e1);auto.
     destruct H6.
     apply raised_wellform';auto.
     unfold synchrony in H7;intuition;auto.

    assert (correct_configuration conf2).
  destruct H4. 
   repeat match goal with
            | [ H: _ /\ _ |- _ ] => destruct H

         end. 
   destruct H16.
     repeat match goal with
            | [ H: _ /\ _ |- _ ] => destruct H

         end. 
     apply termL5 with (conf:=conf) (e:=e2);auto.
     destruct H6.
     apply raised_wellform';auto.
     unfold synchrony in H8;intuition;auto.

   assert (correct_configuration conf1').
  destruct H4. 
   repeat match goal with
            | [ H: _ /\ _ |- _ ] => destruct H

         end. 
   destruct H17.
     repeat match goal with
            | [ H: _ /\ _ |- _ ] => destruct H

         end. 
     apply termL5 with (conf:=conf1) (e:=e2);auto.
     destruct H13.
     apply raised_wellform';auto.
     unfold synchrony in H9;intuition;auto.

     
  apply H12;auto.
 
  rewrite <- uniqListNoDupEq.
  apply uniqListFilter;auto.
  destruct H13;auto.
  destruct H15;auto.

   rewrite <- uniqListNoDupEq.
  apply uniqListFilter;auto.
  destruct H6;auto.
  destruct H14;auto.

  SearchAbout incl.
  apply NoDup_incl_length;auto.

    rewrite <- uniqListNoDupEq.
  apply uniqListFilter;auto.
  destruct H6;auto.
  destruct H14;auto.

  

Qed.

Lemma diamondFin': forall M (conf conf1 conf2 conf2': configuration M)  e1 e2, 
(forall v1 v2 , In v1 (dom (datastate conf)) -> In v2 (dom (datastate conf)) -> 
updateVarEv M (eventDefinition e1)  v1 -> updateVarEv M (eventDefinition e2) v2 -> v1 <> v2) -> 
(forall v1 v2 , In v1 (dom (datastate conf)) -> In v2 (dom (datastate conf)) -> 
updateVarEv M (eventDefinition e1)  v1 -> usedVarEv M (eventDefinition e2) v2 -> v1 <> v2) ->
(forall v1 v2 , In v1 (dom (datastate conf)) -> In v2 (dom (datastate conf)) -> 
updateVarEv M (eventDefinition e2)  v1 -> usedVarEv M (eventDefinition e1) v2 -> v1 <> v2)  ->
(forall ev1 ev2, In ev1 (events M) -> In ev2 (events M) -> raisedEv M (eventDefinition e1) ev1 -> 
           eventKind ev1 = Internal -> eventKind ev2 = Internal ->        raisedEv M (eventDefinition e2) ev2 -> ev1 <> ev2) ->
(forall sce1 sce2, In sce1 (dom (controlstate conf)) -> In sce2 (dom (controlstate conf)) -> In (eventDefinition e1) (alphabet sce1) -> In (eventDefinition e2) (alphabet sce2) -> sce1 <> sce2) ->
WellFormed M ->
e1 <> e2 ->
correct_configuration conf -> synchrony conf conf1 e1 ->  synchrony conf conf2 e2 ->
synchrony conf2 conf2' e1 ->
Permutation  (filterList (finishedscenarios conf2) (finishedscenarios conf2') scenario_dec)
             (filterList (finishedscenarios conf) (finishedscenarios conf1) scenario_dec).
Proof.
  intros.
  apply diamondFin with (e1:=e2) (e2:=e1);auto.
  intros.
  unfold not;intros.
  unfold not in H.
  apply H with (v1:=v2) (v2:=v1);auto.

  intros.
  unfold not;intros.
  unfold not in H2.
  apply H2 with (ev1:=ev2) (ev2:=ev1);auto.

   intros.
  unfold not;intros.
  unfold not in H3.
  apply H3 with (sce1:=sce2) (sce2:=sce1);auto.

  

  
Qed.


Lemma diamondFinAll1': forall M (conf conf1 conf2 conf1' conf2': configuration M)  e1 e2 , 
(forall v1 v2 , In v1 (dom (datastate conf)) -> In v2 (dom (datastate conf)) -> 
updateVarEv M (eventDefinition e1)  v1 -> updateVarEv M (eventDefinition e2) v2 -> v1 <> v2) -> 
(forall v1 v2 , In v1 (dom (datastate conf)) -> In v2 (dom (datastate conf)) -> 
updateVarEv M (eventDefinition e1)  v1 -> usedVarEv M (eventDefinition e2) v2 -> v1 <> v2) ->
(forall v1 v2 , In v1 (dom (datastate conf)) -> In v2 (dom (datastate conf)) -> 
updateVarEv M (eventDefinition e2)  v1 -> usedVarEv M (eventDefinition e1) v2 -> v1 <> v2)  ->
(forall ev1 ev2, In ev1 (events M) -> In ev2 (events M) -> raisedEv M (eventDefinition e1) ev1 -> 
           eventKind ev1 = Internal -> eventKind ev2 = Internal ->        raisedEv M (eventDefinition e2) ev2 -> ev1 <> ev2) ->
(forall sce1 sce2, In sce1 (dom (controlstate conf)) -> In sce2 (dom (controlstate conf)) -> In (eventDefinition e1) (alphabet sce1) -> In (eventDefinition e2) (alphabet sce2) -> sce1 <> sce2) ->
WellFormed M ->
e1 <> e2 ->
correct_configuration conf -> synchrony conf conf1 e1 ->  synchrony conf conf2 e2 ->
synchrony conf1 conf1' e2 -> synchrony conf2 conf2' e1 ->
incl (filterList (finishedscenarios conf) (finishedscenarios conf2') scenario_dec)
     (filterList (finishedscenarios conf) (finishedscenarios conf1') scenario_dec). 
Proof.
  intros.
  unfold incl;intros.
    remember H11.
    clear Heqi.
    apply filterL1 in H11.
    apply filterL2 in i;auto.
    apply filterIn;auto.
    assert (In a (finishedscenarios conf2) \/ ~ In a (finishedscenarios conf2)).
    apply excluded_middle.
    destruct H12.
    remember H8.
    clear Heqs.
    apply syncFinish with (sce:=a) in s;auto.
    assert (~ In (eventDefinition e1) (alphabet a)).
    unfold not;intros.
    unfold not in H3.

      assert (correct_configuration conf2).
     destruct H4.
   repeat match goal with
            | [ H: _ /\ _ |- _ ] => destruct H

         end. 
   destruct H16.
     repeat match goal with
            | [ H: _ /\ _ |- _ ] => destruct H

         end. 
     apply termL5 with (conf:=conf) (e:=e2);auto.
     destruct H6.
     apply raised_wellform';auto.
     unfold synchrony in H8;intuition;auto.

     assert (In a (dom (controlstate conf))).
   rewrite domControlSync with (conf':=conf2) (e:=e2);auto.      
   destruct H14.
   unfold scenarioInclusion in inclusion.
   unfold incl in inclusion;apply inclusion;auto.    
   

    apply H3 with (sce1:=a) (sce2:=a);auto.
    assert (~ In a (finishedscenarios conf1)).
    unfold not;intros.
    apply syncFinish with (sce:=a) in H7;auto.
    remember H9.
    clear Heqs0.
    assert (correct_configuration conf1).
    destruct H4.
 
   repeat match goal with
            | [ H: _ /\ _ |- _ ] => destruct H

         end. 
   destruct H17.
     repeat match goal with
            | [ H: _ /\ _ |- _ ] => destruct H

         end. 
     apply termL5 with (conf:=conf) (e:=e1);auto.
     destruct H6.
     apply raised_wellform';auto.
     unfold synchrony in H7;intuition;auto.

     assert (correct_configuration conf2).
    destruct H4.
 
   repeat match goal with
            | [ H: _ /\ _ |- _ ] => destruct H

         end. 
   destruct H18.
     repeat match goal with
            | [ H: _ /\ _ |- _ ] => destruct H

         end. 
     apply termL5 with (conf:=conf) (e:=e2);auto.
     destruct H6.
     apply raised_wellform';auto.
     unfold synchrony in H8;intuition;auto.


      assert (correct_configuration conf1').
    destruct H4.
 
   repeat match goal with
            | [ H: _ /\ _ |- _ ] => destruct H

         end. 
   destruct H19.
     repeat match goal with
            | [ H: _ /\ _ |- _ ] => destruct H

         end. 
     apply termL5 with (conf:=conf1) (e:=e2);auto.
     destruct H15.
     apply raised_wellform';auto.
     unfold synchrony in H9;intuition;auto.

     unfold synchrony in s0.
     destruct s0.
     unfold combineFunc in H19.
     remember (constructConfigList (dom (controlstate conf1)) e2 conf1).
     destruct e;inversion H19.
     clear H21.
     unfold constructConfigList in Heqe.
     destruct v;inversion H19.
     clear H21.
     remember (innerCombineFunc'''' conf1 (c :: v)).
     destruct o;inversion H19.
    simpl.      
    pose proof finishedInList'.
    assert (In a (filter
              (fun x : scenario => inList event_definition_dec (eventDefinition e2) (alphabet x))
              (filterList (finishedscenarios conf1) (dom (controlstate conf1)) scenario_dec)) ).
    apply filter_In;auto.
    split.
    apply filterIn;auto.
    rewrite <- domControlSync with (conf:=conf) (e:=e1);auto.
    rewrite  domControlSync with (conf':=conf2) (e:=e2);auto.    
    destruct H16.
    unfold  scenarioInclusion in inclusion.
    unfold incl in inclusion.
    apply inclusion;auto.
    SearchAbout inList.
    apply inListLemma;auto.
    apply H20 with (lst:= (filter
              (fun x : scenario => inList event_definition_dec (eventDefinition e2) (alphabet x))
              (filterList (finishedscenarios conf1) (dom (controlstate conf1)) scenario_dec)))
                   (e:=e2) (conf:=conf1) (v:=c::v) ;auto.
    SearchAbout uniqList.
    apply filterUniq;auto.
    SearchAbout filterList.
    apply uniqListFilter;destruct H15;auto.
    unfold incl;intros.
    apply filter_In in H23.
    destruct H23.
    apply filterL2 in H23;auto.     
    destruct H4;intuition;auto.         
    destruct H4.
     repeat match goal with
            | [ H: _ /\ _ |- _ ] => destruct H

         end. 
    
     destruct H25.
     repeat match goal with
            | [ H: _ /\ _ |- _ ] => destruct H

            end.
     repeat(split;auto).

     assert (correct_configuration conf1).
    destruct H4.
 
   repeat match goal with
            | [ H: _ /\ _ |- _ ] => destruct H

         end. 
   destruct H15.
     repeat match goal with
            | [ H: _ /\ _ |- _ ] => destruct H

         end. 
     apply termL5 with (conf:=conf) (e:=e1);auto.
     destruct H6.
     apply raised_wellform';auto.
     unfold synchrony in H7;intuition;auto.

     assert (correct_configuration conf2).
    destruct H4.
 
   repeat match goal with
            | [ H: _ /\ _ |- _ ] => destruct H

         end. 
   destruct H16.
     repeat match goal with
            | [ H: _ /\ _ |- _ ] => destruct H

         end. 
     apply termL5 with (conf:=conf) (e:=e2);auto.
     destruct H6.
     apply raised_wellform';auto.
     unfold synchrony in H8;intuition;auto.

      assert (correct_configuration conf2').
    destruct H4.
 
   repeat match goal with
            | [ H: _ /\ _ |- _ ] => destruct H

         end. 
   destruct H17.
     repeat match goal with
            | [ H: _ /\ _ |- _ ] => destruct H

         end. 
     apply termL5 with (conf:=conf2) (e:=e1);auto.
     destruct H14.
     apply raised_wellform';auto.
     unfold synchrony in H10;intuition;auto.
     

    assert (In (eventDefinition e1) (alphabet a)).
    apply syncFinish with (sce:=a) in H10;auto.
    assert (~ In (eventDefinition e2) (alphabet a)). 
    unfold not;intros.
    unfold not in H3.


     assert (In a (dom (controlstate conf))).
   rewrite domControlSync with (conf':=conf2) (e:=e2);auto.      
   rewrite domControlSync with (conf':=conf2') (e:=e1);auto.
   destruct H15.
   unfold scenarioInclusion in inclusion.
   unfold incl in inclusion;apply inclusion;auto.    
   
    apply H3 with (sce1:=a) (sce2:=a);auto.

    assert (In a (finishedscenarios conf1)).

    remember H7.
    clear Heqs.

     unfold synchrony in s.
     destruct s.
     unfold combineFunc in H19.
     remember (constructConfigList (dom (controlstate conf)) e1 conf).
     destruct e;inversion H19.
     clear H21.
     unfold constructConfigList in Heqe.
     destruct v;inversion H19.
     clear H21.
     remember (innerCombineFunc'''' conf (c :: v)).
     destruct o;inversion H19.
    simpl.      
    pose proof finishedInList'.
    assert (In a (filter
              (fun x : scenario => inList event_definition_dec (eventDefinition e1) (alphabet x))
              (filterList (finishedscenarios conf) (dom (controlstate conf)) scenario_dec)) ).
    apply filter_In;auto.
    split.
    apply filterIn;auto.
    rewrite  domControlSync with (conf':=conf2) (e:=e2);auto.
    rewrite  domControlSync with (conf':=conf2') (e:=e1);auto.
    
    destruct H15.
    unfold  scenarioInclusion in inclusion.
    unfold incl in inclusion.
    apply inclusion;auto.
  
    apply inListLemma;auto.
    apply H20 with (lst:= (filter
              (fun x : scenario => inList event_definition_dec (eventDefinition e1) (alphabet x))
              (filterList (finishedscenarios conf) (dom (controlstate conf)) scenario_dec)))
                   (e:=e1) (conf:=conf) (v:=c::v) ;auto.
    apply filterUniq;auto.
    apply uniqListFilter;destruct H6;auto.
    unfold incl;intros.
    apply filter_In in H23.
    destruct H23.
    apply filterL2 in H23;auto.     
    destruct H4;intuition;auto.         
    destruct H4.
     repeat match goal with
            | [ H: _ /\ _ |- _ ] => destruct H

         end. 
    
     destruct H25.
     repeat match goal with
            | [ H: _ /\ _ |- _ ] => destruct H

            end.
     repeat(split;auto).

     SearchAbout finishedscenarios.
     apply  finishedInvariantSync with (conf:=conf1) (e:=e2);auto.
Qed.


Lemma diamondFinAll1'': forall M (conf conf1 conf2 conf1' conf2': configuration M)  e1 e2 , 
(forall v1 v2 , In v1 (dom (datastate conf)) -> In v2 (dom (datastate conf)) -> 
updateVarEv M (eventDefinition e1)  v1 -> updateVarEv M (eventDefinition e2) v2 -> v1 <> v2) -> 
(forall v1 v2 , In v1 (dom (datastate conf)) -> In v2 (dom (datastate conf)) -> 
updateVarEv M (eventDefinition e1)  v1 -> usedVarEv M (eventDefinition e2) v2 -> v1 <> v2) ->
(forall v1 v2 , In v1 (dom (datastate conf)) -> In v2 (dom (datastate conf)) -> 
updateVarEv M (eventDefinition e2)  v1 -> usedVarEv M (eventDefinition e1) v2 -> v1 <> v2)  ->
(forall ev1 ev2, In ev1 (events M) -> In ev2 (events M) -> raisedEv M (eventDefinition e1) ev1 -> 
           eventKind ev1 = Internal -> eventKind ev2 = Internal ->        raisedEv M (eventDefinition e2) ev2 -> ev1 <> ev2) ->
(forall sce1 sce2, In sce1 (dom (controlstate conf)) -> In sce2 (dom (controlstate conf)) -> In (eventDefinition e1) (alphabet sce1) -> In (eventDefinition e2) (alphabet sce2) -> sce1 <> sce2) ->
WellFormed M ->
e1 <> e2 ->
correct_configuration conf -> synchrony conf conf1 e1 ->  synchrony conf conf2 e2 ->
synchrony conf1 conf1' e2 -> synchrony conf2 conf2' e1 ->
incl (filterList (finishedscenarios conf) (finishedscenarios conf1') scenario_dec)
     (filterList (finishedscenarios conf) (finishedscenarios conf2') scenario_dec). 
Proof.
  intros.
  apply diamondFinAll1' with (conf1:=conf2) (conf2:=conf1) (e1:=e2) (e2:=e1);auto.
  intros.
  unfold not in H;unfold not;intros;apply H with (v1:=v2) (v2:=v1);auto.   
  intros;unfold not in H2;unfold not;intros;apply H2 with (ev1:=ev2) (ev2:=ev1);auto.
   intros;unfold not in H3;unfold not;intros;apply H3 with (sce1:=sce2) (sce2:=sce1);auto.
  
Qed.


Lemma diamondFinAll1: forall M (conf conf1 conf2 conf1' conf2': configuration M)  e1 e2 , 
(forall v1 v2 , In v1 (dom (datastate conf)) -> In v2 (dom (datastate conf)) -> 
updateVarEv M (eventDefinition e1)  v1 -> updateVarEv M (eventDefinition e2) v2 -> v1 <> v2) -> 
(forall v1 v2 , In v1 (dom (datastate conf)) -> In v2 (dom (datastate conf)) -> 
updateVarEv M (eventDefinition e1)  v1 -> usedVarEv M (eventDefinition e2) v2 -> v1 <> v2) ->
(forall v1 v2 , In v1 (dom (datastate conf)) -> In v2 (dom (datastate conf)) -> 
updateVarEv M (eventDefinition e2)  v1 -> usedVarEv M (eventDefinition e1) v2 -> v1 <> v2)  ->
(forall ev1 ev2, In ev1 (events M) -> In ev2 (events M) -> raisedEv M (eventDefinition e1) ev1 -> 
           eventKind ev1 = Internal -> eventKind ev2 = Internal ->        raisedEv M (eventDefinition e2) ev2 -> ev1 <> ev2) ->
(forall sce1 sce2, In sce1 (dom (controlstate conf)) -> In sce2 (dom (controlstate conf)) -> In (eventDefinition e1) (alphabet sce1) -> In (eventDefinition e2) (alphabet sce2) -> sce1 <> sce2) ->
WellFormed M ->
e1 <> e2 ->
correct_configuration conf -> synchrony conf conf1 e1 ->  synchrony conf conf2 e2 ->
synchrony conf1 conf1' e2 -> synchrony conf2 conf2' e1 ->
incl (filterList (finishedscenarios conf) (finishedscenarios conf2') scenario_dec)
     (filterList (finishedscenarios conf) (finishedscenarios conf1') scenario_dec)
/\
incl (filterList (finishedscenarios conf) (finishedscenarios conf1') scenario_dec)
     (filterList (finishedscenarios conf) (finishedscenarios conf2') scenario_dec). 
Proof.
  intros.
  split.
  apply diamondFinAll1' with (conf1:=conf1) (conf2:=conf2) (e1:=e1) (e2:=e2);auto.
   apply diamondFinAll1'' with (conf1:=conf1) (conf2:=conf2) (e1:=e1) (e2:=e2);auto.

Qed.


Lemma diamondFinAll2: forall M (conf conf1 conf2 conf1' conf2': configuration M)  e1 e2 , 
(forall v1 v2 , In v1 (dom (datastate conf)) -> In v2 (dom (datastate conf)) -> 
updateVarEv M (eventDefinition e1)  v1 -> updateVarEv M (eventDefinition e2) v2 -> v1 <> v2) -> 
(forall v1 v2 , In v1 (dom (datastate conf)) -> In v2 (dom (datastate conf)) -> 
updateVarEv M (eventDefinition e1)  v1 -> usedVarEv M (eventDefinition e2) v2 -> v1 <> v2) ->
(forall v1 v2 , In v1 (dom (datastate conf)) -> In v2 (dom (datastate conf)) -> 
updateVarEv M (eventDefinition e2)  v1 -> usedVarEv M (eventDefinition e1) v2 -> v1 <> v2)  ->
(forall ev1 ev2, In ev1 (events M) -> In ev2 (events M) -> raisedEv M (eventDefinition e1) ev1 -> 
          eventKind ev1 = Internal -> eventKind ev2 = Internal ->         raisedEv M (eventDefinition e2) ev2 -> ev1 <> ev2) ->
(forall sce1 sce2, In sce1 (dom (controlstate conf)) -> In sce2 (dom (controlstate conf)) -> In (eventDefinition e1) (alphabet sce1) -> In (eventDefinition e2) (alphabet sce2) -> sce1 <> sce2) ->
WellFormed M ->
e1 <> e2 ->
correct_configuration conf -> synchrony conf conf1 e1 ->  synchrony conf conf2 e2 ->
synchrony conf1 conf1' e2 -> synchrony conf2 conf2' e1 ->
Permutation (filterList (finishedscenarios conf) (finishedscenarios conf2') scenario_dec)
            (filterList (finishedscenarios conf) (finishedscenarios conf1') scenario_dec).


Proof.
  intros.
  
  pose proof diamondFinAll1;auto.

  assert (   incl (filterList (finishedscenarios conf) (finishedscenarios conf2') scenario_dec)
          (filterList (finishedscenarios conf) (finishedscenarios conf1') scenario_dec) /\
        incl (filterList (finishedscenarios conf) (finishedscenarios conf1') scenario_dec)
          (filterList (finishedscenarios conf) (finishedscenarios conf2') scenario_dec)). 

  apply H11 with (conf1:=conf1) (conf2:=conf2) (e1:=e1) (e2:=e2);auto.

  destruct H12.
  pose proof NoDup_Permutation_bis.
  apply H14;auto.
  SearchAbout NoDup.
  rewrite <- uniqListNoDupEq.
  apply uniqListFilter;auto.
  destruct H6;auto.
  assert (correct_configuration conf2').
  destruct H4.

     repeat match goal with
            | [ H: _ /\ _ |- _ ] => destruct H

         end. 
    
     destruct H17.
     repeat match goal with
            | [ H: _ /\ _ |- _ ] => destruct H

            end.
     apply termL5 with (conf:=conf2) (e:=e1);auto.
     apply termL5 with (conf:=conf) (e:=e2);auto.
     destruct H6.
     apply raised_wellform';auto.
     unfold synchrony in H8;intuition;auto.
    destruct H6.  unfold synchrony in H7;intuition;auto.

    destruct H15;auto.

    assert (correct_configuration conf1').
  destruct H4.

     repeat match goal with
            | [ H: _ /\ _ |- _ ] => destruct H

         end. 
    
     destruct H17.
     repeat match goal with
            | [ H: _ /\ _ |- _ ] => destruct H

            end.
     apply termL5 with (conf:=conf1) (e:=e2);auto.
     apply termL5 with (conf:=conf) (e:=e1);auto.
     destruct H6.
     apply raised_wellform';auto.
     unfold synchrony in H7;intuition;auto.
    destruct H6.  unfold synchrony in H8;intuition;auto.

    rewrite <- uniqListNoDupEq.
  apply uniqListFilter;auto.
  destruct H6;auto.
  destruct H15;auto.
  SearchAbout incl.
  apply NoDup_incl_length;auto.

    rewrite <- uniqListNoDupEq.
  apply uniqListFilter;auto.
  destruct H6;auto.

   assert (correct_configuration conf1').
  destruct H4.

     repeat match goal with
            | [ H: _ /\ _ |- _ ] => destruct H

         end. 
    
     destruct H17.
     repeat match goal with
            | [ H: _ /\ _ |- _ ] => destruct H

            end.
     apply termL5 with (conf:=conf1) (e:=e2);auto.
     apply termL5 with (conf:=conf) (e:=e1);auto.
     destruct H6.
     apply raised_wellform';auto.
     unfold synchrony in H7;intuition;auto.
     destruct H6.  unfold synchrony in H8;intuition;auto.
     destruct H15;auto.
     

  
  
Qed.



Lemma filterListNil': forall A (l:list A) decA,
    l = filterList nil l decA.
Proof.
     intros A l. induction l. 
     intros.        simpl;auto.
  simpl.   intros. f_equal;auto. 
Qed.

Lemma diamondFinAll3: forall M (conf conf1 conf2 conf1' conf2': configuration M)  e1 e2 , 
(forall v1 v2 , In v1 (dom (datastate conf)) -> In v2 (dom (datastate conf)) -> 
updateVarEv M (eventDefinition e1)  v1 -> updateVarEv M (eventDefinition e2) v2 -> v1 <> v2) -> 
(forall v1 v2 , In v1 (dom (datastate conf)) -> In v2 (dom (datastate conf)) -> 
updateVarEv M (eventDefinition e1)  v1 -> usedVarEv M (eventDefinition e2) v2 -> v1 <> v2) ->
(forall v1 v2 , In v1 (dom (datastate conf)) -> In v2 (dom (datastate conf)) -> 
updateVarEv M (eventDefinition e2)  v1 -> usedVarEv M (eventDefinition e1) v2 -> v1 <> v2)  ->
(forall ev1 ev2, In ev1 (events M) -> In ev2 (events M) -> raisedEv M (eventDefinition e1) ev1 -> 
            eventKind ev1 = Internal -> eventKind ev2 = Internal ->       raisedEv M (eventDefinition e2) ev2 -> ev1 <> ev2) ->
(forall sce1 sce2, In sce1 (dom (controlstate conf)) -> In sce2 (dom (controlstate conf)) -> In (eventDefinition e1) (alphabet sce1) -> In (eventDefinition e2) (alphabet sce2) -> sce1 <> sce2) ->
WellFormed M ->
e1 <> e2 ->
correct_configuration conf -> synchrony conf conf1 e1 ->  synchrony conf conf2 e2 ->
synchrony conf1 conf1' e2 -> synchrony conf2 conf2' e1 ->
incl (finishedscenarios conf2')
     (finishedscenarios conf1')
/\
incl (finishedscenarios conf1')
 (finishedscenarios conf2'). 
Proof.
  intros.
  pose proof diamondFinAll1.
  assert (        incl (filterList (finishedscenarios conf) (finishedscenarios conf2') scenario_dec)
          (filterList (finishedscenarios conf) (finishedscenarios conf1') scenario_dec) /\
        incl (filterList (finishedscenarios conf) (finishedscenarios conf1') scenario_dec)
             (filterList (finishedscenarios conf) (finishedscenarios conf2') scenario_dec)).
  apply H11 with (conf1:=conf1) (conf2:=conf2) (e1:=e1) (e2:=e2);auto.
  destruct H12.
  unfold incl in H12.
  unfold incl in H13.   
  split.
  - unfold incl;intros.
    assert (In a (finishedscenarios conf) \/ ~ In a (finishedscenarios conf)).
    apply excluded_middle.
    destruct H15.
    assert (In a (finishedscenarios conf1)).
    apply  finishedInvariantSync with (conf:=conf) (e:=e1);auto.
     apply  finishedInvariantSync with (conf:=conf1) (e:=e2);auto.
     assert (In a (filterList (finishedscenarios conf) (finishedscenarios conf2') scenario_dec) ).
     apply filterIn;auto.
     apply H12 in H16.
     apply filterL2 in H16;auto.      
  - unfold incl;intros.
    assert (In a (finishedscenarios conf) \/ ~ In a (finishedscenarios conf)).
    apply excluded_middle.
    destruct H15.
    assert (In a (finishedscenarios conf2)).
    apply  finishedInvariantSync with (conf:=conf) (e:=e2);auto.
     apply  finishedInvariantSync with (conf:=conf2) (e:=e1);auto.
     assert (In a (filterList (finishedscenarios conf) (finishedscenarios conf1') scenario_dec) ).
     apply filterIn;auto.
     apply H13 in H16.
     apply filterL2 in H16;auto.
     
Qed.

 
Lemma diamondFinAll: forall M (conf conf1 conf2 conf1' conf2': configuration M)  e1 e2 , 
(forall v1 v2 , In v1 (dom (datastate conf)) -> In v2 (dom (datastate conf)) -> 
updateVarEv M (eventDefinition e1)  v1 -> updateVarEv M (eventDefinition e2) v2 -> v1 <> v2) -> 
(forall v1 v2 , In v1 (dom (datastate conf)) -> In v2 (dom (datastate conf)) -> 
updateVarEv M (eventDefinition e1)  v1 -> usedVarEv M (eventDefinition e2) v2 -> v1 <> v2) ->
(forall v1 v2 , In v1 (dom (datastate conf)) -> In v2 (dom (datastate conf)) -> 
updateVarEv M (eventDefinition e2)  v1 -> usedVarEv M (eventDefinition e1) v2 -> v1 <> v2)  ->
(forall ev1 ev2, In ev1 (events M) -> In ev2 (events M) -> raisedEv M (eventDefinition e1) ev1 -> 
           eventKind ev1 = Internal -> eventKind ev2 = Internal ->        raisedEv M (eventDefinition e2) ev2 -> ev1 <> ev2) ->
(forall sce1 sce2, In sce1 (dom (controlstate conf)) -> In sce2 (dom (controlstate conf)) -> In (eventDefinition e1) (alphabet sce1) -> In (eventDefinition e2) (alphabet sce2) -> sce1 <> sce2) ->
WellFormed M ->
e1 <> e2 ->
correct_configuration conf -> synchrony conf conf1 e1 ->  synchrony conf conf2 e2 ->
synchrony conf1 conf1' e2 -> synchrony conf2 conf2' e1 ->
Permutation(finishedscenarios conf2')
     (finishedscenarios conf1')
.
Proof.
  intros.
  pose proof diamondFinAll3.
  assert  (incl (finishedscenarios conf2') (finishedscenarios conf1') /\
           incl (finishedscenarios conf1') (finishedscenarios conf2')).
  apply H11 with (conf:=conf) (conf1:=conf1) (conf2:=conf2) (e1:=e1) (e2:=e2);auto.
  destruct H12.
  assert (correct_configuration conf1).
    destruct H4.

     repeat match goal with
            | [ H: _ /\ _ |- _ ] => destruct H

         end. 
    
     destruct H16.
              
              
     repeat match goal with
            | [ H: _ /\ _ |- _ ] => destruct H

            end.
     apply termL5 with (conf:=conf) (e:=e1);auto.
   
     destruct H6.
     apply raised_wellform';auto.
     unfold synchrony in H7;intuition;auto.

   assert (correct_configuration conf2).
    destruct H4.

     repeat match goal with
            | [ H: _ /\ _ |- _ ] => destruct H

         end. 
    
     destruct H17.
              
              
     repeat match goal with
            | [ H: _ /\ _ |- _ ] => destruct H

            end.
     apply termL5 with (conf:=conf) (e:=e2);auto.
   
     destruct H6.
     apply raised_wellform';auto.
     unfold synchrony in H8;intuition;auto.

      assert (correct_configuration conf1').
    destruct H4.

     repeat match goal with
            | [ H: _ /\ _ |- _ ] => destruct H

         end. 
    
     destruct H18.
              
              
     repeat match goal with
            | [ H: _ /\ _ |- _ ] => destruct H

            end.
     apply termL5 with (conf:=conf1) (e:=e2);auto.
   
     destruct H14.
     apply raised_wellform';auto.
     unfold synchrony in H9;intuition;auto.

      assert (correct_configuration conf2').
    destruct H4.

     repeat match goal with
            | [ H: _ /\ _ |- _ ] => destruct H

         end. 
    
     destruct H19.
              
              
     repeat match goal with
            | [ H: _ /\ _ |- _ ] => destruct H

            end.
     apply termL5 with (conf:=conf2) (e:=e1);auto.
   
     destruct H15.
     apply raised_wellform';auto.
     unfold synchrony in H10;intuition;auto.


  apply NoDup_Permutation_bis;auto.
  SearchAbout NoDup.
  rewrite <- uniqListNoDupEq;auto.
  destruct H17;auto.
   rewrite <- uniqListNoDupEq;auto.
   destruct H16;auto.
   SearchAbout NoDup.
   apply NoDup_incl_length;auto.
    rewrite <- uniqListNoDupEq;auto.  destruct H16;auto.
Qed.

Print equivConf.



Lemma chainMergeFinMap'
     : forall (M : monitor) (conf : configuration M) (sce : scenario),
    correct_configuration conf ->
       In sce (finishedscenarios conf) <->
       (exists ev : event_definition, In (sce, ev) (sceEventMap conf)).
Proof.
  intros.
  destruct H.
  split;intros.
  
-
  rewrite <-  sceEventMapRange in H.
  apply domInRev;auto.
-  destruct H.
   rewrite <- sceEventMapRange;auto. 
    apply domIn with (x:=x);auto.    
  Qed. 


Lemma domInUniq: forall (A B:Type) (s:A) (e x: B) (env: list (A*B)),
    In (s,e) ( env) ->
    In (s,x) ( env) ->
    uniqList (dom env) ->
    e = x. 
Proof. intros.
generalize dependent s. 
generalize dependent e.
generalize dependent x. 
induction env;intros.
- inversion H.
- destruct H.  destruct H0. destruct a. inversion H;inversion H0;subst;auto.
  inversion H1;subst.
  simpl in H5.
  SearchAbout dom.
  apply domIn in H0.   contradiction.
  destruct H0.
  subst.
  simpl in *. inversion H1;subst. apply domIn in H.   contradiction.
  apply IHenv with (s:=s);auto.
  inversion H1;subst;auto.  
Qed.


Lemma syncFinishIn: forall M (conf conf': configuration M) s e,
    WellFormed M ->
    correct_configuration conf ->
    synchrony conf conf' e ->
    In s (dom (controlstate conf)) ->
    In (eventDefinition e) (alphabet s) ->
    In s (finishedscenarios conf').
Proof.
  intros.
  assert (In s (finishedscenarios conf) \/ ~ In s (finishedscenarios conf)).
  apply excluded_middle.
  destruct H4.
  SearchAbout finishedscenarios.
  apply finishedInvariantSync with (conf:=conf) (e:=e);auto.
  remember H1.
  clear Heqs0.
  pose proof finishedInList'.   
  unfold synchrony in H1.
  destruct H1.
  unfold combineFunc in H6.
  remember (constructConfigList (dom (controlstate conf)) e conf).
  destruct e0;inversion H6.
  clear H8.
  unfold  constructConfigList in Heqe0.
  destruct v;inversion H6.
  clear H8.
  remember (innerCombineFunc'''' conf (c :: v)).
  destruct o;inversion H6;simpl.   
  apply H5 with (lst:=(filter
               (fun x : scenario => inList event_definition_dec (eventDefinition e) (alphabet x))
               (filterList (finishedscenarios conf) (dom (controlstate conf)) scenario_dec))) (e:=e) (conf:=conf) (v:=c::v);auto.
  SearchAbout uniqList. 
  apply filterUniq;auto.   
  apply uniqListFilter;destruct H0;auto. 
  unfold incl;intros.
  apply filter_In in H7;destruct H7.
  apply filterL2 in H7;auto.
  apply filter_In;auto.
  split;auto.
  apply filterIn;auto.
  SearchAbout inList.
  apply inListLemma;auto.
  destruct H.
  intuition;auto.
  destruct H. 
 repeat match goal with
            | [ H: _ /\ _ |- _ ] => destruct H

            end.
      destruct H10.
   repeat match goal with
            | [ H: _ /\ _ |- _ ] => destruct H

          end.
   repeat(split;auto).
Qed.    
   

Lemma diamondFinMap1: forall M (conf conf1 conf2 conf1' conf2': configuration M)  e1 e2 , 
(forall v1 v2 , In v1 (dom (datastate conf)) -> In v2 (dom (datastate conf)) -> 
updateVarEv M (eventDefinition e1)  v1 -> updateVarEv M (eventDefinition e2) v2 -> v1 <> v2) -> 
(forall v1 v2 , In v1 (dom (datastate conf)) -> In v2 (dom (datastate conf)) -> 
updateVarEv M (eventDefinition e1)  v1 -> usedVarEv M (eventDefinition e2) v2 -> v1 <> v2) ->
(forall v1 v2 , In v1 (dom (datastate conf)) -> In v2 (dom (datastate conf)) -> 
updateVarEv M (eventDefinition e2)  v1 -> usedVarEv M (eventDefinition e1) v2 -> v1 <> v2)  ->
(forall ev1 ev2, In ev1 (events M) -> In ev2 (events M) -> raisedEv M (eventDefinition e1) ev1 -> 
           eventKind ev1 = Internal -> eventKind ev2 = Internal ->        raisedEv M (eventDefinition e2) ev2 -> ev1 <> ev2) ->
(forall sce1 sce2, In sce1 (dom (controlstate conf)) -> In sce2 (dom (controlstate conf)) -> In (eventDefinition e1) (alphabet sce1) -> In (eventDefinition e2) (alphabet sce2) -> sce1 <> sce2) ->
WellFormed M ->
e1 <> e2 ->
correct_configuration conf -> synchrony conf conf1 e1 ->  synchrony conf conf2 e2 ->
synchrony conf1 conf1' e2 -> synchrony conf2 conf2' e1 ->
incl (sceEventMap conf2')
     (sceEventMap conf1').
Proof.
  intros.
  unfold incl;intros.

  assert (correct_configuration conf1).

   destruct H4.

     repeat match goal with
            | [ H: _ /\ _ |- _ ] => destruct H

         end. 
    
     destruct H14.
              
              
     repeat match goal with
            | [ H: _ /\ _ |- _ ] => destruct H

            end.
     apply termL5 with (conf:=conf) (e:=e1);auto.
   
     destruct H6.
     apply raised_wellform';auto.
     unfold synchrony in H7;intuition;auto.

     
   assert (correct_configuration conf2).

   destruct H4.

     repeat match goal with
            | [ H: _ /\ _ |- _ ] => destruct H

         end. 
    
     destruct H15.
              
              
     repeat match goal with
            | [ H: _ /\ _ |- _ ] => destruct H

            end.
     apply termL5 with (conf:=conf) (e:=e2);auto.
   
     destruct H6.
     apply raised_wellform';auto.
     unfold synchrony in H8;intuition;auto.

   assert (correct_configuration conf1').

   destruct H4.

     repeat match goal with
            | [ H: _ /\ _ |- _ ] => destruct H

         end. 
    
     destruct H16.
              
              
     repeat match goal with
            | [ H: _ /\ _ |- _ ] => destruct H

            end.
     apply termL5 with (conf:=conf1) (e:=e2);auto.
   
     destruct H12.
     apply raised_wellform';auto.
     unfold synchrony in H9;intuition;auto.

       assert (correct_configuration conf2').

   destruct H4.

     repeat match goal with
            | [ H: _ /\ _ |- _ ] => destruct H

         end. 
    
     destruct H17.
              
              
     repeat match goal with
            | [ H: _ /\ _ |- _ ] => destruct H

            end.
     apply termL5 with (conf:=conf2) (e:=e1);auto.
   
     destruct H13.
     apply raised_wellform';auto.
     unfold synchrony in H10;intuition;auto.
     destruct a.
  
  assert ((exists e', In (s,e') (sceEventMap conf)) \/ ~ (exists e', In (s,e') (sceEventMap conf))).
  apply excluded_middle.
  destruct H16.
  destruct H16.
  Check sceEventMapNoChangeSync.
   assert (In (s,x) (sceEventMap conf2)). 
  

  apply sceEventMapNoChangeSync with (conf:=conf) (e:=e2);auto.

  

  pose proof chainMergeFinMap'.
  rewrite H17. exists x;auto.
  auto. 

   assert (In (s,x) (sceEventMap conf2')). 
    apply sceEventMapNoChangeSync with (conf:=conf2) (e:=e1);auto.

  

  pose proof chainMergeFinMap'.
  rewrite H18. exists x;auto.
  auto.
  assert (e = x \/ e <> x).
  apply excluded_middle.
  destruct H19. subst.

  assert (In (s,x) (sceEventMap conf1)).

  apply sceEventMapNoChangeSync with (conf:=conf) (e:=e1);auto.
  rewrite chainMergeFinMap';auto.
  exists x;auto.
   apply sceEventMapNoChangeSync with (conf:=conf1) (e:=e2);auto.  
  rewrite chainMergeFinMap';auto.
  exists x;auto.
  assert (uniqList (dom (sceEventMap conf2'))).
  destruct H15.
   rewrite uniqListNoDupEq.
   SearchAbout uniqList. rewrite uniqListNoDupEq in finish_uniq.
      apply Permutation_NoDup with (l':=dom (sceEventMap conf2')) in finish_uniq;auto.
      apply Permutation_sym;auto.
      
  pose proof domInUniq.
  apply H21 with (e:=e) (x:=x) in H11;auto.   
  contradiction.

  assert (~ In s (finishedscenarios conf)).
  rewrite chainMergeFinMap';auto.

   assert ((exists e', In (s,e') (sceEventMap conf2)) \/ ~ (exists e', In (s,e') (sceEventMap conf2))).

   apply excluded_middle.
   destruct H18.
   destruct H18.
   SearchAbout sceEventMap.
   assert (x = eventDefinition e2).
   destruct H4.
      repeat match goal with
            | [ H: _ /\ _ |- _ ] => destruct H

            end.
      destruct H21.
   repeat match goal with
            | [ H: _ /\ _ |- _ ] => destruct H

            end.     
      apply syncMapFinishEventDef with (M:=M) (conf:=conf) (conf':=conf2) (sce:=s);auto.
      repeat(split;auto).
   unfold synchrony in H8;intuition;auto.       
   unfold not;intros.
  apply H16;exists x;auto.    
  subst.
  assert (In (s, eventDefinition e2) (sceEventMap conf2')).
  apply sceEventMapNoChangeSync with (conf:=conf2) (e:=e1);auto.
  SearchAbout sceEventMap.
  rewrite  chainMergeFinMap'. 
  exists (eventDefinition e2);auto.  
  auto. 
  assert (e = eventDefinition e2).
  apply domInUniq with (A:=scenario) (s:=s) (env:= (sceEventMap conf2'));auto.

  

  destruct H15.

   rewrite uniqListNoDupEq.
 rewrite uniqListNoDupEq in finish_uniq.
      apply Permutation_NoDup with (l':=dom (sceEventMap conf2')) in finish_uniq;auto.
      apply Permutation_sym;auto.

      
  subst. 
  assert ( ~ (exists e' : event_definition, In (s, e') (sceEventMap conf1))). 
  unfold not;intros.
    rewrite <- chainMergeFinMap' in H20;auto.  
    assert (In (eventDefinition e1) (alphabet s)).
    apply syncFinish with (conf:=conf) (conf':=conf1) (re:=e1);auto.
    assert (In (eventDefinition e2) (alphabet s)).
    destruct H13.
    apply   sceEventMapAlphabet;auto.
    assert (In s (dom (controlstate conf))).
    rewrite domControlSync with (conf':=conf1) (e:=e1);auto.     
    destruct H12.
    unfold scenarioInclusion in inclusion;unfold incl in inclusion;apply inclusion;auto.    
    unfold not in H3.
    apply H3 with (sce1:=s) (sce2:=s);auto.


    assert (In (eventDefinition e2) (alphabet s)).
    destruct H13.
    apply sceEventMapAlphabet;auto.
    assert (~ In s (finishedscenarios conf1)).
    unfold not;intros.     
    apply syncFinish with (conf:=conf) (re:=e1) in H22;auto.
    unfold not in H3.
    assert (In s (finishedscenarios conf2')).
    SearchAbout   sceEventMap.
    apply  chainMergeFinMap';auto.
    exists (eventDefinition e2);auto.   
    assert (In s (dom (controlstate conf))).
    rewrite domControlSync with (conf':=conf2) (e:=e2);auto.
    rewrite domControlSync with (conf':=conf2') (e:=e1);auto.    
    destruct H15.
     unfold scenarioInclusion in inclusion;unfold incl in inclusion;apply inclusion;auto.
    
       apply H3 with (sce1:=s) (sce2:=s);auto.
       remember H4.
       clear Heqw.
       destruct H4.
      repeat match goal with
            | [ H: _ /\ _ |- _ ] => destruct H

            end.
      destruct H25.
   repeat match goal with
            | [ H: _ /\ _ |- _ ] => destruct H

            end.         
           
    apply syncFinishedMap with (conf:=conf1);auto.
    SearchAbout finishedscenarios.
    pose proof finishedInList'.
    pose proof syncFinishIn. 
    apply H42 with (conf:=conf1) (e:=e2);auto.          
    rewrite <- domControlSync with (conf:=conf) (e:=e1);auto.
    rewrite  domControlSync with (conf':=conf2) (e:=e2);auto.
    destruct H13. unfold scenarioInclusion in inclusion.
    unfold incl in inclusion.     
    apply inclusion.

    SearchAbout dom.
        
    apply Permutation_in with (l:=dom (sceEventMap conf2));auto.
       
    apply domIn with (x:=eventDefinition e2);auto.

    repeat(split;auto).
    assert (In e1 (raisedevents conf)).
    unfold synchrony in H7;intuition;auto.             
    SearchAbout raisedevents.
    apply  raisedPreservation with (conf:=conf) (conf1:=conf1) (conf2:=conf2) (e1:=e1);auto.

    SearchAbout sceEventMap.
    assert (e = eventDefinition e1).
    apply syncMapFinishEventDef' with (M:=M) (conf:=conf2) (conf':=conf2') (sce:=s);auto.
    unfold not;intros.
    apply H18.
    exists e;auto.     
    subst. 
    SearchAbout sceEventMap. 
    assert (In (eventDefinition e1) (alphabet s)).
    destruct H15.
    apply sceEventMapAlphabet;auto.
    assert (~ In (eventDefinition e2) (alphabet s)).
    unfold not;intros.

    assert (In s (finishedscenarios conf2')).
    apply  chainMergeFinMap';auto.
    exists (eventDefinition e1);auto.   
    assert (In s (dom (controlstate conf))).
    rewrite domControlSync with (conf':=conf2) (e:=e2);auto.
    rewrite domControlSync with (conf':=conf2') (e:=e1);auto.    
    destruct H15.
    unfold scenarioInclusion in inclusion;unfold incl in inclusion;apply inclusion;auto.

    
    unfold not in H3.
    apply H3 with (sce1:=s) (sce2:=s);auto.
    assert (In (s, eventDefinition e1) (sceEventMap conf1)).
    apply syncFinishedMap with (conf:=conf);auto.
    apply syncFinishIn with (conf:=conf) (e:=e1);auto.
    rewrite domControlSync with (conf':=conf2) (e:=e2);auto.
    rewrite domControlSync with (conf':=conf2') (e:=e1);auto.    
    destruct H15.
    unfold scenarioInclusion in inclusion.
    unfold incl in inclusion.
    apply inclusion.

        apply Permutation_in with (l:=dom (sceEventMap conf2'));auto.

        apply domIn with (x:=eventDefinition e1);auto.
        
    
    destruct H4;intuition;auto.
    destruct H4.
     repeat match goal with
            | [ H: _ /\ _ |- _ ] => destruct H

            end.    
     destruct H23.
    repeat(split;intuition;auto).      
    unfold synchrony in H7;intuition;auto.
    SearchAbout  sceEventMap.
    apply sceEventMapNoChangeSync with (conf:=conf1) (e:=e2);auto.
    destruct H12.

     apply Permutation_in with (l:=dom (sceEventMap conf1));auto.

        apply domIn with (x:=eventDefinition e1);auto.
        

Qed.

Lemma diamondFinMap2: forall M (conf conf1 conf2 conf1' conf2': configuration M)  e1 e2 , 
(forall v1 v2 , In v1 (dom (datastate conf)) -> In v2 (dom (datastate conf)) -> 
updateVarEv M (eventDefinition e1)  v1 -> updateVarEv M (eventDefinition e2) v2 -> v1 <> v2) -> 
(forall v1 v2 , In v1 (dom (datastate conf)) -> In v2 (dom (datastate conf)) -> 
updateVarEv M (eventDefinition e1)  v1 -> usedVarEv M (eventDefinition e2) v2 -> v1 <> v2) ->
(forall v1 v2 , In v1 (dom (datastate conf)) -> In v2 (dom (datastate conf)) -> 
updateVarEv M (eventDefinition e2)  v1 -> usedVarEv M (eventDefinition e1) v2 -> v1 <> v2)  ->
(forall ev1 ev2, In ev1 (events M) -> In ev2 (events M) -> raisedEv M (eventDefinition e1) ev1 -> 
            eventKind ev1 = Internal -> eventKind ev2 = Internal ->       raisedEv M (eventDefinition e2) ev2 -> ev1 <> ev2) ->
(forall sce1 sce2,  In sce1 (dom (controlstate conf)) -> In sce2 (dom (controlstate conf)) -> In (eventDefinition e1) (alphabet sce1) -> In (eventDefinition e2) (alphabet sce2) -> sce1 <> sce2) ->
WellFormed M ->
e1 <> e2 ->
correct_configuration conf -> synchrony conf conf1 e1 ->  synchrony conf conf2 e2 ->
synchrony conf1 conf1' e2 -> synchrony conf2 conf2' e1 ->
incl (sceEventMap conf1')
     (sceEventMap conf2').
Proof.
  intros.
  apply diamondFinMap1 with (conf:=conf) (conf1:=conf2) (conf2:=conf1) (e1:=e2) (e2:=e1);auto.
  intros.
  unfold not;intros.
  unfold not in H. apply H with (v1:=v2) (v2:=v1);auto.
  intros.
  unfold not in H2.   unfold not;intros. apply H2 with (ev1:=ev2) (ev2:=ev1);auto.
  intros.
  unfold not;intros. unfold not in H3. apply H3 with (sce1:=sce2) (sce2:=sce1);auto.
Qed.

Lemma domUniq: forall (A B:Type)(env: list (A*B)),
    uniqList (dom env) ->
    uniqList env. 
Proof. intros.

induction env;intros.
- constructor. 
- simpl in *. destruct a.  simpl in *.
  inversion H;subst.
  constructor;auto.
  unfold not;intros. apply domIn in H0. contradiction. 
Qed.


Lemma diamondFinMapAll:  forall M (conf conf1 conf2 conf1' conf2': configuration M)  e1 e2, 
(forall v1 v2 , In v1 (dom (datastate conf)) -> In v2 (dom (datastate conf)) -> 
updateVarEv M (eventDefinition e1)  v1 -> updateVarEv M (eventDefinition e2) v2 -> v1 <> v2) -> 
(forall v1 v2 , In v1 (dom (datastate conf)) -> In v2 (dom (datastate conf)) -> 
updateVarEv M (eventDefinition e1)  v1 -> usedVarEv M (eventDefinition e2) v2 -> v1 <> v2) ->
(forall v1 v2 , In v1 (dom (datastate conf)) -> In v2 (dom (datastate conf)) -> 
updateVarEv M (eventDefinition e2)  v1 -> usedVarEv M (eventDefinition e1) v2 -> v1 <> v2)  ->
(forall ev1 ev2, In ev1 (events M) -> In ev2 (events M) -> raisedEv M (eventDefinition e1) ev1 -> 
            eventKind ev1 = Internal -> eventKind ev2 = Internal ->       raisedEv M (eventDefinition e2) ev2 -> ev1 <> ev2) ->
(forall sce1 sce2, In sce1 (dom (controlstate conf)) -> In sce2 (dom (controlstate conf)) -> In (eventDefinition e1) (alphabet sce1) -> In (eventDefinition e2) (alphabet sce2) -> sce1 <> sce2) ->
WellFormed M ->
e1 <> e2 ->
correct_configuration conf -> synchrony conf conf1 e1 ->  synchrony conf conf2 e2 ->
synchrony conf1 conf1' e2 -> synchrony conf2 conf2' e1 ->
Permutation (sceEventMap conf2')
     (sceEventMap conf1')
.
Proof.
  intros.
  pose proof diamondFinMap1.
  assert (incl (sceEventMap conf2') (sceEventMap conf1')).
  apply H11 with (conf:=conf) (conf1:=conf1) (conf2:=conf2) (e1:=e1) (e2:=e2);auto.
  clear H11.
  pose proof diamondFinMap2.
  assert (incl (sceEventMap conf1') (sceEventMap conf2')).
  apply H11 with (conf:=conf) (conf1:=conf1) (conf2:=conf2) (e1:=e1) (e2:=e2);auto.
  clear H11.


  assert (correct_configuration conf1).

   destruct H4.

     repeat match goal with
            | [ H: _ /\ _ |- _ ] => destruct H

         end. 
    
     destruct H15.
              
              
     repeat match goal with
            | [ H: _ /\ _ |- _ ] => destruct H

            end.
     apply termL5 with (conf:=conf) (e:=e1);auto.
   
     destruct H6.
     apply raised_wellform';auto.
     unfold synchrony in H7;intuition;auto.

     
   assert (correct_configuration conf2).

   destruct H4.

     repeat match goal with
            | [ H: _ /\ _ |- _ ] => destruct H

         end. 
    
     destruct H16.
              
              
     repeat match goal with
            | [ H: _ /\ _ |- _ ] => destruct H

            end.
     apply termL5 with (conf:=conf) (e:=e2);auto.
   
     destruct H6.
     apply raised_wellform';auto.
     unfold synchrony in H8;intuition;auto.

   assert (correct_configuration conf1').

   destruct H4.

     repeat match goal with
            | [ H: _ /\ _ |- _ ] => destruct H

         end. 
    
     destruct H17.
              
              
     repeat match goal with
            | [ H: _ /\ _ |- _ ] => destruct H

            end.
     apply termL5 with (conf:=conf1) (e:=e2);auto.
   
     destruct H11.
     apply raised_wellform';auto.
     unfold synchrony in H9;intuition;auto.

       assert (correct_configuration conf2').

   destruct H4.

     repeat match goal with
            | [ H: _ /\ _ |- _ ] => destruct H

         end. 
    
     destruct H18.
              
              
     repeat match goal with
            | [ H: _ /\ _ |- _ ] => destruct H

            end.
     apply termL5 with (conf:=conf2) (e:=e1);auto.
   
     destruct H14.
     apply raised_wellform';auto.
     unfold synchrony in H10;intuition;auto.
  
  
  apply NoDup_Permutation_bis;auto.
  assert (uniqList (dom (sceEventMap (conf2')))). 
  destruct H16 .

    rewrite uniqListNoDupEq.
   rewrite uniqListNoDupEq in finish_uniq.
      apply Permutation_NoDup with (l':=dom (sceEventMap conf2')) in finish_uniq;auto.
      apply Permutation_sym;auto.

  SearchAbout  NoDup.   rewrite <- uniqListNoDupEq. 
  
Check domUniq. 
  apply domUniq in H17;auto. 
 
  
   apply uniqListNoDupEq;auto.

    assert (uniqList (dom (sceEventMap (conf1')))). 
  destruct H15 .

 rewrite uniqListNoDupEq.
   rewrite uniqListNoDupEq in finish_uniq.
      apply Permutation_NoDup with (l':=dom (sceEventMap conf1')) in finish_uniq;auto.
      apply Permutation_sym;auto.
      

  apply domUniq in H17;auto. 
 
 
   apply  NoDup_incl_length;auto.

   destruct H15 .

    rewrite <- uniqListNoDupEq.
   
   rewrite uniqListNoDupEq in finish_uniq.
      apply Permutation_NoDup with (l':=dom (sceEventMap conf1')) in finish_uniq;auto.
      rewrite <- uniqListNoDupEq in finish_uniq.
    
  apply domUniq in finish_uniq;auto. 
  apply Permutation_sym;auto. 
  
Qed.
     
Locate equivConf. Check equivConfSyncBasic. 
Print equivConf. SearchAbout Permutation. 


Lemma exportedInvariantCombine: forall M  v (conf conf' : configuration M)  re ,
 
 In re (exportedevents conf) ->
innerCombineFunc'''' conf v = Some conf' ->
 In re (exportedevents conf').
Proof. intros ? v. induction v.
- intros. simpl in H0. inversion H0.
-intros. simpl in H0. 
remember (innerCombineFunc'''' conf v ).
destruct o;inversion H0.
remember (mergeConfigFunc' conf a c ).
destruct e;inversion H0. subst.
unfold mergeConfigFunc' in Heqe.
destruct (mergeDataStateFunc (datastate conf) (datastate a) (datastate c) );inversion Heqe. 
destruct ( mergeControlStateFunc (controlstate conf) (controlstate a) (controlstate c));inversion H4.
destruct v. Focus 2. inversion H0;subst. simpl. rewrite in_app_iff. right.
apply IHv with (conf:=conf);auto.
remember (mergeConfigFunc' conf conf a ).
destruct e;inversion H0.
subst.
unfold mergeConfigFunc' in Heqe0. 
destruct (mergeDataStateFunc (datastate conf) (datastate conf) (datastate a) );inversion Heqe0. 
destruct ( mergeControlStateFunc (controlstate conf) (controlstate conf) (controlstate a));inversion H5.
simpl. rewrite in_app_iff. left;auto.
destruct v;inversion H3.

remember (mergeConfigFunc' conf conf a ).
destruct e;inversion H0.
subst.
unfold mergeConfigFunc' in Heqe0. 
destruct (mergeDataStateFunc (datastate conf) (datastate conf) (datastate a) );inversion Heqe0. 
destruct ( mergeControlStateFunc (controlstate conf) (controlstate conf) (controlstate a));inversion H5.
simpl. rewrite in_app_iff. left;auto.


remember (mergeConfigFunc' conf conf a ).
destruct e;inversion H0.
subst.
unfold mergeConfigFunc' in Heqe. 
destruct (mergeDataStateFunc (datastate conf) (datastate conf) (datastate a) );inversion Heqe. 
Focus 2. destruct v;inversion H0. destruct ( mergeControlStateFunc (controlstate conf) (controlstate conf) (controlstate a));inversion H4. destruct v;inversion H0. subst. 
simpl. rewrite in_app_iff. left;auto.

Qed.

Lemma exportedInvariantSync: forall e M (conf conf': configuration M) re,
synchrony conf conf' e -> 
In re (exportedevents conf)
-> In re (exportedevents conf').
Proof. intros. unfold synchrony in H.  
  repeat match goal with
            | [ H: _ /\ _ |- _ ] => destruct H

            end.
unfold combineFunc in H1.

remember (constructConfigList (dom (controlstate conf)) e conf).
destruct e0;inversion H1.
clear H3.
destruct v;inversion H1. 
remember (innerCombineFunc'''' conf (c :: v)). 
destruct o;inversion H1.
unfold removeEventFromConf.
simpl.
apply exportedInvariantCombine with (v:=c::v) (conf:=conf);auto. 


(*eapply finishedInvariantCombine. apply H. auto. apply H4. intros.
pose proof finishedInvariant. symmetry in Heqe0. unfold constructConfigList in Heqe0.
eapply H6. apply Heqe0. auto. auto. inversion H4. *)
Qed.

Lemma innerExported: forall M sceList (conf c: configuration M) l  e re ,
    uniqList sceList ->
    Result l = constructConfigList' sceList e conf ->
    Some c = innerCombineFunc'''' conf l ->
    ~ In re (exportedevents conf) ->
    In re (exportedevents c) ->
    (exists conf', In conf' l /\ In re (exportedevents conf')).
Proof.
  intros M sceList;induction sceList.
-  intros. simpl in H0. inversion H0;subst. simpl in H1. inversion H1. 
-
  intros.
  simpl in *.
  remember (constructConfig a e conf).
  destruct e0;inversion H0.
  clear H5.
  remember (constructConfigList' sceList e conf ).
  destruct e0;inversion H0.
  subst.
  clear H0.
  simpl in H1.
  destruct v0;inversion H1.
  clear H4.
  remember (mergeConfigFunc' conf conf v ).
  destruct e0;inversion H1.
  subst.
  clear H1.
  unfold  mergeConfigFunc' in Heqe2.
  destruct (mergeDataStateFunc (datastate conf) (datastate conf) (datastate v) );inversion Heqe2.
  destruct (mergeControlStateFunc (controlstate conf) (controlstate conf) (controlstate v));inversion Heqe2.
  subst.
  simpl in H3.
  rewrite in_app_iff in H3.
  destruct H3.
  contradiction.
  exists v;intuition;auto.   
  clear H4.
    
  remember (innerCombineFunc'''' conf (c0 :: v0) ).
  destruct o;inversion H1.
  clear H4.
  remember (mergeConfigFunc' conf v c1 ).
  destruct e0;inversion H1.
  subst.

   unfold  mergeConfigFunc' in Heqe2.
  destruct (mergeDataStateFunc (datastate conf) (datastate v) (datastate c1) );inversion Heqe2.
  destruct (mergeControlStateFunc (controlstate conf) (controlstate v) (controlstate c1));inversion Heqe2.
  subst.
  simpl in H3.
  rewrite in_app_iff in H3.

  destruct H3.

  exists v;intuition;auto.

  apply IHsceList with (e:=e) (re:=re) in Heqo;auto.
  destruct Heqo.
  exists x;intuition;auto. 
  inversion H;subst;auto.
Qed.



Print constructConfigList'.

Lemma calcuListEqual: forall exprs ds0 ds0'  v v',
    ( forall a : atom, filterStateUsedExprList exprs a -> getValue a ds0 = getValue a ds0') ->
    Result v = calculateExprList ds0 exprs ->
    Result v' = calculateExprList ds0' exprs ->
    v = v'. 
Proof.
  intro exprs;induction exprs.
-
  intros.   simpl in *. inversion H0;inversion H1;subst;auto.
-  intros.
   simpl in *.
   remember (evalMonad ds0 a).
   destruct e;inversion H0.
   clear H3.
   remember (evalMonad ds0' a).
   destruct e;inversion H1.
   assert (evalMonad ds0 a = evalMonad ds0' a).
   apply evalMonadEq;auto. 
   intros.
   apply H.
   rewrite H2;auto.
   rewrite H2 in Heqe.    
   rewrite <- Heqe0 in Heqe;inversion Heqe;subst.
   remember (calculateExprList ds0 exprs).
   destruct e;inversion H0.    
   subst.
   remember (calculateExprList ds0' exprs).
   destruct e;inversion H1.
   subst.
   f_equal.    apply IHexprs with (ds0:=ds0) (ds0':=ds0') (v:=v0);auto.
   intros.    apply H;auto. destruct (filterStateUsedExpr a a0 );auto.
Qed.

Lemma valueNoChange': forall env env' s s' v ,
    Some env' = updateValueEnvInv s v env ->
    s <> s' ->
    getValue s' env = getValue s' env'.
Proof. intro env;induction env. 
       -  intros. simpl in H. destruct s;inversion H. inversion H;subst. auto.
       - intros. destruct env'. simpl in H.
         destruct s;inversion H.    clear H2. destruct a;destruct p.
         destruct ( atom_eq_dec (AIdent s) a);inversion H.
         destruct (typeValMatch t v);inversion H.
         destruct (updateValueEnvInv (AIdent s) v env);inversion H. 
         destruct a;destruct p.
         simpl in H.
         destruct s;inversion H.          clear H2. destruct p0.
         destruct p.
         destruct (atom_eq_dec (AIdent s) a).
         destruct (typeValMatch t v ).
         inversion H;subst.
         simpl. destruct s';auto. destruct ( atom_eq_dec (AIdent s0) (AIdent s)).
         inversion e. exfalso;apply H0;auto. auto.
         inversion H.
         remember (updateValueEnvInv (AIdent s) v env).
         destruct o. inversion H;subst.
         simpl. 
         destruct s';auto.          destruct (atom_eq_dec (AIdent s0) a);auto.
         apply IHenv with (s:=(AIdent s)) (v:=v);auto.
         simpl.
         destruct s';auto.
         inversion H. 
Qed.


Lemma updateValueInv': forall v v' s v3,
    In s (dom v) ->
    Some v' = updateValueEnvInv s v3 v ->
    getValue s v' = Some v3.
Proof.
  intro v;induction v;intros.
  -  inversion H.
  -  simpl in H0.
     destruct s;inversion H0.      destruct a;destruct p.
     simpl in H.
     destruct H.
     +  subst. destruct (atom_eq_dec (AIdent s) (AIdent s)).
        destruct (typeValMatch t v3). inversion H0;subst.  simpl.
        destruct (atom_eq_dec (AIdent s) (AIdent s));auto.
        contradiction.    inversion H0.      contradiction.
     +  destruct (atom_eq_dec (AIdent s) a).
        destruct (typeValMatch t v3 ). inversion H0;subst. simpl;auto.
        destruct (atom_eq_dec (AIdent s) (AIdent s));auto. contradiction.
        inversion H0.
        remember (updateValueEnvInv (AIdent s) v3 v).
       destruct o;inversion H0.
       subst.  simpl.
       destruct (atom_eq_dec (AIdent s) a ).
       contradiction.     apply IHv;auto .    
Qed.


Lemma execActionAppEqual'': forall act eventList v v1  l1 l2 v' v'' l' l'' a,
    Result (v', l') = execAction (v, l1) act eventList ->
    Result (v'', l'') = execAction (v1, l2) act eventList ->
    getValue a v = getValue a v1 ->
     In a (dom v) ->
    (dom v = dom v1) ->
    (forall va, In va (dom v) -> filterStateUsedAct act va = true ->
                getValue va v = getValue va v1) ->
    getValue a v' = getValue a v''.
Proof.
  intro act;induction act.
  - intros. simpl in *.
     inversion H;inversion H0;subst.
     auto.

  - intros. 
     simpl in *. 
     destruct l;inversion H.   clear H6.  destruct a0;inversion H.
     clear H6.
     remember (evalMonad v e ).
     destruct e0;inversion H.
     clear H6.
     remember (evalMonad v1 e).
     destruct e0;inversion H0. clear H6. 
     remember (updateValueEnvInv (AIdent s) v0 (v)).
     destruct o;inversion H. subst. 
         
     remember ( updateValueEnvInv (AIdent s) v2 (v1)).
     destruct o;inversion H0.
     subst.
        assert  ( evalMonad (v) e = evalMonad (v1) e).
   apply evalMonadEq;auto. intros.  
   
    assert (In v5 (dom v) \/ ~ In v5 (dom v)).
   apply excluded_middle.
   destruct H6.
   assert (In v5 (dom v1)).
   rewrite <- H3;auto.
   apply H4;auto.  
   assert (~ In v5 (dom v1)).
   rewrite <- H3;auto. 
   rewrite getValueNone';auto.  rewrite getValueNone';auto. 
   Check valueNoChange.
   Locate valueNoChange.
      
    assert (a = (AIdent s) \/ a <> (AIdent s)).
   apply excluded_middle.
   destruct H6.
   subst.
   
   Focus 2.
   pose proof valueNoChange'. 
   apply H7 with (s':= a) in Heqo;auto.
  apply H7 with (s':= a) in Heqo0;auto. 
  rewrite <- Heqo.  rewrite <- Heqo0.  auto. Check updateValueInv.
  Locate updateValueInv.
  
   pose proof updateValueInv'.
   apply H6 in Heqo;auto. apply H6 in Heqo0;auto. rewrite H5 in Heqe0.   rewrite <- Heqe1 in Heqe0.  inversion Heqe0;subst. rewrite Heqo;rewrite Heqo0. auto.
   rewrite <- H3;auto.
  -  intros.  
  simpl in *.   
  remember (calculateExprList (v) exprs).
  destruct e;inversion H. clear H6.
  remember (calculateExprList (v1) exprs).
  destruct e;inversion H0.
  clear H6.
  remember (getEventByName ident eventList).
  destruct o;inversion H.
  clear H6.
  remember (parameterMatchFunc v0 (eventParams e)).
  destruct b;inversion H.
 subst. 
  remember (parameterMatchFunc v2 (eventParams e)).
  destruct b;inversion H0.
  subst.
  auto.
  - intros. 
 
  simpl in H;simpl in H0.
  remember (execAction (v, l1) act1 eventList).
  destruct e;inversion H.
  remember (execAction (v1, l2) act1 eventList).
  destruct e;inversion H0.
  clear H6.
  clear H7.
  destruct v0.
  destruct v2.
  
  assert ( getValue a v0 = getValue a v2).
  eapply IHact1 with (v:=v) (v1:=v1);auto. apply Heqe. apply Heqe0. 
    intros.
  apply H4;auto. simpl. rewrite H6;auto.
  eapply IHact2 with (v:=v0) (v1:=v2) (l1:=l) (l2:=l0);auto.
   apply H.
 apply H0. 
  
  pose proof execActionUniqList. 
  apply H6 in Heqe. rewrite <- Heqe. auto. 
  pose proof execActionUniqList.
  apply H6 in Heqe. apply H6 in Heqe0. rewrite <- Heqe;rewrite <- Heqe0.
  auto.   intros.

  apply IHact1 with (v:=v) (v1:=v1) (eventList:=eventList) (l1:=l1) (l2:=l2) (l':=l) (l'':=l0);auto.
  pose proof execActionUniqList.
  apply H8 in Heqe.
  rewrite Heqe in H4.  apply H4 in H6.  auto. simpl. rewrite H7;intuition;auto.
   
   pose proof execActionUniqList.
  apply H8 in Heqe.
  rewrite Heqe;auto.
  intros.
  apply H4;auto. simpl. rewrite H9;intuition;auto.

Qed.

Lemma execActionInEvent: forall act ds0  ds0' l l1 l1' ds1 ds1'   el ,
    Result (ds1,l1) = execAction (ds0, l) act el ->
    Result (ds1',l1') = execAction (ds0', l) act el ->
   
    ( forall v : atom,
       filterStateUsedAct act v-> 
       getValue v ds0 = getValue v ds0') ->
    dom ds0 = dom ds0' ->
   l1 = l1'. 
Proof.
  intro act;induction act.
- intros. 
  simpl in *.     
  inversion H;inversion H0;subst.    auto.
-  intros.
   rename H2 into dome.    simpl in *. 
   destruct l.    destruct a;inversion H.
   
   remember (evalMonad ds0 e).
      clear H3.
      destruct e0;inversion H.
      clear H3.
      remember (updateValueEnvInv (AIdent s) v ds0).
      destruct o;inversion H.
      subst.
      destruct (evalMonad ds0' e );inversion H0.
      destruct (updateValueEnvInv (AIdent s) v1 ds0');inversion H0.
      subst.
      auto.
-      
  intros.  rename H2 into dome.
  simpl in *.
  remember ( calculateExprList ds0 exprs ).
  destruct e;inversion H.
  clear H3.
  remember (calculateExprList ds0' exprs ).
  destruct e;inversion H0.
  clear H3.
  pose proof calcuListEqual.
  assert (v = v0).
  apply H2 with (exprs:=exprs) (ds0:=ds0) (ds0':=ds0');auto.
  subst.   
  remember (getEventByName ident el).
  destruct o;inversion H;subst.
  clear H4.
  remember (parameterMatchFunc v0 (eventParams e)).
  destruct b;inversion H.
  subst.
  inversion H0;subst.
  auto.  
- intros.  rename H2 into dome.
  simpl in *.
  remember (execAction (ds0, l) act1 el).
  destruct e;inversion H.
  clear H3.
  remember (execAction (ds0', l) act1 el).
  destruct e;inversion H0.
  clear H3.

  destruct v;destruct v0.
  assert (l0 = l2).
  eapply IHact1 . apply Heqe. apply Heqe0.
  intros.
  apply H1;auto.
  rewrite H2;intuition;auto.
  auto.   subst.   
  eapply IHact2 with (ds0:=v)  (ds0':=v0) ;auto.

  apply  H. 
  apply H0. 
  intros.   assert ((filterStateUsedAct act1 v1 || filterStateUsedAct act2 v1)%bool ).
  rewrite H2;intuition;auto.
  apply H1 in H3.

  Focus 2. 

  SearchAbout execAction.
  assert (dom ds0' = dom v0). 
  eapply typeActionNoChange;auto.
  apply Heqe0.
  assert (dom ds0 = dom v).
   eapply typeActionNoChange;auto.
   apply Heqe.
   rewrite <- H2;rewrite <- H3;auto.
  assert (dom ds0 = dom v).
   eapply typeActionNoChange;auto.
   apply Heqe.
   assert (dom ds0' = dom v0). 
  eapply typeActionNoChange;auto.
  apply Heqe0.
  assert (In v1 (dom v) \/ ~ In v1 (dom v)).
  apply excluded_middle.
  destruct H6.
  
  
   
  eapply execActionAppEqual'' with (act:=act1) (v:=ds0) (v1:=ds0');auto.
     apply Heqe.  apply Heqe0.  
  rewrite H4;auto. 
  intros.
  apply H1.   rewrite H8;intuition;auto.
  assert (~ In v1 (dom v0)).
  unfold not;intros.
  rewrite dome in H4.   
  rewrite H4 in H5.   rewrite H5 in H6. contradiction.
  SearchAbout getValue.
  rewrite getValueNone';auto.  rewrite getValueNone';auto.
Qed.


Lemma constructConfigExportedIn: forall M (conf conf1 conf' conf'': configuration M) sce e1 e2 e,
    correct_configuration conf ->
    synchrony conf conf1 e1 ->
    e1 <> e2 ->
    stateEvDefInstanceMapEquiv M ->
    correctStateEvStepMap' M ->
    stepExistsMon' M sce ->
    (forall v,  In v (dom (datastate conf)) ->  usedVarEv M (eventDefinition e2) v -> getValue v (datastate conf) = getValue v (datastate conf1)) ->
    In sce (scenarios M) ->
    In (eventDefinition e2) (alphabet sce) ->
    getScenarioState sce (controlstate conf) = getScenarioState sce (controlstate conf1) ->
    Result conf' = constructConfig sce e2 conf ->
    Result conf'' = constructConfig sce e2 conf1 ->
    In e2 (raisedevents conf) ->
    typeCheck M ->
    transEvMapEventInstanceProp M ->
    transEvMapProp M ->
    stpStMapEquiv' M ->
    stateEvDefInstanceMapEquivEListProp M ->
    stateSceIn M ->
    In e (exportedevents conf') ->
    In e (exportedevents conf''). 
Proof.

  intros. rename H13 into transInProp.
  rename H14 into transProp.
  rename H15 into stpEquiv.
  rename H16 into stateMapEquivProp.
  rename H17 into stateIn.
  unfold constructConfig in *.
  rewrite <- H8 in H10.
  remember (getScenarioState sce (controlstate conf) ).
  destruct o;inversion H10.
  clear H14.
  remember (transEvMapFunc (stateEvDefInstanceMap M) (Some s, Some (eventDefinition e2)) ).
  destruct o;inversion H10.
  clear H14.
  assert (findEventInstance e2 (datastate conf) l = findEventInstance e2 (datastate conf1) l).
  
  apply findEventValueEq;auto.
  intros.

  assert (In v (dom (datastate conf)) \/ ~ In v (dom (datastate conf))). 
  apply excluded_middle.
  destruct H15.
    
  apply H5;auto.   unfold usedVarEv.
  exists sce. split.
  Focus 2.
   
  apply basic_ts;auto.
  rename H15 into vdd.
  
  unfold correctStateEvStepMap' in H3.
  unfold stepExistsMon' in H4.
  unfold stateEvDefInstanceMapEquiv in H2. 
  assert (exists stp : step, In (s, ei, sce, Some stp) (stateEvStepMap' M)).
  apply H4  with (e:=(eventDefinition e2)) (l:=l);auto.

  rewrite semantic_rules.stateEvDefInstanceMapEquiv'. symmetry;auto. 
  destruct H2;auto.
  destruct H15.   
  apply H3 in H15.
  destruct H15.
  destruct H16.
  apply scenarioUsedVarIn with (stp:=x);auto.
  subst;auto.   

  assert (dom (datastate conf) = dom (datastate conf1)).
   assert (dom2 (datastate conf) = dom2 (datastate conf1)).
  apply syncDSDom2 with (e:=e1) ;auto.
  rewrite <- dom2dom'. 
  rewrite <- dom2dom'.    rewrite H16;auto.
  SearchAbout getValue.
  rewrite getValueNone'. rewrite getValueNone'. auto. rewrite <- H16;auto. auto. 

  assert (dom2 (datastate conf) = dom2 (datastate conf1)).
  apply syncDSDom2 with (e:=e1) ;auto.
  rewrite <- dom2dom'. 
  rewrite <- dom2dom'.    rewrite H13;auto. 
  intros.
  apply tyEnvVar with (env:=datastate conf);auto.  
  destruct H;auto.
  rewrite <- H13 in H10.
  remember (findEventInstance e2 (datastate conf) l).
  destruct o;inversion H9.
  clear H15.
  remember (createValueEnv (eventArgs e0) (eventParams (eventDefinition e2)) (eventArguments e2)).
  destruct e3;inversion H9.
  clear H15.
  assert (getStep' conf sce e0 = getStep' conf1 sce e0).
  unfold getStep'.
  rewrite <- Heqo.
  rewrite <- H8.
  auto.
  rewrite <- H14 in H10.
  remember (getStep' conf sce e0).
  destruct o;inversion H9.
  clear H16.
  remember (configTransition (extendValEnv (datastate conf) v) e2 e0 sce s0 conf).
  destruct e3;inversion H9.
  subst.
  remember (configTransition (extendValEnv (datastate conf1) v) e2 e0 sce s0 conf1).
  destruct e3;inversion H9.
  subst.
  unfold configTransition in Heqe0,Heqe1.
  remember (execAction (extendValEnv (datastate conf) v, []) (stepActions s0)
              (filter
                 (fun e : event_definition =>
                  match eventKind e with
                  | Internal => true
                  | Imported => false
                  | Exported => true
                  end) (events M))).
  destruct e3;inversion Heqe0.
  clear H16.
  destruct v2.
  remember ( execAction (extendValEnv (datastate conf1) v, []) (stepActions s0)
              (filter
                 (fun e : event_definition =>
                  match eventKind e with
                  | Internal => true
                  | Imported => false
                  | Exported => true
                  end) (events M))).
  destruct e3;inversion Heqe1.
  clear H16.
  destruct v3.
  inversion Heqe0;subst;simpl.
  inversion Heqe1;subst;simpl. simpl in H18. inversion H10;subst. simpl.
  clear H10;clear Heqe1. clear H9;clear Heqe0.
  apply filter_In in H18.
  destruct H18.
  apply filter_In;auto.
  split;auto.   
  Focus 2. inversion H10.
  
  unfold extendValEnv in Heqe2, Heqe4.
 
  (*getValueIn'*)
  SearchAbout execAction. 
  assert ( dom (datastate conf ++ v) = dom v2 ).
  eapply execActionUniqList. 
  apply Heqe2.
  assert ( dom (datastate conf1 ++ v) = dom v3).
  eapply execActionUniqList.   apply Heqe4.

  Print execAction.
  
  SearchAbout execAction.
  
  assert (  exists (act : action) (exprs : list expr),
    In act (transitionIntoBasicActionList (stepActions s0)) /\
    act = RaiseStmt (eventId (eventDefinition e)) exprs).

  eapply execActionRaisingEvent ;auto.
  apply Heqe2.
  unfold not;intros.
  inversion H17.
  auto.

  pose proof execActionInEvent.
  assert (l0 = l1).
  apply H18 with (act:=stepActions s0) (ds0:=datastate conf ++ v) (ds0':=datastate conf1 ++ v) (l:=[]) (ds1:=v2) (ds1':=v3) (el:=(filter
               (fun e : event_definition =>
                match eventKind e with
                | Internal => true
                | Imported => false
                | Exported => true
                end) (events M)));auto.
  Focus 2.   
  rewrite domApp. 
  rewrite domApp.
  
  destruct H.
  rewrite <- dom2dom'.   
  rewrite   ds_dom_eq .
  assert (correct_configuration conf1).
  Check termL5.
  apply termL5 with (conf:=conf) (e:=e1);auto.
 repeat(split;auto).   
 apply raised_wellform'.
 unfold synchrony in H0;intuition;auto.
 destruct H. 
    rewrite <- dom2dom'. rewrite <- dom2dom'.   
      rewrite   ds_dom_eq0;auto .
      Focus 2.   subst;auto.
      intros.
      SearchAbout filterStateUsedAct.
      assert (In v0 (dom (datastate conf)) \/ ~ In v0 (dom (datastate conf))).
      apply  excluded_middle.
      destruct H20.
      Focus 2.
      SearchAbout getValue.
  rewrite getValueNotInNoUniq'.       
  rewrite getValueNotInNoUniq'.
  auto.
  unfold not;intros.
  destruct H.
   rewrite <- dom2dom' in H20.   
   rewrite  ds_dom_eq in H20;auto .

    assert (correct_configuration conf1).
  Check termL5.
  apply termL5 with (conf:=conf) (e:=e1);auto.
 repeat(split;auto).   
 apply raised_wellform'.
 unfold synchrony in H0;intuition;auto.
 destruct H.
   rewrite <- dom2dom' in H21.  rewrite   ds_dom_eq0 in H21;auto .
  auto.  

  assert (In v0 (dom (datastate conf1))).
 destruct H.
   rewrite <- dom2dom' in H20.       rewrite <- dom2dom'.     
rewrite  ds_dom_eq in H20;auto .

 assert (correct_configuration conf1).
  Check termL5.
  apply termL5 with (conf:=conf) (e:=e1);auto.
 repeat(split;auto).   
 apply raised_wellform'.
 unfold synchrony in H0;intuition;auto.

 destruct H.
    rewrite   ds_dom_eq0 ;auto .

    
    rewrite   getValueInNoUniq';auto. 
      rewrite getValueInNoUniq';auto. 
      apply H5;auto.
      unfold  usedVarEv.
      exists sce.
      split;auto.
      Focus 2.
      Print triggerSce.
      apply  basic_ts;auto.
      SearchAbout  scenarioUsedVar.
      apply  scenarioUsedVarIn' with (stp:=s0);auto.
  SearchAbout traces.      
  unfold  correctStateEvStepMap' in H3.
  unfold stateEvDefInstanceMapEquiv in H2.
  destruct H2.
  Print stpStMap'.
  SearchAbout stateEvStepMap'.
  assert (Some s0 = stpStpMapFunc (stateEvStepMap' M) (s, e0, sce)).
  apply getStepMap' with (conf:=conf);auto.
  SearchAbout  stpStpMapFunc. symmetry in H23. 
  rewrite  <- stpStMapEquivLem in H23.
  Focus 2.   unfold stpStMapEquiv' in *;auto. 
   assert ( In s0 (traces sce) /\ stepEvent s0 = e0 /\ pre_state s0 = s).
   apply H3;auto.
  destruct H24;auto.    
Qed.



Lemma constructConfigExportedIn': forall M (conf conf1 conf' conf'': configuration M) sce e1 e2 e,
    correct_configuration conf ->
    synchrony conf conf1 e1 ->
    e1 <> e2 ->
    stateEvDefInstanceMapEquiv M ->
    correctStateEvStepMap' M ->
    stepExistsMon' M sce ->
    (forall v,  In v (dom (datastate conf)) -> usedVarEv M (eventDefinition e2) v -> getValue v (datastate conf) = getValue v (datastate conf1)) ->
    In sce (scenarios M) ->
    In (eventDefinition e2) (alphabet sce) ->
    getScenarioState sce (controlstate conf) = getScenarioState sce (controlstate conf1) ->
    Result conf' = constructConfig sce e2 conf ->
    Result conf'' = constructConfig sce e2 conf1 ->
    In e2 (raisedevents conf) ->
    typeCheck M ->
    transEvMapEventInstanceProp M ->
    transEvMapProp M ->
    stpStMapEquiv' M ->
    stateEvDefInstanceMapEquivEListProp M ->
    stateSceIn M ->
    In e (exportedevents conf'') ->
    In e (exportedevents conf'). 
Proof.

  intros. rename H13 into transInProp.
  rename H14 into transProp.
  rename H15 into stpEquiv.
  rename H16 into stateMapEquivProp.
  rename H17 into stateIn.
  unfold constructConfig in *.
  rewrite <- H8 in H10.
  remember (getScenarioState sce (controlstate conf) ).
  destruct o;inversion H10.
  clear H14.
  remember (transEvMapFunc (stateEvDefInstanceMap M) (Some s, Some (eventDefinition e2)) ).
  destruct o;inversion H10.
  clear H14.
  assert (findEventInstance e2 (datastate conf) l = findEventInstance e2 (datastate conf1) l).

   apply findEventValueEq;auto.
  intros.

  assert (In v (dom (datastate conf)) \/ ~ In v (dom (datastate conf))). 
  apply excluded_middle.
  destruct H15.
    
  apply H5;auto.   unfold usedVarEv.
  exists sce. split.
  Focus 2.
   
  apply basic_ts;auto.
  rename H15 into vdd.
  
  unfold correctStateEvStepMap' in H3.
  unfold stepExistsMon' in H4.
  unfold stateEvDefInstanceMapEquiv in H2. 
  assert (exists stp : step, In (s, ei, sce, Some stp) (stateEvStepMap' M)).
  apply H4  with (e:=(eventDefinition e2)) (l:=l);auto.

  rewrite semantic_rules.stateEvDefInstanceMapEquiv'. symmetry;auto. 
  destruct H2;auto.
  destruct H15.   
  apply H3 in H15.
  destruct H15.
  destruct H16.
  apply scenarioUsedVarIn with (stp:=x);auto.
  subst;auto.   

  assert (dom (datastate conf) = dom (datastate conf1)).
   assert (dom2 (datastate conf) = dom2 (datastate conf1)).
  apply syncDSDom2 with (e:=e1) ;auto.
  rewrite <- dom2dom'. 
  rewrite <- dom2dom'.    rewrite H16;auto.
  SearchAbout getValue.
  rewrite getValueNone'. rewrite getValueNone'. auto. rewrite <- H16;auto. auto.
  
  assert (dom2 (datastate conf) = dom2 (datastate conf1)).
  apply syncDSDom2 with (e:=e1) ;auto.
  rewrite <- dom2dom'. 
  rewrite <- dom2dom'.    rewrite H13;auto. 
  intros.
  apply tyEnvVar with (env:=datastate conf);auto.  
  destruct H;auto.
  rewrite <- H13 in H10.
  remember (findEventInstance e2 (datastate conf) l).
  destruct o;inversion H9.
  clear H15.
  remember (createValueEnv (eventArgs e0) (eventParams (eventDefinition e2)) (eventArguments e2)).
  destruct e3;inversion H9.
  clear H15.
  assert (getStep' conf sce e0 = getStep' conf1 sce e0).
  unfold getStep'.
  rewrite <- Heqo.
  rewrite <- H8.
  auto.
  rewrite <- H14 in H10.
  remember (getStep' conf sce e0).
  destruct o;inversion H9.
  clear H16.
  remember (configTransition (extendValEnv (datastate conf) v) e2 e0 sce s0 conf).
  destruct e3;inversion H9.
  subst.
  remember (configTransition (extendValEnv (datastate conf1) v) e2 e0 sce s0 conf1).
  destruct e3;inversion H9.
  subst.
  unfold configTransition in Heqe0,Heqe1.
  remember (execAction (extendValEnv (datastate conf) v, []) (stepActions s0)
              (filter
                 (fun e : event_definition =>
                  match eventKind e with
                  | Internal => true
                  | Imported => false
                  | Exported => true
                  end) (events M))).
  destruct e3;inversion Heqe0.
  clear H16.
  destruct v2.
  remember ( execAction (extendValEnv (datastate conf1) v, []) (stepActions s0)
              (filter
                 (fun e : event_definition =>
                  match eventKind e with
                  | Internal => true
                  | Imported => false
                  | Exported => true
                  end) (events M))).
  destruct e3;inversion Heqe1.
  clear H16.
  destruct v3.
  inversion Heqe0;subst;simpl.
  inversion Heqe1;subst;simpl. inversion H10;subst.  simpl in H18. 
  clear H10;clear Heqe1. clear H9;clear Heqe0.
  apply filter_In in H18.
  destruct H18.
  apply filter_In;auto.
  split;auto.   
  Focus 2. inversion H10.
  
  unfold extendValEnv in Heqe2, Heqe4.
 
  (*getValueIn'*)
  SearchAbout execAction. 
  assert ( dom (datastate conf ++ v) = dom v2 ).
  eapply execActionUniqList. 
  apply Heqe2.
  assert ( dom (datastate conf1 ++ v) = dom v3).
  eapply execActionUniqList.   apply Heqe4.

  
  assert (  exists (act : action) (exprs : list expr),
    In act (transitionIntoBasicActionList (stepActions s0)) /\
    act = RaiseStmt (eventId (eventDefinition e)) exprs).
  Check execActionRaisingEvent.
    
  eapply execActionRaisingEvent ;auto.
  apply Heqe4.
  unfold not;intros.
  inversion H17.
  auto.

  pose proof execActionInEvent.
  assert (l0 = l1).
  apply H18 with (act:=stepActions s0) (ds0:=datastate conf ++ v) (ds0':=datastate conf1 ++ v) (l:=[]) (ds1:=v2) (ds1':=v3) (el:=(filter
               (fun e : event_definition =>
                match eventKind e with
                | Internal => true
                | Imported => false
                | Exported => true
                end) (events M)));auto.
  Focus 2.   
  rewrite domApp. 
  rewrite domApp.
  
  destruct H.
  rewrite <- dom2dom'.   
  rewrite   ds_dom_eq .
  assert (correct_configuration conf1).
 
  apply termL5 with (conf:=conf) (e:=e1);auto.
 repeat(split;auto).   
 apply raised_wellform'.
 unfold synchrony in H0;intuition;auto.
 destruct H. 
    rewrite <- dom2dom'. rewrite <- dom2dom'.   
      rewrite   ds_dom_eq0;auto .
      Focus 2.   subst;auto.
      intros.
      assert (In v0 (dom (datastate conf)) \/ ~ In v0 (dom (datastate conf))).
      apply  excluded_middle.
      destruct H20.
      Focus 2.
 
  rewrite getValueNotInNoUniq'.       
  rewrite getValueNotInNoUniq'.
  auto.
  unfold not;intros.
  destruct H.
   rewrite <- dom2dom' in H20.   
   rewrite  ds_dom_eq in H20;auto .

    assert (correct_configuration conf1).

  apply termL5 with (conf:=conf) (e:=e1);auto.
 repeat(split;auto).   
 apply raised_wellform'.
 unfold synchrony in H0;intuition;auto.
 destruct H.
   rewrite <- dom2dom' in H21.  rewrite   ds_dom_eq0 in H21;auto .
  auto.  

  assert (In v0 (dom (datastate conf1))).
 destruct H.
   rewrite <- dom2dom' in H20.       rewrite <- dom2dom'.     
rewrite  ds_dom_eq in H20;auto .

 assert (correct_configuration conf1).
  apply termL5 with (conf:=conf) (e:=e1);auto.
 repeat(split;auto).   
 apply raised_wellform'.
 unfold synchrony in H0;intuition;auto.

 destruct H.
    rewrite   ds_dom_eq0 ;auto .
    rewrite   getValueInNoUniq';auto. 
      rewrite getValueInNoUniq';auto. 
      apply H5;auto.
      unfold  usedVarEv.
      exists sce.
      split;auto.
      Focus 2.
      apply  basic_ts;auto.
      apply  scenarioUsedVarIn' with (stp:=s0);auto.
  unfold  correctStateEvStepMap' in H3.
  unfold stateEvDefInstanceMapEquiv in H2.
  destruct H2.

  assert (Some s0 = stpStpMapFunc (stateEvStepMap' M) (s, e0, sce)).
  apply getStepMap' with (conf:=conf);auto.
  symmetry in H23. 
  rewrite  <- stpStMapEquivLem in H23.
  Focus 2.   unfold stpStMapEquiv' in *;auto. 
   assert ( In s0 (traces sce) /\ stepEvent s0 = e0 /\ pre_state s0 = s).
   apply H3;auto.
  destruct H24;auto.    
Qed.

Lemma innerExported': forall M sceList (conf c: configuration M) l  e re ,
    uniqList sceList ->
    Result l = constructConfigList' sceList e conf ->
    Some c = innerCombineFunc'''' conf l ->
    (exists conf', In conf' l /\ In re (exportedevents conf')) ->
    In re (exportedevents c)
    .
Proof.
  intros M sceList;induction sceList.
-  intros. simpl in H0. inversion H0;subst. simpl in H1. inversion H1. 
-
  intros.
  simpl in *.
  remember (constructConfig a e conf).
  destruct e0;inversion H0.
  clear H4.
  remember (constructConfigList' sceList e conf ).
  destruct e0;inversion H0.
  subst.
  clear H0.
  simpl in H1.
  destruct v0;inversion H1.
  clear H3.
  remember (mergeConfigFunc' conf conf v ).
  destruct e0;inversion H1.
  subst.
  clear H1.
  unfold  mergeConfigFunc' in Heqe2.
  destruct (mergeDataStateFunc (datastate conf) (datastate conf) (datastate v) );inversion Heqe2.
  destruct (mergeControlStateFunc (controlstate conf) (controlstate conf) (controlstate v));inversion Heqe2.
  subst. simpl. 
   
  rewrite in_app_iff. destruct H2. destruct H0. destruct H0;subst.
  right;auto.   inversion H0.
  
 
  clear H3.
    
  remember (innerCombineFunc'''' conf (c0 :: v0) ).
  destruct o;inversion H1.
  clear H3.
  remember (mergeConfigFunc' conf v c1 ).
  destruct e0;inversion H1.
  subst.

   unfold  mergeConfigFunc' in Heqe2.
  destruct (mergeDataStateFunc (datastate conf) (datastate v) (datastate c1) );inversion Heqe2.
  destruct (mergeControlStateFunc (controlstate conf) (controlstate v) (controlstate c1));inversion Heqe2.
  subst.
  simpl.  
  rewrite in_app_iff.
  clear Heqe2. clear H1. clear H3.
  destruct H2.
  destruct H0.
  destruct H0.
  subst. left;auto.
    

  apply IHsceList with (e:=e) (re:=re) in Heqo;auto.
  inversion H;subst;auto.   
  exists x;intuition;auto. 
 
Qed.


Lemma innerRaised': forall M sceList (conf c: configuration M) l  e re ,
    uniqList sceList ->
    Result l = constructConfigList' sceList e conf ->
    Some c = innerCombineFunc'''' conf l ->
    (exists conf', In conf' l /\ In re (raisedevents conf')) ->
    In re (raisedevents c)
    .
Proof.
  intros M sceList;induction sceList.
-  intros. simpl in H0. inversion H0;subst. simpl in H1. inversion H1. 
-
  intros.
  simpl in *.
  remember (constructConfig a e conf).
  destruct e0;inversion H0.
  clear H4.
  remember (constructConfigList' sceList e conf ).
  destruct e0;inversion H0.
  subst.
  clear H0.
  simpl in H1.
  destruct v0;inversion H1.
  clear H3.
  remember (mergeConfigFunc' conf conf v ).
  destruct e0;inversion H1.
  subst.
  clear H1.
  unfold  mergeConfigFunc' in Heqe2.
  destruct (mergeDataStateFunc (datastate conf) (datastate conf) (datastate v) );inversion Heqe2.
  destruct (mergeControlStateFunc (controlstate conf) (controlstate conf) (controlstate v));inversion Heqe2.
  subst. simpl. 
   
  rewrite in_app_iff. destruct H2. destruct H0. destruct H0;subst.
  right;auto.   inversion H0.
  
 
  clear H3.
    
  remember (innerCombineFunc'''' conf (c0 :: v0) ).
  destruct o;inversion H1.
  clear H3.
  remember (mergeConfigFunc' conf v c1 ).
  destruct e0;inversion H1.
  subst.

   unfold  mergeConfigFunc' in Heqe2.
  destruct (mergeDataStateFunc (datastate conf) (datastate v) (datastate c1) );inversion Heqe2.
  destruct (mergeControlStateFunc (controlstate conf) (controlstate v) (controlstate c1));inversion Heqe2.
  subst.
  simpl.  
  rewrite in_app_iff.
  clear Heqe2. clear H1. clear H3.
  destruct H2.
  destruct H0.
  destruct H0.
  subst. left;auto.
    

  apply IHsceList with (e:=e) (re:=re) in Heqo;auto.
  inversion H;subst;auto.   
  exists x;intuition;auto. 
 
Qed.

    
    
Lemma diamondExportedAll1:  forall M (conf conf1 conf2 conf1' conf2': configuration M)  e1 e2, 
(forall v1 v2 , In v1 (dom (datastate conf)) -> In v2 (dom (datastate conf)) ->
updateVarEv M (eventDefinition e1)  v1 -> updateVarEv M (eventDefinition e2) v2 -> v1 <> v2) -> 
(forall v1 v2 ,  In v1 (dom (datastate conf)) -> In v2 (dom (datastate conf)) ->
updateVarEv M (eventDefinition e1)  v1 -> usedVarEv M (eventDefinition e2) v2 -> v1 <> v2) ->
(forall v1 v2 ,  In v1 (dom (datastate conf)) -> In v2 (dom (datastate conf)) ->
updateVarEv M (eventDefinition e2)  v1 -> usedVarEv M (eventDefinition e1) v2 -> v1 <> v2)  ->
(forall ev1 ev2, In ev1 (events M) -> In ev2 (events M) -> raisedEv M (eventDefinition e1) ev1 -> 
              eventKind ev1 = Internal -> eventKind ev2 = Internal ->     raisedEv M (eventDefinition e2) ev2 -> ev1 <> ev2) ->
(forall sce1 sce2,  In sce1 (dom (controlstate conf)) -> In sce2 (dom (controlstate conf)) -> In (eventDefinition e1) (alphabet sce1) -> In (eventDefinition e2) (alphabet sce2) -> sce1 <> sce2) ->
WellFormed M ->
e1 <> e2 ->
correct_configuration conf -> synchrony conf conf1 e1 ->  synchrony conf conf2 e2 ->
synchrony conf1 conf1' e2 -> synchrony conf2 conf2' e1 ->
incl (exportedevents conf2')
     (exportedevents conf1')
.
Proof.
  intros.

  assert (correct_configuration conf1).

   destruct H4.

     repeat match goal with
            | [ H: _ /\ _ |- _ ] => destruct H

         end. 
    
     destruct H13.
              
              
     repeat match goal with
            | [ H: _ /\ _ |- _ ] => destruct H

            end.
     apply termL5 with (conf:=conf) (e:=e1);auto.
   
     destruct H6.
     apply raised_wellform';auto.
     unfold synchrony in H7;intuition;auto.

     
   assert (correct_configuration conf2).

   destruct H4.

     repeat match goal with
            | [ H: _ /\ _ |- _ ] => destruct H

         end. 
    
     destruct H14.
              
              
     repeat match goal with
            | [ H: _ /\ _ |- _ ] => destruct H

            end.
     apply termL5 with (conf:=conf) (e:=e2);auto.
   
     destruct H6.
     apply raised_wellform';auto.
     unfold synchrony in H8;intuition;auto.

   assert (correct_configuration conf1').

   destruct H4.

     repeat match goal with
            | [ H: _ /\ _ |- _ ] => destruct H

         end. 
    
     destruct H15.
              
              
     repeat match goal with
            | [ H: _ /\ _ |- _ ] => destruct H

            end.
     apply termL5 with (conf:=conf1) (e:=e2);auto.
   
     destruct H11.
     apply raised_wellform';auto.
     unfold synchrony in H9;intuition;auto.

       assert (correct_configuration conf2').

   destruct H4.

     repeat match goal with
            | [ H: _ /\ _ |- _ ] => destruct H

         end. 
    
     destruct H16.
              
              
     repeat match goal with
            | [ H: _ /\ _ |- _ ] => destruct H

            end.
     apply termL5 with (conf:=conf2) (e:=e1);auto.
   
     destruct H12.
     apply raised_wellform';auto.
     unfold synchrony in H10;intuition;auto.
  
  unfold incl;intros.
  assert (In a (exportedevents conf) \/ ~ In a (exportedevents conf)).
  apply excluded_middle.
  destruct H16.
  assert (In a (exportedevents conf1)).
  apply exportedInvariantSync with (e:=e1) (conf:=conf);auto.
   apply exportedInvariantSync with (e:=e2) (conf:=conf1);auto.   
  
  assert (In a (exportedevents conf1) \/ ~ In a (exportedevents conf1)).    
  apply excluded_middle.
  destruct H17.
  apply exportedInvariantSync with (e:=e2) (conf:=conf1);auto.
    
   assert (In a (exportedevents conf2) \/ ~ In a (exportedevents conf2)).
   apply excluded_middle.
   destruct H18.

   remember H8.
   clear Heqs.
   remember H9.
   clear Heqs0.

   unfold synchrony in s;unfold synchrony in s0.
   destruct s;destruct s0.

   unfold combineFunc in H20;unfold combineFunc in H22.
   remember (constructConfigList (dom (controlstate conf)) e2 conf).
   destruct e;inversion H20.
   clear H24.
   remember (constructConfigList (dom (controlstate conf1)) e2 conf1).
   destruct e;inversion H22.
   clear H24.

   unfold constructConfigList in *.
   destruct v;inversion H20.
   clear H24.
   remember ( innerCombineFunc'''' conf (c :: v)).
   destruct o;inversion H20.
   clear H20.
   destruct v0;inversion H22.
   clear H23.
   remember (innerCombineFunc'''' conf1 (c1 :: v0) ).
   destruct o;inversion H22.
   clear H22.
   simpl.
   rewrite <- H24 in H18;simpl in H18.  

   pose proof innerExported.

   assert ( exists conf' : configuration M, In conf' (c :: v) /\ In a (exportedevents conf')).
   apply H20 with (sceList:=(filter
              (fun x : scenario => inList event_definition_dec (eventDefinition e2) (alphabet x))
              (filterList (finishedscenarios conf) (dom (controlstate conf)) scenario_dec))) (conf:=conf) (c:=c0) (e:=e2) ;auto.
   SearchAbout filter.
   apply filterUniq;auto.
   apply uniqListFilter;destruct H6;intuition;auto.
   destruct H22.
   destruct H22.
   Check termL2.
   assert (exists sce : scenario, In sce (filter
              (fun x : scenario => inList event_definition_dec (eventDefinition e2) (alphabet x))
              (filterList (finishedscenarios conf) (dom (controlstate conf)) scenario_dec)) /\ Result x = constructConfig sce e2 conf).
   apply termL2 with (conf:=conf) (e:=e2) (lst:=c::v) ;auto.
   destruct H26.
   destruct H26.



   assert (dom (controlstate conf) = dom (controlstate conf1)).
  apply domControlSync with (e:=e1);auto.
  rewrite <- H28 in Heqe0.
  assert ((filter
              (fun x : scenario => inList event_definition_dec (eventDefinition e2) (alphabet x))
              (filterList (finishedscenarios conf) (dom (controlstate conf)) scenario_dec)) =
          (filter
               (fun x : scenario => inList event_definition_dec (eventDefinition e2) (alphabet x))
               (filterList (finishedscenarios conf1) (dom (controlstate conf)) scenario_dec))).
  apply   filterEqual;auto.
  unfold incl;intros. Check finishedInvariantSync. 
  apply finishedInvariantSync with (conf:=conf) (e:=e1);auto.   
  intros.
  apply  inListFalse;auto.
  unfold not;intros.
  assert (In a0 (dom (controlstate conf))).
  rewrite domControlSync with (conf':=conf1) (e:=e1);auto. 
  destruct H11. 
  unfold scenarioInclusion in inclusion;unfold incl in inclusion;apply inclusion;auto. 
      
  apply H3 with (sce1:=a0) in H31;auto.    

  apply syncFinish with (M:=M) (conf:=conf) (conf':=conf1);auto.
  rewrite H29 in Heqe.
  rewrite H29 in H26. 
  clear H29.   

  Check termL2'.
  assert (exists conf' : configuration M, Result conf' = constructConfig x0 e2 conf1).
  apply termL2' with (conf:=conf1) (e:=e2) (scs:=(filter
               (fun x : scenario => inList event_definition_dec (eventDefinition e2) (alphabet x))
               (filterList (finishedscenarios conf1) (dom (controlstate conf)) scenario_dec)) ) (lst:=c1::v0);auto.
  destruct H29.
  SearchAbout   constructConfigList'.
  assert (In x1 (c1::v0)).
  apply constructIn with (l:=(filter
              (fun x : scenario => inList event_definition_dec (eventDefinition e2) (alphabet x))
              (filterList (finishedscenarios conf1) (dom (controlstate conf)) scenario_dec)) ) (e:=e2) (conf:=conf1) (x:=x0) ;auto. 
  assert (In a (exportedevents x1)).
  pose proof constructConfigExportedIn.
  remember H4.
  clear Heqw.   
  destruct H4.
  repeat match goal with
            | [ H: _ /\ _ |- _ ] => destruct H

         end.
  destruct H34.
  repeat match goal with
            | [ H: _ /\ _ |- _ ] => destruct H

         end.    
  apply H31 with (conf:=conf) (conf1:=conf1) (conf':=x) (sce:=x0) (e1:=e1) (e2:=e2);auto.
  apply H44;auto.

  assert (In x0 (dom (controlstate conf))).
  apply filter_In in H26.
  destruct H26.   
  apply filterL2 in H26;auto.
  destruct H6.
  rewrite <-   cs_consist;auto.
  intros.
  SearchAbout usedVarEv.
  assert (~ updateVarEv M (eventDefinition e1) v1).
  unfold not;intros.
  unfold not in H.
  apply H0 with (v1:=v1) (v2:=v1);auto.
  apply diamondDSNoChange with (e1:=e1) (e2:=e2);auto.

   assert (In x0 (dom (controlstate conf))).
  apply filter_In in H26.
  destruct H26.   
  apply filterL2 in H26;auto.
  destruct H6.
  rewrite <-   cs_consist;auto.

  apply filter_In in H26.
  destruct H26.
  SearchAbout inList.
  apply reverseinListLemma in H50;auto.
  SearchAbout  getScenarioState.
  apply diamondCSNoChange with (e1:=e1);auto.
  unfold not;intros.
  assert ( In (eventDefinition e2) (alphabet x0)).
   apply filter_In in H26.
  destruct H26.
  SearchAbout inList.
  apply reverseinListLemma in H51;auto.


  SearchAbout x0.
  assert (In x0 (dom (controlstate conf))).
  apply filter_In in H26.   
  destruct H26.
  apply filterL2 in H26;auto.
  
  unfold not in H3;apply H3 with (sce1:=x0) (sce2:=x0);auto.
  pose proof innerExported'.
  apply H32 with (sceList:=  (filter
             (fun x : scenario => inList event_definition_dec (eventDefinition e2) (alphabet x))
             (filterList (finishedscenarios conf1) (dom (controlstate conf)) scenario_dec))) (conf:=conf1) (l:=c1::v0) (e:=e2) ;auto.
  apply filterUniq;auto.
  apply uniqListFilter.
  Focus 2.
  destruct H6;intuition;auto.
  destruct H11;intuition;auto.
  exists x1;auto.   
  assert (In a (exportedevents conf1)).


   remember H7.
   clear Heqs.
   remember H10.
   clear Heqs0.

   unfold synchrony in s;unfold synchrony in s0.
   destruct s;destruct s0.

   unfold combineFunc in H20;unfold combineFunc in H22.
   remember (constructConfigList (dom (controlstate conf)) e1 conf).
   destruct e;inversion H20.
   clear H24.
   remember (constructConfigList (dom (controlstate conf2)) e1 conf2).
   destruct e;inversion H22.
   clear H24.

   unfold constructConfigList in *.
   destruct v;inversion H20.
   clear H24.
   remember ( innerCombineFunc'''' conf (c :: v)).
   destruct o;inversion H20.
   clear H20.
   destruct v0;inversion H22.
   clear H23.
   remember (innerCombineFunc'''' conf2 (c1 :: v0) ).
   destruct o;inversion H22.
   clear H22.
   simpl.
   rewrite <- H23 in H15;simpl in H15.  

   pose proof innerExported.

   assert ( exists conf' : configuration M, In conf' (c1 :: v0) /\ In a (exportedevents conf')).
   apply H20 with (sceList:=(filter
              (fun x : scenario => inList event_definition_dec (eventDefinition e1) (alphabet x))
              (filterList (finishedscenarios conf2) (dom (controlstate conf2)) scenario_dec))) (conf:=conf2) (c:=c2) (e:=e1) ;auto.
  
   apply filterUniq;auto.
   apply uniqListFilter;destruct H12;intuition;auto.
   destruct H22.
   destruct H22.
  
   assert (exists sce : scenario, In sce (filter
              (fun x : scenario => inList event_definition_dec (eventDefinition e1) (alphabet x))
              (filterList (finishedscenarios conf2) (dom (controlstate conf2)) scenario_dec)) /\ Result x = constructConfig sce e1 conf2).
   apply termL2 with (conf:=conf2) (e:=e1) (lst:=c1::v0) ;auto.
   destruct H26.
   destruct H26.

   assert (dom (controlstate conf) = dom (controlstate conf2)).
  apply domControlSync with (e:=e2);auto.
  rewrite <- H28 in Heqe0. rewrite <- H28 in H26. 
  assert ((filter
              (fun x : scenario => inList event_definition_dec (eventDefinition e1) (alphabet x))
              (filterList (finishedscenarios conf) (dom (controlstate conf)) scenario_dec)) =
          (filter
               (fun x : scenario => inList event_definition_dec (eventDefinition e1) (alphabet x))
               (filterList (finishedscenarios conf2) (dom (controlstate conf)) scenario_dec))).
  apply   filterEqual;auto.
  unfold incl;intros. 
  apply finishedInvariantSync with (conf:=conf) (e:=e2);auto.   
  intros.
  apply  inListFalse;auto.
  unfold not;intros.

  
  assert (In a0 (dom (controlstate conf))).
  rewrite domControlSync with (conf':=conf2) (e:=e2);auto. 
  destruct H12. 
  unfold scenarioInclusion in inclusion;unfold incl in inclusion;apply inclusion;auto.

  
  apply H3 with (sce1:=a0) (sce2:=a0) in H31;auto.    
  
  apply syncFinish with (M:=M) (conf:=conf) (conf':=conf2);auto.
  rewrite H29 in Heqe.

  clear H29.   

  assert (exists conf' : configuration M, Result conf' = constructConfig x0 e1 conf).
  apply termL2' with (conf:=conf) (e:=e1) (scs:=(filter
               (fun x : scenario => inList event_definition_dec (eventDefinition e1) (alphabet x))
               (filterList (finishedscenarios conf2) (dom (controlstate conf)) scenario_dec)) ) (lst:=c::v);auto.
  destruct H29.
  assert (In x1 (c::v)).
  apply constructIn with (l:=(filter
              (fun x : scenario => inList event_definition_dec (eventDefinition e1) (alphabet x))
              (filterList (finishedscenarios conf2) (dom (controlstate conf)) scenario_dec)) ) (e:=e1) (conf:=conf) (x:=x0) ;auto. 
  assert (In a (exportedevents x1)).
  pose proof constructConfigExportedIn'.
  remember H4.
  clear Heqw.   
  destruct H4.
  repeat match goal with
            | [ H: _ /\ _ |- _ ] => destruct H

         end.
  destruct H34.
  repeat match goal with
            | [ H: _ /\ _ |- _ ] => destruct H

         end.

  
  apply H31 with (conf:=conf) (conf1:=conf2) (conf'':= x) (conf':=x1) (sce:=x0) (e1:=e2) (e2:=e1);auto.
  apply H44;auto.

  assert (In x0 (dom (controlstate conf))).
  apply filter_In in H26.
  destruct H26.   
  apply filterL2 in H26;auto.
  destruct H6.
  rewrite <-   cs_consist;auto.
  intros.
 
  assert (~ updateVarEv M (eventDefinition e2) v1).
  unfold not;intros.
  unfold not in H1.
  apply H1 with (v1:=v1) (v2:=v1);auto.
 
  apply diamondDSNoChange with (e1:=e2) (e2:=e1);auto.

   assert (In x0 (dom (controlstate conf))).
  apply filter_In in H26.
  destruct H26.   
  apply filterL2 in H26;auto.
  destruct H6.
  rewrite <-   cs_consist;auto.

  apply filter_In in H26.
   destruct H26.
  apply reverseinListLemma in H50;auto.
  apply diamondCSNoChange with (e1:=e2);auto.
  unfold not;intros.
  assert ( In (eventDefinition e1) (alphabet x0)).
   apply filter_In in H26.
  destruct H26.
  apply reverseinListLemma in H51;auto.
  
  unfold not in H3;apply H3 with (sce1:=x0) (sce2:=x0);auto.
  apply filter_In in H26.
  destruct H26.
  apply filterL2 in H26;auto.
  
  apply filter_In in H26.
  destruct H26.
  apply filterL2 in H26;auto.
           
  pose proof innerExported'.
  apply H32 with (sceList:=  (filter
             (fun x : scenario => inList event_definition_dec (eventDefinition e1) (alphabet x))
             (filterList (finishedscenarios conf2) (dom (controlstate conf)) scenario_dec))) (conf:=conf) (l:=c::v) (e:=e1) ;auto.
  apply filterUniq;auto.
  apply uniqListFilter.
  Focus 2.
  destruct H6;intuition;auto.
  destruct H12;intuition;auto.
  exists x1;auto.   
  
  
  
  apply exportedInvariantSync with (conf:=conf1) (e:=e2);auto.   

     
Qed. 


Lemma diamondExportedAll2:  forall M (conf conf1 conf2 conf1' conf2': configuration M)  e1 e2, 
(forall v1 v2 ,  In v1 (dom (datastate conf)) -> In v2 (dom (datastate conf)) ->
updateVarEv M (eventDefinition e1)  v1 -> updateVarEv M (eventDefinition e2) v2 -> v1 <> v2) -> 
(forall v1 v2 ,  In v1 (dom (datastate conf)) -> In v2 (dom (datastate conf)) ->
updateVarEv M (eventDefinition e1)  v1 -> usedVarEv M (eventDefinition e2) v2 -> v1 <> v2) ->
(forall v1 v2 ,  In v1 (dom (datastate conf)) -> In v2 (dom (datastate conf)) ->
updateVarEv M (eventDefinition e2)  v1 -> usedVarEv M (eventDefinition e1) v2 -> v1 <> v2)  ->
(forall ev1 ev2, In ev1 (events M) -> In ev2 (events M) -> raisedEv M (eventDefinition e1) ev1 -> 
           eventKind ev1 = Internal -> eventKind ev2 = Internal ->        raisedEv M (eventDefinition e2) ev2 -> ev1 <> ev2) ->
(forall sce1 sce2, In sce1 (dom (controlstate conf)) -> In sce2 (dom (controlstate conf)) -> In (eventDefinition e1) (alphabet sce1) -> In (eventDefinition e2) (alphabet sce2) -> sce1 <> sce2) ->
WellFormed M ->
e1 <> e2 ->
correct_configuration conf -> synchrony conf conf1 e1 ->  synchrony conf conf2 e2 ->
synchrony conf1 conf1' e2 -> synchrony conf2 conf2' e1 ->
incl (exportedevents conf1')
     (exportedevents conf2')
.
Proof.
  intros.
  apply diamondExportedAll1 with (conf:=conf) (conf1:=conf2) (conf2:=conf1) (e1:=e2) (e2:=e1);auto.
  intros.
  unfold not;intros.
  unfold not in H.
  apply H with (v1:=v2) (v2:=v1);auto.

  intros.
  unfold not;intros.
  unfold not in H2.
  apply H2 with (ev1:=ev2) (ev2:=ev1);auto.

  intros.
  unfold not;intros.
  unfold not in H3.
  apply H3 with (sce1:=sce2) (sce2:=sce1);auto.
  

Qed. 

Lemma raisedInvariantSync: forall M (conf conf': configuration M) e e1,
      synchrony conf conf' e ->
      In e1 (raisedevents conf) ->
      e1 <> e ->
      In e1 (raisedevents conf').
Proof.
  intros.
  unfold synchrony in H.
  destruct H.
  unfold combineFunc in H2.
  remember (constructConfigList (dom (controlstate conf)) e conf).
  destruct e0;inversion H2.
  clear H4.
  destruct v;inversion H2.
  clear H4.
  remember (innerCombineFunc'''' conf (c :: v)).
  destruct o;inversion H2.
  simpl.
  SearchAbout raisedevents.   
  apply innerCombineRaisedPreservation with (re:=e1) in Heqo;auto.
  SearchAbout   removeEvent'.   
  apply  removeEventPreservation;auto.
Qed.   

 

Lemma removeEventEqual: forall l e e1,
    In e1 l ->
    ~ In e1 (removeEvent' e l) ->
    e1 = e.
Proof.
  intro l;induction l.
  -  intros. inversion H.
  -  intros.
     destruct H;subst.
      simpl in *.      
      destruct (raisedEvent_dec e e1 );auto.
     exfalso;apply H0.       
     left;auto.
     apply IHl;auto. unfold not;intros.
     apply H0;auto.      
     simpl. destruct (raisedEvent_dec e a);auto.
   right;auto.      
Qed.


Lemma raisedInvariantSync': forall M (conf conf': configuration M) e e1,
      synchrony conf conf' e ->
      In e1 (raisedevents conf) ->
      ~ In e1 (raisedevents conf') ->
       e1 = e .
Proof.
  intros.
  unfold synchrony in H.
  destruct H.
  unfold combineFunc in H2.
  remember (constructConfigList (dom (controlstate conf)) e conf).
  destruct e0;inversion H2.
  clear H4.
  destruct v;inversion H2.
  clear H4.
  remember (innerCombineFunc'''' conf (c :: v)).
  destruct o;inversion H2.
    apply innerCombineRaisedPreservation with (re:=e1) in Heqo;auto.
  rewrite <- H4 in H1. simpl in H1. 
  apply removeEventEqual with (l:=(raisedevents c0)) ;auto. 
Qed.  
(*Lemma diamondRaisedAll1:  forall M (conf conf1 conf2 conf1' conf2': configuration M)  e1 e2, 
(forall v1 v2 ,
updateVarEv M (eventDefinition e1)  v1 -> updateVarEv M (eventDefinition e2) v2 -> v1 <> v2) -> 
(forall v1 v2 ,
updateVarEv M (eventDefinition e1)  v1 -> usedVarEv M (eventDefinition e2) v2 -> v1 <> v2) ->
(forall v1 v2 , 
updateVarEv M (eventDefinition e2)  v1 -> usedVarEv M (eventDefinition e1) v2 -> v1 <> v2)  ->
(forall ev1 ev2, In ev1 (events M) -> In ev2 (events M) -> raisedEv M (eventDefinition e1) ev1 -> 
                 raisedEv M (eventDefinition e2) ev2 -> ev1 <> ev2) ->
(forall sce1 sce2, In (eventDefinition e1) (alphabet sce1) -> In (eventDefinition e2) (alphabet sce2) -> sce1 <> sce2) ->
WellFormed M ->
e1 <> e2 ->
correct_configuration conf -> synchrony conf conf1 e1 ->  synchrony conf conf2 e2 ->
synchrony conf1 conf1' e2 -> synchrony conf2 conf2' e1 ->
incl (raisedevents conf2')
     (raisedevents conf1')
.*)

Lemma syncFinishExists: forall M (conf conf' :configuration M) e,
      
    synchrony conf conf' e ->
    correct_configuration conf ->
       (exists sce, ~ In sce (finishedscenarios conf) /\ In sce (finishedscenarios conf')).
Proof.
  intros.
  rename H0 into corr. 
  unfold synchrony in H.
  destruct H.
  unfold combineFunc in H0.
  remember (constructConfigList (dom (controlstate conf)) e conf).
  destruct e0;inversion H0.
  unfold constructConfigList  in Heqe0.
  destruct v;inversion H0.
  clear H3.
  remember (innerCombineFunc'''' conf (c :: v) ).
  destruct o;inversion H2.
  simpl.
  Check termL2.
  assert (exists sce : scenario, In sce (filter
               (fun x : scenario => inList event_definition_dec (eventDefinition e) (alphabet x))
               (filterList (finishedscenarios conf) (dom (controlstate conf)) scenario_dec)) /\ Result  c = constructConfig sce e conf).
  apply termL2 with (conf:=conf) (e:=e) (lst:=c::v);auto.
  split;auto.   
  left;auto.
  destruct H1.
  exists x.
  destruct H1.
  apply filter_In in H1.
  destruct H1.
  split.
  apply filterL1 in H1;auto.   
  SearchAbout finishedscenarios. 
  assert (In x (finishedscenarios c)).
  rewrite wellForm.termL3 with (e:=e) (conf:=conf) (sce:=x);auto.
  left;auto.
  SearchAbout finishedscenarios.
  pose proof finishedInList''.
  apply H7 with (lst:=(filter
               (fun x : scenario => inList event_definition_dec (eventDefinition e) (alphabet x))
               (filterList (finishedscenarios conf) (dom (controlstate conf)) scenario_dec))) (e:=e) (M:=M) (conf:=conf) (v:=c::v);auto.
  apply filterUniq.
  apply uniqListFilter;destruct corr;intuition;auto.
  unfold incl;intros.
  apply filter_In in H8.
  destruct H8.
  apply filterL2 in H8;auto.
  apply filter_In;auto.
  
  
Qed.


Lemma raisedEvInAlphabet:
     forall (M : monitor) (conf conf' : configuration M) (e re : raisedEvent),
  correct_configuration conf ->
  basicPreconditionMon M ->
  synchrony conf conf' e ->
  ~ In re (raisedevents conf) ->
  In re (raisedevents conf') ->
  noMergeError' M ->
  raisedEv M (eventDefinition e) (eventDefinition re).
Proof.
  intros.
  unfold raisedEv.
  assert ( exists (sce : scenario) (tr : step) (act : action) (exprs : list expr),
    ~ In sce (finishedscenarios conf) /\
    In (sce, eventDefinition e) (sceEventMap conf') /\
    In tr (getTransitionsOfScenario sce) /\
    In act (transitionIntoBasicActionList (stepActions tr)) /\
    act = RaiseStmt (eventId (eventDefinition re)) exprs /\
    eventDefinition e = event (stepEvent tr)).
  apply syncRaised'';auto.
  destruct H5.
  destruct H5.
  destruct H5.
  destruct H5.
  repeat match goal with
            | [ H: _ /\ _ |- _ ] => destruct H

         end.

  exists x.
  split.
  SearchAbout   scenarioRaise.
  eapply scenarioRaiseIn;auto.
  Focus 2.   
  apply H7.
  Focus 2.
  rewrite H9 in H8.
  apply H8.
  destruct H0.

  repeat match goal with
            | [ H: _ /\ _ |- _ ] => destruct H

         end.

  assert (correct_configuration conf').
  apply termL5 with (conf:=conf) (e:=e);auto.   
  destruct H.
  apply   raised_wellform' ;auto.
  unfold synchrony in H1; intuition;auto.
  destruct H21.
  assert (In x (finishedscenarios conf')).
  assert (In x (dom (sceEventMap conf'))).
  SearchAbout dom.
  eapply  domIn ;auto.
  apply H6.
  apply Permutation_in with (l:=(dom (sceEventMap conf')) );auto.
  assert (In x (dom (controlstate conf'))).
  unfold scenarioInclusion in inclusion.
  unfold incl in inclusion.   
  apply inclusion;auto.
  rewrite <- cs_consist;auto.
  Print triggerSce.
  apply basic_ts;auto.
  Focus 2.
  SearchAbout alphabet.
  apply syncFinish with (M:=M) (conf:=conf) (conf':=conf');auto.

  destruct H0.

  repeat match goal with
            | [ H: _ /\ _ |- _ ] => destruct H

         end.

  assert (correct_configuration conf').
  apply termL5 with (conf:=conf) (e:=e);auto.   
  destruct H.
  apply   raised_wellform' ;auto.
  unfold synchrony in H1; intuition;auto.

  SearchAbout sceEventMap.
  apply chainMergeFinMap';auto.
  exists (eventDefinition e);auto.

  destruct H0.

  repeat match goal with
            | [ H: _ /\ _ |- _ ] => destruct H

         end.

  assert (correct_configuration conf').
  apply termL5 with (conf:=conf) (e:=e);auto.   
  destruct H.
  apply   raised_wellform' ;auto.
  unfold synchrony in H1; intuition;auto.
  remember H21. 
 clear Heqc.   destruct H21.
  rewrite <-   cs_consist.
  assert (In x (finishedscenarios conf')).

  apply chainMergeFinMap';auto.
   exists (eventDefinition e);auto.

    unfold scenarioInclusion in inclusion.
  unfold incl in inclusion.   
  apply inclusion;auto.
  
  
Qed.

(*syncRaised'':
  forall (M : monitor) (conf conf' : configuration M) (e re : raisedEvent),
  correct_configuration conf ->
  basicPreconditionMon M ->
  synchrony conf conf' e ->
  ~ In re (raisedevents conf) ->
  In re (raisedevents conf') ->
  noMergeError' M ->
  exists (sce : scenario) (tr : step) (act : action) (exprs : list expr),
    ~ In sce (finishedscenarios conf) /\
    In (sce, eventDefinition e) (sceEventMap conf') /\
    In tr (getTransitionsOfScenario sce) /\
    In act (transitionIntoBasicActionList (stepActions tr)) /\
    act = RaiseStmt (eventId (eventDefinition re)) exprs /\
    eventDefinition e = event (stepEvent tr)*)

 (*syncRaised':
  forall (M : monitor) (conf conf' : configuration M) (e re : raisedEvent),
  correct_configuration conf ->
  basicPreconditionMon M ->
  synchrony conf conf' e ->
  ~ In re (raisedevents conf) ->
  In re (raisedevents conf') ->
  noMergeError' M ->
  exists (sce : scenario) (tr : step) (act : action) (exprs : list expr),
    In (sce, eventDefinition e) (sceEventMap conf') /\
    In tr (getTransitionsOfScenario sce) /\
    In act (transitionIntoBasicActionList (stepActions tr)) /\
    act = RaiseStmt (eventId (eventDefinition re)) exprs /\
    eventDefinition e = event (stepEvent tr)*)
 


  
Lemma constructConfigRaisedIn: forall M (conf conf1 conf' conf'': configuration M) sce e1 e2 e,
    correct_configuration conf ->
    synchrony conf conf1 e1 ->
    e1 <> e2 ->
    stateEvDefInstanceMapEquiv M ->
    correctStateEvStepMap' M ->
    stepExistsMon' M sce ->
    (forall v,  In v (dom (datastate conf)) -> usedVarEv M (eventDefinition e2) v -> getValue v (datastate conf) = getValue v (datastate conf1)) ->
    In sce (scenarios M) ->
    In (eventDefinition e2) (alphabet sce) ->
    getScenarioState sce (controlstate conf) = getScenarioState sce (controlstate conf1) ->
    Result conf' = constructConfig sce e2 conf ->
    Result conf'' = constructConfig sce e2 conf1 ->
    In e2 (raisedevents conf) ->
    typeCheck M ->
    transEvMapEventInstanceProp M ->
    transEvMapProp M ->
    stpStMapEquiv' M ->
    stateEvDefInstanceMapEquivEListProp M ->
    stateSceIn M ->
    In e (raisedevents conf') ->
    In e (raisedevents conf''). 
Proof.

  intros. rename H13 into transInProp.
  rename H14 into transProp.
  rename H15 into stpEquiv.
  rename H16 into stateMapEquivProp.
  rename H17 into stateIn.
  unfold constructConfig in *.
  rewrite <- H8 in H10.
  remember (getScenarioState sce (controlstate conf) ).
  destruct o;inversion H10.
  clear H14.
  remember (transEvMapFunc (stateEvDefInstanceMap M) (Some s, Some (eventDefinition e2)) ).
  destruct o;inversion H10.
  clear H14.
  assert (findEventInstance e2 (datastate conf) l = findEventInstance e2 (datastate conf1) l).



   apply findEventValueEq;auto.
  intros.

  assert (In v (dom (datastate conf)) \/ ~ In v (dom (datastate conf))). 
  apply excluded_middle.
  destruct H15.
    
  apply H5;auto.   unfold usedVarEv.
  exists sce. split.
  Focus 2.
   
  apply basic_ts;auto.
  rename H15 into vdd.
  
  unfold correctStateEvStepMap' in H3.
  unfold stepExistsMon' in H4.
  unfold stateEvDefInstanceMapEquiv in H2. 
  assert (exists stp : step, In (s, ei, sce, Some stp) (stateEvStepMap' M)).
  apply H4  with (e:=(eventDefinition e2)) (l:=l);auto.

  rewrite semantic_rules.stateEvDefInstanceMapEquiv'. symmetry;auto. 
  destruct H2;auto.
  destruct H15.   
  apply H3 in H15.
  destruct H15.
  destruct H16.
  apply scenarioUsedVarIn with (stp:=x);auto.
  subst;auto.   

  assert (dom (datastate conf) = dom (datastate conf1)).
   assert (dom2 (datastate conf) = dom2 (datastate conf1)).
  apply syncDSDom2 with (e:=e1) ;auto.
  rewrite <- dom2dom'. 
  rewrite <- dom2dom'.    rewrite H16;auto.
  SearchAbout getValue.
  rewrite getValueNone'. rewrite getValueNone'. auto. rewrite <- H16;auto. auto.

  
 
  assert (dom2 (datastate conf) = dom2 (datastate conf1)).
  apply syncDSDom2 with (e:=e1) ;auto.
  rewrite <- dom2dom'. 
  rewrite <- dom2dom'.    rewrite H13;auto. 
  intros.
  apply tyEnvVar with (env:=datastate conf);auto.  
  destruct H;auto.
  rewrite <- H13 in H10.
  remember (findEventInstance e2 (datastate conf) l).
  destruct o;inversion H9.
  clear H15.
  remember (createValueEnv (eventArgs e0) (eventParams (eventDefinition e2)) (eventArguments e2)).
  destruct e3;inversion H9.
  clear H15.
  assert (getStep' conf sce e0 = getStep' conf1 sce e0).
  unfold getStep'.
  rewrite <- Heqo.
  rewrite <- H8.
  auto.
  rewrite <- H14 in H10.
  remember (getStep' conf sce e0).
  destruct o;inversion H9.
  clear H16.
  remember (configTransition (extendValEnv (datastate conf) v) e2 e0 sce s0 conf).
  destruct e3;inversion H9.
  subst.
  remember (configTransition (extendValEnv (datastate conf1) v) e2 e0 sce s0 conf1).
  destruct e3;inversion H9.
  subst.
  unfold configTransition in Heqe0,Heqe1.
  remember (execAction (extendValEnv (datastate conf) v, []) (stepActions s0)
              (filter
                 (fun e : event_definition =>
                  match eventKind e with
                  | Internal => true
                  | Imported => false
                  | Exported => true
                  end) (events M))).
  destruct e3;inversion Heqe0.
  clear H16.
  destruct v2.
  remember ( execAction (extendValEnv (datastate conf1) v, []) (stepActions s0)
              (filter
                 (fun e : event_definition =>
                  match eventKind e with
                  | Internal => true
                  | Imported => false
                  | Exported => true
                  end) (events M))).
  destruct e3;inversion Heqe1.
  clear H16.
  destruct v3.
  inversion Heqe0;subst;simpl.
  inversion Heqe1;subst;simpl. simpl in H18. inversion H10;subst. simpl.
  clear H10;clear Heqe1. clear H9;clear Heqe0.
  apply filter_In in H18.
  destruct H18.
  apply filter_In;auto.
  split;auto.   
  Focus 2. inversion H10.
  
  unfold extendValEnv in Heqe2, Heqe4.
 
  (*getValueIn'*)
  SearchAbout execAction. 
  assert ( dom (datastate conf ++ v) = dom v2 ).
  eapply execActionUniqList. 
  apply Heqe2.
  assert ( dom (datastate conf1 ++ v) = dom v3).
  eapply execActionUniqList.   apply Heqe4.


  assert (  exists (act : action) (exprs : list expr),
    In act (transitionIntoBasicActionList (stepActions s0)) /\
    act = RaiseStmt (eventId (eventDefinition e)) exprs).

  eapply execActionRaisingEvent ;auto.
  apply Heqe2.
  unfold not;intros.
  inversion H17.
  auto.

  pose proof execActionInEvent.
  assert (l0 = l1).
  apply H18 with (act:=stepActions s0) (ds0:=datastate conf ++ v) (ds0':=datastate conf1 ++ v) (l:=[]) (ds1:=v2) (ds1':=v3) (el:=(filter
               (fun e : event_definition =>
                match eventKind e with
                | Internal => true
                | Imported => false
                | Exported => true
                end) (events M)));auto.
  Focus 2.   
  rewrite domApp. 
  rewrite domApp.
  
  destruct H.
  rewrite <- dom2dom'.   
  rewrite   ds_dom_eq .
  assert (correct_configuration conf1).
  Check termL5.
  apply termL5 with (conf:=conf) (e:=e1);auto.
 repeat(split;auto).   
 apply raised_wellform'.
 unfold synchrony in H0;intuition;auto.
 destruct H. 
    rewrite <- dom2dom'. rewrite <- dom2dom'.   
      rewrite   ds_dom_eq0;auto .
      Focus 2.   subst;auto.
      intros.
      SearchAbout filterStateUsedAct.
      assert (In v0 (dom (datastate conf)) \/ ~ In v0 (dom (datastate conf))).
      apply  excluded_middle.
      destruct H20.
      Focus 2.
      SearchAbout getValue.
  rewrite getValueNotInNoUniq'.       
  rewrite getValueNotInNoUniq'.
  auto.
  unfold not;intros.
  destruct H.
   rewrite <- dom2dom' in H20.   
   rewrite  ds_dom_eq in H20;auto .

    assert (correct_configuration conf1).
  Check termL5.
  apply termL5 with (conf:=conf) (e:=e1);auto.
 repeat(split;auto).   
 apply raised_wellform'.
 unfold synchrony in H0;intuition;auto.
 destruct H.
   rewrite <- dom2dom' in H21.  rewrite   ds_dom_eq0 in H21;auto .
  auto.  

  assert (In v0 (dom (datastate conf1))).
 destruct H.
   rewrite <- dom2dom' in H20.       rewrite <- dom2dom'.     
rewrite  ds_dom_eq in H20;auto .

 assert (correct_configuration conf1).
  Check termL5.
  apply termL5 with (conf:=conf) (e:=e1);auto.
 repeat(split;auto).   
 apply raised_wellform'.
 unfold synchrony in H0;intuition;auto.

 destruct H.
    rewrite   ds_dom_eq0 ;auto .
    SearchAbout getValue.
    rewrite   getValueInNoUniq';auto. 
      rewrite getValueInNoUniq';auto. 
      apply H5;auto.
      unfold  usedVarEv.
      exists sce.
      split;auto.
      Focus 2.
      Print triggerSce.
      apply  basic_ts;auto.
      SearchAbout  scenarioUsedVar.
      apply  scenarioUsedVarIn' with (stp:=s0);auto.
  SearchAbout traces.      
  unfold  correctStateEvStepMap' in H3.
  unfold stateEvDefInstanceMapEquiv in H2.
  destruct H2.
  Print stpStMap'.
  SearchAbout stateEvStepMap'.
  assert (Some s0 = stpStpMapFunc (stateEvStepMap' M) (s, e0, sce)).
  apply getStepMap' with (conf:=conf);auto.
  SearchAbout  stpStpMapFunc. symmetry in H23. 
  rewrite  <- stpStMapEquivLem in H23.
  Focus 2.   unfold stpStMapEquiv' in *;auto. 
   assert ( In s0 (traces sce) /\ stepEvent s0 = e0 /\ pre_state s0 = s).
   apply H3;auto.
  destruct H24;auto.    
Qed.



Lemma constructConfigRaisedIn': forall M (conf conf1 conf' conf'': configuration M) sce e1 e2 e,
    correct_configuration conf ->
    synchrony conf conf1 e1 ->
    e1 <> e2 ->
    stateEvDefInstanceMapEquiv M ->
    correctStateEvStepMap' M ->
    stepExistsMon' M sce ->
    (forall v,  In v (dom (datastate conf)) -> usedVarEv M (eventDefinition e2) v -> getValue v (datastate conf) = getValue v (datastate conf1)) ->
    In sce (scenarios M) ->
    In (eventDefinition e2) (alphabet sce) ->
    getScenarioState sce (controlstate conf) = getScenarioState sce (controlstate conf1) ->
    Result conf' = constructConfig sce e2 conf ->
    Result conf'' = constructConfig sce e2 conf1 ->
    In e2 (raisedevents conf) ->
    typeCheck M ->
    transEvMapEventInstanceProp M ->
    transEvMapProp M ->
    stpStMapEquiv' M ->
    stateEvDefInstanceMapEquivEListProp M ->
    stateSceIn M ->
    In e (raisedevents conf'') ->
    In e (raisedevents conf'). 
Proof.

  intros. rename H13 into transInProp.
  rename H14 into transProp.
  rename H15 into stpEquiv.
  rename H16 into stateMapEquivProp.
  rename H17 into stateIn.
  unfold constructConfig in *.
  rewrite <- H8 in H10.
  remember (getScenarioState sce (controlstate conf) ).
  destruct o;inversion H10.
  clear H14.
  remember (transEvMapFunc (stateEvDefInstanceMap M) (Some s, Some (eventDefinition e2)) ).
  destruct o;inversion H10.
  clear H14.
  assert (findEventInstance e2 (datastate conf) l = findEventInstance e2 (datastate conf1) l).


   apply findEventValueEq;auto.
  intros.

  assert (In v (dom (datastate conf)) \/ ~ In v (dom (datastate conf))). 
  apply excluded_middle.
  destruct H15.
    
  apply H5;auto.   unfold usedVarEv.
  exists sce. split.
  Focus 2.
   
  apply basic_ts;auto.
  rename H15 into vdd.
  
  unfold correctStateEvStepMap' in H3.
  unfold stepExistsMon' in H4.
  unfold stateEvDefInstanceMapEquiv in H2. 
  assert (exists stp : step, In (s, ei, sce, Some stp) (stateEvStepMap' M)).
  apply H4  with (e:=(eventDefinition e2)) (l:=l);auto.

  rewrite semantic_rules.stateEvDefInstanceMapEquiv'. symmetry;auto. 
  destruct H2;auto.
  destruct H15.   
  apply H3 in H15.
  destruct H15.
  destruct H16.
  apply scenarioUsedVarIn with (stp:=x);auto.
  subst;auto.   

  assert (dom (datastate conf) = dom (datastate conf1)).
   assert (dom2 (datastate conf) = dom2 (datastate conf1)).
  apply syncDSDom2 with (e:=e1) ;auto.
  rewrite <- dom2dom'. 
  rewrite <- dom2dom'.    rewrite H16;auto.
  SearchAbout getValue.
  rewrite getValueNone'. rewrite getValueNone'. auto. rewrite <- H16;auto. auto.

  
  assert (dom2 (datastate conf) = dom2 (datastate conf1)).
  apply syncDSDom2 with (e:=e1) ;auto.
  rewrite <- dom2dom'. 
  rewrite <- dom2dom'.    rewrite H13;auto. 
  intros.
  apply tyEnvVar with (env:=datastate conf);auto.  
  destruct H;auto.
  rewrite <- H13 in H10.
  remember (findEventInstance e2 (datastate conf) l).
  destruct o;inversion H9.
  clear H15.
  remember (createValueEnv (eventArgs e0) (eventParams (eventDefinition e2)) (eventArguments e2)).
  destruct e3;inversion H9.
  clear H15.
  assert (getStep' conf sce e0 = getStep' conf1 sce e0).
  unfold getStep'.
  rewrite <- Heqo.
  rewrite <- H8.
  auto.
  rewrite <- H14 in H10.
  remember (getStep' conf sce e0).
  destruct o;inversion H9.
  clear H16.
  remember (configTransition (extendValEnv (datastate conf) v) e2 e0 sce s0 conf).
  destruct e3;inversion H9.
  subst.
  remember (configTransition (extendValEnv (datastate conf1) v) e2 e0 sce s0 conf1).
  destruct e3;inversion H9.
  subst.
  unfold configTransition in Heqe0,Heqe1.
  remember (execAction (extendValEnv (datastate conf) v, []) (stepActions s0)
              (filter
                 (fun e : event_definition =>
                  match eventKind e with
                  | Internal => true
                  | Imported => false
                  | Exported => true
                  end) (events M))).
  destruct e3;inversion Heqe0.
  clear H16.
  destruct v2.
  remember ( execAction (extendValEnv (datastate conf1) v, []) (stepActions s0)
              (filter
                 (fun e : event_definition =>
                  match eventKind e with
                  | Internal => true
                  | Imported => false
                  | Exported => true
                  end) (events M))).
  destruct e3;inversion Heqe1.
  clear H16.
  destruct v3.
  inversion Heqe0;subst;simpl.
  inversion Heqe1;subst;simpl. inversion H10;subst.  simpl in H18. 
  clear H10;clear Heqe1. clear H9;clear Heqe0.
  apply filter_In in H18.
  destruct H18.
  apply filter_In;auto.
  split;auto.   
  Focus 2. inversion H10.
  
  unfold extendValEnv in Heqe2, Heqe4.
 
  (*getValueIn'*)
  SearchAbout execAction. 
  assert ( dom (datastate conf ++ v) = dom v2 ).
  eapply execActionUniqList. 
  apply Heqe2.
  assert ( dom (datastate conf1 ++ v) = dom v3).
  eapply execActionUniqList.   apply Heqe4.

  
  assert (  exists (act : action) (exprs : list expr),
    In act (transitionIntoBasicActionList (stepActions s0)) /\
    act = RaiseStmt (eventId (eventDefinition e)) exprs).
  Check execActionRaisingEvent.
    
  eapply execActionRaisingEvent ;auto.
  apply Heqe4.
  unfold not;intros.
  inversion H17.
  auto.

  pose proof execActionInEvent.
  assert (l0 = l1).
  apply H18 with (act:=stepActions s0) (ds0:=datastate conf ++ v) (ds0':=datastate conf1 ++ v) (l:=[]) (ds1:=v2) (ds1':=v3) (el:=(filter
               (fun e : event_definition =>
                match eventKind e with
                | Internal => true
                | Imported => false
                | Exported => true
                end) (events M)));auto.
  Focus 2.   
  rewrite domApp. 
  rewrite domApp.
  
  destruct H.
  rewrite <- dom2dom'.   
  rewrite   ds_dom_eq .
  assert (correct_configuration conf1).
 
  apply termL5 with (conf:=conf) (e:=e1);auto.
 repeat(split;auto).   
 apply raised_wellform'.
 unfold synchrony in H0;intuition;auto.
 destruct H. 
    rewrite <- dom2dom'. rewrite <- dom2dom'.   
      rewrite   ds_dom_eq0;auto .
      Focus 2.   subst;auto.
      intros.
      assert (In v0 (dom (datastate conf)) \/ ~ In v0 (dom (datastate conf))).
      apply  excluded_middle.
      destruct H20.
      Focus 2.
 
  rewrite getValueNotInNoUniq'.       
  rewrite getValueNotInNoUniq'.
  auto.
  unfold not;intros.
  destruct H.
   rewrite <- dom2dom' in H20.   
   rewrite  ds_dom_eq in H20;auto .

    assert (correct_configuration conf1).

  apply termL5 with (conf:=conf) (e:=e1);auto.
 repeat(split;auto).   
 apply raised_wellform'.
 unfold synchrony in H0;intuition;auto.
 destruct H.
   rewrite <- dom2dom' in H21.  rewrite   ds_dom_eq0 in H21;auto .
  auto.  

  assert (In v0 (dom (datastate conf1))).
 destruct H.
   rewrite <- dom2dom' in H20.       rewrite <- dom2dom'.     
rewrite  ds_dom_eq in H20;auto .

 assert (correct_configuration conf1).
  apply termL5 with (conf:=conf) (e:=e1);auto.
 repeat(split;auto).   
 apply raised_wellform'.
 unfold synchrony in H0;intuition;auto.

 destruct H.
    rewrite   ds_dom_eq0 ;auto .
    rewrite   getValueInNoUniq';auto. 
      rewrite getValueInNoUniq';auto. 
      apply H5;auto.
      unfold  usedVarEv.
      exists sce.
      split;auto.
      Focus 2.
      apply  basic_ts;auto.
      apply  scenarioUsedVarIn' with (stp:=s0);auto.
  unfold  correctStateEvStepMap' in H3.
  unfold stateEvDefInstanceMapEquiv in H2.
  destruct H2.

  assert (Some s0 = stpStpMapFunc (stateEvStepMap' M) (s, e0, sce)).
  apply getStepMap' with (conf:=conf);auto.
  symmetry in H23. 
  rewrite  <- stpStMapEquivLem in H23.
  Focus 2.   unfold stpStMapEquiv' in *;auto. 
   assert ( In s0 (traces sce) /\ stepEvent s0 = e0 /\ pre_state s0 = s).
   apply H3;auto.
  destruct H24;auto.    
Qed.

(*noDupEventDefinitionRaised''*)

Lemma diamondRaisedAll1:  forall M (conf conf1 conf2 conf1' conf2': configuration M)  e1 e2, 
(forall v1 v2 , In v1 (dom (datastate conf)) -> In v2 (dom (datastate conf)) ->
updateVarEv M (eventDefinition e1)  v1 -> updateVarEv M (eventDefinition e2) v2 -> v1 <> v2) -> 
(forall v1 v2 , In v1 (dom (datastate conf)) -> In v2 (dom (datastate conf)) ->
updateVarEv M (eventDefinition e1)  v1 -> usedVarEv M (eventDefinition e2) v2 -> v1 <> v2) ->
(forall v1 v2 , In v1 (dom (datastate conf)) -> In v2 (dom (datastate conf)) ->
updateVarEv M (eventDefinition e2)  v1 -> usedVarEv M (eventDefinition e1) v2 -> v1 <> v2)  ->
(forall ev1 ev2, In ev1 (events M) -> In ev2 (events M) -> raisedEv M (eventDefinition e1) ev1 -> 
                  eventKind ev1 = Internal -> eventKind ev2 = Internal -> raisedEv M (eventDefinition e2) ev2 -> ev1 <> ev2) ->
(forall sce1 sce2, In sce1 (dom (controlstate conf)) -> In sce2 (dom (controlstate conf)) -> In (eventDefinition e1) (alphabet sce1) -> In (eventDefinition e2) (alphabet sce2) -> sce1 <> sce2) ->
WellFormed M ->
e1 <> e2 ->
(initialConfig conf \/ (exists conf' e, chainMerge conf' conf e)) -> synchrony conf conf1 e1 ->  synchrony conf conf2 e2 ->
synchrony conf1 conf1' e2 -> synchrony conf2 conf2' e1 ->
incl (raisedevents conf2')
     (raisedevents conf1')
.
Proof.
  intros.
  assert (correct_configuration conf).
  destruct H6.
  destruct H6;intuition;auto.
  destruct H6.   destruct H6.
  destruct H4.

     repeat match goal with
            | [ H: _ /\ _ |- _ ] => destruct H

         end. 
    
     destruct H13.
              
              
     repeat match goal with
            | [ H: _ /\ _ |- _ ] => destruct H

            end.

     
  apply termL5' with (conf:=x) (e:=x0);auto.   
  remember H6. clear Heqc. 
  apply chainMergeInitialEvent in c.
  apply chainMergeInitial in H6.
  destruct H6.
  destruct H6.
 apply raised_wellform';auto.   
 rename H11 into corrconf.
 
  assert (correct_configuration conf1).

   destruct H4.

     repeat match goal with
            | [ H: _ /\ _ |- _ ] => destruct H

         end. 
    
     destruct H13.
              
              
     repeat match goal with
            | [ H: _ /\ _ |- _ ] => destruct H

            end.
     apply termL5 with (conf:=conf) (e:=e1);auto.
        
     destruct corrconf.
     apply raised_wellform';auto.
     unfold synchrony in H7;intuition;auto.

     
   assert (correct_configuration conf2).

   destruct H4.

     repeat match goal with
            | [ H: _ /\ _ |- _ ] => destruct H

         end. 
    
     destruct H14.
              
              
     repeat match goal with
            | [ H: _ /\ _ |- _ ] => destruct H

            end.
     apply termL5 with (conf:=conf) (e:=e2);auto.
   
     destruct corrconf.
     apply raised_wellform';auto.
     unfold synchrony in H8;intuition;auto.

   assert (correct_configuration conf1').

   destruct H4.

     repeat match goal with
            | [ H: _ /\ _ |- _ ] => destruct H

         end. 
    
     destruct H15.
              
              
     repeat match goal with
            | [ H: _ /\ _ |- _ ] => destruct H

            end.
     apply termL5 with (conf:=conf1) (e:=e2);auto.
   
     destruct H11.
     apply raised_wellform';auto.
     unfold synchrony in H9;intuition;auto.

       assert (correct_configuration conf2').

   destruct H4.

     repeat match goal with
            | [ H: _ /\ _ |- _ ] => destruct H

         end. 
    
     destruct H16.
              
              
     repeat match goal with
            | [ H: _ /\ _ |- _ ] => destruct H

            end.
     apply termL5 with (conf:=conf2) (e:=e1);auto.
   
     destruct H12.
     apply raised_wellform';auto.
     unfold synchrony in H10;intuition;auto.
  
  unfold incl;intros.
  assert (In a (raisedevents conf) \/ ~ In a (raisedevents conf)).
  apply excluded_middle.
  destruct H16.

-

  assert (In a (raisedevents conf2) \/ ~ In a (raisedevents conf2)).
  apply excluded_middle.
  destruct H17.
  assert (a <> e2 /\ a <> e1).
  split. 
  +
    unfold not;intros.
    subst.
    unfold synchrony in H8.
    destruct H8.
    unfold combineFunc in H18.
    destruct (constructConfigList (dom (controlstate conf)) e2 conf );inversion H18.
    clear H20.
    destruct v;inversion H18.
    clear H20.
    destruct (innerCombineFunc'''' conf (c :: v));inversion H18.
    inversion H18;subst.
    simpl in H17. SearchAbout removeEvent'. apply removeNotIn in H17;auto.
  +   unfold not;intros.
    subst.
    unfold synchrony in H10.
    destruct H10.
    unfold combineFunc in H18.
    destruct (constructConfigList (dom (controlstate conf2)) e1 conf2 );inversion H18.
    clear H20.
    destruct v;inversion H18.
    clear H20.
    destruct (innerCombineFunc'''' conf2 (c :: v));inversion H18.
    inversion H18;subst.
    simpl in H15. apply removeNotIn in H15;auto.
   +    
     destruct H18.
          
  assert (In a (raisedevents conf1)).
  
  apply raisedInvariantSync with (e:=e1) (conf:=conf);auto.

  apply raisedInvariantSync with (e:=e2) (conf:=conf1);auto.

  + 
    assert (a = e2).
    apply raisedInvariantSync' with (M:=M) (conf:=conf) (conf':=conf2);auto. 
    
    subst.
    exfalso.
    pose proof noDupEventDefinition''.
    destruct H6.
    destruct H4.
        repeat match goal with
            | [ H: _ /\ _ |- _ ] => destruct H

            end.
   assert ((forall re0 : raisedEvent,
         In re0 (raisedevents conf2') ->
         ~
         (exists ev : event_definition,
            In ev (range (sceEventMap conf2')) /\ eventDefinition re0 = ev)) /\
        (forall re0 re' : raisedEvent,
         In re0 (raisedevents conf2') ->
         In re' (raisedevents conf2') -> re0 <> re' -> eventDefinition re0 <> eventDefinition re')).
   apply H18 with (conf:=conf) (re:=e2);auto.
  
   apply chain' with (conf':=conf2) (event2:=e1);auto.
   apply basic';auto.
   split. apply noMultIn;auto. apply noMultImportedIn;auto. 
   destruct H24.
   assert (~
        (exists ev : event_definition,
            In ev (range (sceEventMap conf2')) /\ eventDefinition e2 = ev)).
   apply H27;auto.
   apply H29.
   pose proof syncFinishExists.
   assert (exists sce : scenario,
              ~ In sce (finishedscenarios conf) /\ In sce (finishedscenarios conf2)).
   apply H30 with (e:=e2);auto.
   destruct H31.
   destruct H31.
   SearchAbout sceEventMap.
   exists (eventDefinition e2).
   
   split;auto.
   assert (In (x, eventDefinition e2) ((sceEventMap conf2))).
   SearchAbout sceEventMap.
   apply syncFinishedMap with (conf:=conf);auto.

   unfold not;intros.
   rewrite <- chainMergeFinMap' in H33.
   contradiction.
  auto.    
  destruct H21.
  repeat match goal with
            | [ H: _ /\ _ |- _ ] => destruct H

         end.
  repeat(split;auto).
  assert (In (x, eventDefinition e2) (sceEventMap conf2')). 
  SearchAbout sceEventMap.
  apply sceEventMapNoChangeSync with (conf:=conf2) (e:=e1);auto.
  SearchAbout  range.
  apply rangeDomInRev with (a:=x);auto.

  destruct H6. 
  destruct H6.


   destruct H4.
        repeat match goal with
            | [ H: _ /\ _ |- _ ] => destruct H

            end.
   assert ((forall re0 : raisedEvent,
         In re0 (raisedevents conf2') ->
         ~
         (exists ev : event_definition,
            In ev (range (sceEventMap conf2')) /\ eventDefinition re0 = ev)) /\
        (forall re0 re' : raisedEvent,
         In re0 (raisedevents conf2') ->
         In re' (raisedevents conf2') -> re0 <> re' -> eventDefinition re0 <> eventDefinition re')).
   apply H18 with (conf:=x) (re:=x0);auto.
   assert (chainMerge x conf2 x0).
   apply chain' with (conf':=conf) (event2:=e2);auto.
   
   apply chain' with (conf':=conf2) (event2:=e1);auto.

   split. apply noMultIn;auto. apply noMultImportedIn;auto. 
   destruct H27.
   assert (~
        (exists ev : event_definition,
            In ev (range (sceEventMap conf2')) /\ eventDefinition e2 = ev)).
   apply H27;auto.
   apply H29.
   pose proof syncFinishExists.
   assert (exists sce : scenario,
              ~ In sce (finishedscenarios conf) /\ In sce (finishedscenarios conf2)).
   apply H30 with (e:=e2);auto.
   destruct H31.
   destruct H31.
   exists (eventDefinition e2).
   
   split;auto.
   assert (In (x1, eventDefinition e2) ((sceEventMap conf2))).
 
   apply syncFinishedMap with (conf:=conf);auto.

   unfold not;intros.
   rewrite <- chainMergeFinMap' in H33.
   contradiction.
  auto.    
  destruct H21.
  repeat match goal with
            | [ H: _ /\ _ |- _ ] => destruct H

         end.
  repeat(split;auto).
  assert (In (x1, eventDefinition e2) (sceEventMap conf2')). 
  apply sceEventMapNoChangeSync with (conf:=conf2) (e:=e1);auto.

  apply rangeDomInRev with (a:=x1);auto.

-
    
 
    
   assert (In a (raisedevents conf2) \/ ~ In a (raisedevents conf2)).
   apply excluded_middle.
   destruct H17.
   assert (~ In a (raisedevents conf1)).
   unfold not;intros.

   pose proof raisedEvInAlphabet.
      
   assert ( raisedEv M (eventDefinition e2) (eventDefinition a)).
   destruct H4.
    repeat match goal with
            | [ H: _ /\ _ |- _ ] => destruct H

           end.
    
   apply H19 with (conf:=conf) (conf':=conf2);auto.
   


   assert ( raisedEv M (eventDefinition e1) (eventDefinition a)).
   destruct H4.
    repeat match goal with
            | [ H: _ /\ _ |- _ ] => destruct H

           end.
    
    apply H19 with (conf:=conf) (conf':=conf1);auto.
    unfold not in H2.
    apply H2 with (ev1:=eventDefinition a) (ev2:=eventDefinition a);auto.
    SearchAbout events.
    apply syncEvents with (conf:=conf) (conf':=conf1) (e:=e1);auto.
      apply syncEvents with (conf:=conf) (conf':=conf2) (e:=e2);auto.

   
      apply raisedIntervalSync with (conf:=conf) (conf':=conf1) (e:=e1);auto. 
      apply raisedIntervalSync with (conf:=conf) (conf':=conf1) (e:=e1);auto.
      
   (*innerCombineFuncRaisedEvents*)
   remember H8.
   clear Heqs.
   remember H9.
   clear Heqs0.

   unfold synchrony in s;unfold synchrony in s0.
   destruct s;destruct s0.

   unfold combineFunc in H20;unfold combineFunc in H22.
   remember (constructConfigList (dom (controlstate conf)) e2 conf).
   destruct e;inversion H20.
   clear H24.
   remember (constructConfigList (dom (controlstate conf1)) e2 conf1).
   destruct e;inversion H22.
   clear H24.

   unfold constructConfigList in *.
   destruct v;inversion H20.
   clear H24.
   remember ( innerCombineFunc'''' conf (c :: v)).
   destruct o;inversion H20.
   clear H20.
   destruct v0;inversion H22.
   clear H23.
   remember (innerCombineFunc'''' conf1 (c1 :: v0) ).
   destruct o;inversion H22.
   clear H22.
   simpl. 
   rewrite <- H24 in H17;simpl in H17.  
   assert (a <> e2).
   unfold not;intros.
   rewrite H20 in H16.  assert (In e2 (raisedevents conf)).
   unfold synchrony in H8;intuition;auto. 
   contradiction.
   SearchAbout  removeEvent'.
   apply removeEventPreservation;auto.
   assert (In a (raisedevents c0)).
   SearchAbout removeEvent'.
   apply removeIn in H17;auto.    
         
   pose proof innerCombineFuncRaisedEvents.
   
     
   assert ( exists conf' : configuration M, In conf' (c :: v) /\ In a (raisedevents conf')).
   apply H25 with  (conf:=conf) (conf':=c0)  ;auto.
   destruct H26.
   destruct H26. 
   
   assert (exists sce : scenario, In sce (filter
              (fun x : scenario => inList event_definition_dec (eventDefinition e2) (alphabet x))
              (filterList (finishedscenarios conf) (dom (controlstate conf)) scenario_dec)) /\ Result x = constructConfig sce e2 conf).
   apply termL2 with (conf:=conf) (e:=e2) (lst:=c::v) ;auto.
   destruct H28.
   destruct H28.

   

   assert (dom (controlstate conf) = dom (controlstate conf1)).
  apply domControlSync with (e:=e1);auto.
  rewrite <- H30 in Heqe0.
  assert ((filter
              (fun x : scenario => inList event_definition_dec (eventDefinition e2) (alphabet x))
              (filterList (finishedscenarios conf) (dom (controlstate conf)) scenario_dec)) =
          (filter
               (fun x : scenario => inList event_definition_dec (eventDefinition e2) (alphabet x))
               (filterList (finishedscenarios conf1) (dom (controlstate conf)) scenario_dec))).
  apply   filterEqual;auto.
  unfold incl;intros. 
  apply finishedInvariantSync with (conf:=conf) (e:=e1);auto.   
  intros.
  apply  inListFalse;auto.
  unfold not;intros.

  assert (In a0 (dom (controlstate conf))).
  rewrite domControlSync with (conf':=conf1) (e:=e1);auto. 
  destruct H11.
  unfold scenarioInclusion in inclusion;unfold incl in inclusion;apply inclusion;auto.   
    
  apply H3 with (sce1:=a0) in H33;auto.    
  
  apply syncFinish with (M:=M) (conf:=conf) (conf':=conf1);auto.
  rewrite H31 in Heqe.
  rewrite H31 in H28. 
  clear H31.   

  assert (exists conf' : configuration M, Result conf' = constructConfig x0 e2 conf1).
  apply termL2' with (conf:=conf1) (e:=e2) (scs:=(filter
               (fun x : scenario => inList event_definition_dec (eventDefinition e2) (alphabet x))
               (filterList (finishedscenarios conf1) (dom (controlstate conf)) scenario_dec)) ) (lst:=c1::v0);auto.
  destruct H31.
  assert (In x1 (c1::v0)).
  apply constructIn with (l:=(filter
              (fun x : scenario => inList event_definition_dec (eventDefinition e2) (alphabet x))
              (filterList (finishedscenarios conf1) (dom (controlstate conf)) scenario_dec)) ) (e:=e2) (conf:=conf1) (x:=x0) ;auto. 
  assert (In a (raisedevents x1)).
  pose proof constructConfigRaisedIn.
  
  remember H4.
  clear Heqw.   
  destruct H4.
  repeat match goal with
            | [ H: _ /\ _ |- _ ] => destruct H

         end.
  destruct H36.
  repeat match goal with
            | [ H: _ /\ _ |- _ ] => destruct H

         end.    
  apply H33 with (conf:=conf) (conf1:=conf1) (conf':=x) (sce:=x0) (e1:=e1) (e2:=e2);auto.
  apply H46;auto.

  assert (In x0 (dom (controlstate conf))).
  apply filter_In in H28.
  destruct H28.   
  apply filterL2 in H28;auto.
  destruct corrconf .
  rewrite <-   cs_consist;auto.
  intros.
  assert (~ updateVarEv M (eventDefinition e1) v1).
  unfold not;intros.
  unfold not in H.
  apply H0 with (v1:=v1) (v2:=v1);auto.
  apply diamondDSNoChange with (e1:=e1) (e2:=e2);auto.

   assert (In x0 (dom (controlstate conf))).
  apply filter_In in H28.
  destruct H28.   
  apply filterL2 in H28;auto.
  destruct corrconf.
  rewrite <-   cs_consist;auto.

  apply filter_In in H28.
  destruct H28.
  apply reverseinListLemma in H52;auto.
  apply diamondCSNoChange with (e1:=e1);auto.
  unfold not;intros.
  assert ( In (eventDefinition e2) (alphabet x0)).
   apply filter_In in H28.
  destruct H28.
  apply reverseinListLemma in H53;auto.

  assert (In x0 (dom (controlstate conf))).
  apply filter_In in H28;destruct H28;apply filterL2 in H28;auto.   
  unfold not in H3;apply H3 with (sce1:=x0) (sce2:=x0);auto.

  
  pose proof innerRaised'.
  
  
  apply H34 with (sceList:=  (filter
             (fun x : scenario => inList event_definition_dec (eventDefinition e2) (alphabet x))
             (filterList (finishedscenarios conf1) (dom (controlstate conf)) scenario_dec))) (conf:=conf1) (l:=c1::v0) (e:=e2) ;auto.
  apply filterUniq;auto.
  apply uniqListFilter.
  Focus 2.
  destruct corrconf;intuition;auto.
  destruct H11;intuition;auto.
  exists x1;auto.   

  assert (In a (raisedevents conf1)).

   remember H7.
   clear Heqs.
   remember H10.
   clear Heqs0.

   unfold synchrony in s;unfold synchrony in s0.
   destruct s;destruct s0.

   unfold combineFunc in H19;unfold combineFunc in H21.
   remember (constructConfigList (dom (controlstate conf)) e1 conf).
   destruct e;inversion H19.
   clear H23.
   remember (constructConfigList (dom (controlstate conf2)) e1 conf2).
   destruct e;inversion H21.
   clear H23.

   unfold constructConfigList in *.
   destruct v;inversion H19.
   clear H23.
   remember ( innerCombineFunc'''' conf (c :: v)).
   destruct o;inversion H19.
   clear H19.
   destruct v0;inversion H21.
   clear H22.
   remember (innerCombineFunc'''' conf2 (c1 :: v0) ).
   destruct o;inversion H21.
   clear H21.
   simpl.
   rewrite <- H22 in H15;simpl in H15.  

   assert (a <> e1).
   unfold not;intros.
   subst.
   unfold synchrony in H7.    
   destruct H7.
   contradiction.
   SearchAbout removeEvent'.
   apply    removeEventPreservation ;auto.
   SearchAbout removeEvent'.
   apply removeIn in H15.
     
   pose proof innerCombineFuncRaisedEvents.
   
   assert ( exists conf' : configuration M, In conf' (c1 :: v0) /\ In a (raisedevents conf')).
   apply H21 with  (conf:=conf2) (conf':=c2) ;auto.
  
  
   destruct H24.
   destruct H24.
  
   assert (exists sce : scenario, In sce (filter
              (fun x : scenario => inList event_definition_dec (eventDefinition e1) (alphabet x))
              (filterList (finishedscenarios conf2) (dom (controlstate conf2)) scenario_dec)) /\ Result x = constructConfig sce e1 conf2).
   apply termL2 with (conf:=conf2) (e:=e1) (lst:=c1::v0) ;auto.
   destruct H26.
   destruct H26.

   assert (dom (controlstate conf) = dom (controlstate conf2)).
  apply domControlSync with (e:=e2);auto.
  rewrite <- H28 in Heqe0. rewrite <- H28 in H26. 
  assert ((filter
              (fun x : scenario => inList event_definition_dec (eventDefinition e1) (alphabet x))
              (filterList (finishedscenarios conf) (dom (controlstate conf)) scenario_dec)) =
          (filter
               (fun x : scenario => inList event_definition_dec (eventDefinition e1) (alphabet x))
               (filterList (finishedscenarios conf2) (dom (controlstate conf)) scenario_dec))).
  apply   filterEqual;auto.
  unfold incl;intros. 
  apply finishedInvariantSync with (conf:=conf) (e:=e2);auto.   
  intros.
  apply  inListFalse;auto.
  unfold not;intros.

  assert (In a0 (dom (controlstate conf))).
  rewrite domControlSync with (conf':=conf2) (e:=e2);auto. 
  destruct H12. 
  unfold scenarioInclusion in inclusion;unfold incl in inclusion;apply inclusion;auto.   
       
  
  apply H3 with (sce1:=a0) (sce2:=a0) in H31;auto.    
  apply syncFinish with (M:=M) (conf:=conf) (conf':=conf2);auto.
  rewrite H29 in Heqe.

  clear H29.   

  assert (exists conf' : configuration M, Result conf' = constructConfig x0 e1 conf).
  apply termL2' with (conf:=conf) (e:=e1) (scs:=(filter
               (fun x : scenario => inList event_definition_dec (eventDefinition e1) (alphabet x))
               (filterList (finishedscenarios conf2) (dom (controlstate conf)) scenario_dec)) ) (lst:=c::v);auto.
  destruct H29.
  assert (In x1 (c::v)).
  apply constructIn with (l:=(filter
              (fun x : scenario => inList event_definition_dec (eventDefinition e1) (alphabet x))
              (filterList (finishedscenarios conf2) (dom (controlstate conf)) scenario_dec)) ) (e:=e1) (conf:=conf) (x:=x0) ;auto. 
  assert (In a (raisedevents x1)).
  pose proof constructConfigRaisedIn'.
  remember H4.
  clear Heqw.   
  destruct H4.
  repeat match goal with
            | [ H: _ /\ _ |- _ ] => destruct H

         end.
  destruct H34.
  repeat match goal with
            | [ H: _ /\ _ |- _ ] => destruct H

         end.

  
  apply H31 with (conf:=conf) (conf1:=conf2) (conf'':= x) (conf':=x1) (sce:=x0) (e1:=e2) (e2:=e1);auto.
  apply H44;auto.

  assert (In x0 (dom (controlstate conf))).
  apply filter_In in H26.
  destruct H26.   
  apply filterL2 in H26;auto.
  destruct corrconf.
  rewrite <-   cs_consist;auto.
  intros.
 
  assert (~ updateVarEv M (eventDefinition e2) v1).
  unfold not;intros.
  unfold not in H1.
  apply H1 with (v1:=v1) (v2:=v1);auto.

  SearchAbout v1.
  
  apply diamondDSNoChange with (e1:=e2) (e2:=e1);auto.

   assert (In x0 (dom (controlstate conf))).
  apply filter_In in H26.
  destruct H26.   
  apply filterL2 in H26;auto.
  destruct corrconf.
  rewrite <-   cs_consist;auto.

  apply filter_In in H26.
   destruct H26.
  apply reverseinListLemma in H50;auto.
  apply diamondCSNoChange with (e1:=e2);auto.
  unfold not;intros.
  assert ( In (eventDefinition e1) (alphabet x0)).
   apply filter_In in H26.
  destruct H26.
  apply reverseinListLemma in H51;auto.

  assert (In x0 (dom (controlstate conf))).
  apply filter_In in H26;destruct H26;apply filterL2 in H26;auto.
    
  unfold not in H3;apply H3 with (sce1:=x0) (sce2:=x0);auto.
  pose proof innerRaised'.
  apply H32 with (sceList:=  (filter
             (fun x : scenario => inList event_definition_dec (eventDefinition e1) (alphabet x))
             (filterList (finishedscenarios conf2) (dom (controlstate conf)) scenario_dec))) (conf:=conf) (l:=c::v) (e:=e1) ;auto.
  apply filterUniq;auto.
  apply uniqListFilter.
  Focus 2.
  destruct corrconf;intuition;auto.
  destruct H12;intuition;auto.
  exists x1;auto.   
  
  
  
  assert (a <> e2). 
  unfold not;intros.
  subst.
  unfold synchrony in H8.
  destruct H8.
  contradiction.   
  SearchAbout raisedevents.
  apply raisedInvariantSync with (conf:=conf1) (e:=e2);auto.
   

     
Qed.


Lemma diamondRaisedAll2:  forall M (conf conf1 conf2 conf1' conf2': configuration M)  e1 e2, 
(forall v1 v2 , In v1 (dom (datastate conf)) -> In v2 (dom (datastate conf)) ->
updateVarEv M (eventDefinition e1)  v1 -> updateVarEv M (eventDefinition e2) v2 -> v1 <> v2) -> 
(forall v1 v2 , In v1 (dom (datastate conf)) -> In v2 (dom (datastate conf)) ->
updateVarEv M (eventDefinition e1)  v1 -> usedVarEv M (eventDefinition e2) v2 -> v1 <> v2) ->
(forall v1 v2 , In v1 (dom (datastate conf)) -> In v2 (dom (datastate conf)) ->
updateVarEv M (eventDefinition e2)  v1 -> usedVarEv M (eventDefinition e1) v2 -> v1 <> v2)  ->
(forall ev1 ev2, In ev1 (events M) -> In ev2 (events M) -> raisedEv M (eventDefinition e1) ev1 -> 
           eventKind ev1 = Internal -> eventKind ev2 = Internal ->      raisedEv M (eventDefinition e2) ev2 -> ev1 <> ev2) ->
(forall sce1 sce2, In sce1 (dom (controlstate conf)) -> In sce2 (dom (controlstate conf)) -> In (eventDefinition e1) (alphabet sce1) -> In (eventDefinition e2) (alphabet sce2) -> sce1 <> sce2) ->
WellFormed M ->
e1 <> e2 ->
(initialConfig conf \/ (exists conf' e, chainMerge conf' conf e)) -> synchrony conf conf1 e1 ->  synchrony conf conf2 e2 ->
synchrony conf1 conf1' e2 -> synchrony conf2 conf2' e1 ->
incl (raisedevents conf1')
     (raisedevents conf2')
.
Proof.

  intros.
  apply diamondRaisedAll1 with (conf:=conf) (conf1:=conf2) (conf2:=conf1) (e1:=e2) (e2:=e1);auto.
  intros.
  unfold not;intros;unfold not in H;apply H with (v1:=v2) (v2:=v1);auto.
  intros.
   unfold not;intros;unfold not in H2;apply H2 with (ev1:=ev2) (ev2:=ev1);auto.
    intros.
   unfold not;intros;unfold not in H3;apply H3 with (sce1:=sce2) (sce2:=sce1);auto.
Qed.

Definition filterStateUpdateAll (act: action) : bool :=
   match act with
  | StateUpdate (LExp _) e =>  true
  | _ => false
   end.


Fixpoint scenarioUpdateVarAll (sceList : list scenario) : list scenario :=
  match sceList with
  | nil => nil
  | sce::lst' => let stps := getTransitionsOfScenario sce in
                 let acts := filter (fun act => filterStateUpdateAll act) (retrieveAction stps) in
                 match acts with
                 | _ :: _ => sce :: (scenarioUpdateVarAll lst' )
                 | _ => (scenarioUpdateVarAll lst' )                
                 end
  end.


Lemma domSyncData: forall M (conf conf': configuration M) e,
    WellFormed M ->
    correct_configuration conf ->
    synchrony conf conf' e ->
    dom (datastate conf) = dom (datastate conf').
Proof.
  intros.
  destruct H0.
  rewrite <- dom2dom'.   
  rewrite ds_dom_eq. 
  assert (correct_configuration conf').
  destruct H.
  repeat match goal with
        | [ H: _ /\ _ |- _ ] => destruct H
        | [ H: exists _, _ |- _] => destruct H
            end.
 destruct H3.     
 repeat match goal with
        | [ H: _ /\ _ |- _ ] => destruct H
        | [ H: exists _, _ |- _] => destruct H
            end.
  apply termL5 with (conf:=conf) (e:=e);auto.
  split;auto.
  apply raised_wellform' ;auto.
  unfold synchrony in H1;intuition;auto.   
  destruct H0.
  rewrite <- dom2dom'.   
  rewrite ds_dom_eq0.   
  auto.
Qed.


Lemma domSyncData': forall M (conf conf': configuration M) e,
    WellFormed M ->
    correct_configuration conf ->
    synchrony conf conf' e ->
    dom2 (datastate conf) = dom2 (datastate conf').
Proof.
  intros.
  destruct H0.
  rewrite ds_dom_eq. 
  assert (correct_configuration conf').
  destruct H.
  repeat match goal with
        | [ H: _ /\ _ |- _ ] => destruct H
        | [ H: exists _, _ |- _] => destruct H
            end.
 destruct H3.     
 repeat match goal with
        | [ H: _ /\ _ |- _ ] => destruct H
        | [ H: exists _, _ |- _] => destruct H
            end.
  apply termL5 with (conf:=conf) (e:=e);auto.
  split;auto.
  apply raised_wellform' ;auto.
  unfold synchrony in H1;intuition;auto.   
  destruct H0.
  rewrite ds_dom_eq0.   
  auto.
Qed.


Lemma dsEq: forall (ds0 ds1 ds2: value_env),
    dom2 ds0 = dom2 ds1 ->
    dom2 ds0 = dom2 ds2 ->
    uniqList (dom ds0) ->
    (forall v, In v (dom ds0) -> (exists s, AIdent s = v) /\ getValue v ds1 = getValue v ds2) ->
    ds1 = ds2.
Proof.
  intro ds0;induction ds0.
  -    intros.
       destruct ds1. destruct ds2. auto.
       inversion H0.
       inversion H.
  -  intros.
     destruct ds1;inversion H.
     destruct ds2;inversion H0.
     destruct a;destruct p;destruct p0.  
     destruct p1;destruct p;destruct p0.  subst;auto. simpl in H4;simpl in H5;simpl in H7;simpl in H8;subst. 
     assert ((exists s : string, AIdent s = a1) /\
       getValue a1 ((a1, (t1, r0)) :: ds1) = getValue a1 ((a1, (t1, r1)) :: ds2)).
     apply H2 with (v:=a1);auto. simpl;intuition;auto. 
     destruct H3.      destruct H3. rewrite <- H3 in H4 ;simpl in H4.
     destruct (atom_eq_dec (AIdent x) (AIdent x)).
     inversion H4;subst;f_equal.
     apply IHds0;auto.
     inversion H1;subst;auto.
     intros.
  assert ((exists s : string, AIdent s = v) /\
          getValue v ((AIdent x, (t1, r1)) :: ds1) = getValue v ((AIdent x, (t1, r1)) :: ds2)).
  apply H2;auto.
  simpl;right;auto.
  destruct H5.
  split;auto.
  simpl in H7.
  destruct H5.   
   subst.         
   destruct (atom_eq_dec (AIdent x0) (AIdent x)).
   inversion H1;subst. subst. rewrite e0 in H3. 
 contradiction.    
  auto.    
  contradiction.
  Qed.

Lemma csEq: forall (ds0 ds1 ds2: scenario_env),
    dom ds0 = dom ds1 ->
    dom ds0 = dom ds2 ->
    uniqList (dom ds0) ->              
    (forall v, In v (dom ds0) -> getScenarioState v ds1 = getScenarioState v ds2) ->
    ds1 = ds2.
Proof.
  intro ds0;induction ds0.
  -    intros.
       destruct ds1. destruct ds2. auto.
       inversion H0.
       inversion H.
  -  intros.
     destruct ds1;inversion H.
     destruct ds2;inversion H0.
     destruct a;destruct p;destruct p0;simpl in *.      
     subst.
    assert ((if string_dec (scenarioId s3) (scenarioId s3) then Some s2 else getScenarioState s3 ds1) =
            (if string_dec (scenarioId s3) (scenarioId s3) then Some s4 else getScenarioState s3 ds2)).
    apply H2;intuition;auto.
    destruct  (string_dec (scenarioId s3) (scenarioId s3) ).
    inversion H3;f_equal;auto.
    subst.
    apply IHds0;auto.
    inversion H1;subst;auto.
    intros.
    assert ((if string_dec (scenarioId v) (scenarioId s3) then Some s4 else getScenarioState v ds1) =
            (if string_dec (scenarioId v) (scenarioId s3) then Some s4 else getScenarioState v ds2)).
    apply H2;intuition;auto.
       
    destruct (string_dec (scenarioId v) (scenarioId s3)).
    SearchAbout scenarioId.
    apply ScenarioEquivalence in e0;auto.
    subst. inversion H1;subst.     
    contradiction.
    auto.
  contradiction.     
    Qed.


     
Lemma diamondL1: forall M (conf conf1 conf2 conf1' conf2': configuration M)  e1 e2, 
(forall v1 v2 , In v1 (dom (datastate conf)) -> In v2 (dom (datastate conf)) ->
updateVarEv M (eventDefinition e1)  v1 -> updateVarEv M (eventDefinition e2) v2 -> v1 <> v2) -> 
(forall v1 v2 , In v1 (dom (datastate conf)) -> In v2 (dom (datastate conf)) ->
updateVarEv M (eventDefinition e1)  v1 -> usedVarEv M (eventDefinition e2) v2 -> v1 <> v2) ->
(forall v1 v2 , In v1 (dom (datastate conf)) -> In v2 (dom (datastate conf)) ->
updateVarEv M (eventDefinition e2)  v1 -> usedVarEv M (eventDefinition e1) v2 -> v1 <> v2)  ->
(forall ev1 ev2, In ev1 (events M) -> In ev2 (events M) -> raisedEv M (eventDefinition e1) ev1 -> 
      eventKind ev1 = Internal -> eventKind ev2 = Internal ->           raisedEv M (eventDefinition e2) ev2 -> ev1 <> ev2) ->
(forall sce1 sce2, In sce1 (dom (controlstate conf)) -> In sce2 (dom (controlstate conf)) -> In (eventDefinition e1) (alphabet sce1) -> In (eventDefinition e2) (alphabet sce2) -> sce1 <> sce2) ->
WellFormed M ->
e1 <> e2 ->
(initialConfig conf \/ (exists conf' e, chainMerge conf' conf e)) -> synchrony conf conf1 e1 ->  synchrony conf conf2 e2 ->
synchrony conf1 conf1' e2 -> synchrony conf2 conf2' e1 -> equivConf conf1' conf2'.
Proof.
 intros. 
  assert (correct_configuration  conf).
   destruct H4.

    repeat match goal with
        | [ H: _ /\ _ |- _ ] => destruct H
        | [ H: exists _, _ |- _] => destruct H
            end.
      destruct H13.

       repeat match goal with
        | [ H: _ /\ _ |- _ ] => destruct H
        | [ H: exists _, _ |- _] => destruct H
              end.

  destruct H6;destruct H6. auto. 
  destruct H6.          apply termL5' with (conf:=x) (e:=x0);intuition;auto.
  remember H6.
  clear Heqc.
  apply chainMergeInitial in c.
  destruct c.   destruct H29.
  apply  raised_wellform'  ;auto.
  apply chainMergeInitialEvent in H6;auto.   

  assert (correct_configuration conf1).
  destruct H4.

    repeat match goal with
        | [ H: _ /\ _ |- _ ] => destruct H
        | [ H: exists _, _ |- _] => destruct H
            end.
      destruct H14.

       repeat match goal with
        | [ H: _ /\ _ |- _ ] => destruct H
        | [ H: exists _, _ |- _] => destruct H
              end.
  apply termL5 with (conf:=conf) (e:=e1);auto.  
  destruct H11.
  apply  raised_wellform' ;auto.
  unfold synchrony in H7;intuition;auto.   

  
  assert (correct_configuration conf2).
  destruct H4.

    repeat match goal with
        | [ H: _ /\ _ |- _ ] => destruct H
        | [ H: exists _, _ |- _] => destruct H
            end.
      destruct H15.

       repeat match goal with
        | [ H: _ /\ _ |- _ ] => destruct H
        | [ H: exists _, _ |- _] => destruct H
              end.
  apply termL5 with (conf:=conf) (e:=e2);auto.  
  destruct H11.
  apply  raised_wellform' ;auto.
  unfold synchrony in H8;intuition;auto.

  
  
  split.
  
  pose proof diamondDSAll.
  assert (forall v, In v (dom (datastate conf)) ->
                    getValue v (datastate conf1') = getValue v (datastate conf2')).
  intros.
   apply H14 with (conf:=conf) (conf1:=conf1) (conf2:=conf2) (e1:=e1) (e2:=e2);auto.
  
   assert (dom2 (datastate conf) = dom2 (datastate conf1)).
   apply domSyncData' with (e:=e1);auto.
    assert (dom2 (datastate conf) = dom2 (datastate conf2)).
    apply domSyncData' with (e:=e2);auto.
   assert (dom2 (datastate conf1) = dom2 (datastate conf1')).
   apply domSyncData' with (e:=e2);auto.
    assert (dom2 (datastate conf2) = dom2 (datastate conf2')).
    apply domSyncData' with (e:=e1);auto.
    apply dsEq with (ds0:=datastate conf);auto.
  rewrite H16;auto.     
  rewrite H17;auto.
  
  destruct H11;auto. rewrite <- dom2dom'. rewrite ds_dom_eq.
  destruct    correct_mon;auto.
  intros.
  split;auto.
  
  SearchAbout (AIdent _).
  apply tyEnvVar with (env:= datastate conf);auto.
  destruct H11;auto.   

  split.
    pose proof diamondCSAll.
  assert (forall sce, In sce (dom (controlstate conf)) ->
                      getScenarioState sce (controlstate conf1') = getScenarioState sce (controlstate conf2')).
  intros.
  apply H14   with (conf:=conf) (conf1:=conf1) (conf2:=conf2) (e1:=e1) (e2:=e2);auto.
  assert (dom (controlstate conf) = dom (controlstate conf1)).
  
   apply domControlSync with (e:=e1);auto.
    assert (dom (controlstate conf) = dom (controlstate conf2)).
    apply domControlSync with (e:=e2);auto.
   assert (dom (controlstate conf1) = dom (controlstate conf1')).
   apply domControlSync with (e:=e2);auto.
    assert (dom (controlstate conf2) = dom (controlstate conf2')).
    apply domControlSync with (e:=e1);auto.
 apply  csEq with (ds0:=(controlstate conf));auto.
 rewrite H16;auto.     rewrite H17;auto. destruct H11;auto.
 split.
   
 apply diamondRaisedAll2 with (conf:=conf) (conf1:=conf1) (conf2:=conf2) (e1:=e1) (e2:=e2);auto.
 split.
 apply diamondRaisedAll1 with (conf:=conf) (conf1:=conf1) (conf2:=conf2) (e1:=e1) (e2:=e2);auto.

 split.
 SearchAbout (Permutation (finishedscenarios _) (finishedscenarios _)).
 apply diamondFinAll  with (conf:=conf) (conf1:=conf2) (conf2:=conf1) (e1:=e2) (e2:=e1);auto. 
 intros.
 unfold not in *;intros;apply H with (v1:=v2) (v2:=v1);auto.
 unfold not in *;intros;apply H2 with (ev1:=ev2) (ev2:=ev1);auto.
  unfold not in *;intros;apply H3 with (sce1:=sce2) (sce2:=sce1);auto.

  split.
  SearchAbout (incl (exportedevents _) (exportedevents _)).   
  apply diamondExportedAll2  with (conf:=conf) (conf1:=conf1) (conf2:=conf2) (e1:=e1) (e2:=e2);auto.
  split.
  apply diamondExportedAll1  with (conf:=conf) (conf1:=conf1) (conf2:=conf2) (e1:=e1) (e2:=e2);auto.

  SearchAbout (Permutation (sceEventMap _) (sceEventMap _)).
  apply diamondFinMapAll with  (conf:=conf) (conf1:=conf2) (conf2:=conf1) (e1:=e2) (e2:=e1);auto. 

   intros.
 unfold not in *;intros;apply H with (v1:=v2) (v2:=v1);auto.
 unfold not in *;intros;apply H2 with (ev1:=ev2) (ev2:=ev1);auto.
  unfold not in *;intros;apply H3 with (sce1:=sce2) (sce2:=sce1);auto.
  
Qed.





Lemma raisedEventLedTo': forall M (conf conf' : configuration M) re,
    chainMerge conf conf' re ->
    transEvMapProp M ->
    stpStMapEquiv' M ->
    correctStateEvStepMap' M ->
    stateEvDefInstanceMapEquiv M ->
    stateEvDefInstanceMapEquivEListProp M ->
    stateSceIn M ->
    (forall re', In re' (raisedevents conf') -> staticEventLeadTo' M (eventDefinition re) (eventDefinition re) (eventDefinition re')).
Proof.
  intros. 
  rename H0 into evMapProp. rename H1 into mapEquiv. rename H2 into stpMap. rename H3 into stMapEq.
  rename H4 into sei. rename H5 into sci. rename H6 into H0. 
  generalize dependent re'. 
  induction H. 
  rename event into ev. 
  - intros.
    rename H0 into tempH.
    rename H1 into H0.
    rename tempH into H1. 
    apply staticLeadBasicCase'. unfold raiseAction. remember H1. clear Heqs. remember H. clear Heqi. rename s into ss.
    rename i into ii. 
    unfold synchrony in H1.
    destruct H1.
    unfold combineFunc in H2.
    remember ( constructConfigList (dom (controlstate conf)) ev conf).
    destruct e;inversion H2.
    unfold constructConfigList in Heqe.
    destruct v;inversion H2.
    clear H4.
    clear H2.

    destruct v.
    
     remember (mergeConfigFunc' conf conf c).
     destruct e;inversion H5.
     unfold removeEventFromConf in H3.
     rewrite <- H3 in H0. simpl in H0.
     remember H0. clear Heqi.
     apply removeIn in H0.
     assert (re' <> ev).
     unfold not. intros. rewrite H2 in i. 
     
     apply removeNotIn in i. auto.
     SearchAbout mergeConfigFunc'.
      pose proof mergeConfigFuncRaisedEvent.
     assert (In re' (raisedevents conf) \/ In re' (raisedevents c)).
     apply H4 with (v:=v) (conf:=conf);auto.
     apply initialConfigRaisedSingle with (re:=ev);auto.
     destruct H6.
     apply initialConfigRaisedSingle with (re':=re') in H1;auto.
     contradiction. 

      pose proof termL2.
    assert ( exists sce : scenario, In sce (filter
              (fun x : scenario =>
               inList event_definition_dec (eventDefinition ev) (alphabet x))
              (filterList (finishedscenarios conf) (dom (controlstate conf))
                          scenario_dec)) /\ Result c = constructConfig sce ev conf).
    apply H7 with (lst:=c::nil);auto.
    split;auto. left;auto.
    destruct H8. destruct H8.
    pose proof constructConfigRaised. exists x. split.
    Print   triggerSce.
    apply  basic_ts;auto.
     apply filter_In in H8.
     destruct H8. apply filterL2 in H8;auto.
     destruct H. destruct H. rewrite <- cs_consist ;auto.
      apply filter_In in H8.
     destruct H8. SearchAbout inList. apply reverseinListLemma in H11;auto. 

     split.
     
    apply filter_In in H8.
     destruct H8. apply filterL2 in H8;auto.
   destruct H. destruct H. rewrite <- cs_consist ;auto. 
       
   apply H10 with (conf:=conf) (conf':=c);auto. 
   Focus 2.
     apply filter_In in H8.
     destruct H8. apply filterL2 in H8;auto. 
     eapply initialConfigRaisedSingle;auto.
     apply H1. auto.

     
    remember (innerCombineFunc'''' conf (c0::v)).
    destruct o;inversion H5.
    remember (mergeConfigFunc' conf c c1).
    destruct e;inversion H5. subst. clear H5.
    unfold mergeConfigFunc' in Heqe0.
    remember (mergeDataStateFunc (datastate conf) (datastate c) (datastate c1) ).
    destruct e;inversion Heqe0.
    remember (mergeControlStateFunc (controlstate conf) (controlstate c) (controlstate c1)).
    destruct e;inversion Heqe0.
    rewrite H5 in H0. simpl in H0;subst.
    remember H0. clear Heqi.
    apply removeIn in i.
   
    assert (re' <> ev).
    unfold not. intros. rewrite H2 in H0.
    apply removeNotIn in H0. inversion H0.

     rewrite in_app_iff in i.
    destruct i. Focus 2. 
    pose proof innerCombineFuncRaisedEvents.
    assert (~ In re' (raisedevents conf)).
    apply initialConfigRaisedSingle with (re:=ev);auto. 
    assert (exists conf'' : configuration M, In conf'' (c0::v) /\ In re' (raisedevents conf'')). 
    apply H6 with (conf':=c1) (conf:=conf);auto.

    destruct H8.
    destruct H8.
    pose proof termL2.
    assert (exists sce : scenario, In sce (filter
              (fun x : scenario =>
               inList event_definition_dec (eventDefinition ev) (alphabet x))
              (filterList (finishedscenarios conf) (dom (controlstate conf))
                          scenario_dec)) /\ Result x = constructConfig sce ev conf).
    apply H10 with (lst:=(c::c0::v));auto.
    split;auto. right;auto.
    destruct H11. destruct H11.
    exists x0.
    split.

    apply  basic_ts;auto.
     apply filter_In in H11.
     destruct H11. apply filterL2 in H11;auto.
     destruct H. destruct H. rewrite <- cs_consist ;auto.
      apply filter_In in H11.
      destruct H11.  apply reverseinListLemma in H13;auto.
      
    
      split.
      
    apply filter_In in H11.
    destruct H11.
    apply filterL2 in H11.
    destruct H.
    destruct H.
    rewrite <- cs_consist;auto.
    pose proof constructConfigRaised.
    apply H13 with (conf:=conf) (conf':=x);auto. destruct H;auto.
    apply filter_In in H11.
    destruct H11. apply filterL2 in H11;auto.
   (* apply filterL2 in H4.*)

    pose proof termL2.
    assert ( exists sce : scenario, In sce (filter
              (fun x : scenario =>
               inList event_definition_dec (eventDefinition ev) (alphabet x))
              (filterList (finishedscenarios conf) (dom (controlstate conf))
                          scenario_dec)) /\ Result c = constructConfig sce ev conf).
    apply H6 with (lst:=c::c0::v);auto.
    split;auto. left;auto.
    destruct H7. destruct H7.
    pose proof constructConfigRaised. exists x. split.

    apply  basic_ts;auto.
     apply filter_In in H7.
     destruct H7. apply filterL2 in H7;auto.
     destruct H. destruct H. rewrite <- cs_consist ;auto.
      apply filter_In in H7.
      destruct H7.  apply reverseinListLemma in H10;auto.
   split. 
      
    

    apply filter_In in H7.
     destruct H7. apply filterL2 in H7;auto.
   destruct H. destruct H. rewrite <- cs_consist ;auto. 
       
   apply H9 with (conf:=conf) (conf':=c);auto.
   Focus 2.
     apply filter_In in H7.
     destruct H7. apply filterL2 in H7;auto. 
     eapply initialConfigRaisedSingle;auto.
     apply H1. auto.
   

  -  intros. 
    assert (In re' (raisedevents conf') \/ ~ In re' (raisedevents conf')).
    apply excluded_middle.
    destruct H2.
+
    apply IHchainMerge;auto.
+    
    apply staticLeadTransit' with (ev2:=eventDefinition event2);auto.
    apply IHchainMerge;auto.
    unfold synchrony in H0. destruct H0;auto.
    unfold raiseAction. 
    
    pose proof domControlSyncChain.
     rename H3 into domCSEq. 
    assert (dom (controlstate conf) = dom (controlstate conf')).
   
    apply domCSEq with (e:=event1);auto.
    rename H3 into dcc.
    assert (M = M).
    eapply monitorObjNoChangeChain with (e:=event1);eauto.
    rename H3 into monObjEq. 
    unfold synchrony in H0.
    destruct H0.
    unfold combineFunc in H3.
    remember ( constructConfigList (dom (controlstate conf')) event2 conf').
    destruct e;inversion H3.
    unfold constructConfigList in Heqe.
    destruct v;inversion H3.
    clear H5.
    clear H3.

    destruct v. 

    remember (mergeConfigFunc' conf' conf' c).
     destruct e;inversion H6.
     unfold removeEventFromConf in H4.
     rewrite <- H4 in H1. simpl in H1.
     remember H1. clear Heqi.
     apply removeIn in H1.
     assert (re' <> event2).
     unfold not. intros. rewrite H3 in i. 
     
     apply removeNotIn in i. auto.
      pose proof mergeConfigFuncRaisedEvent.
     assert (In re' (raisedevents conf') \/ In re' (raisedevents c)).
     apply H5 with (v:=v) (conf:=conf');auto.
     destruct H7.
     contradiction. 
    
      pose proof termL2.
    assert ( exists sce : scenario, In sce (filter
              (fun x : scenario =>
               inList event_definition_dec (eventDefinition event2) (alphabet x))
              (filterList (finishedscenarios conf') (dom (controlstate conf'))
                          scenario_dec)) /\ Result c = constructConfig sce event2 conf').
    apply H8 with (lst:=c::nil);auto.
    split;auto. left;auto.
    destruct H9. destruct H9.
    pose proof constructConfigRaised.

     

    exists x. remember H.  clear Heqc0. split.
    Print triggerSce. 
    
    apply induction_ts with (e2:=eventDefinition event2);auto.
    Focus 2.
    apply basic_ts. 
      apply filter_In in H9.
     destruct H9. apply filterL2 in H9;auto.
     assert (correct_configuration conf').
     remember H.
     clear Heqc1.
     apply chainMergeInitial in c0.
     destruct c0.
     apply termL5' with (conf:=conf) (e:=event1);auto.
     apply chainMergeInitialEvent in c1.
     destruct H13.
     apply raised_wellform';auto.
     destruct H13.
   
     
     rewrite <- cs_consist ;auto.
           
       apply filter_In in H9.
       destruct H9.
      apply reverseinListLemma in H12;auto.
    SearchAbout staticEventLeadTo. 
    apply raisedEventLedTo with (conf:=conf) (conf':=conf');auto.
      
    Check monitorObjNoChangeChain. 

    split.
    
    destruct H. destruct H.
    destruct H. rewrite <- cs_consist. 
     apply filter_In in H9.
     destruct H9. apply filterL2 in H;auto.
     rewrite <- domControlSyncChain with (conf:=conf) (e:=event) in H;auto.
     
        apply chainMergeInitial in H. destruct H.  destruct H.
        rewrite <- cs_consist ;auto.
        rewrite dcc.
        
          apply filter_In in H9.
          destruct H9. apply filterL2 in H;auto.
    pose proof monitorObjNoChangeChain.
    assert (M = M).
    eapply H12 with (e:=event1);eauto.
    
            
   apply H11 with (conf:=conf') (conf':=c);(try rewrite <- H13;auto). 
   apply filter_In in H9.
    destruct H9.
    apply filterL2 in H9;auto.  

    remember (innerCombineFunc'''' conf' (c0::v)).
    destruct o;inversion H6. 
    remember (mergeConfigFunc' conf' c c1).
    destruct e;inversion H6. subst. clear H4;clear H6.
    unfold mergeConfigFunc' in Heqe0.
    remember (mergeDataStateFunc (datastate conf') (datastate c) (datastate c1) ).
    destruct e;inversion Heqe0.
    remember (mergeControlStateFunc (controlstate conf') (controlstate c) (controlstate c1)).
    destruct e;inversion Heqe0.
    rewrite H5 in H1;simpl in H1;subst.
    remember H1. clear Heqi.
    apply removeIn in i.
    assert (re' <> event2).
    unfold not. intros. rewrite <- H3 in H0.
    contradiction. 
    
     rewrite in_app_iff in i.
    destruct i. Focus 2. 
    pose proof innerCombineFuncRaisedEvents.
     
    assert (exists conf'' : configuration M, In conf'' (c0::v) /\ In re' (raisedevents conf'')). 
    apply H6 with (conf':=c1) (conf:=conf');auto.
    destruct H7.
    destruct H7.
    pose proof termL2.
    assert (exists sce : scenario, In sce (filter
              (fun x : scenario =>
               inList event_definition_dec (eventDefinition event2) (alphabet x))
              (filterList (finishedscenarios conf') (dom (controlstate conf'))
                          scenario_dec)) /\ Result x = constructConfig sce event2 conf').
    apply H9 with (lst:=(c::c0::v));auto.
    split;auto. right;auto.
    destruct H10. destruct H10.

    
    exists x0.
    split.
    Print triggerSce. 
    apply induction_ts with (e2:=eventDefinition event2);auto.
     apply raisedEventLedTo with (conf:=conf) (conf':=conf');auto.    
     apply basic_ts;auto.

     apply filter_In in H10.
     destruct H10.
     apply filterL2 in H10.
     assert (correct_configuration conf').
    apply termL5' with (conf:=conf) (e:=event1);auto.      
    remember H.
    clear Heqc2.
    apply chainMergeInitial in c2.
    destruct c2.
    destruct H13.
    apply    raised_wellform';auto.
    apply chainMergeInitialEvent in H;auto.
    destruct H13.
    rewrite <- cs_consist;auto.     
    apply filter_In in H10.
    destruct H10.     
    SearchAbout inList. apply reverseinListLemma in H12;auto.
    
   
    
    split.
    apply filter_In in H10.
    destruct H10.
    apply filterL2 in H10.
    rewrite <- dcc in H10.
     remember H. clear Heqc2. apply chainMergeInitial in c2.
    destruct c2. destruct H13.  rewrite  cs_consist in H10 ;auto.
   
    
    pose proof monitorObjNoChangeChain.
    assert (M = M).
    eapply H12 with (e:=event1);eauto. 
    pose proof constructConfigRaised.
   
    
    apply H14 with (conf:=conf') (conf':=x);(try rewrite <- H13;auto);auto.
     apply filter_In in H10.
    destruct H10.
    apply filterL2 in H10;auto.
    

    pose proof termL2.
    assert ( exists sce : scenario, In sce (filter
              (fun x : scenario =>
               inList event_definition_dec (eventDefinition event2) (alphabet x))
              (filterList (finishedscenarios conf') (dom (controlstate conf'))
                          scenario_dec)) /\ Result c = constructConfig sce event2 conf').
    apply H6 with (lst:=c::c0::v);auto.
    split;auto. left;auto.
    destruct H7. destruct H7.
    pose proof constructConfigRaised. exists x.


    split.


     apply induction_ts with (e2:=eventDefinition event2);auto.
     apply raisedEventLedTo with (conf:=conf) (conf':=conf');auto.    
     apply basic_ts;auto.

     apply filter_In in H7.
     destruct H7.
     apply filterL2 in H7.
     assert (correct_configuration conf').
    apply termL5' with (conf:=conf) (e:=event1);auto.      
    remember H.
    clear Heqc2.
    apply chainMergeInitial in c2.
    destruct c2.
    destruct H11.
    apply    raised_wellform';auto.
    apply chainMergeInitialEvent in H;auto.
    destruct H11.
    rewrite <- cs_consist;auto.     
    apply filter_In in H7.
    destruct H7.     
     apply reverseinListLemma in H10;auto.
    

    split.
    assert (In x (dom (controlstate conf'))).
    apply filter_In in H7. destruct H7. apply filterL2 in H7;auto.
    rewrite <- domControlSyncChain with (conf:=conf) (e:=event1) in H10;auto. 
    apply chainMergeInitial in H. destruct H.  destruct H.
    rewrite <- cs_consist ;auto. 
    pose proof monitorObjNoChangeChain.
    assert (M = M).
    eapply H10 with (e:=event1);eauto.
    
    apply H9 with (conf:=conf') (conf':=c);(try rewrite <- H11;auto);auto.
    apply filter_In in H7.
    destruct H7.
    apply filterL2 in H7;auto.
 
Qed.


(*Lemma no_lead_case_rev': forall e ev1 ev2 mon,  staticEventLeadTo' mon e ev1 ev2 ->
                          (exists sce : scenario,
                             triggerSce mon e sce /\ In sce (scenarios mon) /\
                             (exists (tr : step) (act : action) (exprs : list expr),
                                In tr (getTransitionsOfScenario sce) /\
                                In act (transitionIntoBasicActionList (stepActions tr)) /\
                                act = RaiseStmt (eventId ev2) exprs /\ ev1 = event (stepEvent tr))) \/ (exists ev3, (exists sce : scenario,
                             triggerSce mon e sce /\ In sce (scenarios mon) /\
                             (exists (tr : step) (act : action) (exprs : list expr),
                                In tr (getTransitionsOfScenario sce) /\
                                In act (transitionIntoBasicActionList (stepActions tr)) /\
                                act = RaiseStmt (eventId ev2) exprs /\ ev3 = event (stepEvent tr)))/\ staticEventLeadTo' mon e ev1 ev3).
Proof.
  intros;induction H.
  left;auto.
  right.
  destruct  IHstaticEventLeadTo'1.
  destruct  IHstaticEventLeadTo'2.
  exists ev2. split;auto.
  destruct H2. 
  exists x. destruct H2.  split;auto.
  eapply staticLeadTransit'. apply H.  auto.
  destruct (IHstaticEventLeadTo'2).
 
  exists ev2. split;auto.
  destruct H2. destruct H2.
  exists x. split;auto. 
  eapply staticLeadTransit'. apply H.  auto.
Qed.*)

Lemma fr_in: forall l stp act,
    In stp l ->
    In act ((transitionIntoBasicActionList (stepActions stp))) ->
    In act  (fold_right
       (fun (stp : step) (lst : list action) =>
          transitionIntoBasicActionList (stepActions stp) ++ lst) [] l).
Proof.
  intro l;induction l.
  - intros. inversion H.
  - intros. simpl in  *.
    destruct H.
    subst.
    apply in_app_iff. left;auto.
    apply in_app_iff. right. apply IHl with (stp:=stp);auto.
Qed.

Lemma scenarioRaiseIn: forall l v x,
    In x l ->
    (exists tr act exprs,
       In tr (getTransitionsOfScenario x) /\
         In act (transitionIntoBasicActionList (stepActions tr)) /\
         act = RaiseStmt (eventId v) exprs) ->
    In x (scenarioRaise l v).
Proof.
  intro l;induction l;intros.
  - inversion H.
  - simpl in *.
    destruct H.
    subst.
    remember (filter (fun act : action => filterRaiseStmt act (eventId v))
                     (retrieveAction (getTransitionsOfScenario x))).
    destruct l0.
    repeat match goal with
        | [ H: _ /\ _ |- _ ] => destruct H
        | [ H: exists _, _ |- _] => destruct H
         end.
    assert (In x1 (filter (fun act : action => filterRaiseStmt act (eventId v))
                         (retrieveAction (getTransitionsOfScenario x)))).
    apply filter_In;auto.
    split.
    unfold  getTransitionsOfScenario in *.
    unfold  retrieveAction.
    apply fr_in with (stp:=x0);auto.
    rewrite H1. simpl.  destruct ( string_dec (eventId v) (eventId v));auto.
   rewrite <- Heql0 in H2.
   inversion H2.
   left;auto.
   remember (filter (fun act : action => filterRaiseStmt act (eventId v))
                    (retrieveAction (getTransitionsOfScenario a))).
   destruct l0.
   apply IHl;auto.
   right.
   apply IHl;auto.    

Qed.


       

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



SearchAbout sceEventMap.
SearchAbout alphabet.



Lemma usedEventLedTo'''': forall M (conf conf' : configuration M) re e1 e2 ,
    chainMerge conf conf' re ->
    WellFormed M ->
     (staticEventLeadTo' M (eventDefinition re) e1 e2) ->
    
     ((exists re', eventDefinition re' = e1 /\ In re' (raisedevents conf'))) ->
     traceAlphabetIn M ->
     noMultAlphabet'' M ->
     importedNoCommonAlphabet'' M ->
     raiseInternal M ->
    ~((exists re', eventDefinition re' = e2 /\ In re' (raisedevents conf'))) /\
    ~ (In e2 (range (sceEventMap conf'))).  
Proof.
    intros.
    generalize dependent conf.
    generalize dependent conf'.
    induction H1.
    - rename H3 into tam. rename H4 into nma; rename H5 into inma. rename H6 into rim. intros.
      
       assert (correct_configuration conf).
    apply chainMergeInitial in H1.  destruct H1;auto.
    assert (correct_configuration conf').
    destruct H0.
      repeat match goal with
        | [ H: _ /\ _ |- _ ] => destruct H
        | [ H: exists _, _ |- _] => destruct H
             end.
      destruct H6.
      apply termL5' with (conf:=conf) (e:=re);intuition;auto.
      apply chainMergeInitialEvent in H1.
      destruct H3.
      apply raised_wellform' ;auto.
      rename H3 into corr;rename H4 into corr'. 
      
    unfold not;intros.
    repeat match goal with
        | [ H: _ /\ _ |- _ ] => destruct H
        | [ H: exists _, _ |- _] => destruct H
          end.   
    subst.
    split.
    intros.
    unfold raiseAction in H.
     repeat match goal with
        | [ H: _ /\ _ |- _ ] => destruct H
        | [ H: exists _, _ |- _] => destruct H
          end.        
     subst.
    
     assert (exists (ev : event_definition) (sce : scenario) (tr : step) (act : action) 
  (exprs : list expr),
    In (sce, ev) (sceEventMap conf') /\
    In tr (getTransitionsOfScenario sce) /\
    In act (transitionIntoBasicActionList (stepActions tr)) /\
    act = RaiseStmt (eventId (eventDefinition x0)) exprs /\ ev = event (stepEvent tr)).
     apply chainMergeRaised with (conf:=conf) (e:=re);auto.
     destruct H0;intuition;auto.      destruct H0;intuition;auto.    
     repeat match goal with
        | [ H: _ /\ _ |- _ ] => destruct H
        | [ H: exists _, _ |- _] => destruct H
          end.  
     assert (In x5 (finishedscenarios conf')).
     apply chainMergeFinMap';auto.
     exists x3;auto.

     subst. 
     assert ( (stepEvent x2) <>  (stepEvent x6)).
     unfold not;intros.
     rewrite <- H11 in H2.
     pose proof noDupEventDefinition''.
     assert ((forall re0 : raisedEvent,
         In re0 (raisedevents conf') ->
         ~
         (exists ev : event_definition,
            In ev (range (sceEventMap conf')) /\ eventDefinition re0 = ev)) /\
        (forall re0 re' : raisedEvent,
         In re0 (raisedevents conf') ->
         In re' (raisedevents conf') -> re0 <> re' -> eventDefinition re0 <> eventDefinition re')).
     destruct H0.
     repeat match goal with
        | [ H: _ /\ _ |- _ ] => destruct H
        | [ H: exists _, _ |- _] => destruct H
          end.  
     apply H12 with (conf:=conf) (re:=re);intuition;auto.
     split;auto. apply noMultIn;auto. apply noMultImportedIn;auto.
     destruct H14.
     apply H14 with (re0:=x) in H3;auto. 
     unfold not in H3;apply H3.
     exists (event (stepEvent x2)).
     split;auto.
     SearchAbout range. apply rangeDomInRev with (a:=x5);auto.
     unfold getTransitionsOfScenario in *.
          
     assert (x1 = x5 \/ x1 <> x5).
     apply excluded_middle.
     destruct H12.
     subst.
    
     assert (eventDefinition re = event (stepEvent x6) \/ ~ (eventDefinition re = event (stepEvent x6))).
     apply excluded_middle.
     destruct H12.
     unfold importedNoCommonAlphabet'' in inma.
     unfold not in inma.      
     apply inma with (e1:=event (stepEvent x6)) (e2:=event (stepEvent x2));auto.
     rewrite <- H12.
     destruct corr.
     apply  raise_in;auto.
     apply chainMergeInitialEvent in H1;auto.
     rewrite <- H12.
     SearchAbout Imported.
     apply chainMergeRuleImport with (M:=M) (conf:=conf) (conf':=conf') (e:=re);auto.
     rewrite <- H12.
     SearchAbout staticEventLeadTo.
     rewrite <- H9.
     SearchAbout  staticEventLeadTo.
     destruct H0.
       repeat match goal with
        | [ H: _ /\ _ |- _ ] => destruct H
        | [ H: exists _, _ |- _] => destruct H
              end.
      destruct H16.        
     apply raisedEventLedTo with (conf:=conf) (conf':=conf') (re:=re);intuition;auto.
     intros.
     rewrite <- H12 in H14. rewrite <- H9 in H14.
     assert (eventKind (eventDefinition x) = Internal).
     SearchAbout Internal.
     apply raisedInterval with (conf:=conf) (conf':=conf') (e:=re);auto.
     destruct H0;intuition;auto.
     assert (eventKind (eventDefinition re) = Imported).
     apply chainMergeRuleImport with (M:=M) (conf:=conf) (conf':=conf') (e:=re);auto.
     rewrite <- H14 in H15. rewrite H16 in H15;inversion H15.
     exists x5;split;auto.
     split.
     rewrite <- H12.
     
     rewrite <- H12 in H2.
     
     apply sceEventMapAlphabet with  (conf0:=conf') (sce:=x5);auto.
     rewrite <- H9.
    
     apply basic_ts;auto.
     unfold traceAlphabetIn in tam.
     rewrite H9. apply tam;auto.

     unfold noMultAlphabet'' in nma.
     apply  nma with (e:=eventDefinition re) (e1:=event (stepEvent x2)) (e2:=event (stepEvent x6)) ;auto.
      destruct corr.
     apply  raise_in;auto.
     apply chainMergeInitialEvent in H1;auto.
     rewrite <- H9.
      destruct H0.
       repeat match goal with
        | [ H: _ /\ _ |- _ ] => destruct H
        | [ H: exists _, _ |- _] => destruct H
              end.
      destruct H16.        
     apply raisedEventLedTo with (conf:=conf) (conf':=conf') (re:=re);intuition;auto.     
     SearchAbout staticEventLeadTo.
     assert (In (event (stepEvent x6)) (range (sceEventMap conf'))).
     SearchAbout range.
     apply rangeDomInRev with (a:=x5);auto.
     destruct H0.
      repeat match goal with
        | [ H: _ /\ _ |- _ ] => destruct H
        | [ H: exists _, _ |- _] => destruct H
              end.
      destruct H17.   
     apply usedEventLedTo with (conf:=conf) (re:=re) in H14;intuition;auto.
     repeat(split;auto).      apply chainMergeInitialEvent in H1;auto.
     unfold not;intros.

     rewrite <- H9 in H14. 
     pose proof noDupEventDefinition''.
     assert ((forall re0 : raisedEvent,
         In re0 (raisedevents conf') ->
         ~
         (exists ev : event_definition,
            In ev (range (sceEventMap conf')) /\ eventDefinition re0 = ev)) /\
        (forall re0 re' : raisedEvent,
         In re0 (raisedevents conf') ->
         In re' (raisedevents conf') -> re0 <> re' -> eventDefinition re0 <> eventDefinition re')).
     destruct H0.
     repeat match goal with
        | [ H: _ /\ _ |- _ ] => destruct H
        | [ H: exists _, _ |- _] => destruct H
          end.  
     apply H15 with (conf:=conf) (re:=re);intuition;auto.
     split. apply noMultIn;auto. apply noMultImportedIn;auto.
     destruct H16.
     apply H16 with (re0:=x) in H3;auto. 
     unfold not in H3;apply H3.
     exists (eventDefinition x).
     split;auto.
     rewrite H14.  apply rangeDomInRev with (a:=x5);auto.
     exists x5.
     split;auto.
     
     split.
      unfold traceAlphabetIn in tam.
      apply basic_ts;auto.
     apply basic_ts;auto.        

     destruct H0.
          
     repeat match goal with
        | [ H: _ /\ _ |- _ ] => destruct H
        | [ H: exists _, _ |- _] => destruct H
            end.
     unfold noDupRaise'' in H17.
     assert (In (eventDefinition x0) (events M)).
     destruct corr'.
     apply raise_in;auto.      
     apply H17 in H22.

     destruct H22.

     assert (eventKind (eventDefinition x0) = Internal).
     SearchAbout Internal.
     apply raisedInterval with (M:=M) (conf:=conf) (conf':=conf') (e:=re);auto.
     apply H22 with (sce1:=x1) (sce2:=x5) in H24;auto.
     apply H24.
     exists (eventDefinition re).
     split;auto.
     destruct corr.
     apply raise_in;auto.
     apply chainMergeInitialEvent in H1;auto.      
     split;auto.
     assert (eventDefinition re = event (stepEvent x6) \/ ~ (eventDefinition re = event (stepEvent x6))).
     apply excluded_middle.
     destruct H25.
     rewrite <- H25 in H2.
     apply basic_ts;auto.
     destruct corr'.
     rewrite <- cs_consist. 
     unfold scenarioInclusion in inclusion;unfold incl in inclusion;apply inclusion;auto.
     SearchAbout sceEventMap.
     apply  sceEventMapAlphabet with (sce:=x5) (conf0:=conf');auto.
     apply induction_ts with (e2:=event (stepEvent x6));auto.
     Focus 2.
     apply basic_ts;auto.
         destruct corr'.
     rewrite <- cs_consist. 
     unfold scenarioInclusion in inclusion;unfold incl in inclusion;apply inclusion;auto.
     
     apply  sceEventMapAlphabet with (sce:=x5) (conf0:=conf');auto.
     SearchAbout staticEventLeadTo.

     assert (In (event (stepEvent x6)) (range (sceEventMap conf'))).
     apply rangeDomInRev with (a:=x5);auto.
 
      destruct H16.   
     apply usedEventLedTo with (conf:=conf) (re:=re) in H26;intuition;auto.
      repeat(split;auto).      apply chainMergeInitialEvent in H1;auto.
      SearchAbout scenarioRaise.
      eapply wellForm.scenarioRaiseIn;auto. 
      unfold  getTransitionsOfScenario.
      apply H6. apply H7.
       eapply wellForm.scenarioRaiseIn;auto. 
 destruct corr'.
     rewrite <- cs_consist. 
     unfold scenarioInclusion in inclusion;unfold incl in inclusion;apply inclusion;auto.
       unfold  getTransitionsOfScenario.
      apply H8. apply H10.





      intros.

      unfold raiseAction in H.
      SearchAbout sceEventMap.

      pose proof chainMergeSceEventMap.

       repeat match goal with
        | [ H: _ /\ _ |- _ ] => destruct H
        | [ H: exists _, _ |- _] => destruct H
              end.

       subst.

       SearchAbout range.
       apply rangeDomIn in H2.
       destruct H2.

     assert (ev2 = eventDefinition re \/
       (exists
          (ev : event_definition) (sce' : scenario) (tr : step) (act : action) 
        (exprs : list expr),
          In (sce', ev) (sceEventMap conf') /\
          In tr (getTransitionsOfScenario sce') /\
          In act (transitionIntoBasicActionList (stepActions tr)) /\
          act = RaiseStmt (eventId ev2) exprs /\ ev = event (stepEvent tr))).
     apply H4 with (conf:=conf) (sce:=x2);destruct H0;intuition;auto.

     destruct H8.

     assert (eventKind (eventDefinition re) = Imported).
     
     apply chainMergeRuleImport with (conf:=conf) (conf':=conf');auto.
     assert (eventKind ev2 = Internal).
     unfold raiseInternal in rim.
     assert (eventKind ev2 = Internal \/ eventKind ev2 = Exported).
      apply rim with (sce:=x0) (tr:=x1) (exprs:=x3);auto.        
     destruct corr'.
     apply raise_in_finished with (sce:=x2);auto.
     destruct H11;auto.
     destruct corr'.
     apply raisedType_finished in H2;auto.    destruct H2;auto.   rewrite H11 in H2. inversion H2. 
    
     
     rewrite H8 in H11. rewrite H11 in H10;inversion H10.

      repeat match goal with
        | [ H: _ /\ _ |- _ ] => destruct H
        | [ H: exists _, _ |- _] => destruct H
             end.
      subst.

      assert ((stepEvent x1) <> (stepEvent x6)).
      unfold not;intros.
      rewrite <- H12 in H8.
            

      pose proof noDupEventDefinition''.
     assert ((forall re0 : raisedEvent,
         In re0 (raisedevents conf') ->
         ~
         (exists ev : event_definition,
            In ev (range (sceEventMap conf')) /\ eventDefinition re0 = ev)) /\
        (forall re0 re' : raisedEvent,
         In re0 (raisedevents conf') ->
         In re' (raisedevents conf') -> re0 <> re' -> eventDefinition re0 <> eventDefinition re')).
     destruct H0.
     repeat match goal with
        | [ H: _ /\ _ |- _ ] => destruct H
        | [ H: exists _, _ |- _] => destruct H
          end.  
     apply H13 with (conf:=conf) (re:=re);intuition;auto.
     split. apply noMultIn;auto. apply noMultImportedIn;auto.
     destruct H14.
     apply H14 with (re0:=x) in H3;auto.
     apply H3.
     exists (event (stepEvent x1));split;auto.
     SearchAbout range.
     apply rangeDomInRev with (a:=x5);auto.

     
     (*x1 = x5 ...*)

      assert (x0 = x5 \/ x0 <> x5).
     apply excluded_middle.
     destruct H13.
     subst.
     assert (eventDefinition re = event (stepEvent x6) \/ ~ (eventDefinition re = event (stepEvent x6))).
     apply excluded_middle.
     destruct H13.
     unfold importedNoCommonAlphabet'' in inma.
     unfold not in inma.      
     apply inma with (e1:=event (stepEvent x6)) (e2:=event (stepEvent x1));auto.
     rewrite <- H13.
     destruct corr.
     apply  raise_in;auto.
     apply chainMergeInitialEvent in H1;auto.
     rewrite <- H13.
     apply chainMergeRuleImport with (M:=M) (conf:=conf) (conf':=conf') (e:=re);auto.
     rewrite <- H13.
     rewrite <- H9.
     destruct H0.
       repeat match goal with
        | [ H: _ /\ _ |- _ ] => destruct H
        | [ H: exists _, _ |- _] => destruct H
              end.
      destruct H16.        
     apply raisedEventLedTo with (conf:=conf) (conf':=conf') (re:=re);intuition;auto.
     intros.
     rewrite <- H13 in H14. rewrite <- H9 in H14.
     assert (eventKind (eventDefinition x) = Internal).
     apply raisedInterval with (conf:=conf) (conf':=conf') (e:=re);auto.
     destruct H0;intuition;auto.
     assert (eventKind (eventDefinition re) = Imported).
     apply chainMergeRuleImport with (M:=M) (conf:=conf) (conf':=conf') (e:=re);auto.
     rewrite <- H14 in H15. rewrite H16 in H15;inversion H15.
     exists x5;split;auto.
     split.
     rewrite <- H13.
     rewrite <- H13 in H8. 
     apply sceEventMapAlphabet with  (conf0:=conf') (sce:=x5);auto. 


     (* rewrite <- H9.
    
     apply basic_ts;auto.
     unfold traceAlphabetIn in tam.
     rewrite H9. apply tam;auto.*)

     rewrite <- H9. 
     apply basic_ts;auto.
     unfold traceAlphabetIn in tam.
     rewrite H9. apply tam;auto.


     
     unfold noMultAlphabet'' in nma.
     apply  nma with (e:=eventDefinition re) (e1:=event (stepEvent x1)) (e2:=event (stepEvent x6)) ;auto.
      destruct corr.
     apply  raise_in;auto.
     apply chainMergeInitialEvent in H1;auto.
     rewrite <- H9.
      destruct H0.
       repeat match goal with
        | [ H: _ /\ _ |- _ ] => destruct H
        | [ H: exists _, _ |- _] => destruct H
              end.
      destruct H16.        
     apply raisedEventLedTo with (conf:=conf) (conf':=conf') (re:=re);intuition;auto.     
     assert (In (event (stepEvent x6)) (range (sceEventMap conf'))).
     apply rangeDomInRev with (a:=x5);auto.
     destruct H0.
      repeat match goal with
        | [ H: _ /\ _ |- _ ] => destruct H
        | [ H: exists _, _ |- _] => destruct H
              end.
      destruct H17.   
     apply usedEventLedTo with (conf:=conf) (re:=re) in H14;intuition;auto.
     repeat(split;auto).      apply chainMergeInitialEvent in H1;auto.
     unfold not;intros.

     rewrite <- H9 in H14. 
     pose proof noDupEventDefinition''.
     assert ((forall re0 : raisedEvent,
         In re0 (raisedevents conf') ->
         ~
         (exists ev : event_definition,
            In ev (range (sceEventMap conf')) /\ eventDefinition re0 = ev)) /\
        (forall re0 re' : raisedEvent,
         In re0 (raisedevents conf') ->
         In re' (raisedevents conf') -> re0 <> re' -> eventDefinition re0 <> eventDefinition re')).
     destruct H0.
     repeat match goal with
        | [ H: _ /\ _ |- _ ] => destruct H
        | [ H: exists _, _ |- _] => destruct H
          end.  
     apply H15 with (conf:=conf) (re:=re);intuition;auto.
     split. apply noMultIn;auto. apply noMultImportedIn;auto.
     destruct H16.
     apply H16 with (re0:=x) in H3;auto. 
     unfold not in H3;apply H3.
     exists (eventDefinition x).
     split;auto.
     rewrite H14.  apply rangeDomInRev with (a:=x5);auto.
     exists x5.
     split;auto.
     
     split.
      unfold traceAlphabetIn in tam.
      apply basic_ts;auto.
     apply basic_ts;auto.        

     destruct H0.
          
     repeat match goal with
        | [ H: _ /\ _ |- _ ] => destruct H
        | [ H: exists _, _ |- _] => destruct H
            end.
     unfold noDupRaise'' in H17.
     assert (In ev2 (events M)).
     destruct corr'.
     apply raise_in_finished with (sce:=x2);auto.      
     apply H17 in H22.

     destruct H22.

     assert (eventKind ev2 = Internal).
     
     unfold raiseInternal in rim.
     assert (eventKind ev2 = Internal \/ eventKind ev2 = Exported). 
     apply rim with (sce:=x0)  (tr:=x1) (exprs:=x3);auto.
     destruct corr'.
     apply  raise_in_finished  with (sce:=x2);auto.
     destruct H24;auto.
     destruct corr'.
     apply raisedType_finished in H2;auto.   destruct H2;auto.  rewrite H24 in H2. inversion H2. 
                
     apply H22 with (sce1:=x0) (sce2:=x5) in H24;auto.
     apply H24.
     exists (eventDefinition re).
     split;auto.
     destruct corr.
     apply raise_in;auto.
     apply chainMergeInitialEvent in H1;auto.      
     split;auto.
     assert (eventDefinition re = event (stepEvent x6) \/ ~ (eventDefinition re = event (stepEvent x6))).
     apply excluded_middle.
     destruct H25.
     rewrite <- H25 in H8.
     apply basic_ts;auto.
        destruct corr'.
     rewrite <- cs_consist. 
     unfold scenarioInclusion in inclusion;unfold incl in inclusion;apply inclusion;auto.
     SearchAbout sceEventMap.
     apply chainMergeFinMap' ;auto.
     repeat(split;auto).      
     exists (eventDefinition re);auto.
     
     SearchAbout sceEventMap.
     destruct corr'. 
     apply   sceEventMapAlphabet with (sce:=x5);auto.
      apply induction_ts with (e2:=event (stepEvent x6));auto.
     Focus 2.
     apply basic_ts;auto.
         destruct corr'.
     rewrite <- cs_consist. 
     unfold scenarioInclusion in inclusion;unfold incl in inclusion;apply inclusion;auto.
        apply chainMergeFinMap' ;auto.
     repeat(split;auto).      
     exists (event (stepEvent x6));auto.
          
     apply  sceEventMapAlphabet with (sce:=x5) (conf0:=conf');auto.

     assert (In (event (stepEvent x6)) (range (sceEventMap conf'))).
     apply rangeDomInRev with (a:=x5);auto.
 
      destruct H16.   
     apply usedEventLedTo with (conf:=conf) (re:=re) in H26;intuition;auto.
      repeat(split;auto).      apply chainMergeInitialEvent in H1;auto.
      eapply wellForm.scenarioRaiseIn;auto. 
      apply H6. apply H7.
       eapply wellForm.scenarioRaiseIn;auto. 
 destruct corr'.
     rewrite <- cs_consist. 
     unfold scenarioInclusion in inclusion;unfold incl in inclusion;apply inclusion;auto.
     apply chainMergeFinMap' ;auto.
     repeat(split;auto).  exists (event (stepEvent x6));auto.
      apply H10. apply H11.

     (**)
     (*case: x1=x5*)
     
     (*x ->  x0*)
     (*sce:x5, e1 = event (stepEvent x6), e2:=  *)
     (*exists sce1 where x is raised*)
     (*sce1 is in finishedscenarios*)
     (*x0 -> x, .....triggerSce mon (eventDefinition x0) sce1*)
     (*since x0 is in pending list, sce1 should not be in finishedscenarios*)
     (*contradictioin*)
 
     
  - rename H3 into tam. rename H4 into nma; rename H5 into inma. rename H6 into rim.   intros. 
    assert (correct_configuration conf).
    apply chainMergeInitial in H3.  destruct H3;auto.
    assert (correct_configuration conf').
    destruct H0.
      repeat match goal with
        | [ H: _ /\ _ |- _ ] => destruct H
        | [ H: exists _, _ |- _] => destruct H
             end.
      destruct H7.
      apply termL5' with (conf:=conf) (e:=re);intuition;auto.
      apply chainMergeInitialEvent in H3.
      destruct H4.
      apply raised_wellform' ;auto.
    rename H4 into corr;rename H5 into corr'.       
    assert ( ~
                         (exists re' : raisedEvent,
                            eventDefinition re' = ev2 /\ In re' (raisedevents conf')) /\
                         ~ In ev2 (range (sceEventMap conf'))).

    apply  IHstaticEventLeadTo' with (conf':=conf') (conf:=conf);auto.
    destruct H4.
    split.
    unfold not;intros.
    unfold raiseAction in H.
    repeat match goal with
        | [ H: _ /\ _ |- _ ] => destruct H
        | [ H: exists _, _ |- _] => destruct H
          end.
    subst.
    assert (exists (ev : event_definition) (sce : scenario) (tr : step) (act : action) 
  (exprs : list expr),
    In (sce, ev) (sceEventMap conf') /\
    In tr (getTransitionsOfScenario sce) /\
    In act (transitionIntoBasicActionList (stepActions tr)) /\
    act = RaiseStmt (eventId (eventDefinition x)) exprs /\ ev = event (stepEvent tr)).
    destruct H0. Check chainMergeRaised. 
    apply chainMergeRaised with (conf:=conf) (e:=re);intuition;auto.
    repeat match goal with
        | [ H: _ /\ _ |- _ ] => destruct H
        | [ H: exists _, _ |- _] => destruct H
          end.   
    subst.
    assert ((stepEvent x2) <> (stepEvent x6)).
    unfold not;intros.
   
    rewrite <- H13 in H2.
   
    apply  rangeDomInRev in H2. 
    contradiction.     
    unfold getTransitionsOfScenario in *.
    assert (x1 = x5 \/ x1 <> x5).
    apply excluded_middle.
    destruct H14;subst.
    Print WellFormed.
    Print noMultAlphabet. Print noMultAlphabet'.
    assert (In x5 (finishedscenarios conf')).
    SearchAbout sceEventMap.
    apply chainMergeFinMap';auto.
    exists (event (stepEvent x6));auto.
    SearchAbout x0.     
    Print triggerSce.
    (*event (stepEvent x2) is in the alphabet of scenario x5*)
    (*triggerSce mon (event (stepEvent x2)) x5*)
    (*triggerSce mon (event (stepEvent x6)) x5*)
    
    Print WellFormed.           Print noDupRaise''.
    Print noMultAlphabet. Print noMultAlphabet'.
     assert (In (event (stepEvent x6)) (alphabet x5)).
     SearchAbout alphabet.
     destruct H0.
      repeat match goal with
        | [ H: _ /\ _ |- _ ] => destruct H
        | [ H: exists _, _ |- _] => destruct H
          end.           
      destruct H17.
      repeat match goal with
        | [ H: _ /\ _ |- _ ] => destruct H
        | [ H: exists _, _ |- _] => destruct H
          end.
      apply chainMergeSceMapAlpha with (M:=M) (conf:=conf) (conf':=conf') (e:=re);intuition;auto.
      repeat(split;auto).   apply chainMergeInitialEvent in H3;auto.
      assert (In (event (stepEvent x2)) (alphabet x5)).
      unfold traceAlphabetIn in tam.
      apply tam;auto.

      assert (eventDefinition re = event (stepEvent x6) \/ eventDefinition re <> event (stepEvent x6)).
      apply excluded_middle.
      destruct H17.
      unfold importedNoCommonAlphabet'' in inma.
      apply inma with  (e1:=event (stepEvent x6)) (e2:=eventDefinition x0); auto.
      rewrite <- H17.       
      
       apply chainMergeInitialEvent in H3.
       destruct corr.
       apply  raise_in;auto.
       rewrite <- H17.
       SearchAbout Imported.
       apply chainMergeRuleImport with (M:=M) (conf:=conf) (conf':=conf');auto.
       rewrite <- H17.        
      
       destruct H0.
         repeat match goal with
        | [ H: _ /\ _ |- _ ] => destruct H
        | [ H: exists _, _ |- _] => destruct H
          end.
         destruct H20.
                
       apply raisedEventLedTo with (conf':=conf') (conf:=conf);intuition;auto.
       rewrite <- H17. unfold not; intros.
       assert (eventKind (eventDefinition re) = Imported).
       apply chainMergeRuleImport with (M:=M) (conf:=conf) (conf':=conf');auto.
       rewrite H18 in H19.
              
       SearchAbout   Internal.
       
       assert (eventKind (eventDefinition x0) = Internal).
       destruct H0. 
       apply raisedInterval with (M:=M) (conf:=conf) (conf':=conf') (e:=re);intuition;auto.
       rewrite H20 in H19;inversion H19.
       exists x5.
       split;auto.
       rewrite <- H17.
       split;auto.
       rewrite  H17.
      
     apply sceEventMapAlphabet with  (conf0:=conf') (sce:=x5);auto.
       apply induction_ts with (e2:= (event (stepEvent x2)));auto.
       Focus 2.

     apply basic_ts;auto.
       apply staticEventTwo with (e:=eventDefinition re);auto.

       unfold noMultAlphabet'' in nma.
      apply nma with  (e:=eventDefinition re) (e1:=eventDefinition x0) (e2:=event (stepEvent x6)); auto.
     
      
       apply chainMergeInitialEvent in H3.
       destruct corr.
       apply  raise_in;auto.
     
      
       destruct H0.
         repeat match goal with
        | [ H: _ /\ _ |- _ ] => destruct H
        | [ H: exists _, _ |- _] => destruct H
          end.
         destruct H20.
                
       apply raisedEventLedTo with (conf':=conf') (conf:=conf);intuition;auto.
       SearchAbout staticEventLeadTo. 
       assert (In (event (stepEvent x6)) (range (sceEventMap conf')) ).
       SearchAbout range.
       apply   rangeDomInRev with (a:=x5);auto.
       SearchAbout staticEventLeadTo.

        destruct H0.
         repeat match goal with
        | [ H: _ /\ _ |- _ ] => destruct H
        | [ H: exists _, _ |- _] => destruct H
          end.
         destruct H21.
         repeat match goal with
        | [ H: _ /\ _ |- _ ] => destruct H
        | [ H: exists _, _ |- _] => destruct H
          end.
         
       apply usedEventLedTo with (conf:=conf) (re:=re)in H18;auto.
       Focus 2.
       repeat(split;auto).
       apply chainMergeInitialEvent in H3;auto.
          destruct H18.
          rewrite H18 in H17.
          contradiction.
          auto.
          unfold not;intros.
          SearchAbout sceEventMap.
          pose proof noDupEventDefinition''.
       assert ( (forall re0 : raisedEvent,
         In re0 (raisedevents conf') ->
         ~
         (exists ev : event_definition,
            In ev (range (sceEventMap conf')) /\ eventDefinition re0 = ev)) /\
        (forall re0 re' : raisedEvent,
         In re0 (raisedevents conf') ->
         In re' (raisedevents conf') -> re0 <> re' -> eventDefinition re0 <> eventDefinition re')).
       destruct H0.
      apply H19 with (M:=M) (conf:=conf) (conf':=conf') (re:=re);intuition;auto.        
      split. apply noMultIn;auto. apply noMultImportedIn;auto.
      destruct H20.
      unfold not in H20.
      apply H20 with (re0:=x0);auto.
      exists (event (stepEvent x6));split;auto.
        apply   rangeDomInRev with (a:=x5);auto.     
      
       exists x5.
       split;auto.
       split.
     
       Print triggerSce.
       
       apply induction_ts with (e2:= (event (stepEvent x2)));auto.
        apply staticEventTwo with (e:=eventDefinition re);auto.
      apply basic_ts;auto.
       SearchAbout  triggerSce. 
       apply basic_ts;auto.
 
       
       destruct H0.
      repeat match goal with
        | [ H: _ /\ _ |- _ ] => destruct H
        | [ H: exists _, _ |- _] => destruct H
          end.
      unfold noDupRaise'' in H18.
      assert (In (eventDefinition x) (events M)).
      destruct corr'.
      apply raise_in;auto.
      apply H18 in H23.
      destruct H23.
      assert (eventKind (eventDefinition x) = Internal ).
      apply raisedInterval with (M:=M) (conf:=conf) (conf':=conf') (e:=re);auto.
      apply H23 with (sce1:=x1) (sce2:=x5) in H25;auto.
      unfold not in H25.
      apply H25.
      exists (eventDefinition re).
      split;auto.
      apply chainMergeInitialEvent in H3.
      destruct corr.
      apply  raise_in;auto.
      split;auto.
       assert (eventDefinition re = event (stepEvent x6) \/ eventDefinition re <> event (stepEvent x6)).
      apply excluded_middle.
      destruct H26.
      subst. rewrite <- H26 in H2.
      
      
      apply basic_ts ;auto.
      assert (In x5 (finishedscenarios conf')).
      SearchAbout sceEventMap.
      apply  chainMergeFinMap';auto.
      exists (eventDefinition re);auto.
      destruct corr'.
      rewrite <- cs_consist;auto.
      SearchAbout sceEventMap.
      apply sceEventMapAlphabet with (conf0:=conf');auto.
      apply induction_ts with (e2:= event (stepEvent x6));auto.
      Focus 2. apply basic_ts ;auto.
       assert (In x5 (finishedscenarios conf')).
      SearchAbout sceEventMap.
      apply  chainMergeFinMap';auto.
      exists (event (stepEvent x6));auto.
      destruct corr'.
      rewrite <- cs_consist;auto.
      apply sceEventMapAlphabet with (conf0:=conf');auto.
   

       assert (In (event (stepEvent x6)) (range (sceEventMap conf')) ).
       apply   rangeDomInRev with (a:=x5);auto.


         destruct H17.
         repeat match goal with
        | [ H: _ /\ _ |- _ ] => destruct H
        | [ H: exists _, _ |- _] => destruct H
          end.
         
         apply usedEventLedTo with (conf:=conf) (re:=re)in H27;auto.
         destruct H27.
     rewrite H27 in H26.          
     contradiction.     auto.
     repeat(split;auto).
     apply chainMergeInitialEvent in H3;auto.
     Print scenarioRaise.
     SearchAbout scenarioRaise.
     eapply wellForm.scenarioRaiseIn;auto.
     unfold getTransitionsOfScenario.
     apply H10.
     apply H11.

      eapply wellForm.scenarioRaiseIn;auto.
      assert (In x5 (finishedscenarios conf')).
      apply  chainMergeFinMap';auto.
      exists (event (stepEvent x6));auto.
      destruct corr'.
      rewrite <- cs_consist;auto.
      unfold getTransitionsOfScenario.       
      apply H6.
      apply H12.


    (*second*)



      

      unfold not;intros.
    Check chainMergeRaised. 
    SearchAbout sceEventMap.
    pose proof chainMergeSceEventMap.
    SearchAbout  range.
    apply rangeDomIn in H6.
    destruct H6.
    assert (ev3 <> eventDefinition re).
    unfold not;intros.
    unfold raiseAction in H.
    destruct H.
    destruct H.
    unfold  raiseInternal in rim.
    assert (eventKind ev3 = Internal).
     repeat match goal with
        | [ H: _ /\ _ |- _ ] => destruct H
        | [ H: exists _, _ |- _] => destruct H
            end.
     rewrite H13 in H12.
     assert (eventKind ev3 = Internal \/ eventKind ev3 = Exported).

     
     apply rim with (sce:=x0) (exprs:=x4) (tr:=x2);auto.
     rewrite  H8.     destruct corr.
     apply  raise_in ;auto.    apply chainMergeInitialEvent in H3;auto.

     destruct H15;auto. destruct corr'. apply raisedType_finished  in H6;destruct H6;auto. 
     rewrite H15 in H6;inversion H6. 

     
    rewrite H8 in H10.
    assert (eventKind (eventDefinition re) = Imported).
    SearchAbout Imported.     apply chainMergeRuleImport with (M:=M) (conf:=conf) (conf':=conf');auto.
    rewrite H10 in H11;inversion H11.
    assert (ev3 = eventDefinition re \/
       (exists
          (ev : event_definition) (sce' : scenario) (tr : step) (act : action) 
        (exprs : list expr),
          In (sce', ev) (sceEventMap conf') /\
          In tr (getTransitionsOfScenario sce') /\
          In act (transitionIntoBasicActionList (stepActions tr)) /\
          act = RaiseStmt (eventId ev3) exprs /\ ev = event (stepEvent tr))).
    apply H7 with (conf:=conf) (sce:=x);auto.
    destruct H0;intuition;auto.    destruct H0;intuition;auto.    
    destruct H9.
    contradiction.
       repeat match goal with
        | [ H: _ /\ _ |- _ ] => destruct H
        | [ H: exists _, _ |- _] => destruct H
              end.
       subst.
       unfold  raiseAction in H.
        repeat match goal with
        | [ H: _ /\ _ |- _ ] => destruct H
        | [ H: exists _, _ |- _] => destruct H
              end.    
        subst.
       
    assert ((stepEvent x3) <> (stepEvent x2)).
    unfold not;intros.
   
    rewrite H15 in H5.
   
    apply  rangeDomInRev in H9. 
    contradiction.     
    unfold getTransitionsOfScenario in *.
    assert (x0 = x1 \/ x0 <> x1).
    apply excluded_middle.
    destruct H16;subst.
    assert (In x1 (finishedscenarios conf')).
    apply chainMergeFinMap';auto.
    exists (event (stepEvent x2));auto.
    (*event (stepEvent x2) is in the alphabet of scenario x5*)
    (*triggerSce mon (event (stepEvent x2)) x5*)
    (*triggerSce mon (event (stepEvent x6)) x5*)
   
     assert (In (event (stepEvent x2)) (alphabet x1)).
     destruct H0.
      repeat match goal with
        | [ H: _ /\ _ |- _ ] => destruct H
        | [ H: exists _, _ |- _] => destruct H
          end.           
      destruct H19.
      repeat match goal with
        | [ H: _ /\ _ |- _ ] => destruct H
        | [ H: exists _, _ |- _] => destruct H
          end.
      apply chainMergeSceMapAlpha with (M:=M) (conf:=conf) (conf':=conf') (e:=re);intuition;auto.
      repeat(split;auto).   apply chainMergeInitialEvent in H3;auto.
      assert (In (event (stepEvent x3)) (alphabet x1)).
      unfold traceAlphabetIn in tam.
      apply tam;auto.

      assert (eventDefinition re = event (stepEvent x2) \/ eventDefinition re <> event (stepEvent x2)).
      apply excluded_middle.
      destruct H19.
      unfold importedNoCommonAlphabet'' in inma.
      apply inma with  (e1:=event (stepEvent x2)) (e2:=eventDefinition x5); auto.
      rewrite <- H19.       
      
       apply chainMergeInitialEvent in H3.
       destruct corr.
       apply  raise_in;auto.
       rewrite <- H19.
       apply chainMergeRuleImport with (M:=M) (conf:=conf) (conf':=conf');auto.
       rewrite <- H19.        
      
       destruct H0.
         repeat match goal with
        | [ H: _ /\ _ |- _ ] => destruct H
        | [ H: exists _, _ |- _] => destruct H
          end.
         destruct H22.
                
       apply raisedEventLedTo with (conf':=conf') (conf:=conf);intuition;auto.
       rewrite <- H19. unfold not; intros.
       assert (eventKind (eventDefinition re) = Imported).
       apply chainMergeRuleImport with (M:=M) (conf:=conf) (conf':=conf');auto.
       rewrite H20 in H21.
              
      
       
       assert (eventKind (eventDefinition x5) = Internal).
       destruct H0. 
       apply raisedInterval with (M:=M) (conf:=conf) (conf':=conf') (e:=re);intuition;auto.
       rewrite H22 in H21;inversion H21.
       exists x1.
       split;auto.
       rewrite <- H19.
       split;auto.
       rewrite H19.
       Print  sceEventMapAlphabet. 
       apply sceEventMapAlphabet with  (conf0:=conf') (sce:=x1);auto.
       apply induction_ts with (e2:= (event (stepEvent x3)));auto.
       Focus 2.  apply basic_ts;auto.
       apply staticEventTwo with (e:=eventDefinition re);auto.
      
       unfold noMultAlphabet'' in nma.
      apply nma with  (e:=eventDefinition re) (e1:=eventDefinition x5) (e2:=event (stepEvent x2)); auto.
     
      
       apply chainMergeInitialEvent in H3.
       destruct corr.
       apply  raise_in;auto.
     
      
       destruct H0.
         repeat match goal with
        | [ H: _ /\ _ |- _ ] => destruct H
        | [ H: exists _, _ |- _] => destruct H
          end.
         destruct H22.
                
       apply raisedEventLedTo with (conf':=conf') (conf:=conf);intuition;auto.
       assert (In (event (stepEvent x2)) (range (sceEventMap conf')) ).
       apply   rangeDomInRev with (a:=x1);auto.
    
        destruct H0.
         repeat match goal with
        | [ H: _ /\ _ |- _ ] => destruct H
        | [ H: exists _, _ |- _] => destruct H
          end.
         destruct H23.
         repeat match goal with
        | [ H: _ /\ _ |- _ ] => destruct H
        | [ H: exists _, _ |- _] => destruct H
          end.
         
       apply usedEventLedTo with (conf:=conf) (re:=re)in H20;auto.
       Focus 2.
       repeat(split;auto).
       apply chainMergeInitialEvent in H3;auto.
          destruct H20.
          rewrite H20 in H19.
          contradiction.
          auto.
          unfold not;intros.
          pose proof noDupEventDefinition''.
       assert ( (forall re0 : raisedEvent,
         In re0 (raisedevents conf') ->
         ~
         (exists ev : event_definition,
            In ev (range (sceEventMap conf')) /\ eventDefinition re0 = ev)) /\
        (forall re0 re' : raisedEvent,
         In re0 (raisedevents conf') ->
         In re' (raisedevents conf') -> re0 <> re' -> eventDefinition re0 <> eventDefinition re')).
       destruct H0.
      apply H21 with (M:=M) (conf:=conf) (conf':=conf') (re:=re);intuition;auto.        
      split. apply noMultIn;auto. apply noMultImportedIn;auto.
      destruct H22.
      unfold not in H22.
      apply H22 with (re0:=x5);auto.
      exists (event (stepEvent x2));split;auto.
        apply   rangeDomInRev with (a:=x1);auto.     
      
       exists x1.
       split;auto.
       split.
     
       apply induction_ts with (e2:= (event (stepEvent x3)));auto.
        apply staticEventTwo with (e:=eventDefinition re);auto.
      apply basic_ts;auto.
       apply basic_ts;auto.

       destruct H0.
      repeat match goal with
        | [ H: _ /\ _ |- _ ] => destruct H
        | [ H: exists _, _ |- _] => destruct H
          end.
      unfold noDupRaise'' in H20.
      assert (In ev3 (events M)).
       
      SearchAbout ev3.
      destruct corr'.
      apply  raise_in_finished with (sce:= x);auto.
            
  
     
      apply H20 in H25.
      destruct H25.
      assert (eventKind ev3 = Internal ).
      SearchAbout Internal.
      unfold raiseInternal in rim.

      assert ( eventKind ev3 = Internal \/ eventKind ev3 = Exported).
           
      apply rim with (exprs:=x7) (tr:=x3) (sce:=x0) ;auto.
      destruct corr'.
      apply  raise_in_finished with (sce:= x);auto.     

      destruct H27;auto.
      destruct corr'. apply raisedType_finished in H6;destruct H6;auto.
      rewrite H27 in H6;inversion H6.       
      
      apply H25 with (sce1:=x0) (sce2:=x1) in H27;auto.
      unfold not in H27.
      apply H27.
      exists (eventDefinition re).
      split;auto.
      apply chainMergeInitialEvent in H3.
      destruct corr.
      apply  raise_in;auto.
      split;auto.
       assert (eventDefinition re = event (stepEvent x2) \/ eventDefinition re <> event (stepEvent x2)).
      apply excluded_middle.
      destruct H28.
      subst. rewrite <- H28 in H9.
      
      
      apply basic_ts ;auto.
      assert (In x1 (finishedscenarios conf')).
      apply  chainMergeFinMap';auto.
      exists (eventDefinition re);auto.
      destruct corr'.
      rewrite <- cs_consist;auto.
      apply sceEventMapAlphabet with (conf0:=conf');auto.
      apply induction_ts with (e2:= event (stepEvent x2));auto.
      Focus 2. apply basic_ts ;auto.
       assert (In x1 (finishedscenarios conf')).
      apply  chainMergeFinMap';auto.
      exists (event (stepEvent x2));auto.
      destruct corr'.
      rewrite <- cs_consist;auto.
      apply sceEventMapAlphabet with (conf0:=conf');auto.

       assert (In (event (stepEvent x2)) (range (sceEventMap conf')) ).
       apply   rangeDomInRev with (a:=x1);auto.
       destruct H19. 
       
repeat match goal with
        | [ H: _ /\ _ |- _ ] => destruct H
        | [ H: exists _, _ |- _] => destruct H
          end.
      
         apply usedEventLedTo with (conf:=conf) (re:=re)in H29;auto.
         destruct H29.
     rewrite H29 in H28.          
     contradiction.     auto.
     repeat(split;auto). 
     apply chainMergeInitialEvent in H3;auto.
   
     eapply wellForm.scenarioRaiseIn;auto.
     unfold getTransitionsOfScenario.
     apply H12.
     apply H13.

      eapply wellForm.scenarioRaiseIn;auto.
      assert (In x1 (finishedscenarios conf')).
      apply  chainMergeFinMap';auto.
      exists (event (stepEvent x2));auto.
      destruct corr'.
      rewrite <- cs_consist;auto.
      unfold getTransitionsOfScenario.       
      apply H10.
      apply H11.

   
    (*noDupRaise'': *)
Qed.



Lemma usedEventLedTo': forall M (conf conf' : configuration M) re,
    chainMerge conf conf' re ->
    transEvMapProp M ->
    stpStMapEquiv' M ->
    correctStateEvStepMap' M ->
    stateEvDefInstanceMapEquiv M ->
    noMergeError' M ->
    basicPrecondition conf re ->
    (forall ev, In ev (range (sceEventMap conf'))  -> ev = (eventDefinition re) \/ staticEventLeadTo M (eventDefinition re) ev).
Proof. 
 intros. 
 rename H0 into evMapProp. rename H1 into mapEquiv. rename H2 into stpMap. rename H3 into stMapEq.
 rename H4 into noMerge. rename H5 into bp. 
  rename H6 into H0.
  generalize dependent ev. 
  induction H. 
  rename event into ev. 
 -  intros.
    remember H1. clear Heqi. apply rangeDomIn in i. 
    
    remember i. clear Heqe.
    
    pose proof chainMergeFinMap.
    destruct i.
    destruct H2 with (conf:=conf) (conf':=conf') (e:=ev) (sce:=x);auto.
    constructor;auto.
    assert ((exists ev : event_definition, In (x, ev) (sceEventMap conf'))).
    exists ev0;auto. apply H5 in H6.
    SearchAbout eventDefinition.
    pose proof syncMapFinishEventDef.
    left. apply H7 with (conf:=conf) (conf':=conf') (sce:=x);auto. destruct H;auto.
    unfold not. intros. destruct H.
    repeat match goal with
            | [ H: _ /\ _ |- _ ] => destruct H

           end.
    rewrite H12 in H8;inversion H8.         
  -   intros. 
    
      assert ( In ev (range (sceEventMap conf')) \/ ~ ( In ev (range (sceEventMap conf')))).
      apply excluded_middle.
      destruct H2.
      assert (ev = eventDefinition event1 \/
              staticEventLeadTo M (eventDefinition event1) ev).
      apply IHchainMerge;auto. auto. 
      right. remember H0. clear Heqs. 
       unfold synchrony in H0.
      destruct H0.
      assert (ev = eventDefinition event2).
      apply rangeDomIn in H1.
      assert (~ (exists a, In (a,ev) (sceEventMap conf'))).
      unfold not. intros. apply H2. destruct H4.
      apply rangeDomInRev in H4. 
      auto.   Check syncMapFinishEventDef.
      pose proof syncMapFinishEventDef. destruct H1. 
      apply H5 with (conf:=conf') (conf':=conf'') (sce:=x);auto.
      Focus 3. unfold not. intros. apply H4. exists x;auto.
      Focus 2.

      
      destruct bp.
        repeat match goal with
            | [ H: _ /\ _ |- _ ] => destruct H

           end.
      split;(try (rewrite <- monitorObjNoChangeChain with (conf:=conf) (e:=event1);auto)).
      Focus 2. repeat(split;auto).
       unfold synchrony in s. destruct s;auto.
      
      apply termL5' with (conf:=conf) (conf':=conf') (e:=event1);auto.
      remember H. clear Heqc. 
      apply chainMergeInitial in H. destruct H. destruct H. apply raised_wellform'.
       apply chainMergeInitialEvent in c. auto.
      destruct bp. 
      repeat match goal with
            | [ H: _ /\ _ |- _ ] => destruct H

           end.    

      
      
       apply termL5' with (conf:=conf) (conf':=conf') (e:=event1);auto.
       remember H. clear Heqc. 
      apply chainMergeInitial in H. destruct H. destruct H. apply raised_wellform'.
   apply chainMergeInitialEvent in c. auto.
  
     
      pose proof raisedEventLedTo.
      
      rewrite H4.
   eapply H5 with (conf':=conf');eauto.    
Qed.




Lemma diamond: forall M (conf conf1 conf2: configuration M)  e1 e2,
 WellFormed M -> deter_prop M -> (initialConfig conf \/ (exists conf' e, chainMerge conf' conf e)) -> synchrony conf conf1 e1 ->  synchrony conf conf2 e2 ->
e1 <> e2 -> 
 (exists conf1' conf2', 
  synchrony conf1 conf1' e2 /\ synchrony conf2 conf2' e1 /\ equivConf conf1' conf2'). 
Proof.
  intros.
  rename H into wf. rename H0 into H. rename H1 into H0. rename H2 into H1.
  rename H3 into H2. rename H4 into H3. 
  destruct H0.
  exfalso.
  destruct H0.
  destruct H4.
  unfold synchrony in H1;unfold synchrony in H2.
  destruct H1.
  destruct H2.
  destruct (raisedevents conf).   
  inversion H1.
  destruct l.
  destruct H1;inversion H1.
  destruct H2;inversion H2.
  subst.   
  contradiction.
  inversion H4.
  destruct H0.
  destruct H0.
  
  
    assert (correct_configuration  conf).
 remember H.  clear Heqd.   destruct H.
  rename H4 into  temp. rename H into dp'. 
   destruct wf. 
    repeat match goal with
        | [ H: _ /\ _ |- _ ] => destruct H
        | [ H: exists _, _ |- _] => destruct H
            end.
      destruct H10.

       repeat match goal with
        | [ H: _ /\ _ |- _ ] => destruct H
        | [ H: exists _, _ |- _] => destruct H
              end.

         apply termL5' with (conf:=x) (e:=x0);intuition;auto.
  remember H0.
  clear Heqc.
  apply chainMergeInitial in c.
  destruct c.   destruct H26.
  apply  raised_wellform'  ;auto.
  apply chainMergeInitialEvent in H0;auto.
  

  assert (eventDefinition e1 <> eventDefinition e2).

  
  pose proof noDupEventDefinitionRaised''.
    
  assert ( uniqList
             (map (fun re0 : raisedEvent => eventId (eventDefinition re0)) (raisedevents conf))).
 

  destruct H. destruct H. destruct wf. 
    repeat match goal with
        | [ H: _ /\ _ |- _ ] => destruct H
        | [ H: exists _, _ |- _] => destruct H
              end.
    apply H5 with (conf:=x) (re:=x0);auto.
    split. apply noMultIn;auto. apply noMultImportedIn;auto.
   assert (In e1 (raisedevents conf)).
    unfold synchrony in H1;intuition;auto.
    
    assert (In e2 (raisedevents conf)).
    unfold synchrony in H2;intuition;auto.

    apply uniqListEventIdNotEq with (l:=raisedevents conf);auto.
  rename H5 into evn.   
  pose proof diamondL2.
  assert (exists conf1' : configuration M, synchrony conf1 conf1' e2).
  apply H5 with (conf:=conf) (conf2:=conf2) (e1:=e1);auto.
  destruct H. destruct H. 
  destruct H7.
 destruct H8.   intros. 
 
  repeat match goal with
        | [ H: _ /\ _ |- _ ] => destruct H
        | [ H: exists _, _ |- _] => destruct H
              end.
  apply H17 with (e1:=eventDefinition e1) (e2:=eventDefinition e2);auto.


    exists (eventDefinition x0).
  split.

  assert (correct_configuration x).
  apply chainMergeInitial in H0.
  destruct H0;auto.
  destruct H18.
  apply  raise_in;auto.
  apply chainMergeInitialEvent in H0.
  auto.
  split.
  remember H0.
  clear Heqc.  
    apply chainMergeInitialEvent in H0.
    apply  chainMergeInitial in c;auto.
    destruct c.
    destruct H18.
    destruct H19. destruct H19. 
    apply H19 in H0.
    destruct H0;auto.
    unfold   importedEvent in H0.
    destruct (eventKind (eventDefinition x0) );inversion H0;auto.

    split.

    destruct wf.
    repeat match goal with
        | [ H: _ /\ _ |- _ ] => destruct H
        | [ H: exists _, _ |- _] => destruct H
           end.
    destruct H21.
    repeat match goal with
        | [ H: _ /\ _ |- _ ] => destruct H
        | [ H: exists _, _ |- _] => destruct H
           end.   

    apply raisedEventLedTo' with (conf:=x) (conf':=conf);auto.
    unfold synchrony in H1;intuition;auto.
    split.
     destruct wf.
    repeat match goal with
        | [ H: _ /\ _ |- _ ] => destruct H
        | [ H: exists _, _ |- _] => destruct H
           end.
    destruct H21.
    repeat match goal with
        | [ H: _ /\ _ |- _ ] => destruct H
        | [ H: exists _, _ |- _] => destruct H
           end.   

    apply raisedEventLedTo' with (conf:=x) (conf':=conf);auto.
    unfold synchrony in H2;intuition;auto.

    split.
    unfold not;intros.
    pose proof usedEventLedTo''''.
  assert ( ~ (exists re' : raisedEvent, eventDefinition re' = eventDefinition e2 /\ In re' (raisedevents conf)) /\
           ~ In (eventDefinition e2) (range (sceEventMap conf))).
  
   apply H19 with (conf:=x) (conf':=conf) (re:=x0) (e1:=eventDefinition e1) (e2:=eventDefinition e2);intuition;auto.  
   exists e1;auto.
   split;auto.  unfold synchrony in H1;intuition;auto.  
 (* destruct wf;intuition;auto.   destruct wf;intuition;auto. *) destruct H20.
   apply H20.
   exists e2;split;auto.
   unfold synchrony in H2;intuition;auto.    

   unfold not;intros.

   pose proof usedEventLedTo''''.

    assert ( ~ (exists re' : raisedEvent, eventDefinition re' = eventDefinition e1 /\ In re' (raisedevents conf)) /\
           ~ In (eventDefinition e1) (range (sceEventMap conf))).
  
   apply H19 with (conf:=x) (conf':=conf) (re:=x0) (e1:=eventDefinition e2) (e2:=eventDefinition e1);intuition;auto.  
   exists e2;auto. 
   split;auto.  unfold synchrony in H2;intuition;auto.
  (* destruct wf;intuition;auto.   destruct wf;intuition;auto.*)  destruct H20.
 
   apply H20.
   exists e1;split;auto.
   unfold synchrony in H1;intuition;auto.

 

  destruct H4. rewrite <- cs_consist;auto. 
   destruct H4. rewrite <- cs_consist;auto. 
 destruct H;intuition;auto. 
  
   pose proof diamondL3.
  assert (exists conf2' : configuration M, synchrony conf2 conf2' e1).
  apply H10 with (conf:=conf) (conf1:=conf1) (e2:=e2);auto.

   destruct H.
destruct H12.  
  intros. 
 
  repeat match goal with
        | [ H: _ /\ _ |- _ ] => destruct H
        | [ H: exists _, _ |- _] => destruct H
              end.
  apply H19 with (e1:=eventDefinition e1) (e2:=eventDefinition e2);auto.


  exists (eventDefinition x0).
  split.

  assert (correct_configuration x).
  apply chainMergeInitial in H0.
  destruct H0;auto.
  destruct H20.
  apply  raise_in;auto.
  apply chainMergeInitialEvent in H0.
  auto.
  split.
  remember H0.
  clear Heqc.  
    apply chainMergeInitialEvent in H0.
    apply  chainMergeInitial in c;auto.
    destruct c.
    destruct H20.
    destruct H21. destruct H21. 
    apply H21 in H0.
    destruct H0;auto.
    unfold   importedEvent in H0.
    destruct (eventKind (eventDefinition x0) );inversion H0;auto.

    split.

    destruct wf.
    repeat match goal with
        | [ H: _ /\ _ |- _ ] => destruct H
        | [ H: exists _, _ |- _] => destruct H
           end.
    destruct H23.
    repeat match goal with
        | [ H: _ /\ _ |- _ ] => destruct H
        | [ H: exists _, _ |- _] => destruct H
           end.   

    apply raisedEventLedTo' with (conf:=x) (conf':=conf);auto.
    unfold synchrony in H1;intuition;auto.
    split.
     destruct wf.
    repeat match goal with
        | [ H: _ /\ _ |- _ ] => destruct H
        | [ H: exists _, _ |- _] => destruct H
           end.
    destruct H23.
    repeat match goal with
        | [ H: _ /\ _ |- _ ] => destruct H
        | [ H: exists _, _ |- _] => destruct H
           end.   

    apply raisedEventLedTo' with (conf:=x) (conf':=conf);auto.
    unfold synchrony in H2;intuition;auto.

    split.
    unfold not;intros.
    pose proof usedEventLedTo''''.
  assert ( ~ (exists re' : raisedEvent, eventDefinition re' = eventDefinition e2 /\ In re' (raisedevents conf)) /\
           ~ In (eventDefinition e2) (range (sceEventMap conf))).
  
   apply H21 with (conf:=x) (conf':=conf) (re:=x0) (e1:=eventDefinition e1) (e2:=eventDefinition e2);intuition;auto.  
   exists e1;auto.
   split;auto.  unfold synchrony in H1;intuition;auto.   
 (*  destruct wf;intuition;auto.   destruct wf;intuition;auto.  *)
   destruct H22.
   apply H22.
   exists e2;split;auto.
   unfold synchrony in H2;intuition;auto.    

   unfold not;intros.

   pose proof usedEventLedTo''''.

    assert ( ~ (exists re' : raisedEvent, eventDefinition re' = eventDefinition e1 /\ In re' (raisedevents conf)) /\
           ~ In (eventDefinition e1) (range (sceEventMap conf))).
  
   apply H21 with (conf:=x) (conf':=conf) (re:=x0) (e1:=eventDefinition e2) (e2:=eventDefinition e1);intuition;auto.  
   exists e2;auto.
   split;auto.  unfold synchrony in H2;intuition;auto.   
 (*  destruct wf;intuition;auto.   destruct wf;intuition;auto. *)
   destruct H22.
   apply H22.
   exists e1;split;auto.
   unfold synchrony in H1;intuition;auto. 

  
  destruct H4. rewrite <- cs_consist;auto. 
   destruct H4. rewrite <- cs_consist;auto. 
   destruct H.
  
  destruct H6.
  destruct H12.
  exists x1;exists x2;split;auto.
  split;auto.
  apply diamondL1 with (conf:=conf) (conf1:=conf1) (conf2:=conf2) (e1:=e1) (e2:=e2);auto.

   intros.
  apply H with (e1:=eventDefinition e1) (e2:=eventDefinition e2);auto.
 (*begin*)
  exists (eventDefinition x0).
  split.

  assert (correct_configuration x).
  apply chainMergeInitial in H0.
  destruct H0;auto.
  destruct H18.
  apply  raise_in;auto.
  apply chainMergeInitialEvent in H0.
  auto.
  split.
  remember H0.
  clear Heqc.  
    apply chainMergeInitialEvent in H0.
    apply  chainMergeInitial in c;auto.
    destruct c.
    destruct H18.
    destruct H19. destruct H19. 
    apply H19 in H0.
    destruct H0;auto.
    unfold   importedEvent in H0.
    destruct (eventKind (eventDefinition x0) );inversion H0;auto.

    split.

    destruct wf.
    repeat match goal with
        | [ H: _ /\ _ |- _ ] => destruct H
        | [ H: exists _, _ |- _] => destruct H
           end.
    destruct H24.
    repeat match goal with
        | [ H: _ /\ _ |- _ ] => destruct H
        | [ H: exists _, _ |- _] => destruct H
           end.   

    apply raisedEventLedTo' with (conf:=x) (conf':=conf);auto.
    unfold synchrony in H1;intuition;auto.
    split.
     destruct wf.
    repeat match goal with
        | [ H: _ /\ _ |- _ ] => destruct H
        | [ H: exists _, _ |- _] => destruct H
           end.
    destruct H24.
    repeat match goal with
        | [ H: _ /\ _ |- _ ] => destruct H
        | [ H: exists _, _ |- _] => destruct H
           end.   

    apply raisedEventLedTo' with (conf:=x) (conf':=conf);auto.
    unfold synchrony in H2;intuition;auto.

    split.
    unfold not;intros.
    pose proof usedEventLedTo''''.
  assert ( ~ (exists re' : raisedEvent, eventDefinition re' = eventDefinition e2 /\ In re' (raisedevents conf)) /\
           ~ In (eventDefinition e2) (range (sceEventMap conf))).
  
   apply H19 with (conf:=x) (conf':=conf) (re:=x0) (e1:=eventDefinition e1) (e2:=eventDefinition e2);intuition;auto.  
   exists e1;auto.
   split;auto.  unfold synchrony in H1;intuition;auto.
   (*destruct wf;intuition;auto.   destruct wf;intuition;auto. *)
   destruct H20.
   apply H20.
   exists e2;split;auto.
   unfold synchrony in H2;intuition;auto.    

   unfold not;intros.

   pose proof usedEventLedTo''''.

    assert ( ~ (exists re' : raisedEvent, eventDefinition re' = eventDefinition e1 /\ In re' (raisedevents conf)) /\
           ~ In (eventDefinition e1) (range (sceEventMap conf))).
  
   apply H19 with (conf:=x) (conf':=conf) (re:=x0) (e1:=eventDefinition e2) (e2:=eventDefinition e1);intuition;auto.  
   exists e2;auto.
   split;auto.  unfold synchrony in H2;intuition;auto.
   (* destruct wf;intuition;auto.   destruct wf;intuition;auto. *)
   destruct H20.
   apply H20.
   exists e1;split;auto.
   unfold synchrony in H1;intuition;auto.    
(*end*)
   
   
  destruct H4.
  apply raise_in;auto.
  unfold synchrony in H2;intuition;auto.
    destruct H4.
  apply raise_in;auto.
  unfold synchrony in H1;intuition;auto.

  destruct H4.
  rewrite <- ds_dom_eq.
  rewrite dom2dom'.
  auto.

   destruct H4.
  rewrite <- ds_dom_eq.
  rewrite dom2dom'.
  auto.

  intros.

  (*start here*)



  destruct H13.   
  apply H13 with (e1:=eventDefinition e1) (e2:=eventDefinition e2);auto.


    exists (eventDefinition x0).
  split.

  assert (correct_configuration x).
  apply chainMergeInitial in H0.
  destruct H0;auto.
  destruct H19.
  apply  raise_in;auto.
  apply chainMergeInitialEvent in H0.
  auto.
  split.
  remember H0.
  clear Heqc.  
    apply chainMergeInitialEvent in H0.
    apply  chainMergeInitial in c;auto.
    destruct c.
    destruct H19.
    destruct H20. destruct H20. 
    apply H20 in H0.
    destruct H0;auto.
    unfold   importedEvent in H0.
    destruct (eventKind (eventDefinition x0) );inversion H0;auto.

    split.

    destruct wf.
    repeat match goal with
        | [ H: _ /\ _ |- _ ] => destruct H
        | [ H: exists _, _ |- _] => destruct H
           end.
    destruct H24.
    repeat match goal with
        | [ H: _ /\ _ |- _ ] => destruct H
        | [ H: exists _, _ |- _] => destruct H
           end.   

    apply raisedEventLedTo' with (conf:=x) (conf':=conf);auto.
    unfold synchrony in H1;intuition;auto.
    split.
     destruct wf.
    repeat match goal with
        | [ H: _ /\ _ |- _ ] => destruct H
        | [ H: exists _, _ |- _] => destruct H
           end.
    destruct H24.
    repeat match goal with
        | [ H: _ /\ _ |- _ ] => destruct H
        | [ H: exists _, _ |- _] => destruct H
           end.   

    apply raisedEventLedTo' with (conf:=x) (conf':=conf);auto.
    unfold synchrony in H2;intuition;auto.

    split.
    unfold not;intros.
    pose proof usedEventLedTo''''.
  assert ( ~ (exists re' : raisedEvent, eventDefinition re' = eventDefinition e2 /\ In re' (raisedevents conf)) /\
           ~ In (eventDefinition e2) (range (sceEventMap conf))).
  
   apply H20 with (conf:=x) (conf':=conf) (re:=x0) (e1:=eventDefinition e1) (e2:=eventDefinition e2);intuition;auto.  
   exists e1;auto.
   split;auto.  unfold synchrony in H1;intuition;auto.
 (*  destruct wf;intuition;auto.   destruct wf;intuition;auto.*) 
   destruct H21.
   apply H21.
   exists e2;split;auto.
   unfold synchrony in H2;intuition;auto.    

   unfold not;intros.

   pose proof usedEventLedTo''''.

    assert ( ~ (exists re' : raisedEvent, eventDefinition re' = eventDefinition e1 /\ In re' (raisedevents conf)) /\
           ~ In (eventDefinition e1) (range (sceEventMap conf))).
  
   apply H20 with (conf:=x) (conf':=conf) (re:=x0) (e1:=eventDefinition e2) (e2:=eventDefinition e1);intuition;auto.  
   exists e2;auto.
   split;auto.  unfold synchrony in H2;intuition;auto.
   (* destruct wf;intuition;auto.   destruct wf;intuition;auto. *)
   destruct H21.
   apply H21.
   exists e1;split;auto.
   unfold synchrony in H1;intuition;auto.

   
  destruct H4.
  apply raise_in;auto.
  unfold synchrony in H2;intuition;auto.
    destruct H4.
  apply raise_in;auto.
  unfold synchrony in H1;intuition;auto.

  destruct H4.
  rewrite <- ds_dom_eq.
  rewrite dom2dom'.
  auto.

   destruct H4.
  rewrite <- ds_dom_eq.
  rewrite dom2dom'.
  auto.

  intros.


  
  
  
  destruct H13.   destruct H18.  
  unfold not;intros. 
  apply H18 with (v1:=v2) (v2:=v1) (e1:=eventDefinition e1) (e2:=eventDefinition e2);auto.



    exists (eventDefinition x0).
  split.

  assert (correct_configuration x).
  apply chainMergeInitial in H0.
  destruct H0;auto.
  destruct H21.
  apply  raise_in;auto.
  apply chainMergeInitialEvent in H0.
  auto.
  split.
  remember H0.
  clear Heqc.  
    apply chainMergeInitialEvent in H0.
    apply  chainMergeInitial in c;auto.
    destruct c.
    destruct H21.
    destruct H22. destruct H22. 
    apply H22 in H0.
    destruct H0;auto.
    unfold   importedEvent in H0.
    destruct (eventKind (eventDefinition x0) );inversion H0;auto.

    split.

    destruct wf. 
    repeat match goal with
        | [ H: _ /\ _ |- _ ] => destruct H
        | [ H: exists _, _ |- _] => destruct H
           end.
    destruct H25.
    repeat match goal with
        | [ H: _ /\ _ |- _ ] => destruct H
        | [ H: exists _, _ |- _] => destruct H
           end.   

    apply raisedEventLedTo' with (conf:=x) (conf':=conf);auto.
    unfold synchrony in H1;intuition;auto.
    split.
     destruct wf.
    repeat match goal with
        | [ H: _ /\ _ |- _ ] => destruct H
        | [ H: exists _, _ |- _] => destruct H
           end.
    destruct H25.
    repeat match goal with
        | [ H: _ /\ _ |- _ ] => destruct H
        | [ H: exists _, _ |- _] => destruct H
           end.   

    apply raisedEventLedTo' with (conf:=x) (conf':=conf);auto.
    unfold synchrony in H2;intuition;auto.

    split.
    unfold not;intros.
    pose proof usedEventLedTo''''.
  assert ( ~ (exists re' : raisedEvent, eventDefinition re' = eventDefinition e2 /\ In re' (raisedevents conf)) /\
           ~ In (eventDefinition e2) (range (sceEventMap conf))).
  
   apply H22 with (conf:=x) (conf':=conf) (re:=x0) (e1:=eventDefinition e1) (e2:=eventDefinition e2);intuition;auto.  
   exists e1;auto.
   split;auto.  unfold synchrony in H1;intuition;auto.
  (*  destruct wf;intuition;auto.   destruct wf;intuition;auto. *)
   destruct H23.
   apply H23.
   exists e2;split;auto.
   unfold synchrony in H2;intuition;auto.    

   unfold not;intros.

   pose proof usedEventLedTo''''.

    assert ( ~ (exists re' : raisedEvent, eventDefinition re' = eventDefinition e1 /\ In re' (raisedevents conf)) /\
           ~ In (eventDefinition e1) (range (sceEventMap conf))).
  
   apply H22 with (conf:=x) (conf':=conf) (re:=x0) (e1:=eventDefinition e2) (e2:=eventDefinition e1);intuition;auto.  
   exists e2;auto.
   split;auto.  unfold synchrony in H2;intuition;auto.
   (* destruct wf;intuition;auto.   destruct wf;intuition;auto. *)
   destruct H23.
   apply H23.
   exists e1;split;auto.
   unfold synchrony in H1;intuition;auto. 





  destruct H4.
  apply raise_in;auto.
  unfold synchrony in H2;intuition;auto.
    destruct H4.
  apply raise_in;auto.
  unfold synchrony in H1;intuition;auto.

  destruct H4.
  rewrite <- ds_dom_eq.
  rewrite dom2dom'.
  auto.

   destruct H4.
  rewrite <- ds_dom_eq.
  rewrite dom2dom'.
  auto.


  
  intros.

  
  destruct H13.   destruct H20. destruct H21.  unfold not;intros. 
  apply H21 with (ev1:=ev1) (ev2:=ev2) (e1:=eventDefinition e1) (e2:=eventDefinition e2);auto.


    exists (eventDefinition x0).
  split.

  assert (correct_configuration x).
  apply chainMergeInitial in H0.
  destruct H0;auto.
  destruct H24.
  apply  raise_in;auto.
  apply chainMergeInitialEvent in H0.
  auto.
  split.
  remember H0.
  clear Heqc.  
    apply chainMergeInitialEvent in H0.
    apply  chainMergeInitial in c;auto.
    destruct c.
    destruct H24.
    destruct H25. destruct H25. 
    apply H25 in H0.
    destruct H0;auto.
    unfold   importedEvent in H0.
    destruct (eventKind (eventDefinition x0) );inversion H0;auto.

    split.

    destruct wf.
    repeat match goal with
        | [ H: _ /\ _ |- _ ] => destruct H
        | [ H: exists _, _ |- _] => destruct H
           end.
    destruct H27.
    repeat match goal with
        | [ H: _ /\ _ |- _ ] => destruct H
        | [ H: exists _, _ |- _] => destruct H
           end.   

    apply raisedEventLedTo' with (conf:=x) (conf':=conf);auto.
    unfold synchrony in H1;intuition;auto.
    split.
     destruct wf.
    repeat match goal with
        | [ H: _ /\ _ |- _ ] => destruct H
        | [ H: exists _, _ |- _] => destruct H
           end.
    destruct H27.
    repeat match goal with
        | [ H: _ /\ _ |- _ ] => destruct H
        | [ H: exists _, _ |- _] => destruct H
           end.   

    apply raisedEventLedTo' with (conf:=x) (conf':=conf);auto.
    unfold synchrony in H2;intuition;auto.

    split.
    unfold not;intros.
    pose proof usedEventLedTo''''.
  assert ( ~ (exists re' : raisedEvent, eventDefinition re' = eventDefinition e2 /\ In re' (raisedevents conf)) /\
           ~ In (eventDefinition e2) (range (sceEventMap conf))).
  
   apply H25 with (conf:=x) (conf':=conf) (re:=x0) (e1:=eventDefinition e1) (e2:=eventDefinition e2);intuition;auto.  
   exists e1;auto.
   split;auto.  unfold synchrony in H1;intuition;auto.
   (* destruct wf;intuition;auto.   destruct wf;intuition;auto.*) 
   destruct H26.
   apply H26.
   exists e2;split;auto.
   unfold synchrony in H2;intuition;auto.    

   unfold not;intros.

   pose proof usedEventLedTo''''.

    assert ( ~ (exists re' : raisedEvent, eventDefinition re' = eventDefinition e1 /\ In re' (raisedevents conf)) /\
           ~ In (eventDefinition e1) (range (sceEventMap conf))).
  
   apply H25 with (conf:=x) (conf':=conf) (re:=x0) (e1:=eventDefinition e2) (e2:=eventDefinition e1);intuition;auto.  
   exists e2;auto.
   split;auto.  unfold synchrony in H2;intuition;auto.
(*    destruct wf;intuition;auto.   destruct wf;intuition;auto. *)
   destruct H26.
   apply H26.
   exists e1;split;auto.
   unfold synchrony in H1;intuition;auto.

   


  destruct H4.
  apply raise_in;auto.
  unfold synchrony in H2;intuition;auto.
    destruct H4.
  apply raise_in;auto.
  unfold synchrony in H1;intuition;auto.

  intros. 


 
  
   destruct H13. destruct H18.
  destruct H19. 
   

  apply H20 with (e1:=eventDefinition e1) (e2:=eventDefinition e2);auto.

    exists (eventDefinition x0).
  split.

  assert (correct_configuration x).
  apply chainMergeInitial in H0.
  destruct H0;auto.
  destruct H21.
  apply  raise_in;auto.
  apply chainMergeInitialEvent in H0.
  auto.
  split.
  remember H0.
  clear Heqc.  
    apply chainMergeInitialEvent in H0.
    apply  chainMergeInitial in c;auto.
    destruct c.
    destruct H21.
    destruct H22. destruct H22. 
    apply H22 in H0.
    destruct H0;auto.
    unfold   importedEvent in H0.
    destruct (eventKind (eventDefinition x0) );inversion H0;auto.

    split.

    destruct wf.
    repeat match goal with
        | [ H: _ /\ _ |- _ ] => destruct H
        | [ H: exists _, _ |- _] => destruct H
           end.
    destruct H24.
    repeat match goal with
        | [ H: _ /\ _ |- _ ] => destruct H
        | [ H: exists _, _ |- _] => destruct H
           end.   

    apply raisedEventLedTo' with (conf:=x) (conf':=conf);auto.
    unfold synchrony in H1;intuition;auto.
    split.
     destruct wf.
    repeat match goal with
        | [ H: _ /\ _ |- _ ] => destruct H
        | [ H: exists _, _ |- _] => destruct H
           end.
    destruct H24.
    repeat match goal with
        | [ H: _ /\ _ |- _ ] => destruct H
        | [ H: exists _, _ |- _] => destruct H
           end.   

    apply raisedEventLedTo' with (conf:=x) (conf':=conf);auto.
    unfold synchrony in H2;intuition;auto.

    split.
    unfold not;intros.
    pose proof usedEventLedTo''''.
  assert ( ~ (exists re' : raisedEvent, eventDefinition re' = eventDefinition e2 /\ In re' (raisedevents conf)) /\
           ~ In (eventDefinition e2) (range (sceEventMap conf))).
  
   apply H22 with (conf:=x) (conf':=conf) (re:=x0) (e1:=eventDefinition e1) (e2:=eventDefinition e2);intuition;auto.  
   exists e1;auto.
   split;auto.  unfold synchrony in H1;intuition;auto.
  (*  destruct wf;intuition;auto.   destruct wf;intuition;auto.*) 
   destruct H23.
   apply H23.
   exists e2;split;auto.
   unfold synchrony in H2;intuition;auto.    

   unfold not;intros.

   pose proof usedEventLedTo''''.

    assert ( ~ (exists re' : raisedEvent, eventDefinition re' = eventDefinition e1 /\ In re' (raisedevents conf)) /\
           ~ In (eventDefinition e1) (range (sceEventMap conf))).
  
   apply H22 with (conf:=x) (conf':=conf) (re:=x0) (e1:=eventDefinition e2) (e2:=eventDefinition e1);intuition;auto.  
   exists e2;auto.
   split;auto.  unfold synchrony in H2;intuition;auto.
   (* destruct wf;intuition;auto.   destruct wf;intuition;auto.*) 
   destruct H23.
   apply H23.
   exists e1;split;auto.
   unfold synchrony in H1;intuition;auto.

   
  destruct H4. rewrite <- cs_consist;auto. 
   destruct H4. rewrite <- cs_consist;auto. 
 
  right.   
 exists x;exists x0;auto.   
Qed.




 

Lemma constructListEquiv': forall scs M  (conf conf' : configuration M)
                                 (l1 l2: list (configuration M)) e,
equivConf conf conf' ->
Result l1 = constructConfigList' scs  e conf ->
Result l2 = constructConfigList' scs  e conf' ->
l1 = l2.
Proof.
  intro scs;induction scs.
  intros. simpl in *;subst. inversion H0;inversion H1;subst;auto.
  intros.
  simpl in *.
  remember (constructConfig a e conf).
  remember (constructConfig a e conf').
  destruct e0;inversion H0. clear H3.
  destruct e1;inversion H1. clear H3. 
  assert (v = v0).                                         
  apply equivConfSyncBasic with (conf:=conf) (conf':=conf') (e:=e) (sce:=a);auto.
  subst.
  remember (constructConfigList' scs e conf).
  remember (constructConfigList' scs e conf').
  destruct e0;inversion H0.
  destruct e1;inversion H1.
  subst. f_equal.
  apply IHscs with (conf:=conf) (conf':=conf') (e:=e);auto.   
Qed.

Lemma constructListEquivExists: forall M scs scs' (conf  : configuration M)
                                 (l1 l2: list (configuration M)) e,
Permutation scs scs' ->
Result l1 = constructConfigList' scs  e conf ->
(exists l2, Result l2 = constructConfigList' scs'  e conf).
Proof.
     intros. 
  generalize dependent conf; generalize dependent l1;generalize dependent e. 
  induction H.
  intros. simpl in *. inversion H0;subst. exists nil;auto.
  intros.
  simpl in *.
  remember (constructConfig x e conf).
  destruct e0;inversion H0.
  remember (constructConfigList' l e conf).
  destruct e0;inversion H0.
  subst.
  apply IHPermutation in Heqe1;auto.
  destruct Heqe1. rewrite <- H1. exists (v::x0);auto.

  intros.
  simpl in *.
  remember (constructConfig y e conf). 
  destruct e0;inversion H0.
  remember (constructConfig x e conf).
  destruct e0;inversion H0.
  remember (constructConfigList' l e conf ).
  destruct e0;inversion H1. exists (v0::v::v1);auto.
  intros.
  apply IHPermutation1 in H1;auto.   
  destruct H1.
  apply IHPermutation2  in H1;auto. 
Qed.


Lemma constructListEquivExists': forall scs M   (conf conf'  : configuration M)
                                        (l1 : list (configuration M)) e,
equivConf conf conf' ->
Result l1 = constructConfigList' scs  e conf ->
(exists l2, Result l2 = constructConfigList' scs  e conf').
Proof.
  intro scs;induction scs.
  -
   intros. simpl in *. exists nil;auto. 
  - 
  intros.
  simpl in *.
  remember (constructConfig a e conf).
  destruct e0;inversion H0.
  remember (constructConfigList' scs e conf).
  destruct e0;inversion H0.
  subst.
  apply IHscs with (conf':=conf') in Heqe1;auto.
  destruct Heqe1. rewrite <- H1.
  pose proof equivConfSyncBasic'.
 apply H3 with (conf':=conf') in Heqe0;auto.   
 destruct Heqe0.
  rewrite <- H4.  
exists (x0::x);auto.  Qed.

Lemma constructListEquivExists'': forall M scs scs' (conf conf' : configuration M)
                                        (l1 : list (configuration M)) e,
equivConf conf conf' ->
Permutation scs scs' ->
Result l1 = constructConfigList' scs  e conf ->
(exists l2, Result l2 = constructConfigList' scs'  e conf').
Proof.
     intros. 
  generalize dependent conf; generalize dependent l1;generalize dependent e. 
 generalize dependent conf'.   induction H0.
  intros. simpl in *. inversion H1;subst. exists nil;auto.
  intros.
  simpl in *.
  remember (constructConfig x e conf).
  destruct e0;inversion H1.
  pose proof equivConfSyncBasic'.
  apply H2 with (conf':=conf') in Heqe0;auto.   
  destruct Heqe0.
  rewrite <- H4.
  remember (constructConfigList' l e conf ).
  destruct e0;inversion H1.
  apply IHPermutation with (conf':=conf') in Heqe0;auto. 
  destruct Heqe0. rewrite <- H5. 
  exists (x0::x1);auto.
  intros.
  simpl in *.
  remember (constructConfig y e conf).
  destruct e0;inversion H1.
  remember (constructConfig x e conf).
  destruct e0;inversion H1.
  remember (constructConfigList' l e conf).
  destruct e0;inversion H1.
  subst.
  pose proof equivConfSyncBasic'.
  apply H0 with (conf':=conf') in Heqe0;auto.
  apply H0 with (conf':=conf') in Heqe1;auto.
  destruct Heqe0.
  destruct Heqe1.
  rewrite <- H5.  rewrite <- H4.
  pose proof constructListEquivExists'.
  apply H6 with (conf':=conf') in Heqe2;auto.   
  destruct Heqe2. rewrite <- H7. exists (x1 :: x0 :: x2);auto.   
  intros.
  apply IHPermutation1 with (conf':=conf') in H1;auto.
  destruct H1.
  apply IHPermutation2 with (conf':=conf') in H0;auto.   
  apply equivConf_Refl;auto.   
Qed.


Lemma constructListEquiv: forall M scs scs' (conf conf' : configuration M)
                                 (l1 l2: list (configuration M)) e,
equivConf conf conf' ->
Permutation scs scs' ->
Result l1 = constructConfigList' scs  e conf ->
Result l2 = constructConfigList' scs'  e conf' ->
 confEquivList l1 l2. 
Proof.
  intros. 
  generalize dependent conf; generalize dependent conf';generalize dependent l1;generalize dependent l2;generalize dependent e. 
  induction H0.
  intros.  simpl in *.  inversion H2;inversion H1;subst;constructor.
  intros.
  simpl in H1;simpl in H2.
  remember (constructConfig x e conf').
  remember (constructConfig x e conf).
  destruct e0;inversion H2.
  clear H4.
  destruct e1;inversion H1.
  clear H1.
  remember (constructConfigList' l' e conf').
  destruct e0;inversion H2.
  remember (constructConfigList' l e conf). 
  destruct e0;inversion H4. 
  assert (v0 = v).
  apply equivConfSyncBasic with (conf:=conf) (conf':=conf') (e:=e) (sce:=x);auto.   
  subst.
  constructor. apply equivConf_Refl;auto.
  apply IHPermutation with (conf:=conf) (conf':=conf') (e:=e);auto. 

  intros.
  simpl in *.
  remember (constructConfig x e conf' ).
  destruct e0;inversion H2. clear H3.
  remember (constructConfig y e conf'). 
  destruct e0;inversion H2. clear H3.
  remember (constructConfigList' l e conf').
  destruct e0;inversion H2.   
  remember (constructConfig y e conf).
  destruct e0;inversion H1. clear H4.
  remember (constructConfig x e conf).
  destruct e0;inversion H1. clear H4.
  remember (constructConfigList' l e conf). 
  destruct e0;inversion H1.
  assert (v3 = v).  apply equivConfSyncBasic with (conf:=conf) (conf':=conf') (e:=e) (sce:=x);auto.  subst.
  assert (v2 = v0).  apply equivConfSyncBasic with (conf:=conf) (conf':=conf') (e:=e) (sce:=y);auto.  subst. 
  apply confEqSwap;auto. apply equivConf_Refl;auto. apply equivConf_Refl;auto.
  pose proof constructListEquiv'.
  assert (v4 = v1). 
  apply H0 with (scs:=l) (conf:=conf) (conf':=conf') (e:=e);auto.
  subst.
  apply confEquivList_refl;auto.

  intros.        
  pose proof constructListEquivExists.
  assert (exists l3 : list (configuration M), Result l3 = constructConfigList' l' e conf).
apply H0 with (scs:=l) (l1:=l1) ;auto.   
destruct H3.
remember H2.
clear Heqe0. 
apply IHPermutation2 with (l1:=x) (conf:=conf) in H2;auto.

  pose proof constructListEquivExists.
  assert (exists l3 : list (configuration M), Result l3 = constructConfigList' l' e conf').
  apply H4 with (scs:=l'') (l1:=l2) ;auto.   
  apply Permutation_sym;auto.
  destruct H5.
  apply IHPermutation1 with (l2:=x0) (conf':=conf') in H1;auto.
  pose proof constructListEquiv'.
  assert (x = x0).
  apply H6 with (scs:=l') (conf:=conf) (conf':=conf') (e:=e);auto.
  subst.
  apply confEquivListTransitivity with (x:=x0);auto.
  
Qed.







Lemma constructListEquiv'': forall M scs scs' (conf conf' : configuration M)
                                 (l1 l2: list (configuration M)) e,
equivConf conf conf' ->
Permutation scs scs' ->
Result l1 = constructConfigList' scs  e conf ->
Result l2 = constructConfigList' scs'  e conf' ->
uniqList scs -> Permutation l1 l2. 
Proof.
  intros. 
  generalize dependent conf; generalize dependent conf';generalize dependent l1;generalize dependent l2;generalize dependent e. 
  induction H0.
  intros.  simpl in *.  inversion H2;inversion H1;subst;constructor.
  intros.
  simpl in H1;simpl in H2.
  remember (constructConfig x e conf').
  remember (constructConfig x e conf).
  destruct e0;inversion H2.
  clear H5.
  destruct e1;inversion H1.
  clear H1.
  remember (constructConfigList' l' e conf').
  destruct e0;inversion H2.
  remember (constructConfigList' l e conf). 
  destruct e0;inversion H5. 
  assert (v0 = v).
  apply equivConfSyncBasic with (conf:=conf) (conf':=conf') (e:=e) (sce:=x);auto.   
  subst.
  constructor. 
  apply IHPermutation with (conf:=conf) (conf':=conf') (e:=e);auto. 
  inversion H3;subst;auto. 
  
  
  intros.
  simpl in *.
  remember (constructConfig x e conf' ).
  destruct e0;inversion H2. clear H4.
  remember (constructConfig y e conf'). 
  destruct e0;inversion H2. clear H4.
  remember (constructConfigList' l e conf').
  destruct e0;inversion H2.   
  remember (constructConfig y e conf).
  destruct e0;inversion H1. clear H5.
  remember (constructConfig x e conf).
  destruct e0;inversion H1. clear H5.
  remember (constructConfigList' l e conf). 
  destruct e0;inversion H1.
  assert (v3 = v).  apply equivConfSyncBasic with (conf:=conf) (conf':=conf') (e:=e) (sce:=x);auto.  subst.
  assert (v2 = v0).  apply equivConfSyncBasic with (conf:=conf) (conf':=conf') (e:=e) (sce:=y);auto.  subst.
  Print Permutation.
   pose proof constructListEquiv'.
   assert (v4 = v1). 
   apply H0 with (scs:=l) (conf:=conf) (conf':=conf') (e:=e);auto.
subst.    
  apply perm_swap;auto. 
 
  intros.        
  pose proof constructListEquivExists.
  assert (exists l3 : list (configuration M), Result l3 = constructConfigList' l' e conf).
apply H0 with (scs:=l) (l1:=l1) ;auto.   
destruct H4.
remember H2.
clear Heqe0. 
apply IHPermutation2 with (l1:=x) (conf:=conf) in H2;auto.
Focus 2. 
 
rewrite uniqListNoDupEq.
apply Permutation_NoDup with (l:=l);auto.
rewrite <- uniqListNoDupEq;auto.
  pose proof constructListEquivExists.
  assert (exists l3 : list (configuration M), Result l3 = constructConfigList' l' e conf').
  apply H5 with (scs:=l'') (l1:=l2) ;auto.   
  SearchAbout Permutation.
  apply Permutation_sym;auto.
  destruct H6.
  apply IHPermutation1 with (l2:=x0) (conf':=conf') in H1;auto.
  pose proof constructListEquiv'.
  assert (x = x0).
  apply H7 with (scs:=l') (conf:=conf) (conf':=conf') (e:=e);auto.
  subst.
  Print Permutation. 
  apply perm_trans with (l':=x0);auto.
  
Qed.



Lemma mergeDataStateFuncEquiv: forall ds ds1 ds2 v1 v2 v3 v4,
    Result v1 =  mergeDataStateFunc ds ds ds1 ->
    Result v2 = mergeDataStateFunc ds ds2 v1 ->
    Result v3 = mergeDataStateFunc ds ds ds2 ->
    Result v4 = mergeDataStateFunc ds ds1 v3 ->
    v2 = v4.
Proof.
  intro ds;induction ds.
  - intros.  destruct ds1;destruct ds2. simpl in *.
    inversion H;inversion H1;subst. inversion H0;inversion H2;auto.
    simpl in H0. inversion H0.
    simpl in H2. inversion H2.
    simpl in H. inversion H.     
  -  intros.
     destruct ds1. simpl in H. destruct a;destruct p. inversion H.
     destruct ds2. simpl in H0. destruct a;destruct p. destruct p0. inversion H0.
     simpl in *.
     destruct a;destruct p0. destruct p1. destruct p. destruct p. destruct p0.
     destruct ( atom_eq_dec a a). Focus 2. contradiction.
     destruct (atom_eq_dec a a1).  Focus 2. inversion H.
     destruct (typ_eq_dec t t). Focus 2. contradiction.
     destruct (typ_eq_dec t t0). Focus 2. inversion H.
     destruct (atom_eq_dec a a0). Focus 2. inversion H1.
     destruct (typ_eq_dec t t1). Focus 2. inversion H1.
     remember (mergeDataStateFunc ds ds ds1).
     destruct e5;inversion H. clear H4.
     remember ( mergeDataStateFunc ds ds ds2).
     destruct e5;inversion H1. clear H4.
     subst.
     destruct (range_typ_dec r r0).
     inversion H;subst.
     destruct (range_typ_dec r0 r1).
     inversion H1;subst. 
     destruct (atom_eq_dec a0 a0).
     Focus 2. contradiction.
     destruct (typ_eq_dec t1 t1). 
     Focus 2. contradiction.
     remember (mergeDataStateFunc ds ds2 v).
     destruct e3;inversion H0. clear H4.
     remember (mergeDataStateFunc ds ds1 v0).
     destruct e3;inversion H2.
     clear H4. destruct (range_typ_dec r1 r1). Focus 2. contradiction.
     inversion H0;inversion H2. f_equal.
     eapply IHds;auto. apply Heqe5. apply Heqe3. apply Heqe0. auto.
     destruct (atom_eq_dec a0 a0). Focus 2. inversion H0.
     destruct (typ_eq_dec t1 t1). Focus 2. inversion H0.
     remember (mergeDataStateFunc ds ds2 v).
     destruct e3;inversion H0.
     clear H4.
     destruct (range_typ_dec r1 r0).
     subst.
     contradiction.
     destruct (range_typ_dec r0 r0). Focus 2.  inversion H0.
     inversion H0;inversion H1.  rewrite H5 in H2.
     destruct (atom_eq_dec a0 a0). Focus 2. inversion H2.
     destruct (typ_eq_dec t1 t1). Focus 2.  inversion H2.
       remember ( mergeDataStateFunc ds ds1 v0 ).    
       destruct e6;inversion H2.
       destruct (range_typ_dec r0 r1). contradiction.
       inversion H6. f_equal.
       eapply IHds;auto. apply Heqe5. apply Heqe3. apply Heqe0. auto.
       destruct (range_typ_dec r r). Focus 2. contradiction.
       inversion H;subst.
       destruct (range_typ_dec r r1).
       subst. inversion H1;subst.
       destruct (atom_eq_dec a0 a0). Focus 2. contradiction.
       destruct (typ_eq_dec t1 t1). Focus 2. contradiction.
       remember (mergeDataStateFunc ds ds2 v). 
       destruct e4;inversion H0.
       remember (mergeDataStateFunc ds ds1 v0).
       destruct e4;inversion H2.
       destruct (range_typ_dec r1 r0).
       contradiction.
       destruct (range_typ_dec r0 r1).
       symmetry in e4.        contradiction.
       destruct (range_typ_dec r1 r1).
       Focus 2. inversion H0.
       inversion H0;inversion H2.
       f_equal.
       eapply IHds;auto. apply Heqe5. apply Heqe4. apply Heqe0. auto.
       inversion H1;subst. 
        destruct (atom_eq_dec a0 a0).
        Focus 2.      inversion H0.
        destruct (typ_eq_dec t1 t1). Focus 2. contradiction.
        remember (mergeDataStateFunc ds ds2 v ).
        destruct e4;inversion H0. clear H4.
        remember (mergeDataStateFunc ds ds1 v0 ).
        destruct e4;inversion H2.
        
        destruct (range_typ_dec r1 r0).
        subst.
        destruct (range_typ_dec r0 r0). 
        Focus 2.  contradiction.
        inversion H4;inversion H0;subst. f_equal. 
        eapply IHds;auto. apply Heqe5. apply Heqe4. apply Heqe0. auto.
        destruct (range_typ_dec r0 r1).
        subst.  contradiction.
        destruct ( range_typ_dec r0 r). subst. contradiction.
        destruct (range_typ_dec r1 r). subst.
        inversion H0;inversion H2;subst. f_equal.
           eapply IHds;auto. apply Heqe5. apply Heqe4. apply Heqe0. auto. inversion H0.
Qed.


Lemma mergeControlStateFuncEquiv: forall ds ds1 ds2 v1 v2 v3 v4,
    Result v1 =  mergeControlStateFunc ds ds ds1 ->
    Result v2 = mergeControlStateFunc ds ds2 v1 ->
    Result v3 = mergeControlStateFunc ds ds ds2 ->
    Result v4 = mergeControlStateFunc ds ds1 v3 ->
    v2 = v4.
Proof.
  intro ds;induction ds.
  - intros.  destruct ds1;destruct ds2. simpl in *.
    inversion H;inversion H1;subst. inversion H0;inversion H2;auto.
    simpl in H0. inversion H0.
    simpl in H2. inversion H2.
    simpl in H. inversion H.     
  -  intros.
     destruct ds1. simpl in H. destruct a.  inversion H.
     destruct ds2. simpl in H0. destruct a.  inversion H0. 
     simpl in *.
     destruct a. destruct p;destruct p0.
     destruct (scenario_dec s s). Focus 2. inversion H.
     destruct (scenario_dec s s1);inversion H.
     destruct (scenario_dec s s3);inversion H1. subst.
     remember (mergeControlStateFunc ds ds ds2).
     destruct e0;inversion H1. 
     remember (mergeControlStateFunc ds ds ds1).
     destruct e0;inversion H4. clear H;clear H6. clear H7. 
     destruct (string_dec s0 s2).
     destruct (string_dec s0 s4). subst.
     inversion H4;inversion H5;subst.
     destruct ( scenario_dec s3 s3). Focus 2. inversion H0.
          remember (mergeControlStateFunc ds ds2 v0). 
          destruct e1;inversion H0.
          clear H3.
    remember (mergeControlStateFunc ds ds1 v). 
    destruct e1;inversion H2.
    destruct (string_dec s2 s2). Focus 2. inversion H0.
    inversion H0. inversion H2;subst.
    f_equal.
    eapply IHds. apply Heqe1. apply Heqe2.  apply Heqe0. auto. 
    destruct (string_dec s0 s0). Focus 2. contradiction.
    inversion H1;subst.
    inversion H4;subst.
    destruct (scenario_dec s3 s3). 
    Focus 2. contradiction. 
    remember (mergeControlStateFunc ds ds2 v0).
    destruct e2;inversion H0.
    remember (mergeControlStateFunc ds ds1 v ). 
    destruct e2;inversion H2.
    destruct (string_dec s2 s4).
   contradiction.     destruct (string_dec s4 s2).
   symmetry in e2. contradiction.
   destruct (string_dec s2 s2).
   Focus 2. inversion H2.
   inversion H3;inversion H6.   f_equal.
     eapply IHds. apply Heqe1. apply Heqe2.  apply Heqe0. auto.
     destruct (string_dec s0 s0).
     Focus 2.   contradiction.
     destruct (string_dec s0 s4).
  subst.      
  inversion H1;subst.
  inversion H4;subst.
  destruct (scenario_dec s3 s3).
  Focus 2.  inversion H0.
  remember (mergeControlStateFunc ds ds2 v0).
  destruct e2.   Focus 2. inversion H0.
  remember (mergeControlStateFunc ds ds1 v).
  destruct e2.    Focus 2. inversion H2.
  destruct (string_dec s4 s2).
  contradiction.
  destruct (string_dec s2 s4).
  symmetry in e2. contradiction.
  destruct (string_dec s4 s4).
  Focus 2. inversion H0.
  inversion H0;subst.   
  inversion H2;subst.
f_equal.    eapply IHds. apply Heqe1. apply Heqe2.  apply Heqe0. auto. 
inversion H4;inversion H5;subst.
destruct ( scenario_dec s3 s3).
Focus 2. inversion H2.
remember (mergeControlStateFunc ds ds2 v0).
destruct e2;inversion H0.
remember ( mergeControlStateFunc ds ds1 v ).
destruct e2;inversion H2.
clear H3;clear H6. 
destruct (string_dec s4 s2).
destruct (string_dec s2 s4).
subst. Focus 2. symmetry in e2. contradiction.
inversion H2;subst.
inversion H0;subst.
f_equal.
eapply IHds. apply Heqe1. apply Heqe2.  apply Heqe0. auto.
destruct (string_dec s4 s0).
symmetry in e2. contradiction.
destruct (string_dec s2 s4).
symmetry in e2. contradiction.
destruct (string_dec s2 s0 );inversion H0.
inversion H3;subst.
inversion H2;subst.
f_equal. eapply IHds. apply Heqe1. apply Heqe2.  apply Heqe0. auto.
Qed. 


Lemma innterCombineFuncEquiv': forall M (l: list (configuration M))  (conf conf': configuration M)  v1 v2,
    equivConf conf conf' ->
    Some v1 = innerCombineFunc'''' conf l ->
    Some v2 = innerCombineFunc'''' conf' l ->
    equivConf v1 v2. 
Proof.
  intros M l.
  induction l.
  - intros.
    simpl in H0;simpl in H1.
    inversion H0.
  -
    intros.
    simpl in H0;simpl in H1.
    destruct l.
     
    remember (mergeConfigFunc' conf conf a).
    destruct e;inversion H0.
    remember (mergeConfigFunc' conf' conf' a ).
    destruct e;inversion H1.
    subst.
    unfold  mergeConfigFunc' in *.
    unfold equivConf in H.
    repeat match goal with
            | [ H: _ /\ _ |- _ ] => destruct H

                     end.    
    rewrite <- H in Heqe0.
    rewrite <- H2 in Heqe0.
    destruct ( mergeDataStateFunc (datastate conf) (datastate conf) (datastate a));inversion Heqe. 
    clear H10.
    destruct ( mergeControlStateFunc (controlstate conf) (controlstate conf) (controlstate a));inversion Heqe.
    inversion Heqe0;subst.
    split;simpl;auto. split;auto.
    repeat(split;try (apply Permutation_app_tail;auto)).

    unfold incl in *.
    intros.
    rewrite in_app_iff.
    rewrite in_app_iff in H9.
    destruct H9;intuition;auto. 

     unfold incl in *.
    intros.
    rewrite in_app_iff.
    rewrite in_app_iff in H9.
    destruct H9;intuition;auto.

     unfold incl in *.
    intros.
    rewrite in_app_iff.
    rewrite in_app_iff in H9.
    destruct H9;intuition;auto.
     unfold incl in *.
    intros.
    rewrite in_app_iff.
    rewrite in_app_iff in H9.
    destruct H9;intuition;auto. 



    
    remember (innerCombineFunc'''' conf (c :: l)).
    destruct o;inversion H0.
    remember (innerCombineFunc'''' conf' (c :: l) ).
    destruct o;inversion H1.  clear H3;clear H4.
    remember (mergeConfigFunc' conf a c0 ).
    destruct e;inversion H0.
    remember (mergeConfigFunc' conf' a c1).
    destruct e;inversion H1.     subst.
    assert (equivConf c0 c1).
    apply IHl with (conf:=conf) (conf':=conf');auto.
    unfold equivConf in H2.
    unfold equivConf in H. 
     repeat match goal with
            | [ H: _ /\ _ |- _ ] => destruct H

                     end. 
    
   unfold  mergeConfigFunc' in *.
  
    rewrite <- H2 in Heqe0.
    rewrite <- H3 in Heqe0.
    rewrite <- H in Heqe0.
    rewrite <- H10 in Heqe0.
    
    destruct ( mergeDataStateFunc (datastate conf) (datastate a) (datastate c0));inversion Heqe. 
    clear H16.
    destruct ( mergeControlStateFunc (controlstate conf) (controlstate a) (controlstate c0));inversion Heqe.
    inversion Heqe0;subst.
    split;simpl;auto. split;auto.
    repeat(split;try (apply Permutation_app_head;auto)).

     unfold incl in *.
    intros.
    rewrite in_app_iff.
    rewrite in_app_iff in H16.
    destruct H16;intuition;auto.

      unfold incl in *.
    intros.
    rewrite in_app_iff.
    rewrite in_app_iff in H16.
    destruct H16;intuition;auto.

      unfold incl in *.
    intros.
    rewrite in_app_iff.
    rewrite in_app_iff in H16.
    destruct H16;intuition;auto.

      unfold incl in *.
    intros.
    rewrite in_app_iff.
    rewrite in_app_iff in H16.
    destruct H16;intuition;auto.
    
Qed.

    
Lemma mergeConfigFuncEquivExists: forall M (conf conf' a: configuration M) v1,
    equivConf conf conf' ->
    Result v1 = mergeConfigFunc' conf conf a ->
    (exists v2, Result v2 = mergeConfigFunc' conf' conf' a /\ equivConf v1 v2).
Proof.
  intros.
  unfold equivConf in H.
  unfold mergeConfigFunc' in *.  
   repeat match goal with
            | [ H: _ /\ _ |- _ ] => destruct H

          end.
   rewrite <- H1. rewrite <- H.
   remember (mergeDataStateFunc (datastate conf) (datastate conf) (datastate a)).
   destruct e;inversion H0.
   remember (mergeControlStateFunc (controlstate conf) (controlstate conf) (controlstate a)).
   destruct e;inversion H0.
   exists ( {|
      datastate := v;
      controlstate := v0;
      raisedevents := raisedevents conf' ++ raisedevents a;
      exportedevents := exportedevents conf' ++ exportedevents a;
      finishedscenarios := finishedscenarios conf' ++ finishedscenarios a;
      sceEventMap := sceEventMap conf' ++ sceEventMap a |}).
   split;auto.
   split;simpl;auto.    split;auto.
   repeat (split; try (apply Permutation_app_tail;auto)).

     unfold incl in *.
    intros.
    rewrite in_app_iff.
    rewrite in_app_iff in H8.
    destruct H8;intuition;auto.

    
     unfold incl in *.
    intros.
    rewrite in_app_iff.
    rewrite in_app_iff in H8.
    destruct H8;intuition;auto.
    
     unfold incl in *.
    intros.
    rewrite in_app_iff.
    rewrite in_app_iff in H8.
    destruct H8;intuition;auto.
    
     unfold incl in *.
    intros.
    rewrite in_app_iff.
    rewrite in_app_iff in H8.
    destruct H8;intuition;auto.

  
Qed.



Lemma mergeConfigFuncEquivExists': forall M (conf conf' a b c: configuration M) v1,
    equivConf conf conf' ->
    equivConf b c ->
    Result v1 = mergeConfigFunc' conf a b ->
    (exists v2, Result v2 = mergeConfigFunc' conf' a c /\ equivConf v1 v2).
Proof.
  intros.
  unfold equivConf in H. unfold equivConf in H0. 
  unfold mergeConfigFunc' in *.  
   repeat match goal with
            | [ H: _ /\ _ |- _ ] => destruct H

          end.
   rewrite <- H. rewrite <- H0. rewrite <- H9. rewrite <- H2. 
   remember (mergeDataStateFunc (datastate conf) (datastate a) (datastate b)).
   destruct e;inversion H1.
   remember (mergeControlStateFunc (controlstate conf) (controlstate a) (controlstate b)).
   destruct e;inversion H1.
   exists ({|
      datastate := v;
      controlstate := v0;
      raisedevents := raisedevents a ++ raisedevents c;
      exportedevents := exportedevents a ++ exportedevents c;
      finishedscenarios := finishedscenarios a ++ finishedscenarios c;
      sceEventMap := sceEventMap a ++ sceEventMap c |}).
   split;auto.
   split;simpl;auto.    split;auto.
   repeat (split; try (apply Permutation_app_head;auto)). 

   
     unfold incl in *.
    intros.
    rewrite in_app_iff.
    rewrite in_app_iff in H16.
    destruct H16;intuition;auto.

     unfold incl in *.
    intros.
    rewrite in_app_iff.
    rewrite in_app_iff in H16.
    destruct H16;intuition;auto.

     unfold incl in *.
    intros.
    rewrite in_app_iff.
    rewrite in_app_iff in H16.
    destruct H16;intuition;auto.

     unfold incl in *.
    intros.
    rewrite in_app_iff.
    rewrite in_app_iff in H16.
    destruct H16;intuition;auto.
    

Qed.


  
Lemma innterCombineFuncEquivExist: forall M (l: list (configuration M))  (conf conf': configuration M)  v1,
    equivConf conf conf' ->
    Some v1 = innerCombineFunc'''' conf l ->
    (exists v2, Some v2 = innerCombineFunc'''' conf' l /\
    equivConf v1 v2). 
Proof.
  intros M l.
  induction l.
  - intros.
    simpl in H0. 
    inversion H0.
  -
    intros.
    simpl in *.
    
    destruct l.
     
    remember (mergeConfigFunc' conf conf a).
    destruct e;inversion H0.
    pose proof mergeConfigFuncEquivExists. subst. 
    assert (exists v2 : configuration M, Result v2 = mergeConfigFunc' conf' conf' a /\ equivConf v v2).
    apply H1 with (conf:=conf);auto. destruct H2. 
    destruct H2.
    rewrite <- H2.   exists x;auto.
    remember (innerCombineFunc'''' conf (c :: l)).
    destruct o;inversion H0.
    apply IHl with (conf':=conf') in Heqo;auto. 
    destruct Heqo.
    destruct H1. rewrite <- H1.
    remember (mergeConfigFunc' conf a c0). destruct e;inversion H0. 
    subst.
    pose proof mergeConfigFuncEquivExists'. 
    apply H4 with (conf':=conf') (c:=x) in Heqe;auto.
    destruct Heqe. destruct H5. 
    rewrite <- H5. exists x0;auto. 
Qed.




Lemma mergeDataStateFuncEquivExist : forall ds ds1 ds2 v1 v2 ,
    Result v1 =  mergeDataStateFunc ds ds ds1 ->
    Result v2 = mergeDataStateFunc ds ds2 v1 ->
    (exists v3 v4, Result v3 = mergeDataStateFunc ds ds ds2 /\
    Result v4 = mergeDataStateFunc ds ds1 v3 /\
    v2 = v4).
Proof.
  intro ds;induction ds.
  - intros.  destruct ds1;destruct ds2. simpl in *.
    inversion H;subst.  inversion H0;subst.  exists nil. exists nil;split;auto.
    simpl in H0. inversion H0. 
    simpl in H. inversion H.
    simpl in H. inversion H. 
 
  -  intros.
     destruct ds1. simpl in H. destruct a;destruct p. inversion H.
     destruct ds2. simpl in H0. destruct a;destruct p. destruct p0. inversion H0.
     simpl in *.
     destruct a;destruct p0. destruct p1. destruct p. destruct p. destruct p0.
     destruct ( atom_eq_dec a a). Focus 2. contradiction.
     destruct (atom_eq_dec a a1).  Focus 2. inversion H.
     destruct (typ_eq_dec t t). Focus 2. contradiction.
     destruct (typ_eq_dec t t0). Focus 2. inversion H. subst. 
  
     remember (mergeDataStateFunc ds ds ds1).
     destruct e0;inversion H. clear H2.
  
     destruct (range_typ_dec r r0). subst. 
     inversion H;subst.
     destruct (atom_eq_dec a1 a0).
     Focus 2. inversion H0. subst. 
     destruct (atom_eq_dec a0 a0). 
     Focus 2. contradiction.
     destruct (typ_eq_dec t0 t1). Focus 2.  inversion H0.
     subst. destruct (typ_eq_dec t1 t1). Focus 2. inversion H0. 
     remember (mergeDataStateFunc ds ds2 v).
     destruct e3;inversion H0.
     destruct (range_typ_dec r1 r0).
     subst.
     destruct (range_typ_dec r0 r0). Focus 2. contradiction.
     assert (exists v3 v4 : list (atom * (typ * range_typ)),
           Result v3 = mergeDataStateFunc ds ds ds2 /\
           Result v4 = mergeDataStateFunc ds ds1 v3 /\ v0 = v4).
     apply IHds with (v1:=v);auto.
     destruct H1. destruct H1.
     destruct H1.

     rewrite <- H1.   destruct H3.
     subst. exists (((a0, (t1, r0)) :: x) ).
     rewrite <- H3.
     destruct (atom_eq_dec a0 a0). Focus 2. contradiction.
     destruct ( typ_eq_dec t1 t1).
     Focus 2.  contradiction.
     destruct (range_typ_dec r0 r0).
     Focus 2.  contradiction.
     subst.
     inversion H0;subst.
       
     exists (((a0, (t1, r0)) :: x0)).  split;auto.

     destruct (range_typ_dec r0 r0).
     Focus 2. contradiction.
     inversion H0.
     destruct (range_typ_dec r0 r1).
     subst.   contradiction.
       assert (exists v3 v4 : list (atom * (typ * range_typ)),
           Result v3 = mergeDataStateFunc ds ds ds2 /\
           Result v4 = mergeDataStateFunc ds ds1 v3 /\ v0 = v4).
       apply IHds with (v1:=v);auto.
    
     destruct H1. destruct H1.
     destruct H1.

     rewrite <- H1.   destruct H4.
     subst. exists (((a0, (t1, r1)) :: x) ).
       destruct (atom_eq_dec a0 a0). Focus 2. contradiction.
     destruct ( typ_eq_dec t1 t1).
     Focus 2.  contradiction.
     destruct (range_typ_dec r0 r1). subst. 
contradiction.   
     subst.
    rewrite <- H4.    
       
     exists (((a0, (t1, r1)) :: x0)).  split;auto.
     destruct (range_typ_dec r r).
     Focus 2.  contradiction.
    inversion H;subst.      
    destruct ( atom_eq_dec a1 a0).
    Focus 2.   inversion H0.
    subst.
    destruct (atom_eq_dec a0 a0).
    Focus 2.   inversion H0.
    destruct (typ_eq_dec t0 t1).
    subst.    destruct (typ_eq_dec t1 t1).
    Focus 2.  contradiction.
    remember (mergeDataStateFunc ds ds2 v).
    destruct e4;inversion H0.
    destruct (range_typ_dec r1 r0).
    subst.
    inversion H2.

     assert (exists v3 v4 : list (atom * (typ * range_typ)),
           Result v3 = mergeDataStateFunc ds ds ds2 /\
           Result v4 = mergeDataStateFunc ds ds1 v3 /\ v0 = v4).
       apply IHds with (v1:=v);auto.
    
     destruct H1. destruct H1.
     destruct H1.

     rewrite <- H1.   destruct H4.
     subst.
     destruct (range_typ_dec r r0 ).
 subst. contradiction.      exists (((a0, (t1, r0)) :: x) ).
 destruct (atom_eq_dec a0 a0).
    Focus 2.   contradiction. 
    destruct (typ_eq_dec t1 t1).
    Focus 2.  contradiction.
    rewrite <- H4.
    
  
    destruct (range_typ_dec r0 r0).
  Focus 2.     contradiction. exists (((a0, (t1, r0)) :: x0)). split;auto. 
 
    destruct (range_typ_dec r1 r). 
    subst.

     inversion H2.

     assert (exists v3 v4 : list (atom * (typ * range_typ)),
           Result v3 = mergeDataStateFunc ds ds ds2 /\
           Result v4 = mergeDataStateFunc ds ds1 v3 /\ v0 = v4).
       apply IHds with (v1:=v);auto.
    
     destruct H1. destruct H1.
     destruct H1.

     rewrite <- H1.   destruct H4.
     subst.
     destruct (range_typ_dec r r).
Focus 2.  subst. contradiction.      exists (((a0, (t1, r)) :: x) ).
 destruct (atom_eq_dec a0 a0).
    Focus 2.   contradiction. 
    destruct (typ_eq_dec t1 t1).
    Focus 2.  contradiction.
    rewrite <- H4.
    destruct (range_typ_dec r0 r).
    subst. contradiction.
     destruct (range_typ_dec r r).
Focus 2.  subst. contradiction.      exists (((a0, (t1, r0)) :: x0) ).
    split;auto. 
destruct (range_typ_dec r0 r ). 
subst. contradiction.
inversion H0.
inversion H0. 
Qed.


Lemma mergeControlStateFuncEquivExist : forall ds ds1 ds2 v1 v2 ,
    Result v1 =  mergeControlStateFunc ds ds ds1 ->
    Result v2 = mergeControlStateFunc ds ds2 v1 ->
    (exists v3 v4, Result v3 = mergeControlStateFunc ds ds ds2 /\
    Result v4 = mergeControlStateFunc ds ds1 v3 /\
    v2 = v4).
Proof.
  intro ds;induction ds.
  - intros.  destruct ds1;destruct ds2. simpl in *.
    inversion H;subst.  inversion H0;subst.  exists nil. exists nil;split;auto.
    simpl in H0. inversion H0. 
    simpl in H. inversion H.
    simpl in H. inversion H. 
 
  -  intros.
     destruct ds1. simpl in H. destruct a.  inversion H.
     destruct ds2. simpl in H0. destruct a.  inversion H0.
     simpl in *.
     destruct a;destruct p. destruct p0.
     destruct (scenario_dec s s).
     Focus 2. contradiction .
     destruct (scenario_dec s s1).
     Focus 2. inversion H.
     subst.
     remember (mergeControlStateFunc ds ds ds1).
     destruct e0;inversion H.     
     destruct (string_dec s0 s2). subst.
     inversion H2;subst.      
     destruct (scenario_dec s1 s3).
     Focus 2.  inversion H0.
     subst. destruct (scenario_dec s3 s3).  Focus 2. contradiction.
     remember (mergeControlStateFunc ds ds2 v). destruct e1;inversion H0.
     clear H3. destruct (string_dec s4 s2).  subst.
     inversion H0;subst.
     assert ( exists v3 v4 : list (scenario * scenario_state),
           Result v3 = mergeControlStateFunc ds ds ds2 /\
           Result v4 = mergeControlStateFunc ds ds1 v3 /\ v0 = v4).
     eapply IHds. apply Heqe0. auto.
     destruct H1. destruct H1. destruct H1. destruct H3.
     subst.  rewrite <- H1.   destruct (string_dec s2 s2). Focus 2. contradiction.
     exists ((s3, s2) :: x) .
     destruct (scenario_dec s3 s3). Focus 2. contradiction.
     rewrite <- H3. destruct (string_dec s2 s2).    Focus 2.   contradiction.
     exists ((s3, s2) :: x0);split;auto.
     destruct (string_dec s2 s2).
     Focus 2.  contradiction.
       assert ( exists v3 v4 : list (scenario * scenario_state),
           Result v3 = mergeControlStateFunc ds ds ds2 /\
           Result v4 = mergeControlStateFunc ds ds1 v3 /\ v0 = v4).
       eapply IHds. apply Heqe0. auto.
       destruct H1. destruct H1. destruct H1. destruct H3. subst.    
   rewrite <- H1. 
   destruct (string_dec s2 s4). subst. contradiction.
   exists ((s3, s4) :: x).
   destruct (scenario_dec s3 s3). Focus 2. contradiction. 
   rewrite <- H3.
   destruct (string_dec s2 s4). subst.   contradiction.
   exists ((s3, s4) :: x0); inversion H0. split;auto. 
   destruct (string_dec s0 s0). Focus 2.  contradiction.
   inversion H;subst.
   destruct (scenario_dec s1 s3). subst. destruct (scenario_dec s3 s3). Focus 2. contradiction.
   remember (mergeControlStateFunc ds ds2 v). destruct e2;inversion H0.
   destruct (string_dec s4 s2).
   inversion H3.
      assert ( exists v3 v4 : list (scenario * scenario_state),
           Result v3 = mergeControlStateFunc ds ds ds2 /\
           Result v4 = mergeControlStateFunc ds ds1 v3 /\ v0 = v4).
      eapply IHds. apply Heqe0. auto.
   destruct H1. destruct H1. destruct H1. destruct H5. subst.    
   rewrite <- H1. 
   destruct (string_dec s0 s2).
   contradiction. exists ((s3, s2) :: x).
   destruct (scenario_dec s3 s3). 
   Focus 2. contradiction.
   rewrite <- H5.
   destruct (string_dec s2 s2). 
  Focus 2. contradiction.
  exists  ((s3, s2) :: x0) .      split;auto.
  destruct (string_dec s4 s0). subst.  inversion H3;subst.


      assert ( exists v3 v4 : list (scenario * scenario_state),
           Result v3 = mergeControlStateFunc ds ds ds2 /\
           Result v4 = mergeControlStateFunc ds ds1 v3 /\ v0 = v4).
      eapply IHds. apply Heqe0. auto.
   destruct H1. destruct H1. destruct H1. destruct H4. subst.    
   rewrite <- H1. 
   destruct (string_dec s0 s0).
Focus 2.    contradiction. exists ((s3, s0) :: x).
   destruct (scenario_dec s3 s3). 
   Focus 2. contradiction.
rewrite <- H4. 
   destruct (string_dec s2 s0). subst. contradiction. 
destruct (string_dec s0 s0). 
Focus 2. contradiction.   exists ((s3, s2) :: x0);split;auto.

destruct (string_dec s2 s0). subst. inversion H3;subst.
contradiction. 
inversion H0. inversion H0. 
Qed.

Lemma mergeConfigFuncBothExist: forall M (conf x y v v0: configuration M),
    Result v = mergeConfigFunc' conf conf x ->
    Result v0 = mergeConfigFunc' conf y v ->
    (exists c v2, Result c = mergeConfigFunc' conf conf y /\ Result v2 = mergeConfigFunc' conf x c
                  /\ equivConf v0 v2).                                                             Proof.
  intros.
  unfold  mergeConfigFunc' in *.
  remember (mergeDataStateFunc (datastate conf) (datastate conf) (datastate x) ).
  destruct e;inversion H.
  remember (mergeControlStateFunc (controlstate conf) (controlstate conf) (controlstate x)).
  destruct e;inversion H.
  inversion H;subst. clear H4.  clear H.  
  simpl in *.
  remember (mergeDataStateFunc (datastate conf) (datastate y) v1).
  destruct e;inversion H0.
  remember (mergeControlStateFunc (controlstate conf) (controlstate y) v2).  
  destruct e;inversion H1.
  subst. clear H1;clear H0.   clear H2.
  pose proof mergeDataStateFuncEquivExist.
  pose proof mergeControlStateFuncEquivExist.  
  assert ( exists v3 v4 : list (atom * (typ * range_typ)),
        Result v3 = mergeDataStateFunc (datastate conf) (datastate conf)  (datastate y) /\
        Result v4 = mergeDataStateFunc (datastate conf) (datastate x) v3 /\ v = v4).
  eapply H.  apply Heqe.  auto.
  assert ( exists v v' ,
        Result v = mergeControlStateFunc (controlstate conf) (controlstate conf)  (controlstate y) /\
        Result v' = mergeControlStateFunc (controlstate conf) (controlstate x) v /\ v3 = v').
  eapply H0.
  apply Heqe0. auto. 
  repeat match goal with
           | [ H: _ /\ _ |- _ ] => destruct H
            | [ H: exists _, _ |- _] => destruct H
            

          end. subst. 
  rewrite <- H1. rewrite <- H2.
  exists ({|
      datastate := x2;
      controlstate := x0;
      raisedevents := raisedevents conf ++ raisedevents y;
      exportedevents := exportedevents conf ++ exportedevents y;
      finishedscenarios := finishedscenarios conf ++ finishedscenarios y;
      sceEventMap := sceEventMap conf ++ sceEventMap y |}). 
  simpl. 
  rewrite <- H5. rewrite <- H3.
   exists ({|
      datastate := x3;
      controlstate := x1;
      raisedevents := raisedevents x ++ raisedevents conf ++ raisedevents y;
      exportedevents := exportedevents x ++ exportedevents conf ++ exportedevents y;
      finishedscenarios := finishedscenarios x ++ finishedscenarios conf ++ finishedscenarios y;
      sceEventMap := sceEventMap x ++ sceEventMap conf ++ sceEventMap y |}).  
 split;auto. split;auto. split;simpl;auto. 
 split;auto.

 split.

  unfold incl in *.
    intros.
    rewrite in_app_iff.  rewrite in_app_iff. 
    rewrite in_app_iff in H4.  rewrite in_app_iff in H4.
    destruct H4;intuition;auto.

    split. 

   unfold incl in *.
    intros.
    rewrite in_app_iff.  rewrite in_app_iff. 
    rewrite in_app_iff in H4.  rewrite in_app_iff in H4.
    destruct H4;intuition;auto.
 
 (* SearchAbout Permutation.
  assert (Permutation (raisedevents y ++ raisedevents conf ++ raisedevents x) (raisedevents conf  ++ raisedevents y ++ raisedevents x) ). 
   rewrite app_assoc.     rewrite app_assoc.
   SearchAbout Permutation. 
  apply Permutation_app_tail;auto. apply Permutation_app_comm;auto. 
  assert (Permutation (raisedevents x ++ raisedevents conf ++ raisedevents y) (raisedevents conf ++ raisedevents x ++ raisedevents y)).
    rewrite app_assoc.     rewrite app_assoc.
  apply Permutation_app_tail;auto. apply Permutation_app_comm;auto.            
  split.  eapply Permutation_trans. apply H4.
  apply Permutation_sym. eapply Permutation_trans. apply H6.
 apply Permutation_app_head;auto. apply Permutation_app_comm;auto.   
*)
 split. 
 assert (Permutation (finishedscenarios y ++ finishedscenarios conf ++ finishedscenarios x) (finishedscenarios conf  ++ finishedscenarios y ++ finishedscenarios x) ). 
   rewrite app_assoc.     rewrite app_assoc.
  apply Permutation_app_tail;auto. apply Permutation_app_comm;auto. 
  assert (Permutation (finishedscenarios x ++ finishedscenarios conf ++ finishedscenarios y) (finishedscenarios conf ++ finishedscenarios x ++ finishedscenarios y)).
    rewrite app_assoc.     rewrite app_assoc.
  apply Permutation_app_tail;auto. apply Permutation_app_comm;auto.            
 eapply Permutation_trans. apply H4.
  apply Permutation_sym. eapply Permutation_trans. apply H6.
  apply Permutation_app_head;auto. apply Permutation_app_comm;auto.
  split.


   unfold incl in *.
    intros.
    rewrite in_app_iff.  rewrite in_app_iff. 
    rewrite in_app_iff in H4.  rewrite in_app_iff in H4.
    destruct H4;intuition;auto.

    split.
    
     unfold incl in *.
    intros.
    rewrite in_app_iff.  rewrite in_app_iff. 
    rewrite in_app_iff in H4.  rewrite in_app_iff in H4.
    destruct H4;intuition;auto.

   assert (Permutation (sceEventMap y ++ sceEventMap conf ++ sceEventMap x) (sceEventMap conf  ++ sceEventMap y ++ sceEventMap x) ). 
   rewrite app_assoc.     rewrite app_assoc.
  apply Permutation_app_tail;auto. apply Permutation_app_comm;auto. 
  assert (Permutation (sceEventMap x ++ sceEventMap conf ++ sceEventMap y) (sceEventMap conf ++ sceEventMap x ++ sceEventMap y)).
    rewrite app_assoc.     rewrite app_assoc.
  apply Permutation_app_tail;auto. apply Permutation_app_comm;auto.            
 eapply Permutation_trans. apply H4.
  apply Permutation_sym. eapply Permutation_trans. apply H6.
  apply Permutation_app_head;auto. apply Permutation_app_comm;auto.
Qed. 
  


Lemma mergeDataStateFuncEquivExist' : forall ds ds1 ds2 v1 v2 x,
    Result v1 =  mergeDataStateFunc ds ds1 x ->
    Result v2 = mergeDataStateFunc ds ds2 v1 ->
    (exists v3 v4, Result v3 = mergeDataStateFunc ds ds2 x /\
    Result v4 = mergeDataStateFunc ds ds1 v3 /\
    v2 = v4).
Proof.
 intro ds;induction ds.
  - intros.  destruct ds1;destruct ds2;destruct x. simpl in *.
    inversion H;subst.  inversion H0;subst.  exists nil. exists nil;split;auto.
    simpl in H. inversion H. 
    simpl in H0. inversion H0.
    simpl in H. inversion H. 
    simpl in H. inversion H.
    simpl in H. inversion H.
    simpl in H. inversion H.
     simpl in H. inversion H. 
  -  intros.
     destruct ds1. simpl in H. destruct a;destruct p. inversion H.
     destruct ds2. simpl in H0. destruct a;destruct p. destruct p0. inversion H0.
     destruct x. simpl in H. destruct a;destruct p0;destruct p. destruct p1;destruct p. inversion H.
     simpl in *.
      destruct a;destruct p0. destruct p2. destruct p. destruct p. destruct p1. destruct p.
      destruct p0.
      
     repeat (match goal with
             | [H: Result _ = (if range_typ_dec ?a ?b then _ else _) |- _] => destruct (range_typ_dec a b)
             | [H: Result _ = Result ((_, (_, _)) :: _) |- _] => inversion H;subst;clear H                      | [H: Result _ =                                                                                    match mergeDataStateFunc ?a ?b ?c with                                                                                                | Result _  => _                                                                                   | Error _ => _ end |- _] => remember  (mergeDataStateFunc a b c ) as de; destruct de                                                    
             | [H: Result _ = Error _ |- _] => inversion H                                                      | [H: Result _ = if typ_eq_dec ?a ?b then _ else Error _ |- _] => destruct (typ_eq_dec a b)
             | [H: Result _ = if atom_eq_dec ?a ?b then _ else Error _ |- _] => destruct (atom_eq_dec a b)
             | [H1:  Result ?v1 = mergeDataStateFunc ?ds ?ds1 ?x, H2: Result ?v = mergeDataStateFunc ?ds ?ds2 ?v1, H3: forall (ds1 ds2 : value_env) (v1 v2 : list (atom * (typ * range_typ))) (x : value_env),
         Result v1 = mergeDataStateFunc ds ds1 x ->
         Result v2 = mergeDataStateFunc ds ds2 v1 ->
         exists v3 v4 : list (atom * (typ * range_typ)),
           Result v3 = mergeDataStateFunc ds ds2 x /\
           Result v4 = mergeDataStateFunc ds ds1 v3 /\ v2 = v4  |- _] => apply H3 with (ds1:=ds1) (x:=x) in H2;auto;clear H3
             | [H: exists _, _|- _] => destruct H
             | [H: _ /\ _ |- _] => destruct H
             | [H: Result ?x0 = mergeDataStateFunc ?ds ?ds ?ds2 |- exists _ _, Result _ = match mergeDataStateFunc ds ds ds2 with
                           | Result _ => _
                           | Error _ => _ end
                                                                               /\ _] => rewrite <- H;clear H
             | [ H: _ |- exists _ _, (Result _ = if range_typ_dec ?a ?b then _ else _) /\ _] => destruct (range_typ_dec a b)
                                                                                                               | [H: ?a <> ?a |- _] => contradiction
            | [H: ?a <> ?b, H1: ?a = ?b |- _] => subst;contradiction
            | [H: ?a <> ?b, H1: ?b = ?a |- _] => subst;contradiction                                           | [ H: _ |-  exists _ _ ,
    (Result _ = Result ((?a0, (?t2, ?r1)) :: ?x0)) /\
    _] => exists ((a0, (t2, r1)) :: x0)
            | [H: _ |- context[if ?X then _ else _]] =>  destruct X
            | [H:  Result ?x1 = mergeDataStateFunc ?ds ?ds1 ?x0 |- context[match mergeDataStateFunc ?ds ?ds1 ?x0 with | Result _ =>_ | Error _ => _ end]] => rewrite <- H;simpl                                                    
                   end);subst;
                     repeat(match goal with
                          | [H: _ |- exists _,
    Result _ = Result _ /\
    Result _ = Result ((?a0, (?t2, ?r1)) :: ?x1) /\ (?a0, (?t2, ?r1)) :: ?x1 = _] => exists  ((a0, (t2, r1)) :: x1);split;auto
                            end).
Qed.


Lemma mergeControlStateFuncEquivExist' : forall ds ds1 ds2 v1 v2 x,
    Result v1 =  mergeControlStateFunc ds ds1 x ->
    Result v2 = mergeControlStateFunc ds ds2 v1 ->
    (exists v3 v4, Result v3 = mergeControlStateFunc ds ds2 x /\
    Result v4 = mergeControlStateFunc ds ds1 v3 /\
    v2 = v4).
Proof.
 intro ds;induction ds.
  - intros.  destruct ds1;destruct ds2;destruct x. simpl in *.
    inversion H;subst.  inversion H0;subst.  exists nil. exists nil;split;auto.
    simpl in H. inversion H. 
    simpl in H0. inversion H0.
    simpl in H. inversion H. 
    simpl in H. inversion H.
    simpl in H. inversion H.
    simpl in H. inversion H.
     simpl in H. inversion H. 
  -  intros.
     destruct ds1. simpl in H. destruct a. inversion H.
     destruct ds2. simpl in H0. destruct a.  inversion H0.
     destruct x. simpl in H. destruct a;destruct p.  inversion H.
     simpl in *.
     destruct a;destruct p. destruct p1. destruct p0.
     
     repeat (match goal with
             | [H : context[if ?X then _ else _] |- _] => destruct X
                                                                  
             | [H: Result _ = Result ( (_, _) :: _) |- _] => inversion H;subst;clear H                      | [H: Result _ =                                                                                    match mergeControlStateFunc ?a ?b ?c with                                                                                                | Result _  => _                                                                                   | Error _ => _ end |- _] => remember  (mergeControlStateFunc a b c ) as de; destruct de                                                    
             | [H: Result _ = Error _ |- _] => inversion H                                        
             | [H1:  Result ?v1 = mergeControlStateFunc ?ds ?ds1 ?x, H2: Result ?v = mergeControlStateFunc ?ds ?ds2 ?v1, H3: forall (ds1 ds2 : scenario_env) (v1 v2 : list (scenario * scenario_state))
           (x : scenario_env),
         Result v1 = mergeControlStateFunc ds ds1 x ->
         Result v2 = mergeControlStateFunc ds ds2 v1 ->
         exists v3 v4 : list (scenario * scenario_state),
           Result v3 = mergeControlStateFunc ds ds2 x /\
           Result v4 = mergeControlStateFunc ds ds1 v3 /\ v2 = v4  |- _] => apply H3 with (ds1:=ds1) (x:=x) in H2;auto;clear H3
             | [H: exists _, _|- _] => destruct H
             | [H: _ /\ _ |- _] => destruct H
             | [H: Result ?x0 = mergeControlStateFunc ?ds ?ds ?ds2 |- exists _ _, Result _ = match mergeControlStateFunc ds ds ds2 with
                           | Result _ => _
                           | Error _ => _ end
                                                                               /\ _] => rewrite <- H;clear H
             | [ H: _ |- exists _ _, (Result _ = if ?X then _ else _) /\ _] => destruct X                       | [H: ?a <> ?a |- _] => contradiction
            | [H: ?a <> ?b, H1: ?a = ?b |- _] => subst;contradiction
            | [H: ?a <> ?b, H1: ?b = ?a |- _] => subst;contradiction
              | [ H: _ |-  exists _ _ ,
    (Result _ = Result ?Y /\
    _ )] => exists Y
             | [H: _ |- context[if ?X then _ else _]] =>  destruct X                               
            | [H:  Result ?x1 = mergeControlStateFunc ?ds ?ds1 ?x0 |- context[match mergeControlStateFunc ?ds ?ds1 ?x0 with | Result _ =>_ | Error _ => _ end]] => rewrite <- H;simpl
                                    
             end);subst;
                     repeat(match goal with
                          | [H: _ |- exists _,
    Result _ = Result _ /\
    Result _ = Result ?Y /\ ?Y = _] => exists  Y;split;auto end). 
 
Qed.


Lemma mergeConfigFuncBothExist': forall M (conf c0 x y v v0: configuration M),
    Result v = mergeConfigFunc' conf x c0 ->
    Result v0 = mergeConfigFunc' conf y v ->
    (exists c v2, Result c = mergeConfigFunc' conf y c0 /\ Result v2 = mergeConfigFunc' conf x c
                  /\ equivConf v0 v2).                                                             Proof.
    intros.
  unfold  mergeConfigFunc' in *.
  remember (mergeDataStateFunc (datastate conf) (datastate x) (datastate c0) ).
  destruct e;inversion H.
  remember (mergeControlStateFunc (controlstate conf) (controlstate x) (controlstate c0)).
  destruct e;inversion H.
  inversion H;subst. clear H4.  clear H.  
  simpl in *.
  remember (mergeDataStateFunc (datastate conf) (datastate y) v1).
  destruct e;inversion H0.
  remember (mergeControlStateFunc (controlstate conf) (controlstate y) v2).  
  destruct e;inversion H1.
  subst. clear H1;clear H0.   clear H2.
  pose proof mergeDataStateFuncEquivExist'.
  pose proof mergeControlStateFuncEquivExist'.
  assert (exists v3 v4 : list (atom * (typ * range_typ)),
        Result v3 = mergeDataStateFunc (datastate conf) (datastate y) (datastate c0) /\
        Result v4 = mergeDataStateFunc (datastate conf) (datastate x) v3 /\ v = v4).
  eapply H. apply Heqe. auto.
   assert (exists v3' v4',
        Result v3' = mergeControlStateFunc (controlstate conf) (controlstate y) (controlstate c0) /\
        Result v4' = mergeControlStateFunc (controlstate conf) (controlstate x) v3' /\ v3 = v4').
   eapply H0. apply Heqe0. auto. 
   repeat (match goal with
          | [H: exists _, _|- _] => destruct H
          | [H: _ /\ _ |- _] => destruct H
          end).                                
  subst. 
  rewrite <- H1. rewrite <- H2. exists ({|
      datastate := x2;
      controlstate := x0;
      raisedevents := raisedevents y ++ raisedevents c0;
      exportedevents := exportedevents y ++ exportedevents c0;
      finishedscenarios := finishedscenarios y ++ finishedscenarios c0;
      sceEventMap := sceEventMap y ++ sceEventMap c0 |}).
  simpl in *. 
  rewrite <- H5;rewrite <- H3. 
 exists ({|
      datastate := x3;
      controlstate := x1;
      raisedevents := raisedevents x ++ raisedevents y ++ raisedevents c0;
      exportedevents := exportedevents x ++ exportedevents y ++ exportedevents c0;
      finishedscenarios := finishedscenarios x ++ finishedscenarios y ++ finishedscenarios c0;
      sceEventMap := sceEventMap x ++ sceEventMap y ++ sceEventMap c0 |} ).
  split;auto. 
  split;auto.
split;simpl;auto. 
split;auto. 

repeat(split; (try ( rewrite app_assoc;rewrite app_assoc;apply Permutation_app_tail;apply Permutation_app_comm  ))). 

 unfold incl in *.
    intros.
    rewrite in_app_iff.  rewrite in_app_iff. 
    rewrite in_app_iff in H4.  rewrite in_app_iff in H4.
    destruct H4;intuition;auto.

     unfold incl in *.
    intros.
    rewrite in_app_iff.  rewrite in_app_iff. 
    rewrite in_app_iff in H4.  rewrite in_app_iff in H4.
    destruct H4;intuition;auto.


     unfold incl in *.
    intros.
    rewrite in_app_iff.  rewrite in_app_iff. 
    rewrite in_app_iff in H4.  rewrite in_app_iff in H4.
    destruct H4;intuition;auto.


     unfold incl in *.
    intros.
    rewrite in_app_iff.  rewrite in_app_iff. 
    rewrite in_app_iff in H4.  rewrite in_app_iff in H4.
    destruct H4;intuition;auto.

 
 Qed.

Lemma innterCombineFuncEquivExist': forall M (l l': list (configuration M))  (conf : configuration M)  v1,
    Permutation l l' ->
    Some v1 = innerCombineFunc'''' conf l ->
    (exists v2, Some v2 = innerCombineFunc'''' conf l' /\
    equivConf v1 v2). 
Proof.
  intros.
  generalize dependent conf.  generalize dependent v1.
  induction H.
  -  intros.
     simpl in H0.
     inversion H0.
  - intros.
    simpl in *.
    destruct l.
    destruct l'.
    remember (mergeConfigFunc' conf conf x).
    destruct e;inversion H0.
    subst.
    exists v;auto. split;auto.  apply equivConf_Refl;auto. 
    SearchAbout Permutation.   apply Permutation_nil_cons in H;inversion H.
    destruct l'.
    apply Permutation_sym in H.   apply Permutation_nil_cons in H;inversion H.   
    remember (innerCombineFunc'''' conf (c :: l)).
    destruct o;inversion H0.
    apply IHPermutation in Heqo;auto. destruct Heqo. destruct H1. rewrite <- H1.
    remember (mergeConfigFunc' conf x c1).
    destruct e;inversion H0.
    subst.
    pose proof mergeConfigFuncEquivExists'.
    apply H4 with (conf':=conf) (c:=x0) in Heqe;auto.     
    destruct Heqe.
    destruct H5.
    rewrite <- H5.  exists x1;auto. apply equivConf_Refl;auto.
 
  - intros.
    simpl in *.
    destruct l.
    remember ( mergeConfigFunc' conf conf x ).
    destruct e;inversion H0.
    remember (mergeConfigFunc' conf y v).
    destruct e;inversion H0.
    subst.
   pose proof mergeConfigFuncBothExist.  
   assert (exists c v2 : configuration M,
        Result c = mergeConfigFunc' conf conf y /\
        Result v2 = mergeConfigFunc' conf x c /\ equivConf v0 v2).
   eapply H.    apply Heqe. auto.
   destruct H2. destruct H2. destruct H2. destruct H3.
   rewrite <- H2.  rewrite <- H3. exists x1;auto.
   remember (innerCombineFunc'''' conf (c :: l)).
   destruct o;inversion H0.
   remember (mergeConfigFunc' conf x c0).
   destruct e;inversion H1.
   remember (mergeConfigFunc' conf y v).
   destruct e.
   inversion H0. subst.
   Focus 2.   inversion H0.
   pose proof mergeConfigFuncBothExist'.
   assert ( exists c v2 : configuration M,
        Result c = mergeConfigFunc' conf y c0 /\
        Result v2 = mergeConfigFunc' conf x c /\ equivConf v0 v2).
  eapply H. apply Heqe. auto.  
  repeat(match goal with
         | [H: exists _, _ |- _] => destruct H
         | [H: _ /\ _ |- _] => destruct H
         end                              
        ).
  rewrite <- H3.   rewrite <- H4;auto. exists x1;auto.
  - intros.
     apply IHPermutation1 in H1.     
     destruct H1. destruct H1.  apply IHPermutation2 in H1.
     destruct H1. exists x0. split;intuition.  eapply equivConf_Trans. apply H2;auto. auto. 
Qed.
 
   Lemma mergeDataStateFuncEquiv': forall ds ds1 ds2 c1 v1 v2 v3 v4,
    Result v1 =  mergeDataStateFunc ds ds1 c1 ->
    Result v2 = mergeDataStateFunc ds ds2 v1 ->
    Result v3 = mergeDataStateFunc ds ds2 c1 ->
    Result v4 = mergeDataStateFunc ds ds1 v3 ->
    v2 = v4.
Proof.
  intro ds;induction ds.
  - intros.  destruct ds1;destruct ds2;destruct c1. simpl in *.
    inversion H;inversion H1;subst. inversion H0;inversion H2;auto.
    simpl in H. inversion H.
    simpl in H0. inversion H0.
    simpl in H. inversion H.
    simpl in H;inversion H.
    simpl in H;inversion H.
    simpl in H;inversion H.
   simpl in H;inversion H.     
  -  intros.
     destruct ds1. simpl in H. destruct a;destruct p. inversion H.
     destruct ds2. simpl in H0. destruct a;destruct p. destruct p0. inversion H0.
     destruct c1. simpl in H. destruct a. destruct p1. destruct p. destruct p. inversion H. 
     simpl in *.
     destruct a;destruct p0. destruct p2. destruct p. destruct p. destruct p1. destruct p. destruct p0. 
     destruct ( atom_eq_dec a a1). Focus 2. inversion H.
     destruct (atom_eq_dec a a2).  Focus 2. inversion H. subst. 
     destruct (typ_eq_dec t t0). Focus 2. inversion H.
     destruct (typ_eq_dec t t1). Focus 2. inversion H. subst. 
     destruct (atom_eq_dec a2 a0). Focus 2. inversion H1.
     destruct (typ_eq_dec t1 t2). Focus 2. inversion H1.
     remember (mergeDataStateFunc ds ds1 c1).
     destruct e1;inversion H. clear H4. subst. 
     remember ( mergeDataStateFunc ds ds2 c1).
     destruct e;inversion H1. clear H4.
     subst.
     destruct (range_typ_dec r0 r1). subst.
     inversion H;subst.
     
    
     destruct (range_typ_dec r2 r1).
     inversion H1;subst. 
     destruct (atom_eq_dec a0 a0).
     Focus 2. contradiction.
     destruct (typ_eq_dec t2 t2). 
     Focus 2. contradiction.
     remember (mergeDataStateFunc ds ds2 v).
     destruct e1;inversion H0. clear H4.
     remember (mergeDataStateFunc ds ds1 v0).
     destruct e1;inversion H2.
     clear H4. destruct (range_typ_dec r1 r1). Focus 2. contradiction.
     inversion H0;inversion H2. f_equal.
     eapply IHds;auto. apply Heqe1. apply Heqe0. apply Heqe. auto.
     destruct (atom_eq_dec a0 a0). Focus 2. inversion H0.
     destruct (typ_eq_dec t2 t2). Focus 2. inversion H0.
     remember (mergeDataStateFunc ds ds2 v).
     destruct e1;inversion H0.
     clear H4.
     destruct (range_typ_dec r2 r).
     subst.
     inversion H0. inversion H1;subst. 
     destruct (atom_eq_dec a0 a0). Focus 2. inversion H2.
     destruct (typ_eq_dec t2 t2). Focus 2.  inversion H2.

     
     destruct (range_typ_dec r1 r1). Focus 2. contradiction. 
    
    
       remember ( mergeDataStateFunc ds ds1 v0 ).    
       destruct e4;inversion H2.
        f_equal.
        eapply IHds;auto. apply Heqe1. apply Heqe0. apply Heqe. auto.

        
       destruct (range_typ_dec r1 r). Focus 2. inversion H0.
       inversion H0;subst. inversion H1;subst. 
    
       destruct (atom_eq_dec a0 a0). Focus 2. contradiction.
       destruct (typ_eq_dec t2 t2). Focus 2. contradiction.
       remember (mergeDataStateFunc ds ds1 v0). 
       destruct e3;inversion H2.
    
       destruct (range_typ_dec r r2). symmetry in e3. 
       contradiction.
    
       inversion H0;inversion H4.
       f_equal.
       eapply IHds;auto. apply Heqe1. apply Heqe0. apply Heqe. auto.
      destruct (range_typ_dec r0 r). 
      subst. inversion H;subst. destruct (range_typ_dec r2 r1).
     subst.       
inversion H1;subst.     
        destruct (atom_eq_dec a0 a0).
        Focus 2.      inversion H0.
        destruct (typ_eq_dec t2 t2). Focus 2. contradiction.
        remember (mergeDataStateFunc ds ds2 v ).
        destruct e1;inversion H0. clear H4.
        remember (mergeDataStateFunc ds ds1 v0 ).
        destruct e1;inversion H2.
        
        destruct (range_typ_dec r r1).
        subst.      contradiction. inversion H4;subst. 
        f_equal.  
        eapply IHds;auto. apply Heqe1. apply Heqe0. apply Heqe. auto.
        destruct (range_typ_dec r2 r).
        subst.    inversion H1;subst.

         destruct (atom_eq_dec a0 a0).
        Focus 2.      inversion H0.
        destruct (typ_eq_dec t2 t2). Focus 2. contradiction.
        remember (mergeDataStateFunc ds ds2 v ).
        destruct e1;inversion H0. clear H4.
        remember (mergeDataStateFunc ds ds1 v0 ).
        destruct e1;inversion H2.
 destruct (range_typ_dec r r1).
        subst.      contradiction. inversion H4;subst. 
        f_equal.  
        eapply IHds;auto. apply Heqe1. apply Heqe0. apply Heqe. auto.
        
        destruct (range_typ_dec r1 r ). subst. contradiction. inversion H1.
        destruct (range_typ_dec r1 r).
        subst.  inversion H;subst. destruct (range_typ_dec r2 r). subst.
        inversion H1;subst. 

         destruct (atom_eq_dec a0 a0).
        Focus 2.      inversion H0.
        destruct (typ_eq_dec t2 t2). Focus 2. contradiction.
        remember (mergeDataStateFunc ds ds2 v ).
        destruct e1;inversion H0. clear H4.
        remember (mergeDataStateFunc ds ds1 v0 ).
        destruct e1;inversion H2. clear H4. destruct (range_typ_dec r r0). subst. contradiction.
        destruct (range_typ_dec r0 r). subst.   contradiction.
        
 destruct (range_typ_dec r r). Focus 2. contradiction. 
       inversion H0;inversion H2.   
        f_equal.  
        eapply IHds;auto. apply Heqe1. apply Heqe0. apply Heqe. auto.
    inversion H1;subst.         

      destruct (atom_eq_dec a0 a0).
        Focus 2.      inversion H0.
        destruct (typ_eq_dec t2 t2). Focus 2. contradiction.
        remember (mergeDataStateFunc ds ds2 v ).
        destruct e1;inversion H0. clear H4.
        remember (mergeDataStateFunc ds ds1 v0 ).
        destruct e1;inversion H2. clear H4. destruct (range_typ_dec r0 r2). subst.
        destruct (range_typ_dec r2 r2). Focus 2.   contradiction.
    
       inversion H0;inversion H2.   
        f_equal.  
        eapply IHds;auto. apply Heqe1. apply Heqe0. apply Heqe. auto.
        

        destruct (range_typ_dec r2 r0).
        subst.  contradiction.
        destruct ( range_typ_dec r0 r). subst. contradiction.
        inversion H0.

        inversion H. 
Qed.

Lemma mergeControlStateFuncEquiv': forall ds ds1 ds2 c1 v1 v2 v3 v4,
    Result v1 =  mergeControlStateFunc ds ds1 c1 ->
    Result v2 = mergeControlStateFunc ds ds2 v1 ->
    Result v3 = mergeControlStateFunc ds ds2 c1 ->
    Result v4 = mergeControlStateFunc ds ds1 v3 ->
    v2 = v4.
Proof.
  intro ds;induction ds.
  - intros.  destruct ds1;destruct ds2;destruct c1. simpl in *.
    inversion H;inversion H1;subst. inversion H0;inversion H2;auto.
    simpl in H. inversion H.
    simpl in H0. inversion H0.
    simpl in H. inversion H.
    simpl in H. inversion H.
    simpl in H. inversion H.
    simpl in H. inversion H.
    simpl in H. inversion H.
  -  intros.
     destruct ds1. simpl in H. destruct a.  inversion H.
     destruct ds2. simpl in H0. destruct a.  inversion H0.
     destruct c1.
    simpl in H. destruct a.    destruct p;auto. inversion H.  
     simpl in *.
     destruct a. destruct p;destruct p1. destruct p0.
     
     destruct (scenario_dec s s1);inversion H. clear H4. 
     destruct (scenario_dec s s3);inversion H. clear H4. subst.
     remember (mergeControlStateFunc ds ds1 c1).
     destruct e;inversion H. clear H4.
     destruct (string_dec s2 s4). subst.
     inversion H;subst. 
     destruct (scenario_dec s3 s5).
     Focus 2.     inversion H0.
     destruct (scenario_dec s3 s3).
     Focus 2.  inversion H0.     
     
     remember (mergeControlStateFunc ds ds2 c1).
     destruct e1;inversion H1. clear H4.
     remember (mergeControlStateFunc ds ds2 v ).
     destruct e1;inversion H0. clear H4. subst. 
     destruct (string_dec s6 s4).
     subst.   inversion H1;subst.
     destruct (scenario_dec s5 s5). Focus 2. inversion H2.
     remember (mergeControlStateFunc ds ds1 v0).
     destruct e1;inversion H2.
     destruct (string_dec s4 s4). Focus 2. contradiction. 
     inversion H0;inversion H2;subst.   f_equal.
          
   
    eapply IHds. apply Heqe. apply Heqe0.  apply Heqe1. auto. 
    destruct (string_dec s6 s0).
    subst.
    inversion H1;subst.
    
    destruct (scenario_dec s5 s5). Focus 2. contradiction.
    remember (mergeControlStateFunc ds ds1 v0).
    destruct e1;inversion H2.
    destruct ( string_dec s4 s4).   Focus 2.   contradiction.
    inversion H0;inversion H2.   f_equal.
    eapply IHds. apply Heqe. apply Heqe0.  apply Heqe1. auto.
    destruct (string_dec s4 s0).
    subst.
    inversion H1;subst. 
  destruct (scenario_dec s5 s5). Focus 2. contradiction.
    remember (mergeControlStateFunc ds ds1 v0).
    destruct e1;inversion H2.
   destruct (string_dec s0 s6). subst. contradiction. 
      inversion H0;inversion H2.   f_equal.
      eapply IHds. apply Heqe. apply Heqe0.  apply Heqe1. auto.

      inversion H0.
      destruct (string_dec s2 s0).
    subst.       
    inversion H;subst. 

    destruct (scenario_dec s3 s5).
    subst.
    destruct (scenario_dec s5 s5). Focus 2. contradiction.
    remember (mergeControlStateFunc ds ds2 c1).
    destruct e0;inversion H1.
    clear H4.
    remember (mergeControlStateFunc ds ds2 v).
    destruct e0;inversion H0.
   clear H4.     
   destruct (string_dec s6 s4).
   subst.  inversion H1;subst.
   destruct (scenario_dec s5 s5).
   Focus 2.  inversion H2.
   remember (mergeControlStateFunc ds ds1 v0).
   destruct e1;inversion H2.
   destruct ( string_dec s0 s4).
   contradiction.
   inversion H0;inversion H4.
   f_equal.
    eapply IHds. apply Heqe. apply Heqe1.  apply Heqe0. auto.
    destruct (string_dec s6 s0).
    subst. inversion H1;subst.
    destruct (scenario_dec s5 s5). Focus 2. inversion H2.
    remember (mergeControlStateFunc ds ds1 v0).
    destruct e1;inversion H2.
    destruct (string_dec s0 s4).
    contradiction.
    inversion H0;inversion H4;f_equal.
        eapply IHds. apply Heqe. apply Heqe1.  apply Heqe0. auto.

        destruct (string_dec s4 s0).
        symmetry in e0.
        contradiction. 
        inversion H1.
        inversion H1.
   destruct (string_dec s4 s0). subst.          
   inversion H;subst.
   destruct (scenario_dec s3 s5).
   subst.
   remember (mergeControlStateFunc ds ds2 c1).
   destruct e;inversion H1.
   clear H4. destruct (string_dec s6 s0);subst.
   inversion H1;subst.    
   destruct (scenario_dec s5 s5).
   Focus 2. inversion H2.
   remember (mergeControlStateFunc ds ds1 v0).
   destruct e0;inversion H2.
   clear H4.
   remember (mergeControlStateFunc ds ds2 v).
   destruct e0;inversion H0.
   destruct (string_dec s2 s0). contradiction.
   destruct (string_dec s0 s2). symmetry in e0. contradiction.
   destruct (string_dec s0 s0). Focus 2. contradiction.
   inversion H2;inversion H0.  f_equal.
       eapply IHds. apply Heqe. apply Heqe2.  apply Heqe0. auto.  
  inversion H1;subst. 
  destruct (scenario_dec s5 s5).
Focus 2. contradiction.    
remember (mergeControlStateFunc ds ds1 v0).
destruct e0;inversion H2.
clear H4. remember (mergeControlStateFunc ds ds2 v).
destruct e0;inversion H0.
destruct (string_dec s2 s6).
subst. destruct (string_dec s6 s6).
Focus 2. contradiction.
inversion H4;inversion H2. f_equal. 
 eapply IHds. apply Heqe. apply Heqe2.  apply Heqe0. auto.  
 destruct (string_dec s6 s2).
 subst.  contradiction.
 destruct (string_dec s2 s0).
 subst.  contradiction.
 inversion H0. inversion H1.
inversion H.  
Qed.

Lemma innterCombineFuncEquiv: forall M (conf conf': configuration M) l1 l2 v1 v2,
    Permutation l1 l2 ->
    equivConf conf conf' ->
    Some v1 = innerCombineFunc'''' conf l1 ->
    Some v2 = innerCombineFunc'''' conf' l2 ->
    equivConf v1 v2. 
Proof.
   intros. 
  generalize dependent conf; generalize dependent conf'; generalize dependent v1; generalize dependent v2. 
  induction H. 
   - intros.
     simpl in *. inversion H1.
   - intros.
     simpl in *.
     destruct l. destruct l'.
     remember (mergeConfigFunc' conf' conf' x).
     destruct e;inversion H2.      
     remember (mergeConfigFunc' conf conf x).
     destruct e;inversion H1. subst.
     unfold mergeConfigFunc' in Heqe.
     unfold mergeConfigFunc' in Heqe0.
     unfold equivConf in H0.
     repeat match goal with
            | [ H: _ /\ _ |- _ ] => destruct H

                     end.
     rewrite <- H0 in Heqe.
     rewrite <- H3 in Heqe. 
     destruct ( mergeDataStateFunc (datastate conf) (datastate conf) (datastate x));inversion Heqe.     destruct (mergeControlStateFunc (controlstate conf) (controlstate conf) (controlstate x));inversion Heqe0. inversion H11.
     split;simpl;auto. split;auto.
     repeat(split; try (apply Permutation_app_tail;auto)).

      unfold incl in *.
    intros.
    rewrite in_app_iff. 
    rewrite in_app_iff in H10. 
    destruct H10;intuition;auto.

       unfold incl in *.
    intros.
    rewrite in_app_iff. 
    rewrite in_app_iff in H10. 
    destruct H10;intuition;auto.


       unfold incl in *.
    intros.
    rewrite in_app_iff. 
    rewrite in_app_iff in H10. 
    destruct H10;intuition;auto.

       unfold incl in *.
    intros.
    rewrite in_app_iff. 
    rewrite in_app_iff in H10. 
    destruct H10;intuition;auto.
    
    
    apply Permutation_nil_cons in H. inversion H.
    destruct l'.
    apply Permutation_sym in H.   apply Permutation_nil_cons in H. inversion H.
    remember (innerCombineFunc'''' conf' (c0 :: l')). destruct o;inversion H2. clear H4. 
    remember (innerCombineFunc'''' conf (c :: l) ). destruct o;inversion H1. clear H4. 
    assert (equivConf c2 c1).
    apply IHPermutation with (conf:=conf) (conf':=conf');auto.
    apply equivConf_Sym in H3. 
    remember (mergeConfigFunc' conf' x c1 ).
    destruct e;inversion H2.
    remember (mergeConfigFunc' conf x c2).
    destruct e;inversion H1. subst.
    unfold mergeConfigFunc' in Heqe;unfold mergeConfigFunc' in Heqe0.
    unfold equivConf in H0. 
    unfold equivConf in H3.
      repeat match goal with
            | [ H: _ /\ _ |- _ ] => destruct H

                     end.
      rewrite <- H0 in Heqe.
      rewrite <- H11 in Heqe. 
      rewrite  H3 in Heqe.
      rewrite  H4 in Heqe.
      destruct (mergeDataStateFunc (datastate conf) (datastate x) (datastate c2));inversion Heqe. 
      destruct (mergeControlStateFunc (controlstate conf) (controlstate x) (controlstate c2) );inversion H19.
      inversion Heqe0.
      split;simpl;auto. split;auto.
        
      
      repeat(split; try (apply Permutation_app_head;apply Permutation_sym;auto)). 



         unfold incl in *.
    intros.
    rewrite in_app_iff. 
    rewrite in_app_iff in H18. 
    destruct H18;intuition;auto.

      unfold incl in *.
    intros.
    rewrite in_app_iff. 
    rewrite in_app_iff in H18. 
    destruct H18;intuition;auto.

      unfold incl in *.
    intros.
    rewrite in_app_iff. 
    rewrite in_app_iff in H18. 
    destruct H18;intuition;auto.

      unfold incl in *.
    intros.
    rewrite in_app_iff. 
    rewrite in_app_iff in H18. 
    destruct H18;intuition;auto.
    
  
     

   - intros.
     simpl in *. destruct l.
     remember (mergeConfigFunc' conf' conf' y).
     destruct e;inversion H2. 
     remember (mergeConfigFunc' conf' x v).
     destruct e;inversion H2.
     remember ( mergeConfigFunc' conf conf x).
     destruct e;inversion H1.
     subst.
     remember (mergeConfigFunc' conf y v3 ).
     destruct e;inversion H1. subst. clear H1;clear H3;clear H5.
     unfold mergeConfigFunc' in *.
     unfold equivConf in H0.
        repeat match goal with
            | [ H: _ /\ _ |- _ ] => destruct H

               end.
        rewrite <- H in Heqe;rewrite <- H in Heqe0.
        rewrite <- H0 in Heqe;rewrite <- H0 in Heqe0.
        remember (mergeDataStateFunc (datastate conf) (datastate conf) (datastate y)).
        destruct e;inversion Heqe. 
     remember (mergeControlStateFunc (controlstate conf) (controlstate conf) (controlstate y)).        destruct e;inversion Heqe.                                                                           inversion Heqe;subst. 
     clear Heqe.
     clear H9. clear H11.
     remember ( mergeDataStateFunc (datastate conf) (datastate conf) (datastate x)).
     destruct e;inversion Heqe1.
     remember (mergeControlStateFunc (controlstate conf) (controlstate conf) (controlstate x)).
     destruct e;inversion Heqe1.
     subst.      clear H9. simpl in *.  clear Heqe1.
     remember (mergeDataStateFunc (datastate conf) (datastate x) v1).
     destruct e;inversion Heqe0.
     remember ( mergeControlStateFunc (controlstate conf) (controlstate x) v4 ).
     destruct e;inversion Heqe0.
     remember (mergeDataStateFunc (datastate conf) (datastate y) v).
     destruct e;inversion Heqe2.
     remember (mergeControlStateFunc (controlstate conf) (controlstate y) v5).
     destruct e;inversion Heqe2.
     clear H12. clear H11. clear H10. clear H9. clear Heqe2.
     pose proof mergeDataStateFuncEquiv.
     split;simpl;auto.
     apply H8 with (v1:=v) (v3:=v1) (ds:=datastate conf) (ds1:=datastate x) (ds2:=datastate y);auto.
     split.
     pose proof mergeControlStateFuncEquiv.
     apply H9 with (v1:=v5) (v3:=v4) (ds:=controlstate conf) (ds1:=controlstate x) (ds2:=controlstate y);auto.     
     split.

     
     
        unfold incl in *.
    intros.
    rewrite in_app_iff. rewrite in_app_iff. 
    rewrite in_app_iff in H9.  rewrite in_app_iff in H9. 
    destruct H9;intuition;auto.

    split. 
        unfold incl in *.
    intros.
    rewrite in_app_iff. rewrite in_app_iff. 
    rewrite in_app_iff in H9.  rewrite in_app_iff in H9. 
    destruct H9;intuition;auto.

    
    (* assert (Permutation (raisedevents x ++ raisedevents y ++ raisedevents conf)  (raisedevents y ++ raisedevents x ++ raisedevents conf) ).
    SearchAbout app. 
    rewrite app_assoc.     rewrite app_assoc.
    apply Permutation_app_tail;auto. apply Permutation_app_comm;auto.

    
    assert (Permutation (raisedevents y ++ raisedevents conf ++ raisedevents x) (raisedevents x ++ raisedevents y ++ raisedevents conf)).
    apply Permutation_trans with (l':=(raisedevents y ++ raisedevents x ++ raisedevents conf));auto.    apply Permutation_sym;auto.
    assert (Permutation (raisedevents x ++ raisedevents conf' ++ raisedevents y) (raisedevents x ++ raisedevents y ++ raisedevents conf')).
    apply Permutation_app_head;auto.   apply Permutation_app_comm;auto.
    apply Permutation_trans with (l':=(raisedevents x ++ raisedevents y ++ raisedevents conf));auto.
    apply Permutation_sym.   apply  Permutation_trans with (l':=(raisedevents x ++ raisedevents y ++ raisedevents conf'));auto.  rewrite app_assoc.     rewrite app_assoc. apply Permutation_app_head;auto.  apply Permutation_sym;auto.

    split.*)

    split. 

      assert (Permutation (finishedscenarios y ++ finishedscenarios conf ++ finishedscenarios x)  (finishedscenarios y ++ finishedscenarios x ++ finishedscenarios conf) ).
     apply Permutation_app_head;auto.
      apply Permutation_app_comm;auto.
     assert (Permutation (finishedscenarios x ++ finishedscenarios y ++ finishedscenarios conf)  (finishedscenarios y ++ finishedscenarios x ++ finishedscenarios conf) ).

    rewrite app_assoc.     rewrite app_assoc.
    apply Permutation_app_tail;auto. apply Permutation_app_comm;auto.
    assert (Permutation (finishedscenarios y ++ finishedscenarios conf ++ finishedscenarios x) (finishedscenarios x ++ finishedscenarios y ++ finishedscenarios conf)).
    apply Permutation_trans with (l':=(finishedscenarios y ++ finishedscenarios x ++ finishedscenarios conf));auto.    apply Permutation_sym;auto.
    assert (Permutation (finishedscenarios x ++ finishedscenarios conf' ++ finishedscenarios y) (finishedscenarios x ++ finishedscenarios y ++ finishedscenarios conf')).
    apply Permutation_app_head;auto.   apply Permutation_app_comm;auto.
    apply Permutation_trans with (l':=(finishedscenarios x ++ finishedscenarios y ++ finishedscenarios conf));auto.
    apply Permutation_sym.   apply  Permutation_trans with (l':=(finishedscenarios x ++ finishedscenarios y ++ finishedscenarios conf'));auto.  rewrite app_assoc.     rewrite app_assoc. apply Permutation_app_head;auto.  apply Permutation_sym;auto.

    split.


        unfold incl in *.
    intros.
    rewrite in_app_iff. rewrite in_app_iff. 
    rewrite in_app_iff in H9.  rewrite in_app_iff in H9. 
    destruct H9;intuition;auto.

    split.
    
    
        unfold incl in *.
    intros.
    rewrite in_app_iff. rewrite in_app_iff. 
    rewrite in_app_iff in H9.  rewrite in_app_iff in H9. 
    destruct H9;intuition;auto.


     
 (*   
assert (Permutation (exportedevents y ++ exportedevents conf ++ exportedevents x)  (exportedevents y ++ exportedevents x ++ exportedevents conf) ).
     apply Permutation_app_head;auto.
      apply Permutation_app_comm;auto.
     assert (Permutation (exportedevents x ++ exportedevents y ++ exportedevents conf)  (exportedevents y ++ exportedevents x ++ exportedevents conf) ).

    rewrite app_assoc.     rewrite app_assoc.
    apply Permutation_app_tail;auto. apply Permutation_app_comm;auto.
    assert (Permutation (exportedevents y ++ exportedevents conf ++ exportedevents x) (exportedevents x ++ exportedevents y ++ exportedevents conf)).
    apply Permutation_trans with (l':=(exportedevents y ++ exportedevents x ++ exportedevents conf));auto.    apply Permutation_sym;auto.
    assert (Permutation (exportedevents x ++ exportedevents conf' ++ exportedevents y) (exportedevents x ++ exportedevents y ++ exportedevents conf')).
    apply Permutation_app_head;auto.   apply Permutation_app_comm;auto.
    apply Permutation_trans with (l':=(exportedevents x ++ exportedevents y ++ exportedevents conf));auto.
    apply Permutation_sym.   apply  Permutation_trans with (l':=(exportedevents x ++ exportedevents y ++ exportedevents conf'));auto.  rewrite app_assoc.     rewrite app_assoc. apply Permutation_app_head;auto.  apply Permutation_sym;auto.
*)
    assert (Permutation (sceEventMap y ++ sceEventMap conf ++ sceEventMap x)  (sceEventMap y ++ sceEventMap x ++ sceEventMap conf) ).
     apply Permutation_app_head;auto.
      apply Permutation_app_comm;auto.
     assert (Permutation (sceEventMap x ++ sceEventMap y ++ sceEventMap conf)  (sceEventMap y ++ sceEventMap x ++ sceEventMap conf) ).

    rewrite app_assoc.     rewrite app_assoc.
    apply Permutation_app_tail;auto. apply Permutation_app_comm;auto.
    assert (Permutation (sceEventMap y ++ sceEventMap conf ++ sceEventMap x) (sceEventMap x ++ sceEventMap y ++ sceEventMap conf)).
    apply Permutation_trans with (l':=(sceEventMap y ++ sceEventMap x ++ sceEventMap conf));auto.    apply Permutation_sym;auto.
    assert (Permutation (sceEventMap x ++ sceEventMap conf' ++ sceEventMap y) (sceEventMap x ++ sceEventMap y ++ sceEventMap conf')).
    apply Permutation_app_head;auto.   apply Permutation_app_comm;auto.
    apply Permutation_trans with (l':=(sceEventMap x ++ sceEventMap y ++ sceEventMap conf));auto.
    apply Permutation_sym.   apply  Permutation_trans with (l':=(sceEventMap x ++ sceEventMap y ++ sceEventMap conf'));auto.  rewrite app_assoc.     rewrite app_assoc. apply Permutation_app_head;auto.  apply Permutation_sym;auto.
    remember (innerCombineFunc'''' conf' (c :: l)).
    destruct o;inversion H2.  clear H3.
    remember (innerCombineFunc'''' conf (c :: l)).
    destruct o;inversion H1.
    remember (mergeConfigFunc' conf' y c0).
    destruct e;inversion H2.
    remember (mergeConfigFunc' conf' x v).
    destruct e;inversion H2.
    remember ( mergeConfigFunc' conf x c1 ).
    destruct e;inversion H1.
    remember (mergeConfigFunc' conf y v3).
    destruct e;inversion H1.
    subst.  clear H4;clear H6. clear H1;clear H3.
    clear H2.
    assert (equivConf c1 c0).
    apply innterCombineFuncEquiv' with (l:=(c::l)) (conf:=conf) (conf':=conf');auto.     
    unfold mergeConfigFunc' in *.
    unfold equivConf in *.     
     repeat match goal with
            | [ H: _ /\ _ |- _ ] => destruct H

               end.
     rewrite <- H in Heqe.   rewrite <- H1 in Heqe.
     rewrite <- H0 in Heqe. rewrite <- H8 in Heqe.
     rewrite <- H0 in Heqe0. rewrite <- H8 in Heqe0.
     remember (mergeDataStateFunc (datastate conf) (datastate y) (datastate c1)).
     destruct e;inversion Heqe.
     clear H16.
     remember (mergeControlStateFunc (controlstate conf) (controlstate y) (controlstate c1) ).
     destruct e;inversion Heqe.
     clear H16.
     inversion Heqe;subst;simpl in Heqe0 .    clear Heqe.
     remember (mergeDataStateFunc (datastate conf) (datastate x) v1).
     destruct e;inversion Heqe0.  clear H16.     
     remember (mergeControlStateFunc (controlstate conf) (controlstate x) v2).
     destruct e;inversion Heqe0.
     simpl.
     clear H16. clear Heqe0.
     remember (mergeDataStateFunc (datastate conf) (datastate x) (datastate c1)). 
     destruct e;inversion Heqe1. clear H16.
     remember (mergeControlStateFunc (controlstate conf) (controlstate x) (controlstate c1)).  
     destruct e;inversion Heqe1.
     clear H16. inversion Heqe1;subst.
     simpl in Heqe2.  clear Heqe1.
     remember (mergeDataStateFunc (datastate conf) (datastate y) v6).
     destruct e;inversion Heqe2.
     clear H16.
     remember (mergeControlStateFunc (controlstate conf) (controlstate y) v7). 
     destruct e;inversion Heqe2.
     simpl.
     split. 
     pose proof mergeDataStateFuncEquiv'.
     symmetry. 
     eapply H15 with (ds:=datastate conf) (c1:=datastate c1) (ds1:=datastate y) (ds2:=datastate x);auto. apply Heqe3. 
     auto.  apply Heqe0. auto.
     split.
     pose proof mergeControlStateFuncEquiv'.
     symmetry.
    eapply H15 with (ds:=controlstate conf) (c1:=controlstate c1) (ds1:=controlstate y) (ds2:=controlstate x);auto. apply Heqe4. 
     auto.  apply Heqe6. auto.
     split; (try ( rewrite app_assoc;     rewrite app_assoc;
  apply Permutation_app;auto;  apply Permutation_app_comm;auto)). 

    
        unfold incl in *.
    intros.
    rewrite in_app_iff. rewrite in_app_iff. 
    rewrite in_app_iff in H15.  rewrite in_app_iff in H15. 
    destruct H15;intuition;auto.

    split. 
        unfold incl in *.
    intros.
    rewrite in_app_iff. rewrite in_app_iff. 
    rewrite in_app_iff in H15.  rewrite in_app_iff in H15. 
    destruct H15;intuition;auto.

    

     split; (try ( rewrite app_assoc;     rewrite app_assoc;
                   apply Permutation_app;auto;  apply Permutation_app_comm;auto)).

     split.


         unfold incl in *.
    intros.
    rewrite in_app_iff. rewrite in_app_iff. 
    rewrite in_app_iff in H15.  rewrite in_app_iff in H15. 
    destruct H15;intuition;auto.

    split.


        unfold incl in *.
    intros.
    rewrite in_app_iff. rewrite in_app_iff. 
    rewrite in_app_iff in H15.  rewrite in_app_iff in H15. 
    destruct H15;intuition;auto.
     
      

      (try ( rewrite app_assoc;     rewrite app_assoc;
                   apply Permutation_app;auto;  apply Permutation_app_comm;auto)).
      

      
   - intros.
     
     assert (exists v2 : configuration M, Some v2 = innerCombineFunc'''' conf l' /\ equivConf v1 v2).
      pose proof innterCombineFuncEquivExist'. 
      apply H4 with (l:=l);auto.
      destruct H4.   destruct H4.   apply IHPermutation2 with (v1:=x) (conf:=conf) in H2;auto.
       eapply equivConf_Trans. apply H5. auto.
Qed. 


Lemma mergeConfigFuncEquivExistsConf: forall M (conf conf' a b: configuration M) v1,
    equivConf conf conf' ->
    equivConf a b ->
    Result v1 = mergeConfigFunc' conf conf a ->
    (exists v2, Result v2 = mergeConfigFunc' conf' conf' b /\ equivConf v1 v2).
Proof.
  intros.
  unfold equivConf in H. unfold equivConf in H0. 
  unfold mergeConfigFunc' in *.  
   repeat match goal with
            | [ H: _ /\ _ |- _ ] => destruct H

          end.
   rewrite <- H. rewrite <- H9. rewrite <- H0. rewrite <- H2.
     
   remember (mergeDataStateFunc (datastate conf) (datastate conf) (datastate a)).
   destruct e;inversion H1.
   remember (mergeControlStateFunc (controlstate conf) (controlstate conf) (controlstate a)).
   destruct e;inversion H1.
   exists ({|
      datastate := v;
      controlstate := v0;
      raisedevents := raisedevents conf' ++ raisedevents b;
      exportedevents := exportedevents conf' ++ exportedevents b;
      finishedscenarios := finishedscenarios conf' ++ finishedscenarios b;
      sceEventMap := sceEventMap conf' ++ sceEventMap b |}).
   split;auto.
   split;simpl;auto.    split;auto.
   SearchAbout Permutation.
   
   repeat (split; try (apply Permutation_app;auto)).

    unfold incl in *.
     intros.
     rewrite in_app_iff.
     rewrite in_app_iff in H16.
     destruct H16;intuition;auto.


     unfold incl in *.
     intros.
     rewrite in_app_iff.
     rewrite in_app_iff in H16.
     destruct H16;intuition;auto.


     unfold incl in *.
     intros.
     rewrite in_app_iff.
     rewrite in_app_iff in H16.
     destruct H16;intuition;auto.

     unfold incl in *.
     intros.
     rewrite in_app_iff.
     rewrite in_app_iff in H16.
     destruct H16;intuition;auto.

    
   
Qed.


Lemma mergeConfigFuncAllEquiv: forall M (conf conf' conf1 conf1' conf2 conf2' v v': configuration M),
    equivConf conf conf' ->
    equivConf conf1 conf1' ->
    equivConf conf2 conf2' ->
    Result v = mergeConfigFunc' conf conf1 conf2 ->
    Result v' = mergeConfigFunc' conf' conf1' conf2' ->
    equivConf v v'.
Proof.
  intros.
  unfold mergeConfigFunc' in *.
  unfold equivConf in H; unfold equivConf in H0; unfold equivConf in H1.
   repeat match goal with
            | [ H: _ /\ _ |- _ ] => destruct H

           end.
  rewrite <- H in H3. rewrite <- H18 in H3. 
  rewrite <- H0 in H3.    rewrite <- H4 in H3.
  rewrite <- H1 in H3.  rewrite <- H11 in H3.
  remember (mergeDataStateFunc (datastate conf) (datastate conf1) (datastate conf2)).
  destruct e;inversion H2.   clear H26.
  remember (mergeControlStateFunc (controlstate conf) (controlstate conf1) (controlstate conf2)).
  destruct e;inversion H2.
  subst.   inversion H3;subst.
  split;simpl;auto.
  split;auto.
  repeat(split; try (apply Permutation_app));auto.

  unfold incl in *.
     intros.
     rewrite in_app_iff.
     rewrite in_app_iff in H25.
     destruct H25;intuition;auto.

     unfold incl in *.
     intros.
     rewrite in_app_iff.
     rewrite in_app_iff in H25.
     destruct H25;intuition;auto.


     unfold incl in *.
     intros.
     rewrite in_app_iff.
     rewrite in_app_iff in H25.
     destruct H25;intuition;auto.


     unfold incl in *.
     intros.
     rewrite in_app_iff.
     rewrite in_app_iff in H25.
     destruct H25;intuition;auto.

Qed.

Lemma mergeConfigFuncAllEquivExists: forall M (conf conf' conf1 conf1' conf2 conf2' v: configuration M),
    equivConf conf conf' ->
    equivConf conf1 conf1' ->
    equivConf conf2 conf2' ->
    Result v = mergeConfigFunc' conf conf1 conf2 ->
    (exists v', 
    Result v' = mergeConfigFunc' conf' conf1' conf2' /\
    equivConf v v').
Proof.
  intros.
   unfold mergeConfigFunc' in *.
  unfold equivConf in H; unfold equivConf in H0; unfold equivConf in H1.
   repeat match goal with
            | [ H: _ /\ _ |- _ ] => destruct H

           end.
  rewrite <- H . rewrite <- H0. 
  rewrite <- H3.    rewrite <- H1.
  rewrite <- H17.  rewrite <- H10.
  remember (mergeDataStateFunc (datastate conf) (datastate conf1) (datastate conf2)).
  destruct e;inversion H2.   clear H25.
  remember (mergeControlStateFunc (controlstate conf) (controlstate conf1) (controlstate conf2)).
  destruct e;inversion H2.
  subst.   exists ( {|
      datastate := v0;
      controlstate := v1;
      raisedevents := raisedevents conf1' ++ raisedevents conf2';
      exportedevents := exportedevents conf1' ++ exportedevents conf2';
      finishedscenarios := finishedscenarios conf1' ++ finishedscenarios conf2';
      sceEventMap := sceEventMap conf1' ++ sceEventMap conf2' |}). 
  split;simpl;auto.
  split;simpl;auto.
  split;auto.   
  repeat(split; try (apply Permutation_app));auto.

  unfold incl in *.
     intros.
     rewrite in_app_iff.
     rewrite in_app_iff in H24.
     destruct H24;intuition;auto.

  unfold incl in *.
     intros.
     rewrite in_app_iff.
     rewrite in_app_iff in H24.
     destruct H24;intuition;auto.



       unfold incl in *.
     intros.
     rewrite in_app_iff.
     rewrite in_app_iff in H24.
     destruct H24;intuition;auto.



       unfold incl in *.
     intros.
     rewrite in_app_iff.
     rewrite in_app_iff in H24.
     destruct H24;intuition;auto.
  
Qed. 
                                


Lemma Permutation_App_3: forall A l1 l2 l3 l1' l2' l3',
    @Permutation A l1 l1' ->
    @Permutation A l2 l2' ->
    @Permutation A l3 l3' ->
    @Permutation A (l1 ++ l2 ++ l3) (l3' ++ l2' ++ l1').
Proof.
  intros.
  assert (Permutation (l1 ++ l2 ++ l3) (l2 ++ l1 ++ l3)).
  rewrite app_assoc. rewrite app_assoc. apply Permutation_app_tail.     
  apply Permutation_app_comm.
   assert (Permutation (l3' ++ l2' ++ l1') (l2' ++ l3' ++ l1')).
  rewrite app_assoc. rewrite app_assoc. apply Permutation_app_tail.     
  apply Permutation_app_comm.
  eapply Permutation_trans.
  apply H2.
  apply Permutation_sym.   eapply Permutation_trans.
  apply H3.
  apply Permutation_app. apply Permutation_sym;auto. 
  assert (Permutation (l3' ++ l1') (l1' ++ l3')).
  apply Permutation_app_comm.
  eapply Permutation_trans. apply H4.   apply Permutation_app;apply Permutation_sym;auto. 
Qed.


Lemma Permutation_App_3': forall A l1 l2 l3 l1' l2' l3',
    @Permutation A l1 l1' ->
    @Permutation A l2 l2' ->
    @Permutation A l3 l3' ->
    @Permutation A (l1 ++ l2 ++ l3) (l2' ++ l1' ++ l3').
Proof.
  intros.
  assert (Permutation (l1 ++ l2 ++ l3) (l2 ++ l1 ++ l3)).
  rewrite app_assoc. rewrite app_assoc. apply Permutation_app_tail.     
  apply Permutation_app_comm.
 
  eapply Permutation_trans.
  apply H2.
 
  apply Permutation_app;auto.  apply Permutation_app;auto. 
  
Qed.


Lemma mergeConfigFuncBothExistEquiv:
  forall (M : monitor) (conf conf' x x' y y' v v0 : configuration M),
    equivConf x x' ->
    equivConf y y' ->
    equivConf conf conf' ->
  Result v = mergeConfigFunc' conf conf x ->
  Result v0 = mergeConfigFunc' conf y' v ->
  exists c v2 : configuration M,
    Result c = mergeConfigFunc' conf' conf' y /\
    Result v2 = mergeConfigFunc' conf' x' c /\ equivConf v0 v2. 
Proof.

   intros.
   unfold  mergeConfigFunc' in *.
   unfold equivConf in H;unfold equivConf in H0;unfold equivConf in H1.
   repeat match goal with
           | [ H: _ /\ _ |- _ ] => destruct H
            | [ H: exists _, _ |- _] => destruct H
            

          end.
   rewrite <- H in *. rewrite <- H0 in *. rewrite <- H1 in *.
   rewrite <- H18 in *. rewrite <- H11 in *. rewrite <- H4 in *.
   remember ( mergeDataStateFunc (datastate conf) (datastate conf) (datastate x)).
   destruct e;inversion H2.
   remember (mergeControlStateFunc (controlstate conf) (controlstate conf) (controlstate x)).
   destruct e;inversion H2.
   clear H26.
   remember ( mergeDataStateFunc (datastate conf) (datastate y) (datastate v) ).
   destruct e;inversion H3.
   remember (mergeControlStateFunc (controlstate conf) (controlstate y) (controlstate v)).
   destruct e;inversion H3.
   clear H26;clear H3.
   clear H2. rewrite H27 in H28;simpl in H28. rewrite H27;simpl.
   rewrite H27 in *;simpl in *. clear H28.
   
    pose proof mergeDataStateFuncEquivExist.
   pose proof mergeControlStateFuncEquivExist.
   assert (exists v3' v4' : list (atom * (typ * range_typ)),
         Result v3' = mergeDataStateFunc (datastate conf) (datastate conf) (datastate y) /\
         Result v4' = mergeDataStateFunc (datastate conf) (datastate x) v3' /\ v3 = v4').
   eapply H2;auto. apply Heqe. auto.
   assert (exists v3' v4' ,
         Result v3' = mergeControlStateFunc (controlstate conf) (controlstate conf) (controlstate y) /\
         Result v4' = mergeControlStateFunc (controlstate conf) (controlstate x) v3' /\ v4 = v4').
   eapply H3;auto. apply Heqe0. auto.
   repeat (match goal with
           | [H: exists _, _ |- _] => destruct H
           | [H: _ /\ _|- _] => destruct H
           end).
   subst.    
   rewrite <- H25.
   rewrite <- H26.
   exists ({|
      datastate := x2;
      controlstate := x0;
      raisedevents := raisedevents conf' ++ raisedevents y;
      exportedevents := exportedevents conf' ++ exportedevents y;
      finishedscenarios := finishedscenarios conf' ++ finishedscenarios y;
      sceEventMap := sceEventMap conf' ++ sceEventMap y |}).
   simpl.   rewrite <- H30.  rewrite <- H28.
   exists ( {|
      datastate := x3;
      controlstate := x1;
      raisedevents := raisedevents x' ++ raisedevents conf' ++ raisedevents y;
      exportedevents := exportedevents x' ++ exportedevents conf' ++ exportedevents y;
      finishedscenarios := finishedscenarios x' ++ finishedscenarios conf' ++ finishedscenarios y;
      sceEventMap := sceEventMap x' ++ sceEventMap conf' ++ sceEventMap y |} ).
   simpl;split;auto.   split;auto.
   split;simpl;auto.
   split;auto.
   repeat (match goal with
           | [H:_ |- _ /\ _] => split
           | [H: _ |- Permutation (_ ++ _ ++ _) (_ ++ _ ++ _) ] => apply Permutation_App_3
           | [H: _ |- Permutation _ _] => apply Permutation_sym;auto
           end).

     unfold incl in *.
     intros.
     rewrite in_app_iff.  rewrite in_app_iff.
     rewrite in_app_iff in H27. rewrite in_app_iff in H27.
     destruct H27;intuition;auto.

 unfold incl in *.
     intros.
     rewrite in_app_iff.  rewrite in_app_iff.
     rewrite in_app_iff in H27. rewrite in_app_iff in H27.
     destruct H27;intuition;auto.

      unfold incl in *.
     intros.
     rewrite in_app_iff.  rewrite in_app_iff.
     rewrite in_app_iff in H27. rewrite in_app_iff in H27.
     destruct H27;intuition;auto.

      unfold incl in *.
     intros.
     rewrite in_app_iff.  rewrite in_app_iff.
     rewrite in_app_iff in H27. rewrite in_app_iff in H27.
     destruct H27;intuition;auto.


Qed.

Lemma mergeConfigFuncBothExistEquiv':
  forall (M : monitor) (conf conf' c0 c1 x y x' y' v v0 : configuration M),
    equivConf conf conf' ->
    equivConf c0 c1 ->
    equivConf x x' ->
    equivConf y y' ->
  Result v = mergeConfigFunc' conf x c0 ->
  Result v0 = mergeConfigFunc' conf y v ->
  exists c v2 : configuration M,
    Result c = mergeConfigFunc' conf' y' c1 /\
    Result v2 = mergeConfigFunc' conf' x' c /\ equivConf v0 v2. 
Proof.

     intros.
   unfold  mergeConfigFunc' in *.
   unfold equivConf in H;unfold equivConf in H0;unfold equivConf in H1;unfold equivConf in H2. 
   
   repeat match goal with
           | [ H: _ /\ _ |- _ ] => destruct H
            | [ H: exists _, _ |- _] => destruct H
            

          end.
   rewrite <- H in *. rewrite <- H0 in *. rewrite <- H1 in *. rewrite <- H2 in *. 
   rewrite <- H26 in *. rewrite <- H19 in *. rewrite <- H12  in *. rewrite <- H5 in *.
   
   remember ( mergeDataStateFunc (datastate conf) (datastate x) (datastate c0)).
   destruct e;inversion H3.
   remember (mergeControlStateFunc (controlstate conf) (controlstate x) (controlstate c0)).
   destruct e;inversion H3.
   clear H34. subst;simpl in *. clear H3.
   
   remember ( mergeDataStateFunc (datastate conf) (datastate y) ( v1) ).
   destruct e;inversion H4.
   remember (mergeControlStateFunc (controlstate conf) (controlstate y) ( v2)).
   destruct e;inversion H4. subst;simpl in *. 
   clear H33;clear H4.
   pose proof mergeDataStateFuncEquivExist'.
   pose proof mergeControlStateFuncEquivExist'.
   assert (exists v3' v4' : list (atom * (typ * range_typ)),
         Result v3' = mergeDataStateFunc (datastate conf) (datastate y) (datastate c0) /\
         Result v4' = mergeDataStateFunc (datastate conf) (datastate x) v3' /\ v = v4').
   eapply H3;auto. apply Heqe. auto.
   assert (exists v3' v4' ,
         Result v3' = mergeControlStateFunc (controlstate conf) (controlstate y) (controlstate c0) /\
         Result v4' = mergeControlStateFunc (controlstate conf) (controlstate x) v3' /\ v3 = v4').
   eapply H4;auto. apply Heqe0. auto.
   repeat (match goal with
           | [H: exists _, _ |- _] => destruct H
           | [H: _ /\ _|- _] => destruct H
           end).
   subst.    
   rewrite <- H33.
   rewrite <- H34.
   exists ({|
      datastate := x2;
      controlstate := x0;
      raisedevents := raisedevents y' ++ raisedevents c1;
      exportedevents := exportedevents y' ++ exportedevents c1;
      finishedscenarios := finishedscenarios y' ++ finishedscenarios c1;
      sceEventMap := sceEventMap y' ++ sceEventMap c1 |}).
   simpl.   rewrite <- H35.  rewrite <- H37.
   exists ( {|
      datastate := x3;
      controlstate := x1;
      raisedevents := raisedevents x' ++ raisedevents y' ++ raisedevents c1;
      exportedevents := exportedevents x' ++ exportedevents y' ++ exportedevents c1;
      finishedscenarios := finishedscenarios x' ++ finishedscenarios y' ++ finishedscenarios c1;
      sceEventMap := sceEventMap x' ++ sceEventMap y' ++ sceEventMap c1 |} ).
   simpl;split;auto.   split;auto.
   split;simpl;auto.
   split;auto.
repeat (match goal with
           | [H:_ |- _ /\ _] => split
           | [H: _ |- Permutation (_ ++ _ ++ _) (_ ++ _ ++ _) ] => apply Permutation_App_3'
           | [H: _ |- Permutation _ _] => apply Permutation_sym;auto
           end).

 unfold incl in *.
     intros.
     rewrite in_app_iff.  rewrite in_app_iff.
     rewrite in_app_iff in H36. rewrite in_app_iff in H36.
     destruct H36;intuition;auto.

      unfold incl in *.
     intros.
     rewrite in_app_iff.  rewrite in_app_iff.
     rewrite in_app_iff in H36. rewrite in_app_iff in H36.
     destruct H36;intuition;auto.
      unfold incl in *.
     intros.
     rewrite in_app_iff.  rewrite in_app_iff.
     rewrite in_app_iff in H36. rewrite in_app_iff in H36.
     destruct H36;intuition;auto.
      unfold incl in *.
     intros.
     rewrite in_app_iff.  rewrite in_app_iff.
     rewrite in_app_iff in H36. rewrite in_app_iff in H36.
     destruct H36;intuition;auto.
     

Qed.


Lemma innterCombineFuncEquivExistList': forall M (l l': list (configuration M))  (conf : configuration M)  v1,
    confEquivList l l' ->
    Some v1 = innerCombineFunc'''' conf l ->
    (exists v2, Some v2 = innerCombineFunc'''' conf l' /\
    equivConf v1 v2). 
Proof.
  intros.
  generalize dependent conf.  generalize dependent v1.
  induction H.
  -  intros.
     simpl in H0.
     inversion H0.
  - intros.
    simpl in *.
    destruct l.
    destruct l'.
    remember (mergeConfigFunc' conf0 conf0 conf).
    destruct e;inversion H0.
    inversion H1;subst. 
    SearchAbout mergeConfigFunc'.
    pose proof mergeConfigFuncEquivExistsConf.
    assert (exists v2, Result v2 = mergeConfigFunc' conf0 conf0 conf' /\ equivConf v v2).
    eapply H2 ;auto. apply equivConf_Refl. apply H. auto.
    destruct H3. destruct H3. rewrite <- H3. exists x;auto.
    subst. 
    pose proof mergeConfigFuncEquivExistsConf.
    assert (exists v2, Result v2 = mergeConfigFunc' conf0 conf0 conf' /\ equivConf v v2).
     eapply H4 ;auto. apply equivConf_Refl. apply H. auto.
    destruct H5. destruct H5. rewrite <- H5. exists x;auto.
    inversion H1;subst.     split;auto. inversion H1.
    inversion H1. apply confEquivList_cons_nil in H0. inversion H0.
    remember (innerCombineFunc'''' conf0 (c :: l)).
    destruct o;inversion H1.
    remember (mergeConfigFunc' conf0 conf c0).
    destruct e;inversion H1.
    subst.
    destruct l'.
    apply confEquivList_sym in H0.  apply confEquivList_cons_nil in H0. inversion H0.
    clear H3.
    apply IHconfEquivList in Heqo.
    destruct Heqo. destruct H2. rewrite <- H2. 
    SearchAbout mergeConfigFunc'.
    pose proof mergeConfigFuncAllEquivExists.
    assert ( exists v2 : configuration M, Result v2 = mergeConfigFunc' conf0 conf' x /\ equivConf v v2).
   eapply H4. 
   apply equivConf_Refl;auto.
  apply H. apply H3.  auto. destruct H5.   destruct H5. rewrite <- H5. exists x0;auto. 
  - intros.
    simpl in *.
    destruct l;destruct l'.    
    remember (mergeConfigFunc' conf conf conf2).
    destruct e;inversion H2.
    remember (mergeConfigFunc' conf conf1 v).
    destruct e;inversion H2.
    subst.
    SearchAbout mergeConfigFunc'.
    pose proof mergeConfigFuncBothExistEquiv.
    assert ( exists c v2 : configuration M,
         Result c = mergeConfigFunc' conf conf conf1' /\
         Result v2 = mergeConfigFunc' conf conf2' c /\ equivConf v0 v2).
    eapply H3.    apply H0. apply equivConf_Sym in H;apply H.  apply  equivConf_Refl;auto.
    apply Heqe. auto.
       repeat (match goal with
           | [H: exists _, _ |- _] => destruct H
           | [H: _ /\ _|- _] => destruct H
               end).
       rewrite <- H5. rewrite <- H6. exists x0;auto.
  apply confEquivList_cons_nil in H1;inversion H1.    
  apply confEquivList_sym in H1.  apply confEquivList_cons_nil in H1;inversion H1.
  remember (innerCombineFunc'''' conf (c :: l)).
  destruct o;inversion H2.
  apply  IHconfEquivList in Heqo.   destruct Heqo.
  destruct H3.
  rewrite <- H3.
  SearchAbout mergeConfigFunc' .
  remember (mergeConfigFunc' conf conf2 c1).
   destruct e;inversion H2.
   remember (mergeConfigFunc' conf conf1 v).
  destruct e;inversion H2.    
 subst.   pose proof mergeConfigFuncBothExistEquiv'.
assert (  exists c v2 : configuration M,
         Result c = mergeConfigFunc' conf conf1' x /\
         Result v2 = mergeConfigFunc' conf conf2' c /\ equivConf v0 v2).
apply H6 with (conf:=conf) (c0:=c1) (x:=conf2) (y:=conf1) (v:=v);auto.
apply equivConf_Refl;auto.
 repeat (match goal with
           | [H: exists _, _ |- _] => destruct H
           | [H: _ /\ _|- _] => destruct H
         end).
 rewrite <- H8.  rewrite <- H9. exists x1;auto.
  -
    intros.
    apply IHconfEquivList1 in H1. repeat (match goal with
           | [H: exists _, _ |- _] => destruct H
           | [H: _ /\ _|- _] => destruct H
         end).    
    apply IHconfEquivList2 in H1.
destruct H1.    destruct H1. exists x0;auto. split;auto. eapply equivConf_Trans. apply H2. auto. 

Qed.


Lemma innterCombineFuncEquivListExists: forall M (conf conf': configuration M) l1 l2 v1,
    confEquivList l1 l2 ->
    equivConf conf conf' ->
    Some v1 = innerCombineFunc'''' conf l1 ->
    (exists v2, Some v2 = innerCombineFunc'''' conf' l2 /\ equivConf v1 v2). 
Proof.
   intros.
  generalize dependent conf. generalize dependent conf'.  generalize dependent v1.
  induction H.
  -  intros.
     simpl in H1.
     inversion H1. 
  - intros.
    simpl in *.
    destruct l.
    destruct l'.
    remember (mergeConfigFunc' conf0 conf0 conf).
    destruct e;inversion H0.
    inversion H2;subst. 
    pose proof mergeConfigFuncEquivExistsConf.
    assert (exists v2, Result v2 = mergeConfigFunc' conf'0 conf'0 conf' /\ equivConf v v2).
    eapply H3;auto. apply H1. apply H. auto.
    destruct H4. destruct H4. rewrite <- H4. exists x;auto.
    subst. 
    pose proof mergeConfigFuncEquivExistsConf.
    assert (exists v2, Result v2 = mergeConfigFunc' conf'0 conf'0 conf' /\ equivConf v v2).
     eapply H5 ;auto. apply H1. apply H.  auto.
    destruct H6.  destruct H6. rewrite <- H6. exists x;auto.
    inversion H2;subst. split;auto.    inversion H2.  inversion H2. 
   apply confEquivList_cons_nil in H0. inversion H0.
    remember (innerCombineFunc'''' conf0 (c :: l)).
    destruct o;inversion H2.
    remember (mergeConfigFunc' conf0 conf c0).
    destruct e;inversion H2.
    subst.
    destruct l'.
    apply confEquivList_sym in H0.  apply confEquivList_cons_nil in H0. inversion H0.
    clear H4. 
    apply IHconfEquivList with (conf':=conf'0) in Heqo;auto. 
    destruct Heqo. destruct H3. rewrite <- H3. 
    pose proof mergeConfigFuncAllEquivExists.
    assert ( exists v2 : configuration M, Result v2 = mergeConfigFunc' conf'0 conf' x /\ equivConf v v2).
   eapply H5. 
   apply H1;auto.
  apply H. apply H4.  auto. destruct H6.   destruct H6. rewrite <- H6. exists x0;auto. 
  - intros.
    simpl in *.
    destruct l;destruct l'.    
    remember (mergeConfigFunc' conf conf conf2).
    destruct e;inversion H3.
    remember (mergeConfigFunc' conf conf1 v).
    destruct e;inversion H3.
    subst.
    pose proof mergeConfigFuncBothExistEquiv.
    assert ( exists c v2 : configuration M,
         Result c = mergeConfigFunc' conf' conf' conf1' /\
         Result v2 = mergeConfigFunc' conf' conf2' c /\ equivConf v0 v2).
    eapply H4.    apply H0. apply equivConf_Sym in H;apply H.  apply H2.
    apply Heqe. auto.
       repeat (match goal with
           | [H: exists _, _ |- _] => destruct H
           | [H: _ /\ _|- _] => destruct H
               end).
       rewrite <- H6. rewrite <- H7. exists x0;auto.
  apply confEquivList_cons_nil in H1;inversion H1.    
  apply confEquivList_sym in H1.  apply confEquivList_cons_nil in H1;inversion H1.
  remember (innerCombineFunc'''' conf (c :: l)).
  destruct o;inversion H3.
  apply  IHconfEquivList with (conf':=conf') in Heqo;auto.   destruct Heqo.
  destruct H4.
  rewrite <- H4.
  remember (mergeConfigFunc' conf conf2 c1).
   destruct e;inversion H3. 
   remember (mergeConfigFunc' conf conf1 v).
  destruct e;inversion H3.    
 subst.   pose proof mergeConfigFuncBothExistEquiv'.
assert (  exists c v2 : configuration M,
         Result c = mergeConfigFunc' conf' conf1' x /\
         Result v2 = mergeConfigFunc' conf' conf2' c /\ equivConf v0 v2).
apply H7 with (conf:=conf) (c0:=c1) (x:=conf2) (y:=conf1) (v:=v);auto.
 repeat (match goal with
           | [H: exists _, _ |- _] => destruct H
           | [H: _ /\ _|- _] => destruct H
         end).
 rewrite <- H9.  rewrite <- H10. exists x1;auto.
  -
    intros.
    apply IHconfEquivList1 with (conf':=conf') in H2;auto. repeat (match goal with
           | [H: exists _, _ |- _] => destruct H
           | [H: _ /\ _|- _] => destruct H
                                                                   end).
    SearchAbout innerCombineFunc''''.
    
    apply innterCombineFuncEquivExist with (conf':=conf) in H2;auto.  
    destruct H2.
    destruct H2.
    apply IHconfEquivList2 with (conf':=conf') in H2.  destruct H2. destruct H2.
 exists x1;auto.     split;auto. 
eapply equivConf_Trans. apply H3. eapply equivConf_Trans.
apply H4. auto. 
auto.  apply equivConf_Sym;auto. 
Qed.

  
  
Lemma innterCombineFuncEquivList: forall M (conf conf': configuration M) l1 l2 v1 v2,
    confEquivList l1 l2 ->
    equivConf conf conf' ->
    Some v1 = innerCombineFunc'''' conf l1 ->
    Some v2 = innerCombineFunc'''' conf' l2 ->
    equivConf v1 v2. 
Proof.
  intros.
  generalize dependent conf;generalize dependent conf'.
  generalize dependent v1; generalize dependent v2.
  induction H.
  - intros.
    simpl in *.
    inversion H1.
  - intros.
    simpl in *.
    destruct l'.    
    destruct l.
    remember (mergeConfigFunc' conf'0 conf'0 conf').
    destruct e;inversion H2.
    remember (mergeConfigFunc' conf0 conf0 conf).
    destruct e;inversion H3.
    subst.
    pose proof mergeConfigFuncEquivExistsConf.
    assert (exists v : configuration M, Result v = mergeConfigFunc' conf'0 conf'0 conf' /\ equivConf v0 v).      
    apply H4 with (conf:=conf0) (a:=conf);auto.
    destruct H5.   destruct H5. rewrite <- H5 in Heqe.  inversion Heqe;subst. auto.
    (*confEquivList_cons_nil*)
    SearchAbout confEquivList. 
    apply confEquivList_sym in H0.
    apply  confEquivList_cons_nil in H0;inversion H0.
    destruct l.
    apply  confEquivList_cons_nil in H0;inversion H0.
    remember (innerCombineFunc'''' conf'0 (c :: l')).
    destruct o;inversion H2.  clear H5.
    remember (innerCombineFunc'''' conf0 (c0 :: l) ).
    destruct o;inversion H3.
    remember (mergeConfigFunc' conf'0 conf' c1).
    destruct e;inversion H2.
    remember (mergeConfigFunc' conf0 conf c2).
    destruct e;inversion H3. subst.
    assert (equivConf c2 c1).
    apply IHconfEquivList with (conf':=conf'0) (conf:=conf0);auto.     
    pose proof mergeConfigFuncAllEquiv.
  eapply H6.     
  apply H1.     apply H.    
  apply H4.   auto.   auto.
  - intros.
   simpl in *.     
   destruct l'.     
   destruct l.     
   remember (mergeConfigFunc' conf' conf' conf1').
   destruct e;inversion H2.
   clear H6.
   remember (mergeConfigFunc' conf' conf2' v).
   destruct e;inversion H2. subst.
   remember ( mergeConfigFunc' conf conf conf2).
    destruct e;inversion H4.
    remember (mergeConfigFunc' conf conf1 v2).
    destruct e;inversion H4.
    subst.
    pose proof mergeConfigFuncBothExistEquiv. 
    assert (exists c v2 : configuration M,
         Result c = mergeConfigFunc' conf conf conf2/\
         Result v2 = mergeConfigFunc' conf conf1 c /\ equivConf v0 v2).
   apply H5 with (conf:=conf') (x:= conf1') (y':= conf2') (v:= v);auto.     
   apply equivConf_Sym;auto.  apply equivConf_Sym;auto.        
   repeat (match goal with
           | [H: exists _, _ |- _] => destruct H
           | [H: _ /\ _|- _] => destruct H
           end).
    rewrite <- Heqe1 in H7. inversion H7;subst. 
     rewrite <- Heqe2 in H8.
 inversion H8;subst.     
 apply equivConf_Sym;auto.
 apply confEquivList_sym in H1;apply confEquivList_cons_nil in H1;auto. 
 inversion H1.
 destruct l.
 apply confEquivList_cons_nil in H1;inversion H1.
 remember (innerCombineFunc'''' conf' (c :: l')).
 destruct o;inversion H2.
 clear H6.
 remember (innerCombineFunc'''' conf (c0 :: l)).
 destruct o;inversion H4.
 assert (equivConf c2 c1).
 apply IHconfEquivList with (conf':=conf') (conf:=conf);auto.
 remember (mergeConfigFunc' conf' conf1' c1 ).
 destruct e;inversion H2.
 remember (mergeConfigFunc' conf' conf2' v).
 destruct e;inversion H2.
 remember (mergeConfigFunc' conf conf2 c2 ).
 destruct e;inversion H4.
 clear H10.
 remember (mergeConfigFunc' conf conf1 v3).
 destruct e;inversion H4.
 subst.
 pose proof mergeConfigFuncBothExistEquiv'.
 assert (exists c v2 : configuration M,
         Result c = mergeConfigFunc' conf conf2 c2 /\
         Result v2 = mergeConfigFunc' conf conf1 c /\ equivConf v0 v2).
apply H7 with (conf:=conf') (c0:=c1) (x:=conf1') (y:=conf2') (v:=v);auto; 
  apply equivConf_Sym;auto.
 repeat (match goal with
           | [H: exists _, _ |- _] => destruct H
           | [H: _ /\ _|- _] => destruct H
           end).
 rewrite <- Heqe1 in H9.
 inversion H9;subst. rewrite <- Heqe2 in H10.
inversion H10;subst.   apply equivConf_Sym;auto. 
  - intros.
    SearchAbout innerCombineFunc''''.
    pose proof innterCombineFuncEquivExistList'. 
    assert  ( exists v3 : configuration M, Some v3 = innerCombineFunc'''' conf' l2 /\ equivConf v2 v3).
    apply H4 with (l:=l3);auto.
    apply confEquivList_sym;auto.     
   destruct H5.   destruct H5.    
 apply IHconfEquivList1 with (v1:=v1) (conf:=conf)  in H5;auto.    
 eapply equivConf_Trans.     apply H5;auto. apply equivConf_Sym;auto. 
Qed.

Lemma Permutation_filter: forall A l1 l2 f,
    Permutation l1 l2 ->
    Permutation (@filter A f l1) (@filter A f l2).
Proof.
  intros.
  generalize dependent f.
  induction H.
  -  intros.
    simpl;auto.      
  - intros.
    simpl in *.
    destruct (f x).
    constructor.  apply IHPermutation.    apply IHPermutation. 
  - intros.
    simpl in *.
    destruct (f y).    
    destruct (f x).
    SearchAbout Permutation.
    apply  perm_swap;auto.
    constructor.  apply Permutation_refl;auto.    
    apply Permutation_refl;auto.
  - intros. eapply Permutation_trans. apply IHPermutation1. apply IHPermutation2;auto. 
Qed.

Lemma Permutation_filterList: forall A   l l1 l2 decA,
    Permutation l1 l2 ->
    Permutation (@filterList A l1 l decA) (@filterList A l2 l decA).
Proof.
  intros A l.
   induction l.   
 -  intros. simpl;auto.
  -  intros.
     simpl;auto.
     remember (inList decA a l1).
   destruct b.      
   remember (inList decA a l2).
   destruct b.
   apply IHl;auto.
   SearchAbout inList. 
   symmetry in Heqb; symmetry in Heqb0.
   apply reverseinListLemma in Heqb.
   apply reverseinListFalse in Heqb0.
   SearchAbout Permutation.    
   apply Permutation_in with (x:=a) in H;auto.
   contradiction.
   
    remember (inList decA a l2).
   destruct b.  symmetry in Heqb; symmetry in Heqb0.
    apply reverseinListLemma in Heqb0.
   apply reverseinListFalse in Heqb. apply Permutation_sym in H. 
   apply Permutation_in with (x:=a) in H;auto.
     contradiction.        
     constructor.  apply IHl;auto.
Qed.



Lemma equivConfSyncExists: forall M (conf conf' conf1 conf2: configuration M) e,
    equivConf conf conf' ->
    synchrony conf conf1 e ->
    (exists conf2, synchrony conf' conf2 e).
Proof.
  intros.
  unfold synchrony in *.
  destruct H0.
  unfold  combineFunc in *.
  remember (constructConfigList (dom (controlstate conf)) e conf).
  
  destruct e0;inversion H1.
  destruct v;inversion H1.   
  clear H4.
  unfold constructConfigList in *.
  pose proof constructListEquivExists''.
  remember (innerCombineFunc'''' conf (c :: v)).
  destruct o;inversion H1.
  pose proof constructListEquiv.
  remember H.
  clear Heqe1.
  unfold equivConf in e0. destruct e0. destruct H7. rewrite <- H7. 
  assert (exists l2 : list (configuration M), Result l2 = constructConfigList' (filter
               (fun x : scenario => inList event_definition_dec (eventDefinition e) (alphabet x))
               (filterList (finishedscenarios conf') (dom (controlstate conf)) scenario_dec)) e conf').
  eapply H2 with (scs:=(filter
               (fun x : scenario => inList event_definition_dec (eventDefinition e) (alphabet x))
               (filterList (finishedscenarios conf) (dom (controlstate conf)) scenario_dec))) ;auto.   
  apply H.  Focus 2. apply Heqe0.
  apply Permutation_filter;auto.
  apply Permutation_filterList;auto.
 unfold equivConf in H.   
  repeat match goal with
            | [ H: _ /\ _ |- _ ] => destruct H

                     end.
  auto.
 destruct H9. 
 rewrite <- H9.
 pose proof constructListEquiv.
 assert (confEquivList (c::v) x). 
 eapply H10 with (l1:=c::v) (l2:=x) (scs:=(filter
               (fun x : scenario => inList event_definition_dec (eventDefinition e) (alphabet x))
               (filterList (finishedscenarios conf) (dom (controlstate conf)) scenario_dec))) (scs':= (filter
            (fun x : scenario => inList event_definition_dec (eventDefinition e) (alphabet x))
            (filterList (finishedscenarios conf') (dom (controlstate conf)) scenario_dec)));auto. 
 apply H.    apply Permutation_filter;auto.
  apply Permutation_filterList;auto.  unfold equivConf in H.   
  repeat match goal with
            | [ H: _ /\ _ |- _ ] => destruct H

                     end.
  auto.
  apply Heqe0. auto.
  destruct x.
  apply confEquivList_sym in H11.   apply confEquivList_cons_nil in H11. inversion H11.
  pose proof innterCombineFuncEquivListExists.
 apply H12 with (conf':=conf') (l2:=(c1 :: x)) in Heqo;auto. 
  repeat (match goal with
           | [H: exists _, _ |- _] => destruct H
           | [H: _ /\ _|- _] => destruct H
           end).  
  rewrite <- H13.
  unfold removeEventFromConf in *. exists ( {|
      datastate := datastate x0;
      controlstate := controlstate x0;
      raisedevents := removeEvent' e (raisedevents x0);
      exportedevents := exportedevents x0;
      finishedscenarios := finishedscenarios x0;
      sceEventMap := sceEventMap x0 |});auto.

  (*split;auto.
  unfold equivConf in H.
    repeat match goal with
            | [ H: _ /\ _ |- _ ] => destruct H

                     end.
    SearchAbout Permutation.
  apply Permutation_in with (l:=raisedevents conf);auto.     *)
Qed.


Lemma removeEventPermu: forall l1 l2 e,
    Permutation l1 l2 ->
    Permutation (removeEvent' e l1) (removeEvent' e l2).
Proof.
  intros.
  generalize dependent e.
  induction H.
  - intros.
    simpl. constructor.
  - intros.
    simpl in *.
    destruct (raisedEvent_dec e x ).
    subst.  apply IHPermutation.
    constructor. apply IHPermutation.
  -  intros. simpl.
    destruct (raisedEvent_dec e y). subst .
    destruct (raisedEvent_dec y x).
    subst.  apply Permutation_refl;auto.
    constructor. apply Permutation_refl;auto.
    destruct (raisedEvent_dec e x);subst.
    constructor. apply Permutation_refl;auto.
    SearchAbout Permutation.
    apply perm_swap;auto.      
  -   intros.
      eapply Permutation_trans.
    apply IHPermutation1.  apply IHPermutation2.    
Qed.


Lemma removeEventIncl: forall l1 l2 e,
    incl l1 l2 ->
    incl (removeEvent' e l1) (removeEvent' e l2).
Proof.
  intro l1. induction l1. 
  
  - intros.
    simpl. unfold incl in *. intros. inversion H0. 
  - intros.
    simpl in *.
    destruct (raisedEvent_dec e a).
    subst.  apply IHl1. unfold incl in *;intros. apply H. right;auto. 
    simpl in *;unfold incl in *;intros.
    destruct H0;subst.
    SearchAbout removeEvent'.
    apply   removeEventPreservation;auto.
    apply H.     left;auto.
        
    apply IHl1;auto.
       intros.
    apply H;intuition;auto.
    
    
Qed.


Lemma equivConfSync: forall M (conf conf' conf1 conf2: configuration M) e,
    correct_configuration conf -> equivConf conf conf' ->
    synchrony conf conf1 e ->
    synchrony conf' conf2 e ->
    equivConf conf1 conf2.
Proof.
  intros.
  unfold synchrony in H1.
  unfold synchrony in H2.
  destruct H1;destruct H2.
  unfold combineFunc in H3.
  unfold combineFunc in H4.
  remember (constructConfigList (dom (controlstate conf)) e conf).
  destruct e0;inversion H3. clear H6.
  remember (constructConfigList (dom (controlstate conf')) e conf' ).
  destruct e0;inversion H4.
  destruct v;inversion H3. clear H7.
  destruct v0;inversion H6. clear H7.
  unfold constructConfigList in Heqe0.
  unfold constructConfigList in Heqe1.
  SearchAbout filter.
  assert (equivList (filter
               (fun x : scenario => inList event_definition_dec (eventDefinition e) (alphabet x))
               (filterList (finishedscenarios conf) (dom (controlstate conf)) scenario_dec)) (filter
               (fun x : scenario => inList event_definition_dec (eventDefinition e) (alphabet x))
               (filterList (finishedscenarios conf') (dom (controlstate conf')) scenario_dec))).
  apply filterEquiv;auto.
  unfold equivConf in H0.
  destruct H0. destruct H5. rewrite <- H5.
  SearchAbout filterList.
  apply filterListEquiv;auto.
   repeat match goal with
            | [ H: _ /\ _ |- _ ] => destruct H

                     end.
   auto.
   pose proof constructListEquiv''.
   assert (Permutation (c :: v) (c0 :: v0)).
   apply H7 with (scs:=(filter
               (fun x : scenario => inList event_definition_dec (eventDefinition e) (alphabet x))
               (filterList (finishedscenarios conf) (dom (controlstate conf)) scenario_dec)) ) (scs':=(filter
            (fun x : scenario => inList event_definition_dec (eventDefinition e) (alphabet x))
            (filterList (finishedscenarios conf') (dom (controlstate conf')) scenario_dec))) (conf:=conf) (conf':=conf') (e:=e);auto.
  
   apply filterUniq.
   destruct H. 
   apply uniqListFilter;auto.
   remember (innerCombineFunc'''' conf (c :: v)).
   destruct o;inversion H3.
   remember (innerCombineFunc'''' conf' (c0 :: v0)).
   destruct o;inversion H6.    
   assert (equivConf c1 c2).
   
   apply innterCombineFuncEquiv with (conf:=conf) (conf':=conf') (l1:=c::v) (l2:=c0::v0);auto. 
   unfold removeEventFromConf.
   unfold equivConf in H9;unfold equivConf;simpl.    
    repeat match goal with
            | [ H: _ /\ _ |- _ ] => destruct H

           end.
    split;auto.  split;auto.  split. Focus 2. repeat (split;auto).

    apply removeEventIncl;auto. 
  apply removeEventIncl;auto. 
    Qed.



Print filter.


      
Inductive chainMergeWithFuel M : configuration M -> configuration M -> nat ->  Prop :=
| basic_zero : forall conf, chainMergeWithFuel  conf conf 0 
| basic_one : forall conf conf' e, synchrony conf conf' e -> chainMergeWithFuel conf conf' (S O)
| inductive_multi: forall conf conf' conf'' n  e,  chainMergeWithFuel conf conf' n  -> synchrony conf' conf'' e ->  chainMergeWithFuel conf conf'' (S n)
.



Lemma chainMergeCorrect: forall M n (conf conf1 : configuration M),
    WellFormed M ->
    initialConfig conf ->
    chainMergeWithFuel conf conf1 n ->
    correct_configuration conf1.
Proof.
  intros.
  induction H1.
  destruct H0;auto.
   unfold WellFormed in H.
              repeat match goal with
            | [ H: _ /\ _ |- _ ] => destruct H

                     end.
  destruct H4. 
   repeat match goal with
            | [ H: _ /\ _ |- _ ] => destruct H

                     end.
              
   apply termL5 with (conf:=conf) (e:=e);auto.
   destruct H0;auto.
   unfold synchrony in H1.
   destruct H1.
   destruct H0. destruct H0.
   apply raised_wellform';auto.
unfold WellFormed in H.
              repeat match goal with
            | [ H: _ /\ _ |- _ ] => destruct H

                     end.
  destruct H5. 
   repeat match goal with
            | [ H: _ /\ _ |- _ ] => destruct H

                     end.
   remember H0. clear Heqi. apply  IHchainMergeWithFuel in i.
   apply termL5 with (conf:=conf') (e:=e);auto.
     unfold synchrony in H2.
   destruct H2.
   destruct i. 
   apply raised_wellform';auto.
Qed.

Lemma chainMergeCorrect': forall M n (conf conf1 : configuration M),
    WellFormed M ->
    correct_configuration conf ->
    chainMergeWithFuel conf conf1 n ->
    correct_configuration conf1.
Proof.
  intros.
   unfold WellFormed in H.
              repeat match goal with
            | [ H: _ /\ _ |- _ ] => destruct H

                     end.
  destruct H4. 
   repeat match goal with
            | [ H: _ /\ _ |- _ ] => destruct H

          end.

   
  induction H1.
  auto.

   apply termL5 with (conf:=conf) (e:=e);auto.
   destruct H0;auto.
   unfold synchrony in H1.
   destruct H1.
 
   apply raised_wellform';auto.
   
   apply  IHchainMergeWithFuel in H0. 
   apply termL5 with (conf:=conf') (e:=e);auto.
     unfold synchrony in H20.
   destruct H20.
   destruct H0. 
   apply raised_wellform';auto.
Qed.


Lemma chainMergeSync: forall M (conf conf1 : configuration M),
    chainMergeWithFuel conf conf1 1 ->
    (exists e, synchrony conf conf1 e). 
Proof.
  intros.
  inversion H;subst.
  exists e;auto.
  inversion H1;subst.
  exists e;auto. 
Qed.

Lemma chainMergeSync': forall n M (conf conf1 : configuration M),
    chainMergeWithFuel conf conf1 (S n) ->
    (exists e c , synchrony conf c e). 
Proof.
  intro n;induction n.
  - intros. apply chainMergeSync in H;auto.  destruct H. exists x. exists conf1;auto.
  - intros. inversion H;subst. apply IHn in H1. auto. 
Qed.

Lemma chainMergeNoFuel: forall n M  (conf conf1 : configuration M),
    initialConfig conf ->
    chainMergeWithFuel conf conf1 (S n) ->
    (exists e, chainMerge conf conf1 e). 
Proof.
  intro n;induction n.   intros.
  apply chainMergeSync in H0. destruct H0. 
   exists x.     
 apply basic';auto.  
 intros.
 inversion H0;subst.
 apply IHn in H2;auto.
 destruct H2.
 exists x. apply chain' with (conf':=conf') (event2:=e);auto. 
Qed. 
  


Lemma wellFormedNoErrorSync: forall M (conf : configuration M) ,
    WellFormed M ->
    syncProgress conf ->
    correct_configuration conf ->
    ~ (finalConfig conf) ->
    (exists c e, synchrony conf c e).
Proof.
  intros.
  unfold synchrony. 
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
  destruct H12.  exists x.
  exists r;intuition. 

Qed.

Lemma filterListIncl: forall A l2 l1 (p: forall n m: A, {n = m} + { n <> m}),
    incl l2 l1 ->
    filterList l1 l2 p = nil
    . 
Proof.
   intros A l2;induction l2. 
   - intros.
     simpl in *. auto. 
     
   - intros. simpl in *.
     unfold incl in H.
     remember (inList p a l1).
     destruct b.
     symmetry in Heqb.   
     apply reverseinListLemma in Heqb.
     apply IHl2;auto.  unfold incl;intros. apply H. right;auto.
     symmetry in Heqb.
     SearchAbout inList.
     apply reverseinListFalse in Heqb.
     exfalso;apply Heqb. apply H;auto. left;auto. 
Qed.
     


Lemma finalNoSync: forall M (conf : configuration M) ,
    (finalConfig conf) ->
    ~(exists c e, synchrony conf c e).
Proof.
  intros.
  unfold not;intros. 
  unfold synchrony.
  destruct H0. destruct H0.
  unfold synchrony in H0.
  destruct H0.
  unfold finalConfig in H.
  destruct H.  destruct ((raisedevents conf)). inversion H0. inversion H.

  unfold combineFunc in H1.
  remember (constructConfigList (dom (controlstate conf)) x0 conf).
  destruct e;inversion H1.
  destruct v;inversion H1.
  unfold constructConfigList in Heqe.
  clear H4.
  remember ((filter
              (fun x : scenario => inList event_definition_dec (eventDefinition x0) (alphabet x))
              (filterList (finishedscenarios conf) (dom (controlstate conf)) scenario_dec))).
  destruct l.
  simpl in Heqe. inversion Heqe.
  SearchAbout filter.
  assert ((filterList (finishedscenarios conf) (dom (controlstate conf)) scenario_dec) <> []).
  unfold not;intros.
  rewrite H2 in Heql.
  simpl in Heql. inversion Heql.
  apply H2.
  apply filterListIncl;auto. 
 
  Qed.


Lemma weakConfluence: forall n M (conf  conf1 conf2: configuration M)  ,
    WellFormed M ->
     deter_prop M ->
    initialConfig conf ->
    chainMergeWithFuel conf conf1 n ->
    chainMergeWithFuel conf conf2 1 ->
    finalConfig conf1 \/ (exists n' conf1' conf2',
        chainMergeWithFuel conf1 conf1' 1 /\ chainMergeWithFuel conf2 conf2' n' /\
        equivConf conf1' conf2'). 
Proof.
    intro n;induction n. 
    - intros. inversion H2;subst.
      inversion H3;subst.
      right.       exists (O).
      exists conf2. exists conf2.
      split.
      apply basic_one with (e:=e);auto.
      split. apply basic_zero.
      apply equivConf_Refl;auto.
      right. 
      inversion H5;subst.
      exists O. exists conf2. exists conf2.
      split.  apply basic_one with (e:=e);auto.
      split. apply basic_zero.
      apply equivConf_Refl;auto.
    - intros.
      inversion H2;subst. 
      assert (finalConfig conf1 \/ ~ (finalConfig conf1)).
      apply excluded_middle.
      destruct H4. left;auto.
      right. exists (S O).
      apply chainMergeSync in H3.
      destruct H3. 
      assert (e = x \/ e <> x).
      apply excluded_middle.
      destruct H5.
      subst.
      unfold synchrony in H3.
      unfold synchrony in H7.
      destruct H7.
      destruct H3.
      rewrite H7 in H6.
      inversion H6;subst.
      pose proof wellFormedNoErrorSync.
      assert (exists (c : configuration M) (e : raisedEvent), synchrony conf1 c e). 
      apply H8;auto.
     
      apply chainMergeSync in H2.
      destruct H2.
      remember H.
      clear Heqw.
     unfold WellFormed in w.
              repeat match goal with
            | [ H: _ /\ _ |- _ ] => destruct H

                     end.
        
     apply  preserveSync with (conf:=conf) (re:=x0);auto.
     apply basic';auto.
     split. apply noMultIn;auto. apply noMultImportedIn;auto.
     apply chainMergeSync in H2.
     destruct H2.
     destruct H1.
      unfold WellFormed in H.
              repeat match goal with
            | [ H: _ /\ _ |- _ ] => destruct H

                     end.
              destruct H15.
               repeat match goal with
            | [ H: _ /\ _ |- _ ] => destruct H

                     end.
               apply termL5 with (conf:=conf) (e:=x0);auto.
               unfold synchrony in H2.
               destruct H1. apply  raised_wellform';auto. intuition;auto.
               destruct H9.  destruct H9.  exists x0. exists x0. split.
               apply basic_one with (e:=x1);intuition. split. apply basic_one with (e:=x1);intuition.
     apply equivConf_Refl;auto.         
    
      pose proof diamond.
      assert (   exists conf1' conf2' : configuration M,
                 synchrony conf1 conf1' x /\ synchrony conf2 conf2' e /\ equivConf conf1' conf2').
      apply H6 with (conf:=conf);auto. destruct H1;auto.
      destruct H8.
      destruct H8.
      exists x0. exists x1.
      split. apply basic_one with (e:=x);intuition.
      split. apply basic_one with (e:=e);intuition.
      intuition.
      remember H5. clear Heqc. 
      apply IHn with (conf2:=conf2) in H5;auto.
      destruct H5.
      apply finalNoSync in H4.
      exfalso;apply H4.
      exists conf1. exists e;auto. 
     
      destruct H4.
      destruct H4.
      destruct H4.
     
      destruct H4.
      apply chainMergeSync in H4.
      destruct H4.
      
      assert (e= x2 \/ e <> x2).
      apply excluded_middle.
      destruct H6.
      subst.
      unfold synchrony in H8.
      unfold synchrony in H4.
      destruct H8. 
      destruct H4.
      rewrite H8 in H7.
      inversion H7; subst.
      
      assert (finalConfig conf1 \/ ~ (finalConfig conf1)).
      apply excluded_middle.
      destruct H9.
      left;auto.
      right.
      destruct H5.
      exists (S x).
      assert (exists x' e', synchrony conf1 x' e').
      apply wellFormedNoErrorSync;auto.

         
    
      remember H.
      clear Heqw.
     unfold WellFormed in w.
              repeat match goal with
            | [ H: _ /\ _ |- _ ] => destruct H

                     end.
    Focus 2.           
    apply chainMergeCorrect with (n:= S n) (conf:=conf);auto.
    apply chainMergeNoFuel in H2;auto.
    destruct H2. 
     apply  preserveSync with (conf:=conf) (re:=x0);auto.
   split. apply noMultIn;auto. apply noMultImportedIn;auto.      
      destruct H11.
      destruct H11.
      exists x0.
      assert (exists y, synchrony x1 y x3).
      eapply equivConfSyncExists;auto. apply H10. apply H11. 
      destruct H12.
      exists x4.
      split. apply basic_one with (e:=x3);intuition.
      split. apply inductive_multi with (conf':=x1) (e:=x3);auto.
      apply equivConfSync with (conf:=conf1) (conf':=x1) (e:=x3);auto.
      apply chainMergeCorrect with (conf:=conf) (n:= S n);auto. 
    
      
       pose proof diamond.
      assert (   exists conf1' conf2' : configuration M,
                 synchrony conf1 conf1' x2 /\ synchrony x0 conf2' e /\ equivConf conf1' conf2').
      apply H7 with (conf:=conf');auto.
      SearchAbout conf'.
      destruct n. 
      inversion c;auto. subst.  left;auto.     
      right.   exists conf.   
      apply chainMergeNoFuel with (n:=n);auto.
         
      (*apply chainMergeCorrect with (n:=n) (conf:=conf);auto. *)
  
       destruct H9;auto.
      destruct H9.
      destruct H9.
      destruct H10.
      right.
      exists (S x).
      exists x3.
      assert (exists x3', synchrony x1 x3' e).
       eapply equivConfSyncExists;auto. destruct H5. apply e0. apply H10. 
     
      destruct H12. 
      exists x5. 
            
      split. apply basic_one with (e:=x2);intuition.
      split.   apply inductive_multi with (conf':=x1) (e:=e);intuition.
        eapply equivConf_Trans. apply H11. apply equivConfSync with (conf:=x0) (conf':=x1) (e:=e);intuition;auto.
        assert (chainMergeWithFuel conf x0 (S n)).
        apply inductive_multi with (conf':=conf') (e:=x2);auto.
        apply chainMergeCorrect with (conf:=conf) (n:= S n);auto. 
Qed.

Local Close Scope N. 
Lemma termL4': forall M (conf conf' : configuration M) e, chainMerge conf conf' e ->
       List.length (finishedscenarios conf) < List.length (finishedscenarios conf').
Proof.
  intros. induction H.
-  apply termL4 with (e:=event);auto. 
- apply termL4 in H0. omega. 
Qed.

Lemma chainMergeFuelInte: forall n M (conf conf' conf'': configuration M) e,
    chainMerge conf conf' e ->
    chainMergeWithFuel conf' conf'' n ->
    chainMerge conf conf'' e.
Proof.
  intro n;induction n. 
  - intros. inversion H0. subst. auto.
  -  intros. 
     inversion H0.
     subst.
          
      apply chain' with (conf':=conf') (event2:=e0);auto.
      subst.
      assert (chainMerge conf conf'0 e).
      apply IHn with (conf'':=conf'0) (conf':=conf');auto.
   apply chain' with (conf':=conf'0) (event2:=e0);auto.    
Qed.


Lemma weakConfluence': forall n M (conf  conf1 conf2: configuration M)  ,
    WellFormed M ->
     deter_prop M ->
    (initialConfig conf \/ (exists iconf e, chainMerge iconf conf e))->
    chainMergeWithFuel conf conf1 n ->
    chainMergeWithFuel conf conf2 1 ->
   ((exists x econf1, chainMergeWithFuel conf2 econf1 x /\ equivConf conf1 econf1) \/ exists n' conf1' conf2',
        chainMergeWithFuel conf1 conf1' 1 /\ chainMergeWithFuel conf2 conf2' n' /\
        equivConf conf1' conf2'). 
Proof.
    intro n;induction n. 
    - intros. inversion H2;subst.
      inversion H3;subst.
      right.        exists (O).
      exists conf2. exists conf2.
      split.
      apply basic_one with (e:=e);auto.
      split. apply basic_zero.
      apply equivConf_Refl;auto.
      right. 
      inversion H5;subst.
      exists O. exists conf2. exists conf2.
      split.  apply basic_one with (e:=e);auto.
      split. apply basic_zero.
      apply equivConf_Refl;auto.
    - intros.
      inversion H2;subst.
      apply chainMergeSync in H3.
      destruct H3.
      assert (e = x \/ e <> x).
       apply excluded_middle.
       destruct H4. subst.
        unfold synchrony in H3.
      unfold synchrony in H7.
      destruct H7.
      destruct H3.
      rewrite H5 in H6.
      inversion H6;subst.
      left;auto.             
      exists 0. exists conf2. constructor.        
      constructor. apply equivConf_Refl;auto.            
    
      pose proof diamond.
      assert (   exists conf1' conf2' : configuration M,
                 synchrony conf1 conf1' x /\ synchrony conf2 conf2' e /\ equivConf conf1' conf2').
      apply H5 with (conf:=conf);auto.
     (* destruct H1;auto. destruct H1;auto. destruct H1.
      destruct H1.
        unfold WellFormed in H.
              repeat match goal with
            | [ H: _ /\ _ |- _ ] => destruct H

                     end.
              destruct H8.
      repeat match goal with
            | [ H: _ /\ _ |- _ ] => destruct H

             end.
      apply termL5' with (conf:=x0) (e:=x1);auto.
      remember H1. clear Heqc. apply chainMergeInitial in H1.
      apply chainMergeInitialEvent in c.
      destruct H1. destruct H1.
      apply raised_wellform';auto. 
            *)  
      destruct H6.
      destruct H6.
      right. exists (S O). exists x0. exists x1.
      split. apply basic_one with (e:=x);intuition.
      split. apply basic_one with (e:=e);intuition.
      intuition.

      remember H5. clear Heqc. 
      apply IHn with (conf2:=conf2) in H5;auto.
      destruct H5.
      destruct H4.    left. destruct H4. destruct H4. exists (S x).
      assert (exists x', synchrony x0 x' e).
       eapply equivConfSyncExists;auto. apply H5. apply H8. 
      destruct H6. 
      exists x1.     split;auto. eapply inductive_multi. apply H4. apply H6. 

       apply equivConfSync with (conf:=conf') (conf':=x0) (e:=e);intuition;auto.
       
        apply chainMergeCorrect with (conf:=conf) (n:=  n);auto.
   SearchAbout  chainMergeWithFuel.            
   apply chainMergeCorrect' with (conf:=conf) (n:=n);auto.
   destruct H7. destruct H1.
   remember H1. clear Heqc0. apply chainMergeInitial in H1. destruct H1.
   unfold WellFormed in H. 

        repeat match goal with
            | [ H: _ /\ _ |- _ ] => destruct H

                     end.
              destruct H14.
      repeat match goal with
            | [ H: _ /\ _ |- _ ] => destruct H

             end. 
   apply termL5' with (conf:=x2) (e:=x3);auto. 
   destruct H1.
   apply chainMergeInitialEvent in c0.   intuition.  
      destruct H4.
      destruct H4.
      destruct H4.
     
      destruct H4.
      apply chainMergeSync in H4.
      destruct H4.
      
      assert (e= x2 \/ e <> x2).
      apply excluded_middle.
      destruct H6.
      subst.
      unfold synchrony in H8.
      unfold synchrony in H4.
      destruct H8. 
      destruct H4.
      rewrite H8 in H7.
      inversion H7; subst.
      left.
      exists x.  exists x1. intuition. 
      destruct H5. 
      
       pose proof diamond.
      assert (   exists conf1' conf2' : configuration M,
                 synchrony conf1 conf1' x2 /\ synchrony x0 conf2' e /\ equivConf conf1' conf2').
      apply H9 with (conf:=conf');auto.


      destruct H1.
      destruct n.       
      inversion c.
      subst.
      left;auto.
      SearchAbout chainMergeWithFuel. right.
      exists conf.  apply chainMergeNoFuel with (n:=n);auto.
      destruct H1.
      destruct H1.
      right.
      exists x3.
      SearchAbout  chainMergeWithFuel.   
      exists x4.      
      eapply chainMergeFuelInte ;auto.
   apply H1.       apply c.      
     (* apply chainMergeCorrect' with (n:=n) (conf:=conf);auto.*)

     (*     destruct H1;auto. destruct H1;auto. destruct H1.
      destruct H1.
        unfold WellFormed in H.
              repeat match goal with
            | [ H: _ /\ _ |- _ ] => destruct H

                     end.
              destruct H11.
      repeat match goal with
            | [ H: _ /\ _ |- _ ] => destruct H

             end.
      apply termL5' with (conf:=x3) (e:=x4);auto.
      remember H1. clear Heqc0. apply chainMergeInitial in H1.
      apply chainMergeInitialEvent in c0.
      destruct H1. destruct H1.
      apply raised_wellform';auto.
      *)
      
  
       destruct H10;auto.
      destruct H10.
      destruct H10.
      destruct H11.
      right.
      exists (S x).
      exists x3.
      assert (exists x3', synchrony x1 x3' e).
       eapply equivConfSyncExists;auto. apply H7. apply H11. 
      destruct H13. 
      exists x5. 
            
      split. apply basic_one with (e:=x2);intuition.
      split.   apply inductive_multi with (conf':=x1) (e:=e);intuition.
      eapply equivConf_Trans. apply H12.
      apply equivConfSync with (conf:=x0) (conf':=x1) (e:=e);auto.
      assert (chainMergeWithFuel conf x0 (S n)).
      apply inductive_multi with (conf':=conf') (e:=x2);intuition.      
         apply chainMergeCorrect' with (conf:=conf) (n:= S n);auto. 
         destruct H1.
   destruct H1;auto.          
  destruct H1.  destruct H1.  remember H1. clear Heqc0. 
    unfold WellFormed in H. 

        repeat match goal with
            | [ H: _ /\ _ |- _ ] => destruct H

                     end.
              destruct H17.
      repeat match goal with
            | [ H: _ /\ _ |- _ ] => destruct H

             end. 
   apply termL5' with (conf:=x6) (e:=x7);auto. apply chainMergeInitial in H1. 
   destruct H1. destruct H1. 
   apply chainMergeInitialEvent in c0.    intuition.

   
Qed.


    

Lemma Permutation_dom: forall (A B:Type)  (env env': list (A*B)),
    Permutation env env' ->
    Permutation (dom env) (dom env').
Proof.
  intros.
  induction H.
  -  apply Permutation_refl;auto.
  -  simpl.
     destruct x.   simpl in *.
     constructor;auto.      
  -  simpl in *.
     destruct y.  destruct x.  simpl.
     constructor.
  -  eapply Permutation_trans.      
     apply IHPermutation1.
     auto.
Qed.

Lemma correct_equivConf: forall M (conf conf': configuration M),
    equivConf conf conf' ->
    correct_configuration conf ->
    correct_configuration conf'. 
Proof.
  intros.
  unfold  equivConf in H.
    repeat match goal with
            | [ H: _ /\ _ |- _ ] => destruct H

           end.
  destruct H0. 
  split;(try (rewrite <- H); try (rewrite <- H1));auto.   
  
    
  pose proof Permutation_NoDup.
 rewrite uniqListNoDupEq.   rewrite uniqListNoDupEq in finish_uniq.
  apply H0 with (l:=finishedscenarios conf);auto.
  unfold scenarioInclusion in *.
  unfold incl in *.
  intros.

  assert (In a (finishedscenarios conf)).
  apply Permutation_in with (l:=finishedscenarios conf').   apply Permutation_sym;auto.
  auto. apply inclusion in H8.  apply Permutation_in with (l:=(dom (controlstate conf)));auto. 
  rewrite H1.   apply Permutation_refl;auto.
  
  Focus 2.
  intros.
 apply  sceEventMapAlphabet;auto. apply Permutation_in with (l:=sceEventMap conf');auto.   
   
 apply Permutation_sym;auto.

 
 apply Permutation_sym.
  
 eapply Permutation_trans.
 apply Permutation_sym.   apply H4.
 eapply Permutation_trans.
 apply Permutation_sym.  apply sceEventMapRange.
 apply Permutation_dom;auto.
 intros.
 apply raise_in_finished with (sce:=sce);auto. 
 apply Permutation_in with (l:=(sceEventMap conf'));auto.  
  apply Permutation_sym;auto.  

   intros.
 apply raisedType_finished with (sce:=sce);auto. 
 apply Permutation_in with (l:=(sceEventMap conf'));auto.  
 apply Permutation_sym;auto.
 
Qed.


  


Lemma Confluence: forall n m M (conf  conf1 conf2: configuration M)  ,
    WellFormed M ->
     deter_prop M ->
    initialConfig conf ->
    chainMergeWithFuel conf conf1 n ->
    chainMergeWithFuel conf conf2 m ->
    (exists x econf1, chainMergeWithFuel conf2 econf1 x /\ equivConf conf1 econf1) \/ (exists x econf2, chainMergeWithFuel conf1 econf2 x /\ equivConf conf2 econf2) \/ (exists n' m' conf1' conf2',
        chainMergeWithFuel conf1 conf1' m' /\ chainMergeWithFuel conf2 conf2' n' /\
        equivConf conf1' conf2').
Proof.
  intro n;induction n.
  - intros. inversion H2;subst.
   right. right.     exists O.
    exists m. exists conf2. exists conf2.
    split;auto.
    split. constructor.
    apply equivConf_Refl;auto.
  -
    intros.
    
    inversion H2;subst.
    pose proof weakConfluence'.
    remember H3. clear Heqc. 
    apply H4 with (conf2:=conf1) in H3;auto.
    destruct H3.
    right;left.
    auto.
    destruct H3.   destruct H3. destruct H3.
    right;right.
    exists 1. exists x. exists x1. exists x0.
    intuition.
    apply equivConf_Sym;auto.
    remember H3. clear Heqc. 
    apply IHn with (conf1:=conf') in H3;auto.
    destruct H3.
    destruct H3.   destruct H3. destruct H3.
    left.
    assert (exists ex0 , synchrony x0 ex0 e).
     eapply equivConfSyncExists;auto. apply H4. apply H8.  
    destruct H6. 
    exists (S x).
    exists x1.
    split;auto.
    eapply inductive_multi;auto. apply H3. apply H6.


     apply equivConfSync with (conf:=conf') (conf':=x0) (e:=e);auto.
       
         apply chainMergeCorrect with (conf:=conf) (n:= n);auto. 
       
    
    destruct H3.
 
     destruct H3.
     destruct H3.   destruct H3.
     assert (chainMergeWithFuel conf' conf1 1).
     apply basic_one with (e:=e);auto.
     pose proof weakConfluence'.
    apply H7 with (conf2:=conf1) in H3;auto. 
    destruct H3.
    destruct H3. destruct H3. destruct H3.
    right;left.
    exists x1.   exists x2.
    split;auto.
    eapply equivConf_Trans.   apply H4. auto.
    destruct H3. destruct H3. destruct H3.
    right;right;auto.
    destruct H3. destruct H9. SearchAbout chainMergeWithFuel. apply chainMergeSync in H3.
   destruct H3.     
   assert (exists x0', synchrony conf2 x0' x4).
    eapply equivConfSyncExists;auto. apply equivConf_Sym in H4;apply H4. apply H3. 
   destruct H11.
   exists (S O). exists x1. exists x3.  exists x5.
   split;intuition;auto.
   apply basic_one with (e:=x4);auto.    
   eapply equivConf_Trans. apply equivConf_Sym in H10. apply H10. apply equivConfSync with (conf:=x0) (conf':=conf2) (e:=x4);auto. assert (correct_configuration conf2). 
         
   apply chainMergeCorrect with (conf:=conf) (n:= m);auto.
   apply correct_equivConf with (conf:=conf2);auto. 
    apply equivConf_Sym;auto. 

 
   inversion H5. 
   subst. 
   left;auto.
  subst. 
  right. exists conf. exists e0. apply basic';auto.
  subst. apply chainMergeNoFuel in H5;auto. right. exists conf;auto. 
  destruct H3. destruct H3. destruct H3. destruct H3.
   pose proof weakConfluence'.
   assert (chainMergeWithFuel conf' conf1 1).
   apply basic_one with (e:=e);auto. 
   destruct H3.
   apply H4 with (conf2:=conf1) in H3;auto.
   destruct H3.
   destruct H3.
   destruct H3. destruct H3.
   
 
   destruct H7.
   right;right.
   exists x. exists x3. exists x4. exists x2. split;auto. split;auto.
   eapply equivConf_Trans. apply equivConf_Sym in H9;apply H9. auto.
     destruct H3.
   destruct H3.
   destruct H3. destruct H3.
   destruct H9.   destruct H7.
   right;right.
   apply chainMergeSync in H3. destruct H3. 
   assert (exists x2' , synchrony x2 x2' x6).
    eapply equivConfSyncExists;auto. apply H11. apply H3. 
   destruct H12. exists (S x). exists x3. exists  x5. exists x7.
   split;auto. split;auto.    eapply inductive_multi;auto. apply H7. apply H12.
   eapply equivConf_Trans. apply equivConf_Sym in H10;apply H10.  
   apply equivConfSync with (conf:=x1) (conf':=x2) (e:=x6);auto. 
    assert (correct_configuration x2).
   
    apply chainMergeCorrect' with (conf:=conf2) (n:= x);auto.
       apply chainMergeCorrect with (conf:=conf) (n:= m);auto.  
   apply correct_equivConf with (conf:=x2);auto. 
  apply equivConf_Sym;auto.  
    inversion H5. 
   subst. 
   left;auto.
  subst. 
  right. exists conf. exists e0. apply basic';auto.
  subst. apply chainMergeNoFuel in H5;auto. right. exists conf;auto. 
 
   
Qed. 


Lemma Confluence': forall n m M (conf  conf1 conf2: configuration M)  ,
    WellFormed M ->
     deter_prop M ->
    initialConfig conf ->
    chainMergeWithFuel conf conf1 n ->
    chainMergeWithFuel conf conf2 m ->
     (exists n' m' conf1' conf2',
        chainMergeWithFuel conf1 conf1' m' /\ chainMergeWithFuel conf2 conf2' n' /\
        equivConf conf1' conf2').
Proof.
  intro n;induction n.
  - intros. inversion H2;subst.
  exists O.
    exists m. exists conf2. exists conf2.
    split;auto.
    split. constructor.
    apply equivConf_Refl;auto.
  -
    intros.
    
    inversion H2;subst.
    pose proof weakConfluence'.
    remember H3. clear Heqc. 
    apply H4 with (conf2:=conf1) in H3;auto.
    destruct H3.

    destruct H3.   destruct H3. destruct H3.
    exists O. exists x. exists x0. exists conf2.
    split;auto. split. constructor. apply equivConf_Sym;auto. 
    
    destruct H3.   destruct H3. destruct H3.
    exists 1. exists x. exists x1. exists x0.
    intuition.
    apply equivConf_Sym;auto.

    
    remember H3. clear Heqc. 
    apply IHn with (conf1:=conf') in H3;auto.
    destruct H3.
    destruct H3.   destruct H3. destruct H3.


    pose proof weakConfluence'.
    destruct H3. destruct H6. 
    assert ( chainMergeWithFuel conf' conf1 1).
    apply basic_one with (e:=e);auto.
    
    apply H4 with (conf2:=conf1) in H3;auto.
    destruct H3.
    destruct H3.   destruct H3. destruct H3.
    exists x. exists x3. exists x4. exists x2.
    split;auto. split;auto. eapply equivConf_Trans. apply equivConf_Sym in H10;apply H10;auto.
    auto. 

    destruct H3.
    destruct H3.   destruct H3. destruct H3.
   destruct H10. 
  

   apply chainMergeSync in H3.
   destruct H3.     
   assert (exists x0', synchrony x2 x0' x6).
    eapply equivConfSyncExists;auto. apply H7. apply H3. 
   
   destruct H12.  exists (S x). exists x3. exists  x5. exists x7.
   split;auto. split;auto.    eapply inductive_multi;auto. apply H6. apply H12.
   eapply equivConf_Trans. apply equivConf_Sym in H11;apply H11.

    apply equivConfSync with (conf:=x1) (conf':=x2) (e:=x6);auto. 
    assert (correct_configuration x2).
   
    apply chainMergeCorrect' with (conf:=conf2) (n:= x);auto.
       apply chainMergeCorrect with (conf:=conf) (n:= m);auto.  
   apply correct_equivConf with (conf:=x2);auto. 
   apply equivConf_Sym;auto.


    inversion H5. 
   subst. 
   left;auto.
  subst. 
  right. exists conf. exists e0. apply basic';auto.
  subst. apply chainMergeNoFuel in H5;auto. right. exists conf;auto. 
  
   
Qed.

Theorem deterministicMacroStep: 
   forall m n M (conf conf' conf'': configuration M) ,   WellFormed M ->
     deter_prop M -> initialConfig conf -> chainMergeWithFuel conf conf' m -> chainMergeWithFuel conf conf'' n -> finalConfig conf' -> finalConfig conf'' -> equivConf conf' conf''.
Proof.
  pose proof Confluence'.
  intros.
  assert (      exists (n' m' : nat) (conf1' conf2' : configuration M),
        chainMergeWithFuel conf' conf1' m' /\
        chainMergeWithFuel conf'' conf2' n' /\ equivConf conf1' conf2').
  apply H with (n:=m) (m:=n) (conf:=conf);auto.
  destruct H7. destruct H7.
  destruct H7. destruct H7.
  destruct H7. 
  destruct H8.
  SearchAbout finalConfig.
  apply finalNoSync in H5.
  apply finalNoSync in H6.
  destruct x0.
  destruct x. inversion H7;subst. inversion H8;subst. auto.
  inversion H8;subst.
  apply chainMergeSync in H8. exfalso;apply H6. 
  exists x2.   auto.
  apply chainMergeSync' in H8. exfalso;apply H6. 
  destruct H8. destruct H8.
  exists x3;exists x0;auto. 
  inversion H7;subst. exfalso;apply H5. 
  exists x1.  exists e;auto. auto.
  apply chainMergeSync' in H7. exfalso;apply H5. 
  destruct H7. destruct H7.
  exists x4;exists x3;auto.
  
  
Qed.   

Lemma chainMerge2Fuel: forall M (conf conf': configuration M) e,
    chainMerge conf conf' e ->
    (exists n, chainMergeWithFuel conf conf' n).
Proof.
  intros.
  induction H.
  exists (S O).
  Print chainMergeWithFuel.
  apply basic_one with (e:=event);auto.
  destruct IHchainMerge.
  Print chainMergeWithFuel.  
  exists (S x).
  apply inductive_multi with (e:=event2) (conf':=conf');auto.
Qed.   
  
  
Lemma deterministicMacroStepChainMerge': 
   forall  M (conf conf' conf'': configuration M) e,   WellFormed M ->
                                                       deter_prop M -> chainMerge conf conf' e -> chainMerge conf conf'' e -> finalConfig conf' -> finalConfig conf'' -> equivConf conf' conf''.
Proof.
  intros.
  assert (initialConfig conf).
  apply chainMergeInitial in H1;auto.   
  pose proof deterministicMacroStep.
  apply chainMerge2Fuel in H1. apply chainMerge2Fuel in H2.
  destruct H1. destruct H2. 
  apply H6 with (conf:=conf) (m:=x) (n:=x0);auto.
Qed.



Lemma deterministicMacroStepChainMerge: 
   forall  M (conf conf' conf'': configuration M) e,   WellFormed M ->
                                                       chainMerge conf conf' e -> chainMerge conf conf'' e -> finalConfig conf' -> finalConfig conf'' -> equivConf conf' conf''.
Proof.
  intros.
  assert (initialConfig conf).
  apply chainMergeInitial in H1;auto.   
  pose proof deterministicMacroStep.
  apply chainMerge2Fuel in H0. apply chainMerge2Fuel in H1.
  destruct H0. destruct H1. 
  apply H5 with (conf:=conf) (m:=x) (n:=x0);auto.
  apply deter_prop_final_impl;auto.
  destruct H;intuition;auto.
  destruct H.
  repeat(split;intuition).   
Qed.
   
(*proofs for wellformedness*)
(*proof of termination*)


Require Import Coq.Sets.Ensembles.
Require Import  Coq.omega.Omega.
Require Import Coq.Lists.List.


Require Coq.Bool.Bool.
Require Coq.Lists.ListDec.

Require Import Coq.Strings.String.

Require Export smedlDef.SmedlAST_submission.
Require Export smedlDef.semantic_rules.
Require Export wellFormScenario.
Require Export smedlDef.smedl_common_lemmas.
Require Import Coq.Sorting.Permutation.


Print initialConfig.
Print chainMerge.

Print stuckConfig. 


Lemma monitorObjNoChangeConstruct: forall M (conf conf' : configuration M) sce e,
    Result conf' = constructConfig sce e conf ->
    M = M.
Proof. reflexivity. Qed.

Lemma constructProp: forall M (conf conf' : configuration M) re sce,
    Result conf' = constructConfig sce re conf ->
    (forall sce st e0 s0,  In st (sceStateRelation sce) -> In (st, e0, Some s0) (stateEvStepMap M) -> (In s0 (traces sce) /\  (pre_state s0 = st)))
                             ->
    (forall sce st e0 s0,  In st (sceStateRelation sce) -> In (st, e0, Some s0) (stateEvStepMap M) -> (In s0 (traces sce) /\  (pre_state s0 = st)))
                             .
Proof.
  intros.
  eapply H0; eauto.
Qed.

(*In st (sceStateRelation sce0) -> In (st,ei,Some stp) (stateEvStepMap mon) ->
    In stp (traces scenario)*)

(*if a state s is in a scenario and step stp has s as pre step, then stp is in the scenario*)                             

Lemma sceStateRelationIn: forall lst s,
    In s lst ->
    In (pro_state s) (collectStates lst). 
Proof.
  intro lst;induction lst.
  - intros. inversion H. 
  - intros. inversion H. subst.
    destruct H.
    simpl. destruct (string_dec (pro_state s) (pre_state s)).
    left;auto.
    right. simpl. left;auto.
    simpl.
    destruct (string_dec (pro_state s) (pre_state s)).
    left;auto.
    right. simpl. left;auto.
    simpl.
    destruct (string_dec (pro_state a) (pre_state a)).
    
    assert (s=a \/ s <> a).
    apply excluded_middle. destruct H1. subst. 
    simpl. left;auto. simpl. 
    assert (pre_state a = pro_state s \/ pre_state a <> pro_state s). 
    apply excluded_middle. destruct H2. left;auto.
    right.
    apply filterIn. apply IHlst;auto.
    unfold mergeList'.
    unfold not. intros.
    apply H2. apply in_app_iff in H3.
    destruct H3. destruct H3;auto. inversion H3.
    apply filterL2 in H3. destruct H3;inversion H3. auto.

     assert (s=a \/ s <> a).
    apply excluded_middle. destruct H1. subst. 
    simpl. right.  left;auto. 
    assert (pre_state a = pro_state s \/ pre_state a <> pro_state s). 
    apply excluded_middle. destruct H2. left;auto.
    right.  apply in_app_iff. 
    assert (pro_state s = pro_state a \/ pro_state s <> pro_state a).
     apply excluded_middle. destruct H3. left;auto. left;auto. right. 
    apply filterIn. apply IHlst;auto.
    unfold mergeList'.
    unfold not. intros.
    apply in_app_iff in H4.
    destruct H4. apply H2. destruct H4;auto. inversion H4.
    apply filterL2 in H4. apply H3. destruct H4;auto. inversion H4.
Qed.

Definition stepInScenario (mon: object) : Prop :=
    forall sce s stp ei , In sce (scenarios mon) -> In s (sceStateRelation sce) -> In (s,ei,Some stp) (stateEvStepMap mon) -> In stp (traces sce).                          

Lemma updateCSIn: forall cs s1 s2 sce,
    uniqList (dom cs) ->
    In (sce, s1) (updateScenarioState' sce s2 cs) ->
    s1 = s2.
Proof. 
  intro cs;induction cs.
  - intros. simpl in H0;inversion H0.
  - intros.
    inversion H;subst.
    destruct a. simpl in *.
    destruct (string_dec (scenarioId s) (scenarioId sce)).
    inversion H0. subst.
    inversion H1;subst. auto.
    apply IHcs with (sce:=sce);auto.
    inversion H0;subst.
    inversion H1;subst. contradiction.
    apply IHcs with (sce:=sce);auto. 
Qed.



Lemma updateCSNoChange: forall cs sce sce' st s ,
    In (sce', st) (updateScenarioState' sce s cs) ->
    sce <> sce' ->
    In (sce', st) cs. 
Proof.
  intro cs;induction cs. 
  -  intros. simpl in H. inversion H.
  -  intros. simpl. simpl in H. destruct a;subst.
     destruct (string_dec (scenarioId s0) (scenarioId sce)).
     destruct H. inversion H;subst.
     SearchAbout scenarioId.
     apply ScenarioEquivalence in e. symmetry in e. contradiction.
     right. apply IHcs with (sce:=sce) (s:=s);auto.
     destruct H. inversion H;subst. left;auto.
     right.  apply IHcs with (sce:=sce) (s:=s);auto.
Qed.

Lemma constructConfigSceNoChange: forall M (conf conf' : configuration M) re sce sce' st,
    Result conf' = constructConfig sce re conf ->
    sce <> sce' ->
    In (sce', st) (controlstate conf') ->
    In (sce', st) (controlstate conf).
Proof.
  intros.
  unfold constructConfig in H.
   remember (getScenarioState sce (controlstate conf)).
   destruct o;inversion H.
  remember (transEvMapFunc (stateEvDefInstanceMap M) (Some s, Some (eventDefinition re))). 
  destruct o;inversion H. 
  remember (findEventInstance re (datastate conf)
                              l).
  destruct o;inversion H.
  remember (createValueEnv (eventArgs e) (eventParams (eventDefinition re))
                           (eventArguments re)).
  destruct e0;inversion H.
  remember ( getStep' conf sce e).
  destruct o;inversion H.
  remember (configTransition (extendValEnv (datastate conf) v) re e sce s0 conf ).
  destruct e0;inversion Heqe1.
  unfold configTransition in H8.
  remember ( execAction (extendValEnv (datastate conf) v, nil) (stepActions s0)
           (filter
              (fun e : event_definition =>
               match eventKind e with
               | Internal => true
               | Imported => false
               | Exported => true
               end) (events M))).
  destruct e0;inversion H8.
  destruct v1.  subst.  inversion H9. inversion H3.  rewrite H11 in H1. rewrite H10 in H1;simpl in H1. clear H10. clear H9. clear H8.  unfold updateControlState in H1.
  pose proof updateCSNoChange.
  apply H2 with (sce:=sce) (s:=(pro_state s0));auto. inversion H. 
Qed.

Print correctStateEvStepMap'.

(*Lemma constructProp': forall conf conf' re sce,
    uniqList (dom (controlstate conf)) ->
    
    Result conf' = constructConfig sce re conf ->
    In sce (dom (controlstate conf)) ->
    correctStateEvStepMap' M ->
    stpStMapEquiv' M ->
    stepInScenario M ->
    dom (controlstate conf) = (scenarios M) ->
    (forall sce st, In (sce,st) (controlstate conf) -> In st (sceStateRelation sce)) ->
    (forall sce st, In (sce,st) (controlstate conf') -> In st (sceStateRelation sce)).                             
Proof.
  intros.
    
  assert (M = (monitor_obj conf')).
  apply  monitorObjNoChangeConstruct with (sce:=sce) (e:=re);auto.
  assert (sce = sce0 \/ ~ sce = sce0).
  apply excluded_middle.
  destruct H9. subst.
  unfold constructConfig in H0.
  remember (getScenarioState sce0 (controlstate conf)).
  destruct o;inversion H0.
  remember (findEventInstance re (datastate conf)
                              (transEvMap (Some s, Some (eventDefinition re)))).
  destruct o;inversion H0.
  remember (createValueEnv (eventArgs e) (eventParams (eventDefinition re))
                           (eventArguments re)).
  destruct e0;inversion H0.
  remember ( getStep' conf sce0 e).
  destruct o;inversion H0.
  remember (configTransition (extendValEnv (datastate conf) v) re e sce0 s0 conf ).
  destruct e0;inversion Heqe1.
  unfold configTransition in H14.
  remember ( execAction (extendValEnv (datastate conf) v, nil) (stepActions s0)
           (filter
              (fun e : event_definition =>
               match eventKind e with
               | Internal => true
               | Imported => false
               | Exported => true
               end) (events M))).
  destruct e0;inversion H14.
  destruct v1.  subst.  inversion H15. inversion H0.  rewrite H17 in H7. rewrite H16 in H7;simpl in H7. clear H15. clear H14. clear H16. subst. 
  
  unfold updateControlState in H7.
  unfold correctStateEvStepMap' in H2.
  unfold stpStMapEquiv' in H3.
  apply getStepMap' with (s:=s) in Heqo1;auto. symmetry in Heqo1. 
  rewrite <- H3 in Heqo1. remember Heqo1. clear Heqi. 
  apply H2 in Heqo1.
  destruct Heqo1.
  apply inControlState in Heqo;auto. apply H6 in Heqo.
  unfold stepInScenario in H4.
  assert (In s0 (traces sce0)).
  apply H4 with (s:=s) (ei:=e);auto.
  rewrite <- H5;auto.
  assert (st=(pro_state s0)).
  apply updateCSIn with (cs:=(controlstate conf)) (sce:=sce0);auto.
  rewrite H16. 
  unfold sceStateRelation.
  pose proof sceStateRelationIn.
  apply H17. unfold getTransitionsOfScenario. auto. inversion H0.
  apply H6.
  pose proof constructConfigSceNoChange.
  apply H10 with (conf':=conf') (re:=re) (sce:=sce);auto. 
Qed.
 *)

(*Lemma constructPropSync: forall conf conf' re,
    uniqList (dom (controlstate conf)) ->  
    synchrony conf conf' re ->
    correctStateEvStepMap M ->
    stpStMapEquiv M ->
    stepInScenario M ->
    dom (controlstate conf) = (scenarios M) ->
    (forall sce st, In (sce,st) (controlstate conf) -> In st (sceStateRelation sce)) ->
    (forall sce st, In (sce,st) (controlstate conf') -> In st (sceStateRelation sce)).                             
Proof.
  intros.
  unfold synchrony in H0.
  destruct H0.
  unfold combineFunc in H7.
  remember (constructConfigList (dom (controlstate conf)) re conf).
  destruct e;inversion H7. clear H9.
  destruct v;inversion H7. clear H7.
  remember (innerCombineFunc'''' conf v).
  destruct o;inversion H9.
  remember ( mergeConfigFunc' conf c0 c ).
  destruct e;inversion H9.
  unfold removeEventFromConf in H10.
  rewrite <- H10 in H6;simpl in H6.
  unfold constructConfigList in Heqe.
  unfold mergeConfigFunc' in Heqe0.
  remember (mergeDataStateFunc (datastate conf) (datastate c0) (datastate c)).
  destruct e;inversion Heqe0. clear H11.
  remember (mergeControlStateFunc (controlstate conf) (controlstate c0) (controlstate c)). destruct e;inversion Heqe0. rewrite H11 in H6;simpl in H6.
  Print mergeControlStateFunc.
  assert (In sce ((filter
              (fun x : scenario =>
               inList event_definition_dec (eventDefinition re) (alphabet x))
              (filterList (finishedscenarios conf) (dom (controlstate conf))
                 scenario_dec))) \/ ~ (In sce ((filter
              (fun x : scenario =>
               inList event_definition_dec (eventDefinition re) (alphabet x))
              (filterList (finishedscenarios conf) (dom (controlstate conf))
                          scenario_dec))))).
  apply excluded_middle.
  destruct H7.
  
Admitted.  
    (*how to decide step s0 is a transition in sce0*)
  (*how to use getTransitionsOfScenario*)
  (*In (st,ei,Some stp) (stateEvStepMap mon)*)
  (*stpStMap (st, ei) = Some s0)*)
  (*Definition correctStateEvStepMap (mon:object) := 
  (forall st ei stp, In (st,ei,Some stp) (stateEvStepMap mon) ->
                     (stepEvent stp = ei) /\ (pre_state stp = st))*)
  (*In s (sceStateRelation sce0) -> exists stp, ...*)
  (*In st (sceStateRelation sce0) -> In (st,ei,Some stp) (stateEvStepMap mon) ->
    In stp (traces scenario)*)
*)

     Print correct_configuration.                              
                             
Definition syncProgress `(conf: configuration M) : Prop :=
  forall re, In re (raisedevents conf) -> (filter
         (fun x0 : scenario => inList event_definition_dec (eventDefinition re) (alphabet x0))
         (filterList (finishedscenarios conf) (dom (controlstate conf)) scenario_dec)) <> nil.

Definition syncProgress' `(conf: configuration M) : Prop :=
  (raisedevents conf) <> nil /\ forall re, In re (raisedevents conf) -> (filter
         (fun x0 : scenario => inList event_definition_dec (eventDefinition re) (alphabet x0))
         (filterList (finishedscenarios conf) (dom (controlstate conf)) scenario_dec)) <> nil.

Lemma syncPro: forall `(conf: configuration M),
    syncProgress' conf -> syncProgress conf.
Proof.
  intros.
  unfold syncProgress;unfold syncProgress' in H.
  intros.
  destruct H.
  apply H1 in H0;auto.   
Qed.


Definition finalConfig' `(conf:configuration M):Prop:=
(List.length (raisedevents conf) = O).


Fixpoint transitionIntoBasicActionList (act:action) : list action :=
  match act with
  | Skip => Skip :: nil
  | StateUpdate a e => (StateUpdate a e) :: nil
  | RaiseStmt s elist => (RaiseStmt s elist) :: nil
  | Seq act1 act2 => app (transitionIntoBasicActionList act1) (transitionIntoBasicActionList act2)
 end.                         
  
Inductive staticEventLeadTo (mon: object) : event_definition -> event_definition -> Prop :=
| staticLeadBasicCase : forall ev1 ev2,
    (exists (sce:scenario), In sce (scenarios mon) /\                
                (exists tr act exprs, In tr (getTransitionsOfScenario sce) /\ In act (transitionIntoBasicActionList (stepActions tr)) /\ act = RaiseStmt (eventId ev2) exprs /\  ev1 = (event (stepEvent tr))))
                -> staticEventLeadTo mon ev1 ev2
| staticLeadTransit : forall ev1 ev2 ev3, staticEventLeadTo mon ev1 ev2 -> staticEventLeadTo mon ev2  ev3 -> staticEventLeadTo mon ev1 ev3.

Print event_definition.
Print EventKind.

SearchAbout events.
Print events. 
  
Definition noMultAlphabet' (mon : object) : Prop :=
  forall e e1 e2, In e (events mon) -> staticEventLeadTo mon e e1 -> staticEventLeadTo mon e e2 -> e1 <> e2 -> ~ (exists sce, In sce (scenarios mon) /\ In e1 (alphabet sce) /\ In e2 (alphabet sce)).
(*get e1 and e2 based on mon and e, then if e1 <> e2, then forall sce, e1 and e2 cannot both exist in sce*)


Definition importedNoCommonAlphabet (mon : object) : Prop :=
  forall e1 e2 , In e1 (events mon) -> eventKind e1 = Imported -> e1 <> e2 ->  ~ (exists sce, In sce (scenarios mon) /\ In e1 (alphabet sce) /\ In e2 (alphabet sce)) .

Definition importedNoCommonAlphabet' (mon : object) : Prop :=
  forall e1 e2 , In e1 (events mon) -> eventKind e1 = Imported -> staticEventLeadTo mon e1 e2 -> e1 <> e2 ->  ~ (exists sce, In sce (scenarios mon) /\ In e1 (alphabet sce) /\ In e2 (alphabet sce)) .

Definition noMultAlphabet (mon : object) : Prop :=
  noMultAlphabet' mon /\ importedNoCommonAlphabet' mon.

Definition retrieveAction (stps: list step) : list action :=
  fold_right (fun stp lst => app (transitionIntoBasicActionList (stepActions stp)) lst) nil stps.

Definition filterStateUpdate (act: action) (v: atom) : bool :=
   match act with
  | StateUpdate (LExp a) e => if atom_eq_dec a v then true else false
  | _ => false
 end.
  
Fixpoint scenarioUpdateVar (sceList : list scenario) (a: atom) : list scenario :=
  match sceList with
  | nil => nil
  | sce::lst' => let stps := getTransitionsOfScenario sce in
                 let acts := filter (fun act => filterStateUpdate act a) (retrieveAction stps) in
                 match acts with
                 | _ :: _ => sce :: (scenarioUpdateVar lst' a)
                 | _ => (scenarioUpdateVar lst' a)                
                 end
  end.

Print step.
Print event_instance.
Print expr.


Fixpoint filterStateUsedExpr (ex: expr) (v: atom) : bool :=
  match ex with
  | EAtom a => if atom_eq_dec a v then true else false
  | EOr a b => orb (filterStateUsedExpr a v)  (filterStateUsedExpr b v)
  | EAnd a b =>  orb (filterStateUsedExpr a v)  (filterStateUsedExpr b v)
  | EEq a b => orb (filterStateUsedExpr a v)  (filterStateUsedExpr b v)
  | ELt a b => orb (filterStateUsedExpr a v)  (filterStateUsedExpr b v)
  | ELe a b => orb (filterStateUsedExpr a v)  (filterStateUsedExpr b v)                 
  | ENot a =>  (filterStateUsedExpr a v)
  | EPlus a b =>  orb (filterStateUsedExpr a v)  (filterStateUsedExpr b v)              
  | EMult a b  =>  orb (filterStateUsedExpr a v)  (filterStateUsedExpr b v)
  | EDiv a b =>  orb (filterStateUsedExpr a v)  (filterStateUsedExpr b v)
  | EMod a b =>  orb (filterStateUsedExpr a v)  (filterStateUsedExpr b v)                   
 end. 

Fixpoint filterStateUsedExprList list_ex v : bool :=
  match list_ex with
 | nil => false
 | ex::l' => if filterStateUsedExpr ex v then true else filterStateUsedExprList l' v
end.             
   
Fixpoint filterStateUsedAct (act: action) (v: atom) : bool :=
   match act with
  | StateUpdate _ e => filterStateUsedExpr e v
  | RaiseStmt _ le => filterStateUsedExprList le v
  | Seq a1 a2 => orb (filterStateUsedAct a1 v) (filterStateUsedAct a2 v)                                    
  | _ => false                                            
   end.

Print step. 
Print event_instance.

Fixpoint scenarioUsedVar (sceList : list scenario) (a: atom) : list scenario :=
  match sceList with
  | nil => nil
  | sce::lst' => let stps := getTransitionsOfScenario sce in
                 let acts := filter (fun stp => orb (filterStateUsedAct (stepActions stp) a) (filterStateUsedExpr (eventWhenExpr (stepEvent stp)) a)) stps in
                 match acts with
                 | _ :: _ => sce :: (scenarioUsedVar lst' a)
                 | _ => (scenarioUsedVar lst' a)                
                 end
  end.


Local Open Scope nat_scope. 
Definition noMergeError (mon : object) : Prop :=
  forall v, In v (dom (dsmon mon)) -> List.length (scenarioUpdateVar (scenarios mon) v) <= (S O).



SearchAbout In.




Definition noIntersection A (l1:list A) (l2: list A) : Prop :=
  (forall a, In a l1 -> ~ In a l2) /\
  (forall a, In a l2 -> ~ In a l1).                       


Lemma noIntersectionNoRefl: forall A (l: list A),
   l <> nil -> ~ noIntersection l l.
Proof. intros; induction l.  contradiction. 
       unfold not. intros.
       unfold noIntersection in H0.
       destruct H0.
       destruct H0 with (a0:=a);auto. left;auto. left;auto. 
Qed.

Lemma noIntersectionNoRefl_rev: forall A (l: list A),
    noIntersection l l -> l = nil.
Proof.
  intros;induction l.
  auto. unfold noIntersection in H.   destruct H.
  destruct H with (a0:=a). left;auto. left;auto. 
Qed.

               
Definition noMergeError' (mon : object) : Prop :=
  forall v, In v (dom (dsmon mon)) -> (List.length (scenarioUpdateVar (scenarios mon) v) <= (S O) 
                                       \/ (forall sce1 sce2, In sce1 (scenarioUpdateVar (scenarios mon) v) -> In sce2 (scenarioUpdateVar (scenarios mon) v) -> sce1 <> sce2 -> noIntersection (alphabet sce1) (alphabet sce2))).



Lemma alphabetNoIntersectionNotIn: forall scs sce1 sce2 e,
   noIntersection (alphabet sce1) (alphabet sce2) -> 
  ~ (In sce1 (filter (fun x => inList (event_definition_dec) e (alphabet x)) scs) /\
     In sce2 (filter (fun x => inList (event_definition_dec) e (alphabet x)) scs)). 
Proof.
  intros.
  assert (In sce1 scs \/ ~ In sce1 scs).
  apply excluded_middle.
  destruct H0.
  Focus 2.
  unfold not. intros.
  destruct H1.
  SearchAbout filter. apply filter_In in H1. destruct H1. contradiction.
  assert (In sce2 scs \/ ~ In sce2 scs).
  apply excluded_middle.
  destruct H1.
  Focus 2.
  unfold not. intros.
  destruct H2. apply filter_In in H3. destruct H3. contradiction.
  generalize dependent sce1.  generalize dependent sce2.  generalize dependent e. 
  induction scs.
-  intros. inversion H1. 
- intros. unfold not. intros. destruct H2.
   apply filter_In in H2. destruct H2.
  apply filter_In in H3. destruct H3.
   apply reverseinListLemma in H4.
   apply reverseinListLemma in H5. unfold noIntersection in H.
   destruct H.   apply H in H4. contradiction.
Qed. 

Definition filterRaiseStmt (act: action) (s: string) : bool :=
   match act with
   | RaiseStmt s' e => if string_dec s s' then
                         true
                       else
                         false
  | _ => false
   end.

Fixpoint scenarioRaise (sceList : list scenario) (v: event_definition) : list scenario :=
  match sceList with
  | nil => nil
  | sce::lst' => let stps := getTransitionsOfScenario sce in
                 let acts := filter (fun act => filterRaiseStmt act (eventId v)) (retrieveAction stps) in
                 match acts with
                 | _ :: _ => sce :: (scenarioRaise lst' v)
                 | _ => (scenarioRaise lst' v)                
                 end
  end.  




Definition noDupRaise (mon : object) : Prop :=
  forall v, In v (events mon) -> (List.length (scenarioRaise (scenarios mon) (v)) <=1) /\
                                 (forall sce stp acts, In sce (scenarios mon) -> In stp (getTransitionsOfScenario sce) -> acts = filter (fun act => filterRaiseStmt act (eventId v)) (transitionIntoBasicActionList (stepActions stp)) -> List.length acts <= 1).

Print event_definition.
SearchAbout EventKind. 

Definition noDupRaise' (mon : object) : Prop :=
  forall v, In v (events mon) ->  ( (eventKind v = Internal \/ eventKind v = Imported) -> (List.length (scenarioRaise (scenarios mon) (v)) <=1)) /\
                                 (forall sce stp acts, In sce (scenarios mon) -> In stp (getTransitionsOfScenario sce) -> acts = filter (fun act => filterRaiseStmt act (eventId v)) (transitionIntoBasicActionList (stepActions stp)) -> List.length acts <= 1).


Inductive triggerSce (mon: object) : event_definition -> scenario  -> Prop :=
| basic_ts: forall e sce, In sce (scenarios mon) -> In e (alphabet sce) -> triggerSce mon e sce 
| induction_ts: forall e1 e2 sce, staticEventLeadTo mon e1 e2 -> triggerSce mon e2 sce  -> triggerSce mon e1 sce
.

Definition noDupRaise'' (mon : object) : Prop :=
  forall v, In v (events mon) ->  
((eventKind v = Internal) -> (forall sce1 sce2, In sce1 (scenarioRaise (scenarios mon) (v)) ->
In sce2 (scenarioRaise (scenarios mon) (v)) -> sce1 <> sce2 -> (~ exists e, In e (events mon) /\ triggerSce mon e sce1 /\ triggerSce mon e sce2))) /\
                                 (forall sce stp acts, In sce (scenarios mon) -> In stp (getTransitionsOfScenario sce) -> acts = filter (fun act => filterRaiseStmt act (eventId v)) (transitionIntoBasicActionList (stepActions stp)) -> List.length acts <= 1).

  

(*ConfigOfMon_refl*)

Definition basicPrecondition {M} (conf : configuration M) re: Prop :=
  correct_configuration conf
    /\ typeCheck M
    /\ In re (raisedevents conf)
    /\ stateEvDefInstanceMapEquiv M
    /\ transEvMapProp M
    /\ transEvMapEventInstanceProp M
    /\ stpStMapEquiv' M
    /\ (forall sce, In sce (scenarios M) -> stepExistsMon' M sce)
    /\ correctStateEvStepMap' M
    /\ stateEvDefInstanceMapEquivEListProp M
    /\ alphabetScenario'' M
    /\ stateSceProp M
    /\ stateSceIn M.

Print chainMerge.




Lemma constructList'NotNil: forall scs M (conf : configuration M) re,
    correct_configuration conf ->
    basicPrecondition conf re ->
    scs <> nil ->
    incl scs (dom (controlstate conf)) ->
    (forall sce, In sce scs -> (~ In sce (finishedscenarios conf)) /\
    In (eventDefinition re) (alphabet sce)) ->             
    (exists lst, Result lst = constructConfigList' scs re conf /\ lst <> nil).

Proof.
  intro scs;induction scs;intros;(try contradiction). 
  simpl.
  
  pose proof staticConstructNoError''.
  assert (exists conf' : configuration M, constructConfig a re conf = Result conf').
  unfold basicPrecondition in H0.
  repeat match goal with
            | [ H: _ /\ _ |- _ ] => destruct H

                 end.
 apply H4;auto.   
 unfold incl in H2.
 apply H2 with (a0:=a);left;auto.
 apply H11. destruct H.
 rewrite <- cs_consist.
 unfold incl in H2. apply H2. left;auto.
 destruct H3 with (sce:=a). left;auto. auto. 
  destruct H3 with (sce:=a). left;auto. auto. 
  
 destruct H5.
 rewrite H5.
 assert (scs = nil \/ scs <> nil).
 apply excluded_middle.
 destruct H6.
 rewrite H6. simpl. exists (x::nil).
 split;auto.
 unfold not. intros. inversion H7.
 
 
 assert (exists lst : list (configuration M),
            Result lst = constructConfigList' scs re conf /\ lst <> nil).
 apply IHscs;auto.
 unfold incl. intros.
 unfold incl in H2.
 apply H2;auto. right;auto.
 intros. apply H3;auto. right;auto.
 destruct H7. destruct H7.
 rewrite <- H7.
 exists (x::x0). split;auto. unfold not. intros. inversion H9.
 Qed. 
 
Lemma constructListNoErr: forall M (conf : configuration M) re,
    correct_configuration conf ->
    syncProgress conf ->
    basicPrecondition conf re ->
    (exists lst, Result lst = constructConfigList (dom (controlstate conf)) re conf /\ lst <> nil).
Proof.
  intros.
  pose proof constructList'NotNil. 
  unfold  constructConfigList.
  apply H2;auto.
  
  unfold syncProgress in H0.
  apply H0;auto. unfold basicPrecondition in H1.
            repeat match goal with
            | [ H: _ /\ _ |- _ ] => destruct H

                   end.
            auto.
            unfold incl. intros.
            SearchAbout filter.
            rewrite filter_In in H3.
            destruct H3.
            SearchAbout filterList.
  apply filterL2 in H3;auto.  intros.  rewrite filter_In in H3.          
  destruct H3.
  apply filterL1 in H3;auto. split;auto.
  SearchAbout inList.
  apply reverseinListLemma in H4;auto. 
Qed.

Check getValue. 

Lemma mergeDSCorrect: forall (ds:value_env) ds1 ds2,
    uniqList (dom ds) ->
    dom2 ds = dom2 ds1 ->
    dom2 ds = dom2 ds2 ->
    (forall a, In a (dom ds) -> (exists s, AIdent s = a)) ->
    (forall s v v1 v2, In (AIdent s) (dom ds) -> Some v = getValue (AIdent s) ds ->
    Some v1 = getValue (AIdent s) ds1 -> Some v2 = getValue (AIdent s) ds2 -> v <> v1 -> v <> v2 -> v1 = v2) ->
    (exists (ds':value_env), Result ds' = mergeDataStateFunc ds ds1 ds2).  
Proof. intro ds;induction ds. 
       - intros. destruct ds1. destruct ds2. simpl. exists nil;auto.
         inversion H1. inversion H0.
       - intros. destruct ds1;inversion H0. destruct ds2;inversion H1.
         destruct a;destruct p;subst. simpl in *;subst. destruct p1;destruct p;subst.
         simpl in H6;subst. destruct p0;subst. simpl.
         simpl in *;subst. destruct p;simpl in *;subst. 
         destruct (atom_eq_dec a a). Focus 2.  contradiction.
         destruct (typ_eq_dec t t). Focus 2. contradiction.
         remember (mergeDataStateFunc ds ds1 ds2).
         destruct e1. subst. Focus 2.
        assert (exists ds' : value_env, Result ds' = mergeDataStateFunc ds ds1 ds2).  
        apply IHds;auto. inversion H;auto. intros. apply H3 with (s:=s0) (v:=v);auto.
        inversion H;subst. destruct (atom_eq_dec (AIdent s0) a). subst.
        contradiction. auto.
        destruct (atom_eq_dec (AIdent s0) a). subst. inversion H;subst. contradiction.
        auto.  destruct (atom_eq_dec (AIdent s0) a). subst. inversion H;subst. contradiction.
        auto. destruct H4. rewrite <- H4 in Heqe1;inversion Heqe1.
        destruct (range_typ_dec r0 r1);auto. exists ((a, (t, r0)) :: v);auto.
        destruct (range_typ_dec r0 r);auto. exists (((a, (t, r1)) :: v));auto.
        destruct (range_typ_dec r1 r).  exists ((a, (t, r0)) :: v);auto.
         assert (exists s : string,  AIdent s = a).
        apply H2. left;auto. destruct H4. assert (r0 = r1).  apply H3 with (s:=x) (v:=r);auto.
        destruct (atom_eq_dec (AIdent x) a);auto. rewrite H4 in n2. contradiction.
        destruct (atom_eq_dec (AIdent x) a);auto. rewrite H4 in n2. contradiction.
        destruct (atom_eq_dec (AIdent x) a);auto. rewrite H4 in n2. contradiction.
        contradiction. 
Qed.

Lemma mergeDSCorrect': forall (ds:value_env) ds1 ds2,
    uniqList (dom ds) ->
    dom2 ds = dom2 ds1 ->
    dom2 ds = dom2 ds2 ->
    (forall a, In a (dom ds) -> (exists s, AIdent s = a)) ->
    (forall s v v1 v2, In (AIdent s) (dom ds) -> Some v = getValue (AIdent s) ds ->
    Some v1 = getValue (AIdent s) ds1 -> Some v2 = getValue (AIdent s) ds2 -> v = v1 \/ v = v2) ->
    (exists (ds':value_env), Result ds' = mergeDataStateFunc ds ds1 ds2).  
Proof. intro ds;induction ds. 
       - intros. destruct ds1. destruct ds2. simpl. exists nil;auto.
         inversion H1. inversion H0.
       - intros. destruct ds1;inversion H0. destruct ds2;inversion H1.
         destruct a;destruct p;subst. simpl in *;subst. destruct p1;destruct p;subst.
         simpl in H6;subst. destruct p0;subst. simpl.
         simpl in *;subst. destruct p;simpl in *;subst. 
         destruct (atom_eq_dec a a). Focus 2.  contradiction.
         destruct (typ_eq_dec t t). Focus 2. contradiction.
         remember (mergeDataStateFunc ds ds1 ds2).
         destruct e1. subst. Focus 2.
        assert (exists ds' : value_env, Result ds' = mergeDataStateFunc ds ds1 ds2).  
        apply IHds;auto. inversion H;auto. intros. apply H3 with (s:=s0) (v:=v);auto.
        inversion H;subst. destruct (atom_eq_dec (AIdent s0) a). subst.
        contradiction. auto.
        destruct (atom_eq_dec (AIdent s0) a). rewrite e1 in H4. inversion H. subst. contradiction. 
        auto.  destruct (atom_eq_dec (AIdent s0) a). subst. inversion H;subst. contradiction.
        auto. destruct H4. rewrite <- H4 in Heqe1;inversion Heqe1.
        destruct (range_typ_dec r0 r1);auto. exists ((a, (t, r0)) :: v);auto.
        destruct (range_typ_dec r0 r);auto. exists (((a, (t, r1)) :: v));auto.
        destruct (range_typ_dec r1 r).  exists ((a, (t, r0)) :: v);auto.
         assert (exists s : string,  AIdent s = a).
        apply H2. left;auto. destruct H4. destruct H3 with (s:=x) (v:=r) (v1:=r0) (v2:=r1);auto.  
        destruct (atom_eq_dec (AIdent x) a);auto. contradiction. 
        destruct (atom_eq_dec (AIdent x) a);auto. contradiction.
        destruct (atom_eq_dec (AIdent x) a);auto.  contradiction.
        rewrite H5 in n0. contradiction. rewrite H5 in n1. contradiction. 
Qed.



Lemma mergeCSCorrect: forall (cs:scenario_env) cs1 cs2,
    uniqList (dom cs) ->
    dom cs = dom cs1 ->
    dom cs = dom cs2 ->
    (forall sce v v1 v2, In sce (dom cs) -> In (sce,v) cs ->
    In (sce,v1) cs1 -> In (sce,v2) cs2 -> v <> v1 -> v <> v2 -> v1 = v2) ->
    (exists (cs':scenario_env), Result cs' = mergeControlStateFunc cs cs1 cs2).  
Proof. intro cs;induction cs. 
       - intros. destruct cs1. destruct cs2. simpl. exists nil;auto.
         inversion H1. inversion H0.
       - intros. destruct cs1;inversion H0. destruct cs2;inversion H1.
         destruct a;destruct p;subst. simpl in *;subst. destruct p0;subst.
         simpl. simpl in H2. 
         destruct (scenario_dec s s). Focus 2.  contradiction.
        
         remember (mergeControlStateFunc cs cs1 cs2).
         destruct e0. subst. Focus 2.
        assert (exists cs' : scenario_env, Result cs' = mergeControlStateFunc cs cs1 cs2).  
        apply IHcs;auto. inversion H;auto. intros. apply H2 with (sce:=sce) (v:=v) ;auto.
        destruct H3. 
        rewrite <- H3 in Heqe0;inversion Heqe0.  destruct (string_dec s2 s1). subst.  exists ((s, s1) :: v);auto.
 destruct (string_dec s2 s0);auto. exists (((s, s1) :: v));auto.
        destruct (string_dec s1 s0).  exists (((s, s2) :: v));auto.
          assert (s2 = s1).  apply H2 with (sce:=s) (v:=s0);auto.
       contradiction.
(* destruct (string_dec s2 s3). subst.  exists ((s, s3) :: v);auto.
        destruct (string_dec s2 s0);auto. exists (((s, s3) :: v));auto.
        destruct (string_dec s3 s0).  exists (((s, s2) :: v));auto.
          assert (s2 = s3).  apply H2 with (sce:=s) (v:=s0);auto.
       contradiction. *)
Qed.

Lemma mergeCSCorrect': forall (cs:scenario_env) cs1 cs2,
    uniqList (dom cs) ->
    dom cs = dom cs1 ->
    dom cs = dom cs2 ->
    (forall sce v v1 v2, In sce (dom cs) -> In (sce,v) cs ->
    In (sce,v1) cs1 -> In (sce,v2) cs2 -> v = v1 \/ v = v2) ->
    (exists (cs':scenario_env), Result cs' = mergeControlStateFunc cs cs1 cs2).  
Proof. intro cs;induction cs. 
       - intros. destruct cs1. destruct cs2. simpl. exists nil;auto.
         inversion H1. inversion H0.
       - intros. destruct cs1;inversion H0. destruct cs2;inversion H1.
         destruct a;destruct p;subst. simpl in *;subst. destruct p0;subst.
         simpl. simpl in H2. 
         destruct (scenario_dec s s). Focus 2.  contradiction.
        
         remember (mergeControlStateFunc cs cs1 cs2).
         destruct e0. subst. Focus 2.
        assert (exists cs' : scenario_env, Result cs' = mergeControlStateFunc cs cs1 cs2).  
        apply IHcs;auto. inversion H;auto. intros. apply H2 with (sce:=sce) (v:=v) ;auto.
        destruct H3. 
        rewrite <- H3 in Heqe0;inversion Heqe0.
        destruct (string_dec s2 s1). subst.  exists ((s, s1) :: v);auto.
        destruct (string_dec s2 s0);auto. exists (((s, s1) :: v));auto.
        destruct (string_dec s1 s0).  exists (((s, s2) :: v));auto.
        
        assert (s0 = s2 \/ s0 = s1).  apply H2 with (sce:=s) (v:=s0);auto.
        destruct H3. rewrite H3 in n0;contradiction. rewrite H3 in n1;contradiction. 
      (*  destruct (string_dec s2 s3). subst.  exists ((s, s3) :: v);auto.
        destruct (string_dec s2 s0);auto. exists (((s, s3) :: v));auto.
        destruct (string_dec s3 s0).  exists (((s, s2) :: v));auto.
        
        assert (s0 = s2 \/ s0 = s3).  apply H2 with (sce:=s) (v:=s0);auto.
        destruct H3. rewrite H3 in n0;contradiction. rewrite H3 in n1;contradiction. 
     *) 
Qed.

Print correct_configuration.


Lemma mergeConfigCorrect: forall M (conf conf1 conf2 : configuration M),
    correct_configuration conf ->
    dom (controlstate conf) = dom (controlstate conf1) ->
    dom (controlstate conf) = dom (controlstate conf2) ->
    dom2 (datastate conf) = dom2 (datastate conf1) ->
    dom2 (datastate conf) = dom2 (datastate conf2) ->
    (forall s v v1 v2, In (AIdent s) (dom (datastate conf)) -> Some v = getValue (AIdent s) (datastate conf) ->   Some v1 = getValue (AIdent s) (datastate conf1) -> Some v2 = getValue (AIdent s) (datastate conf2) -> v <> v1 -> v <> v2 -> v1 = v2) ->
    (forall sce v v1 v2, In sce (dom (controlstate conf)) -> In (sce,v) (controlstate conf) ->
                         In (sce,v1) (controlstate conf1) -> In (sce,v2) (controlstate conf2) -> v <> v1 -> v <> v2 -> v1 = v2) ->
    exists conf', Result conf' = mergeConfigFunc conf conf1 conf2. 
Proof.
  intros. 
  pose proof  mergeDSCorrect.
  pose proof  mergeCSCorrect.
  unfold mergeConfigFunc.
  assert (exists ds' : value_env, Result ds' = mergeDataStateFunc (datastate conf) (datastate conf1) (datastate conf2)).
  apply H6;auto.
  destruct H.
  Print correct_object.
  destruct correct_mon.
  SearchAbout dom2.
  apply dom2dom in ds_dom_eq. rewrite  ds_dom_eq. auto.
  intros. destruct H. SearchAbout tyEnv. apply tyEnvVar with (env:=(datastate conf));auto.
  destruct H8. rewrite <- H8.
  assert (exists cs' : scenario_env, Result cs' =  mergeControlStateFunc (controlstate conf) (controlstate conf1) (controlstate conf2)).
  apply H7;auto.
  destruct H;auto. destruct H9. rewrite <- H9.
  exists ({|
      datastate := x;
      controlstate := x0;
      raisedevents := mergeList' (raisedevents conf1) (raisedevents conf2) raisedEvent_dec;
      exportedevents := mergeList' (exportedevents conf1) (exportedevents conf2)
                          raisedEvent_dec;
      finishedscenarios := finishedscenarios conf1 ++
                           finishedscenarios conf2 ++ finishedscenarios conf;
      sceEventMap := sceEventMap conf1 ++ sceEventMap conf2 ++ sceEventMap conf |});auto. 
Qed.


Lemma mergeConfigCorrect': forall M (conf conf1 conf2 : configuration M),
    correct_configuration conf ->
    dom (controlstate conf) = dom (controlstate conf1) ->
    dom (controlstate conf) = dom (controlstate conf2) ->
    dom2 (datastate conf) = dom2 (datastate conf1) ->
    dom2 (datastate conf) = dom2 (datastate conf2) ->
    (forall s v v1 v2, In (AIdent s) (dom (datastate conf)) -> Some v = getValue (AIdent s) (datastate conf) ->   Some v1 = getValue (AIdent s) (datastate conf1) -> Some v2 = getValue (AIdent s) (datastate conf2) -> v = v1 \/ v = v2) ->
    (forall sce v v1 v2, In sce (dom (controlstate conf)) -> In (sce,v) (controlstate conf) ->
                         In (sce,v1) (controlstate conf1) -> In (sce,v2) (controlstate conf2) -> v = v1 \/ v = v2) ->
    exists conf', Result conf' = mergeConfigFunc' conf conf1 conf2. 
Proof.
  intros. 
  pose proof  mergeDSCorrect'.
  pose proof  mergeCSCorrect'.
  unfold mergeConfigFunc'.
  assert (exists ds' : value_env, Result ds' = mergeDataStateFunc (datastate conf) (datastate conf1) (datastate conf2)).
  apply H6;auto.
  destruct H.
  Print correct_object.
  destruct correct_mon.
  SearchAbout dom2.
  apply dom2dom in ds_dom_eq. rewrite  ds_dom_eq. auto.
  intros. destruct H. SearchAbout tyEnv. apply tyEnvVar with (env:=(datastate conf));auto.
  destruct H8. rewrite <- H8.
  assert (exists cs' : scenario_env, Result cs' =  mergeControlStateFunc (controlstate conf) (controlstate conf1) (controlstate conf2)).
  apply H7;auto.
  destruct H;auto. destruct H9. rewrite <- H9.
  (*exists ({|
      monitor_obj := monitor_obj conf;
      datastate := x;
      controlstate := x0;
      raisedevents := mergeList' (raisedevents conf1) (raisedevents conf2) raisedEvent_dec;
      exportedevents := mergeList' (exportedevents conf1) (exportedevents conf2)
                          raisedEvent_dec;
      finishedscenarios := finishedscenarios conf1 ++
                           finishedscenarios conf2 ;
      sceEventMap := sceEventMap conf1 ++ sceEventMap conf2 |});auto. *)
  exists ({|
      datastate := x;
      controlstate := x0;
      raisedevents := raisedevents conf1 ++ raisedevents conf2;
      exportedevents := exportedevents conf1 ++ exportedevents conf2;
      finishedscenarios := finishedscenarios conf1 ++ finishedscenarios conf2;
      sceEventMap := sceEventMap conf1 ++ sceEventMap conf2 |});auto.
Qed. 

Print noMergeError'.


  
Lemma scenariosUpdateSingle: forall mon sce1 sce2 ,
    noMergeError mon ->
    sce1 <> sce2 ->
    (forall v, In v (dom (dsmon mon)) -> (In sce1 (scenarioUpdateVar (scenarios mon) v) /\ ~ In sce2 (scenarioUpdateVar (scenarios mon) v)) \/ (In sce2 (scenarioUpdateVar (scenarios mon) v) /\ ~ In sce1 (scenarioUpdateVar (scenarios mon) v)) \/ (~ In sce1 (scenarioUpdateVar (scenarios mon) v) /\ ~ In sce2 (scenarioUpdateVar (scenarios mon) v))).
Proof.
  intros. unfold noMergeError in H.
  
  apply H in H1.
  assert ((exists n, (scenarioUpdateVar (scenarios mon) v) = n::nil) \/ (scenarioUpdateVar (scenarios mon) v) = nil).
  destruct ((scenarioUpdateVar (scenarios mon) v)).  right;auto.
  simpl in H1. destruct l. left. exists s;auto. inversion H1. inversion H3.
  destruct H2.
  destruct H2.
  rewrite H2.
  assert (sce1 = x \/ sce1 <> x).
  apply excluded_middle. destruct H3. subst. left;auto.  split;auto. left;auto.
  unfold not. intros. destruct H3. contradiction. inversion H3.
  assert (sce2 = x \/ sce2 <> x). apply excluded_middle. destruct H4.
  right;left;auto. split;(try (left;auto||unfold not;intros)). unfold not. intros.
  destruct H5;inversion H5. symmetry in H5;contradiction.
  right;right. split;(unfold not;intros;destruct H5;inversion H5;symmetry in H5;contradiction).
  Print scenarioUpdateVar.
  rewrite H2. right;right.
   split;(unfold not;intros;destruct H3;inversion H3;symmetry in H3;contradiction).
Qed.

Lemma scenariosUpdateSingle': forall mon sce1 sce2 v,
    noMergeError' mon ->
    sce1 <> sce2 ->
    In v (dom (dsmon mon)) ->
    In sce1 (scenarioUpdateVar (scenarios mon) v) ->
    In sce2 (scenarioUpdateVar (scenarios mon) v) ->
    noIntersection (alphabet sce1) (alphabet sce2). 
Proof.
  intros.
  unfold noMergeError' in H.
  apply H in H1. destruct H1.
  Focus 2.  apply H1;auto.
  destruct ((scenarioUpdateVar (scenarios mon) v)).
  inversion H2. destruct l. destruct H2. destruct H3. subst. contradiction.
  inversion H3. inversion H2. inversion H1. inversion H5.
Qed.

Lemma scenariosUpdateSingle'': forall mon sce1 sce2 ,
    noMergeError' mon ->
    sce1 <> sce2 ->
    
    ~ (noIntersection (alphabet sce1) (alphabet sce2)) ->
    (forall v, In v (dom (dsmon mon)) -> (In sce1 (scenarioUpdateVar (scenarios mon) v) /\ ~ In sce2 (scenarioUpdateVar (scenarios mon) v)) \/ (In sce2 (scenarioUpdateVar (scenarios mon) v) /\ ~ In sce1 (scenarioUpdateVar (scenarios mon) v)) \/ (~ In sce1 (scenarioUpdateVar (scenarios mon) v) /\ ~ In sce2 (scenarioUpdateVar (scenarios mon) v))).
   
Proof.
  intros.
  assert (  
    ~ (In sce1 (scenarioUpdateVar (scenarios mon) v) /\
    In sce2 (scenarioUpdateVar (scenarios mon) v))). 
  unfold not. intros.
  destruct H3.
  apply scenariosUpdateSingle' with (sce1:=sce1) (sce2:=sce2) (v:=v) in H;auto.
  assert (In sce1 (scenarioUpdateVar (scenarios mon) v) \/ ~ (In sce1 (scenarioUpdateVar (scenarios mon) v))).
  apply excluded_middle.
  destruct H4.
  assert (In sce2 (scenarioUpdateVar (scenarios mon) v) \/ ~ (In sce2 (scenarioUpdateVar (scenarios mon) v))).
   apply excluded_middle.
  destruct H5.
  exfalso;apply H3;auto. left;auto.
  assert (In sce2 (scenarioUpdateVar (scenarios mon) v) \/ ~ (In sce2 (scenarioUpdateVar (scenarios mon) v))).
   apply excluded_middle.
   destruct H5.
  right;left;auto.  right;right;auto.   
Qed.


  
Lemma scenarioIn: forall env sce  s0,
    Some s0 = getScenarioState sce env ->
    In sce (dom env).
Proof.  
    intro env;induction env.    
    - intros. simpl in H. inversion H.
    - intros. simpl.
      simpl in H. destruct a.
      destruct (string_dec (scenarioId sce) (scenarioId s)).
      simpl. inversion H. SearchAbout scenarioId.
      rewrite ScenarioEquivalence in e. subst;left;auto.
      apply IHenv in H;auto. 
Qed.


Print retrieveAction. 

(*transitionIntoBasicActionList*)

Lemma valueNoChange: forall env env' s s' v ,
    Some env' = updateValueEnvInv (AIdent s) v env ->
    s <> s' ->
    getValue (AIdent s') env = getValue (AIdent s') env'.
Proof. intro env;induction env. 
       -  intros. simpl in H. inversion H;subst. auto.
       - intros. destruct env'. simpl in H.
         destruct a;destruct p.
         destruct ( atom_eq_dec (AIdent s) a);inversion H.
         destruct (typeValMatch t v);inversion H.
         destruct (updateValueEnvInv (AIdent s) v env);inversion H. 
         destruct a;destruct p.
         simpl in H.
         destruct p0.
         destruct p.
         destruct (atom_eq_dec (AIdent s) a).
         destruct (typeValMatch t v ).
         inversion H;subst.
         simpl. destruct ( atom_eq_dec (AIdent s') (AIdent s)).
         inversion e. exfalso;apply H0;auto. auto.
         inversion H.
         remember (updateValueEnvInv (AIdent s) v env).
         destruct o. inversion H;subst.
         simpl. 
         destruct (atom_eq_dec (AIdent s') a);auto.
         apply IHenv with (s:=s) (v:=v);auto.
         simpl.
         inversion H. 
Qed.

Lemma getValueNone: forall env s ,
    ~ In (AIdent s) (dom env) ->
    getValue (AIdent s) env = None.
Proof.
  intro env;induction env.
  - intros.
    simpl;auto.
  - intros.
    simpl. destruct a;destruct p.
    destruct (atom_eq_dec (AIdent s) a). subst.
    simpl in H. exfalso;apply H. left;auto.
    apply IHenv. unfold not. intros.
    apply H. simpl;right;auto. 
Qed.  


Lemma filterPlus: forall A l1 l2 f  ,
    @filter A f (l1++l2) = nil ->
    @filter A f l1 = nil. 
Proof.
  intros A l1. induction l1.
  - intros. simpl in H. auto.
  - intros. simpl in H.
    simpl.
    destruct (f a). inversion H.
    apply IHl1 with (l2:=l2);auto. 
Qed.

Lemma filterPlus': forall A l1 l2 f  ,
    @filter A f (l1++l2) = nil ->
    @filter A f l2 = nil. 
Proof.
  intros A l1. induction l1.
  - intros. auto. 
  - intros. simpl in H.
    simpl.
    destruct (f a). inversion H.
    apply IHl1 with (l2:=l2);auto. 
Qed.

Check fold_right.

Lemma filterPlus'': forall A B (l:list B)  f (g: B -> list A) (x:B),
    In x l ->
    @filter A f (fold_right (fun a lst2 => g a ++lst2) nil l) = nil ->
    @filter A f (g x) = nil. 
Proof.
  intros A B l. induction l.
  - intros. inversion H. 
  - intros. destruct H.
    + subst. simpl in H0.
      apply filterPlus with (l2:=fold_right (fun (a : B) (lst2 : list A) => g a ++ lst2) nil l);auto.
    +  simpl in *.
 apply filterPlus' with (l1:= g a) in H0;auto.
   
Qed.


Lemma varNoChangeExecuteAction: forall act env l env' l'  s eventList,
    filter (fun act : action => filterStateUpdate act (AIdent s)) (transitionIntoBasicActionList act) = nil ->
    Result (env', l') = execAction (env, l) act eventList ->
     getValue (AIdent s) env = getValue (AIdent s) env'.
Proof.
  intro act;induction act.
   - intros;simpl in *. inversion H0;auto. 
   - intros. simpl in H.
     destruct l.
     destruct (atom_eq_dec a (AIdent s)). 
     inversion H.
     simpl in H0.
     destruct a;inversion H0.
     remember (evalMonad env e).
     destruct e0;inversion H2.
     remember (updateValueEnvInv (AIdent s0) v env).
     destruct o;inversion H3. subst.
     SearchAbout getValue.
     assert (In (AIdent s) (dom env) \/ ~ In (AIdent s) (dom env)).
     apply excluded_middle. 
     destruct H1. apply valueNoChange with (s:=s0) (v:=v);auto.
     unfold not. intros. subst. contradiction.
     rewrite getValueNone;auto.
     SearchAbout updateValueEnvInv. assert (dom env = dom v0).
     apply updateEnvDomNoChange with (s:=s0) (v:=v);auto.
     rewrite H4 in H1.
     rewrite getValueNone;auto.
   -
     intros.
     simpl in H0.
     destruct (calculateExprList env exprs);inversion H0.
     destruct (getEventByName ident eventList);inversion H0.
     destruct (parameterMatchFunc v (eventParams e));inversion H0. 
     subst;auto.
   - intros.
     simpl in H0.
     remember (execAction (env, l) act1 eventList).
     destruct e;inversion H0.
     destruct v.
     apply IHact1 with (s:=s) in Heqe;auto.
     apply IHact2 with (s:=s) in H0;auto.
     rewrite H0 in Heqe;auto.
     simpl in H.
     SearchAbout filter.
     apply  filterPlus' with (l1:=(transitionIntoBasicActionList act1));auto.
     apply  filterPlus with (l2:=(transitionIntoBasicActionList act2));auto.
Qed.


Print getTransitionsOfScenario. 
  (* noMergeError M -> Result conf' = constructConfig sce1 re conf ->*)

(* noMergeError M -> conf => conf' -> conf => conf'' -> In var (dom (datastate conf)) -> In (var, (t,v1)) (datastate conf) -> In (var, (t,v2)) (datastate conf') -> In (var, (t,v3)) (datastate conf'') -> (v1 = v2 \/ v1 = v3)  *)

Lemma sceNotUpdateVar: forall lst sce stps  s,
    In sce lst ->
    ~ In sce (scenarioUpdateVar lst (AIdent s)) ->
    stps = getTransitionsOfScenario sce ->
    (forall stp, In stp stps ->  filter (fun act : action => filterStateUpdate act (AIdent s)) (transitionIntoBasicActionList (stepActions stp)) = nil). 
Proof. 
  intro lst;induction lst.
  - intros. inversion H.
  - intros. 
    simpl in H0.
    destruct H.
    + subst.
      remember ( filter (fun act : action => filterStateUpdate act (AIdent s))
                        (retrieveAction (getTransitionsOfScenario sce))).
      destruct l.
      unfold retrieveAction in Heql.
      pose proof filterPlus''. symmetry in Heql. apply H with (x:=stp) in Heql;auto.
      exfalso;apply H0. left;auto. 
    + remember ( filter (fun act : action => filterStateUpdate act (AIdent s))
                        (retrieveAction (getTransitionsOfScenario a))).
      destruct l.
      apply IHlst with (sce:=sce) (stps:=stps);auto.
      apply IHlst with (sce:=sce) (stps:=stps);auto.
      unfold not. intros. apply H0. right;auto. 
Qed.


Print updateDataState. 
Lemma updateDataStateDom : forall v x (env:value_env),
    uniqList (dom v) ->
    dom v = dom (env ++ x) ->
    dom env = dom (updateDataState v (dom env)). 
Proof.
  intro v;induction v.
  - intros.
    destruct env. auto. inversion H0.
  - intros. simpl.
    destruct a.
    remember (inList atom_eq_dec a (dom env)).
    destruct b. 
    simpl. simpl in H.
    
    destruct env. SearchAbout inList.
    symmetry in Heqb. apply reverseinListLemma in Heqb.
    inversion Heqb. simpl in H0.  destruct p0.
    simpl in *. inversion H;subst. f_equal. inversion H0;auto.
    inversion H0. subst.
    apply IHv in H5;auto.
    SearchAbout updateDataState.
    rewrite <- updateDSNotIn with (n:=a0);auto.
    symmetry in Heqb. SearchAbout inList.
    apply reverseinListFalse in Heqb.
    inversion H;subst.
    destruct env.
    SearchAbout updateDataState.
    rewrite updateDSNil. auto.
    inversion H0. destruct p0. simpl in *;auto.
    exfalso;apply Heqb;left;auto. 
Qed.

Lemma updateDataStateDom2 : forall v x (env:value_env),
    uniqList (dom v) ->
    dom2 v = dom2 (env ++ x) ->
    dom2 env = dom2 (updateDataState v (dom env)). 
Proof.
  intro v;induction v.
  - intros.
    destruct env. auto. inversion H0.
  - intros. simpl.
    destruct a.
    remember (inList atom_eq_dec a (dom env)).
    destruct b. 
    simpl. destruct p. simpl. simpl in *.
        
    destruct env. 
    symmetry in Heqb. apply reverseinListLemma in Heqb.
    inversion Heqb. simpl in *.   destruct p.
    simpl in *. simpl. destruct p. simpl. simpl in H0. inversion H;subst. inversion H0;subst. f_equal.
    Check updateDSNotIn. 

    apply IHv in H6;auto.
    rewrite <- updateDSNotIn with (n:=a0);auto.
    symmetry in Heqb. 
    apply reverseinListFalse in Heqb.
    inversion H;subst.
    destruct env.
    rewrite updateDSNil. auto.
    inversion H0. destruct p0. simpl in *;auto.
    exfalso;apply Heqb;left;auto. 
Qed. 
    

Lemma getValueIn: forall env1 env2 s,
    uniqList (dom (env1++env2)) ->
    In (AIdent s) (dom env1) ->
    getValue (AIdent s) (env1 ++ env2) = getValue (AIdent s) env1.
Proof. 
   intro env1;induction env1. 
   - intros.
     inversion H0.
   - intros.
     simpl. destruct a;destruct p.
     destruct H0. simpl in H0.
     destruct (atom_eq_dec (AIdent s) a). auto. rewrite H0 in n. contradiction.
     inversion H;subst.
     destruct (atom_eq_dec (AIdent s) a).
     auto.
     apply IHenv1;auto. 
Qed.

Lemma getValueIn': forall v1 (env1:value_env) env2  s,
    uniqList (dom v1) ->
    dom (env1 ++ env2) = dom v1 ->
    In (AIdent s) (dom env1) ->
    getValue (AIdent s) v1 = getValue (AIdent s) (updateDataState v1 (dom env1)).
Proof.
  intro v1;induction v1.   
  -
    intros.
    destruct env1. simpl. auto.
    inversion H0.
  -
    intros. destruct env1.
    inversion H1.
    destruct a;destruct p.
    destruct p0;destruct p.
    inversion H1;subst. simpl in *. simpl.
    subst. inversion H0;subst.
    destruct (atom_eq_dec (AIdent s) (AIdent s)).
    simpl. destruct (atom_eq_dec (AIdent s) (AIdent s)).
    auto. contradiction. contradiction.
    simpl.
    inversion H;subst. 
    inversion H0;subst.
    destruct (atom_eq_dec (AIdent s) a).
    destruct (atom_eq_dec a a).
    simpl. destruct (atom_eq_dec (AIdent s) a). auto.
    exfalso;apply n;auto. contradiction.
    destruct (atom_eq_dec a a). simpl.
    destruct (atom_eq_dec (AIdent s) a).
    exfalso;apply n;auto.
    SearchAbout updateDataState.
    rewrite <- updateDSNotIn with (n:=a);auto.
    apply IHv1 with (env2:=env2);auto.
     contradiction.
Qed.

Print stateEvDefInstanceMapEquiv. 

Lemma domUniqEqual: forall A B (l:list (A*B)) a b1 b2,
    uniqList (dom l) ->
    In (a,b1) l ->
    In (a,b2) l ->
    b1 = b2. 
Proof.
  intros A B l;induction l. 
- intros. inversion H0. 
- intros. simpl in *. destruct H0;destruct H1.
  rewrite H1 in H0. inversion H0;auto.
  rewrite H0 in H. simpl in H.
  inversion H;subst. apply domIn in H1. contradiction.
  rewrite H1 in H;simpl in *. 
  inversion H;subst.
  apply domIn in H0.
  contradiction.
  apply IHl with (a:=a0);auto.
  inversion H;auto.
Qed.


Lemma varNotChangeBasic: forall M (conf conf' : configuration M) sce re s,
    correct_configuration conf ->
    Result conf' = constructConfig sce re conf ->
    (~ In sce (scenarioUpdateVar (dom (controlstate conf)) (AIdent s))) ->
    stpStMapEquiv' M ->
    stateEvDefInstanceMapEquivEListProp M ->
    stateEvDefInstanceMapEquiv M ->
    transEvMapProp M ->
    correctStateEvStepMap' M ->
    getValue (AIdent s) (datastate conf) = getValue (AIdent s) (datastate conf').
Proof.
  intros. rename H2 into stpStMapEq. rename H3 into stateEvMapProp. rename H4 into mapEquiv.
  
  rename H5 into transProp. rename H6 into correctStMap. 
  unfold constructConfig in H0.
  remember (getScenarioState sce (controlstate conf)).
  destruct o;inversion H0.
  remember (transEvMapFunc (stateEvDefInstanceMap M) (Some s0, Some (eventDefinition re))). 
  destruct o;inversion H0. 
  remember ( findEventInstance re (datastate conf)
                               l).

  
  destruct o;inversion H0.
  remember (createValueEnv (eventArgs e) (eventParams (eventDefinition re)) (eventArguments re)).  destruct e0;inversion H0. 
  remember (getStep' conf sce e).
  destruct o;inversion H0.
  remember (configTransition (extendValEnv (datastate conf) v) re e sce s1 conf ).
  destruct e0;inversion H0.
  unfold configTransition in Heqe1.
  remember ( execAction (extendValEnv (datastate conf) v, nil) (stepActions s1)
              (filter
                 (fun e : event_definition =>
                  match eventKind e with
                  | Internal => true
                  | Imported => false
                  | Exported => true
                  end) (events M))).
  destruct e0;inversion Heqe1.
  subst.
  
  destruct H.

  
  unfold correctStateEvStepMap' in correctStMap.
  assert (In s1 (traces sce) /\ stepEvent s1 = e /\ pre_state s1 = s0). 
  apply correctStMap.
  pose proof stpStMapEquivLem. rename H into lem.
  apply lem;auto. symmetry.
  
  unfold stpStMapEquiv'  in stpStMapEq.
  Check getStepMap'. 
   apply getStepMap' with (conf:=conf) (sce:=sce);auto.
  
  
  destruct H. 
  pose proof sceNotUpdateVar.
  unfold getTransitionsOfScenario in H8. 
  apply H8  with (lst:=(dom (controlstate conf))) (sce:=sce) (s:=s)in H;auto.
  Focus 2.
  apply scenarioIn in Heqo;auto. pose proof varNoChangeExecuteAction. destruct v1. 
  apply H10 with (env:=extendValEnv (datastate conf) v) (l:=nil) (env':=v1) (l':=l0) (eventList:=(filter
               (fun e : event_definition =>
                match eventKind e with
                | Internal => true
                | Imported => false
                | Exported => true
                end) (events M))) in H;auto.
  unfold extendValEnv in H. inversion Heqe1;simpl.

  

  assert ( dom (extendValEnv (datastate conf) v) = dom v1).
  
  apply typeActionNoChange with (action:= (stepActions s1)) (r:=l0) (eventList:=(filter
               (fun e : event_definition =>
                match eventKind e with
                | Internal => true
                | Imported => false
                | Exported => true
                end) (events M))) (l:=nil) ;auto.
  unfold extendValEnv in H11.
  pose proof updateDataStateDom.
  assert (uniqList (dom v1)).
  rewrite <- H11.
  unfold stateEvDefInstanceMapEquivEListProp in stateEvMapProp.

  
  unfold stateEvDefInstanceMapEquiv in mapEquiv. 
  remember Heqo0. clear Heqe3. Check findEventInstanceIn.
  remember Heqo1. clear Heqe3.   apply findEventInstanceIn in e1;auto.
  remember e0.  clear Heqe3.
  symmetry in e2. apply semantic_rules.stateEvDefInstanceMapEquiv' in e2;auto.
  Focus 2. auto. destruct mapEquiv;auto. 
 (* symmetry in Heql0. rewrite  <- mapEquiv in Heql0.*)
 assert (event e = eventDefinition re). apply findInstanceDefMon with (lst:=l) (ds:= (datastate conf)) (mon:=M) (st:=s0);auto. rename H14 into eDef. 
 Check stateEvMapProp.   apply  stateEvMapProp in e2;auto. Focus 2.
 unfold not. intros. rewrite H14 in e1. inversion e1. 
 (*destruct mapEquiv. 
 apply inControlState in Heqo;auto.
 apply sceStateCorrect in Heqo;auto. Focus 2.  apply scenarioIn in Heqo;auto.
 apply H15 with (e:=eventDefinition re) in Heqo;auto.
 Focus 2.
 unfold stateSceProp in ssp.
  eapply ssp;auto.  apply e2. apply e1. auto. 
  destruct Heqo.  destruct H16.
  
  assert (x=l).
  eapply domUniqEqual. apply H14. apply H17. auto. subst. auto. 
 *)
(*  Focus 2. unfold not. intros. rewrite H12 in e0;inversion e0.*)
repeat (match goal with
            | [H: _ /\ _ |-_] => destruct H
            | [H: exists _, _ |- _] => destruct H
        end).

remember (createTypEnv (eventArgs x) (eventParams (event x))).
destruct e2;(try (inversion H19)).
remember (createTypEnv (eventArgs x0) (eventParams (event x0)) ).
destruct e2;inversion H19. 

repeat (match goal with
            | [H: _ /\ _ |-_] => destruct H
            | [H: exists _, _ |- _] => destruct H
              end).

rewrite H17 in Heqo1.
unfold typeCheckInstance in H20.
unfold typeCheckInstance in H21.

repeat (match goal with
            | [H: _ /\ _ |-_] => destruct H
            | [H: exists _, _ |- _] => destruct H
        end).
SearchAbout findEventInstance.
remember Heqo1. clear Heqe5. apply findEventInstanceIn in Heqo1;auto.

inversion Heqo1. 
 apply createEqual with (vl:=(eventArguments re)) (v2:=v) in Heqe3;auto.
rewrite domApp. rewrite domApp in H28.  rewrite <- ds_dom_eq in H28;auto.
rewrite dom2dom' in H28. rewrite <-Heqe3;auto. rewrite H29. rewrite eDef;auto.
destruct H29;inversion H29.   

apply createEqual with (vl:=(eventArguments re)) (v2:=v) in Heqe4;auto.
rewrite domApp. rewrite domApp in H26. SearchAbout dsmon. rewrite <- ds_dom_eq in H26;auto.
SearchAbout dom2. rewrite dom2dom' in H26. rewrite <-Heqe4;auto. rewrite H29. rewrite eDef;auto.

  assert (dom  (datastate conf) = dom (updateDataState v1 (dom  (datastate conf)))).
  apply H13 with (x:=v);auto.
  
assert (In (AIdent s) (dom (datastate conf)) \/ ~ In (AIdent s) (dom (datastate conf))).
  apply excluded_middle.
  destruct H16.
  Focus 2.
  rewrite getValueNone;auto.
  rewrite <- getValueNone with (env:=(updateDataState v1 (dom (datastate conf)))) (s:=s);auto.
  rewrite H15 in H16;auto.
  rewrite getValueIn with (env2:=v) in H;auto.
  Focus 2. rewrite <- H11 in H14;auto. 
  rewrite H. Check createEqual. 
  SearchAbout updateDataState.
  apply getValueIn' with (env2:=v);auto. 

Qed. 



Lemma uniqListSce: forall l (sce:scenario) (v1:scenario_state) v2,
    uniqList (dom l) ->
    In sce (dom l) ->
    In (sce, v1) l ->
    In (sce, v2) l ->
    v1 = v2. 
Proof.
   intro l;induction l.   
   - intros. inversion H0.
   - intros. simpl in H0. simpl in H1.
     simpl in H2. destruct a. simpl in *. 
     destruct H0. subst. 
     destruct H1. destruct H2. rewrite H1 in H0. inversion H0;auto.
      inversion H. subst.
     apply domIn in H1. contradiction.
      destruct H2. inversion H;subst. apply domIn in H0;contradiction.
     inversion H;subst. apply domIn in H0;contradiction.
      inversion H;subst.
     destruct H1. destruct H2. rewrite H2 in H1;inversion H1;auto.
     inversion H1;subst. inversion H1;subst;contradiction.
     destruct H2. inversion H2;subst. apply domIn in H1;contradiction.
     apply IHl with (sce:=sce);auto. 
Qed.      
     


Lemma termL3: forall e M (conf conf' : configuration M) sce,  Result conf' = constructConfig sce e conf  ->
 (finishedscenarios conf' = sce::nil).
Proof. 
intros. unfold constructConfig in H.   
destruct (getScenarioState sce (controlstate conf)).
destruct (transEvMapFunc (stateEvDefInstanceMap M) (Some s, Some (eventDefinition e))). 
destruct (findEventInstance e (datastate conf) l).  
destruct (createValueEnv (eventArgs e0) (eventParams (eventDefinition e)) (eventArguments e)) .
destruct (getStep' conf sce e0). 
  unfold  configTransition in H.

destruct (execAction (extendValEnv (datastate conf) v, nil) (stepActions s0)
            (filter
               (fun e : event_definition =>
                match eventKind e with
                | Internal => true
                | Imported => false
                | Exported => true
                end) (events M))) .
destruct v0. inversion H;subst. simpl. auto. 
 inversion H.  
inversion H.  inversion H. inversion H. inversion H. inversion H. 
Qed.




Lemma dom2DS: forall re M (conf conf' : configuration M) sce,
    In sce (dom (controlstate conf))->
    correct_configuration conf  ->
    Result conf' = constructConfig sce re conf  ->
    stateEvDefInstanceMapEquivEListProp M ->
    stateEvDefInstanceMapEquiv M ->
    transEvMapProp M ->
 (dom2 (datastate conf)) = (dom2 (datastate conf')).
Proof. intros.
      rename H2 into stateEvMapProp. rename H3 into mapEquiv.
  rename H4 into transProp.
       unfold constructConfig in H1.
       
       remember (getScenarioState sce (controlstate conf)).
       destruct o;inversion H1.
       remember (transEvMapFunc (stateEvDefInstanceMap M) (Some s, Some (eventDefinition re))).
destruct o;inversion H1.        
remember (findEventInstance re (datastate conf) l).
destruct o;inversion H1.
remember (createValueEnv (eventArgs e) (eventParams (eventDefinition re)) (eventArguments re)).
destruct e0;inversion H1. 
remember (getStep' conf sce e ).
destruct o;inversion H1.
remember (configTransition (extendValEnv (datastate conf) v) re e sce s0 conf).
destruct e0;inversion H1. subst.
unfold configTransition in Heqe1.

remember (execAction (extendValEnv (datastate conf) v, nil) (stepActions s0)
            (filter
               (fun e : event_definition =>
                match eventKind e with
                | Internal => true
                | Imported => false
                | Exported => true
                end) (events M))).
destruct e0;inversion Heqe1. 
destruct v1;inversion H1. simpl. unfold extendValEnv in Heqe2.
pose proof updateDataStateDom2. inversion H8;simpl.
assert (dom (datastate conf ++ v) = dom v1).
apply typeActionNoChange with (action:=(stepActions s0)) (r:=l0) (l:=nil) (eventList:=(filter
               (fun e : event_definition =>
                match eventKind e with
                | Internal => true
                | Imported => false
                | Exported => true
                end) (events M)));auto.
apply H2 with (x:=v);auto. 

Focus 2.
rewrite <- typeActionNoChangeDom2 with (env:=datastate conf ++ v) (action:=(stepActions s0)) (r:=l0) (l:=nil) (eventList:=(filter
               (fun e : event_definition =>
                match eventKind e with
                | Internal => true
                | Imported => false
                | Exported => true
                end) (events M)));auto.

 rewrite <- H9.
  unfold stateEvDefInstanceMapEquivEListProp in stateEvMapProp.
  remember Heqo0. clear Heqe3.
  symmetry in e0. rewrite  <- semantic_rules.stateEvDefInstanceMapEquiv' in e0;auto.
  Focus 2. unfold stateEvDefInstanceMapEquiv in mapEquiv.
  destruct mapEquiv;auto.
  remember Heqo1. clear Heqe3. 
  (*remember Heqo0. clear Heqe3.  unfold stateEvDefInstanceMapEquiv in mapEquiv.*)  apply findEventInstanceIn in e1;auto.  (*remember (transEvMap (Some s, Some (eventDefinition re))).  symmetry in Heql0. rewrite  <- mapEquiv in Heql0.*)
 assert (event e = eventDefinition re).  apply findInstanceDefMon with (lst:=l) (ds:= (datastate conf)) (mon:=M) (st:=s);auto. rename H11 into eDef. 
 Check stateEvMapProp.  apply  stateEvMapProp in e0.

 Focus 2. unfold not. intros. rewrite H11 in e1;inversion e1.
repeat (match goal with
            | [H: _ /\ _ |-_] => destruct H
            | [H: exists _, _ |- _] => destruct H
        end).

remember (createTypEnv (eventArgs x) (eventParams (event x))).
destruct e0;(try (inversion H13)).
remember (createTypEnv (eventArgs x0) (eventParams (event x0)) ).
destruct e0;inversion H13. 

repeat (match goal with
            | [H: _ /\ _ |-_] => destruct H
            | [H: exists _, _ |- _] => destruct H
              end).

rewrite H11 in e1.
unfold typeCheckInstance in H14.
unfold typeCheckInstance in H15.
Print stateSceProp. 
repeat (match goal with
            | [H: _ /\ _ |-_] => destruct H
            | [H: exists _, _ |- _] => destruct H
        end).
destruct e1. subst. 
 apply createEqual with (vl:=(eventArguments re)) (v2:=v) in Heqe3;auto.
rewrite domApp. rewrite domApp in H22.  erewrite <- ds_dom_eq in H22;eauto.
 rewrite dom2dom' in H22. rewrite <-Heqe3;auto. rewrite eDef;auto. simpl in H23. destruct H23;inversion H23;subst.   

apply createEqual with (vl:=(eventArguments re)) (v2:=v) in Heqe4;auto.
rewrite domApp. rewrite domApp in H20.  erewrite <- ds_dom_eq in H20;eauto. rewrite dom2dom' in H20. rewrite <-Heqe4;auto. rewrite eDef;auto.
Qed.



Lemma innerCombineCS: forall M (conf : configuration M) sceList v0  re  c,
    correct_configuration conf ->
    incl sceList (dom (controlstate conf)) ->
    Result v0 = constructConfigList' sceList re conf ->
    Some c = innerCombineFunc'''' conf v0 ->
    dom (controlstate conf) = dom (controlstate c). 
Proof. intros ?? sceList;induction sceList. 
       - intros.
         simpl in H1.  inversion H1.   rewrite H4 in H2.
         simpl in H2. inversion H2.
       - intros.
         simpl in H1.
         remember (constructConfig a re conf).
         destruct e;inversion H1.
         clear H4.
         remember (constructConfigList' sceList re conf).
         destruct e;inversion H1. rewrite H4 in H2.
         simpl in H2.
         destruct v1.
         subst.
          remember (mergeConfigFunc' conf conf v).
         destruct e. inversion H2;subst.
         Focus 2. inversion H2.
         apply mergeConfigFuncCSNoChange with (conf1:=conf) (conf2:=v);auto.
         
         remember ( innerCombineFunc'''' conf (c0::v1)).
         destruct o;inversion H2.
        clear H5.  subst. remember (mergeConfigFunc' conf v c1).
         destruct e;
         inversion H2;subst.
       
         apply mergeConfigFuncCSNoChange with (conf1:=v) (conf2:=c1);auto.
Qed.




Lemma mergeDataFuncUpdate: forall dso ds1 ds2 ds3 a,
Result ds3 = mergeDataStateFunc dso ds1 ds2 ->
getValue a dso = getValue a ds1 ->
getValue a dso = getValue a ds2 ->
getValue a dso = getValue a ds3.
Proof. intro dso. induction dso;intros;simpl.
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
destruct (atom_eq_dec (AIdent s) a2). inversion H1.
destruct (atom_eq_dec (AIdent s) a2). auto. exfalso;apply n;auto.
simpl in H1.
simpl in H0.
destruct (atom_eq_dec (AIdent s) a2 ). exfalso;apply n;auto.    
apply IHdso with (ds1:=ds1) (ds2:=ds2) ;auto. 
destruct (range_typ_dec r0 r).
subst. simpl in H1. simpl in H0.   destruct a0;auto. inversion H. 
simpl. auto. simpl. inversion H. simpl. auto.

(*destruct (atom_eq_dec (AIdent s) a1).*) subst. 
destruct (atom_eq_dec (AIdent s) a2). inversion H1. 
exfalso;apply n;auto. subst. 
(*exfalso;apply n0;auto. 
destruct (atom_eq_dec (AIdent s) a2).
rewrite e in n0. exfalso;apply n0;auto.*)
inversion H. simpl.
(*destruct (atom_eq_dec (AIdent s) a2).*)
destruct (atom_eq_dec (AIdent s) a2).
exfalso;apply n0;auto.  
apply IHdso with (ds1:=ds1) (ds2:=ds2);auto.
inversion H;auto.  inversion H;auto. inversion H;auto.
destruct (range_typ_dec r1 r). subst.                 
simpl in H0.
simpl in H1.
destruct a0;auto. inversion H;auto.
inversion H;auto.
(*destruct (atom_eq_dec (AIdent s) a1).  *)
destruct (atom_eq_dec (AIdent s) a2). subst. 
(*inversion H0. exfalso;apply n;auto. inversion H0. exfalso;apply n;auto.
destruct (atom_eq_dec (AIdent s) a2).
subst. exfalso;apply n1;auto.
*)
inversion H.
simpl.
(*destruct (atom_eq_dec (AIdent s) a1).*)
destruct (atom_eq_dec (AIdent s) (AIdent s)). auto. 
exfalso;apply n1;auto.
inversion H;subst.
simpl.
destruct (atom_eq_dec (AIdent s) a2).
exfalso;apply n1;auto. 
apply IHdso with (ds1:=ds1) (ds2:=ds2);auto.
inversion H;subst;auto.
inversion H;subst;auto.
inversion H;subst;auto.
inversion H.
inversion H. inversion H.
inversion H.
inversion H.
inversion H.
Qed.   


(*mergeDataFuncUpdate*)         
Lemma mergeConfigFuncDSVarEqual: forall M (conf conf1 conf2 : configuration M) v s,
    Result v = mergeConfigFunc' conf conf1 conf2 ->
    getValue (AIdent s) (datastate conf) = getValue (AIdent s) (datastate conf1) ->
    getValue (AIdent s) (datastate conf) = getValue (AIdent s) (datastate conf2) ->
    getValue (AIdent s) (datastate conf) = getValue (AIdent s) (datastate conf1) ->       
    getValue (AIdent s) (datastate conf) = getValue (AIdent s) (datastate v).
Proof.
  intros.
  unfold mergeConfigFunc' in H.
  remember (mergeDataStateFunc (datastate conf) (datastate conf1) (datastate conf2)). 
  destruct e;inversion H.   clear H4.
  remember ( mergeControlStateFunc (controlstate conf) (controlstate conf1)
                                   (controlstate conf2)).
  destruct e;inversion H;simpl.
  pose proof mergeDataFuncUpdate.
  apply H3 with (ds1:=(datastate conf1)) (ds2:=datastate conf2);auto. 
Qed.




Lemma innerCombineFuncVarNoChange: forall sceList M (conf : configuration M) v0 c re s,
    correct_configuration conf ->
    Result v0 = constructConfigList' sceList re conf ->
    Some c = innerCombineFunc'''' conf v0 ->
    In (AIdent s) (dom (datastate conf)) ->
    (forall sce : scenario,
        In sce sceList ->
        ~ In sce (scenarioUpdateVar (scenarios M) (AIdent s))) ->
     stpStMapEquiv' M ->
  stateEvDefInstanceMapEquivEListProp M ->
  stateEvDefInstanceMapEquiv M ->
  transEvMapProp M ->
  correctStateEvStepMap'  M ->
    getValue (AIdent s) (datastate conf) = getValue (AIdent s) (datastate c).
Proof. intro sceList;induction sceList.
       - intros.
         simpl in H0. inversion H0;subst.
         simpl in H1. inversion H1. 
       -
         intros.
         Print stateSceProp. 
         simpl in H0.
         remember (constructConfig a re conf).
         destruct e;inversion H0.
         remember (constructConfigList' sceList re conf).
         destruct e;inversion H0.
         rewrite H11 in H1.
         simpl in H1. subst.
         destruct v1. clear H10. clear H0. 
         remember (mergeConfigFunc' conf conf v).
         destruct e;inversion H1. subst.
         pose proof mergeConfigFuncDSVarEqual.
         apply H0 with (conf1:=conf) (conf2:=v);auto.
         pose proof   varNotChangeBasic.
         apply H9 with (sce:=a) (re:=re);auto.
         destruct H. rewrite cs_consist;auto. apply H3;left;auto.
         clear H10. clear H0.
         remember (innerCombineFunc'''' conf (c0 :: v1)).
         destruct o;inversion H1;subst;simpl. clear H9. 
         remember (mergeConfigFunc' conf v c1).
         destruct e;inversion H1.
         subst.
         apply IHsceList with (re:=re) (s:=s) in Heqo;auto.
         Focus 2. intros.
         apply H3. right;auto.
         assert ( ~ In a (scenarioUpdateVar (scenarios M) (AIdent s))).
         apply H3;left;auto.

         
         pose proof   varNotChangeBasic.
         assert (getValue (AIdent s) (datastate conf) = getValue (AIdent s) (datastate v)). apply H9 with (sce:=a) (re:=re);auto.
         destruct H. rewrite cs_consist;auto.
         pose proof mergeConfigFuncDSVarEqual.
         apply H11 with (conf1:=v) (conf2:=c1);auto.
     
Qed. 



Lemma sceNoChange': forall    lst sce sce'  s0, 
sce<>sce' -> 
getScenarioState sce' (lst) =
getScenarioState sce' (updateControlState (lst) sce s0).
Proof. intro lst.  induction lst.
- intros. simpl. auto.
- intros.
simpl. destruct a. destruct (string_dec (scenarioId sce') (scenarioId s)). 
+  unfold updateControlState. simpl. 
destruct (string_dec (scenarioId s) (scenarioId sce)). 
* simpl. unfold not in H. rewrite <- e in e0.       
rewrite ScenarioEquivalence in e0. exfalso. apply H. symmetry;auto.
* simpl. rewrite e.    
destruct (string_dec (scenarioId s) (scenarioId s)). auto. exfalso;apply n0. auto.
+  unfold updateControlState; simpl.
destruct (string_dec (scenarioId s) (scenarioId sce)). 
* simpl. rewrite e. destruct (string_dec (scenarioId sce') (scenarioId sce)).
rewrite ScenarioEquivalence in e0. exfalso. apply H. symmetry;auto.
apply IHlst. auto.
* simpl. destruct (string_dec (scenarioId sce') (scenarioId s)). 
exfalso. apply n. auto. apply IHlst. auto.
Qed.

(*aux lemma to prove sceNoChangeList *)
Lemma sceNoChange: forall M (conf conf' : configuration M) sce e, constructConfig sce e conf = Result conf'
-> (forall sce', sce' <> sce /\ In sce (dom (controlstate conf)) -> getScenarioState sce' (  (controlstate conf)) = getScenarioState sce' (  (controlstate conf'))).
Proof.
intros. unfold constructConfig in H. 
destruct (getScenarioState sce (controlstate conf));inversion H;clear H2.
destruct (transEvMapFunc (stateEvDefInstanceMap M) (Some s, Some (eventDefinition e)));inversion H;clear H2.
destruct (findEventInstance e (datastate conf) l); inversion H;clear H2.
destruct (createValueEnv (eventArgs e0) (eventParams (eventDefinition e)) (eventArguments e));inversion H;clear H2.
destruct (getStep' conf sce e0);inversion H;clear H2.
unfold configTransition in H.
destruct (execAction (extendValEnv (datastate conf) v, nil) (stepActions s0)
            (filter
               (fun e : event_definition =>
                match eventKind e with
                | Internal => true
                | Imported => false
                | Exported => true
                end) (events M)));inversion H;auto. 
 destruct v0. inversion H2;simpl. 
    
 apply sceNoChange'. destruct H0;auto.
Qed. 


(*mergeDataFuncUpdate*)         
Lemma mergeConfigFuncScenarioStateNoChange: forall sce M (conf conf1 conf2 : configuration M) v,
    In sce (dom (controlstate conf)) ->
    Result v = mergeConfigFunc' conf conf1 conf2 ->
    getScenarioState sce (controlstate conf) = getScenarioState sce (controlstate conf1) ->
    getScenarioState sce (controlstate conf) = getScenarioState sce (controlstate conf2) ->
    getScenarioState sce (controlstate conf) = getScenarioState sce (controlstate v)      
   .
Proof.
  intros.
  unfold mergeConfigFunc' in H0.
  remember (mergeDataStateFunc (datastate conf) (datastate conf1) (datastate conf2)). 
  destruct e;inversion H0.   clear H4.
  remember ( mergeControlStateFunc (controlstate conf) (controlstate conf1)
                                   (controlstate conf2)).
  destruct e;inversion H0;simpl.
  pose proof mergeControlSceInvariant.
  pose proof domMergeConfig.
  assert (dom (controlstate conf) = dom (controlstate conf1) /\ dom (controlstate conf) = dom (controlstate conf2)).
  apply H5;auto.
  exists v1;auto. destruct H6. 
  apply H3 with (cs1:=(controlstate conf1)) (cs2:=(controlstate conf2));auto.
  rewrite H6 in H7;auto.
  rewrite H1 in H2;auto. 
Qed.


Lemma getScenarioStateNone: forall env sce ,
    ~ In sce (dom env) ->
    getScenarioState sce env = None.  
Proof.         
  intro env;induction env.
  - intros. simpl;auto.
  - intros. simpl.
    destruct a.
    destruct (string_dec (scenarioId sce) (scenarioId s)).
    SearchAbout scenarioId.
    rewrite ScenarioEquivalence in e;auto. subst.
    exfalso;apply H. simpl;left;auto.
    apply IHenv;auto. unfold not. intros. apply H;simpl;right;auto.
Qed.


Lemma innerCombineFuncVarScenarioStateNoChange: forall sceList sce M (conf : configuration M) v0 c re,
    correct_configuration conf ->
    Result v0 = constructConfigList' sceList re conf ->
    incl sceList (dom (controlstate conf)) ->
    ~ In sce sceList ->
    Some c = innerCombineFunc'''' conf v0 ->
    getScenarioState sce (controlstate conf) = getScenarioState sce (controlstate c). 
Proof.
  intro sceList;induction sceList. 

  - intros.
    simpl in H0. inversion H0;subst.
    simpl in H3. inversion H3.
  - intros.
    simpl in H0.
    remember (constructConfig a re conf).
     destruct e;inversion H0. remember (constructConfigList' sceList re conf).
     destruct e;inversion H0.
     rewrite H6 in H3.
     simpl in *.
     destruct v1. subst. clear H5. 
      remember (mergeConfigFunc' conf conf v).
         destruct e;inversion H3. subst.
    clear H3. pose proof mergeConfigFuncScenarioStateNoChange.       
         assert (In sce (dom (controlstate conf)) \/ ~ In sce (dom (controlstate conf))).
         apply excluded_middle.
         destruct H4.        
         apply H3 with (conf1:=conf) (conf2:=v);auto.
         apply sceNoChange with (sce:=a) (conf':=v) (e:=re);auto.
         split. unfold not. intros. apply H2;left;auto.
         
         unfold incl in H1. apply H1;left;auto.
         pose proof getScenarioStateNone.
         rewrite H5;auto.
         pose proof mergeConfigFuncCSNoChange.
         assert (dom (controlstate conf) = dom (controlstate v0)).
         apply  mergeConfigFuncCSNoChange with (conf1:=conf) (conf2:=v);auto.
        symmetry in H5.   apply H5. rewrite H7 in H4. 
        auto.

         remember (innerCombineFunc'''' conf (c0::v1)).
         destruct o;inversion H3. clear H7.  
         subst.   remember (mergeConfigFunc' conf v c1).
         destruct e;inversion H3.
         subst. clear H5. clear H3.  
         apply IHsceList with (re:=re) (sce:=sce)  in Heqo;auto.
         Focus 2. intros. unfold incl in H1. unfold incl. intros.
         apply H1;auto. right;auto.
         assert (a <> sce).
         unfold not. intros. apply H2. left;auto.
         pose proof sceNoChange.
         assert (getScenarioState sce (controlstate conf) = getScenarioState sce (controlstate v)).         apply H4 with (sce:=a) (e:=re);auto.
         split;auto. unfold incl in H1. apply H1;left;auto.
         
         assert (In sce (dom (controlstate conf)) \/ ~ In sce (dom (controlstate conf))).
         apply excluded_middle.
         destruct H6.
          apply  mergeConfigFuncScenarioStateNoChange with (conf1:=v) (conf2:=c1);auto.
        
        
         pose proof getScenarioStateNone.
         rewrite H7;auto.
         pose proof mergeConfigFuncCSNoChange. symmetry. 
apply H7.       assert (dom (controlstate conf) = dom (controlstate v0)).
         apply  mergeConfigFuncCSNoChange with (conf1:=v) (conf2:=c1);auto.
         rewrite <-  H9. 
        auto.   
Qed.

Lemma inScenarioState: forall env sce v ,
    uniqList (dom env) ->
    In (sce, v) env ->
    Some v = getScenarioState sce env.
Proof.
  intro env;induction env. 
  -  intros. inversion H0.
  - intros.
    destruct a. simpl in *.
    destruct H0.
    inversion H0;subst.
    destruct (string_dec (scenarioId sce) (scenarioId sce));auto.
    contradiction.
    destruct (string_dec (scenarioId sce) (scenarioId s)).
    SearchAbout scenarioId.
    rewrite ScenarioEquivalence in e. subst.
    inversion H;subst. apply domIn in H0. contradiction.
    apply IHenv;auto. inversion H;auto. 
Qed.


Lemma mergeDSDom2NoChange': forall ds ds1 ds2 v,
    Result v = mergeDataStateFunc ds ds1 ds2 ->
    dom2 ds2 = dom2 ds. 
Proof.   
  intro ds;induction ds.
  - intros. simpl in H.
    destruct ds1;inversion H.
    destruct ds2;inversion H;auto. 
  -
    intros.
    destruct ds1;inversion H.
    destruct a;destruct p. inversion H1.
    destruct ds2;inversion H1.
    destruct a;destruct p0. destruct p. destruct p;inversion H1.
    destruct a;destruct p1;destruct p;destruct p.
    destruct p0;destruct p.
    destruct (atom_eq_dec a a0);inversion H1.
    destruct (atom_eq_dec a a1);inversion H1.
    destruct (typ_eq_dec t t0);inversion H1.
    destruct (typ_eq_dec t t1);inversion H1.
    subst.     remember (mergeDataStateFunc ds ds1 ds2).
    destruct e;inversion H1.
    
    destruct (range_typ_dec r0 r1).
    subst. inversion H1;simpl.
    f_equal.
    apply IHds with (ds1:=ds1) (ds2:=ds2) (v:=v0);auto.
    destruct (range_typ_dec r0 r).
    subst.
    inversion H1;simpl. f_equal.
    apply IHds with (ds1:=ds1) (ds2:=ds2) (v:=v0);auto.
    destruct (range_typ_dec r1 r).
    inversion H1;simpl. f_equal.
    apply IHds with (ds1:=ds1) (ds2:=ds2) (v:=v0);auto.
    inversion H1.
Qed.

Lemma innerCombineNoErr: forall M (conf : configuration M) sceList l re ,
    correct_configuration conf ->
    noMergeError' M ->
    basicPrecondition conf re ->
    incl sceList (dom (controlstate conf)) ->
    uniqList sceList ->
    Result l = constructConfigList' sceList re conf ->
    l <> nil ->
    (forall sce1 sce2, In sce1 sceList -> In sce2 sceList -> ~ noIntersection (alphabet sce1) (alphabet sce2)) -> 
    exists conf' : configuration M, innerCombineFunc'''' conf l = Some conf'.
Proof.
  intros ?? sceList;induction sceList.
  -  intros. simpl in H4.  inversion H4;subst. contradiction.
  -  intros. rename H6 into noInter. simpl in H4. 
     
     remember (constructConfig a re conf).
     destruct e;inversion H4. remember (constructConfigList' sceList re conf).
     destruct e;inversion H4.
     simpl.  subst.     

     assert (exists s,  Result s = mergeConfigFunc' conf conf v).
     pose proof mergeConfigCorrect'.
     apply H6;auto. 
     Focus 3.  intros. rewrite <- H10 in H9. inversion H9;left;auto.
     Focus 3. intros. left.
     remember H. clear Heqc. destruct c.
     apply uniqListSce with (l:=controlstate conf) (sce:=sce);auto.
     pose proof domControlSyncL1.
     apply H8 with (e:=re) (sce:=a);auto. unfold incl in H2. apply H2. left;auto.
     pose proof dom2DS.
     destruct H1;auto.
     repeat (match goal with
            | [H: _ /\ _ |-_] => destruct H
            | [H: exists _, _ |- _] => destruct H
             end).
     rename H19 into stSceProp.
     rename H20 into scIn. 
     apply H8 with (re:=re) (sce:=a);auto.
     unfold incl in H2. apply H2;auto. left;auto.
     
     destruct H6. rewrite <- H6.
     destruct v0. exists x;auto.
     assert ( exists conf' : configuration M, innerCombineFunc'''' conf (c::v0) = Some conf').
     apply IHsceList with (re:=re);auto.
     unfold incl;unfold incl in H2. intros. apply H2;auto. right;auto.
     inversion H3;subst;auto. unfold not;intros. inversion H8.
     intros. apply noInter;auto. right. auto. right;auto.
     rename H8 into existConf. 
            
     remember (innerCombineFunc'''' conf (c :: v0) ).
     destruct o.      
     pose proof mergeConfigCorrect'.
     assert (exists conf', Result conf' = mergeConfigFunc' conf v c0). 
     apply H8;auto.
     SearchAbout (dom (controlstate _) = dom (controlstate _)).
     pose proof domMerge'.
     assert (dom (controlstate conf) = dom (controlstate conf) /\ dom (controlstate conf) = dom (controlstate v)).
     apply H9. exists x;auto. destruct H10;auto. 
     SearchAbout innerCombineFunc''''. 
     apply innerCombineCS with (sceList:=sceList) (v0:=c::v0) (re:=re);auto.
     unfold incl;intros. unfold incl in H2. apply H2;auto. right;auto.  
     Focus 2. 
     pose proof innerCombineDSDom2.
     apply H9 with (sceList:=sceList) (v0:=c::v0) (re:=re);auto.
     unfold incl in H2. unfold incl. intros. apply H2;auto. right;auto.
     unfold mergeConfigFunc' in H6.
     remember (mergeDataStateFunc (datastate conf) (datastate conf) (datastate v) ).
     symmetry. 
     destruct e;inversion H6. apply mergeDSDom2NoChange' with (ds1:=(datastate conf)) (v:=v1);auto. 
       
     intros.

     assert (In a ((scenarioUpdateVar (scenarios M) (AIdent s))) \/ ~ (In a ((scenarioUpdateVar (scenarios M) (AIdent s))))). 
     apply excluded_middle.
     destruct H13.
     
     assert (forall sce, In sce (sceList) -> ~ In sce ((scenarioUpdateVar (scenarios M) (AIdent s)))).
     intros.
     pose proof scenariosUpdateSingle''.
     apply H15 with (sce1:=a) (sce2:=sce) (v:=AIdent s) in H0;auto.
     destruct H0. destruct H0;auto.
     destruct H0. destruct H0;contradiction.
     destruct H0;contradiction.
     unfold not. intros. subst.
     inversion H3;subst. contradiction.
     apply  noInter;auto. left;auto.  right;auto. 
     erewrite <- ds_dom_eq;eauto. 
     rewrite dom2dom';auto.
     pose proof innerCombineFuncVarNoChange.
     assert (getValue (AIdent s) (datastate conf) = getValue (AIdent s) (datastate c0));auto.
     destruct H1.
     repeat (match goal with
            | [H: _ /\ _ |-_] => destruct H
            | [H: exists _, _ |- _] => destruct H
              end).
     apply H15 with (sceList:=sceList) (v0:=c::v0) (re:=re);auto.
     rewrite <- H10 in H16.
     rewrite <- H12 in H16. inversion H16. right;auto. 

     pose proof varNotChangeBasic.
     destruct H1.
     
     repeat (match goal with
            | [H: _ /\ _ |-_] => destruct H
            | [H: exists _, _ |- _] => destruct H
             end).
     rename H25 into stSceProp.
     rename H26 into scIn. 
     assert (getValue (AIdent s) (datastate conf) = getValue (AIdent s) (datastate v)).
     apply H14 with (sce:=a) (re:=re);auto.
     destruct H. rewrite cs_consist;auto.
      rewrite <- H10 in H25.
     rewrite <- H11 in H25. inversion H25. left;auto. 
     intros.
     assert (a = sce \/ a <> sce).
     apply excluded_middle.
     destruct H13. subst.
     pose proof innerCombineFuncVarScenarioStateNoChange.
     assert (getScenarioState sce (controlstate conf) = getScenarioState sce (controlstate c0)).
     apply H13 with (sceList:=sceList) (v0:=c::v0) (re:=re);auto.
     unfold incl in H2. unfold incl;intros. apply H2. right;auto.
     inversion H3;subst;auto.
    
     pose proof inScenarioState.
     apply H15 in H10;auto.
     apply H15 in H12;auto.
     rewrite H14 in H10.
     rewrite <- H12 in H10. inversion H10;auto. 
     Focus 2.
     destruct H;auto. 
     assert (dom (controlstate conf) = dom (controlstate c0)).
     apply innerCombineCS with (sceList:=sceList) (v0:=c::v0) (re:=re);auto.
     unfold incl in H2. unfold incl;intros. apply H2;right;auto.
     rewrite <- H16;destruct H;auto. 
     assert (getScenarioState sce (controlstate conf) = getScenarioState sce (controlstate v)).  
     apply sceNoChange with (sce:=a) (e:=re);auto.
     split;auto. unfold incl in H2;apply H2. left;auto.
     pose proof inScenarioState.
     apply H15 in H10;auto.
     apply H15 in H11;auto.
     rewrite H14 in H10.
     rewrite <- H11 in H10. inversion H10;auto.
     Focus 2.
     destruct H;auto.
     assert (dom (controlstate conf) = dom (controlstate v)).
     apply domControlSyncL1 with (sce:=a) (e:=re);auto. 
     unfold incl in H2;apply H2. left;auto.
     rewrite <- H16;destruct H;auto. 
          
     destruct H9.
     rewrite <- H9. exists x0;auto.
     destruct existConf. inversion H8. 
     
Qed.


Lemma combineNoErr: forall M (conf : configuration M) re,
    correct_configuration conf ->
    noMergeError' M ->
    syncProgress conf ->
    basicPrecondition conf re ->
    (exists conf', combineFunc re conf = Some conf').
Proof.
  intros.
  pose proof constructListNoErr.
  assert (exists lst : list (configuration M),
             Result lst = constructConfigList (dom (controlstate conf)) re conf /\ lst <> nil).
  apply H3;auto.
  destruct H4. destruct H4.
  unfold combineFunc.
  rewrite <- H4. 
  unfold constructConfigList in H4. 
  assert (exists conf' : configuration M, innerCombineFunc'''' conf x = Some conf').
  pose proof innerCombineNoErr. 
  apply H6 with (re:=re) (sceList:=(filter
            (fun x : scenario =>
             inList event_definition_dec (eventDefinition re) (alphabet x))
            (filterList (finishedscenarios conf) (dom (controlstate conf)) scenario_dec)));auto.
  unfold incl;intros.
  SearchAbout filter.
  apply filter_In in H7.
  destruct H7.
  SearchAbout filterList.
  apply filterL2 in H7;auto.
  SearchAbout filterList.
  assert (uniqList (filterList (finishedscenarios conf) (dom (controlstate conf)) scenario_dec)).
  apply uniqListFilter;auto.
  destruct H;auto.
  destruct H;auto.
  apply filterUniq;auto.
  intros.
  SearchAbout noIntersection.
  unfold not. intros.
  apply filter_In in H7. apply filter_In in H8. destruct H7. destruct H8.
  SearchAbout inList. apply reverseinListLemma in H10; apply reverseinListLemma in H11.
  unfold noIntersection in H9. destruct H9. apply H9 in H10. contradiction. 
  destruct H6.
  rewrite H6.
  destruct x. contradiction. 
  exists ((removeEventFromConf re x0));auto. 
 
Qed.

 
         (*Lemma mergeConfig'Correct: forall conf conf1 conf2,
    correct_configuration conf ->
    dom (controlstate conf) = dom (controlstate conf1) ->
    dom (controlstate conf) = dom (controlstate conf2) ->
    dom2 (datastate conf) = dom2 (datastate conf1) ->
    dom2 (datastate conf) = dom2 (datastate conf2) ->
    (forall s v v1 v2, In (AIdent s) (dom (datastate conf)) -> Some v = getValue (AIdent s) (datastate conf) ->   Some v1 = getValue (AIdent s) (datastate conf1) -> Some v2 = getValue (AIdent s) (datastate conf2) -> v = v1 \/ v = v2) ->
    (forall sce v v1 v2, In sce (dom (controlstate conf)) -> In (sce,v) (controlstate conf) ->
                         In (sce,v1) (controlstate conf1) -> In (sce,v2) (controlstate conf2) -> v = v1 -> v = v2) ->
    exists conf', Result conf' = mergeConfigFunc' conf conf1 conf2. 
Proof.
  intros. 
  pose proof  mergeDSCorrect.
  pose proof  mergeCSCorrect.
  unfold mergeConfigFunc.
  assert (exists ds' : value_env, Result ds' = mergeDataStateFunc (datastate conf) (datastate conf1) (datastate conf2)).
  apply H6;auto.
  destruct H.
  Print correct_object.
  destruct correct_mon.
  SearchAbout dom2.
  apply dom2dom in ds_dom_eq. rewrite  ds_dom_eq. auto.
  intros. destruct H. SearchAbout tyEnv. apply tyEnvVar with (env:=(datastate conf));auto.
  destruct H8. rewrite <- H8.
  assert (exists cs' : scenario_env, Result cs' =  mergeControlStateFunc (controlstate conf) (controlstate conf1) (controlstate conf2)).
  apply H7;auto.
  destruct H;auto. destruct H9. rewrite <- H9.
  exists ({|
      monitor_obj := monitor_obj conf;
      datastate := x;
      controlstate := x0;
      raisedevents := mergeList' (raisedevents conf1) (raisedevents conf2) raisedEvent_dec;
      exportedevents := mergeList' (exportedevents conf1) (exportedevents conf2)
                          raisedEvent_dec;
      finishedscenarios := finishedscenarios conf1 ++
                           finishedscenarios conf2 ++ finishedscenarios conf;
      sceEventMap := sceEventMap conf1 ++ sceEventMap conf2 ++ sceEventMap conf |});auto. 
Qed.*)
Print basicPrecondition. 

Definition basicPreconditionMon mon : Prop :=  typeCheck mon  /\ stateEvDefInstanceMapEquiv mon /\ transEvMapProp mon /\ transEvMapEventInstanceProp mon /\ stpStMapEquiv' mon /\ (forall sce, In sce (scenarios mon) -> stepExistsMon' mon sce) /\ correctStateEvStepMap' mon /\ stateEvDefInstanceMapEquivEListProp mon /\ alphabetScenario'' mon /\ stateSceProp mon /\ stateSceIn mon.


Lemma syncNoErr: forall M (conf : configuration M) re,
    correct_configuration conf ->
    In re (raisedevents conf) ->
    noMergeError' M ->
    syncProgress conf ->
    basicPreconditionMon M->
    (exists conf', synchrony conf conf' re).
Proof.
  intros.
  unfold synchrony.
  pose proof combineNoErr.
  destruct H3.
  repeat (match goal with
            | [H: _ /\ _ |-_] => destruct H
            | [H: exists _, _ |- _] => destruct H
           end).
  assert (exists conf' : configuration M, combineFunc re conf = Some conf'). 
  apply H4;auto.
  
  unfold basicPrecondition;split;auto.
  repeat (split;auto). 
  destruct H15.
   
  exists x;split;auto.   
Qed.

Lemma innerCombineFuncRaisedEvents: forall M confList (conf  conf' : configuration M) re,
    Some conf' = innerCombineFunc'''' conf confList ->
    In re (raisedevents conf') ->
    ~ In re (raisedevents conf) ->
    (exists conf'', In conf'' confList /\ In re (raisedevents conf'')).
Proof.
  intros ? confList;induction confList.
  - intros.
    simpl in H. inversion H.
  - intros. rename H1 into nre. 
    simpl in H.
    destruct confList. 
     remember (mergeConfigFunc' conf conf a). 
    destruct e;inversion H. subst.
    unfold mergeConfigFunc' in Heqe.
     remember (mergeDataStateFunc (datastate conf) (datastate conf) (datastate a) ).
    destruct e;inversion Heqe. clear H2.
    remember (mergeControlStateFunc (controlstate conf) (controlstate conf) (controlstate a)).   destruct e;inversion Heqe.
    rewrite H2 in H0;simpl in *;subst. clear Heqe. clear H.
    (* unfold mergeList' in H0.*)
     rewrite in_app_iff in H0.
     destruct H0. contradiction.
      exists a. split. left;auto.
      auto.     (*apply filterL2 in H;auto.*)

      
    
    remember (innerCombineFunc'''' conf (c::confList)).
    destruct o;inversion H. clear H2.
    remember (mergeConfigFunc' conf a c0 ).
    destruct e;inversion H;subst.
    unfold mergeConfigFunc' in Heqe.
    remember (mergeDataStateFunc (datastate conf) (datastate a) (datastate c0) ).
    destruct e;inversion Heqe. clear H2.
    remember (mergeControlStateFunc (controlstate conf) (controlstate a) (controlstate c0)).   destruct e;inversion Heqe.
    rewrite H2 in H0;simpl in *;subst. clear Heqe.
    clear H.
    (*unfold mergeList' in H0.*)
    rewrite in_app_iff in H0.
    destruct H0.
    Focus 2.     
    apply IHconfList with (re:=re) in Heqo;auto.
    destruct Heqo. exists x. 
    split. right;auto. destruct H0;auto.
    destruct H0;auto.
    exists a. split. left;auto. auto. 
Qed.







Lemma removeNotIn: forall lst re ,
    ~ In re (removeEvent' re lst). 
Proof.
  intro lst;induction lst. 
  - intros. simpl. unfold not. intros. auto.
  - intros. unfold not. intros.
    simpl in H.
    destruct (raisedEvent_dec re a). subst.
    apply IHlst with (re:=a);auto.
    simpl in H. destruct H. rewrite H in n. contradiction.
    apply IHlst with (re:=re);auto.
Qed.


Lemma removeIn: forall lst re re' ,
    In re (removeEvent' re' lst) ->
    In re lst. 
Proof.
  intro lst;induction lst. 
  - intros. simpl in H. inversion H. 
  - intros. 
    simpl in H.
    destruct (raisedEvent_dec re' a). subst.
    apply IHlst in H. right;auto.
    destruct H. subst. left;auto. 
    apply IHlst in H;auto. right;auto. 
   
Qed.




    
Lemma innerCombineFuncRaised: forall sceList M (conf : configuration M) c v  re re',
    initialConfig conf ->
    In re (raisedevents conf) ->
    incl sceList (dom (controlstate conf)) ->
    Result v = constructConfigList' sceList re conf->
    Some c = innerCombineFunc'''' conf v ->
    In re' (raisedevents c) ->
    re <> re' ->
    (exists conf', In conf' v /\ In re' (raisedevents conf')). 
Proof.
  intro sceList;induction sceList;intros. 
  - simpl in H2. inversion H2;subst. simpl in H3.  inversion H3.
  - rename H5 into reNeq. simpl in H2.
    remember (constructConfig a re conf).
    destruct e;inversion H2. clear H6.
    remember (constructConfigList' sceList re conf).
    destruct e;inversion H2. subst.
    simpl in H3.
    destruct v1. 

       remember (mergeConfigFunc' conf conf v0).
    destruct e;inversion H3. subst.
     unfold mergeConfigFunc' in Heqe1.
    remember (mergeDataStateFunc (datastate conf) (datastate conf) (datastate v0)). 
    destruct e;inversion Heqe1.
    clear H6. clear H3;clear H2.
    remember ( mergeControlStateFunc (controlstate conf) (controlstate conf)
                                     (controlstate v0)).
    destruct e;inversion Heqe1.
    rewrite H3 in H4. simpl in H4.
    rewrite in_app_iff in H4.
    destruct H4.
    assert (re = re').
    destruct H.
    repeat (match goal with
            | [H: _ /\ _ |-_] => destruct H
            | [H: exists _, _ |- _] => destruct H
            end).
    destruct ((raisedevents conf) ).   inversion H4.
    destruct l. destruct H0;destruct H2.
    rewrite H0 in H2. auto. inversion H2. inversion H0. inversion H2.
    inversion H4. rewrite H4 in reNeq. contradiction.
    (*apply filterL2 in H3.*) exists v0. split. left;auto. auto.

    remember (innerCombineFunc'''' conf (c0::v1)).
    destruct o;inversion H3;subst.
    remember (mergeConfigFunc' conf v0 c1).
    destruct e;inversion H3;subst.
    unfold mergeConfigFunc' in Heqe1.
    remember (mergeDataStateFunc (datastate conf) (datastate v0) (datastate c1)). 
    destruct e;inversion Heqe1.
    clear H7. clear H3;clear H6.
    remember ( mergeControlStateFunc (controlstate conf) (controlstate v0)
                                     (controlstate c1)).
    destruct e;inversion Heqe1.
    rewrite H5 in H4;simpl in H4.
    rewrite in_app_iff in H4.
    destruct H4. Focus 2. 
    apply IHsceList with (re:=re) (re':=re') in Heqo ;auto.
    destruct Heqo. destruct H4. exists x. split;auto. right;auto.
    unfold incl;intros;unfold incl in H1. apply H1;auto. right;auto.
     (*    apply filterL2 in H3;auto.*)
    exists v0. split. left;auto. auto.
    
Qed. 

Lemma constructConfigList'In: forall M (conf : configuration M) sceList c v ev,
    Result (c::v) =  constructConfigList' sceList ev conf->
    (exists sceList', Result v =  constructConfigList' sceList' ev conf /\ incl sceList' sceList). 
Proof. 
  intros. destruct sceList.
  simpl in H. inversion H.
  simpl in H.
  destruct (constructConfig s ev conf);inversion H.
  exists sceList.
  remember (constructConfigList' sceList ev conf).
  destruct e;inversion H. split;auto.
  unfold incl. intros. right;auto. 
Qed.

Lemma raisedEventsInternal: forall M (conf conf' : configuration M) sce re re',
    Result conf' = constructConfig sce re conf ->
    In re' (raisedevents conf') ->
    ~ In re' (raisedevents conf) ->
    (eventKind (eventDefinition re') = Internal). 
Proof.
  intros.
  rename H1 into notRaised. 
  unfold constructConfig in H.
  remember (getScenarioState sce (controlstate conf)).
  destruct o;inversion H. clear H2.
  remember ( transEvMapFunc (stateEvDefInstanceMap M) (Some s, Some (eventDefinition re))).
  destruct o;inversion H. clear H2.
  remember ( findEventInstance re (datastate conf)
                               l).
  destruct o;inversion H. clear H2.
  remember ( createValueEnv (eventArgs e) (eventParams (eventDefinition re))
                            (eventArguments re)).
  destruct e0;inversion H. clear H2.
  remember (getStep' conf sce e).
  destruct o;inversion H. clear H2.
  remember (configTransition (extendValEnv (datastate conf) v) re e sce s0 conf).
  destruct e0;inversion H. subst.
  unfold configTransition in Heqe1.
  remember ( execAction (extendValEnv (datastate conf) v, nil) 
              (stepActions s0)
              (filter
                 (fun e : event_definition =>
                  match eventKind e with
                  | Internal => true
                  | Imported => false
                  | Exported => true
                  end) (events M))).
  destruct e0;inversion Heqe1.
  destruct v1. inversion H2. rewrite H3 in H0. simpl in H0.
  apply filter_In in H0.
  destruct H0.
   destruct (eventKind (eventDefinition re'));simpl in H1;inversion H1. auto.

Qed.


Lemma raisedEventsInternal': forall M (conf conf' : configuration M) sce re re',
    Result conf' = constructConfig sce re conf ->
    In re' (raisedevents conf') ->
    (eventKind (eventDefinition re') = Internal). 
Proof.
  intros.
  unfold constructConfig in H.
  remember (getScenarioState sce (controlstate conf)).
  destruct o;inversion H. clear H2.
  remember ( transEvMapFunc (stateEvDefInstanceMap M) (Some s, Some (eventDefinition re))).
  destruct o;inversion H. clear H2.
  remember ( findEventInstance re (datastate conf)
                               l).
  destruct o;inversion H. clear H2.
  remember ( createValueEnv (eventArgs e) (eventParams (eventDefinition re))
                            (eventArguments re)).
  destruct e0;inversion H. clear H2.
  remember (getStep' conf sce e).
  destruct o;inversion H. clear H2.
  remember (configTransition (extendValEnv (datastate conf) v) re e sce s0 conf).
  destruct e0;inversion H. subst.
  unfold configTransition in Heqe1.
  remember ( execAction (extendValEnv (datastate conf) v, nil) 
              (stepActions s0)
              (filter
                 (fun e : event_definition =>
                  match eventKind e with
                  | Internal => true
                  | Imported => false
                  | Exported => true
                  end) (events M))).
  destruct e0;inversion Heqe1.
  destruct v1. inversion H2. rewrite H3 in H0. simpl in H0.
  apply filter_In in H0.
  destruct H0.
   destruct (eventKind (eventDefinition re'));simpl in H1;inversion H1. auto.
Qed.

Lemma chainMergeRuleImport: forall M (conf conf' : configuration M) e,
    chainMerge conf conf' e ->
    eventKind (eventDefinition e) = Imported. 
Proof. 
  intros.
  induction H. subst. 
  unfold synchrony in H0.
  destruct H.
  
         repeat (match goal with
            | [H: _ /\ _ |-_] => destruct H
            | [H: exists _, _ |- _] => destruct H
               end).
         apply H3 in H0.
         destruct H0.
   unfold importedEvent in H0.          
   destruct (eventKind (eventDefinition event));inversion H0;auto.       
  auto. 
Qed.

Lemma chainMergeRuleImportIn: forall M (conf conf' : configuration M) e,
    chainMerge conf conf' e ->
    eventKind (eventDefinition e) = Imported /\ In e (raisedevents conf). 
Proof. 
  intros. split.
  apply chainMergeRuleImport with (conf:=conf) (conf':=conf');auto. 
  induction H. subst. 
  unfold synchrony in H0. destruct H0;auto. auto. 
  
Qed.

Lemma mergeConfigFuncRaisedEvent: forall M (conf : configuration M) c1 c2 v re,
    Result v = mergeConfigFunc' conf c1 c2 ->
    In re (raisedevents v) ->
    ~ In re (raisedevents conf) ->
    (In re (raisedevents c1) \/ In re (raisedevents c2)). 
Proof.
  intros.
  unfold mergeConfigFunc' in H.
  remember (mergeDataStateFunc (datastate conf) (datastate c1) (datastate c2) ).
  destruct e;inversion H. clear H3.
  remember (mergeControlStateFunc (controlstate conf) (controlstate c1) (controlstate c2)).
  destruct e;inversion H. rewrite H3 in H0. simpl in H0.
  (*unfold mergeList' in H0.*)
  apply in_app_iff in H0.
  destruct H0.
  left;auto.
  (*  apply filterL2 in H0.*) right;auto.
Qed.

Lemma raisedEventNoImported: forall M (conf conf' : configuration M) re,
    chainMerge conf conf' re ->
    (forall re', In re' (raisedevents conf') -> eventDefinition re <> eventDefinition re').
Proof.
  intros.
  induction H.
  
  - rename event into ev.  unfold synchrony in H1.
   
    destruct H1.
    unfold combineFunc in H2.
    remember (constructConfigList (dom (controlstate conf)) ev conf).
    destruct e;inversion H2.
    clear H4.
    unfold constructConfigList in Heqe.
    destruct v;inversion H2.
    clear H2.

    destruct v.
    
       remember ( mergeConfigFunc' conf conf c).
       destruct e;inversion H4.
       unfold removeEventFromConf in H3.
       rewrite <- H3 in H0. simpl in H0.

         assert (ev <> re').
    pose proof removeNotIn.
    assert (~In ev ((removeEvent' ev (raisedevents v)))).
    apply H2;auto.
    unfold not. intros.
    rewrite <- H6 in H0. contradiction.
    

    unfold mergeConfigFunc' in Heqe0.
    remember (mergeDataStateFunc (datastate conf) (datastate conf) (datastate c) ).
    destruct e;inversion Heqe0.
    remember ( mergeControlStateFunc (controlstate conf) (controlstate conf) (controlstate c)).
    destruct e;inversion Heqe0. rewrite H7 in H0. simpl in H0.
    apply removeIn in H0.
    rewrite in_app_iff in H0.
    destruct H0. 

    assert (ev = re').
    destruct H. 
       repeat (match goal with
            | [H: _ /\ _ |-_] => destruct H
            | [H: exists _, _ |- _] => destruct H
               end).
       destruct ((raisedevents conf)).   inversion H1.
       destruct l. destruct H1. destruct H0. rewrite H0 in H1;auto.
       inversion H0. inversion H1. inversion H5. rewrite H5 in H2.
       contradiction.

       (*apply filterL2 in H0.*)

    pose proof termL2.
    assert (exists sce : scenario, In sce (filter
              (fun x : scenario =>
               inList event_definition_dec (eventDefinition ev) (alphabet x))
              (filterList (finishedscenarios conf) (dom (controlstate conf))
                          scenario_dec)) /\ Result c = constructConfig sce ev conf).
    apply H5 with (lst:=c::nil);auto.   split;auto.  left;auto.
    destruct H8.
    destruct H8.
    pose proof raisedEventsInternal.
    assert (eventKind (eventDefinition re') = Internal).
    apply H10 with (conf':=c) (conf:=conf) (sce:=x) (re:=ev);auto.
     unfold not. intros.
    assert (ev = re').
    destruct H. 
       repeat (match goal with
            | [H: _ /\ _ |-_] => destruct H
            | [H: exists _, _ |- _] => destruct H
               end).
       destruct ((raisedevents conf)).   inversion H11.
       destruct l. destruct H1. destruct H11. rewrite H11 in H1;auto.
       inversion H11. inversion H1. inversion H12. rewrite H12 in H2.
       contradiction.

        assert (eventKind (eventDefinition ev) = Imported).
        destruct H. 
       repeat (match goal with
            | [H: _ /\ _ |-_] => destruct H
            | [H: exists _, _ |- _] => destruct H
               end).
       apply H13 in H1.
       destruct H1.
       unfold importedEvent in H1.
       destruct (eventKind (eventDefinition ev) );inversion H1. auto.
       unfold not. intros.
       rewrite H13 in H12. rewrite H12 in H11. inversion H11.

    
    remember (innerCombineFunc'''' conf (c0::v)).
    destruct o;inversion H4.
    clear H4.
    remember ( mergeConfigFunc' conf c c1).
    destruct e;inversion H3. subst. clear H3.
    unfold removeEventFromConf in H0.
    simpl in H0.
    assert (In re' (raisedevents v0)). 
    apply removeIn with (re':=ev);auto. 
    unfold mergeConfigFunc' in Heqe0.
    remember (mergeDataStateFunc (datastate conf) (datastate c) (datastate c1) ).
    destruct e;inversion Heqe0.
    remember ( mergeControlStateFunc (controlstate conf) (controlstate c) (controlstate c1)).
    destruct e;inversion Heqe0. rewrite H5 in H2. simpl in H2.
    rewrite in_app_iff in H2.
    destruct H2. Focus 2. 
    assert (ev <> re').
    pose proof removeNotIn.
    assert (~In ev ((removeEvent' ev (raisedevents v0)))).
    apply H3;auto.
    unfold not. intros.
    rewrite <- H7 in H0. contradiction.
    pose proof innerCombineFuncRaised.
    pose proof constructConfigList'In.
    assert (exists sceList' : list scenario, Result (c0::v) = constructConfigList' sceList' ev conf /\ incl sceList' ((filter
              (fun x : scenario =>
               inList event_definition_dec (eventDefinition ev) (alphabet x))
              (filterList (finishedscenarios conf) (dom (controlstate conf))
                 scenario_dec)))).  
    apply H7 with (c:=c);auto.           
    destruct H8. destruct H8.
    
    assert (exists conf' : configuration M, In conf' (c0::v) /\ In re' (raisedevents conf')).
    
    apply H6 with (sceList:=x) (conf:=conf) (c:=c1) (re:=ev);auto.
    unfold incl in H9.
    unfold incl. intros.
    apply H9 in H10.
    apply filter_In in H10.
    destruct H10.
    apply filterL2 in H10;auto. 
    destruct H10. destruct H10.
    pose proof termL2.
    assert ( exists sce : scenario, In sce x /\ Result x0 =  constructConfig sce ev conf).    apply H12 with (lst:=(c0::v));auto.
    destruct H13. destruct H13.
    pose proof raisedEventsInternal.
    assert (eventKind (eventDefinition re') = Internal).
    apply H15 with (conf':=x0) (conf:=conf) (sce:=x1) (re:=ev);auto.
    unfold not. intros.
    assert (ev = re').
    destruct H. 
       repeat (match goal with
            | [H: _ /\ _ |-_] => destruct H
            | [H: exists _, _ |- _] => destruct H
               end).
       destruct ((raisedevents conf)).   inversion H16.
       destruct l. destruct H1. destruct H16. rewrite H16 in H1;auto.
       inversion H16. inversion H1. inversion H17. rewrite H17 in H3.
       contradiction.
       assert (eventKind (eventDefinition ev) = Imported).
        destruct H. 
       repeat (match goal with
            | [H: _ /\ _ |-_] => destruct H
            | [H: exists _, _ |- _] => destruct H
               end).
       apply H18 in H1.
       destruct H1.
       unfold importedEvent in H1.
       destruct (eventKind (eventDefinition ev) );inversion H1. auto.
       unfold not. intros.
       rewrite H18 in H17. rewrite H17 in H16. inversion H16.
      assert (ev <> re').
    pose proof removeNotIn.
    assert (~In ev ((removeEvent' ev (raisedevents v0)))).
    apply H3;auto.
    unfold not. intros.
    rewrite <- H7 in H0. contradiction.
    pose proof termL2.
    assert (exists sce : scenario, In sce (filter
              (fun x : scenario =>
               inList event_definition_dec (eventDefinition ev) (alphabet x))
              (filterList (finishedscenarios conf) (dom (controlstate conf))
                          scenario_dec)) /\ Result c = constructConfig sce ev conf).
    apply H6 with (lst:=c::c0::v);auto.   split;auto.  left;auto.
    destruct H7.
    destruct H7.
    pose proof raisedEventsInternal.
    assert (eventKind (eventDefinition re') = Internal).
    apply H9 with (conf':=c) (conf:=conf) (sce:=x) (re:=ev);auto.
     unfold not. intros.
    assert (ev = re').
    destruct H. 
       repeat (match goal with
            | [H: _ /\ _ |-_] => destruct H
            | [H: exists _, _ |- _] => destruct H
               end).
       destruct ((raisedevents conf)).   inversion H10.
       destruct l. destruct H1. destruct H10. rewrite H10 in H1;auto.
       inversion H10. inversion H1. inversion H11. rewrite H11 in H3.
       contradiction.

        assert (eventKind (eventDefinition ev) = Imported).
        destruct H. 
       repeat (match goal with
            | [H: _ /\ _ |-_] => destruct H
            | [H: exists _, _ |- _] => destruct H
               end).
       apply H12 in H1.
       destruct H1.
       unfold importedEvent in H1.
       destruct (eventKind (eventDefinition ev) );inversion H1. auto.
       unfold not. intros.
       rewrite H12 in H11. rewrite H11 in H10. inversion H10.

       

  -  pose proof chainMergeRuleImport.
     rename H2 into chainImport.
     assert (eventKind (eventDefinition event1) = Imported).
     apply chainImport with (conf:=conf) (conf':=conf');auto.
     rename H2 into evImport. 
     assert (In re'  (raisedevents conf')  \/ ~ (In re'  (raisedevents conf'))). 
     apply excluded_middle.
     destruct H2. apply IHchainMerge in H2;auto.
     unfold synchrony in H1.
     destruct H1.
     unfold combineFunc in H3.
     remember (constructConfigList (dom (controlstate conf')) event2 conf'). 
     destruct e;inversion H3.
     destruct v;inversion H3. clear H5.
     clear IHchainMerge.
     clear H3.

     destruct v.
     
       remember (mergeConfigFunc' conf' conf' c).
     destruct e;inversion H6.
     unfold removeEventFromConf in H4.
     rewrite <- H4 in H0.
     simpl in H0.
     apply removeIn in H0.
     pose proof mergeConfigFuncRaisedEvent.
     assert (In re' (raisedevents conf') \/ In re' (raisedevents c)).
     apply H3 with (v:=v) (conf:=conf');auto.
     destruct H5. contradiction.

      unfold constructConfigList in Heqe.
     pose proof termL2.
     assert (exists sce : scenario, In sce (filter
              (fun x : scenario =>
               inList event_definition_dec (eventDefinition event2) (alphabet x))
              (filterList (finishedscenarios conf') (dom (controlstate conf'))
                          scenario_dec)) /\ Result c = constructConfig sce event2 conf').
     apply H7 with (lst:=c::nil);auto. split;auto. left;auto.
     destruct H8;destruct H8.
     pose proof raisedEventsInternal.
     assert (eventKind (eventDefinition re') = Internal).
     apply H10 with (conf:=conf') (conf':=c) (sce:=x) (re:=event2);auto.
     unfold not;intros. rewrite <- H12 in H11. rewrite evImport in H11;inversion H11.


     
     
     remember (innerCombineFunc'''' conf' (c0::v)).
     destruct o;inversion H6.
     remember (mergeConfigFunc' conf' c c1).
     destruct e;inversion H4.
     unfold removeEventFromConf in H5.
     rewrite <- H5 in H0. simpl in H0.
     apply removeIn in H0.
     pose proof mergeConfigFuncRaisedEvent.
     assert (In re' (raisedevents c) \/ In re' (raisedevents c1)).
     apply H3 with (conf:=conf') (v:=v0);auto.
     destruct H7. Focus 2. 
     pose proof innerCombineFuncRaisedEvents.
     assert (exists conf'' : configuration M, In conf'' (c0::v) /\ In re' (raisedevents conf'')). 
     apply H8 with (conf:=conf') (conf':=c1);auto.
     destruct H9.
     destruct H9.
     unfold constructConfigList in Heqe.
     pose proof termL2.
     assert (exists sce : scenario, In sce (filter
              (fun x : scenario =>
               inList event_definition_dec (eventDefinition event2) (alphabet x))
              (filterList (finishedscenarios conf') (dom (controlstate conf'))
                          scenario_dec)) /\ Result x = constructConfig sce event2 conf').
     apply H11 with (lst:=c::c0::v);auto.      split;auto. right;auto.
     destruct H12. destruct H12.
     pose proof raisedEventsInternal.
     assert (eventKind (eventDefinition re') = Internal).
     apply H14 with (conf:=conf') (conf':=x) (sce:=x0) (re:=event2);auto.
     unfold not;intros. rewrite <- H16 in H15. rewrite evImport in H15;inversion H15. 
     unfold constructConfigList in Heqe.
     pose proof termL2.
     assert (exists sce : scenario, In sce (filter
              (fun x : scenario =>
               inList event_definition_dec (eventDefinition event2) (alphabet x))
              (filterList (finishedscenarios conf') (dom (controlstate conf'))
                          scenario_dec)) /\ Result c = constructConfig sce event2 conf').
     apply H8 with (lst:=c::c0::v);auto. split;auto. left;auto.
     destruct H9;destruct H9.
     pose proof raisedEventsInternal.
     assert (eventKind (eventDefinition re') = Internal).
     apply H11 with (conf:=conf') (conf':=c) (sce:=x) (re:=event2);auto.
     unfold not;intros. rewrite <- H13 in H12. rewrite evImport in H12;inversion H12. 
Qed.


Lemma initialConfigRaisedSingle: forall M (conf : configuration M) re re',
    initialConfig conf ->
    In re (raisedevents conf) ->
    re <> re' ->
    ~In re' (raisedevents conf). 
Proof. 
  intros.
  destruct H.
  destruct H2.
  unfold not.
  intros.
  apply H1.
  destruct (raisedevents conf). inversion H2.
  destruct l. destruct H0;destruct H4;inversion H4;inversion H0.  rewrite H4 in H0;auto.
  inversion H2. 
Qed.

 

Lemma getEventId: forall lst id  e,
    Some e = getEventByName id lst ->
    id = eventId e. 
Proof. intro lst;induction lst. 
       - intros. simpl in H. inversion H. 
       - intros. simpl in H.
         destruct (string_dec (eventId a) id).
         inversion H;subst. auto.
         apply IHlst in H;auto.
Qed.

Lemma execActionRaisingEvent: forall actList env l env' l' re  eventList,
    Result (env',l') = execAction (env, l) actList eventList ->
    ~ In re l ->
    In re l' ->
    exists (act : action) (exprs : list expr),
    In act (transitionIntoBasicActionList actList) /\
    act = RaiseStmt (eventId (eventDefinition re)) exprs.
Proof.
  intro actList;induction actList.
  - intros;simpl in *. inversion H;simpl in *. subst. contradiction. 
  - intros. simpl in H.
    destruct l;inversion H.    clear H3.
    destruct a;inversion H. clear H3.
    destruct (evalMonad env e);inversion H. clear H3. 
    destruct ( updateValueEnvInv (AIdent s) v env ).
    inversion H;subst. contradiction.
    inversion H. 
  - intros.
    exists ((RaiseStmt ident exprs)).
    exists exprs. 
    simpl in H.
    remember (calculateExprList env exprs).
    destruct e;inversion H. clear H3.
    remember (getEventByName ident eventList).
    destruct o;inversion H.
    remember (parameterMatchFunc v (eventParams e)).
    destruct b;inversion H. 
    rewrite H5 in H1.
    destruct H1. Focus 2. contradiction.
    rewrite <- H1. simpl.
    
    split. left;auto.
    rewrite getEventId with (id:=ident) (e:=e) (lst:=eventList);auto.
  -
    intros.
    simpl in H. 
    remember (execAction (env, l) actList1 eventList).
    destruct e;inversion H.
    destruct v.
    simpl.
    assert (In re l0 \/ ~ In re l0).
    apply excluded_middle.
    destruct H2. 
    apply IHactList1 with (re:=re) in Heqe;auto.
    destruct Heqe.
    destruct H4.
    destruct H4.
    exists x.
    exists x0.
    split;auto.
    apply in_app_iff. left;auto.
    apply IHactList2 with (re:=re) in H;auto.
    destruct H.
    destruct H.
    destruct H.
    exists x. exists x0. split;auto. 
    apply in_app_iff. right;auto.
Qed.



Lemma constructConfigRaised: forall M (conf conf' : configuration M) re re' sce,
    Result conf' = constructConfig sce re conf ->
    ~ In re' (raisedevents conf) ->
    In re' (raisedevents conf') ->  
    transEvMapProp M ->
    stpStMapEquiv' M ->
    correctStateEvStepMap' M ->
    stateEvDefInstanceMapEquiv M ->
     In sce (dom (controlstate conf)) ->
    exists (tr : step) (act : action) (exprs : list expr),
    In tr (getTransitionsOfScenario sce) /\
    In act (transitionIntoBasicActionList (stepActions tr)) /\
    act = RaiseStmt (eventId (eventDefinition re')) exprs /\
    eventDefinition re = event (stepEvent tr).
Proof.
  
  intros.
  rename H2 into evMapProp. rename H3 into mapEquiv. rename H4 into stpMap. rename H5 into stMapEq. rename H6 into sceCon. 
  unfold constructConfig in H.
  remember (getScenarioState sce (controlstate conf)).
  destruct o;inversion H;clear H3.
  remember (transEvMapFunc (stateEvDefInstanceMap M) (Some s, Some (eventDefinition re))).
  destruct o;inversion H;clear H3.
  remember (findEventInstance re (datastate conf)
           l).
  destruct o;inversion H;clear H3.
  remember (createValueEnv (eventArgs e) (eventParams (eventDefinition re))
           (eventArguments re)).
  destruct e0;inversion H;clear H3.
  remember (getStep' conf sce e).
  destruct o;inversion H;clear H3.
  remember (configTransition (extendValEnv (datastate conf) v) re e sce s0 conf ).
  destruct e0;inversion H;clear H3.
  unfold configTransition in Heqe1.
  inversion H;subst. clear H.
  remember ( execAction (extendValEnv (datastate conf) v, nil) 
              (stepActions s0)
              (filter
                 (fun e : event_definition =>
                  match eventKind e with
                  | Internal => true
                  | Imported => false
                  | Exported => true
                  end) (events M))).
  destruct e0;inversion Heqe1.
  destruct v1. clear H2.
  inversion Heqe1. rewrite H2 in H1. simpl in H1.
  clear H2.

  
  apply filter_In in H1. destruct H1. 
  Check execActionRaisingEvent. 
  (*apply in_app_iff in H1.
  destruct H1. Focus 2.
  apply removeIn in H.
  contradiction.
  apply filter_In in H.
  destruct H.*)
  pose proof execActionRaisingEvent.
  assert (exists (act : action) (exprs : list expr),
         In act (transitionIntoBasicActionList (stepActions s0)) /\
         act = RaiseStmt (eventId (eventDefinition re')) exprs).
  eapply H2;auto. apply Heqe2. unfold not. intros. inversion H3. auto.
  exists s0.
  destruct H3. destruct H3.
  exists x. exists x0.
  destruct H3.

  
  unfold stateEvDefInstanceMapEquiv in stMapEq.
  unfold correctStateEvStepMap' in stpMap.
  unfold stpStMapEquiv' in mapEquiv.
  unfold transEvMapProp in evMapProp. 

  
  unfold getTransitionsOfScenario.
  
  split;auto.


  
  Focus 2. split;auto. split;auto.
  assert (event e = eventDefinition re).
  
  apply findEventInstanceIn in Heqo1;auto.
  symmetry in Heqo0. apply semantic_rules.stateEvDefInstanceMapEquiv' in Heqo0;auto.
  Focus 2.
  destruct stMapEq;auto. 
 (* remember  (transEvMap (Some s, Some (eventDefinition re))).
  symmetry in Heql0. 
  rewrite <- stMapEq in Heql0.*)
  eapply evMapProp. apply Heqo0. auto.

  
  
  apply getStepMap' with (s:=s) in Heqo2;auto.
  
  symmetry in Heqo2.
  apply stpStMapEquivLem in Heqo2;auto. 
   remember Heqo2. clear Heqi. 
  apply stpMap in Heqo2.
  destruct Heqo2. destruct H7. rewrite H7. auto.
 
  
  remember Heqo. clear Heqe3. 
  apply inControlState in Heqo;auto.


  
  apply findEventInstanceIn in Heqo1.
  (*remember  (transEvMap (Some s, Some (eventDefinition re))).
  symmetry in Heql0. *)
   apply getStepMap' with (s:=s) in Heqo2;auto.
 
  symmetry in Heqo2. 
   apply stpStMapEquivLem in Heqo2;auto. 
  apply  stpMap  with (sce:=sce) in Heqo2;auto.
  destruct Heqo2;auto. 
Qed. 


(*
cs_state_consist : forall (sce : scenario) (st : scenario_state) 
                       (e0 : event_instance) (s0 : step),
                     In (sce, st) (controlstate conf) ->
                     In (st, e0, Some s0) (stateEvStepMap M) ->
                     In s0 (traces sce) /\ pre_state s0 = st
 *)

(*
Lemma constructConfigCSState: forall conf conf' sce re,
    (forall (sce : scenario) (st : scenario_state) 
                       (e0 : event_instance) (s0 : step),
                     In (sce, st) (controlstate conf) ->
                     In (st, e0, Some s0) (stateEvStepMap M) ->
                     In s0 (traces sce) /\ pre_state s0 = st) ->
    Result conf' = constructConfig sce re conf ->
    (forall (sce : scenario) (st : scenario_state) 
                       (e0 : event_instance) (s0 : step),
                     In (sce, st) (controlstate conf') ->
                     In (st, e0, Some s0) (stateEvStepMap (monitor_obj conf')) ->
                     In s0 (traces sce) /\ pre_state s0 = st). 
Proof. intros. 
       SearchAbout traces.
       Print correct_configuration. 
       apply H with e0. 
 *)




Lemma domControlSyncChain: forall M (conf conf' : configuration M) e,  chainMerge conf conf' e ->  (dom (controlstate conf)) = (dom (controlstate conf')).
Proof. intros.
       induction H.
       - apply domControlSync with (e:=event);auto.
       - apply domControlSync in H0. rewrite H0 in IHchainMerge;auto. 

Qed.


Lemma chainMergeInitial: forall M (conf conf' : configuration M) e,
    chainMerge conf conf' e ->
    initialConfig conf. 
Proof.
  intros.
  induction H. auto. 
  auto. 
Qed.                                







Lemma monitorObjNoChangeChain: forall M (conf conf' : configuration M) e,
    chainMerge conf conf' e ->
    M = M. 
Proof. reflexivity. Qed.

Print initialConfig. 
      
Lemma raisedEventLedTo: forall M (conf conf' : configuration M) re,
    chainMerge conf conf' re ->
    transEvMapProp M ->
    stpStMapEquiv' M ->
    correctStateEvStepMap' M ->
    stateEvDefInstanceMapEquiv M ->
    (forall re', In re' (raisedevents conf') -> staticEventLeadTo M (eventDefinition re) (eventDefinition re')).
Proof.
  intros. 
  rename H0 into evMapProp. rename H1 into mapEquiv. rename H2 into stpMap. rename H3 into stMapEq.
  rename H4 into H0.
  generalize dependent re'. 
  induction H. 
  rename event into ev. 
  - intros.
    rename H0 into tempH.
    rename H1 into H0.
    rename tempH into H1. 
    apply staticLeadBasicCase.
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
    apply staticLeadTransit with (ev2:=eventDefinition event2);auto.
    apply IHchainMerge;auto.
    unfold synchrony in H0. destruct H0;auto.
    apply staticLeadBasicCase.
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
    pose proof constructConfigRaised. exists x. remember H.  clear Heqc0. split.
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
    pose proof constructConfigRaised. exists x. split.
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

Lemma rangeApp: forall (A:Type) (B: Type) (env env': list (A*B)),
range (env ++ env') = range env ++ range env'.
Proof. intros A B env.
induction env.
- intros. simpl. auto.
- intros. simpl. f_equal. apply IHenv.
Qed.



Lemma filterListNil: forall l,
    l = filterList nil l scenario_dec.
Proof. intro l;induction l. 
       simpl;auto.
  simpl.   f_equal;auto. 
Qed.

Print syncProgress.



(* jww (2018-01-06): Teng, can you please complete this new proof? *)

Lemma filterListIncl: forall A l2 l1 (p: forall n m: A, {n = m} + { n <> m}),
    filterList l1 l2 p = nil ->
    incl l2 l1. 
Proof.
   intros A l2;induction l2. 
   - intros.
     unfold incl. intros. inversion H0. 
     
   - intros. simpl in H.
     remember (inList p a l1).
     destruct b.
    
     symmetry in Heqb.  SearchAbout inList.
     apply reverseinListLemma in Heqb. unfold incl. intros.
     apply IHl2 in H. unfold incl in H.
     destruct H0. subst. auto. 
     apply H. auto. inversion H. 
Qed.
     


Lemma getEventIn: forall l f e ident,
    Some e = getEventByName ident (filter f l) ->
    In e l.
Proof.
  intro l;induction l. 
  - intros. simpl in H. inversion H.
  - intros. simpl in H.
    destruct (f a);subst.
    simpl in H.
    destruct (string_dec (eventId a) ident).
    inversion H;left;auto.
    apply IHl in H. right;auto.
    apply IHl in H. right;auto. 
Qed.


Lemma execActionEvents: forall actions l v  v' l' ll f re ,
    Result (v', l') =  execAction (v,l) actions
                                  (filter
                                     f ll) ->
    ~ In re l ->
    In re l' ->
    In (eventDefinition re) ll. 
Proof.       
  intro actions;induction actions.
    - intros;simpl in *. inversion H;subst. contradiction. 
    - intros.
      simpl in H. 
      destruct l;inversion H. clear H3.
      destruct a;inversion H;subst.
      remember (evalMonad v e ).
      destruct e0;inversion H.
      destruct (updateValueEnvInv (AIdent s) v0 v );inversion H.
      subst. contradiction.
    - intros.
      simpl in H.
      remember (calculateExprList v exprs).
      destruct e;inversion H.
      remember (getEventByName ident (filter f ll)).
      destruct o;inversion H3. subst.
      remember (parameterMatchFunc v0 (eventParams e)).
      destruct b;inversion H3. subst. 
      simpl in H1. destruct H1.
      rewrite <- H1. simpl.
      Focus 2. contradiction.
      SearchAbout getEventByName.
      Print getEventByName.
      apply getEventIn in Heqo;auto.
    - intros.
      simpl in H.
      remember (execAction (v, l) actions1 (filter f ll)).
      destruct e;inversion H.
      destruct v0.
      assert (In re l0 \/ ~ In re l0).
      apply excluded_middle;auto.
      destruct H2.
      apply IHactions1 with (re:=re) in Heqe;auto.

            apply IHactions2 with (re:=re) in H;auto.
Qed.

Lemma constructConfigEvents: forall M (conf conf' : configuration M) re re' sce,
    Result conf' = constructConfig sce re conf ->
    ~ In re' (raisedevents conf) ->
    In re' (raisedevents conf') ->
    In (eventDefinition re') (events M). 
Proof.
  intros.
  unfold constructConfig in H.
  remember (getScenarioState sce (controlstate conf)).
  destruct o;inversion H.
  remember (transEvMapFunc (stateEvDefInstanceMap M) (Some s, Some (eventDefinition re)) ).
  destruct o;inversion H. 
  remember ( findEventInstance re (datastate conf) l).
  destruct o;inversion H.
  remember ( createValueEnv (eventArgs e) (eventParams (eventDefinition re)) (eventArguments re)). 
  destruct e0;inversion H.
  remember (getStep' conf sce e ).
  destruct o;inversion H5. clear H5;clear H6. clear H3;clear H4.
  remember (configTransition (extendValEnv (datastate conf) v) re e sce s0 conf).
  destruct e0;inversion H. subst.
  unfold configTransition in Heqe1.
  remember (execAction (extendValEnv (datastate conf) v, nil) (stepActions s0)
              (filter
                 (fun e : event_definition =>
                  match eventKind e with
                  | Internal => true
                  | Imported => false
                  | Exported => true
                  end) (events M))). 
  destruct e0;inversion Heqe1.
  destruct v1. clear H3. inversion Heqe1;subst. simpl in H1.
  (*
  apply in_app_iff in H1.  destruct H1. Focus 2.
  SearchAbout removeEvent'.  apply removeIn in H1. contradiction.*)
  apply filter_In in H1. destruct H1. clear H. clear Heqe1.
  Check execAction.
  remember ((eventKind (eventDefinition re'))).
  destruct e0;subst. Focus 2. simpl in H2. inversion H2. 
  Focus 2. simpl in H2. inversion H2.
  pose proof execActionEvents.
  eapply H;auto. apply Heqe2. unfold not. intros. inversion H3. auto. 
Qed.

Lemma syncFinish: forall M (conf conf' : configuration M) sce re,
    correct_configuration conf ->
    synchrony conf conf' re ->
    ~ In sce (finishedscenarios conf) ->
    In sce (finishedscenarios conf') ->
    In (eventDefinition re) (alphabet sce).
Proof.
  intros.
  unfold synchrony in H0.
  destruct H0.
  unfold combineFunc in H3.
  remember ( constructConfigList (dom (controlstate conf)) re conf).
  destruct e;inversion H3.
  destruct v;inversion H3. clear H5. clear H3.
 

   destruct v. 
   remember (mergeConfigFunc' conf conf c).
  destruct e;inversion H6.
  unfold removeEventFromConf in H4.
  rewrite <- H4 in H2. simpl in H2.
 unfold mergeConfigFunc' in Heqe0.
  destruct (mergeDataStateFunc (datastate conf) (datastate conf) (datastate c));inversion Heqe0. 
  destruct (mergeControlStateFunc (controlstate conf) (controlstate conf) (controlstate c));inversion H5.
  rewrite H7 in H2;simpl in H2.
  apply in_app_iff in H2.  clear H7. clear H5. clear H4. 
  clear Heqe0.
  destruct H2. contradiction. 
   pose proof termL2.
  unfold constructConfigList in Heqe. 
  assert (exists sce : scenario, In sce (filter
              (fun x : scenario => inList event_definition_dec (eventDefinition re) (alphabet x))
              (filterList (finishedscenarios conf) (dom (controlstate conf)) scenario_dec)) /\ Result c = constructConfig sce re conf). 
  apply H3 with (lst:=c::nil);auto.
  split;auto. left;auto.
  destruct H4.
  destruct H4.
  apply filter_In in H4.
  destruct H4.
  apply termL3 in H5. rewrite H5 in H2. inversion H2.
  subst.
  apply reverseinListLemma in H7;auto.
  inversion H8.

  remember (innerCombineFunc'''' conf (c0 :: v)).
  destruct o;inversion H6.
  remember (mergeConfigFunc' conf c c1).
  destruct e;inversion H4.
  unfold removeEventFromConf in H5.
  rewrite <- H5 in H2. simpl in H2.
  unfold mergeConfigFunc' in Heqe0.
  destruct (mergeDataStateFunc (datastate conf) (datastate c) (datastate c1));inversion Heqe0. 
  destruct (mergeControlStateFunc (controlstate conf) (controlstate c) (controlstate c1));inversion H7.
  rewrite H8 in H2;simpl in H2.
  apply in_app_iff in H2. clear H8. clear H7. clear H5.
  clear Heqe0.
  destruct H2.
  Focus 2.  
  pose proof finishedscenarioInAll.
   unfold constructConfigList in Heqe.
  remember ((filter
              (fun x : scenario => inList event_definition_dec (eventDefinition re) (alphabet x))
              (filterList (finishedscenarios conf) (dom (controlstate conf)) scenario_dec))).
  destruct l.  simpl in Heqe. inversion Heqe.
  simpl in Heqe.
  remember (constructConfig s re conf).
  destruct e;inversion Heqe.
  remember (constructConfigList' l re conf).
  destruct e;inversion Heqe.
  subst. 
  assert (In sce l \/ In sce (finishedscenarios conf)).
  apply H3 with (e:=re) (v:=c0::v) (c:=c1);auto.
  Focus 3.
  destruct H5.
  pose proof termL2'.
  assert ( exists conf' : configuration M, Result conf' = constructConfig sce re conf). 
  apply H8 with (scs:=l) (lst:=c0::v);auto.
  destruct H9.
  assert (In sce ( filter
           (fun x : scenario => inList event_definition_dec (eventDefinition re) (alphabet x))
           (filterList (finishedscenarios conf) (dom (controlstate conf)) scenario_dec))).
  rewrite <- Heql. right;auto. 
  apply filter_In in H10.
  destruct H10.
  apply reverseinListLemma in H11. auto.
  contradiction.
  assert (uniqList (s::l)).
  rewrite Heql.
  apply filterUniq;auto.
  apply uniqListFilter;auto.
  destruct H;auto.
  destruct H;auto. inversion H5;auto.
  assert (incl (filter
           (fun x : scenario => inList event_definition_dec (eventDefinition re) (alphabet x))
           (filterList (finishedscenarios conf) (dom (controlstate conf)) scenario_dec)) (dom (controlstate conf))).
  unfold incl. intros.
  apply filter_In in H5.
  destruct H5. apply filterL2 in H5;auto.
  rewrite <- Heql in H5.
  unfold incl. intros.
  unfold incl in H5.
  apply H5;right;auto.
  pose proof termL2.
  unfold constructConfigList in Heqe. 
  assert (exists sce : scenario, In sce (filter
              (fun x : scenario => inList event_definition_dec (eventDefinition re) (alphabet x))
              (filterList (finishedscenarios conf) (dom (controlstate conf)) scenario_dec)) /\ Result c = constructConfig sce re conf). 
  apply H3 with (lst:=c::c0::v);auto.
  split;auto. left;auto.
  destruct H5.
  destruct H5.
  apply filter_In in H5.
  destruct H5.
  apply termL3 in H7. rewrite H7 in H2. inversion H2.
  subst.
  apply reverseinListLemma in H8;auto.
  inversion H9.
 
Qed.



    

Lemma finishedScenarioInEventMap: forall sce re M (conf : configuration M) x,
    Result x = constructConfig sce re conf ->
    sceEventMap x =  (sce, eventDefinition re)::nil.
Proof.
  intros.
  unfold constructConfig in H.
  remember (getScenarioState sce (controlstate conf)).
  destruct o;inversion H.
  remember (transEvMapFunc (stateEvDefInstanceMap M) (Some s, Some (eventDefinition re))).
  destruct o;inversion H.
  remember ( findEventInstance re (datastate conf) l).
  destruct o;inversion H.
  remember (createValueEnv (eventArgs e) (eventParams (eventDefinition re)) (eventArguments re)). 
  destruct e0;inversion H2.
  remember (getStep' conf sce e).
  destruct o;inversion H.
  remember (configTransition (extendValEnv (datastate conf) v) re e sce s0 conf ).
  destruct e0;inversion H4. subst.
  unfold configTransition in Heqe1.
  destruct (  execAction (extendValEnv (datastate conf) v, nil) (stepActions s0)
              (filter
                 (fun e : event_definition =>
                  match eventKind e with
                  | Internal => true
                  | Imported => false
                  | Exported => true
                  end) (events M)));inversion Heqe1.
  destruct v1. inversion H6;subst;simpl;auto. 
Qed.

Print mergeConfigFunc'.


Lemma mergeConfigEventMap: forall M (conf conf1 conf2 conf' : configuration M) e sce,
    Result conf' = mergeConfigFunc' conf conf1 conf2 ->
    In (sce,e) (sceEventMap conf1) \/ In (sce,e) (sceEventMap conf2) <->
    In (sce,e) (sceEventMap conf'). 
Proof.
  intros.
  
  unfold mergeConfigFunc' in H.
  destruct (mergeDataStateFunc (datastate conf) (datastate conf1) (datastate conf2));inversion H. 
  destruct (mergeControlStateFunc (controlstate conf) (controlstate conf1) (controlstate conf2));inversion H.
  simpl.
  split.
  intros.
  apply in_app_iff.
  destruct H0. left;auto. right;auto.
  intros.
  apply in_app_iff in H0.
  destruct H0. left;auto. right;auto. 
Qed.



(*innerCombineNoErr*)
Lemma constructConfigListMap: forall lst e sce M (conf : configuration M) v c,
    correct_configuration conf ->
    noMergeError' M ->
    basicPrecondition conf e ->
    uniqList lst ->
    incl lst (dom (controlstate conf)) ->
    In sce lst ->
    Result v = constructConfigList' lst e conf ->
    Some c = innerCombineFunc'''' conf v ->
    (forall sce1 sce2, In sce1 lst -> In sce2 lst -> ~ noIntersection (alphabet sce1) (alphabet sce2)) -> 
    In (sce,eventDefinition e) (sceEventMap c).
Proof.
  intro lst;induction lst.
  - intros. inversion H4.
  - intros. rename H7 into noInter.
   
    destruct H4. subst.
    simpl in H5.
    remember (constructConfig sce e conf).
    destruct e0;inversion H5. clear H7.
    remember (constructConfigList' lst e conf).
    destruct e0;inversion H5.
    subst.
    simpl in H6.

     destruct v1. 
     remember (mergeConfigFunc' conf conf v0).
    destruct e0;inversion H6. subst. clear H5;clear H6.
    apply mergeConfigEventMap with (e:=eventDefinition e) (sce:=sce) in Heqe2;auto.
    destruct Heqe2.  
    apply H4. right.
    apply finishedScenarioInEventMap in Heqe0;auto.
    rewrite Heqe0. left;auto.
    
    remember ( innerCombineFunc'''' conf (c0 :: v1)).
    destruct o;inversion H6. clear H7.
    remember ( mergeConfigFunc' conf v0 c1).
    destruct e0;inversion H6. subst.
    apply mergeConfigEventMap with (e:=eventDefinition e) (sce:=sce) in Heqe2;auto.
    destruct Heqe2.  apply H4.
    apply  finishedScenarioInEventMap in Heqe0.
    rewrite Heqe0. left;left;auto.
   
    simpl in H5.
    remember (constructConfig a e conf ). 
    destruct e0;inversion H5. clear H8.
    remember (constructConfigList' lst e conf).
    destruct e0;inversion H5. subst. clear H5.
    simpl in H6.

    destruct v1. 
     remember (mergeConfigFunc' conf conf v0).
    destruct e0;inversion H6. subst. clear H6.
    apply mergeConfigEventMap with (e:=eventDefinition e) (sce:=sce) in Heqe2;auto.
    destruct Heqe2.  
    apply H5.  Check mergeConfigEventMap.
    SearchAbout constructConfigList'.
    destruct lst. inversion H4. simpl in Heqe1. 
    destruct (constructConfig s e conf );inversion Heqe1.
    destruct (constructConfigList' lst e conf);inversion Heqe1.
    remember (innerCombineFunc'''' conf (c0 :: v1)).
    destruct o;inversion H6. clear H7. 
    apply IHlst with (e:=e) (sce:=sce) in Heqo;auto.
    remember ( mergeConfigFunc' conf v0 c1 ).
    destruct e0;inversion H6. subst.
    apply mergeConfigEventMap with (e:=eventDefinition e) (sce:=sce) in Heqe2;auto.
    destruct Heqe2.  
    apply H5. right;auto. inversion H2;subst;auto.
      unfold incl. unfold incl in H3.
      intros. apply H3;auto. right;auto.
  intros.  apply noInter;auto. right;auto. right;auto. 
Qed.



(*innerCombineNoErr*)
Lemma constructConfigListMapNoChange: forall lst e sce x M (conf : configuration M) v c,
    correct_configuration conf ->
    uniqList lst ->
    incl lst (dom (controlstate conf)) ->
    ~ In sce lst ->
    Result v = constructConfigList' lst e conf ->
    Some c = innerCombineFunc'''' conf v ->
    In (sce, x) (sceEventMap conf) ->
    In (sce, x) (sceEventMap c).
Proof.
  intro lst;induction lst. 
  - intros. simpl in H3. inversion H3. subst. simpl in H4. inversion H4. 
  - intros.
    simpl in H3.
    
    remember (constructConfig a e conf ).
    destruct e0;inversion H3.
    remember (constructConfigList' lst e conf).
    destruct e0;inversion H3. subst.
    simpl in H4.
    destruct v1. 

    
     remember (mergeConfigFunc' conf conf v0). 
    destruct e0;inversion H4.    subst.
     unfold mergeConfigFunc' in Heqe2.
    destruct (mergeDataStateFunc (datastate conf) (datastate conf) (datastate v0));inversion Heqe2.    destruct (mergeControlStateFunc (controlstate conf) (controlstate conf) (controlstate v0));inversion H8. simpl.
    clear H9. clear H8. 
    rewrite in_app_iff. left;auto.

    
    
    remember (innerCombineFunc'''' conf (c0::v1)).
    destruct o;inversion H4. clear H8.
    remember ( mergeConfigFunc' conf v0 c1 ).
    destruct e0;inversion H4. subst.
    unfold mergeConfigFunc' in Heqe2.
    destruct (mergeDataStateFunc (datastate conf) (datastate v0) (datastate c1));inversion Heqe2.    destruct (mergeControlStateFunc (controlstate conf) (controlstate v0) (controlstate c1));inversion H8. simpl.
    clear H9. clear H8.
    rewrite in_app_iff. right.
    apply IHlst with (e:=e) (conf:=conf) (v:=c0::v1);auto.
    inversion H0;auto.
    unfold incl. intros.
    unfold incl in H1.
    apply H1;auto. right;auto. unfold not. intros.
    apply H2. right;auto. 
Qed.

Lemma sceEventMapNoChangeSync: forall M (conf conf' : configuration M) e sce x,
    correct_configuration conf ->
    synchrony conf conf' e ->
    In sce (finishedscenarios conf) ->
    In (sce,x) (sceEventMap conf) ->
    In (sce,x) (sceEventMap conf'). 
Proof.
  intros. rename H1 into fin. rename H2 into H1. 
  unfold synchrony in H0.
  destruct H0. 
  unfold combineFunc in H2.
  remember (constructConfigList (dom (controlstate conf)) e conf).
  destruct e0;inversion H2.
  clear H4.
  destruct v;inversion H2.

  
  destruct v. 
    remember (mergeConfigFunc' conf conf c). 
  destruct e0;inversion H4.
  unfold removeEventFromConf.
  simpl.

  unfold mergeConfigFunc' in Heqe1.
  destruct (mergeDataStateFunc (datastate conf) (datastate conf) (datastate c));inversion Heqe1.
  
  destruct (mergeControlStateFunc (controlstate conf) (controlstate conf) (controlstate c) );inversion H6. simpl;simpl in *.

  apply in_app_iff. left;auto.
  

  remember (innerCombineFunc'''' conf (c0::v)).
  destruct o;inversion H4.
  remember (mergeConfigFunc' conf c c1).
  destruct e0;inversion H5.
  unfold removeEventFromConf in H6.
  unfold removeEventFromConf. simpl.
  clear H6.
  unfold mergeConfigFunc' in Heqe1.
  destruct (mergeDataStateFunc (datastate conf) (datastate c) (datastate c1) );inversion Heqe1.  
  destruct (mergeControlStateFunc (controlstate conf) (controlstate c) (controlstate c1) );inversion H6. simpl.
  clear H7. clear H6.
  rewrite in_app_iff.
  right.  
  unfold constructConfigList in Heqe0.
  remember ( (filter
               (fun x : scenario =>
                inList event_definition_dec (eventDefinition e) (alphabet x))
               (filterList (finishedscenarios conf) (dom (controlstate conf)) scenario_dec))). 
  destruct l. simpl in Heqe0. inversion Heqe0.
  clear H2.
  simpl in Heqe0.
  remember (constructConfig s e conf).
  destruct e0;inversion Heqe0.
  remember (constructConfigList' l e conf ).
  destruct e0;inversion Heqe0.
  subst. 
  pose proof constructConfigListMapNoChange.
  apply H2 with (lst:=l)  (e:=e) (conf:=conf) (v:=c0::v);auto.

   assert (uniqList (s::l)).
  rewrite Heql.
  apply filterUniq.
  apply uniqListFilter;auto. destruct H;auto.
 destruct H;auto. inversion H6;auto.
  assert (incl (s::l) (dom (controlstate conf))).
  rewrite Heql.  unfold incl. intros.
  apply filter_In in H6.
  destruct H6.
  apply filterL2 in H6;auto. unfold incl in H6.
  unfold incl. intros. apply H6;right;auto.
  assert (~ In sce (s::l)).
  rewrite Heql.
  unfold not. intros.
  rewrite filter_In in H6.
  destruct H6. apply filterL1 in H6. contradiction.
  unfold not. intros. apply H6. right;auto. 
Qed.

 

Lemma constructConfigListMapNoChange': forall lst e sce  M (conf : configuration M) v c,
    correct_configuration conf ->
    noMergeError' M ->
    basicPrecondition conf e ->
    uniqList lst ->
    incl lst (dom (controlstate conf)) ->
    In sce lst ->
    Result v = constructConfigList' lst e conf ->
    Some c = innerCombineFunc'''' conf v ->
    ~ (exists ev : event_definition, In (sce, ev) (sceEventMap conf)) ->
    (forall sce1 sce2, In sce1 lst -> In sce2 lst -> ~ noIntersection (alphabet sce1) (alphabet sce2)) ->
    In (sce, (eventDefinition e)) (sceEventMap c).
Proof.
  intro lst;induction lst. 
  -  intros.
     simpl in H5.
     inversion H5;subst. simpl in H6. inversion H6.
  -  intros. rename H8 into noInter. 
     destruct H4. subst.
     simpl in H5.
     remember (constructConfig sce e conf).
     destruct e0;inversion H5.
     remember (constructConfigList' lst e conf).
     destruct e0;inversion H5.
     subst.
     simpl in H6.

     destruct v1.

     
      remember (mergeConfigFunc' conf conf v0).
     destruct e0;inversion H6.
     subst.
     apply mergeConfigEventMap with (e:=eventDefinition e) (sce:=sce) in Heqe2;auto.
     destruct Heqe2.
     apply H4.
      apply finishedScenarioInEventMap in Heqe0.
      rewrite Heqe0. right. left;auto.

      remember (innerCombineFunc'''' conf (c0 :: v1) ).
     destruct o;inversion H6.       
   remember ( mergeConfigFunc' conf v0 c1). 
   destruct e0;inversion H6. subst. 
 apply mergeConfigEventMap with (e:=eventDefinition e) (sce:=sce) in Heqe2;auto.
     destruct Heqe2.
     apply H4.
     left. apply finishedScenarioInEventMap in Heqe0.
rewrite Heqe0;left;auto. 
     
   
     simpl in H5.
     destruct (constructConfig a e conf);inversion H5.
     remember (constructConfigList' lst e conf).
     destruct e0;inversion H9. subst.
     simpl in H6.

     destruct v1.
     destruct lst. inversion H4. simpl in Heqe0.
     destruct (constructConfig s e conf);inversion Heqe0.
     destruct (constructConfigList' lst e conf );inversion Heqe0. 

     remember (innerCombineFunc'''' conf (c0 :: v1)).
     destruct o;inversion H6. clear H10.
     remember (mergeConfigFunc' conf v0 c1).
     destruct e0;inversion H6. subst.
     apply IHlst with (e:=e) (sce:=sce) in Heqo;auto.
       apply mergeConfigEventMap with (e:=eventDefinition e) (sce:=sce) in Heqe1;auto.
       destruct Heqe1. apply H8. right;auto.
       inversion H2;subst;auto. unfold incl;unfold incl in H3. intros. apply H3. right;auto. 
       intros.
     apply noInter;right;auto. 
    
Qed.

Lemma syncFinishedMap: forall M (conf conf' : configuration M) e sce,
   
    correct_configuration conf ->
    synchrony conf conf' e ->
    ~ In sce (finishedscenarios conf) ->
    In sce (finishedscenarios conf') ->
    ~
       (exists ev : event_definition,
           In (sce, ev) (sceEventMap conf)) ->
     noMergeError' M ->
    basicPrecondition conf e ->
    In (sce, (eventDefinition e)) (sceEventMap conf'). 
Proof.
  intros.
  assert (In sce (dom (controlstate conf'))).

  assert (scenarioInclusion conf').
  apply incluSync with (e:=e) (conf:=conf);auto.
  rename H6 into sin.
  unfold scenarioInclusion in sin.
  unfold incl in sin. apply sin;auto.
  
  rewrite <- domControlSync with (e:=e) (conf:=conf) in H6;auto.
  rename H6 into sdc. 
  
  assert ( In (eventDefinition e) (alphabet sce)).
  apply syncFinish with (conf:=conf) (conf':=conf');auto.
  rename H6 into eas. 
  rename H4 into noMer.
  rename H5 into bp. 
  unfold synchrony in H0.
  destruct H0.
  unfold combineFunc  in H4.
  remember (constructConfigList (dom (controlstate conf)) e conf).
  destruct e0;inversion H4.
  destruct v;inversion H4.
  clear H6. 

  remember (innerCombineFunc'''' conf (c :: v)).
  destruct o;inversion H4.   rewrite <- H6 in H7.
  SearchAbout innerCombineFunc''''. inversion H7;subst. unfold removeEventFromConf ;simpl.
  SearchAbout innerCombineFunc''''.
  unfold constructConfigList in Heqe0. 
  apply constructConfigListMapNoChange' with (lst:=(filter
               (fun x : scenario => inList event_definition_dec (eventDefinition e) (alphabet x))
               (filterList (finishedscenarios conf) (dom (controlstate conf)) scenario_dec))) (v:=c::v) (conf:=conf);auto.
  Focus 4.
  intros.
  unfold not;intros.
  pose proof alphabetNoIntersectionNotIn. 
  apply H10 with (scs:=(filterList (finishedscenarios conf) (dom (controlstate conf)) scenario_dec)) (e:=eventDefinition e) in H9;auto.
  SearchAbout filter. apply filterUniq;auto.
  SearchAbout filterList. apply uniqListFilter;destruct H;auto.
  unfold incl;intros. apply filter_In in H5. destruct H5. apply filterL2 in H5;auto.
  apply filter_In. split. SearchAbout filterList.  apply filterIn;auto. SearchAbout inList. 
  apply   inListLemma;auto.
  
Qed. 


Lemma constructConfigListMapInList:
  forall (lst : list scenario) (e : raisedEvent) (sce : scenario) (M : monitor) (conf : configuration M)
    (v : list (configuration M)) (c : configuration M),
  correct_configuration conf ->
  noMergeError' M ->
  basicPrecondition conf e ->
  uniqList lst ->
  incl lst (dom (controlstate conf)) ->
  Result v = constructConfigList' lst e conf ->
  Some c = innerCombineFunc'''' conf v ->
  ~ (exists ev : event_definition, In (sce, ev) (sceEventMap conf)) ->
  In (sce, eventDefinition e) (sceEventMap c) ->
  (forall sce1 sce2, In sce1 lst -> In sce2 lst -> ~ noIntersection (alphabet sce1) (alphabet sce2)) ->
  In sce lst. 
Proof.
  intro lst;induction lst.
  - intros.
    simpl in H4.   inversion H4;subst.   simpl in H5. inversion H5.
  - intros. rename H8 into noInter. 
    simpl in H4.
    remember (constructConfig a e conf).
    destruct e0;inversion H4.
    clear H9.
    remember (constructConfigList' lst e conf ).
    destruct e0;inversion H4. subst.
    assert (sce = a \/ sce <> a).
    apply excluded_middle.
    destruct H8. left;auto.
    right.
    simpl in H5.

    destruct v1. 
     remember (mergeConfigFunc' conf conf v0).
    destruct e0;inversion H5.
    subst.
      apply mergeConfigEventMap with (e:=eventDefinition e ) (sce:=sce) in Heqe2;auto.
    destruct Heqe2.
    apply H10 in H7. destruct H7.
    exfalso;apply H6. exists (eventDefinition e);auto.
    remember Heqe0. clear Heqe2.
    apply finishedScenarioInEventMap in Heqe0.
    rewrite Heqe0 in H7.
    destruct H7;inversion H7. subst. contradiction.

    
    remember (innerCombineFunc'''' conf (c0::v1)).
    destruct o;inversion H5.
    remember (mergeConfigFunc' conf v0 c1).
    clear H10.
    destruct e0;inversion H5.
    subst.
    apply mergeConfigEventMap with (e:=eventDefinition e ) (sce:=sce) in Heqe2;auto.
    destruct Heqe2.
    apply H10 in H7. destruct H7.
    
    apply finishedScenarioInEventMap in Heqe0.
    rewrite Heqe0 in H7.
    destruct H7;subst;inversion H7. subst. contradiction.
    apply IHlst with (e:=e) (sce:=sce) in Heqo;auto.
    inversion H2;auto.
    unfold incl in H3. unfold incl. intros.
    apply H3;right;auto.

    intros;apply noInter;right;auto. 
    
Qed.

Lemma constructConfigListMapEvent:
  forall (lst : list scenario) (e : raisedEvent) (sce : scenario) (M : monitor) (conf : configuration M)
    (v : list (configuration M)) (c : configuration M) x,
  correct_configuration conf ->
  noMergeError' M ->
  basicPrecondition conf e ->
  uniqList lst ->
  incl lst (dom (controlstate conf)) ->
  Result v = constructConfigList' lst e conf ->
  Some c = innerCombineFunc'''' conf v ->
  ~ (exists ev : event_definition, In (sce, ev) (sceEventMap conf)) ->
  In (sce, x) (sceEventMap c) ->
   (forall sce1 sce2, In sce1 lst -> In sce2 lst -> ~ noIntersection (alphabet sce1) (alphabet sce2)) ->
  In sce lst. 
Proof.
  intro lst;induction lst.
  - intros.
    simpl in H4.   inversion H4;subst.   simpl in H5. inversion H5.
  - intros. rename H8 into noInter.
    simpl in H4.
    remember (constructConfig a e conf).
    destruct e0;inversion H4.
    clear H9.
    remember (constructConfigList' lst e conf ).
    destruct e0;inversion H4. subst.
    assert (sce = a \/ sce <> a).
    apply excluded_middle.
    destruct H8. left;auto.
    right.
    simpl in H5.

    destruct v1.
    
      remember (mergeConfigFunc' conf conf v0).
    destruct e0;inversion H5.
    subst.
      apply mergeConfigEventMap with (e:=x ) (sce:=sce) in Heqe2;auto.
    destruct Heqe2.
    apply H10 in H7. destruct H7.
    exfalso;apply H6. exists x;auto.
    remember Heqe0. clear Heqe2.
    apply finishedScenarioInEventMap in Heqe0.
    rewrite Heqe0 in H7.
    destruct H7;inversion H7. subst. contradiction.
  
    remember (innerCombineFunc'''' conf (c0::v1)).
    destruct o;inversion H5.
    remember (mergeConfigFunc' conf v0 c1).
    clear H10.
    destruct e0;inversion H5.
    subst.
    apply mergeConfigEventMap with (e:=x ) (sce:=sce) in Heqe2;auto.
    destruct Heqe2.
    apply H10 in H7. destruct H7.
   
    apply finishedScenarioInEventMap in Heqe0.
    rewrite Heqe0 in H7.
    destruct H7;subst;inversion H7. subst;contradiction.
    apply IHlst with (e:=e) (sce:=sce) (x:=x) in Heqo;auto.
    inversion H2;auto.
    unfold incl in H3. unfold incl. intros.
    apply H3;right;auto.
    intros.
    apply noInter;right;auto. 
   
Qed.

Lemma finishedInList: forall (lst : list scenario) (e : raisedEvent) (M : monitor) (conf : configuration M)
    (v : list (configuration M)) (i : scenario) (c : configuration M),
  uniqList lst ->
  incl lst (dom (controlstate conf)) ->
  Result v = constructConfigList' lst e conf ->
  Some c = innerCombineFunc'''' conf v ->
  In i lst ->
   correct_configuration conf ->
       noMergeError' M ->
       basicPrecondition conf e ->
    (forall sce1 sce2, In sce1 lst -> In sce2 lst -> ~ noIntersection (alphabet sce1) (alphabet sce2)) ->     
  In i (finishedscenarios c).
Proof.
  intro lst;induction lst.
  - intros. inversion H3.
  - intros. rename H4 into correct. rename H5 into noMerge. rename H6 into bp.
    rename H7 into noInter. destruct H3. subst.
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
    intros. apply noInter;right;auto. 
Qed.



Lemma constructConfigTyEnv: forall M (conf conf' : configuration M) e sce,
    tyEnv (datastate conf) ->
    Result conf' = constructConfig sce e conf ->
    wellFormedRaisedEvent e ->
    tyEnv (datastate conf').
Proof.     
  intros.
  
  unfold constructConfig in H0.
  remember (getScenarioState sce (controlstate conf)).
  destruct o;inversion H0.
  remember (transEvMapFunc (stateEvDefInstanceMap M) (Some s, Some (eventDefinition e))).
  destruct o;inversion H0.
  remember (findEventInstance e (datastate conf) l). 
  destruct o;inversion H3.
  remember ( createValueEnv (eventArgs e0) (eventParams (eventDefinition e)) (eventArguments e)).  destruct e1;inversion H4.
  remember (getStep' conf sce e0).
  destruct o;inversion H5.
  remember (configTransition (extendValEnv (datastate conf) v) e e0 sce s0 conf ).
  destruct e1;inversion H0.
  subst.
  unfold configTransition in Heqe0.
  remember (execAction (extendValEnv (datastate conf) v, nil) (stepActions s0)
              (filter
                 (fun e : event_definition =>
                  match eventKind e with
                  | Internal => true
                  | Imported => false
                  | Exported => true
                  end) (events M))).
  destruct e1;inversion Heqe0.
  destruct v1. inversion Heqe0;subst. simpl.

  assert (tyEnv v1).
  eapply typeActionTyEnv.
  apply Heqe2.
  unfold extendValEnv.
  apply tyEnvApp;auto.
  unfold wellFormedRaisedEvent in H1.
  
  SearchAbout createValueEnv.
  eapply raisedTyEnv.
  apply H1. apply Heqe1.
  SearchAbout updateDataState.
  apply updateDSTyEnvPreserved;auto.  
Qed. 



Lemma mergeDSTyEnv: forall ds ds1 ds2 v1,
    tyEnv ds ->
    tyEnv ds1 ->
    tyEnv ds2 ->
    Result v1 = mergeDataStateFunc ds ds1 ds2 ->
    tyEnv v1. 
Proof.
  intro ds;induction ds.
  -  intros.
     destruct ds1.
     destruct ds2.
     simpl in H2. inversion H2. constructor.
     simpl in H2. inversion H2.
     simpl in H2. inversion H2.
  -  intros.
     destruct ds1. simpl in H2. destruct a;destruct p. inversion H2.
     destruct ds2. simpl in H2. destruct a;destruct p0;destruct p.
     destruct p. inversion H2.
     simpl in H2.
     destruct a;destruct p1;destruct p;destruct p0.
     destruct p;destruct p0.
     destruct (atom_eq_dec a a0);inversion H2.
     destruct (atom_eq_dec a a1);inversion H2.
     destruct (typ_eq_dec t t0);inversion H5.
     destruct (typ_eq_dec t t1);inversion H6.
     subst.
     remember (mergeDataStateFunc ds ds1 ds2 ).
     destruct e;inversion H7.
     destruct (range_typ_dec r0 r1).
     subst. inversion H2.
     Print tyEnv.
     inversion H1. subst.
     constructor.
     apply IHds in Heqe;auto.
     inversion H;auto. inversion H0;auto.
     SearchAbout tyEnvPair.
     eapply tyEnvIn. Focus 2.
     apply H1. left;auto.
     destruct ( range_typ_dec r0 r).
     subst.
     inversion H2;subst.
     inversion H1;subst.
     constructor. 
     apply IHds in Heqe;auto.
     inversion H;auto. inversion H0;auto.
     eapply tyEnvIn. Focus 2.
     apply H1. left;auto.
     destruct ( range_typ_dec r1 r).
     Focus 2. inversion H2.
     subst.
     inversion H2.
     inversion H0;subst.
     constructor. 
     apply IHds in Heqe;auto.
     inversion H;auto. inversion H1;auto.
     eapply tyEnvIn. Focus 2.
     apply H0.   left;auto.    
Qed.

Lemma innerCombineTyEnv: forall M (conf : configuration M) sceList v0  re c,
    tyEnv (datastate conf) ->
    incl sceList (dom (controlstate conf)) ->
    Result v0 = constructConfigList' sceList re conf ->
    Some c = innerCombineFunc'''' conf v0 ->
    wellFormedRaisedEvent re ->
    tyEnv (datastate c). 
Proof. intros ?? sceList;induction sceList. 
       - intros.
         simpl in H1. inversion H1;subst.
         simpl in H2. inversion H2.

       - intros.
         simpl in H1.
         remember (constructConfig a re conf).
         destruct e;inversion H1.
         clear H5.
         remember (constructConfigList' sceList re conf).
         destruct e;inversion H1.
         subst.
         simpl in H2.

         destruct v1.
         
          remember (mergeConfigFunc' conf conf v ).
  destruct e;inversion H2.
  subst.
  unfold  mergeConfigFunc' in Heqe1.
   remember (mergeDataStateFunc (datastate conf) (datastate conf) (datastate v)).
  destruct e;inversion Heqe1.
  clear H5.
  remember (mergeControlStateFunc (controlstate conf) (controlstate conf) (controlstate v)). 
  destruct e;inversion Heqe1.
  simpl.
  
   apply mergeDSTyEnv with (ds:=datastate conf) (ds1:=datastate conf) (ds2:=datastate v);auto.
  
   apply constructConfigTyEnv with (conf:=conf) (e:=re) (sce:=a);auto.


  remember (innerCombineFunc'''' conf (c0::v1)).
  destruct o;inversion H2.
         remember (mergeConfigFunc' conf v c1 ).
         destruct e;inversion H2. subst.
          unfold  mergeConfigFunc' in Heqe1.
   remember (mergeDataStateFunc (datastate conf) (datastate v) (datastate c1)).
  destruct e;inversion Heqe1.
  clear H6.
  remember (mergeControlStateFunc (controlstate conf) (controlstate v) (controlstate c1)). 
  destruct e;inversion Heqe1.
  simpl.
  apply mergeDSTyEnv with (ds:=datastate conf) (ds1:=datastate v) (ds2:=datastate c1);auto.
 
  apply constructConfigTyEnv with (conf:=conf) (e:=re) (sce:=a);auto.
  apply IHsceList  with (re:=re) in Heqo;auto.
  unfold incl;intros.
  unfold incl in H0.
  apply H0. right;auto.
 
Qed.

Lemma syncTyEnv: forall M (conf conf' : configuration M) e,
    tyEnv (datastate conf) ->
    synchrony conf conf' e ->
    wellFormedRaisedEvent e ->
    tyEnv (datastate conf').
Proof.
  intros.
  unfold synchrony in H0.
  destruct H0.
  unfold combineFunc in H2.
  remember (constructConfigList (dom (controlstate conf)) e conf).
  destruct e0;inversion H2. clear H4. 
  destruct v;inversion H2.
  clear H2.


  destruct v. 
remember (mergeConfigFunc' conf conf c).
  destruct e0;inversion H4.
  unfold removeEventFromConf;simpl.
  unfold  mergeConfigFunc' in Heqe1.
   remember (mergeDataStateFunc (datastate conf) (datastate conf) (datastate c)).
  destruct e0;inversion Heqe1.
  clear H5.
  remember (mergeControlStateFunc (controlstate conf) (controlstate conf) (controlstate c)). 
  destruct e0;inversion Heqe1.
  simpl.
  apply mergeDSTyEnv with (ds:=datastate conf) (ds1:=datastate conf) (ds2:=datastate c);auto.
   pose proof termL2.
  unfold constructConfigList in Heqe0. 
  assert (exists sce : scenario, In sce (filter
               (fun x : scenario =>
                inList event_definition_dec (eventDefinition e) (alphabet x))
               (filterList (finishedscenarios conf) (dom (controlstate conf)) scenario_dec)) /\ Result c = constructConfig sce e conf).
  apply H2 with (lst:=c::nil);auto. split;auto. left;auto.
  destruct H6.
  destruct H6.
  assert (tyEnv (datastate c)). eapply constructConfigTyEnv;auto.
  apply H. 
  apply H7. auto. auto.
 

  remember (innerCombineFunc'''' conf (c0::v)).
  destruct o;inversion H4.
  remember (mergeConfigFunc' conf c c1 ).
  destruct e0;inversion H4.
  unfold removeEventFromConf. simpl.
  unfold mergeConfigFunc' in Heqe1.
  remember (mergeDataStateFunc (datastate conf) (datastate c) (datastate c1)).
  destruct e0;inversion Heqe1.
  clear H6.
  remember (mergeControlStateFunc (controlstate conf) (controlstate c) (controlstate c1)). 
  destruct e0;inversion Heqe1.
  simpl.
  pose proof termL2.
  unfold constructConfigList in Heqe0. 
  assert (exists sce : scenario, In sce (filter
               (fun x : scenario =>
                inList event_definition_dec (eventDefinition e) (alphabet x))
               (filterList (finishedscenarios conf) (dom (controlstate conf)) scenario_dec)) /\ Result c = constructConfig sce e conf).
  apply H2 with (lst:=c::c0::v);auto. split;auto. left;auto.
  destruct H7.
  destruct H7.
  assert (tyEnv (datastate c)). eapply constructConfigTyEnv;auto. 
  apply H. apply H8. auto.
  
  apply mergeDSTyEnv with (ds:=datastate conf) (ds1:=datastate c) (ds2:=datastate c1);auto.
  pose proof innerCombineTyEnv.
  remember ((filter
               (fun x : scenario =>
                inList event_definition_dec (eventDefinition e) (alphabet x))
               (filterList (finishedscenarios conf) (dom (controlstate conf)) scenario_dec)) ).
  destruct l. simpl in Heqe0. inversion Heqe0.
  simpl in Heqe0.
  remember (constructConfig s e conf).
  destruct e0;inversion Heqe0.
  remember (constructConfigList' l e conf).
  destruct e0;inversion  H12.   
  subst.   
  eapply H10.
  apply H.
  assert (incl (s::l) (dom (controlstate conf))).
  rewrite Heql.
  unfold incl.
  intros.
  apply filter_In in H5.
  destruct H5.
  apply filterL2 in H5;auto.
  assert (incl l (dom (controlstate conf))).
  unfold incl;unfold incl in H5;intros.
  apply H5. right;auto.
  apply H6.
  apply Heqe5. apply Heqo. auto. 
Qed.

Lemma syncEvents: forall M (conf conf' : configuration M) e e',
    synchrony conf conf' e ->
    ~ In e' (raisedevents conf) ->
    In e' (raisedevents conf') ->
    In (eventDefinition e') (events M). 
Proof.
  intros.
  unfold synchrony in H.
  destruct H.
  unfold combineFunc in H2. 
   remember (constructConfigList (dom (controlstate conf)) e conf).
  destruct e0;inversion H2. clear H4. 
  destruct v;inversion H2.
  clear H2.

  destruct v. 
   remember ( mergeConfigFunc' conf conf c).
  destruct e0;inversion H4.
  unfold  removeEventFromConf in H3. rewrite <- H3 in H1. simpl in H1.
   apply removeIn in H1.
   unfold mergeConfigFunc' in Heqe1.
  remember (mergeDataStateFunc (datastate conf) (datastate conf) (datastate c)).
  destruct e0;inversion Heqe1.
  clear H5.
  remember (mergeControlStateFunc (controlstate conf) (controlstate conf) (controlstate c)). 
  destruct e0;inversion Heqe1. rewrite H5 in H1. simpl in *.
  (*unfold mergeList' in H1.*)
  rewrite in_app_iff in H1.
  destruct H1. contradiction.
 (* apply filterL2 in H1.*)
  pose proof termL2.
   unfold constructConfigList in Heqe0. 
  assert (exists sce : scenario, In sce (filter
               (fun x : scenario =>
                inList event_definition_dec (eventDefinition e) (alphabet x))
               (filterList (finishedscenarios conf) (dom (controlstate conf)) scenario_dec)) /\ Result c = constructConfig sce e conf).
  apply H2 with (lst:=c::nil);auto. split;auto. left;auto.
  destruct H6.
  destruct H6. 
  eapply constructConfigEvents.
  apply H7. auto. auto.

  
  
  remember (innerCombineFunc'''' conf (c0::v)).
  destruct o;inversion H4.
  remember (mergeConfigFunc' conf c c1).
  destruct e0;inversion H4.
  unfold removeEventFromConf in H5. rewrite <- H5 in H1. simpl in H1.
  apply removeIn in H1. 
  unfold mergeConfigFunc' in Heqe1.
  remember (mergeDataStateFunc (datastate conf) (datastate c) (datastate c1)).
  destruct e0;inversion Heqe1.
  clear H6.
  remember (mergeControlStateFunc (controlstate conf) (controlstate c) (controlstate c1)). 
  destruct e0;inversion Heqe1. rewrite H6 in H1. simpl in H1.
 
  rewrite in_app_iff in H1.
  destruct H1.
 
  (*apply filterL2 in H1. *)
  pose proof termL2.
  unfold constructConfigList in Heqe0. 
  assert (exists sce : scenario, In sce (filter
               (fun x : scenario =>
                inList event_definition_dec (eventDefinition e) (alphabet x))
               (filterList (finishedscenarios conf) (dom (controlstate conf)) scenario_dec)) /\ Result c = constructConfig sce e conf).
  apply H2 with (lst:=c::c0::v);auto. split;auto. left;auto.
  destruct H7.
  destruct H7. 
  eapply constructConfigEvents.
  apply H8. auto. auto.
 
  apply innerCombineFuncRaisedEvents with (re:=e') in Heqo;auto.
  destruct Heqo. destruct H2.
  pose proof termL2.
  unfold constructConfigList in Heqe0. 
  assert (exists sce : scenario, In sce (filter
               (fun x : scenario =>
                inList event_definition_dec (eventDefinition e) (alphabet x))
               (filterList (finishedscenarios conf) (dom (controlstate conf)) scenario_dec)) /\ Result x = constructConfig sce e conf).
  apply H8 with (lst:=c::c0::v);auto. split;auto. right;auto. 
  destruct H9.
  destruct H9. 
  eapply constructConfigEvents.
  apply H10. auto. auto.
  
Qed.



Lemma mergeDSEvnConsist: forall ds ds1 ds2 v1 tyenv,
    Result v1 = mergeDataStateFunc ds ds1 ds2 ->
    evnConsist tyenv ds ->
    evnConsist tyenv ds1 ->
    evnConsist tyenv ds2 ->
    evnConsist tyenv v1. 
Proof.
  intro ds;induction ds. 
  - intros. destruct ds1;destruct ds2.
    simpl in H. inversion H. subst;auto.
    simpl in H. inversion H.
    simpl in H. inversion H.
    simpl in H. inversion H.
  - intros.
        destruct ds1;destruct ds2.
    simpl in H. destruct a;destruct p. inversion H. 
    simpl in H. destruct a;destruct p. destruct p0. inversion H. 
    simpl in H. destruct a;destruct p. destruct p0;destruct p. inversion H.
    simpl in H.
    destruct a;destruct p1;destruct p;destruct p0.
    destruct p;destruct p0.
    destruct ( atom_eq_dec a a0);inversion H.
    destruct (atom_eq_dec a a1);inversion H.
    destruct (typ_eq_dec t t0);inversion H.
    destruct (typ_eq_dec t t1);inversion H.
    clear H7;clear H4;clear H5;clear H6. 
    subst.
    remember (mergeDataStateFunc ds ds1 ds2).
    destruct e;inversion H. clear H4.
    destruct ( range_typ_dec r0 r1).
    subst.
    inversion H.
    inversion H1;subst.
    constructor.
    inversion H0;subst.
    inversion H2;subst.
    eapply IHds;auto. apply Heqe. auto. auto.
    destruct (range_typ_dec r0 r). 
    subst.
    inversion H.
    inversion H1;subst.
    constructor.
    inversion H0;subst.
    inversion H2;subst.
    eapply IHds;auto. apply Heqe. auto. auto.
     destruct (range_typ_dec r1 r). 
    subst.
    inversion H.
    inversion H1;subst.
    constructor.
    inversion H0;subst.
    inversion H2;subst.
    eapply IHds;auto. apply Heqe. auto. auto.
    inversion H.     
Qed.

Lemma innerCombineEvnConsist: forall M sceList (conf : configuration M) v0  re c,
    correct_configuration conf->
    incl sceList (dom (controlstate conf)) ->
    Result v0 = constructConfigList' sceList re conf ->
    Some c = innerCombineFunc'''' conf v0 ->
    stateEvDefInstanceMapEquivEListProp M ->
    stateEvDefInstanceMapEquiv M ->
    transEvMapProp M ->
    In re (raisedevents conf) ->
    evnConsist (dsmon M) (datastate c).
Proof. intros ? sceList;induction sceList. 
       - intros.
         simpl in H1. inversion H1;subst.
         simpl in H2. inversion H2.

       - intros. rename H6 into rein. 
         simpl in H1.
         remember (constructConfig a re conf).
         destruct e;inversion H1.
         clear H7.
         remember (constructConfigList' sceList re conf).
         destruct e;inversion H1.
         subst.
         simpl in H2.

         destruct v1. 
          remember (mergeConfigFunc' conf conf v ).
  destruct e;inversion H2.
  subst.
  unfold  mergeConfigFunc' in Heqe1.
   remember (mergeDataStateFunc (datastate conf) (datastate conf) (datastate v)).
  destruct e;inversion Heqe1.
  clear H7.
  remember (mergeControlStateFunc (controlstate conf) (controlstate conf) (controlstate v)). 
  destruct e;inversion Heqe1.
  simpl.
  
   apply mergeDSEvnConsist with (ds:=datastate conf) (ds1:=datastate conf) (ds2:=datastate v);auto.
   destruct H;auto.   destruct H;auto.
    assert ( evnConsist (dsmon M) (datastate v)). 
  apply evnConsistPreservation with (conf:=conf) (sce:=a) (re:=re) ;auto.
  auto.
    
         remember (innerCombineFunc'''' conf (c0::v1)).
         destruct o;inversion H2.
         remember (mergeConfigFunc' conf v c1 ).
         destruct e;inversion H2. subst.
          unfold  mergeConfigFunc' in Heqe1.
   remember (mergeDataStateFunc (datastate conf) (datastate v) (datastate c1)).
  destruct e;inversion Heqe1.
  clear H8.
  remember (mergeControlStateFunc (controlstate conf) (controlstate v) (controlstate c1)). 
  destruct e;inversion Heqe1.
  simpl.
  apply mergeDSEvnConsist with (ds:=datastate conf) (ds1:=datastate v) (ds2:=datastate c1);auto.
  destruct H;auto. 
  

  apply evnConsistPreservation with (conf:=conf) (sce:=a) (re:=re) ;auto.
  
  apply IHsceList  with (re:=re) in Heqo;auto.
  unfold incl;intros.
  unfold incl in H0.
  apply H0. right;auto.
  
Qed.

Lemma syncEvnConsit: forall M (conf conf' : configuration M) e,
    correct_configuration conf ->
    synchrony conf conf' e ->
    stateEvDefInstanceMapEquivEListProp M ->
    stateEvDefInstanceMapEquiv M ->
    transEvMapProp M ->
    evnConsist (dsmon M) (datastate conf').
Proof.
  intros.
  unfold synchrony in H0.
  destruct H0.
   unfold combineFunc in H4.
  remember (constructConfigList (dom (controlstate conf)) e conf).
  destruct e0;inversion H4. clear H6. 
  destruct v;inversion H4.
  clear H4.


 destruct v. 
  pose proof mergeDSEvnConsist.
  remember (mergeConfigFunc' conf conf c).
  destruct e0;inversion H6.
   unfold removeEventFromConf. simpl.
  unfold mergeConfigFunc' in Heqe1.
  remember (mergeDataStateFunc (datastate conf) (datastate conf) (datastate c)).
  destruct e0;inversion Heqe1.
  clear H8.
  remember (mergeControlStateFunc (controlstate conf) (controlstate conf) (controlstate c)). 
  destruct e0;inversion Heqe1.
  simpl.
  clear H8. clear Heqe1.
  apply H4 with (ds:=(datastate conf)) (ds1:=(datastate conf)) (ds2:=(datastate c));auto. 
  destruct H;auto. destruct H;auto.
   pose proof termL2.
  unfold constructConfigList in Heqe0. 
  assert (exists sce : scenario, In sce (filter
               (fun x : scenario =>
                inList event_definition_dec (eventDefinition e) (alphabet x))
               (filterList (finishedscenarios conf) (dom (controlstate conf)) scenario_dec)) /\ Result c = constructConfig sce e conf).
  apply H5 with (lst:=c::nil);auto. split;auto. left;auto.

  destruct H8.
  destruct H8.

 
  apply evnConsistPreservation with (conf:=conf) (sce:=x) (re:=e);auto.
  
  
  
  
  remember (innerCombineFunc'''' conf (c0::v)).
  destruct o;inversion H6.
  remember (mergeConfigFunc' conf c c1).
  destruct e0;inversion H6.
  unfold removeEventFromConf. simpl.
  unfold mergeConfigFunc' in Heqe1.
  remember (mergeDataStateFunc (datastate conf) (datastate c) (datastate c1)).
  destruct e0;inversion Heqe1.
  clear H8.
  remember (mergeControlStateFunc (controlstate conf) (controlstate c) (controlstate c1)). 
  destruct e0;inversion Heqe1.
  simpl.
  
  pose proof termL2.
  unfold constructConfigList in Heqe0. 
  assert (exists sce : scenario, In sce (filter
               (fun x : scenario =>
                inList event_definition_dec (eventDefinition e) (alphabet x))
               (filterList (finishedscenarios conf) (dom (controlstate conf)) scenario_dec)) /\ Result c = constructConfig sce e conf).
  apply H4 with (lst:=c::c0::v);auto. split;auto. left;auto.
  destruct H9.
  destruct H9.
  assert (evnConsist (dsmon M) (datastate c)).
 
  apply evnConsistPreservation with (conf:=conf) (sce:=x) (re:=e);auto.
  
  
  clear H8.
  clear Heqe1.
  pose proof mergeDSEvnConsist.
  apply H8 with (ds:=(datastate conf)) (ds1:=(datastate c)) (ds2:=(datastate c1));auto.
  destruct H;auto.
  pose proof innerCombineEvnConsist.
  remember ((filter
               (fun x : scenario =>
                inList event_definition_dec (eventDefinition e) (alphabet x))
               (filterList (finishedscenarios conf) (dom (controlstate conf)) scenario_dec)) ).
  destruct l. simpl in Heqe0. inversion Heqe0.
  simpl in Heqe0.
  remember (constructConfig s e conf).
  destruct e0;inversion Heqe0.
  remember (constructConfigList' l e conf).
  destruct e0;inversion  H14.   
  subst.   
  eapply H12.
  apply H.
  assert (incl (s::l) (dom (controlstate conf))).
  rewrite Heql.
  unfold incl.
  intros.
  apply filter_In in H7.
  destruct H7.
  apply filterL2 in H7;auto.
  assert (incl l (dom (controlstate conf))).
  unfold incl;unfold incl in H7;intros.
  apply H7. right;auto.
  apply H13.
  apply Heqe4. apply Heqo. auto.
auto.   
auto.
auto.
Qed.

Lemma execActionRaisingEventMatch: 
      forall (actList : action) (env : value_env) (l : list raisedEvent) 
         (env' : value_env) (l' : list raisedEvent) (re : raisedEvent)
         (eventList : list event_definition),
       Result (env', l') = execAction (env, l) actList eventList ->
       ~ In re l ->
       In re l' ->
      parameterMatch (eventArguments re) (eventParams (eventDefinition re)). 
Proof. intro actList;induction actList.
  - intros;simpl in *. inversion H;subst. contradiction. 
  - intros. simpl in H.
    destruct l;inversion H.    clear H3.
    destruct a;inversion H. clear H3.
    destruct (evalMonad env e);inversion H. clear H3. 
    destruct ( updateValueEnvInv (AIdent s) v env ).
    inversion H;subst. contradiction.
    inversion H. 
  -  intros.
    simpl in H.
    remember (calculateExprList env exprs).
    destruct e;inversion H. clear H3.
    remember (getEventByName ident eventList).
    destruct o;inversion H. clear H3.
    remember (parameterMatchFunc v (eventParams e)).
    destruct b;inversion H. subst.
    SearchAbout parameterMatchFunc.
    symmetry in Heqb. rewrite parameterMatch_refl.
    
    
    destruct H1. Focus 2. contradiction.
    rewrite <- H1. simpl.
    auto.     
    
  -
    intros.
    simpl in H. 
    remember (execAction (env, l) actList1 eventList).
    destruct e;inversion H.
    destruct v.
    simpl.
    assert (In re l0 \/ ~ In re l0).
    apply excluded_middle.
    destruct H2. 
    apply IHactList1 with (re:=re) in Heqe;auto.
    
    apply IHactList2 with (re:=re) in H;auto.
   
Qed.


Lemma raised_wellform_basic: forall M (conf conf' : configuration M) e sce e',
    correct_configuration conf ->
    Result conf' = constructConfig sce e conf ->
    (forall re', In re' (raisedevents conf) -> wellFormedRaisedEvent re') ->
     In e' (raisedevents conf') ->
    wellFormedRaisedEvent e'.
Proof.
  intros.
   assert (In e' (raisedevents conf) \/ ~ In e' (raisedevents conf)). 
 apply excluded_middle. 
  destruct H3.
  apply H1;auto.
   unfold constructConfig in H0.
  remember (getScenarioState sce (controlstate conf)). 
  destruct o;inversion H0.
  remember (transEvMapFunc (stateEvDefInstanceMap M) (Some s, Some (eventDefinition e))).
  destruct o;inversion H0.
  remember ( findEventInstance e (datastate conf)
                               l).
  destruct o;inversion H0.
  remember ( createValueEnv (eventArgs e0) (eventParams (eventDefinition e))
                            (eventArguments e)).
  destruct e1;inversion H0.
  remember (getStep' conf sce e0).
  destruct o;inversion H0.
  remember (configTransition (extendValEnv (datastate conf) v) e e0 sce s0 conf). 
  destruct e1;inversion H0.
  subst.
  SearchAbout (~ In _ (raisedevents _)).
  unfold wellFormedRaisedEvent.
  SearchAbout parameterMatch.

  
  unfold  configTransition in Heqe0.
  remember ( execAction (extendValEnv (datastate conf) v, nil) 
              (stepActions s0)
              (filter
                 (fun e : event_definition =>
                  match eventKind e with
                  | Internal => true
                  | Imported => false
                  | Exported => true
                  end) (events M))).
  destruct e1;inversion Heqe0. 
  destruct v1.
 
  pose proof execActionRaisingEvent.
  inversion Heqe0;subst. simpl in *.
  
  clear H5;clear H6;clear H7;clear H8;clear H9;clear H10. 
  clear H0. clear Heqe0. 
  (*apply in_app_iff in H2.
  destruct H2.
  Focus 2. apply removeIn in H0. contradiction.  remember H0. clear Heqi. *)
  remember H2.  clear Heqi. 
  apply filter_In in i. destruct i.
  assert (exists (act : action) (exprs : list expr),
         In act (transitionIntoBasicActionList (stepActions s0)) /\
         act = RaiseStmt (eventId (eventDefinition e')) exprs).
  apply H4 with (l':=l0) (l:=nil) (env:=extendValEnv (datastate conf) v) (env':=v1) (eventList:=(filter
               (fun e : event_definition =>
                match eventKind e with
                | Internal => true
                | Imported => false
                | Exported => true
                end) (events M))) ;auto.
  destruct H6. destruct H6.
  destruct H6.
  pose proof execActionRaisingEventMatch.
  eapply H8. apply Heqe2. unfold not. intros. inversion H9.
  auto. 
Qed. 

Lemma raised_wellform': forall M (conf conf' : configuration M) e e',
    correct_configuration conf ->
    wellFormedRaisedEvent e ->
    synchrony conf conf' e ->
    (forall re', In re' (raisedevents conf) -> wellFormedRaisedEvent re') ->
    In e' (raisedevents conf') ->
    wellFormedRaisedEvent e'.
Proof.
  intros.
  assert (In e' (raisedevents conf) \/ ~ In e' (raisedevents conf)). 
  apply excluded_middle. 
  destruct H4.
  apply H2;auto.
  remember H1. clear Heqs.
  unfold synchrony in s.
  destruct s.
   unfold combineFunc in H6.
    remember (constructConfigList (dom (controlstate conf)) e conf).
    destruct e0;inversion H6.
    clear H6.
    unfold constructConfigList in Heqe0.
    destruct v;inversion H8.
    clear H8.

    destruct v. 
    remember ( mergeConfigFunc' conf conf c).
    destruct e0;inversion H7. subst. unfold removeEventFromConf in H3. simpl in H3.
    apply removeIn in H3. 
    unfold mergeConfigFunc' in Heqe1.
    remember (mergeDataStateFunc (datastate conf) (datastate conf) (datastate c) ).
    destruct e0;inversion Heqe1.
    remember ( mergeControlStateFunc (controlstate conf) (controlstate conf) (controlstate c)).
    destruct e0;inversion Heqe1. rewrite H9 in H3. simpl in H3.
    (*unfold mergeList' in H3.*)
    rewrite in_app_iff in H3. destruct H3. contradiction.
    (*apply filterL2 in H3.*)
    pose proof termL2.
    assert (exists sce : scenario, In sce (filter
               (fun x : scenario =>
                inList event_definition_dec (eventDefinition e) (alphabet x))
               (filterList (finishedscenarios conf) (dom (controlstate conf)) scenario_dec)) /\ Result c = constructConfig sce e conf).
    apply H6 with (lst:=c::nil);auto. split;auto. left;auto. 
    destruct H10. destruct H10.
   eapply  raised_wellform_basic. 
   apply H.     apply H11.
     intros. apply H2;auto. auto. 
    
    remember (innerCombineFunc'''' conf (c0::v)).
    destruct o;inversion H7.
    
    remember ( mergeConfigFunc' conf c c1).
    destruct e0;inversion H7. subst. unfold removeEventFromConf in H3. simpl in H3.
    apply removeIn in H3. 
    unfold mergeConfigFunc' in Heqe1.
    remember (mergeDataStateFunc (datastate conf) (datastate c) (datastate c1) ).
    destruct e0;inversion Heqe1.
    remember ( mergeControlStateFunc (controlstate conf) (controlstate c) (controlstate c1)).
    destruct e0;inversion Heqe1. rewrite H10 in H3. simpl in H3.
   (* unfold mergeList' in H3.*)
    rewrite in_app_iff in H3.
    destruct H3. 
    (*apply filterL2 in H3.*)
    clear H10. clear H9.
    pose proof termL2.
    assert (exists sce : scenario, In sce (filter
               (fun x : scenario =>
                inList event_definition_dec (eventDefinition e) (alphabet x))
               (filterList (finishedscenarios conf) (dom (controlstate conf)) scenario_dec)) /\ Result c = constructConfig sce e conf).
    apply H6 with (lst:=c::c0::v);auto. split;auto. left;auto. 
    destruct H9. destruct H9.
   eapply  raised_wellform_basic. 
   apply H.     apply H10.
   intros. apply H2;auto. auto. 
   clear H9;clear H10.
   
     pose proof  innerCombineFuncRaisedEvents.
     assert (exists conf'' : configuration M, In conf'' (c0::v) /\ In e' (raisedevents conf'')).
     apply H6 with (conf:=conf) (conf':=c1);auto.
     destruct H9.
     destruct H9.
      pose proof termL2.
    assert (exists sce : scenario, In sce (filter
               (fun x : scenario =>
                inList event_definition_dec (eventDefinition e) (alphabet x))
               (filterList (finishedscenarios conf) (dom (controlstate conf)) scenario_dec)) /\ Result x = constructConfig sce e conf).
    apply H11 with (lst:=c::c0::v);auto. split;auto. right;auto. 
    destruct H12. destruct H12.
   eapply  raised_wellform_basic. 
   apply H.     apply H13.
   intros. apply H2;auto. auto.
   
Qed.


Lemma raisedIntervalSync: forall M (conf conf' : configuration M) e e',
    correct_configuration conf ->
    synchrony conf conf' e ->
    ~ In e' (raisedevents conf) ->
    In e' (raisedevents conf') ->
    eventKind (eventDefinition e') = Internal.
Proof.
  intros.
  remember H0. clear Heqs.
  unfold synchrony in s.
  destruct s.
  unfold combineFunc in H4.
  remember (constructConfigList (dom (controlstate conf)) e conf).
  destruct e0;inversion H4.
  destruct v;inversion H4.
  unfold constructConfigList in Heqe0.

  
  remember (innerCombineFunc'''' conf (c :: v)). 
  destruct o;inversion H6.
  pose proof innerCombineFuncRaisedEvents.
  rewrite <- H8 in  H2.
  unfold removeEventFromConf in H2. simpl in H2.
  apply removeIn in H2. 
  assert (exists conf'' : configuration M, In conf'' (c::v) /\ In e' (raisedevents conf'')). 
  apply H5 with (conf:=conf) (conf':=c0);auto.
  destruct H9. destruct H9. 
  pose proof termL2.
  assert (exists sce : scenario, In sce (filter
               (fun x : scenario =>
                inList event_definition_dec (eventDefinition e) (alphabet x))
               (filterList (finishedscenarios conf) (dom (controlstate conf)) scenario_dec)) /\ Result x = constructConfig sce e conf).
  apply H11 with (lst:=c::v);auto.
  destruct H12. destruct H12.
  SearchAbout Internal.
  
  pose proof raisedEventsInternal.
  apply H14 with (conf':=x) (sce:=x0) (re:=e) (conf:=conf);auto.
Qed. 

Lemma mergeCSState: forall cs cs1 cs2 v p,
    Result v = mergeControlStateFunc cs cs1 cs2 ->
    ~ In p cs ->
    In p v ->
    (In p cs1 \/ In p cs2). 
Proof.
  intros.
  SearchAbout mergeControlStateFunc. 
  assert (dom cs = dom cs1 /\ dom cs = dom cs2).
  apply domMerge. exists v;auto.
  destruct H2. 
  generalize dependent cs1. generalize dependent cs2.
  generalize dependent p. generalize dependent v. 
  induction cs. 
  intros. destruct cs1. destruct cs2. simpl in H. inversion H. subst. inversion H1. 
  inversion H3.   inversion H2.
  intros.
  destruct cs1. inversion H2.
  destruct cs2. inversion H3.
  simpl in H.
  destruct a. destruct p0. destruct p1.
  destruct (scenario_dec s s1);inversion H. clear H5.
  destruct (scenario_dec s s3);inversion H. clear H5.
  remember (mergeControlStateFunc cs cs1 cs2). 
  destruct e1. Focus 2. inversion H.
  
  destruct (string_dec s2 s4). simpl in H3. inversion H3.
  simpl in H2. inversion H2. subst. 
  subst. inversion H. subst.
  inversion H1. left. left;auto.
  apply IHcs with (p:=p) in Heqe1;auto.
  Focus 2.   unfold not. intros. apply H0. right;auto.
  destruct Heqe1. left;right;auto. right;right;auto.
  destruct (string_dec s2 s0).
  subst. inversion H;subst.  inversion H1.
  right;auto.  left;auto.
  simpl in H3;simpl in H2. inversion H3;inversion H2;subst.
  apply IHcs with (p:=p) in Heqe1;auto.
  Focus 2.   unfold not. intros. apply H0. right;auto.
   destruct Heqe1. left;right;auto. right;right;auto.
   destruct (string_dec s4 s0);inversion H.
  subst. inversion H1. left;left;auto. 
simpl in H3;simpl in H2. inversion H3;inversion H2;subst.
  apply IHcs with (p:=p) in Heqe1;auto.
  Focus 2.   unfold not. intros. apply H0. right;auto.
  destruct Heqe1. left;right;auto. right;right;auto.
Qed.

Lemma constructConfigSceState: forall M (conf c: configuration M) x e sce s,
    correct_configuration conf ->
    Result c = constructConfig x e conf ->
    ~ In (sce, s) (controlstate conf) ->
    In (sce, s) (controlstate c) ->
    sce = x.
Proof.
  intros.
  unfold constructConfig in H0.
  remember (getScenarioState x (controlstate conf)). 
  destruct o;inversion H0;auto. clear H4.
  remember (transEvMapFunc (stateEvDefInstanceMap M) (Some s0, Some (eventDefinition e))).
  destruct o;inversion H0;auto. clear H4.
  remember (findEventInstance e (datastate conf) l).
  destruct o;inversion H0. clear H4.
  remember (createValueEnv (eventArgs e0) (eventParams (eventDefinition e)) (eventArguments e)). 
  destruct e1;inversion H0. clear H4. 
  remember (getStep' conf x e0).
  destruct o;inversion H0. clear H4.
  remember (configTransition (extendValEnv (datastate conf) v) e e0 x s1 conf). 
  destruct e1;inversion H0. subst.
  unfold configTransition in Heqe0.
  remember (execAction (extendValEnv (datastate conf) v, nil) (stepActions s1)
              (filter
                 (fun e : event_definition =>
                  match eventKind e with
                  | Internal => true
                  | Imported => false
                  | Exported => true
                  end) (events M))). 
  destruct e1;inversion Heqe0. clear H4.
  destruct v1.
  inversion Heqe0;subst. simpl in H2.
  SearchAbout updateControlState.
  unfold updateControlState in H2.
  
  assert (sce = x \/ ~ (sce = x)).
  apply excluded_middle.   destruct H3;auto.
  SearchAbout updateScenarioState'.
  SearchAbout traces.
  SearchAbout getStep'.
  SearchAbout stpStMap'. 
  apply updateCSNoChange in H2;auto. contradiction. 
Qed.


Lemma constructConfigSceStateStep: forall M (conf c: configuration M)  e sce s,
    
    correct_configuration conf ->
    Result c = constructConfig sce e conf ->
    In (sce, s) (controlstate c) ->
    stpStMapEquiv' M ->
    correctStateEvStepMap' M ->
    (exists stp, In stp (traces sce) /\ (pro_state stp = s)) .
Proof.
  
  intros.
  rename H2 into stpEquiv.
  rename H3 into corMap. 
  unfold constructConfig in H0.
  remember (getScenarioState sce (controlstate conf)). 
  destruct o;inversion H0;auto. clear H3.
  remember (transEvMapFunc (stateEvDefInstanceMap M) (Some s0, Some (eventDefinition e))).
  destruct o;inversion H0;auto. clear H3.
  remember (findEventInstance e (datastate conf) l).
  destruct o;inversion H0. clear H3.
  remember (createValueEnv (eventArgs e0) (eventParams (eventDefinition e)) (eventArguments e)). 
  destruct e1;inversion H0. clear H3. 
  remember (getStep' conf sce e0).
  destruct o;inversion H0. clear H3.
  remember (configTransition (extendValEnv (datastate conf) v) e e0 sce s1 conf). 
  destruct e1;inversion H0. subst.
  unfold configTransition in Heqe0.
  
  remember (execAction (extendValEnv (datastate conf) v, nil) (stepActions s1)
              (filter
                 (fun e : event_definition =>
                  match eventKind e with
                  | Internal => true
                  | Imported => false
                  | Exported => true
                  end) (events M))). 
  destruct e1;inversion Heqe0. clear H3.
  destruct v1.
  inversion Heqe0;subst. simpl in H1.
  clear Heqe0. clear H0.
  
  unfold updateControlState in H1.
  
  unfold stpStMapEquiv' in stpEquiv.
  unfold correctStateEvStepMap' in corMap.
  
  apply getStepMap' with (s:=s0) in Heqo2;auto.
  symmetry in Heqo2. apply stpStMapEquivLem in Heqo2;auto.
  apply  corMap in Heqo2.
  exists s1. destruct Heqo2.
  split;auto.
  SearchAbout updateScenarioState'.
  apply updateCSIn in H1;auto.
  destruct H;auto. 
  
Qed.



Lemma innerCombineFuncStepState: forall M confList (conf  conf' : configuration M) sce s,
    Some conf' = innerCombineFunc'''' conf confList ->
    In (sce,s) (controlstate conf') ->
    ~ In (sce,s) (controlstate conf) ->
    (exists conf'', In conf'' confList /\ In (sce,s) (controlstate conf'')).
Proof.
  intros ? confList;induction confList.
  - intros.
    simpl in H. inversion H.
  - intros. rename H1 into nre. 
    simpl in H.

    destruct confList. 

     remember (mergeConfigFunc' conf conf a).
    destruct e;inversion H.
    subst.

    unfold mergeConfigFunc' in Heqe.
    remember (mergeDataStateFunc (datastate conf) (datastate conf) (datastate a) ).
    destruct e;inversion Heqe. clear H2.
    remember (mergeControlStateFunc (controlstate conf) (controlstate conf) (controlstate a)).   destruct e;inversion Heqe. clear H2. inversion Heqe. 
    rewrite H2 in H0;simpl in *;subst. clear Heqe.
    clear H. 
    pose proof mergeCSState.
    remember Heqe1.
    clear Heqe.
    apply H with (p:=(sce,s)) in e;auto.
    destruct e. contradiction.
    exists a. split. left;auto. auto.

    
    remember (innerCombineFunc'''' conf (c::confList)).
    destruct o;inversion H. clear H2.
    remember (mergeConfigFunc' conf a c0 ).
    destruct e;inversion H;subst.
    unfold mergeConfigFunc' in Heqe.
    remember (mergeDataStateFunc (datastate conf) (datastate a) (datastate c0) ).
    destruct e;inversion Heqe. clear H2.
    remember (mergeControlStateFunc (controlstate conf) (controlstate a) (controlstate c0)).   destruct e;inversion Heqe.
    rewrite H2 in H0;simpl in *;subst. clear Heqe.
    clear H.
    pose proof mergeCSState.
    remember Heqe1.
    clear Heqe.
    apply H with (p:=(sce,s)) in e;auto.
    destruct e. Focus 2. apply IHconfList with (conf:=conf) in H1;auto.
    destruct H1. exists x. destruct H1.  split.  right;auto. auto.
    exists a. split. left;auto. auto.
   
Qed.

Lemma stateScenarioMapSync: forall M (conf conf' : configuration M) e sce s,
  correct_configuration conf ->
  synchrony conf conf' e ->
  In (sce, s) (controlstate conf') ->
  stpStMapEquiv' M ->
  correctStateEvStepMap' M ->
  stateSceIn M ->
  In (sce, s) (stateScenarioMap M). 
Proof.
  intros.
   rename H2 into stpEquiv.
  rename H3 into corMap.  rename H4 into stIn.
  pose proof domControlSync.  
assert (dom (controlstate conf) = dom (controlstate conf')).
eapply H2. apply H0.
assert (In sce (dom (controlstate conf'))).
SearchAbout dom. 
eapply domIn;auto. apply H1;auto.
assert (In (sce, s) (controlstate conf) \/ ~ In (sce, s) (controlstate conf)).
  apply excluded_middle. 
  destruct H5.
  destruct H.
  apply   sceStateCorrect ;auto.
   
inversion H0.
unfold combineFunc in H7.
remember (constructConfigList (dom (controlstate conf)) e conf). 
destruct e0;inversion H7.
unfold constructConfigList in Heqe0.
destruct v;inversion H9.

clear H9. clear H7. destruct v. 
remember (mergeConfigFunc' conf conf c).
destruct e0;inversion H10. subst.
unfold mergeConfigFunc' in Heqe1.
remember (mergeDataStateFunc (datastate conf) (datastate conf) (datastate c)).
destruct e0;inversion Heqe1.
remember (mergeControlStateFunc (controlstate conf) (controlstate conf) (controlstate c) ).
destruct e0;inversion Heqe1.
rewrite H9 in H1;simpl in H1.
clear Heqe1. clear H9. clear H8.
pose proof mergeCSState.
apply H7 with (p:=(sce,s)) in Heqe3;auto.
destruct Heqe3. contradiction.
pose proof termL2.
assert (exists sce : scenario, In sce (filter
               (fun x : scenario => inList event_definition_dec (eventDefinition e) (alphabet x))
               (filterList (finishedscenarios conf) (dom (controlstate conf)) scenario_dec)) /\ Result c = constructConfig sce e conf).
apply H9 with (lst:=(c::nil)) ;auto.
split;auto. left;auto.
destruct H11. destruct H11.
assert (sce = x).
eapply constructConfigSceState.
apply H. apply H12. apply H5. auto. 
subst.
pose proof constructConfigSceStateStep.
apply H13 with (s:=s) in H12;auto.
destruct H12. destruct H12.
unfold stateSceIn in stIn.
apply stIn;auto.
Focus 2.
exists x0. split. auto. right;auto.
rewrite <- H3 in H4.
destruct H.
rewrite <- cs_consist;auto.


remember (innerCombineFunc'''' conf (c0 :: v)).
destruct o;inversion H10.

remember (mergeConfigFunc' conf c c1).
destruct e0;inversion H8.
subst.
unfold mergeConfigFunc' in Heqe1.
remember (mergeDataStateFunc (datastate conf) (datastate c) (datastate c1)).
destruct e0;inversion Heqe1.
remember (mergeControlStateFunc (controlstate conf) (controlstate c) (controlstate c1) ).
destruct e0;inversion Heqe1.
rewrite H11 in H1;simpl in H1.
clear Heqe1. clear H11. clear H9.


pose proof mergeCSState.
remember Heqe3. clear Heqe1. 
apply H7 with (p:=(sce,s)) in e0;auto.
destruct e0.


pose proof termL2.
assert (exists sce : scenario, In sce (filter
               (fun x : scenario => inList event_definition_dec (eventDefinition e) (alphabet x))
               (filterList (finishedscenarios conf) (dom (controlstate conf)) scenario_dec)) /\ Result c = constructConfig sce e conf).
apply H11 with (lst:=(c::c0::v)) ;auto.
split;auto. left;auto.
destruct H12. destruct H12.
assert (sce = x).
eapply constructConfigSceState.
apply H. apply H13. apply H5. auto. 
subst.
pose proof constructConfigSceStateStep.
apply H14 with (s:=s) in H13;auto.
destruct H13. destruct H13.
unfold stateSceIn in stIn.
apply stIn;auto.
Focus 2.
exists x0. split. auto. right;auto.
rewrite <- H3 in H4.
destruct H. rewrite <- cs_consist;auto.
pose proof innerCombineFuncStepState. 
assert ( exists conf'' : configuration M, In conf'' (c0::v) /\ In (sce, s) (controlstate conf'')). 
apply H11 with (conf:=conf) (conf':=c1);auto.
destruct H12.
destruct H12.
pose proof termL2.
assert (exists sce : scenario, In sce ((filter
               (fun x : scenario => inList event_definition_dec (eventDefinition e) (alphabet x))
               (filterList (finishedscenarios conf) (dom (controlstate conf)) scenario_dec))) /\ Result x = constructConfig sce e conf). 
apply H14 with (lst:=c::c0::v);auto.
split;auto. right;auto.
destruct H15. 
destruct H15.
pose proof constructConfigSceState.
assert (sce = x0).
eapply H17.
apply H.
apply H16. apply H5. apply H13.
subst.

pose proof constructConfigSceStateStep.
apply H18 with (s:=s) in H16;auto.
destruct H16. destruct H16.
unfold stateSceIn in stIn.
apply stIn;auto.
Focus 2.
exists x1. split. auto. right;auto.
rewrite <- H3 in H4.
destruct H.
rewrite <- cs_consist;auto.
Qed.

Lemma constructConfigSceEventMapEqFin: forall M (conf conf':configuration M) re sce,
    Result conf' = constructConfig sce re conf ->
    dom (sceEventMap conf') = finishedscenarios conf'.
Proof.
  intros. 
  pose proof smedl_common_lemmas.termL3.
  pose proof finishedScenarioInEventMap.
  rewrite H1 with (sce:=sce) (re:=re) (conf:=conf);auto. 
  rewrite H0 with (sce:=sce) (e:=re) (conf:=conf);auto. 
Qed.

Lemma mergeConfigFuncSceEVentMapEqFin: forall M (conf conf1 conf2 conf3:configuration M),
    dom (sceEventMap conf1) = finishedscenarios conf1 ->
    dom (sceEventMap conf2) = finishedscenarios conf2 ->
    Result conf3 = mergeConfigFunc' conf conf1 conf2 ->
    dom (sceEventMap conf3) = finishedscenarios conf3. 
Proof.
  intros.
  unfold mergeConfigFunc' in H1.
  destruct (mergeDataStateFunc (datastate conf) (datastate conf1) (datastate conf2));inversion H1.
  destruct (mergeControlStateFunc (controlstate conf) (controlstate conf1) (controlstate conf2));inversion H1.
  simpl.
  rewrite domApp. 
  rewrite H;rewrite H0;auto.   
Qed.


Lemma mergeConfigFuncSceEVentMapEqFin': forall M (conf conf1 conf2 conf3:configuration M),
    Permutation (dom (sceEventMap conf1)) (finishedscenarios conf1) ->
    Permutation (dom (sceEventMap conf2)) (finishedscenarios conf2) ->
    Result conf3 = mergeConfigFunc' conf conf1 conf2 ->
    Permutation (dom (sceEventMap conf3)) (finishedscenarios conf3). 
Proof.
  intros.
    
  unfold mergeConfigFunc' in H1.
  destruct (mergeDataStateFunc (datastate conf) (datastate conf1) (datastate conf2));inversion H1.
  destruct (mergeControlStateFunc (controlstate conf) (controlstate conf1) (controlstate conf2));inversion H1.
  simpl.
  rewrite domApp. 
  SearchAbout Permutation.   apply Permutation_app;auto.
 
Qed.



Lemma innerSceEVentMapEqFin: forall M l (conf  c: configuration M)  ,
    Permutation (dom (sceEventMap conf)) (finishedscenarios conf) -> 
    Some c =  innerCombineFunc'''' conf l ->
    (forall conf', In conf' l ->
                   Permutation (dom (sceEventMap conf')) (finishedscenarios conf')) ->
    Permutation (dom (sceEventMap c)) (finishedscenarios c). 
Proof.
  intros M l;induction l.
  - intros.
    simpl in H0.  inversion H0. 
  -  intros.
     simpl in H0.
     destruct l.
     remember (mergeConfigFunc' conf conf a).
     destruct e;inversion H0.
     subst.
     
     apply mergeConfigFuncSceEVentMapEqFin' with (conf:=conf) (conf1:=conf) (conf2:=a);auto.
          
     apply H1;auto.
     left;auto.
     remember (innerCombineFunc'''' conf (c0 :: l)).
     destruct o;inversion H0.
     clear H3.
     remember (mergeConfigFunc' conf a c1).
     destruct e;inversion H0.
     subst.
      apply mergeConfigFuncSceEVentMapEqFin' with (conf:=conf) (conf1:=a) (conf2:=c1);auto.      
      apply H1;auto.
      left;auto.
      apply IHl with (conf:=conf);auto.
      intros.
      apply H1;auto.
      right;auto.
Qed.

Lemma sceEventMapEqFin: forall M (conf conf':configuration M) e,
    correct_configuration conf ->
    synchrony conf conf' e ->
    Permutation (dom (sceEventMap conf')) (finishedscenarios conf').
Proof.
  
  intros.
  remember H0.
  clear Heqs.
  unfold synchrony in s.
  destruct s.
  unfold combineFunc in H2.
  remember (constructConfigList (dom (controlstate conf)) e conf).
  unfold constructConfigList in Heqe0.   
  destruct e0;inversion H2.
  destruct v;inversion H2.
  clear H5.
  remember (innerCombineFunc'''' conf (c :: v)).
  destruct o;inversion H2.
  simpl.
  apply innerSceEVentMapEqFin with (l:=c::v) (conf:=conf);auto.
  destruct H;auto.
  intros.
  Check termL2.
  assert (exists sce : scenario, In sce (filter
               (fun x : scenario => inList event_definition_dec (eventDefinition e) (alphabet x))
               (filterList (finishedscenarios conf) (dom (controlstate conf)) scenario_dec)) /\ Result conf'0 = constructConfig sce e conf).
  apply termL2 with (conf:=conf) (e:=e) (lst:=c::v);auto.
  destruct H6.
  destruct H6.
  apply constructConfigSceEventMapEqFin in H7;auto.
  rewrite H7.
  SearchAbout Permutation.
   apply  Permutation_refl.  
Qed.


Lemma constructConfigListMapEvent'':
  forall (lst : list scenario) (e : raisedEvent) (sce : scenario) (M : monitor) (conf : configuration M)
    (v : list (configuration M)) (c : configuration M) x,
  Result v = constructConfigList' lst e conf ->
  Some c = innerCombineFunc'''' conf v ->
  ~ (In (sce, x) (sceEventMap conf)) ->
  In (sce, x) (sceEventMap c) ->
  
  In sce lst. 
Proof.
  intro lst;induction lst.
  - intros.
    simpl in H.   inversion H;subst.   simpl in H0. inversion H0.
  - intros. 
    simpl in H.
    remember (constructConfig a e conf).
    destruct e0;inversion H.
    clear H4.
    remember (constructConfigList' lst e conf ).
    destruct e0;inversion H. subst.
    assert (sce = a \/ sce <> a).
    apply excluded_middle.
    
    destruct H3. left;auto.
    right.
    simpl in H0.

    destruct v1. 
    remember (mergeConfigFunc' conf conf v0).
    destruct e0;inversion H0.
    subst.
      apply mergeConfigEventMap with (e:=x ) (sce:=sce) in Heqe2;auto.
    destruct Heqe2.
    apply H5 in H2. destruct H2.
    exfalso;apply H1. auto. 
    remember Heqe0. clear Heqe2.
    apply finishedScenarioInEventMap in Heqe0.
    rewrite Heqe0 in H2.
    destruct H2;inversion H2. subst;contradiction.
    
    
    remember (innerCombineFunc'''' conf (c0::v1)).
    destruct o;inversion H0.
    remember (mergeConfigFunc' conf v0 c1).
    clear H5.
    destruct e0;inversion H0.
    subst.
    apply mergeConfigEventMap with (e:=x ) (sce:=sce) in Heqe2;auto.
    destruct Heqe2.
    apply H5 in H2. destruct H2.
   
    apply finishedScenarioInEventMap in Heqe0.
    rewrite Heqe0 in H2.
    destruct H2;subst;inversion H2. subst. contradiction.
    apply IHlst with (e:=e) (sce:=sce) (x:=x) in Heqo;auto.
    
Qed.

Lemma syncMapNotFinish': forall M (conf conf' : configuration M) e ev sce,
  synchrony conf conf' e ->
  ~ In (sce, ev) (sceEventMap conf) ->
  In (sce, ev) (sceEventMap conf') ->
  ~ (In sce (finishedscenarios conf)).
Proof.
  intros.
  remember H. 
  clear Heqs.
  unfold synchrony in s.
  destruct s.
  
  unfold combineFunc in H3.
  remember (constructConfigList
           (dom (controlstate conf))
           e conf).
  destruct e0;inversion H3.
  destruct v;inversion H5. clear H5. clear H3.


  destruct v. 
    remember (mergeConfigFunc' conf conf c ). 
   destruct e0;inversion H6. 
   unfold  removeEventFromConf in H4.
   rewrite <- H4 in H1;simpl in H1.
    unfold mergeConfigFunc' in Heqe1. 
  remember (mergeDataStateFunc (datastate conf) (datastate conf) (datastate c)). 
  destruct e0;inversion Heqe1.
  remember (mergeControlStateFunc (controlstate conf) (controlstate conf) (controlstate c)). 
  destruct e0;inversion H5.
  rewrite H7 in H1;simpl in H1.
  rewrite in_app_iff in H1.   destruct H1. contradiction. 
  unfold constructConfigList in Heqe0.
  pose proof termL2.
  assert (exists sce : scenario, In sce (filter
               (fun x : scenario => inList event_definition_dec (eventDefinition e) (alphabet x))
               (filterList (finishedscenarios conf) (dom (controlstate conf)) scenario_dec)) /\ Result c = constructConfig sce e conf). 
  apply H3 with (lst:=c::nil);auto.
  split;auto. left;auto.
  destruct H8. destruct H8.
   apply finishedScenarioInEventMap in H9. rewrite H9 in H1. destruct H1;inversion H1.
   apply filter_In in H8. destruct H8. rewrite H11 in H8. apply filterL1 in H8;auto.

   
  
  remember (innerCombineFunc'''' conf (c0::v)).
  destruct o;inversion  H6.
  remember (mergeConfigFunc' conf c c1).
  destruct e0;inversion H4.
  unfold removeEventFromConf in H5.
  rewrite <- H5 in H1. simpl in H1.
  unfold constructConfigList in Heqe0.
  remember ((filter
               (fun x : scenario => inList event_definition_dec (eventDefinition e) (alphabet x))
               (filterList (finishedscenarios conf) (dom (controlstate conf)) scenario_dec))). 
  destruct l.
  simpl in Heqe0.
  inversion Heqe0.
  simpl in Heqe0.
  remember (constructConfig s e conf ).
  destruct e0;inversion Heqe0.
  clear H7.
  remember (constructConfigList' l e conf). 
  destruct e0;inversion Heqe0. rewrite <- H7 in Heqe2. rewrite <- H8 in Heqe3.
  unfold mergeConfigFunc' in Heqe1. 
  remember (mergeDataStateFunc (datastate conf) (datastate c) (datastate c1)). 
  destruct e0;inversion Heqe1.
  remember (mergeControlStateFunc (controlstate conf) (controlstate c) (controlstate c1)). 
  destruct e0;inversion H9.
  rewrite H10 in H1;simpl in H1.
  rewrite in_app_iff in H1.   destruct H1. Focus 2. 
  clear H10. clear H9. clear H5. 
  clear Heqe1.   pose proof  constructConfigListMapEvent''.
    
  assert (In sce l).
  subst. 
  apply H3 with (e:=e) (conf:=conf) (v:=c0::v) (c:=c1) (x:=ev);auto.
  (* assert (uniqList (s::l)). rewrite Heql.  apply filterUniq.
   apply uniqListFilter. destruct H;auto. destruct H;auto. inversion H7;auto. assert (incl (s::l) (dom (controlstate conf))).
   rewrite Heql.  unfold incl. intros. apply filter_In in H7. destruct H7. apply filterL2 in H7;auto.  unfold incl in H7. unfold incl. intros. apply H7.  right;auto.
*)
  (* intros.


     unfold not. intros.
     assert (In sce1 ( filter
           (fun x : scenario => inList event_definition_dec (eventDefinition e) (alphabet x))
           (filterList (finishedscenarios conf) (dom (controlstate conf)) scenario_dec))).
     rewrite <- Heql.   right;auto.
      assert (In sce2 ( filter
           (fun x : scenario => inList event_definition_dec (eventDefinition e) (alphabet x))
           (filterList (finishedscenarios conf) (dom (controlstate conf)) scenario_dec))).
      rewrite <- Heql.   right;auto.
      apply filter_In in H9;apply filter_In in H10. destruct H9;destruct H10. 
      apply reverseinListLemma in H11;apply reverseinListLemma in H12;auto.       unfold noIntersection in H8. destruct H8. apply H8 in H11;contradiction.
     *) 
   
   
   assert (In sce (s::l)). right;auto. rewrite Heql in H9. apply filter_In in H9.
   destruct H9. apply filterL1 in H9;auto.
   apply finishedScenarioInEventMap in Heqe2. rewrite Heqe2 in H1. destruct H1;inversion H1.
   assert (In sce (s::l)). left;auto. rewrite Heql in H3. apply filter_In in H3.
   destruct H3. apply filterL1 in H3;auto. 

Qed.


Check finishedScenarioInEventMap.




Lemma constructConfigListMapEventDef':
  forall (lst : list scenario) (e : raisedEvent) (sce : scenario) (M : monitor) (conf : configuration M)
    (v : list (configuration M)) (c : configuration M) (x:event_definition),

  In sce lst ->
  Result v = constructConfigList' lst e conf ->
  Some c = innerCombineFunc'''' conf v ->
  ~ In (sce, x) (sceEventMap conf) ->
  In (sce, x) (sceEventMap c) ->
  
  x = eventDefinition e.
Proof.
  
    intro lst;induction lst. 
    - intros.
      simpl in H0. inversion H0. subst. simpl in H1. inversion H1.
    - intros. rename H2 into scenot. rename H3 into H7. (* rename H4 into noInter. *)
      simpl in H0.
      remember (constructConfig a e conf ).
      destruct e0;inversion H0.
      remember (constructConfigList' lst e conf ).
      destruct e0;inversion H0. subst.
      simpl in H1.


      destruct v1.
     +
      remember (mergeConfigFunc' conf conf v0) .
    destruct e0;inversion H1. subst.
    
      unfold mergeConfigFunc' in Heqe2.
      destruct (mergeDataStateFunc (datastate conf) (datastate conf) (datastate v0));inversion Heqe2.      clear H4. destruct (mergeControlStateFunc (controlstate conf) (controlstate conf) (controlstate v0) );inversion Heqe2. rewrite  H4 in H7. simpl in H7.
      rewrite in_app_iff in H7.
      destruct H7.
      contradiction.  (*destruct H4.
      rewrite H4 in Heqe0.*)
      apply finishedScenarioInEventMap in Heqe0. rewrite Heqe0 in H2. destruct H2;inversion H2.
  auto.    
      
    +
      
      remember (innerCombineFunc'''' conf (c0::v1)).
      destruct o;inversion H1.
      remember (mergeConfigFunc' conf v0 c1).
      destruct e0;inversion H1. subst.
      unfold mergeConfigFunc' in Heqe2.
      destruct (mergeDataStateFunc (datastate conf) (datastate v0) (datastate c1));inversion Heqe2.      clear H5. destruct (mergeControlStateFunc (controlstate conf) (controlstate v0) (controlstate c1) );inversion Heqe2. rewrite  H5 in H7. simpl in H7.
      rewrite in_app_iff in H7.
      destruct H7.
      *   apply finishedScenarioInEventMap in Heqe0. rewrite Heqe0 in H2. destruct H2;inversion H2.
  auto.    
   
      *       
      (*destruct H4.
      rewrite H4 in Heqe0.
      *)
     
      pose proof constructConfigListMapEvent''.
      assert (In sce lst). 
      apply H6 with (e:=e) (conf:=conf) (v:=c0::v1) (c:=c1) (x:=x);auto.       
   
     
     (* 
 intros. apply noInter;right;auto. 
rewrite H4 in H2. inversion H2;subst. contradiction.*)

      
      pose proof termL2'.
      assert (exists conf' : configuration M, Result conf' = constructConfig sce e conf).    
      eapply H8. symmetry in Heqe1. apply Heqe1. auto.
      destruct H9.
      apply IHlst with (e:=e) (conf:=conf) (v:=c0::v1) (c:=c1) (x:=x) (sce:=sce) in Heqe1;auto.

Qed.

Print correct_configuration .


Lemma syncMapFinishEventDef': forall M (conf conf' : configuration M) e ev sce,
 
  synchrony conf conf' e ->
  ~ In (sce, ev) (sceEventMap conf) ->
  In (sce, ev) (sceEventMap conf') ->
  ev = eventDefinition e.
Proof.

   intros.
  remember H. 
  clear Heqs.
  unfold synchrony in s.
  destruct s.
  
  unfold combineFunc in H3.
  remember (constructConfigList
           (dom (controlstate conf))
           e conf).
  destruct e0;inversion H3.
  destruct v;inversion H5. clear H5. clear H3.

  destruct v. 
    remember (mergeConfigFunc' conf conf c ). 
   destruct e0;inversion H6. 
   unfold  removeEventFromConf in H4.
   rewrite <- H4 in H1;simpl in H1.
    unfold mergeConfigFunc' in Heqe1. 
  remember (mergeDataStateFunc (datastate conf) (datastate conf) (datastate c)). 
  destruct e0;inversion Heqe1.
  remember (mergeControlStateFunc (controlstate conf) (controlstate conf) (controlstate c)). 
  destruct e0;inversion H5.
  rewrite H7 in H1;simpl in H1.
  rewrite in_app_iff in H1.   destruct H1. contradiction. 
  unfold constructConfigList in Heqe0.
  pose proof termL2.
  assert (exists sce : scenario, In sce (filter
               (fun x : scenario => inList event_definition_dec (eventDefinition e) (alphabet x))
               (filterList (finishedscenarios conf) (dom (controlstate conf)) scenario_dec)) /\ Result c = constructConfig sce e conf). 
  apply H3 with (lst:=c::nil);auto.
  split;auto. left;auto.
  destruct H8. destruct H8.
   apply finishedScenarioInEventMap in H9. rewrite H9 in H1. destruct H1;inversion H1.
auto.

  remember (innerCombineFunc'''' conf (c0::v)).
  destruct o;inversion  H6.
  remember (mergeConfigFunc' conf c c1).
  destruct e0;inversion H4.
  unfold removeEventFromConf in H5.
  rewrite <- H5 in H1. simpl in H1.
  unfold constructConfigList in Heqe0.
  remember ((filter
               (fun x : scenario => inList event_definition_dec (eventDefinition e) (alphabet x))
               (filterList (finishedscenarios conf) (dom (controlstate conf)) scenario_dec))). 
  destruct l.
  simpl in Heqe0.
  inversion Heqe0.
  simpl in Heqe0.
  remember (constructConfig s e conf ).
  destruct e0;inversion Heqe0.
  clear H7.
  remember (constructConfigList' l e conf). 
  destruct e0;inversion Heqe0. rewrite <- H7 in Heqe2. rewrite <- H8 in Heqe3.
  unfold mergeConfigFunc' in Heqe1. 
  remember (mergeDataStateFunc (datastate conf) (datastate c) (datastate c1)). 
  destruct e0;inversion Heqe1.
  remember (mergeControlStateFunc (controlstate conf) (controlstate c) (controlstate c1)). 
  destruct e0;inversion H9.
  rewrite H10 in H1;simpl in H1.
  rewrite in_app_iff in H1.   destruct H1.
Focus 2.   clear H10. clear H9. clear H5. 
  clear Heqe1.
  
  apply constructConfigListMapEventDef' with (sce:=sce) (lst:=l) (conf:=conf) (v:=c0::v) (c:=c1);auto.


 (* assert (uniqList (s::l)). rewrite Heql.  apply filterUniq.
   apply uniqListFilter. destruct H;auto. destruct H;auto. inversion H6;auto. assert (incl (s::l) (dom (controlstate conf))).
   rewrite Heql.  unfold incl. intros. apply filter_In in H6. destruct H6. apply filterL2 in H6;auto.  unfold incl in H6. unfold incl. intros. apply H6.  right;auto.
  *)
  
   apply constructConfigListMapEvent'' with (sce:=sce) (lst:=l) (conf:=conf) (v:=c0::v) (c:=c1) (e:=e) (x:=ev);auto.

  (*   assert (uniqList (s::l)). rewrite Heql.  apply filterUniq.
   apply uniqListFilter. destruct H;auto. destruct H;auto. inversion H6;auto. assert (incl (s::l) (dom (controlstate conf))).
   rewrite Heql.  unfold incl. intros. apply filter_In in H6. destruct H6. apply filterL2 in H6;auto.  unfold incl in H6. unfold incl. intros. apply H6.  right;auto.*)

   
 (*  intros.

   
     unfold not. intros.
     assert (In sce1 (filter
           (fun x : scenario => inList event_definition_dec (eventDefinition e) (alphabet x))
           (filterList (finishedscenarios conf) (dom (controlstate conf)) scenario_dec))).
     rewrite <- Heql.   right;auto.
       assert (In sce2 (filter
           (fun x : scenario => inList event_definition_dec (eventDefinition e) (alphabet x))
           (filterList (finishedscenarios conf) (dom (controlstate conf)) scenario_dec))).
      rewrite <- Heql.   right;auto.
      apply filter_In in H11;apply filter_In in H12;destruct H11;destruct H12. 
      apply reverseinListLemma in H13;apply reverseinListLemma in H14;auto.       unfold noIntersection in H10. destruct H10. apply H10 in H13;contradiction.

        intros.

   
     unfold not. intros.
     assert (In sce1 (filter
           (fun x : scenario => inList event_definition_dec (eventDefinition e) (alphabet x))
           (filterList (finishedscenarios conf) (dom (controlstate conf)) scenario_dec))).
     rewrite <- Heql.   right;auto.
       assert (In sce2 (filter
           (fun x : scenario => inList event_definition_dec (eventDefinition e) (alphabet x))
           (filterList (finishedscenarios conf) (dom (controlstate conf)) scenario_dec))).
      rewrite <- Heql.   right;auto.
      apply filter_In in H11;apply filter_In in H12;destruct H11;destruct H12. 
      apply reverseinListLemma in H13;apply reverseinListLemma in H14;auto.       unfold noIntersection in H10. destruct H10. apply H10 in H13;contradiction.

*)      

      
   apply finishedScenarioInEventMap in Heqe2. rewrite Heqe2 in H1. destruct H1;inversion H1.
  auto.    

 
Qed.
Lemma domInRev: forall (A B:Type) (s:A) env,
    In s (dom env) ->
(exists (x:B), In (s,x) env).
Proof. intros.
generalize dependent s. 

induction env;intros.
- inversion H.
- destruct H.  destruct a. simpl in *. subst.
  exists b;left;auto.
  apply IHenv in H.
  destruct H.
  exists x;right;auto.   
Qed.

Lemma termL5: forall M (conf conf' : configuration M) e,
    correct_configuration conf ->
    synchrony conf conf' e  ->
    wellFormedRaisedEvent e ->
    stateEvDefInstanceMapEquivEListProp M ->
    stateEvDefInstanceMapEquiv M ->
    transEvMapProp M ->
     stpStMapEquiv' M ->
     correctStateEvStepMap' M ->
    stateSceIn M ->
    correct_configuration conf'.
Proof. intros. rename H1 into wellForm. rename H2 into sd1. rename H3 into sd2.
       rename  H4 into sd3. rename H5 into sd4. rename H6 into sd5. rename H7 into sd6. remember H. clear Heqc.
destruct H. split. 

pose proof domControlSync.  
assert (dom (controlstate conf) = dom (controlstate conf')).
eapply H. apply H0.

 rewrite <-  H1. auto.
Focus 2.  pose proof uniqSync.
assert (uniqList (dom (controlstate conf')) /\ uniqList (finishedscenarios conf')).
apply H with (conf:=conf) (e:=e);auto. destruct H1;auto.
Focus 2.  pose proof uniqSync. assert (uniqList (dom (controlstate conf')) /\ uniqList (finishedscenarios conf')).
apply H with (conf:=conf) (e:=e);auto. destruct H1;auto.  
Focus 2.  pose proof incluSync. apply H with (conf:=conf) (e:=e);auto.
intros.   apply scenarioStateNotNone. auto.
auto.
Focus 3.
rewrite <- cs_consist.
pose proof domControlSync.  
symmetry. eapply H. apply H0.
Focus 3.
rewrite <- ds_dom_eq.
SearchAbout dom2.
SearchAbout dom2. 
pose proof domControlSync.  
symmetry.
apply syncDSDom2 with (e:=e);auto. 
apply syncTyEnv with (conf:=conf) (e:=e);auto.
intros. 
SearchAbout events.
assert (In e0 (raisedevents conf) \/ ~ In e0 (raisedevents conf)).
apply excluded_middle.
destruct H1.
apply raise_in in H1.

auto.
pose proof syncEvents.
remember H0. clear Heqs. 
apply H2 with (e':=e0) in H0;auto.
auto.
apply syncEvnConsit with (conf:=conf) (e:=e);auto.
intros.
pose proof raised_wellform'.
apply H1 with (conf:=conf) (conf':=conf') (e:=e);auto.
intros.
assert (In re (raisedevents conf) \/ ~In re (raisedevents conf)).
apply excluded_middle. destruct H1. apply raisedType in H1. auto. Check raisedIntervalSync.
Locate raisedIntervalSync. 
apply raisedIntervalSync with (conf':=conf') (e:=e) in H1;auto.
intros.
eapply stateScenarioMapSync;auto. apply c. apply H0. auto.
apply sceEventMapEqFin with (conf:=conf) (e:=e);auto.
intros.
assert (In (sce,e0) (sceEventMap conf) \/ ~ (In (sce,e0) (sceEventMap conf))).
apply excluded_middle.
destruct H1.
apply sceEventMapAlphabet in H1;auto. 

(*syncFinishedMap*)
assert (~ (exists e, In (sce, e) (sceEventMap conf))).
unfold not;intros.
destruct H2.
apply domIn in H2.
rewrite sceEventMapRange in H2. 
apply syncMapNotFinish' with (conf:=conf) (e:=e) in H;auto.                         
pose proof syncMapFinishEventDef'.
assert (e0 = eventDefinition e).
apply H3 with (M:=M) (conf:=conf) (conf':=conf') (sce:=sce);auto.
subst.

pose proof sceEventMapEqFin.

assert (Permutation (dom (sceEventMap conf')) (finishedscenarios conf')).
apply H4 with (conf:=conf) (e:=e);auto.
apply domIn in H. 
SearchAbout Permutation.
assert (In sce ((finishedscenarios conf'))).
eapply Permutation_in.
apply H5. 
auto.   
assert (~ In sce (dom (sceEventMap conf))).
unfold not;intros.

apply domInRev in H7. 
contradiction.
rewrite sceEventMapRange in H7.
apply syncFinish with (M:=M) (conf:=conf) (conf':=conf');auto.

intros.
assert (In (sce, e0) (sceEventMap conf) \/ ~In (sce, e0) (sceEventMap conf)).
apply excluded_middle.
destruct H1.
apply raise_in_finished with (sce:=sce);auto.
pose proof syncMapFinishEventDef'.
assert (e0 = eventDefinition e).
apply H2 with (M:=M) (conf:=conf) (conf':=conf') (sce:=sce);auto.
rewrite  H3. apply raise_in;auto.
unfold synchrony in H0. intuition;auto. 
intros.
assert (In (sce, e0) (sceEventMap conf) \/ ~In (sce, e0) (sceEventMap conf)).
apply excluded_middle.
destruct H1.
apply raisedType_finished with (sce:=sce);auto.
pose proof syncMapFinishEventDef'.
assert (e0 = eventDefinition e).
apply H2 with (M:=M) (conf:=conf) (conf':=conf') (sce:=sce);auto.
rewrite  H3. apply raisedType;auto.
unfold synchrony in H0;intuition. 

Qed.



  
Lemma termL5': forall M (conf conf' : configuration M) e,
    chainMerge conf conf' e  ->
    wellFormedRaisedEvent e ->
    stateEvDefInstanceMapEquivEListProp M ->
    stateEvDefInstanceMapEquiv M ->
    transEvMapProp M ->
      stpStMapEquiv' M ->
     correctStateEvStepMap' M ->
    stateSceIn M ->
    correct_configuration conf'. 
Proof.
  
  intros.
  induction H.
  - apply termL5 with (conf:=conf) (e:=event);auto.
    destruct H;auto.
  - apply termL5 with (conf:=conf') (e:=event2);auto;(try ( rewrite <-monitorObjNoChangeChain with (conf:=conf) (e:=event1);auto)).
    pose proof raised_wellform'.
    remember H7.
    clear Heqs.
    unfold synchrony in H7. destruct H7. 
    assert (correct_configuration conf').
    apply IHchainMerge;auto.
    destruct H10.
    apply  raised_wellform'0. auto. 
Qed.

Lemma chainMergeInitialEvent:
  forall M (conf conf' : configuration M) (e : raisedEvent),
    chainMerge conf conf' e -> (In e (raisedevents conf)). 
Proof. intros. 
       induction H;auto.
      unfold synchrony in H0. destruct H0;auto. 
Qed.


Lemma raisedInterval: forall M (conf conf' : configuration M) e e',   chainMerge conf conf' e -> In e' (raisedevents conf') -> basicPreconditionMon M -> eventKind (eventDefinition e') = Internal.
Proof.
  intros. rename H1 into bp. 
  induction H.
  pose proof raisedIntervalSync.
  apply H2 with (conf:=conf) (conf':=conf') (e:=event);auto.
  destruct H;auto.
  unfold not. intros.
  remember H1. clear Heqs. unfold synchrony in s. destruct s.
  remember H.  clear Heqi. destruct H.
  destruct H6.
  destruct ((raisedevents conf)).
  inversion H6.
  assert (l=nil). destruct l. auto. inversion H6.
  rewrite H8 in H3; rewrite H8 in H4.
  destruct H3;inversion H3;destruct H4;inversion H4. (*subst.*)
 
  assert (eventDefinition event <> eventDefinition e').
  apply raisedEventNoImported with (conf:=conf) (conf':=conf');auto.
  apply basic';auto. rewrite H4 in H3. rewrite H3 in H11. contradiction.
  assert (In e' (raisedevents conf') \/ ~ In e' (raisedevents conf')). 
  apply excluded_middle.
  destruct H2.   apply IHchainMerge in H2;auto.
  apply raisedIntervalSync with (conf:=conf') (conf':=conf'') (e:=event2);auto.
  destruct bp.
  repeat match goal with
            | [ H: _ /\ _ |- _ ] => destruct H

           end.
  apply termL5' with (conf:=conf) (e:=event1);auto.
  remember H. clear Heqc.
  apply chainMergeInitial in c. destruct c. destruct H14.
  apply raised_wellform'0 . 
  apply chainMergeInitialEvent in H;auto.   
Qed.


Lemma chainMergeFinMap: forall M (conf conf' : configuration M) e sce,
    noMergeError' M ->
    basicPrecondition conf e ->
    chainMerge conf conf' e ->
    (In sce (finishedscenarios conf') <-> (exists ev, In (sce, ev) (sceEventMap conf'))). 
Proof. 
  intros.
  generalize dependent sce. rename H into noMerge. rename H0 into bp. rename H1 into H. 
  induction H.
  -  remember H0. clear Heqs.
     unfold synchrony in H0.
     destruct H0.
     unfold combineFunc in H1.
     remember (constructConfigList (dom (controlstate conf)) event conf).
     destruct e;inversion H1.
     destruct v;inversion H1.
     clear H1. clear H3.


     destruct v. 


      remember (mergeConfigFunc' conf conf c ).
     destruct e;inversion H4.
     unfold removeEventFromConf. simpl.
      unfold mergeConfigFunc' in Heqe0.
     destruct ( mergeDataStateFunc (datastate conf) (datastate conf) (datastate c));inversion Heqe0.
     destruct ( mergeControlStateFunc (controlstate conf) (controlstate conf) (controlstate c));inversion H3. simpl. 
     clear Heqe0.
 
     split.
     {
       intros.
       rewrite in_app_iff in H1.
       destruct H1.
       destruct H.
        repeat match goal with
            | [ H: _ /\ _ |- _ ] => destruct H

             end.
        rewrite H8 in H1.  inversion H1.
        exists (eventDefinition event).
        rewrite in_app_iff.
        right.
        unfold constructConfigList in Heqe.
        pose proof termL2.
        assert (exists sce : scenario, In sce (filter
              (fun x : scenario =>
               inList event_definition_dec (eventDefinition event) (alphabet x))
              (filterList (finishedscenarios conf) (dom (controlstate conf)) scenario_dec)) /\ Result c = constructConfig sce event conf).
        apply H6 with  (lst:=c::nil) ;auto. split;auto. left;auto.
        destruct H7.
        destruct H7.
        apply filter_In in H7.
        destruct H7.
        remember H8. clear Heqe0. 
        apply termL3 in H8.
        rewrite H8 in H1.
        destruct H1. rewrite H1 in e.
        apply finishedScenarioInEventMap in e.
        rewrite e. left;auto. inversion H1.
     }
     intros.
     destruct H1.
     rewrite in_app_iff in H1.
     destruct H1.
     destruct H.
        repeat match goal with
            | [ H: _ /\ _ |- _ ] => destruct H

             end.
        rewrite H9 in H1.  inversion H1.
        rewrite in_app_iff.
     right. 
     unfold constructConfigList in Heqe.
      pose proof termL2.
        assert (exists sce : scenario, In sce (filter
              (fun x : scenario =>
               inList event_definition_dec (eventDefinition event) (alphabet x))
              (filterList (finishedscenarios conf) (dom (controlstate conf)) scenario_dec)) /\ Result c = constructConfig sce event conf).
        apply H6 with  (lst:=c::nil) ;auto. split;auto. left;auto.
        destruct H7.
        destruct H7.
        apply filter_In in H7.
        destruct H7.
        remember H8. clear Heqe0.
        apply finishedScenarioInEventMap in e.
      
        rewrite e in H1.
        destruct H1;inversion H1.  rewrite H11 in H8.
        apply termL3 in H8. 
        rewrite H8.   left;auto.
        

     remember (innerCombineFunc'''' conf (c0::v)).
     destruct o;inversion H4.
     unfold constructConfigList in Heqe.
     remember ((filter
              (fun x : scenario =>
               inList event_definition_dec (eventDefinition event) (alphabet x))
              (filterList (finishedscenarios conf) (dom (controlstate conf)) scenario_dec))). 
     destruct l.
     simpl in Heqe. inversion Heqe.
     simpl in Heqe.
     remember (constructConfig s0 event conf).
     destruct e;inversion Heqe. clear H3.
     remember (constructConfigList' l event conf).
     destruct e;inversion Heqe. subst. 
     remember (mergeConfigFunc' conf v0 c1).
     destruct e;inversion H2.
     unfold removeEventFromConf;simpl.
     unfold mergeConfigFunc' in Heqe2.
     destruct ( mergeDataStateFunc (datastate conf) (datastate v0) (datastate c1));inversion Heqe2.
     destruct ( mergeControlStateFunc (controlstate conf) (controlstate v0) (controlstate c1));inversion H5. simpl.
     clear Heqe.  clear Heqe2.
     clear H5.
     split.
     {
     intros.
     assert (~ In sce (finishedscenarios conf)).
     unfold not. intros.
     destruct H.
       repeat match goal with
            | [ H: _ /\ _ |- _ ] => destruct H

              end.
       
     rewrite H9 in H5. inversion H5. 
     rewrite in_app_iff in H1. 
     destruct H1.
     Focus 2. 
     exists (eventDefinition event).
     rewrite in_app_iff. right.
    
     pose proof finishedscenarioInAll.
     assert (In sce l \/ In sce (finishedscenarios conf)).
     apply H7 with (v:=c0::v) (c:=c1) (e:=event);auto.
     assert (uniqList (s0::l)).
     rewrite Heql.
   
     apply filterUniq.
     apply uniqListFilter;destruct H;destruct H;auto.
     inversion H8;auto.
     assert (incl (s0::l) (dom (controlstate conf))).
     unfold incl;intros. rewrite Heql in H8.
     apply filter_In in H8.
     destruct H8.
     apply filterL2 in H8;auto.
     unfold incl. intros. unfold incl in H8.
     apply H8;right;auto.
     destruct H8. Focus 2. contradiction.
     pose proof termL2'.
     assert (exists conf' : configuration M, Result conf' = constructConfig sce event conf).
     apply H9 with (scs:=l) (lst:=c0::v);auto.
     destruct H10.
    
     pose proof constructConfigListMap.
     apply H11 with (lst:=l) (conf:=conf) (v:=c0::v) ;auto.
     destruct H;auto. 
      assert (uniqList (s0::l)).
     rewrite Heql.
     apply filterUniq.
     apply uniqListFilter;destruct H;destruct H;auto.
     inversion H12;auto.
     assert (incl (s0::l) (dom (controlstate conf))).
     unfold incl;intros. rewrite Heql in H12.
     apply filter_In in H12.
     destruct H12.
     apply filterL2 in H12;auto.
     unfold incl. intros. unfold incl in H12.
     apply H12;right;auto.
     intros. unfold not. intros.
     assert (In sce1 (filter
           (fun x : scenario => inList event_definition_dec (eventDefinition event) (alphabet x))
           (filterList (finishedscenarios conf) (dom (controlstate conf)) scenario_dec))).
     rewrite <- Heql.   right;auto.
      assert (In sce2 (filter
           (fun x : scenario => inList event_definition_dec (eventDefinition event) (alphabet x))
           (filterList (finishedscenarios conf) (dom (controlstate conf)) scenario_dec))).
      rewrite <- Heql.   right;auto.
      apply filter_In in H15;apply filter_In in H16;destruct H15;destruct H16. 
      apply reverseinListLemma in H17;apply reverseinListLemma in H18;auto.       unfold noIntersection in H14. apply H14 in H17.  inversion H17. auto.  
     
     remember Heqe0.
     clear Heqe. 
     apply termL3 in Heqe0.
     rewrite Heqe0 in H1. destruct H1;inversion H1.
     exists (eventDefinition event).
     rewrite in_app_iff. left.
     apply finishedScenarioInEventMap in e;auto.
     rewrite e. rewrite H7. left;auto.
}

     intros.
     destruct H1.
     rewrite in_app_iff in H1.
     destruct H1.

     (*Focus 2. 
     rewrite in_app_iff.
     right.
     Focus 2.
      *)
     
     rewrite in_app_iff.
   left.   
     remember Heqe0. clear Heqe.
     
     apply finishedScenarioInEventMap in e;auto.
     rewrite e in H1. destruct H1;inversion H1.
     apply termL3 in Heqe0.
     rewrite Heqe0. left. auto.
     assert ( ~ (exists ev : event_definition, In (sce, ev) (sceEventMap conf))).
     unfold not. intros.
     destruct H5.
     destruct H.
      repeat match goal with
            | [ H: _ /\ _ |- _ ] => destruct H

             end.
      rewrite H10 in H5.    inversion H5.
       rewrite in_app_iff. right. 
      pose proof constructConfigListMapEvent. 
      assert (In sce l).
      apply H7 with (e:=event) (conf:=conf) (v:=c0::v) (c:=c1) (x:=x);auto.
      destruct H;auto.
        assert (uniqList (s0::l)).
     rewrite Heql.
     apply filterUniq.
     apply uniqListFilter;destruct H;destruct H;auto.
     inversion H8;auto.
     assert (incl (s0::l) (dom (controlstate conf))).
     unfold incl;intros. rewrite Heql in H8.
     apply filter_In in H8.
     destruct H8.
     apply filterL2 in H8;auto.
     unfold incl. intros. unfold incl in H8.
     apply H8;right;auto.
     intros.

     unfold not. intros.
     assert (In sce1 (filter
           (fun x : scenario => inList event_definition_dec (eventDefinition event) (alphabet x))
           (filterList (finishedscenarios conf) (dom (controlstate conf)) scenario_dec))).
     rewrite <- Heql.   right;auto.
      assert (In sce2 (filter
           (fun x : scenario => inList event_definition_dec (eventDefinition event) (alphabet x))
           (filterList (finishedscenarios conf) (dom (controlstate conf)) scenario_dec))).
      rewrite <- Heql.   right;auto.
      apply filter_In in H11;apply filter_In in H12;destruct H11;destruct H12. 
       apply reverseinListLemma in H13;apply reverseinListLemma in H14;auto.       unfold noIntersection in H10. destruct H10. apply H10 in H13;contradiction. 
     
     clear H6.
     pose proof termL2'.
     assert (exists conf' : configuration M, Result conf' = constructConfig sce event conf). 
     apply H6 with (scs:=l) (lst:=c0::v);auto.
     destruct H9.
     pose proof finishedInList.
     apply H10 with (lst:=l) (e:=event) (conf:=conf) (v:=c0::v);auto.
       assert (uniqList (s0::l)).
     rewrite Heql.
     apply filterUniq.
     apply uniqListFilter;destruct H;destruct H;auto.
     inversion H11;auto.
     assert (incl (s0::l) (dom (controlstate conf))).
     unfold incl;intros. rewrite Heql in H11.
     apply filter_In in H11.
     destruct H11.
     apply filterL2 in H11;auto.
     unfold incl. intros. unfold incl in H11.
     apply H11;right;auto.
     destruct H;auto.

     intros.

     unfold not. intros.
     assert (In sce1 (filter
           (fun x : scenario => inList event_definition_dec (eventDefinition event) (alphabet x))
           (filterList (finishedscenarios conf) (dom (controlstate conf)) scenario_dec))).
     rewrite <- Heql.   right;auto.
      assert (In sce2 (filter
           (fun x : scenario => inList event_definition_dec (eventDefinition event) (alphabet x))
           (filterList (finishedscenarios conf) (dom (controlstate conf)) scenario_dec))).
      rewrite <- Heql.   right;auto.
      apply filter_In in H14;apply filter_In in H15;destruct H14;destruct H15. 
      apply reverseinListLemma in H16;apply reverseinListLemma in H17;auto.       unfold noIntersection in H13. destruct H13. apply H13 in H16;contradiction.
    
  - assert (forall sce : scenario,
                 In sce (finishedscenarios conf') <->
                 (exists ev : event_definition, In (sce, ev) (sceEventMap conf'))). 
    apply IHchainMerge;auto.
    split.
    {
      intros.
      destruct H1 with sce.
      assert (In sce (finishedscenarios conf') \/ ~ In sce (finishedscenarios conf')).
      apply excluded_middle.
      destruct H5.
      remember H5. clear Heqi. 
      apply H3 in H5.
      destruct H5.
      exists x.
      SearchAbout sceEventMap.
      apply sceEventMapNoChangeSync with (conf:=conf') (e:=event2);auto.
      destruct bp.
      repeat match goal with
            | [ H: _ /\ _ |- _ ] => destruct H

             end.
      apply termL5' with (conf:=conf) (e:=event1);auto.
      destruct H6.
      apply raised_wellform'0;auto. 
    
      exists (eventDefinition event2).
      SearchAbout sceEventMap.
      apply syncFinishedMap with (conf:=conf');auto.

       destruct bp.
      repeat match goal with
            | [ H: _ /\ _ |- _ ] => destruct H

             end.
      apply termL5' with (conf:=conf) (e:=event1);auto.
      destruct H6.
      apply raised_wellform'0;auto. 
    
     

      auto.
      destruct bp.
      split;auto.

       
      repeat match goal with
            | [ H: _ /\ _ |- _ ] => destruct H

             end.
      apply termL5' with (conf:=conf) (e:=event1);auto.
      destruct H6.
      apply raised_wellform'0;auto. 
      
     
        repeat match goal with
            | [ H: _ /\ _ |- _ ] => destruct H

             end.
        auto.
      split;auto.
      split;auto.
      Focus 2.
      split;auto.
      split;auto. 
      split;auto.
      unfold synchrony in H0.  split;auto. split;auto.
destruct H0;auto.      
    } 
    intros.
    
    
    destruct H1 with sce.
    assert ((exists ev : event_definition, In (sce, ev) (sceEventMap conf')) \/ ~ (exists ev : event_definition, In (sce, ev) (sceEventMap conf'))).
    apply excluded_middle. destruct H5.
    
    remember H5. clear Heqe.
    apply H4 in H5.
    pose proof finishedInvariantSync. 
    apply H6 with (conf:=conf') (e:=event2);auto.
   
    
      unfold synchrony in H0.
    destruct H0.
    unfold combineFunc in H6.
    remember (constructConfigList (dom (controlstate conf')) event2 conf').
    destruct e;inversion H6. clear H8.
    destruct v;inversion H6. clear H6.

   
    destruct v. 
     remember (mergeConfigFunc' conf' conf' c). 
    destruct e;inversion H8.
    unfold removeEventFromConf. simpl.
    unfold mergeConfigFunc' in Heqe0.
     destruct ( mergeDataStateFunc (datastate conf') (datastate conf') (datastate c));inversion Heqe0.
     destruct ( mergeControlStateFunc (controlstate conf') (controlstate conf') (controlstate c));inversion H9. simpl;simpl in *. unfold  removeEventFromConf in H7.
     rewrite <- H7 in H2. simpl in H2. 
     rewrite H10 in H2. simpl in H2. 
     clear H9;clear H10. clear H7. clear Heqe0.
     destruct H2.
     rewrite in_app_iff in H2.
     destruct H2.
     Focus 2.
    unfold constructConfigList in Heqe.
     pose proof termL2.
     assert (exists sce : scenario, In sce (filter
              (fun x : scenario =>
               inList event_definition_dec (eventDefinition event2) (alphabet x))
              (filterList (finishedscenarios conf') (dom (controlstate conf')) scenario_dec)) /\ Result c = constructConfig sce event2 conf').
        apply H6 with  (lst:=c::nil) ;auto. split;auto.  left;auto.
        destruct H7.
        destruct H7.
        apply filter_In in H7.
        destruct H7.
        remember H9. clear Heqe0.
        apply finishedScenarioInEventMap in e.
        rewrite e in H2.
        destruct H2;inversion H2.
        apply termL3 in H9. rewrite <- H12. rewrite in_app_iff;right. rewrite H9. left;auto.
        exfalso;apply H5.   exists x;auto.

    
    remember (innerCombineFunc'''' conf' (c0::v)).
    destruct o;inversion H8.
    remember (mergeConfigFunc' conf' c c1).
    destruct e;inversion H7.
    unfold removeEventFromConf. simpl.
    unfold removeEventFromConf in H9.
    rewrite <- H9 in H2. simpl in H2.
     unfold mergeConfigFunc' in Heqe0.
     destruct ( mergeDataStateFunc (datastate conf') (datastate c) (datastate c1));inversion Heqe0.
     destruct ( mergeControlStateFunc (controlstate conf') (controlstate c) (controlstate c1));inversion H10. simpl. 
     rewrite H11 in H2. simpl in H2. 
     clear H11;clear H10. clear H9. clear Heqe0.
     destruct H2.
     rewrite in_app_iff in H2.
     destruct H2.
     
     rewrite in_app_iff. left;auto. 
     unfold constructConfigList in Heqe.
     pose proof termL2.
     
     assert (exists sce : scenario, In sce (filter
              (fun x : scenario =>
               inList event_definition_dec (eventDefinition event2) (alphabet x))
              (filterList (finishedscenarios conf') (dom (controlstate conf')) scenario_dec)) /\ Result c = constructConfig sce event2 conf').
        apply H6 with  (lst:=c::c0::v) ;auto. split;auto.  left;auto.
        destruct H9.
        destruct H9.
        apply filter_In in H9.
        destruct H9.
        remember H10. clear Heqe0.
        apply finishedScenarioInEventMap in e.
        rewrite e in H2.
        destruct H2;inversion H2.
        apply termL3 in H10. rewrite <- H13. rewrite H10. left;auto. 
    rewrite in_app_iff. 
    right.
   
    pose proof constructConfigListMapEvent.
    
    unfold constructConfigList in Heqe.
    remember ((filter
              (fun x : scenario =>
               inList event_definition_dec (eventDefinition event2) (alphabet x))
              (filterList (finishedscenarios conf') (dom (controlstate conf')) scenario_dec))).
    destruct l. simpl in Heqe.  inversion Heqe.
    simpl in Heqe.
    destruct (constructConfig s event2 conf');inversion Heqe.
    remember (constructConfigList' l event2 conf').
    destruct e;inversion Heqe. subst. 
    assert (In sce l).
    apply H6 with (e:=event2) (conf:=conf') (v:=c0::v) (c:=c1) (x:=x);auto.

     destruct bp.
      repeat match goal with
            | [ H: _ /\ _ |- _ ] => destruct H

             end.
      apply termL5' with (conf:=conf) (e:=event1);auto.
      destruct H9.
      apply raised_wellform'0;auto. 

      auto.
      destruct bp.
      split;auto.

     
      repeat match goal with
            | [ H: _ /\ _ |- _ ] => destruct H

             end.
      apply termL5' with (conf:=conf) (e:=event1);auto.
      destruct H9.
      apply raised_wellform'0;auto.
      
      
        repeat match goal with
            | [ H: _ /\ _ |- _ ] => destruct H

             end.
      auto.
      split;auto.
      split;auto.
      
      split;auto.
      split;auto. 
      split;auto. split;auto. split;auto. 
     assert (uniqList (s::l)).
  rewrite Heql.
  apply filterUniq;auto.
  apply uniqListFilter;auto.

  assert (correct_configuration conf').
destruct bp.
      
  repeat match goal with
            | [ H: _ /\ _ |- _ ] => destruct H

             end.
      apply termL5' with (conf:=conf) (e:=event1);auto.
      destruct H9.
      apply raised_wellform'0;auto.
  destruct H9;auto.       

   assert (correct_configuration conf').
destruct bp.
      
  repeat match goal with
            | [ H: _ /\ _ |- _ ] => destruct H

             end.
      apply termL5' with (conf:=conf) (e:=event1);auto.
      destruct H9.
      apply raised_wellform'0;auto.
      destruct H9;auto.
      
   
inversion H9;auto. 


 assert (incl (s::l) (dom (controlstate conf'))).
     unfold incl;intros. rewrite Heql in H9.
     apply filter_In in H9.
     destruct H9.
     apply filterL2 in H9;auto.
     unfold incl. intros. unfold incl in H9.
     apply H9;right;auto.

     intros.

     unfold not. intros.
     assert (In sce1 ( filter
           (fun x : scenario => inList event_definition_dec (eventDefinition event2) (alphabet x))
           (filterList (finishedscenarios conf') (dom (controlstate conf')) scenario_dec))).
     rewrite <- Heql.   right;auto.
       assert (In sce2 ( filter
           (fun x : scenario => inList event_definition_dec (eventDefinition event2) (alphabet x))
           (filterList (finishedscenarios conf') (dom (controlstate conf')) scenario_dec))).
      rewrite <- Heql.   right;auto.
      apply filter_In in H13;apply filter_In in H14;destruct H13;destruct H14. 
       apply reverseinListLemma in H15;apply reverseinListLemma in H16;auto.       unfold noIntersection in H12. destruct H12. apply H12 in H15;contradiction. 
     
     pose proof finishedInList.
     apply H11 with (lst:=l) (e:=event2) (conf:=conf') (v:=c0::v);auto. 
       assert (uniqList (s::l)).
  rewrite Heql.
  apply filterUniq;auto.
  
  apply uniqListFilter;auto.
 
    assert (correct_configuration conf').
destruct bp.
      
  repeat match goal with
            | [ H: _ /\ _ |- _ ] => destruct H

             end.
      apply termL5' with (conf:=conf) (e:=event1);auto.
      destruct H12.
      apply raised_wellform'0;auto.
      destruct H12;auto.

      assert (correct_configuration conf').
      destruct bp.
      
  repeat match goal with
            | [ H: _ /\ _ |- _ ] => destruct H

             end.
      apply termL5' with (conf:=conf) (e:=event1);auto.
      destruct H12.
      apply raised_wellform'0;auto.
      destruct H12;auto.

  inversion H12;auto.
   assert (incl (s::l) (dom (controlstate conf'))).
     unfold incl;intros. rewrite Heql in H12.
     apply filter_In in H12.
     destruct H12.
     apply filterL2 in H12;auto.
     unfold incl. intros. unfold incl in H12.
     apply H12;right;auto.

       destruct bp.
      repeat match goal with
            | [ H: _ /\ _ |- _ ] => destruct H

             end.
      apply termL5' with (conf:=conf) (e:=event1);auto.
      destruct H12.
      apply raised_wellform'0;auto.

      auto.
      destruct bp.
      split;auto.

       repeat match goal with
            | [ H: _ /\ _ |- _ ] => destruct H

             end.
      apply termL5' with (conf:=conf) (e:=event1);auto.
      destruct H12.
      apply raised_wellform'0;auto.

     
        repeat match goal with
            | [ H: _ /\ _ |- _ ] => destruct H

               end.
        
      auto.
      split;auto.
      split;auto.
      
      split;auto.
      split;auto. 
      split;auto.
      split;auto. 
      split;auto.


        intros.

     unfold not. intros.
     assert (In sce1 ( filter
           (fun x : scenario => inList event_definition_dec (eventDefinition event2) (alphabet x))
           (filterList (finishedscenarios conf') (dom (controlstate conf')) scenario_dec))).
     rewrite <- Heql.   right;auto.
       assert (In sce2 ( filter
           (fun x : scenario => inList event_definition_dec (eventDefinition event2) (alphabet x))
           (filterList (finishedscenarios conf') (dom (controlstate conf')) scenario_dec))).
      rewrite <- Heql.   right;auto.
      apply filter_In in H15;apply filter_In in H16;destruct H15;destruct H16. 
      apply reverseinListLemma in H17;apply reverseinListLemma in H18;auto.       unfold noIntersection in H14. destruct H14. apply H14 in H17;contradiction.
 
Qed.

Lemma constructConfigListMapEvent':
  forall (lst : list scenario) (e : raisedEvent) (sce : scenario) (M : monitor) (conf : configuration M)
    (v : list (configuration M)) (c : configuration M) x,
  correct_configuration conf ->
  noMergeError' M ->
  basicPrecondition conf e ->
  uniqList lst ->
  incl lst (dom (controlstate conf)) ->
  Result v = constructConfigList' lst e conf ->
  Some c = innerCombineFunc'''' conf v ->
  ~ (In (sce, x) (sceEventMap conf)) ->
  In (sce, x) (sceEventMap c) ->
  (forall sce1 sce2, In sce1 lst -> In sce2 lst -> ~ noIntersection (alphabet sce1) (alphabet sce2)) ->  
  In sce lst. 
Proof.
  intro lst;induction lst.
  - intros.
    simpl in H4.   inversion H4;subst.   simpl in H5. inversion H5.
  - intros. rename H8 into noInter. 
    simpl in H4.
    remember (constructConfig a e conf).
    destruct e0;inversion H4.
    clear H9.
    remember (constructConfigList' lst e conf ).
    destruct e0;inversion H4. subst.
    assert (sce = a \/ sce <> a).
    apply excluded_middle.
    
    destruct H8. left;auto.
    right.
    simpl in H5.

    destruct v1. 
    remember (mergeConfigFunc' conf conf v0).
    destruct e0;inversion H5.
    subst.
      apply mergeConfigEventMap with (e:=x ) (sce:=sce) in Heqe2;auto.
    destruct Heqe2.
    apply H10 in H7. destruct H7.
    exfalso;apply H6. auto. 
    remember Heqe0. clear Heqe2.
    apply finishedScenarioInEventMap in Heqe0.
    rewrite Heqe0 in H7.
    destruct H7;inversion H7. subst;contradiction.
    
    
    remember (innerCombineFunc'''' conf (c0::v1)).
    destruct o;inversion H5.
    remember (mergeConfigFunc' conf v0 c1).
    clear H10.
    destruct e0;inversion H5.
    subst.
    apply mergeConfigEventMap with (e:=x ) (sce:=sce) in Heqe2;auto.
    destruct Heqe2.
    apply H10 in H7. destruct H7.
   
    apply finishedScenarioInEventMap in Heqe0.
    rewrite Heqe0 in H7.
    destruct H7;subst;inversion H7. subst. contradiction.
    apply IHlst with (e:=e) (sce:=sce) (x:=x) in Heqo;auto.
    inversion H2;auto.
    unfold incl in H3. unfold incl. intros.
    apply H3;right;auto.
    intros;apply noInter;right;auto. 
Qed.

Lemma syncMapNotFinish: forall M (conf conf' : configuration M) e ev sce,
  correct_configuration conf ->
  noMergeError' M ->
  basicPrecondition conf e ->
  synchrony conf conf' e ->
  ~ In (sce, ev) (sceEventMap conf) ->
  In (sce, ev) (sceEventMap conf') ->
  ~ (In sce (finishedscenarios conf)).
Proof.
  intros.
  remember H2. 
  clear Heqs.
  unfold synchrony in s.
  destruct s.
  
  unfold combineFunc in H6.
  remember (constructConfigList
           (dom (controlstate conf))
           e conf).
  destruct e0;inversion H6.
  destruct v;inversion H8. clear H8. clear H6.


  destruct v. 
    remember (mergeConfigFunc' conf conf c ). 
   destruct e0;inversion H9. 
   unfold  removeEventFromConf in H7.
   rewrite <- H7 in H4;simpl in H4.
    unfold mergeConfigFunc' in Heqe1. 
  remember (mergeDataStateFunc (datastate conf) (datastate conf) (datastate c)). 
  destruct e0;inversion Heqe1.
  remember (mergeControlStateFunc (controlstate conf) (controlstate conf) (controlstate c)). 
  destruct e0;inversion H8.
  rewrite H10 in H4;simpl in H4.
  rewrite in_app_iff in H4.   destruct H4. contradiction. 
  unfold constructConfigList in Heqe0.
  pose proof termL2.
  assert (exists sce : scenario, In sce (filter
               (fun x : scenario => inList event_definition_dec (eventDefinition e) (alphabet x))
               (filterList (finishedscenarios conf) (dom (controlstate conf)) scenario_dec)) /\ Result c = constructConfig sce e conf). 
  apply H6 with (lst:=c::nil);auto.
  split;auto. left;auto.
  destruct H11. destruct H11.
   apply finishedScenarioInEventMap in H12. rewrite H12 in H4. destruct H4;inversion H4.
   apply filter_In in H11. destruct H11. rewrite H14 in H11. apply filterL1 in H11;auto.

   
  
  remember (innerCombineFunc'''' conf (c0::v)).
  destruct o;inversion  H9.
  remember (mergeConfigFunc' conf c c1).
  destruct e0;inversion H7.
  unfold removeEventFromConf in H8.
  rewrite <- H8 in H4. simpl in H4.
  unfold constructConfigList in Heqe0.
  remember ((filter
               (fun x : scenario => inList event_definition_dec (eventDefinition e) (alphabet x))
               (filterList (finishedscenarios conf) (dom (controlstate conf)) scenario_dec))). 
  destruct l.
  simpl in Heqe0.
  inversion Heqe0.
  simpl in Heqe0.
  remember (constructConfig s e conf ).
  destruct e0;inversion Heqe0.
  clear H10.
  remember (constructConfigList' l e conf). 
  destruct e0;inversion Heqe0. rewrite <- H10 in Heqe2. rewrite <- H11 in Heqe3.
  unfold mergeConfigFunc' in Heqe1. 
  remember (mergeDataStateFunc (datastate conf) (datastate c) (datastate c1)). 
  destruct e0;inversion Heqe1.
  remember (mergeControlStateFunc (controlstate conf) (controlstate c) (controlstate c1)). 
  destruct e0;inversion H12.
  rewrite H13 in H4;simpl in H4.
  rewrite in_app_iff in H4.   destruct H4. Focus 2. 
  clear H13. clear H12. clear H8. 
  clear Heqe1.   pose proof  constructConfigListMapEvent'.
    
  assert (In sce l).
  subst. 
  apply H6 with (e:=e) (conf:=conf) (v:=c0::v) (c:=c1) (x:=ev);auto.
   assert (uniqList (s::l)). rewrite Heql.  apply filterUniq.
   apply uniqListFilter. destruct H;auto. destruct H;auto. inversion H8;auto. assert (incl (s::l) (dom (controlstate conf))).
   rewrite Heql.  unfold incl. intros. apply filter_In in H8. destruct H8. apply filterL2 in H8;auto.  unfold incl in H8. unfold incl. intros. apply H8.  right;auto.

   intros.

    intros.

     unfold not. intros.
     assert (In sce1 ( filter
           (fun x : scenario => inList event_definition_dec (eventDefinition e) (alphabet x))
           (filterList (finishedscenarios conf) (dom (controlstate conf)) scenario_dec))).
     rewrite <- Heql.   right;auto.
      assert (In sce2 ( filter
           (fun x : scenario => inList event_definition_dec (eventDefinition e) (alphabet x))
           (filterList (finishedscenarios conf) (dom (controlstate conf)) scenario_dec))).
      rewrite <- Heql.   right;auto.
      apply filter_In in H12;apply filter_In in H13. destruct H12;destruct H13. 
      apply reverseinListLemma in H14;apply reverseinListLemma in H15;auto.       unfold noIntersection in H11. destruct H11. apply H11 in H14;contradiction.
      
   
   
   assert (In sce (s::l)). right;auto. rewrite Heql in H12. apply filter_In in H12.
   destruct H12. apply filterL1 in H12;auto.
   apply finishedScenarioInEventMap in Heqe2. rewrite Heqe2 in H4. destruct H4;inversion H4.
   assert (In sce (s::l)). left;auto. rewrite Heql in H6. apply filter_In in H6.
   destruct H6. apply filterL1 in H6;auto. 

Qed.

Lemma constructConfigListMapEventDef:
  forall (lst : list scenario) (e : raisedEvent) (sce : scenario) (M : monitor) (conf : configuration M)
    (v : list (configuration M)) (c : configuration M) (x:event_definition),
  correct_configuration conf ->
  noMergeError' M ->
  basicPrecondition conf e ->
  uniqList lst ->
  incl lst (dom (controlstate conf)) ->
  In sce lst ->
  Result v = constructConfigList' lst e conf ->
  Some c = innerCombineFunc'''' conf v ->
  ~ In (sce, x) (sceEventMap conf) ->
  In (sce, x) (sceEventMap c) ->
  (forall sce1 sce2, In sce1 lst -> In sce2 lst -> ~ noIntersection (alphabet sce1) (alphabet sce2)) ->
  x = eventDefinition e.
Proof.
  
    intro lst;induction lst. 
    - intros.
      simpl in H5. inversion H5. subst. simpl in H6. inversion H6.
    - intros. rename H7 into scenot. rename H8 into H7. rename H9 into noInter. 
      simpl in H5.
      remember (constructConfig a e conf ).
      destruct e0;inversion H5.
      remember (constructConfigList' lst e conf ).
      destruct e0;inversion H5. subst.
      simpl in H6.


      destruct v1.
     +
      remember (mergeConfigFunc' conf conf v0) .
    destruct e0;inversion H6. subst.
    
      unfold mergeConfigFunc' in Heqe2.
      destruct (mergeDataStateFunc (datastate conf) (datastate conf) (datastate v0));inversion Heqe2.      destruct (mergeControlStateFunc (controlstate conf) (controlstate conf) (controlstate v0) );inversion H10. rewrite  H11 in H7. simpl in H7.
      rewrite in_app_iff in H7.
      destruct H7.
      contradiction.  destruct H4.
      rewrite H4 in Heqe0.
      apply finishedScenarioInEventMap in Heqe0. rewrite Heqe0 in H7. destruct H7;inversion H7.
  auto.    
       apply finishedScenarioInEventMap in Heqe0. rewrite Heqe0 in H7. destruct H7;inversion H7.
       auto.

    +
      
      remember (innerCombineFunc'''' conf (c0::v1)).
      destruct o;inversion H6.
      remember (mergeConfigFunc' conf v0 c1).
      destruct e0;inversion H6. subst.
      unfold mergeConfigFunc' in Heqe2.
      destruct (mergeDataStateFunc (datastate conf) (datastate v0) (datastate c1));inversion Heqe2.      destruct (mergeControlStateFunc (controlstate conf) (controlstate v0) (controlstate c1) );inversion H11. rewrite  H12 in H7. simpl in H7.
      rewrite in_app_iff in H7.
      destruct H7.
      *   apply finishedScenarioInEventMap in Heqe0. rewrite Heqe0 in H7. destruct H7;inversion H7.
  auto.    
   
      *       
      destruct H4.
      rewrite H4 in Heqe0.
      
     
      pose proof constructConfigListMapEvent'.
      assert (In sce lst). 
      apply H8 with (e:=e) (conf:=conf) (v:=c0::v1) (c:=c1) (x:=x);auto.       
      inversion H2;auto.
      unfold incl; unfold incl in H3. intros. apply H3;auto. right;auto.
      intros. apply noInter;right;auto. 
      rewrite H4 in H2. inversion H2;subst. contradiction.

      
      pose proof termL2'.
      assert (exists conf' : configuration M, Result conf' = constructConfig sce e conf).    
      eapply H8. symmetry in Heqe1. apply Heqe1. auto.
      destruct H13.
      apply IHlst with (e:=e) (conf:=conf) (v:=c0::v1) (c:=c1) (x:=x) in H4;auto.
      inversion H2;auto.
      unfold incl; unfold incl in H3. intros. apply H3;auto. right;auto.
      intros. apply noInter;right;auto. 
Qed. 
      
    
Lemma syncMapFinishEventDef: forall M (conf conf' : configuration M) e ev sce,
  correct_configuration conf ->
  noMergeError' M ->
  basicPrecondition conf e ->
  synchrony conf conf' e ->
  ~ In (sce, ev) (sceEventMap conf) ->
  In (sce, ev) (sceEventMap conf') ->
  ev = eventDefinition e.
Proof.

   intros.
  remember H2. 
  clear Heqs.
  unfold synchrony in s.
  destruct s.
  
  unfold combineFunc in H6.
  remember (constructConfigList
           (dom (controlstate conf))
           e conf).
  destruct e0;inversion H6.
  destruct v;inversion H8. clear H8. clear H6.

  destruct v. 
    remember (mergeConfigFunc' conf conf c ). 
   destruct e0;inversion H9. 
   unfold  removeEventFromConf in H7.
   rewrite <- H7 in H4;simpl in H4.
    unfold mergeConfigFunc' in Heqe1. 
  remember (mergeDataStateFunc (datastate conf) (datastate conf) (datastate c)). 
  destruct e0;inversion Heqe1.
  remember (mergeControlStateFunc (controlstate conf) (controlstate conf) (controlstate c)). 
  destruct e0;inversion H8.
  rewrite H10 in H4;simpl in H4.
  rewrite in_app_iff in H4.   destruct H4. contradiction. 
  unfold constructConfigList in Heqe0.
  pose proof termL2.
  assert (exists sce : scenario, In sce (filter
               (fun x : scenario => inList event_definition_dec (eventDefinition e) (alphabet x))
               (filterList (finishedscenarios conf) (dom (controlstate conf)) scenario_dec)) /\ Result c = constructConfig sce e conf). 
  apply H6 with (lst:=c::nil);auto.
  split;auto. left;auto.
  destruct H11. destruct H11.
   apply finishedScenarioInEventMap in H12. rewrite H12 in H4. destruct H4;inversion H4.
auto.

  
  remember (innerCombineFunc'''' conf (c0::v)).
  destruct o;inversion  H9.
  remember (mergeConfigFunc' conf c c1).
  destruct e0;inversion H7.
  unfold removeEventFromConf in H8.
  rewrite <- H8 in H4. simpl in H4.
  unfold constructConfigList in Heqe0.
  remember ((filter
               (fun x : scenario => inList event_definition_dec (eventDefinition e) (alphabet x))
               (filterList (finishedscenarios conf) (dom (controlstate conf)) scenario_dec))). 
  destruct l.
  simpl in Heqe0.
  inversion Heqe0.
  simpl in Heqe0.
  remember (constructConfig s e conf ).
  destruct e0;inversion Heqe0.
  clear H10.
  remember (constructConfigList' l e conf). 
  destruct e0;inversion Heqe0. rewrite <- H10 in Heqe2. rewrite <- H11 in Heqe3.
  unfold mergeConfigFunc' in Heqe1. 
  remember (mergeDataStateFunc (datastate conf) (datastate c) (datastate c1)). 
  destruct e0;inversion Heqe1.
  remember (mergeControlStateFunc (controlstate conf) (controlstate c) (controlstate c1)). 
  destruct e0;inversion H12.
  rewrite H13 in H4;simpl in H4.
  rewrite in_app_iff in H4.   destruct H4.
Focus 2.   clear H13. clear H12. clear H8. 
  clear Heqe1.
  
  Check constructConfigListMapEventDef. 
  apply constructConfigListMapEventDef with (sce:=sce) (lst:=l) (conf:=conf) (v:=c0::v) (c:=c1);auto.


  assert (uniqList (s::l)). rewrite Heql.  apply filterUniq.
   apply uniqListFilter. destruct H;auto. destruct H;auto. inversion H6;auto. assert (incl (s::l) (dom (controlstate conf))).
   rewrite Heql.  unfold incl. intros. apply filter_In in H6. destruct H6. apply filterL2 in H6;auto.  unfold incl in H6. unfold incl. intros. apply H6.  right;auto.
  
  
   apply constructConfigListMapEvent' with (sce:=sce) (lst:=l) (conf:=conf) (v:=c0::v) (c:=c1) (e:=e) (x:=ev);auto.

     assert (uniqList (s::l)). rewrite Heql.  apply filterUniq.
   apply uniqListFilter. destruct H;auto. destruct H;auto. inversion H6;auto. assert (incl (s::l) (dom (controlstate conf))).
   rewrite Heql.  unfold incl. intros. apply filter_In in H6. destruct H6. apply filterL2 in H6;auto.  unfold incl in H6. unfold incl. intros. apply H6.  right;auto.

   
   intros.

   
     unfold not. intros.
     assert (In sce1 (filter
           (fun x : scenario => inList event_definition_dec (eventDefinition e) (alphabet x))
           (filterList (finishedscenarios conf) (dom (controlstate conf)) scenario_dec))).
     rewrite <- Heql.   right;auto.
       assert (In sce2 (filter
           (fun x : scenario => inList event_definition_dec (eventDefinition e) (alphabet x))
           (filterList (finishedscenarios conf) (dom (controlstate conf)) scenario_dec))).
      rewrite <- Heql.   right;auto.
      apply filter_In in H13;apply filter_In in H14;destruct H13;destruct H14. 
      apply reverseinListLemma in H15;apply reverseinListLemma in H16;auto.       unfold noIntersection in H12. destruct H12. apply H12 in H15;contradiction.

        intros.

   
     unfold not. intros.
     assert (In sce1 (filter
           (fun x : scenario => inList event_definition_dec (eventDefinition e) (alphabet x))
           (filterList (finishedscenarios conf) (dom (controlstate conf)) scenario_dec))).
     rewrite <- Heql.   right;auto.
       assert (In sce2 (filter
           (fun x : scenario => inList event_definition_dec (eventDefinition e) (alphabet x))
           (filterList (finishedscenarios conf) (dom (controlstate conf)) scenario_dec))).
      rewrite <- Heql.   right;auto.
      apply filter_In in H13;apply filter_In in H14;destruct H13;destruct H14. 
      apply reverseinListLemma in H15;apply reverseinListLemma in H16;auto.       unfold noIntersection in H12. destruct H12. apply H12 in H15;contradiction.

      

      
   apply finishedScenarioInEventMap in Heqe2. rewrite Heqe2 in H4. destruct H4;inversion H4.
  auto.    

 
Qed.

  
  
Lemma constructConfigListMapNoDup:
  forall (lst : list scenario) (e : raisedEvent) (sce : scenario) (x : event_definition)
    (M : monitor) (conf : configuration M) (v : list (configuration M)) (c : configuration M),
  correct_configuration conf ->
  uniqList lst ->
  incl lst (dom (controlstate conf)) ->
  Result v = constructConfigList' lst e conf ->
  Some c = innerCombineFunc'''' conf v ->
  ~ (exists y, In (sce, y) (sceEventMap conf)) ->
  In (sce, x) (sceEventMap c) ->
  x = eventDefinition e. 
Proof.
  intro lst;induction lst.   
  -
    intros.
    simpl in H2. inversion H2;subst. simpl in H3. inversion H3. 
  -
    intros. rename H4 into exs. rename H5 into H4. 
    simpl in H2.
    remember (constructConfig a e conf).
    destruct e0;inversion H2.
    clear H2.
    remember (constructConfigList' lst e conf).
    destruct e0;inversion H6.
    subst.
    simpl in H3.

    destruct v1. 
    remember (mergeConfigFunc' conf conf v0). 
    destruct e0;inversion H3. subst.
     unfold  mergeConfigFunc' in Heqe2.
    remember (mergeDataStateFunc (datastate conf) (datastate conf) (datastate v0)). 
    destruct e0;inversion Heqe2.   clear H5.
    remember (mergeControlStateFunc (controlstate conf) (controlstate conf) (controlstate v0)). 
    destruct e0;inversion Heqe2.
     rewrite H5 in H4;simpl in H4.
    rewrite in_app_iff in H4.
    destruct H4.
    exfalso. apply exs. exists x;auto. 
        apply finishedScenarioInEventMap in Heqe0.
    rewrite Heqe0 in H2.
    destruct H2. inversion H2;auto. inversion H2.

    
    remember (innerCombineFunc'''' conf (c0::v1)).
    destruct o;inversion H3. clear H5.
    remember (mergeConfigFunc' conf v0 c1).
    destruct e0;inversion H3. subst.
    unfold  mergeConfigFunc' in Heqe2.
    remember (mergeDataStateFunc (datastate conf) (datastate v0) (datastate c1)). 
    destruct e0;inversion Heqe2.   clear H5.
    remember (mergeControlStateFunc (controlstate conf) (controlstate v0) (controlstate c1)). 
    destruct e0;inversion Heqe2.
    rewrite H5 in H4;simpl in H4.
    rewrite in_app_iff in H4.
    destruct H4. Focus 2. 
    apply IHlst with (sce:=sce) (conf:=conf) (v:=c0::v1) (c:=c1);auto.
    inversion H0;auto.
    unfold incl. intros. unfold incl in H1. apply H1. right;auto.
   
    apply finishedScenarioInEventMap in Heqe0.
    rewrite Heqe0 in H2.
    destruct H2. inversion H2;auto. inversion H2.

Qed.


      
Lemma chainMergeSceMapAlpha: forall M (conf conf' : configuration M) e ev sce,

     noMergeError' M ->
    basicPrecondition conf e ->
    chainMerge conf conf' e ->
    In (sce, ev) (sceEventMap conf') ->
    In ev (alphabet sce). 
Proof.
  intros. generalize dependent sce.
  rename H into noMerge.  rename H0 into bp. rename H1 into H. generalize dependent ev.
  induction H.
  -
    intros. rename H2 into H1.
  
    assert (~ exists ev', In (sce,ev') (sceEventMap conf)). 
    unfold not. intros.
   
    destruct H2.
    destruct H.
      repeat match goal with
            | [ H: _ /\ _ |- _ ] => destruct H

             end.
      rewrite H6 in H2. inversion H2.

       pose proof chainMergeFinMap.
    rename H3 into cmf.
    
       assert (In sce (finishedscenarios conf')).
    destruct cmf with (conf:=conf) (conf':=conf') (e:=event) (sce:=sce);auto.
    constructor;auto. apply H4;auto. exists ev;auto.
     rename H3 into fin. 
    
      rename H2 into sceMapNotIn. 
      remember H0. clear Heqs. rename s into syn. 
    unfold synchrony in H0.
    destruct H0.
    unfold combineFunc in H2.
    remember (constructConfigList (dom (controlstate conf)) event conf).
    destruct e;inversion H2.
    destruct v;inversion H2.
    clear H2. clear H4.



    destruct v. 
     remember (mergeConfigFunc' conf conf c ).
     destruct e;inversion H5.
     unfold removeEventFromConf in H3.
     rewrite <-  H3 in H1;simpl in H1.
     remember Heqe0. clear Heqe1.
     apply mergeConfigEventMap with (e:=ev) (sce:=sce) in Heqe0;auto.
     unfold constructConfigList in Heqe.
     
     destruct Heqe0.
     apply H4 in H1.
     destruct H1.
     exfalso;apply sceMapNotIn. exists ev;auto.
     pose proof termL2.
     assert (exists sce : scenario, In sce (filter
              (fun x : scenario =>
               inList event_definition_dec (eventDefinition event) (alphabet x))
              (filterList (finishedscenarios conf) (dom (controlstate conf)) scenario_dec)) /\ Result c = constructConfig sce event conf).
     apply H6 with (lst:=c::nil);auto.
     split;auto. left;auto.
     destruct H7. destruct H7.
     
     remember H8. clear Heqe0. 
     apply finishedScenarioInEventMap in e0.
     rewrite e0 in H1. destruct H1;inversion H1.
     rewrite <- H10.
     apply syncFinish with (conf:=conf) (conf':=conf');auto.
     destruct H;auto.
     unfold not. intros.
     destruct H. 
    repeat match goal with
            | [ H: _ /\ _ |- _ ] => destruct H

           end.
    rewrite H14 in H9;inversion H9.
    rewrite <- H3. simpl.
     unfold mergeConfigFunc' in e.
     destruct (mergeDataStateFunc (datastate conf) (datastate conf) (datastate c));inversion e. 
     destruct (mergeControlStateFunc (controlstate conf) (controlstate conf) (controlstate c));inversion H12. simpl.
     rewrite in_app_iff. right.
     
     apply termL3 in H8. rewrite H8.  left;auto.



     
    remember (innerCombineFunc'''' conf (c0::v)).
    destruct o;inversion H5.
    remember (mergeConfigFunc' conf c c1 ).
    destruct e;inversion H3.
    unfold removeEventFromConf in H4.
    rewrite <- H4 in H1. simpl in H1.
     remember Heqe0. clear Heqe1. rename e into mee. 
    apply mergeConfigEventMap with (e:=ev) (sce:=sce) in Heqe0;auto.
    destruct Heqe0.
    apply H6 in H1.
    unfold constructConfigList in Heqe.
    remember ((filter
              (fun x : scenario =>
               inList event_definition_dec (eventDefinition event) (alphabet x))
              (filterList (finishedscenarios conf) (dom (controlstate conf)) scenario_dec))).
    destruct l.
    simpl in Heqe. inversion Heqe.
    simpl in Heqe.
    remember (constructConfig s event conf ).
    destruct e;inversion Heqe.
    remember (constructConfigList' l event conf).
    destruct e;inversion Heqe. 
    
    destruct H1.
    
    remember Heqe0. clear Heqe2. rename e into csc. 
    apply finishedScenarioInEventMap in Heqe0.
    rewrite H9 in H1. 
    rewrite Heqe0 in H1. 
    destruct H1;inversion H1.
   
    apply syncFinish with (conf:=conf) (conf':=conf');auto. 
    destruct H;auto.
    unfold not. intros.
    destruct H.
     repeat match goal with
            | [ H: _ /\ _ |- _ ] => destruct H

             end.
     rewrite H15 in H7. inversion H7.
     
     
     assert (ev = eventDefinition event).
     apply constructConfigListMapNoDup with (lst:=l) (sce:=sce) (conf:=conf) (v:=c0::v) (c:=c1);auto.
     destruct H;auto.


      assert (uniqList (s::l)).
  rewrite  Heql.
  apply filterUniq.
  apply uniqListFilter.
  destruct H. destruct H;auto. destruct H;destruct H;auto.
  inversion H3;auto. inversion H7;auto. 
  unfold incl;intros.
  assert (incl (s::l) (dom (controlstate conf))).
  unfold incl;intros.
  rewrite Heql in H11.
  apply filter_In in H11.
  destruct H11.
  apply filterL2 in H11. auto.
  unfold incl in H11. apply H11. right;auto. rewrite H10;auto. 
                    
     rewrite H7.
     apply syncFinish with (conf:=conf) (conf':=conf');auto. destruct H;auto.
     destruct H;destruct H.
     repeat match goal with
            | [ H: _ /\ _ |- _ ] => destruct H

            end.
     unfold not. intros.   rewrite H12 in H14;inversion H14.
     
  - intros. rename H2 into H1. 
    assert (In (sce, ev) (sceEventMap conf') \/ ~ (In (sce, ev) (sceEventMap conf'))). 
    apply excluded_middle.
     remember H. clear Heqc. apply chainMergeInitialEvent in c.
    remember H. clear Heqc0.  apply chainMergeInitial in c0.
    destruct c0.
    
    destruct bp.
     repeat match goal with
            | [ H: _ /\ _ |- _ ] => destruct H

            end.
     rename H19 into ssp; rename H20 into sin. 
    destruct H2.
    
    apply IHchainMerge in H2. auto.
    auto.  repeat(split;auto). 
     
    assert (eventDefinition event2 = ev).
    pose proof syncMapFinishEventDef.
    symmetry. apply H19 with (conf:=conf') (conf':=conf'') (sce:=sce);auto.
    apply termL5' with (conf:=conf) (conf':=conf') (e:=event1);auto.
    destruct H3. apply raised_wellform'0;auto.
    auto.
    split;auto.
apply termL5' with (conf:=conf) (conf':=conf') (e:=event1);auto.
destruct H5. apply raised_wellform'0;auto.

split;auto;auto.
split. unfold synchrony in H0. destruct H0;auto. 
repeat(split;auto).  rewrite <- H19.  
SearchAbout (alphabet).   apply syncFinish with (conf:=conf') (conf':=conf'');auto.
 apply termL5' with (conf:=conf) (conf':=conf') (e:=event1);auto.
 destruct H5. apply raised_wellform'0;auto.
 pose proof syncMapNotFinish.
 apply H20 with (conf':=conf'') (e:=event2) (ev:=ev);auto.
  apply termL5' with (conf:=conf) (conf':=conf') (e:=event1);auto.
  destruct H5. apply raised_wellform'0;auto.
  auto.

  split.
 apply termL5' with (conf:=conf) (conf':=conf') (e:=event1);auto.
 destruct H5. apply raised_wellform'0;auto.
 split.  auto.
split.   unfold synchrony in H0. destruct H0;auto. 
repeat(split;auto). 
auto.
pose proof chainMergeFinMap.
destruct H20 with (conf:=conf) (conf':=conf'') (e:=event1) (sce:=sce);auto. 
repeat(split;auto). 

apply chain' with (conf':=conf') (event2:=event2);auto.
apply H22. exists ev;auto. 

Qed.

Check chainMergeSceMapAlpha.
Check chainMergeFinMap. 
(*chainMergeSceMapAlpha*)

Lemma finishedExistingEvents: forall M (conf conf' : configuration M) e sce,         
    noMergeError' M ->
    basicPrecondition conf e ->
    chainMerge conf conf' e ->
    In sce (finishedscenarios conf') ->
    (exists ev, In (sce, ev) (sceEventMap conf') /\ In ev (alphabet sce)). 
Proof.
  intros.
  pose proof chainMergeFinMap.
  assert ((exists ev : event_definition, In (sce, ev) (sceEventMap conf'))).
  destruct H3 with (conf:=conf) (conf':=conf') (e:=e) (sce:=sce);auto.
  destruct H4.
  exists x. split;auto.
  apply chainMergeSceMapAlpha with (conf:=conf) (e:=e) in H4;auto.
Qed. 

Lemma rangeDomIn: forall (A B:Type) (lst:list (A*B)) b  , In b (range lst) -> exists a, In (a,b) lst. 
Proof. intros A B lst;induction lst. 
       - intros. inversion H.
       - intros.
         simpl in H.
         destruct H. destruct a. simpl in H. subst. exists a;left;auto.
         destruct a. apply IHlst in H. destruct H. exists x. right;auto. 
Qed.

Lemma rangeDomInRev: forall (A B:Type) (lst:list (A*B)) a b  , In (a,b) ( lst) -> In b (range lst). 
Proof. intros A B lst;induction lst. 
       - intros. inversion H.
       - intros.
         simpl.  destruct a.
         assert (b = b0 \/ b <> b0).
         apply excluded_middle. destruct H0. subst. simpl. left;auto.
         destruct H. inversion H. symmetry in H3. contradiction.
         apply IHlst in H. right;auto. 
Qed.


Lemma usedEventLedTo: forall M (conf conf' : configuration M) re,
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
      apply chainMergeInitial in H. destruct H. destruct H. apply raised_wellform'0.
      SearchAbout chainMerge. apply chainMergeInitialEvent in c. auto.
      destruct bp. 
      repeat match goal with
            | [ H: _ /\ _ |- _ ] => destruct H

           end.    

      
      
       apply termL5' with (conf:=conf) (conf':=conf') (e:=event1);auto.
       remember H. clear Heqc. 
      apply chainMergeInitial in H. destruct H. destruct H. apply raised_wellform'0.
   apply chainMergeInitialEvent in c. auto.
  
     
      pose proof raisedEventLedTo.
      
      rewrite H4.
   eapply H5 with (conf':=conf');eauto.    
Qed.



Fixpoint getEventIdFromRaiseStmt (actList: list action) : list string :=
  match actList with
  | nil => nil
  | (RaiseStmt id _)::actList' => id :: (getEventIdFromRaiseStmt actList')
  | _ :: actList' => (getEventIdFromRaiseStmt actList')
 end.

Lemma getEventIdFromRaiseStmtApp: forall l1 l2,
    getEventIdFromRaiseStmt (l1 ++ l2) =
    getEventIdFromRaiseStmt l1 ++ getEventIdFromRaiseStmt l2. 
Proof.
  intro l1;induction l1. 
- intros. simpl;auto. 
- intros. simpl.
  destruct a;auto. 
  simpl.  f_equal;auto.
Qed.



Lemma filter_add_length':forall (A B :Type) (f: A -> bool) l1 l2,
    List.length (filter f (l1)) <=  List.length (filter f (l1 ++ l2)).
Proof. intros. generalize dependent l2.
  generalize dependent f.
  induction l1. 
       - intros. simpl;simpl in *.  induction l2. simpl. omega. simpl. destruct (f a). simpl.
         omega. auto. 
       - intros. simpl;simpl in *.
         destruct ( f a). simpl.
         assert (Datatypes.length (filter f l1) <= Datatypes.length (filter f (l1 ++ l2))). apply IHl1. omega. apply IHl1. 
Qed.     
  
Lemma filter_add_length: forall (A  :Type) (f: A -> bool) l1 l2,
    List.length (filter f (l1++l2)) <= 1 ->
    List.length (filter f (l1)) <= 1 /\ List.length (filter f (l2)) <= 1.
Proof.
  intros. generalize dependent l2.
  generalize dependent f.
  induction l1. 
  - intros. simpl;simpl in *. split;auto.
  - intros. simpl;simpl in *.
    destruct (f a );simpl.
    simpl in H. 
    assert ((Datatypes.length (filter f (l1 ++ l2))) <= 1). omega.
    apply IHl1 in H0.
    destruct H0. split;auto.
    assert ((Datatypes.length (filter f l1))  <= (Datatypes.length (filter f (l1 ++ l2)))).
    apply filter_add_length';auto. 
     omega.
     apply IHl1;auto. 
Qed.


Lemma appIncluRev: forall (A : Type) (l1 l2 l : list A),
     incl (l1 ++ l2) l -> incl l1 l /\ incl l2 l. 
Proof.
  intros.
  unfold incl in H. 
  split.
  - unfold incl. intros.
    apply H. apply in_app_iff;auto.
  - unfold incl. intros.
    apply H. apply in_app_iff;auto.
Qed.




Lemma getEventIdFromRaiseStmtNotIn': forall l1 i,
    Datatypes.length (filter (fun act : action => filterRaiseStmt act i) (l1)) = 0 ->
    ~ In i (getEventIdFromRaiseStmt l1). 
Proof.
  intro l1;induction l1. 
  - intros. unfold not. intros. inversion H0. 
  - intros. simpl in H. unfold not. intros.
    simpl in *.
    destruct a. simpl in *.  apply IHl1 in H. contradiction. simpl in *.
    apply IHl1 in H. contradiction.
    destruct H0. subst.
    simpl in H.
    destruct (string_dec i i). 
    inversion H;auto. contradiction. 
    simpl in H.  destruct (string_dec i ident). inversion H.
    apply IHl1 in H. contradiction.
    simpl in H. 
    
    apply IHl1 in H. contradiction. 
Qed.

Lemma getEventIdFromRaiseStmtNotIn: forall l1 l2 i,
    Datatypes.length (filter (fun act : action => filterRaiseStmt act i) (l1 ++ l2)) = 0 ->
    ~ In i (getEventIdFromRaiseStmt l2). 
Proof.
  intro l1;induction l1. 
  - intros. simpl in H.
    apply getEventIdFromRaiseStmtNotIn';auto.
  - intros.
    simpl in H. 
    destruct (filterRaiseStmt a i).
    inversion H.
    apply IHl1 in H;auto. 
Qed.



Lemma getEventStringApp: forall l1 l2 i,
    In i (getEventIdFromRaiseStmt l1) ->
    Datatypes.length
         (filter (fun act : action => filterRaiseStmt act i)
                 (l1 ++ l2)) <= 1 ->
    ~ In i (getEventIdFromRaiseStmt l2). 
Proof.
  intro l1;induction l1. 
-
  intros.
  simpl in H.  inversion H.
- intros.
  simpl in H.
  destruct a.
  simpl in H0. apply IHl1;auto. 
  simpl in H0. apply IHl1;auto.
  destruct H. subst.
  simpl in H0.
  destruct (string_dec i i).
  simpl in H0. 
  assert (Datatypes.length (filter (fun act : action => filterRaiseStmt act i) (l1 ++ l2)) = 0).
  
  omega.
  apply getEventIdFromRaiseStmtNotIn in H;auto. 
  contradiction.   
  
  simpl in H0.
  destruct ( string_dec i ident ).
  simpl in H0. 
  apply IHl1;auto. omega. 
  simpl in H0.
  apply IHl1;auto.
  simpl in H0.
   apply IHl1;auto.
Qed.



Lemma uniqRaiseList: forall act lst,
      (forall eventName, In eventName lst -> (Datatypes.length (filter (fun act : action => filterRaiseStmt act eventName)
                                                                       (transitionIntoBasicActionList act)) <= 1)) ->
     incl (getEventIdFromRaiseStmt (transitionIntoBasicActionList act)) lst ->
     uniqList ((getEventIdFromRaiseStmt (transitionIntoBasicActionList act))). 
Proof.
  intro act;induction act.
  - intros;simpl in *. constructor. 
  - intros. 
    simpl in H. simpl. constructor.
  - intros.
    simpl in H. simpl. constructor. constructor. unfold not. intros. inversion H1. 
    
  - simpl.  intros.
    pose proof filter_add_length.
    assert ( forall eventName : string,
      In eventName lst ->  Datatypes.length
        (filter (fun act : action => filterRaiseStmt act eventName)
           (transitionIntoBasicActionList act1)) <= 1 /\ Datatypes.length (filter (fun act : action => filterRaiseStmt act eventName)
           (transitionIntoBasicActionList act2)) <= 1). 
    intros.  apply H1;auto.
    SearchAbout incl.
     assert ((getEventIdFromRaiseStmt
                (transitionIntoBasicActionList act1 ++ transitionIntoBasicActionList act2)) = getEventIdFromRaiseStmt (transitionIntoBasicActionList act1) ++  getEventIdFromRaiseStmt (transitionIntoBasicActionList act2)).
     apply getEventIdFromRaiseStmtApp;auto.      
    
    
     rewrite H3 in H0.
     apply appIncluRev in H0.
     destruct H0. remember H0. clear Heqi. 
     apply IHact1 in H0. remember H4. clear Heqi0. 
     Focus 2. intros.
     destruct H2 with eventName;auto.
     apply IHact2 in H4.
     Focus 2. intros.
     destruct H2 with eventName;auto.
rewrite H3. 
   apply  uniqApp';auto.
   intros.
   assert (In i1 lst). 
   unfold incl in i.  apply i;auto.
   apply H in H6.
   apply getEventStringApp in H6;auto. 
   
   intros.
    assert (In i1 lst). 
   unfold incl in i0.  apply i0;auto.
   apply H in H6. unfold not. intros.
   apply getEventStringApp in H6;auto. 
  Qed.

Print getEventIdFromRaiseStmt. 
  


Lemma eventNameInList : forall lst evId ,
    In evId (map (fun ev : event_definition => eventId ev) lst) ->
    (exists ev, In ev lst /\ evId = eventId ev). 
Proof. intro lst;induction lst. 
- intros. simpl in H. inversion H. 
- intros. simpl. simpl in H.
  destruct H. subst. exists a. split;auto.
  apply IHlst in H.
  destruct H. destruct H. exists x. split;auto. 
Qed.




Lemma getEventNameMapIn : forall l x,
    getEventByName (eventId x) l = Some x ->
     In (eventId x) (map (fun ev : event_definition => eventId ev) l). 
Proof.
  intro l;induction l. 
- intros. simpl in H. inversion H. 
- intros. simpl in H. simpl.  
  destruct (string_dec (eventId a) (eventId x)).
  left;auto.
  apply IHl in H. right;auto. 
Qed.



Lemma raiseActEvent: forall c1 l1 a v ,
    HasTy_action v
                 l1 c1 ->
    In a (getEventIdFromRaiseStmt (transitionIntoBasicActionList c1)) ->
     In a (map (fun ev : event_definition => eventId ev) l1). 
Proof. intro c1;induction c1.
       - intros. simpl in *. inversion H0. 
       - intros. destruct l1. simpl in *. auto.
         simpl. simpl in *. inversion H0. 
       - intros.
         simpl in H0. destruct H0;inversion H0.
         subst. destruct l1.
         Print  HasTy_action. 
         inversion H;auto. subst.
         destruct H2. destruct H0. simpl in H0. inversion H0. 
         simpl.
         inversion H. subst.
         destruct H2. destruct H0.
         simpl in H0.
         destruct (string_dec (eventId e) a). left;auto.
         right. 
         remember H0. clear Heqe0. 
         symmetry in H0.
         SearchAbout getEventByName.
         apply getEventId in H0. subst.
         apply getEventNameMapIn;auto.
       - intros.
         inversion H. subst.
         simpl in H0.
         rewrite getEventIdFromRaiseStmtApp in H0.
         rewrite in_app_iff in H0. destruct H0. 
         apply IHc1_1 with (a:=a) in H3;auto.
          apply IHc1_2 with (a:=a) in H4;auto.
            
Qed.

Lemma mapIncl': forall (A B:Type) (f:A -> B) l a,
    In a l ->
    In (f a) (map f l). 
Proof. intros.      
       generalize dependent a.
       induction l.
       intros. inversion H.
       intros. simpl. destruct H.
       left. subst;auto. right.
       apply IHl;auto. 
Qed.

Lemma mapIncl: forall (A B:Type) (f:A -> B) l1 l,
    incl l1 l ->
    incl (map f l1) (map f l).
Proof. intros. generalize dependent l.
     induction l1. 
       -
         intros. simpl. unfold incl. intros. inversion H0. 
       - intros. simpl. unfold incl in H.
         
         unfold incl. intros.
         destruct H0. Focus 2.
         unfold incl in IHl1;auto. 
         apply IHl1;auto.  intros. apply H. right;auto. 
         
         assert (In a l).
         apply H. left;auto.
         subst.
         apply  mapIncl';auto. 
Qed.

Locate getEventIdFromRaiseStmt. 
Check filter.

SearchAbout importedOrInternalEvent.

(*check if the event is an imported or internal event*)
Definition importedOrInternalEvent_func (ev : event_definition) : bool :=
 (match eventKind ev with
  | Imported => true
  | Internal => true
  | Exported => false
  end).

Check filter. 
(*Lemma noDupEventDef: forall mon sce stp,
    noDupRaise mon ->
    In sce (scenarios mon) ->
    In stp (getTransitionsOfScenario sce) ->
    typeCheck mon ->
    uniqList 
      (getEventIdFromRaiseStmt (transitionIntoBasicActionList (stepActions stp))).*)



Lemma noDupEventDef': forall mon sce stp,
    noDupRaise'' mon ->
    In sce (scenarios mon) ->
    In stp (getTransitionsOfScenario sce) ->
    typeCheck mon ->
    uniqList 
      (getEventIdFromRaiseStmt (transitionIntoBasicActionList (stepActions stp))).
Proof.
  intros. rename H2 into tC. 
  unfold noDupRaise'' in H.
  assert (forall v, In v (events mon) -> (forall (sce : scenario) (stp : step) (acts : list action),
       In sce (scenarios mon) ->
       In stp (getTransitionsOfScenario sce) ->
       acts =
       filter (fun act : action => filterRaiseStmt act (eventId v))
         (transitionIntoBasicActionList (stepActions stp)) -> Datatypes.length acts <= 1)).   
  intros.
  assert ((eventKind v = Internal ->
       forall sce1 sce2 : scenario,
       In sce1 (scenarioRaise (scenarios mon) v) ->
       In sce2 (scenarioRaise (scenarios mon) v) ->
       sce1 <> sce2 ->
       ~
       (exists e : event_definition,
          In e (events mon) /\ triggerSce mon e sce1 /\ triggerSce mon e sce2)) /\
      (forall (sce : scenario) (stp : step) (acts : list action),
       In sce (scenarios mon) ->
       In stp (getTransitionsOfScenario sce) ->
       acts =
       filter (fun act : action => filterRaiseStmt act (eventId v))
              (transitionIntoBasicActionList (stepActions stp)) -> Datatypes.length acts <= 1)).
  
  apply H;auto. destruct H6. apply H7 with (sce:=sce0) (stp:=stp0) ;auto.
  clear H. rename H2 into H.
  pose proof uniqRaiseList. 
  apply H2 with (lst:= map (fun ev => eventId ev) (events mon)). 
  intros. 
  pose proof eventNameInList.
  remember H3. clear Heqi. apply H4 in i. destruct i. destruct H5. 
  apply H with (v:=x) (sce:=sce) (stp:=stp);auto. rewrite H6. auto. 
  unfold typeCheck in tC.
  remember H0. clear Heqi. apply tC in i. 
  unfold typeCheckScenario in i. 
  remember H1. clear Heqi0. apply i in i0.
  unfold typeCheckStep in i0.
  remember (createTypEnv (eventArgs (stepEvent stp)) (eventParams (event (stepEvent stp)))).  
  destruct e;inversion i0.
  clear i0.
  inversion H4.
  simpl in *. unfold incl. intros. inversion H5. 
  simpl. unfold incl. intros. inversion H8.
  Focus 2. simpl.
  unfold incl. intros.
  Print HasTy_action.
  SearchAbout getEventIdFromRaiseStmt.
  rewrite  getEventIdFromRaiseStmtApp in H8.
  apply in_app_iff in H8.
  destruct H8.
  assert (In a (map (fun ev : event_definition => eventId ev) (filter
            (fun e : event_definition =>
             match eventKind e with
             | Internal => true
             | Imported => false
             | Exported => true
             end) (events mon)))).
  eapply raiseActEvent. apply H6. auto. 
  Focus 2.
    assert (In a (map (fun ev : event_definition => eventId ev) (filter
            (fun e : event_definition =>
             match eventKind e with
             | Internal => true
             | Imported => false
             | Exported => true
             end) (events mon)))).
    eapply raiseActEvent. apply H7. auto.
    pose proof mapIncl.
    unfold incl in H10.
    apply H10 with (l1:=(filter
               (fun e : event_definition =>
                match eventKind e with
                | Internal => true
                | Imported => false
                | Exported => true
                end) (events mon)));auto.
    intros. apply filter_In in H11. destruct H11;auto. 
  pose proof mapIncl.
    unfold incl in H10.
    apply H10 with (l1:=(filter
               (fun e : event_definition =>
                match eventKind e with
                | Internal => true
                | Imported => false
                | Exported => true
                end) (events mon)));auto.
    intros. apply filter_In in H11. destruct H11;auto.

    
  simpl. destruct H6.
  destruct H6.
  unfold incl. intros. destruct H8;inversion H8;subst.
  assert (In a (map (fun ev : event_definition => eventId ev) (filter
            (fun e : event_definition =>
             match eventKind e with
             | Internal => true
             | Imported => false
             | Exported => true
             end) (events mon)))). 
  eapply raiseActEvent. apply H4.
  SearchAbout getEventIdFromRaiseStmt. 
  rewrite <- H5. simpl. left;auto.

  pose proof mapIncl.
    unfold incl in H10.
    apply H10 with (l1:=(filter
               (fun e : event_definition =>
                match eventKind e with
                | Internal => true
                | Imported => false
                | Exported => true
                end) (events mon)));auto.
    intros. apply filter_In in H11. destruct H11;auto.
Qed.

Print execAction. 



Lemma inExfalso: forall (A: Type) (l: list A),
    l <> nil -> ~(forall a, In a l -> ~ In a l).
Proof.
  intros. unfold not. intros.
  
  destruct l. Focus 2. apply H0 with a. left;auto. left;auto.
  contradiction. 
Qed. 

Lemma uniqAppRev: forall (A : Type) (l1 l2 : list A),
    uniqList (l1 ++ l2) ->
    uniqList l1 /\ uniqList l2. 
Proof. 
  intros.
  split.
  - generalize dependent l2.
    induction l1. intros. constructor.
    intros. constructor. simpl in *. inversion H;subst.
    apply IHl1 in H2;auto.
    inversion H;subst. unfold not. intros.
    apply H3. rewrite in_app_iff. left;auto. 
  - generalize dependent l2. induction l1.
    intros. simpl in H. auto.
    intros. simpl in H. inversion H;subst.
    apply IHl1;auto. 
Qed.

Lemma execActionIncl:  forall act v l v' l'  eventList,
    Result (v', l') =
          execAction (v, l) act
                     eventList -> incl l l'. 
Proof.
  intro act;induction act.
 - intros;simpl in *. inversion H;subst. unfold incl;intros;auto. 
 - intros. simpl in H.
    
     destruct l;inversion H. 
     destruct a;inversion H. 
     remember (evalMonad v e). destruct e0;inversion H. 
     destruct (updateValueEnvInv (AIdent s) v0 v);inversion H. subst.
     unfold incl. intros;auto.
-  intros. simpl in *. 
     remember (calculateExprList v exprs).      
     destruct e;inversion H.  
     remember (getEventByName ident eventList). 
     destruct o;inversion H.
    
     remember (parameterMatchFunc v0 (eventParams e)). 
     destruct b;inversion H.  subst.
     unfold incl. intros.  right;auto.
- intros.
     simpl in H.
     remember (execAction (v, l) act1 eventList).
     destruct e;inversion H.
     
     destruct v0.
     apply IHact1 in Heqe.
     apply IHact2 in H.
     unfold incl;unfold incl in *.
     intros. apply H. apply Heqe;auto. 
Qed.

Print raisedEvent.
Lemma uniqListNotIn: forall (A:Type) (l1 l2: list A) a,
    uniqList (l1 ++ l2) ->
    In a l2 ->
    ~ In a l1. 
Proof. intros A l1;induction l1. 
- intros. simpl in H. unfold not. intros. inversion H1. 
- intros. simpl in H. inversion H;subst.
  unfold not. intros. destruct H1. subst. apply IHl1 with (a:=a0) in H3;auto.
  apply H4. rewrite in_app_iff. right;auto.
  apply IHl1 with (a:=a0) in H3;auto. 
Qed.

Lemma execActionGetEventIdIn: forall act v0 l0 v l re eventList,
    Result (v0, l0) = execAction (v, l) act eventList ->
    ~ In re l ->
    In re l0 ->
     In (eventId (eventDefinition re))
    (getEventIdFromRaiseStmt (transitionIntoBasicActionList act)).
Proof.
  intro act;induction act.
  -  intros;simpl in *. inversion H;subst. contradiction.  
  -  intros. simpl in H.
     destruct l;inversion H. clear H3. 
     destruct a;inversion H. clear H3.
     remember (evalMonad v e). destruct e0;inversion H. clear H3.
     destruct (updateValueEnvInv (AIdent s) v1 v);inversion H. subst.
     contradiction. 
  -  intros.
     simpl;simpl in *. 
     remember (calculateExprList v exprs).      
     destruct e;inversion H.  clear H3.
     remember (getEventByName ident eventList). 
     destruct o;inversion H.
     clear H3.
     remember (parameterMatchFunc v1 (eventParams e)). 
     destruct b;inversion H.  subst.
     destruct H1. rewrite <- H1. simpl. left.
     SearchAbout getEventByName.
     apply getEventId in Heqo. auto. contradiction. 
  - intros.
     simpl in H.
     remember (execAction (v, l) act1 eventList).
     destruct e;inversion H.
     simpl. 
     destruct v1.
     rewrite getEventIdFromRaiseStmtApp. 
     remember Heqe. clear Heqe0.
     rewrite in_app_iff.
     assert (In re l1 \/ ~ In re l1).
     apply excluded_middle. destruct H2. 
     apply IHact1 with (re:=re) in Heqe;auto.   
     
     
     apply IHact2 with (re:=re)in H;auto. Qed.




Lemma raiseMapIn: forall l evId,
     In evId (map (fun re : raisedEvent => eventId (eventDefinition re)) l) ->
     exists re : raisedEvent, In re l /\ eventId (eventDefinition re) = evId.                 
Proof.
  intro l;induction l. 
- intros. simpl in H. inversion H. 
- intros. simpl. simpl in H.
  destruct H. exists a. split;auto.
  apply IHl in H. destruct H. exists x. destruct H. split;auto. 
Qed.

Lemma execActionRaisedUniq': forall act v  v' l' l eventList,
    Result (v', l') =
          execAction (v, l) act
                     eventList ->
    uniqList (getEventIdFromRaiseStmt (transitionIntoBasicActionList act)) ->
    uniqList (map (fun re => eventId (eventDefinition re)) l) ->
    (forall evId re, In evId (getEventIdFromRaiseStmt (transitionIntoBasicActionList act)) -> In re l -> evId <> (eventId (eventDefinition re))) ->
    uniqList (map (fun re => eventId (eventDefinition re)) l'). 
Proof.
  intro act;induction act.
   - intros;simpl in *. inversion H;auto. 
   - intros. simpl in H.
     simpl in H0.
     destruct l;inversion H. clear H4. 
     destruct a;inversion H. clear H4.
     remember (evalMonad v e). destruct e0;inversion H. clear H4.
     destruct (updateValueEnvInv (AIdent s) v0 v);inversion H. subst.
     auto.      
     
   - intros. simpl in *. 
     remember (calculateExprList v exprs).      
     destruct e;inversion H.  clear H4.
     remember (getEventByName ident eventList). 
     destruct o;inversion H.
     clear H4.
     remember (parameterMatchFunc v0 (eventParams e)). 
     destruct b;inversion H.  subst. simpl. 
     constructor.  auto. unfold not. intros.
     unfold not in H2. apply getEventId in Heqo;auto.  subst.
     assert (exists re, In re l /\ (eventId (eventDefinition re)) = eventId e).
     apply raiseMapIn;auto. 
  
     destruct H4. destruct H4. 
     apply H2 with (evId := eventId e) (re := x);auto. 
   - intros.
     simpl in H.
     remember (execAction (v, l) act1 eventList).
     destruct e;inversion H.
     simpl in H0.
     simpl in H2. destruct v0.
     rewrite getEventIdFromRaiseStmtApp in H0. rewrite getEventIdFromRaiseStmtApp in H2. 
     remember Heqe. clear Heqe0.
     apply IHact1 in Heqe. Focus 3. auto. Focus 2.
     apply uniqAppRev in H0;auto. destruct H0;auto.
     Focus 2. intros. apply H2;auto. apply in_app_iff. left;auto. 
     
     
     apply IHact2 in H;auto. apply uniqAppRev in H0;auto. destruct H0;auto.
     intros.
     assert (In re l \/ ~ In re l).
     apply excluded_middle. destruct H6. 
     apply H2;auto.
     apply in_app_iff. right;auto.
     assert (In (eventId (eventDefinition re)) (getEventIdFromRaiseStmt (transitionIntoBasicActionList act1))).
     pose proof execActionGetEventIdIn. 
     eapply H7.  apply e. auto. auto. 
     
     pose proof uniqListNotIn.
     assert (~ In evId ((getEventIdFromRaiseStmt (transitionIntoBasicActionList act1)))).
     apply H8 with (a:=evId) in H0;auto.
     unfold not. intros. rewrite H10 in H9. contradiction. 
    
    
Qed.

(*(map (fun re0 : raisedEvent => eventId (eventDefinition re0))
       (filter
          (fun re0 : raisedEvent => EventKind_beq (eventKind (eventDefinition re0)) Internal) l))*)


Lemma mapFilterInList: forall (A B: Type) l (f:A ->B) (g: A -> bool) a,
    In a (map f (filter g l)) ->
    In a (map f l).  
Proof. intros A B l;induction l. 
 - intros. simpl in H. inversion H. 
 - intros. simpl in *;simpl.
   destruct (g a). simpl in *. destruct H. left;auto.
   right. apply IHl with (g:=g);auto.
   apply IHl in H. right;auto. 
Qed.

Lemma mapFilterUniqList: forall (A B: Type) l (f:A ->B) (g: A -> bool),
    uniqList (map f l) ->
    uniqList (map f (filter g l)). 
Proof.
  intros A B l;induction l. 
- intros. simpl. constructor. 
- intros. simpl. simpl in H. inversion H;subst.
  destruct (g a). simpl. constructor. apply IHl;auto.
  Focus 2. apply IHl;auto.
  unfold not. intros. apply H3. apply mapFilterInList with (g:=g);auto. 
Qed.


Lemma constructConfigRaisedUniq'': forall M (conf conf' : configuration M) sce re,
    correct_configuration conf ->
    noDupRaise'' M ->
    typeCheck M ->
    In sce (scenarios M) ->
    Result conf' = constructConfig sce re conf ->
     stpStMapEquiv' M ->
    correctStateEvStepMap' M ->
    uniqList (map (fun re => eventId (eventDefinition re)) (raisedevents conf')).  
Proof.
  
  intros. rename H4 into stEquiv. rename H5 into correctState. 
  unfold constructConfig in H3.
  remember (getScenarioState sce (controlstate conf)). 
  destruct o;inversion H3.
  remember (transEvMapFunc (stateEvDefInstanceMap M) (Some s, Some (eventDefinition re))).
  destruct o;inversion H3.
  remember (findEventInstance re (datastate conf) l).
  destruct o;inversion H3.
  remember (createValueEnv (eventArgs e) (eventParams (eventDefinition re)) (eventArguments re)). 
  destruct e0;inversion H3.
  remember (getStep' conf sce e). 
  destruct o;inversion H7.
  remember (configTransition (extendValEnv (datastate conf) v) re e sce s0 conf). 
  destruct e0;inversion H3.
  subst.
  unfold configTransition in Heqe1.
  remember (execAction (extendValEnv (datastate conf) v, nil) (stepActions s0)
              (filter
                 (fun e : event_definition =>
                  match eventKind e with
                  | Internal => true
                  | Imported => false
                  | Exported => true
                  end) (events M))). 
  destruct e0;inversion Heqe1.
  destruct v1. inversion Heqe1. simpl.
  pose proof execActionRaisedUniq'.
  assert (uniqList
    (map (fun re0 : raisedEvent => eventId (eventDefinition re0))
       l0)).
  apply H4 with (act:=(stepActions s0)) (v:=extendValEnv (datastate conf) v) (v':=v1) (l:=nil) (eventList:=(filter
               (fun e : event_definition =>
                match eventKind e with
                | Internal => true
                | Imported => false
                | Exported => true
                end) (events M)));auto. Focus 2. simpl. constructor. 
  
  assert (In s0 (getTransitionsOfScenario sce)).
  (*   remember Heqo. clear Heqe2.
        apply inControlState in Heqo;auto.
   pose proof  getStepMap'. 
        unfold stpStMapEquiv' in H7.
   apply H10 with (s0:=s0) (e0:=e) in e0;auto. 
   symmetry in e0.   rewrite <- H7 in e0.
   remember e0. clear Heqi2.
   unfold correctStateEvStepMap' in stepEventMap.
   
   apply stepEventMap in e0;auto.
     *)
  unfold getTransitionsOfScenario.
  remember Heqo. clear Heqe3.
        apply inControlState in Heqo;auto.
   pose proof  getStepMap'. 
        unfold stpStMapEquiv' in stEquiv.
   apply H12 with (s0:=s0) (e0:=e) in e0;auto. 
   symmetry in e0.   apply stpStMapEquivLem in e0;auto.
   remember e0. clear Heqi.
   unfold correctStateEvStepMap' in correctState. 
   apply correctState in e0;auto. destruct e0;auto.
   destruct H. rewrite cs_consist;auto. 
   pose proof noDupEventDef'.
   apply H13 with (mon:=M) (sce:=sce);auto.
   apply mapFilterUniqList;auto. 
Qed.


Lemma syncRaised': forall M (conf conf' : configuration M) e re,
    correct_configuration conf ->
    
    basicPreconditionMon M ->
    synchrony conf conf' e ->
    ~ In re (raisedevents conf) ->
    In re (raisedevents conf') ->
    noMergeError' M -> 
    (exists sce tr act exprs , In (sce,eventDefinition e) (sceEventMap conf') /\ In tr (getTransitionsOfScenario sce) /\
         In act (transitionIntoBasicActionList (stepActions tr)) /\
         act = RaiseStmt (eventId (eventDefinition re)) exprs /\
         eventDefinition e = SmedlAST_submission.event (stepEvent tr)). 
Proof.
  intros. rename H4 into noMerge. 
  remember H1. clear Heqs.
  unfold synchrony in s.
  destruct s.
  unfold combineFunc in H5.
  remember (constructConfigList (dom (controlstate conf)) e conf).
  destruct e0;inversion H5.
  destruct v;inversion H5.
  unfold constructConfigList in Heqe0.
  
  remember (innerCombineFunc'''' conf (c :: v)). 
  destruct o;inversion H7.
  pose proof innerCombineFuncRaisedEvents.
  rewrite <- H9 in  H3.
  unfold removeEventFromConf in H3. simpl in H3.
  apply removeIn in H3. 
  assert (exists conf'' : configuration M, In conf'' (c::v) /\ In re (raisedevents conf'')). 
  apply H6 with (conf:=conf) (conf':=c0);auto.
  destruct H10. destruct H10. 
  pose proof termL2.
  assert (exists sce : scenario, In sce (filter
               (fun x : scenario =>
                inList event_definition_dec (eventDefinition e) (alphabet x))
               (filterList (finishedscenarios conf) (dom (controlstate conf)) scenario_dec)) /\ Result x = constructConfig sce e conf).
  apply H12 with (lst:=c::v);auto.
  destruct H13. destruct H13.
  pose proof constructConfigRaised.
  exists x0.
  destruct H0.
   repeat match goal with
            | [ H: _ /\ _ |- _ ] => destruct H

          end. rename H24 into ssp;rename H25 into sin. 
   assert ( exists (tr : step) (act : action) (exprs : list expr),
    In tr (getTransitionsOfScenario x0) /\
    In act (transitionIntoBasicActionList (stepActions tr)) /\
    act = RaiseStmt (eventId (eventDefinition re)) exprs /\
    eventDefinition e = event (stepEvent tr)).

   
  apply H15 with (conf:=conf) (conf':=x);auto.
  apply filter_In in H13. destruct H13. apply filterL2 in H13;auto.
  unfold removeEventFromConf. simpl.
  destruct H24. destruct H24. destruct H24.
  exists x1. exists x2. exists x3. split;auto.
 
  apply constructConfigListMap with (lst:=(filter
               (fun x : scenario =>
                inList event_definition_dec (eventDefinition e) (alphabet x))
               (filterList (finishedscenarios conf) (dom (controlstate conf)) scenario_dec))) (conf:=conf) (v:=(c::v));auto.
 repeat( split;auto).  apply filterUniq.
  destruct H. 
  apply uniqListFilter;auto.
  unfold incl. intros.
  apply filter_In in H25. destruct H25.
  apply filterL2 in H25;auto. 
  intros.   apply filter_In in H25. apply filter_In in H26;destruct H25;destruct H26.
  unfold not. intros.
  SearchAbout inList. apply reverseinListLemma in H27; apply reverseinListLemma in H28.
  unfold noIntersection in H29. destruct H29. apply H29 in H27. contradiction. 
Qed.



Lemma syncRaised'': forall M (conf conf' : configuration M) e re,
    correct_configuration conf ->
    
    basicPreconditionMon M ->
    synchrony conf conf' e ->
    ~ In re (raisedevents conf) ->
    In re (raisedevents conf') ->
    noMergeError' M -> 
    (exists sce tr act exprs , ~ In sce (finishedscenarios conf) /\ In (sce,eventDefinition e) (sceEventMap conf') /\ In tr (getTransitionsOfScenario sce) /\
         In act (transitionIntoBasicActionList (stepActions tr)) /\
         act = RaiseStmt (eventId (eventDefinition re)) exprs /\
         eventDefinition e = SmedlAST_submission.event (stepEvent tr)). 
Proof.
  intros. rename H4 into noMerge. 
  remember H1. clear Heqs.
  unfold synchrony in s.
  destruct s.
  unfold combineFunc in H5.
  remember (constructConfigList (dom (controlstate conf)) e conf).
  destruct e0;inversion H5.
  destruct v;inversion H5.
  unfold constructConfigList in Heqe0.
  remember (innerCombineFunc'''' conf (c :: v)). 
  destruct o;inversion H7.
  pose proof innerCombineFuncRaisedEvents.
  rewrite <- H9 in  H3.
  unfold removeEventFromConf in H3. simpl in H3.
  apply removeIn in H3. 
  assert (exists conf'' : configuration M, In conf'' (c::v) /\ In re (raisedevents conf'')). 
  apply H6 with (conf:=conf) (conf':=c0);auto.
  destruct H10. destruct H10. 
  pose proof termL2.
  assert (exists sce : scenario, In sce (filter
               (fun x : scenario =>
                inList event_definition_dec (eventDefinition e) (alphabet x))
               (filterList (finishedscenarios conf) (dom (controlstate conf)) scenario_dec)) /\ Result x = constructConfig sce e conf).
  apply H12 with (lst:=c::v);auto.
  destruct H13. destruct H13.
  
  pose proof constructConfigRaised.
  exists x0.
  destruct H0.
   repeat match goal with
            | [ H: _ /\ _ |- _ ] => destruct H

          end. rename H24 into ssp;rename H25 into sin. 
   assert ( exists (tr : step) (act : action) (exprs : list expr),
    In tr (getTransitionsOfScenario x0) /\
    In act (transitionIntoBasicActionList (stepActions tr)) /\
    act = RaiseStmt (eventId (eventDefinition re)) exprs /\
    eventDefinition e = event (stepEvent tr)).
   
  apply H15 with (conf:=conf) (conf':=x);auto.
  apply filter_In in H13. destruct H13. apply filterL2 in H13;auto.
  unfold removeEventFromConf. simpl.
  destruct H24. destruct H24. destruct H24.
  exists x1. exists x2. exists x3. split;auto. apply filter_In in H13. destruct H13. apply filterL1 in H13;auto. 
  Check constructConfigListMap. split. 
  apply constructConfigListMap with (lst:=(filter
               (fun x : scenario =>
                inList event_definition_dec (eventDefinition e) (alphabet x))
               (filterList (finishedscenarios conf) (dom (controlstate conf)) scenario_dec))) (conf:=conf) (v:=(c::v));auto.
  repeat(split;auto). apply filterUniq.
  destruct H. 
  apply uniqListFilter;auto.
  unfold incl. intros.
  apply filter_In in H25. destruct H25.
  apply filterL2 in H25;auto. 
 
    intros.   apply filter_In in H25. apply filter_In in H26;destruct H25;destruct H26.
    unfold not. intros.
    
  SearchAbout inList. apply reverseinListLemma in H27; apply reverseinListLemma in H28.
  unfold noIntersection in H29. destruct H29. apply H29 in H27. contradiction. auto. 
Qed.
  
Lemma chainMergeRaised: forall M (conf conf' : configuration M) e re,
    basicPreconditionMon M ->
    chainMerge conf conf' e ->
    In re (raisedevents conf') ->
    noMergeError' M -> 
    (exists ev sce tr act exprs , In (sce,ev) (sceEventMap conf') /\ In tr (getTransitionsOfScenario sce) /\
         In act (transitionIntoBasicActionList (stepActions tr)) /\
         act = RaiseStmt (eventId (eventDefinition re)) exprs /\
         ev = SmedlAST_submission.event (stepEvent tr)).
Proof.
  intros.
  generalize dependent re.
  induction H0.
  intros.
  pose proof syncRaised'.
  exists (eventDefinition event).
  apply H4 with (conf:=conf);auto. 
 
  destruct H0;auto.
  unfold not. intros.
   assert (eventDefinition event <> eventDefinition re).
  apply raisedEventNoImported with (conf:=conf) (conf':=conf');auto.
  apply basic';auto.
  assert (re <> event).
  unfold not. intros. rewrite H7 in H6. contradiction.
  assert (In event (raisedevents conf)).
  unfold synchrony in H1. destruct H1;auto.
  destruct H0.
  destruct H9.
  destruct ((raisedevents conf)).
  inversion H8.
  assert (l=nil). destruct l. auto. inversion H9.
  rewrite H11 in H5; rewrite H11 in H8.
  destruct H5;inversion H5;destruct H8;inversion H8. subst.
  contradiction.

  
  intros.
  assert (In re (raisedevents conf') \/ ~ In re (raisedevents conf')).
  apply excluded_middle. 
  destruct H4.
 assert (  exists
                   (ev : event_definition) (sce : scenario) (tr : step) 
                 (act : action) (exprs : list expr),
                   In (sce, ev) (sceEventMap conf') /\
                   In tr (getTransitionsOfScenario sce) /\
                   In act (transitionIntoBasicActionList (stepActions tr)) /\
                   act = RaiseStmt (eventId (eventDefinition re)) exprs /\
                   ev = event (stepEvent tr)).
  
  apply IHchainMerge;auto.
  destruct H5. destruct H5. destruct H5. destruct H5. destruct H5.
  exists x. exists x0. exists x1. exists x2. exists x3.
  split. Focus 2.
   repeat match goal with
            | [ H: _ /\ _ |- _ ] => destruct H

             end.
   split;auto.
   destruct H5.
   SearchAbout (In (_,_) (sceEventMap _)). 
   apply sceEventMapNoChangeSync with (conf:=conf') (e:=event2);auto.
   destruct H.
   repeat match goal with
            | [ H: _ /\ _ |- _ ] => destruct H

          end.
   rename H18 into ssp;rename H19 into sin.    
   apply termL5' with (conf:=conf) (e:=event1);auto.
   remember H0. clear Heqc. 
    apply chainMergeInitial in c. destruct c. destruct H18.
  apply raised_wellform'0 . 
  apply chainMergeInitialEvent in H0;auto.   
 SearchAbout (In (_,_) (sceEventMap _)). 
 pose proof chainMergeFinMap.
 destruct H7 with (conf:=conf) (conf':=conf') (e:=event1) (sce:=x0);auto.
  destruct H.
   repeat match goal with
            | [ H: _ /\ _ |- _ ] => destruct H

             end.
   split;auto.
   apply chainMergeInitial in H0. destruct H0;auto.
   repeat(split;auto). 
   apply chainMergeInitialEvent in H0;auto.
  
   apply H9. exists x;auto. 

   
   pose proof syncRaised'.
   exists (eventDefinition event2). 
   apply H5 with (conf:=conf');auto.
   destruct H.
   
   repeat match goal with
            | [ H: _ /\ _ |- _ ] => destruct H

             end.
     apply termL5' with (conf:=conf) (e:=event1);auto.
   remember H0. clear Heqc. 
    apply chainMergeInitial in c. destruct c. destruct H16.
  apply raised_wellform'0 . 
  apply chainMergeInitialEvent in H0;auto.
Qed.


Lemma chainMergeSceEventMap: forall M (conf conf' : configuration M) e sce x,
    basicPreconditionMon M ->
    chainMerge conf conf' e ->
    noMergeError' M ->
    In (sce,x) (sceEventMap conf') ->
    (x = eventDefinition e \/ exists ev sce' tr act exprs , In (sce',ev) (sceEventMap conf') /\ In tr (getTransitionsOfScenario sce') /\
         In act (transitionIntoBasicActionList (stepActions tr)) /\
         act = RaiseStmt (eventId  x) exprs /\
         ev = SmedlAST_submission.event (stepEvent tr)).
Proof.
  intros. generalize dependent sce. induction H0. 
  - intros. 
    assert (~ In (sce,x) (sceEventMap conf)).
    destruct H0.
     repeat match goal with
            | [ H: _ /\ _ |- _ ] => destruct H

            end. unfold not. intros. 
   rewrite H7 in H8.   inversion H8.    
    SearchAbout (In (_,_) (sceEventMap _)).
    assert (x = eventDefinition event).
    apply syncMapFinishEventDef with (conf:=conf) (conf':=conf') (sce:=sce);auto. 
    destruct H0;auto.
    destruct H.  repeat match goal with
            | [ H: _ /\ _ |- _ ] => destruct H

                        end.
    split;auto.  destruct H0;auto.   split;auto. split. unfold synchrony in H2. destruct H2;auto. repeat(split;auto). 
    rewrite H5 in H3;rewrite H5 in H4.
    left;auto. 
  - intros.
    assert (x = eventDefinition event1 \/ x <> eventDefinition event1).
    apply excluded_middle. destruct H4. left;auto.
    right. assert (In (sce,x) (sceEventMap conf') \/ ~ In (sce,x) (sceEventMap conf')).
    apply excluded_middle. destruct H5.
    apply IHchainMerge in H5;auto.
    destruct H5. contradiction.
    destruct H5. destruct H5. destruct H5. destruct H5. destruct H5.
    repeat match goal with
            | [ H: _ /\ _ |- _ ] => destruct H

           end.
    exists x0. exists x1. exists x2. exists x3. exists x4. split;auto.
    SearchAbout (In (_,_) (sceEventMap _)).
    apply sceEventMapNoChangeSync with (conf:=conf') (e:=event2);auto.
    destruct H.
     repeat match goal with
            | [ H: _ /\ _ |- _ ] => destruct H

            end.
     
   rename H18 into ssp.   rename H19 into sin. apply termL5' with (conf:=conf) (e:=event1);auto.
     remember H0. clear Heqc. apply chainMergeInitial in c. destruct c.
     destruct H18. apply raised_wellform'0.
     apply chainMergeInitialEvent in H0. auto.
     SearchAbout (In (_,_) (sceEventMap _)).
     pose proof chainMergeFinMap.
     destruct H.
     repeat match goal with
            | [ H: _ /\ _ |- _ ] => destruct H

            end.
     rename H19 into ssp;rename H20 into sin. 
         
     destruct H10 with (conf:=conf) (conf':=conf') (e:=event1) (sce:=x1);auto.
     split;auto. apply chainMergeInitial in H0;destruct H0;auto. split;auto.
     split;auto. apply chainMergeInitialEvent in H0;auto. split;auto.
     split;auto. split;auto. split;auto. split;auto. apply H20. exists x0;auto.
     SearchAbout (In (_,_) (sceEventMap _)).
     
     pose proof syncMapFinishEventDef.
      destruct H.
     repeat match goal with
            | [ H: _ /\ _ |- _ ] => destruct H

           end. rename H15 into ssp;rename H16 into sin. 
     assert (x = eventDefinition event2).
     apply H6 with (conf:=conf') (conf':=conf'') (sce:=sce);auto.
     apply termL5' with (conf:=conf) (e:=event1);auto.
      
     remember H0. clear Heqc. apply chainMergeInitial in c. destruct c.
     destruct H15. apply raised_wellform'0.
     apply chainMergeInitialEvent in H0;auto.
     auto.
     split;auto.
       apply termL5' with (conf:=conf) (e:=event1);auto.
      
     remember H0. clear Heqc. apply chainMergeInitial in c. destruct c.
     destruct H15. apply raised_wellform'0.
     apply chainMergeInitialEvent in H0;auto.
     split.  auto.
     split. unfold synchrony in H2. destruct H2;auto.
     split;(try (rewrite <- monitorObjNoChangeChain with (conf:=conf) (e:=event1);auto));auto.  split;auto. split;auto. split;auto. split;auto. 
     rewrite H15.
     assert (In event2 (raisedevents conf')). unfold synchrony in H2. destruct H2;auto.
     pose proof chainMergeRaised.
     assert (exists
          (ev : event_definition) (sce : scenario) (tr : step) 
        (act : action) (exprs : list expr),
          In (sce, ev) (sceEventMap conf') /\
          In tr (getTransitionsOfScenario sce) /\
          In act (transitionIntoBasicActionList (stepActions tr)) /\
          act = RaiseStmt (eventId (eventDefinition event2)) exprs /\ ev = event (stepEvent tr)).
        
     apply H17 with (conf:=conf) (e:=event1);auto.
         
     split;auto. split;auto. split;auto. split;auto. split;auto. split;auto. 
   destruct H18. destruct H18. destruct H18. 
   destruct H18.   destruct H18.
  repeat match goal with
            | [ H: _ /\ _ |- _ ] => destruct H

         end.
  exists x0.   exists x1. exists x2. exists x3. exists x4. split;auto.

  apply sceEventMapNoChangeSync with (conf:=conf')(e:=event2);auto.
    apply termL5' with (conf:=conf) (e:=event1);auto.
      
     remember H0. clear Heqc. apply chainMergeInitial in c. destruct c.
     destruct H23. apply raised_wellform'0.
     apply chainMergeInitialEvent in H0;auto.
     pose proof chainMergeFinMap.
     
     destruct H23 with (conf:=conf) (conf':=conf') (e:=event1) (sce:=x1);auto.
     split;auto. apply chainMergeInitial in H0;destruct H0;auto. split;auto.
     split;auto. apply chainMergeInitialEvent in H0;auto. split;auto.
     split;auto. split;auto. split;auto. split;auto. apply H25. exists x0;auto.
Qed. 
  
  
Lemma retrieveActionIn: forall stpList act stp,
    In act (transitionIntoBasicActionList ((stepActions stp))) ->
    In stp stpList ->
    In act (retrieveAction stpList).
Proof.
  intro stpList;induction stpList. 
  - intros.
    inversion H0.
  - 
    intros. simpl.
    apply in_app_iff. 
    destruct H0.
    subst.  left;auto.
    apply IHstpList in H;auto. 
Qed.


Lemma scenarioRaiseIn: forall  lst x x1 x3 x5 v,
    In x lst ->
    In x1 (getTransitionsOfScenario x) ->
    In x3 (transitionIntoBasicActionList (stepActions x1)) ->
    x3 = RaiseStmt (eventId v) x5 ->
    In x (scenarioRaise lst v). 
Proof.
  intro lst;induction lst. 
  -
    intros.  inversion H. 
  - intros.
    simpl.
    destruct H. 
    subst.
    remember (filter (fun act : action => filterRaiseStmt act (eventId v))
                     (retrieveAction (getTransitionsOfScenario x))).
    destruct l.
    
    assert (In (RaiseStmt (eventId v) x5) (filter (fun act : action => filterRaiseStmt act (eventId v))
                                                  (retrieveAction (getTransitionsOfScenario x)))).
    apply filter_In.                    
    
    simpl. destruct (string_dec (eventId v) (eventId v) ).
     Focus 2.  contradiction. split;auto.
    apply retrieveActionIn with (stp:=x1);auto. 
    rewrite <- Heql in H. inversion H. left;auto.
    remember (filter (fun act : action => filterRaiseStmt act (eventId v))
                     (retrieveAction (getTransitionsOfScenario a))).
    destruct l.
         
    apply IHlst with (x1:=x1) (x3:=x3) (x5:=x5);auto.
   right.   apply IHlst with (x1:=x1) (x3:=x3) (x5:=x5);auto.    
Qed.






Lemma constructConfigRaised': forall M (conf conf' : configuration M) re re' sce,
    Result conf' = constructConfig sce re conf ->
    In re' (raisedevents conf') ->  
    transEvMapProp M ->
    stpStMapEquiv' M ->
    correctStateEvStepMap' M ->
    stateEvDefInstanceMapEquiv M ->
     In sce (dom (controlstate conf)) ->
    exists (tr : step) (act : action) (exprs : list expr),
    In tr (getTransitionsOfScenario sce) /\
    In act (transitionIntoBasicActionList (stepActions tr)) /\
    act = RaiseStmt (eventId (eventDefinition re')) exprs /\
    eventDefinition re = event (stepEvent tr).
Proof.
  intros.
  rename H1 into evMapProp. rename H2 into mapEquiv. rename H3 into stpMap. rename H4 into stMapEq. rename H5 into sceCon. 
  unfold constructConfig in H.
  remember (getScenarioState sce (controlstate conf)).
  destruct o;inversion H. clear H2.
  remember ( transEvMapFunc (stateEvDefInstanceMap M) (Some s, Some (eventDefinition re)) ).
  destruct o;inversion H. clear H2.
  rename Heqo0 into tf. 
  remember (findEventInstance re (datastate conf)
           l).
  destruct o;inversion H;clear H2.
  remember (createValueEnv (eventArgs e) (eventParams (eventDefinition re))
           (eventArguments re)).
  destruct e0;inversion H;clear H2.
  remember (getStep' conf sce e).
  destruct o;inversion H;clear H2.
  remember (configTransition (extendValEnv (datastate conf) v) re e sce s0 conf ).
  destruct e0;inversion H;clear H2.
  unfold configTransition in Heqe1.
  inversion H;subst. clear H.
  remember ( execAction (extendValEnv (datastate conf) v, nil) 
              (stepActions s0)
              (filter
                 (fun e : event_definition =>
                  match eventKind e with
                  | Internal => true
                  | Imported => false
                  | Exported => true
                  end) (events M))).
  destruct e0;inversion Heqe1.
  destruct v1. clear H1.
  inversion Heqe1. rewrite H1 in H0. simpl in H0.
  clear H1.
  apply filter_In in H0. destruct H0. 
 
  (*apply in_app_iff in H1.
  destruct H1. Focus 2.
  apply removeIn in H.
  contradiction.
  apply filter_In in H.
  destruct H.*)
  pose proof execActionRaisingEvent.
  Print execAction. 
  assert (exists (act : action) (exprs : list expr),
         In act (transitionIntoBasicActionList (stepActions s0)) /\
         act = RaiseStmt (eventId (eventDefinition re')) exprs).
  eapply H1;auto. apply Heqe2. unfold not. intros. inversion H2. auto.
  exists s0.
  destruct H2. destruct H2.
  exists x. exists x0.
  destruct H2.
  
  unfold stateEvDefInstanceMapEquiv in stMapEq.
  unfold correctStateEvStepMap' in stpMap.
  unfold stpStMapEquiv' in mapEquiv.
  unfold transEvMapProp in evMapProp. 

  
  unfold getTransitionsOfScenario.
  
  split;auto.
  SearchAbout s0. 
  Focus 2. split;auto. split;auto.
  assert (event e = eventDefinition re).

  symmetry in tf. apply semantic_rules.stateEvDefInstanceMapEquiv' in tf;auto.
  Focus 2. destruct  stMapEq ;auto.
  remember tf. clear Heqi. 
  apply findEventInstanceIn in Heqo0.
 (* remember  (transEvMap (Some s, Some (eventDefinition re))).
  symmetry in Heql0. 
  rewrite <- stMapEq in Heql0.*)
  eapply evMapProp. apply i. auto.
  apply getStepMap' with (s:=s) in Heqo1;auto.
  symmetry in Heqo1. 
  apply stpStMapEquivLem in Heqo1;auto. remember Heqo1. clear Heqi. 
  apply stpMap in Heqo1.
  destruct Heqo1. destruct H6. rewrite H6. auto.
 

  remember Heqo. clear Heqe3. 
  apply inControlState in Heqo;auto.

  apply findEventInstanceIn in Heqo0.
  
 (* remember  (transEvMap (Some s, Some (eventDefinition re))).
  symmetry in Heql0. *)
  apply getStepMap' with (s:=s) in Heqo1;auto.
  symmetry in Heqo1. 
  apply stpStMapEquivLem in Heqo1;auto.
  apply  stpMap  with (sce:=sce) in Heqo1;auto.
  destruct Heqo1;auto. 
Qed.




Lemma constructConfigScenarioIn: forall M (conf conf' : configuration M)  re sce e,
    correct_configuration conf ->
    typeCheck M ->
    transEvMapProp M ->
  stpStMapEquiv' M ->
  correctStateEvStepMap' M ->
  stateEvDefInstanceMapEquiv M ->
    In sce (scenarios M) ->
    Result conf' = constructConfig sce re conf ->
    In e (raisedevents conf') ->
    In sce ((scenarioRaise (scenarios M) (eventDefinition e))). 
Proof.
  intros.
  SearchAbout   scenarioRaise.
  SearchAbout RaiseStmt. 
  pose proof constructConfigRaised'.
  assert ( exists (tr : step) (act : action) (exprs : list expr),
         In tr (getTransitionsOfScenario sce) /\
         In act (transitionIntoBasicActionList (stepActions tr)) /\
         act = RaiseStmt (eventId (eventDefinition e)) exprs /\
         eventDefinition re = event (stepEvent tr)).
  apply H8 with (conf:=conf) (conf':=conf');auto. 
  destruct H.   rewrite cs_consist;auto.
  destruct H9. destruct H9. destruct H9.
  SearchAbout   scenarioRaise.
   repeat match goal with
            | [ H: _ /\ _ |- _ ] => destruct H

              end.
  eapply scenarioRaiseIn. auto. apply H9.  apply H10. apply H11. 
Qed.

Lemma constructConfigEvents': forall M (conf conf' : configuration M) re re' sce,
    Result conf' = constructConfig sce re conf ->
    In re' (raisedevents conf') ->
    In (eventDefinition re') (events M). 
Proof.
  intros.
  unfold constructConfig in H.
  remember (getScenarioState sce (controlstate conf)).
  destruct o;inversion H.
  remember (transEvMapFunc (stateEvDefInstanceMap M) (Some s, Some (eventDefinition re)) ). 
destruct o;inversion H.
  remember ( findEventInstance re (datastate conf) l).
  destruct o;inversion H.
  remember ( createValueEnv (eventArgs e) (eventParams (eventDefinition re)) (eventArguments re)). 
  destruct e0;inversion H.
  remember (getStep' conf sce e ).
  destruct o;inversion H4. clear H4;clear H5. clear H2;clear H3. clear H6. 
  remember (configTransition (extendValEnv (datastate conf) v) re e sce s0 conf).
  destruct e0;inversion H. subst.
  unfold configTransition in Heqe1.
  remember (execAction (extendValEnv (datastate conf) v, nil) (stepActions s0)
              (filter
                 (fun e : event_definition =>
                  match eventKind e with
                  | Internal => true
                  | Imported => false
                  | Exported => true
                  end) (events M))). 
  destruct e0;inversion Heqe1.
  destruct v1. clear H2. inversion Heqe1;subst. simpl in H0.
  (*
  apply in_app_iff in H1.  destruct H1. Focus 2.
  SearchAbout removeEvent'.  apply removeIn in H1. contradiction.*)
  apply filter_In in H0. destruct H0. clear H. clear Heqe1.
  Check execAction.
  remember ((eventKind (eventDefinition re'))).
  destruct e0;subst. Focus 2. simpl in H1. inversion H1. 
  Focus 2. simpl in H1. inversion H1.
  pose proof execActionEvents.
  eapply H;auto. apply Heqe2. unfold not. intros. inversion H2. auto. 
Qed.



Lemma mapRev: forall l e,
  In e (map (fun re : raisedEvent => eventId (eventDefinition re)) l) ->
  (exists re, In re l /\ (eventId (eventDefinition re)) = e). 
Proof. intro;induction l;intros. 
- simpl in H. inversion H. 
- simpl in H. destruct H. exists a. split;auto. left;auto.
  apply IHl in H.  destruct H. destruct H. exists x. split;auto. right;auto.  
Qed.

Print noDupRaise'.
SearchAbout noIntersection.
Print noDupRaise''.

(*raisedEventsInternal'*)
Lemma constructConfigRaisedSceDiff'':  forall M (conf conf' conf'' : configuration M) re sce sce',
    correct_configuration conf ->
    noDupRaise'' M ->
    typeCheck M ->
 transEvMapProp M ->
  stpStMapEquiv' M ->
  correctStateEvStepMap' M ->
  stateEvDefInstanceMapEquiv M ->
    In sce (scenarios M) ->
    In sce' (scenarios M) ->
    sce <> sce' ->
    Result conf' = constructConfig sce re conf ->
    Result conf'' = constructConfig sce' re conf ->
    (exists e : event_definition,
    In e (events M) /\ triggerSce M e sce /\ triggerSce M e sce') ->
    (forall e, In e (map (fun re => eventId (eventDefinition re)) (raisedevents conf')) -> ~ In e (map (fun re => eventId (eventDefinition re)) (raisedevents conf''))) /\
    (forall e, In e (map (fun re => eventId (eventDefinition re)) (raisedevents conf'')) -> ~ In e (map (fun re => eventId (eventDefinition re)) (raisedevents conf'))).
Proof. 
   intros. 
   unfold noDupRaise'' in H0.
   split. 
   -  intros.
      unfold not. intros.
      remember H12. 
      clear Heqi.  apply mapRev in i. destruct i. destruct H14. 
      remember H13. clear Heqi. 
      apply mapRev in i. destruct i. destruct H16. rewrite <- H17 in H15. 
      destruct H0 with (v:=eventDefinition x).
      
      eapply constructConfigEvents' with (conf':=conf') (re:=re) (sce:=sce);eauto. 
      
      assert (In sce (scenarioRaise (scenarios M) (eventDefinition x))). 
      eapply constructConfigScenarioIn with (conf':=conf') (re:=re);eauto. 
      assert (In sce' (scenarioRaise (scenarios M) (eventDefinition x))).
      SearchAbout eventId.
      assert (eventDefinition x = eventDefinition x0).
      apply EventEquivalence;auto.
      rewrite H21. 
      eapply constructConfigScenarioIn with (conf':=conf'') (re:=re);eauto.
      unfold not in H18.
      apply H18 with (sce1:=sce) (sce2:=sce');auto.
      apply raisedEventsInternal' with (M:=M) (conf:=conf) (conf':=conf') (sce:=sce) (re:=re);auto. 
  
   -
     intros.
     unfold not. intros.

     remember H12. 
      clear Heqi.  apply mapRev in i. destruct i. destruct H14. 
      remember H13. clear Heqi. 
      apply mapRev in i. destruct i. destruct H16. rewrite <- H17 in H15. 
      destruct H0 with (v:=eventDefinition x).
      eapply constructConfigEvents' with (conf':=conf'') (re:=re) (sce:=sce');eauto. 
  
      assert (In sce (scenarioRaise (scenarios M) (eventDefinition x0))). 
      eapply constructConfigScenarioIn with (conf':=conf') (re:=re);eauto. 
      assert (In sce' (scenarioRaise (scenarios M) (eventDefinition x))).
       assert (eventDefinition x = eventDefinition x0).
      apply EventEquivalence;auto.
     
      
      eapply constructConfigScenarioIn with (conf':=conf'') (re:=re);eauto.
       assert (eventDefinition x = eventDefinition x0).
       apply EventEquivalence;auto.
       rewrite H22 in H21.
       rewrite H22 in H18. 
       unfold not in H18.
      apply H18 with (sce1:=sce) (sce2:=sce');auto.
      apply raisedEventsInternal' with (M:=M) (conf:=conf) (conf':=conf') (sce:=sce) (re:=re);auto.
      
Qed. 
  





Lemma mapApp: forall (A B: Type) l1 l2  (f: A -> B) ,   
  (map f
       (l1 ++ l2)) = map f l1 ++ map f l2. 
Proof.
  intros A B l1;induction l1;intros. 
- simpl. auto. 
- simpl. f_equal;auto. 
Qed.

Lemma innerCombineFuncRaisedIn': forall M (conf : configuration M) lst vlst re c e,
     correct_configuration conf ->
    typeCheck M ->
 transEvMapProp M ->
  stpStMapEquiv' M ->
  correctStateEvStepMap' M ->
  stateEvDefInstanceMapEquiv M ->
  incl lst ((scenarios M)) ->
  uniqList lst ->
  Result vlst = constructConfigList' lst re conf ->
  Some c = innerCombineFunc'''' conf vlst ->
  In e (map (fun re => eventId (eventDefinition re)) (raisedevents c)) ->
  ~ In e (map (fun re => eventId (eventDefinition re)) (raisedevents conf)) ->
  (exists sce conf', In sce lst /\ In conf' vlst /\ Result conf' = constructConfig sce re conf /\ In e (map (fun re => eventId (eventDefinition re)) (raisedevents conf'))). 
Proof.
  intros ?? lst;induction lst.
  - intros.
    simpl in H7. inversion H7.   subst.  simpl in H8. inversion H8.
  - intros.
    simpl in H7.
    remember (constructConfig a re conf).         
    destruct e0;inversion H7. clear H12.
    remember (constructConfigList' lst re conf). 
    destruct e0;inversion H7.
    subst.
    simpl in H8.

    destruct v0. 
      remember (mergeConfigFunc' conf conf v).
    destruct e0;inversion H8. subst.
    unfold mergeConfigFunc' in Heqe2. 
    destruct (mergeDataStateFunc (datastate conf) (datastate conf) (datastate v) );inversion Heqe2.
    clear H12. 
    destruct (mergeControlStateFunc (controlstate conf) (controlstate conf) (controlstate v));inversion Heqe2.
    rewrite H12 in H9;simpl in H9.
   rewrite mapApp in H9.     
    rewrite in_app_iff in H9.
    destruct H9. contradiction. 
    exists a. exists v. split. left;auto. split. left;auto. split;auto.
     
    
    remember (innerCombineFunc'''' conf (c0::v0)). 
    destruct o;inversion H8.
    remember (mergeConfigFunc' conf v c1).
    destruct e0;inversion H8. subst.
    unfold mergeConfigFunc' in Heqe2.
    destruct (mergeDataStateFunc (datastate conf) (datastate v) (datastate c1) );inversion Heqe2.
    clear H13. 
    destruct (mergeControlStateFunc (controlstate conf) (controlstate v) (controlstate c1));inversion Heqe2.
    rewrite H13 in H9;simpl in H9.
    rewrite mapApp in H9. 
    rewrite in_app_iff in H9.
    destruct H9. Focus 2. 
    apply IHlst with (re:=re) (e:=e) in Heqo;auto.
    Focus 2. unfold incl in H5;unfold incl;intros. apply H5. right;auto.
    Focus 2. inversion H6;auto.
    destruct Heqo. destruct H11. exists x. exists x0.
    destruct H11. split. right;auto. destruct H14. split. right;auto.
    auto.
    exists a. exists v. split. left;auto. split. left;auto. split;auto.


Qed. 



Lemma innerCombineFuncUniq'': forall M (conf : configuration M) lst vlst re c,
     correct_configuration conf ->
    noDupRaise'' M ->
    typeCheck M ->
 transEvMapProp M ->
  stpStMapEquiv' M ->
  correctStateEvStepMap' M ->
  stateEvDefInstanceMapEquiv M ->
  incl lst ((scenarios M)) ->
  uniqList lst ->
  Result vlst = constructConfigList' lst re conf ->
  Some c = innerCombineFunc'''' conf vlst ->
  uniqList (map (fun re => eventId (eventDefinition re)) (raisedevents conf)) ->
  (forall conf' e, In conf' vlst  -> In e (map (fun re : raisedEvent => eventId (eventDefinition re)) (raisedevents conf)) -> ~ In e (map (fun re : raisedEvent => eventId (eventDefinition re)) (raisedevents conf'))) ->
  (forall conf' e, In conf' vlst  -> In e (map (fun re : raisedEvent => eventId (eventDefinition re)) (raisedevents conf')) -> ~ In e (map (fun re : raisedEvent => eventId (eventDefinition re)) (raisedevents conf))) ->
  (forall sce sce', In sce lst -> In sce' lst -> (exists e : event_definition, In e (events M) /\ triggerSce M e sce /\ triggerSce M e sce')) ->
  uniqList (map (fun re => eventId (eventDefinition re)) (raisedevents c)). 
Proof.
  intros ?? lst;induction lst. 
  -  intros.
    simpl in H8. inversion H8;subst;simpl in *. inversion H9. 
  - intros. 
    simpl in H8.
    remember (constructConfig a re conf). 
    destruct e;inversion H8. clear H15.
    remember (constructConfigList' lst re conf).
    destruct e;inversion H8.
    subst.
    simpl in H9.

    destruct v0. 
    remember (mergeConfigFunc' conf conf v). 
    destruct e;inversion H9.
    subst.
    unfold mergeConfigFunc' in Heqe1.
    destruct (mergeDataStateFunc (datastate conf) (datastate conf) (datastate v));inversion Heqe1.    destruct ( mergeControlStateFunc (controlstate conf) (controlstate conf) (controlstate v));inversion H15. simpl.
    rewrite mapApp. 
  
    apply uniqApp';auto.
    apply constructConfigRaisedUniq'' with (conf:=conf) (sce:=a) (re:=re);auto.
    unfold incl in H6. apply H6. left;auto.
    intros. apply H11;auto. left;auto.
    intros. apply H12 with (conf':=v);auto. left;auto.

    remember (innerCombineFunc'''' conf (c0::v0)).
    destruct o;inversion H9;clear H15.

    remember (mergeConfigFunc' conf v c1).
    destruct e;inversion H9.
    subst.
    
    unfold mergeConfigFunc' in Heqe1.
    destruct (mergeDataStateFunc (datastate conf) (datastate v) (datastate c1));inversion Heqe1.    destruct ( mergeControlStateFunc (controlstate conf) (controlstate v) (controlstate c1));inversion H15. simpl. rewrite mapApp. 
    apply uniqApp';auto. Focus 2. apply IHlst with (c:=c1) in Heqe0;auto.
    unfold incl. unfold incl in H6. intros. apply H6. right;auto. inversion H7;auto.
    intros. apply H11. right;auto. auto. intros. apply H12 with (conf':=conf');auto. right;auto.

    intros. apply H13; right;auto. 


    (*intros. apply noInter;right;auto.*) apply constructConfigRaisedUniq'' with (conf:=conf) (sce:=a) (re:=re);auto.
    unfold incl in H6. apply H6. left;auto. Focus 2. 
    intros. assert (In i (map (fun re : raisedEvent => eventId (eventDefinition re)) (raisedevents conf)) \/ ~ In i (map (fun re : raisedEvent => eventId (eventDefinition re)) (raisedevents conf))).
    apply excluded_middle. destruct H17. apply H11;auto. left;auto.
    pose proof innerCombineFuncRaisedIn'.
    
    assert ( exists (sce : scenario) (conf' : configuration M),
          In sce lst /\
          In conf' (c0::v0) /\
          Result conf' = constructConfig sce re conf /\ In i
            (map (fun re0 : raisedEvent => eventId (eventDefinition re0)) (raisedevents conf'))).
    apply H18 with (c:=c1);auto.
    unfold incl in H6;unfold incl.
    intros. apply H6. right;auto. inversion H7;auto.
    destruct H19. destruct H19.
     repeat match goal with
            | [ H: _ /\ _ |- _ ] => destruct H

            end.
     pose proof constructConfigRaisedSceDiff''.
     assert ((forall e, In e
           (map (fun re0 : raisedEvent => eventId (eventDefinition re0)) (raisedevents v)) ->  ~
         In e
           (map (fun re0 : raisedEvent => eventId (eventDefinition re0)) (raisedevents x0))) /\
             (forall e,In e
           (map (fun re0 : raisedEvent => eventId (eventDefinition re0)) (raisedevents x0)) -> ~ In e (map (fun re0 : raisedEvent => eventId (eventDefinition re0)) (raisedevents v)))).
     apply H23 with (conf:=conf) (re:=re) (sce:=a) (sce':=x);auto.
     unfold incl in H6;apply H6. left;auto.
     unfold incl in H6;apply H6. right;auto.
     unfold not. intros. rewrite H24 in H7. inversion H7;subst. contradiction.
     apply H13. left;auto. right;auto. 
      destruct H24. apply H25;auto.

     intros.
     
     unfold not. intros.
     assert (In i (map (fun re : raisedEvent => eventId (eventDefinition re)) (raisedevents conf)) \/ ~ In i (map (fun re : raisedEvent => eventId (eventDefinition re)) (raisedevents conf))).
     apply excluded_middle. destruct H18. apply H11 with (conf':=v) in H18;auto. left;auto.
      pose proof innerCombineFuncRaisedIn'.
    assert ( exists (sce : scenario) (conf' : configuration M),
          In sce lst /\
          In conf' (c0::v0) /\
          Result conf' = constructConfig sce re conf /\ In i
            (map (fun re0 : raisedEvent => eventId (eventDefinition re0)) (raisedevents conf'))).
    apply H19 with (c:=c1);auto.
    unfold incl in H6;unfold incl.
    intros. apply H6. right;auto. inversion H7;auto.
    destruct H20. destruct H20.
     repeat match goal with
            | [ H: _ /\ _ |- _ ] => destruct H

            end.
     pose proof constructConfigRaisedSceDiff''.
     assert ((forall e, In e
           (map (fun re0 : raisedEvent => eventId (eventDefinition re0)) (raisedevents v)) ->  ~
         In e
           (map (fun re0 : raisedEvent => eventId (eventDefinition re0)) (raisedevents x0))) /\
             (forall e,In e
           (map (fun re0 : raisedEvent => eventId (eventDefinition re0)) (raisedevents x0)) -> ~ In e (map (fun re0 : raisedEvent => eventId (eventDefinition re0)) (raisedevents v)))).
     apply H24 with (conf:=conf) (re:=re) (sce:=a) (sce':=x);auto.
     unfold incl in H6;apply H6. left;auto.
     unfold incl in H6;apply H6. right;auto.
     unfold not. intros. rewrite H25 in H7. inversion H7;subst. contradiction.
 apply H13. left;auto. right;auto.           destruct H25. apply H25 in H14;auto.
Qed.




Lemma removeEventUniq: forall l e,
    uniqList l ->
      uniqList (removeEvent' e l).
Proof. intro l;induction l. 
       - intros. simpl. auto.
       - intros. simpl. destruct (raisedEvent_dec e a). subst.
         apply IHl. inversion H;auto.
         constructor. apply IHl;auto. inversion H;auto.
         unfold not. intros. inversion H;subst.
         apply removeIn in H0. contradiction. 
Qed.

Lemma mapRemoveIn: forall (A:Type) l (f: raisedEvent -> A) e e',
    In e' (map f (removeEvent' e l)) ->
    In e' (map f l). 
Proof.  intros A l;induction l;intros.   
- simpl in H. inversion H. 
- simpl in H. simpl. destruct (raisedEvent_dec e a). subst.
  apply IHl in H. right;auto.
  simpl in H. destruct H. left;auto. right. apply IHl with (e:=e);auto. 
Qed. 


Lemma removeEventUniq': forall (A:Type) l (f:raisedEvent -> A) e,
    uniqList (map f l) ->
    uniqList (map f (removeEvent' e l)).
Proof.
   intros A l;induction l;intros.   
- simpl. constructor. 
- simpl in H. inversion H;subst. simpl.
  destruct (raisedEvent_dec e a ). 
  subst. apply IHl;auto. 
  simpl. constructor. apply IHl;auto.
  unfold not. intros.
  apply H3. apply mapRemoveIn with (e:=e);auto. 
Qed.






Lemma noDupEventDefinitionRaised'': forall M (conf conf' : configuration M) re,
    chainMerge conf conf' re ->
    noMergeError' M ->
    noMultAlphabet M ->
    basicPreconditionMon M->
    alphabetRaisingObject M ->
    noDupRaise'' M ->
    uniqList (map (fun re => eventId (eventDefinition re)) (raisedevents conf')). 
Proof.
  intros. 
  induction H.
  -  remember H5. clear Heqs.
     unfold synchrony in s.
     destruct s.
     unfold combineFunc in H7.
     remember (constructConfigList (dom (controlstate conf)) event conf).
     destruct e;inversion H7.
     destruct v;inversion H7.
     remember (innerCombineFunc'''' conf (c :: v)).
     destruct o;inversion H9.
     unfold removeEventFromConf. simpl.
     unfold constructConfigList in Heqe.
     pose proof innerCombineFuncUniq''.
     assert (uniqList (map (fun re => eventId (eventDefinition re)) (raisedevents c0))).
     destruct H2.
      repeat match goal with
            | [ H: _ /\ _ |- _ ] => destruct H

             end.
      rename H20 into ssp;rename H21 into sin. 

      
     apply H8 with (lst:=(filter
              (fun x : scenario =>
               inList event_definition_dec (eventDefinition event) (alphabet x))
              (filterList (finishedscenarios conf) (dom (controlstate conf)) scenario_dec))) (vlst:=c::v) (conf:=conf) (re:=event);auto.
     
     destruct H;auto.
     unfold incl;intros.
     apply filter_In in H20. destruct H20. apply filterL2 in H20.
     destruct H;destruct H. rewrite cs_consist in H20;auto.
     apply filterUniq.
     apply  uniqListFilter.  destruct H;destruct H;auto.
     destruct H;destruct H;auto.
     destruct H.
      repeat match goal with
            | [ H: _ /\ _ |- _ ] => destruct H

             end.
      destruct ((raisedevents conf)). simpl. constructor.  simpl. destruct l. constructor. simpl. constructor.
      unfold not. intros. simpl in H24.  inversion H24. inversion H20.
      intros.
      assert (e = (eventId (eventDefinition event))).
     clear H10. clear H8. 
     remember H5. clear Heqs. unfold synchrony in s. destruct s.
     destruct H.
      repeat match goal with
            | [ H: _ /\ _ |- _ ] => destruct H

             end.
      destruct ((raisedevents conf)). inversion H8.
      destruct l. simpl in H21. destruct H21;inversion H21. destruct H8;inversion H8. auto. inversion H22. 
      unfold not. intros.
      clear H10. clear H8. SearchAbout map.  remember H21. clear Heqi.  apply raiseMapIn in i.
      remember H23. clear Heqi0.  apply raiseMapIn in i0.
      destruct i. destruct H8. destruct i0. destruct H24. rewrite <- H25 in H10.
      SearchAbout eventId. assert (eventDefinition x = eventDefinition x0). apply EventEquivalence;auto.
      assert (event = x). remember H5. clear Heqs. unfold synchrony in s. destruct s.
       destruct H.
      repeat match goal with
            | [ H: _ /\ _ |- _ ] => destruct H

             end.
        destruct ((raisedevents conf)). inversion H8.
      destruct l. simpl in H21. destruct H21;inversion H21. destruct H8;inversion H8. rewrite H34 in H33;auto. destruct H27;inversion H27. rewrite H35 in H34;auto. 
      inversion H29. 
     
      assert (eventKind (eventDefinition x) = Imported).
      apply chainMergeRuleImport with (conf:=conf) (conf':=conf');auto. rewrite <- H27. 
      apply basic';auto.
      pose proof raisedEventsInternal'.
      pose proof termL2.
      assert (exists sce : scenario, In sce (filter
              (fun x : scenario =>
               inList event_definition_dec (eventDefinition event) (alphabet x))
              (filterList (finishedscenarios conf) (dom (controlstate conf)) scenario_dec)) /\ Result conf'0 = constructConfig sce event conf).
      apply H30 with (lst:=c::v);auto.
      destruct H31. destruct H31.
      apply H29 with (re':=x0) in H32;auto.
      rewrite H26 in H28.  rewrite H32 in H28.  inversion H28.
      
      intros. unfold not. intros.

       assert (e = (eventId (eventDefinition event))).
     clear H10. clear H8. 
     remember H5. clear Heqs. unfold synchrony in s. destruct s.
     destruct H.
      repeat match goal with
            | [ H: _ /\ _ |- _ ] => destruct H

             end.
      destruct ((raisedevents conf)). inversion H8.
      destruct l. simpl in H22. destruct H22;inversion H22. destruct H8;inversion H8. auto. inversion H23.


      remember H21. clear Heqi.  apply raiseMapIn in i.
      remember H22. clear Heqi0.  apply raiseMapIn in i0.
      destruct i. destruct H24. destruct i0. destruct H26. rewrite <- H27 in H25.
       assert (eventDefinition x = eventDefinition x0). apply EventEquivalence;auto.
      assert (event = x0). remember H5. clear Heqs. unfold synchrony in s. destruct s.
       destruct H.
      repeat match goal with
            | [ H: _ /\ _ |- _ ] => destruct H

             end.
        destruct ((raisedevents conf)). inversion H29.
        destruct l.   destruct H29;inversion H29;destruct H26;inversion H26. rewrite H36 in H35;auto.
        
      inversion H31. 
     
      assert (eventKind (eventDefinition x0) = Imported).
      apply chainMergeRuleImport with (conf:=conf) (conf':=conf');auto. rewrite <- H29. 
      apply basic';auto.
      pose proof raisedEventsInternal'.
      pose proof termL2.
      assert (exists sce : scenario, In sce (filter
              (fun x : scenario =>
               inList event_definition_dec (eventDefinition event) (alphabet x))
              (filterList (finishedscenarios conf) (dom (controlstate conf)) scenario_dec)) /\ Result conf'0 = constructConfig sce event conf).
      apply H32 with (lst:=c::v);auto.
      destruct H33. destruct H33.
      apply H31 with (re':=x) in H34;auto.
      rewrite H28 in H34.  rewrite H34 in H30.  inversion H30.
      intros.
      exists (eventDefinition event).
      SearchAbout events.
      split. 
      apply raise_in with (conf0:=conf);auto.
      destruct H;auto.
      Print triggerSce.
      SearchAbout filter.
      apply filter_In in H20;apply filter_In in H21;auto.
      destruct H20;destruct H21.
      Print triggerSce.
      split;apply basic_ts.
      SearchAbout sce.
      apply filterL2 in H20.
      destruct H. destruct H.
      rewrite cs_consist in H20.  auto. apply reverseinListLemma with (decA:=event_definition_dec);auto. 
     apply filterL2 in H21.
      destruct H. destruct H.
      rewrite cs_consist in H21.  auto. apply reverseinListLemma with (decA:=event_definition_dec);auto. 
      
      apply removeEventUniq';auto. 
  -
    
    assert (uniqList
                   (map (fun re : raisedEvent => eventId (eventDefinition re))
                      (raisedevents conf'))).
    apply IHchainMerge;auto.

    remember H5. clear Heqs.
     unfold synchrony in s.
     destruct s.
     unfold combineFunc in H8.
     remember (constructConfigList (dom (controlstate conf')) event2 conf').
     destruct e;inversion H8.
     destruct v;inversion H10.
     remember (innerCombineFunc'''' conf' (c :: v)).
     destruct o;inversion H10.
     unfold removeEventFromConf. simpl.
     unfold constructConfigList in Heqe.
     pose proof innerCombineFuncUniq''.
     assert (uniqList
    (map (fun re : raisedEvent => eventId (eventDefinition re))
       ( (raisedevents c0)))).
     remember H2. clear Heqb. 
     destruct H2.
      repeat match goal with
            | [ H: _ /\ _ |- _ ] => destruct H

             end.

      rename H21 into ssp;rename H22 into sin. 
      assert (correct_configuration conf').
     
      apply termL5' with (conf:=conf) (e:=event1);auto.
     remember H. clear Heqc1. apply chainMergeInitial in c1.
     destruct c1.
     destruct H21.
     apply raised_wellform'0;auto.
     apply chainMergeInitialEvent in H;auto.

     
     
     apply H9 with (lst:=(filter
              (fun x : scenario =>
               inList event_definition_dec (eventDefinition event2) (alphabet x))
              (filterList (finishedscenarios conf') (dom (controlstate conf')) scenario_dec))) (vlst:=c::v) (conf:=conf') (re:=event2);auto.

     unfold incl. intros.
     apply filter_In in H22;destruct H22;apply filterL2 in H22.
    
     destruct H21.
     rewrite cs_consist in H22;auto.
     apply filterUniq.
     apply uniqListFilter.
     destruct H21;auto. destruct H21;auto. 
     intros.
     SearchAbout map.
     
     remember H23. clear Heqi. apply raiseMapIn in i. destruct i.  destruct H24. 
     pose proof chainMergeRaised.
     assert ( exists
          (ev : event_definition) (sce : scenario) (tr : step) (act : action) 
        (exprs : list expr),
          In (sce, ev) (sceEventMap conf') /\
          In tr (getTransitionsOfScenario sce) /\
          In act (transitionIntoBasicActionList (stepActions tr)) /\
          act = RaiseStmt (eventId (eventDefinition x)) exprs /\ ev = event (stepEvent tr)).
     apply H26 with (conf:=conf) (e:=event1);auto.
     destruct H27. destruct H27. destruct H27. destruct H27.
     destruct H27.
     destruct H27.
     pose proof chainMergeFinMap.
     destruct H29 with (conf:=conf) (conf':=conf') (e:=event1) (sce:=x1);auto. 
     split;auto. apply chainMergeInitial in H. destruct H;auto. 
     split;auto. split. apply chainMergeInitialEvent in H;auto.
     split;auto. split;auto. 
     split;auto. split;auto. split;auto. assert (In x1 (finishedscenarios conf')). apply H31. exists x0;auto.
   
     assert (noDupRaise'' M).
     auto.
     unfold noDupRaise'' in H33. 
     destruct H33 with (v:=eventDefinition x);auto.
     eapply raise_in;eauto.
    
     repeat match goal with
            | [ H: _ /\ _ |- _ ] => destruct H

             end.

     
     assert (In x1 ((scenarioRaise (scenarios M) (eventDefinition x)))).
     eapply scenarioRaiseIn. Focus 2. apply H28.  Focus 2. apply H36. Focus 2. apply H37.
     remember H21. clear Heqc1. 
     destruct c1. rewrite <- cs_consist.
     unfold scenarioInclusion in inclusion. apply inclusion;auto.
     unfold not. intros.
     clear H11. clear H9.
     remember H40. clear Heqi. apply raiseMapIn in i. destruct i. destruct H9. 
     pose proof termL2.
     assert (exists sce : scenario, In sce (filter
              (fun x : scenario =>
               inList event_definition_dec (eventDefinition event2) (alphabet x))
              (filterList (finishedscenarios conf') (dom (controlstate conf')) scenario_dec)) /\ Result conf'0 = constructConfig sce event2 conf').
     apply H41 with (lst:=c::v);auto. destruct H42. destruct H42.
         apply filter_In in H42.
     destruct H42.
     remember H42. clear Heqi. SearchAbout x1. 
     apply filterL1 in i. apply filterL2 in H42.
     pose proof constructConfigRaised'.
      rewrite <- H11 in H25. assert (eventDefinition x = eventDefinition x5).
    apply EventEquivalence;auto. 
     assert ( exists (tr : step) (act : action) (exprs : list expr),
          In tr (getTransitionsOfScenario x6) /\
          In act (transitionIntoBasicActionList (stepActions tr)) /\
          act = RaiseStmt (eventId (eventDefinition x5)) exprs /\
          eventDefinition event2 = event (stepEvent tr)).
     apply H45 with (conf:=conf') (conf':=conf'0);auto.
     auto.
     destruct H47. destruct H47. destruct H47. 
     repeat match goal with
            | [ H: _ /\ _ |- _ ] => destruct H

            end.
     assert (In x6 ((scenarioRaise (scenarios M) (eventDefinition x5)))).
     eapply scenarioRaiseIn. Focus 2. apply H47.  Focus 2. apply H48. Focus 2. apply H49.
     
     remember H21. clear Heqc1. 
     destruct c1. rewrite <- cs_consist.  auto. rewrite <- H46 in H51.
     
     assert (x6 <> x1). unfold not. intros. rewrite H52 in i. contradiction.
     
     assert (eventKind (eventDefinition x) = Internal).
     SearchAbout Internal.
     apply raisedInterval with (M:=M) (conf:=conf) (conf':=conf') (e:=event1);auto.
     unfold not in H34.
     SearchAbout x1. 
     apply H34 with (sce1:=x1) (sce2:=x6) in H53;auto.
     SearchAbout x6.
     exists (eventDefinition event1).
     split.
     SearchAbout events.
     apply raise_in with (conf0:=conf);auto.
     apply chainMergeInitial in H. destruct H;auto.
     apply chainMergeInitialEvent in H;auto.
     split.
     Print triggerSce.
     assert (eventDefinition event1 = x0 \/ ~(eventDefinition event1 = x0)). 
     apply excluded_middle.
     destruct H54.
     apply basic_ts;auto.
     SearchAbout x1.
     SearchAbout finishedscenarios.
     Print scenarioInclusion.
     destruct H21.
     unfold scenarioInclusion in inclusion. unfold incl in inclusion.
     apply inclusion in H32;auto.
     rewrite cs_consist in H32;auto. 
     
     rewrite H54;
     apply chainMergeSceMapAlpha with (M:=M) (conf:=conf) (conf':=conf') (e:=event1);auto. 
      split;auto.
     apply chainMergeInitial in H. destruct H;auto.
     split;auto. split;auto. apply chainMergeInitialEvent in H;auto.
     repeat(split;auto).
         
     assert ( x0 = eventDefinition event1 \/ staticEventLeadTo M (eventDefinition event1) x0).
     apply usedEventLedTo with (conf:=conf) (conf':=conf');auto.
     split;auto.
     apply chainMergeInitial in H. destruct H;auto.
     split;auto. split;auto. apply chainMergeInitialEvent in H;auto.
     repeat(split;auto).
      apply rangeDomInRev with (a:=x1);auto.
      destruct H55;auto. unfold not in H54. exfalso;apply H54;auto.
      apply induction_ts with (e2:=x0);auto.
      SearchAbout x0.
      
      apply basic_ts;auto.
      SearchAbout x1.

       destruct H21.
     unfold scenarioInclusion in inclusion. unfold incl in inclusion.
     apply inclusion in H32;auto.
     rewrite cs_consist in H32;auto.

      apply chainMergeSceMapAlpha with (M:=M) (conf:=conf) (conf':=conf') (e:=event1);auto.
      split;auto.
     apply chainMergeInitial in H. destruct H;auto.
     split;auto. split;auto. apply chainMergeInitialEvent in H;auto.
     repeat(split;auto).
     SearchAbout x6.
     apply induction_ts with (e2:=eventDefinition event2);auto.
     SearchAbout event2.
     SearchAbout staticEventLeadTo.
     apply raisedEventLedTo with (conf:=conf) (conf':=conf');auto.
     apply basic_ts;auto.
     SearchAbout x6.
      destruct H21.
   
     rewrite cs_consist in H42;auto.
     
     apply reverseinListLemma with (decA:=event_definition_dec);auto. 
     
   
     clear H11.
     intros.
     unfold not. intros.

     remember H22. clear Heqi. apply raiseMapIn in i. destruct i.  destruct H24. 
     remember H23. clear Heqi. apply raiseMapIn in i. destruct i.  destruct H26. 
     pose proof chainMergeRaised.
     assert ( exists
          (ev : event_definition) (sce : scenario) (tr : step) (act : action) 
        (exprs : list expr),
          In (sce, ev) (sceEventMap conf') /\
          In tr (getTransitionsOfScenario sce) /\
          In act (transitionIntoBasicActionList (stepActions tr)) /\
          act = RaiseStmt (eventId (eventDefinition x0)) exprs /\ ev = event (stepEvent tr)).
     apply H28 with (conf:=conf) (e:=event1);auto.
     destruct H29. destruct H29. destruct H29. destruct H29.
     destruct H29.
     destruct H29.
     pose proof chainMergeFinMap.
     destruct H31 with (conf:=conf) (conf':=conf') (e:=event1) (sce:=x2);auto. 
     split;auto. apply chainMergeInitial in H. destruct H;auto. 
     split;auto. split. apply chainMergeInitialEvent in H;auto.
     split;auto. split;auto. 
     split;auto. split;auto. split;auto. assert (In x2 (finishedscenarios conf')). apply H33. exists x1;auto.
    
     assert (noDupRaise'' M).
     auto.
     unfold noDupRaise' in H35. 
     destruct H35 with (v:=eventDefinition x0);auto.
     eapply raise_in;eauto.
    
     repeat match goal with
            | [ H: _ /\ _ |- _ ] => destruct H

             end.

     assert (In x2 ((scenarioRaise (scenarios M) (eventDefinition x0)))).
     eapply scenarioRaiseIn. Focus 2. apply H30.  Focus 2. apply H38. Focus 2. apply H39.
     remember H21. clear Heqc1. 
     destruct c1. rewrite <- cs_consist.
     unfold scenarioInclusion in inclusion. apply inclusion;auto.
     clear H9.
     pose proof termL2.
     assert (exists sce : scenario, In sce (filter
              (fun x : scenario =>
               inList event_definition_dec (eventDefinition event2) (alphabet x))
              (filterList (finishedscenarios conf') (dom (controlstate conf')) scenario_dec)) /\ Result conf'0 = constructConfig sce event2 conf').
     apply H9 with (lst:=c::v);auto. destruct H42. destruct H42.
     apply filter_In in H42.
     destruct H42.
     remember H42. clear Heqi. 
     apply filterL1 in i. apply filterL2 in H42.
     pose proof constructConfigRaised'.
     rewrite <- H27 in H25. assert (eventDefinition x = eventDefinition x0).
      apply EventEquivalence;auto. 
     assert ( exists (tr : step) (act : action) (exprs : list expr),
          In tr (getTransitionsOfScenario x6) /\
          In act (transitionIntoBasicActionList (stepActions tr)) /\
          act = RaiseStmt (eventId (eventDefinition x)) exprs /\
          eventDefinition event2 = event (stepEvent tr)).
     apply H45 with (conf:=conf') (conf':=conf'0);auto.
     destruct H47. destruct H47. destruct H47. 
     repeat match goal with
            | [ H: _ /\ _ |- _ ] => destruct H

            end.
     assert (In x6 ((scenarioRaise (scenarios M) (eventDefinition x)))).
     eapply scenarioRaiseIn. Focus 2. apply H47.  Focus 2. apply H48. Focus 2. apply H49.
     
     remember H21. clear Heqc1. 
     destruct c1. rewrite <- cs_consist.  auto. rewrite  H46 in H51.
     
     assert (x6 <> x2). unfold not. intros. rewrite H52 in i. contradiction.

     assert (eventKind (eventDefinition x0) = Internal).
     SearchAbout x0.
          apply raisedInterval with (M:=M) (conf:=conf) (conf':=conf') (e:=event1);auto.
    
          unfold not in H34.
          SearchAbout x0.
     SearchAbout scenarioRaise.     
     apply H36 with (sce1:=x2) (sce2:=x6) in H53;auto.
     apply H53. 
     exists (eventDefinition event1).
     split.
     apply raise_in with (conf0:=conf);auto.
     apply chainMergeInitial in H. destruct H;auto.
     apply chainMergeInitialEvent in H;auto.
     split.
     SearchAbout x2.
     
     assert (eventDefinition event1 = x1 \/ ~(eventDefinition event1 = x1)). 
     apply excluded_middle.
     destruct H54.
     apply basic_ts;auto.
     SearchAbout x2. 
        destruct H21.
     unfold scenarioInclusion in inclusion. unfold incl in inclusion.
     apply inclusion in H34;auto.
     rewrite cs_consist in H34;auto.

     
     rewrite H54;
     apply chainMergeSceMapAlpha with (M:=M) (conf:=conf) (conf':=conf') (e:=event1);auto. 
      split;auto.
     apply chainMergeInitial in H. destruct H;auto.
     split;auto. split;auto. apply chainMergeInitialEvent in H;auto.
     repeat(split;auto).
         
     assert ( x1 = eventDefinition event1 \/ staticEventLeadTo M (eventDefinition event1) x1).
     apply usedEventLedTo with (conf:=conf) (conf':=conf');auto.
     split;auto.
     apply chainMergeInitial in H. destruct H;auto.
     split;auto. split;auto. apply chainMergeInitialEvent in H;auto.
     repeat(split;auto).
      apply rangeDomInRev with (a:=x2);auto.
      destruct H55;auto. unfold not in H54. exfalso;apply H54;auto.
      apply induction_ts with (e2:=x1);auto.
   
      apply basic_ts;auto.
      SearchAbout x2. 
          destruct H21.
     unfold scenarioInclusion in inclusion. unfold incl in inclusion.
     apply inclusion in H34;auto.
     rewrite cs_consist in H34;auto.
     
      apply chainMergeSceMapAlpha with (M:=M) (conf:=conf) (conf':=conf') (e:=event1);auto.
      split;auto.
     apply chainMergeInitial in H. destruct H;auto.
     split;auto. split;auto. apply chainMergeInitialEvent in H;auto.
     repeat(split;auto).
     apply induction_ts with (e2:=eventDefinition event2);auto.
     apply raisedEventLedTo with (conf:=conf) (conf':=conf');auto.
     apply basic_ts;auto.

     SearchAbout x6. 
 destruct H21.
   
     rewrite cs_consist in H42;auto.
     
     apply reverseinListLemma with (decA:=event_definition_dec);auto. 
   intros. 
   exists (eventDefinition event2).
   split.
   apply raise_in with (conf0:=conf');auto.
 
   apply filter_In in H22;apply filter_In in H23;auto.
   destruct H22. destruct H23.
   apply reverseinListLemma in H24;apply reverseinListLemma in H25;auto. 
   split;apply basic_ts;auto.
   apply filterL2 in H22.
   destruct H21. 
   rewrite cs_consist in H22;auto.

    apply filterL2 in H23.
   destruct H21. 
   rewrite cs_consist in H23;auto.
   
   SearchAbout filter.
   
 
 
   apply removeEventUniq';auto. 
     
Qed.





Lemma raisedMapIn: forall l re,
    In re l ->
     In (eventId (eventDefinition re))
    (map (fun re0 : raisedEvent => eventId (eventDefinition re0)) l).
Proof.
  intro l;induction l;intros. 
  inversion H;auto.
  destruct H. subst. simpl. left;auto. 
  simpl. right. apply IHl;auto. 
Qed.

Lemma uniqListEventIdNotEq: forall l re1 re2,
    In re1 l ->
    In re2 l ->
    re1 <> re2 ->
    (uniqList
       (map (fun re0 : raisedEvent => eventId (eventDefinition re0)) l)) ->
    eventDefinition re1 <> eventDefinition re2. 
Proof.
   intro l;induction l. 
- intros. inversion H. 
- intros. destruct H. destruct H0. rewrite H in H0. contradiction.
  simpl in H2.
  inversion H2;subst.
  unfold not. intros.
  inversion H2;subst. 
  rewrite H in H6.
  apply H6.
  apply raisedMapIn;auto.  
  
  destruct H0. subst.
  simpl in H2. inversion H2;subst.
  unfold not. intros. rewrite <- H0 in H5. apply H5.
  apply raisedMapIn;auto.  
  apply IHl;auto. inversion H2;auto. 
Qed. 




Lemma noDupEventDefinition'': forall M (conf conf' : configuration M) re,
    chainMerge conf conf' re ->
    noMergeError' M ->
    noMultAlphabet M ->
    basicPreconditionMon M->
    alphabetRaisingObject M ->
    noDupRaise'' M ->
    (forall re, In re (raisedevents conf') -> (~ (exists ev, In ev (range (sceEventMap conf')) /\ eventDefinition re = ev))) /\ (forall re re', In re (raisedevents conf') -> In re' (raisedevents conf')-> re <> re' -> eventDefinition re <> eventDefinition re'). 
Proof.
  intros.
  split.
  Focus 2.
  intros.
  pose proof noDupEventDefinitionRaised''.
  assert (uniqList
            (map (fun re0 : raisedEvent => eventId (eventDefinition re0)) (raisedevents conf'))).
  apply H8 with (conf:=conf) (re:=re);auto.
  apply uniqListEventIdNotEq with (l:=(raisedevents conf'));auto. 
  
  induction H.
  -
      intros.
      unfold not. intros.
      destruct H7.
      destruct H7.
      unfold noDupRaise'' in H4.
      apply rangeDomIn in H7.
      destruct H7.
      assert (~ In (x0,x) (sceEventMap conf)).
      destruct H.
      repeat match goal with
            | [ H: _ /\ _ |- _ ] => destruct H

             end.
      unfold not. intros. 
      rewrite H12 in H13.  inversion H13.
      SearchAbout (In (_,_) (sceEventMap _)).
      pose proof syncMapFinishEventDef.
      assert (x = eventDefinition event).
      apply H10 with (conf:=conf) (conf':=conf') (sce:=x0);auto.
      destruct H;auto.
      destruct H2.
       repeat match goal with
            | [ H: _ /\ _ |- _ ] => destruct H

              end. rename H19 into ssp;rename H20 into sin. 
       split;auto.        destruct H;auto.
       split;auto. split.
       unfold synchrony in H5.
       destruct H5;auto.
       split;auto.
       split;auto. split;auto. split;auto. split;auto.  
       rewrite H11 in H8.
       SearchAbout raisedevents.
       pose proof raisedInterval.
       assert (eventKind (eventDefinition re) = Internal).
       apply H12 with (conf:=conf) (conf':=conf') (e:=event);auto.
       apply basic';auto.
       SearchAbout raisedevents.
       pose proof chainMergeRuleImportIn.
       assert (eventKind (eventDefinition event) = Imported /\ In event (raisedevents conf)).
       apply H14 with (conf':=conf');auto. apply basic';auto.
       destruct H15. rewrite H8 in H13. rewrite H15 in H13. inversion H13. 
    
  - intros. remember H5.  clear Heqs. rename s into syncs. 
      assert (In re (raisedevents conf') \/ ~ In re (raisedevents conf')). 
      apply excluded_middle.
      destruct H7.
      assert (~
                 (exists ev : event_definition,
                     In ev (range (sceEventMap conf')) /\ eventDefinition re = ev)).
      apply IHchainMerge;auto.       
      assert (In event2 (raisedevents conf')).
      unfold synchrony in H5. destruct H5;auto.
      
      unfold not. intros.
      destruct H10. destruct H10.
      SearchAbout range. apply rangeDomIn in H10. destruct H10. 
      SearchAbout (In (_,_) (sceEventMap _)).
      rewrite <- H11 in H10. 
      assert (~ In (x0,eventDefinition re) (sceEventMap conf')).
      unfold not. intros. apply H8. exists (eventDefinition re);auto. split;auto.
      SearchAbout range. apply rangeDomInRev with (a:=x0);auto.
      SearchAbout (In (_,_) (sceEventMap _)).
      assert (eventDefinition re= eventDefinition event2).
      remember H2. clear Heqb.   destruct b.
       repeat match goal with
            | [ H: _ /\ _ |- _ ] => destruct H

              end.
      rename H22 into ssp;rename  H23 into sin.        
      apply syncMapFinishEventDef with (conf:=conf') (conf':=conf'') (sce:=x0);auto.
      
           
      apply termL5' with (conf:=conf) (e:=event1);auto.
     remember H. clear Heqc. apply chainMergeInitial in c.
     destruct c.
     destruct H22.
     apply raised_wellform'0;auto.
     apply chainMergeInitialEvent in H;auto.
     split;auto.

     apply termL5' with (conf:=conf) (e:=event1);auto.
     remember H. clear Heqc. apply chainMergeInitial in c.
     destruct c.
     destruct H22.
     apply raised_wellform'0;auto.
     apply chainMergeInitialEvent in H;auto.
     split;auto.
     split;auto.
      split;auto.
      split;auto. split;auto. split;auto. split;auto. 
      assert (re <> event2).
      remember H6. clear Heqi.
      remember H5. clear Heqs. unfold synchrony in s.
      destruct s. unfold combineFunc in H15.
      destruct (constructConfigList (dom (controlstate conf')) event2 conf');inversion H15.
      destruct v;inversion H17.
      destruct (innerCombineFunc'''' conf' (c :: v));inversion H17. rewrite <- H19 in i.
      unfold not. intros. rewrite H16 in i. apply removeNotIn in i. inversion i.

      pose proof noDupEventDefinitionRaised''.
  assert (uniqList
            (map (fun re0 : raisedEvent => eventId (eventDefinition re0)) (raisedevents conf'))).
  apply H15 with (conf:=conf) (re:=event1);auto.
  Check uniqListEventIdNotEq.  assert (eventDefinition re <> eventDefinition event2). 
  apply uniqListEventIdNotEq with (l:=(raisedevents conf'));auto. 
  contradiction.
  assert ( (exists ev : event_definition,
                    In ev (range (sceEventMap conf')) /\ eventDefinition re = ev) \/  ~(exists ev : event_definition,
                                                                                          In ev (range (sceEventMap conf')) /\ eventDefinition re = ev)).
  apply excluded_middle. destruct H8.
  Focus 2.

   assert (In event2 (raisedevents conf')).
      unfold synchrony in H5. destruct H5;auto.
      
      unfold not. intros.
      destruct H10. destruct H10.
      apply rangeDomIn in H10. destruct H10. 
      rewrite <- H11 in H10. 
      assert (~ In (x0,eventDefinition re) (sceEventMap conf')).
      unfold not. intros. apply H8. exists (eventDefinition re);auto. split;auto.
     apply rangeDomInRev with (a:=x0);auto.
      assert (eventDefinition re= eventDefinition event2).
      remember H2. clear Heqb.   destruct b.
       repeat match goal with
            | [ H: _ /\ _ |- _ ] => destruct H

              end.
      rename H22 into ssp;rename H23 into sin.        
      apply syncMapFinishEventDef with (conf:=conf') (conf':=conf'') (sce:=x0);auto.
      
           
      apply termL5' with (conf:=conf) (e:=event1);auto.
     remember H. clear Heqc. apply chainMergeInitial in c.
     destruct c.
     destruct H22.
     apply raised_wellform'0;auto.
     apply chainMergeInitialEvent in H;auto.
     split;auto.

     apply termL5' with (conf:=conf) (e:=event1);auto.
     remember H. clear Heqc. apply chainMergeInitial in c.
     destruct c.
     destruct H22.
     apply raised_wellform'0;auto.
     apply chainMergeInitialEvent in H;auto.
     split;auto.
     split;auto.
      split;auto.
      split;auto. split;auto. split;auto. split;auto. 
      assert (re <> event2).
      remember H6. clear Heqi.
      remember H5. clear Heqs. unfold synchrony in s.
      destruct s. unfold combineFunc in H15.
      destruct (constructConfigList (dom (controlstate conf')) event2 conf');inversion H15.
      destruct v;inversion H17.
      destruct (innerCombineFunc'''' conf' (c :: v));inversion H17. rewrite <- H19 in i.
      unfold not. intros. rewrite H16 in i. apply removeNotIn in i. inversion i.

  
  unfold noDupRaise'' in H4. 
  pose proof chainMergeRaised.
  assert ( exists
          (ev : event_definition) (sce : scenario) (tr : step) (act : action) 
        (exprs : list expr),
          In (sce, ev) (sceEventMap conf') /\
          In tr (getTransitionsOfScenario sce) /\
          In act (transitionIntoBasicActionList (stepActions tr)) /\
          act = RaiseStmt (eventId (eventDefinition event2)) exprs /\ ev = event (stepEvent tr)).
  apply H15 with (conf:=conf) (e:=event1);auto.
  destruct H16. destruct H16. destruct H16. destruct H16. destruct H16. 
  repeat match goal with
            | [ H: _ /\ _ |- _ ] => destruct H

              end.
  assert (In x2 (scenarioRaise (scenarios M) (eventDefinition event2))).
  SearchAbout scenarioRaise.
  eapply scenarioRaiseIn. Focus 2. apply H17. Focus 2. apply H18. Focus 2. apply H19.
 
  remember H16. clear Heqi.

   remember H2. clear Heqb.   destruct b.
       repeat match goal with
            | [ H: _ /\ _ |- _ ] => destruct H

              end.
   rename H30 into ssp;rename H31 into sin.        
   pose proof chainMergeFinMap.
  destruct H30 with (conf:=conf) (conf':=conf') (e:=event1) (sce:=x2);auto.
 
       split;auto.  apply chainMergeInitial in H. destruct H;auto.
       split;auto. split;auto. apply chainMergeInitialEvent in H;auto.
       split;auto. split;auto. split;auto. split;auto. split;auto. 
       assert (In x2 (finishedscenarios conf')). apply H32;auto. exists x1;auto.
       assert (correct_configuration conf').
      apply termL5' with (conf:=conf) (e:=event1);auto.
     remember H. clear Heqc. apply chainMergeInitial in c.
     destruct c.
     destruct H34.
     apply raised_wellform'0;auto.
     apply chainMergeInitialEvent in H;auto.
     destruct H34.
     
      rewrite <- cs_consist.
      unfold scenarioInclusion in inclusion. apply inclusion;auto.

       remember H2. clear Heqb.   destruct b.
       repeat match goal with
            | [ H: _ /\ _ |- _ ] => destruct H

              end.
       rename H31 into ssp;rename H32 into sin. 
      rewrite <- H13 in H21.
     
      pose proof syncRaised''.
     assert (exists (sce : scenario) (tr : step) (act : action) (exprs : list expr),
          ~ In sce (finishedscenarios conf') /\
          In (sce, eventDefinition event2) (sceEventMap conf'') /\
          In tr (getTransitionsOfScenario sce) /\
          In act (transitionIntoBasicActionList (stepActions tr)) /\
          act = RaiseStmt (eventId (eventDefinition re)) exprs /\
          eventDefinition event2 = event (stepEvent tr)).
     
     apply H31;auto.
     apply termL5' with (conf:=conf) (e:=event1);auto.
     remember H. clear Heqc. apply chainMergeInitial in c.
     destruct c.
     destruct H32.
     apply raised_wellform'0;auto.
     apply chainMergeInitialEvent in H;auto.
     destruct H32. destruct H32. destruct H32. destruct H32.
     repeat match goal with
            | [ H: _ /\ _ |- _ ] => destruct H

            end.
     
     assert (In x6 (scenarioRaise (scenarios M) (eventDefinition re))).
      eapply scenarioRaiseIn. Focus 2. apply H34. Focus 2. apply H35. Focus 2. apply H36.
      assert (correct_configuration conf').
          apply termL5' with (conf:=conf) (e:=event1);auto.
     remember H. clear Heqc. apply chainMergeInitial in c.
     destruct c.
     destruct H38.
     apply raised_wellform'0;auto.
     apply chainMergeInitialEvent in H;auto.
      pose proof chainMergeFinMap.
  destruct H39 with (conf:=conf) (conf':=conf'') (e:=event1) (sce:=x6);auto.
   
   split;auto. apply chainMergeInitial in H. destruct H;auto.
  split;auto.  split.   apply chainMergeInitialEvent in H;auto. 
       split;auto. split;auto. 
       split;auto. split;auto. split;auto. apply chain' with (conf':=conf') (event2:=event2);auto. 
       assert (In x6 (finishedscenarios conf'')). apply H41;auto. exists (eventDefinition event2);auto.
       assert (correct_configuration conf'').
          apply termL5' with (conf:=conf) (e:=event1);auto.
   apply chain' with (conf':=conf') (event2:=event2);auto.    remember H. clear Heqc. apply chainMergeInitial in c.
     destruct c.
     destruct H43.
     apply raised_wellform'0;auto.
     apply chainMergeInitialEvent in H;auto.
     
      destruct H43.
      rewrite <- cs_consist.
      unfold scenarioInclusion in inclusion. apply inclusion;auto.


assert (x6 <> x2). unfold not. intros. SearchAbout x2.
assert (In x2 (finishedscenarios conf')).
 pose proof chainMergeFinMap.
     destruct H40 with (conf:=conf) (conf':=conf') (e:=event1) (sce:=x2);auto. 
     split;auto. apply chainMergeInitial in H. destruct H;auto. 
     split;auto. split. apply chainMergeInitialEvent in H;auto.
     split;auto. split;auto. 
     split;auto.  split;auto. split;auto. apply H42. exists x1;auto. rewrite H39 in H32. contradiction.
     destruct H4 with (v:=eventDefinition re);auto.
     rewrite H13. eapply raise_in; eauto.
      apply termL5' with (conf:=conf) (e:=event1);auto.
     remember H. clear Heqc. apply chainMergeInitial in c.
     destruct c.
     destruct H40.
     apply raised_wellform'0;auto.
     apply chainMergeInitialEvent in H;auto.

     unfold synchrony in H5.  destruct H5;auto.
    (* rewrite   monitorObjNoChangeChain with (conf':=conf') (e:=event1) in H40;auto.*)
   (*
     inversion H38. destruct l. destruct H38;inversion H38;destruct H21;inversion H21.    subst. (*symmetry in H38.*) contradiction.
     SearchAbout Internal. 
*)
     assert (eventKind (eventDefinition re) = Internal).
     apply raisedIntervalSync with (conf:=conf') (conf':=conf'') (e:=event2);auto.
     apply termL5' with (conf:=conf) (e:=event1);auto.
     remember H. clear Heqc. 
     apply chainMergeInitialEvent in H;auto. apply chainMergeInitial in c;auto.
     destruct c. destruct H43. apply  raised_wellform'0;auto.
     SearchAbout scenarioRaise.   
     apply H40 with (sce1:=x2) (sce2:=x6) in H43;auto.
     apply H43.
     SearchAbout x6.
     exists (eventDefinition event1).
     split;auto.
     apply raise_in with (conf0:=conf);auto.
     apply chainMergeInitial in H;destruct H;auto.
     apply chainMergeInitialEvent in H;auto.
     split.
     SearchAbout x2.
     assert (eventDefinition event1 = x1 \/ ~ (eventDefinition event1 = x1)).
     apply excluded_middle. destruct H44.
     
     apply basic_ts;auto.
SearchAbout x2. 
SearchAbout sceEventMap.
pose proof chainMergeFinMap.
assert (In x2 (finishedscenarios conf') <->
        (exists x1 : event_definition, In (x2, x1) (sceEventMap conf'))). 
apply H45 with (conf:=conf) (e:=event1);auto.
split;auto.
apply chainMergeInitial in H;destruct H;auto.
split;auto. split. apply chainMergeInitialEvent in H;auto.
repeat(split;auto).
assert ( In x2 (finishedscenarios conf') ).
apply H46. exists x1;auto.
SearchAbout conf'.
assert (correct_configuration conf'). 
apply termL5' with (conf:=conf) (e:=event1);auto.
remember H. clear Heqc.
apply chainMergeInitial in H;auto.
destruct H. destruct H. apply   raised_wellform'0;auto.
apply chainMergeInitialEvent in c;auto.
destruct H48.
unfold scenarioInclusion in inclusion. unfold incl in inclusion.
apply inclusion in H47. rewrite cs_consist in H47. auto.  
 
     rewrite H44.
     SearchAbout alphabet.
     apply chainMergeSceMapAlpha with (M:=M) (conf:=conf) (conf':=conf') (e:=event1);auto.
     split;auto.
      apply chainMergeInitial in H;destruct H;auto.
    split;auto. split;auto. apply chainMergeInitialEvent in H;auto.
    repeat(split;auto).
         
    apply induction_ts with (e2:=x1);auto. 
    SearchAbout staticEventLeadTo.
    assert ( x1 = eventDefinition event1 \/ staticEventLeadTo M (eventDefinition event1) x1).
    apply usedEventLedTo with (conf:=conf) (conf':=conf');auto.
    split;auto.
      apply chainMergeInitial in H;destruct H;auto.
    split;auto. split;auto. apply chainMergeInitialEvent in H;auto.
    repeat(split;auto).
    SearchAbout range  .
    apply  rangeDomInRev with (a:=x2);auto.    
    destruct H45;auto.
    unfold not in H44;exfalso;auto.
    apply basic_ts;auto.


pose proof chainMergeFinMap.
assert (In x2 (finishedscenarios conf') <->
        (exists x1 : event_definition, In (x2, x1) (sceEventMap conf'))). 
apply H45 with (conf:=conf) (e:=event1);auto.
split;auto.
apply chainMergeInitial in H;destruct H;auto.
split;auto. split. apply chainMergeInitialEvent in H;auto.
repeat(split;auto).
assert ( In x2 (finishedscenarios conf') ).
apply H46. exists x1;auto.
SearchAbout conf'.
assert (correct_configuration conf'). 
apply termL5' with (conf:=conf) (e:=event1);auto.
remember H. clear Heqc.
apply chainMergeInitial in H;auto.
destruct H. destruct H. apply   raised_wellform'0;auto.
apply chainMergeInitialEvent in c;auto.
destruct H48.
unfold scenarioInclusion in inclusion. unfold incl in inclusion.
apply inclusion in H47. rewrite cs_consist in H47. auto.


    apply chainMergeSceMapAlpha with (M:=M) (conf:=conf) (conf':=conf') (e:=event1);auto.
        split;auto.
      apply chainMergeInitial in H;destruct H;auto.
    split;auto. split;auto. apply chainMergeInitialEvent in H;auto.
    repeat(split;auto).
    SearchAbout x6.
    apply induction_ts with (e2:=eventDefinition event2);auto. 
    SearchAbout staticEventLeadTo.
    apply   raisedEventLedTo with (conf:=conf) (conf':=conf');auto.
    apply basic_ts;auto.
    SearchAbout x6.


    pose proof chainMergeFinMap.
assert (In x6 (finishedscenarios conf'') <->
        (exists x1 : event_definition, In (x6, x1) (sceEventMap conf''))). 
apply H44 with (conf:=conf) (e:=event1);auto.
split;auto.
apply chainMergeInitial in H;destruct H;auto.
split;auto. split. apply chainMergeInitialEvent in H;auto.
repeat(split;auto).
apply chain' with (conf':=conf') (event2:=event2);auto. 
assert ( In x6 (finishedscenarios conf'') ).
apply H45. exists (eventDefinition event2);auto.

assert (correct_configuration conf''). 
apply termL5' with (conf:=conf) (e:=event1);auto.
apply chain' with (conf':=conf') (event2:=event2);auto. 
remember H. clear Heqc.
apply chainMergeInitial in H;auto.
destruct H. destruct H. apply   raised_wellform'0;auto.
apply chainMergeInitialEvent in c;auto.
destruct H47.
unfold scenarioInclusion in inclusion. unfold incl in inclusion.
apply inclusion in H46. rewrite cs_consist in H46. auto.


     apply chainMergeSceMapAlpha with (M:=M) (conf:=conf) (conf':=conf'') (e:=event1);auto.
     split;auto.
      apply chainMergeInitial in H;destruct H;auto.
    split;auto. split;auto. apply chainMergeInitialEvent in H;auto.
    repeat(split;auto).
    Print chainMerge. 
    apply chain' with (conf':=conf') (event2:=event2);auto. 
   
     
     destruct H8. destruct H8. 
     remember H8. clear Heqi. SearchAbout range. apply rangeDomIn in i.
     destruct i.
     pose proof chainMergeSceEventMap.
     assert (x = eventDefinition event1 \/ (exists
           (ev : event_definition) (sce' : scenario) (tr : step) 
         (act : action) (exprs : list expr),
           In (sce', ev) (sceEventMap conf') /\
           In tr (getTransitionsOfScenario sce') /\
           In act (transitionIntoBasicActionList (stepActions tr)) /\
           act = RaiseStmt (eventId x) exprs /\ ev = event (stepEvent tr))).
     apply H11 with (conf:=conf) (sce:=x0);auto.
     destruct H12.
     Print event_definition. 
     assert (eventKind (eventDefinition re) = Internal).
     SearchAbout Internal.
     apply raisedIntervalSync with (conf:=conf') (conf':=conf'') (e:=event2);auto.

     
      remember H2. clear Heqb.   destruct b.
       repeat match goal with
            | [ H: _ /\ _ |- _ ] => destruct H

              end.
       rename H22 into ssp;rename H23 into sin. 
     
      apply termL5' with (conf:=conf) (e:=event1);auto.
     remember H. clear Heqc. apply chainMergeInitial in c.
     destruct c.
     destruct H22.
     apply raised_wellform'0;auto.
     apply chainMergeInitialEvent in H;auto.

     assert (eventKind (eventDefinition event1) = Imported).
     SearchAbout Imported.
     apply chainMergeRuleImport with (conf:=conf) (conf':=conf');auto.
     rewrite H12 in H9. rewrite H9 in H13. rewrite H13 in H14. inversion H14.

     unfold noDupRaise'' in H4. destruct H12. destruct H12. destruct H12. destruct H12.
     destruct H12.
      repeat match goal with
            | [ H: _ /\ _ |- _ ] => destruct H

             end.
            
      destruct H4 with (v:=eventDefinition re). 

      
     (* rewrite monitorObjNoChangeChain with (conf':=conf'') (e:=event1);auto.*)
     Check raise_in. SearchAbout re. 
      apply raise_in with (conf0:=conf'') ;auto.
 remember H2. clear Heqb.   destruct b.
       repeat match goal with
            | [ H: _ /\ _ |- _ ] => destruct H

              end.
             
       rename H26 into ssp;rename H27 into sin. 
     
      
       apply termL5' with (conf:=conf) (e:=event1);auto.
     apply chain' with (conf':=conf') (event2:=event2);auto.    remember H. clear Heqc. apply chainMergeInitial in c.
     destruct c.
     destruct H26.
     apply raised_wellform'0;auto.
     apply chainMergeInitialEvent in H;auto.
   assert (In x2 (scenarioRaise (scenarios M) (eventDefinition re))). 
   
   eapply scenarioRaiseIn. Focus 2. apply H13. Focus 2. apply H14. Focus 2. rewrite <- H9 in H15. apply H15.

   remember H2. clear Heqb.   destruct b.
       repeat match goal with
            | [ H: _ /\ _ |- _ ] => destruct H

              end.
    rename H28 into ssp;rename H29 into sin. 

    
   pose proof chainMergeFinMap.
     destruct H28 with (conf:=conf) (conf':=conf') (e:=event1) (sce:=x2);auto. 
     split;auto. apply chainMergeInitial in H. destruct H;auto. 
     split;auto. split. apply chainMergeInitialEvent in H;auto.
     split;auto. split;auto. 
     split;auto. split;auto. split;auto. 
     assert (In x2 (finishedscenarios conf')). 
     apply H30. exists x1;auto.
    assert (correct_configuration conf').  
    apply termL5' with (conf:=conf) (e:=event1);auto.
     remember H. clear Heqc. apply chainMergeInitial in c.
     destruct c.
     destruct H32.
     apply raised_wellform'0;auto.
     apply chainMergeInitialEvent in H;auto.
     destruct H32.
     unfold scenarioInclusion in inclusion. unfold incl in inclusion. apply inclusion in H31.   rewrite cs_consist in H31. auto. 
   (*  rewrite monitorObjNoChangeChain with (conf':=conf') (e:=event1);auto.*)

      remember H2. clear Heqb.   destruct b.
       repeat match goal with
            | [ H: _ /\ _ |- _ ] => destruct H

              end. 
       rename H29 into ssp;rename H30 into sin. 
   pose proof chainMergeFinMap.
     destruct H29 with (conf:=conf) (conf':=conf') (e:=event1) (sce:=x2);auto. 
     split;auto. apply chainMergeInitial in H. destruct H;auto. 
     split;auto. split. apply chainMergeInitialEvent in H;auto.
     split;auto. split;auto. 
     split;auto. split;auto. split;auto. 
     assert (In x2 (finishedscenarios conf')). 
       apply H31. exists x1;auto.
   pose proof syncRaised''. 

     assert (exists (sce : scenario) (tr : step) (act : action) (exprs : list expr),
          ~ In sce (finishedscenarios conf') /\
          In (sce, eventDefinition event2) (sceEventMap conf'') /\
          In tr (getTransitionsOfScenario sce) /\
          In act (transitionIntoBasicActionList (stepActions tr)) /\
          act = RaiseStmt (eventId (eventDefinition re)) exprs /\
          eventDefinition event2 = event (stepEvent tr)).
     
     apply H33;auto.
     apply termL5' with (conf:=conf) (e:=event1);auto.
     remember H. clear Heqc. apply chainMergeInitial in c.
     destruct c.
     destruct H34.
     apply raised_wellform'0;auto.
     apply chainMergeInitialEvent in H;auto.
                 
     (*rewrite <- monitorObjNoChangeChain with (conf:=conf) (e:=event1);auto.
     rewrite <- monitorObjNoChangeChain with (conf:=conf) (e:=event1);auto.*)
     destruct H34. destruct H34. destruct H34. destruct H34.
     repeat match goal with
            | [ H: _ /\ _ |- _ ] => destruct H

            end.
     
     assert (In x6 (scenarioRaise (scenarios M) (eventDefinition re))).
      eapply scenarioRaiseIn. Focus 2. apply H36. Focus 2. apply H37. Focus 2. apply H38.
      assert (correct_configuration conf').
          apply termL5' with (conf:=conf) (e:=event1);auto.
     remember H. clear Heqc. apply chainMergeInitial in c.
     destruct c.
     destruct H40.
     apply raised_wellform'0;auto.
     apply chainMergeInitialEvent in H;auto.
      pose proof chainMergeFinMap.
  destruct H41 with (conf:=conf) (conf':=conf'') (e:=event1) (sce:=x6);auto.
   
   split;auto. apply chainMergeInitial in H. destruct H;auto.
  split;auto.  split.   apply chainMergeInitialEvent in H;auto. 
       split;auto. split;auto. 
       split;auto. split;auto. split;auto. apply chain' with (conf':=conf') (event2:=event2);auto. 
       assert (In x6 (finishedscenarios conf'')). apply H43;auto. exists (eventDefinition event2);auto.
       assert (correct_configuration conf'').
          apply termL5' with (conf:=conf) (e:=event1);auto.
   apply chain' with (conf':=conf') (event2:=event2);auto.    remember H. clear Heqc. apply chainMergeInitial in c.
     destruct c.
     destruct H45.
     apply raised_wellform'0;auto.
     apply chainMergeInitialEvent in H;auto.

         destruct H45. (*rewrite monitorObjNoChangeSync with (conf':=conf'') (e:=event2);auto.*)
     rewrite <- cs_consist.
      unfold scenarioInclusion in inclusion. apply inclusion;auto.
(* rewrite <- monitorObjNoChangeChain with (conf:=conf) (e:=event1) in H40;auto.*)

      assert (x6 <> x2). unfold not. intros. rewrite H41 in H34. contradiction.
SearchAbout scenarioRaise. 



 assert (eventKind (eventDefinition re) = Internal).
     apply raisedIntervalSync with (conf:=conf') (conf':=conf'') (e:=event2);auto.
     apply termL5' with (conf:=conf) (e:=event1);auto.
     remember H. clear Heqc. 
     apply chainMergeInitialEvent in H;auto. apply chainMergeInitial in c;auto.
     destruct c. destruct H42. apply  raised_wellform'0;auto.
     apply H17 with (sce1:=x2) (sce2:=x6) in H42;auto.
     unfold not;intros. 
     apply H42.
     exists (eventDefinition event1).
     split;auto.
     apply raise_in with (conf0:=conf);auto.
     apply chainMergeInitial in H;destruct H;auto.
     apply chainMergeInitialEvent in H;auto.
     split.
     assert (eventDefinition event1 = x1 \/ ~ (eventDefinition event1 = x1)).
          apply excluded_middle. destruct H44.
     
          apply basic_ts;auto.

          SearchAbout x2.
          assert (correct_configuration conf').
 apply termL5' with (conf:=conf) (e:=event1);auto.
     remember H. clear Heqc. 
     apply chainMergeInitialEvent in H;auto. apply chainMergeInitial in c;auto.
     destruct c. destruct H45. apply  raised_wellform'0;auto.
     destruct H45.
      unfold scenarioInclusion in inclusion. unfold incl in inclusion.
  SearchAbout x2.      apply inclusion in H32;auto.
     rewrite cs_consist in H32;auto.
     
          
     rewrite H44.
     apply chainMergeSceMapAlpha with (M:=M) (conf:=conf) (conf':=conf') (e:=event1);auto.
     split;auto.
      apply chainMergeInitial in H;destruct H;auto.
    split;auto. split;auto. apply chainMergeInitialEvent in H;auto.
    repeat(split;auto).
         
    apply induction_ts with (e2:=x1);auto. 
    assert ( x1 = eventDefinition event1 \/ staticEventLeadTo M (eventDefinition event1) x1).
    apply usedEventLedTo with (conf:=conf) (conf':=conf');auto.
    split;auto.
      apply chainMergeInitial in H;destruct H;auto.
    split;auto. split;auto. apply chainMergeInitialEvent in H;auto.
    repeat(split;auto).
    apply  rangeDomInRev with (a:=x2);auto.    
    destruct H45;auto.
    unfold not in H44;exfalso;auto.
    apply basic_ts;auto.

    
          SearchAbout x2.
          assert (correct_configuration conf').
 apply termL5' with (conf:=conf) (e:=event1);auto.
     remember H. clear Heqc. 
     apply chainMergeInitialEvent in H;auto. apply chainMergeInitial in c;auto.
     destruct c. destruct H45. apply  raised_wellform'0;auto.
     destruct H45.
      unfold scenarioInclusion in inclusion. unfold incl in inclusion.
  SearchAbout x2.      apply inclusion in H32;auto.
  rewrite cs_consist in H32;auto.

  
    apply chainMergeSceMapAlpha with (M:=M) (conf:=conf) (conf':=conf') (e:=event1);auto.
        split;auto.
      apply chainMergeInitial in H;destruct H;auto.
    split;auto. split;auto. apply chainMergeInitialEvent in H;auto.
    repeat(split;auto).
    SearchAbout event2. 
    apply induction_ts with (e2:=eventDefinition event2);auto. 
    apply   raisedEventLedTo with (conf:=conf) (conf':=conf');auto.
    SearchAbout event2.
    unfold synchrony in H5. destruct H5;auto. 
    apply basic_ts;auto.

    SearchAbout x6.


      pose proof chainMergeFinMap.
assert (In x6 (finishedscenarios conf'') <->
        (exists x1 : event_definition, In (x6, x1) (sceEventMap conf''))). 
apply H44 with (conf:=conf) (e:=event1);auto.
split;auto.
apply chainMergeInitial in H;destruct H;auto.
split;auto. split. apply chainMergeInitialEvent in H;auto.
repeat(split;auto).
apply chain' with (conf':=conf') (event2:=event2);auto. 
assert ( In x6 (finishedscenarios conf'') ).
apply H45. exists (eventDefinition event2);auto.

assert (correct_configuration conf''). 
apply termL5' with (conf:=conf) (e:=event1);auto.
apply chain' with (conf':=conf') (event2:=event2);auto. 
remember H. clear Heqc.
apply chainMergeInitial in H;auto.
destruct H. destruct H. apply   raised_wellform'0;auto.
apply chainMergeInitialEvent in c;auto.
destruct H47.
unfold scenarioInclusion in inclusion. unfold incl in inclusion.
apply inclusion in H46. rewrite cs_consist in H46. auto.


     apply chainMergeSceMapAlpha with (M:=M) (conf:=conf) (conf':=conf'') (e:=event1);auto.
     split;auto.
      apply chainMergeInitial in H;destruct H;auto.
    split;auto. split;auto. apply chainMergeInitialEvent in H;auto.
    repeat(split;auto).
    apply chain' with (conf':=conf') (event2:=event2);auto.

(*
    
destruct ((scenarioRaise (scenarios M) (eventDefinition re))).
inversion H40. destruct l. destruct H40;inversion H40;destruct H19;inversion H19.    subst. (*symmetry in H40.*) contradiction.
SearchAbout re.

  assert (eventKind (eventDefinition re) = Internal).
     apply raisedIntervalSync with (conf:=conf') (conf':=conf'') (e:=event2);auto.
     apply termL5' with (conf:=conf) (e:=event1);auto.
     remember H. clear Heqc. 
     apply chainMergeInitialEvent in H;auto. apply chainMergeInitial in c;auto.
     destruct c. destruct H42. apply  raised_wellform'0;auto.
     assert (eventKind (eventDefinition re) = Internal \/ eventKind (eventDefinition re) = Imported ).   left;auto. apply H17 in H43. inversion H43. inversion H45. 
  *)  
Qed.




Lemma raisedEventsAlphabetChainMerge: forall M (conf conf' : configuration M) e re,
    chainMerge conf conf' e ->
    noMergeError' M ->
    noMultAlphabet M ->
    basicPreconditionMon M->
    alphabetRaisingObject M ->
    noDupRaise'' M ->
    In re (raisedevents conf') ->
    (forall sce, In sce (dom (controlstate conf)) -> In (eventDefinition re) (alphabet sce) -> ~ In sce (finishedscenarios conf')).
Proof.
  intros. rename H0 into noMerge. rename H1 into noMulti. rename H2 into bp. rename H3 into alphaObj. rename H4 into nodr. rename H5 into H0. rename H6 into H1. rename H7 into H2.
  generalize dependent re. generalize dependent sce.
  induction H.


  
  -  intros.
     unfold not. intros.
     assert (In (eventDefinition event) (alphabet sce)).
     apply syncFinish with (conf:=conf) (conf':=conf');auto. destruct H;auto.
     unfold not. intros. destruct H.
     repeat match goal with
            | [ H: _ /\ _ |- _ ] => destruct H

            end.
     rewrite H8 in H5.  inversion H5.     
    
     unfold noMultAlphabet in noMulti.
     destruct noMulti.
     (*unfold importedNoCommonAlphabet in H7.*)
     unfold importedNoCommonAlphabet' in H7.
     unfold not in H7.
     remember H0. clear Heqs.
     remember H. clear Heqi. 
     unfold synchrony in s. destruct s.
     destruct H. destruct H.
repeat match goal with
            | [ H: _ /\ _ |- _ ] => destruct H

           end.
apply H7 with (e1:=(eventDefinition event)) (e2:=eventDefinition re);auto.

(*begin insert*)
assert (correct_configuration conf').
destruct bp.

repeat match goal with
            | [ H: _ /\ _ |- _ ] => destruct H

       end.
apply termL5 with (conf:=conf) (e:=event);auto.
split;auto.
assert (In (eventDefinition re) (events M)).
destruct H13. apply raise_in0;auto.
clear H13;clear H14. 
(*end insert*)

     (*Focus 3*) Focus 4.  exists sce. split;auto.
     rewrite <- cs_consist. auto. 
     destruct H10 with (e:=event);auto. unfold  importedEvent in H13.
     destruct (eventKind (eventDefinition event) );inversion H13;auto. 
     Focus 2. intros.
    
     pose proof raisedEventNoImported.
     
     unfold not in H14.
     apply H14 with (conf:=conf ) (conf':=conf') (re:=event) (re':=re);auto.
     apply basic' with (conf':=conf') ;auto. (*split;auto. split;auto.*)

      destruct bp. 
repeat match goal with
            | [ H: _ /\ _ |- _ ] => destruct H

       end.

     apply raisedEventLedTo with (conf:=conf) (conf':=conf');auto.
     apply basic' with (conf':=conf') ;auto.
     
  -
    intros.
    assert (In re (raisedevents conf') \/ ~ In re (raisedevents conf')).
    apply excluded_middle. destruct H4.
    assert (~ In sce (finishedscenarios conf')).
    apply IHchainMerge with (re:=re);auto.
    unfold not. intros.
    assert (In (eventDefinition event2) (alphabet sce)).
    apply syncFinish with (conf:=conf') (conf':=conf'');auto.
     destruct bp.
    repeat match goal with
            | [ H: _ /\ _ |- _ ] => destruct H

           end.
    rename H16 into ssp;rename H17 into sin. 

      apply termL5' with (conf:=conf) (e:=event1);auto.
     remember H. clear Heqc. 
     apply chainMergeInitial in c.
     destruct c.
     destruct H16.
     apply raised_wellform'0.      
     apply chainMergeInitialEvent with (conf':=conf');auto.
      
    assert (In event2 (raisedevents conf')).
    unfold synchrony in H0. destruct H0;auto.
    pose proof noDupEventDefinition''.
    assert ((forall re0 : raisedEvent,
        In re0 (raisedevents conf') ->
        ~
        (exists ev : event_definition,
           In ev (range (sceEventMap conf')) /\ eventDefinition re0 = ev)) /\
       (forall re0 re' : raisedEvent,
        In re0 (raisedevents conf') ->
        In re' (raisedevents conf') -> re0 <> re' -> eventDefinition re0 <> eventDefinition re') ).
    apply H9 with (conf:=conf) (re:=event1);auto.
    destruct H10. 
    clear H10.  clear H9.
    unfold noMultAlphabet in noMulti.
    destruct noMulti.
    unfold noMultAlphabet' in H9.
    assert ( eventDefinition event2 <> eventDefinition re).
    apply H11;auto.
    assert (~ In event2 (raisedevents conf'')).
    unfold not. intros. unfold synchrony in H0. destruct H0. unfold combineFunc in H13.
    destruct (constructConfigList (dom (controlstate conf')) event2 conf');inversion H13.
    destruct v;inversion H15.
    destruct (innerCombineFunc'''' conf' (c :: v));inversion H15. unfold removeEventFromConf in H17. rewrite <- H17 in H12. simpl in H12. SearchAbout removeEvent'.
    apply removeNotIn in H12;auto. 
    unfold not. intros. rewrite H13 in H12. contradiction.
    
    assert (~ (exists sce : scenario, In sce (scenarios M) /\ In (eventDefinition event2) (alphabet sce) /\ In (eventDefinition re) (alphabet sce))).
    apply H9 with (e:=eventDefinition event1) ;auto.

    
    (*begin insert*)
    assert (correct_configuration conf').
destruct bp.

repeat match goal with
            | [ H: _ /\ _ |- _ ] => destruct H

       end.
apply termL5' with (conf:=conf) (e:=event1);auto.
remember H. clear Heqc. 
apply chainMergeInitial in H. destruct H;auto. destruct H.
apply raised_wellform'0;auto. apply chainMergeInitialEvent in c;auto. 
assert (In (eventDefinition re) (events M)).
destruct H13. apply raise_in;auto.
assert (In (eventDefinition event2) (events M)).
destruct H13. apply raise_in;auto.
clear H13;clear H14;clear H15. 
    (*end insert*)
    
   
    remember H. clear Heqc. 
    apply chainMergeInitialEvent in H.
    eapply raise_in;eauto. apply chainMergeInitial in c.  destruct c;auto.
  
    destruct bp.
    repeat match goal with
            | [ H: _ /\ _ |- _ ] => destruct H

           end.
    eapply raisedEventLedTo with (conf':=conf');eauto.
     destruct bp.
    repeat match goal with
            | [ H: _ /\ _ |- _ ] => destruct H

           end.
    eapply raisedEventLedTo with (conf':=conf');eauto.
    apply H13. exists sce;auto. 
    split;auto.
    SearchAbout scenarios. rewrite <- cs_consist with (conf0:=conf);auto.
    apply chainMergeInitial in H. destruct H;auto. 
    assert (~ In sce (finishedscenarios conf')).
    unfold not. intros.
    
    pose proof chainMergeFinMap.
    assert (exists ev : event_definition, In (sce, ev) (sceEventMap conf')).
    destruct H6 with (conf:=conf) (conf':=conf') (e:=event1) (sce:=sce);auto.
    destruct bp.
    
     repeat match goal with
            | [ H: _ /\ _ |- _ ] => destruct H

            end.
     rename H16 into ssp;rename H17 into sin. 
     split;auto.
     apply chainMergeInitial in H.  destruct H;auto.
     split;auto.
     split.
     apply chainMergeInitialEvent in H;auto.
     split;auto. split;auto. split;auto.
    split;auto. split;auto. 
     pose proof noDupEventDefinition''.
    assert ((forall re0 : raisedEvent,
        In re0 (raisedevents conf'') ->
        ~
        (exists ev : event_definition,
           In ev (range (sceEventMap conf'')) /\ eventDefinition re0 = ev)) /\
       (forall re0 re' : raisedEvent,
        In re0 (raisedevents conf'') ->
        In re' (raisedevents conf'') -> re0 <> re' -> eventDefinition re0 <> eventDefinition re') ).
    apply H8 with (conf:=conf) (re:=event1);auto.
    apply chain' with (conf':=conf') (event2:=event2);auto. 
    destruct H9. clear H10. clear H8. 
    unfold noMultAlphabet in noMulti.
    destruct noMulti.
    unfold noMultAlphabet' in H8.
    destruct H7.
    assert ( eventDefinition re <> x).
    apply H9 in H2. unfold not. intros.
    apply H2. exists x. split;auto.
    
    apply rangeDomInRev with (a:=sce);auto.
    apply sceEventMapNoChangeSync with (conf:=conf') (e:=event2);auto.

    destruct bp.
     repeat match goal with
            | [ H: _ /\ _ |- _ ] => destruct H

           end.
        rename H21 into ssp;rename H22 into sin.
     apply termL5' with (conf:=conf) (e:=event1);auto.
     remember H. clear Heqc. 
     apply chainMergeInitial in c.
     destruct c.
     destruct H21.
     apply raised_wellform'0.
     apply chainMergeInitialEvent with (conf':=conf');auto.
   assert (~ (exists sce : scenario, In sce (scenarios M) /\ In x (alphabet sce) /\ In (eventDefinition re) (alphabet sce))). 
   (*assert ...*)
   assert (x = eventDefinition event1 \/ x <> eventDefinition event1).
   apply excluded_middle. destruct H12.  Focus 2.
   (*begin insert*)
   SearchAbout sceEventMap.
   SearchAbout alphabet.
   
   (*alphabetInObject*)
   assert (In x (alphabet sce)).
   apply chainMergeSceMapAlpha with (M:=M) (conf:=conf) (conf':=conf') (e:=event1);auto.
     destruct bp.
     repeat match goal with
            | [ H: _ /\ _ |- _ ] => destruct H

            end.
     split;auto.   apply chainMergeInitial in H;destruct H;auto. repeat(split;auto).
     apply chainMergeInitialEvent with (conf':=conf') ;auto.
     SearchAbout sce.  clear H13. 
    (*end insert*)
   
  apply H8 with (e:=eventDefinition event1) ;auto.
    remember H. clear Heqc. 
    apply chainMergeInitialEvent in H.
    eapply raise_in;eauto. apply chainMergeInitial in c.  destruct c;auto.
    
    destruct bp.
    repeat match goal with
            | [ H: _ /\ _ |- _ ] => destruct H

           end.
    Focus 2. 

    apply raisedEventLedTo with (conf:=conf) (conf':=conf'');eauto.
    
    apply chain' with (conf':=conf') (event2:=event2);auto.
   
      destruct bp.
    repeat match goal with
            | [ H: _ /\ _ |- _ ] => destruct H

           end.
    auto.

 
     destruct bp.
    repeat match goal with
            | [ H: _ /\ _ |- _ ] => destruct H

           end.
    auto.

    destruct bp.
    repeat match goal with
            | [ H: _ /\ _ |- _ ] => destruct H

           end.
    auto.

    destruct bp.
    repeat match goal with
            | [ H: _ /\ _ |- _ ] => destruct H

           end.
    auto.
    rename H22 into ssp;rename H23 into sin. 

    
    pose proof usedEventLedTo.
    remember H7. clear Heqi. 
    apply rangeDomInRev with (a:=sce) in i;auto.
 
    assert ( x = eventDefinition event1 \/ staticEventLeadTo M (eventDefinition event1) x).
    apply H22 with (conf:=conf) (conf':=conf');auto.
    split;auto.
    apply chainMergeInitial in H. destruct H;auto.
    split;auto. split;auto.
    apply chainMergeInitialEvent in H;auto.
    split;auto. split;auto. split;auto. split;auto. split;auto. 
    destruct H23;auto.
    contradiction.
    (*unfold importedNoCommonAlphabet in H10.*)
    unfold importedNoCommonAlphabet' in H10.
    rewrite  H12. 
    apply H10.
    (*begin insert*)
    (*In re (events M)*)
    (*end insert*)
    apply raise_in with (conf0:=conf).
    apply chainMergeInitial in H.
    destruct H;auto.
    apply chainMergeInitialEvent in H;auto.
    remember H. clear Heqc. 
    apply chainMergeInitial in H.
    destruct H.     
      repeat match goal with
            | [ H: _ /\ _ |- _ ] => destruct H

             end.
      destruct H14 with (e:=event1);auto.
      remember c. clear Heqc0.
      apply chainMergeInitialEvent in c;auto.
      unfold importedEvent  in H17.
      destruct (eventKind (eventDefinition event1));inversion H17;auto.

        destruct bp. 
repeat match goal with
            | [ H: _ /\ _ |- _ ] => destruct H

       end.
rename H22 into ssp;rename H23 into sin. 
apply raisedEventLedTo with (conf:=conf) (conf':=conf'');auto.

     apply chain' with (conf':=conf') (event2:=event2);auto.
       
      rewrite H12 in H11;auto.
      apply H12.  exists sce;auto. split;auto.
      rewrite <- cs_consist with (conf0:=conf);auto.
      apply chainMergeInitial in H.
    destruct H;auto.
    split;auto. 
    
      apply chainMergeSceMapAlpha with (conf:=conf) (conf':=conf') (e:=event1);auto.
      
      destruct bp.
      
repeat match goal with
            | [ H: _ /\ _ |- _ ] => destruct H

           end.
split;auto.
apply chainMergeInitial in H.
    destruct H;auto.
split;auto. 
split;auto.
apply chainMergeInitialEvent in H;auto.
split;auto. split;auto. split;auto. split;auto. split;auto. 
unfold not. intros. 
assert (In (eventDefinition event2) (alphabet sce)). 
apply syncFinish with (conf:=conf') (conf':=conf'') (re:=event2);auto. 
destruct bp.
repeat match goal with
            | [ H: _ /\ _ |- _ ] => destruct H

       end.
rename H16 into ssp;rename H17 into sin. 
 apply termL5' with (conf:=conf) (e:=event1);auto.
     remember H. clear Heqc. 
     apply chainMergeInitial in c.
     destruct c.
     destruct H16.
     apply raised_wellform'0.
     apply chainMergeInitialEvent with (conf':=conf');auto.
unfold noMultAlphabet in noMulti.    
destruct noMulti.
unfold noMultAlphabet' in H8. 
unfold noDupRaise'' in nodr.
pose proof noDupEventDefinition''.
    assert ((forall re0 : raisedEvent,
        In re0 (raisedevents conf'') ->
        ~
        (exists ev : event_definition,
           In ev (range (sceEventMap conf'')) /\ eventDefinition re0 = ev)) /\
       (forall re0 re' : raisedEvent,
        In re0 (raisedevents conf'') ->
        In re' (raisedevents conf'') -> re0 <> re' -> eventDefinition re0 <> eventDefinition re') ).
    apply H10 with (conf:=conf) (re:=event1);auto.
    apply chain' with (conf':=conf') (event2:=event2);auto. 
    split;auto.
    destruct H11. clear H12. clear H10.
    remember H2. clear Heqi. apply H11 in i.

    assert (exists ev : event_definition, In (sce, ev) (sceEventMap conf'')).
    pose proof chainMergeFinMap.
    destruct H10 with (conf:=conf) (conf':=conf'') (e:=event1) (sce:=sce);auto.
    destruct bp.
     repeat match goal with
            | [ H: _ /\ _ |- _ ] => destruct H

           end.
     split;auto.
     apply chainMergeInitial in H.  destruct H;auto.
     split;auto.
     split.
     apply chainMergeInitialEvent in H;auto.
     split;auto. split;auto. split;auto. split;auto. split;auto. 
apply chain' with (conf':=conf') (event2:=event2);auto. 
   destruct H10.   
   assert ( eventDefinition re <> x).
   unfold not. intros.    apply i. exists x.
   split;auto. SearchAbout (In _ (range _)). apply rangeDomInRev with (a:=sce);auto. 
    
   assert (~ (exists sce : scenario, In sce (scenarios M) /\ In x (alphabet sce) /\ In (eventDefinition re) (alphabet sce))).

    assert (x = eventDefinition event1 \/ x <> eventDefinition event1).
   apply excluded_middle. destruct H13.  Focus 2.  
   apply H8 with (e:=eventDefinition event1) ;auto.
   (*begin insert*)
   (*end insert*)
   
    remember H. clear Heqc. 
    apply chainMergeInitialEvent in H.
    apply raise_in with (conf0:=conf);auto. apply chainMergeInitial in c.  destruct c;auto.
    
    destruct bp.
    repeat match goal with
            | [ H: _ /\ _ |- _ ] => destruct H

           end.
    Focus 2. 
    apply raisedEventLedTo with (conf:=conf) (conf':=conf'');auto.
    apply chain' with (conf':=conf') (event2:=event2);auto. 
   
      destruct bp.
    repeat match goal with
            | [ H: _ /\ _ |- _ ] => destruct H

           end.
    auto.

     destruct bp.
    repeat match goal with
            | [ H: _ /\ _ |- _ ] => destruct H

           end.
    auto.

    destruct bp.
    repeat match goal with
            | [ H: _ /\ _ |- _ ] => destruct H

           end.
    auto.

    destruct bp.
    repeat match goal with
            | [ H: _ /\ _ |- _ ] => destruct H

           end.
    auto.
    rename H23 into ssp;rename H24 into sin. 
    pose proof usedEventLedTo.
    
    assert ( x = eventDefinition event1 \/ staticEventLeadTo M (eventDefinition event1) x).
    apply H23 with (conf:=conf) (conf':=conf'');auto.
    apply chain' with (conf':=conf') (event2:=event2);auto. 
    split;auto.
    apply chainMergeInitial in H. destruct H;auto.
    split;auto. split;auto.
    apply chainMergeInitialEvent in H;auto.
    split;auto. split;auto. split;auto. split;auto. split;auto. 
    apply rangeDomInRev with (a:=sce);auto. 
    destruct H24;auto.
    contradiction.
    (*unfold importedNoCommonAlphabet in H9.*)
    unfold importedNoCommonAlphabet' in H9.
    rewrite  H13. 
    apply H9.

    
    apply raise_in with (conf0:=conf).
    apply chainMergeInitial in H.
    destruct H;auto.
   apply chainMergeInitialEvent in H;auto.
   remember H. clear Heqc. 
    apply chainMergeInitial in H.
    destruct H.     
      repeat match goal with
            | [ H: _ /\ _ |- _ ] => destruct H

             end.
      destruct H15 with (e:=event1);auto.
      remember c. clear Heqc0.
      apply chainMergeInitialEvent in c;auto.
      unfold importedEvent  in H18.
      destruct (eventKind (eventDefinition event1));inversion H18;auto.

   destruct bp. 
repeat match goal with
            | [ H: _ /\ _ |- _ ] => destruct H

       end.
apply raisedEventLedTo with (conf:=conf) (conf':=conf'');auto.
     apply chain' with (conf':=conf') (event2:=event2);auto.


      rewrite H13 in H12;auto.
      apply H13.  exists sce;auto. split.
      rewrite <- cs_consist with (conf0:=conf);auto.
      apply chainMergeInitial in H.
    destruct H;auto.  split;auto.
      
      apply chainMergeSceMapAlpha with (conf:=conf) (conf':=conf'') (e:=event1);auto.
      
      destruct bp.
repeat match goal with
            | [ H: _ /\ _ |- _ ] => destruct H

           end.
     split;auto.
    apply chainMergeInitial in H. destruct H;auto.
    split;auto. split;auto.
    apply chainMergeInitialEvent in H;auto.
    split;auto. split;auto. split;auto. split;auto. split;auto. 
   apply chain' with (conf':=conf') (event2:=event2);auto. 
    
Qed.




Lemma preserveSync' : forall M (conf conf' : configuration M) re,
    chainMerge conf conf' re ->
    noMergeError' M ->
    noMultAlphabet M ->
    basicPreconditionMon M->
    alphabetRaisingObject M ->
    noDupRaise'' M ->
    ~ finalConfig' conf' ->
    syncProgress' conf'. 
Proof.
  intros. rename H3 into alpha. rename H4 into raiseNoDup.   rename H5 into H3. 
  induction H.
 - 
   unfold syncProgress'.
   unfold finalConfig' in H3.
   split.
   unfold not;intros.
   apply H3.
   rewrite H5;auto.    
   intros.
   unfold not;intros.
   pose proof raisedEventsAlphabetChainMerge.
   (* assert ((filterList (finishedscenarios conf') (dom (controlstate conf')) scenario_dec) = nil \/ (filterList (finishedscenarios conf') (dom (controlstate conf')) scenario_dec) <> nil).
     apply excluded_middle.
     destruct H8.

     apply filterListIncl in H8;auto.*)
     assert ( forall sce : scenario,
       In sce (dom (controlstate conf)) ->
       In (eventDefinition re) (alphabet sce) -> ~ In sce (finishedscenarios conf')).
     intros.
     apply H7 with (conf:=conf) (e:=event) (re:=re);auto.
     apply basic';auto.
    
     unfold alphabetRaisingObject in alpha.
      assert (correct_configuration conf').
      destruct H2.
     repeat match goal with
            | [ H: _ /\ _ |- _ ] => destruct H

            end.
      apply termL5 with (conf:=conf) (e:=event);auto.
     destruct H;auto.
     destruct H.
     destruct H.
     apply   raised_wellform'0 ;auto.
     unfold synchrony in H4;intuition.
           
     assert (exists sce : scenario, In sce (scenarios M) /\ In (eventDefinition re) (alphabet sce)).
     apply alpha;auto.
     
     apply raise_in with (conf0:=conf');auto.
     destruct H9.
     apply raisedType in H5;auto.
     destruct H10.
     destruct H10.
     unfold not in H8.
     apply H8 with (sce:=x);auto.
    
     destruct H;destruct H.
     
     rewrite  cs_consist;auto.
     assert (In x (finishedscenarios conf') \/ ~ In x (finishedscenarios conf')).
     apply excluded_middle.
     destruct H12;auto.
         
   
    assert (In x (filter
         (fun x0 : scenario => inList event_definition_dec (eventDefinition re) (alphabet x0))
         (filterList (finishedscenarios conf') (dom (controlstate conf')) scenario_dec))).
    apply filter_In;auto.
    split.
  
    apply filterIn;auto.
    destruct H9.    rewrite cs_consist;auto.
    SearchAbout inList.
    apply inListLemma;auto.     rewrite H6 in H13.
    inversion H13.
 -  unfold syncProgress'. 
    unfold finalConfig' in H3.
    split.
     unfold not;intros.
   apply H3.
   rewrite H5;auto.    
   intros.
   unfold not;intros.
     pose proof raisedEventsAlphabetChainMerge.  
     assert ( forall sce : scenario,
       In sce (dom (controlstate conf)) ->
       In (eventDefinition re) (alphabet sce) -> ~ In sce (finishedscenarios conf'')).
     intros.   
     apply H7 with (conf:=conf) (e:=event1) (re:=re);auto.
     apply chain' with (conf':=conf') (event2:=event2) ;auto.      


       unfold alphabetRaisingObject in alpha.
      assert (correct_configuration conf').
      destruct H2.
     repeat match goal with
            | [ H: _ /\ _ |- _ ] => destruct H

            end.
     apply termL5' with (conf:=conf) (e:=event1);auto.
     remember H.
     clear Heqc.
    apply chainMergeInitial in H.    apply chainMergeInitialEvent in c.   
     destruct H;auto.
     destruct H.
    
     apply   raised_wellform'0 ;auto.
     assert (correct_configuration conf'').
         destruct H2.
     repeat match goal with
            | [ H: _ /\ _ |- _ ] => destruct H

            end.
     apply termL5' with (conf:=conf) (e:=event1);auto.
    apply chain' with (conf':=conf') (event2:=event2) ;auto.     remember H.
     clear Heqc.
    apply chainMergeInitial in H.    apply chainMergeInitialEvent in c.   
     destruct H;auto.
     destruct H.
    
     apply   raised_wellform'0 ;auto.
          
           
     assert (exists sce : scenario, In sce (scenarios M) /\ In (eventDefinition re) (alphabet sce)).
     apply alpha;auto.
     
     apply raise_in with (conf0:=conf'');auto.
     destruct H10.
     apply raisedType in H5;auto.
     destruct H11.
     destruct H11.
     unfold not in H8.
     apply H8 with (sce:=x);auto.
     apply chainMergeInitial in H.  
    
     destruct H;destruct H.
     
     rewrite  cs_consist;auto.
     assert (In x (finishedscenarios conf'') \/ ~ In x (finishedscenarios conf'')).
     apply excluded_middle.
     destruct H13;auto.
         
   
    assert (In x (filter
         (fun x0 : scenario => inList event_definition_dec (eventDefinition re) (alphabet x0))
         (filterList (finishedscenarios conf'') (dom (controlstate conf'')) scenario_dec))).
    apply filter_In;auto.
    split.
  
    apply filterIn;auto.
    destruct H10.    rewrite cs_consist;auto.
  
    apply inListLemma;auto.     rewrite H6 in H14.
    inversion H14.
Qed.    

   
Lemma preserveSync : forall M (conf conf' : configuration M) re,
    chainMerge conf conf' re ->
    noMergeError' M ->
    noMultAlphabet M ->
    basicPreconditionMon M->
    alphabetRaisingObject M ->
    noDupRaise'' M ->
    ~ finalConfig conf' ->
    syncProgress conf'. 
Proof.
  intros. rename H3 into alpha. rename H4 into raiseNoDup.   rename H5 into H3. 
  induction H.


  

 - 
   unfold syncProgress.
   remember H4.
   clear Heqs. 
     intros. 
     unfold not. intros.
     unfold not in H3.
     apply H3. 
     unfold finalConfig.
     right.
     Print noMultAlphabet.
     assert ((filterList (finishedscenarios conf') (dom (controlstate conf')) scenario_dec) = nil \/ (filterList (finishedscenarios conf') (dom (controlstate conf')) scenario_dec) <> nil).
     apply excluded_middle.
     destruct H7.

     apply filterListIncl in H7;auto.
     
     SearchAbout filterList.
     remember ( filterList (finishedscenarios conf') (dom (controlstate conf')) scenario_dec).
     destruct l. contradiction. clear H7.
     assert (In re (raisedevents conf) \/ ~ In re (raisedevents conf)).
     apply excluded_middle.
     
     destruct H7.
     
     unfold synchrony in H4.
     destruct H4.
     remember H. clear Heqi.
     remember H5. clear Heqi0. 
     destruct H.
     destruct H9.
     assert (event = re).
     SearchAbout (In _ (raisedevents _)).
     destruct ((raisedevents conf)). inversion H9.
     destruct H4. destruct H7. subst. Focus 2. destruct l0. inversion H7. inversion H9.
     Focus 2.  destruct l0. destruct H7. inversion H4. inversion H7. inversion H9. auto. 
     subst.
     unfold combineFunc in H8.
     destruct (constructConfigList (dom (controlstate conf)) re conf);inversion H8.
     destruct v;inversion H8.

     destruct v.

      destruct (mergeConfigFunc' conf conf c );inversion H13.
     rewrite <- H14 in H5. unfold removeEventFromConf in H5. simpl in H5.
    
     assert (~ In re (removeEvent' re (raisedevents v))).
     apply removeNotIn;auto.
     contradiction.

     
     
     destruct (innerCombineFunc'''' conf (c0::v ));inversion H13.
     destruct ( mergeConfigFunc' conf c c1 );inversion H14.
     rewrite <- H15 in H5. unfold removeEventFromConf in H5. simpl in H5.
    
     assert (~ In re (removeEvent' re (raisedevents v0))).
     apply removeNotIn;auto.
     contradiction.
   

     remember H. 
     clear Heqi.
     remember H5. clear Heqi0.
     
     unfold synchrony in H4.
     destruct H4.
     unfold combineFunc in H8.
     remember (constructConfigList (dom (controlstate conf)) event conf).
     destruct e;inversion H8. clear H10.
     destruct v;inversion H8. unfold constructConfigList in Heqe.

     destruct v. 
        remember (mergeConfigFunc' conf conf c).      
     destruct e;inversion H10.
     rewrite <- H11 in H5.
     unfold removeEventFromConf in H5. simpl in H5.
     apply removeIn in H5.
     unfold mergeConfigFunc' in Heqe0. 
     destruct (mergeDataStateFunc (datastate conf) (datastate conf) (datastate c));inversion Heqe0.
     remember ( mergeControlStateFunc (controlstate conf) (controlstate conf) (controlstate c)).
     destruct e;inversion H12. simpl. rewrite H13 in H5;simpl in H5. clear H12.
     clear Heqe0.
    (* unfold mergeList' in H5.*)
     rewrite in_app_iff in H5.
     
     destruct H5.
     contradiction. 
   (*  apply filterL2 in H5.*)
     pose proof termL2.

         pose proof termL2.
      assert ( exists sce : scenario, In sce (filter
              (fun x : scenario =>
               inList event_definition_dec (eventDefinition event) (alphabet x))
              (filterList (finishedscenarios conf) (dom (controlstate conf)) scenario_dec)) /\ Result c = constructConfig sce event conf).
      apply H12 with (lst:=c::nil);auto.
      split;auto. left;auto.
      destruct H14. destruct H14. 
      apply filter_In in H14. destruct H14.
      clear H13. clear H9;clear H10. clear H11.  
     remember H14. clear Heqi1. 
     apply filterL1 in H14. 
     apply filterL2 in i1. apply reverseinListLemma in H16.
    
     pose proof raisedEventsInternal.
     destruct H2.
         repeat match goal with
            | [ H: _ /\ _ |- _ ] => destruct H

                end.
    rename H22 into ssp;rename H23 into sin. 
         remember H15.   clear Heqe0.        
         apply H9 with (re':=re) in H15;auto.
   
      unfold alphabetRaisingObject in alpha.
      assert (In (eventDefinition re) (events M)).
      pose proof constructConfigEvents.
      eapply H22 with (conf':=c) (re:=event) (sce:=x);eauto. 
   
      remember H22. clear Heqi2. 
      apply alpha in H22;auto.
      destruct H22. destruct H22.
      unfold noMultAlphabet in H1.
      destruct H1.
      unfold importedNoCommonAlphabet' in H24.
      destruct H.
      remember H4. clear Heqi3. 
      apply raise_in in H4;auto.
     repeat match goal with
            | [ H: _ /\ _ |- _ ] => destruct H

            end.
     apply H26 in i3;auto. destruct i3.
     apply H24 with (e2:=eventDefinition re) in H4;auto.
     Focus 2. unfold importedEvent in H29.
     destruct (eventKind (eventDefinition event));inversion H29;auto.
     Focus 3.
     unfold not. intros.
     assert ((eventKind (eventDefinition event)) = Imported).
     unfold importedEvent in H29.
     destruct (eventKind (eventDefinition event));inversion H29;auto.
     rewrite H31 in H32. rewrite H32 in H15;inversion H15.
      
     assert (~ In x0 (finishedscenarios conf')).
     unfold not. intros.
     apply H4.
     exists x0. split;auto. split;auto. 
     pose proof syncFinish.
     apply H32 with (conf:=conf) (conf':=conf');auto.
     unfold not. intros. 
     rewrite H27 in H33. inversion H33. 
   
      
      assert (In x0 (filterList (finishedscenarios conf') (dom (controlstate conf')) scenario_dec)).
      apply filterIn;auto.
      rewrite <- domControlSync with (conf:=conf) (e:=event);auto.
      destruct H;auto. 
      rewrite cs_consist;auto.
      rewrite <- Heql in H32. 
      assert (In x0 (filter
         (fun x0 : scenario => inList event_definition_dec (eventDefinition re) (alphabet x0))
         (s0 :: l) )).
      apply filter_In;auto. split;auto.
       apply inListLemma;auto.
       rewrite H6 in H33;inversion H33.
 apply raisedEventLedTo with (conf:=conf) (conf':=conf');auto. 
      apply basic';auto.  



     

     remember ( innerCombineFunc'''' conf (c0::v)).
     destruct o;inversion H10.

     pose proof innerCombineFuncRaisedEvents.
     remember (mergeConfigFunc' conf c c1).
     destruct e;inversion H11.
     unfold removeEventFromConf. simpl.
     unfold removeEventFromConf in H13.
     rewrite <- H13 in H5. simpl in H5.
     apply removeIn in H5.
     unfold mergeConfigFunc' in Heqe0.
     destruct (mergeDataStateFunc (datastate conf) (datastate c) (datastate c1));inversion Heqe0.
     remember ( mergeControlStateFunc (controlstate conf) (controlstate c) (controlstate c1));inversion H14.
     destruct e;inversion H15. simpl.
     clear H14. rewrite  H16 in H5;simpl in H5.
     rewrite in_app_iff in H5.
     destruct H5. Focus 2. 
     apply H9 with (confList:= c0::v) (conf:=conf) in H5;auto.
     destruct H5. destruct H5.
     pose proof termL2.
     assert (exists sce : scenario, In sce (filter
              (fun x : scenario =>
               inList event_definition_dec (eventDefinition event) (alphabet x))
              (filterList (finishedscenarios conf) (dom (controlstate conf)) scenario_dec)) /\ Result x = constructConfig sce event conf).
     apply H14 with (lst:=c::c0::v);auto. split;auto. right;auto. 
     destruct H17. destruct H17.
     apply filter_In in H17. destruct H17.
     remember H17. clear Heqi1.
     apply filterL1 in H17. 
     apply filterL2 in i1. clear H15.
     clear H8. clear H13.
     clear Heqe0. clear H10;clear H11.
     clear H16. SearchAbout inList. apply reverseinListLemma in H19.

     
     pose proof raisedEventsInternal.
     destruct H2.
         repeat match goal with
            | [ H: _ /\ _ |- _ ] => destruct H

                end.
         rename H23 into ssp;rename H24 into sin.
         remember H18.   clear Heqe0.        
         apply H8 with (re':=re) in H18;auto.
   
     
      unfold alphabetRaisingObject in alpha.
      assert (In (eventDefinition re) (events M)).
      pose proof constructConfigEvents.
      eapply H23 with (conf':=x) (re:=event) (sce:=x0);eauto. 
   
      remember H23. clear Heqi2. 
      apply alpha in H23;auto.
      destruct H23. destruct H23.
      unfold noMultAlphabet in H1.
      destruct H1.
     
      (*unfold importedNoCommonAlphabet in H25.*)
      unfold importedNoCommonAlphabet' in H25.
      
      destruct H.
      remember H4. clear Heqi3. 
      apply raise_in in H4;auto.
     repeat match goal with
            | [ H: _ /\ _ |- _ ] => destruct H

            end.
     apply H27 in i3;auto. destruct i3.
     SearchAbout re. 
     apply H25 with (e2:=eventDefinition re) in H4;auto.
     (*begin insert*)
     (*In (eventDefinition re) (events mon)*)
     (*end insert*)
     Focus 2. unfold importedEvent in H30.
     destruct (eventKind (eventDefinition event));inversion H30;auto.
     Focus 3.
     unfold not. intros.
     assert ((eventKind (eventDefinition event)) = Imported).
     unfold importedEvent in H30.
     destruct (eventKind (eventDefinition event));inversion H30;auto.
     rewrite H32 in H33. rewrite H33 in H18;inversion H18.
      
     assert (~ In x1 (finishedscenarios conf')).
     unfold not. intros.
     apply H4.
     exists x1. split;auto. split;auto.  
     pose proof syncFinish.  
     apply H33 with (conf:=conf) (conf':=conf');auto.
     rewrite H28. unfold not. intros. inversion H34. 
          
     
      
      assert (In x1 (filterList (finishedscenarios conf') (dom (controlstate conf')) scenario_dec)).
      apply filterIn;auto.
      
      apply domControlSync in s;auto. rewrite <- s;auto.
      destruct H. rewrite cs_consist;auto.
      rewrite <- Heql in H33.
      SearchAbout filter.
      assert ((fun x0 : scenario => inList event_definition_dec (eventDefinition re) (alphabet x0)) x1 = true).
      SearchAbout inList. apply inListLemma;auto.
      assert (In x1  (s0 :: l) /\ (fun x0 : scenario => inList event_definition_dec (eventDefinition re) (alphabet x0)) x1 = true). split;auto.
      rewrite <- filter_In in H35. rewrite H6 in H35. inversion H35.

      
       SearchAbout  staticEventLeadTo. 
      apply raisedEventLedTo with (conf:=conf) (conf':=conf');auto. 
      apply basic';auto.       
      remember H5. clear Heqi1.
      (*apply filterL1 in H5.*)
      (*apply filterL2 in i.*)
      pose proof termL2.
      assert ( exists sce : scenario, In sce (filter
              (fun x : scenario =>
               inList event_definition_dec (eventDefinition event) (alphabet x))
              (filterList (finishedscenarios conf) (dom (controlstate conf)) scenario_dec)) /\ Result c = constructConfig sce event conf).
      apply H12 with (lst:=c::c0::v);auto.
      split;auto. left;auto.
      destruct H14. destruct H14. clear H16. clear H15. clear H13. clear Heqe0.
      apply filter_In in H14. destruct H14.

     remember H13. clear Heqi2. 
     apply filterL1 in H13. 
     apply filterL2 in i2. apply reverseinListLemma in H14.
    
     pose proof raisedEventsInternal.
     destruct H2.
         repeat match goal with
            | [ H: _ /\ _ |- _ ] => destruct H

                end.
         rename H25 into ssp;rename H26 into sin. 
     remember H17.   clear Heqe0.        
         apply H15 with (re':=re) in H17;auto.
         
     
      unfold alphabetRaisingObject in alpha.
      assert (In (eventDefinition re) (events M)).
      pose proof constructConfigEvents.
      eapply H25 with (conf':=c) (re:=event) (sce:=x);eauto. 
   
      remember H25. clear Heqi3. 
      apply alpha in H25;auto.
      destruct H25. destruct H25.
      unfold noMultAlphabet in H1.
      destruct H1.
      unfold importedNoCommonAlphabet' in H27.
      destruct H.
      remember H4. clear Heqi4. 
      apply raise_in in H4;auto.
     repeat match goal with
            | [ H: _ /\ _ |- _ ] => destruct H

            end.
     apply H29 in i4;auto. destruct i4.
     apply H27 with (e2:=eventDefinition re) in H4;auto.
     Focus 2. unfold importedEvent in H32.
     destruct (eventKind (eventDefinition event));inversion H32;auto.
     Focus 3.
     unfold not. intros.
     assert ((eventKind (eventDefinition event)) = Imported).
     unfold importedEvent in H32.
     destruct (eventKind (eventDefinition event));inversion H32;auto.
     rewrite H34 in H35. rewrite H35 in H17;inversion H17.
      
     assert (~ In x0 (finishedscenarios conf')).
     unfold not. intros.
     apply H4.
     exists x0. split;auto. split;auto. 
     pose proof syncFinish.
     apply H35 with (conf:=conf) (conf':=conf');auto.
     unfold not. intros. 
     rewrite H30 in H36. inversion H36. 
   
      
      assert (In x0 (filterList (finishedscenarios conf') (dom (controlstate conf')) scenario_dec)).
      apply filterIn;auto.
      rewrite <- domControlSync with (conf:=conf) (e:=event);auto.
      destruct H;auto. 
      rewrite cs_consist;auto.
      rewrite <- Heql in H35. 
      assert (In x0 (filter
         (fun x0 : scenario => inList event_definition_dec (eventDefinition re) (alphabet x0))
         (s0 :: l) )).
      apply filter_In;auto. split;auto.
      SearchAbout inList. apply inListLemma;auto.
      rewrite H6 in H36;inversion H36. 

        apply raisedEventLedTo with (conf:=conf) (conf':=conf');auto. 
      apply basic';auto.       
      
    
    
 -
   unfold syncProgress.
    
     intros. 
     unfold not. intros.
     unfold not in H3.
     apply H3. 
     unfold finalConfig.
     right.
    
     unfold  noMultAlphabet in H1.
     destruct H1.
     unfold noMultAlphabet' in H1.
     remember H4.
     clear Heqs.
     pose proof raisedEventsAlphabetChainMerge.
     assert (chainMerge conf conf'' event1). 
     apply chain' with (conf':=conf') (event2:=event2);auto.
     unfold alphabetRaisingObject in alpha.
     assert (exists sce : scenario,
                In sce (scenarios M) /\ In (eventDefinition re) (alphabet sce)).
     apply alpha.
     assert (correct_configuration conf'').
      destruct H2.
     repeat match goal with
            | [ H: _ /\ _ |- _ ] => destruct H

            end.
     rename H18 into ssp;rename H19 into sin. 
     apply termL5' with (conf:=conf) (e:=event1);auto.
     apply chainMergeInitial in H9.
     destruct H9.
     destruct H9.
     apply raised_wellform'0.
    
     apply chainMergeInitialEvent with (conf':=conf');auto.
     destruct H10.
     Check monitorObjNoChangeChain.
     auto. left;auto. 
     apply raisedInterval with (conf:=conf) (conf':=conf'') (e:=event1);auto.
     destruct H10. 
     destruct H10.

     assert (In x (dom (controlstate conf))).
       apply chainMergeInitial in H9.
     destruct H9.
     destruct H9.
     rewrite  cs_consist;auto.
     
       assert ( forall sce : scenario,
       In sce (dom (controlstate conf)) ->
       In (eventDefinition re) (alphabet sce) -> ~ In sce (finishedscenarios conf'')).
   Check raisedEventsAlphabetChainMerge. 
       apply raisedEventsAlphabetChainMerge with (e:=event1);auto.
       split;auto.
       assert (~ In x (finishedscenarios conf'')). 
       apply H13;auto.
       assert (In x (filter
         (fun x0 : scenario => inList event_definition_dec (eventDefinition re) (alphabet x0))
         (filterList (finishedscenarios conf'') (dom (controlstate conf'')) scenario_dec))). 
       apply filter_In.   split;auto.
       apply  filterIn ;auto.
       Focus 2.
       apply inListLemma;auto.
       Focus 2. rewrite H6 in H15. inversion H15.
     
        assert (correct_configuration conf''). 
      destruct H2.
     repeat match goal with
            | [ H: _ /\ _ |- _ ] => destruct H

            end.
     rename H23 into ssp;rename H24 into sin. 
     apply termL5' with (conf:=conf) (e:=event1);auto.
     apply chainMergeInitial in H9.
     destruct H9.
     destruct H9.
     apply raised_wellform'0.
     apply chainMergeInitialEvent with (conf':=conf');auto.
     remember H15. clear Heqc. 
      destruct H15.
      rewrite    cs_consist.
      auto.
Qed.


Lemma preserveFinal : forall M (conf conf' : configuration M) re,
    chainMerge conf conf' re ->
    noMergeError' M ->
    noMultAlphabet M ->
    basicPreconditionMon M->
    alphabetRaisingObject M ->
    noDupRaise'' M ->
     finalConfig conf' ->
     finalConfig' conf'.
Proof.
  intros.
  unfold finalConfig in H5.
  unfold finalConfig'.
  destruct H5;auto.
  pose proof raisedEventsAlphabetChainMerge.
  unfold  alphabetRaisingObject in H3.
  remember H.
  clear Heqc.
  apply chainMergeInitialEvent in c.
  remember H.   
  clear Heqc0.
  apply chainMergeInitial in c0.   
  destruct c0.
  assert (correct_configuration conf').
  destruct H2.
  repeat match goal with
            | [ H: _ /\ _ |- _ ] => destruct H

            end. 
  apply termL5' with (conf:=conf) (e:=re);auto.   
  destruct H7.
  apply raised_wellform'0 ;auto.  remember ((raisedevents conf')). 
  destruct l.
  auto.
  assert (  forall sce : scenario,
       In sce (dom (controlstate conf)) ->
       In (eventDefinition r) (alphabet sce) -> ~ In sce (finishedscenarios conf')).
  apply H6 with (e:=re);auto.
  rewrite <- Heql;left;auto.     
  assert (exists sce : scenario, In sce (scenarios M) /\ In (eventDefinition r) (alphabet sce)).
  apply H3.
  destruct H9.
  apply raise_in;auto.
  rewrite <- Heql;left;auto.
  destruct H9.
  apply raisedType;auto.
  rewrite <- Heql;left;auto. 
  destruct H11.
  destruct H11.
  assert (~ In x (finishedscenarios conf')).
  apply H10;auto.   
  apply chainMergeInitial in H.
  destruct H.
  destruct H.
  rewrite cs_consist;auto.   
  unfold incl in H5.
  assert (In x (dom (controlstate conf'))).
  destruct H9.
  rewrite cs_consist;auto.
 apply H5 in H14.   contradiction. 
Qed.
      

Lemma progressConf: forall M (conf conf' : configuration M) re,
    chainMerge conf conf' re ->
    noMergeError' M ->
    noMultAlphabet M ->
    basicPreconditionMon M->
    alphabetRaisingObject M ->
    noDupRaise'' M ->
    ~ finalConfig' conf' ->
    (forall re', In re' (raisedevents conf') -> (exists conf'', synchrony conf' conf'' re')).
Proof.
  intros.
  assert (syncProgress' conf').
  apply preserveSync' with (conf:=conf) (re:=re);auto.
  SearchAbout syncProgress.
  assert (syncProgress conf').
  apply syncPro;auto.
  
  apply syncNoErr;auto.
  destruct H2.
  repeat match goal with
            | [ H: _ /\ _ |- _ ] => destruct H

            end.  
  apply termL5' with (conf:=conf) (e:=re);auto.   
  remember H.   clear Heqc.
  apply chainMergeInitial in H.
  apply chainMergeInitialEvent in c.
  destruct H;destruct H.
  apply raised_wellform'0;auto.
Qed. 
  

        

Definition UpperBound `(conf:configuration M): nat :=
List.length (dom (controlstate conf)) - List.length (finishedscenarios conf).


Definition UpperBound' `(conf:configuration M) (p: (finalConfig conf) + ~(finalConfig conf) ) : nat := 
match p with
| inl p' => O
| inr p' => List.length (dom (controlstate conf)) - List.length (finishedscenarios conf)
end. 


Local Close Scope Z_scope.
Local Close Scope N_scope.
Local Close Scope Q_scope.
Lemma decrease': forall a b c, a > 0 /\ b >=0 /\ c>=0 /\  a>=b /\ a>=c /\ c < b -> a-b < a-c.
Proof. intros.    

   repeat match goal with
            | [ H: _ /\ _ |- _ ] => destruct H

            end.
omega.
Qed.   

(*after each micro-step, the upperbound is reduced*)
Lemma decrease: forall M (conf conf' : configuration M) e, 
correct_configuration conf -> synchrony conf conf' e -> UpperBound conf' <   UpperBound conf.
Proof. intros.  remember H0. remember H0. remember H0. clear Heqs1.     clear Heqs. clear Heqs0.    apply termL4 in H0.   apply domControlSync in s.  
unfold   UpperBound.   rewrite s. apply decrease'.  split.   destruct H. 
destruct ( dom (controlstate conf)). unfold not in cs_non_empty. exfalso. apply cs_non_empty. auto.
rewrite <- s. simpl. auto. omega. 
split. omega. 
split. omega. 
split. Focus 2. split. Focus 2. auto. 
rewrite <- s.  

apply sceInclusion; destruct H; auto; auto. apply incluSync in s0.     apply sceInclusion.   
Focus 3. auto. Focus 3. destruct H. auto. apply uniqSync in s1; destruct s1; auto.
split;auto. split;auto.   
apply uniqSync in s1; destruct s1; auto.
apply uniqSync in s1; destruct s1; auto.
Qed.   

Lemma lengthNotEq: forall A l1 l2 (s1:A),
    uniqList l1 ->
    uniqList l2 ->
    In s1 l2 ->
    ~In s1 l1 ->
    incl l1 l2 ->
    Datatypes.length l1 <> Datatypes.length l2.
Proof.
  intros.
  pose proof Permutation.NoDup_Permutation_bis.
  unfold not. intros.
  assert (Permutation.Permutation l1 l2).
  apply H4. SearchAbout NoDup. rewrite <- uniqListNoDupEq;auto.
  rewrite <- uniqListNoDupEq;auto. rewrite H5;auto. auto.
  SearchAbout Permutation.Permutation.
  apply Permutation.Permutation_sym in H6. 
  apply  Permutation.Permutation_in with (x:=s1) in H6;auto.
Qed.

(*after each micro-step, the upperbound is reduced*)
Lemma decrease'': forall M (conf conf' : configuration M) e (p1: (finalConfig conf) + ~(finalConfig conf) )  (p2:(finalConfig conf') + ~(finalConfig conf')), 
correct_configuration conf -> synchrony conf conf' e -> @UpperBound' M conf'  p2 <   @UpperBound' M conf  p1.
Proof. intros. destruct p1. simpl.  
       unfold finalConfig in f.
       unfold synchrony in H0.  destruct H0.
       destruct f. destruct ((raisedevents conf)). inversion H0. inversion H2.
       unfold UpperBound'. 
       destruct p2.
               
       unfold combineFunc in H1.
       remember (constructConfigList (dom (controlstate conf)) e conf ).
       destruct e0;inversion H1.
       destruct v;inversion H4.
       unfold constructConfigList in Heqe0.
       
       clear H4. clear H5. clear H1.
       remember ( (filter
               (fun x : scenario =>
                inList event_definition_dec (eventDefinition e) (alphabet x))
               (filterList (finishedscenarios conf) (dom (controlstate conf)) scenario_dec))).
       destruct l.  simpl in Heqe0.   inversion Heqe0.
       remember ((filterList (finishedscenarios conf) (dom (controlstate conf)) scenario_dec)).
       destruct l0. simpl in Heql.  inversion Heql.
       unfold incl in H2.
       assert (In s0 (dom (controlstate conf)) /\ ~ In s0 (finishedscenarios conf)).
       split.
       assert (In s0 (s0::l0)). left;auto.
       rewrite Heql0 in H1. apply filterL2 in H1;auto.
        assert (In s0 (s0::l0)). left;auto.
        rewrite Heql0 in H1. apply filterL1 in H1;auto.
        destruct H1.
       apply H2 in H1. contradiction.    

        unfold combineFunc in H1.
       remember (constructConfigList (dom (controlstate conf)) e conf ).
       destruct e0;inversion H1.
       destruct v;inversion H4.
       unfold constructConfigList in Heqe0.
       
       clear H4. clear H5. clear H1.
       remember ( (filter
               (fun x : scenario =>
                inList event_definition_dec (eventDefinition e) (alphabet x))
               (filterList (finishedscenarios conf) (dom (controlstate conf)) scenario_dec))).
       destruct l.  simpl in Heqe0.   inversion Heqe0.
       remember ((filterList (finishedscenarios conf) (dom (controlstate conf)) scenario_dec)).
       destruct l0. simpl in Heql.  inversion Heql.
       unfold incl in H2.
       assert (In s0 (dom (controlstate conf)) /\ ~ In s0 (finishedscenarios conf)).
       split.
       assert (In s0 (s0::l0)). left;auto.
       rewrite Heql0 in H1. apply filterL2 in H1;auto.
        assert (In s0 (s0::l0)). left;auto.
        rewrite Heql0 in H1. apply filterL1 in H1;auto.
        destruct H1.
        apply H2 in H1. contradiction.
        
       simpl.
       unfold UpperBound'.  destruct p2.
       unfold finalConfig in n.
       destruct H.

        remember H0. clear Heqs. 
        unfold synchrony in H0.  destruct H0.
       (*destruct f. destruct ((raisedevents conf)). inversion H0. inversion H2.
       unfold UpperBound'. 
       destruct p2.*)
               
       unfold combineFunc in H0.
       remember (constructConfigList (dom (controlstate conf)) e conf ).
       destruct e0;inversion H0.
       destruct v;inversion H0. clear H0. clear H2. 
       unfold constructConfigList in Heqe0.
       remember ( (filter
               (fun x : scenario =>
                inList event_definition_dec (eventDefinition e) (alphabet x))
               (filterList (finishedscenarios conf) (dom (controlstate conf)) scenario_dec))).
       destruct l.  simpl in Heqe0.   inversion Heqe0.
       SearchAbout scenarioInclusion. 
       remember ((filterList (finishedscenarios conf) (dom (controlstate conf)) scenario_dec)).
       destruct l0. simpl in Heql.  inversion Heql.
      
       assert (In s1 (dom (controlstate conf)) /\ ~ In s1 (finishedscenarios conf)).
       split.
       assert (In s1 (s1::l0)). left;auto.
       rewrite Heql0 in H0. apply filterL2 in H0;auto.
        assert (In s1 (s1::l0)). left;auto.
        rewrite Heql0 in H0. apply filterL1 in H0;auto.
        destruct H0.
        SearchAbout scenarioInclusion.  
        assert (scenarioInclusion conf).
        apply inclusion.
        unfold scenarioInclusion in H2.
        SearchAbout incl. 
        assert (Datatypes.length (finishedscenarios conf) <= Datatypes.length  (dom (controlstate conf))).
        apply NoDup_incl_length.
        SearchAbout NoDup. rewrite <- uniqListNoDupEq.
        auto. auto. assert (Datatypes.length (finishedscenarios conf) <> Datatypes.length (dom (controlstate conf))).
        unfold not. intros.
        
        pose proof lengthNotEq.
        unfold not in H6. apply H6 with (A:=scenario) (l1:=(finishedscenarios conf)) (l2:=(dom (controlstate conf))) (s1:=s1);auto. omega. 
       pose proof decrease.
       apply H1 in H0;auto. 

Qed.



Lemma pred_increasing : forall n m,
      n <= m ->
      Nat.pred n <= Nat.pred m.
  Proof.
    induction n; cbn; intros.
    apply le_0_n.
    induction H; subst; cbn; eauto.
    destruct m; eauto.
  Qed.

  Hint Resolve le_S_n.

 Lemma strong_induction_all : forall (P: nat -> Prop) n,
      P 0 -> (forall m, (forall n, n < m -> P n) -> P m) -> (forall m, m <= n -> P m).
  Proof.
    induction n; intros.
    inversion H1. auto.
    inversion H1.
    apply H0.
    intros.  apply IHn. auto. intros.
    apply H0. 
    intros.     apply H4. 
    auto.     omega.
    apply IHn;auto.   
  Qed.
  
Lemma StrongInd1 :
  forall P: nat -> Prop,
    P 0 ->
    (forall n, (forall m, m < n -> P m) -> P (n)) ->
    (forall n, P n).
Proof. intros.
   
       pose proof strong_induction_all.
   apply H1 with (n:=n);auto.        
Qed.

      
    
    

  
Lemma Ind': forall P: nat -> Prop,
     P 0 ->
     (forall n, (forall m, m <= n -> P m) -> P (S n)) ->
    (forall n, (forall m, m < n -> P m) -> P (n)). 
Proof.
 induction n. 
 - intros. auto.
 - intros. apply H0.
   intros. apply H1. omega. 
Qed.

Lemma StrongInd :
  forall P: nat -> Prop,
    P 0 ->
    (forall n, (forall m, m <= n -> P m) -> P (S n)) ->
    (forall n, P n).
Proof. 
  intros.
  assert ( (forall n, (forall m, m < n -> P m) -> P (n))).
  apply Ind';auto.
  apply StrongInd1;auto. 
Qed.


Print initialConfig. 


    
Inductive Connected (M : monitor) : configuration M -> configuration M -> raisedEvent -> Prop :=
| ConnectedRefl: forall a e, Connected a a e
| ConnectedTrans: forall a1 a2 a3 e e', synchrony  a1 a2 e -> Connected a2 a3  e' -> Connected a1 a3 e.


Print synchrony. 




(*if upperbound is greater than 0 and no error, then it can step forward*)
(*Lemma NonZeroCanStep': forall conf e ,
correct_configuration conf  -> exists conf', synchrony conf conf' e.
Proof. intros. 
unfold generalErrConfig in H0.  
assert (~conflict e conf /\  (exists conf', combineFunc e conf = Result conf')).
split. unfold not. intros. unfold not in H0. apply H0. right. left. auto.
unfold not in H0.     
assert ((exists conf' : configuration M, Result conf' = combineFunc e conf) \/ ((exists s, Error s = combineFunc e conf))).
apply  combineConstruction. destruct H1. destruct H1. exists x. symmetry. auto. exfalso. apply H0. right. right.
destruct H1. exists x. symmetry. auto.            

destruct H1. destruct H2.   
assert (synchrony conf x e). unfold synchrony . split.      
    destruct H.    auto. split. Focus 2. split. auto. auto.
unfold not.  intros. unfold not in H0. apply H0. left. auto.
exists x. auto. 
Qed.*)

(*aux lemma, if two unique list l1 and l2 have the same length and l1 is included in l2, then l2 is included in l1*)
Lemma revIncl: forall (A: Type) (l1 l2:list A),
incl l1 l2 -> uniqList (l1) -> uniqList (l2) -> List.length l1 = List.length l2
-> incl l2 l1.
Proof. intros.
assert (forall (A:Type)  (l:list A), NoDup l <-> uniqList l).
intros. split.
intros. induction l.  inversion H3. Print  uniqList. apply uniqL_nilL.
     Print  uniqList. apply uniqL_push. apply IHl. inversion H3.
auto. inversion H3. auto. intros.
induction l. apply NoDup_nil. apply NoDup_cons.
inversion H3. auto. apply IHl. inversion H3. auto.           
apply NoDup_length_incl.
Focus 2. omega. Focus 2. auto.
destruct H3 with (A:=A) (l:=l1). apply H5. auto.
Qed.


Print finalConfig. 
Print incl.

Check scenarioIn. 


Fixpoint scenarioIncl (l1: list scenario) (l2: list scenario) : bool :=
  match l1 with
  | nil => true
  | sce::l1' => if inList (scenario_dec) sce l2 then
                  scenarioIncl l1' l2
                else
                  false
  end.

Lemma scenarioInc_cor: forall l1 l2,
    scenarioIncl l1 l2 = true <-> incl l1 l2. 
Proof.
  intro l1;induction l1.
  - intros. split;intros. unfold incl;intros. inversion H0.
    simpl;auto.
  - split;intros.
    simpl in *.
    remember (inList scenario_dec a l2).
    destruct b. symmetry in Heqb.
    SearchAbout inList.
    apply reverseinListLemma in Heqb.
    apply IHl1 in H.
    unfold incl;intros. destruct H0;subst. auto.
    unfold incl in H. apply H;auto. 
    inversion H.     
    unfold incl in H.
 
    simpl. 
      remember (inList scenario_dec a l2).
      destruct b. symmetry in Heqb.
      apply reverseinListLemma in Heqb.
      apply IHl1.     unfold incl;intros.  apply H.  right;auto.
      symmetry in Heqb.
      SearchAbout inList. apply reverseinListFalse in Heqb.
      assert (In a l2). apply H;left;auto. contradiction. 
Qed.


Definition checkFinal M (conf: configuration M) : bool :=
  if beq_nat (List.length (raisedevents conf)) O then true
  else
     scenarioIncl (dom (controlstate conf)) (finishedscenarios conf)
 . 

Local Close Scope N. 
 Lemma checkFinal_correct: forall M (conf: configuration M),
     checkFinal conf = true <-> finalConfig conf. 
 Proof.
   intros. split.
 - intros. 
   unfold finalConfig.
   unfold checkFinal in H.
   remember (List.length (raisedevents conf)). 
   destruct n. left;auto.
   simpl in *. 
   right.
   apply scenarioInc_cor;auto.
 - intros.
   unfold finalConfig in H.
   destruct H.
   unfold checkFinal.
   rewrite H. simpl;auto.
   rewrite <- scenarioInc_cor in H.
   unfold  checkFinal.
   destruct (List.length (raisedevents conf) =? 0);auto. 
   
Qed.    
   

Lemma finalConfig_dec: forall M (conf' : configuration M), {finalConfig conf'} + {~ finalConfig conf'}.
Proof.
  intros.
  remember (checkFinal conf').
  destruct b.
  symmetry in Heqb. apply  checkFinal_correct in Heqb. left;auto.
  symmetry in Heqb. right. unfold not;intros.
  apply checkFinal_correct in H. rewrite H in Heqb. inversion Heqb. 
(*  unfold finalConfig.
  
  assert ({Datatypes.length (raisedevents conf') = 0} + {Datatypes.length (raisedevents conf') <> 0}).
  destruct ((raisedevents conf')). simpl. left;auto.
  right. unfold not. intros. inversion H. 
 
  inversion H.
  left. left;auto.
  assert ({ incl (dom (controlstate conf')) (finishedscenarios conf')} + {~incl (dom (controlstate conf')) (finishedscenarios conf')}).
  SearchAbout incl.
  Locate  ListDec.incl_dec.
 
  apply ListDec.incl_dec.
  SearchAbout scenario. apply scenario_dec.
  destruct H1. left. right;auto.
  right. unfold not;intros.
  destruct H1. contradiction. contradiction. *)
Defined.

Print Assumptions ListDec.incl_dec. 

(*if all state machines finishes execution, configuration is stuck
Lemma conditionNotStep: forall conf, 
 correct_configuration conf 
-> Datatypes.length (dom (controlstate conf)) - Datatypes.length (finishedscenarios conf) = 0 
-> finalConfig conf.  
Proof.  
Admitted.                     
 *)

(*when upperbound is zero, it is stuck*)
Lemma ZeroIsFinal: forall M (conf : configuration M) (p: (finalConfig conf) + ~(finalConfig conf) ),  
 correct_configuration conf -> @UpperBound' M conf p = O -> finalConfig conf.
Proof. 
intros.
destruct p.  auto. unfold finalConfig.
simpl in H0. destruct H.
unfold scenarioInclusion in inclusion.

right.


assert (Datatypes.length (dom (controlstate conf)) >= Datatypes.length (finishedscenarios conf)).
SearchAbout (finishedscenarios).
apply sceInclusion;auto.
assert (Datatypes.length (dom (controlstate conf)) =  Datatypes.length (finishedscenarios conf)). omega.
apply revIncl;auto. 

Qed. 



Lemma TerminatesOnConnected': forall M (a : configuration M) e,
((exists a' e', chainMerge a' a e') \/ (initialConfig a))
-> In e (raisedevents a)
-> noMergeError' M ->
syncProgress a ->
noMultAlphabet M ->
basicPreconditionMon M->
alphabetRaisingObject M ->
noDupRaise'' M -> 
exists a',  Connected a a' e /\  (finalConfig a').
Proof.
intros. rename H5 into alpha. rename H6 into nodup.  
pose proof finalConfig_dec a.
destruct H5. exists a. split. apply ConnectedRefl.  auto.    
remember (@UpperBound' M a (inr n)) as mes. 
 revert dependent a. generalize dependent e. 
 induction mes using StrongInd; intros.
 assert (correct_configuration a).
 destruct H. Focus 2. destruct H;auto.
 destruct H. destruct H.
 destruct H4.
 repeat match goal with
            | [ H: _ /\ _ |- _ ] => destruct H

          end.
 rename H13 into ssp;rename H14 into sin.  apply termL5' with (conf:=x) (e:=x0);auto.
 
 remember H. clear Heqc. apply chainMergeInitial in c. destruct c.
   repeat match goal with
            | [ H: _ /\ _ |- _ ] => destruct H

          end.
   destruct H13.
   apply    raised_wellform'0. apply chainMergeInitialEvent in H;auto.
  
- eauto using ConnectedRefl, ZeroIsFinal.
  
  - pose proof syncNoErr.
    assert (correct_configuration a).

    destruct H0. Focus 2. destruct H0;auto.
 destruct H0. destruct H0.

 
(* Admitted. jww (2018-01-06): Teng, can you please complete this proof again, if it is
   needed?*)
 destruct H4.
 repeat match goal with
            | [ H: _ /\ _ |- _ ] => destruct H

        end.
rename H15 into ssp;rename H16 into sin.  
 apply termL5' with (conf:=x) (e:=x0);auto.
 
 remember H0. clear Heqc. apply chainMergeInitial in c. destruct c.
   repeat match goal with
            | [ H: _ /\ _ |- _ ] => destruct H

          end.
   destruct H15.
   apply    raised_wellform'0. apply chainMergeInitialEvent in H0;auto.
  (* rewrite  monitorObjNoChangeChain with (conf':=a) (e:=x0);auto. 
   rewrite  monitorObjNoChangeChain with (conf':=a) (e:=x0);auto.
   rewrite  monitorObjNoChangeChain with (conf':=a) (e:=x0);auto.*)
    
assert (exists conf', synchrony a conf' e).
apply H6;auto. 
  destruct H8.
pose proof finalConfig_dec x.
destruct H9. exists x. split. apply ConnectedTrans with (a2:=x) (e':=e). auto. apply ConnectedRefl.
 auto. remember H8. clear Heqs. apply decrease'' with (p1:=inr n) (p2:=inr n0)  in H8;auto. 
remember (UpperBound' (inr n0)). 
rewrite <-  Heqmes in H8. assert (n1<=mes). omega.  
assert (~(raisedevents x = nil)). unfold not. intros. unfold not in n0. apply  n0.
unfold finalConfig. left. rewrite H10;auto.
assert (Datatypes.length (raisedevents x) <> 0).
unfold not. intros. apply n0. unfold finalConfig. left;auto. 


assert (exists e', In e' (raisedevents x)). destruct (raisedevents x).
contradiction. exists r;auto. left;auto. destruct H12.

apply H with (e:=x0) (a:=x) (n:=n0) in H9;auto.
destruct H9. destruct H9.
exists x1. split;auto. 
apply ConnectedTrans with (a2:=x) (e':=x0);auto.
destruct H0. destruct H0.
destruct H0. left. 
exists x1. exists x2.  apply chain' with (conf':=a) (event2:=e);auto. 
left. exists a. exists e.  apply basic';auto.


(*apply monitorObjNoChangeSync in s. rewrite <- s;auto.
destruct H5.
        repeat match goal with
            | [ H: _ /\ _ |- _ ] => destruct H

               end.
        
        apply termL5 with (conf:=a) (e:=e);auto.
 destruct H0.   apply raised_wellform'0 . unfold synchrony in s. destruct s;auto. 
*)
 pose proof preserveSync.
 destruct H0. destruct H0.
destruct H0.  
 apply H13 with (conf:=x1) (re:=x2);auto. apply chain' with (conf':=a) (event2:=e);auto. 
 
apply H13 with (conf:=a) (conf':=x) (re:=e);auto. apply basic';auto.
  
Qed.









Inductive ConnectedBack (M : monitor) : configuration M -> configuration M -> raisedEvent -> Prop :=
| ConnectedBackRefl: forall a e, ConnectedBack a a e
| ConnectedBackTrans: forall a1 a2 a3 e1 e2, ConnectedBack a1 a2 e1 -> synchrony a2 a3 e2-> ConnectedBack a1 a3 e1.


Fixpoint Connected_RevApp {M : monitor} {a1 a2 a3: configuration M} {e e':raisedEvent} (pr: Connected a2 a3 e') (acc: ConnectedBack a1 a2 e) : ConnectedBack a1 a3 e.
  destruct pr.
  - assumption.
  - eapply Connected_RevApp.
    + eassumption.
    + eauto using ConnectedBackTrans.
Defined.

Lemma Connected_ConnectedBack :
  forall M (a1 a2 : configuration M) e, Connected a1 a2 e -> ConnectedBack a1 a2 e.
Proof.
  eauto using Connected_RevApp, ConnectedBackRefl.
Qed.

Lemma TerminatesBack': forall M (a : configuration M) e, 
((exists a' e', chainMerge a' a e') \/ (initialConfig a)) ->
 In e (raisedevents a) ->
noMergeError' M ->
syncProgress a ->
noMultAlphabet M ->
basicPreconditionMon M->
alphabetRaisingObject M ->
noDupRaise'' M -> 
exists a',  ConnectedBack a a' e /\  (finalConfig a').
Proof.
intros. pose proof Connected_ConnectedBack.
pose proof TerminatesOnConnected'. 
destruct H8 with (a:=a) (e:=e);auto.
destruct H9.
apply H7 in H9. exists x. split;auto. 
Qed.


 

(*initial configuration has one pending event*)
Lemma initialConfigOneRaisedEvent: forall re M (conf : configuration M) re',
initialConfig conf -> In re (raisedevents conf) -> In re' (raisedevents conf) -> re = re'.
Proof. intros. unfold initialConfig in H.    
repeat match goal with
            | [ H: _ /\ _ |- _ ] => destruct H

            end.
induction (raisedevents conf).  inversion H0. destruct l. destruct H0. destruct H1. rewrite <-  H0. auto.
inversion H1. inversion H0. inversion H2.
Qed.           

Lemma syncEvent: forall M (conf conf' : configuration M) re, synchrony conf conf' re -> In re (raisedevents conf). 
Proof.
intros. unfold synchrony in H. 
repeat match goal with
            | [ H: _ /\ _ |- _ ] => destruct H

            end.
auto.
Qed.    


(*relation between ConnectedBack and chainMerge*)
 Lemma ConnectedBack_SmedlConnected :
  forall M (a1 a2 : configuration M) e, initialConfig a1 
-> In e (raisedevents a1)
-> ConnectedBack a1 a2 e -> (a1 = a2 \/ chainMerge a1 a2 e).
Proof.
induction 3.
  - left. auto.  
  - remember H. clear Heqi.    apply IHConnectedBack in H. destruct H. Focus 2. right. eapply chain'. apply H. apply H2.
assert (In e2 (raisedevents a2)). apply syncEvent with a3. 
auto. assert (e1=e2). apply initialConfigOneRaisedEvent with M a1. auto. auto. rewrite <- H in H3. auto.  rewrite <- H4 in H2. 
right. apply basic'. auto. rewrite <- H in H2;auto.
auto. 
Qed.

(*relation between ConnectedBack and chainMerge*)
 Lemma Connected_chainmerge :
  forall M (a1 a2 : configuration M) e, initialConfig a1 
-> In e (raisedevents a1)
-> Connected a1 a2 e -> (a1 = a2 \/ chainMerge a1 a2 e).
Proof. pose proof ConnectedBack_SmedlConnected. pose proof Connected_ConnectedBack.
       intros.
apply H;auto.        
Qed.

(*if an initial configuration cannot raise error, it is not stuck*)
Lemma InitialNotStuckNorError: forall M (a : configuration M), initialConfig a  ->  (~ finalConfig a).
Proof.
  intros. unfold not. intros.
  unfold finalConfig in H0. destruct H.
   repeat match goal with
            | [ H: _ /\ _ |- _ ] => destruct H

         end.
  destruct H0.
  
  rewrite H0 in H1. inversion H1.
  rewrite H3 in H0.
  unfold incl in H0.
  destruct H.
  destruct ( dom (controlstate a)). contradiction.
  destruct H0 with s;auto. left;auto. 
 
Qed. 


(*termination theorem*)



Theorem Terminates: forall M (conf : configuration M) e (p:finalConfig conf + ~ finalConfig conf),
    initialConfig conf->
    In e (raisedevents conf) ->
noMergeError' M ->
syncProgress conf ->
noMultAlphabet M ->
basicPreconditionMon M->
alphabetRaisingObject M ->
noDupRaise'' M -> 
  (exists conf', chainMerge conf conf' e  /\ (finalConfig conf')).
Proof.
intros. rename H5 into alpha. rename H6 into nodup. pose proof  TerminatesBack'. remember H. clear Heqi.  unfold initialConfig in H.  destruct H. destruct H6.
remember H0. clear Heqi0.   
apply H7 in H0. apply H5 with (e:=e) in H2;auto. 
destruct H2.           
exists x. destruct H2. split;auto. 
 
apply ConnectedBack_SmedlConnected in H2;auto.
destruct H2. rewrite <- H2 in H8. 
apply InitialNotStuckNorError in i. contradiction. auto. 
Qed.


Theorem TerminatesFinal: forall M (conf : configuration M) e (p:finalConfig conf + ~ finalConfig conf),
    initialConfig conf->
    In e (raisedevents conf) ->
noMergeError' M ->
syncProgress conf ->
noMultAlphabet M ->
basicPreconditionMon M->
alphabetRaisingObject M ->
noDupRaise'' M -> 
(exists conf', chainMerge conf conf' e  /\ (finalConfig' conf')).
Proof.
  intros.
  assert  (exists conf', chainMerge conf conf' e  /\ (finalConfig conf')).
  apply Terminates;auto.
  destruct H7.
  destruct H7.
  exists x.
  split;auto.
  apply preserveFinal with (conf:=conf) (re:=e);auto.
  
Qed.

(*
Lemma chainMergeProgress: forall conf re,
    initialConfig conf ->
    In re (raisedevents conf) ->
    noMergeError M ->
    noMultAlphabet M ->
    basicPreconditionMon M ->
    alphabetRaisingObject M ->
    noDupRaise M ->
    alphabetRaisingObject M ->
    (exists conf', chainMerge conf conf' re /\ (finalConfig conf')).
Proof.
  intros. pose proof syncNoErr.
  assert ( exists conf' : configuration M, synchrony conf conf' re).
  apply H7;auto.   destruct H;auto.
  SearchAbout syncProgress.
  apply initialImplyProgress;auto.
  destruct H8.
  
  exists x. apply basic';auto. 
Admitted.
 *)

Inductive chainMergeRanking (M : monitor): nat -> configuration M -> configuration M -> raisedEvent -> Prop :=
| rank_basic: forall conf conf' re, initialConfig conf -> synchrony conf conf' re -> chainMergeRanking (S O) conf conf' re
| rank_inductive: forall conf conf' conf'' re n re', chainMergeRanking n conf conf' re -> synchrony conf' conf'' re' ->  chainMergeRanking (S n) conf conf'' re.

Lemma chainMergeRankingFinite : forall M (conf conf' : configuration M) re,
    chainMerge conf conf' re ->
    (exists n, chainMergeRanking n conf conf' re). 
Proof.   
  intros.
  induction H.
  exists (S O).
  apply rank_basic;auto.
  destruct IHchainMerge.
  exists (S x).
  apply rank_inductive with (conf':=conf') (re':=event2);auto.
Qed.


Lemma rankLimited: forall M (conf conf' : configuration M) re n,
    chainMergeRanking n conf conf' re ->
    n <= (List.length (finishedscenarios conf')).
Proof.
  intros. induction H.
  SearchAbout finishedscenarios.
  pose proof termL4.
  remember H0. clear Heqs. apply H1 in s.
  destruct H0. destruct H.
  repeat match goal with
            | [ H: _ /\ _ |- _ ] => destruct H

         end.
  rewrite H5 in s.   simpl in s. omega. 

   pose proof termL4.
  remember H0. clear Heqs. apply H1 in s.
  omega.
Qed.   

Lemma rankBounded: forall M (conf conf' : configuration M) re,
    basicPreconditionMon M ->
    chainMerge  conf conf' re ->
    (List.length (finishedscenarios conf')) <= (List.length (dom (controlstate conf))).
Proof.
  intros.
  assert (correct_configuration conf').
  destruct H.
  repeat match goal with
            | [ H: _ /\ _ |- _ ] => destruct H

         end.
  rename H9 into ssp;rename H10 into sin.   
  apply termL5' with (conf:=conf) (e:=re);auto.
  remember H0. clear Heqc. apply chainMergeInitial in c.
  destruct c. destruct H9. apply raised_wellform'0.
  apply chainMergeInitialEvent in H0;auto. 
  assert ( Datatypes.length (dom (controlstate conf')) >=
       Datatypes.length (finishedscenarios conf')
         ).
  apply sceInclusion.
  destruct H1;auto.   destruct H1;auto. destruct H1;auto.
  destruct H1.
  remember H0. clear Heqc. 
  apply chainMergeInitial in H0. destruct H0. destruct H0.
  rewrite cs_consist0.
  rewrite <- cs_consist.   omega.
Qed.

Lemma chainMergeRankingFiniteRev : forall M (conf conf' : configuration M) n re,
    chainMergeRanking n conf conf' re ->
    chainMerge conf conf' re. 
Proof.   
  intros.
  induction H. apply basic';auto.
  apply chain' with (conf':=conf') (event2:=re');auto.
  
Qed.


Lemma rankLimited': forall M (conf conf' : configuration M) re n,
    basicPreconditionMon M ->
    chainMergeRanking n conf conf' re ->
    n <= (List.length (dom (controlstate conf))).
Proof.
  intros. 
  pose proof rankLimited.
  assert (n <= Datatypes.length (finishedscenarios conf')).
  apply H1 with (conf:=conf) (re:=re);auto.
  pose proof rankBounded.
  assert (Datatypes.length (finishedscenarios conf') <=
          Datatypes.length (dom (controlstate conf))).
  apply H3 with (re:=re);auto.
  apply chainMergeRankingFiniteRev in H0. auto. 
  omega. 
  
Qed.

Lemma alwaysTerminate: forall M (conf conf': configuration M) e (p:finalConfig conf + ~ finalConfig conf),
    initialConfig conf->
    In e (raisedevents conf) ->
noMergeError' M ->
syncProgress conf ->
noMultAlphabet M ->
basicPreconditionMon M->
alphabetRaisingObject M ->
noDupRaise'' M ->
chainMerge conf conf' e  ->
(~ exists conf'' e', synchrony conf' conf'' e') ->
finalConfig' conf'. 
Proof.
  intros.
  assert (finalConfig' conf' \/ ~ finalConfig' conf').
  apply excluded_middle.
  destruct H9;auto.
  pose proof progressConf.
  assert ( forall re' : raisedEvent,
        In re' (raisedevents conf') ->
        exists conf'' : configuration M, synchrony conf' conf'' re').
  apply H10 with (conf:=conf) (re:=e);auto.
  exfalso;apply H8.
  assert ((raisedevents conf')  <> nil).
  unfold not in H9.
  unfold not;intros.   
  apply H9.
  unfold   finalConfig'.
  rewrite H12;auto.
  destruct (raisedevents conf').
  contradiction.
  assert (exists conf'' : configuration M, synchrony conf' conf'' r).
  apply H11;left;auto.
  destruct H13.
  exists x;exists r;auto.
Qed.

Lemma initialImplyProgress: forall M (conf : configuration M),
    initialConfig conf -> syncProgress conf.
Proof.
  intros.
  destruct H.
  unfold syncProgress.
  intros.
  destruct H0.
  destruct ((raisedevents conf)).
  inversion H0.
  destruct l. Focus 2. inversion H0.
  destruct H2.
  destruct H3.
  apply H2 in H1.
  destruct H1.
  destruct H5.
  rewrite H3.
  unfold not. intros.
  destruct H5.

  remember ((filterList nil (dom (controlstate conf)) scenario_dec)).
  assert (In x l).
  rewrite <- filterListNil in Heql. rewrite Heql;auto.
  assert (In x l /\ (fun x0 : scenario => inList event_definition_dec (eventDefinition re) (alphabet x0)) x = true).
  split;auto.
  apply inListLemma;auto.
  rewrite <- filter_In in H9. rewrite H6 in H9. inversion  H9.
Defined.

Lemma alwaysTerminateN: forall M (conf conf': configuration M) e n (p:finalConfig conf + ~ finalConfig conf),
noMergeError' M ->
noMultAlphabet M ->
basicPreconditionMon M->
alphabetRaisingObject M ->
noDupRaise'' M ->
chainMergeRanking n conf conf' e  ->
(~ exists conf'' e', synchrony conf' conf'' e') ->
finalConfig' conf' /\  n <= (List.length (dom (controlstate conf))). 
Proof.
  intros.
  
 
  assert (chainMerge conf conf' e).
  apply chainMergeRankingFiniteRev with (n:=n);auto.
  assert (initialConfig conf).
  apply chainMergeInitial in H6;auto.
  assert (syncProgress conf).
  apply initialImplyProgress;auto.
  assert (In e (raisedevents conf)).
  apply chainMergeInitialEvent in H6;auto.   
  assert (finalConfig' conf').
  apply alwaysTerminate with (conf:=conf) (e:=e);auto. 
  split;auto.
  apply rankLimited' with (conf':=conf') (re:=e);auto.
  
Qed.

Check termL4. 
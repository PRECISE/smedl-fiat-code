
Require Import Coq.Sets.Ensembles.
Require Import  Coq.omega.Omega.
Require Import Coq.Lists.List.


Require Coq.Bool.Bool.
Require Coq.Lists.ListDec.

Require Import Coq.Strings.String.

Require Export SmedlAST_submission.
Require Export semantic_rules.


Local Close Scope Z_scope.
Local Close Scope N_scope.
Local Close Scope Q_scope.
(*aux lemma for proving termination*)
Lemma termL40': forall l1 l2, List.length (l1) <=
List.length (mergeList' (l1) (l2) scenario_dec).
Proof. intros.  generalize dependent l2.   induction l1.
intros.  simpl. omega.
intros. simpl.  
assert (forall (A:Type) (l l1: list A), Datatypes.length (l1) <= Datatypes.length ((l1) ++ l)).
intros. induction l0. simpl. omega. simpl. omega. destruct H with (A:=scenario) (l1:=l1) (l:=filterList (a :: l1) l2 scenario_dec).
 omega. omega. 
Qed.


(*aux lemma for proving termination*)
Lemma termL41': forall M (conf conf' : configuration M) v, innerCombineFunc'''' conf v = Some conf'
-> (Datatypes.length (finishedscenarios conf) <= Datatypes.length (finishedscenarios conf')).
Proof. intros. generalize dependent conf. generalize dependent conf'.     induction v.
intros.  simpl in H. inversion H.  
intros. 
simpl in H.
destruct v.

remember (mergeConfigFunc' conf conf a ).

destruct e;inversion H;subst.
unfold mergeConfigFunc' in Heqe. 
destruct (mergeDataStateFunc (datastate conf) (datastate conf) (datastate a)).
destruct (mergeControlStateFunc (controlstate conf) (controlstate conf) (controlstate a)).
inversion Heqe. simpl. 
 rewrite app_length. omega. 
 inversion Heqe. inversion Heqe.
 remember (innerCombineFunc'''' conf (c :: v)).
 destruct o;inversion H.
 symmetry in Heqo. apply IHv in Heqo.
 
 remember (mergeConfigFunc' conf a c0).
 destruct e;inversion H.
 subst.  
unfold mergeConfigFunc' in Heqe. 
destruct (mergeDataStateFunc (datastate conf) (datastate a) (datastate c0)).
destruct (mergeControlStateFunc (controlstate conf) (controlstate a) (controlstate c0)).
inversion Heqe. 
simpl.  clear H2. 
rewrite app_length. omega.
inversion Heqe.
inversion Heqe.
 
                                                                        
(*remember (innerCombineFunc'''' conf v).
destruct o;inversion H.  unfold mergeConfigFunc' in H1. 
destruct (mergeDataStateFunc (datastate conf) (datastate c) (datastate a)).
destruct (mergeControlStateFunc (controlstate conf) (controlstate c) (controlstate a)).
inversion H1. simpl. assert (Datatypes.length (finishedscenarios conf) <=
                             Datatypes.length (finishedscenarios c)).
apply IHv;auto. rewrite app_length. omega. inversion H1. inversion H1.
unfold mergeConfigFunc' in H1. 
destruct (mergeDataStateFunc (datastate conf) (datastate conf) (datastate a)).
destruct (mergeControlStateFunc (controlstate conf) (controlstate conf) (controlstate a)).
inversion H1. simpl. rewrite app_length. omega. inversion H1. inversion H1. *)

Qed.

Lemma termL2: forall M (conf : configuration M) e lst scs conf', constructConfigList' scs e conf = Result lst /\
 In conf' lst -> exists sce, In sce scs /\  Result conf' = constructConfig sce e conf.
Proof.
intros. destruct H.  generalize dependent lst. induction scs.
- intros. simpl in H. induction lst. inversion H0. inversion H.
- intros. induction lst. simpl in H. inversion H0. simpl in H.
 
  simpl in H0. destruct H0. remember (constructConfig a e conf ). destruct e0.
  destruct (constructConfigList' scs e). inversion H;subst. exists a. split. simpl;left. auto. apply Heqe0. inversion H. 
inversion H. inversion H.  simpl. destruct  (constructConfig a e conf ).

 remember (constructConfigList' scs e conf).
destruct e0. inversion H.  subst. destruct IHscs with lst;auto.   exists x. 
destruct H1. split. right;auto. auto. inversion H. inversion H. 
Qed.

Lemma termL3: forall M (conf conf' : configuration M) e sce,
    Result conf' = constructConfig sce e conf  ->
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
                end) (events M))).
destruct v0. inversion H;subst. simpl;auto. 

repeat(inversion H). inversion H. inversion H. inversion H. inversion H. inversion H. 
Qed.

Lemma termL23:  forall M (conf conf' : configuration M) e lst scs,
    constructConfigList scs e conf = Result lst /\
    In conf' lst -> exists sce, In sce scs /\ (finishedscenarios conf' = sce::nil).
Proof. intros.   apply termL2 in H. destruct H. exists x. destruct H.   split.  Focus 2. 

       apply termL3 with (e:=e) (conf:=conf);auto.
 apply filter_In in H.    destruct H.    
 apply filterL2 in H.  auto.  
Qed.

(*Lemma 1*)
Lemma termL4: forall M (conf conf' : configuration M) e, synchrony conf conf' e ->
List.length (finishedscenarios conf) < List.length (finishedscenarios conf').
Proof. 
intros.  
repeat match goal with
            | [|- forall _,_]  => progress intros
            | [ |-  _  /\  _  ] =>  split
            | [ H: synchrony _ _ _ |- _ ] => unfold synchrony in H

            | [ H: _ /\ _ |- _ ] => destruct H
            | _ => unfold equivConf
end.    
unfold combineFunc in H0.  
remember (constructConfigList (dom (controlstate conf)) e conf).
destruct e0;inversion H0.    destruct v;inversion H0. clear H2.
clear H0.
destruct v.

remember (mergeConfigFunc' conf conf c).
destruct e0;inversion H3.
unfold removeEventFromConf. simpl.
unfold mergeConfigFunc' in Heqe1. 
destruct (mergeDataStateFunc (datastate conf) (datastate conf) (datastate c) ).
destruct (mergeControlStateFunc (controlstate conf) (controlstate conf)
                                (controlstate c)).
inversion Heqe1. simpl.
rewrite app_length.
pose proof termL23.
assert (exists sce : scenario, In sce (dom (controlstate conf)) /\ finishedscenarios c = sce :: nil).
eapply H0;auto. split. symmetry. apply Heqe0. left;auto.
destruct H4. destruct H4. rewrite H5;simpl. 
omega.   
inversion Heqe1. inversion Heqe1. 
remember (innerCombineFunc'''' conf (c0 :: v)).
destruct o;inversion H3.

remember (mergeConfigFunc' conf c c1).
destruct e0;inversion H1.
unfold removeEventFromConf. simpl.
unfold mergeConfigFunc' in Heqe1.
destruct (mergeDataStateFunc (datastate conf) (datastate c) (datastate c1));inversion Heqe1. clear H4.
destruct ( mergeControlStateFunc (controlstate conf) (controlstate c) (controlstate c1));inversion Heqe1. simpl.  rewrite app_length.
assert (Datatypes.length (finishedscenarios conf) <=
        Datatypes.length (finishedscenarios c1)).
pose proof  termL41'.
apply H0 with (v:=(c0::v));auto. 
pose proof termL23.
assert (exists sce : scenario, In sce (dom (controlstate conf)) /\ finishedscenarios c = sce :: nil).
eapply H5;auto. split. symmetry. apply Heqe0. left;auto.
destruct H6. destruct H6. rewrite H7.
simpl. omega.
(*remember (innerCombineFunc'''' conf v).
destruct o;inversion H3.
remember (mergeConfigFunc' conf c0 c).
destruct e0;inversion H1.
unfold removeEventFromConf. simpl.
unfold mergeConfigFunc' in Heqe1.
destruct (mergeDataStateFunc (datastate conf) (datastate c0) (datastate c));inversion Heqe1. clear H4.
destruct ( mergeControlStateFunc (controlstate conf) (controlstate c0) (controlstate c));inversion Heqe1. simpl.  rewrite app_length.
assert (Datatypes.length (finishedscenarios conf) <=
        Datatypes.length (finishedscenarios c0)).
pose proof  termL41'.
apply H0 with (v:=v);auto. 
pose proof termL23.
assert (exists sce : scenario, In sce (dom (controlstate conf)) /\ finishedscenarios c = sce :: nil).
eapply H5;auto. split. symmetry. apply Heqe0. left;auto.
destruct H6. destruct H6. rewrite H7.
simpl. omega.

remember (mergeConfigFunc' conf conf c).
destruct e0;inversion H1.
unfold removeEventFromConf. simpl.
unfold mergeConfigFunc' in Heqe1. 
destruct (mergeDataStateFunc (datastate conf) (datastate conf) (datastate c) ).
destruct (mergeControlStateFunc (controlstate conf) (controlstate conf)
                                (controlstate c)).
inversion Heqe1. simpl.
rewrite app_length.
pose proof termL23.
assert (exists sce : scenario, In sce (dom (controlstate conf)) /\ finishedscenarios c = sce :: nil).
eapply H0;auto. split. symmetry. apply Heqe0. left;auto.
destruct H5. destruct H5. rewrite H6;simpl. 
omega.   
inversion Heqe1. inversion Heqe1. *)
Qed.

(*aux lemma for proving termination*)
Lemma sceInclusion: forall M (conf : configuration M), uniqList (dom (controlstate conf)) -> uniqList  (finishedscenarios conf)
-> scenarioInclusion conf-> 
 List.length (dom (controlstate conf)) >= List.length ( (finishedscenarios conf)).
Proof. intros.  apply listInclusion. split. auto. split. auto. unfold scenarioInclusion in H1.  auto.
Qed.

Lemma LL1': forall M (conf conf' : configuration M) sce re,
    constructConfig sce re conf = Result (conf') ->
    dom (controlstate conf) = (dom (controlstate conf'))
      /\  (finishedscenarios conf' = sce::nil).
Proof. intros.
split.  Focus 2.    apply termL3 with (e:=re) (conf:=conf). symmetry. auto.
unfold constructConfig in H.
destruct (getScenarioState sce (controlstate conf)).
destruct (transEvMapFunc (stateEvDefInstanceMap M) (Some s, Some (eventDefinition re))). 
destruct (findEventInstance re (datastate conf) l).
destruct (createValueEnv (eventArgs e) (eventParams (eventDefinition re)) (eventArguments re)).
destruct (getStep' conf sce e ).
 unfold configTransition in H.  
destruct (execAction (extendValEnv (datastate conf) v, nil) (stepActions s0)
            (filter
               (fun e : event_definition =>
                match eventKind e with
                | Internal => true
                | Imported => false
                | Exported => true
                end) (events M))).
destruct v0. inversion H;simpl. 
unfold updateControlState. 
assert (forall s1, dom s1 = dom (updateScenarioState' sce (pro_state s0) s1)).
intros. induction s1. simpl.

simpl. auto.
  destruct a. simpl. 
destruct ( string_dec (scenarioId s2) (scenarioId sce)). simpl.  f_equal. auto. simpl. f_equal. auto.
apply H0. 
inversion H. inversion H. inversion H. inversion H. inversion H.  inversion H. 
Qed. 


Lemma domControlSyncL1: forall M (conf conf' : configuration M) e sce,
    In sce (dom (controlstate conf))
      -> correct_configuration conf
      -> Result conf' = constructConfig sce e conf
      -> (dom (controlstate conf)) = (dom (controlstate conf')).
Proof. intros. 
SearchAbout constructConfig.
symmetry in H1. apply LL1' in H1. destruct H1.
auto.
Qed.

Lemma mergeControlInvariant: forall cso cs1 cs2 cs3, (dom cso = dom cs1) -> (dom cs1 = dom cs2) 
-> (Result cs3 = mergeControlStateFunc cso cs1 cs2)-> (dom cso) = (dom cs3).
Proof. intros. generalize dependent cso. generalize dependent cs1. generalize dependent cs2. 
induction (cs3). intros. 

destruct (cso). auto. destruct cs1.  inversion H. destruct cs2. inversion H0. simpl in H1.
destruct p;destruct p0;destruct p1.    destruct (scenario_dec s s1).  destruct (scenario_dec s s3).  subst. 
destruct (mergeControlStateFunc l cs1 cs2). subst.
destruct (string_dec s2 s4). inversion H1.
destruct (string_dec s2 s0). inversion H1.
destruct (string_dec s4 s0). inversion  H1. 
inversion H1. inversion H1. inversion H1.  inversion H1.  
 
intros.
destruct cso;destruct cs1;destruct cs2. simpl in H1. inversion H1.
simpl in H1. inversion H1. simpl in H1. inversion H1.
simpl in H1. inversion H1. 
inversion H. inversion H.
inversion H0.
simpl in H1.  destruct p; destruct p0; destruct p1.
simpl in H0. simpl in H. inversion H0;subst. inversion H;subst. 
destruct (scenario_dec s3 s3).     
 remember (mergeControlStateFunc cso cs1 cs2). 
 destruct (e0).   destruct (string_dec s2 s4). subst. inversion H1;auto. 
 subst. simpl. f_equal.
apply IHl with (cs2:=cs2) (cs1:=cs1);auto.  

destruct (string_dec s2 s0).  subst.  inversion H1.  simpl. f_equal.  
subst.  apply IHl with (cs2:=cs2) (cs1:=cs1);auto.

destruct (string_dec s4 s0).  
inversion H1.    subst. simpl. f_equal.
apply IHl with (cs2:=cs2) (cs1:=cs1);auto.  

inversion H1. inversion H1. inversion H1.     
Qed.

Lemma mergeControlSceInvariant: forall cso cs1 cs2 cs3 sce, In sce (dom cso) -> (dom cso = dom cs1) -> (dom cs1 = dom cs2)
-> Result cs3 = mergeControlStateFunc cso cs1 cs2 -> getScenarioState sce (cs1) = getScenarioState sce (cs2) -> 
 getScenarioState sce (cs1) = getScenarioState sce (cso)
-> getScenarioState sce (cso) = getScenarioState sce (cs3).
Proof. intro cso. induction cso.
- intros. inversion H.
- intros. simpl in H. destruct H. 

+ simpl. destruct a.   destruct (string_dec (scenarioId sce) (scenarioId s)). 
* simpl in H2. destruct cs1. inversion H2. destruct cs2.  inversion H1.  inversion H1. subst.
inversion H0;subst. simpl. destruct p;destruct p0.  destruct (scenario_dec (fst (s, s1))).
simpl. simpl in H3.  destruct (string_dec (scenarioId s) (scenarioId s)). inversion H0.       
destruct (scenario_dec (fst (s, s1)) s2).  inversion e2.
destruct (mergeControlStateFunc cso cs1 cs2).    
destruct (string_dec s1 s3). inversion H2. simpl.  
destruct (string_dec (scenarioId s) (scenarioId s)).  simpl in H4.
destruct (string_dec (scenarioId s) (scenarioId s)). symmetry;auto.
exfalso;apply n. auto.  exfalso;apply n. auto.  simpl in H4.  
destruct (string_dec s1 s0). inversion H2. simpl.   
destruct (string_dec (scenarioId s) (scenarioId s)). 
destruct (string_dec (scenarioId s) (scenarioId s2)). rewrite e3 in H3. auto.
rewrite <- e2 in n0. simpl in n0. exfalso;apply n0;auto.
exfalso;apply n0;auto. 
destruct (string_dec s3 s0).  
inversion H2. simpl.        
destruct ( string_dec (scenarioId s) (scenarioId s)).  symmetry;auto.
 exfalso;apply n1;auto. inversion H2. inversion H2. inversion H2.    exfalso;apply n;auto. inversion H2. 
* 
rewrite <- H in n. simpl in n. exfalso;apply n;auto.
+ simpl.  destruct a.     destruct (string_dec (scenarioId sce) (scenarioId s)). 
*
simpl in H2. destruct cs1. inversion H2. destruct cs2.  inversion H1.  inversion H1. subst.
inversion H0;subst. simpl. destruct p;destruct p0.  destruct (scenario_dec (fst (s, s1))).
simpl. simpl in H3.  
destruct (scenario_dec (fst (s, s1)) s2).  
destruct (mergeControlStateFunc cso cs1 cs2).    
destruct (string_dec s1 s3). inversion H2. simpl.  
 simpl in H4.
destruct (string_dec (scenarioId sce) (scenarioId s)).  symmetry;auto.
exfalso;apply n. auto.   simpl in H4.
destruct (string_dec s1 s0). inversion H2 . simpl. 
destruct (string_dec (scenarioId sce) (scenarioId s)).  rewrite e0 in e1. 
destruct (string_dec (scenarioId sce) (scenarioId s2)). rewrite e2 in H3. auto.
rewrite <- e1 in n0.   exfalso;apply n0. auto. exfalso;apply n0. auto. 
destruct (string_dec (scenarioId sce) (scenarioId s)).
destruct (string_dec s3 s0). 
 inversion H2. simpl. 
rewrite e2. 
destruct (string_dec (scenarioId s) (scenarioId s)). symmetry. auto.  
exfalso;apply n1.  auto. inversion H2.
destruct (string_dec s3 s0). inversion H2. simpl.
destruct (string_dec (scenarioId sce) (scenarioId s)).
exfalso;apply n1;auto. simpl in e. exfalso;apply n2;auto. inversion H2. inversion H2. inversion H2.
inversion H2.       
  

* simpl in H4.   destruct (string_dec (scenarioId sce) (scenarioId s)).
rewrite e in n.   exfalso;apply n;auto. 
simpl in H2. 

destruct cs1. inversion H2. destruct cs2.  inversion H1.  inversion H1. subst.
inversion H0;subst. simpl. destruct p;destruct p0.  destruct (scenario_dec (fst (s, s1)) s).
simpl. simpl in H3.  
destruct (scenario_dec (fst (s, s1)) s2). Focus 2. inversion H2. Focus 2. inversion H2.    
remember (mergeControlStateFunc cso cs1 cs2).
destruct e1.   
destruct (string_dec s1 s3). Focus 3. inversion H2.      inversion H2. simpl.  
 simpl in H4.
destruct (string_dec (scenarioId sce) (scenarioId s)). 
exfalso;apply n. auto.  destruct (string_dec (scenarioId sce) (scenarioId s2) ).
  rewrite e in e0. rewrite <- e0 in e2. exfalso;apply n0.  auto.
apply IHcso with (cs1:=cs1) (cs2:=cs2). auto. auto. auto. auto. auto. auto. 
simpl in H4.  
destruct (string_dec s1 s0). inversion H2. simpl.
destruct (string_dec (scenarioId sce) (scenarioId s)).  exfalso;apply n0.  auto.
 destruct (string_dec (scenarioId sce) (scenarioId s2) ).
  rewrite e in e0. rewrite <- e0 in e2. exfalso;apply n0.  auto.
apply IHcso with (cs1:=cs1) (cs2:=cs2). auto. auto. auto. auto. auto. auto.
destruct (string_dec s3 s0). 
     destruct (string_dec (scenarioId sce) (scenarioId s)). exfalso;apply n0.  auto.
 destruct (string_dec (scenarioId sce) (scenarioId s2) ). simpl in H6.
rewrite H6 in n3. 
   exfalso;apply n3.  auto. 
inversion H2. simpl. 
destruct (string_dec (scenarioId sce) (scenarioId s)).   exfalso;apply n0.  auto. 
apply IHcso with (cs1:=cs1) (cs2:=cs2). auto. auto. auto. auto. auto. auto. inversion H2. 
  

Qed. 
   
Lemma mergeControlSceInvariant': forall M (config config1 config2 config3 : configuration M)
 sce, dom (controlstate config) = dom (controlstate config1) ->
dom (controlstate config1) = dom (controlstate config2)->
In sce (dom (controlstate config)) ->
 Result config3 = mergeConfigFunc config config1 config2
-> getScenarioState sce ( (controlstate config1)) = getScenarioState sce ( (controlstate config2)) 
-> getScenarioState sce (( (controlstate config1))) = getScenarioState sce (( (controlstate config)))
-> getScenarioState sce ( (controlstate config)) = getScenarioState sce ( (controlstate config3)).
Proof. intros. 
unfold mergeConfigFunc in H2.
destruct (mergeDataStateFunc (datastate config) (datastate config1) (datastate config2) ).
remember (mergeControlStateFunc (controlstate config) (controlstate config1) (controlstate config2)).
destruct e.  
inversion H2;subst. simpl.    
apply mergeControlSceInvariant with (cs1:=controlstate config1) (cs2:=controlstate config2);auto.

inversion H2. inversion H2.
Qed. 

Lemma domMergeConfig1: forall v v1 v2,  (exists v3, Result (v3) = 
mergeControlStateFunc (v) (v1) (v2)) ->
 dom v = dom v1.
Proof.  
Print mergeControlStateFunc. intro v. 
induction v.
intros. destruct H.  destruct v1. auto.
simpl in H. 
inversion H.
intros. destruct H. destruct v1. simpl in H.  destruct a. inversion H.
destruct v2. simpl in H. destruct a;destruct p. inversion H. 
simpl in H.  
 destruct a. destruct p.  destruct p0. 
destruct (scenario_dec s s1). 
destruct (scenario_dec s s3). subst.
remember (mergeControlStateFunc v v1 v2).
destruct e. simpl. f_equal.
apply IHv with (v2:=v2);auto.
exists v0;auto. 
inversion H. inversion H.  inversion H.             
Qed. 

Lemma domMergeConfig2: forall v v1 v2,  (exists v3, Result (v3) = 
mergeControlStateFunc (v) (v1) (v2)) ->
 dom v = dom v2.
Proof.  
Print mergeControlStateFunc. intro v. 
induction v.
intros. destruct H.  destruct v1. destruct v2.  auto.
simpl in H. 
inversion H.
intros. simpl in H.  inversion H.
intros. 
destruct H. destruct v1. simpl in H.  destruct a. inversion H.
destruct v2. simpl in H. destruct a;destruct p. inversion H. 
simpl in H.  
 destruct a. destruct p.  destruct p0. 
destruct (scenario_dec s s1). 
destruct (scenario_dec s s3). subst.
remember (mergeControlStateFunc v v1 v2).
destruct e. simpl. subst. f_equal.
apply IHv with (v1:=v1);auto.
exists v0;auto. 
inversion H. inversion H.  inversion H.             
Qed.


Lemma domMergeConfig: forall v v1 v2,  (exists v3, Result (v3) = 
mergeControlStateFunc (v) (v1) (v2)) ->
 dom v = dom v1 /\ dom v = dom v2.
Proof. intros. split. apply domMergeConfig1 with v2. auto.
     apply domMergeConfig2 with v1. auto.
Qed. 

Lemma mergeConfigFuncCSNoChange: forall M (conf conf1 conf2 : configuration M) v,
    Result v = mergeConfigFunc' conf conf1 conf2 ->
    dom (controlstate conf) = dom (controlstate v). 
Proof.
  intros.
  unfold mergeConfigFunc' in H.
  remember ( mergeDataStateFunc (datastate conf) (datastate conf1) (datastate conf2)).
  destruct e;inversion H.
  remember (  mergeControlStateFunc (controlstate conf) (controlstate conf1)
                                    (controlstate conf2)).
  destruct e;inversion H;auto. simpl.
  pose proof domMergeConfig.
  assert (dom (controlstate conf) = dom (controlstate conf1) /\ dom (controlstate conf) = dom (controlstate conf2)).
  apply H0. exists v1;auto.
  destruct H3. 
  
  pose proof mergeControlInvariant.
  apply H5 with (cs1:=(controlstate conf1)) (cs2:=(controlstate conf2));auto.
  rewrite H3 in H4;auto. 
Qed.

Lemma domMerge: forall  originconf conf' conf'',  (exists rconf,  Result (rconf) = mergeControlStateFunc originconf conf' conf'')
-> (dom ( originconf)) = (dom ( conf')) /\ (dom ( originconf)) = (dom ( conf'')).
Proof.   intros. apply domMergeConfig. auto. 
Qed.

Lemma domMerge': forall M (originconf conf' conf'' : configuration M),  (exists rconf,  Result (rconf) = mergeConfigFunc' originconf conf' conf'')
-> (dom (controlstate originconf)) = (dom (controlstate conf')) /\ (dom (controlstate originconf)) = (dom (controlstate conf'')).
Proof.   intros. destruct H. unfold mergeConfigFunc' in H.
destruct (mergeDataStateFunc (datastate originconf) (datastate conf') (datastate conf'') ).
Focus 2. inversion H.
remember (mergeControlStateFunc (controlstate originconf) (controlstate conf') (controlstate conf'')).
destruct e. 
apply    domMerge. exists v0. auto. inversion H.      
Qed.

Lemma appInclu
     : forall (A : Type) (l1 l2 l : list A),
    incl l1 l -> incl l2 l -> incl ( l1 ++ l2 ) l.
Proof. intros A l1;induction l1. 
-intros. simpl;auto.  
- intros. simpl.   unfold incl.
  intros. destruct H1. subst. unfold incl in H. apply H;auto. left;auto.
  apply in_app_iff in H1. destruct H1.
  unfold incl in H. apply H. right;auto. 
 
  unfold incl in H0. apply H0. auto.
Qed.   

Lemma incluSyncL1: forall M (conf conf' : configuration M) sce e,   In sce (dom (controlstate conf)) -> correct_configuration conf  -> Result conf' = constructConfig sce e conf  -> 
scenarioInclusion conf'.
Proof. intros. destruct H0.  unfold scenarioInclusion. unfold scenarioInclusion in inclusion.
       symmetry in H1. apply LL1' in H1. destruct H1. rewrite H1.    apply inclInvariant.
    unfold incl. intros. destruct H2. rewrite <- H0;auto. unfold not. intros. inversion H2.
Qed.


(*aux lemma for proving incluSyncL4*)
Lemma incluSyncL2: forall M (rconf originconf conf' conf'' : configuration M),   Result (rconf) = mergeConfigFunc' originconf conf' conf''
/\ scenarioInclusion originconf /\ scenarioInclusion conf' /\ scenarioInclusion conf'' -> scenarioInclusion rconf.

Proof.  intros. destruct H. remember H. clear Heqe.    
apply mergeConfigFuncCSNoChange in H. assert ( (dom (controlstate originconf)) = (dom (controlstate conf')) /\ (dom (controlstate originconf)) = (dom (controlstate conf''))). 
 apply domMerge'. exists rconf. auto.     
 
repeat match goal with
            | [ H: _ /\ _ |- _ ] => destruct H
            end.

unfold  scenarioInclusion.
rewrite <- H.     
unfold mergeConfigFunc' in e. 
destruct ( mergeDataStateFunc (datastate originconf)
        (datastate conf') (datastate conf'')).
remember (mergeControlStateFunc (controlstate originconf) (controlstate conf') (controlstate conf'')). 
destruct e0;inversion e;auto.  simpl. 
destruct (mergeControlStateFunc (controlstate originconf) (controlstate conf') (controlstate conf'')).
Focus 2. inversion Heqe0. Focus 2.   inversion e.

destruct (mergeList' (raisedevents conf') (raisedevents conf'') raisedEvent_dec). 
destruct (mergeList' (exportedevents conf') (exportedevents conf'') raisedEvent_dec).
inversion e. simpl.
Check mergeInclu.
SearchAbout incl. 
apply appInclu;auto. unfold scenarioInclusion in H3. rewrite H1;auto.  rewrite H2;auto.
apply appInclu;auto. unfold scenarioInclusion in H3. rewrite H1;auto.  rewrite H2;auto.
apply appInclu;auto. unfold scenarioInclusion in H3. rewrite H1;auto.  rewrite H2;auto.


Qed.  


(*aux lemma for proving incluSync*)
Lemma incluSyncL4: forall M v (conf : configuration M) e  w,
    correct_configuration conf
      -> (forall conf', In conf' v
            -> (exists sce,
                   In sce (dom (controlstate conf))
                     /\  Result (conf')=  constructConfig sce e conf))
      -> Some (w) =  innerCombineFunc'''' conf v
      -> scenarioInclusion w.
Proof.
intros ? v. induction v.
- intros. simpl in H1. inversion H1.
- intros. simpl in H1.
  destruct v. 
 remember (mergeConfigFunc' conf conf a).
  destruct e0;inversion H1;auto. subst.
  pose proof incluSyncL2.
  apply incluSyncL2 with (originconf:=conf) (conf':=conf) (conf'':=a);auto. split;auto.
  split. destruct H;auto. split.  destruct H;auto.
destruct H0 with a. left;auto. 
destruct H3.   
apply incluSyncL1 with (e:=e) (conf:=conf) (sce:=x);auto.
remember (innerCombineFunc'''' conf (c :: v)).
destruct o;inversion H1. clear H3.  
remember (mergeConfigFunc' conf a c0).
destruct e0;inversion H1. subst.
apply IHv with (e:=e) in Heqo;auto.
Focus 2. 
intros.
apply H0. right;auto.
 pose proof incluSyncL2.
  apply incluSyncL2 with (originconf:=conf) (conf':=a) (conf'':=c0);auto. split;auto.
  split. destruct H;auto. split.  destruct H0 with a;auto.
left;auto. destruct H3.   
apply incluSyncL1 with (e:=e) (conf:=conf) (sce:=x);auto.
auto. 
(*remember (innerCombineFunc'''' conf v). destruct o;inversion H1;auto. remember (mergeConfigFunc' conf c a). destruct e0;inversion H1;auto;subst. 
  simpl in H0. destruct H0 with a. left. auto. destruct H2.
  SearchAbout mergeConfigFunc'.
  pose proof incluSyncL2.
  apply incluSyncL2 with (originconf:=conf) (conf':=c) (conf'':=a);auto. split;auto.
  split. destruct H;auto. split.
  
  apply IHv with (e:=e) in Heqo;auto.
  apply incluSyncL1 with (e:=e) (conf:=conf) (sce:=x);auto.
  remember (mergeConfigFunc' conf conf a).
  destruct e0;inversion H1;auto. subst.
  pose proof incluSyncL2.
  apply incluSyncL2 with (originconf:=conf) (conf':=conf) (conf'':=a);auto. split;auto.
  split. destruct H;auto. split.  destruct H;auto.
destruct H0 with a. left;auto. 
destruct H4.   
  apply incluSyncL1 with (e:=e) (conf:=conf) (sce:=x);auto.
*)
Qed. 
  
(*aux lemma for proving termL5*)
Lemma incluSync: forall M (conf conf' : configuration M) e,  correct_configuration conf -> synchrony conf conf' e -> scenarioInclusion conf'.
Proof. intros.   
unfold synchrony in H0. 
   repeat match goal with
            | [ H: _ /\ _ |- _ ] => destruct H

            end.

unfold combineFunc in H1.

remember (constructConfigList (dom (controlstate conf)) e conf).
destruct e0. destruct v. inversion H1.

Focus 2. inversion H1. remember (innerCombineFunc'''' conf (c :: v)).
destruct o;inversion H1.  unfold removeEventFromConf. unfold scenarioInclusion.
simpl. pose proof incluSyncL4.
assert (scenarioInclusion c0).
apply H2 with (v:=(c::v)) (conf:=conf) (e:=e);auto. intros.
pose proof termL2.
unfold constructConfigList in Heqe0.
assert (exists sce : scenario,
    In sce (filter
               (fun x : scenario =>
                inList event_definition_dec (eventDefinition e) (alphabet x))
               (filterList (finishedscenarios conf) (dom (controlstate conf))
                  scenario_dec)) /\ Result conf'0 = constructConfig sce e conf). 
apply H5 with (lst:=c::v);auto.
destruct H6. destruct H6. exists x. split;auto. apply filter_In in H6.
destruct H6. apply filterL2 in H6;auto.
unfold scenarioInclusion in H4. auto. 
Qed.



Lemma uniqSyncL1: forall M (conf conf' : configuration M) e sce,   In sce (dom (controlstate conf)) -> correct_configuration conf  -> Result conf' = constructConfig sce e conf  -> 
uniqList (dom (controlstate conf')) 
/\ uniqList (finishedscenarios conf').
Proof.  intros. assert (dom (controlstate conf) = dom (controlstate conf')).
symmetry in H1. apply LL1' in H1. destruct H1. auto. 
destruct H0. split. rewrite <- H2. auto.
symmetry in H1. apply LL1' in H1. 
destruct H1. rewrite H1.  constructor. constructor. unfold not. intros. inversion H3. 
Qed.    
           
  
  
Lemma uniqSyncL2: forall M (rconf originconf conf' conf'' : configuration M), correct_configuration originconf
-> uniqList (dom (controlstate conf')) 
-> uniqList (finishedscenarios conf') 
-> uniqList (dom (controlstate conf'')) 
-> uniqList (finishedscenarios conf'') 
->  Result (rconf) = mergeConfigFunc' originconf conf' conf'' 
-> (forall i : scenario, In i (finishedscenarios conf') -> ~ In i (finishedscenarios conf''))
-> (forall i : scenario, In i (finishedscenarios conf'') -> ~ In i (finishedscenarios conf'))
-> uniqList (dom (controlstate rconf)) 
/\ uniqList (finishedscenarios rconf).
Proof. intros.
split.
- assert ( dom (controlstate originconf) = dom (controlstate conf') /\
       dom (controlstate originconf) = dom (controlstate conf'')). 
apply     domMerge'. exists rconf. auto. 

assert ((dom (controlstate rconf) = (dom (controlstate conf')))).
destruct H7.

apply mergeConfigFuncCSNoChange in H4;auto. rewrite H4 in H7;auto.
destruct H7. rewrite H8;auto. 

- unfold mergeConfigFunc' in H4.           
destruct (mergeDataStateFunc (datastate originconf) (datastate conf') (datastate conf'')).
destruct (mergeControlStateFunc (controlstate originconf) (controlstate conf') (controlstate conf'')).
inversion H4. simpl. 
Focus 2. inversion H4. Focus 2. inversion H4.
clear H8. 
SearchAbout uniqList.
apply uniqApp';auto. 
Qed.   

Lemma finishedscenarioIn: forall lst e M (conf : configuration M) v i c,
    uniqList lst ->
    incl lst (dom (controlstate conf)) ->
    Result v = constructConfigList' lst e conf ->
    Some c = innerCombineFunc'''' conf v ->
    In i (finishedscenarios c) ->
    ~ In i (finishedscenarios conf) ->
    In i lst. 
Proof. intro lst;induction lst. 
       - intros. simpl in H1. inversion H1;subst. simpl in H2.  inversion H2.
       - intros. simpl in H1.
         remember (constructConfig a e conf).
         destruct e0;inversion H1. clear H6.
         remember (constructConfigList' lst e conf).
         destruct e0;inversion H1. subst.
         clear H1.
         simpl in H2.
         destruct v1.
           remember (mergeConfigFunc' conf conf v0).
         destruct e0;inversion H2. subst.

          unfold mergeConfigFunc' in Heqe2.
         destruct (mergeDataStateFunc (datastate conf) (datastate conf) (datastate v0));inversion Heqe2. destruct (mergeControlStateFunc (controlstate conf) (controlstate conf) (controlstate v0));inversion H2;subst. inversion H5. rewrite H6 in H3. simpl in H3. clear H5.
         clear H6. clear H2. 
         apply in_app_iff in H3. destruct H3.
         contradiction.
         apply termL3 in Heqe0. rewrite Heqe0 in H1. destruct H1. subst. left;auto.
         inversion H1. 
         inversion H5.
         remember (innerCombineFunc'''' conf (c0 :: v1)).
         destruct o;inversion H2;subst.
         clear H5.
         remember (mergeConfigFunc' conf v0 c1).
         destruct e0;inversion H2. subst. clear H2.
         unfold mergeConfigFunc' in Heqe2.
         destruct (mergeDataStateFunc (datastate conf) (datastate v0) (datastate c1));inversion Heqe2. destruct (mergeControlStateFunc (controlstate conf) (controlstate v0) (controlstate c1));inversion H2;subst. simpl in H3. clear Heqe2.
         clear H2.
         apply in_app_iff in H3. destruct H3.
         Focus 2. 
         apply IHlst with (e:=e) (i:=i) in Heqo;auto.
         Focus 2. inversion H;auto. Focus 2.
         unfold incl. unfold  incl in H0. 
         intros.    apply H0;auto. right;auto.
         right;auto.
         apply termL3 in Heqe0. rewrite Heqe0 in H1. destruct H1. subst. left;auto.
         inversion H1.
         (*remember (innerCombineFunc'''' conf v1).
         destruct o;inversion H2;subst. clear H5.
         remember (mergeConfigFunc' conf c0 v0).
         destruct e0;inversion H2. subst. clear H2.
         unfold mergeConfigFunc' in Heqe2.
         destruct (mergeDataStateFunc (datastate conf) (datastate c0) (datastate v0));inversion Heqe2. destruct (mergeControlStateFunc (controlstate conf) (controlstate c0) (controlstate v0));inversion H2;subst. simpl in H3. clear Heqe2.
         clear H2.
         apply in_app_iff in H3. destruct H3.
         apply IHlst with (e:=e) (i:=i) in Heqo;auto.
         Focus 2. inversion H;auto. Focus 2.
         unfold incl. unfold  incl in H0. 
         intros.    apply H0;auto. right;auto.
         right;auto.
         apply termL3 in Heqe0. rewrite Heqe0 in H1. destruct H1. subst. left;auto.
         inversion H1.
         clear H5.
         remember (mergeConfigFunc' conf conf v0).
         destruct e0;inversion H2. subst.

          unfold mergeConfigFunc' in Heqe2.
         destruct (mergeDataStateFunc (datastate conf) (datastate conf) (datastate v0));inversion Heqe2. destruct (mergeControlStateFunc (controlstate conf) (controlstate conf) (controlstate v0));inversion H2;subst. inversion H5. rewrite H6 in H3. simpl in H3. clear H5.
         clear H6. clear H2. 
         apply in_app_iff in H3. destruct H3.
         contradiction.
         apply termL3 in Heqe0. rewrite Heqe0 in H1. destruct H1. subst. left;auto.
         inversion H1. 
      inversion H5. *)
Qed.

Lemma termL2': forall scs M (conf : configuration M) e lst  sce, constructConfigList' scs e conf = Result lst ->
 In sce scs -> exists conf', Result conf' = constructConfig sce e conf.
Proof.  intro lst. induction lst.
- intros. inversion H0.
- intros. destruct H0. simpl in H. 
remember (constructConfig a e conf). destruct e0.
 
remember (constructConfigList' lst e conf).

destruct e0. subst. exists v;auto. inversion H. inversion H. 
simpl in H.
remember ( constructConfig a e conf ).
destruct e0;inversion H. clear H2. 
remember (constructConfigList' lst e conf ).
destruct e0;inversion H. subst. 


symmetry in Heqe1. apply IHlst  with (sce:=sce) in Heqe1 ;auto.
     
Qed.


Lemma finishedscenarioInAll: forall lst e M (conf : configuration M) v i c,
    uniqList lst ->
    incl lst (dom (controlstate conf)) ->
    Result v = constructConfigList' lst e conf ->
    Some c = innerCombineFunc'''' conf v ->
     In i (finishedscenarios c) ->
    (In i lst \/ In i (finishedscenarios conf)). 
Proof. intro lst;induction lst. 
       - intros. simpl in H1. inversion H1;subst. simpl in H2.  inversion H2.
       - intros. simpl in H1.
         remember (constructConfig a e conf).
         destruct e0;inversion H1. clear H5.
         remember (constructConfigList' lst e conf).
         destruct e0;inversion H1. subst.
         clear H1.
         simpl in H2.
         
         destruct v1.
         remember (mergeConfigFunc' conf conf v0).
         destruct e0;inversion H2. subst.
         unfold mergeConfigFunc' in Heqe2.
         destruct (mergeDataStateFunc (datastate conf) (datastate conf) (datastate v0));inversion Heqe2. destruct (mergeControlStateFunc (controlstate conf) (controlstate conf) (controlstate v0));inversion H2;subst. inversion H4. rewrite H5 in H3;simpl in H3.  clear Heqe2.
         clear H4. clear H5.  clear H2. 
         
         apply in_app_iff in H3. destruct H3.
         right;auto.
         SearchAbout finishedscenarios.
         apply termL3 in Heqe0. rewrite Heqe0 in H1. destruct H1. subst. left;left;auto. 
inversion H1.          inversion H4. 
         remember (innerCombineFunc'''' conf (c0 :: v1)). 
           destruct o;inversion H2;subst. clear H4.
         remember (mergeConfigFunc' conf v0 c1).
         destruct e0;inversion H2. subst. clear H2.
         unfold mergeConfigFunc' in Heqe2.
         destruct (mergeDataStateFunc (datastate conf) (datastate v0) (datastate c1));inversion Heqe2. destruct (mergeControlStateFunc (controlstate conf) (controlstate v0) (controlstate c1));inversion H2;subst. simpl in H3. clear Heqe2.
         clear H2.
         apply in_app_iff in H3. destruct H3.
         Focus 2. 
          apply IHlst with (e:=e) (i:=i) in Heqo;auto.
          
          destruct Heqo.
          left. right;auto. right;auto. inversion H;auto. 
           
         unfold incl. unfold  incl in H0. 
         intros.    apply H0;auto. right;auto.
         apply termL3 in Heqe0. rewrite Heqe0 in H1. destruct H1. subst.
         left;auto. left;auto. inversion H1. 
         (*remember (innerCombineFunc'''' conf v1).
         destruct o;inversion H2;subst. clear H4.
         remember (mergeConfigFunc' conf c0 v0).
         destruct e0;inversion H2. subst. clear H2.
         unfold mergeConfigFunc' in Heqe2.
         destruct (mergeDataStateFunc (datastate conf) (datastate c0) (datastate v0));inversion Heqe2. destruct (mergeControlStateFunc (controlstate conf) (controlstate c0) (controlstate v0));inversion H2;subst. simpl in H3. clear Heqe2.
         clear H2. 
         
         apply in_app_iff in H3. destruct H3. 
         apply IHlst with (e:=e) (i:=i) in Heqo;auto. destruct Heqo.
         left. right;auto. right;auto. inversion H;auto. 
         
         unfold incl. unfold  incl in H0. 
         intros.    apply H0;auto. right;auto.
         apply termL3 in Heqe0. rewrite Heqe0 in H1. destruct H1. subst.
         left;auto. left;auto. inversion H1. 
         clear H4. 
        
          unfold mergeConfigFunc' in H2.
         destruct (mergeDataStateFunc (datastate conf) (datastate conf) (datastate v0));inversion H2. destruct (mergeControlStateFunc (controlstate conf) (controlstate conf) (controlstate v0));inversion H2;subst. simpl in H3. clear H2.
         clear H4.
         
         
         apply in_app_iff in H3. destruct H3. right;auto.

          apply termL3 in Heqe0. rewrite Heqe0 in H1. destruct H1. subst.
         left;auto. left;auto. inversion H1. 
Qed. *)

(*(forall conf', In conf' v -> (exists sce, In sce lst /\  Result (conf')=  constructConfig sce e conf ))
->*)
Qed. 
         
Lemma uniqSyncL3: forall M (conf : configuration M) lst v e  w,
    correct_configuration conf ->
    uniqList lst ->
    incl lst (dom (controlstate conf)) ->
   
Result v =
          constructConfigList'
            lst e
            conf ->
(forall sce, In sce lst -> ~ In sce (finishedscenarios conf)) ->
Some(w) =  innerCombineFunc'''' conf v ->  uniqList (dom (controlstate w)) 
/\ uniqList (finishedscenarios w).
Proof. 
intros ? ? lst. induction lst.
- intros. simpl in H2. inversion H2;subst. simpl in H4. inversion H4. 
- intros. simpl in H2.
  remember (constructConfig a e conf).
  destruct e0;inversion H2. clear H6.
  remember (constructConfigList' lst e conf).
  destruct e0;inversion H2;subst. clear H2.
  simpl in H4.
  destruct v1.
   remember (mergeConfigFunc' conf conf v0).
  destruct e0;inversion H4;auto. subst.
  split.
  pose proof mergeConfigFuncCSNoChange. 
  rewrite <- mergeConfigFuncCSNoChange with (conf:= conf) (conf1:=conf) (conf2:=v0) (v:=v);auto. destruct H;auto.
  unfold mergeConfigFunc' in Heqe2.
  destruct (mergeDataStateFunc (datastate conf) (datastate conf) (datastate v0));inversion Heqe2.
  destruct (mergeControlStateFunc (controlstate conf) (controlstate conf) (controlstate v0));inversion H5. simpl.
  clear H6. clear H4;clear H5. clear Heqe2.
  apply uniqApp';auto.
  destruct H;auto.
  apply termL3 in Heqe0. rewrite Heqe0. constructor. constructor.
  unfold not. intros. inversion H2.
  intros.
  apply termL3 in Heqe0. rewrite Heqe0. unfold not. intros.
  destruct H4;subst. Focus 2. inversion H4.
  destruct H3 with (sce:=i);auto. left;auto.
  intros.
  apply H3;auto.
  apply termL3 in Heqe0. rewrite Heqe0 in H2.
  destruct H2. subst. left;auto. inversion H2.

  remember (innerCombineFunc'''' conf (c :: v1)). 
   destruct o;inversion H4.
  remember (mergeConfigFunc' conf v0 c0 ).
  destruct e0;inversion H4;subst. clear H4;clear H5.
  split.
  pose proof mergeConfigFuncCSNoChange.
  apply H2 in Heqe2. rewrite <- Heqe2. destruct H;auto.
  unfold mergeConfigFunc' in Heqe2.
  remember (mergeDataStateFunc (datastate conf) (datastate v0) (datastate c0)).
  destruct e0;inversion Heqe2.
  remember ( mergeControlStateFunc (controlstate conf) (controlstate v0) (controlstate c0)).
  destruct e0;inversion H4. simpl.
  apply uniqApp'. Focus 2. 
  apply IHlst with (e:=e) in Heqo;auto. Focus 2. inversion H0;auto.
  Focus 2. 

  unfold incl. intros. unfold incl in H1. apply H1;auto. right;auto.
  destruct Heqo;auto. intros. apply H3. right;auto. 
  apply termL3 in Heqe0;auto. rewrite Heqe0. constructor. constructor. unfold not. intros.
  inversion H2.
  intros.  SearchAbout finishedscenarios. apply termL3 in Heqe0. rewrite Heqe0 in H2.
  destruct H2. subst.  Focus 2. inversion H2.
assert ( ~ In i (finishedscenarios conf)).
  apply H3;auto. left;auto.
 unfold not. intros.
  pose proof finishedscenarioInAll.
  assert (  In i lst \/ In i (finishedscenarios conf)).
  apply H6 with (e:=e) (v:=c::v1) (c:=c0);auto.
  inversion H0;auto.
  unfold incl;intros. unfold incl in H1. apply H1;auto. right;auto.
  destruct H7. inversion H0;subst. contradiction. contradiction.
  intros.
  unfold not;intros. 
  apply termL3 in Heqe0.  rewrite Heqe0 in H6. destruct H6. Focus 2. 
  inversion H6.   subst.  pose proof finishedscenarioInAll. 
 
  assert (  In i lst \/ In i (finishedscenarios conf)).
  apply H5 with (e:=e) (v:=c::v1) (c:=c0);auto.
  inversion H0;auto.
  unfold incl;intros. unfold incl in H1. apply H1;auto. right;auto.
  destruct H6. inversion H0;subst. contradiction.
  destruct H3 with i. left;auto. auto. 
  (*
  remember (innerCombineFunc'''' conf v1).
  destruct o;inversion H4.
  remember (mergeConfigFunc' conf c v0 ).
  destruct e0;inversion H4;subst. clear H4;clear H5.
  split.
  pose proof mergeConfigFuncCSNoChange.
  apply H2 in Heqe2. rewrite <- Heqe2. destruct H;auto.
  unfold mergeConfigFunc' in Heqe2.
  remember (mergeDataStateFunc (datastate conf) (datastate c) (datastate v0)).
  destruct e0;inversion Heqe2.
  remember ( mergeControlStateFunc (controlstate conf) (controlstate c) (controlstate v0)).
  destruct e0;inversion H4. simpl.
  apply uniqApp'.
  apply IHlst with (e:=e) in Heqo;auto. Focus 2. inversion H0;auto.
  Focus 2. 

  unfold incl. intros. unfold incl in H1. apply H1;auto. right;auto.
  destruct Heqo;auto. intros. apply H3. right;auto. 
  apply termL3 in Heqe0;auto. rewrite Heqe0. constructor. constructor. unfold not. intros.
  inversion H2.
  intros.
  remember Heqe0. clear Heqe5. 
  apply termL3 in Heqe0;auto. rewrite Heqe0.
  unfold not. intros. destruct H6;inversion H6. subst. clear H7.
  pose proof finishedscenarioIn. clear Heqe2. clear H4. 
  apply H5 with (i:=i) (c:=c) in Heqe1;auto. inversion H0;subst. contradiction.
  inversion H0;auto. unfold incl. unfold incl in H1. intros.
  apply H1;auto. right;auto. apply H3. left;auto.
  intros. clear H5. clear H4. clear Heqe2.
  apply termL3 in Heqe0. rewrite Heqe0 in H2. destruct H2. 
  subst.
  assert ( ~ In i (finishedscenarios conf)).
  apply H3;auto. left;auto.
  unfold not. intros.
  pose proof finishedscenarioInAll.
  assert (  In i lst \/ In i (finishedscenarios conf)).
  apply H5 with (e:=e) (v:=v1) (c:=c);auto.
  inversion H0;auto.
  unfold incl;intros. unfold incl in H1. apply H1;auto. right;auto.
  destruct H6. inversion H0;subst. contradiction. contradiction. inversion H2.
  remember (mergeConfigFunc' conf conf v0).
  destruct e0;inversion H4;auto. subst.
  split.
  SearchAbout (mergeConfigFunc').
  pose proof mergeConfigFuncCSNoChange. 
  rewrite <- mergeConfigFuncCSNoChange with (conf:= conf) (conf1:=conf) (conf2:=v0) (v:=v);auto. destruct H;auto.
  unfold mergeConfigFunc' in Heqe2.
  destruct (mergeDataStateFunc (datastate conf) (datastate conf) (datastate v0));inversion Heqe2.
  destruct (mergeControlStateFunc (controlstate conf) (controlstate conf) (controlstate v0));inversion H6. simpl.
  clear H7. clear H6. clear H4;clear H5. clear Heqe2.
  SearchAbout uniqList.
  apply uniqApp';auto.
  destruct H;auto.
  apply termL3 in Heqe0. rewrite Heqe0. constructor. constructor.
  unfold not. intros. inversion H2.
  intros.
  apply termL3 in Heqe0. rewrite Heqe0. unfold not. intros.
  destruct H4;subst. Focus 2. inversion H4.
  destruct H3 with (sce:=i);auto. left;auto.
  intros.
  apply H3;auto.
  apply termL3 in Heqe0. rewrite Heqe0 in H2.
  destruct H2. subst. left;auto. inversion H2. *)
Qed.   
 
Lemma filterUniq: forall A (l:list A) (f:A -> bool),
    uniqList l ->
    uniqList (@filter A f l).
Proof. intros A l;induction l.
       - intros. simpl. constructor.
       - intros. simpl.
         destruct (f a).
         inversion H;subst.
         constructor.
         apply IHl;auto.
         SearchAbout filter.
         unfold not;intros;apply H3.
         apply filter_In in H0. destruct H0;auto.
         apply IHl;inversion H;subst;auto. 
Qed.

        
       
Lemma uniqSync: forall M (conf conf' : configuration M) e,  correct_configuration conf -> synchrony conf conf' e -> uniqList (dom (controlstate conf'))
/\ uniqList (finishedscenarios conf').
Proof.  intros.   
unfold synchrony in H0. 
   repeat match goal with
            | [ H: _ /\ _ |- _ ] => destruct H

            end.

unfold combineFunc in H1. unfold constructConfigList in H1.

remember ( constructConfigList'
           (filter
              (fun x : scenario => inList event_definition_dec (eventDefinition e) (alphabet x))
              (filterList (finishedscenarios conf) (dom (controlstate conf)) scenario_dec)) e
           conf).
destruct e0;inversion H1.  destruct v;inversion H3.  clear H3. clear H1.

destruct v.
remember (mergeConfigFunc' conf conf c).
destruct e0;inversion H4.
unfold removeEventFromConf;simpl.
split.
apply mergeConfigFuncCSNoChange in Heqe1. rewrite <- Heqe1.
destruct H;auto. 
unfold mergeConfigFunc' in Heqe1.
destruct (mergeDataStateFunc (datastate conf) (datastate conf) (datastate c));inversion Heqe1. 
destruct ( mergeControlStateFunc (controlstate conf) (controlstate conf)
                                 (controlstate c));inversion H3;auto.
simpl.

apply uniqApp';auto.
destruct H;auto.

pose proof termL2.

assert (exists sce : scenario, In sce (filter
               (fun x : scenario =>
                inList event_definition_dec (eventDefinition e) (alphabet x))
               (filterList (finishedscenarios conf) (dom (controlstate conf))
                  scenario_dec)) /\ Result c = constructConfig sce e conf). 
apply H1 with (lst:=c::nil);auto. split;auto. left;auto.
destruct H6. destruct H6.
apply termL3 in H7. rewrite H7. constructor. constructor. unfold not. intros.
inversion H8.
intros. 

pose proof termL2.

assert (exists sce : scenario, In sce (filter
               (fun x : scenario =>
                inList event_definition_dec (eventDefinition e) (alphabet x))
               (filterList (finishedscenarios conf) (dom (controlstate conf))
                  scenario_dec)) /\ Result c = constructConfig sce e conf). 
apply H6 with (lst:=c::nil);auto. split;auto. left;auto.
destruct H7. 
destruct H7. 
apply filter_In in H7. 
destruct H7.
unfold not;intros.
apply filterL1 in H7.
apply termL3 in H8. rewrite H8 in H10. destruct H10. subst. contradiction. 
inversion H10.
intros. unfold not;intros. 

pose proof termL2.

assert (exists sce : scenario, In sce (filter
               (fun x : scenario =>
                inList event_definition_dec (eventDefinition e) (alphabet x))
               (filterList (finishedscenarios conf) (dom (controlstate conf))
                  scenario_dec)) /\ Result c = constructConfig sce e conf). 
apply H7 with (lst:=c::nil);auto. split;auto. left;auto.
destruct H8. 
destruct H8. 
apply filter_In in H8.
destruct H8. 
apply filterL1 in H8.
apply termL3 in H9. rewrite H9 in H1. destruct H1. subst. contradiction. 
inversion H1.
remember (c0 :: v). 


remember (innerCombineFunc'''' conf l).
destruct o;inversion H4;subst.
remember ( mergeConfigFunc' conf c c1). 
destruct e0;inversion H2;subst.
unfold removeEventFromConf;simpl.

pose proof domMerge'.
assert (dom (controlstate conf) = dom (controlstate c) /\
        dom (controlstate conf) = dom (controlstate c1)).
apply H1;auto. exists v0;auto. 
destruct H3. 
apply uniqSyncL2 with (originconf:=conf) (conf':=c) (conf'':=c1) ;auto.
rewrite <- H3.  destruct H;auto. 
Focus 2. rewrite <- H5. destruct H;auto. 
Focus 2.
pose proof termL2.
pose proof uniqSyncL3.
pose proof termL2.
assert (exists sce : scenario, In sce (filter
               (fun x : scenario =>
                inList event_definition_dec (eventDefinition e) (alphabet x))
               (filterList (finishedscenarios conf) (dom (controlstate conf))
                           scenario_dec))  /\ Result c = constructConfig sce e conf).
apply H8 with (lst:=(c :: c0 :: v));auto.
split;auto. left;auto.
destruct H9. destruct H9.

apply uniqSyncL1 in H10;auto. Focus 2.
apply filter_In in H9. destruct H9. apply filterL2 in H9;auto.  destruct H10;auto.
 apply filter_In in H9. destruct H9.

assert (uniqList (dom (controlstate c1)) /\ uniqList (finishedscenarios c1)).

 remember ((filter
               (fun x : scenario =>
                inList event_definition_dec (eventDefinition e) (alphabet x))
               (filterList (finishedscenarios conf) (dom (controlstate conf))
                           scenario_dec))).
 destruct l. simpl in Heqe0. inversion Heqe0.
 apply H7 with (conf:=conf) (lst:=l) (v:=(c0::v)) (e:=e);auto.
 assert (uniqList ( filter
           (fun x : scenario => inList event_definition_dec (eventDefinition e) (alphabet x))
           (filterList (finishedscenarios conf) (dom (controlstate conf)) scenario_dec))).
 SearchAbout filter. apply filterUniq;auto.
 SearchAbout filterList. apply uniqListFilter;destruct H;auto.
 rewrite <- Heql in H13. inversion H13;subst;auto.
 unfold incl;intros.
 assert (In a (s::l)). right;auto. rewrite  Heql in H14.
 SearchAbout filter. apply filter_In in H14. destruct H14. apply filterL2 in H14;auto.
 simpl in Heqe0. 
 destruct (constructConfig s e conf );inversion Heqe0.
 remember (constructConfigList' l e conf).
 destruct e0;inversion H14. auto. 
 intros.

 assert (In sce (s::l)). right;auto. rewrite  Heql in H14.
 apply filter_In in H14. destruct H14. apply filterL1 in H14;auto.
 destruct H13;auto. 

 remember ((filter
               (fun x : scenario =>
                inList event_definition_dec (eventDefinition e) (alphabet x))
               (filterList (finishedscenarios conf) (dom (controlstate conf))
                           scenario_dec))).
 destruct l. simpl in Heqe0. inversion Heqe0.
 simpl in Heqe0.
 remember (constructConfig s e conf).
 destruct e0;inversion Heqe0.
 destruct (constructConfigList' l e conf);inversion Heqe0. subst.
 apply termL3 in Heqe2. rewrite Heqe2. constructor. constructor. unfold not;intros. inversion H6. 
 intros.
 unfold not;intros.
  remember ((filter
               (fun x : scenario =>
                inList event_definition_dec (eventDefinition e) (alphabet x))
               (filterList (finishedscenarios conf) (dom (controlstate conf))
                           scenario_dec))).
 destruct l. simpl in Heqe0. inversion Heqe0.
 simpl in Heqe0.
 remember (constructConfig s e conf).
 destruct e0;inversion Heqe0.
clear H9.  remember (constructConfigList' l e conf). destruct e0;inversion Heqe0. subst.
apply termL3 in Heqe2. rewrite Heqe2 in H6. destruct H6. subst.
Focus 2. inversion H6.
pose proof finishedscenarioIn.
apply H6 with (lst:=l) (e:=e) (i:=i) in Heqo;auto. 
assert (uniqList ( filter
           (fun x : scenario => inList event_definition_dec (eventDefinition e) (alphabet x))
           (filterList (finishedscenarios conf) (dom (controlstate conf)) scenario_dec))).
SearchAbout filter.
apply filterUniq.
SearchAbout filterList. apply uniqListFilter;destruct H;auto.
rewrite <- Heql in H8. inversion H8;subst. contradiction.
assert (uniqList ( filter
           (fun x : scenario => inList event_definition_dec (eventDefinition e) (alphabet x))
           (filterList (finishedscenarios conf) (dom (controlstate conf)) scenario_dec))).
apply filterUniq.
 apply uniqListFilter;destruct H;auto.
 rewrite <- Heql in H8. inversion H8;subst;auto.
 unfold incl;intros.
 assert (In a (i::l)). right;auto. 
rewrite Heql in H9. apply filter_In in H9. destruct H9. apply filterL2 in H9;auto. 
assert (In i (i::l)). left;auto. 
rewrite Heql in H8. apply filter_In in H8. destruct H8. apply filterL1 in H8;auto. 
intros.
unfold not;intros. 

 remember ((filter
               (fun x : scenario =>
                inList event_definition_dec (eventDefinition e) (alphabet x))
               (filterList (finishedscenarios conf) (dom (controlstate conf))
                           scenario_dec))).
 destruct l. simpl in Heqe0. inversion Heqe0.
 simpl in Heqe0.
 remember (constructConfig s e conf).
 destruct e0;inversion Heqe0.
 remember(constructConfigList' l e conf). destruct e0;inversion Heqe0. subst.
 clear Heqe0.  apply termL3 in Heqe2. rewrite Heqe2 in H7. destruct H7;subst.  Focus 2. inversion H7.
clear H9. pose proof finishedscenarioIn.
 apply H7 with (lst:=l) (e:=e) (i:=i) in Heqo;auto. 
assert (uniqList ( filter
           (fun x : scenario => inList event_definition_dec (eventDefinition e) (alphabet x))
           (filterList (finishedscenarios conf) (dom (controlstate conf)) scenario_dec))).
apply filterUniq.
 apply uniqListFilter;destruct H;auto.
rewrite <- Heql in H8. inversion H8;subst. contradiction.
assert (uniqList ( filter
           (fun x : scenario => inList event_definition_dec (eventDefinition e) (alphabet x))
           (filterList (finishedscenarios conf) (dom (controlstate conf)) scenario_dec))).
apply filterUniq.
 apply uniqListFilter;destruct H;auto.
 rewrite <- Heql in H8. inversion H8;subst;auto.
 unfold incl;intros.
 assert (In a (i::l)). right;auto. 
rewrite Heql in H9. apply filter_In in H9. destruct H9. apply filterL2 in H9;auto. 
assert (In i (i::l)). left;auto. 
rewrite Heql in H8. apply filter_In in H8. destruct H8. apply filterL1 in H8;auto.


Qed.


(*
(*aux lemma*)
Lemma termL3': forall e conf sce conf',  Result conf' = constructConfig sce e conf  ->
 (forall sce', In sce' (finishedscenarios conf) ->In sce'  (finishedscenarios conf')).
Proof. 
intros. pose proof termL3. 
assert (finishedscenarios conf' = sce :: finishedscenarios conf).  
eapply H1. apply H. rewrite H2. simpl; right;auto.  
Qed.

(*aux lemma*)
Lemma finishedInvariant: forall e conf lst scs sce, constructConfigList' scs e conf = Result lst
(*-> In sce scs*) -> In sce (finishedscenarios conf) 
-> (forall conf', In conf' lst -> In sce (finishedscenarios conf')).
Proof. intros. pose proof termL2'. pose proof termL3'. pose proof termL2.
assert (constructConfigList' scs e conf = Result lst /\ In conf' lst).
split;auto. apply H4 in H5. destruct H5.  destruct H5. 
eapply H3 in H6. apply H6. auto.      
Qed.

(*aux lemma*)
Lemma finishedSceInvariant: forall config config1 config2 config3
 sce, In sce (dom (controlstate config)) -> 
(In sce (finishedscenarios config1) \/
In sce (finishedscenarios config2)) ->
 Result config3 = mergeConfigFunc config config1 config2
-> In sce (finishedscenarios config3) .
Proof. intros.
unfold mergeConfigFunc in H1.     
destruct (mergeDataStateFunc (datastate config) (datastate config1) (datastate config2)).
destruct (mergeControlStateFunc (controlstate config) (controlstate config1) (controlstate config2)).
inversion H1. simpl. unfold  mergeList'.
apply in_or_app. destruct H0. left. auto. 
assert (In sce (finishedscenarios config1) \/ ~(In sce (finishedscenarios config1))).
apply excluded_middle.  destruct H2. left. auto.     right.
SearchAbout filterIn. apply filterIn. auto. auto. inversion H1. inversion H1.    
Qed.
 
 (*aux lemma*)
Lemma finishedInvariantCombine: forall lst conf conf'  sce ,
correct_configuration conf -> In sce (finishedscenarios conf) ->
innerCombineFunc' conf None lst= Result conf' ->
(forall conf', In conf' lst -> In sce (finishedscenarios conf'))
-> In sce (finishedscenarios conf').
Proof. intro lst. induction lst.
- intros. simpl in H1. inversion H1.
-intros. simpl in H1. destruct lst. 
+ simpl in H1. apply H2. inversion H1. simpl;left;auto.
+ simpl in H1.  
remember ( innerCombineFunc' conf (Some c) lst ).
destruct e.   
assert (conf'=a \/ ~(conf'=a)). 
apply excluded_middle. destruct H3.
apply H2. rewrite H3. simpl;left;auto. Focus 2. inversion H1.
assert (In sce (finishedscenarios v)).
 
apply IHlst with (conf:=conf). auto. auto. symmetry;auto. 
intros. apply H2. simpl;right;auto.
eapply finishedSceInvariant. Focus 2. right. apply H4. Focus 2. symmetry. apply H1.
destruct H.
 unfold scenarioInclusion in inclusion. unfold incl in inclusion. apply inclusion. auto.
Qed.                     
*)

Print innerCombineFunc''''.

Lemma finishedInvariantCombine: forall M  v (conf conf' : configuration M)  sce ,
 
 In sce (finishedscenarios conf) ->
innerCombineFunc'''' conf v = Some conf' ->
 In sce (finishedscenarios conf').
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

Lemma finishedInvariantSync: forall e M (conf conf': configuration M) sce,
synchrony conf conf' e -> 
In sce (finishedscenarios conf)
-> In sce (finishedscenarios conf').
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
apply finishedInvariantCombine with (v:=c::v) (conf:=conf);auto. 


(*eapply finishedInvariantCombine. apply H. auto. apply H4. intros.
pose proof finishedInvariant. symmetry in Heqe0. unfold constructConfigList in Heqe0.
eapply H6. apply Heqe0. auto. auto. inversion H4. *)
Qed.

Lemma domControlSync: forall M (conf conf' : configuration M) e,  synchrony conf conf' e ->  (dom (controlstate conf)) = (dom (controlstate conf')).
Proof. intros.
unfold synchrony in H. 
   repeat match goal with
            | [ H: _ /\ _ |- _ ] => destruct H

            end.
unfold combineFunc in H0.   
remember (constructConfigList (dom (controlstate conf)) e conf).

destruct e0;inversion H0. destruct v;inversion H2.
clear H3. clear H0.

remember (innerCombineFunc'''' conf (c::v)).

destruct o;inversion H2;auto.
unfold removeEventFromConf. simpl.
SearchAbout innerCombineFunc''''. 
simpl in Heqo.
destruct v.
 remember (mergeConfigFunc' conf conf c).
  destruct e0;inversion Heqo.
subst.   apply mergeConfigFuncCSNoChange with (conf1:=conf) (conf2:=c);auto.
remember (innerCombineFunc'''' conf (c1 :: v)). 
destruct o;inversion Heqo.
clear H3. 
remember (mergeConfigFunc' conf c c2).
destruct e0;inversion Heqo. subst.
Check mergeConfigFuncCSNoChange. 
  apply mergeConfigFuncCSNoChange with (conf1:=c) (conf2:=c2);auto.
 
Qed.

Lemma monitorObjNoChangeSync: forall M (conf conf' : configuration M) e,
    synchrony conf conf' e -> M = M.
Proof. reflexivity. Qed.

Lemma scenarioStateNotNone: forall l sce, In sce (dom l) -> getScenarioState sce l <> None.
Proof. intros. induction (l). 
- inversion H.
- simpl. destruct a.   
destruct (string_dec (scenarioId sce) (scenarioId s)).
unfold not;intros. inversion H0. apply IHl0. simpl in H. 
destruct H. rewrite H in n. exfalso. apply n. auto. auto.
Qed.

Lemma mergeDSDom2NoChange: forall ds ds1 ds2 v,
    Result v = mergeDataStateFunc ds ds1 ds2 ->
    dom2 v = dom2 ds. 
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
    remember (mergeDataStateFunc ds ds1 ds2).
    destruct e3;inversion H1.
    subst. 
    destruct (range_typ_dec r0 r1).
    subst. inversion H1;simpl.
    f_equal.
    apply IHds with (ds1:=ds1) (ds2:=ds2);auto.
    destruct (range_typ_dec r0 r).
    subst.
    inversion H1;simpl. f_equal.
    apply IHds with (ds1:=ds1) (ds2:=ds2);auto.
    destruct (range_typ_dec r1 r).
    inversion H1;simpl. f_equal.
    apply IHds with (ds1:=ds1) (ds2:=ds2);auto.
    inversion H1.
Qed.

Lemma mergeConfigFuncDom2NoChange: forall M (conf conf1 conf2 : configuration M) v,
  Result v = mergeConfigFunc' conf conf1 conf2 ->
  dom2 (datastate conf) = dom2 (datastate v). 
Proof. intros.
       unfold mergeConfigFunc'  in H.
       remember (mergeDataStateFunc (datastate conf) (datastate conf1) (datastate conf2)).       destruct e;inversion H.
       remember (mergeControlStateFunc (controlstate conf) (controlstate conf1)
                                       (controlstate conf2)).
       destruct e;inversion H1.
       simpl.
       pose proof mergeDSDom2NoChange.
       symmetry. 
       apply H0 with (ds1:=(datastate conf1)) (ds2:=(datastate conf2));auto.
Qed.


Lemma innerCombineDSDom2: forall M (conf : configuration M) sceList v0  re c,
    correct_configuration conf ->
    incl sceList (dom (controlstate conf)) ->
    Result v0 = constructConfigList' sceList re conf ->
    Some c = innerCombineFunc'''' conf v0 ->
 
    dom2 (datastate conf) = dom2 (datastate c).
Proof.
  intros ?? sceList;induction sceList.
  - intros.
    simpl in H1. inversion H1;auto. subst. simpl in H2.
    inversion H2.
  - intros.
    simpl in H1.
    remember (constructConfig a re conf ). 
    destruct e;inversion H1.
    remember (constructConfigList' sceList re conf).
    destruct e;inversion H1.
    rewrite H5 in H2.
    simpl in H2.
    destruct v1.
    subst.
     remember (mergeConfigFunc' conf conf v).
    destruct e;inversion H2.
    apply mergeConfigFuncDom2NoChange with (conf1:=conf) (conf2:=v);auto.
    
    remember (innerCombineFunc'''' conf (c0::v1)).
    destruct o;inversion H2.
clear H6.     subst. remember (mergeConfigFunc' conf v c1).
    destruct e;inversion H2.
    subst.
    apply mergeConfigFuncDom2NoChange with (conf1:=v) (conf2:=c1);auto. 
   
Qed.

Lemma syncDSDom2: forall M (conf conf' : configuration M) e,
    correct_configuration conf ->
    synchrony conf conf' e ->
    dom2 (datastate conf) = dom2 (datastate conf').
Proof.
  intros.
  unfold synchrony in H0.
  destruct H0.
  unfold combineFunc in H1.
  remember (constructConfigList (dom (controlstate conf)) e conf ). 
  destruct e0;inversion H1.
  destruct v;inversion H3.
  clear H4. clear H1.
  remember (innerCombineFunc'''' conf (c::v)). 
  destruct o;inversion H3.
  unfold removeEventFromConf;simpl.
  simpl in Heqo.
  destruct v.
   remember (mergeConfigFunc' conf conf c).
  destruct e0;inversion Heqo. 
subst.  
  apply mergeConfigFuncDom2NoChange with (conf1:=conf) (conf2:=c);auto.

  remember (innerCombineFunc'''' conf (c1::v)). 
  destruct o;inversion Heqo.
clear H4.   unfold removeEventFromConf;simpl.
  
  remember (mergeConfigFunc' conf c c2). 
  destruct e0;inversion Heqo. subst. 
 
  apply mergeConfigFuncDom2NoChange with (conf1:=c) (conf2:=c2);auto.
  
Qed.

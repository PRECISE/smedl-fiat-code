(*
date: 04/09/2018
author: Teng Zhang
*)

(*definition of semantic rules*)

Require Import
  Coq.Strings.String
  Coq.Lists.List
  Coq.Bool.Bool
  Coq.Vectors.Vector
  Coq.ZArith.ZArith
  Coq.ZArith.Zdigits
  Coq.QArith.QArith_base
  Coq.QArith.Qabs
  Coq.FSets.FMapList
  Coq.FSets.FMapFacts
  Coq.Init.Notations
  Coq.omega.Omega.

Require Import Coq.Sorting.Permutation.
Require Export SmedlAST_submission.
Require Export SMEDL_helper.

Set Implicit Arguments.
Set Boolean Equality Schemes.

Unset Strict Implicit.
Unset Printing Implicit Defensive.
Generalizable All Variables.

Require Import Coq.Strings.Ascii.

Section semantic_rule.

(*from state of the state machine and the event instance, get the current step*)
  Definition stepStateMap := (scenario_state*event_instance)->option step.
  
  Definition stepStateMap' := (scenario_state*event_instance*scenario)->option (step).
  
(*construct stepStateMap*)
Definition update_stepStateMap (map: stepStateMap) (key: scenario_state*event_instance) (value: option step): stepStateMap :=
fun (key':scenario_state*event_instance) => if string_dec (fst key') (fst key) 
                                                                          then if event_instance_dec (snd key') (snd key) 
                                                                                     then value 
                                                                                  else map key' 
                                                                       else map key'.


(*given scenario state and event definition, return corresponding list of event_instances*)
Definition transitionEventMap := (option scenario_state* option event_definition) -> list event_instance.
(*construct transtionCondtionMap*)
Definition update_transitionEventMap (map:transitionEventMap) (key:option scenario_state* option event_definition) (value: event_instance) : transitionEventMap :=
fun (key': option scenario_state*option event_definition) => 
match fst key', snd key', fst key, snd key with
| Some fk',Some sk', Some fk,Some sk => if string_dec (fk') (fk) 
                                 then if  string_dec (eventId (sk)) (eventId (sk')) 
                                                  then value::(map key) 
                                          else map key'
                         else map key'
| _,_,_,_ =>map key'
end.

(*map from state to its possible triggering event*)
Definition stateEventDefMap := option scenario_state -> list event_definition.
Definition update_stateEventDefMap (map:stateEventDefMap) (key:option scenario_state) (ev: event_definition) : stateEventDefMap :=
fun (key': option scenario_state) => match key' with
                                                        | None => nil
                                                        | Some s => match key with
                                                                            | None => nil
                                                                            | Some s' => if string_dec s s' then ev::(map (key')) else map key'
                                                                            end
                                                        end
.


Print object.
Print find. 

Definition getStepFromMap (mon:object) (e:scenario_state*event_instance) : option step
  := match find (fun (x:(scenario_state * event_instance * option step)) => if string_dec (fst (fst x)) (fst e)
                               then
                                 if (event_instance_dec (snd (fst x)) (snd e))
                                 then
                                   true
                                 else
                                   false
                               else
                                 false
                ) (stateEvStepMap mon) with
     | Some (s, ei, x) => x
     | None => None
     end. 


(*environment*)
(*scenario_state -> list event_definition*)
Parameter stEvMap: stateEventDefMap.
(*scenario_state*event_definition -> list event_instance*)
Parameter transEvMap : transitionEventMap.
(*scenario_state*event_instance -> option step*)
Parameter stpStMap': stepStateMap'.
Parameter stpStMap: stepStateMap. 
Parameter eventList: list event_definition. 
 
(*data structure*)

(*used in configuration*)
(*data structure to represent the event raised*)
(*pathE*)

Definition monitor : Set := object.

(*current state of the monitor*)
Record configuration (M : monitor) : Type :={
  datastate : value_env;
  controlstate : scenario_env; 
  raisedevents :  list raisedEvent; (*all raised events, removed after being handled*)
  exportedevents: list raisedEvent; (*only for exported events*)
  finishedscenarios: list scenario;(*no change, using more strict definition*)
  sceEventMap: list (scenario*event_definition);
}.

Definition sceEventMap_dec (n m : list (scenario*event_definition)) : {n = m} + { n <> m}.
Proof. pose proof scenario_dec. pose proof event_definition_dec. repeat decide equality.  
Qed.



Definition configuration_dec {M : monitor} (n m : configuration M) : {n = m} + { n <> m}.
Proof. pose proof expr_eq_dec. repeat decide equality.  
Qed. 

Definition scenarioInclusion `(conf: configuration M) : Prop:=
incl  (finishedscenarios conf) (dom (controlstate conf)).


(*we assume that state update only updates state variables so that domain of (datastate conf) will never change, meaning 
uniq (datastate conf) always holds
Another assumption is that the update will follow the typechecking rule of normal programming languages*)

Inductive evnConsist : typ_env -> value_env -> Prop :=
| e_con_base: evnConsist nil nil
| e_con_ind: forall n (ty:typ) v te ev, evnConsist te ev -> evnConsist (((AIdent n),ty)::te) (((AIdent n),(ty,v))::ev).

Definition tyEnvPair (t:typ) (r:range_typ) :=
      match (t,r) with
        | (Int, (inl (inl (inl (inl _))))) => True
        | (Float, (inl (inl (inl (inr _))))) => True
        | (Str, (inl (inl (inr _)))) => True
        | (Bool, (inl (inr _))) => True
        | (Pointer, (inr _)) => True
        | (Thread, (inr _)) => True
        | (Opaque, (inr _)) => True                         
        | _ => False
      end.            

Inductive tyEnv: value_env -> Prop :=
| ty_base: tyEnv nil
| ty_ind: forall n t r ve, tyEnv ve -> tyEnvPair t r -> tyEnv (((AIdent n),(t,r))::ve).
                                                             
Lemma tyEnvApp: forall v1 v2,
    tyEnv v1 ->
    tyEnv v2 ->
    tyEnv (v1++v2).
Proof. 
  intro v1;induction v1.
  -
    intros. simpl. 
    auto. 
  -
    intros.
    SearchAbout app.
    rewrite <- app_comm_cons.
    
    inversion H; subst.
    apply ty_ind;auto. 
Qed.

Lemma valConsist: forall env t_env   s ty,
    evnConsist t_env env ->
    tyEnv env ->
    HasTy t_env (EAtom (AIdent s)) ty ->
    (exists v, In (AIdent s, (ty, v)) env).
Proof.
  intro env;induction env.
  -  intros. inversion H. subst. inversion H1.
     subst. SearchAbout find. apply find_some in H3.
     destruct H3. inversion H2.
  - intros.
    inversion H;inversion H0;subst.
    inversion H1.
    subst. simpl.
    inversion H6;subst. simpl in H3.
    destruct (atom_eq_dec (AIdent n) (AIdent s)). inversion e;subst.
    inversion H3;subst. exists v;left;auto.
    assert (exists v0 : range_typ, In (AIdent s, (ty, v0)) env).
    apply IHenv with (t_env:=te);auto.
    apply HasTy_Var;auto.
    destruct H2. exists x;right;auto. 
Qed.

Lemma domIn: forall (A B:Type) (s:A) (x:B) env,
In  (s,x) env ->
In s (dom env).
Proof. intros.
generalize dependent s. 
generalize dependent x.
induction env;intros.
- inversion H.
- destruct H. rewrite H. left;auto.
simpl. right. apply IHenv with (x:=x). auto.
Qed.

Lemma  getValueIn: forall ds s v t,  uniqList (dom ds) -> In ((AIdent s), (t, v)) (ds) -> getValue (AIdent s) ds = Some v.
Proof. intros. 
induction ds. inversion H0. 
simpl. destruct a;auto.
simpl. destruct p;auto. 
 
destruct (atom_eq_dec (AIdent s) a).
subst.  inversion H;subst. simpl in H0. destruct H0.
inversion H0;auto. apply domIn in H0.  contradiction.
apply IHds. inversion H;auto. simpl in H0.
destruct H0. inversion H0;subst. contradiction. 
auto. 
Qed.

Lemma tyEnvIn: forall ve s ty x,
    In (AIdent s, (ty, x)) ve ->
    tyEnv ve ->
    tyEnvPair ty x. 
Proof. intro ve. 
  induction ve;intros. 
- inversion H. 
- inversion H0;subst.
  inversion H. inversion H1;subst. 
  auto.   
  apply IHve with (s:=s);auto. 
Qed.

Check dom.



Record correct_configuration `(conf: configuration M) : Prop :={
(*ds_uniq: uniq (datastate conf);*)
(*ds_type_check : forall prod, In prod (datastate conf) -> typeCheck prod;*)
cs_non_empty: dom (controlstate conf)<> nil;
sce_state_no_empty: forall sce, In sce (dom (controlstate conf)) -> getScenarioState sce (controlstate conf) <> None;
finish_uniq: uniqList (finishedscenarios conf);
cs_dom_uniq: uniqList (dom (controlstate conf));
inclusion: scenarioInclusion conf;
correct_mon : correct_object M;
ds_tyEnv:tyEnv (datastate conf);
raise_in: (forall e, In e (raisedevents conf) -> In (eventDefinition e) (events M));
(*export_in: (forall e, In e (exportedevents conf) -> In (eventDefinition e) (events (monitor_obj conf)));*)
cs_consist: dom (controlstate conf) = (scenarios M);
(*cs_state_consist: forall sce st e0 s0, In (sce,st) (controlstate conf) -> In (st, e0, Some s0) (stateEvStepMap (monitor_obj conf)) -> (In s0 (traces sce) /\  (pre_state s0 = st));
cs_state_consist': forall sce st e0 s0,  In st (sceStateRelation sce) -> In (st, e0, Some s0) (stateEvStepMap (monitor_obj conf)) -> (In s0 (traces sce) /\  (pre_state s0 = st));
sce_state_in: forall sce st, In (sce,st) (controlstate conf) -> In st (sceStateRelation sce);*)
ds_dom_eq: (dom2 (datastate conf)) = ((dsmon M));
ds_consist: evnConsist (dsmon M) (datastate conf);
raised_wellform': forall e,  In e (raisedevents conf) ->
                             wellFormedRaisedEvent e;
raisedType: forall re, In re (raisedevents conf) -> eventKind (eventDefinition re) = Internal \/ eventKind (eventDefinition re) = Imported;
sceStateCorrect: forall sce s, In (sce,s) (controlstate conf) -> In (sce, s) (stateScenarioMap M);
sceEventMapRange : Permutation (dom (sceEventMap conf)) (finishedscenarios conf);
sceEventMapAlphabet:  forall sce e, In (sce,e) (sceEventMap conf) -> In e (alphabet sce);
raise_in_finished: forall sce e,  In (sce,e) (sceEventMap conf) -> In e (events M);
raisedType_finished: forall sce e, In (sce,e) (sceEventMap conf)-> eventKind e = Internal \/ eventKind e = Imported;
(*ds_ty_eq: (forall n t1 t2, In (n,t1) (dom2 (datastate conf)) -> (In (n,t2) ( (dsmon (monitor_obj conf)))) -> t1 = t2)*)
(*sceEventMapRange:  dom (sceEventMap conf) = (finishedscenarios conf);*)
                                                            }.




Definition importEventBool (ev:event_definition) : bool := 
if  (eventKind_dec (eventKind ev) Imported) then true else  false.

Print transitionEventMap.
Print object.

Definition op_string_dec (n m : option string) : {n = m} + { n <> m}.
Proof.  destruct n. destruct m. pose proof string_dec.
        destruct H with (s1:=s) (s2:=s0).   left;auto. rewrite e ;auto. 
        right. unfold not. intros. inversion H0. contradiction.
        right. unfold not. intros. inversion H.
        destruct m.
        right. unfold not. intros. inversion H.
        left;auto. 
Defined.


Definition op_event_definition_dec (n m : option event_definition) : {n = m} + { n <> m}.
Proof.
  destruct n;destruct m.
  pose proof event_definition_dec.
  destruct H with (n:=e) (m:=e0);auto. left. rewrite e1;auto. 
  right. unfold not. intros. inversion H0. contradiction.
  right. unfold not. intros. inversion H.
  right. unfold not;intros;inversion H. left;auto. 
 
Defined. 

Fixpoint transEvMapFunc 
          (l : list  (option scenario_state * option event_definition *
                      list event_instance)) (f: (option scenario_state * option event_definition)) :  option (list event_instance) :=
  match l with
  | nil => None
  | ((a, b),c) :: l' => if op_string_dec a (fst f) then
                          if op_event_definition_dec b (snd f) then
                            Some c
                          else
                            transEvMapFunc l' f
                        else
                          transEvMapFunc l' f
  end.

Fixpoint transEvMapFunc' 
          (l : list  (option scenario_state * option event_definition *
                      list event_instance)) (f: (option scenario_state * option event_definition)) :   (list event_instance) :=
  match l with
  | nil => nil
  | ((a, b),c) :: l' => if op_string_dec a (fst f) then
                          if op_event_definition_dec b (snd f) then
                             c
                          else
                            transEvMapFunc' l' f
                        else
                          transEvMapFunc' l' f
  end. 

Print object.

Definition transEvMapFuncMon (mon: object)
          (f: (option scenario_state * option event_definition)) :  option (list event_instance) :=
    transEvMapFunc (stateEvDefInstanceMap mon) f. 

Print dom2.



Lemma stateEvDefInstanceMapEquiv' : forall (l : list  (option scenario_state * option event_definition *
                      list event_instance)),
  uniqList (dom l) ->  (forall st ev eList, In (Some st, Some ev, eList) l
                       <-> transEvMapFunc l (Some st, Some ev) = Some eList). 
Proof.
  intro l;induction l.   
  - split.  intros. 
     inversion H0.     intros. simpl in H0. inversion H0. 
  - intros.
    simpl in H.
    split;intros.
    inversion H0. subst. 
    simpl. 
    simpl in *.
    
    destruct (string_dec st st);auto. Focus 2. contradiction.
    destruct (event_definition_dec ev ev). Focus 2. contradiction. auto. 
    (*Check eq_rec_r. 
    destruct (eq_rec_r (fun s : string => {Some s = Some st} + {Some s <> Some st}) (left eq_refl) e).
    Focus 2. contradiction.
    destruct (eq_rec_r (fun s : string => {Some s = Some st} + {Some s <> Some st}) (left eq_refl)).   Focus 2. contradiction. 
    
    destruct (op_string_dec (Some st) (Some st)).
    destruct (op_event_definition_dec (Some ev) (Some ev)).
     auto.     
     contradiction.
     contradiction.*)
    
     simpl.
     destruct a. destruct p.
     destruct (op_string_dec o (Some st)).
     subst.
     destruct (op_event_definition_dec o0 (Some ev)).
     simpl in H. inversion H;subst.
     SearchAbout dom.
     apply domIn in H1. contradiction. apply IHl;auto. inversion H;subst. auto.
     apply IHl;auto. inversion H;subst. auto.
     simpl in *.
     destruct a;destruct p.
     destruct (op_string_dec o (Some st)).
     destruct (op_event_definition_dec o0 (Some ev)).
     subst. 
     simpl in H. inversion H0;subst. left;auto.
     subst. apply IHl in H0. right;auto.
     inversion H;subst;auto.
     apply IHl in H0. right;auto.
     inversion H;subst;auto.
Qed.
Print object.
Print stepStateMap'.

Definition op_stpMap_dec (n m :  (scenario_state * event_instance * scenario)) : {n = m} + { n <> m}.
Proof.
  destruct n;destruct m. destruct p;destruct p0.
  pose proof string_dec. pose proof event_instance_dec.
  pose proof scenario_dec.
  destruct H with (s1:=s1) (s2:=s2); destruct H0 with (n:=e) (m:=e0); destruct H1 with (n:=s) (m:=s0);auto. left. rewrite e1;rewrite e2;rewrite e3;auto. right. unfold not. intros.
  inversion H2. contradiction.
right. unfold not. intros.
inversion H2. contradiction.
right. unfold not. intros.
inversion H2. contradiction.
right. unfold not. intros.
inversion H2. contradiction.
right. unfold not. intros.
inversion H2. contradiction.
right. unfold not. intros.
inversion H2. contradiction.
right. unfold not. intros.
  inversion H2. contradiction.
Defined. 

Fixpoint stpStpMapFunc (l : list (scenario_state * event_instance * scenario * option step))
         (f: (scenario_state * event_instance * scenario)) : option step :=
  match l with
 |  nil => None
 | (a,d)::l' => if op_stpMap_dec a f then
                  d
                else
                  stpStpMapFunc l' f
 end. 

Print object. 
  
Definition stpStpMapFuncMon (mon: object)
          (f: (scenario_state * event_instance * scenario)) :  option step :=
    stpStpMapFunc (stateEvStepMap'  mon) f. 
                                                               
Lemma stpStMapEquivLem: forall l,
  uniqList (dom l) -> (forall st ei stp sce, In (st,ei,sce,Some stp) l <-> stpStpMapFunc l (st, ei,sce) = Some stp).
Proof.
  intro l;induction l.   
- split;intros. 
  inversion H0. simpl in H0. 
  inversion H0. 
-
  split;intros.
  simpl in H0.
  destruct H0;subst.
  simpl.
  destruct (string_dec st st). destruct (event_instance_dec ei ei ).
  destruct (scenario_dec sce sce ). auto. contradiction. contradiction. contradiction. 
 (* destruct (op_stpMap_dec (st, ei, sce) (st, ei, sce)). auto. 
  contradiction.*)   
  inversion H;subst. 
  destruct a. simpl in *. 
  destruct (op_stpMap_dec p (st, ei, sce)).
  subst.
  inversion H;subst.
  apply domIn in H0. contradiction. 
  apply IHl;auto.
  simpl in *.
  destruct a.
  subst.
  destruct (op_stpMap_dec p (st, ei, sce)).
  subst. left;auto. 
  apply IHl in H0. right;auto. 
  inversion H;subst;auto.   
Qed.

Fixpoint getEventInstances' (ev:event_definition) (sce_env: scenario_env) (sceList: list scenario) (l : list  (option scenario_state * option event_definition *
                      list event_instance)): list event_instance :=
match sce_env with
| nil => nil
| (s,state)::env'=>   if inList scenario_dec s (sceList)  then 
                                (getEventInstances' ev env' sceList l) 
                      else
                        match (transEvMapFunc l (Some state, Some ev)) with
                        | None => (getEventInstances' ev env' sceList l)
                        | Some l' => 
                          mergeList' l' (getEventInstances' ev env' sceList l) (event_instance_dec)
                       end
end. 


Definition getEventInstances (ev:event_definition) `(conf: configuration M) (l : list  (option scenario_state * option event_definition *
                      list event_instance)) : list event_instance :=
getEventInstances' ev (controlstate conf) (finishedscenarios conf) l.


(*get all variables from an expression*)
Fixpoint getVariables (e:expr) : list atom :=
match e with
| EOr x y => mergeList' (getVariables x) (getVariables y) (atom_eq_dec)
| EAnd x y => mergeList' (getVariables x) (getVariables y) (atom_eq_dec)
| EEq x y  => mergeList' (getVariables x) (getVariables y) (atom_eq_dec)
| ELt x y => mergeList' (getVariables x) (getVariables y) (atom_eq_dec)
| ELe x y => mergeList' (getVariables x) (getVariables y) (atom_eq_dec)
| EPlus x y => mergeList' (getVariables x) (getVariables y) (atom_eq_dec)
| EMult x y => mergeList' (getVariables x) (getVariables y) (atom_eq_dec)
| EDiv x y => mergeList' (getVariables x) (getVariables y) (atom_eq_dec)
| EMod x y => mergeList' (getVariables x) (getVariables y) (atom_eq_dec)
| ENot x => getVariables x
| EAtom x => match x with 
                     | AIdent i => (AIdent i)::nil
                     | _ => nil
                     end           
end.

Fixpoint getUpdated (a:  action) : list atom :=
match a with
| StateUpdate (LExp (AIdent s)) ex =>  (AIdent s)::nil
| Seq a1 a2 => let r1 := getUpdated a1 in
                 let r2 :=  getUpdated a2 in
                 mergeList' r1 r2 (atom_eq_dec)
| _ => nil                            
end.

Fixpoint getVarsFromExprList (lst: list expr): list atom := 
match lst with
| nil => nil
| e::lst' => mergeList' (getVariables e) (getVarsFromExprList  lst') (atom_eq_dec)   
end.


Fixpoint getUsedFromActions (a: action) : list atom :=
  match a with
  | StateUpdate (LExp (AIdent s)) ex => (getVariables ex)
                                                   
  | RaiseStmt n lst =>  (getVarsFromExprList lst)                     
  | Seq a1 a2 => let r1 := getUsedFromActions a1 in
                 let r2 :=  getUsedFromActions a2 in
                 mergeList' r1 r2 (atom_eq_dec)
  | _ => nil                         
  end.                         
        

 
 

Definition getUpdatedVariablesFromScenario `(conf:configuration M) (stp:step)  : list atom
:= filterListReverse (dom (datastate conf)) (getUpdated (stepActions stp)) (atom_eq_dec).

Definition getUsedVariablesFromScenario `(conf:configuration M) (stp:step)  : list atom
:= 
filterListReverse (dom (datastate conf)) (mergeList' (getVariables (eventWhenExpr (stepEvent stp))) (getUsedFromActions (stepActions stp)) (atom_eq_dec)) (atom_eq_dec)
.


Definition getStep  `(conf: configuration M) (sce: scenario) (e: event_instance) : option step := 
match getScenarioState sce (controlstate conf) with
| None => None
| Some s =>  stpStMap (s,e)
end.

(*Definition getStep'  `(conf: configuration M) (sce: scenario) (e: event_instance) : option (step) := 
match getScenarioState sce (controlstate conf) with
| None => None
| Some s =>  stpStMap' (s,e,sce)                      
end.*)
Print object.

Definition getStep'  `(conf: configuration M) (sce: scenario) (e: event_instance) : option (step) := 
match getScenarioState sce (controlstate conf) with
| None => None
| Some s =>  stpStpMapFunc (stateEvStepMap' M) (s,e,sce)                      
end.

Definition getStep''  `(conf: configuration M) (sce: scenario) (e: event_instance) : option step := 
match getScenarioState sce (controlstate conf) with
| None => None
| Some s =>  getStepFromMap M (s,e)
end.

(*Definition stpStMapEquiv (mon:object) :=
  (forall st ei stp, In (st,ei,Some stp) (stateEvStepMap mon) <-> stpStMap (st, ei) = Some stp).*)




  (*uniqList (dom2 (stateEvStepMap mon))*)
  (* destruct ((stateEvStepMap mon)). inversion H.
         simpl.
         simpl in H.
         destruct H. rewrite H. 
         simpl. destruct (string_dec st st).
         destruct (event_instance_dec ei ei). auto.
         contradiction. contradiction.
         
         Print getStepFromMap.
         *)

Local Open Scope Z_scope.
Local Open Scope string_scope.







(*(a: atom) (t: typ) (v: range_typ) (en:value_env):*)
(*Fixpoint getValue (a: atom) (en:value_env) : option range_typ :=*)
(*semantics function*)
(*assume that n will be in the set of state variables*)
Print value_env.
Print typ_env.




Fixpoint updateDataState (ven:value_env) (lst: list atom) : value_env :=
match ven with
| nil =>  nil
| (a,v)::ven' => if (inList atom_eq_dec a (lst)) then (a,v)::(updateDataState ven' lst) else (updateDataState ven' lst)
end. 

Definition updateControlState (cs:scenario_env) (sce: scenario) (stp: step) :scenario_env := 
updateScenarioState' sce (pro_state stp) cs.

 

Fixpoint removeEvent' (re : raisedEvent) (lst : list raisedEvent) : list raisedEvent :=
match lst with
| nil => nil
| re' :: lst' => if raisedEvent_dec re re' then removeEvent' re lst' else re'::(removeEvent' re lst')
end. 


(*update configuration*)
Print configuration.

Definition configTransition  (env:value_env) (re:raisedEvent) (e:event_instance) (sce : scenario) (stp: step) `(conf: configuration M) : @ErrorOrResult (configuration M) := 
match (execAction (env,nil) (stepActions stp) (filter
             (fun e : event_definition =>
              match eventKind e with
              | Internal => true
              | Imported => false
              | Exported => true
              end) (events M))) with
| Error s => Error s
| Result (ds',res) => let ds'':= updateDataState ds' (dom (datastate conf)) in
                      Result ({|
datastate := ds'';
controlstate := updateControlState (controlstate conf) sce stp;
(*raisedevents := app (filter (fun re => EventKind_beq (eventKind (eventDefinition re)) Internal) res) (removeEvent' re ((raisedevents) conf));
exportedevents := app (filter (fun re => EventKind_beq (eventKind (eventDefinition re)) Exported) res) (exportedevents conf);*)
raisedevents :=  (filter (fun re => EventKind_beq (eventKind (eventDefinition re)) Internal) res) ;
exportedevents := (filter (fun re => EventKind_beq (eventKind (eventDefinition re)) Exported) res);
finishedscenarios := sce::nil;
sceEventMap := (sce,(eventDefinition re))::nil;
                                                    
|})
end.



(*here we require existance of eventWhenExpr for the reason that multiple event_instances may correspond to this raised event.
We could add  guard expressions to each event. For one without when, we could add a true
*)
Fixpoint findEventInstance (re:raisedEvent) (en:value_env) (elist: list event_instance): option event_instance :=
match elist with
| nil => None
| e::lst' => let ex_env := createValueEnv (eventArgs e) (eventParams (eventDefinition re)) (eventArguments re) in
                 match ex_env with
                   | Result (env) => let extend_env := (extendValEnv (en) (env)) in                   
                                              match evalMonad extend_env (eventWhenExpr e) with
                                              | Result (inl (inr true)) =>Some e
                                              | Result (inl (inr false)) => findEventInstance re en lst'
                                              |_ => None                                                
                                              end
                  | _ => None
                end
end.

Print object.

(*basic rule*)
Definition constructConfig (sce: scenario) (re: raisedEvent)  `(conf : configuration M) : ErrorOrResult:=
let sce_state := (getScenarioState sce (controlstate conf)) in
                     match sce_state with
                    | None =>  (Error error1)
                    | Some state =>  
                       match (transEvMapFunc (stateEvDefInstanceMap M)  (Some state , Some (eventDefinition re))) with
                                 | None => Error error3
                                 | Some le => 
                               let e' :=  findEventInstance re (datastate conf) le in
                          match e' with 
                          | None =>  Error error3
                          | Some e => 
                            let ex_env' := createValueEnv (eventArgs e) (eventParams (eventDefinition re)) (eventArguments re) in 
                            match ex_env' with
                            |  (Error s) =>  (Error error12)
                            | Result (ex_env) => 
                            let extend_env := (extendValEnv (datastate conf) (ex_env) ) in
                               let stp:= (getStep' conf sce e) in match stp with 
                                  | None =>  (Error error4)
                                  | Some stp' =>  match configTransition extend_env re e sce stp' conf with
                                                                | Error s => Error error11
                                                                | Result s => Result s
                                                 end
                                   end         
                                  end
                             end
                     end
                   end
.

Print findEventInstance. 




Fixpoint constructConfigList' (scs: list scenario) (re: raisedEvent) `(conf : configuration M): ErrorOrResult :=
match scs with
| nil => Result (nil)
| sce::scenarios' => match constructConfig sce re conf with
                                | Result conf' => match constructConfigList' scenarios' re conf with                                                         | Error s => Error s
                                                          | Result (lst) =>  Result ( conf' :: lst)
                                                          end                           
                                | Error s => Error (s)
                              end

end.

(*core method in synchrony rule, find all state machines that can be triggered by re and execute transitions*)
Definition constructConfigList (scs: list scenario) (re: raisedEvent) `(conf : configuration M): ErrorOrResult :=
let scs' := (filterList (finishedscenarios conf) scs scenario_dec) in
let scs'' :=  filter (fun x => inList (event_definition_dec) (eventDefinition re) (alphabet x)) scs' in 
constructConfigList' scs'' re conf.


(*definition of an error configuration*)
Definition ErrConfig  (e: raisedEvent) `(conf: configuration M) :Prop:=
In e (raisedevents conf) -> (exists s, constructConfigList (dom (controlstate conf)) e conf = Error (s)). 

(*no data state conflicts*)
Definition noDataConflict  (dso ds1 ds2:value_env): Prop :=
forall s, In s (dom (dso)) -> 
(exists str, AIdent str = s) /\ ( (getValue s dso <> getValue s ds1) /\ (getValue s dso <> getValue s ds2) -> getValue s ds1 = getValue s ds2).

(*no control state conflicts*)
Definition noControlConflict (cso cs1 cs2 :scenario_env): Prop :=
forall s, getScenarioState s cso <> getScenarioState s cs1 -> getScenarioState s cso <> getScenarioState s cs2 -> getScenarioState s cs1 = getScenarioState s cs2.

(*no conflicts, used in the definition of synchrony rule*)
Definition noConflict {M : monitor} (originConf conf1 conf2: configuration M): Prop := noDataConflict (datastate originConf) (datastate conf1) (datastate conf2) 
                /\ noControlConflict (controlstate originConf) (controlstate conf1) (controlstate conf2). 

(*merge datastate*)
Fixpoint mergeDataStateFunc  (dso ds1 ds2:value_env) : ErrorOrResult :=
match dso, ds1, ds2 with
| (n1,(t1,v0))::lst0, (n2,(t2,v1))::lst1, (n3,(t3,v2))::lst2 => if atom_eq_dec n1 n2 then 
                                                                                           if atom_eq_dec n1 n3 then 
                                                                                                   if typ_eq_dec t1 t2 then 
                                                                                                        if typ_eq_dec t1 t3 then
                                              let r :=  mergeDataStateFunc lst0 lst1 lst2 in 
                                                match r with
                                                | Error s => Error s
                                                | Result lst =>  if range_typ_dec v1 v2 then  Result ((n1,(t1,v1))::lst)
                                                                                                                              else if ((range_typ_dec v1 v0)) then 
                                                                                                                              Result ((n1,(t1,v2))::lst)
                                                                                                                              else if ((range_typ_dec v2 v0)) then
                                                                                                                               Result ((n1,(t1,v1))::lst)
                                                                                                                              else Error error13
                      
                                                                  
                                               end
                                                else Error error5 else Error error5 else Error error5 else Error error5
| nil, nil, nil => Result nil
| _,_,_ => Error error6
end.

(*merge controlstate*)
Fixpoint mergeControlStateFunc  (cso cs1 cs2: scenario_env) : ErrorOrResult :=
match cso, cs1, cs2 with
| (sc0,s0)::lst0, (sc1,s1)::lst1, (sc2,s2)::lst2 => if scenario_dec sc0 sc1 then 
                                                                                           if scenario_dec sc0 sc2 then 
                                              let r :=  mergeControlStateFunc lst0 lst1 lst2 in 
                                                match r with
                                                | Error s => Error s
                                                | Result lst =>  if string_dec s1 s2 then  Result ((sc0,s1)::lst)
                                                                                                                              else if ((string_dec s1 s0)) then 
                                                                                                                              Result ((sc0,s2)::lst)
                                                                                                                              else  if ((string_dec s2 s0)) then Result ((sc0,s1)::lst)
                                                                                                                              else Error error14
          
                                                                  
                                               end
                                                else Error error7 else Error error7
| nil, nil, nil => Result nil
| _,_,_ => Error error6
end.


(*merge configuration*)

Local Open Scope list_scope.
     
Definition mergeConfigFunc {M : monitor} (config config1 config2 : configuration M):  @ErrorOrResult (configuration M) := 
let ds:= mergeDataStateFunc (datastate config) (datastate config1) (datastate config2) 
in match ds with
   | Error s => Error s
   | Result ds' => 
let cs:= mergeControlStateFunc (controlstate config) (controlstate config1) (controlstate config2) 
in  match cs with
   | Error s => Error s
   | Result cs' => 
let raisedEvents := mergeList' (raisedevents config1) (raisedevents config2) (raisedEvent_dec) in
let exportedEvents := mergeList' (exportedevents config1) (exportedevents config2) (raisedEvent_dec) in
let finishedEvents := (finishedscenarios config1) ++ (finishedscenarios config2) ++ (finishedscenarios config) in
let sceEventMaps :=  (sceEventMap config1) ++ (sceEventMap config2) ++ (sceEventMap config) in
Result ({|
datastate := ds';
controlstate :=cs';
raisedevents := raisedEvents;
exportedevents := exportedEvents;
finishedscenarios := finishedEvents;
sceEventMap := sceEventMaps;
|})
end
end.




Definition mergeConfigFunc' {M : monitor} (config config1 config2 : configuration M) : @ErrorOrResult (configuration M) := 
let ds:= mergeDataStateFunc (datastate config) (datastate config1) (datastate config2) 
in match ds with
   | Error s => Error s
   | Result ds' => 
let cs:= mergeControlStateFunc (controlstate config) (controlstate config1) (controlstate config2) 
in  match cs with
   | Error s => Error s
   | Result cs' => 
(*let raisedEvents := mergeList' (raisedevents config1) (raisedevents config2) (raisedEvent_dec) in
let exportedEvents := mergeList' (exportedevents config1) (exportedevents config2) (raisedEvent_dec) in*)
let raisedEvents := app (raisedevents config1) (raisedevents config2) in
let exportedEvents := app (exportedevents config1) (exportedevents config2)  in
let finishedEvents := (finishedscenarios config1) ++ (finishedscenarios config2)  in
let sceEventMaps :=  (sceEventMap config1) ++ (sceEventMap config2)  in
Result ({|
datastate := ds';
controlstate :=cs';
raisedevents := raisedEvents;
exportedevents := exportedEvents;
finishedscenarios := finishedEvents;
sceEventMap := sceEventMaps;
|})
end
end.


  
Fixpoint innerCombineFunc'' {M : monitor} (lst: list (configuration M)) (o1: configuration M) (o2: configuration M) : option (configuration M) := match lst with
  | conf::lst' => let v := mergeConfigFunc' o1 o2 conf in
                  match v with
                  | Result conf' => innerCombineFunc'' lst' o1 conf'
                  | Error  s => None
                  end
  | _ => None           
  end.


Fixpoint innerCombineFunc''' `(originconf: configuration M)  (confList: list (configuration M)): option (configuration M):=
  match confList with
  | conf' :: l =>  match innerCombineFunc''' originconf  l with                   
                    | Some c => match mergeConfigFunc' originconf c conf' with
                                 | Error s => None
                                 | Result rc => Some rc
                                end
                    | None => match mergeConfigFunc' originconf originconf conf' with
                              | Error s => None
                              | Result c => Some c
                              end
                   end
  | _ => None
  end.


Fixpoint innerCombineFunc'''' `(originconf: configuration M)  (confList: list (configuration M)) : option (configuration M) :=
  match confList with
  | conf' :: nil => match mergeConfigFunc' originconf originconf conf' with
                    | Error s => None
                    | Result c => Some c
                    end
  | conf' :: l => match innerCombineFunc'''' originconf  l with
                            | Some c =>  match  mergeConfigFunc' originconf conf' c with
                                          | Error s => None
                                          | Result rc => Some rc
                                         end
                            | None => None
                            end
  | _ => None                           
  end.

Print innerCombineFunc''''. 



(*Fixpoint innerCombineFunc'''' `(originconf: configuration M)  (confList: list (configuration M)) : option (configuration M) :=
  match confList with
  | conf' :: nil => match mergeConfigFunc' originconf originconf conf' with
                    | Error s => None
                    | Result c => Some c
                    end
  | conf' :: conf'' :: l => match innerCombineFunc'''' originconf  l with
                            | Some c =>  match  mergeConfigFunc' originconf conf' conf'' with
                                          | Error s => None
                                          | Result rc => match mergeConfigFunc' originconf rc c with
                                                         | Error s => None
                                                         | Result c => Some c
                                                         end
                                         end
                            | None => None
                            end
  | _ => None                           
  end.
*)





Fixpoint innerCombineFunc' `(originconf: configuration M) (conf: option (configuration M)) (confList: list (configuration M)) : ErrorOrResult :=

match conf with
| None => match confList with
                 | nil => Error error9
                 | conf'::confList' => innerCombineFunc' originconf (Some conf') (confList')
                end
| Some conf' => match confList with
                 | nil => Result conf'
                 | conf''::confList' =>  let rconf := innerCombineFunc' originconf (Some conf'') ( (confList'))  in
                                                  match rconf with
                                                  | Error s => Error s
                                                  | Result rc => mergeConfigFunc originconf conf' rc 
                                                  end
                end

end.


Definition removeEventFromConf (e:raisedEvent) `(conf:configuration M) : configuration M :=
   ({|
datastate := (datastate conf);
controlstate := (controlstate conf);
raisedevents := removeEvent' e ((raisedevents) conf);
exportedevents := (exportedevents conf);
finishedscenarios := (finishedscenarios conf);
sceEventMap := (sceEventMap conf);
|}).
             
Definition combineFunc  (e: raisedEvent) `(conf: configuration M): option (configuration M) := 

match constructConfigList (dom (controlstate conf)) e conf with
| (Error s) => None
| Result (lst) => match lst with
                         | nil => None
                         | lst' => match innerCombineFunc''''  conf lst' with
                                   | Some v => Some (removeEventFromConf e v)
                                   | None => None
                                   end
                        end
end
.

(*
(*merge datastate*)
Fixpoint mergeDataStateFunc  (dso ds1 ds2:value_env) : ErrorOrResult :=
match dso, ds1, ds2 with
| (n1,(t1,v0))::lst0, (n2,(t2,v1))::lst1, (n3,(t3,v2))::lst2 => if atom_eq_dec n1 n2 then 
                                                                                           if atom_eq_dec n1 n3 then 
                                                                                                   if typ_eq_dec t1 t2 then 
                                                                                                        if typ_eq_dec t1 t3 then
                                              let r :=  mergeDataStateFunc lst0 lst1 lst2 in 
                                                match r with
                                                | Error s => Error s
                                                | Result lst =>  if range_typ_dec v1 v2 then  Result ((n1,(t1,v1))::lst)
                                                                                                                              else if ((range_typ_dec v1 v0)) then 
                                                                                                                              Result ((n1,(t1,v2))::lst)
                                                                                                                              else if ((range_typ_dec v2 v0)) then
                                                                                                                               Result ((n1,(t1,v1))::lst)
                                                                                                                              else Error error13
                      
                                                                  
                                               end
                                                else Error error5 else Error error5 else Error error5 else Error error5
| nil, nil, nil => Result nil
| _,_,_ => Error error6
end.

(*merge controlstate*)
Fixpoint mergeControlStateFunc  (cso cs1 cs2: scenario_env) : ErrorOrResult :=
match cso, cs1, cs2 with
| (sc0,s0)::lst0, (sc1,s1)::lst1, (sc2,s2)::lst2 => if scenario_dec sc0 sc1 then 
                                                                                           if scenario_dec sc0 sc2 then 
                                              let r :=  mergeControlStateFunc lst0 lst1 lst2 in 
                                                match r with
                                                | Error s => Error s
                                                | Result lst =>  if string_dec s1 s2 then  Result ((sc0,s1)::lst)
                                                                                                                              else if ((string_dec s1 s0)) then 
                                                                                                                              Result ((sc0,s2)::lst)
                                                                                                                              else  if ((string_dec s2 s0)) then Result ((sc0,s1)::lst)
                                                                                                                              else Error error14
          
                                                                  
                                               end
                                                else Error error7 else Error error7
| nil, nil, nil => Result nil
| _,_,_ => Error error6
end.


(*merge configuration*)
Definition mergeConfigFunc (config config1 config2 : configuration):  ErrorOrResult:= 
let ds:= mergeDataStateFunc (datastate config) (datastate config1) (datastate config2) 
in match ds with
   | Error s => Error s
   | Result ds' => 
let cs:= mergeControlStateFunc (controlstate config) (controlstate config1) (controlstate config2) 
in  match cs with
   | Error s => Error s
   | Result cs' => 
let raisedEvents := mergeList' (raisedevents config1) (raisedevents config2) (raisedEvent_dec) in
let exportedEvents := mergeList' (exportedevents config1) (exportedevents config2) (raisedEvent_dec) in
let finishedEvents := mergeList' (finishedscenarios config1) (finishedscenarios config2) (scenario_dec) in
Result ({|
monitor_obj := (monitor_obj config);
datastate := ds';
controlstate :=cs';
raisedevents := raisedEvents;
exportedevents := exportedEvents;
finishedscenarios := finishedEvents;

|})
end
end.



Fixpoint innerCombineFunc' (originconf: configuration) (conf: option configuration) (confList: (list configuration)): ErrorOrResult:=

match conf with
| None => match confList with
                 | nil => Error error8
                 | conf'::confList' => innerCombineFunc' originconf (Some conf') (confList')
                end
| Some conf' => match confList with
                 | nil => Result conf'
                 | conf''::confList' =>  let rconf := innerCombineFunc' originconf (Some conf'') ( (confList'))  in
                                                  match rconf with
                                                  | Error s => Error s
                                                  | Result rc => mergeConfigFunc originconf conf' rc 
                                                  end
                end

end.



Definition combineFunc  (e: raisedEvent) (conf: configuration): ErrorOrResult := 

match constructConfigList (dom (controlstate conf)) e conf with
| (Error s) => Error s
| Result (lst) => match lst with
                         | nil => Error error9
                         | lst' =>  innerCombineFunc' conf None lst'
                        end
end
.

*)

Definition conflict (e: raisedEvent) `(conf: configuration M) :Prop:=
(exists clist, (constructConfigList (dom (controlstate conf)) e conf = 
Result (clist)) /\ exists conf1 conf2, In conf1 clist /\ In conf2 clist /\ ~(noConflict conf conf1 conf2)). 

(*combine configurations having same source configuration and same triggering event*)
Definition synchrony {M : monitor} (conf conf' :configuration M) (event:raisedEvent) : Prop :=
In event (raisedevents conf) /\ combineFunc event conf = Some (conf').

(*
Definition synchrony  (conf conf' :configuration) (event:raisedEvent) : Prop :=
In event (raisedevents conf) /\ ~(ErrConfig event conf ) /\  ~(conflict event conf) /\ combineFunc event conf = Result (conf').
 *)

(*initial configuration*)
Definition readyConfig  `(conf :configuration M) : Prop :=
correct_configuration conf /\ raisedevents conf = nil
/\ (exportedevents conf) = nil                                 
/\ (finishedscenarios conf) = nil
/\ (sceEventMap conf) = nil.

(*initial configuration*)
Definition initialConfig  `(conf :configuration M) : Prop :=
correct_configuration conf /\ (length (raisedevents conf) = S O) 
/\ (forall e,  In e (raisedevents conf) -> importedEvent (eventDefinition e)
/\ (exists sce, In sce (dom (controlstate conf)) 
/\ In (eventDefinition e) ((alphabet) sce)))
/\ (finishedscenarios conf) = nil
/\ (sceEventMap conf) = nil.

Print configuration.

Definition configStEq {M : monitor} (conf conf': configuration M) : Prop :=
  datastate conf = datastate conf' /\
  controlstate conf = controlstate conf'.
  
  
Definition configTrans {M : monitor} (conf conf': configuration M) : Prop :=
 readyConfig conf /\ initialConfig conf' /\ configStEq conf conf'. 

Definition configTransRev {M : monitor} (conf conf': configuration M) : Prop :=
 configStEq conf conf' /\ readyConfig conf'.
             
(*chain merge rule*)
Inductive chainMerge (M : monitor) : configuration M -> configuration M-> raisedEvent ->  Prop :=
| basic': forall conf conf' event, initialConfig conf ->  synchrony conf conf' event -> chainMerge conf conf' event
| chain': forall conf conf'' conf' event1 event2, chainMerge conf conf' event1 -> synchrony conf' conf'' event2-> chainMerge conf conf'' event1.

Inductive chainMergeStep (M : monitor) : configuration M -> configuration M-> raisedEvent -> nat -> Prop :=
| merge_basic: forall conf conf' event, (importedEvent (eventDefinition event)) ->  synchrony conf conf' event -> chainMergeStep conf conf' event O
| merge_chain: forall conf conf'' conf' event1 event2 n, chainMergeStep conf conf' event1 n -> synchrony conf' conf'' event2-> chainMergeStep conf conf'' event1 (S n).


(* transEvMap ((getScenarioState sce (controlstate conf)), Some (eventDefinition e))  = nil)
means that e is not in the alphabet of sce
SMEDL asks for the complete scenario, so if e is in the alphabet of 
sce, then transEvMap should always return a value
 *)

(*
Definition finalConfig (conf:configuration):Prop:=
correct_configuration conf /\ ((length (raisedevents conf) = O)  \/ (forall e  , In e (raisedevents conf) -> (~importedOrInternalEvent (eventDefinition e) 
/\  (forall sce, In sce (dom (controlstate conf)) /\ ~ (In sce (finishedscenarios conf)) -> transEvMap ((getScenarioState sce (controlstate conf)), Some (eventDefinition e))  = nil)))).
 *)

Definition finalConfig `(conf:configuration M):Prop:=
(length (raisedevents conf) = O)  \/  incl (dom (controlstate conf)) (finishedscenarios conf).

Definition chainMergeTrans {M : monitor} (conf conf' econf: configuration M) (e: raisedEvent) (rconf: configuration M)  (events: list raisedEvent)  : Prop :=
   configTrans conf conf' /\ chainMerge conf' econf e /\ finalConfig econf /\ configTransRev econf rconf /\ events = exportedevents econf.

                                                                                                
(*definition of stuck configuration*)
Definition stuckConfig `(conf:configuration M):Prop:=
  (forall e , In e (raisedevents conf) -> (~(exists conf', synchrony conf conf' e))).

(*equivlance relation between two configurations*)
Definition equivConf {M : monitor} (conf conf':configuration M) : Prop :=
(datastate conf) = (datastate conf') /\ (controlstate conf) = (controlstate conf')
/\ incl (raisedevents conf) (raisedevents conf') /\ incl (raisedevents conf') (raisedevents conf) /\ Permutation (finishedscenarios conf) (finishedscenarios conf')
/\ incl (exportedevents conf) (exportedevents conf') /\ incl (exportedevents conf') (exportedevents conf) /\ Permutation (sceEventMap conf) (sceEventMap conf').

(*equivConf is an equivalence relation*)
Lemma equivConf_Refl {M : monitor} : forall x : configuration M,
equivConf x x. 
Proof. intros. unfold equivConf;split;auto. repeat(try (split;auto)).
       unfold incl;intros;auto.
       unfold incl;intros;auto.

       unfold incl;intros;auto.
       unfold incl;intros;auto.
       
Qed.

Lemma equivConf_Sym {M : monitor} : forall x1 x2 : configuration M,
equivConf x1 x2 <-> equivConf x2 x1. 
Proof. intros. split.
- intros. unfold equivConf in H. 
    repeat match goal with
            | [ H: _ /\ _ |- _ ] => destruct H

            end. 
unfold equivConf. repeat(split;auto);repeat(apply Permutation_sym; auto).

- intros. unfold equivConf in H. 
    repeat match goal with
            | [ H: _ /\ _ |- _ ] => destruct H

           end.
    unfold equivConf. repeat(split;auto);repeat(apply Permutation_sym; auto).
Qed.     

Lemma equivConf_Trans {M : monitor} : forall x1 x2 x3 : configuration M,
equivConf x1 x2 -> equivConf x2 x3 -> equivConf x1 x3. 
Proof. intros. unfold equivConf in H. unfold equivConf in H0.
    repeat match goal with
            | [ H: _ /\ _ |- _ ] => destruct H

            end. 
    unfold equivConf. split;auto. rewrite H;auto.  split. rewrite <- H1;auto.
    split.
unfold incl in *. intros. apply H2. apply H9;auto.
split.
unfold incl in *. intros. apply H10. apply H3;auto.

split.

eapply Permutation_trans. apply H11. auto.
split. 

unfold incl in *. intros. apply H5. apply H12;auto.
split.
unfold incl in *. intros. apply H13. apply H6;auto.
eapply Permutation_trans. apply H14. auto.
Qed.


(*(*equivlance relation between two configurations*)
Definition equivConf {M : monitor} (conf conf':configuration M) : Prop :=
(datastate conf) = (datastate conf') /\ (controlstate conf) = (controlstate conf')
/\ Permutation (raisedevents conf) (raisedevents conf') /\ Permutation (finishedscenarios conf) (finishedscenarios conf')
/\ incl (exportedevents conf) (exportedevents conf') /\ incl (exportedevents conf') (exportedevents conf) /\ Permutation (sceEventMap conf) (sceEventMap conf').

(*equivConf is an equivalence relation*)
Lemma equivConf_Refl {M : monitor} : forall x : configuration M,
equivConf x x. 
Proof. intros. unfold equivConf;split;auto. repeat(try (split;auto)).
       unfold incl;intros;auto.
        unfold incl;intros;auto.
Qed.

Lemma equivConf_Sym {M : monitor} : forall x1 x2 : configuration M,
equivConf x1 x2 <-> equivConf x2 x1. 
Proof. intros. split.
- intros. unfold equivConf in H. 
    repeat match goal with
            | [ H: _ /\ _ |- _ ] => destruct H

            end. 
unfold equivConf. repeat(split;auto);repeat(apply Permutation_sym; auto).

- intros. unfold equivConf in H. 
    repeat match goal with
            | [ H: _ /\ _ |- _ ] => destruct H

           end.
    unfold equivConf. repeat(split;auto);repeat(apply Permutation_sym; auto).
Qed.     

Lemma equivConf_Trans {M : monitor} : forall x1 x2 x3 : configuration M,
equivConf x1 x2 -> equivConf x2 x3 -> equivConf x1 x3. 
Proof. intros. unfold equivConf in H. unfold equivConf in H0.
    repeat match goal with
            | [ H: _ /\ _ |- _ ] => destruct H

            end. 
    unfold equivConf. split;auto. rewrite H;auto.  split. rewrite <- H1;auto.
split. 
eapply Permutation_trans. apply H8. auto.
split. 
eapply Permutation_trans. apply H9. auto.
split.
unfold incl in *. intros. apply H4. apply H10;auto.
split.
unfold incl in *. intros. apply H11. apply H10;auto.
eapply Permutation_trans. apply H12. auto.
Qed.*)

End semantic_rule.


(*Fixpoint eventInPath (ev:event_definition) (lst: list event_definition): bool :=
match lst with
| nil => false
| ev'::lst' => if event_definition_dec ev ev' then true else eventInPath ev lst'
end. 

Fixpoint checkUpdateValue' (a:atom) (lst: list updatedVariable) (re:raisedEvent) : bool :=
match lst with
| nil => true
| v::lst' => if (atom_eq_dec a (up_var v)) then eventInPath (eventTag v) (pathEvents re) else checkUpdateValue' a lst' re
end. 


Fixpoint checkUsedValue'' (evList:list event_definition) (pathList: list event_definition) : bool :=
match evList with
| nil => true
| ev::lst' => if eventInPath ev pathList then checkUsedValue'' lst' pathList else false
end. 


Fixpoint checkUsedValue' (a:atom) (lst: list usedVariable) (re:raisedEvent) : bool :=
match lst with
| nil => true
| v::lst' => if (atom_eq_dec a (used_var v)) then checkUsedValue'' (used_eventTagList v) (pathEvents re) else checkUsedValue' a lst' re
end.

Print configuration. 


Fixpoint checkValue (conf:configuration) (re:raisedEvent) (lst: list atom)   : bool :=
match lst with
| nil => true
| a::lst' => if checkUpdateValue' a (updatedvariableList conf) re then checkValue conf re lst' else  false
end.

Fixpoint checkUpdatedUsedValue (conf:configuration) (re:raisedEvent) (lst: list atom) : bool :=
match lst with
| nil => true
| a::lst' => if checkUsedValue' a (usedvariableList conf) re then checkUpdatedUsedValue conf re lst' else  false
end.


Definition checkValueNonDeterminism (conf:configuration) (re:raisedEvent)  (stp:step) :bool :=
let usedVariables :=  getUsedVariablesFromScenario conf stp in
let updatedVariables := getUpdatedVariablesFromScenario conf stp in
checkValue conf re usedVariables &&  
checkValue conf re updatedVariables &&
checkUpdatedUsedValue conf re updatedVariables
.

Fixpoint updateUsedVariables' (lst: list usedVariable) (a: atom) (re:raisedEvent) : option usedVariable
:=
match lst with
| nil => None
| uv::lst' => if atom_eq_dec a (used_var uv) then 
   Some {|used_var := (used_var uv); used_eventTagList:= ( eventDefinition re) :: (used_eventTagList uv) |}
else updateUsedVariables' lst' a re
end. 


Fixpoint updateUsedVariables (lst: list usedVariable) (lstAtom: list atom) (re:raisedEvent)
:  list usedVariable := 
match lstAtom with
| nil => lst
| a::lstAtom' => match  (updateUsedVariables' lst a re) with
                        | None => (updateUsedVariables lst lstAtom' re)
                        | Some uv => uv :: (updateUsedVariables lst lstAtom' re)
                       end
end.


Fixpoint updatedVariable' (lst: list updatedVariable) (a: atom) (re:raisedEvent) : option updatedVariable
:=
match lst with
| nil => None
| uv::lst' => if atom_eq_dec a (up_var uv) then 
   Some {|up_var := (up_var uv); eventTag:= ( eventDefinition re) |}
else updatedVariable' lst' a re
end. 


Fixpoint updateUpdateVariables (lst: list updatedVariable) (lstAtom: list atom) (re:raisedEvent)
:  list updatedVariable := 
match lstAtom with
| nil => lst
| a::lstAtom' => match  (updatedVariable' lst a re) with
                        | None => (updateUpdateVariables lst lstAtom' re)
                        | Some uv => uv :: (updateUpdateVariables lst lstAtom' re)
                       end
end.

Fixpoint newUpdateVariables (lstAtom : list atom) (re:raisedEvent): list updatedVariable :=
match lstAtom with
| nil => nil
| a::lstAtom' => {|up_var := a; eventTag := eventDefinition re |} :: newUpdateVariables lstAtom' re
end.

Fixpoint newUsedVariables (lstAtom : list atom) (re:raisedEvent): list usedVariable :=
match lstAtom with
| nil => nil
| a::lstAtom' => {|used_var := a; used_eventTagList := (eventDefinition re)::nil |} :: newUsedVariables lstAtom' re
end.*)
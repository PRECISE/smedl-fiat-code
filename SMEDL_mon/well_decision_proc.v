(*auxiliary decision procedures for proving wellformedness of a monitor definition*)
(*Refer to Monitor_oni.v for application*)

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
Require Import Coq.Lists.ListDec. 



(*stateSceIn = 
fun mon : object =>
forall (sce : scenario) (s : scenario_state),
In sce (scenarios mon) ->
In (sce, s) (stateScenarioMap mon) <->
(exists step0 : step, In step0 (traces sce) /\ (pre_state step0 = s \/ pro_state step0 = s))*)
Fixpoint checkStepExists  s (lst: list step) : bool :=
  match lst with
  | nil => false
  | stp::lst' => if string_dec (pre_state stp) s then
                   true
                 else
                   if string_dec (pro_state stp) s then
                     true
                   else
                     checkStepExists s lst'
  end.


 
Lemma checkStepExists_cor: forall lst s ,
    checkStepExists s lst ->
    (exists step0 : step, In step0 lst /\ (pre_state step0 = s \/ pro_state step0 = s)). 
Proof.
  intro lst;induction lst. 
  - intros;simpl in *. inversion H. 
  - intros. 
    simpl in *.
    destruct (string_dec (pre_state a) s).
    exists a;split;intuition.
    destruct (string_dec (pro_state a) s). 
    exists a;split;intuition.
    apply IHlst in H;auto.
    destruct H. exists x;intuition. 
Qed.


Lemma checkStepExists_cor_rev: forall lst s ,
     (exists step0 : step, In step0 lst /\ (pre_state step0 = s \/ pro_state step0 = s)) ->
    checkStepExists s lst. 
Proof.
  intro lst;induction lst. 
  - intros;simpl in *. destruct H. destruct H. inversion H. 
  - intros. 
    simpl in *.
    destruct H.
    destruct H.
    destruct H;subst.
    destruct H0.
    rewrite H. 
    destruct (string_dec s s);auto.
    destruct ( string_dec (pre_state x) s);auto.
    rewrite H.
    destruct (string_dec s s);auto.
    destruct H0.
    destruct (string_dec (pre_state a) s).
    auto.
    destruct (string_dec (pro_state a) s);auto.
    apply IHlst;auto.
    exists x;intuition.
    destruct (string_dec (pre_state a) s);auto. 
    destruct (string_dec (pro_state a) s);auto.
    apply IHlst;auto. exists x;intuition. 
Qed.


Fixpoint checkStepExistsSce s sce (lst: list (scenario*scenario_state)) : bool :=
  match lst with
  | nil => false
  | (sce',s') :: lst' => if scenario_dec sce sce' then
                           if string_dec s s' then
                             true
                           else
                             checkStepExistsSce s sce lst'
                         else
                           checkStepExistsSce s sce lst'
  end.

Lemma checkStepExistsSce_rev_cor: forall lst s sce,
    In (sce, s) lst  ->
    checkStepExistsSce s sce lst. 
Proof.
  intro lst;induction lst;simpl in *;intros.
  - inversion H.
  - destruct H;subst.
    destruct (scenario_dec sce sce);
    destruct (string_dec s s);auto.  
    destruct a.
    apply IHlst in H;intuition;auto.
    destruct (scenario_dec sce s0);auto;
    destruct (string_dec s s1 );auto.   
Qed.

Lemma checkStepExistsSce_cor : forall lst s sce,
    checkStepExistsSce s sce lst ->
    In (sce, s) lst.
Proof.
  intro lst;induction lst;simpl in *;intros.
  - inversion H.
  - destruct a.
    destruct (scenario_dec sce s0). 
    destruct (string_dec s s1). 
    subst;left;auto. 
    right;apply IHlst;auto.
    right;apply IHlst;auto.
Qed.




Definition checkStepState stp (lst: list (scenario*scenario_state)) sce' : bool :=
  if checkStepExistsSce (pre_state stp) sce' lst then
    if checkStepExistsSce (pro_state stp) sce' lst then
      true
    else
      false
  else
    false. 



Lemma checkStepState_cor: forall lst stp sce ,
    checkStepState stp lst sce ->    
    In (sce, pre_state stp) lst /\  In (sce, pro_state stp) lst. 
Proof.
  intros. unfold checkStepState in H.
  remember (checkStepExistsSce (pre_state stp) sce lst).
  destruct b;inversion H.
  remember (checkStepExistsSce (pro_state stp) sce lst).
  destruct b;inversion H;auto.
  symmetry in Heqb;symmetry in Heqb0.
  apply checkStepExistsSce_cor  in Heqb;
  apply checkStepExistsSce_cor  in Heqb0;auto. 
Qed.

Lemma checkStepState_rev_cor: forall lst stp sce,
    In (sce, pre_state stp) lst ->
    In (sce, pro_state stp) lst ->
    checkStepState stp lst sce . 
Proof.
  intros. unfold checkStepState.
  apply checkStepExistsSce_rev_cor in H.
  apply checkStepExistsSce_rev_cor in H0.
  rewrite H;rewrite H0;auto.   
Qed.   
  
    

Fixpoint checkStepExistsList  (lst: list (scenario*scenario_state)) (stpList: list step) sce : bool :=
  match stpList with
  | nil => true
  | stp::lst' => if checkStepState stp lst sce then
                   checkStepExistsList lst lst' sce
                 else
                   false
  end.



Lemma checkStepExistsList_cor: forall stpList lst sce stp,
    checkStepExistsList lst stpList sce ->
    In stp stpList ->
    ( In (sce, pre_state stp) lst /\  In (sce, pro_state stp) lst).  
Proof.
  intro stpList;induction stpList;simpl in *;intros.
  - inversion H0.
  - remember (checkStepState a lst sce).
    destruct b.
    symmetry in Heqb.
    apply checkStepState_cor in Heqb;auto. destruct H0;subst. 
auto.     apply IHstpList with (stp:=stp) in H;auto. inversion H. 
Qed.


Lemma checkStepExistsList_rev_cor: forall stpList lst sce,
    
    (forall stp, In stp stpList ->
     ( In (sce, pre_state stp) lst /\  In (sce, pro_state stp) lst)) ->
    checkStepExistsList lst stpList sce.  
Proof.
  intro stpList;induction stpList;simpl in *;intros.
  - auto. 
  - assert (checkStepState a lst sce).
    assert (In (sce, pre_state a) lst /\ In (sce, pro_state a) lst).
    apply H;auto. destruct H0. 
    apply checkStepState_rev_cor;auto.
    rewrite H0;auto. 
   Qed.


Fixpoint checkStepExistsSceList sceList  (lst: list (scenario*scenario_state)) : bool :=
  match sceList with
  | nil => true
  | sce::lst' => if checkStepExistsList lst (traces sce) sce then
                     checkStepExistsSceList lst' lst
                 else
                     false
                
  end.




    
Fixpoint checkStateSceInScenarioMapLeft sce (lst: list (scenario*scenario_state)) : bool :=
  match lst with
  | nil => true
  | (sce',s)::lst' => if scenario_dec sce sce' then
                        if checkStepExists  s (traces sce) then
                          checkStateSceInScenarioMapLeft sce lst'
                        else
                          false
                      else
                        checkStateSceInScenarioMapLeft sce lst'
  end.




    

Lemma checkStateSceInScenarioMapLeft_cor: forall lst sce s,
    checkStateSceInScenarioMapLeft sce lst ->
    In (sce, s) lst ->
(exists step0 : step, In step0 (traces sce) /\ (pre_state step0 = s \/ pro_state step0 = s)). 
Proof.
  intro lst;induction lst;simpl in *;intros.
  - inversion H0.
  - destruct H0;subst.
    destruct (scenario_dec sce sce).     
    Focus 2. contradiction.
    remember (checkStepExists s (traces sce) ).
    destruct b;inversion H.
   symmetry in Heqb.     
   apply checkStepExists_cor in Heqb;auto.
   destruct a.
   destruct (scenario_dec sce s0);apply IHlst;auto.
   destruct (checkStepExists s1 (traces sce));inversion H; auto. 
Qed.




Lemma checkStateSceInScenarioMapLeft_cor_rev: forall lst sce,
    (forall s, In (sce, s) lst ->
    (exists step0 : step, In step0 (traces sce) /\ (pre_state step0 = s \/ pro_state step0 = s)))
    ->
checkStateSceInScenarioMapLeft sce lst. 
Proof.
  intro lst;induction lst;simpl in *;intros.
  - auto. 
  - destruct a.
    destruct (scenario_dec sce s);subst.
    pose proof checkStepExists_cor_rev.
    assert (checkStepExists s0 (traces s) = true).
    apply H0;auto.
    rewrite H1;auto.
    apply IHlst;auto. 
Qed.

     
Fixpoint checkStateSceInLeft (sceList: list scenario) (lst: list (scenario*scenario_state)) : bool :=
  match sceList with
  | nil => true
  | sce::lst' => if checkStateSceInScenarioMapLeft sce lst then
                   checkStateSceInLeft lst' lst
                 else
                   false
  end.


Lemma checkStateSceInLeft_cor: forall sceList lst,
    checkStateSceInLeft sceList lst ->
    forall (sce : scenario) (s : scenario_state),
In sce sceList ->
In (sce, s) lst ->
(exists step0 : step, In step0 (traces sce) /\ (pre_state step0 = s \/ pro_state step0 = s)). 
Proof.
  intro sceList;induction sceList;simpl in *;intros.
  - inversion H0.
  - destruct H0;subst.
    remember (checkStateSceInScenarioMapLeft sce lst). 
    destruct b. symmetry in Heqb.
   apply checkStateSceInScenarioMapLeft_cor with (s:=s) in Heqb;auto.
   inversion H.
     destruct (checkStateSceInScenarioMapLeft a lst);inversion H. 
     apply IHsceList with (lst:=lst);auto.
Qed.


Lemma checkStateSceInLeft_rev_cor: forall sceList lst ,
(forall sce s, In sce sceList ->
In (sce, s) lst ->
(exists step0 : step, In step0 (traces sce) /\ (pre_state step0 = s \/ pro_state step0 = s))) ->
checkStateSceInLeft sceList lst. 
Proof.
  intro sceList;induction sceList;simpl in *;intros.
  - auto. 
  - assert (checkStateSceInScenarioMapLeft a lst = true).
    apply checkStateSceInScenarioMapLeft_cor_rev;auto.
    rewrite H0;auto. 
    (*remember (checkStateSceInScenarioMapLeft sce lst). 
    destruct b. symmetry in Heqb.
   apply checkStateSceInScenarioMapLeft_cor with (s:=s) in Heqb;auto.
   inversion H.
     destruct (checkStateSceInScenarioMapLeft a lst);inversion H. 
     apply IHsceList with (lst:=lst);auto.*)
Qed.



Lemma checkStepExistsSceList_cor: forall sceList s lst,
    checkStepExistsSceList sceList lst ->
    (forall sce, In sce sceList ->
                 (exists step0 : step, In step0 (traces sce) /\ (pre_state step0 = s \/ pro_state step0 = s)) -> In (sce, s) lst ). 
Proof.
  intro sceList;induction sceList;simpl in *;intros.
  - inversion H0.
  -  destruct H0;subst.
     remember ( checkStepExistsList lst (traces sce) sce).   
     destruct b.
     symmetry in Heqb.
     destruct H1. destruct H0.  
     apply checkStepExistsList_cor with (stp:=x) in Heqb;auto.
     destruct Heqb. 
     destruct H1;subst. auto. auto.
     inversion H.
     destruct (checkStepExistsList lst (traces a) a);inversion H;apply IHsceList;auto.
   
Qed.



Lemma checkStepExistsSceList_cor_rev: forall sceList  lst,
    (forall sce stp, In sce sceList ->
                 In stp (traces sce) -> In (sce, pre_state stp) lst /\ In (sce, pro_state stp) lst)  ->
    checkStepExistsSceList sceList lst. 
Proof.
  intro sceList;induction sceList;simpl in *;intros.
  - auto. 
  -
    assert (checkStepExistsList lst (traces a) a = true).
    apply checkStepExistsList_rev_cor;auto.
    
    rewrite H0;auto.
  Qed.

    
Lemma stateSceIn_dec: forall mon,
    checkStateSceInLeft (scenarios mon) (stateScenarioMap mon) ->
    checkStepExistsSceList (scenarios mon) (stateScenarioMap mon) ->
    stateSceIn mon. 
Proof.
  intros.
  unfold stateSceIn.
  intros.
  split.
  apply checkStateSceInLeft_cor with ( (scenarios mon));auto.
  apply checkStepExistsSceList_cor with ( (scenarios mon));auto.
Qed.


Lemma stateSceIn_dec_rev: forall mon,
    stateSceIn mon ->
    checkStateSceInLeft (scenarios mon) (stateScenarioMap mon) .

Proof.
  intros. unfold stateSceIn in H.
  apply checkStateSceInLeft_rev_cor;auto.
  intros.
  apply H;auto. 
Qed.

Lemma stateSceIn_dec_rev': forall mon,
    stateSceIn mon ->
    checkStepExistsSceList (scenarios mon) (stateScenarioMap mon) .
Proof.
  intros. unfold stateSceIn in H.
  apply checkStepExistsSceList_cor_rev;auto.
  intros. split;apply H;auto.
  exists stp;auto. 
  exists stp;auto.
Qed.

Lemma stateSceIn_dec_all: forall mon,
    stateSceIn mon <->
    (checkStateSceInLeft (scenarios mon) (stateScenarioMap mon)
     /\  checkStepExistsSceList (scenarios mon) (stateScenarioMap mon) ).
Proof.
  intros;split;auto;intros.   
  split.   
  apply stateSceIn_dec_rev;auto. 
  apply  stateSceIn_dec_rev';auto.
  apply stateSceIn_dec;intuition;auto. 
Qed. 

  (*stateSceProp = 
fun mon : object =>
forall (s : scenario_state) (e : event_definition) (l : list event_instance) (sce : scenario),
In (Some s, Some e, l) (stateEvDefInstanceMap mon) ->
In (sce, s) (stateScenarioMap mon) -> In e (alphabet sce)*)


Fixpoint checkStateScePropScenarioMap st e (lst: list (scenario*scenario_state)) : bool :=
  match lst with
  | (sce, st')::lst' => if string_dec st' st then
                          if inList event_definition_dec e (alphabet sce) then
                            checkStateScePropScenarioMap st e lst'
                          else
                            false
                        else
                          checkStateScePropScenarioMap st e lst'
  | _ => true
 end. 

Lemma checkStateScePropScenarioMap_cor: forall lst st e sce,
    checkStateScePropScenarioMap st e lst ->
    In (sce, st) lst -> In e (alphabet sce). 
Proof.
  intro lst;induction lst;simpl in *;intros.
  - inversion H0.
  - destruct H0;subst.
    destruct ( string_dec st st). 
    remember (inList event_definition_dec e (alphabet sce)).
    destruct b;inversion H.
    symmetry in Heqb. apply reverseinListLemma in Heqb;auto. contradiction.
    apply IHlst with (st:=st);auto.
    destruct a. destruct (string_dec s0 st);auto.
    destruct (inList event_definition_dec e (alphabet s));inversion H;auto. 
Qed.


Lemma checkStateScePropScenarioMap_rev_cor: forall lst st e,
    
    (forall sce, In (sce, st) lst -> In e (alphabet sce)) ->
    checkStateScePropScenarioMap st e lst. 
Proof.
  intro lst;induction lst;simpl in *;intros.
  - auto. 
  - destruct a.
    destruct (string_dec s0 st).
    subst.
    assert (In e (alphabet s)).
    apply H;auto.
    SearchAbout inList.
    apply inListLemma with (decA:=event_definition_dec) in H0;auto.
    rewrite H0. apply IHlst;auto.
    apply IHlst;auto. 
Qed.

Fixpoint checkStateSceProp  (lst: list (option scenario_state * option event_definition * list event_instance)) lst1 : bool :=
  match lst with
  | nil => true
  | (Some st, Some e', elst) :: lst' => if checkStateScePropScenarioMap st e' lst1 then
                                          checkStateSceProp lst' lst1
                                        else
                                          false
  | (_, _, _) :: lst' =>  checkStateSceProp  lst' lst1                                        
  end.

Lemma checkStateSceProp_cor: forall lst lst1,
    checkStateSceProp lst lst1 ->
    forall (s : scenario_state) (e : event_definition) (l : list event_instance) (sce : scenario),
In (Some s, Some e, l) lst ->
In (sce, s) lst1 -> In e (alphabet sce). 
Proof.
  intro lst;induction lst;simpl in *;intros.
  - inversion H0.
  - destruct a;destruct p.
    destruct H0. inversion H0;subst.
    remember (checkStateScePropScenarioMap s e lst1). 
    destruct b; inversion H.
    symmetry in Heqb.
    apply checkStateScePropScenarioMap_cor with (sce:=sce) in Heqb;auto.
    destruct o. destruct o0;apply IHlst with (lst1:=lst1) (s:=s) (l:=l);auto. 
    destruct (checkStateScePropScenarioMap s0 e0 lst1);inversion H;auto. 
    apply IHlst  with (lst1:=lst1) (s:=s) (l:=l);auto.    
Qed.

Lemma checkStateSceProp_rev_cor: forall lst lst1,
    
    (forall (s : scenario_state) (e : event_definition) (l : list event_instance) (sce : scenario),
In (Some s, Some e, l) lst ->
In (sce, s) lst1 -> In e (alphabet sce)) ->
checkStateSceProp lst lst1. 
Proof.
  intro lst;induction lst;simpl in *;intros.
  - auto.
    
  - destruct a;destruct p.
    destruct o;destruct o0.
    assert (checkStateScePropScenarioMap s e lst1).
    apply checkStateScePropScenarioMap_rev_cor;auto.
    intros.  apply H with (s0:=s) (l0:=l);auto.
    rewrite H0;auto.
    apply IHlst;auto.
    intros.
    apply H with (s0:=s0) (l0:=l0);auto.
    apply IHlst;auto.
     intros.
     apply H with (s0:=s0) (l0:=l0);auto.
      apply IHlst;auto.
     intros.
     apply H with (s:=s) (l0:=l0);auto.
     apply IHlst;auto.
     intros.
     apply H with (s:=s) (l0:=l0);auto.
Qed.

Lemma stateSceProp_dec: forall mon,
    checkStateSceProp (stateEvDefInstanceMap mon) (stateScenarioMap mon) <->
    stateSceProp mon.
Proof.
  intros;split;intros. unfold  stateSceProp;apply  checkStateSceProp_cor;auto.
  apply checkStateSceProp_rev_cor;auto.
Qed.


(*alphabetScenario'' = 
fun mon : object =>
forall (sce : scenario) (e : event_definition) (st : scenario_state) (elst : list event_instance),
In sce (scenarios mon) ->
In e (alphabet sce) ->
In (Some st, Some e, elst) (stateEvDefInstanceMap mon) ->
elst <> [] /\ (exists stp : step, In stp (traces sce) /\ st = pre_state stp)
     : object -> Prop*)


Fixpoint findStep (lst: list step) (st: scenario_state) : bool :=
  match lst with
  | nil => false
  | stp::lst' => if string_dec st (pre_state stp) then
                   true
                 else
                  findStep lst' st
  end.


Lemma findStep_cor : forall lst st,
    findStep lst st ->
    (exists stp : step, In stp lst /\ st = pre_state stp). 
Proof.
  intro lst;induction lst;simpl in *;intros. 
  - inversion H.
  - destruct (string_dec st (pre_state a));subst.
    exists a;intuition.
    apply IHlst in H;auto.
    destruct H. exists x;intuition. 
Qed.

Lemma findStep_rev_cor : forall lst st,
    (exists stp : step, In stp lst /\ st = pre_state stp) -> findStep lst st
    . 
Proof.
  intro lst;induction lst;simpl in *;intros. 
  - destruct H. destruct H. inversion H.
  - destruct H. destruct H.
    destruct H;subst. destruct (string_dec (pre_state x) (pre_state x));auto.
    destruct (string_dec (pre_state x) (pre_state a)). 
   auto.     apply IHlst;auto. exists x;auto. 
Qed.



Fixpoint checkAlphabetStateEvDefInsMap sce e (lst: list (option scenario_state * option event_definition * list event_instance)) : bool :=
  match lst with
  | nil => true
  | (Some st, Some e', elst) :: lst' => if event_definition_dec e e' then
                                         if list_eq_dec event_instance_dec elst [] then
                                           false
                                             
                                           else
                                             if findStep (traces sce) st then
                                               checkAlphabetStateEvDefInsMap sce e lst'            
                                             else
                                               false
                                        else
                                           checkAlphabetStateEvDefInsMap sce e lst'    
                                      
  | (_, _, _) :: lst' =>  checkAlphabetStateEvDefInsMap sce e lst'                                        
  end.


Lemma checkAlphabetStateEvDefInsMap_cor: forall lst sce e st elst,
    checkAlphabetStateEvDefInsMap sce e lst ->
  
   In (Some st, Some e, elst) lst ->
   elst <> [] /\ (exists stp : step, In stp (traces sce) /\ st = pre_state stp). 
Proof.
  intro lst;induction lst;simpl in *;intros. 
- inversion H0.                 
- destruct a;destruct p.
  destruct H0;(try (inversion H0;subst)).
  destruct (event_definition_dec e e);inversion H.
  destruct (list_eq_dec event_instance_dec elst []);inversion H.
  
  remember (findStep (traces sce) st).
  destruct b;inversion H. symmetry in Heqb. 
  apply findStep_cor in Heqb;auto.
  contradiction.   destruct o;destruct o0;apply IHlst with (e:=e);auto.
  destruct (event_definition_dec e e0);inversion H;subst.
  destruct (list_eq_dec event_instance_dec l []).
  inversion H2.
  destruct (findStep (traces sce) s);inversion H2;auto. auto.  
Qed.


Lemma checkAlphabetStateEvDefInsMap_rev_cor: forall lst sce  e,
   (forall st  elst, In (Some st, Some e, elst) lst ->
   elst <> [] /\ (exists stp : step, In stp (traces sce) /\ st = pre_state stp)) ->
   checkAlphabetStateEvDefInsMap sce e lst. 
Proof.
  intro lst;induction lst;simpl in *;intros. 
- auto.            
- destruct a;destruct p.
  destruct o;auto. destruct o0;auto.
  destruct (event_definition_dec e e0);auto. 
  subst.   
  assert (l <> [] /\ (exists stp : step, In stp (traces sce) /\ s = pre_state stp)).
  
  apply H;auto.  destruct H0.
  destruct (list_eq_dec event_instance_dec l []). contradiction.  
  assert (findStep (traces sce) s ).
  apply findStep_rev_cor;auto. rewrite H2;auto. 
Qed.

  
Fixpoint checkAlphabetSceEvent sce (elst: list event_definition) (lst: list (option scenario_state * option event_definition * list event_instance)) : bool :=
  match elst with
  | nil => true
  | e::lst' => if checkAlphabetStateEvDefInsMap sce e lst then
                 checkAlphabetSceEvent sce lst' lst
               else
                 false
  end.

Lemma checkAlphabetSceEvent_cor: forall evLst lst sce e st elst,
    checkAlphabetSceEvent sce evLst lst ->
   In e evLst ->
   In (Some st, Some e, elst) lst ->
   elst <> [] /\ (exists stp : step, In stp (traces sce) /\ st = pre_state stp).
Proof.
  intro evLst;induction evLst;simpl in *;intros .
- inversion H0. 
- destruct H0;subst.
  remember ( checkAlphabetStateEvDefInsMap sce e lst). 
  destruct b.
  symmetry in Heqb.
  apply checkAlphabetStateEvDefInsMap_cor with (st:=st) (elst:=elst) in Heqb;auto.  
  inversion H.
  destruct ( checkAlphabetStateEvDefInsMap sce a lst); inversion H;apply IHevLst with (lst:=lst) (e:=e);auto.
Qed.

Lemma checkAlphabetSceEvent_rev_cor: forall evLst lst sce ,
    
   (forall e st elst, In e evLst ->
   In (Some st, Some e, elst) lst ->
   elst <> [] /\ (exists stp : step, In stp (traces sce) /\ st = pre_state stp)) 
   -> checkAlphabetSceEvent sce evLst lst.
Proof.
  intro evLst;induction evLst;simpl in *;intros .
- auto. 
- assert (checkAlphabetStateEvDefInsMap sce a lst).
  apply checkAlphabetStateEvDefInsMap_rev_cor;auto.
  intros.
  apply H with (e:=a);auto. rewrite H0;auto.
  apply IHevLst;auto. intros.
  apply H with (e:=e);auto. 
Qed.


Fixpoint checkAlphabetScenario (lst: list (option scenario_state * option event_definition * list event_instance)) sceList : bool :=
  match sceList with
  | nil => true
  | sce::lst' => if checkAlphabetSceEvent sce (alphabet sce) lst then
                   checkAlphabetScenario lst lst'
                 else
                   false
  end. 

Lemma checkAlphabetScenario_cor: forall sceList sce lst e st elst,
    checkAlphabetScenario lst sceList ->
    In sce sceList->
In e (alphabet sce) ->
In (Some st, Some e, elst) lst ->
elst <> [] /\ (exists stp : step, In stp (traces sce) /\ st = pre_state stp). 
Proof.
  intro sceList;induction sceList;simpl in *;intros. 
- inversion H0. 
- destruct H0;subst.
  remember (checkAlphabetSceEvent sce (alphabet sce) lst). 
  destruct b.
  symmetry in Heqb.
  apply checkAlphabetSceEvent_cor with (e:=e) (st:=st) (elst:=elst) in Heqb;auto. 
  inversion H.
  destruct (checkAlphabetSceEvent a (alphabet a) lst);inversion H;apply IHsceList with (lst:=lst) (e:=e);auto.  
Qed.

Lemma checkAlphabetScenario_rev_cor: forall sceList  lst ,
    
   (forall sce e st elst, In sce sceList->
In e (alphabet sce) ->
In (Some st, Some e, elst) lst ->
elst <> [] /\ (exists stp : step, In stp (traces sce) /\ st = pre_state stp))
-> checkAlphabetScenario lst sceList. 
Proof.
  intro sceList;induction sceList;simpl in *;intros. 
- auto. 
- assert (checkAlphabetSceEvent a (alphabet a) lst).
  apply checkAlphabetSceEvent_rev_cor;auto.
  intros. apply H with (e:=e);auto.
  rewrite H0;auto. apply IHsceList;auto.
  intros. apply H with (e:=e);auto. 
Qed.

Lemma alphabetScenario_dec: forall mon,
    checkAlphabetScenario (stateEvDefInstanceMap mon)  (scenarios mon) ->
    alphabetScenario'' mon.
Proof.
  intros;unfold   alphabetScenario''.
  intros. apply checkAlphabetScenario_cor with (sceList:=scenarios mon) (lst:= (stateEvDefInstanceMap mon)) (e:=e);auto.
Qed.

Lemma alphabetScenario_dec_all: forall mon,
    checkAlphabetScenario (stateEvDefInstanceMap mon)  (scenarios mon) <->
    alphabetScenario'' mon.
Proof.
  intros;split;intros. 
   unfold   alphabetScenario''.
   intros. apply checkAlphabetScenario_cor with (sceList:=scenarios mon) (lst:= (stateEvDefInstanceMap mon)) (e:=e);auto.
   apply checkAlphabetScenario_rev_cor;auto. 
Qed.


(*correctStateEvStepMap' = 
fun mon : object =>
forall (st : scenario_state) (ei : event_instance) (stp : step) (sce : scenario),
In (st, ei, sce, Some stp) (stateEvStepMap' mon) ->
In stp (traces sce) /\ stepEvent stp = ei /\ pre_state stp = st
     : object -> Prop*)
  (*correctStateEvStepMap'*)

Fixpoint checklegalStateEvStpMap (lst: list (scenario_state*event_instance*scenario*(option step))) :bool :=
  match lst with
  | nil => true
  | (st,ei,sce,Some stp)::lst' => if inList step_dec stp (traces sce) then
                                    if event_instance_dec (stepEvent stp) ei then
                                      if string_dec (pre_state stp) st then
                                        checklegalStateEvStpMap lst'
                                      else
                                        false
                                    else
                                      false
                                  else
                                    false
  | (_,_,_,None) :: lst' => checklegalStateEvStpMap lst'                                   
end.                                         


Lemma checklegalStateEvStpMap_cor: forall lst,
    checklegalStateEvStpMap lst ->
    (forall (st : scenario_state) (ei : event_instance) (stp : step) (sce : scenario),
In (st, ei, sce, Some stp) lst ->
In stp (traces sce) /\ stepEvent stp = ei /\ pre_state stp = st). 
Proof.
  intro lst;induction lst;simpl in *;intros.
- inversion H0. 
- destruct H0;subst.
  remember (inList step_dec stp (traces sce)).
  destruct b;inversion H.
  symmetry in Heqb.
  destruct (event_instance_dec (stepEvent stp) ei);inversion H;subst;auto.
  destruct (string_dec (pre_state stp) st); inversion H;subst;auto.
  apply reverseinListLemma in Heqb;auto.
  destruct a;destruct p. destruct p.
  destruct o;apply IHlst;auto.
  destruct (inList step_dec s1 (traces s));inversion H.
  destruct ( event_instance_dec (stepEvent s1) e);inversion H2;auto.
  destruct (string_dec (pre_state s1) s0);inversion H2;auto. 
Qed.



Lemma checklegalStateEvStpMap_cor_dec: forall mon,
    checklegalStateEvStpMap (stateEvStepMap' mon) ->
    correctStateEvStepMap'  mon.
Proof.
  intros. unfold correctStateEvStepMap' ;apply checklegalStateEvStpMap_cor;auto. 
Qed.

Lemma checklegalStateEvStpMap_cor_rev: forall lst,
     (forall st ei stp sce, In (st, ei, sce, Some stp) lst ->
      In stp (traces sce) /\ stepEvent stp = ei /\ pre_state stp = st)
   ->    checklegalStateEvStpMap lst. 
Proof.
  intro lst;induction lst;simpl in *;intros.
  - auto. 
  - destruct a;destruct p. destruct p.
    destruct o;auto.
    assert (inList step_dec s1 (traces s)).
    SearchAbout inList.
    apply inListLemma;auto.
    assert ( In s1 (traces s) /\ stepEvent s1 = e /\ pre_state s1 = s0).
    apply H;auto. destruct H0;auto.
    rewrite H0.
    assert ( (stepEvent s1) = e).
    assert ( In s1 (traces s) /\ stepEvent s1 = e /\ pre_state s1 = s0).
    apply H;auto. destruct H1;auto. destruct H2;auto.
    rewrite H1;auto.
    destruct (event_instance_dec e e).
    Focus 2. contradiction. clear e0.
     assert ( In s1 (traces s) /\ stepEvent s1 = e /\ pre_state s1 = s0).
     apply H;auto.
     (destruct H2).  destruct H3.   rewrite H4.
     destruct (string_dec s0 s0).
    apply IHlst;auto. contradiction.      
Qed. 
  
Lemma checklegalStateEvStpMap_cor_rev_dec: forall mon,
     correctStateEvStepMap'  mon ->
    checklegalStateEvStpMap (stateEvStepMap' mon)
   .
Proof.
  intros. unfold correctStateEvStepMap' in H.
  apply checklegalStateEvStpMap_cor_rev.
  intros;apply H;auto. 
Qed.

Lemma checklegalStateEvStpMap_cor_dec_all: forall mon,
     correctStateEvStepMap'  mon <->
    checklegalStateEvStpMap (stateEvStepMap' mon)
   .
   Proof.
 intros;split;intros.     
 apply checklegalStateEvStpMap_cor_rev_dec;auto.
 apply checklegalStateEvStpMap_cor_dec;auto.
   Qed.
   
(*stepExistsMon' = 
fun (mon : object) (sce : scenario) =>
forall (s : scenario_state) (ei : event_instance) (e : event_definition)
  (l : list event_instance),
In (Some s, Some e, l) (stateEvDefInstanceMap mon) ->
In ei l ->
In e (alphabet sce) -> exists stp : step, In (s, ei, sce, Some stp) (stateEvStepMap' mon)*)

   
   Print stepExistsMon'.



Fixpoint checkExistsStp (lst: list (scenario_state*event_instance*scenario*(option step))) s ei   sce :=
  match lst with
  | nil => false
  | (s',ei',sce',Some stp') :: lst' => if string_dec s s' then
                                         if event_instance_dec ei ei' then
                                             if scenario_dec sce sce' then
                                               true
                                           else
                                             checkExistsStp lst' s ei  sce
                                         else
                                           checkExistsStp lst' s ei  sce
                                       else
                                         checkExistsStp lst' s ei sce
  | _::lst' => checkExistsStp lst' s ei  sce
  end.



Lemma checkExistsStp_cor: forall lst s ei  sce,
    checkExistsStp lst s ei sce->
    exists stp : step, In (s, ei, sce, Some stp) lst. 
Proof.
  intro lst;induction lst;simpl in *;intros. 
  - inversion H.
  - destruct a;destruct p. destruct p;subst.
    destruct o.
    Focus 2. apply IHlst with (sce:=sce) in H;auto.
    destruct H. exists x;right;auto.
    destruct (string_dec s s1);subst.
    destruct (event_instance_dec ei e);subst.
    destruct (scenario_dec sce s0);subst. 
   
    
    exists s2;left;auto.
    apply IHlst in H.
    destruct H. exists x;right;auto.
    apply IHlst in H.
    destruct H. exists x;right;auto.
    apply IHlst in H.
    destruct H. exists x;right;auto.
   
Qed.

Lemma checkExistsStp_rev_cor: forall lst s ei  sce,
    (exists stp : step, In (s, ei, sce, Some stp) lst) ->
    checkExistsStp lst s ei sce 
    . 
Proof.
  intro lst;induction lst;simpl in *;intros. 
  - destruct H. inversion H.
  - destruct a;destruct p. destruct p;subst.
    destruct H. destruct H. inversion H;subst.
    destruct ( string_dec s s);auto.
    destruct ( event_instance_dec ei ei);auto.
    destruct ( scenario_dec sce sce);auto.
    
    destruct o.
    Focus 2. apply IHlst;auto. exists x;auto. 
    
    destruct (string_dec s s1);subst. 
    destruct (event_instance_dec ei e);subst.
    destruct ( scenario_dec sce s0);subst.
    auto. 
    apply IHlst;auto. exists x;auto.
     apply IHlst;auto. exists x;auto.
      apply IHlst;auto. exists x;auto.
Qed.


    
Fixpoint checkExistsStpEi elst (lst: list (scenario_state*event_instance*scenario*(option step))) s sce :=
  match elst with
  | nil => true
  | ei :: lst' => if checkExistsStp lst s ei sce then
                    checkExistsStpEi lst' lst s  sce
                  else
                    false
  end.

Lemma checkExistsStpEi_cor: forall elst lst s sce,
    checkExistsStpEi elst lst s sce ->
    (forall ei, In ei elst -> exists stp : step, In (s, ei, sce, Some stp) lst). 
Proof.
  intro elst;induction elst;simpl in *;intros. 
  -  inversion H0.
  -  destruct H0;subst.
     remember (checkExistsStp lst s ei sce).
     destruct b;inversion H.
     symmetry in Heqb.
     apply checkExistsStp_cor in Heqb. auto.
     destruct (checkExistsStp lst s a sce);inversion H;auto. 
Qed. 

Lemma checkExistsStpEi_rev_cor: forall elst lst s sce,
    (forall ei, In ei elst -> exists stp : step, In (s, ei, sce, Some stp) lst) ->
    checkExistsStpEi elst lst s sce. 
Proof.
  intro elst;induction elst;simpl in *;intros. 
  -  auto. 
  -  assert (exists stp : step, In (s, a, sce, Some stp) lst).
     apply H;auto.  destruct H0.     
     assert (checkExistsStp lst s a sce).
     apply checkExistsStp_rev_cor;auto.
     rewrite H1.
     apply IHelst;auto. 
Qed. 


Fixpoint checkExistsMon sce (lst: list ((option scenario_state)*(option event_definition)*(list event_instance)))  lst2 : bool :=
  match lst with
  | nil => true
  | (Some st, Some ev, elst) :: lst' =>
    if (inList event_definition_dec ev (alphabet sce)) then
      if (checkExistsStpEi elst lst2 st sce) then
         checkExistsMon sce lst' lst2
    else
      false
    else
      checkExistsMon sce lst' lst2
  | _::lst' => checkExistsMon sce lst' lst2
end. 

Lemma checkExistsMon_cor: forall lst lst2  sce  ,
    checkExistsMon sce lst lst2 ->
 (forall e s l ei,   In (Some s, Some e, l) lst ->
   In ei l -> In e (alphabet sce) ->
 exists stp : step, In (s, ei, sce, Some stp) lst2). 
Proof.
  intro lst;induction lst;simpl in *;intros.
- inversion H0. 
-  destruct H0;subst.
   remember (inList event_definition_dec e (alphabet sce)). 
    remember (checkExistsStpEi l lst2 s sce). 
   destruct b;destruct b0;simpl in *;inversion H.
   symmetry in Heqb. symmetry in Heqb0. 
   apply checkExistsStpEi_cor with (ei:=ei) in Heqb0;auto.    
   symmetry in Heqb.  SearchAbout inList. apply reverseinListFalse in Heqb;auto.
  contradiction. symmetry in Heqb.  apply reverseinListFalse in Heqb;auto.
  contradiction.    destruct a;destruct p.
   destruct o;apply IHlst with (l:=l) (e:=e);auto. 
   destruct o0;auto.
  destruct (inList event_definition_dec e0 (alphabet sce));destruct (checkExistsStpEi l0 lst2 s0 sce)%bool;inversion H;auto.  
Qed.

Lemma checkExistsMon_rev_cor: forall lst lst2 sce,
    
  (forall s e l, In (Some s, Some e, l) lst ->
  (forall ei, In ei l -> In e (alphabet sce) ->
               exists stp : step, In (s, ei, sce, Some stp) lst2))
 -> checkExistsMon sce lst lst2. 
Proof.
  intro lst;induction lst;simpl in *;intros.
- auto. 
-  destruct a;destruct p.
   destruct o.
   destruct o0.
   assert (forall ei : event_instance,
              In ei l ->   In e (alphabet sce) -> exists stp : step, In (s, ei, sce, Some stp) lst2).
   apply H with (e0:=e);auto.
   remember (inList event_definition_dec e (alphabet sce)).
   destruct b;auto.
   symmetry in Heqb. apply reverseinListLemma in Heqb;auto.
   assert (checkExistsStpEi l lst2 s sce).
   apply checkExistsStpEi_rev_cor;auto.
   rewrite H1;auto.
   apply IHlst;auto.
     intros.
   apply H with (e0:=e0) (l0:=l0);auto.
     apply IHlst;auto.
   intros.
   apply H with (e0:=e0) (l0:=l0);auto.
    apply IHlst;auto.
   intros.
   apply H with (e:=e) (l0:=l0);auto.
   apply IHlst;auto.
     intros.
   apply H with (e:=e) (l0:=l0);auto.
Qed.



Lemma stepExistsMon_dec: forall mon sce,

    checkExistsMon sce (stateEvDefInstanceMap mon) (stateEvStepMap' mon) <->
    stepExistsMon' mon sce. 
Proof.
  intros;split;intros. 
  unfold   stepExistsMon'.
  intros. apply checkExistsMon_cor with (l:=l) (lst:=(stateEvDefInstanceMap mon) ) (e:=e);auto.
  apply checkExistsMon_rev_cor;auto.
  unfold   stepExistsMon' in H.
  intros. apply H with (e:=e) (l:=l);auto. 
Qed.

Fixpoint checkExistsMonSceList mon (slst: list scenario)   : bool :=
  match slst with
  | nil => true
  | sce::lst' => if checkExistsMon sce (stateEvDefInstanceMap mon) (stateEvStepMap' mon) then
                   checkExistsMonSceList mon lst'
                 else
                   false
  end.                    

Lemma stepExistsMon_all_cor: forall lst mon sce ,
    In sce lst ->
    checkExistsMonSceList mon lst ->
    stepExistsMon' mon sce. 
 
Proof.
  intro lst;induction lst;intros. 
  -   inversion H.
  - destruct H;subst. simpl in H0.
    remember (checkExistsMon sce (stateEvDefInstanceMap mon) (stateEvStepMap' mon)).
    destruct b;inversion H0. symmetry in Heqb. apply stepExistsMon_dec;auto.
    apply IHlst;auto. 
    simpl in H0.
   destruct ( checkExistsMon a (stateEvDefInstanceMap mon) (stateEvStepMap' mon));inversion H0;auto.  
Qed.

Lemma stepExistsMon_all_rev_cor: forall lst mon ,
    (forall sce, In sce lst ->    
    stepExistsMon' mon sce) -> checkExistsMonSceList mon lst. 
 
Proof.
  intro lst;induction lst;intros. 
  -   simpl;auto. 
  - simpl in *.
    assert (stepExistsMon' mon a). 
    apply H;auto.
    apply stepExistsMon_dec in H0;auto.
       
    rewrite H0;auto. 
Qed.

Lemma stepExistsMon_all_cor': forall lst mon ,
    checkExistsMonSceList mon lst ->
    (forall sce, In sce lst ->    
    stepExistsMon' mon sce) . 
 
Proof.
  intro lst;induction lst;intros. 
  -   inversion H0. 
  - simpl in *.
    destruct H0;subst. 
    apply stepExistsMon_dec;auto.
    destruct (checkExistsMon sce (stateEvDefInstanceMap mon) (stateEvStepMap' mon));auto.
    apply IHlst;auto.
    destruct (checkExistsMon a (stateEvDefInstanceMap mon) (stateEvStepMap' mon));inversion H.
  apply H2;auto.     
Qed.


Lemma stepExistsMon_all_cor_all: forall lst mon ,
    checkExistsMonSceList mon lst <->
    (forall sce, In sce lst ->    
    stepExistsMon' mon sce) . 
 
Proof.
  intros;split;intros. 
  apply  stepExistsMon_all_cor with (lst:=lst);auto.
  apply stepExistsMon_all_rev_cor;auto. 
Qed.



Definition string_ei_sce_dec (n m : (scenario_state * event_instance * scenario)) : {n = m} + { n <> m}.
Proof. 
  pose proof string_dec. 
  pose proof event_instance_dec.
  pose proof scenario_dec. 
  destruct n;destruct m.
  destruct p;destruct p0. 
  destruct H with (s1:=s1) (s2:= s2);destruct H0 with (n:=e) (m:=e0);
    destruct H1 with (n:=s) (m:=s0);subst. left;auto.
  right;unfold not;intros;inversion H2;contradiction.
  right;unfold not;intros;inversion H2;contradiction.
 right;unfold not;intros;inversion H2;contradiction.
 right;unfold not;intros;inversion H2;contradiction.
 right;unfold not;intros;inversion H2;contradiction.
 right;unfold not;intros;inversion H2;contradiction.
 
  right;unfold not;intros;inversion H2;subst. contradiction.
Defined.


Definition checkstpStMapEquiv  (lst : list (scenario_state * event_instance * scenario)) : bool :=
     if  NoDup_dec string_ei_sce_dec lst then
       true
     else
       false. 


Lemma stpStMapEquiv_dec: forall mon,
    checkstpStMapEquiv (dom (stateEvStepMap' mon)) ->
    uniqList ((dom (stateEvStepMap' mon))). 
Proof.
  intros.
  unfold checkstpStMapEquiv in H. 
  destruct (NoDup_dec string_ei_sce_dec (dom (stateEvStepMap' mon))). 
   rewrite uniqListNoDupEq;auto. 
  inversion H.
Qed.


Lemma stpStMapEquiv_rev_dec: forall mon,
     uniqList ((dom (stateEvStepMap' mon))) ->
    checkstpStMapEquiv (dom (stateEvStepMap' mon))
   . 
Proof.
  intros.
  rewrite uniqListNoDupEq in H.   unfold checkstpStMapEquiv. 
  destruct (NoDup_dec string_ei_sce_dec (dom (stateEvStepMap' mon))). 
  auto.    
  contradiction. 
Qed.



(*transEvMapEventInstanceProp = 
fun mon : object =>
forall (st : scenario_state) (e : event_definition) (lst : list event_instance),
In (Some st, Some e, lst) (stateEvDefInstanceMap mon) ->
forall ei : event_instance,
In ei lst ->
exists (stp : step) (sce : scenario),
  In sce (scenarios mon) /\ In stp (traces sce) /\ pre_state stp = st /\ stepEvent stp = ei
     : object -> Prop*)



Fixpoint checkEvInLstStep (ei:event_instance) (st: scenario_state) (lst: list step) : bool :=
  match lst with
  | nil => false
  | stp::lst' => if string_dec (pre_state stp) st then
                  if event_instance_dec (stepEvent stp) ei then
                     true
                  else
                    checkEvInLstStep ei st lst'
                else
                  checkEvInLstStep ei st lst'
 end.

Lemma checkEvInLstStep_cor: forall l st ei,
    checkEvInLstStep ei st l ->
    (exists stp, 
        In stp l /\
        pre_state stp = st /\ stepEvent stp = ei).
Proof.
  intro l;induction l;intros.
 - simpl in H. inversion H. 
 - simpl in *;subst;auto.
   destruct ( string_dec (pre_state a) st);inversion H. 
   subst.   
   destruct ( event_instance_dec (stepEvent a) ei);auto. exists a;intuition.
   apply IHl in H;auto. 
   destruct H. exists x;intuition.
   apply IHl in H;auto. destruct H. exists x;intuition. 
Qed.



Lemma checkEvInLstStep_rev_cor: forall l st ei,
    (exists stp,
        In stp l /\
        pre_state stp = st /\ stepEvent stp = ei) -> checkEvInLstStep ei st l
    .
Proof.
  intro l;induction l;intros.
 - simpl in *;auto.  destruct H. destruct H. inversion H. 
 - simpl in *;subst;auto.
   destruct H. destruct H. destruct H;subst.
   destruct H0. rewrite H. rewrite H0.
   destruct (string_dec st st);auto.
   destruct (event_instance_dec ei ei );auto.
   destruct H0.
   destruct (string_dec (pre_state a) st);auto. 
   destruct ( event_instance_dec (stepEvent a) ei);auto. 
   apply IHl;auto.   exists x;intuition.
    apply IHl;auto.   exists x;intuition. 
Qed.

Definition checkEvInLstStepSce (ei:event_instance) (st: scenario_state) sce: bool :=
      checkEvInLstStep ei st (traces sce). 

Fixpoint checkEvInLstEi (l: list step) (st: scenario_state) (lst: list event_instance) : bool :=
  match lst with
  | nil => true
  | ei::l' => if checkEvInLstStep ei st l then
                 checkEvInLstEi l st l' 
               else
                 false
  end.




Fixpoint checkEvInLstEiSce (l:list scenario) (st: scenario_state) (ei:  event_instance) : bool :=
  match l with
  | nil => false
  | sce::l' => if checkEvInLstStepSce ei st sce then
                 true
               else
                 checkEvInLstEiSce l' st ei
  end.

Lemma checkEvInLstEiSce_cor: forall l st ei,
    checkEvInLstEiSce l st ei ->
    (
    exists sce stp,
      In sce l /\ In stp (traces sce) /\ pre_state stp = st /\ stepEvent stp = ei).
Proof.
   intro lst;induction lst.   
   - intros;simpl in *. inversion H. 
   - intros;simpl in *.
    
     remember (checkEvInLstStepSce ei st a).
     destruct b;inversion H.
     symmetry in Heqb.
     apply checkEvInLstStep_cor in Heqb.
     destruct Heqb. exists a;exists x;auto. 
          apply IHlst in H;auto. 
  destruct H.   destruct H. exists x;exists x0;intuition. 
Qed.

Lemma checkEvInLstEiSce_rev_cor: forall l st ei,
    (exists sce stp,
      In sce l /\ In stp (traces sce) /\ pre_state stp = st /\ stepEvent stp = ei) ->
    checkEvInLstEiSce l st ei. 
Proof.
   intro l;induction l.   
   - intros;simpl in *. destruct H. destruct H. destruct H. inversion H. 
   - intros;simpl in *.
     destruct H. destruct H.
     destruct H. destruct H;subst. 
     assert (checkEvInLstStepSce ei st x ).
    
     unfold  checkEvInLstStepSce.
     apply checkEvInLstStep_rev_cor;auto.
     exists x0;intuition. rewrite H;auto. 
     destruct (checkEvInLstStepSce ei st a );auto;apply IHl;auto.
     exists x;exists x0;intuition. 
Qed.

Lemma checkEvInLstEi_cor: forall lst l st ,
    checkEvInLstEi l st lst ->
    (forall ei,
        In ei lst ->
    exists stp,
      In stp l /\ pre_state stp = st /\ stepEvent stp = ei).
Proof.
   intro lst;induction lst.   
   - intros;simpl in *. inversion H0. 
   - intros;simpl in *.
     destruct H0;subst.
     remember (checkEvInLstStep ei st l).
     destruct b;inversion H.
     symmetry in Heqb.
     apply checkEvInLstStep_cor in Heqb.
     auto. 
         apply IHlst;auto. 
      destruct (checkEvInLstStep a st l);inversion H;auto. 
Qed.

Lemma checkEvInLstEi_rev_cor: forall lst l st  ,
    (forall ei,
        In ei lst ->
    exists stp,
      In stp l /\ pre_state stp = st /\ stepEvent stp = ei) ->
    checkEvInLstEi l st lst
.
Proof. 
  intro lst;induction lst.   
   - intros;simpl in *. auto. 
   - intros;simpl in *.
     assert (checkEvInLstStep a st l).
     apply checkEvInLstStep_rev_cor;auto.
     rewrite H0.
     apply IHlst;auto. 
Qed.
    

Fixpoint checkEvInLstSce (l: list scenario) (st: scenario_state) (lst: list event_instance) : bool :=
  match lst with
  | nil => true
  | ei::l' => if checkEvInLstEiSce l st ei then
                 checkEvInLstSce l st l'
              else
                 false
  end.


Lemma checkEvInLstSce_cor: forall lst  l st ,
    checkEvInLstSce l st lst ->
    (forall ei,
        In ei lst ->
    exists (stp : step) (sce : scenario),
  In sce l /\ In stp (traces sce) /\ pre_state stp = st /\ stepEvent stp = ei).
Proof.
  intro lst;induction lst.
  -  intros;simpl in *.
     inversion H0.
  -  intros;simpl in *.
     destruct H0;subst.
           remember (checkEvInLstEiSce l st ei).      
     destruct b;inversion H. 
     symmetry in Heqb.    
     apply checkEvInLstEiSce_cor with (ei:=ei) in Heqb;auto. 
     destruct Heqb.
     destruct H0.
     exists x0;exists x. intuition.
     
     remember ( checkEvInLstEiSce l st a).
     destruct b;inversion H.
     apply IHlst;auto. 
Qed.


Lemma checkEvInLstSce_rev_cor: forall lst l st ,
    (forall ei,
        In ei lst ->
    exists (stp : step) (sce : scenario),
  In sce l /\ In stp (traces sce) /\ pre_state stp = st /\ stepEvent stp = ei) ->
    checkEvInLstSce l st lst
    .
Proof.
  intro lst;induction lst.
  -  intros;simpl in *.
     auto. 
  -  intros;simpl in *.
     assert (checkEvInLstEiSce l st a).
     apply checkEvInLstEiSce_rev_cor;auto.
     assert ( exists (stp : step) (sce : scenario),
                In sce l /\ In stp (traces sce) /\ pre_state stp = st /\ stepEvent stp = a).
     apply H;auto. destruct H0. destruct H0. exists x0;exists x;intuition. 
     rewrite H0.  apply IHlst;auto. 
     
Qed.


Fixpoint checkEvInLstSceMap (lst: list ((option scenario_state)*(option event_definition)*(list event_instance))) lst1 : bool :=
   match lst with
  | nil => true
  | (Some st, Some ev, elst) :: lst' =>
    if checkEvInLstSce lst1 st elst then
      checkEvInLstSceMap lst' lst1
    else
      false
  | _::lst' => checkEvInLstSceMap lst' lst1
      
   end.


Lemma transEvMapEventInstanceProp_cor: forall lst lst1,
    checkEvInLstSceMap lst lst1 ->
    (forall (st : scenario_state) (e : event_definition) (elst : list event_instance),
In (Some st, Some e, elst) lst ->
forall ei : event_instance,
In ei elst ->
exists (stp : step) (sce : scenario),
  In sce lst1 /\ In stp (traces sce) /\ pre_state stp = st /\ stepEvent stp = ei).
Proof.
  intro lst;induction lst;simpl in *;intros.
 - inversion H0. 
 -  destruct a;destruct p.
    destruct H0. inversion H0;subst.
    remember (checkEvInLstSce lst1 st elst ).
    destruct b;inversion H.
    symmetry in Heqb.
    apply checkEvInLstSce_cor with (ei:=ei) in Heqb;auto.
    destruct o;destruct o0;apply IHlst with (e:=e) (elst:=elst);auto.
    destruct (checkEvInLstSce lst1 s l);inversion H;auto.      
Qed.

Lemma transEvMapEventInstanceProp_rev_cor: forall lst lst1,
    
    (forall (st : scenario_state) (e : event_definition) (elst : list event_instance),
In (Some st, Some e, elst) lst ->
forall ei : event_instance,
In ei elst ->
exists (stp : step) (sce : scenario),
  In sce lst1 /\ In stp (traces sce) /\ pre_state stp = st /\ stepEvent stp = ei)
  -> checkEvInLstSceMap lst lst1.
Proof.
  intro lst;induction lst;simpl in *;intros.
 - auto.
 -  destruct a;destruct p.
    destruct o;auto.  destruct o0;auto.
    assert (checkEvInLstSce lst1 s l).
    apply checkEvInLstSce_rev_cor;auto.
    intros.
    assert ( forall ei : event_instance,
      In ei l ->
      exists (stp : step) (sce : scenario),
        In sce lst1 /\ In stp (traces sce) /\ pre_state stp = s /\ stepEvent stp = ei).
    apply H with (e0:=e);auto.
    apply H1 in H0. auto.
    rewrite H0;auto.
    apply IHlst;auto.
    intros.
    apply H with (e0:=e0) (elst:=elst);auto.
    apply IHlst;auto.
     intros.
     apply H with (e:=e) (elst:=elst);auto.
    apply IHlst;auto.
     intros.
     apply H with (e:=e) (elst:=elst);auto.
     
Qed.


Lemma transEvMapEventInstanceProp_cor_all: forall mon,
    checkEvInLstSceMap (stateEvDefInstanceMap mon) (scenarios mon) <->
    transEvMapEventInstanceProp mon.
Proof.
  intros. split;intros. unfold   transEvMapEventInstanceProp;apply transEvMapEventInstanceProp_cor;auto.
  apply transEvMapEventInstanceProp_rev_cor;auto. 
Qed.

(*transEvMapProp = 
fun mon : object =>
forall (st : scenario_state) (re : raisedEvent) (lst : list event_instance),
In (Some st, Some (eventDefinition re), lst) (stateEvDefInstanceMap mon) ->
forall ei : event_instance, In ei lst -> event ei = eventDefinition re
     : object -> Prop*)

Fixpoint checkEvInLst (lst: list event_instance) (e: event_definition) : bool :=
  match lst with
  | nil => true
  | ei::lst' => if event_definition_dec (event ei) e then
                  checkEvInLst lst' e
                else
                  false
 end. 


Lemma checkEvInList_cor: forall lst e,
    checkEvInLst lst e ->
    (forall ei, In ei lst -> event ei = e).
Proof.
  intro lst;induction lst.
  - intros. inversion H0.
  - intros. simpl in *;subst. destruct H0;subst.
    destruct (event_definition_dec (event ei) e). 
    auto. inversion H.
    destruct (event_definition_dec (event a) e);apply IHlst;auto. inversion H. 
Qed.


Lemma checkEvInList_rev_cor: forall lst e,
    (forall ei, In ei lst -> event ei = e) ->
    checkEvInLst lst e 
    .
Proof.
  intro lst;induction lst.
  - intros;simpl. auto. 
  - intros. simpl in *;subst.
    simpl.
    assert (event a = e).
    apply H;auto.     rewrite H0. 
    destruct (event_definition_dec e e);auto.
Qed.


Lemma checkEvInList_re_rev_cor: forall lst e re,
    eventDefinition re = e ->
    (forall ei,  In ei lst -> event ei = e) ->
    checkEvInLst lst e 
    .
Proof.
  intro lst;induction lst.
  - intros;simpl. auto. 
  - intros. simpl in *;subst.
    
    assert (event a = eventDefinition re).
    apply H0;auto.     rewrite H. 
    destruct (event_definition_dec (eventDefinition re) (eventDefinition re));auto.
    apply IHlst with (re:=re);auto.
Qed.

    

Fixpoint findEvInStateEvDefList  (lst: list ((option scenario_state)*(option event_definition)*(list event_instance))) : bool :=
  match lst with
  | nil => true
  | (Some st, Some ev, elst) :: lst' =>
    if checkEvInLst elst ev then
      findEvInStateEvDefList lst'
    else
      false
  | _::lst' => findEvInStateEvDefList lst'
      
  end. 



Lemma findEvInStateEvDefList_cor: forall lst',
    findEvInStateEvDefList lst' ->
    (forall (st : scenario_state) ev (lst : list event_instance),
In (Some st, Some ev, lst) lst' ->
forall ei : event_instance, In ei lst -> event ei = ev). 
Proof. intro lst';induction lst'. 
       - intros. inversion H0. 
       - intros.
         simpl in *.
         destruct a;destruct p;subst.
         destruct H0;subst.
         inversion H0;subst.
         remember (checkEvInLst lst ev).
         destruct b;inversion H.
         symmetry in Heqb.  apply checkEvInList_cor with (ei:=ei) in Heqb;auto.
         destruct o;
           apply IHlst' with (st:=st) (lst:=lst);auto.
         destruct o0;auto.
         destruct (checkEvInLst l e);inversion H;auto. 
Qed.

Lemma findEvInStateEvDefList_rev_cor: forall lst' ,
    
    (forall (st : scenario_state) ev  (lst : list event_instance),
In (Some st, Some ev, lst) lst' ->
forall ei : event_instance, In ei lst -> event ei = ev) ->
  findEvInStateEvDefList lst'. 
Proof. intro lst';induction lst'. 
       - intros;simpl. auto. 
       - intros.
        
        simpl in *.
         
         destruct a;destruct p;subst.
         destruct o;auto.  destruct o0;auto.
         
    
         assert (checkEvInLst l e ).
         
         apply checkEvInList_rev_cor;auto. intros.
         apply H with (st:=s) (lst:=l);auto.          
         rewrite H0;auto.
         apply IHlst';auto.
         intros. apply H with (st:=st) (lst:=lst);auto.
          apply IHlst';auto.
         intros. apply H with (st:=st) (lst:=lst);auto.
       apply IHlst';auto.
         intros. apply H with (st:=st) (lst:=lst);auto.
Qed.



Lemma findEvInStateEvDefList_cor_all: forall mon,
    findEvInStateEvDefList (stateEvDefInstanceMap mon) <->
    transEvMapProp mon.
Proof.
  intros. split;intros. unfold  transEvMapProp; apply findEvInStateEvDefList_cor;auto.
  apply findEvInStateEvDefList_rev_cor;auto.
   
Qed.

(*stateEvDefInstanceMapEquiv = 
fun mon : object =>
uniqList (dom (stateEvDefInstanceMap mon)) /\
(forall (sce : scenario) (s : scenario_state) (e : event_definition),
 In (sce, s) (stateScenarioMap mon) ->
 In e (alphabet sce) ->
 exists el : list event_instance, el <> [] /\ In (Some s, Some e, el) (stateEvDefInstanceMap mon))
     : object -> Prop*)



Fixpoint findEl (sce:string) (e:event_definition) (lst: list ((option scenario_state)*(option event_definition)*(list event_instance))) : bool :=
  match lst with
  | (Some s, Some ev, el)::lst' => if string_dec sce s then
                               if event_definition_dec e ev then
                                 if list_eq_dec event_instance_dec el [] then
                                   findEl sce e lst'
                                 else
                                   true
                               else
                                 findEl sce e lst'
                                   else
                                     findEl sce e lst'
  | (_,_,_)::lst' => findEl sce e lst'
  | nil => false                          
  end.

Lemma findEl_cor: forall lst s e ,
    findEl s e lst ->
    exists el : list event_instance, el <> [] /\ In (Some s, Some e, el) lst.
Proof.
  intro lst;induction lst.
  - intros;simpl in *;inversion H.
  - intros;simpl in *.
    destruct a;destruct p;simpl in *.
    destruct o;destruct o0.
    destruct (string_dec s s0).
    destruct (event_definition_dec e e0). subst.
    remember ( list_eq_dec event_instance_dec l []).
    destruct s;inversion H.
    apply IHlst in H;auto.
    (destruct H). destruct H.  exists x. split;auto. exists l;split;auto.
    apply IHlst in H;auto.
    (destruct H). destruct H.  exists x. split;auto.
      apply IHlst in H;auto.
      (destruct H). destruct H.  exists x. split;auto.
        apply IHlst in H;auto.
    (destruct H). destruct H.  exists x. split;auto.  apply IHlst in H;auto.
    (destruct H). destruct H.  exists x. split;auto.  apply IHlst in H;auto.
    (destruct H). destruct H.  exists x. split;auto.
Qed.


Lemma findEl_rev_cor: forall lst s e ,   
    (exists el : list event_instance, el <> [] /\ In (Some s, Some e, el) lst) ->
    findEl s e lst.
Proof.
  intro lst;induction lst.
  - intros;simpl in *;intros. destruct H. destruct H. inversion H0. 
  - intros;simpl in *.
     destruct H. destruct H.
     destruct H0;subst. 
     destruct (string_dec s s);auto.
     destruct (event_definition_dec e e);auto.
     destruct (list_eq_dec event_instance_dec x []);auto.
    
    destruct a;destruct p;simpl in *.
    destruct o;destruct o0;(try apply IHlst;auto;try (exists x;intuition)).
      
    
    destruct (string_dec s s0);
    destruct (event_definition_dec e e0);(try apply IHlst;auto;try (exists x;intuition)).
   subst.    
    
    destruct ( list_eq_dec event_instance_dec l []). 
    
    apply IHlst;auto.
     exists x;intuition. auto. 
Qed.

    
Fixpoint findEl' (sce:string) (elst:list event_definition) (lst: list ((option scenario_state)*(option event_definition)*(list event_instance))) : bool :=
  match elst with
  | e::lst' => if findEl sce e lst then
                 findEl' sce lst' lst
               else
                 false
  | nil => true                          
  end.

Lemma findlEl_cor': forall  elst lst s e,
    findEl' s elst lst ->
 In e elst ->
 exists el : list event_instance, el <> [] /\ In (Some s, Some e, el) lst. 
Proof.
  intro elst;induction elst;intros.
  - inversion H0.
  - simpl in *.
    destruct H0;subst.
    remember (findEl s e lst). 
    destruct b;inversion H.
    symmetry in Heqb.
    apply findEl_cor in Heqb.
    destruct Heqb. destruct H0.
    exists x;split;auto.
    destruct (findEl s a lst );inversion H.
    apply IHelst with (e:=e) in H;auto. 
Qed.

Lemma findlEl_rev_cor': forall  elst lst s ,
  (forall e, In e elst ->exists el : list event_instance, el <> [] /\ In (Some s, Some e, el) lst) ->  
  
    findEl' s elst lst
 . 
Proof.
  intro elst;induction elst;intros.
  - simpl;auto. 
  - simpl in *.
    assert (exists el : list event_instance, el <> [] /\ In (Some s, Some a, el) lst).
    apply H;auto. destruct H0. 
    assert (findEl s a lst).
    apply findEl_rev_cor;auto. rewrite H1. apply IHelst ;auto. 
Qed.


Fixpoint findElFromMap  (lst: list (scenario*scenario_state)) lst1 : bool :=
  match lst with
  | nil => true
  | (sce,s)::lst' => if findEl' s (alphabet sce) lst1 then
                       findElFromMap  lst' lst1
                     else
                       false
 end                        
.


Lemma findlElFromMap_cor': forall  lst lst1 ,
    
    (forall (sce : scenario) (s : scenario_state) (e : event_definition),
 In (sce, s) lst ->
 In e (alphabet sce) ->
 exists el : list event_instance, el <> [] /\ In (Some s, Some e, el) lst1) ->
findElFromMap lst lst1. 
Proof.
  intro lst;induction lst.
- intros;simpl;auto. 
- intros;simpl in *.
  destruct a.
  assert (findEl' s0 (alphabet s) lst1 ). 
  apply findlEl_rev_cor';auto.
  intros. apply H with (sce:=s);auto. rewrite H0.
  apply IHlst;auto.
  intros.
  apply H with (sce:=sce);auto.  
Qed.

Lemma findlElFromMap_rev_cor': forall  lst lst1 ,
    findElFromMap lst lst1 ->
    (forall (sce : scenario) (s : scenario_state) (e : event_definition),
 In (sce, s) lst ->
 In e (alphabet sce) ->
 exists el : list event_instance, el <> [] /\ In (Some s, Some e, el) lst1). 
Proof.
  intro lst;induction lst.
- intros.  inversion H0. 
- intros;simpl in *.
  destruct H0;subst.
  remember (findEl' s (alphabet sce) lst1).
  destruct b;inversion H.
  symmetry in Heqb.
  apply findlEl_cor' with (e:=e) in Heqb;auto. 
  destruct a.
  destruct (findEl' s1 (alphabet s0) lst1 );inversion H. 
  apply IHlst with (sce:=sce);auto.   
Qed.



Definition op_string_ev_dec (n m : (option string)*(option event_definition)) : {n = m} + { n <> m}.
Proof. 
  pose proof op_string_dec. 
  pose proof op_event_definition_dec.
  destruct n;destruct m.
  destruct H with (n:=o) (m:= o1);destruct H0 with (n:=o0) (m:=o2);subst;auto.
 right. unfold not. intros. inversion H1. contradiction. 
 right. unfold not. intros. inversion H1. contradiction.
 right. unfold not. intros. inversion H1. contradiction.
Defined. 

Definition checkStateEvDefInstanceMap_aux lst1 : bool :=
  if NoDup_dec op_string_ev_dec  lst1 then
    true
  else
    false.




Definition checkStateEvDefInstanceMap  (lst: list (scenario*scenario_state)) lst1 lst2  : bool :=
  if  NoDup_dec op_string_ev_dec  lst2 then
    if findElFromMap lst lst1 then
      true
    else
      false
  else
    false . 



Lemma checkStateEvDefInstanceMap_cor: forall lst lst1,
    checkStateEvDefInstanceMap lst lst1 (dom lst1)->
    (uniqList (dom lst1) /\
(forall (sce : scenario) (s : scenario_state) (e : event_definition),
 In (sce, s) lst ->
 In e (alphabet sce) ->
 exists el : list event_instance, el <> [] /\ In (Some s, Some e, el) lst1)). 
Proof. 
  intros.
  unfold checkStateEvDefInstanceMap in H.
  split.
 
  rewrite uniqListNoDupEq.
  destruct (NoDup_dec op_string_ev_dec (dom lst1));auto.  
  inversion H.
  generalize dependent lst1.
  induction lst;simpl in *;intros. 
  - intros. inversion H0.
    
- 
 
  destruct (NoDup_dec op_string_ev_dec (dom lst1)).
  Focus 2. inversion H.
  destruct a. 
  destruct H0;subst.
  inversion H0;subst.
  
  remember (findEl' s (alphabet sce) lst1). 
  destruct b.
  symmetry in Heqb.
  remember (findElFromMap lst lst1).
  destruct b. symmetry in Heqb0.
  Focus 2. inversion H.
  
  Focus 2.
  inversion H.
  apply findlEl_cor' with (e:=e) in Heqb;auto.
  unfold checkStateEvDefInstanceMap_aux in IHlst.
  
 
  apply IHlst with (sce:=sce);auto.
  destruct ( NoDup_dec op_string_ev_dec (dom lst1));auto.
  destruct (findEl' s1 (alphabet s0) lst1);auto. inversion H. 
 
Qed.


Lemma checkStateEvDefInstanceMap_rev_cor: forall lst lst1,
    (uniqList (dom lst1) /\
(forall (sce : scenario) (s : scenario_state) (e : event_definition),
 In (sce, s) lst ->
 In e (alphabet sce) ->
 exists el : list event_instance, el <> [] /\ In (Some s, Some e, el) lst1)) ->
 checkStateEvDefInstanceMap lst lst1 (dom lst1). 
Proof. 
  intros.
  unfold checkStateEvDefInstanceMap.
 
  destruct H. 
  rewrite uniqListNoDupEq in H.
  
  
    destruct  (NoDup_dec op_string_ev_dec (dom lst1));auto.
    assert (findElFromMap lst lst1).
    apply findlElFromMap_cor';auto.
 rewrite H1;auto.     
  
Qed. 


Lemma stateEvDefInstanceMapEquiv_cor_all: forall mon,
    checkStateEvDefInstanceMap (stateScenarioMap mon) (stateEvDefInstanceMap mon) (dom (stateEvDefInstanceMap mon))  <->
    stateEvDefInstanceMapEquiv mon. 
Proof.
  intros. split;intros. 
  unfold stateEvDefInstanceMapEquiv.
  apply checkStateEvDefInstanceMap_cor;auto.
  apply checkStateEvDefInstanceMap_rev_cor;auto. 
Qed.



  (*alphabetRaisingObject
fun mon : object =>
forall e : event_definition,
In e (events mon) ->
eventKind e = Internal \/ eventKind e = Imported ->
exists sce : scenario, In sce (scenarios mon) /\ In e (alphabet sce)*)

Fixpoint findScenarioInAlphabet (lst: list scenario) (e: event_definition): bool :=
  match lst with
  | nil => false
  | sce::lst' => if inList event_definition_dec e (alphabet sce) then
                   true
                 else
                   findScenarioInAlphabet lst' e
end. 

Lemma findScenarioInAlphabet_cor: forall lst e,
    findScenarioInAlphabet lst e ->
    exists sce : scenario, In sce lst /\ In e (alphabet sce).
Proof.
  intro lst;induction lst. 
  -  intros;simpl in *;inversion H.
  - intros. simpl in *.
    remember (inList event_definition_dec e (alphabet a)).
    destruct b.
    symmetry in Heqb. apply reverseinListLemma in Heqb.  
    exists a;auto.  
    apply IHlst in H.
    repeat(destruct H).
    exists x. split;auto. 
Qed.


Lemma findScenarioInAlphabet_rev_cor: forall lst e,
    (exists sce : scenario, In sce lst /\ In e (alphabet sce)) ->
    findScenarioInAlphabet lst e
    .
Proof.
  intro lst;induction lst. 
  -  intros;simpl in *;inversion H. destruct H0;inversion H0. 
  - intros. simpl in *.
    destruct H. destruct H.  destruct H;subst.
    SearchAbout inList. apply inListLemma with (decA:=event_definition_dec) in H0;auto.
    rewrite H0. auto. 
    destruct ( inList event_definition_dec e (alphabet a) );auto.
   apply IHlst;auto. exists x;auto. 
Qed.


Fixpoint checkAlphabetRaise mon (lst: list event_definition) : bool :=
  match lst with
  | nil => true
  | e::lst' => match eventKind e with
               | Exported => checkAlphabetRaise mon lst'
               | _ => if findScenarioInAlphabet (scenarios mon) e then
                        checkAlphabetRaise mon lst'
                      else
                        false
               end       
  end.                               


Lemma checkAlphabetRaise_cor: forall lst  mon ,
    checkAlphabetRaise mon lst ->
    (forall e : event_definition,
In e lst ->
eventKind e = Internal \/ eventKind e = Imported ->
exists sce : scenario, In sce (scenarios mon) /\ In e (alphabet sce)). 
Proof.
  intro lst;induction lst.   
- intros. inversion H0. 
- intros. destruct H0. 
  subst.
  simpl in H.
  destruct H1. subst.
  rewrite H0 in H;simpl in *.
  remember (findScenarioInAlphabet (scenarios mon) e). 
  destruct b. Focus 2. inversion H.
  symmetry in Heqb.
  apply findScenarioInAlphabet_cor in Heqb;auto. 
  rewrite H0 in H.
   remember (findScenarioInAlphabet (scenarios mon) e). 
  destruct b. Focus 2. inversion H.
  symmetry in Heqb.
  apply findScenarioInAlphabet_cor in Heqb;auto.
  apply IHlst;auto. 
  simpl in H.
  destruct (eventKind a);subst;auto.
  destruct (findScenarioInAlphabet (scenarios mon) a);auto. inversion H.
  destruct (findScenarioInAlphabet (scenarios mon) a);auto. inversion H.
Qed.


Lemma checkAlphabetRaise_rev_cor: forall lst  mon ,
    (forall e : event_definition,
In e lst ->
eventKind e = Internal \/ eventKind e = Imported ->
exists sce : scenario, In sce (scenarios mon) /\ In e (alphabet sce)) ->
    checkAlphabetRaise mon lst
    . 
Proof.
  intro lst;induction lst.   
- intros. simpl;auto. 
- intros.
  simpl in *.
  remember (eventKind a ).
  destruct e. 
  assert (exists sce : scenario, In sce (scenarios mon) /\ In a (alphabet sce)).
  apply H;auto.
  destruct H0.
  assert (findScenarioInAlphabet (scenarios mon) a).
  apply findScenarioInAlphabet_rev_cor;auto.
  rewrite H1;auto.
   assert (findScenarioInAlphabet (scenarios mon) a).
   apply findScenarioInAlphabet_rev_cor;auto.
   rewrite H0;auto.
   apply IHlst;auto. 
 
Qed.

Lemma checkAlphabetRaise_cor_dec: forall mon,
    checkAlphabetRaise mon (events mon) <->
    alphabetRaisingObject mon. 
Proof.
  intros. split;intros. 
  unfold alphabetRaisingObject.
  intros.
  apply checkAlphabetRaise_cor with (lst:=events mon);auto.
  apply checkAlphabetRaise_rev_cor;auto. 
Qed.

(*noDupRaise*)

Print event_definition.
Print noDupRaise''.


Definition scenarioRaiseEventCheck mon (v: event_definition)  : bool :=
  match (eventKind v) with
  | Exported => true
  | _ =>
    Nat.leb (List.length (scenarioRaise (scenarios mon) v)) 1
  end.

Print noDupRaise. 

Fixpoint checkRaiseInStp' (v: event_definition) (lst: list step) : bool :=
  match lst with
  | nil => true
  | stp::lst' => let acts :=
 filter (fun act : action => filterRaiseStmt act (eventId v))
        (transitionIntoBasicActionList (stepActions stp)) in
                 if Nat.leb (List.length acts) 1 then
                   checkRaiseInStp' v lst'
                 else
                   false
 end. 



Lemma checkRaiseInStp_cor': forall l v  stp,
  checkRaiseInStp' v l ->
  In stp l ->
  (Datatypes.length
     (filter (fun act : action => filterRaiseStmt act (eventId v))
             (transitionIntoBasicActionList (stepActions stp))) <= 1)%nat. 
Proof.
   intro l;induction l. 
   - intros. inversion H0.
   - intros. simpl in *.
     destruct H0;subst.
     remember ((Datatypes.length
          (filter (fun act : action => filterRaiseStmt act (eventId v))
             (transitionIntoBasicActionList (stepActions stp))) <=? 1)%nat). 
     destruct b. Focus 2. inversion H.
     destruct ((filter (fun act : action => filterRaiseStmt act (eventId v))
                       (transitionIntoBasicActionList (stepActions stp))));simpl in *. 
     omega.
     destruct l0. simpl in *. omega.
     inversion Heqb.
    destruct ((Datatypes.length
          (filter (fun act : action => filterRaiseStmt act (eventId v))
             (transitionIntoBasicActionList (stepActions a))) <=? 1))%nat. 
    Focus 2.  inversion H.
     apply IHl;auto. 
Qed.

Lemma checkRaiseInStp_rev_cor': forall l v ,
   
  (forall stp, In stp l -> (Datatypes.length
     (filter (fun act : action => filterRaiseStmt act (eventId v))
             (transitionIntoBasicActionList (stepActions stp))) <= 1)%nat) ->

   checkRaiseInStp' v l. 
Proof.
   intro l;induction l. 
   - intros. simpl;auto. 
   - intros. simpl in *.
     assert ((Datatypes.length
         (filter (fun act : action => filterRaiseStmt act (eventId v))
                 (transitionIntoBasicActionList (stepActions a))) <= 1)%nat).
     apply H;auto.
     
     remember ((filter (fun act : action => filterRaiseStmt act (eventId v))
                       (transitionIntoBasicActionList (stepActions a)))).
     destruct l0. simpl in *;auto.
     destruct l0. simpl in *;auto.
     inversion H0. inversion H2. 
     
Qed.
     
Fixpoint checkRaiseInStp (v: event_definition) (lst: list scenario) : bool :=
  match lst with
  | nil => true
  | sce::lst' => let stpList := getTransitionsOfScenario sce in
                 if checkRaiseInStp' v stpList then
                   checkRaiseInStp v lst'
                 else
                   false
end.                      



Lemma checkRaiseInStp_cor: forall lst v ,
    checkRaiseInStp v lst ->
    (forall (sce : scenario) (stp : step) (acts : list action),
  In sce lst ->
  In stp (getTransitionsOfScenario sce) ->
  acts =
  filter (fun act : action => filterRaiseStmt act (eventId v))
         (transitionIntoBasicActionList (stepActions stp)) -> (Datatypes.length acts <= 1)%nat).
Proof.
  intro lst;induction lst.
- intros. inversion H0. 
- intros. simpl in *.
  destruct H0;subst.
  {
    remember (checkRaiseInStp' v (getTransitionsOfScenario sce)). 
    destruct b. Focus 2. inversion H.
    symmetry in Heqb. 

    apply checkRaiseInStp_cor' with (stp:=stp) in Heqb;auto.
  }
  {
    destruct (checkRaiseInStp' v (getTransitionsOfScenario a)). 
    eapply IHlst;auto.  auto. apply H0.   auto.  inversion H. 
  }
Qed.

Lemma checkRaiseInStp_rev_cor: forall lst v ,
    (forall (sce : scenario) (stp : step) (acts : list action),
  In sce lst ->
  In stp (getTransitionsOfScenario sce) ->
  acts =
  filter (fun act : action => filterRaiseStmt act (eventId v))
         (transitionIntoBasicActionList (stepActions stp)) -> (Datatypes.length acts <= 1)%nat) ->checkRaiseInStp v lst
    .
Proof.
  intro lst;induction lst.
- intros. simpl;auto. 
- intros. simpl in *.
  assert (checkRaiseInStp' v (getTransitionsOfScenario a)).
  apply checkRaiseInStp_rev_cor';auto. 
  intros.
  apply H with (stp:=stp) (sce:=a);auto.
  rewrite H0;auto. apply IHlst;auto.
  intros. apply H with (stp:=stp) (sce:=sce);auto.
  Qed.

Print noDupRaise. 


Fixpoint checkNoDup mon (lst: list event_definition) : bool :=
  match lst with
  | nil => true
  | v::lst' => if andb (scenarioRaiseEventCheck mon v) (checkRaiseInStp v (scenarios mon)) then
                 checkNoDup mon lst'
               else
                 false
  end.


Fixpoint checkNoDup' mon (lst: list event_definition) : bool :=
  match lst with
  | nil => true
  | v::lst' => if (checkRaiseInStp v (scenarios mon)) then
                 checkNoDup' mon lst'
               else
                 false
  end.

Print noDupRaise. 


Lemma checkNoDup_cor: forall lst  mon v,
    In v lst ->
    
    checkNoDup mon lst ->
    ((eventKind v = Internal \/ eventKind v = Imported) -> Datatypes.length (scenarioRaise (scenarios mon) v) <= 1)%nat /\ (forall (sce : scenario) (stp : step) (acts : list action),
 In sce (scenarios mon) ->
 In stp (getTransitionsOfScenario sce) ->
 acts =
 filter (fun act : action => filterRaiseStmt act (eventId v))
   (transitionIntoBasicActionList (stepActions stp)) -> (Datatypes.length acts <= 1)%nat). 
Proof. 
  intro lst;induction lst.
  - intros. inversion H.
  - intros. destruct H;subst.
   
    simpl in H0.
    remember (scenarioRaiseEventCheck mon v).
    remember (checkRaiseInStp v (scenarios mon)).
    destruct b.
    destruct b0.
    unfold scenarioRaiseEventCheck in Heqb.
    split.
    intros.     
    destruct H.
    rewrite H in Heqb.     
   
    destruct ((scenarioRaise (scenarios mon) v));auto.
    destruct l;auto. inversion Heqb.
    rewrite H in Heqb.
     destruct ((scenarioRaise (scenarios mon) v));auto.
    destruct l;auto. inversion Heqb.
    simpl in H0.    
    intros. symmetry in Heqb0. 
    apply checkRaiseInStp_cor with (sce:=sce) (acts:=acts) (stp:=stp) in Heqb0;auto.
    simpl in H0.  inversion H0.
    simpl in H0. inversion H0. 
    
    simpl in H0.
    destruct (andb (scenarioRaiseEventCheck mon a) (checkRaiseInStp a (scenarios mon))). 
    apply IHlst;auto. inversion H0.
Qed.


Lemma checkNoDup_cor': forall lst  mon v,
    In v lst -> 
    checkNoDup' mon lst ->
    (forall (sce : scenario) (stp : step) (acts : list action),
 In sce (scenarios mon) ->
 In stp (getTransitionsOfScenario sce) ->
 acts =
 filter (fun act : action => filterRaiseStmt act (eventId v))
   (transitionIntoBasicActionList (stepActions stp)) -> (Datatypes.length acts <= 1)%nat). 
Proof. 
  intro lst;induction lst.
  - intros. inversion H.
  - intros. 
    
   
    simpl in H0.
    remember (checkRaiseInStp v (scenarios mon)).
    destruct b.
    symmetry in Heqb. 
    apply checkRaiseInStp_cor with (sce:=sce) (acts:=acts) (stp:=stp) in Heqb;auto.
    destruct H. subst.   
    rewrite <- Heqb in H0.  inversion H0.
    destruct (checkRaiseInStp a (scenarios mon) );inversion H0.
    
    apply IHlst with (mon:=mon) (v:=v) (sce:=sce) (stp:=stp);auto. 
Qed.


Lemma checkNoDup_cor_rev: forall lst  mon ,
   (forall v, In v lst -> 
    ((eventKind v = Internal \/ eventKind v = Imported) ->Datatypes.length (scenarioRaise (scenarios mon) v) <= 1)%nat /\ (forall (sce : scenario) (stp : step) (acts : list action),
 In sce (scenarios mon) ->
 In stp (getTransitionsOfScenario sce) ->
 acts =
 filter (fun act : action => filterRaiseStmt act (eventId v))
        (transitionIntoBasicActionList (stepActions stp)) -> (Datatypes.length acts <= 1)%nat))
-> checkNoDup mon lst. 
Proof. 
  intro lst;induction lst.
  - intros. simpl. auto. 
  - intros;simpl in *.
    assert ((eventKind a = Internal \/ eventKind a = Imported -> Datatypes.length (scenarioRaise (scenarios mon) a) <= 1)%nat /\
      (forall (sce : scenario) (stp : step) (acts : list action),
       In sce (scenarios mon) ->
       In stp (getTransitionsOfScenario sce) ->
       acts =
       filter (fun act : action => filterRaiseStmt act (eventId a))
              (transitionIntoBasicActionList (stepActions stp)) -> (Datatypes.length acts <= 1)%nat)).
    apply H;auto. destruct H0.
   
     
   assert  (scenarioRaiseEventCheck mon a).
   unfold    scenarioRaiseEventCheck.
   remember (eventKind a).
   destruct e.
   assert ((Datatypes.length (scenarioRaise (scenarios mon) a) <= 1)%nat).
   apply H0. left;auto.
   
  
   destruct ((scenarioRaise (scenarios mon) a) ). simpl. auto.
   destruct l. simpl. auto. inversion H2. inversion H4.

    assert ((Datatypes.length (scenarioRaise (scenarios mon) a) <= 1)%nat).
   apply H0. right;auto.
      destruct ((scenarioRaise (scenarios mon) a) ). simpl. auto.
   destruct l. simpl. auto. inversion H2. inversion H4.
  auto. 
   
 
   assert (checkRaiseInStp a (scenarios mon)).
   apply  checkRaiseInStp_rev_cor;auto.
   rewrite H2;rewrite H3. simpl.
   
   apply IHlst;auto. 
 
Qed.

Lemma checkNoDup_cor_rev': forall lst  mon ,
   (forall v, In v lst -> 
    (forall (sce : scenario) (stp : step) (acts : list action),
 In sce (scenarios mon) ->
 In stp (getTransitionsOfScenario sce) ->
 acts =
 filter (fun act : action => filterRaiseStmt act (eventId v))
        (transitionIntoBasicActionList (stepActions stp)) -> (Datatypes.length acts <= 1)%nat))
-> checkNoDup' mon lst. 
Proof. 
  intro lst;induction lst.
  - intros. simpl. auto. 
  - intros;simpl in *.
    assert ((forall v : event_definition,
           In v lst ->
           forall (sce : scenario) (stp : step) (acts : list action),
           In sce (scenarios mon) ->
           In stp (getTransitionsOfScenario sce) ->
           acts =
           filter (fun act : action => filterRaiseStmt act (eventId v))
             (transitionIntoBasicActionList (stepActions stp)) ->
           (Datatypes.length acts <= 1)%nat) ).
    intros.
    apply H with (sce:=sce) (v:=v) (stp:=stp);auto.
         
    assert (
      (forall (sce : scenario) (stp : step) (acts : list action),
       In sce (scenarios mon) ->
       In stp (getTransitionsOfScenario sce) ->
       acts =
       filter (fun act : action => filterRaiseStmt act (eventId a))
              (transitionIntoBasicActionList (stepActions stp)) -> (Datatypes.length acts <= 1)%nat)).
    apply H;auto. 
   assert (checkRaiseInStp a (scenarios mon)).
   apply  checkRaiseInStp_rev_cor;auto. rewrite H2.
 
   
   
 
 apply IHlst;auto. 

Qed.

Lemma checkNoDup_cor_dec_all_left: forall mon,
    ( (forall v, In v (events mon) -> 
    (forall (sce : scenario) (stp : step) (acts : list action),
 In sce (scenarios mon) ->
 In stp (getTransitionsOfScenario sce) ->
 acts =
 filter (fun act : action => filterRaiseStmt act (eventId v))
        (transitionIntoBasicActionList (stepActions stp)) -> (Datatypes.length acts <= 1)%nat))) <-> checkNoDup' mon (events mon).  
Proof.
  intros;split;intros.   
   apply checkNoDup_cor_rev';auto.
  apply checkNoDup_cor' with (lst:=events mon) (mon:=mon) (v:=v) (sce:=sce) (stp:=stp);auto.
Qed.


Lemma checkNoDup_cor_ds: forall mon,
    checkNoDup mon (events mon) ->
    noDupRaise' mon. 
Proof.
  intros.
  unfold noDupRaise'.
  intros. 
  apply checkNoDup_cor with (v:=v) in H;auto. 
Qed.

Lemma checkNoDup_cor_rev_ds: forall mon,
   noDupRaise' mon -> checkNoDup mon (events mon)
    . 
    Proof.
      intros.
      unfold noDupRaise' in H.
      apply checkNoDup_cor_rev;auto. 
    Qed.

Lemma checkNoDup_cor_dec_all: forall mon,
    noDupRaise' mon <-> checkNoDup mon (events mon).  
Proof.
  intros;split;intros.   
  apply checkNoDup_cor_rev_ds;auto.
  apply checkNoDup_cor_ds;auto.
Qed.

(*noMergeError'*)
Fixpoint noInterCheck l1 l2 : bool :=
  match l1 with
  | [] => true
  | s::l1' => if inList (event_definition_dec) s l2 then
                false
              else
                noInterCheck l1' l2
  end.                            

Print noMergeError'.

Fixpoint aux_check_sce sce l : bool :=
  match l with
  | nil => true
  | s::l' => if scenario_dec sce s then
               aux_check_sce sce l'
             else
               if andb (noInterCheck (alphabet s) (alphabet sce)) (noInterCheck (alphabet sce) (alphabet s)) then
                 aux_check_sce sce l'
               else
                 false
end. 

Fixpoint aux_check_sce' l' l : bool :=
  match l' with
  | nil => true
  | s::l'' => if  aux_check_sce s l then
               aux_check_sce' l'' l
             else               
                 false
  end.


Lemma noInterCheck_cor: forall l1 l2,
    noInterCheck l1 l2 ->
    (forall e, In e l1 -> ~ (In e l2)). 
Proof.
  intro l1;induction l1.   
  - intros. inversion H0.
  - intros. destruct H0;subst.
    simpl in H. 
    remember (inList event_definition_dec e l2). 
    destruct b. 
    inversion H.
    unfold not. intros.
    symmetry in Heqb.
    SearchAbout inList.
    apply reverseinListFalse in Heqb. apply Heqb;auto.
    simpl in H.
    remember (inList event_definition_dec a l2).
    destruct b. inversion H.
    apply IHl1 with (e:=e) in H;auto. 
Qed.

Lemma noInterCheck_cor_rev: forall l1 l2,
    (forall e, In e l1 -> ~ (In e l2)) -> noInterCheck l1 l2
    . 
Proof.
  intro l1;induction l1.   
  - intros. simpl in *. auto. 
  - intros. simpl in *.
    remember (inList event_definition_dec a l2 ).
    destruct b.
    symmetry in Heqb. apply reverseinListLemma in Heqb.
    
    destruct H with (e:=a);auto.
    apply IHl1;auto. 
 
Qed. 

Lemma aux_check_sce_cor_rev : forall l sce1 ,
    (forall sce2, In sce2 l ->
    sce1 <> sce2 ->
    (forall e, In e (alphabet sce1) -> ~ In e (alphabet sce2)) /\
    (forall e, In e (alphabet sce2) -> ~ In e (alphabet sce1))) ->
    aux_check_sce sce1 l.
Proof.
  intro l;induction l. 
  -  intros. simpl. auto. 
  -  intros.
    
     simpl in *.
     destruct (scenario_dec sce1 a). subst.
     apply IHl;auto.     
     destruct H with (sce2:=a);auto.
    
     apply noInterCheck_cor_rev in H0.
     apply noInterCheck_cor_rev in H1.
     rewrite H0. rewrite H1;simpl.
     apply IHl.
     intros.
     apply H;auto. 
Qed.      
  
Lemma aux_check_sce_cor : forall l sce1 sce2 ,
    In sce2 l ->
    aux_check_sce sce1 l ->
    sce1 <> sce2 ->
    (forall e, In e (alphabet sce1) -> ~ In e (alphabet sce2)) /\
    (forall e, In e (alphabet sce2) -> ~ In e (alphabet sce1)).                                  
Proof. 
  intro l; induction l.
  - intros. inversion H.
  - intros.
    simpl in *.
    destruct H;subst.
    destruct (scenario_dec sce1 sce2).
    contradiction.
    remember (andb (noInterCheck (alphabet sce2) (alphabet sce1))
                   (noInterCheck (alphabet sce1) (alphabet sce2))).
    destruct b.
    remember (noInterCheck (alphabet sce2) (alphabet sce1)).
    destruct b.
    remember (noInterCheck (alphabet sce1) (alphabet sce2)).
    destruct b. Focus 2. simpl in Heqb. inversion Heqb.
    Focus 2. simpl in Heqb;inversion Heqb.
    Focus 2. inversion H0.
    symmetry in Heqb0; symmetry in Heqb1.
    split;intros. 
    apply noInterCheck_cor with (e:=e) in Heqb1;auto.
    apply noInterCheck_cor with (e:=e) in Heqb0;auto.
    destruct (scenario_dec sce1 a);auto.
    remember (noInterCheck (alphabet a) (alphabet sce1)). 
    remember (noInterCheck (alphabet sce1) (alphabet a)).     
    destruct b0;destruct b;simpl in *.
    apply IHl with (sce1:=sce1) in H;auto. inversion H0. inversion H0. inversion H0. 
Qed. 

Lemma aux_check_sce_cor_rev': forall l1 l2 , 
  (forall sce1 sce2,  In sce1 l1 -> In sce2 l2 ->
  sce1 <> sce2 -> noIntersection (alphabet sce1) (alphabet sce2)) ->
  aux_check_sce' l1 l2. 
Proof.
    intro l1;induction l1. 
- intros. simpl. auto. 
- intros.
  simpl in *.  
  assert (aux_check_sce a l2).
  apply   aux_check_sce_cor_rev .
  intros.
  unfold noIntersection in H.
  apply H;auto.
  rewrite H0.
  apply IHl1;auto.   
Qed.

Lemma aux_check_sce_cor': forall l1  l2,
    aux_check_sce' l1 l2 ->
    ( forall sce1 sce2 : scenario,
  In sce1 l1 ->
  In sce2 l2 ->
  sce1 <> sce2 -> noIntersection (alphabet sce1) (alphabet sce2)). 
Proof.
  intro l1;induction l1.
  -  intros. inversion H0.
  - intros.  
    destruct H0;subst.
    unfold noIntersection.
    apply aux_check_sce_cor with (l:=l2);auto.
    simpl in H.
    remember (aux_check_sce sce1 l2 ).
    destruct b;auto.
    simpl in H.
   
        remember (aux_check_sce a l2 ).
        destruct b;auto.
        Focus 2. inversion H.
    
    apply IHl1 with (l2:=l2);auto.
Qed. 

      
Fixpoint noMergeCheck (mon: object) (l: list atom) : bool :=
  match l with
  | nil => true
  | v::l' => if Nat.leb (Datatypes.length (scenarioUpdateVar (scenarios mon) v))  1 then
               noMergeCheck mon l'
             else
               if aux_check_sce' (scenarioUpdateVar (scenarios mon) v) (scenarioUpdateVar (scenarios mon) v) then
                 noMergeCheck mon l'
               else
                 false
  end.



Lemma noMergeCheck_cor: forall l mon v , noMergeCheck mon l -> 
  In v l ->
  (Datatypes.length (scenarioUpdateVar (scenarios mon) v) <= 1)%nat \/
  (forall sce1 sce2 : scenario,
   In sce1 (scenarioUpdateVar (scenarios mon) v) ->
   In sce2 (scenarioUpdateVar (scenarios mon) v) ->
   sce1 <> sce2 -> noIntersection (alphabet sce1) (alphabet sce2)).
Proof.
  intro l;induction l.
  - intros. inversion H0.
  - intros.
    simpl in H.
    remember ((Datatypes.length (scenarioUpdateVar (scenarios mon) a) <=? 1)%nat).
    destruct b.
    destruct H0;subst. 
    left;auto. destruct ((scenarioUpdateVar (scenarios mon) v));simpl in *. omega.
    destruct l0;simpl in *. omega. inversion Heqb.
    apply IHl with (v:=v) in H;auto.
    destruct H0;subst.
    right.
    remember (aux_check_sce' (scenarioUpdateVar (scenarios mon) v) (scenarioUpdateVar (scenarios mon) v)). destruct b.
    
    Focus 2. inversion H.
    symmetry in Heqb0.
    intros. 
    apply aux_check_sce_cor' with (sce1:=sce1) (sce2:=sce2) in Heqb0;auto.
    
    remember (aux_check_sce' (scenarioUpdateVar (scenarios mon) a) (scenarioUpdateVar (scenarios mon) a)). destruct b.
    apply IHl;auto. inversion H. 
Qed.

Lemma noMergeCheck_rev_cor: forall l mon , 
 (forall v, In v l ->
  (Datatypes.length (scenarioUpdateVar (scenarios mon) v) <= 1)%nat \/
  (forall sce1 sce2 : scenario,
   In sce1 (scenarioUpdateVar (scenarios mon) v) ->
   In sce2 (scenarioUpdateVar (scenarios mon) v) ->
   sce1 <> sce2 -> noIntersection (alphabet sce1) (alphabet sce2))) ->
  noMergeCheck mon l .
Proof.
  intro l;induction l.
  - intros. simpl ;auto. 
  - intros.
    simpl in *.
    assert ((Datatypes.length (scenarioUpdateVar (scenarios mon) a) <= 1)%nat \/
      (forall sce1 sce2 : scenario,
       In sce1 (scenarioUpdateVar (scenarios mon) a) ->
       In sce2 (scenarioUpdateVar (scenarios mon) a) ->
       sce1 <> sce2 -> noIntersection (alphabet sce1) (alphabet sce2))).
    apply H;auto.
    destruct H0.
    destruct ((scenarioUpdateVar (scenarios mon) a)).
    simpl;auto.
    destruct l0;auto.
    simpl in *;auto.
    inversion H0. inversion H2.
    destruct ((Datatypes.length (scenarioUpdateVar (scenarios mon) a) <=? 1)%nat);auto.
    assert (aux_check_sce' (scenarioUpdateVar (scenarios mon) a) (scenarioUpdateVar (scenarios mon) a)). apply aux_check_sce_cor_rev';auto. 
       rewrite H1;auto.   
   Qed.

Print noMergeError'.

Lemma  noMergeCheck_cor_ds : forall mon,
    noMergeCheck mon (dom (dsmon mon)) ->
    noMergeError' mon. 
Proof.
  intros.
  unfold noMergeError' .
  intros.
  apply noMergeCheck_cor with (l:=dom (dsmon mon));auto. 
Qed.

Lemma  noMergeCheck_cor_rev_ds : forall mon,
    noMergeError' mon ->
    noMergeCheck mon (dom (dsmon mon))
    . 
Proof.
  intros.
  unfold noMergeError' in H.
  intros.
  apply noMergeCheck_rev_cor;auto. 
 
Qed.

Lemma  noMergeCheck_cor_all : forall mon,
    noMergeError' mon <->
    noMergeCheck mon (dom (dsmon mon))
    . 
Proof.
  intros;split;intros.
  apply noMergeCheck_cor_rev_ds;auto.
  apply noMergeCheck_cor_ds;auto. 

Qed.
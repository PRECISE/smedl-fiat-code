(*proofs for wellformedness*)

Require Import Coq.Sets.Ensembles.
Require Import  Coq.omega.Omega.

Require Import Fiat.ADT Fiat.ADTNotation.

Require Export smedlDef.SmedlAST_submission.
Require Export smedlDef.semantic_rules.


Require Import Coq.Lists.List.
Print configuration.

Check importEventBool.

Require Coq.Bool.Bool.
Require Coq.Lists.ListDec.

Require Import Coq.Strings.String.

Definition range := 
  fun (A B : Type) (env : list (A * B)) => map (fun v : A * B => snd v) env.





Lemma typeValMatch_refl: forall ty v,
    typeValMatch ty v <-> tyEnvPair ty v.
Proof. 
  intros.
  split. 
  - intros. destruct ty;unfold tyEnvPair;inversion H;destruct v;inversion H;auto;destruct s;inversion H;auto;destruct s;inversion H;auto;destruct s;inversion H;auto.
  -  intros. destruct ty;unfold tyEnvPair in H;destruct v;(try destruct s;try (inversion H);auto).

     destruct s;try (inversion H);auto. destruct s;try (inversion H);auto.
     destruct s;try (inversion H);auto. destruct s;try (inversion H);auto.

     destruct s;try (inversion H);auto.
 Qed. 

                        

Print stateEvStepMap.
Print object. 

Definition eventListObjectEquiv (mon: object) : Prop := eventList = events mon.


Definition stpStMapEquiv (mon:object) :=
  (forall st ei stp, In (st,ei,Some stp) (stateEvStepMap mon) <-> stpStMap (st, ei) = Some stp).

Definition stpStMapEquiv' (mon:object) :=
  uniqList (dom (stateEvStepMap' mon)). 

Definition stpStMapEquiv'' (mon:object) :=
  (forall st ei stp sce, In (st,ei,sce,Some stp) (stateEvStepMap' mon) <-> stpStMap' (st, ei,sce) = Some stp).

Print step.

Definition correctStateEvStepMap (mon:object) := 
  (forall st ei stp, In (st,ei,Some stp) (stateEvStepMap mon) ->
                     (stepEvent stp = ei) /\ (pre_state stp = st)).

Definition correctStateEvStepMap' (mon:object) := 
  (forall st ei stp sce, In (st,ei,sce,Some stp) (stateEvStepMap' mon) ->
                     (In stp (traces sce) /\ (stepEvent stp = ei) /\ (pre_state stp = st))). 


Definition stateEvDefInstanceMapEquiv' (mon :object):=
  (forall st ev eList, In (Some st, Some ev, eList) (stateEvDefInstanceMap mon)
                       <-> transEvMap (Some st, Some ev) = eList). 

Print object. 
           
Definition stateEvDefInstanceMapEquiv (mon :object):=
  uniqList (dom (stateEvDefInstanceMap mon)) /\ 
           (forall sce s e, In (sce, s) (stateScenarioMap mon) ->
            In e (alphabet sce) -> (exists el, el <> nil /\ In (Some s, Some e, el) (stateEvDefInstanceMap mon))).

           
Definition transEvMapProp (mon: object) : Prop :=
  forall st e lst, In (Some st, Some e, lst) (stateEvDefInstanceMap mon) ->
                    (forall ei, In ei lst -> (event ei = e)).



Print correct_configuration. 
Definition uniqDSDom (mon:object) := uniqList (dom (dsmon mon)). 
  
Definition ConfigOfMon `(conf:configuration M) (mon:object) : Prop :=
  (dom (controlstate conf)) = (scenarios mon) /\ (*same scenarios*)
  (dom (datastate conf)) = (dom (dsmon mon)) /\
  (forall e, In e (raisedevents conf) -> In (eventDefinition e) (events mon)) /\
  (forall e, In e (exportedevents conf) -> In (eventDefinition e) (events mon)) /\
  (forall sce st e0 s0, In (sce,st) (controlstate conf) -> In (st, e0, Some s0) (stateEvStepMap M) -> (In s0 (traces sce) /\  (pre_state s0 = st))). (*same state variables*)


(*type check signature*)
Inductive typeCheckTypeSignatures:  typ_env -> list typ -> list expr -> Prop :=
| basic_typSig : forall env, typeCheckTypeSignatures env [] []
| ind_typSig: forall env (t:typ) ex (ts':list typ) (eL':list expr), typeCheckTypeSignatures env ts' eL' -> HasTy env ex t -> typeCheckTypeSignatures env (t::ts') (ex::eL').                                                   
 (* match (tS,eL) with
  | (nil,nil) => True
  | (t::ts',ex::eL') => translateTyp t = returnTyp ex env/\ typeCheckTypeSignatures ts' eL' env                                   
  | _ => False
  end. *)              


Fixpoint createTypEnv (nlst : list string) (tlst : list typ) :
  ErrorOrResult :=
  match (nlst,tlst) with
  | ([],[]) => Result []
  | (s :: nlst', t::tlst') =>
        match createTypEnv nlst' tlst' with
          | Result ve => Result ((AIdent s, t) :: ve)
          | Error s0 => Error s0
        end
   
   | (_,_) => Error "number of list not matched" 
  end.

Print extendEnv. 


(*type check each action*)




Definition typeCheckInstance (ei : event_instance) (env: typ_env) : Prop :=
  (List.length (eventArgs ei) = List.length (eventParams (event ei))) /\ HasTy env (eventWhenExpr ei) Bool /\ uniqList (dom env).

Print expr. 
Definition excludedBoolExpr (e1: expr) (e2: expr) : Prop :=
  match e2 with
  | ENot x => if expr_eq_dec x e1 then True else False
  | _ => False
  end
.
  
Print event_instance.

Print getScenarioState.
SearchAbout controlstate. 

Definition alphabetInObject (mon:object) : Prop :=
  forall e sce, In sce (scenarios mon) -> In e (alphabet sce) -> In e (events mon).

Print event_definition. 
Definition alphabetRaisingObject (mon:object) : Prop :=
  forall e , In e (events mon) -> eventKind e = Internal \/ eventKind e = Imported -> (exists sce, In sce (scenarios mon) /\ In e (alphabet sce)). 
    
Definition alphabetScenario' (mon:object) : Prop :=
  forall sce e st, In sce (scenarios mon) -> In e (alphabet sce) -> (exists (stp:step) (elst: list event_instance), In stp (traces sce) /\  st = (pre_state stp) /\ (In (Some st, Some e, elst) (stateEvDefInstanceMap mon) /\ elst <> nil)).

Definition alphabetScenario (mon:object) : Prop :=
  forall sce e , In sce (scenarios mon) -> In e (alphabet sce) -> (exists (stp:step) (elst: list event_instance) st, In stp (traces sce) /\  st = (pre_state stp) /\ (In (Some st, Some e, elst) (stateEvDefInstanceMap mon) /\ elst <> nil)). 

Definition alphabetScenario_rev (mon:object) : Prop :=
  forall sce e st, In sce (scenarios mon) ->  (exists (stp:step) (elst: list event_instance), In stp (traces sce) /\  st = (pre_state stp) /\ (In (Some st, Some e, elst) (stateEvDefInstanceMap mon) /\ elst <> nil)) -> In e (alphabet sce). 


Definition alphabetStep (mon:object) : Prop :=
  forall  st e lst, In (Some st, Some e, lst) (stateEvDefInstanceMap mon) -> (forall ei, In ei lst -> (exists stp, In (st, ei, Some stp) (stateEvStepMap mon) /\ st = pre_state stp)).

Print object.

Definition stateSceProp (mon:object) : Prop :=
  forall s e l  sce,  In (Some s, Some e, l) (stateEvDefInstanceMap mon) ->
                         In (sce,s) (stateScenarioMap mon) ->
                        In e (alphabet sce).

Print scenario.

Definition stateSceIn (mon:object) : Prop :=
  forall sce s, In sce (scenarios mon) ->
                In (sce,s) (stateScenarioMap mon) <-> (exists step, In step (traces sce) /\ (pre_state step = s \/ pro_state step = s)).

Definition stepStateSceIn (mon:object) : Prop :=
  forall sce stp , In sce (scenarios mon) -> In stp (traces sce) ->
                    In (sce, (pre_state stp)) (stateScenarioMap mon)
                    /\ In (sce, (pro_state stp)) (stateScenarioMap mon).

Print object. 


(*
Definition reverseAlphabetScenario (mon:object) : Prop :=
  forall sce e  stp st,  ~ In e (alphabet sce) -> In sce (scenarios mon) -> In stp (traces sce)  -> st = (pre_state stp) ->  ~ (exists lst, In (Some st, Some e, lst) (stateEvDefInstanceMap mon) /\ lst <> nil).
*)


Definition stateEvDefInstanceMapEquivEListProp (mon: object):=
  (forall st ev eList, In (Some st, Some ev, eList) (stateEvDefInstanceMap mon) -> eList <> nil -> 
                       (exists e1 e2, eList = e1 :: e2 :: nil /\
                                      eventArgs e1 = eventArgs e2 /\
                                      let ex1 := createTypEnv (eventArgs e1) (eventParams (event e1)) in
                                      let ex2 := createTypEnv (eventArgs e2) (eventParams (event e2)) in
                                      match ex1, ex2 with
                                      | Result ex1', Result ex2' =>
                                        typeCheckInstance e1 (dsmon mon ++ ex1') /\ typeCheckInstance e2 (dsmon mon ++ ex2') /\ excludedBoolExpr (eventWhenExpr e1) (eventWhenExpr e2)
                                     | _, _ => False
                                       end))
  . 




(*type check each transition*)

Print extendEnv.
Print object.
Print filter.
Definition typeCheckStep (mon:object) (stp:step)  : Prop :=
   let ei := (stepEvent stp) in
  let extendedEnv := createTypEnv (eventArgs ei) (eventParams (event ei)) in
  match extendedEnv with
  | Error _ => False
  | Result ex => let ex_env := ( ((identities mon) ++ (variables mon)) ++ ex) in typeCheckInstance ei ex_env /\ HasTy_action ex_env (filter (fun e => match (eventKind e) with
                                                    | Imported => false
                                                    | _ => true
                                                                         
                                                   end) (events mon)) (stepActions stp)
  end.
    
  
(*type check for each scenario*)
Definition typeCheckScenario (mon:object)  (sce:scenario) : Prop :=
  let stps := getTransitionsOfScenario sce in
  forall stp, In stp stps -> typeCheckStep mon stp.

(*type check the monitor*)
Definition typeCheck (mon:object) : Prop :=
  forall sce, In sce (scenarios mon) -> typeCheckScenario mon sce.



Print tyEnv.

Print event_instance. 




Lemma raisedTyEnv: forall vl tl nl v,
    parameterMatch vl tl->
    Result v = createValueEnv nl tl vl ->
    tyEnv v.
Proof.
    intro vl;induction vl.   
    - intros. 
      destruct tl. destruct nl. simpl in H0. inversion H0;auto. 
      apply ty_base. simpl in H0. inversion H0.
      destruct nl. simpl in H0. inversion H0. inversion H0. 
    -  intros.
       destruct nl. destruct tl. simpl in H0. inversion H0. simpl in H0. inversion H0.
       destruct tl. simpl in H0. inversion H0.
       simpl in H0.
       remember (createValueEnv nl tl vl).
       destruct e.
       
       inversion H;subst.
       apply IHvl in Heqe;auto.
       inversion H0;subst.
       Print tyEnv.
       apply ty_ind;auto.
       rewrite <- typeValMatch_refl;auto.
    inversion H0.        
Qed.

       
      
Lemma raised_wellform: forall M (conf : configuration M) e,
    correct_configuration conf -> In e (raisedevents conf) ->
    wellFormedRaisedEvent e.
Proof.
  intros. destruct H;auto. 
Qed.


Lemma correct_configuration_tyEnv: forall M (conf : configuration M),
    correct_configuration conf -> tyEnv (datastate conf).
Proof. 
    intros. destruct H;auto. 
Qed.

Definition raised_wellform_prop `(conf:configuration M) := forall e, In e (raisedevents conf) -> wellFormedRaisedEvent e.



Lemma findEventInstanceIn: forall lst e0 e env ,
Some e0 = findEventInstance e env lst ->
In e0 lst.
Proof. intro lst. induction lst;simpl;intros.
- inversion H.
- remember (eventWhenExpr a). 
remember (createValueEnv (eventArgs a) (eventParams (eventDefinition e)) (eventArguments e)).
destruct e2;inversion H. 
remember (evalMonad (extendValEnv env v) e1).
destruct e2;inversion H.
destruct v0;auto;inversion H.
destruct s;inversion H3;auto.
destruct b. inversion H;subst. left;auto.
right.
apply IHlst in H;auto. 
Qed.


Lemma findInstanceDef: forall lst e re ds ,
    Some e =  findEventInstance re ds lst ->
    (forall ei, In ei lst -> event ei = eventDefinition re) ->
    event e = eventDefinition re.
Proof.
  pose proof findEventInstanceIn.
  intros.
  apply H1.
  eapply H;auto.
  apply H0. 
Qed.


Lemma findInstanceDefMon: forall lst re st ei ds mon ,
     transEvMapProp mon ->
    In (Some st, Some (eventDefinition re), lst) (stateEvDefInstanceMap mon) ->
    Some ei =  findEventInstance re ds lst ->
    event ei = eventDefinition re.
Proof.
  
  pose proof findInstanceDef.
  pose proof findEventInstanceIn. 
  intros.
  unfold  transEvMapProp in H1.
  remember H2.
  clear Heqi.  
  apply H1 with (ei:=ei) in H2.
  Focus 2.
  eapply H0;auto.
  apply H3.
  apply H2. 
Qed.

Lemma createValEnvCorrect: forall nlst tlst vlst s,
    List.length nlst = List.length tlst ->
    List.length nlst = List.length vlst ->
    createValueEnv nlst tlst vlst <> Error s. 
Proof.
  intro nlst;induction nlst. 
  intros. destruct tlst; destruct vlst. 
  simpl. unfold not. intros. inversion H1. 
  inversion H0. 
  inversion H.
  inversion H.
  intros.
  simpl.
  destruct tlst.
  inversion H.
  destruct vlst.
  inversion H0.
  remember ( createValueEnv nlst tlst vlst).
  destruct e.
  inversion H.  inversion H0.
  simpl. unfold not. intros. inversion H1.
  inversion H.  inversion H0.
  assert (createValueEnv nlst tlst vlst <> Error s0).
  apply IHnlst;auto.
  exfalso;apply H1;auto.
Qed.

Lemma createValEnvCorrect': forall nlst tlst vlst ,
    List.length nlst = List.length tlst ->
    List.length nlst = List.length vlst ->
    (exists v, Result v= createValueEnv nlst tlst vlst).
Proof.
  intro nlst;induction nlst. 
  intros. destruct tlst; destruct vlst. 
  simpl. exists [];auto. inversion H0.  inversion H.
  inversion H.
  intros.
  destruct tlst;inversion H. destruct vlst;inversion H0.
  simpl. 
  remember ( createValueEnv nlst tlst vlst).
  destruct e.
  inversion H.  inversion H0.
  simpl. exists (((AIdent a, (t, r)) :: v));auto.
  apply IHnlst with (vlst:=vlst) in H2;auto.
  destruct H2. rewrite <-H1 in Heqe;inversion Heqe. 
 
Qed.

Definition transEvMapEventInstanceProp (mon: object) : Prop :=
  forall st e lst, In (Some st, Some e, lst) (stateEvDefInstanceMap mon) ->
                   (forall ei, In ei lst -> (exists stp sce , In sce (scenarios mon) /\ In stp (traces sce) /\ pre_state stp = st /\ stepEvent stp = ei) ).

(*Lemma traceIn: forall lst trace stp,
    In trace lst ->
    In stp (traceSteps trace) ->
    In stp (getTransitionsFromTraces lst).
Proof.  
  intro lst;induction lst. 
  intros. inversion H.
  intros.
  inversion H;subst.
  simpl in H. destruct H;subst.
  simpl.
  SearchAbout "++".
  rewrite in_app_iff. left;auto.
  simpl.
  rewrite in_app_iff. left;auto.
  simpl.
  rewrite in_app_iff. right;auto.
  apply IHlst with (trace0:=trace);auto.
Qed.
 *)

Print typeCheckInstance.

Lemma eventInstanceTypeCorrect: forall mon st e lst ei,
    In (Some st, Some e, lst) (stateEvDefInstanceMap mon) ->
    transEvMapEventInstanceProp mon ->
    typeCheck mon ->
    In ei lst ->
    (exists t_env, typeCheckInstance ei t_env).
Proof. 
   intros. 
   unfold typeCheck in H1.
   unfold transEvMapEventInstanceProp in H0.
   apply H0  with (ei:=ei) in H;auto.
   destruct H.
   destruct H.
   destruct H.
   apply H1 in H. 
   unfold typeCheckScenario in H.
   destruct H3.
   destruct H4.
   unfold getTransitionsOfScenario in H.
  
   apply H in H3.
   unfold typeCheckStep in H3.
   destruct (createTypEnv (eventArgs (stepEvent x)) (eventParams (event (stepEvent x))));inversion H3.
   unfold extendEnv in H3. 
   destruct H3. exists (( (identities mon ++ variables mon) ++ v)). 
   
   rewrite H5 in H3.
   auto. 
Qed.

Print sce_state_no_empty. 

Definition stepExistsMon (mon: object) : Prop :=
  forall s ei e l,
    In (Some s, Some e, l)  (stateEvDefInstanceMap mon) ->
    In ei l ->
    (exists stp, In (s, ei, Some stp) (stateEvStepMap mon)).

Definition stepExistsMon' (mon: object) (sce:scenario): Prop :=
  forall s ei e l,
    In (Some s, Some e, l)  (stateEvDefInstanceMap mon) ->
    In ei l ->
    In e (alphabet sce) ->
    (exists stp, In (s, ei, sce, Some stp) (stateEvStepMap' mon)).

Definition stepExistsMon'' (mon: object) (sce:scenario): Prop :=
  forall s ei e l,
    In (Some s, Some e, l)  (stateEvDefInstanceMap mon) ->
    In ei l ->
    (exists stp, In (s, ei, sce, Some stp) (stateEvStepMap' mon)).

Lemma findInstanceEvalTrue: forall l e re env  v ,
    Some e = findEventInstance re env l ->
    Result v = createValueEnv (eventArgs e) (eventParams (event e)) (eventArguments re) ->
    event e = eventDefinition re ->
    evalMonad (extendEnv env v) (eventWhenExpr e) = Result (inl (inr true)). 
Proof.
  intro l;induction l.
  -  intros.
     simpl in H. 
     inversion H.
  - intros.
    simpl in H.
   
    remember (createValueEnv (eventArgs a) (eventParams (eventDefinition re)) (eventArguments re)).
    destruct e0;inversion H.
    remember (evalMonad (extendValEnv env v0) (eventWhenExpr a)).
    destruct e0;inversion H.
    destruct v1;inversion H.
    destruct s;inversion H.
    destruct b. Focus 2.
    
    apply IHl with (e:=e) (re:=re);auto.
    inversion H3;subst.
    rewrite H1 in H0.
    rewrite <- H0 in Heqe0. inversion Heqe0;subst. auto. 
Qed.

Lemma paraLengthEq: forall lst1 lst2,
    parameterMatch lst1 lst2 ->
    Datatypes.length lst1 = Datatypes.length lst2. 
Proof. intros.
       induction H. auto.
       simpl. f_equal. 
       auto. 
      
 Qed. 

Lemma inControlState: forall env sce s,
Some s = getScenarioState sce (env) ->
In sce (dom (env)) ->
In (sce,s) env.
Proof. intro env. induction env.
- intros. inversion H0.
- intros. destruct H0. simpl in H. 
destruct a. simpl in H0. subst.    
destruct (string_dec (scenarioId sce) (scenarioId sce)).
inversion H. subst. left;auto.
exfalso;apply n;auto.
simpl in H. destruct a.   
destruct (string_dec (scenarioId sce) (scenarioId s0)).
SearchAbout scenarioId. rewrite ScenarioEquivalence in e. subst. inversion H. subst. left;auto.     
 right. apply IHenv;auto.
Qed.


Lemma getStepMap: forall M (conf : configuration M) sce s0 e0 s,
Some s0 = getStep conf sce e0 ->
Some s = getScenarioState sce (controlstate conf) ->
Some s0 = stpStMap (s, e0).
Proof. intros. 
 Print getStep.
unfold  getStep in H.
rewrite <- H0 in H. auto.
Qed.

Lemma getStepMap': forall M (conf : configuration M) sce s0 e0 s,
Some s0 = getStep' conf sce e0 ->
Some s = getScenarioState sce (controlstate conf) ->
Some s0 = stpStpMapFunc (stateEvStepMap' M) (s, e0, sce).
Proof. intros. 
 
unfold  getStep' in H.
rewrite <- H0 in H. auto.
Qed.

Print configTransition. 





(*need to modify HasTy_action to state that event name occurs in the internal or exported events of mon*)
(*distinct internal, imported and exported events in object*)
(*well typed value_env -> well-typed expression -> well-typed cmd -> evalMonad returns true and value returned should have the same type as the variable being assigned*)
(*well type -> variables in createValueEnv is well typed*)



    
Lemma evalMonadCorrect: forall ex env t_env ty,
    uniqList (dom env) ->
    tyEnv env ->
    HasTy t_env ex ty ->
    evnConsist t_env env ->
    (exists v, Result v = evalMonad env ex /\ typeValMatch ty v). 
Proof.
  intro ex. induction ex.
  - intros env t_env ty u. intros. 
    inversion H0;inversion H0;subst.
    simpl.
    unfold BindBool. unfold Bind.
    apply IHex1 with (env:=env) in H4;auto.
    apply IHex2 with (env:=env) in H6;auto.
    repeat (match goal with
            | [H: _ /\ _ |-_] => destruct H
            | [H: exists _, _ |- _] => destruct H
            end).
    simpl in H5.  destruct x0;inversion H5. destruct s;inversion H5.
    simpl in H3.  destruct x;inversion H3. destruct s;inversion H3.
    rewrite <- H4;rewrite <- H2;auto. exists ((inl (inr (b || b0)%bool)) );auto.
 - intros env t_env ty u. intros. 
    inversion H0;inversion H0;subst.
    simpl.
    unfold BindBool. unfold Bind.
    apply IHex1 with (env:=env) in H4;auto.
    apply IHex2 with (env:=env) in H6;auto.
    repeat (match goal with
            | [H: _ /\ _ |-_] => destruct H
            | [H: exists _, _ |- _] => destruct H
            end).
    simpl in H5.  destruct x0;inversion H5. destruct s;inversion H5.
    simpl in H3.  destruct x;inversion H3. destruct s;inversion H3.
    rewrite <- H4;rewrite <- H2;auto. exists ((inl (inr (b && b0)%bool)) );auto.
 - intros env t_env ty u. intros. 
   inversion H0;subst.
   simpl.
   unfold BindData. unfold Bind.
    apply IHex1 with (env:=env) in H4;auto.
    apply IHex2 with (env:=env) in H6;auto.
    repeat (match goal with
            | [H: _ /\ _ |-_] => destruct H
            | [H: exists _, _ |- _] => destruct H
            end).
    destruct t;simpl in H5;simpl in H3.
    destruct x0;destruct x;inversion H5;inversion H3;destruct s0;destruct s;inversion H3;inversion H5;destruct s;destruct s0;inversion H3;inversion H5;destruct s;destruct s0;rewrite <- H4;rewrite <- H2;inversion H3;inversion H5;simpl.
    exists ((inl (inr (z =? z0)%Z)));auto.

    destruct x0;destruct x;inversion H5;inversion H3;destruct s0;destruct s;inversion H3;inversion H5;destruct s;destruct s0;inversion H3;inversion H5;destruct s;destruct s0;rewrite <- H4;rewrite <- H2;inversion H3;inversion H5;simpl.
    exists ((inl (inr (QArith_base.Qeq_bool q q0))));auto.

    destruct x0;destruct x;inversion H5;inversion H3;destruct s0;destruct s;inversion H3;inversion H5;destruct s;destruct s0;inversion H3;inversion H5;destruct s;destruct s0;rewrite <- H4;rewrite <- H2;inversion H3;inversion H5;simpl.
    exists ((inl (inr (string_dec_bool "" ""))));auto.
    exists ((inl (inr (string_dec_bool "" (String a s0)))));auto. 
    exists ((inl (inr (string_dec_bool (String a s) ""))));auto. 
    exists ((inl (inr (string_dec_bool (String a s) (String a0 s0)))));auto.

     destruct x0;destruct x;inversion H5;inversion H3;destruct s0;destruct s;inversion H3;inversion H5;rewrite <- H4;rewrite <- H2;inversion H3;inversion H5;simpl.
     exists (inl (inr (Bool.eqb b0 b)));auto.

     destruct x0;destruct x;inversion H5;inversion H3;inversion H3;inversion H5;rewrite <- H4;rewrite <- H2;inversion H3;inversion H5;simpl.
     exists (inl (inr (n =? n0)%nat));auto.
          destruct x0;destruct x;inversion H5;inversion H3;inversion H3;inversion H5;rewrite <- H4;rewrite <- H2;inversion H3;inversion H5;simpl.
          exists (inl (inr (n =? n0)%nat));auto.
               destruct x0;destruct x;inversion H5;inversion H3;inversion H3;inversion H5;rewrite <- H4;rewrite <- H2;inversion H3;inversion H5;simpl.
               exists (inl (inr (n =? n0)%nat));auto.
 -  intros env t_env ty u. intros. 
     inversion H0;subst. 
     simpl.
    unfold BindNum. unfold Bind.
    apply IHex1 with (env:=env) in H4;auto.
    apply IHex2 with (env:=env) in H6;auto.
    repeat (match goal with
            | [H: _ /\ _ |-_] => destruct H
            | [H: exists _, _ |- _] => destruct H
            end).
    simpl in H5.  destruct x0;inversion H5. destruct s;inversion H5.
    simpl in H3.  destruct x;inversion H3. destruct s;inversion H3.
    destruct s;inversion H5;destruct s0;inversion H3.
    destruct s;inversion H3;auto. destruct s;inversion H3.  
    rewrite <- H4;rewrite <- H2;auto. exists (inl (inr (z <? z0)%Z));auto.         
    destruct s0;inversion H5;destruct s0;inversion H3.

    simpl. 
    unfold BindNum. unfold Bind.
    apply IHex1 with (env:=env) in H4;auto.
    apply IHex2 with (env:=env) in H6;auto.
    repeat (match goal with
            | [H: _ /\ _ |-_] => destruct H
            | [H: exists _, _ |- _] => destruct H
            end).
    simpl in H5.  destruct x0;inversion H5. destruct s;inversion H5.
    simpl in H3.  destruct x;inversion H3. destruct s;inversion H3.
    destruct s;inversion H5;destruct s0;inversion H3.
    destruct s;inversion H3;auto. destruct s;inversion H3.  
    rewrite <- H4;rewrite <- H2;auto. exists ((inl (inr (QArith_base.Qle_bool q q0 && negb (QArith_base.Qeq_bool q q0))%bool)));auto.         
    destruct s0;inversion H5;destruct s0;inversion H3.
-  intros env t_env ty u. intros. 
     inversion H0;subst. 
     simpl.
    unfold BindNum. unfold Bind.
    apply IHex1 with (env:=env) in H4;auto.
    apply IHex2 with (env:=env) in H6;auto.
    repeat (match goal with
            | [H: _ /\ _ |-_] => destruct H
            | [H: exists _, _ |- _] => destruct H
            end).
    simpl in H5.  destruct x0;inversion H5. destruct s;inversion H5.
    simpl in H3.  destruct x;inversion H3. destruct s;inversion H3.
    destruct s;inversion H5;destruct s0;inversion H3.
    destruct s;inversion H3;auto. destruct s;inversion H3.  
    rewrite <- H4;rewrite <- H2;auto. exists (inl (inr (z <=? z0)%Z));auto.         
    destruct s0;inversion H5;destruct s0;inversion H3.

    simpl. 
    unfold BindNum. unfold Bind.
    apply IHex1 with (env:=env) in H4;auto.
    apply IHex2 with (env:=env) in H6;auto.
    repeat (match goal with
            | [H: _ /\ _ |-_] => destruct H
            | [H: exists _, _ |- _] => destruct H
            end).
    simpl in H5.  destruct x0;inversion H5. destruct s;inversion H5.
    simpl in H3.  destruct x;inversion H3. destruct s;inversion H3.
    destruct s;inversion H5;destruct s0;inversion H3.
    destruct s;inversion H3;auto. destruct s;inversion H3.  
    rewrite <- H4;rewrite <- H2;auto. exists (inl (inr (QArith_base.Qle_bool q q0)));auto.         
    destruct s0;inversion H5;destruct s0;inversion H3.
- intros env t_env ty u. intros.  inversion H0;subst;simpl;unfold BindNum;unfold Bind; apply IHex1 with (env:=env) in H4;auto; apply IHex2 with (env:=env) in H6;auto; repeat (match goal with
            | [H: _ /\ _ |-_] => destruct H
            | [H: exists _, _ |- _] => destruct H
            end);simpl in H5;simpl in H3;destruct x0;inversion H5;destruct s;inversion H5;
    simpl in H3;destruct x;inversion H3;destruct s;inversion H3;destruct s;inversion H5;destruct s0;inversion H3;destruct s;inversion H3;auto;destruct s;inversion H3;rewrite <- H4;rewrite <- H2;auto. exists (inl (inl (inl (inl (z + z0)%Z))));auto. 
  exists (inl (inl (inl (inr (QArith_base.Qplus q q0)))));auto.
-  intros env t_env ty u. intros.  inversion H0;subst;simpl;unfold BindNum;unfold Bind; apply IHex1 with (env:=env) in H4;auto; apply IHex2 with (env:=env) in H6;auto; repeat (match goal with
            | [H: _ /\ _ |-_] => destruct H
            | [H: exists _, _ |- _] => destruct H
            end);simpl in H5;simpl in H3;destruct x0;inversion H5;destruct s;inversion H5;
    simpl in H3;destruct x;inversion H3;destruct s;inversion H3;destruct s;inversion H5;destruct s0;inversion H3;destruct s;inversion H3;auto;destruct s;inversion H3;rewrite <- H4;rewrite <- H2;auto. exists (inl (inl (inl (inl (z * z0)%Z))));auto. 
  exists (inl (inl (inl (inr (QArith_base.Qmult q q0)))));auto.
- intros env t_env ty u. intros.
  inversion H0;subst;simpl;unfold BindNum;unfold Bind; apply IHex1 with (env:=env) in H4;auto; apply IHex2 with (env:=env) in H6;auto; repeat (match goal with
            | [H: _ /\ _ |-_] => destruct H
            | [H: exists _, _ |- _] => destruct H
            end);simpl in H5;simpl in H3;destruct x0;inversion H5;destruct s;inversion H5;
    simpl in H3;destruct x;inversion H3;destruct s;inversion H3;destruct s;inversion H5;destruct s0;inversion H3;destruct s;inversion H3;auto;destruct s;inversion H3;rewrite <- H4;rewrite <- H2;auto. exists (inl (inl (inl (inl (z / z0)%Z))));auto. 
  exists (inl (inl (inl (inr (QArith_base.Qdiv q q0))))) ;auto.
- intros env t_env ty u. intros.  inversion H0;subst;simpl;unfold BindZ;unfold Bind; apply IHex1 with (env:=env) in H4;auto; apply IHex2 with (env:=env) in H6;auto; repeat (match goal with
            | [H: _ /\ _ |-_] => destruct H
            | [H: exists _, _ |- _] => destruct H
            end);simpl in H5;simpl in H3;destruct x0;inversion H5;destruct s;inversion H5;
    simpl in H3;destruct x;inversion H3;destruct s;inversion H3;destruct s;inversion H5;destruct s0;inversion H3;destruct s;inversion H3;auto;destruct s;inversion H3;rewrite <- H4;rewrite <- H2;auto. exists (inl (inl (inl (inl (z mod z0)%Z))));auto. 
-  intros env t_env ty u. intros.  inversion H0;subst;simpl;unfold BindBool;unfold Bind. apply IHex with (env:=env) in H3;auto. repeat (match goal with
            | [H: _ /\ _ |-_] => destruct H
            | [H: exists _, _ |- _] => destruct H
            end). simpl in H3. destruct x;inversion H3;destruct s;inversion H3;rewrite <- H2;auto. exists (inl (inr (negb b)));auto. 
- intros env t_env ty u. intros. 
  
  pose proof valConsist. remember H1. clear Heqe. 
  inversion H0;subst.   
  apply H2 with (s:=s) (ty:=ty) in H1;auto.
  destruct H1.  simpl.
  pose proof getValueIn. remember H1. clear Heqi.  
  apply H3 in H1;auto. rewrite H1.
  inversion H. subst;inversion i. subst. simpl in i.
  destruct i. inversion H7;subst. unfold tyEnvPair in H6.
  
  destruct x. destruct s0. destruct s0. destruct s0 . destruct ty;inversion H6. 
  exists ((inl (inl (inl (inl z))))). split;auto.
  destruct ty;inversion H6. 
  exists (inl (inl (inl (inr q)))). split;auto.
  destruct ty;inversion H6.
  exists (inl (inl (inr s0))). split;auto.
   destruct ty;inversion H6. 
  exists (inl (inr b)). split;auto.
destruct ty;inversion H6.
exists (inr n) . split;auto.

  exists (inr n) . split;auto.

  exists (inr n) . split;auto.
  pose proof tyEnvIn. 
  apply H8 in H7;auto.
  destruct x. destruct s0. destruct s0. destruct s0 .
  exists (inl (inl (inl (inl z)))). split;auto.
  rewrite typeValMatch_refl;auto.

   exists (inl (inl (inl (inr q)))). split;auto.
   rewrite typeValMatch_refl;auto.

      exists (inl (inl ( (inr s0)))). split;auto.
   rewrite typeValMatch_refl;auto.

      exists ( (inl (inr b))). split;auto.
      rewrite typeValMatch_refl;auto.

         exists ( (inr n0)). split;auto.
   rewrite typeValMatch_refl;auto.
   
    exists ((inl (inl (inl (inl n)))) );auto.
    exists ((inl (inl (inl (inr q)))) );auto.
    exists ((inl (inr b)));auto. 
    exists ((inr 0%nat));auto.    
    exists ((inl (inl (inr s))));auto.   
Qed. 


Lemma updateEnvType: forall env t_env ty x s,
    uniqList (dom env) ->
    typeValMatch ty x ->
    evnConsist t_env env ->
    getType (AIdent s) t_env = Some ty ->
    (exists ven, Some ven = updateValueEnvInv (AIdent s) x env). 
Proof.                  
  intro env;induction env;intros. 
 - simpl. exists [];auto. 
 - simpl.
   destruct a;destruct p.
   destruct (atom_eq_dec (AIdent s) a).
   subst.
   inversion H1;subst. simpl in H2.
   destruct (atom_eq_dec (AIdent s) (AIdent s)).
   inversion H2;subst.
   destruct (typeValMatch ty x ). exists (((AIdent s, (ty, x)) :: env));auto.
   inversion H0.
   exfalso;apply n;auto.
   assert (exists ven : value_env, Some ven = updateValueEnvInv (AIdent s) x env).
   inversion H1;subst.
   
   apply IHenv with (t_env:=te) (ty:=ty);auto.
   inversion H;auto.
   simpl in H2. destruct (atom_eq_dec (AIdent s) (AIdent n0)).
   contradiction. auto.
   destruct H3. rewrite <- H3. exists ((a, (t, r)) :: x0);auto.
Qed. 


Lemma updateEnvDomNoChange: forall env s v  env',
    Some env' = updateValueEnvInv (AIdent s) v env ->
    dom env = dom env'. 
Proof.
     intro env;induction env;intros.     
     - simpl in H. inversion H;auto.
     - simpl in H.
       destruct a;destruct p.
       destruct (atom_eq_dec (AIdent s) a);auto;inversion H. 
       destruct (typeValMatch t v);inversion H;auto.
       remember (updateValueEnvInv (AIdent s) v env).
       destruct o. inversion H;simpl;auto. f_equal.
       apply IHenv with (s:=s) (v:=v);auto.
       inversion H.
Qed.

Lemma updateEnvDomNoChange': forall env s v  env',
    Some env' = updateValueEnvInv (AIdent s) v env ->
    dom2 env = dom2 env'. 
Proof.
     intro env;induction env;intros.     
     - simpl in H. inversion H;auto.
     - simpl in H.
       destruct a;destruct p.
       destruct (atom_eq_dec (AIdent s) a);auto;inversion H. 
       destruct (typeValMatch t v);inversion H;auto.
       remember (updateValueEnvInv (AIdent s) v env).
       destruct o. inversion H;simpl;auto. f_equal.
       apply IHenv with (s:=s) (v:=v);auto.
       inversion H.
Qed.

Lemma typeActionNoChange: forall action env v r  eventList l,
    Result (v,r) = execAction (env, l) action eventList ->
    dom env = dom v.
Proof. intro action;induction action.
       - intros;simpl in *. inversion H;auto. 
       - intros. simpl in H.
         destruct l;inversion H.
         destruct a;inversion H. 
         remember (evalMonad env e ).
         destruct e0;inversion H2.
         remember (updateValueEnvInv (AIdent s) v0 env).
         destruct o;inversion H;subst.
         apply updateEnvDomNoChange with (s:=s) (v:=v0);auto.
       - intros.
         simpl in H.
         destruct (calculateExprList env exprs);inversion H.
         destruct (getEventByName ident eventList );auto.
         destruct (parameterMatchFunc v0 (eventParams e));inversion H. 
         inversion H. auto. inversion H.
       - intros.
         simpl in H.
         remember (execAction (env, l) action1 eventList).
         destruct e;inversion H. 
         destruct v0.
         apply IHaction1 in Heqe.
         apply IHaction2 in H1.  rewrite H1 in Heqe;auto. 
Qed.

Lemma typeActionNoChangeDom2: forall action env v r  eventList l,
    Result (v,r) = execAction (env, l) action eventList ->
    dom2 env = dom2 v.
Proof. intro action;induction action.
       - intros;simpl in *;inversion H;auto. 
       - intros. simpl in H.
         destruct l;inversion H.
         destruct a;inversion H. 
         remember (evalMonad env e ).
         destruct e0;inversion H2.
         remember (updateValueEnvInv (AIdent s) v0 env).
         destruct o;inversion H;subst.
         Check updateEnvDomNoChange. 
         apply updateEnvDomNoChange' with (s:=s) (v:=v0);auto.
       - intros.
         simpl in H.
         destruct (calculateExprList env exprs);inversion H.
         destruct (getEventByName ident eventList );auto.
         destruct (parameterMatchFunc v0 (eventParams e));inversion H.
         inversion H. auto. inversion H.
       - intros.
         simpl in H.
         remember (execAction (env, l) action1 eventList).
         destruct e;inversion H. 
         destruct v0.
         apply IHaction1 in Heqe.
         apply IHaction2 in H1.  rewrite H1 in Heqe;auto. 
Qed.


Lemma updateEnvTy: forall env v s v1,
    tyEnv env ->
    Some v1 = updateValueEnvInv (AIdent s) v env ->
    tyEnv v1. 
Proof. 
 intro env; induction env. 
 - intros. simpl in H0. inversion H0;auto.
 -  intros.
    inversion H;subst.  simpl in H0. 
    destruct (atom_eq_dec (AIdent s) (AIdent n)).
    inversion e;subst;auto.
    remember (typeValMatch t v). 
    destruct b;inversion H0;subst.
    
    apply ty_ind;auto.
    rewrite <- typeValMatch_refl;auto.
    remember (updateValueEnvInv (AIdent s) v env).
    destruct o;inversion H0;auto.
    apply IHenv in Heqo;auto. 
    apply ty_ind;auto.
Qed.



Lemma typeActionTyEnv: forall action env v r  eventList l,
    Result (v,r) = execAction (env, l) action eventList ->
    tyEnv env ->
    tyEnv v.
Proof. Print tyEnv. 
       intro action;induction action.
       
       - intros. simpl in *. inversion H;auto. 
       - intros.
         simpl in H.
        destruct l;inversion H.
         destruct a;inversion H. 
         remember (evalMonad env e ).
         destruct e0;inversion H2.
         remember (updateValueEnvInv (AIdent s) v0 env).
         destruct o;inversion H;subst.
         pose proof updateEnvTy.
         apply H1 with (env:=env) (v:=v0) (s:=s) ;auto.
       -
         intros. simpl in H.
         remember (calculateExprList env exprs ).
         destruct e;inversion H.
         remember (getEventByName ident eventList ).
         destruct o;inversion H2. subst;auto.
         remember (parameterMatchFunc v0 (eventParams e)).
         destruct b;inversion H2. subst. auto. 
       - intros.
         simpl in H.
         remember (execAction (env, l) action1 eventList ).
         destruct e;inversion H. 
         destruct v0;subst.
         apply IHaction1 in Heqe;auto.
         apply IHaction2 in H;auto.          
Qed.

Lemma updateEnvConsistent: forall env t_env v s v1,
    evnConsist t_env env ->
    Some v1 = updateValueEnvInv (AIdent s) v env ->
    evnConsist t_env v1.
Proof. 
     intro env; induction env. 
 - intros. simpl in H0. inversion H0;auto.
 -  intros.
    inversion H;subst.  simpl in H0. 
    destruct (atom_eq_dec (AIdent s) (AIdent n)).
    inversion e;subst;auto.
    remember (typeValMatch ty v). 
    destruct b;inversion H0;subst.
    apply e_con_ind;auto.
    
    
    remember (updateValueEnvInv (AIdent s) v env).
    destruct o;inversion H0;auto.
    apply e_con_ind;auto.
    apply IHenv with (t_env:=te) in Heqo;auto. 
  
Qed. 

Lemma typeActionTyConsistent: forall action env t_env v r  eventList l,
    Result (v,r) = execAction (env, l) action eventList ->
    evnConsist t_env env ->
    evnConsist t_env v.
Proof.
  intro action;induction action.
  - intros;simpl in H;inversion H;auto. 
  -  intros. simpl in H.
    destruct l;inversion H.
         destruct a;inversion H. 
         remember (evalMonad env e ).
         destruct e0;inversion H2.
         remember (updateValueEnvInv (AIdent s) v0 env).
         destruct o;inversion H;subst.
         inversion H0. subst. 
         simpl in Heqo. inversion Heqo;auto. 
         subst.
         simpl in Heqo.
         destruct (atom_eq_dec (AIdent s) (AIdent n)).
         inversion e0;subst.
         remember ( typeValMatch ty v0).
         destruct b;inversion Heqo;subst.          
         Print evnConsist.
         apply e_con_ind;auto.
         remember (updateValueEnvInv (AIdent s) v0 ev).
         destruct o;inversion Heqo.
         apply e_con_ind;auto.
         pose proof updateEnvConsistent.
         apply H5 with (env:=ev) (v:=v0) (s:=s);auto.

  -  intros. simpl in H.
         remember (calculateExprList env exprs ).
         destruct e;inversion H.
         remember (getEventByName ident eventList ).
         destruct o;inversion H2. subst;auto.
          remember (parameterMatchFunc v0 (eventParams e)).
         destruct b;inversion H2. subst. auto. 
       - intros.
         simpl in H.
         remember (execAction (env, l) action1 eventList ).
         destruct e;inversion H. 
         destruct v0;subst.
         apply IHaction1 with (t_env:=t_env) in Heqe;auto.
         apply IHaction2 with (t_env:=t_env)  in H;auto.
Qed. 

Lemma calculateTypeCheck: forall lst env t_env ,
    uniqList (dom env) ->
    tyEnv env ->
    evnConsist t_env env ->
    (forall ex, In ex lst -> (exists ty, HasTy t_env ex ty)) ->
    (exists v, Result v = calculateExprList env lst).
Proof. intro lst;induction lst.
       - intros. simpl. exists nil;auto. 
       - intros. simpl.
         assert (exists ty : typ, HasTy t_env a ty).
         apply H2;auto. 
         left;auto.
         destruct H3.          
        
         pose proof evalMonadCorrect.
         
         assert (exists v : range_typ, Result v = evalMonad env a /\ typeValMatch x v).
         apply H4 with (t_env:=t_env);auto.
         destruct H5. destruct H5.
         rewrite <- H5.
         assert (exists v : list range_typ, Result v = calculateExprList env lst).
         apply IHlst with (t_env:=t_env) ;auto.
         intros.
         apply H2;right;auto.
         destruct H7.
         rewrite <- H7.
         exists (x0::x1);auto.
Qed.

Lemma hasTyList: forall t_env lst tlst,
    HasTy_ExprList t_env lst tlst ->
    (forall ex : expr, In ex lst -> exists ty : typ, HasTy t_env ex ty
    ).
Proof.
  intros.
  generalize dependent ex.
  induction H.
  - intros. inversion H0.
  - intros.
    destruct H1. subst.
    exists ty;auto.
    apply IHHasTy_ExprList;auto. 
Qed.

Lemma calculateMatch: forall env t_env lst tlst x,
    uniqList (dom env) ->
    tyEnv env ->
    HasTy_ExprList t_env lst tlst ->
    evnConsist t_env env ->
    Result x = calculateExprList env lst ->
    parameterMatch x tlst.
Proof. 
  intros.
  generalize dependent x.
  generalize dependent env.
  induction H1.
  - intros.
   simpl in H3. inversion H3.  constructor.    
  - intros.
    simpl in H4. 
    remember (evalMonad env ex). 
    destruct e0;inversion H4.
    remember (calculateExprList env e).
    destruct e0;inversion H6.  inversion H4;subst.
    constructor.
    apply IHHasTy_ExprList with (env:=env);auto.
    SearchAbout tyEnvPair.
    pose proof evalMonadCorrect.
    apply H5 with (env:=env) in H;auto.
    destruct H. destruct H.
    rewrite <- Heqe0 in H. inversion H;subst. auto. 
Qed.


Lemma typeAction: forall  t_env (env:value_env) action eventList l,
    uniqList (dom env) ->
    tyEnv env ->
    evnConsist t_env env ->
    HasTy_action t_env eventList action ->
    (exists v r, Result (v,r) = execAction (env, l) action eventList).
Proof.
  pose proof evalMonadCorrect.
  intros. generalize dependent l. generalize dependent env.   induction H3.
  intros. simpl in *. exists env;exists l;auto. 
  intros. 
  simpl.
  assert (exists v : range_typ, Result v = evalMonad env ex /\ typeValMatch ty v).
  apply H with (t_env:=t_env);auto.
  destruct H5. destruct H5. 
  rewrite <- H5.
  pose proof updateEnvType. 
  assert (exists ven : value_env, Some ven = updateValueEnvInv (AIdent s) x env). 
  apply H7 with (t_env:=t_env) (ty:=ty);auto.
  destruct H8. rewrite <- H8.
  exists x0; exists l;auto.
  intros. simpl.
  pose proof calculateTypeCheck.
  assert (exists v : list range_typ, Result v = calculateExprList env lst).
  
  apply H4 with (t_env:=t_env);auto.
 
  destruct H0. destruct H0.
   apply hasTyList with (tlst:= eventParams x);auto. 
  
  destruct H5. rewrite <- H5.
  destruct H0. destruct H0. rewrite  H0.
  exists env; exists ({| eventDefinition := x0; eventArguments := x |} :: l);auto. 
  pose proof calculateMatch.
  assert (parameterMatchFunc x (eventParams x0) = true).
  rewrite <- parameterMatch_refl.
  apply H7 with (env:=env) (t_env:=t_env) (lst:=lst);auto.
  rewrite H8. auto. 
  simpl. intros. 
  destruct  IHHasTy_action1 with (l:=l) (env:=env);auto. destruct H3.
  rewrite <- H3.
  destruct IHHasTy_action2 with (l:=x0) (env:=x);auto.
  pose proof typeActionNoChange.
  assert (dom env = dom x).
  apply H4 with (action:=c1) (r:=x0) (eventList:=eventList) (l:=l);auto.
  rewrite <- H5;auto.
  pose proof typeActionTyEnv.
  apply H4 with (action:=c1) (r:=x0) (eventList:=eventList) (l:=l) (env:=env);auto.   
  pose proof typeActionTyConsistent.
  apply H4 with (action:=c1) (r:=x0) (eventList:=eventList) (l:=l) (env:=env);auto.
  destruct H4. exists x1;exists x2;auto.
Qed.


                          

Print constructConfig. 

SearchAbout findEventInstance.
Print findEventInstance.

Lemma createEqual: forall sl tl vl v1 v2,
    Result v1 = createTypEnv sl tl ->
    Result v2 = createValueEnv sl tl vl ->
    dom v1 = dom v2.
Proof.
  intro sl;induction sl.
  - intros.
    destruct tl.     destruct vl.
    simpl in H;simpl in H0. inversion H;inversion H0;auto.
    inversion H0.
    inversion H.
  - intros. destruct tl;destruct vl;inversion H.
    inversion H0.
    simpl in H0.
    remember (createValueEnv sl tl vl).
    remember (createTypEnv sl tl).
    destruct e;destruct e0;inversion H0;inversion H2.
    simpl. f_equal.
    apply IHsl with (tl:=tl) (vl:=vl);auto.
Qed.

Lemma domApp: forall (A:Type) (B: Type) (env env': list (A*B)),
dom (env ++ env') = dom env ++ dom env'.
Proof. intros A B env.
induction env.
- intros. simpl. auto.
- intros. simpl. f_equal. apply IHenv.
Qed.

Lemma evnConsistDom2: forall env,
    (forall a, In a (dom env) -> (exists s, AIdent s = a)) -> evnConsist (dom2 env) env. 
Proof. intro env;induction env. 
       -
         simpl.  intros. constructor.
       -
         simpl.
         intros.        
         destruct a. simpl.
         destruct p. simpl.
         simpl in H.
         destruct H with (a0:=a);auto.
         rewrite <- H0.
         constructor;auto. 
Qed.

Lemma tyEnvVar: forall env,
    tyEnv env ->
    (forall a, In a (dom env) -> (exists s, AIdent s = a)). 
Proof. 
   intro env. induction env. 
  - intros. inversion H0. 
  - intros. simpl in H0.
    inversion H;subst.
    simpl in H0.
    destruct H0.
    exists n;auto. 
    apply IHenv;auto. 
Qed.

Lemma dom2Equal: forall nl tl vl v1 v2,
    Result v1 = createTypEnv nl tl ->
    Result v2 = createValueEnv nl tl vl ->
    v1 = dom2 v2. 
Proof.                         
   intro nl;induction nl. 
   - intros. destruct tl. destruct vl. simpl in H0. inversion H0.
     simpl. simpl in H. inversion H;auto.  
     inversion H0.  inversion H.
   -  intros.
      destruct tl. inversion H.
      destruct vl. inversion H0. 
      simpl in H.
      simpl in H0.
      remember (createTypEnv nl tl).
      destruct e;inversion H.
      remember (createValueEnv nl tl vl).
      destruct e;inversion H0.
      simpl. f_equal.
      apply IHnl with (tl:=tl) (vl:=vl);auto.
Qed.

Lemma dom2App: forall (A:Type) (B: Type) (C: Type) (env env': list (A*(B*C))),
dom2 (env ++ env') = dom2 env ++ dom2 env'.
Proof. intros A B C env.
induction env.
- intros. simpl. auto.
- intros. simpl. f_equal. apply IHenv.
Qed.

Check dom2Equal.

Lemma dom2Equal': forall (env:value_env) (t_env:typ_env),
    dom env = dom t_env ->
    evnConsist t_env env ->
    dom2 env = t_env.
Proof. intro env; induction env.
       - intros. destruct t_env.
         simpl;auto.
         inversion H0.
       - intros.
         destruct t_env.
         inversion H0.
         inversion H0;subst.
         simpl in H.
         inversion H.
         simpl. f_equal.
         apply IHenv;auto.
Qed.

Lemma dom2Equal'': forall (env:value_env) (t_env:typ_env),
    evnConsist t_env env ->
    dom2 env = t_env.
Proof. intro env; induction env.
       - intros. destruct t_env.
         simpl;auto.
         inversion H.
       - intros.
         destruct t_env.
         inversion H.
         inversion H;subst.
         
         simpl. f_equal.
         apply IHenv;auto.
Qed. 

Print ConfigOfMon. 

(*Lemma ConfigOfMon_refl: forall conf,
    correct_configuration conf ->
    ConfigOfMon conf (monitor_obj conf). 
Proof. 
  intros.
  destruct H.
  unfold ConfigOfMon.     
  split;auto.
Qed.*)

(*ds_dom_eq: (dom2 (datastate conf)) = ((dsmon (monitor_obj conf)));
 *)

SearchAbout dom2.
Lemma dom2dom: forall (env:value_env) (t_env:typ_env),
    dom2 env = t_env ->
    dom env = dom t_env. 
Proof.
  intro env;induction env.
- intros.  destruct t_env. auto. inversion H. 
- intros. destruct t_env. inversion H. simpl.
  f_equal. simpl in H. inversion H. destruct p. simpl. auto.
  apply IHenv;auto. inversion H;auto.
Qed.


(*Lemma sce_state_no_empty': forall env sce ,
    In sce (dom env) ->
    getScenarioState' sce env <> None. 
Proof.
  intro env;induction env.
-  intros.  inversion H. 
- intros. destruct H. destruct a.  
  simpl.  simpl in *.   subst.
Admitted.
*)

(*Definition alphabetScenario_rev (mon:object) : Prop :=
  forall sce e st, In sce (scenarios mon) ->  (exists (stp:step) (elst: list event_instance), In stp (traces sce) /\  st = (pre_state stp) /\ (In (Some st, Some e, elst) (stateEvDefInstanceMap mon) /\ elst <> nil)) -> In e (alphabet sce). 


Definition alphabetStep (mon:object) : Prop :=
  forall  st e lst, In (Some st, Some e, lst) (stateEvDefInstanceMap mon) -> (forall ei, In ei lst -> (exists stp, In (st, ei, Some stp) (stateEvStepMap mon) /\ st = pre_state stp)).*)


Lemma staticConstructNoError': forall M (conf : configuration M) sce  re,
    constructConfig sce re conf <> Error error3
      -> correct_configuration conf
      -> typeCheck M
      -> In sce (dom (controlstate conf))
      -> In re (raisedevents conf)
      -> stateEvDefInstanceMapEquiv M
      -> transEvMapProp M
      -> transEvMapEventInstanceProp M
      -> stpStMapEquiv' M
      -> stepExistsMon' M sce
      -> ~ In sce (finishedscenarios conf)
      -> correctStateEvStepMap' M
      -> stateSceProp M                          
      -> (exists conf', constructConfig sce re conf = Result conf').
Proof.
  intros. 
  rename H8 into stepExists.
  rename H9 into noFinish.
  rename H10 into stepEventMap.
  rename H11 into stSceProp.
  
  unfold constructConfig.
  unfold constructConfig in H.
  
  remember ( getScenarioState sce (controlstate conf) ).
  destruct o.
  Focus 2.
  
  apply   sce_state_no_empty with (sce0:=sce) in H0;auto.
  exfalso;apply H0;auto.
  remember (transEvMapFunc (stateEvDefInstanceMap M) (Some s, Some (eventDefinition re))).
  destruct o.
  Focus 2.
  unfold stateEvDefInstanceMapEquiv in H4.
  
  contradiction.
  SearchAbout transEvMapFunc.
  pose proof semantic_rules.stateEvDefInstanceMapEquiv'.
  
  remember Heqo0.
  clear Heqe. symmetry in e. 
  apply H8 in e. 
  rename e into em.
  remember (findEventInstance re (datastate conf) l).
  destruct o.
  Focus 2.
  exfalso;apply H;auto.
  remember (createValueEnv (eventArgs e) (eventParams (eventDefinition re)) (eventArguments re)). 

  remember H0. clear Heqc.
  Focus 2. unfold stateEvDefInstanceMapEquiv in H4;auto. 
   destruct H4;auto. 
  pose proof findInstanceDefMon.
  remember em. clear Heqi. 
  apply H9 with (ei:=e) (ds:=(datastate conf)) in em;auto.
  
  (*remember ((transEvMap (Some s, Some (eventDefinition re)))).
  
  remember Heql.  clear Heqe1. 
  symmetry in Heql.
  destruct H4 with (st:=s) (ev := (eventDefinition re)) (eList:=l) . 
  apply H8 in Heql.
  remember Heql. clear Heqi. 
  pose proof findInstanceDefMon.
  apply H9 with (ei:=e) (ds:=(datastate conf)) in Heql;auto.*)
  
  rewrite <- em in Heqe0.
    destruct e0.
  Focus 2.
  assert (exists en, typeCheckInstance e en).
  pose proof eventInstanceTypeCorrect.
  eapply H10;auto. apply i. auto. auto.
  Check findEventInstanceIn. 
  apply findEventInstanceIn in Heqo1;auto.
  
  (*rename e1 into e0. 
  rewrite e0 in Heqo0.*)
  destruct H10. 
  unfold typeCheckInstance in H10.
  destruct H10.
  
  (*rewrite Heql in Heqe0.*)
  pose proof raised_wellform.
  assert (wellFormedRaisedEvent re). 
  apply H12 with (conf:=conf);auto.
  
  unfold  wellFormedRaisedEvent in H13.
  assert (Datatypes.length (eventArguments re) =
          Datatypes.length ((eventParams (eventDefinition re)))).
  apply paraLengthEq;auto. 
  pose proof createValEnvCorrect.
  assert (createValueEnv (eventArgs e) (eventParams (eventDefinition re)) (eventArguments re) <> Error s0).
  apply H15;auto.  rewrite em in H10;auto. rewrite H14. rewrite em in H10;auto.
  
 
 
  exfalso;apply H16;auto. rewrite <- em;auto. 
  remember (getStep' conf sce e).
  destruct o.
  Focus 2.
  
  unfold getStep' in Heqo2.
    rewrite <- Heqo in Heqo2.
  unfold stpStMapEquiv' in H7.
    assert (In e l).
  apply findEventInstanceIn with (env:=(datastate conf)) (e:=re);auto.
 (*  rewrite e1 in Heqo0;auto. 
  assert (In (Some s, Some (eventDefinition re),
              (transEvMap (Some s, Some (eventDefinition re)))) (stateEvDefInstanceMap M)).
  rewrite e1 in i. 
  apply i;auto.*)
  
  unfold stepExistsMon' in stepExists.
  
  apply stepExists with (ei:=e) in i;auto.
  destruct i.
  pose proof stpStMapEquivLem.
  apply H12 with (st:=s) (ei:=e) (stp:=x) (sce:=sce) in H7;auto.
  apply H7 in H11.   rewrite H11 in Heqo2;inversion Heqo2. 
 
  (*apply H12 in H11.
  rewrite H11 in Heqo2.
  inversion Heqo2. *)
  unfold stateSceProp in stSceProp.
 
  
  apply stSceProp with (l:=l) (s:=s) ;auto. SearchAbout s.
  SearchAbout stateScenarioMap. (*rewrite e1;auto.*)
  destruct c.  apply sceStateCorrect;auto.
  
  apply inControlState;auto.    
 
  remember (configTransition (extendValEnv (datastate conf) v) re e sce s0 conf). 
  destruct e0.
  exists ( v0);auto.
  unfold configTransition in Heqe1.

  
  unfold typeCheck in H1.
  remember H0. clear Heqc0. destruct c0.
   remember H3.  clear Heqi0. remember H2. clear Heqi1. rewrite cs_consist in H2. apply H1 in H2.
  unfold  typeCheckScenario in H2.
  unfold getTransitionsOfScenario in H2.
        repeat match goal with
            | [ H: _ /\ _ |- _ ] => destruct H

               end.
        remember Heqo. clear Heqe2.
        apply inControlState in Heqo;auto.
        
   pose proof  getStepMap'. 
   unfold stpStMapEquiv' in H7.
   
   apply H10 with (s0:=s0) (e0:=e) in e0;auto. 
   symmetry in e0.
   pose proof stpStMapEquivLem.
   
   apply H11 with (st:=s) (ei:=e) (stp:=s0) (sce:=sce) in e0;auto.
   
  
   remember e0. clear Heqi2.
   unfold correctStateEvStepMap' in stepEventMap.
   
   apply stepEventMap in e0;auto.
     
   (*apply  cs_state_consist with (sce:=sce) in e0;auto.*)

   
   
   destruct e0. 

   apply H2 in H12.
                unfold typeCheckStep in H12.

                
     remember (createTypEnv (eventArgs (stepEvent s0)) (eventParams (event (stepEvent s0)))).            destruct e0;inversion H12. 
              repeat match goal with
            | [ H: _ /\ _ |- _ ] => destruct H

               end.             
              clear H14;clear H15.
              
    remember (execAction (extendValEnv (datastate conf) v, []) (stepActions s0)
              (filter
                 (fun e : event_definition =>
                  match eventKind e with
                  | Internal => true
                  | Imported => false
                  | Exported => true
                  end) (events M))).      
    destruct e0.  destruct v1; inversion Heqe1.
    pose proof typeAction.
   
    assert (exists v' r,
               Result (v', r) = execAction ((extendValEnv (datastate conf) v), []) (stepActions s0) (filter
             (fun e : event_definition =>
              match eventKind e with
              | Internal => true
              | Imported => false
              | Exported => true
              end) (events M))).
    
     unfold correctStateEvStepMap' in stepEventMap.
    apply stepEventMap in i2. destruct i2. destruct H18. 
    rewrite H18 in Heqe2. 
    
    pose proof createEqual.
    assert (dom v0 = dom v). 
    apply H20 with (sl:=(eventArgs e) ) (tl:=(eventParams (event e))) (vl:=(eventArguments re));auto. 
    apply H14 with (t_env:=(dom2 ((extendValEnv (datastate conf) v))));auto.
    unfold extendValEnv.
    unfold typeCheckInstance in H12.
    
    repeat match goal with
            | [ H: _ /\ _ |- _ ] => destruct H

           end.
   rewrite domApp. 
   rewrite <- H21. apply dom2dom in ds_dom_eq. 
   rewrite ds_dom_eq.
   unfold dsmon. rewrite domApp in H23. auto.
   unfold extendValEnv.
   apply tyEnvApp.
   apply correct_configuration_tyEnv;auto.
   

   
   apply raisedTyEnv with (nl:=(eventArgs e)) (tl:=(eventParams (event e))) (vl:=(eventArguments re));auto.
    pose proof raised_wellform.
  assert (wellFormedRaisedEvent re). 
  apply H22 with (conf:=conf);auto.
  unfold  wellFormedRaisedEvent in H23.
 
  rewrite em;auto.
  unfold extendValEnv.
  apply evnConsistDom2.
  intros.
  rewrite domApp in H22.
  rewrite in_app_iff in H22;auto.
  pose proof tyEnvVar.
  destruct H22.
  
  apply H23 with (env:=(datastate conf));auto.
  apply H23 with (env:=v);auto.
  apply raisedTyEnv with (nl:=(eventArgs e)) (tl:=(eventParams (event e))) (vl:=(eventArguments re));auto.
    pose proof raised_wellform.
  assert (wellFormedRaisedEvent re). 
  apply H24 with (conf:=conf);auto.
  unfold  wellFormedRaisedEvent in H24.
  rewrite em;auto.
  unfold extendValEnv.
  pose proof dom2Equal.
  pose proof dom2App.
  rewrite H23.
  rewrite <- H22 with (v2:=v) (v1:=v0) (nl:=(eventArgs e)) (tl:=(eventParams (event e))) (vl:=(eventArguments re));auto.
  pose proof  dom2Equal'.
  rewrite H24 with (t_env:=(identities M ++ variables M)) (env:=datastate conf);auto.
  Focus 2.  
  destruct H15. destruct H15. 
  rewrite <- H15 in Heqe3. 
  inversion Heqe3.
   apply dom2dom in ds_dom_eq. 
   rewrite ds_dom_eq.
   unfold dsmon. auto. 
Qed.



 (* Lemma staticConstructNoError: forall conf  sce  re, constructConfig sce re conf <> Error error3 -> correct_configuration conf ->  typeCheck (monitor_obj conf) ->  In sce (dom (controlstate conf)) -> In re (raisedevents conf) -> stateEvDefInstanceMapEquiv (monitor_obj conf) -> transEvMapProp (monitor_obj conf) -> transEvMapEventInstanceProp (monitor_obj conf) -> stpStMapEquiv (monitor_obj conf) -> stepExistsMon (monitor_obj conf) -> ~ In sce (finishedscenarios conf) -> correctStateEvStepMap (monitor_obj conf) -> (exists conf', constructConfig sce re conf = Result conf').
Proof.
  intros. 
  rename H8 into stepExists.
  rename H9 into noFinish.
  rename H10 into stepEventMap.
  unfold constructConfig.
  unfold constructConfig in H. 
  remember ( getScenarioState sce (controlstate conf) ).
  destruct o.
  Focus 2.
  apply   sce_state_no_empty with (sce:=sce) in H0;auto.
  exfalso;apply H0;auto.
  remember (findEventInstance re (datastate conf) (transEvMap (Some s, Some (eventDefinition re)))).
  destruct o.
  Focus 2.
  exfalso;apply H;auto.
  clear H.
  remember (createValueEnv (eventArgs e) (eventParams (eventDefinition re)) (eventArguments re)). 

  remember H0. clear Heqc.
  unfold stateEvDefInstanceMapEquiv in H4. 
  remember ((transEvMap (Some s, Some (eventDefinition re)))).
  
  remember Heql.  clear Heqe1. 
  symmetry in Heql.
  destruct H4 with (st:=s) (ev := (eventDefinition re)) (eList:=l) . 
  apply H8 in Heql.
  remember Heql. clear Heqi. 
  pose proof findInstanceDefMon.
  apply H9 with (ei:=e) (ds:=(datastate conf)) in Heql;auto.
  rewrite <- Heql in Heqe0.
    destruct e0.
  Focus 2.
  assert (exists en, typeCheckInstance e en).
  pose proof eventInstanceTypeCorrect.
  eapply H10;auto. 
  apply findEventInstanceIn in Heqo0;auto.
  
  rename e1 into e0. 
  rewrite e0 in Heqo0.
  destruct H10. 
  unfold typeCheckInstance in H10.
  destruct H10.
  SearchAbout createValueEnv.
  
  rewrite Heql in Heqe0.
  pose proof raised_wellform.
  assert (wellFormedRaisedEvent re). 
  apply H12 with (conf:=conf);auto.
  
  unfold  wellFormedRaisedEvent in H13.
  assert (Datatypes.length (eventArguments re) =
          Datatypes.length ((eventParams (eventDefinition re)))).
  apply paraLengthEq;auto. 
  pose proof createValEnvCorrect.
  assert (createValueEnv (eventArgs e) (eventParams (eventDefinition re)) (eventArguments re) <> Error s0).
  apply H15;auto. auto. 
  rewrite Heql in H10. auto. subst. SearchAbout eventArgs. rewrite H10.
  rewrite Heql. auto.
 
  exfalso;apply H16;auto. 
  remember (getStep conf sce e).
  destruct o.
  Focus 2.
  unfold getStep in Heqo1.
  rewrite <- Heqo in Heqo1.
  unfold stpStMapEquiv in H8.
    assert (In e (transEvMap (Some s, Some (eventDefinition re)))).
  apply findEventInstanceIn with (env:=(datastate conf)) (e:=re);auto.
  rewrite e1 in Heqo0;auto. 
  (*unfold stateEvDefInstanceMapEquiv in H5.
  destruct H5.*)
  assert (In (Some s, Some (eventDefinition re),
              (transEvMap (Some s, Some (eventDefinition re)))) (stateEvDefInstanceMap (monitor_obj conf))).
  rewrite e1 in i. 
  apply i;auto.
  unfold stepExistsMon in stepExists. 
  apply stepExists with (ei:=e) in H11;auto.
  destruct H11.
  SearchAbout stateEvStepMap. 
  destruct H7 with (st:=s) (ei:=e) (stp:=x);auto.
  
  apply H12 in H11.
  rewrite H11 in Heqo1.
  inversion Heqo1.
  remember (configTransition (extendValEnv (datastate conf) v) re e sce s0 conf). 
  destruct e0.
  exists ( v0);auto.
  unfold configTransition in Heqe1.
  
  unfold typeCheck in H1.
  remember H0. clear Heqc0. destruct c0.
   remember H3.  clear Heqi0. remember H2. clear Heqi1. rewrite cs_consist in H2. apply H1 in H2.
  unfold  typeCheckScenario in H2.
  unfold getTransitionsOfScenario in H2.
        repeat match goal with
            | [ H: _ /\ _ |- _ ] => destruct H

               end.
        remember Heqo. clear Heqe2.
        apply inControlState in Heqo;auto.
   pose proof  getStepMap. 
        unfold stpStMapEquiv in H7.
   apply H10 with (s0:=s0) (e0:=e) in e0;auto. 
   symmetry in e0.   rewrite <- H7 in e0.
   remember e0. clear Heqi2.
   Print getStep. 
   apply  cs_state_consist with (sce:=sce) in e0;auto.
  
   
   destruct e0. 

                apply H2 in H11.
                unfold typeCheckStep in H11.
          
     remember (createTypEnv (eventArgs (stepEvent s0)) (eventParams (event (stepEvent s0)))).            destruct e0;inversion H11. 
              repeat match goal with
            | [ H: _ /\ _ |- _ ] => destruct H

               end.             
              clear H13;clear H14.
    remember (execAction (extendValEnv (datastate conf) v, []) (stepActions s0)
              (filter
                 (fun e : event_definition =>
                  match eventKind e with
                  | Internal => true
                  | Imported => false
                  | Exported => true
                  end) (events (monitor_obj conf)))).      
    destruct e0.  destruct v1; inversion Heqe1.
    pose proof typeAction.
   
    assert (exists v' r,
               Result (v', r) = execAction ((extendValEnv (datastate conf) v), []) (stepActions s0) (filter
             (fun e : event_definition =>
              match eventKind e with
              | Internal => true
              | Imported => false
              | Exported => true
              end) (events (monitor_obj conf)))).
    
     unfold correctStateEvStepMap in stepEventMap.
    apply stepEventMap in i2. destruct i2. 
    rewrite H14 in Heqe2. 
    
    pose proof createEqual.
    assert (dom v0 = dom v). 
    apply H17 with (sl:=(eventArgs e) ) (tl:=(eventParams (event e))) (vl:=(eventArguments re));auto. 
    apply H13 with (t_env:=(dom2 ((extendValEnv (datastate conf) v))));auto.
    unfold extendValEnv.
    unfold typeCheckInstance in H11.
    
    repeat match goal with
            | [ H: _ /\ _ |- _ ] => destruct H

           end.
   rewrite domApp. 
   rewrite <- H18. apply dom2dom in ds_dom_eq. 
   rewrite ds_dom_eq.
   unfold dsmon. rewrite domApp in H20. auto.
   unfold extendValEnv.
   apply tyEnvApp.
   apply correct_configuration_tyEnv;auto.
   
   SearchAbout tyEnv.
   apply raisedTyEnv with (nl:=(eventArgs e)) (tl:=(eventParams (event e))) (vl:=(eventArguments re));auto.
    pose proof raised_wellform.
  assert (wellFormedRaisedEvent re). 
  apply H19 with (conf:=conf);auto.
  unfold  wellFormedRaisedEvent in H20.
  SearchAbout e.
  rewrite Heql;auto.
  unfold extendValEnv.
  apply evnConsistDom2.
  intros.
  rewrite domApp in H19.
  rewrite in_app_iff in H19;auto.
  pose proof tyEnvVar.
  destruct H19.
  
  apply H20 with (env:=(datastate conf));auto.
  apply H20 with (env:=v);auto.
  apply raisedTyEnv with (nl:=(eventArgs e)) (tl:=(eventParams (event e))) (vl:=(eventArguments re));auto.
    pose proof raised_wellform.
  assert (wellFormedRaisedEvent re). 
  apply H21 with (conf:=conf);auto.
  unfold  wellFormedRaisedEvent in H21.
  rewrite Heql;auto.
  unfold extendValEnv.
  pose proof dom2Equal.
  pose proof dom2App.
  rewrite H20.
  rewrite <- H19 with (v2:=v) (v1:=v0) (nl:=(eventArgs e)) (tl:=(eventParams (event e))) (vl:=(eventArguments re));auto.
  pose proof  dom2Equal'.
  rewrite H21 with (t_env:=(identities (monitor_obj conf) ++ variables (monitor_obj conf))) (env:=datastate conf);auto.
  Focus 2.  
  destruct H14. destruct H14. 
  rewrite <- H14 in Heqe3. 
  inversion Heqe3.
   apply dom2dom in ds_dom_eq. 
   rewrite ds_dom_eq.
   unfold dsmon. auto. 
Qed. 
*)

(*
 Lemma staticConstructNoError: forall conf  sce  re, constructConfig sce re conf <> Error error3 -> correct_configuration conf ->  typeCheck (monitor_obj conf) ->  In sce (dom (controlstate conf)) -> In re (raisedevents conf) -> stateEvDefInstanceMapEquiv (monitor_obj conf) -> transEvMapProp (monitor_obj conf) -> transEvMapEventInstanceProp (monitor_obj conf) -> stpStMapEquiv (monitor_obj conf) -> stepExistsMon (monitor_obj conf) -> ~ In sce (finishedscenarios conf) -> correctStateEvStepMap (monitor_obj conf) -> (exists conf', constructConfig sce re conf = Result conf').
Proof.
  intros. 
  rename H8 into stepExists.
  rename H9 into noFinish.
  rename H10 into stepEventMap.
  unfold constructConfig.
  unfold constructConfig in H. 
  remember ( getScenarioState sce (controlstate conf) ).
  destruct o.
  Focus 2.
  apply   sce_state_no_empty with (sce:=sce) in H0;auto.
  exfalso;apply H0;auto.
  remember (findEventInstance re (datastate conf) (transEvMap (Some s, Some (eventDefinition re)))).
  destruct o.
  Focus 2.
  exfalso;apply H;auto.
  clear H.
  remember (createValueEnv (eventArgs e) (eventParams (eventDefinition re)) (eventArguments re)). 

  remember H0. clear Heqc.
  unfold stateEvDefInstanceMapEquiv in H4. 
  remember ((transEvMap (Some s, Some (eventDefinition re)))).
  
  remember Heql.  clear Heqe1. 
  symmetry in Heql.
  destruct H4 with (st:=s) (ev := (eventDefinition re)) (eList:=l) . 
  apply H8 in Heql.
  remember Heql. clear Heqi. 
  pose proof findInstanceDefMon.
  apply H9 with (ei:=e) (ds:=(datastate conf)) in Heql;auto.
  rewrite <- Heql in Heqe0.
    destruct e0.
  Focus 2.
  assert (exists en, typeCheckInstance e en).
  pose proof eventInstanceTypeCorrect.
  eapply H10;auto. 
  apply findEventInstanceIn in Heqo0;auto.
  
  rename e1 into e0. 
  rewrite e0 in Heqo0.
  destruct H10. 
  unfold typeCheckInstance in H10.
  destruct H10.
  SearchAbout createValueEnv.
  
  rewrite Heql in Heqe0.
  pose proof raised_wellform.
  assert (wellFormedRaisedEvent re). 
  apply H12 with (conf:=conf);auto.
  
  unfold  wellFormedRaisedEvent in H13.
  assert (Datatypes.length (eventArguments re) =
          Datatypes.length ((eventParams (eventDefinition re)))).
  apply paraLengthEq;auto. 
  pose proof createValEnvCorrect.
  assert (createValueEnv (eventArgs e) (eventParams (eventDefinition re)) (eventArguments re) <> Error s0).
  apply H15;auto. auto. 
  rewrite Heql in H10. auto. subst. SearchAbout eventArgs. rewrite H10.
  rewrite Heql. auto.
 
  exfalso;apply H16;auto. 
  remember (getStep conf sce e).
  destruct o.
  Focus 2.
  unfold getStep in Heqo1.
  rewrite <- Heqo in Heqo1.
  unfold stpStMapEquiv in H8.
    assert (In e (transEvMap (Some s, Some (eventDefinition re)))).
  apply findEventInstanceIn with (env:=(datastate conf)) (e:=re);auto.
  rewrite e1 in Heqo0;auto. 
  (*unfold stateEvDefInstanceMapEquiv in H5.
  destruct H5.*)
  assert (In (Some s, Some (eventDefinition re),
              (transEvMap (Some s, Some (eventDefinition re)))) (stateEvDefInstanceMap (monitor_obj conf))).
  rewrite e1 in i. 
  apply i;auto.
  unfold stepExistsMon in stepExists. 
  apply stepExists with (ei:=e) in H11;auto.
  destruct H11.
  SearchAbout stateEvStepMap. 
  destruct H7 with (st:=s) (ei:=e) (stp:=x);auto.
  
  apply H12 in H11.
  rewrite H11 in Heqo1.
  inversion Heqo1.
  remember (configTransition (extendValEnv (datastate conf) v) re e sce s0 conf). 
  destruct e0.
  exists ( v0);auto.
  unfold configTransition in Heqe1.
  
  unfold typeCheck in H1.
  remember H0. clear Heqc0. destruct c0.
   remember H3.  clear Heqi0. remember H2. clear Heqi1. rewrite cs_consist in H2. apply H1 in H2.
  unfold  typeCheckScenario in H2.
  unfold getTransitionsOfScenario in H2.
        repeat match goal with
            | [ H: _ /\ _ |- _ ] => destruct H

               end.
        remember Heqo. clear Heqe2.
        apply inControlState in Heqo;auto.
   pose proof  getStepMap. 
        unfold stpStMapEquiv in H7.
   apply H10 with (s0:=s0) (e0:=e) in e0;auto. 
   symmetry in e0.   rewrite <- H7 in e0.
   remember e0. clear Heqi2. SearchAbout stateEvStepMap. 
   apply  cs_state_consist with (sce:=sce) in e0;auto.
   destruct e0. 

                apply H2 in H11.
                unfold typeCheckStep in H11.
          
     remember (createTypEnv (eventArgs (stepEvent s0)) (eventParams (event (stepEvent s0)))).            destruct e0;inversion H11. 
              repeat match goal with
            | [ H: _ /\ _ |- _ ] => destruct H

               end.             
              clear H13;clear H14.
    remember (execAction (extendValEnv (datastate conf) v, []) (stepActions s0)
              (filter
                 (fun e : event_definition =>
                  match eventKind e with
                  | Internal => true
                  | Imported => false
                  | Exported => true
                  end) (events (monitor_obj conf)))).      
    destruct e0.  destruct v1; inversion Heqe1.
    pose proof typeAction.
   
    assert (exists v' r,
               Result (v', r) = execAction ((extendValEnv (datastate conf) v), []) (stepActions s0) (filter
             (fun e : event_definition =>
              match eventKind e with
              | Internal => true
              | Imported => false
              | Exported => true
              end) (events (monitor_obj conf)))).
    
     unfold correctStateEvStepMap in stepEventMap.
    apply stepEventMap in i2. destruct i2. 
    rewrite H14 in Heqe2. 
    
    pose proof createEqual.
    assert (dom v0 = dom v). 
    apply H17 with (sl:=(eventArgs e) ) (tl:=(eventParams (event e))) (vl:=(eventArguments re));auto. 
    apply H13 with (t_env:=(dom2 ((extendValEnv (datastate conf) v))));auto.
    unfold extendValEnv.
    unfold typeCheckInstance in H11.
    
    repeat match goal with
            | [ H: _ /\ _ |- _ ] => destruct H

           end.
   rewrite domApp. 
   rewrite <- H18. apply dom2dom in ds_dom_eq. 
   rewrite ds_dom_eq.
   unfold dsmon. rewrite domApp in H20. auto.
   unfold extendValEnv.
   apply tyEnvApp.
   apply correct_configuration_tyEnv;auto.
   
   SearchAbout tyEnv.
   apply raisedTyEnv with (nl:=(eventArgs e)) (tl:=(eventParams (event e))) (vl:=(eventArguments re));auto.
    pose proof raised_wellform.
  assert (wellFormedRaisedEvent re). 
  apply H19 with (conf:=conf);auto.
  unfold  wellFormedRaisedEvent in H20.
  SearchAbout e.
  rewrite Heql;auto.
  unfold extendValEnv.
  apply evnConsistDom2.
  intros.
  rewrite domApp in H19.
  rewrite in_app_iff in H19;auto.
  pose proof tyEnvVar.
  destruct H19.
  
  apply H20 with (env:=(datastate conf));auto.
  apply H20 with (env:=v);auto.
  apply raisedTyEnv with (nl:=(eventArgs e)) (tl:=(eventParams (event e))) (vl:=(eventArguments re));auto.
    pose proof raised_wellform.
  assert (wellFormedRaisedEvent re). 
  apply H21 with (conf:=conf);auto.
  unfold  wellFormedRaisedEvent in H21.
  rewrite Heql;auto.
  unfold extendValEnv.
  pose proof dom2Equal.
  pose proof dom2App.
  rewrite H20.
  rewrite <- H19 with (v2:=v) (v1:=v0) (nl:=(eventArgs e)) (tl:=(eventParams (event e))) (vl:=(eventArguments re));auto.
  pose proof  dom2Equal'.
  rewrite H21 with (t_env:=(identities (monitor_obj conf) ++ variables (monitor_obj conf))) (env:=datastate conf);auto.
  Focus 2.  
  destruct H14. destruct H14. 
  rewrite <- H14 in Heqe3. 
  inversion Heqe3.
   apply dom2dom in ds_dom_eq. 
   rewrite ds_dom_eq.
   unfold dsmon. auto. 
Qed.
 *)

SearchAbout findEventInstance.
Print findEventInstance.
SearchAbout raisedEvent. 
SearchAbout createValueEnv. 
Print evnConsist.
Print tyEnv. 
Print stateEvDefInstanceMapEquivEListProp.

(*in findEventInstance, elist always have two elements and expression returns true or false*)
(*Lemma evalMonadCorrect: forall ex env t_env ty,
    uniqList (dom env) ->
    tyEnv env ->
    HasTy t_env ex ty ->
    evnConsist t_env env ->
    (exists v, Result v = evalMonad env ex /\ typeValMatch ty v). 
 *)

Lemma evnConsistNameEq: forall t_env env,
    evnConsist t_env env ->
    dom t_env = dom env.
Proof. intros.
       induction H;auto.
       simpl. f_equal;auto.
Qed.

Lemma evnConsistApp: forall t1 e1 t2 e2,
    evnConsist t1 e1 ->
    evnConsist t2 e2 ->
    evnConsist (t1++t2) (e1++e2). 
Proof.
  intros. generalize dependent t2;generalize dependent e2. 
  induction H.
  - intros. simpl;auto.
  - intros. simpl.
    SearchAbout app.
    constructor.
    apply IHevnConsist;auto. 
Qed.

Lemma evalMonadInverse: forall env1  e1 v,
    Result (inl (inr v)) = evalMonad env1 e1 ->
    Result (inl (inr (negb v))) =  evalMonad env1 (ENot e1). 
Proof. intros.
       simpl.
       rewrite <- H.
       simpl.
       auto. 
   
Qed. 

Print stateEvDefInstanceMapEquiv. 

Definition alphabetScenario'' mon :=
forall (sce : scenario) (e : event_definition) (st : scenario_state) elst,
       In sce (scenarios mon) ->
       In e (alphabet sce) ->
       In (Some st, Some e, elst) (stateEvDefInstanceMap mon) ->
       elst<> [] /\ (exists (stp : step),  In stp (traces sce) /\ st = pre_state stp). 



Lemma noError3': forall elst mon env st sce re,
    uniqList (dom (dsmon mon)) ->
    evnConsist (dsmon mon) env ->
    tyEnv env ->
    wellFormedRaisedEvent re ->
    transEvMapProp mon ->
    In (Some st, Some (eventDefinition re), elst) (stateEvDefInstanceMap mon) ->
    stateEvDefInstanceMapEquivEListProp mon ->     
    stateEvDefInstanceMapEquiv mon ->
    In sce (scenarios mon) ->
    In (eventDefinition re) (alphabet sce) ->
    alphabetScenario'' mon ->
    (exists ei, Some ei = findEventInstance re env elst). 
Proof.  
  intros.
  rename H9 into as''. 
  remember H4. clear Heqi.
  
  apply H5 in H4.
 
  unfold alphabetScenario'' in as''.   
 
  remember i. clear Heqi0.
  apply  as'' with (sce:=sce) in i0;auto. 
  
  
  destruct i0. 
  destruct H10.   destruct H10. apply H4 in H9.
  rename x into stpX. 
  clear H4.
   clear H5. clear H6. clear H7. clear H8. 

  
  repeat (match goal with
            | [H: _ /\ _ |-_] => destruct H
            | [H: exists _, _ |- _] => destruct H
            end).
      remember (createTypEnv (eventArgs x) (eventParams (event x)) ).
      remember (createTypEnv (eventArgs x0) (eventParams (event x0)) ).
      simpl in H6. 
      destruct e. Focus 2. inversion H6. 
      destruct e0. Focus 2. inversion H6. 
 repeat (match goal with
            | [H: _ /\ _ |-_] => destruct H
            | [H: exists _, _ |- _] => destruct H
               end).
      
              unfold typeCheckInstance in H6.
              unfold typeCheckInstance in H7.
               repeat (match goal with
            | [H: _ /\ _ |-_] => destruct H
            | [H: exists _, _ |- _] => destruct H
               end).
       subst. 
       simpl.
       unfold transEvMapProp in H3. subst. 
       assert ( forall ei : event_instance, In ei [x; x0] -> event ei = eventDefinition re).
       remember (pre_state stpX) as st.
       apply H3 with (st:=st);auto.
       assert (event x = eventDefinition re).
       apply H3 with (st:=(pre_state stpX)) (lst:=x::[x0]);auto.   left;auto.
       assert (event x0 = eventDefinition re).
       apply H3 with (st:=(pre_state stpX)) (lst:=x::[x0]);auto.   right;left;auto.
    
       rewrite H5 in Heqe.
       rewrite H5.
       unfold wellFormedRaisedEvent in H2.
       unfold extendValEnv.
       assert (Datatypes.length (eventArguments re) = Datatypes.length (eventParams (eventDefinition re))).
       apply paraLengthEq;auto.
       pose proof createValEnvCorrect'.
       
       apply H17  with (vlst:= (eventArguments re)) in H7;auto.
       Focus 2.
       
       rewrite H16;auto. rewrite H15 in H7. auto. 
       unfold excludedBoolExpr in H8.

       
       
       remember (eventWhenExpr x0).
       destruct e; try (inversion H8;auto).
       destruct (expr_eq_dec e (eventWhenExpr x));inversion H8.
       rewrite  e0 in Heqe1.
       inversion H9;subst.
       unfold dsmon in H9.
       unfold dsmon in H11.
       pose proof evalMonadCorrect.
       destruct H7. 
       assert (exists v : range_typ, Result v = evalMonad (env ++ x1) (eventWhenExpr x)  /\ typeValMatch Bool v).
       apply H18 with (t_env:=(identities mon ++ variables mon) ++ v);auto.
       unfold dsmon in H12.
       assert (dom v = dom x1).
       rewrite H15 in H7.
       
       apply createEqual with (sl:=(eventArgs x0)) (tl:=(eventParams (eventDefinition re))) (vl:=(eventArguments re)) ;auto. rewrite H11 in Heqe. auto. 
       pose proof evnConsistNameEq.
       assert (dom (identities mon ++ variables mon) = dom (env)).
       apply H21;auto. 
       rewrite domApp. 
        rewrite <- H22.
        rewrite domApp in H12.  rewrite <- H20;auto.
        rewrite H15 in Heqe0. rewrite H11 in Heqe.  rewrite <- Heqe0 in Heqe. inversion Heqe. auto. 
       apply tyEnvApp;auto.
       apply raisedTyEnv with (vl:=(eventArguments re)) (tl:=(eventParams (eventDefinition re)) ) (nl:=(eventArgs x0));auto. rewrite H15 in H7;auto. 
       apply evnConsistApp;auto.
        assert (v = dom2 x1).
       apply dom2Equal with (vl:=(eventArguments re)) (tl:=(eventParams (eventDefinition re)) ) (nl:=(eventArgs x0));auto. rewrite  H11 in Heqe. auto. rewrite H15 in H7;auto. 
       rewrite H20;
         apply evnConsistDom2;auto.
       intros.
       apply tyEnvVar with (env:=x1);auto.
       apply raisedTyEnv with (vl:=(eventArguments re)) (tl:=(eventParams (eventDefinition re)) ) (nl:=(eventArgs x0));auto. rewrite H15 in H7;auto. 
       destruct H20.
       destruct H20.
       rewrite H15 in H7; rewrite <- H7. 
       rewrite <- H20.
       simpl in H21.
       destruct x2;inversion H21. destruct s;inversion H21. 
       destruct b. exists x;auto.
       pose proof evalMonadInverse. 
       apply H22 in H20.
       rewrite <- H20. 
       simpl. exists x0;auto. 

Qed.

(*Lemma noError3: forall elst mon env st  re,
    uniqList (dom (dsmon mon)) ->
    evnConsist (dsmon mon) env ->
    tyEnv env ->
    wellFormedRaisedEvent re ->
    transEvMapProp mon ->
    In (Some st, Some (eventDefinition re), elst) (stateEvDefInstanceMap mon) ->
    stateEvDefInstanceMapEquivEListProp mon ->
    (exists ei, Some ei = findEventInstance re env elst). 
Proof.  
  intros.
  remember H4. clear Heqi.
  
  apply H5 in H4.
      repeat (match goal with
            | [H: _ /\ _ |-_] => destruct H
            | [H: exists _, _ |- _] => destruct H
            end).
      remember (createTypEnv (eventArgs x) (eventParams (event x)) ).
      remember (createTypEnv (eventArgs x0) (eventParams (event x0)) ).
      simpl in H7. 
      destruct e. Focus 2. inversion H7. 
      destruct e0. Focus 2. inversion H7.
 repeat (match goal with
            | [H: _ /\ _ |-_] => destruct H
            | [H: exists _, _ |- _] => destruct H
               end).
      
              unfold typeCheckInstance in H7.
              unfold typeCheckInstance in H8.
               repeat (match goal with
            | [H: _ /\ _ |-_] => destruct H
            | [H: exists _, _ |- _] => destruct H
               end).
       subst. 
       simpl.
       unfold transEvMapProp in H3. subst. 
       assert ( forall ei : event_instance, In ei [x; x0] -> event ei = eventDefinition re).
       apply H3 with (st:=st);auto.
       assert (event x = eventDefinition re).
       apply H4.   left;auto.
       assert (event x0 = eventDefinition re).
       apply H4.   right;left;auto.
           
       rewrite H14 in Heqe. 
       rewrite H15 in Heqe0. 

       rewrite H6 in Heqe.
       rewrite H6.
       rewrite <- Heqe in Heqe0. inversion Heqe0;subst. 
       unfold wellFormedRaisedEvent in H2.
       unfold extendValEnv.
       assert (Datatypes.length (eventArguments re) = Datatypes.length (eventParams (eventDefinition re))).
       apply paraLengthEq;auto.
       pose proof createValEnvCorrect'.
       
       apply H17  with (vlst:= (eventArguments re)) in H8;auto.
       Focus 2.
       rewrite H16;auto. rewrite H15 in H8. auto. 
       unfold excludedBoolExpr in H9.
       
                                   
       remember (eventWhenExpr x0).
       destruct e; try (inversion H9;auto).
       destruct (expr_eq_dec e (eventWhenExpr x));inversion H9.
       rewrite  e0 in Heqe1.
       inversion H10;subst.
       unfold dsmon in H10.
       unfold dsmon in H12.
       pose proof evalMonadCorrect.
       destruct H8. 
       assert (exists v : range_typ, Result v = evalMonad (env ++ x1) (eventWhenExpr x)  /\ typeValMatch Bool v).
       apply H18 with (t_env:=(identities mon ++ variables mon) ++ v);auto.
       unfold dsmon in H13.
       assert (dom v = dom x1).
       rewrite H15 in H8.
       apply createEqual with (sl:=(eventArgs x0)) (tl:=(eventParams (eventDefinition re))) (vl:=(eventArguments re)) ;auto.
       pose proof evnConsistNameEq.
       assert (dom (identities mon ++ variables mon) = dom (env)).
       apply H21;auto.
       rewrite domApp.
       rewrite <- H22. rewrite <- H20.
       rewrite domApp in H13. auto.
       apply tyEnvApp;auto.
       apply raisedTyEnv with (vl:=(eventArguments re)) (tl:=(eventParams (eventDefinition re)) ) (nl:=(eventArgs x0));auto. rewrite H15 in H8;auto. 
       apply evnConsistApp;auto.
        assert (v = dom2 x1).
       apply dom2Equal with (vl:=(eventArguments re)) (tl:=(eventParams (eventDefinition re)) ) (nl:=(eventArgs x0));auto. rewrite H15 in H8;auto. 
       rewrite H20;
         apply evnConsistDom2;auto.
       intros.
       apply tyEnvVar with (env:=x1);auto.
       apply raisedTyEnv with (vl:=(eventArguments re)) (tl:=(eventParams (eventDefinition re)) ) (nl:=(eventArgs x0));auto. rewrite H15 in H8;auto. 
       destruct H20.
       destruct H20.
       rewrite H15 in H8; rewrite <- H8. 
       rewrite <- H20.
       simpl in H21.
       destruct x2;inversion H21. destruct s;inversion H21.
       destruct b. exists x;auto.
       pose proof evalMonadInverse. 
       apply H22 in H20.
       rewrite <- H20. 
       simpl. exists x0;auto. 

Qed. 
 *)


Print correct_configuration.

Check staticConstructNoError'.





Lemma staticConstructNoError'': forall M (conf : configuration M) sce re,
    correct_configuration conf
      -> typeCheck M
      -> In sce (dom (controlstate conf))
      -> In re (raisedevents conf)
      -> stateEvDefInstanceMapEquiv M
      -> transEvMapProp M
      -> transEvMapEventInstanceProp M
      -> stpStMapEquiv' M
      -> stepExistsMon' M sce
      -> ~ In sce (finishedscenarios conf)
      -> correctStateEvStepMap' M
      -> stateEvDefInstanceMapEquivEListProp M
      -> alphabetScenario'' M
      -> In (eventDefinition re) (alphabet sce)
      -> stateSceProp M 
      -> (exists conf', constructConfig sce re conf = Result conf').
Proof.
  
  intros. rename H11 into alphaSce. rename H12 into reAlphabet. rename H13 into stSceProp.
       pose proof staticConstructNoError'.
       apply H11;auto.
       pose proof noError3'.
       unfold constructConfig.
       remember (getScenarioState sce (controlstate conf)).
      
       destruct o.
       Focus 2.
       unfold not. intros. inversion H13;auto.
      unfold stateEvDefInstanceMapEquiv in H3. 
      destruct H3.
      assert (exists el : list event_instance,
                 el <> [] /\ In (Some s, Some (eventDefinition re), el) (stateEvDefInstanceMap M)).
      apply H13 with (sce:=sce);auto.
      destruct H. apply sceStateCorrect ;auto.
      SearchAbout getScenarioState.
      apply inControlState;auto.
      destruct H14.
      destruct H14.
      remember H15. clear Heqi.
      pose proof semantic_rules.stateEvDefInstanceMapEquiv'.
      apply H16 in i. rewrite i. 
       assert (exists ei : event_instance, Some ei = findEventInstance re (datastate conf) x).
       remember H. clear Heqc.
       destruct H.
       destruct correct_mon;auto.
       unfold alphabetScenario'' in alphaSce.
       apply inControlState in Heqo;auto.
       
       apply H12 with (mon:=M) (st:=s) (sce:=sce);auto.
       split;auto. rewrite <- cs_consist;auto.  
      destruct H17. rewrite <- H17. 
     
       destruct (createValueEnv (eventArgs x0) (eventParams (eventDefinition re)) (eventArguments re)). destruct (getStep' conf sce x0).
       destruct (configTransition (extendValEnv (datastate conf) v) re x0 sce s0 conf ). 
       unfold not. intros.  inversion H18.
       unfold not. intros. inversion H18.
       unfold not. intros. inversion H18. unfold not. intros. inversion H18.
       auto. 
Qed.

SearchAbout execAction.
Check constructConfig. 

Lemma updateDSTyEnvPreserved: forall v1 v2,
      tyEnv v1 ->
      tyEnv (updateDataState v1 v2).
  Proof.
    intros. induction H.
    - simpl. constructor.
    - simpl.
      destruct ( inList atom_eq_dec (AIdent n) v2);auto.
      constructor;auto.
  Qed.
  
Lemma typEnvPreservation :forall M (conf conf' : configuration M) sce re,
    correct_configuration conf ->
    In re (raisedevents conf) ->
    Result conf' = constructConfig sce re conf ->
    tyEnv (datastate conf').
Proof.
  intros.
  unfold constructConfig in H1.
  remember (getScenarioState sce (controlstate conf)).
  destruct o;inversion H1.
  remember (transEvMapFunc (stateEvDefInstanceMap M) (Some s, Some (eventDefinition re)) ). 
  destruct o;inversion H1. 
  remember (findEventInstance re (datastate conf)
                                       l).
  destruct o;inversion H1.
  remember ( createValueEnv (eventArgs e) (eventParams (eventDefinition re)) (eventArguments re)).
  destruct e0;inversion H1.
  remember (getStep' conf sce e).
  destruct o;inversion H1.
  remember (configTransition (extendValEnv (datastate conf) v) re e sce s0 conf).
  destruct e0;inversion H1.
  subst.
  unfold configTransition in Heqe1.
  remember (execAction (extendValEnv (datastate conf) v, []) (stepActions s0)
              (filter
                 (fun e : event_definition =>
                  match eventKind e with
                  | Internal => true
                  | Imported => false
                  | Exported => true
                  end) (events M))). 
  destruct e0;inversion Heqe1. destruct v1. inversion Heqe1;simpl.
  
  pose proof typeActionTyEnv.
  apply H2 in Heqe2. Focus 2. unfold extendValEnv.
  
  apply tyEnvApp. destruct H;auto.
  SearchAbout createValueEnv.
  apply raisedTyEnv with (vl:=(eventArguments re)) (tl:=(eventParams (eventDefinition re))) (nl:=(eventArgs e));auto.
  Print raised_wellform.
  apply raised_wellform with (e:=re) in H. unfold wellFormedRaisedEvent in H;auto. auto.
  apply updateDSTyEnvPreserved;auto. 
Qed. 

SearchAbout evnConsist. 

Lemma evnConsistProp: forall t_env1 t_env2 env,
    evnConsist (t_env1 ++ t_env2) env ->
    (exists env1 env2, env1++env2=env /\ evnConsist t_env1 env1 /\ evnConsist t_env2 env2). 
Proof.
  intro t_env1. 
  induction t_env1.
  - intros. simpl. simpl in H. exists nil. simpl.
    exists env;auto. split;auto. split;(try constructor). auto.  
  
  - intros. simpl in H. inversion H;subst.
    apply IHt_env1 in H3. destruct H3. destruct H0.
    
    repeat (match goal with
            | [H: _ /\ _ |-_] => destruct H
            | [H: exists _, _ |- _] => destruct H
            end).
    exists ((AIdent n, (ty, v)) :: x).     exists x0.
    split;auto. simpl. f_equal;auto.
    split;auto. constructor. auto.
Qed.

Lemma updateDSNotIn: forall ev n dev,
    ~ In n (dom ev) ->
    (updateDataState ev dev) = (updateDataState ev (n::dev)).
Proof.
  intro ev; induction ev.
  - intros. simpl in H. simpl. auto.
  - intros. simpl in H. simpl.
    destruct a. destruct (inList atom_eq_dec a dev).
    destruct (atom_eq_dec a n). f_equal. subst. apply IHev;auto.
    f_equal. apply IHev;auto.
    destruct (atom_eq_dec a n).
    subst. simpl in H. unfold not in H. destruct H. left;auto.
    apply IHev;auto.
Qed.



Lemma evnConsistEq: forall t_env1 v1 x x1,
    evnConsist t_env1 x ->
    uniqList (dom v1) ->
    x ++ x1 = v1 ->
    evnConsist t_env1 (updateDataState v1 (dom x)).
Proof. 
 intro t_env1; induction t_env1. 
 - intros. inversion H. simpl.
   subst. simpl.
   induction x1. simpl. auto.
   simpl. destruct a. inversion H0. subst. simpl in IHx1. apply IHx1 in H3. auto.
 - intros. inversion H;subst.
   simpl. destruct (atom_eq_dec (AIdent n) (AIdent n)).
   Focus 2. contradiction.
   constructor. inversion H0;subst.  
   apply IHt_env1 with (x1:=x1) (v1:=ev++x1) in H5;auto. Print updateDataState. 
   rewrite <- updateDSNotIn with (n:=AIdent n);auto. 
Qed.

Lemma dom2dom': forall (v:value_env),
    dom (dom2 v) = dom v. 
Proof. intro v;induction v;auto.
       simpl. f_equal. auto.
Qed.

Lemma updateDSNil : forall v,
    (updateDataState v nil) = nil.
Proof.
    intro v;induction v;auto. 
    simpl.
    destruct a;auto.
Qed.



Check evnConsistDom2. 

Lemma updateDSNull: forall env1 env2 ev,
    dom2 env1 = dom2 env2 ->
    [] = updateDataState env1 ev ->
    [] = updateDataState env2 ev.
Proof. intro env1;induction env1. 
       -  intros. destruct env2. auto. inversion H.
       - intros. destruct env2. inversion H.
         simpl in H0. simpl.
         inversion H. destruct p;destruct a. simpl in *;subst.
         destruct (inList atom_eq_dec a0 ev).
         inversion H0. apply IHenv1;auto.
Qed.

Lemma evnConsistDom2Eq': forall t_env1 env1 env2,
    evnConsist t_env1 env1 ->
    dom2 env1 = dom2 env2 ->
    evnConsist t_env1 env2.
Proof.
  intro t_env1;induction t_env1.
  - intros.
    destruct env1. destruct env2.
    simpl. constructor.  inversion H0.
    destruct env2. inversion H0. simpl in H0.
    inversion H0.  destruct p. destruct p0.
    simpl. simpl in *.   subst. inversion H. 
  - intros.
    inversion H;subst.
    destruct env2.  inversion H0. destruct p.
    inversion H0;subst.
    destruct p. constructor. 
   apply IHt_env1 with ev;auto. 
Qed. 

SearchAbout updateDataState.

Lemma updateDSDom2Eq: forall env1 env2 ev,
    dom2 env1 = dom2 env2 ->
    dom2 (updateDataState env1 ev) = dom2 (updateDataState env2 ev).
Proof.
  intro env1;induction env1;intros;destruct env2;auto;(try (inversion H)).
  destruct a;destruct p;subst. simpl in *;subst.
  destruct p;destruct p0.
  simpl in H2;subst.
  destruct (inList atom_eq_dec a0 ev).
  simpl. f_equal. apply IHenv1;auto.
  apply IHenv1;auto. 
Qed.

Lemma evnConsistDom2Eq: forall t_env1 env1 env2 ev,
    evnConsist t_env1 (updateDataState env1 ev) ->
    dom2 env1 = dom2 env2 ->
    evnConsist t_env1 (updateDataState env2 ev).
Proof. pose proof updateDSDom2Eq.
       intros.
       apply H with (ev:=ev) in H1;auto.
       apply evnConsistDom2Eq' with (env1:=(updateDataState env1 ev));auto. 
Qed. 

Lemma evnConsistEq': forall t_env1 v1 x x1,
    evnConsist t_env1 x ->
    uniqList (dom v1) ->
    dom2 (x ++ x1) = dom2 v1 ->
    evnConsist t_env1 (updateDataState v1 (dom x)).
Proof. 
 intro t_env1; induction t_env1. 
 - intros. inversion H. simpl.
   subst. simpl. simpl in H1. Print evnConsist.
   SearchAbout updateDataState. rewrite updateDSNil. constructor. 
   
 - intros. inversion H;subst.
   simpl. destruct v1.  inversion H1. destruct p.
   inversion H1;subst. simpl in H. destruct p. simpl.
   simpl in H. destruct (atom_eq_dec (AIdent n) (AIdent n)).
   Focus 2. contradiction. 
   constructor. simpl in H1. clear e. clear H1. inversion H0;subst.  
   apply IHt_env1 with (x1:=x1) (v1:=ev++x1) in H5;auto.
   SearchAbout dom2.
   rewrite <- updateDSNotIn with (n:=AIdent n);auto.
   eapply evnConsistDom2Eq.  apply H5. auto.
   inversion H0. subst. apply dom2dom in H6.  rewrite H6. rewrite dom2dom';auto. 
Qed.
              
 (*Lemma evnConsistEq': forall t_env1 v1 x x1,
    evnConsist t_env1 x ->
    uniqList (dom t_env1) ->
    x ++ x1 = v1 ->
    evnConsist t_env1 (updateDataState v1 (dom x)).
Proof.  
 intro t_env1; induction t_env1. 
 - intros. inversion H. simpl.
   subst. simpl.
   induction x1. simpl. auto.
   simpl. destruct a. auto.  
 - intros. inversion H;subst.
   simpl. destruct (atom_eq_dec (AIdent n) (AIdent n)).
   Focus 2. contradiction.
   constructor. inversion H0;subst. 
   apply IHt_env1 with (x1:=x1) (v1:=ev++x1) in H5;auto. 
   rewrite <- updateDSNotIn with (n:=AIdent n);auto. unfold not. intros.
   apply H4. 
   assert (dom (t_env1) = dom ((updateDataState (ev ++ x1) (dom ev)))).
   apply evnConsistNameEq;auto.
   rewrite H1 in H4. 
Qed.*)

Check typeCheck.
SearchAbout createValueEnv. 
Print transEvMapProp. 

Lemma evnConsistPreservation :forall M (conf conf' : configuration M) sce re,
    correct_configuration conf ->
    In re (raisedevents conf) ->
    Result conf' = constructConfig sce re conf ->
    stateEvDefInstanceMapEquivEListProp M ->
    stateEvDefInstanceMapEquiv M ->
    transEvMapProp M ->
    evnConsist (dsmon M) (datastate conf').
Proof.
  intros. rename H2 into stateEvMapProp. rename H3 into mapEquiv. rename H4 into transEvMProp.
  unfold constructConfig in H1.
  remember (getScenarioState sce (controlstate conf)).
  destruct o;inversion H1.
  remember (transEvMapFunc (stateEvDefInstanceMap M) (Some s, Some (eventDefinition re))). 
  destruct o;inversion H1.

  
  remember (findEventInstance re (datastate conf)
                                       l).
  destruct o;inversion H1.
  remember ( createValueEnv (eventArgs e) (eventParams (eventDefinition re)) (eventArguments re)).
  destruct e0;inversion H1.
  remember (getStep' conf sce e).
  destruct o;inversion H1.
  remember (configTransition (extendValEnv (datastate conf) v) re e sce s0 conf).
  destruct e0;inversion H1.
  subst.
  unfold configTransition in Heqe1.
  remember (execAction (extendValEnv (datastate conf) v, []) (stepActions s0)
              (filter
                 (fun e : event_definition =>
                  match eventKind e with
                  | Internal => true
                  | Imported => false
                  | Exported => true
                  end) (events M))).

  
  destruct e0;inversion Heqe1. destruct v1. 
  inversion Heqe1;simpl.
  unfold extendValEnv in Heqe2.  assert (uniqList (dom (datastate conf ++ v))). unfold stateEvDefInstanceMapEquivEListProp in stateEvMapProp.
  remember Heqo0. clear Heqe3.
  Check findEventInstanceIn.
  
  unfold stateEvDefInstanceMapEquiv in mapEquiv. remember Heqo1.   clear Heqe3. apply findEventInstanceIn in Heqo1;auto.
  Check findInstanceDefMon.  destruct mapEquiv.
  apply semantic_rules.stateEvDefInstanceMapEquiv' with (st:=s) (ev:=eventDefinition re) (eList:=l) in H2. symmetry in e0. rewrite <- H2 in e0. 
  assert (event e = eventDefinition re).
 
  apply findInstanceDefMon with (lst:=l) (ds:= (datastate conf)) (mon:=M) (st:=s);auto. rename H11 into eDef. 
Check stateEvMapProp. remember e0. clear Heqi. apply  stateEvMapProp in e0. Focus 2. unfold not. intros. rewrite H11 in e1;inversion e1.
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
SearchAbout eventDefinition. 
(*rewrite eDef in e0.*)
unfold typeCheckInstance in H14.
unfold typeCheckInstance in H15.
unfold transEvMapProp in transEvMProp.
assert (event x = eventDefinition re).
apply transEvMProp with (st:=s) (lst:=l);auto. rewrite H11. left;auto. 
assert (event x0 = eventDefinition re).
apply transEvMProp with (st:=s) (lst:=l);auto. rewrite H11. right;left;auto. 
repeat (match goal with
            | [H: _ /\ _ |-_] => destruct H
            | [H: exists _, _ |- _] => destruct H
        end).
(*destruct e0. subst.*)

SearchAbout createTypEnv. apply createEqual with (vl:=(eventArguments re)) (v2:=v) in Heqe3;auto.
rewrite domApp. rewrite domApp in H24. erewrite <- ds_dom_eq in H24;eauto.
rewrite dom2dom' in H24. rewrite <-Heqe3;auto.
SearchAbout findEventInstance.
apply findEventInstanceIn in e1. rewrite H11 in e1.
destruct e1. subst. 
rewrite eDef;auto.
rewrite H12. rewrite H19.
inversion H25. subst.
auto. inversion H26. 

(*apply createEqual with (vl:=(eventArguments re)) (v2:=v) in Heqe4;auto.
rewrite domApp. rewrite domApp in H17. SearchAbout dsmon. erewrite <- ds_dom_eq in H17;eauto.
SearchAbout dom2. rewrite dom2dom' in H17. rewrite <-Heqe4;auto. rewrite eDef;auto.*)
rename H2 into unList.

Check execActionUniqList.
 
  rewrite execActionUniqList with (a:=(stepActions s0)) (lre:=nil) (eventList:=(filter (fun e : event_definition =>
                match eventKind e with
                | Internal => true
                | Imported => false
                | Exported => true
                end) (events M))) (ven':=v1) (lre':=l0) in unList. apply typeActionTyConsistent with (t_env:=dom2 (datastate conf ++ v)) in Heqe2;auto. Focus 2.  apply evnConsistDom2;auto. intros. rewrite domApp in H2.
  apply in_app_or in H2. destruct H2.
  apply tyEnvVar with (datastate conf);auto. destruct H;auto.
  apply tyEnvVar with v;auto.
  apply raisedTyEnv with (nl:=(eventArgs e)) (tl:=(eventParams (eventDefinition re))) (vl:=(eventArguments re));auto. 
  apply raised_wellform with (e:=re) in H;auto. 
  rewrite dom2App in Heqe2.
  pose proof evnConsistProp.
  apply H2 in Heqe2.
      repeat (match goal with
            | [H: _ /\ _ |-_] => destruct H
            | [H: exists _, _ |- _] => destruct H
              end).
      destruct H.
      rewrite ds_dom_eq in H11. pose proof evnConsistEq'.

      apply H with (x1:=x0);auto.
       rewrite <- H10. rewrite dom2App. rewrite dom2App.  f_equal.
       rewrite ds_dom_eq. symmetry. apply dom2Equal'';auto. 
auto.       
Qed. 

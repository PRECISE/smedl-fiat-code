(*AST of SMEDL
*)

(*
date: 04/19/2017
author: Teng Zhang
*)


(*Syntax related to the monitor and auxiliary lemmas are defined in this file, which will be used in definition of semantics*)
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
  Coq.Classes.EquivDec.

Require Import Coq.Sorting.Permutation.

 
Set Implicit Arguments.
Set Decidable Equality Schemes.

Unset Strict Implicit.
Unset Printing Implicit Defensive.
Generalizable All Variables.

Require Import Coq.Strings.Ascii.

Open Scope N_scope.

Definition typeErr : string := "Type error".
Definition zeroErr: string := "zero divisor". 
Definition eventNotDeclaredErr : string := "event not declared".

(*Used to distinct between normal value and error*)
Inductive ErrorOrResult{T} :=
| Result : forall v: T, @ErrorOrResult T
| Error : forall s: string, @ErrorOrResult T.


Section AST.

(* type            = ?/[a-zA-Z][A-Za-z0-9_]*/? ;
   identifier      = ?/[a-zA-Z][A-Za-z0-9_]*/? ;
   identifier_list = @:identifier {',' @:identifier}* | () ;
   target          = identifier  ;
   integer         = ?/[-+]?[0-9]+/? ;
   float           = ?/[-+]?[0-9]*\.?[0-9]+/? ; *)

(*supported type in SMEDL*)
Inductive typ :=
| Int 
| Float
| Str
| Bool
| Pointer
| Opaque
| Thread
.

Check typ_eq_dec. 


(* variable_declaration
       = type:type var:identifier {',' var:identifier}* ';' ; *)

(* atom = integer | float | identifier | 'true' | 'false' | string | 'null' ; *)

Inductive atom : Set :=
  | AInt   : Z -> atom
  | AFloat : Q -> atom
  | AIdent : string -> atom
  | ABool  : bool -> atom
  | ANull  : atom
  | AString : string -> atom.

(*Scheme Equality for atom.*)
Check atom_eq_dec. 

(*typing environment*)
Definition typ_env := (list (atom * typ)).

Definition ty_denotes (ty : typ) : Type :=
match ty with
| Int => Z
| Float => Q
| Str => string                
| Bool => bool
| Pointer => nat
| Opaque => nat                  
| Thread => nat                  
end.

(*supported value in SMEDL*)
(*Z and nat has different usage, but nat may be removed later*)
Definition range_typ : Set := (Z+Q+string+bool+nat).

Definition range_typ_dec (re:range_typ):  forall re', {re = re'} + {re <> re'}.
Proof. repeat decide equality.   Defined.  

Check range_typ_dec. 
(*value environment*)
(*used to represent the scope in SMEDL*)
Definition value_env := (list (atom *( typ * range_typ))).

Fixpoint typeValMatch (t: typ) (v: range_typ) : bool :=
  match (t,v) with
  | (Int, (inl (inl (inl (inl _))))) => true
  | (Float, (inl (inl (inl (inr _))))) => true                                     
  | (Str, (inl (inl (inr _)))) => true
  | (Bool, (inl (inr _))) => true
  | (Pointer, (inr _)) => true
  | (Opaque, (inr _)) => true
  | (Thread, (inr _)) => true
  | _ => false                         
  end.

Fixpoint wellVeFun (ven: value_env) : bool :=
  match ven with
  | nil => true
  | (AIdent _,(t,v))::ven' => typeValMatch t v && wellVeFun ven'
  | _ => false                                        
  end.
 

(*return domination*)
Definition dom (A:Type) (B: Type) (env: list (A*B)): list A := 
  map (fun v:(A*B) => fst v) env.

Check map.
 

Definition dom2 (A:Type) (B: Type) (C: Type) (env: list (A*(B*C))): list (A * B) := 
  map (fun v:(A*(B*C)) => (fst v, (fst (snd v)))) env.

Definition dom2' (A:Type) (B: Type) (C: Type) (env: list (A*B*C)): list (A * B) := 
  map (fun v:(A*B*C) => (fst (fst v), snd (fst v))) env.


Definition string_dec_bool (s1:string) (s2:string) : bool :=
if string_dec s1 s2 then true else false. 

(*currently not used*)
Inductive uniq (A : Type) : list (atom * A) -> Prop :=
|  uniq_nil : uniq nil
| uniq_push : forall (x : atom) 
                  (a : A) (E : list (atom * A)),
                uniq E ->
                ~(In x (dom E)) -> uniq ((x,a)::E).

Inductive uniqList (A : Type) : list (A) -> Prop :=
|  uniqL_nilL: uniqList nil
| uniqL_push : forall  
                  (a : A) (E : list ( A)),
                uniqList E ->
                ~(In a (E)) -> uniqList ((a)::E).

Lemma uniqListNoDupEq: forall (A:Type) l,  uniqList l <-> @NoDup A l.
Proof. intros.
split.
- induction l. intros. constructor.
 intros. inversion H. subst. apply NoDup_cons;auto.
- induction l. intros. constructor. intros. inversion H;subst. apply uniqL_push;auto.
Qed.

                    
(*auxiliary lemma*)
(*append of two jointed unique list is a uniqlist*)
Lemma uniqApp': forall (A:Type) (l1 l2:list A),
uniqList l1 -> uniqList l2 -> (forall i, In i l1 -> ~(In i l2)) ->
(forall i, In i l2 -> ~(In i l1)) -> uniqList(l1 ++ l2).  
Proof. intros A l1.
induction l1. intros. simpl. auto.   
intros. inversion H. subst.
assert (~ In a l2). apply H1. simpl. left. auto.    
simpl. apply uniqL_push. apply IHl1. auto. auto. intros. apply H1. simpl. right. auto.
intros. apply H2 in H4. unfold not in H4. unfold not. intros. apply H4.
simpl. right. auto. unfold not. intros.
apply in_app_iff in H4. destruct H4. 
unfold not in H6. apply H6. auto. unfold not in H3. apply H3. auto.
Qed.       
       
                  
(*auxiliary function, bool version of "In" *)
Fixpoint inList (A: Type) (decA: forall (x y:A), {x=y} + {x<>y}) (x: A) (lst : list A) : bool :=
match lst with
| nil => false
| y::lst' => if decA x y then true else (inList decA x lst')
end.


(*two lists are permutation of each other*)
Definition equivList {A: Type}   (l1: list A) (l2: list A) : Prop := 
Permutation l1 l2.


  
  
(*auxiliary function, update value of a varialbe in the environment*)
Fixpoint updateValueEnvInv (a: atom) (v: range_typ) (en:value_env): option value_env :=
match a with
| AIdent i => match en with
                        | nil => Some nil
                        | (a',(t',v'))::en' => if atom_eq_dec a a' then
                                                   if typeValMatch t' v then
                                                     Some ((a',(t',v))::en')
                                                   else
                                                     None
                                              else
                                                match (updateValueEnvInv a v en') with
                                                | Some ven' => Some ((a',(t', v')) :: ven')
                                                | None => None
                                                end
                   end

| _ => None
end
.


(*auxiliary function, create a new environment based on the variable names, types and values*)
Fixpoint createValueEnv (nlst: list string) (tlst: list typ) (vlst: list range_typ): (ErrorOrResult):=
  match nlst,tlst,vlst with
| nil, nil, nil => Result (nil)
| s::nlst', t::tlst', v::vlst' => match createValueEnv nlst' tlst' vlst' with
                                                       | Error (s) => (Error s)
                                                       | Result (ve) => Result ((AIdent s,(t,v)):: ve)
                                                    end
| _, _, _ => Error ("number of list not matched")
end. 

(*auxiliary function,get the type of a variable from the environment*)
Fixpoint getType (a: atom) (en:typ_env) : option typ :=
match a with
| AIdent i => match en with
                        | nil => None
                        | (a',v)::en' => if  atom_eq_dec a a' then Some v else getType a en'
                   end
| _ => None
end.

Fixpoint getTypeValue (a:atom) (en:value_env) : option (typ *range_typ) :=
match a with
| AIdent s =>
  match en with
  | nil => None
  | (a',(t,v)) ::en'  => if atom_eq_dec a a' then Some (t,v) else getTypeValue a en' 
 end
| _ => None
end.

(*auxiliary function,get the value of a variable from the environment*)
Fixpoint getValue (a: atom) (en:value_env) : option range_typ :=
match a with
| AIdent i => match en with
                        | nil => None
                        | (a',(_,v))::en' => if  atom_eq_dec a a' then Some v else getValue a en'
                   end
| _ => None
end.


(*extend environment*)
(*assume that newly added variables are fresh to the environment*)
Definition extendEnv (A:Type) (en: list (atom * A)) (pen: list (atom * A)) : list (atom * A) := app en pen.

Definition extendValEnv  (en: value_env) (pen: value_env) : value_env := app en pen.

(* expression = or_ex:and_expr {'||' or_ex:and_expr}+ | @:and_expr ;
   expression_list = @:expression {',' @:expression}* | () ;
   and_expr = and_ex:sub_expr {'&&' and_ex:sub_expr}+ | @:sub_expr ;
   sub_expr = {'!!'}*'!(' not_ex:expression ')'
            | {'!!'}*'(' @:expression ')'
            | @:comp_expr ;
   comp_expr = comp:arith_expr
                 {operator:('>=' | '<=' | '==' | '!=' | '>' | '<')
                      comp:arith_expr}+
             | '(' @:comp_expr ')'
             | @:arith_expr ;
   arith_expr = arith:term {operator:('+' | '-' | '*' | '/' | '%') arith:term}+
              | @:term ;
   term = {unary:('+' | '-' | '~' | '!')}* atom:atom {trailer:trailer}*
        | {unary:('+' | '-' | '~')}* '(' @:arith_expr ')' ;
   trailer = '[' [index:expression] ']'
           | '(' [params:expression_list] ')'
           | '.' dot:identifier {trailer:trailer}* ; *)

Inductive expr : Set :=
  (* or_expr *)
  | EOr : expr -> expr -> expr

  (* and_expr *)
  | EAnd : expr -> expr -> expr

  (* comp_expr *)
  | EEq  : expr -> expr -> expr
  | ELt  : expr -> expr -> expr
  | ELe  : expr -> expr -> expr

  (* arith_expr *)
  | EPlus  : expr -> expr -> expr
  | EMult  : expr -> expr -> expr
  | EDiv   : expr -> expr -> expr
  | EMod   : expr -> expr -> expr

  (* term *)
(*  | ECmp : expr -> expr*)
  | ENot : expr -> expr

  | EAtom  : atom -> expr
.

SearchAbout list sumbool.



(* event_definition =
       error:['error'] event_id:identifier ['(' params:parameter_list ')']
           ['=' definition:expression] ;
   parameter_list = @:type {',' @:type}* | () ;
   event_definition_list = @:event_definition {',' @:event_definition}* ';' ; *)

Check expr_eq_dec. 

 (*Lemma expr_eq_dec : forall e1 e2: expr, {e1 = e2} + {e1 <> e2}.
Proof.
 fix rec 1.
 repeat decide equality.
Qed.*)

(*Instance expr_eq_dec1: EqDec expr eq. *)


Record exprlist :={
lst: list expr
}.

Lemma exprlist_eq_dec :
 forall e1 e2: exprlist, {e1 = e2} + {e1 <> e2}.
Proof. pose proof expr_eq_dec. repeat decide equality.  
Defined. 


Inductive EventKind := Internal | Imported | Exported.


Definition eventKind_dec (n m : EventKind) : {n = m} + { n <> m}.
Proof. repeat decide equality. 
Defined.

Definition EventKind_beq (n m : EventKind) : bool :=
  match (n,m) with
  | (Internal,Internal) => true
  | (Imported,Imported) => true
  | (Exported,Exported) =>true
  | _ => false
  end. 

Record event_definition : Set := {
  eventKind   : EventKind;
  eventId     : string;
  eventParams : list typ;
 (* eventParams : list string;*)
  (*eventDef    : option expr*)
}.


Definition event_definition_dec (n m : event_definition) : {n = m} + { n <> m}.
Proof. repeat decide equality. 
Defined. 

Record correct_event_definition (ev : event_definition) : Prop := {
}.

(* actions = '{' actions:action_item_list '}' ;
   action_item_list = @:action_item ';' { @:action_item ';' }* ;
   action_item
       = state_update:state_update
       | raise_stmt:raise_stmt
       | instantiation:instantiation_stmt
       | call_stmt:call_stmt ;
   raise_stmt = 'raise' id:identifier ['(' expr_list+:expression_list ')'] ;
   instantiation_stmt
       = 'new' id:identifier ['(' state_update_list+:state_update_list ')'] ;
   call_stmt = target:target '(' expr_list+:expression_list ')' ;

   state_update = target:target operator:('++' | '--')
       | target:target operator:'=' expression:expression ;
   state_update_list = @:state_update {',' @:state_update}* | () ; *)

Inductive LValue :=
| LExp : atom -> LValue.

(*Lemma LValue_eq_dec : forall e1 e2: LValue, {e1 = e2} + {e1 <> e2}.
Proof.
 fix rec 1.
 repeat decide equality. 
Qed.*)


(*Instantiation and CallStmt are not used for now*)
Inductive action : Set :=
  | Skip : action
  | StateUpdate : LValue -> expr -> action
  | RaiseStmt (ident : string) (exprs : list expr) : action
  | Seq : action -> action -> action.



Lemma action_eq_dec :
 forall e1 e2: action, {e1 = e2} + {e1 <> e2}.
Proof. intros. 
pose proof expr_eq_dec.
repeat decide equality.
Defined.  


(* event_instance = expression:expression ['when' when:expression] ; *)

Record event_instance : Set := {
  event: event_definition; (*event definition of this instance*)
  eventArgs     : list string; (*indentifiers*)
  eventWhenExpr : expr
}.



Definition event_instance_dec (n m : event_instance) : {n = m} + { n <> m}.
Proof.  pose proof  atom_eq_dec.  intros. decide equality. Focus 3. 
apply event_definition_dec. 
Focus 2.  
repeat decide equality.
 decide equality.                
Defined. 

Check string_dec. 

(* step_definition = step_event:event_instance [step_actions:actions] ; *)

Definition scenario_state := string. 



Record step : Set := {
  pre_state : scenario_state; (*source state of the step*)
  stepEvent : event_instance;
  stepActions : action;
  pro_state : scenario_state (*target state of the step*)
}.

Definition step_dec (n m : step) : {n = m} + { n <> m}.
Proof.  pose proof action_eq_dec. pose proof expr_eq_dec.
 repeat decide equality.
Defined.  




(* trace_definition
       = start_state:identifier '->'
           {trace_steps+:step_definition '->'}+  end_state:identifier
           ['else' [else_actions:actions] '->' else_state:identifier] ; *)

Record trace : Set := {
  startState  : string;
  traceSteps  : list step;      (* non-empty *)
  endState    : string;

}.

Definition trace_dec (n m : trace) : {n = m} + { n <> m}.
Proof.  pose proof expr_eq_dec.
 repeat decide equality. Defined. 

Record correct_trace (tr : trace) : Prop := {
   _ : (0 < length (traceSteps tr))%nat
 
}.

(* scenario_definition
       = atomic:['atomic'] scenario_id:identifier
           ':' traces:{trace_definition}+ ; *)

(*state machine*)
Record scenario : Set := {
  scenarioId : string;
  traces     : list step       (* non-empty *);
  alphabet : list event_definition (*list of events triggering the transition in the scenario*)
}.

Definition scenario_dec (n m : scenario) : {n = m} + { n <> m}.
Proof. pose proof expr_eq_dec.
 repeat decide equality. Defined. 

Record correct_scenario (s : scenario) : Prop := {
  _ : (0 < length (traces s))%nat ;
  _ : uniqList (traces s)
}.

(*mapping from scenario to its current state*)
(*assume that with in the same monitor, all states in different state machine have a unique name*)
Definition scenario_env := (list (scenario*scenario_state)).

Definition scenario_state_dec (n m : scenario*scenario_state) : {n = m} + { n <> m}.
Proof. pose proof scenario_dec. pose proof string_dec. 
 repeat decide equality. Defined. 

Print string_dec. 
Fixpoint getScenarioState (sce:scenario) (env: scenario_env) : option  scenario_state :=
match env with
| nil => None
| (s,e)::en' => if (string_dec) (scenarioId sce) (scenarioId s) then Some e else getScenarioState sce en'
end.

Check string_dec.

Check scenario_dec.

Fixpoint getScenarioState' (sce:scenario) (env: scenario_env) : option  scenario_state :=
match env with
| nil => None
| (s,e)::en' => if scenario_dec sce s then Some e else getScenarioState sce en'
end.


Fixpoint updateScenarioState' (sce:scenario) (st:scenario_state) (env:scenario_env) :  scenario_env :=
match env with
| nil => nil
| (s,e)::en' => if string_dec (scenarioId s) (scenarioId sce) then (s,st)::updateScenarioState' sce st en' else (s,e)::updateScenarioState' sce st en'
end.

Print scenario.
Print trace.


Fixpoint getTransitionsFromTraces  (lt: list trace) : list step :=
  match lt with
  | nil => nil
  | tr::lt' =>  (traceSteps tr) ++ (getTransitionsFromTraces lt')
end.

Definition getTransitionsOfScenario (sce:scenario) : list step :=  (traces sce). 

Print step.

(*elements in l1 will be filtered out from l2*)
Fixpoint filterList (A:Type) (l1: list A) (l2: list A) (decA: forall (x y:A), {x=y} + {x<>y}) : list A:=
match l2 with
| nil => nil
| e'::lst => if inList decA e' l1 then filterList  l1 lst decA else e'::filterList  l1 lst decA
end.

Definition mergeList' (A:Type) (l1: list A) (l2: list A) (decA: forall (x y:A), {x=y} + {x<>y})  : list A :=
let l2':= filterList l1 l2 decA in
app l1 l2'.

Print step.

Fixpoint collectStates (lst: list step) : list scenario_state :=
  match lst with
  | nil => nil
  | (stp::lst') => mergeList' (mergeList' ((pre_state stp)::nil) ((pro_state stp)::nil) string_dec) (collectStates lst') string_dec
  end.

Definition sceStateRelation (sce:scenario) : list scenario_state :=
  collectStates (getTransitionsOfScenario sce). 

(* import_definition = '#import' import_id:identifier ;
   object =
       imports+:{import_definition}*
       'object' object:identifier
       ['identity' identity+:{variable_declaration}+]
       ['state' state+:{variable_declaration}+]
       'events'
           { 'internal' internal_events+:event_definition_list
           | 'exported' exported_events+:event_definition_list}*
           'imported' imported_events+:event_definition_list
           { 'imported' imported_events+:event_definition_list
           | 'internal' internal_events+:event_definition_list
           | 'exported' exported_events+event_definition_list}*
       'scenarios'
           scenarios+:{scenario_definition}+ $ ; *)

(*monitor*)
Record object : Type := {
  imports    : list string;
  objectId   : string;
  identities : typ_env;      (* name -> type *)
  variables  : typ_env;      (* name -> type *)
  events     : list event_definition;
  scenarios  : list scenario;         (* non-empty *)
  stateEvStepMap : list (scenario_state*event_instance*option step);
  stateEvStepMap' : list (scenario_state*event_instance*scenario*option step);
  stateEvDefInstanceMap : list ((option scenario_state)*(option event_definition)*(list event_instance));
  stepScenarioMap: list (scenario*step); (*range uniq*)
  stateScenarioMap: list (scenario*scenario_state);
  (*range uniq && step and state should correspond to same scenario, steps sharing the same state should correspond to the same scenario*)
}.

Definition object_dec (n m : object) : {n = m} + { n <> m}.
Proof. pose proof expr_eq_dec.
 repeat decide equality. Defined. 


(*check if the event is an imported event*)
Definition importedEvent (ev : event_definition) : Prop :=
  match eventKind ev with
  | Imported => True
  | Internal => False
  | Exported => False
  end.

(*check if the event is an imported or internal event*)
Definition importedOrInternalEvent (ev : event_definition) : Prop :=
 (match eventKind ev with
  | Imported => True
  | Internal => True
  | Exported => False
  end).


Definition dsmon (mon:object) := (identities mon) ++ (variables mon).
Print dom2. 
Check stateEvStepMap.


Record correct_object (obj : object) : Prop := {
  _ : List.Forall correct_event_definition (events obj);
  _ : List.Exists importedEvent (events obj);
  _ : List.Forall correct_scenario (scenarios obj);
  _ : (0 < length (scenarios obj))%nat;
  _ : uniqList (dom (dsmon obj));
  (*_ : uniqList (dom2' (stateEvStepMap obj));*)
  _ : uniqList (events obj);
}.


Record raisedEvent : Type :={
  eventDefinition: event_definition;
  eventArguments     : list (range_typ);
}.

Definition raisedEvent_dec (n m : raisedEvent) : {n = m} + { n <> m}.
Proof. repeat decide equality. 
Defined. 




End AST.

(*Arguments AInt _.
Arguments AFloat _.
Arguments ABool _.
Arguments AIdent _.
Arguments ANull.

Arguments EOr _ _.
Arguments EAnd _ _.

Arguments EEq _ _.

Arguments ELt _ _.
Arguments ELe _ _.


Arguments EPlus _ _.
Arguments EMult _ _.
Arguments EDiv _ _.
Arguments EMod _ _.

(* Arguments ECmp _. *)
Arguments ENot _.

Arguments EAtom _.


Arguments expr.*)

Section Monad.



(*aux function for evaluation*)
Definition Bind {T} : @ErrorOrResult T -> (T -> @ErrorOrResult T) -> @ErrorOrResult T :=
  fun val func =>
    match val with
    | Error err => Error err
    | Result v => (func v)
    end.

Notation ret v := (Result v).

Notation "x <t- m ; y" := (Bind m (fun x => y))
                           (at level 51, right associativity,
                            format "'[v' x  <t-  m ; '/' y ']'").

(*
Definition BindZ : ErrorOrResult -> (Z -> ErrorOrResult) -> ErrorOrResult :=
  fun val func =>
    v <- val;
    match v with
    | AInt n => func n
    | _ => Error typeErr 
    end.

Definition BindQ : ErrorOrResult -> (Q -> ErrorOrResult) -> ErrorOrResult :=
  fun val func =>
    v <- val;
    match v with
    | AFloat q => func q
    | _  => Error typeErr
    end.

Definition BindNum : ErrorOrResult -> (Z+Q -> ErrorOrResult) -> ErrorOrResult :=
  fun val func =>
    v <- val;
    match v with
    | AFloat q => func (inr q)
    | AInt n => func (inl n)
    | _  => Error typeErr
    end.

Definition BindBool : ErrorOrResult -> (bool -> ErrorOrResult) -> ErrorOrResult :=
  fun val func =>
    v <- val;
    match v with
    | ABool b => func b
    | _  => Error typeErr
    end.


Definition BindStr : ErrorOrResult -> (string -> ErrorOrResult) -> ErrorOrResult :=
  fun val func =>
    v <- val;
    match v with
    | AString s => func s
    | _  => Error typeErr
    end.

Definition BindData: ErrorOrResult -> (Z+Q+bool+string -> ErrorOrResult) -> ErrorOrResult :=
  fun val func =>
    v <- val;
    match v with
    | AString s => func (inr s)
    | ABool b => func (inl (inr b))
    | AInt n => func (inl (inl (inl n)))
    | AFloat q => func (inl (inl (inr q)))
    | _  => Error typeErr
    end.
 *)

Print ErrorOrResult. 

Definition BindZ : (@ErrorOrResult range_typ) -> (Z -> ErrorOrResult) -> ErrorOrResult :=
  fun val func =>
    v <t- val;
    match v with
    | (inl (inl (inl (inl n)))) => func n
    | _ => Error typeErr 
    end.

Definition BindQ : (@ErrorOrResult range_typ) -> (Q -> ErrorOrResult) -> ErrorOrResult :=
  fun val func =>
    v <t- val;
    match v with
    | (inl (inl (inl (inr q)))) => func q
    | _  => Error typeErr
    end.

Definition BindNum : (@ErrorOrResult range_typ) -> (Z+Q -> ErrorOrResult) -> ErrorOrResult :=
  fun val func =>
    v <t- val;
    match v with
    | (inl (inl (inl (inr q)))) => func (inr q)
    | (inl (inl (inl (inl n)))) => func (inl n)
    | _  => Error typeErr
    end.

Definition BindBool : (@ErrorOrResult range_typ) -> (bool -> ErrorOrResult) -> ErrorOrResult :=
  fun val func =>
    v <t- val;
    match v with
    | (inl (inr b)) => func b
    | _  => Error typeErr
    end.


Definition BindStr : (@ErrorOrResult range_typ) -> (string -> ErrorOrResult) -> ErrorOrResult :=
  fun val func =>
    v <t- val;
    match v with
    | (inl (inl (inr s))) => func s
    | _  => Error typeErr
    end.


Definition BindData: (@ErrorOrResult range_typ) -> (range_typ -> ErrorOrResult) -> ErrorOrResult :=
  fun val func =>
    v <t- val;
      func v.

   




End Monad.

Notation "x <z- m ; y" := (BindZ m (fun x => y))
                             (at level 51, right associativity,
                              format "'[v' x  <z-  m ; '/' y ']'").

Notation "x <q- m ; y" := (BindQ m (fun x => y))
                             (at level 51, right associativity,
                              format "'[v' x  <q-  m ; '/' y ']'").

Notation "x <num- m ; y" := (BindNum m (fun x => y))
                             (at level 51, right associativity,
                              format "'[v' x  <num-  m ; '/' y ']'").


Notation "x <bool- m ; y" := (BindBool m (fun x => y))
                              (at level 51, right associativity,
                               format "'[v' x  <bool-  m ; '/' y ']'").


Notation "x <data- m ; y" := (BindData m (fun x => y))
                              (at level 51, right associativity,
                               format "'[v' x  <data-  m ; '/' y ']'").


Print range_typ.




(*Notation retInt v := (Result (AInt v)).
Notation retBool v := (Result (ABool v)).
Notation retFloat v := (Result (AFloat v)).
Notation retStr v := (Result (AString v)).
Notation retNull v := (Result (ANull)).*)

Section Denotation.

Definition Expr := expr.

Import ListNotations.



Print AFloat. 

Notation retInt v := (Result (inl (inl (inl (inl v))))).
Notation retBool v := (Result (inl (inr v))).
Notation retFloat v := (Result (inl (inl (inl (inr v))))).
Notation retStr v := (Result ((inl (inl (inr v))))).
Notation retNull := (Result (inr O)).

Local Open Scope Z_scope.
Local Open Scope string_scope.
Local Open Scope Q_scope.

(*expr evaluation*)
(*use monad to hide error info*)
Locate "*".

Fixpoint evalMonad (env:value_env) (e:expr): ErrorOrResult :=
match e with
|EOr x y => b1 <bool- (evalMonad env x);
                   b2 <bool- evalMonad env y; 
                   retBool ((b1 || b2))
|EAnd x y => b1 <bool- evalMonad env x;
                   b2 <bool- evalMonad env y;
                   retBool ((b1 && b2))
| ENot x => b1 <bool- evalMonad env x;
                   retBool ( (negb b1))
| EEq x y => n1 <data- (evalMonad env x);
             n2 <data- (evalMonad env y);
                    match n1, n2 with
                    | (inl (inl (inl (inl i)))), (inl (inl (inl (inl j)))) => retBool ( (i =? j)) 
                    | (inl (inl (inl (inr p)))),(inl (inl (inl (inr q)))) =>  retBool ( (Qeq_bool p q))
                    | (inl (inl (inr s1))),  (inl (inl (inr s2))) => retBool ( (string_dec_bool s1 s2))
                    | (inl (inr s1)), (inl (inr s2)) => retBool (eqb s1 s2)
                    | (inr s1), (inr s2)   => retBool (beq_nat s1 s2)
                    | _, _ => Error typeErr                                 
                   end

| ELt x y => n1 <num- evalMonad env x;
                    n2 <num- evalMonad env y;
                    match n1, n2 with
                    | (inl i), (inl j) => retBool ( (i <? j))
                    | (inr p), (inr q) =>  retBool ( (Qle_bool p q) && (negb (Qeq_bool p q)))
                    | _,_ =>  Error typeErr                               
                   end

| ELe x y => n1 <num- evalMonad env x;
                    n2 <num- evalMonad env y;
                    match n1, n2 with
                    | (inl i), (inl j) => retBool ( (i <=? j))
                    | (inr p), (inr q) =>  retBool ( (Qle_bool p q) )
                    | _,_ =>  Error typeErr                              
                   end


| EPlus x y => n1 <num- evalMonad env x;
                    n2 <num- evalMonad env y;
                    match n1, n2 with
                    | (inl i), (inl j)  => retInt (Z.add i j)
                    | (inr p), (inr q) =>  retFloat (p + q)
                    | _, _ =>  Error typeErr                              
                   end 
| EMult x y => n1 <num- evalMonad env x;
                    n2 <num- evalMonad env y;
                    match n1, n2 with
                    | (inl i), (inl j)  => retInt (Z.mul i j)
                    | (inr p), (inr q) =>  retFloat (p * q)
                    | _, _ =>  Error typeErr                                   
                   end 

| EDiv x y => n1 <num- evalMonad env x;
                    n2 <num- evalMonad env y;
                    match n1, n2 with
                    | (inl i), (inl j)  => retInt (Z.div i j)
                    | (inr p), (inr q) =>  retFloat (p / q)
                    | _, _ =>  Error typeErr                                   
                   end 

| EMod x y => n1 <z- evalMonad env x;
                    n2 <z- evalMonad env y;
                    retInt (n1 mod n2)

|EAtom x => match x with
    | AIdent i => match getValue  (AIdent i) env with
                        | None => Error typeErr
                        | Some (inl (inl (inl (inl z)))) => retInt (z)
                        | Some (inl (inl (inl (inr q)))) => retFloat (q)
                        | Some (inl (inl (inr s))) => retStr (s)
                        | Some (inl (inr b)) => retBool (b)                                     
                        | Some (inr n) => Result (inr n)
                        end
    | AInt z => retInt (z)
    | AFloat q =>  retFloat (q)
    | AString s => retStr (s)
    | ANull => retNull
    | ABool b => retBool b
    end
           
end.

Print expr.
Print find.

Inductive HasTy (Gamma : typ_env) : expr -> typ -> Prop :=
| HasTy_Var : forall s ty,
    find (fun p => match p with
                   | (pa,_) => if atom_eq_dec pa (AIdent s) then true else false
                   end) (Gamma) = Some ((AIdent s),ty) ->
   HasTy Gamma (EAtom (AIdent s)) ty
| HasTy_LitInt : forall n,
    HasTy Gamma  (EAtom (AInt n) ) Int
| HasTy_LitFloat : forall q,
    HasTy Gamma  (EAtom (AFloat q)) Float        
| HasTy_LitBool : forall b,
    HasTy Gamma  (EAtom (ABool b)) Bool
| HasTy_LitNull :
    HasTy Gamma  (EAtom (ANull )) Pointer         
| HasTy_LitStr : forall s,
    HasTy Gamma  (EAtom (AString s)) Str          
| HasTy_Op2_Plus1 : forall {e1 e2},
   HasTy Gamma e1 Int ->
   HasTy Gamma e2 Int ->
   HasTy Gamma (EPlus e1 e2) Int
| HasTy_Op2_Plus2 : forall {e1 e2},
   HasTy Gamma e1 Float ->
   HasTy Gamma e2 Float ->
   HasTy Gamma (EPlus e1 e2) Float       
| HasTy_Op2_Mult1 : forall {e1 e2},
   HasTy Gamma e1 Int ->
   HasTy Gamma e2 Int ->
   HasTy Gamma (EMult e1 e2) Int
| HasTy_Op2_Mult2 : forall {e1 e2},
   HasTy Gamma e1 Float ->
   HasTy Gamma e2 Float ->
   HasTy Gamma (EMult e1 e2) Float        
| HasTy_Op2_Div1 : forall {e1 e2},
   HasTy Gamma e1 Int ->
   HasTy Gamma e2 Int ->
   HasTy Gamma (EDiv e1 e2) Int
| HasTy_Op2_Div2 : forall {e1 e2},
   HasTy Gamma e1 Float ->
   HasTy Gamma e2 Float ->
   HasTy Gamma (EDiv e1 e2) Float     
| HasTy_Op2_Mod : forall {e1 e2},
   HasTy Gamma e1 Int ->
   HasTy Gamma e2 Int ->
   HasTy Gamma (EMod e1 e2) Int
| HasTy_Op2_And : forall {e1 e2},
   HasTy Gamma e1 Bool ->
   HasTy Gamma e2 Bool ->
   HasTy Gamma (EAnd e1 e2) Bool
| HasTy_Op2_Or : forall {e1 e2},
   HasTy Gamma e1 Bool ->
   HasTy Gamma e2 Bool ->
   HasTy Gamma (EOr e1 e2) Bool
| HasTy_Op2_Eq : forall {e1 e2 t},
   HasTy Gamma e1 t ->
   HasTy Gamma e2 t ->
   HasTy Gamma (EEq e1 e2) Bool         
| HasTy_Op2_Lt1 : forall {e1 e2},
   HasTy Gamma e1 Int ->
   HasTy Gamma e2 Int ->
   HasTy Gamma (ELt e1 e2) Bool
| HasTy_Op2_Lt2 : forall {e1 e2},
   HasTy Gamma e1 Float ->
   HasTy Gamma e2 Float ->
   HasTy Gamma (ELt e1 e2) Bool     
| HasTy_Op2_Le1 : forall {e1 e2},
   HasTy Gamma e1 Int ->
   HasTy Gamma e2 Int ->
   HasTy Gamma (ELe e1 e2) Bool
| HasTy_Op2_Le2 : forall {e1 e2},
   HasTy Gamma e1 Float ->
   HasTy Gamma e2 Float ->
   HasTy Gamma (ELe e1 e2) Bool         
| HasTy_Op2_Not : forall {e1},
   HasTy Gamma e1 Bool ->
   HasTy Gamma (ENot e1) Bool
.
         


Definition typeCheckExpr (ex:expr) (env: typ_env): Prop :=
  exists ty, HasTy env ex ty.
Locate "/".





Fixpoint calculateExprList (en:value_env) (lst: list expr): (ErrorOrResult) :=
match lst with
| nil => Result (nil)
| ex::lst' => match evalMonad en ex with
                  | Error error =>  (Error error)
                  | Result v => match calculateExprList en lst' with
                                      | (Error s) => (Error s)
                                      | Result (vlst) => Result (v:: vlst)
                                      end
                  end
end.

Fixpoint getEventByName (name: string) (elist: list event_definition):  option event_definition := 
match elist with
| nil => None
| e::lst' => if string_dec (eventId e) name then Some e else getEventByName name lst'
end.

Inductive parameterMatch  : list range_typ -> list typ -> Prop :=
| basic_paraMatch : parameterMatch nil nil
| ind_paraMatch : forall rlst tlst rt t, parameterMatch rlst tlst -> typeValMatch t rt = true -> parameterMatch (rt::rlst) (t::tlst).

Fixpoint parameterMatchFunc (rl: list range_typ) (tl: list typ) : bool :=
  match (rl,tl) with
  | (nil,nil) => true
  | (rt::rlst, t::tlst) => if typeValMatch t rt then parameterMatchFunc rlst tlst
                           else
                             false
  | (_,_) => false
end. 

(*list of actual parameters is consistent with its event definition*)
Definition wellFormedRaisedEvent (re: raisedEvent) : Prop :=
  parameterMatch (eventArguments re) (eventParams (eventDefinition re)).

Lemma parameterMatch_refl: forall l tl,
    parameterMatch l tl <-> parameterMatchFunc l tl = true. 
Proof.
  intro l;induction l. 
-
  intros.
  split;intros. 
  destruct tl;auto. inversion H.
  destruct tl;inversion H. constructor.  
-
  split.
  intros.
  destruct tl;inversion H. subst.
  simpl.
  destruct (typeValMatch t a).
  apply IHl;auto. inversion H5.
  intros.
  destruct tl;inversion H.
  constructor. apply IHl;auto.
  inversion H.
  destruct (typeValMatch t a ).
  auto. inversion H1.
  destruct (typeValMatch t a ). auto. inversion H1. 
Qed.

Check HasTy.
Print event_definition. 

Inductive HasTy_ExprList (Gamma: typ_env) : list expr -> list typ -> Prop :=
| basic_eList: HasTy_ExprList Gamma nil nil
| inductive_eList: forall e l ex ty, HasTy_ExprList Gamma e l -> HasTy Gamma ex ty -> HasTy_ExprList Gamma (ex::e) (ty::l). 
  
Inductive HasTy_action (Gamma : typ_env) (el: list event_definition) : action -> Prop :=
| HasTy_action_Skip : HasTy_action Gamma el Skip
| HasTy_action_Assign: forall s ex ty,
     getType (AIdent s) Gamma = Some ty ->
     HasTy Gamma ex ty ->
     HasTy_action Gamma el (StateUpdate (LExp (AIdent s)) ex)
| HasTy_action_Raise: forall n  lst,
    (exists e, getEventByName n el = Some e /\ HasTy_ExprList Gamma lst (eventParams e) ) -> 
    HasTy_action Gamma el (RaiseStmt n lst)
| HasTy_action_Seq: forall c1 c2,
    HasTy_action Gamma el c1 ->
    HasTy_action Gamma el c2 ->
    HasTy_action Gamma el (Seq c1 c2).


(*
Inductive action : Set :=
  | StateUpdate : LValue -> expr -> action
  | RaiseStmt (ident : string) (exprs : list expr) : action
  | Seq : action -> action -> action.
 *)

                              
End Denotation.

(*
Fixpoint execAction  (etaE: value_env*(list raisedEvent)) (a:action) (eventList: list event_definition) : ErrorOrResult :=
  match a with
  | StateUpdate (LExp (AIdent s)) ex => let er := evalMonad (fst etaE) ex in
                                 match er with
                                 | Result v =>
                                     match updateValueEnvInv (AIdent s) v (fst etaE) with
                                     | Some ven => Result (ven,snd etaE)                                                                | None => Error typeErr
                                                                                                                                        end
                                 | Error r => Error r
                                 end
  | RaiseStmt n lst =>  let vlist := calculateExprList (fst etaE) lst in
                              match vlist with
                              | (Error s) => Error s
                              | Result (vlist') => 
                              let event :=  getEventByName n eventList in 
                                         match event with
                                         | None => Error eventNotDeclaredErr
                                         | Some ev => Result (fst etaE, (app ({|eventDefinition := ev; eventArguments := vlist';  |}::nil) (snd etaE)))
                                         end
                             end              
  | Seq a1 a2 => let r1 := execAction  etaE a1 eventList in
                 match r1 with
                 | Result re1 => execAction  re1 a2 eventList
                 | Error r => Error r                           
                 end
  | _ => Error typeErr                   
  end.

 *)


Print event_definition.

Fixpoint execAction  (etaE: value_env*(list raisedEvent)) (a:action) (eventList: list event_definition) : ErrorOrResult :=
  match a with
  | StateUpdate (LExp (AIdent s)) ex => let er := evalMonad (fst etaE) ex in
                                 match er with
                                 | Result v =>
                                     match updateValueEnvInv (AIdent s) v (fst etaE) with
                                     | Some ven => Result (ven,snd etaE)                                                                | None => Error typeErr
                                                                                                                                        end
                                 | Error r => Error r
                                 end
  | RaiseStmt n lst =>  let vlist := calculateExprList (fst etaE) lst in
                              match vlist with
                              | (Error s) => Error s
                              | Result (vlist') => 
                              let event :=  getEventByName n eventList in 
                                         match event with
                                         | None => Error eventNotDeclaredErr
                                         | Some ev => if parameterMatchFunc vlist' (eventParams  ev) then
                                                        Result (fst etaE, (app ({|eventDefinition := ev; eventArguments := vlist';  |}::nil) (snd etaE)))
                                                      else Error typeErr
                                         end
                             end              
  | Seq a1 a2 => let r1 := execAction  etaE a1 eventList in
                 match r1 with
                 | Result re1 => execAction  re1 a2 eventList
                 | Error r => Error r                           
                 end
  | Skip => Result etaE                 
  | _ => Error typeErr                   
  end.

Lemma updateVEDomNotChanged: forall env a v  env',
    Some env' = updateValueEnvInv (AIdent a) v env ->
    dom env' = dom env.
Proof.
  intro env;induction env.
  - intros. simpl in H. inversion H;auto.
  - intros.
    simpl in H.
    destruct a;destruct p.
    destruct (atom_eq_dec (AIdent a0) a).
    destruct (typeValMatch t v);inversion H.
    auto.
    remember (updateValueEnvInv (AIdent a0) v env).
    destruct o;inversion H.
    simpl;f_equal.
    apply IHenv with (a:=a0) (v:=v);auto.
Qed.

Lemma execActionUniqList : forall a ven lre  eventList ven' lre',   
    Result (ven', lre') = execAction (ven,lre) a eventList ->
    dom ven = dom ven'.
Proof. intro a;induction a.
       - intros;simpl in H. inversion H;auto.  
       - intros. simpl in H.
         destruct l;inversion H.  destruct a;inversion H.
         destruct (evalMonad ven e);inversion H.
         remember (updateValueEnvInv (AIdent s) v ven).
         destruct o;inversion H.
         symmetry;apply updateVEDomNotChanged  with (a:=s) (v:=v);auto. 
       -
         intros.
         simpl in H.
         destruct (calculateExprList ven exprs);inversion H.
         destruct (getEventByName ident eventList);inversion H1.
         destruct (parameterMatchFunc v (eventParams e));inversion H2. 
         auto.
       - intros.
         simpl in H.
         remember (execAction (ven, lre) a1 eventList).
         destruct e;inversion H.
         destruct v.
         apply IHa1 in Heqe.
         apply IHa2 in H. rewrite H in Heqe;auto. 
Qed.          



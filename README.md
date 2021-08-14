# Correct-by-construction implementation of runtime monitors using stepwise refinement

This repository contains the complete code base for the paper "Correct-by-construction implementation of runtime monitors using stepwise refinement".

## Dependencies:
  * Coq 8.7.0 (compiled with OCaml 4.04.0)
  * GHC 8.0.1
  * To step through the examples:  GNU Emacs 24.3+, Proof General 4.4+

## Get the codebase from the repositories:

First, clone repo :

*git clone https://gitlab.precise.seas.upenn.edu/tengz/smedl-fiat-code.git*

Inside  smedl-fiat-code directory, clone the fiat repo:

*git clone https://gitlab.precise.seas.upenn.edu/tengz/fiat.git*

(If you cannot clone them, please download the repo from this page and also the fiat repo, unzip them and put the fiat folder into the folder of this repo.)


## Directory structure: 

The Coq definitions and proofs and code for case study are in the directory SMEDL_mon.

smedlDef:  Coq definitions for SMEDL AST and semantic rules and auxiliary lemmas for proving well-formedness.

wellFormScenario.v and wellForm.v:  Proofs for well-formedness and termination

Refinement.v: ADT definition and refinement proofs

deter_definition.v and determinism.v : Definitions and proofs for determinism 

aux_monitor.v and well_decision_proc.v: auxiliary tactics and decision procedures to prove well-formedness of a monitor

Extract.v: Extraction of Coq definition into Haskell code

Monitor_oni.v: Definition and well-formedness proof for parseCC

casestudy/HString.hs: Haskell library required for monitor code

casestuy/oni_adaptor.hs: glue code for monitor parseCC

## Compile and run:

* compile Fiat: Go into directory fiat,  `git clean -dfx` and `make`

* compile definition and proofs: Go into directory SMEDL_mon, `make`

* compile and run the case study: copy the generate Haskell file *smedlmon.hs* in SMEDL_mon into the directory casestudy;  In directory casestudy, `make` and `./test`. 



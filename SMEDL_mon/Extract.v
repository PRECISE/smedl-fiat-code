

Require Import

        Monitor_oni
  Coq.Strings.Ascii
  Coq.Strings.String.

(** Eq *)

(** Eq *)

Extraction Implicit eq_rect   [ x y ].
Extraction Implicit eq_rect_r [ x y ].
Extraction Implicit eq_rec    [ x y ].
Extraction Implicit eq_rec_r  [ x y ].

Extract Inlined Constant eq_rect   => "".
Extract Inlined Constant eq_rect_r => "".
Extract Inlined Constant eq_rec    => "".
Extract Inlined Constant eq_rec_r  => "".

(** Ord *)

Extract Inductive comparison =>
  "Prelude.Ordering" ["Prelude.EQ" "Prelude.LT" "Prelude.GT"].

(** Int *)

Extract Inductive Datatypes.nat => "Prelude.Int"
  ["(0 :: Prelude.Int)" "HString.nsucc"]
  "(\fO fS n -> if n Prelude.<= 0 then fO () else fS (Prelude.pred n))".

Extract Inlined Constant EqNat.beq_nat         => "((Prelude.==) :: Prelude.Int -> Prelude.Int -> Prelude.Bool)".
Extract Inlined Constant Compare_dec.le_lt_dec => "((Prelude.<=) :: Prelude.Int -> Prelude.Int -> Prelude.Bool)".
Extract Inlined Constant Compare_dec.le_gt_dec => "(Prelude.>)".
Extract Inlined Constant Compare_dec.le_dec    => "((Prelude.<=) :: Prelude.Int -> Prelude.Int -> Prelude.Bool)".
Extract Inlined Constant Compare_dec.lt_dec    => "(Prelude.<)".
Extract Inlined Constant Compare_dec.leb       => "((Prelude.<=) :: Prelude.Int -> Prelude.Int -> Prelude.Bool)".

Extract Inlined Constant plus  => "(Prelude.+)".
Extract Inlined Constant minus => "(Prelude.-)".
Extract Inlined Constant mult  => "(Prelude.* )".
Extract Inlined Constant pred  => "(Prelude.pred :: Prelude.Int -> Prelude.Int)".
Extract Inlined Constant min   => "Prelude.min".
Extract Inlined Constant max   => "(Prelude.max :: Prelude.Int -> Prelude.Int -> Prelude.Int)".

(** positive, N, Z, Q *)

Require Import Coq.NArith.NArith.
Require Import Coq.ZArith.ZArith.
Require Import Coq.QArith.QArith.

Extract Inductive positive => "Prelude.Int" [
  "(\x -> 2 Prelude.* x Prelude.+ 1)"
  "(\x -> 2 Prelude.* x)"
  "1" ]
  "(\fI fO fH n -> if n Prelude.== 1 then fH () else
                   if Prelude.odd n then fI (n `Prelude.div` 2)
                                    else fO (n `Prelude.div` 2))".

Extract Inductive N => "Prelude.Int" [ "0" "(\x -> x)" ]
  "(\fO fP n -> if n Prelude.== 0 then fO () else fP n)".

Extract Inlined Constant N.to_nat    => "Prelude.id".
Extract Inlined Constant N.of_nat    => "Prelude.id".
Extract Inlined Constant N.add       => "(Prelude.+)".
Extract Inlined Constant N.sub       => "(Prelude.-)".
Extract Inlined Constant N.mul       => "(Prelude.*)".
Extract Inlined Constant N.max       => "Prelude.max".
Extract Inlined Constant N.min       => "Prelude.min".
Extract Inlined Constant N.ltb       => "(Prelude.<)".
Extract Inlined Constant N.leb       => "(Prelude.<=)".

Extract Inductive Z => "Prelude.Int" [ "0" "(\x -> x)" "Prelude.negate" ]
  "(\fO fP fN n -> if n Prelude.== 0 then fO () else
                   if n Prelude.> 0 then fP n else fN (Prelude.negate n))".

Extract Inlined Constant Z.of_nat    => "Prelude.id".
Extract Inlined Constant Z.to_nat    => "Prelude.id".

Extract Inlined Constant Z.add       => "(Prelude.+)".
Extract Inlined Constant Z.sub       => "(Prelude.-)".
Extract Inlined Constant Z.mul       => "(Prelude.*)".
Extract Inlined Constant Z.max       => "Prelude.max".
Extract Inlined Constant Z.min       => "Prelude.min".
Extract Inlined Constant Z_ge_lt_dec => "(Prelude.>=)".
Extract Inlined Constant Z_gt_le_dec => "(Prelude.>)".

Extract Constant Z.div =>
  "(\n m -> if m Prelude.== 0 then 0 else Prelude.div n m)".
Extract Constant Z.modulo =>
  "(\n m -> if m Prelude.== 0 then 0 else Prelude.mod n m)".

Extract Inductive Q => "(GHC.Real.Ratio Prelude.Int)" [ "(GHC.Real.:%)" ].

Extract Inlined Constant Qplus  => "(Prelude.+)".
Extract Inlined Constant Qminus => "(Prelude.-)".
Extract Inlined Constant Qmult  => "(Prelude.*)".

Extract Constant Qdiv =>
  "(\n m -> if m Prelude.== 0 then 0 else n Prelude./ m)".

(** Bool *)

Extract Inductive bool    => "Prelude.Bool" ["Prelude.True" "Prelude.False"].
Extract Inductive sumbool => "Prelude.Bool" ["Prelude.True" "Prelude.False"].

(* Extract Inlined Constant Equality.bool_beq => "((Prelude.==) :: Prelude.Bool -> Prelude.Bool -> Prelude.Bool)". *)
Extract Inlined Constant Bool.bool_dec     => "((Prelude.==) :: Prelude.Bool -> Prelude.Bool -> Prelude.Bool)".

Extract Inlined Constant Sumbool.sumbool_of_bool => "".

Extract Inlined Constant negb => "Prelude.not".
Extract Inlined Constant orb  => "(Prelude.||)".
Extract Inlined Constant andb => "(Prelude.&&)".

(** Maybe *)

Extract Inductive option => "Prelude.Maybe" ["Prelude.Just" "Prelude.Nothing"].
Extract Inductive sumor  => "Prelude.Maybe" ["Prelude.Just" "Prelude.Nothing"].

(** Either *)

Extract Inductive sum => "Prelude.Either" ["Prelude.Left" "Prelude.Right"].

(** List *)

Extract Inductive list => "[]" ["[]" "(:)"].

Extract Inlined Constant app             => "(Prelude.++)".
Extract Inlined Constant List.map        => "Prelude.map".
Extract         Constant List.fold_left  => "\f l z -> Data.List.foldl f z l".
Extract Inlined Constant List.fold_right => "Data.List.foldr".
Extract Inlined Constant List.find       => "Data.List.find".
Extract Inlined Constant List.length     =>
  "(Data.List.length :: [a] -> Prelude.Int)".

(** Tuple *)

Extract Inductive prod => "(,)" ["(,)"].
Extract Inductive sigT => "(,)" ["(,)"].

Extract Inlined Constant fst    => "Prelude.fst".
Extract Inlined Constant snd    => "Prelude.snd".
Extract Inlined Constant projT1 => "Prelude.fst".
Extract Inlined Constant projT2 => "Prelude.snd".

Extract Inlined Constant proj1_sig => "".

(** Unit *)

Extract Inductive unit => "()" ["()"].

(** Vector *)

Require Import Coq.Vectors.Vector.

Extract Inductive Vector.t => "[]" [ "[]" "(\x _n xs -> x:xs)" ]
  "(\fnil fcons xs -> case xs of [] -> fnil (); x:xs -> fcons x 0 xs)".
Extract Inductive VectorDef.t => "[]" [ "[]" "(\x _n xs -> x:xs)" ]
  "(\fnil fcons xs -> case xs of [] -> fnil (); x:xs -> fcons x 0 xs)".

(* Extract Inductive Word.word => "[Prelude.Bool]" [ "[]" "(\x _n xs -> x:xs)" ] *)
(*   "(\fnil fcons xs -> case xs of [] -> fnil (); x:xs -> fcons x 0 xs)". *)

(* Extract Inlined Constant Word.whd => "(Prelude.const Prelude.head)". *)
(* Extract Inlined Constant Word.wtl => "(Prelude.const Prelude.tail)". *)

(**************************************************************************)
(* The following extraction constants are only valid for Coq 8.4, and     *)
(* are needed there to workaround an incorrect use of [unsafeCoerce],     *)
(* which results in a core dump when attempting to evaluate a certain     *)
(* thunk.                                                                 *)
(*                                                                        *)
(* These are not only not needed in 8.5, but will actually cause          *)
(* compilation errors there, because the [unsafeCoerce] statements are    *)
(* no longer used, resulting in type mismatches with the [()] type that   *)
(* is used here.                                                          *)
(**************************************************************************)
(* COQ 8.4 START HERE                                                     *)
(**************************************************************************)

(*
Extract Constant ilist.ilist "a" "b" => "()".

Extract Constant ilist.icons    =>
  "\_ _ _ x xs -> unsafeCoerce (x:unsafeCoerce xs)".
Extract Constant ilist.inil     => "unsafeCoerce []".
Extract Constant ilist.ilist_hd =>
  "\_ _ -> unsafeCoerce Prelude.. Prelude.head Prelude.. unsafeCoerce".
Extract Constant ilist.ilist_tl =>
  "\_ _ -> unsafeCoerce Prelude.. Prelude.tail Prelude.. unsafeCoerce".

Extract Constant ilist.ith =>
  "Data.Function.fix Prelude.$ \f _ _ v n ->
  case unsafeCoerce v of
    Build_prim_prod x xs ->
      case n of F1 _    -> x
                FS _ n' -> f __ __ xs n'".

Extract Constant ilist2.ilist2 "a" "b" => "()".

Extract Constant ilist2.icons2    =>
  "\_ _ _ x xs -> unsafeCoerce (x:unsafeCoerce xs)".
Extract Constant ilist2.inil2     => "unsafeCoerce []".
Extract Constant ilist2.ilist2_hd =>
  "\_ _ -> unsafeCoerce Prelude.. Prelude.head Prelude.. unsafeCoerce".
Extract Constant ilist2.ilist2_tl =>
  "\_ _ -> unsafeCoerce Prelude.. Prelude.tail Prelude.. unsafeCoerce".

Extract Constant ilist2.ith2 =>
  "Data.Function.fix Prelude.$ \f _ _ v n ->
  case n of F1 _    -> (unsafeCoerce v) Prelude.!! 0
            FS _ n' -> case unsafeCoerce v of
                         []     -> __
                         (x:xs) -> f __ __ (unsafeCoerce xs) n'".
*)

(**************************************************************************)
(* COQ 8.4 END HERE                                                       *)
(**************************************************************************)

(** String *)

Extract Inductive string => "Prelude.String" ["[]" "(:)"].
Extract Inductive ascii  => "Prelude.Char" ["HString.asciiToChar"]
  "HString.foldChar".

Extract Inlined Constant ascii_of_nat => "Data.Char.chr".
Extract Inlined Constant nat_of_ascii => "Data.Char.ord".
Extract Inlined Constant ascii_of_N   => "Data.Char.chr".
Extract Inlined Constant ascii_of_pos => "Data.Char.chr".

(** Fiat *)

Extract Constant Common.If_Then_Else     => "\c t e -> if c then t else e".
Extract Constant Common.If_Opt_Then_Else => "\c t e -> Data.Maybe.maybe e t c".

(* Extract Inlined Constant Operations.List.take => "Data.List.take". *)
(* Extract Inlined Constant Operations.List.drop => "Data.List.drop". *)

(* Extract Inlined Constant Decidable_witness => "". *)

(*
Extract Constant Implementation.ProgramImpl =>
  "GHC.Base.error ""programImpl not defined""".
Extract Constant Implementation.program =>
  "GHC.Base.error ""program not defined""".
Extract Constant Implementation.MI.MonitorImpl =>
  "GHC.Base.error ""monitorImpl not defined""".
Extract Constant Implementation.MI.monitor =>
  "GHC.Base.error ""monitor not defined""".
Extract Constant Implementation.runSPV' =>
  "GHC.Base.error ""runSPV' not defined""".
Extract Constant SPV_parser.Parser.ComputationalSplitter' =>
  "GHC.Base.error ""ComputationalSplitter' not defined""".
Extract Constant FinishingLemma.finish_Sharpening_SplitterADT =>
  "GHC.Base.error ""finish_Sharpening_SplitterADT not defined""".
Extract Constant FinishingLemma.finish_Sharpening_SplitterADT' =>
  "GHC.Base.error ""finish_Sharpening_SplitterADT' not defined""".
*)

(** Final extraction *)

Extraction Language Haskell.

Unset Extraction KeepSingleton.
Set Extraction AutoInline.
Set Extraction Optimize.
Set Extraction AccessOpaque.

(*extract coq function into haskell file*)
Extraction "smedlmon.hs" mon_oni_new parseCC_processEvent createRaised ilist.prim_prod.


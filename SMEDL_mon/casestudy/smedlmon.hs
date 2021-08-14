{-# OPTIONS_GHC -cpp -XMagicHash #-}
{- For Hugs, use the option -F"cpp -P -traditional" -}

module Smedlmon where

import qualified Prelude
import qualified HString
import qualified Data.Char
import qualified Data.List
import qualified Data.Ratio
import qualified GHC.Real
import qualified Data.Function
import qualified Data.Maybe
import Debug.Trace


#ifdef __GLASGOW_HASKELL__
import qualified GHC.Base
import qualified GHC.Prim
#else
-- HUGS
import qualified IOExts
#endif

#ifdef __GLASGOW_HASKELL__
--unsafeCoerce :: a -> b
unsafeCoerce = GHC.Base.unsafeCoerce#
#else
-- HUGS
--unsafeCoerce :: a -> b
unsafeCoerce = IOExts.unsafeCoerce
#endif

#ifdef __GLASGOW_HASKELL__
type Any = GHC.Prim.Any
#else
-- HUGS
type Any = ()
#endif

__ :: any
__ = Prelude.error "Logical or arity value used"

false_rect :: a1
false_rect =
  Prelude.error "absurd case"

bool_rect :: a1 -> a1 -> Prelude.Bool -> a1
bool_rect f f0 b =
  case b of {
   Prelude.True -> f;
   Prelude.False -> f0}

bool_rec :: a1 -> a1 -> Prelude.Bool -> a1
bool_rec =
  bool_rect

nat_rect :: a1 -> (Prelude.Int -> a1 -> a1) -> Prelude.Int -> a1
nat_rect f f0 n =
  (\fO fS n -> if n Prelude.<= 0 then fO () else fS (Prelude.pred n))
    (\_ -> f)
    (\n0 -> f0 n0 (nat_rect f f0 n0))
    n

nat_rec :: a1 -> (Prelude.Int -> a1 -> a1) -> Prelude.Int -> a1
nat_rec =
  nat_rect

sum_rect :: (a1 -> a3) -> (a2 -> a3) -> (Prelude.Either a1 a2) -> a3
sum_rect f f0 s =
  case s of {
   Prelude.Left x -> f x;
   Prelude.Right x -> f0 x}

sum_rec :: (a1 -> a3) -> (a2 -> a3) -> (Prelude.Either a1 a2) -> a3
sum_rec =
  sum_rect

list_rect :: a2 -> (a1 -> ([] a1) -> a2 -> a2) -> ([] a1) -> a2
list_rect f f0 l =
  case l of {
   [] -> f;
   (:) y l0 -> f0 y l0 (list_rect f f0 l0)}

list_rec :: a2 -> (a1 -> ([] a1) -> a2 -> a2) -> ([] a1) -> a2
list_rec =
  list_rect

compOpp :: Prelude.Ordering -> Prelude.Ordering
compOpp r =
  case r of {
   Prelude.EQ -> Prelude.EQ;
   Prelude.LT -> Prelude.GT;
   Prelude.GT -> Prelude.LT}

type Sig a = a
  -- singleton inductive, whose constructor was exist
  
sumbool_rect :: (() -> a1) -> (() -> a1) -> Prelude.Bool -> a1
sumbool_rect f f0 s =
  case s of {
   Prelude.True -> f __;
   Prelude.False -> f0 __}

sumbool_rec :: (() -> a1) -> (() -> a1) -> Prelude.Bool -> a1
sumbool_rec =
  sumbool_rect

eqb :: Prelude.Bool -> Prelude.Bool -> Prelude.Bool
eqb b1 b2 =
  case b1 of {
   Prelude.True -> b2;
   Prelude.False ->
    case b2 of {
     Prelude.True -> Prelude.False;
     Prelude.False -> Prelude.True}}

filter :: (a1 -> Prelude.Bool) -> ([] a1) -> [] a1
filter f l =
  case l of {
   [] -> [];
   (:) x l0 ->
    case f x of {
     Prelude.True -> (:) x (filter f l0);
     Prelude.False -> filter f l0}}

positive_rect :: (Prelude.Int -> a1 -> a1) -> (Prelude.Int -> a1 -> a1) -> a1
                 -> Prelude.Int -> a1
positive_rect f f0 f1 p =
  (\fI fO fH n -> if n Prelude.== 1 then fH () else
                   if Prelude.odd n then fI (n `Prelude.div` 2)
                                    else fO (n `Prelude.div` 2))
    (\p0 -> f p0 (positive_rect f f0 f1 p0))
    (\p0 -> f0 p0 (positive_rect f f0 f1 p0))
    (\_ -> f1)
    p

positive_rec :: (Prelude.Int -> a1 -> a1) -> (Prelude.Int -> a1 -> a1) -> a1
                -> Prelude.Int -> a1
positive_rec =
  positive_rect

z_rect :: a1 -> (Prelude.Int -> a1) -> (Prelude.Int -> a1) -> Prelude.Int ->
          a1
z_rect f f0 f1 z =
  (\fO fP fN n -> if n Prelude.== 0 then fO () else
                   if n Prelude.> 0 then fP n else fN (Prelude.negate n))
    (\_ -> f)
    (\x -> f0 x)
    (\x -> f1 x)
    z

z_rec :: a1 -> (Prelude.Int -> a1) -> (Prelude.Int -> a1) -> Prelude.Int ->
         a1
z_rec =
  z_rect

succ :: Prelude.Int -> Prelude.Int
succ x =
  (\fI fO fH n -> if n Prelude.== 1 then fH () else
                   if Prelude.odd n then fI (n `Prelude.div` 2)
                                    else fO (n `Prelude.div` 2))
    (\p -> (\x -> 2 Prelude.* x) (succ p))
    (\p -> (\x -> 2 Prelude.* x Prelude.+ 1) p)
    (\_ -> (\x -> 2 Prelude.* x) 1)
    x

add :: Prelude.Int -> Prelude.Int -> Prelude.Int
add x y =
  (\fI fO fH n -> if n Prelude.== 1 then fH () else
                   if Prelude.odd n then fI (n `Prelude.div` 2)
                                    else fO (n `Prelude.div` 2))
    (\p ->
    (\fI fO fH n -> if n Prelude.== 1 then fH () else
                   if Prelude.odd n then fI (n `Prelude.div` 2)
                                    else fO (n `Prelude.div` 2))
      (\q -> (\x -> 2 Prelude.* x) (add_carry p q))
      (\q -> (\x -> 2 Prelude.* x Prelude.+ 1) (add p q))
      (\_ -> (\x -> 2 Prelude.* x) (succ p))
      y)
    (\p ->
    (\fI fO fH n -> if n Prelude.== 1 then fH () else
                   if Prelude.odd n then fI (n `Prelude.div` 2)
                                    else fO (n `Prelude.div` 2))
      (\q -> (\x -> 2 Prelude.* x Prelude.+ 1) (add p q))
      (\q -> (\x -> 2 Prelude.* x) (add p q))
      (\_ -> (\x -> 2 Prelude.* x Prelude.+ 1) p)
      y)
    (\_ ->
    (\fI fO fH n -> if n Prelude.== 1 then fH () else
                   if Prelude.odd n then fI (n `Prelude.div` 2)
                                    else fO (n `Prelude.div` 2))
      (\q -> (\x -> 2 Prelude.* x) (succ q))
      (\q -> (\x -> 2 Prelude.* x Prelude.+ 1) q)
      (\_ -> (\x -> 2 Prelude.* x) 1)
      y)
    x

add_carry :: Prelude.Int -> Prelude.Int -> Prelude.Int
add_carry x y =
  (\fI fO fH n -> if n Prelude.== 1 then fH () else
                   if Prelude.odd n then fI (n `Prelude.div` 2)
                                    else fO (n `Prelude.div` 2))
    (\p ->
    (\fI fO fH n -> if n Prelude.== 1 then fH () else
                   if Prelude.odd n then fI (n `Prelude.div` 2)
                                    else fO (n `Prelude.div` 2))
      (\q -> (\x -> 2 Prelude.* x Prelude.+ 1) (add_carry p q))
      (\q -> (\x -> 2 Prelude.* x) (add_carry p q))
      (\_ -> (\x -> 2 Prelude.* x Prelude.+ 1) (succ p))
      y)
    (\p ->
    (\fI fO fH n -> if n Prelude.== 1 then fH () else
                   if Prelude.odd n then fI (n `Prelude.div` 2)
                                    else fO (n `Prelude.div` 2))
      (\q -> (\x -> 2 Prelude.* x) (add_carry p q))
      (\q -> (\x -> 2 Prelude.* x Prelude.+ 1) (add p q))
      (\_ -> (\x -> 2 Prelude.* x) (succ p))
      y)
    (\_ ->
    (\fI fO fH n -> if n Prelude.== 1 then fH () else
                   if Prelude.odd n then fI (n `Prelude.div` 2)
                                    else fO (n `Prelude.div` 2))
      (\q -> (\x -> 2 Prelude.* x Prelude.+ 1) (succ q))
      (\q -> (\x -> 2 Prelude.* x) (succ q))
      (\_ -> (\x -> 2 Prelude.* x Prelude.+ 1) 1)
      y)
    x

pred_double :: Prelude.Int -> Prelude.Int
pred_double x =
  (\fI fO fH n -> if n Prelude.== 1 then fH () else
                   if Prelude.odd n then fI (n `Prelude.div` 2)
                                    else fO (n `Prelude.div` 2))
    (\p -> (\x -> 2 Prelude.* x Prelude.+ 1) ((\x -> 2 Prelude.* x) p))
    (\p -> (\x -> 2 Prelude.* x Prelude.+ 1) (pred_double p))
    (\_ -> 1)
    x

mul :: Prelude.Int -> Prelude.Int -> Prelude.Int
mul x y =
  (\fI fO fH n -> if n Prelude.== 1 then fH () else
                   if Prelude.odd n then fI (n `Prelude.div` 2)
                                    else fO (n `Prelude.div` 2))
    (\p -> add y ((\x -> 2 Prelude.* x) (mul p y)))
    (\p -> (\x -> 2 Prelude.* x) (mul p y))
    (\_ -> y)
    x

compare_cont :: Prelude.Ordering -> Prelude.Int -> Prelude.Int ->
                Prelude.Ordering
compare_cont r x y =
  (\fI fO fH n -> if n Prelude.== 1 then fH () else
                   if Prelude.odd n then fI (n `Prelude.div` 2)
                                    else fO (n `Prelude.div` 2))
    (\p ->
    (\fI fO fH n -> if n Prelude.== 1 then fH () else
                   if Prelude.odd n then fI (n `Prelude.div` 2)
                                    else fO (n `Prelude.div` 2))
      (\q -> compare_cont r p q)
      (\q -> compare_cont Prelude.GT p q)
      (\_ -> Prelude.GT)
      y)
    (\p ->
    (\fI fO fH n -> if n Prelude.== 1 then fH () else
                   if Prelude.odd n then fI (n `Prelude.div` 2)
                                    else fO (n `Prelude.div` 2))
      (\q -> compare_cont Prelude.LT p q)
      (\q -> compare_cont r p q)
      (\_ -> Prelude.GT)
      y)
    (\_ ->
    (\fI fO fH n -> if n Prelude.== 1 then fH () else
                   if Prelude.odd n then fI (n `Prelude.div` 2)
                                    else fO (n `Prelude.div` 2))
      (\_ -> Prelude.LT)
      (\_ -> Prelude.LT)
      (\_ -> r)
      y)
    x

compare :: Prelude.Int -> Prelude.Int -> Prelude.Ordering
compare =
  compare_cont Prelude.EQ

eqb0 :: Prelude.Int -> Prelude.Int -> Prelude.Bool
eqb0 p q =
  (\fI fO fH n -> if n Prelude.== 1 then fH () else
                   if Prelude.odd n then fI (n `Prelude.div` 2)
                                    else fO (n `Prelude.div` 2))
    (\p0 ->
    (\fI fO fH n -> if n Prelude.== 1 then fH () else
                   if Prelude.odd n then fI (n `Prelude.div` 2)
                                    else fO (n `Prelude.div` 2))
      (\q0 -> eqb0 p0 q0)
      (\_ -> Prelude.False)
      (\_ -> Prelude.False)
      q)
    (\p0 ->
    (\fI fO fH n -> if n Prelude.== 1 then fH () else
                   if Prelude.odd n then fI (n `Prelude.div` 2)
                                    else fO (n `Prelude.div` 2))
      (\_ -> Prelude.False)
      (\q0 -> eqb0 p0 q0)
      (\_ -> Prelude.False)
      q)
    (\_ ->
    (\fI fO fH n -> if n Prelude.== 1 then fH () else
                   if Prelude.odd n then fI (n `Prelude.div` 2)
                                    else fO (n `Prelude.div` 2))
      (\_ -> Prelude.False)
      (\_ -> Prelude.False)
      (\_ -> Prelude.True)
      q)
    p

double :: Prelude.Int -> Prelude.Int
double x =
  (\fO fP fN n -> if n Prelude.== 0 then fO () else
                   if n Prelude.> 0 then fP n else fN (Prelude.negate n))
    (\_ -> 0)
    (\p -> (\x -> x) ((\x -> 2 Prelude.* x) p))
    (\p -> Prelude.negate ((\x -> 2 Prelude.* x) p))
    x

succ_double :: Prelude.Int -> Prelude.Int
succ_double x =
  (\fO fP fN n -> if n Prelude.== 0 then fO () else
                   if n Prelude.> 0 then fP n else fN (Prelude.negate n))
    (\_ -> (\x -> x) 1)
    (\p -> (\x -> x) ((\x -> 2 Prelude.* x Prelude.+ 1) p))
    (\p -> Prelude.negate (pred_double p))
    x

pred_double0 :: Prelude.Int -> Prelude.Int
pred_double0 x =
  (\fO fP fN n -> if n Prelude.== 0 then fO () else
                   if n Prelude.> 0 then fP n else fN (Prelude.negate n))
    (\_ -> Prelude.negate 1)
    (\p -> (\x -> x) (pred_double p))
    (\p -> Prelude.negate ((\x -> 2 Prelude.* x Prelude.+ 1) p))
    x

pos_sub :: Prelude.Int -> Prelude.Int -> Prelude.Int
pos_sub x y =
  (\fI fO fH n -> if n Prelude.== 1 then fH () else
                   if Prelude.odd n then fI (n `Prelude.div` 2)
                                    else fO (n `Prelude.div` 2))
    (\p ->
    (\fI fO fH n -> if n Prelude.== 1 then fH () else
                   if Prelude.odd n then fI (n `Prelude.div` 2)
                                    else fO (n `Prelude.div` 2))
      (\q -> double (pos_sub p q))
      (\q -> succ_double (pos_sub p q))
      (\_ -> (\x -> x) ((\x -> 2 Prelude.* x) p))
      y)
    (\p ->
    (\fI fO fH n -> if n Prelude.== 1 then fH () else
                   if Prelude.odd n then fI (n `Prelude.div` 2)
                                    else fO (n `Prelude.div` 2))
      (\q -> pred_double0 (pos_sub p q))
      (\q -> double (pos_sub p q))
      (\_ -> (\x -> x) (pred_double p))
      y)
    (\_ ->
    (\fI fO fH n -> if n Prelude.== 1 then fH () else
                   if Prelude.odd n then fI (n `Prelude.div` 2)
                                    else fO (n `Prelude.div` 2))
      (\q -> Prelude.negate ((\x -> 2 Prelude.* x) q))
      (\q -> Prelude.negate (pred_double q))
      (\_ -> 0)
      y)
    x

opp :: Prelude.Int -> Prelude.Int
opp x =
  (\fO fP fN n -> if n Prelude.== 0 then fO () else
                   if n Prelude.> 0 then fP n else fN (Prelude.negate n))
    (\_ -> 0)
    (\x0 -> Prelude.negate x0)
    (\x0 -> (\x -> x) x0)
    x

compare0 :: Prelude.Int -> Prelude.Int -> Prelude.Ordering
compare0 x y =
  (\fO fP fN n -> if n Prelude.== 0 then fO () else
                   if n Prelude.> 0 then fP n else fN (Prelude.negate n))
    (\_ ->
    (\fO fP fN n -> if n Prelude.== 0 then fO () else
                   if n Prelude.> 0 then fP n else fN (Prelude.negate n))
      (\_ -> Prelude.EQ)
      (\_ -> Prelude.LT)
      (\_ -> Prelude.GT)
      y)
    (\x' ->
    (\fO fP fN n -> if n Prelude.== 0 then fO () else
                   if n Prelude.> 0 then fP n else fN (Prelude.negate n))
      (\_ -> Prelude.GT)
      (\y' -> compare x' y')
      (\_ -> Prelude.GT)
      y)
    (\x' ->
    (\fO fP fN n -> if n Prelude.== 0 then fO () else
                   if n Prelude.> 0 then fP n else fN (Prelude.negate n))
      (\_ -> Prelude.LT)
      (\_ -> Prelude.LT)
      (\y' -> compOpp (compare x' y'))
      y)
    x

leb :: Prelude.Int -> Prelude.Int -> Prelude.Bool
leb x y =
  case compare0 x y of {
   Prelude.GT -> Prelude.False;
   _ -> Prelude.True}

ltb :: Prelude.Int -> Prelude.Int -> Prelude.Bool
ltb x y =
  case compare0 x y of {
   Prelude.LT -> Prelude.True;
   _ -> Prelude.False}

eqb1 :: Prelude.Int -> Prelude.Int -> Prelude.Bool
eqb1 x y =
  (\fO fP fN n -> if n Prelude.== 0 then fO () else
                   if n Prelude.> 0 then fP n else fN (Prelude.negate n))
    (\_ ->
    (\fO fP fN n -> if n Prelude.== 0 then fO () else
                   if n Prelude.> 0 then fP n else fN (Prelude.negate n))
      (\_ -> Prelude.True)
      (\_ -> Prelude.False)
      (\_ -> Prelude.False)
      y)
    (\p ->
    (\fO fP fN n -> if n Prelude.== 0 then fO () else
                   if n Prelude.> 0 then fP n else fN (Prelude.negate n))
      (\_ -> Prelude.False)
      (\q -> eqb0 p q)
      (\_ -> Prelude.False)
      y)
    (\p ->
    (\fO fP fN n -> if n Prelude.== 0 then fO () else
                   if n Prelude.> 0 then fP n else fN (Prelude.negate n))
      (\_ -> Prelude.False)
      (\_ -> Prelude.False)
      (\q -> eqb0 p q)
      y)
    x

pos_div_eucl :: Prelude.Int -> Prelude.Int -> (,) Prelude.Int Prelude.Int
pos_div_eucl a b =
  (\fI fO fH n -> if n Prelude.== 1 then fH () else
                   if Prelude.odd n then fI (n `Prelude.div` 2)
                                    else fO (n `Prelude.div` 2))
    (\a' ->
    case pos_div_eucl a' b of {
     (,) q r ->
      let {
       r' = (Prelude.+) ((Prelude.*) ((\x -> x) ((\x -> 2 Prelude.* x) 1)) r)
              ((\x -> x) 1)}
      in
      case ltb r' b of {
       Prelude.True -> (,)
        ((Prelude.*) ((\x -> x) ((\x -> 2 Prelude.* x) 1)) q) r';
       Prelude.False -> (,)
        ((Prelude.+) ((Prelude.*) ((\x -> x) ((\x -> 2 Prelude.* x) 1)) q)
          ((\x -> x) 1)) ((Prelude.-) r' b)}})
    (\a' ->
    case pos_div_eucl a' b of {
     (,) q r ->
      let {r' = (Prelude.*) ((\x -> x) ((\x -> 2 Prelude.* x) 1)) r} in
      case ltb r' b of {
       Prelude.True -> (,)
        ((Prelude.*) ((\x -> x) ((\x -> 2 Prelude.* x) 1)) q) r';
       Prelude.False -> (,)
        ((Prelude.+) ((Prelude.*) ((\x -> x) ((\x -> 2 Prelude.* x) 1)) q)
          ((\x -> x) 1)) ((Prelude.-) r' b)}})
    (\_ ->
    case leb ((\x -> x) ((\x -> 2 Prelude.* x) 1)) b of {
     Prelude.True -> (,) 0 ((\x -> x) 1);
     Prelude.False -> (,) ((\x -> x) 1) 0})
    a

div_eucl :: Prelude.Int -> Prelude.Int -> (,) Prelude.Int Prelude.Int
div_eucl a b =
  (\fO fP fN n -> if n Prelude.== 0 then fO () else
                   if n Prelude.> 0 then fP n else fN (Prelude.negate n))
    (\_ -> (,) 0 0)
    (\a' ->
    (\fO fP fN n -> if n Prelude.== 0 then fO () else
                   if n Prelude.> 0 then fP n else fN (Prelude.negate n))
      (\_ -> (,) 0 0)
      (\_ -> pos_div_eucl a' b)
      (\b' ->
      case pos_div_eucl a' ((\x -> x) b') of {
       (,) q r ->
        (\fO fP fN n -> if n Prelude.== 0 then fO () else
                   if n Prelude.> 0 then fP n else fN (Prelude.negate n))
          (\_ -> (,) (opp q) 0)
          (\_ -> (,) (opp ((Prelude.+) q ((\x -> x) 1)))
          ((Prelude.+) b r))
          (\_ -> (,) (opp ((Prelude.+) q ((\x -> x) 1))) ((Prelude.+) b r))
          r})
      b)
    (\a' ->
    (\fO fP fN n -> if n Prelude.== 0 then fO () else
                   if n Prelude.> 0 then fP n else fN (Prelude.negate n))
      (\_ -> (,) 0 0)
      (\_ ->
      case pos_div_eucl a' b of {
       (,) q r ->
        (\fO fP fN n -> if n Prelude.== 0 then fO () else
                   if n Prelude.> 0 then fP n else fN (Prelude.negate n))
          (\_ -> (,) (opp q) 0)
          (\_ -> (,) (opp ((Prelude.+) q ((\x -> x) 1)))
          ((Prelude.-) b r))
          (\_ -> (,) (opp ((Prelude.+) q ((\x -> x) 1))) ((Prelude.-) b r))
          r})
      (\b' ->
      case pos_div_eucl a' ((\x -> x) b') of {
       (,) q r -> (,) q (opp r)})
      b)
    a

div :: Prelude.Int -> Prelude.Int -> Prelude.Int
div = (\n m -> if m Prelude.== 0 then 0 else Prelude.div n m)

modulo :: Prelude.Int -> Prelude.Int -> Prelude.Int
modulo = (\n m -> if m Prelude.== 0 then 0 else Prelude.mod n m)

zeq_bool :: Prelude.Int -> Prelude.Int -> Prelude.Bool
zeq_bool x y =
  case compare0 x y of {
   Prelude.EQ -> Prelude.True;
   _ -> Prelude.False}

ascii_rect :: (Prelude.Bool -> Prelude.Bool -> Prelude.Bool -> Prelude.Bool
              -> Prelude.Bool -> Prelude.Bool -> Prelude.Bool -> Prelude.Bool
              -> a1) -> Prelude.Char -> a1
ascii_rect f a =
  HString.foldChar
    (\x x0 x1 x2 x3 x4 x5 x6 -> f x x0 x1 x2 x3 x4 x5 x6)
    a

ascii_rec :: (Prelude.Bool -> Prelude.Bool -> Prelude.Bool -> Prelude.Bool ->
             Prelude.Bool -> Prelude.Bool -> Prelude.Bool -> Prelude.Bool ->
             a1) -> Prelude.Char -> a1
ascii_rec =
  ascii_rect

ascii_dec :: Prelude.Char -> Prelude.Char -> Prelude.Bool
ascii_dec a b =
  ascii_rec (\b0 b1 b2 b3 b4 b5 b6 b7 x ->
    HString.foldChar
      (\b8 b9 b10 b11 b12 b13 b14 b15 ->
      sumbool_rec (\_ ->
        sumbool_rec (\_ ->
          sumbool_rec (\_ ->
            sumbool_rec (\_ ->
              sumbool_rec (\_ ->
                sumbool_rec (\_ ->
                  sumbool_rec (\_ ->
                    sumbool_rec (\_ -> Prelude.True) (\_ -> Prelude.False)
                      (((Prelude.==) :: Prelude.Bool -> Prelude.Bool -> Prelude.Bool)
                        b7 b15)) (\_ -> Prelude.False)
                    (((Prelude.==) :: Prelude.Bool -> Prelude.Bool -> Prelude.Bool)
                      b6 b14)) (\_ -> Prelude.False)
                  (((Prelude.==) :: Prelude.Bool -> Prelude.Bool -> Prelude.Bool)
                    b5 b13)) (\_ -> Prelude.False)
                (((Prelude.==) :: Prelude.Bool -> Prelude.Bool -> Prelude.Bool)
                  b4 b12)) (\_ -> Prelude.False)
              (((Prelude.==) :: Prelude.Bool -> Prelude.Bool -> Prelude.Bool)
                b3 b11)) (\_ -> Prelude.False)
            (((Prelude.==) :: Prelude.Bool -> Prelude.Bool -> Prelude.Bool)
              b2 b10)) (\_ -> Prelude.False)
          (((Prelude.==) :: Prelude.Bool -> Prelude.Bool -> Prelude.Bool) b1
            b9)) (\_ -> Prelude.False)
        (((Prelude.==) :: Prelude.Bool -> Prelude.Bool -> Prelude.Bool) b0
          b8))
      x) a b

string_rect :: a1 -> (Prelude.Char -> Prelude.String -> a1 -> a1) ->
               Prelude.String -> a1
string_rect f f0 s =
  case s of {
   [] -> f;
   (:) a s0 -> f0 a s0 (string_rect f f0 s0)}

string_rec :: a1 -> (Prelude.Char -> Prelude.String -> a1 -> a1) ->
              Prelude.String -> a1
string_rec =
  string_rect

string_dec :: Prelude.String -> Prelude.String -> Prelude.Bool
string_dec s1 s2 =
  string_rec (\x ->
    case x of {
     [] -> Prelude.True;
     (:) _ _ -> Prelude.False}) (\a _ h x ->
    case x of {
     [] -> Prelude.False;
     (:) a0 s0 ->
      sumbool_rec (\_ ->
        sumbool_rec (\_ -> Prelude.True) (\_ -> Prelude.False) (h s0)) (\_ ->
        Prelude.False) (ascii_dec a a0)}) s1 s2

data T =
   F1 Prelude.Int
 | FS Prelude.Int T

caseS :: (a1 -> Prelude.Int -> ([] a1) -> a2) -> Prelude.Int -> ([] a1) -> a2
caseS h _ v =
  (\fnil fcons xs -> case xs of [] -> fnil (); x:xs -> fcons x 0 xs)
    (\_ -> __)
    (\h0 n t -> h h0 n t)
    v

nth :: Prelude.Int -> ([] a1) -> T -> a1
nth _ v' p =
  case p of {
   F1 n -> caseS (\h _ _ -> h) n v';
   FS n p' -> caseS (\_ -> nth) n v' p'}

map :: (a1 -> a2) -> Prelude.Int -> ([] a1) -> [] a2
map f _ v =
  (\fnil fcons xs -> case xs of [] -> fnil (); x:xs -> fcons x 0 xs)
    (\_ -> [])
    (\a n v' -> (\x _n xs -> x:xs) (f a) n (map f n v'))
    v

qnum :: (GHC.Real.Ratio Prelude.Int) -> Prelude.Int
qnum q =
  case q of {
   (GHC.Real.:%) qnum0 _ -> qnum0}

qden :: (GHC.Real.Ratio Prelude.Int) -> Prelude.Int
qden q =
  case q of {
   (GHC.Real.:%) _ qden0 -> qden0}

qeq_bool :: (GHC.Real.Ratio Prelude.Int) -> (GHC.Real.Ratio Prelude.Int) ->
            Prelude.Bool
qeq_bool x y =
  zeq_bool ((Prelude.*) (qnum x) ((\x -> x) (qden y)))
    ((Prelude.*) (qnum y) ((\x -> x) (qden x)))

qle_bool :: (GHC.Real.Ratio Prelude.Int) -> (GHC.Real.Ratio Prelude.Int) ->
            Prelude.Bool
qle_bool x y =
  leb ((Prelude.*) (qnum x) ((\x -> x) (qden y)))
    ((Prelude.*) (qnum y) ((\x -> x) (qden x)))

qdiv :: (GHC.Real.Ratio Prelude.Int) -> (GHC.Real.Ratio Prelude.Int) ->
        (GHC.Real.Ratio Prelude.Int)
qdiv = (\n m -> if m Prelude.== 0 then 0 else n Prelude./ m)

typeErr :: Prelude.String
typeErr =
  (:) 'T' ((:) 'y' ((:) 'p' ((:) 'e' ((:) ' ' ((:) 'e' ((:) 'r' ((:) 'r' ((:)
    'o' ((:) 'r' [])))))))))

eventNotDeclaredErr :: Prelude.String
eventNotDeclaredErr =
  (:) 'e' ((:) 'v' ((:) 'e' ((:) 'n' ((:) 't' ((:) ' ' ((:) 'n' ((:) 'o' ((:)
    't' ((:) ' ' ((:) 'd' ((:) 'e' ((:) 'c' ((:) 'l' ((:) 'a' ((:) 'r' ((:)
    'e' ((:) 'd' [])))))))))))))))))

data ErrorOrResult t =
   Result t
 | Error Prelude.String

internal_bool_beq :: Prelude.Bool -> Prelude.Bool -> Prelude.Bool
internal_bool_beq x y =
  case x of {
   Prelude.True -> y;
   Prelude.False ->
    case y of {
     Prelude.True -> Prelude.False;
     Prelude.False -> Prelude.True}}

internal_ascii_beq :: Prelude.Char -> Prelude.Char -> Prelude.Bool
internal_ascii_beq x y =
  HString.foldChar
    (\x0 x1 x2 x3 x4 x5 x6 x7 ->
    HString.foldChar
      (\x8 x9 x10 x11 x12 x13 x14 x15 ->
      (Prelude.&&) (internal_bool_beq x0 x8)
        ((Prelude.&&) (internal_bool_beq x1 x9)
          ((Prelude.&&) (internal_bool_beq x2 x10)
            ((Prelude.&&) (internal_bool_beq x3 x11)
              ((Prelude.&&) (internal_bool_beq x4 x12)
                ((Prelude.&&) (internal_bool_beq x5 x13)
                  ((Prelude.&&) (internal_bool_beq x6 x14)
                    (internal_bool_beq x7 x15))))))))
      y)
    x

internal_string_beq :: Prelude.String -> Prelude.String -> Prelude.Bool
internal_string_beq x y =
  case x of {
   [] -> case y of {
          [] -> Prelude.True;
          (:) _ _ -> Prelude.False};
   (:) x0 x1 ->
    case y of {
     [] -> Prelude.False;
     (:) x2 x3 ->
      (Prelude.&&) (internal_ascii_beq x0 x2) (internal_string_beq x1 x3)}}

data Typ =
   Int
 | Float
 | Str
 | Bool
 | Pointer
 | Opaque
 | Thread

typ_rect :: a1 -> a1 -> a1 -> a1 -> a1 -> a1 -> a1 -> Typ -> a1
typ_rect f f0 f1 f2 f3 f4 f5 t =
  case t of {
   Int -> f;
   Float -> f0;
   Str -> f1;
   Bool -> f2;
   Pointer -> f3;
   Opaque -> f4;
   Thread -> f5}

typ_rec :: a1 -> a1 -> a1 -> a1 -> a1 -> a1 -> a1 -> Typ -> a1
typ_rec =
  typ_rect

internal_typ_beq :: Typ -> Typ -> Prelude.Bool
internal_typ_beq x y =
  case x of {
   Int -> case y of {
           Int -> Prelude.True;
           _ -> Prelude.False};
   Float -> case y of {
             Float -> Prelude.True;
             _ -> Prelude.False};
   Str -> case y of {
           Str -> Prelude.True;
           _ -> Prelude.False};
   Bool -> case y of {
            Bool -> Prelude.True;
            _ -> Prelude.False};
   Pointer -> case y of {
               Pointer -> Prelude.True;
               _ -> Prelude.False};
   Opaque -> case y of {
              Opaque -> Prelude.True;
              _ -> Prelude.False};
   Thread -> case y of {
              Thread -> Prelude.True;
              _ -> Prelude.False}}

typ_eq_dec :: Typ -> Typ -> Prelude.Bool
typ_eq_dec x y =
  let {b = internal_typ_beq x y} in
  case b of {
   Prelude.True -> Prelude.True;
   Prelude.False -> Prelude.False}

data Atom =
   AInt Prelude.Int
 | AFloat (GHC.Real.Ratio Prelude.Int)
 | AIdent Prelude.String
 | ABool Prelude.Bool
 | ANull
 | AString Prelude.String

atom_rect :: (Prelude.Int -> a1) -> ((GHC.Real.Ratio Prelude.Int) -> a1) ->
             (Prelude.String -> a1) -> (Prelude.Bool -> a1) -> a1 ->
             (Prelude.String -> a1) -> Atom -> a1
atom_rect f f0 f1 f2 f3 f4 a =
  case a of {
   AInt x -> f x;
   AFloat x -> f0 x;
   AIdent x -> f1 x;
   ABool x -> f2 x;
   ANull -> f3;
   AString x -> f4 x}

atom_rec :: (Prelude.Int -> a1) -> ((GHC.Real.Ratio Prelude.Int) -> a1) ->
            (Prelude.String -> a1) -> (Prelude.Bool -> a1) -> a1 ->
            (Prelude.String -> a1) -> Atom -> a1
atom_rec =
  atom_rect

internal_positive_beq :: Prelude.Int -> Prelude.Int -> Prelude.Bool
internal_positive_beq x y =
  (\fI fO fH n -> if n Prelude.== 1 then fH () else
                   if Prelude.odd n then fI (n `Prelude.div` 2)
                                    else fO (n `Prelude.div` 2))
    (\x0 ->
    (\fI fO fH n -> if n Prelude.== 1 then fH () else
                   if Prelude.odd n then fI (n `Prelude.div` 2)
                                    else fO (n `Prelude.div` 2))
      (\x1 -> internal_positive_beq x0 x1)
      (\_ -> Prelude.False)
      (\_ -> Prelude.False)
      y)
    (\x0 ->
    (\fI fO fH n -> if n Prelude.== 1 then fH () else
                   if Prelude.odd n then fI (n `Prelude.div` 2)
                                    else fO (n `Prelude.div` 2))
      (\_ -> Prelude.False)
      (\x1 -> internal_positive_beq x0 x1)
      (\_ -> Prelude.False)
      y)
    (\_ ->
    (\fI fO fH n -> if n Prelude.== 1 then fH () else
                   if Prelude.odd n then fI (n `Prelude.div` 2)
                                    else fO (n `Prelude.div` 2))
      (\_ -> Prelude.False)
      (\_ -> Prelude.False)
      (\_ -> Prelude.True)
      y)
    x

internal_Z_beq :: Prelude.Int -> Prelude.Int -> Prelude.Bool
internal_Z_beq x y =
  (\fO fP fN n -> if n Prelude.== 0 then fO () else
                   if n Prelude.> 0 then fP n else fN (Prelude.negate n))
    (\_ ->
    (\fO fP fN n -> if n Prelude.== 0 then fO () else
                   if n Prelude.> 0 then fP n else fN (Prelude.negate n))
      (\_ -> Prelude.True)
      (\_ -> Prelude.False)
      (\_ -> Prelude.False)
      y)
    (\x0 ->
    (\fO fP fN n -> if n Prelude.== 0 then fO () else
                   if n Prelude.> 0 then fP n else fN (Prelude.negate n))
      (\_ -> Prelude.False)
      (\x1 -> internal_positive_beq x0 x1)
      (\_ -> Prelude.False)
      y)
    (\x0 ->
    (\fO fP fN n -> if n Prelude.== 0 then fO () else
                   if n Prelude.> 0 then fP n else fN (Prelude.negate n))
      (\_ -> Prelude.False)
      (\_ -> Prelude.False)
      (\x1 -> internal_positive_beq x0 x1)
      y)
    x

internal_Q_beq :: (GHC.Real.Ratio Prelude.Int) ->
                  (GHC.Real.Ratio Prelude.Int) -> Prelude.Bool
internal_Q_beq x y =
  case x of {
   (GHC.Real.:%) qnum0 qden0 ->
    case y of {
     (GHC.Real.:%) qnum1 qden1 ->
      (Prelude.&&) (internal_Z_beq qnum0 qnum1)
        (internal_positive_beq qden0 qden1)}}

internal_atom_beq :: Atom -> Atom -> Prelude.Bool
internal_atom_beq x y =
  case x of {
   AInt x0 ->
    case y of {
     AInt x1 -> internal_Z_beq x0 x1;
     _ -> Prelude.False};
   AFloat x0 ->
    case y of {
     AFloat x1 -> internal_Q_beq x0 x1;
     _ -> Prelude.False};
   AIdent x0 ->
    case y of {
     AIdent x1 -> internal_string_beq x0 x1;
     _ -> Prelude.False};
   ABool x0 ->
    case y of {
     ABool x1 -> internal_bool_beq x0 x1;
     _ -> Prelude.False};
   ANull -> case y of {
             ANull -> Prelude.True;
             _ -> Prelude.False};
   AString x0 ->
    case y of {
     AString x1 -> internal_string_beq x0 x1;
     _ -> Prelude.False}}

atom_eq_dec :: Atom -> Atom -> Prelude.Bool
atom_eq_dec x y =
  let {b = internal_atom_beq x y} in
  case b of {
   Prelude.True -> Prelude.True;
   Prelude.False -> Prelude.False}

type Typ_env = [] ((,) Atom Typ)

type Range_typ =
  Prelude.Either
  (Prelude.Either
  (Prelude.Either (Prelude.Either Prelude.Int (GHC.Real.Ratio Prelude.Int))
  Prelude.String) Prelude.Bool) Prelude.Int

range_typ_dec :: Range_typ -> Range_typ -> Prelude.Bool
range_typ_dec re re' =
  sum_rec (\a x ->
    case x of {
     Prelude.Left s ->
      sumbool_rec (\_ -> Prelude.True) (\_ -> Prelude.False)
        (sum_rec (\a0 x0 ->
          case x0 of {
           Prelude.Left s0 ->
            sumbool_rec (\_ -> Prelude.True) (\_ -> Prelude.False)
              (sum_rec (\a1 x1 ->
                case x1 of {
                 Prelude.Left s1 ->
                  sumbool_rec (\_ -> Prelude.True) (\_ -> Prelude.False)
                    (sum_rec (\a2 x2 ->
                      case x2 of {
                       Prelude.Left z ->
                        sumbool_rec (\_ -> Prelude.True) (\_ ->
                          Prelude.False)
                          (z_rec (\x3 ->
                            (\fO fP fN n -> if n Prelude.== 0 then fO () else
                   if n Prelude.> 0 then fP n else fN (Prelude.negate n))
                              (\_ -> Prelude.True)
                              (\_ -> Prelude.False)
                              (\_ -> Prelude.False)
                              x3) (\p x3 ->
                            (\fO fP fN n -> if n Prelude.== 0 then fO () else
                   if n Prelude.> 0 then fP n else fN (Prelude.negate n))
                              (\_ -> Prelude.False)
                              (\p0 ->
                              sumbool_rec (\_ -> Prelude.True) (\_ ->
                                Prelude.False)
                                (positive_rec (\_ h x4 ->
                                  (\fI fO fH n -> if n Prelude.== 1 then fH () else
                   if Prelude.odd n then fI (n `Prelude.div` 2)
                                    else fO (n `Prelude.div` 2))
                                    (\p2 ->
                                    sumbool_rec (\_ -> Prelude.True) (\_ ->
                                      Prelude.False) (h p2))
                                    (\_ -> Prelude.False)
                                    (\_ -> Prelude.False)
                                    x4) (\_ h x4 ->
                                  (\fI fO fH n -> if n Prelude.== 1 then fH () else
                   if Prelude.odd n then fI (n `Prelude.div` 2)
                                    else fO (n `Prelude.div` 2))
                                    (\_ -> Prelude.False)
                                    (\p2 ->
                                    sumbool_rec (\_ -> Prelude.True) (\_ ->
                                      Prelude.False) (h p2))
                                    (\_ -> Prelude.False)
                                    x4) (\x4 ->
                                  (\fI fO fH n -> if n Prelude.== 1 then fH () else
                   if Prelude.odd n then fI (n `Prelude.div` 2)
                                    else fO (n `Prelude.div` 2))
                                    (\_ -> Prelude.False)
                                    (\_ -> Prelude.False)
                                    (\_ -> Prelude.True)
                                    x4) p p0))
                              (\_ -> Prelude.False)
                              x3) (\p x3 ->
                            (\fO fP fN n -> if n Prelude.== 0 then fO () else
                   if n Prelude.> 0 then fP n else fN (Prelude.negate n))
                              (\_ -> Prelude.False)
                              (\_ -> Prelude.False)
                              (\p0 ->
                              sumbool_rec (\_ -> Prelude.True) (\_ ->
                                Prelude.False)
                                (positive_rec (\_ h x4 ->
                                  (\fI fO fH n -> if n Prelude.== 1 then fH () else
                   if Prelude.odd n then fI (n `Prelude.div` 2)
                                    else fO (n `Prelude.div` 2))
                                    (\p2 ->
                                    sumbool_rec (\_ -> Prelude.True) (\_ ->
                                      Prelude.False) (h p2))
                                    (\_ -> Prelude.False)
                                    (\_ -> Prelude.False)
                                    x4) (\_ h x4 ->
                                  (\fI fO fH n -> if n Prelude.== 1 then fH () else
                   if Prelude.odd n then fI (n `Prelude.div` 2)
                                    else fO (n `Prelude.div` 2))
                                    (\_ -> Prelude.False)
                                    (\p2 ->
                                    sumbool_rec (\_ -> Prelude.True) (\_ ->
                                      Prelude.False) (h p2))
                                    (\_ -> Prelude.False)
                                    x4) (\x4 ->
                                  (\fI fO fH n -> if n Prelude.== 1 then fH () else
                   if Prelude.odd n then fI (n `Prelude.div` 2)
                                    else fO (n `Prelude.div` 2))
                                    (\_ -> Prelude.False)
                                    (\_ -> Prelude.False)
                                    (\_ -> Prelude.True)
                                    x4) p p0))
                              x3) a2 z);
                       Prelude.Right _ -> Prelude.False}) (\b x2 ->
                      case x2 of {
                       Prelude.Left _ -> Prelude.False;
                       Prelude.Right q ->
                        sumbool_rec (\_ -> Prelude.True) (\_ ->
                          Prelude.False)
                          (case b of {
                            (GHC.Real.:%) qnum0 qden0 ->
                             case q of {
                              (GHC.Real.:%) qnum1 qden1 ->
                               sumbool_rec (\_ ->
                                 sumbool_rec (\_ -> Prelude.True) (\_ ->
                                   Prelude.False)
                                   (positive_rec (\_ h x3 ->
                                     (\fI fO fH n -> if n Prelude.== 1 then fH () else
                   if Prelude.odd n then fI (n `Prelude.div` 2)
                                    else fO (n `Prelude.div` 2))
                                       (\p0 ->
                                       sumbool_rec (\_ -> Prelude.True)
                                         (\_ -> Prelude.False) (h p0))
                                       (\_ -> Prelude.False)
                                       (\_ -> Prelude.False)
                                       x3) (\_ h x3 ->
                                     (\fI fO fH n -> if n Prelude.== 1 then fH () else
                   if Prelude.odd n then fI (n `Prelude.div` 2)
                                    else fO (n `Prelude.div` 2))
                                       (\_ -> Prelude.False)
                                       (\p0 ->
                                       sumbool_rec (\_ -> Prelude.True)
                                         (\_ -> Prelude.False) (h p0))
                                       (\_ -> Prelude.False)
                                       x3) (\x3 ->
                                     (\fI fO fH n -> if n Prelude.== 1 then fH () else
                   if Prelude.odd n then fI (n `Prelude.div` 2)
                                    else fO (n `Prelude.div` 2))
                                       (\_ -> Prelude.False)
                                       (\_ -> Prelude.False)
                                       (\_ -> Prelude.True)
                                       x3) qden0 qden1)) (\_ ->
                                 Prelude.False)
                                 (z_rec (\x3 ->
                                   (\fO fP fN n -> if n Prelude.== 0 then fO () else
                   if n Prelude.> 0 then fP n else fN (Prelude.negate n))
                                     (\_ -> Prelude.True)
                                     (\_ -> Prelude.False)
                                     (\_ -> Prelude.False)
                                     x3) (\p x3 ->
                                   (\fO fP fN n -> if n Prelude.== 0 then fO () else
                   if n Prelude.> 0 then fP n else fN (Prelude.negate n))
                                     (\_ -> Prelude.False)
                                     (\p0 ->
                                     sumbool_rec (\_ -> Prelude.True) (\_ ->
                                       Prelude.False)
                                       (positive_rec (\_ h x4 ->
                                         (\fI fO fH n -> if n Prelude.== 1 then fH () else
                   if Prelude.odd n then fI (n `Prelude.div` 2)
                                    else fO (n `Prelude.div` 2))
                                           (\p2 ->
                                           sumbool_rec (\_ -> Prelude.True)
                                             (\_ -> Prelude.False) (h p2))
                                           (\_ -> Prelude.False)
                                           (\_ -> Prelude.False)
                                           x4) (\_ h x4 ->
                                         (\fI fO fH n -> if n Prelude.== 1 then fH () else
                   if Prelude.odd n then fI (n `Prelude.div` 2)
                                    else fO (n `Prelude.div` 2))
                                           (\_ -> Prelude.False)
                                           (\p2 ->
                                           sumbool_rec (\_ -> Prelude.True)
                                             (\_ -> Prelude.False) (h p2))
                                           (\_ -> Prelude.False)
                                           x4) (\x4 ->
                                         (\fI fO fH n -> if n Prelude.== 1 then fH () else
                   if Prelude.odd n then fI (n `Prelude.div` 2)
                                    else fO (n `Prelude.div` 2))
                                           (\_ -> Prelude.False)
                                           (\_ -> Prelude.False)
                                           (\_ -> Prelude.True)
                                           x4) p p0))
                                     (\_ -> Prelude.False)
                                     x3) (\p x3 ->
                                   (\fO fP fN n -> if n Prelude.== 0 then fO () else
                   if n Prelude.> 0 then fP n else fN (Prelude.negate n))
                                     (\_ -> Prelude.False)
                                     (\_ -> Prelude.False)
                                     (\p0 ->
                                     sumbool_rec (\_ -> Prelude.True) (\_ ->
                                       Prelude.False)
                                       (positive_rec (\_ h x4 ->
                                         (\fI fO fH n -> if n Prelude.== 1 then fH () else
                   if Prelude.odd n then fI (n `Prelude.div` 2)
                                    else fO (n `Prelude.div` 2))
                                           (\p2 ->
                                           sumbool_rec (\_ -> Prelude.True)
                                             (\_ -> Prelude.False) (h p2))
                                           (\_ -> Prelude.False)
                                           (\_ -> Prelude.False)
                                           x4) (\_ h x4 ->
                                         (\fI fO fH n -> if n Prelude.== 1 then fH () else
                   if Prelude.odd n then fI (n `Prelude.div` 2)
                                    else fO (n `Prelude.div` 2))
                                           (\_ -> Prelude.False)
                                           (\p2 ->
                                           sumbool_rec (\_ -> Prelude.True)
                                             (\_ -> Prelude.False) (h p2))
                                           (\_ -> Prelude.False)
                                           x4) (\x4 ->
                                         (\fI fO fH n -> if n Prelude.== 1 then fH () else
                   if Prelude.odd n then fI (n `Prelude.div` 2)
                                    else fO (n `Prelude.div` 2))
                                           (\_ -> Prelude.False)
                                           (\_ -> Prelude.False)
                                           (\_ -> Prelude.True)
                                           x4) p p0))
                                     x3) qnum0 qnum1)}})}) a1 s1);
                 Prelude.Right _ -> Prelude.False}) (\b x1 ->
                case x1 of {
                 Prelude.Left _ -> Prelude.False;
                 Prelude.Right s1 ->
                  sumbool_rec (\_ -> Prelude.True) (\_ -> Prelude.False)
                    (string_rec (\x2 ->
                      case x2 of {
                       [] -> Prelude.True;
                       (:) _ _ -> Prelude.False}) (\a1 _ h x2 ->
                      case x2 of {
                       [] -> Prelude.False;
                       (:) a2 s3 ->
                        sumbool_rec (\_ ->
                          sumbool_rec (\_ -> Prelude.True) (\_ ->
                            Prelude.False) (h s3)) (\_ -> Prelude.False)
                          (ascii_rec (\b0 b1 b2 b3 b4 b5 b6 b7 x3 ->
                            HString.foldChar
                              (\b8 b9 b10 b11 b12 b13 b14 b15 ->
                              sumbool_rec (\_ ->
                                sumbool_rec (\_ ->
                                  sumbool_rec (\_ ->
                                    sumbool_rec (\_ ->
                                      sumbool_rec (\_ ->
                                        sumbool_rec (\_ ->
                                          sumbool_rec (\_ ->
                                            sumbool_rec (\_ -> Prelude.True)
                                              (\_ -> Prelude.False)
                                              (bool_rec (\x4 ->
                                                case x4 of {
                                                 Prelude.True -> Prelude.True;
                                                 Prelude.False ->
                                                  Prelude.False}) (\x4 ->
                                                case x4 of {
                                                 Prelude.True ->
                                                  Prelude.False;
                                                 Prelude.False ->
                                                  Prelude.True}) b7 b15))
                                            (\_ -> Prelude.False)
                                            (bool_rec (\x4 ->
                                              case x4 of {
                                               Prelude.True -> Prelude.True;
                                               Prelude.False -> Prelude.False})
                                              (\x4 ->
                                              case x4 of {
                                               Prelude.True -> Prelude.False;
                                               Prelude.False -> Prelude.True})
                                              b6 b14)) (\_ -> Prelude.False)
                                          (bool_rec (\x4 ->
                                            case x4 of {
                                             Prelude.True -> Prelude.True;
                                             Prelude.False -> Prelude.False})
                                            (\x4 ->
                                            case x4 of {
                                             Prelude.True -> Prelude.False;
                                             Prelude.False -> Prelude.True})
                                            b5 b13)) (\_ -> Prelude.False)
                                        (bool_rec (\x4 ->
                                          case x4 of {
                                           Prelude.True -> Prelude.True;
                                           Prelude.False -> Prelude.False})
                                          (\x4 ->
                                          case x4 of {
                                           Prelude.True -> Prelude.False;
                                           Prelude.False -> Prelude.True}) b4
                                          b12)) (\_ -> Prelude.False)
                                      (bool_rec (\x4 ->
                                        case x4 of {
                                         Prelude.True -> Prelude.True;
                                         Prelude.False -> Prelude.False})
                                        (\x4 ->
                                        case x4 of {
                                         Prelude.True -> Prelude.False;
                                         Prelude.False -> Prelude.True}) b3
                                        b11)) (\_ -> Prelude.False)
                                    (bool_rec (\x4 ->
                                      case x4 of {
                                       Prelude.True -> Prelude.True;
                                       Prelude.False -> Prelude.False})
                                      (\x4 ->
                                      case x4 of {
                                       Prelude.True -> Prelude.False;
                                       Prelude.False -> Prelude.True}) b2
                                      b10)) (\_ -> Prelude.False)
                                  (bool_rec (\x4 ->
                                    case x4 of {
                                     Prelude.True -> Prelude.True;
                                     Prelude.False -> Prelude.False}) (\x4 ->
                                    case x4 of {
                                     Prelude.True -> Prelude.False;
                                     Prelude.False -> Prelude.True}) b1 b9))
                                (\_ -> Prelude.False)
                                (bool_rec (\x4 ->
                                  case x4 of {
                                   Prelude.True -> Prelude.True;
                                   Prelude.False -> Prelude.False}) (\x4 ->
                                  case x4 of {
                                   Prelude.True -> Prelude.False;
                                   Prelude.False -> Prelude.True}) b0 b8))
                              x3) a1 a2)}) b s1)}) a0 s0);
           Prelude.Right _ -> Prelude.False}) (\b x0 ->
          case x0 of {
           Prelude.Left _ -> Prelude.False;
           Prelude.Right b0 ->
            sumbool_rec (\_ -> Prelude.True) (\_ -> Prelude.False)
              (bool_rec (\x1 ->
                case x1 of {
                 Prelude.True -> Prelude.True;
                 Prelude.False -> Prelude.False}) (\x1 ->
                case x1 of {
                 Prelude.True -> Prelude.False;
                 Prelude.False -> Prelude.True}) b b0)}) a s);
     Prelude.Right _ -> Prelude.False}) (\b x ->
    case x of {
     Prelude.Left _ -> Prelude.False;
     Prelude.Right n ->
      sumbool_rec (\_ -> Prelude.True) (\_ -> Prelude.False)
        (nat_rec (\x0 ->
          (\fO fS n -> if n Prelude.<= 0 then fO () else fS (Prelude.pred n))
            (\_ -> Prelude.True)
            (\_ -> Prelude.False)
            x0) (\_ h x0 ->
          (\fO fS n -> if n Prelude.<= 0 then fO () else fS (Prelude.pred n))
            (\_ -> Prelude.False)
            (\n1 ->
            sumbool_rec (\_ -> Prelude.True) (\_ -> Prelude.False) (h n1))
            x0) b n)}) re re'

type Value_env = [] ((,) Atom ((,) Typ Range_typ))

typeValMatch :: Typ -> Range_typ -> Prelude.Bool
typeValMatch t v =
  case t of {
   Int ->
    case v of {
     Prelude.Left s ->
      case s of {
       Prelude.Left s0 ->
        case s0 of {
         Prelude.Left s1 ->
          case s1 of {
           Prelude.Left _ -> Prelude.True;
           Prelude.Right _ -> Prelude.False};
         Prelude.Right _ -> Prelude.False};
       Prelude.Right _ -> Prelude.False};
     Prelude.Right _ -> Prelude.False};
   Float ->
    case v of {
     Prelude.Left s ->
      case s of {
       Prelude.Left s0 ->
        case s0 of {
         Prelude.Left s1 ->
          case s1 of {
           Prelude.Left _ -> Prelude.False;
           Prelude.Right _ -> Prelude.True};
         Prelude.Right _ -> Prelude.False};
       Prelude.Right _ -> Prelude.False};
     Prelude.Right _ -> Prelude.False};
   Str ->
    case v of {
     Prelude.Left s ->
      case s of {
       Prelude.Left s0 ->
        case s0 of {
         Prelude.Left _ -> Prelude.False;
         Prelude.Right _ -> Prelude.True};
       Prelude.Right _ -> Prelude.False};
     Prelude.Right _ -> Prelude.False};
   Bool ->
    case v of {
     Prelude.Left s ->
      case s of {
       Prelude.Left _ -> Prelude.False;
       Prelude.Right _ -> Prelude.True};
     Prelude.Right _ -> Prelude.False};
   _ ->
    case v of {
     Prelude.Left _ -> Prelude.False;
     Prelude.Right _ -> Prelude.True}}

dom :: ([] ((,) a1 a2)) -> [] a1
dom env =
  Prelude.map Prelude.fst env

string_dec_bool :: Prelude.String -> Prelude.String -> Prelude.Bool
string_dec_bool s1 s2 =
  case string_dec s1 s2 of {
   Prelude.True -> Prelude.True;
   Prelude.False -> Prelude.False}

inList :: (a1 -> a1 -> Prelude.Bool) -> a1 -> ([] a1) -> Prelude.Bool
inList decA x lst =
  case lst of {
   [] -> Prelude.False;
   (:) y lst' ->
    case decA x y of {
     Prelude.True -> Prelude.True;
     Prelude.False -> inList decA x lst'}}

updateValueEnvInv :: Atom -> Range_typ -> Value_env -> Prelude.Maybe
                     Value_env
updateValueEnvInv a v en =
  case a of {
   AIdent _ ->
    case en of {
     [] -> Prelude.Just [];
     (:) p en' ->
      case p of {
       (,) a' p0 ->
        case p0 of {
         (,) t' v' ->
          case atom_eq_dec a a' of {
           Prelude.True ->
            case typeValMatch t' v of {
             Prelude.True -> Prelude.Just ((:) ((,) a' ((,) t' v)) en');
             Prelude.False -> Prelude.Nothing};
           Prelude.False ->
            case updateValueEnvInv a v en' of {
             Prelude.Just ven' -> Prelude.Just ((:) ((,) a' ((,) t' v'))
              ven');
             Prelude.Nothing -> Prelude.Nothing}}}}};
   _ -> Prelude.Nothing}

createValueEnv :: ([] Prelude.String) -> ([] Typ) -> ([] Range_typ) ->
                  ErrorOrResult ([] ((,) Atom ((,) Typ Range_typ)))
createValueEnv nlst tlst vlst =
  case nlst of {
   [] ->
    case tlst of {
     [] ->
      case vlst of {
       [] -> Result [];
       (:) _ _ -> Error ((:) 'n' ((:) 'u' ((:) 'm' ((:) 'b' ((:) 'e' ((:) 'r'
        ((:) ' ' ((:) 'o' ((:) 'f' ((:) ' ' ((:) 'l' ((:) 'i' ((:) 's' ((:)
        't' ((:) ' ' ((:) 'n' ((:) 'o' ((:) 't' ((:) ' ' ((:) 'm' ((:) 'a'
        ((:) 't' ((:) 'c' ((:) 'h' ((:) 'e' ((:) 'd'
        []))))))))))))))))))))))))))};
     (:) _ _ -> Error ((:) 'n' ((:) 'u' ((:) 'm' ((:) 'b' ((:) 'e' ((:) 'r'
      ((:) ' ' ((:) 'o' ((:) 'f' ((:) ' ' ((:) 'l' ((:) 'i' ((:) 's' ((:) 't'
      ((:) ' ' ((:) 'n' ((:) 'o' ((:) 't' ((:) ' ' ((:) 'm' ((:) 'a' ((:) 't'
      ((:) 'c' ((:) 'h' ((:) 'e' ((:) 'd' []))))))))))))))))))))))))))};
   (:) s nlst' ->
    case tlst of {
     [] -> Error ((:) 'n' ((:) 'u' ((:) 'm' ((:) 'b' ((:) 'e' ((:) 'r' ((:)
      ' ' ((:) 'o' ((:) 'f' ((:) ' ' ((:) 'l' ((:) 'i' ((:) 's' ((:) 't' ((:)
      ' ' ((:) 'n' ((:) 'o' ((:) 't' ((:) ' ' ((:) 'm' ((:) 'a' ((:) 't' ((:)
      'c' ((:) 'h' ((:) 'e' ((:) 'd' []))))))))))))))))))))))))));
     (:) t tlst' ->
      case vlst of {
       [] -> Error ((:) 'n' ((:) 'u' ((:) 'm' ((:) 'b' ((:) 'e' ((:) 'r' ((:)
        ' ' ((:) 'o' ((:) 'f' ((:) ' ' ((:) 'l' ((:) 'i' ((:) 's' ((:) 't'
        ((:) ' ' ((:) 'n' ((:) 'o' ((:) 't' ((:) ' ' ((:) 'm' ((:) 'a' ((:)
        't' ((:) 'c' ((:) 'h' ((:) 'e' ((:) 'd' []))))))))))))))))))))))))));
       (:) v vlst' ->
        case createValueEnv nlst' tlst' vlst' of {
         Result ve -> Result ((:) ((,) (AIdent s) ((,) t v)) ve);
         Error s0 -> Error s0}}}}

getValue :: Atom -> Value_env -> Prelude.Maybe Range_typ
getValue a en =
  case a of {
   AIdent _ ->
    case en of {
     [] -> Prelude.Nothing;
     (:) p en' ->
      case p of {
       (,) a' p0 ->
        case p0 of {
         (,) _ v ->
          case atom_eq_dec a a' of {
           Prelude.True -> Prelude.Just v;
           Prelude.False -> getValue a en'}}}};
   _ -> Prelude.Nothing}

extendValEnv :: Value_env -> Value_env -> Value_env
extendValEnv =
  (Prelude.++)

data Expr =
   EOr Expr Expr
 | EAnd Expr Expr
 | EEq Expr Expr
 | ELt Expr Expr
 | ELe Expr Expr
 | EPlus Expr Expr
 | EMult Expr Expr
 | EDiv Expr Expr
 | EMod Expr Expr
 | ENot Expr
 | EAtom Atom

expr_rect :: (Expr -> a1 -> Expr -> a1 -> a1) -> (Expr -> a1 -> Expr -> a1 ->
             a1) -> (Expr -> a1 -> Expr -> a1 -> a1) -> (Expr -> a1 -> Expr
             -> a1 -> a1) -> (Expr -> a1 -> Expr -> a1 -> a1) -> (Expr -> a1
             -> Expr -> a1 -> a1) -> (Expr -> a1 -> Expr -> a1 -> a1) ->
             (Expr -> a1 -> Expr -> a1 -> a1) -> (Expr -> a1 -> Expr -> a1 ->
             a1) -> (Expr -> a1 -> a1) -> (Atom -> a1) -> Expr -> a1
expr_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 e =
  case e of {
   EOr e0 e1 ->
    f e0 (expr_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 e0) e1
      (expr_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 e1);
   EAnd e0 e1 ->
    f0 e0 (expr_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 e0) e1
      (expr_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 e1);
   EEq e0 e1 ->
    f1 e0 (expr_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 e0) e1
      (expr_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 e1);
   ELt e0 e1 ->
    f2 e0 (expr_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 e0) e1
      (expr_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 e1);
   ELe e0 e1 ->
    f3 e0 (expr_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 e0) e1
      (expr_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 e1);
   EPlus e0 e1 ->
    f4 e0 (expr_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 e0) e1
      (expr_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 e1);
   EMult e0 e1 ->
    f5 e0 (expr_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 e0) e1
      (expr_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 e1);
   EDiv e0 e1 ->
    f6 e0 (expr_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 e0) e1
      (expr_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 e1);
   EMod e0 e1 ->
    f7 e0 (expr_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 e0) e1
      (expr_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 e1);
   ENot e0 -> f8 e0 (expr_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 e0);
   EAtom a -> f9 a}

expr_rec :: (Expr -> a1 -> Expr -> a1 -> a1) -> (Expr -> a1 -> Expr -> a1 ->
            a1) -> (Expr -> a1 -> Expr -> a1 -> a1) -> (Expr -> a1 -> Expr ->
            a1 -> a1) -> (Expr -> a1 -> Expr -> a1 -> a1) -> (Expr -> a1 ->
            Expr -> a1 -> a1) -> (Expr -> a1 -> Expr -> a1 -> a1) -> (Expr ->
            a1 -> Expr -> a1 -> a1) -> (Expr -> a1 -> Expr -> a1 -> a1) ->
            (Expr -> a1 -> a1) -> (Atom -> a1) -> Expr -> a1
expr_rec =
  expr_rect

internal_expr_beq :: Expr -> Expr -> Prelude.Bool
internal_expr_beq x y =
  case x of {
   EOr x0 x1 ->
    case y of {
     EOr x2 x3 ->
      (Prelude.&&) (internal_expr_beq x0 x2) (internal_expr_beq x1 x3);
     _ -> Prelude.False};
   EAnd x0 x1 ->
    case y of {
     EAnd x2 x3 ->
      (Prelude.&&) (internal_expr_beq x0 x2) (internal_expr_beq x1 x3);
     _ -> Prelude.False};
   EEq x0 x1 ->
    case y of {
     EEq x2 x3 ->
      (Prelude.&&) (internal_expr_beq x0 x2) (internal_expr_beq x1 x3);
     _ -> Prelude.False};
   ELt x0 x1 ->
    case y of {
     ELt x2 x3 ->
      (Prelude.&&) (internal_expr_beq x0 x2) (internal_expr_beq x1 x3);
     _ -> Prelude.False};
   ELe x0 x1 ->
    case y of {
     ELe x2 x3 ->
      (Prelude.&&) (internal_expr_beq x0 x2) (internal_expr_beq x1 x3);
     _ -> Prelude.False};
   EPlus x0 x1 ->
    case y of {
     EPlus x2 x3 ->
      (Prelude.&&) (internal_expr_beq x0 x2) (internal_expr_beq x1 x3);
     _ -> Prelude.False};
   EMult x0 x1 ->
    case y of {
     EMult x2 x3 ->
      (Prelude.&&) (internal_expr_beq x0 x2) (internal_expr_beq x1 x3);
     _ -> Prelude.False};
   EDiv x0 x1 ->
    case y of {
     EDiv x2 x3 ->
      (Prelude.&&) (internal_expr_beq x0 x2) (internal_expr_beq x1 x3);
     _ -> Prelude.False};
   EMod x0 x1 ->
    case y of {
     EMod x2 x3 ->
      (Prelude.&&) (internal_expr_beq x0 x2) (internal_expr_beq x1 x3);
     _ -> Prelude.False};
   ENot x0 ->
    case y of {
     ENot x1 -> internal_expr_beq x0 x1;
     _ -> Prelude.False};
   EAtom x0 ->
    case y of {
     EAtom x1 -> internal_atom_beq x0 x1;
     _ -> Prelude.False}}

expr_eq_dec :: Expr -> Expr -> Prelude.Bool
expr_eq_dec x y =
  let {b = internal_expr_beq x y} in
  case b of {
   Prelude.True -> Prelude.True;
   Prelude.False -> Prelude.False}

data EventKind =
   Internal
 | Imported
 | Exported

eventKind_rect :: a1 -> a1 -> a1 -> EventKind -> a1
eventKind_rect f f0 f1 e =
  case e of {
   Internal -> f;
   Imported -> f0;
   Exported -> f1}

eventKind_rec :: a1 -> a1 -> a1 -> EventKind -> a1
eventKind_rec =
  eventKind_rect

eventKind_dec :: EventKind -> EventKind -> Prelude.Bool
eventKind_dec n m =
  eventKind_rec (\x ->
    case x of {
     Internal -> Prelude.True;
     _ -> Prelude.False}) (\x ->
    case x of {
     Imported -> Prelude.True;
     _ -> Prelude.False}) (\x ->
    case x of {
     Exported -> Prelude.True;
     _ -> Prelude.False}) n m

eventKind_beq :: EventKind -> EventKind -> Prelude.Bool
eventKind_beq n m =
  case n of {
   Internal -> case m of {
                Internal -> Prelude.True;
                _ -> Prelude.False};
   Imported -> case m of {
                Imported -> Prelude.True;
                _ -> Prelude.False};
   Exported -> case m of {
                Exported -> Prelude.True;
                _ -> Prelude.False}}

data Event_definition =
   Build_event_definition EventKind Prelude.String ([] Typ)

eventKind :: Event_definition -> EventKind
eventKind e =
  case e of {
   Build_event_definition eventKind0 _ _ -> eventKind0}

eventId :: Event_definition -> Prelude.String
eventId e =
  case e of {
   Build_event_definition _ eventId0 _ -> eventId0}

eventParams :: Event_definition -> [] Typ
eventParams e =
  case e of {
   Build_event_definition _ _ eventParams0 -> eventParams0}

event_definition_dec :: Event_definition -> Event_definition -> Prelude.Bool
event_definition_dec n m =
  case n of {
   Build_event_definition eventKind0 eventId0 eventParams0 ->
    case m of {
     Build_event_definition eventKind1 eventId1 eventParams1 ->
      sumbool_rec (\_ ->
        sumbool_rec (\_ ->
          sumbool_rec (\_ -> Prelude.True) (\_ -> Prelude.False)
            (list_rec (\x ->
              case x of {
               [] -> Prelude.True;
               (:) _ _ -> Prelude.False}) (\a1 _ h x ->
              case x of {
               [] -> Prelude.False;
               (:) t l0 ->
                sumbool_rec (\_ ->
                  sumbool_rec (\_ -> Prelude.True) (\_ -> Prelude.False)
                    (h l0)) (\_ -> Prelude.False)
                  (typ_rec (\x0 ->
                    case x0 of {
                     Int -> Prelude.True;
                     _ -> Prelude.False}) (\x0 ->
                    case x0 of {
                     Float -> Prelude.True;
                     _ -> Prelude.False}) (\x0 ->
                    case x0 of {
                     Str -> Prelude.True;
                     _ -> Prelude.False}) (\x0 ->
                    case x0 of {
                     Bool -> Prelude.True;
                     _ -> Prelude.False}) (\x0 ->
                    case x0 of {
                     Pointer -> Prelude.True;
                     _ -> Prelude.False}) (\x0 ->
                    case x0 of {
                     Opaque -> Prelude.True;
                     _ -> Prelude.False}) (\x0 ->
                    case x0 of {
                     Thread -> Prelude.True;
                     _ -> Prelude.False}) a1 t)}) eventParams0 eventParams1))
          (\_ -> Prelude.False)
          (string_rec (\x ->
            case x of {
             [] -> Prelude.True;
             (:) _ _ -> Prelude.False}) (\a0 _ h x ->
            case x of {
             [] -> Prelude.False;
             (:) a1 s0 ->
              sumbool_rec (\_ ->
                sumbool_rec (\_ -> Prelude.True) (\_ -> Prelude.False) (h s0))
                (\_ -> Prelude.False)
                (ascii_rec (\b b0 b1 b2 b3 b4 b5 b6 x0 ->
                  HString.foldChar
                    (\b7 b8 b9 b10 b11 b12 b13 b14 ->
                    sumbool_rec (\_ ->
                      sumbool_rec (\_ ->
                        sumbool_rec (\_ ->
                          sumbool_rec (\_ ->
                            sumbool_rec (\_ ->
                              sumbool_rec (\_ ->
                                sumbool_rec (\_ ->
                                  sumbool_rec (\_ -> Prelude.True) (\_ ->
                                    Prelude.False)
                                    (bool_rec (\x1 ->
                                      case x1 of {
                                       Prelude.True -> Prelude.True;
                                       Prelude.False -> Prelude.False})
                                      (\x1 ->
                                      case x1 of {
                                       Prelude.True -> Prelude.False;
                                       Prelude.False -> Prelude.True}) b6
                                      b14)) (\_ -> Prelude.False)
                                  (bool_rec (\x1 ->
                                    case x1 of {
                                     Prelude.True -> Prelude.True;
                                     Prelude.False -> Prelude.False}) (\x1 ->
                                    case x1 of {
                                     Prelude.True -> Prelude.False;
                                     Prelude.False -> Prelude.True}) b5 b13))
                                (\_ -> Prelude.False)
                                (bool_rec (\x1 ->
                                  case x1 of {
                                   Prelude.True -> Prelude.True;
                                   Prelude.False -> Prelude.False}) (\x1 ->
                                  case x1 of {
                                   Prelude.True -> Prelude.False;
                                   Prelude.False -> Prelude.True}) b4 b12))
                              (\_ -> Prelude.False)
                              (bool_rec (\x1 ->
                                case x1 of {
                                 Prelude.True -> Prelude.True;
                                 Prelude.False -> Prelude.False}) (\x1 ->
                                case x1 of {
                                 Prelude.True -> Prelude.False;
                                 Prelude.False -> Prelude.True}) b3 b11))
                            (\_ -> Prelude.False)
                            (bool_rec (\x1 ->
                              case x1 of {
                               Prelude.True -> Prelude.True;
                               Prelude.False -> Prelude.False}) (\x1 ->
                              case x1 of {
                               Prelude.True -> Prelude.False;
                               Prelude.False -> Prelude.True}) b2 b10))
                          (\_ -> Prelude.False)
                          (bool_rec (\x1 ->
                            case x1 of {
                             Prelude.True -> Prelude.True;
                             Prelude.False -> Prelude.False}) (\x1 ->
                            case x1 of {
                             Prelude.True -> Prelude.False;
                             Prelude.False -> Prelude.True}) b1 b9)) (\_ ->
                        Prelude.False)
                        (bool_rec (\x1 ->
                          case x1 of {
                           Prelude.True -> Prelude.True;
                           Prelude.False -> Prelude.False}) (\x1 ->
                          case x1 of {
                           Prelude.True -> Prelude.False;
                           Prelude.False -> Prelude.True}) b0 b8)) (\_ ->
                      Prelude.False)
                      (bool_rec (\x1 ->
                        case x1 of {
                         Prelude.True -> Prelude.True;
                         Prelude.False -> Prelude.False}) (\x1 ->
                        case x1 of {
                         Prelude.True -> Prelude.False;
                         Prelude.False -> Prelude.True}) b b7))
                    x0) a0 a1)}) eventId0 eventId1)) (\_ -> Prelude.False)
        (eventKind_rec (\x ->
          case x of {
           Internal -> Prelude.True;
           _ -> Prelude.False}) (\x ->
          case x of {
           Imported -> Prelude.True;
           _ -> Prelude.False}) (\x ->
          case x of {
           Exported -> Prelude.True;
           _ -> Prelude.False}) eventKind0 eventKind1)}}

type LValue = Atom
  -- singleton inductive, whose constructor was LExp
  
lValue_rect :: (Atom -> a1) -> LValue -> a1
lValue_rect f =
  f

lValue_rec :: (Atom -> a1) -> LValue -> a1
lValue_rec =
  lValue_rect

data Action =
   Skip
 | StateUpdate LValue Expr
 | RaiseStmt Prelude.String ([] Expr)
 | Seq Action Action

action_rect :: a1 -> (LValue -> Expr -> a1) -> (Prelude.String -> ([] 
               Expr) -> a1) -> (Action -> a1 -> Action -> a1 -> a1) -> Action
               -> a1
action_rect f f0 f1 f2 a =
  case a of {
   Skip -> f;
   StateUpdate l e -> f0 l e;
   RaiseStmt ident exprs -> f1 ident exprs;
   Seq a0 a1 ->
    f2 a0 (action_rect f f0 f1 f2 a0) a1 (action_rect f f0 f1 f2 a1)}

action_rec :: a1 -> (LValue -> Expr -> a1) -> (Prelude.String -> ([] 
              Expr) -> a1) -> (Action -> a1 -> Action -> a1 -> a1) -> Action
              -> a1
action_rec =
  action_rect

data Event_instance =
   Build_event_instance Event_definition ([] Prelude.String) Expr

eventArgs :: Event_instance -> [] Prelude.String
eventArgs e =
  case e of {
   Build_event_instance _ eventArgs0 _ -> eventArgs0}

eventWhenExpr :: Event_instance -> Expr
eventWhenExpr e =
  case e of {
   Build_event_instance _ _ eventWhenExpr0 -> eventWhenExpr0}

event_instance_dec :: Event_instance -> Event_instance -> Prelude.Bool
event_instance_dec n m =
  case n of {
   Build_event_instance event0 eventArgs0 eventWhenExpr0 ->
    case m of {
     Build_event_instance event1 eventArgs1 eventWhenExpr1 ->
      sumbool_rec (\_ ->
        sumbool_rec (\_ ->
          sumbool_rec (\_ -> Prelude.True) (\_ -> Prelude.False)
            (expr_rec (\_ h0 _ h1 x ->
              case x of {
               EOr e1 e2 ->
                sumbool_rec (\_ ->
                  sumbool_rec (\_ -> Prelude.True) (\_ -> Prelude.False)
                    (h1 e2)) (\_ -> Prelude.False) (h0 e1);
               _ -> Prelude.False}) (\_ h0 _ h1 x ->
              case x of {
               EAnd e1 e2 ->
                sumbool_rec (\_ ->
                  sumbool_rec (\_ -> Prelude.True) (\_ -> Prelude.False)
                    (h1 e2)) (\_ -> Prelude.False) (h0 e1);
               _ -> Prelude.False}) (\_ h0 _ h1 x ->
              case x of {
               EEq e1 e2 ->
                sumbool_rec (\_ ->
                  sumbool_rec (\_ -> Prelude.True) (\_ -> Prelude.False)
                    (h1 e2)) (\_ -> Prelude.False) (h0 e1);
               _ -> Prelude.False}) (\_ h0 _ h1 x ->
              case x of {
               ELt e1 e2 ->
                sumbool_rec (\_ ->
                  sumbool_rec (\_ -> Prelude.True) (\_ -> Prelude.False)
                    (h1 e2)) (\_ -> Prelude.False) (h0 e1);
               _ -> Prelude.False}) (\_ h0 _ h1 x ->
              case x of {
               ELe e1 e2 ->
                sumbool_rec (\_ ->
                  sumbool_rec (\_ -> Prelude.True) (\_ -> Prelude.False)
                    (h1 e2)) (\_ -> Prelude.False) (h0 e1);
               _ -> Prelude.False}) (\_ h0 _ h1 x ->
              case x of {
               EPlus e1 e2 ->
                sumbool_rec (\_ ->
                  sumbool_rec (\_ -> Prelude.True) (\_ -> Prelude.False)
                    (h1 e2)) (\_ -> Prelude.False) (h0 e1);
               _ -> Prelude.False}) (\_ h0 _ h1 x ->
              case x of {
               EMult e1 e2 ->
                sumbool_rec (\_ ->
                  sumbool_rec (\_ -> Prelude.True) (\_ -> Prelude.False)
                    (h1 e2)) (\_ -> Prelude.False) (h0 e1);
               _ -> Prelude.False}) (\_ h0 _ h1 x ->
              case x of {
               EDiv e1 e2 ->
                sumbool_rec (\_ ->
                  sumbool_rec (\_ -> Prelude.True) (\_ -> Prelude.False)
                    (h1 e2)) (\_ -> Prelude.False) (h0 e1);
               _ -> Prelude.False}) (\_ h0 _ h1 x ->
              case x of {
               EMod e1 e2 ->
                sumbool_rec (\_ ->
                  sumbool_rec (\_ -> Prelude.True) (\_ -> Prelude.False)
                    (h1 e2)) (\_ -> Prelude.False) (h0 e1);
               _ -> Prelude.False}) (\_ h0 x ->
              case x of {
               ENot e0 ->
                sumbool_rec (\_ -> Prelude.True) (\_ -> Prelude.False)
                  (h0 e0);
               _ -> Prelude.False}) (\a1 x ->
              case x of {
               EAtom a2 ->
                sumbool_rec (\_ -> Prelude.True) (\_ -> Prelude.False)
                  (atom_eq_dec a1 a2);
               _ -> Prelude.False}) eventWhenExpr0 eventWhenExpr1)) (\_ ->
          Prelude.False)
          (list_rec (\x ->
            case x of {
             [] -> Prelude.True;
             (:) _ _ -> Prelude.False}) (\a0 _ h0 x ->
            case x of {
             [] -> Prelude.False;
             (:) s l0 ->
              sumbool_rec (\_ ->
                sumbool_rec (\_ -> Prelude.True) (\_ -> Prelude.False)
                  (h0 l0)) (\_ -> Prelude.False)
                (string_rec (\x0 ->
                  case x0 of {
                   [] -> Prelude.True;
                   (:) _ _ -> Prelude.False}) (\a1 _ h1 x0 ->
                  case x0 of {
                   [] -> Prelude.False;
                   (:) a2 s1 ->
                    sumbool_rec (\_ ->
                      sumbool_rec (\_ -> Prelude.True) (\_ -> Prelude.False)
                        (h1 s1)) (\_ -> Prelude.False)
                      (ascii_rec (\b b0 b1 b2 b3 b4 b5 b6 x1 ->
                        HString.foldChar
                          (\b7 b8 b9 b10 b11 b12 b13 b14 ->
                          sumbool_rec (\_ ->
                            sumbool_rec (\_ ->
                              sumbool_rec (\_ ->
                                sumbool_rec (\_ ->
                                  sumbool_rec (\_ ->
                                    sumbool_rec (\_ ->
                                      sumbool_rec (\_ ->
                                        sumbool_rec (\_ -> Prelude.True)
                                          (\_ -> Prelude.False)
                                          (bool_rec (\x2 ->
                                            case x2 of {
                                             Prelude.True -> Prelude.True;
                                             Prelude.False -> Prelude.False})
                                            (\x2 ->
                                            case x2 of {
                                             Prelude.True -> Prelude.False;
                                             Prelude.False -> Prelude.True})
                                            b6 b14)) (\_ -> Prelude.False)
                                        (bool_rec (\x2 ->
                                          case x2 of {
                                           Prelude.True -> Prelude.True;
                                           Prelude.False -> Prelude.False})
                                          (\x2 ->
                                          case x2 of {
                                           Prelude.True -> Prelude.False;
                                           Prelude.False -> Prelude.True}) b5
                                          b13)) (\_ -> Prelude.False)
                                      (bool_rec (\x2 ->
                                        case x2 of {
                                         Prelude.True -> Prelude.True;
                                         Prelude.False -> Prelude.False})
                                        (\x2 ->
                                        case x2 of {
                                         Prelude.True -> Prelude.False;
                                         Prelude.False -> Prelude.True}) b4
                                        b12)) (\_ -> Prelude.False)
                                    (bool_rec (\x2 ->
                                      case x2 of {
                                       Prelude.True -> Prelude.True;
                                       Prelude.False -> Prelude.False})
                                      (\x2 ->
                                      case x2 of {
                                       Prelude.True -> Prelude.False;
                                       Prelude.False -> Prelude.True}) b3
                                      b11)) (\_ -> Prelude.False)
                                  (bool_rec (\x2 ->
                                    case x2 of {
                                     Prelude.True -> Prelude.True;
                                     Prelude.False -> Prelude.False}) (\x2 ->
                                    case x2 of {
                                     Prelude.True -> Prelude.False;
                                     Prelude.False -> Prelude.True}) b2 b10))
                                (\_ -> Prelude.False)
                                (bool_rec (\x2 ->
                                  case x2 of {
                                   Prelude.True -> Prelude.True;
                                   Prelude.False -> Prelude.False}) (\x2 ->
                                  case x2 of {
                                   Prelude.True -> Prelude.False;
                                   Prelude.False -> Prelude.True}) b1 b9))
                              (\_ -> Prelude.False)
                              (bool_rec (\x2 ->
                                case x2 of {
                                 Prelude.True -> Prelude.True;
                                 Prelude.False -> Prelude.False}) (\x2 ->
                                case x2 of {
                                 Prelude.True -> Prelude.False;
                                 Prelude.False -> Prelude.True}) b0 b8))
                            (\_ -> Prelude.False)
                            (bool_rec (\x2 ->
                              case x2 of {
                               Prelude.True -> Prelude.True;
                               Prelude.False -> Prelude.False}) (\x2 ->
                              case x2 of {
                               Prelude.True -> Prelude.False;
                               Prelude.False -> Prelude.True}) b b7))
                          x1) a1 a2)}) a0 s)}) eventArgs0 eventArgs1)) (\_ ->
        Prelude.False) (event_definition_dec event0 event1)}}

type Scenario_state = Prelude.String

data Step =
   Build_step Scenario_state Event_instance Action Scenario_state

stepActions :: Step -> Action
stepActions s =
  case s of {
   Build_step _ _ stepActions0 _ -> stepActions0}

pro_state :: Step -> Scenario_state
pro_state s =
  case s of {
   Build_step _ _ _ pro_state0 -> pro_state0}

data Scenario =
   Build_scenario Prelude.String ([] Step) ([] Event_definition)

scenarioId :: Scenario -> Prelude.String
scenarioId s =
  case s of {
   Build_scenario scenarioId0 _ _ -> scenarioId0}

alphabet :: Scenario -> [] Event_definition
alphabet s =
  case s of {
   Build_scenario _ _ alphabet0 -> alphabet0}

scenario_dec :: Scenario -> Scenario -> Prelude.Bool
scenario_dec n m =
  case n of {
   Build_scenario scenarioId0 traces0 alphabet0 ->
    case m of {
     Build_scenario scenarioId1 traces1 alphabet1 ->
      sumbool_rec (\_ ->
        sumbool_rec (\_ ->
          sumbool_rec (\_ -> Prelude.True) (\_ -> Prelude.False)
            (list_rec (\x ->
              case x of {
               [] -> Prelude.True;
               (:) _ _ -> Prelude.False}) (\a1 _ h0 x ->
              case x of {
               [] -> Prelude.False;
               (:) e l0 ->
                sumbool_rec (\_ ->
                  sumbool_rec (\_ -> Prelude.True) (\_ -> Prelude.False)
                    (h0 l0)) (\_ -> Prelude.False)
                  (case a1 of {
                    Build_event_definition eventKind0 eventId0
                     eventParams0 ->
                     case e of {
                      Build_event_definition eventKind1 eventId1
                       eventParams1 ->
                       sumbool_rec (\_ ->
                         sumbool_rec (\_ ->
                           sumbool_rec (\_ -> Prelude.True) (\_ ->
                             Prelude.False)
                             (list_rec (\x0 ->
                               case x0 of {
                                [] -> Prelude.True;
                                (:) _ _ -> Prelude.False}) (\a4 _ h1 x0 ->
                               case x0 of {
                                [] -> Prelude.False;
                                (:) t l2 ->
                                 sumbool_rec (\_ ->
                                   sumbool_rec (\_ -> Prelude.True) (\_ ->
                                     Prelude.False) (h1 l2)) (\_ ->
                                   Prelude.False)
                                   (typ_rec (\x1 ->
                                     case x1 of {
                                      Int -> Prelude.True;
                                      _ -> Prelude.False}) (\x1 ->
                                     case x1 of {
                                      Float -> Prelude.True;
                                      _ -> Prelude.False}) (\x1 ->
                                     case x1 of {
                                      Str -> Prelude.True;
                                      _ -> Prelude.False}) (\x1 ->
                                     case x1 of {
                                      Bool -> Prelude.True;
                                      _ -> Prelude.False}) (\x1 ->
                                     case x1 of {
                                      Pointer -> Prelude.True;
                                      _ -> Prelude.False}) (\x1 ->
                                     case x1 of {
                                      Opaque -> Prelude.True;
                                      _ -> Prelude.False}) (\x1 ->
                                     case x1 of {
                                      Thread -> Prelude.True;
                                      _ -> Prelude.False}) a4 t)})
                               eventParams0 eventParams1)) (\_ ->
                           Prelude.False)
                           (string_rec (\x0 ->
                             case x0 of {
                              [] -> Prelude.True;
                              (:) _ _ -> Prelude.False}) (\a3 _ h1 x0 ->
                             case x0 of {
                              [] -> Prelude.False;
                              (:) a4 s0 ->
                               sumbool_rec (\_ ->
                                 sumbool_rec (\_ -> Prelude.True) (\_ ->
                                   Prelude.False) (h1 s0)) (\_ ->
                                 Prelude.False)
                                 (ascii_rec (\b b0 b1 b2 b3 b4 b5 b6 x1 ->
                                   HString.foldChar
                                     (\b7 b8 b9 b10 b11 b12 b13 b14 ->
                                     sumbool_rec (\_ ->
                                       sumbool_rec (\_ ->
                                         sumbool_rec (\_ ->
                                           sumbool_rec (\_ ->
                                             sumbool_rec (\_ ->
                                               sumbool_rec (\_ ->
                                                 sumbool_rec (\_ ->
                                                   sumbool_rec (\_ ->
                                                     Prelude.True) (\_ ->
                                                     Prelude.False)
                                                     (bool_rec (\x2 ->
                                                       case x2 of {
                                                        Prelude.True ->
                                                         Prelude.True;
                                                        Prelude.False ->
                                                         Prelude.False})
                                                       (\x2 ->
                                                       case x2 of {
                                                        Prelude.True ->
                                                         Prelude.False;
                                                        Prelude.False ->
                                                         Prelude.True}) b6
                                                       b14)) (\_ ->
                                                   Prelude.False)
                                                   (bool_rec (\x2 ->
                                                     case x2 of {
                                                      Prelude.True ->
                                                       Prelude.True;
                                                      Prelude.False ->
                                                       Prelude.False})
                                                     (\x2 ->
                                                     case x2 of {
                                                      Prelude.True ->
                                                       Prelude.False;
                                                      Prelude.False ->
                                                       Prelude.True}) b5 b13))
                                                 (\_ -> Prelude.False)
                                                 (bool_rec (\x2 ->
                                                   case x2 of {
                                                    Prelude.True ->
                                                     Prelude.True;
                                                    Prelude.False ->
                                                     Prelude.False}) (\x2 ->
                                                   case x2 of {
                                                    Prelude.True ->
                                                     Prelude.False;
                                                    Prelude.False ->
                                                     Prelude.True}) b4 b12))
                                               (\_ -> Prelude.False)
                                               (bool_rec (\x2 ->
                                                 case x2 of {
                                                  Prelude.True ->
                                                   Prelude.True;
                                                  Prelude.False ->
                                                   Prelude.False}) (\x2 ->
                                                 case x2 of {
                                                  Prelude.True ->
                                                   Prelude.False;
                                                  Prelude.False ->
                                                   Prelude.True}) b3 b11))
                                             (\_ -> Prelude.False)
                                             (bool_rec (\x2 ->
                                               case x2 of {
                                                Prelude.True -> Prelude.True;
                                                Prelude.False ->
                                                 Prelude.False}) (\x2 ->
                                               case x2 of {
                                                Prelude.True -> Prelude.False;
                                                Prelude.False -> Prelude.True})
                                               b2 b10)) (\_ -> Prelude.False)
                                           (bool_rec (\x2 ->
                                             case x2 of {
                                              Prelude.True -> Prelude.True;
                                              Prelude.False -> Prelude.False})
                                             (\x2 ->
                                             case x2 of {
                                              Prelude.True -> Prelude.False;
                                              Prelude.False -> Prelude.True})
                                             b1 b9)) (\_ -> Prelude.False)
                                         (bool_rec (\x2 ->
                                           case x2 of {
                                            Prelude.True -> Prelude.True;
                                            Prelude.False -> Prelude.False})
                                           (\x2 ->
                                           case x2 of {
                                            Prelude.True -> Prelude.False;
                                            Prelude.False -> Prelude.True})
                                           b0 b8)) (\_ -> Prelude.False)
                                       (bool_rec (\x2 ->
                                         case x2 of {
                                          Prelude.True -> Prelude.True;
                                          Prelude.False -> Prelude.False})
                                         (\x2 ->
                                         case x2 of {
                                          Prelude.True -> Prelude.False;
                                          Prelude.False -> Prelude.True}) b
                                         b7))
                                     x1) a3 a4)}) eventId0 eventId1)) (\_ ->
                         Prelude.False)
                         (eventKind_rec (\x0 ->
                           case x0 of {
                            Internal -> Prelude.True;
                            _ -> Prelude.False}) (\x0 ->
                           case x0 of {
                            Imported -> Prelude.True;
                            _ -> Prelude.False}) (\x0 ->
                           case x0 of {
                            Exported -> Prelude.True;
                            _ -> Prelude.False}) eventKind0 eventKind1)}})})
              alphabet0 alphabet1)) (\_ -> Prelude.False)
          (list_rec (\x ->
            case x of {
             [] -> Prelude.True;
             (:) _ _ -> Prelude.False}) (\a0 _ h0 x ->
            case x of {
             [] -> Prelude.False;
             (:) s l0 ->
              sumbool_rec (\_ ->
                sumbool_rec (\_ -> Prelude.True) (\_ -> Prelude.False)
                  (h0 l0)) (\_ -> Prelude.False)
                (case a0 of {
                  Build_step pre_state0 stepEvent0 stepActions0 pro_state0 ->
                   case s of {
                    Build_step pre_state1 stepEvent1 stepActions1
                     pro_state1 ->
                     sumbool_rec (\_ ->
                       sumbool_rec (\_ ->
                         sumbool_rec (\_ ->
                           sumbool_rec (\_ -> Prelude.True) (\_ ->
                             Prelude.False)
                             (string_rec (\x0 ->
                               case x0 of {
                                [] -> Prelude.True;
                                (:) _ _ -> Prelude.False}) (\a4 _ h1 x0 ->
                               case x0 of {
                                [] -> Prelude.False;
                                (:) a5 s1 ->
                                 sumbool_rec (\_ ->
                                   sumbool_rec (\_ -> Prelude.True) (\_ ->
                                     Prelude.False) (h1 s1)) (\_ ->
                                   Prelude.False)
                                   (ascii_rec (\b b0 b1 b2 b3 b4 b5 b6 x1 ->
                                     HString.foldChar
                                       (\b7 b8 b9 b10 b11 b12 b13 b14 ->
                                       sumbool_rec (\_ ->
                                         sumbool_rec (\_ ->
                                           sumbool_rec (\_ ->
                                             sumbool_rec (\_ ->
                                               sumbool_rec (\_ ->
                                                 sumbool_rec (\_ ->
                                                   sumbool_rec (\_ ->
                                                     sumbool_rec (\_ ->
                                                       Prelude.True) (\_ ->
                                                       Prelude.False)
                                                       (bool_rec (\x2 ->
                                                         case x2 of {
                                                          Prelude.True ->
                                                           Prelude.True;
                                                          Prelude.False ->
                                                           Prelude.False})
                                                         (\x2 ->
                                                         case x2 of {
                                                          Prelude.True ->
                                                           Prelude.False;
                                                          Prelude.False ->
                                                           Prelude.True}) b6
                                                         b14)) (\_ ->
                                                     Prelude.False)
                                                     (bool_rec (\x2 ->
                                                       case x2 of {
                                                        Prelude.True ->
                                                         Prelude.True;
                                                        Prelude.False ->
                                                         Prelude.False})
                                                       (\x2 ->
                                                       case x2 of {
                                                        Prelude.True ->
                                                         Prelude.False;
                                                        Prelude.False ->
                                                         Prelude.True}) b5
                                                       b13)) (\_ ->
                                                   Prelude.False)
                                                   (bool_rec (\x2 ->
                                                     case x2 of {
                                                      Prelude.True ->
                                                       Prelude.True;
                                                      Prelude.False ->
                                                       Prelude.False})
                                                     (\x2 ->
                                                     case x2 of {
                                                      Prelude.True ->
                                                       Prelude.False;
                                                      Prelude.False ->
                                                       Prelude.True}) b4 b12))
                                                 (\_ -> Prelude.False)
                                                 (bool_rec (\x2 ->
                                                   case x2 of {
                                                    Prelude.True ->
                                                     Prelude.True;
                                                    Prelude.False ->
                                                     Prelude.False}) (\x2 ->
                                                   case x2 of {
                                                    Prelude.True ->
                                                     Prelude.False;
                                                    Prelude.False ->
                                                     Prelude.True}) b3 b11))
                                               (\_ -> Prelude.False)
                                               (bool_rec (\x2 ->
                                                 case x2 of {
                                                  Prelude.True ->
                                                   Prelude.True;
                                                  Prelude.False ->
                                                   Prelude.False}) (\x2 ->
                                                 case x2 of {
                                                  Prelude.True ->
                                                   Prelude.False;
                                                  Prelude.False ->
                                                   Prelude.True}) b2 b10))
                                             (\_ -> Prelude.False)
                                             (bool_rec (\x2 ->
                                               case x2 of {
                                                Prelude.True -> Prelude.True;
                                                Prelude.False ->
                                                 Prelude.False}) (\x2 ->
                                               case x2 of {
                                                Prelude.True -> Prelude.False;
                                                Prelude.False -> Prelude.True})
                                               b1 b9)) (\_ -> Prelude.False)
                                           (bool_rec (\x2 ->
                                             case x2 of {
                                              Prelude.True -> Prelude.True;
                                              Prelude.False -> Prelude.False})
                                             (\x2 ->
                                             case x2 of {
                                              Prelude.True -> Prelude.False;
                                              Prelude.False -> Prelude.True})
                                             b0 b8)) (\_ -> Prelude.False)
                                         (bool_rec (\x2 ->
                                           case x2 of {
                                            Prelude.True -> Prelude.True;
                                            Prelude.False -> Prelude.False})
                                           (\x2 ->
                                           case x2 of {
                                            Prelude.True -> Prelude.False;
                                            Prelude.False -> Prelude.True}) b
                                           b7))
                                       x1) a4 a5)}) pro_state0 pro_state1))
                           (\_ -> Prelude.False)
                           (action_rec (\x0 ->
                             case x0 of {
                              Skip -> Prelude.True;
                              _ -> Prelude.False}) (\l1 e x0 ->
                             case x0 of {
                              StateUpdate l2 e0 ->
                               sumbool_rec (\_ ->
                                 sumbool_rec (\_ -> Prelude.True) (\_ ->
                                   Prelude.False) (expr_eq_dec e e0)) (\_ ->
                                 Prelude.False)
                                 (lValue_rec (\a3 x1 ->
                                   sumbool_rec (\_ -> Prelude.True) (\_ ->
                                     Prelude.False)
                                     (atom_rec (\z x2 ->
                                       case x2 of {
                                        AInt z0 ->
                                         sumbool_rec (\_ -> Prelude.True)
                                           (\_ -> Prelude.False)
                                           (z_rec (\x3 ->
                                             (\fO fP fN n -> if n Prelude.== 0 then fO () else
                   if n Prelude.> 0 then fP n else fN (Prelude.negate n))
                                               (\_ -> Prelude.True)
                                               (\_ -> Prelude.False)
                                               (\_ -> Prelude.False)
                                               x3) (\p x3 ->
                                             (\fO fP fN n -> if n Prelude.== 0 then fO () else
                   if n Prelude.> 0 then fP n else fN (Prelude.negate n))
                                               (\_ -> Prelude.False)
                                               (\p0 ->
                                               sumbool_rec (\_ ->
                                                 Prelude.True) (\_ ->
                                                 Prelude.False)
                                                 (positive_rec (\_ h1 x4 ->
                                                   (\fI fO fH n -> if n Prelude.== 1 then fH () else
                   if Prelude.odd n then fI (n `Prelude.div` 2)
                                    else fO (n `Prelude.div` 2))
                                                     (\p2 ->
                                                     sumbool_rec (\_ ->
                                                       Prelude.True) (\_ ->
                                                       Prelude.False) 
                                                       (h1 p2))
                                                     (\_ ->
                                                     Prelude.False)
                                                     (\_ -> Prelude.False)
                                                     x4) (\_ h1 x4 ->
                                                   (\fI fO fH n -> if n Prelude.== 1 then fH () else
                   if Prelude.odd n then fI (n `Prelude.div` 2)
                                    else fO (n `Prelude.div` 2))
                                                     (\_ ->
                                                     Prelude.False)
                                                     (\p2 ->
                                                     sumbool_rec (\_ ->
                                                       Prelude.True) (\_ ->
                                                       Prelude.False) 
                                                       (h1 p2))
                                                     (\_ -> Prelude.False)
                                                     x4) (\x4 ->
                                                   (\fI fO fH n -> if n Prelude.== 1 then fH () else
                   if Prelude.odd n then fI (n `Prelude.div` 2)
                                    else fO (n `Prelude.div` 2))
                                                     (\_ ->
                                                     Prelude.False)
                                                     (\_ ->
                                                     Prelude.False)
                                                     (\_ -> Prelude.True)
                                                     x4) p p0))
                                               (\_ -> Prelude.False)
                                               x3) (\p x3 ->
                                             (\fO fP fN n -> if n Prelude.== 0 then fO () else
                   if n Prelude.> 0 then fP n else fN (Prelude.negate n))
                                               (\_ -> Prelude.False)
                                               (\_ -> Prelude.False)
                                               (\p0 ->
                                               sumbool_rec (\_ ->
                                                 Prelude.True) (\_ ->
                                                 Prelude.False)
                                                 (positive_rec (\_ h1 x4 ->
                                                   (\fI fO fH n -> if n Prelude.== 1 then fH () else
                   if Prelude.odd n then fI (n `Prelude.div` 2)
                                    else fO (n `Prelude.div` 2))
                                                     (\p2 ->
                                                     sumbool_rec (\_ ->
                                                       Prelude.True) (\_ ->
                                                       Prelude.False) 
                                                       (h1 p2))
                                                     (\_ ->
                                                     Prelude.False)
                                                     (\_ -> Prelude.False)
                                                     x4) (\_ h1 x4 ->
                                                   (\fI fO fH n -> if n Prelude.== 1 then fH () else
                   if Prelude.odd n then fI (n `Prelude.div` 2)
                                    else fO (n `Prelude.div` 2))
                                                     (\_ ->
                                                     Prelude.False)
                                                     (\p2 ->
                                                     sumbool_rec (\_ ->
                                                       Prelude.True) (\_ ->
                                                       Prelude.False) 
                                                       (h1 p2))
                                                     (\_ -> Prelude.False)
                                                     x4) (\x4 ->
                                                   (\fI fO fH n -> if n Prelude.== 1 then fH () else
                   if Prelude.odd n then fI (n `Prelude.div` 2)
                                    else fO (n `Prelude.div` 2))
                                                     (\_ ->
                                                     Prelude.False)
                                                     (\_ ->
                                                     Prelude.False)
                                                     (\_ -> Prelude.True)
                                                     x4) p p0))
                                               x3) z z0);
                                        _ -> Prelude.False}) (\q x2 ->
                                       case x2 of {
                                        AFloat q0 ->
                                         sumbool_rec (\_ -> Prelude.True)
                                           (\_ -> Prelude.False)
                                           (case q of {
                                             (GHC.Real.:%) qnum0 qden0 ->
                                              case q0 of {
                                               (GHC.Real.:%) qnum1 qden1 ->
                                                sumbool_rec (\_ ->
                                                  sumbool_rec (\_ ->
                                                    Prelude.True) (\_ ->
                                                    Prelude.False)
                                                    (positive_rec
                                                      (\_ h1 x3 ->
                                                      (\fI fO fH n -> if n Prelude.== 1 then fH () else
                   if Prelude.odd n then fI (n `Prelude.div` 2)
                                    else fO (n `Prelude.div` 2))
                                                        (\p0 ->
                                                        sumbool_rec (\_ ->
                                                          Prelude.True)
                                                          (\_ ->
                                                          Prelude.False)
                                                          (h1 p0))
                                                        (\_ ->
                                                        Prelude.False)
                                                        (\_ ->
                                                        Prelude.False)
                                                        x3) (\_ h1 x3 ->
                                                      (\fI fO fH n -> if n Prelude.== 1 then fH () else
                   if Prelude.odd n then fI (n `Prelude.div` 2)
                                    else fO (n `Prelude.div` 2))
                                                        (\_ ->
                                                        Prelude.False)
                                                        (\p0 ->
                                                        sumbool_rec (\_ ->
                                                          Prelude.True)
                                                          (\_ ->
                                                          Prelude.False)
                                                          (h1 p0))
                                                        (\_ ->
                                                        Prelude.False)
                                                        x3) (\x3 ->
                                                      (\fI fO fH n -> if n Prelude.== 1 then fH () else
                   if Prelude.odd n then fI (n `Prelude.div` 2)
                                    else fO (n `Prelude.div` 2))
                                                        (\_ ->
                                                        Prelude.False)
                                                        (\_ ->
                                                        Prelude.False)
                                                        (\_ ->
                                                        Prelude.True)
                                                        x3) qden0 qden1))
                                                  (\_ -> Prelude.False)
                                                  (z_rec (\x3 ->
                                                    (\fO fP fN n -> if n Prelude.== 0 then fO () else
                   if n Prelude.> 0 then fP n else fN (Prelude.negate n))
                                                      (\_ ->
                                                      Prelude.True)
                                                      (\_ ->
                                                      Prelude.False)
                                                      (\_ -> Prelude.False)
                                                      x3) (\p x3 ->
                                                    (\fO fP fN n -> if n Prelude.== 0 then fO () else
                   if n Prelude.> 0 then fP n else fN (Prelude.negate n))
                                                      (\_ ->
                                                      Prelude.False)
                                                      (\p0 ->
                                                      sumbool_rec (\_ ->
                                                        Prelude.True) (\_ ->
                                                        Prelude.False)
                                                        (positive_rec
                                                          (\_ h1 x4 ->
                                                          (\fI fO fH n -> if n Prelude.== 1 then fH () else
                   if Prelude.odd n then fI (n `Prelude.div` 2)
                                    else fO (n `Prelude.div` 2))
                                                            (\p2 ->
                                                            sumbool_rec
                                                              (\_ ->
                                                              Prelude.True)
                                                              (\_ ->
                                                              Prelude.False)
                                                              (h1 p2))
                                                            (\_ ->
                                                            Prelude.False)
                                                            (\_ ->
                                                            Prelude.False)
                                                            x4) (\_ h1 x4 ->
                                                          (\fI fO fH n -> if n Prelude.== 1 then fH () else
                   if Prelude.odd n then fI (n `Prelude.div` 2)
                                    else fO (n `Prelude.div` 2))
                                                            (\_ ->
                                                            Prelude.False)
                                                            (\p2 ->
                                                            sumbool_rec
                                                              (\_ ->
                                                              Prelude.True)
                                                              (\_ ->
                                                              Prelude.False)
                                                              (h1 p2))
                                                            (\_ ->
                                                            Prelude.False)
                                                            x4) (\x4 ->
                                                          (\fI fO fH n -> if n Prelude.== 1 then fH () else
                   if Prelude.odd n then fI (n `Prelude.div` 2)
                                    else fO (n `Prelude.div` 2))
                                                            (\_ ->
                                                            Prelude.False)
                                                            (\_ ->
                                                            Prelude.False)
                                                            (\_ ->
                                                            Prelude.True)
                                                            x4) p p0))
                                                      (\_ -> Prelude.False)
                                                      x3) (\p x3 ->
                                                    (\fO fP fN n -> if n Prelude.== 0 then fO () else
                   if n Prelude.> 0 then fP n else fN (Prelude.negate n))
                                                      (\_ ->
                                                      Prelude.False)
                                                      (\_ ->
                                                      Prelude.False)
                                                      (\p0 ->
                                                      sumbool_rec (\_ ->
                                                        Prelude.True) (\_ ->
                                                        Prelude.False)
                                                        (positive_rec
                                                          (\_ h1 x4 ->
                                                          (\fI fO fH n -> if n Prelude.== 1 then fH () else
                   if Prelude.odd n then fI (n `Prelude.div` 2)
                                    else fO (n `Prelude.div` 2))
                                                            (\p2 ->
                                                            sumbool_rec
                                                              (\_ ->
                                                              Prelude.True)
                                                              (\_ ->
                                                              Prelude.False)
                                                              (h1 p2))
                                                            (\_ ->
                                                            Prelude.False)
                                                            (\_ ->
                                                            Prelude.False)
                                                            x4) (\_ h1 x4 ->
                                                          (\fI fO fH n -> if n Prelude.== 1 then fH () else
                   if Prelude.odd n then fI (n `Prelude.div` 2)
                                    else fO (n `Prelude.div` 2))
                                                            (\_ ->
                                                            Prelude.False)
                                                            (\p2 ->
                                                            sumbool_rec
                                                              (\_ ->
                                                              Prelude.True)
                                                              (\_ ->
                                                              Prelude.False)
                                                              (h1 p2))
                                                            (\_ ->
                                                            Prelude.False)
                                                            x4) (\x4 ->
                                                          (\fI fO fH n -> if n Prelude.== 1 then fH () else
                   if Prelude.odd n then fI (n `Prelude.div` 2)
                                    else fO (n `Prelude.div` 2))
                                                            (\_ ->
                                                            Prelude.False)
                                                            (\_ ->
                                                            Prelude.False)
                                                            (\_ ->
                                                            Prelude.True)
                                                            x4) p p0))
                                                      x3) qnum0 qnum1)}});
                                        _ -> Prelude.False}) (\s0 x2 ->
                                       case x2 of {
                                        AIdent s1 ->
                                         sumbool_rec (\_ -> Prelude.True)
                                           (\_ -> Prelude.False)
                                           (string_rec (\x3 ->
                                             case x3 of {
                                              [] -> Prelude.True;
                                              (:) _ _ -> Prelude.False})
                                             (\a5 _ h1 x3 ->
                                             case x3 of {
                                              [] -> Prelude.False;
                                              (:) a6 s3 ->
                                               sumbool_rec (\_ ->
                                                 sumbool_rec (\_ ->
                                                   Prelude.True) (\_ ->
                                                   Prelude.False) (h1 s3))
                                                 (\_ -> Prelude.False)
                                                 (ascii_rec
                                                   (\b b0 b1 b2 b3 b4 b5 b6 x4 ->
                                                   HString.foldChar
                                                     (\b7 b8 b9 b10 b11 b12 b13 b14 ->
                                                     sumbool_rec (\_ ->
                                                       sumbool_rec (\_ ->
                                                         sumbool_rec (\_ ->
                                                           sumbool_rec (\_ ->
                                                             sumbool_rec
                                                               (\_ ->
                                                               sumbool_rec
                                                                 (\_ ->
                                                                 sumbool_rec
                                                                   (\_ ->
                                                                   sumbool_rec
                                                                    (\_ ->
                                                                    Prelude.True)
                                                                    (\_ ->
                                                                    Prelude.False)
                                                                    (bool_rec
                                                                    (\x5 ->
                                                                    case x5 of {
                                                                     Prelude.True ->
                                                                    Prelude.True;
                                                                     Prelude.False ->
                                                                    Prelude.False})
                                                                    (\x5 ->
                                                                    case x5 of {
                                                                     Prelude.True ->
                                                                    Prelude.False;
                                                                     Prelude.False ->
                                                                    Prelude.True})
                                                                    b6 b14))
                                                                   (\_ ->
                                                                   Prelude.False)
                                                                   (bool_rec
                                                                    (\x5 ->
                                                                    case x5 of {
                                                                     Prelude.True ->
                                                                    Prelude.True;
                                                                     Prelude.False ->
                                                                    Prelude.False})
                                                                    (\x5 ->
                                                                    case x5 of {
                                                                     Prelude.True ->
                                                                    Prelude.False;
                                                                     Prelude.False ->
                                                                    Prelude.True})
                                                                    b5 b13))
                                                                 (\_ ->
                                                                 Prelude.False)
                                                                 (bool_rec
                                                                   (\x5 ->
                                                                   case x5 of {
                                                                    Prelude.True ->
                                                                    Prelude.True;
                                                                    Prelude.False ->
                                                                    Prelude.False})
                                                                   (\x5 ->
                                                                   case x5 of {
                                                                    Prelude.True ->
                                                                    Prelude.False;
                                                                    Prelude.False ->
                                                                    Prelude.True})
                                                                   b4 b12))
                                                               (\_ ->
                                                               Prelude.False)
                                                               (bool_rec
                                                                 (\x5 ->
                                                                 case x5 of {
                                                                  Prelude.True ->
                                                                   Prelude.True;
                                                                  Prelude.False ->
                                                                   Prelude.False})
                                                                 (\x5 ->
                                                                 case x5 of {
                                                                  Prelude.True ->
                                                                   Prelude.False;
                                                                  Prelude.False ->
                                                                   Prelude.True})
                                                                 b3 b11))
                                                             (\_ ->
                                                             Prelude.False)
                                                             (bool_rec
                                                               (\x5 ->
                                                               case x5 of {
                                                                Prelude.True ->
                                                                 Prelude.True;
                                                                Prelude.False ->
                                                                 Prelude.False})
                                                               (\x5 ->
                                                               case x5 of {
                                                                Prelude.True ->
                                                                 Prelude.False;
                                                                Prelude.False ->
                                                                 Prelude.True})
                                                               b2 b10))
                                                           (\_ ->
                                                           Prelude.False)
                                                           (bool_rec (\x5 ->
                                                             case x5 of {
                                                              Prelude.True ->
                                                               Prelude.True;
                                                              Prelude.False ->
                                                               Prelude.False})
                                                             (\x5 ->
                                                             case x5 of {
                                                              Prelude.True ->
                                                               Prelude.False;
                                                              Prelude.False ->
                                                               Prelude.True})
                                                             b1 b9)) (\_ ->
                                                         Prelude.False)
                                                         (bool_rec (\x5 ->
                                                           case x5 of {
                                                            Prelude.True ->
                                                             Prelude.True;
                                                            Prelude.False ->
                                                             Prelude.False})
                                                           (\x5 ->
                                                           case x5 of {
                                                            Prelude.True ->
                                                             Prelude.False;
                                                            Prelude.False ->
                                                             Prelude.True})
                                                           b0 b8)) (\_ ->
                                                       Prelude.False)
                                                       (bool_rec (\x5 ->
                                                         case x5 of {
                                                          Prelude.True ->
                                                           Prelude.True;
                                                          Prelude.False ->
                                                           Prelude.False})
                                                         (\x5 ->
                                                         case x5 of {
                                                          Prelude.True ->
                                                           Prelude.False;
                                                          Prelude.False ->
                                                           Prelude.True}) b
                                                         b7))
                                                     x4) a5 a6)}) s0 s1);
                                        _ -> Prelude.False}) (\b x2 ->
                                       case x2 of {
                                        ABool b0 ->
                                         sumbool_rec (\_ -> Prelude.True)
                                           (\_ -> Prelude.False)
                                           (bool_rec (\x3 ->
                                             case x3 of {
                                              Prelude.True -> Prelude.True;
                                              Prelude.False -> Prelude.False})
                                             (\x3 ->
                                             case x3 of {
                                              Prelude.True -> Prelude.False;
                                              Prelude.False -> Prelude.True})
                                             b b0);
                                        _ -> Prelude.False}) (\x2 ->
                                       case x2 of {
                                        ANull -> Prelude.True;
                                        _ -> Prelude.False}) (\s0 x2 ->
                                       case x2 of {
                                        AString s1 ->
                                         sumbool_rec (\_ -> Prelude.True)
                                           (\_ -> Prelude.False)
                                           (string_rec (\x3 ->
                                             case x3 of {
                                              [] -> Prelude.True;
                                              (:) _ _ -> Prelude.False})
                                             (\a5 _ h1 x3 ->
                                             case x3 of {
                                              [] -> Prelude.False;
                                              (:) a6 s3 ->
                                               sumbool_rec (\_ ->
                                                 sumbool_rec (\_ ->
                                                   Prelude.True) (\_ ->
                                                   Prelude.False) (h1 s3))
                                                 (\_ -> Prelude.False)
                                                 (ascii_rec
                                                   (\b b0 b1 b2 b3 b4 b5 b6 x4 ->
                                                   HString.foldChar
                                                     (\b7 b8 b9 b10 b11 b12 b13 b14 ->
                                                     sumbool_rec (\_ ->
                                                       sumbool_rec (\_ ->
                                                         sumbool_rec (\_ ->
                                                           sumbool_rec (\_ ->
                                                             sumbool_rec
                                                               (\_ ->
                                                               sumbool_rec
                                                                 (\_ ->
                                                                 sumbool_rec
                                                                   (\_ ->
                                                                   sumbool_rec
                                                                    (\_ ->
                                                                    Prelude.True)
                                                                    (\_ ->
                                                                    Prelude.False)
                                                                    (bool_rec
                                                                    (\x5 ->
                                                                    case x5 of {
                                                                     Prelude.True ->
                                                                    Prelude.True;
                                                                     Prelude.False ->
                                                                    Prelude.False})
                                                                    (\x5 ->
                                                                    case x5 of {
                                                                     Prelude.True ->
                                                                    Prelude.False;
                                                                     Prelude.False ->
                                                                    Prelude.True})
                                                                    b6 b14))
                                                                   (\_ ->
                                                                   Prelude.False)
                                                                   (bool_rec
                                                                    (\x5 ->
                                                                    case x5 of {
                                                                     Prelude.True ->
                                                                    Prelude.True;
                                                                     Prelude.False ->
                                                                    Prelude.False})
                                                                    (\x5 ->
                                                                    case x5 of {
                                                                     Prelude.True ->
                                                                    Prelude.False;
                                                                     Prelude.False ->
                                                                    Prelude.True})
                                                                    b5 b13))
                                                                 (\_ ->
                                                                 Prelude.False)
                                                                 (bool_rec
                                                                   (\x5 ->
                                                                   case x5 of {
                                                                    Prelude.True ->
                                                                    Prelude.True;
                                                                    Prelude.False ->
                                                                    Prelude.False})
                                                                   (\x5 ->
                                                                   case x5 of {
                                                                    Prelude.True ->
                                                                    Prelude.False;
                                                                    Prelude.False ->
                                                                    Prelude.True})
                                                                   b4 b12))
                                                               (\_ ->
                                                               Prelude.False)
                                                               (bool_rec
                                                                 (\x5 ->
                                                                 case x5 of {
                                                                  Prelude.True ->
                                                                   Prelude.True;
                                                                  Prelude.False ->
                                                                   Prelude.False})
                                                                 (\x5 ->
                                                                 case x5 of {
                                                                  Prelude.True ->
                                                                   Prelude.False;
                                                                  Prelude.False ->
                                                                   Prelude.True})
                                                                 b3 b11))
                                                             (\_ ->
                                                             Prelude.False)
                                                             (bool_rec
                                                               (\x5 ->
                                                               case x5 of {
                                                                Prelude.True ->
                                                                 Prelude.True;
                                                                Prelude.False ->
                                                                 Prelude.False})
                                                               (\x5 ->
                                                               case x5 of {
                                                                Prelude.True ->
                                                                 Prelude.False;
                                                                Prelude.False ->
                                                                 Prelude.True})
                                                               b2 b10))
                                                           (\_ ->
                                                           Prelude.False)
                                                           (bool_rec (\x5 ->
                                                             case x5 of {
                                                              Prelude.True ->
                                                               Prelude.True;
                                                              Prelude.False ->
                                                               Prelude.False})
                                                             (\x5 ->
                                                             case x5 of {
                                                              Prelude.True ->
                                                               Prelude.False;
                                                              Prelude.False ->
                                                               Prelude.True})
                                                             b1 b9)) (\_ ->
                                                         Prelude.False)
                                                         (bool_rec (\x5 ->
                                                           case x5 of {
                                                            Prelude.True ->
                                                             Prelude.True;
                                                            Prelude.False ->
                                                             Prelude.False})
                                                           (\x5 ->
                                                           case x5 of {
                                                            Prelude.True ->
                                                             Prelude.False;
                                                            Prelude.False ->
                                                             Prelude.True})
                                                           b0 b8)) (\_ ->
                                                       Prelude.False)
                                                       (bool_rec (\x5 ->
                                                         case x5 of {
                                                          Prelude.True ->
                                                           Prelude.True;
                                                          Prelude.False ->
                                                           Prelude.False})
                                                         (\x5 ->
                                                         case x5 of {
                                                          Prelude.True ->
                                                           Prelude.False;
                                                          Prelude.False ->
                                                           Prelude.True}) b
                                                         b7))
                                                     x4) a5 a6)}) s0 s1);
                                        _ -> Prelude.False}) a3 x1)) l1 l2);
                              _ -> Prelude.False}) (\ident exprs x0 ->
                             case x0 of {
                              RaiseStmt ident0 exprs0 ->
                               sumbool_rec (\_ ->
                                 sumbool_rec (\_ -> Prelude.True) (\_ ->
                                   Prelude.False)
                                   (list_rec (\x1 ->
                                     case x1 of {
                                      [] -> Prelude.True;
                                      (:) _ _ -> Prelude.False})
                                     (\a4 _ h1 x1 ->
                                     case x1 of {
                                      [] -> Prelude.False;
                                      (:) e l2 ->
                                       sumbool_rec (\_ ->
                                         sumbool_rec (\_ -> Prelude.True)
                                           (\_ -> Prelude.False) (h1 l2))
                                         (\_ -> Prelude.False)
                                         (expr_eq_dec a4 e)}) exprs exprs0))
                                 (\_ -> Prelude.False)
                                 (string_rec (\x1 ->
                                   case x1 of {
                                    [] -> Prelude.True;
                                    (:) _ _ -> Prelude.False})
                                   (\a3 _ h1 x1 ->
                                   case x1 of {
                                    [] -> Prelude.False;
                                    (:) a4 s1 ->
                                     sumbool_rec (\_ ->
                                       sumbool_rec (\_ -> Prelude.True)
                                         (\_ -> Prelude.False) (h1 s1))
                                       (\_ -> Prelude.False)
                                       (ascii_rec
                                         (\b b0 b1 b2 b3 b4 b5 b6 x2 ->
                                         HString.foldChar
                                           (\b7 b8 b9 b10 b11 b12 b13 b14 ->
                                           sumbool_rec (\_ ->
                                             sumbool_rec (\_ ->
                                               sumbool_rec (\_ ->
                                                 sumbool_rec (\_ ->
                                                   sumbool_rec (\_ ->
                                                     sumbool_rec (\_ ->
                                                       sumbool_rec (\_ ->
                                                         sumbool_rec (\_ ->
                                                           Prelude.True)
                                                           (\_ ->
                                                           Prelude.False)
                                                           (bool_rec (\x3 ->
                                                             case x3 of {
                                                              Prelude.True ->
                                                               Prelude.True;
                                                              Prelude.False ->
                                                               Prelude.False})
                                                             (\x3 ->
                                                             case x3 of {
                                                              Prelude.True ->
                                                               Prelude.False;
                                                              Prelude.False ->
                                                               Prelude.True})
                                                             b6 b14)) (\_ ->
                                                         Prelude.False)
                                                         (bool_rec (\x3 ->
                                                           case x3 of {
                                                            Prelude.True ->
                                                             Prelude.True;
                                                            Prelude.False ->
                                                             Prelude.False})
                                                           (\x3 ->
                                                           case x3 of {
                                                            Prelude.True ->
                                                             Prelude.False;
                                                            Prelude.False ->
                                                             Prelude.True})
                                                           b5 b13)) (\_ ->
                                                       Prelude.False)
                                                       (bool_rec (\x3 ->
                                                         case x3 of {
                                                          Prelude.True ->
                                                           Prelude.True;
                                                          Prelude.False ->
                                                           Prelude.False})
                                                         (\x3 ->
                                                         case x3 of {
                                                          Prelude.True ->
                                                           Prelude.False;
                                                          Prelude.False ->
                                                           Prelude.True}) b4
                                                         b12)) (\_ ->
                                                     Prelude.False)
                                                     (bool_rec (\x3 ->
                                                       case x3 of {
                                                        Prelude.True ->
                                                         Prelude.True;
                                                        Prelude.False ->
                                                         Prelude.False})
                                                       (\x3 ->
                                                       case x3 of {
                                                        Prelude.True ->
                                                         Prelude.False;
                                                        Prelude.False ->
                                                         Prelude.True}) b3
                                                       b11)) (\_ ->
                                                   Prelude.False)
                                                   (bool_rec (\x3 ->
                                                     case x3 of {
                                                      Prelude.True ->
                                                       Prelude.True;
                                                      Prelude.False ->
                                                       Prelude.False})
                                                     (\x3 ->
                                                     case x3 of {
                                                      Prelude.True ->
                                                       Prelude.False;
                                                      Prelude.False ->
                                                       Prelude.True}) b2 b10))
                                                 (\_ -> Prelude.False)
                                                 (bool_rec (\x3 ->
                                                   case x3 of {
                                                    Prelude.True ->
                                                     Prelude.True;
                                                    Prelude.False ->
                                                     Prelude.False}) (\x3 ->
                                                   case x3 of {
                                                    Prelude.True ->
                                                     Prelude.False;
                                                    Prelude.False ->
                                                     Prelude.True}) b1 b9))
                                               (\_ -> Prelude.False)
                                               (bool_rec (\x3 ->
                                                 case x3 of {
                                                  Prelude.True ->
                                                   Prelude.True;
                                                  Prelude.False ->
                                                   Prelude.False}) (\x3 ->
                                                 case x3 of {
                                                  Prelude.True ->
                                                   Prelude.False;
                                                  Prelude.False ->
                                                   Prelude.True}) b0 b8))
                                             (\_ -> Prelude.False)
                                             (bool_rec (\x3 ->
                                               case x3 of {
                                                Prelude.True -> Prelude.True;
                                                Prelude.False ->
                                                 Prelude.False}) (\x3 ->
                                               case x3 of {
                                                Prelude.True -> Prelude.False;
                                                Prelude.False -> Prelude.True})
                                               b b7))
                                           x2) a3 a4)}) ident ident0);
                              _ -> Prelude.False}) (\_ h1 _ h2 x0 ->
                             case x0 of {
                              Seq a5 a6 ->
                               sumbool_rec (\_ ->
                                 sumbool_rec (\_ -> Prelude.True) (\_ ->
                                   Prelude.False) (h2 a6)) (\_ ->
                                 Prelude.False) (h1 a5);
                              _ -> Prelude.False}) stepActions0 stepActions1))
                         (\_ -> Prelude.False)
                         (case stepEvent0 of {
                           Build_event_instance event0 eventArgs0
                            eventWhenExpr0 ->
                            case stepEvent1 of {
                             Build_event_instance event1 eventArgs1
                              eventWhenExpr1 ->
                              sumbool_rec (\_ ->
                                sumbool_rec (\_ ->
                                  sumbool_rec (\_ -> Prelude.True) (\_ ->
                                    Prelude.False)
                                    (expr_eq_dec eventWhenExpr0
                                      eventWhenExpr1)) (\_ -> Prelude.False)
                                  (list_rec (\x0 ->
                                    case x0 of {
                                     [] -> Prelude.True;
                                     (:) _ _ -> Prelude.False})
                                    (\a3 _ h1 x0 ->
                                    case x0 of {
                                     [] -> Prelude.False;
                                     (:) s0 l2 ->
                                      sumbool_rec (\_ ->
                                        sumbool_rec (\_ -> Prelude.True)
                                          (\_ -> Prelude.False) (h1 l2))
                                        (\_ -> Prelude.False)
                                        (string_rec (\x1 ->
                                          case x1 of {
                                           [] -> Prelude.True;
                                           (:) _ _ -> Prelude.False})
                                          (\a4 _ h2 x1 ->
                                          case x1 of {
                                           [] -> Prelude.False;
                                           (:) a5 s2 ->
                                            sumbool_rec (\_ ->
                                              sumbool_rec (\_ ->
                                                Prelude.True) (\_ ->
                                                Prelude.False) (h2 s2))
                                              (\_ -> Prelude.False)
                                              (ascii_rec
                                                (\b b0 b1 b2 b3 b4 b5 b6 x2 ->
                                                HString.foldChar
                                                  (\b7 b8 b9 b10 b11 b12 b13 b14 ->
                                                  sumbool_rec (\_ ->
                                                    sumbool_rec (\_ ->
                                                      sumbool_rec (\_ ->
                                                        sumbool_rec (\_ ->
                                                          sumbool_rec (\_ ->
                                                            sumbool_rec
                                                              (\_ ->
                                                              sumbool_rec
                                                                (\_ ->
                                                                sumbool_rec
                                                                  (\_ ->
                                                                  Prelude.True)
                                                                  (\_ ->
                                                                  Prelude.False)
                                                                  (bool_rec
                                                                    (\x3 ->
                                                                    case x3 of {
                                                                     Prelude.True ->
                                                                    Prelude.True;
                                                                     Prelude.False ->
                                                                    Prelude.False})
                                                                    (\x3 ->
                                                                    case x3 of {
                                                                     Prelude.True ->
                                                                    Prelude.False;
                                                                     Prelude.False ->
                                                                    Prelude.True})
                                                                    b6 b14))
                                                                (\_ ->
                                                                Prelude.False)
                                                                (bool_rec
                                                                  (\x3 ->
                                                                  case x3 of {
                                                                   Prelude.True ->
                                                                    Prelude.True;
                                                                   Prelude.False ->
                                                                    Prelude.False})
                                                                  (\x3 ->
                                                                  case x3 of {
                                                                   Prelude.True ->
                                                                    Prelude.False;
                                                                   Prelude.False ->
                                                                    Prelude.True})
                                                                  b5 b13))
                                                              (\_ ->
                                                              Prelude.False)
                                                              (bool_rec
                                                                (\x3 ->
                                                                case x3 of {
                                                                 Prelude.True ->
                                                                  Prelude.True;
                                                                 Prelude.False ->
                                                                  Prelude.False})
                                                                (\x3 ->
                                                                case x3 of {
                                                                 Prelude.True ->
                                                                  Prelude.False;
                                                                 Prelude.False ->
                                                                  Prelude.True})
                                                                b4 b12))
                                                            (\_ ->
                                                            Prelude.False)
                                                            (bool_rec (\x3 ->
                                                              case x3 of {
                                                               Prelude.True ->
                                                                Prelude.True;
                                                               Prelude.False ->
                                                                Prelude.False})
                                                              (\x3 ->
                                                              case x3 of {
                                                               Prelude.True ->
                                                                Prelude.False;
                                                               Prelude.False ->
                                                                Prelude.True})
                                                              b3 b11)) (\_ ->
                                                          Prelude.False)
                                                          (bool_rec (\x3 ->
                                                            case x3 of {
                                                             Prelude.True ->
                                                              Prelude.True;
                                                             Prelude.False ->
                                                              Prelude.False})
                                                            (\x3 ->
                                                            case x3 of {
                                                             Prelude.True ->
                                                              Prelude.False;
                                                             Prelude.False ->
                                                              Prelude.True})
                                                            b2 b10)) (\_ ->
                                                        Prelude.False)
                                                        (bool_rec (\x3 ->
                                                          case x3 of {
                                                           Prelude.True ->
                                                            Prelude.True;
                                                           Prelude.False ->
                                                            Prelude.False})
                                                          (\x3 ->
                                                          case x3 of {
                                                           Prelude.True ->
                                                            Prelude.False;
                                                           Prelude.False ->
                                                            Prelude.True}) b1
                                                          b9)) (\_ ->
                                                      Prelude.False)
                                                      (bool_rec (\x3 ->
                                                        case x3 of {
                                                         Prelude.True ->
                                                          Prelude.True;
                                                         Prelude.False ->
                                                          Prelude.False})
                                                        (\x3 ->
                                                        case x3 of {
                                                         Prelude.True ->
                                                          Prelude.False;
                                                         Prelude.False ->
                                                          Prelude.True}) b0
                                                        b8)) (\_ ->
                                                    Prelude.False)
                                                    (bool_rec (\x3 ->
                                                      case x3 of {
                                                       Prelude.True ->
                                                        Prelude.True;
                                                       Prelude.False ->
                                                        Prelude.False})
                                                      (\x3 ->
                                                      case x3 of {
                                                       Prelude.True ->
                                                        Prelude.False;
                                                       Prelude.False ->
                                                        Prelude.True}) b b7))
                                                  x2) a4 a5)}) a3 s0)})
                                    eventArgs0 eventArgs1)) (\_ ->
                                Prelude.False)
                                (case event0 of {
                                  Build_event_definition eventKind0 eventId0
                                   eventParams0 ->
                                   case event1 of {
                                    Build_event_definition eventKind1
                                     eventId1 eventParams1 ->
                                     sumbool_rec (\_ ->
                                       sumbool_rec (\_ ->
                                         sumbool_rec (\_ -> Prelude.True)
                                           (\_ -> Prelude.False)
                                           (list_rec (\x0 ->
                                             case x0 of {
                                              [] -> Prelude.True;
                                              (:) _ _ -> Prelude.False})
                                             (\a4 _ h1 x0 ->
                                             case x0 of {
                                              [] -> Prelude.False;
                                              (:) t l2 ->
                                               sumbool_rec (\_ ->
                                                 sumbool_rec (\_ ->
                                                   Prelude.True) (\_ ->
                                                   Prelude.False) (h1 l2))
                                                 (\_ -> Prelude.False)
                                                 (typ_rec (\x1 ->
                                                   case x1 of {
                                                    Int -> Prelude.True;
                                                    _ -> Prelude.False})
                                                   (\x1 ->
                                                   case x1 of {
                                                    Float -> Prelude.True;
                                                    _ -> Prelude.False})
                                                   (\x1 ->
                                                   case x1 of {
                                                    Str -> Prelude.True;
                                                    _ -> Prelude.False})
                                                   (\x1 ->
                                                   case x1 of {
                                                    Bool -> Prelude.True;
                                                    _ -> Prelude.False})
                                                   (\x1 ->
                                                   case x1 of {
                                                    Pointer -> Prelude.True;
                                                    _ -> Prelude.False})
                                                   (\x1 ->
                                                   case x1 of {
                                                    Opaque -> Prelude.True;
                                                    _ -> Prelude.False})
                                                   (\x1 ->
                                                   case x1 of {
                                                    Thread -> Prelude.True;
                                                    _ -> Prelude.False}) a4
                                                   t)}) eventParams0
                                             eventParams1)) (\_ ->
                                         Prelude.False)
                                         (string_rec (\x0 ->
                                           case x0 of {
                                            [] -> Prelude.True;
                                            (:) _ _ -> Prelude.False})
                                           (\a3 _ h1 x0 ->
                                           case x0 of {
                                            [] -> Prelude.False;
                                            (:) a4 s1 ->
                                             sumbool_rec (\_ ->
                                               sumbool_rec (\_ ->
                                                 Prelude.True) (\_ ->
                                                 Prelude.False) (h1 s1))
                                               (\_ -> Prelude.False)
                                               (ascii_rec
                                                 (\b b0 b1 b2 b3 b4 b5 b6 x1 ->
                                                 HString.foldChar
                                                   (\b7 b8 b9 b10 b11 b12 b13 b14 ->
                                                   sumbool_rec (\_ ->
                                                     sumbool_rec (\_ ->
                                                       sumbool_rec (\_ ->
                                                         sumbool_rec (\_ ->
                                                           sumbool_rec (\_ ->
                                                             sumbool_rec
                                                               (\_ ->
                                                               sumbool_rec
                                                                 (\_ ->
                                                                 sumbool_rec
                                                                   (\_ ->
                                                                   Prelude.True)
                                                                   (\_ ->
                                                                   Prelude.False)
                                                                   (bool_rec
                                                                    (\x2 ->
                                                                    case x2 of {
                                                                     Prelude.True ->
                                                                    Prelude.True;
                                                                     Prelude.False ->
                                                                    Prelude.False})
                                                                    (\x2 ->
                                                                    case x2 of {
                                                                     Prelude.True ->
                                                                    Prelude.False;
                                                                     Prelude.False ->
                                                                    Prelude.True})
                                                                    b6 b14))
                                                                 (\_ ->
                                                                 Prelude.False)
                                                                 (bool_rec
                                                                   (\x2 ->
                                                                   case x2 of {
                                                                    Prelude.True ->
                                                                    Prelude.True;
                                                                    Prelude.False ->
                                                                    Prelude.False})
                                                                   (\x2 ->
                                                                   case x2 of {
                                                                    Prelude.True ->
                                                                    Prelude.False;
                                                                    Prelude.False ->
                                                                    Prelude.True})
                                                                   b5 b13))
                                                               (\_ ->
                                                               Prelude.False)
                                                               (bool_rec
                                                                 (\x2 ->
                                                                 case x2 of {
                                                                  Prelude.True ->
                                                                   Prelude.True;
                                                                  Prelude.False ->
                                                                   Prelude.False})
                                                                 (\x2 ->
                                                                 case x2 of {
                                                                  Prelude.True ->
                                                                   Prelude.False;
                                                                  Prelude.False ->
                                                                   Prelude.True})
                                                                 b4 b12))
                                                             (\_ ->
                                                             Prelude.False)
                                                             (bool_rec
                                                               (\x2 ->
                                                               case x2 of {
                                                                Prelude.True ->
                                                                 Prelude.True;
                                                                Prelude.False ->
                                                                 Prelude.False})
                                                               (\x2 ->
                                                               case x2 of {
                                                                Prelude.True ->
                                                                 Prelude.False;
                                                                Prelude.False ->
                                                                 Prelude.True})
                                                               b3 b11))
                                                           (\_ ->
                                                           Prelude.False)
                                                           (bool_rec (\x2 ->
                                                             case x2 of {
                                                              Prelude.True ->
                                                               Prelude.True;
                                                              Prelude.False ->
                                                               Prelude.False})
                                                             (\x2 ->
                                                             case x2 of {
                                                              Prelude.True ->
                                                               Prelude.False;
                                                              Prelude.False ->
                                                               Prelude.True})
                                                             b2 b10)) (\_ ->
                                                         Prelude.False)
                                                         (bool_rec (\x2 ->
                                                           case x2 of {
                                                            Prelude.True ->
                                                             Prelude.True;
                                                            Prelude.False ->
                                                             Prelude.False})
                                                           (\x2 ->
                                                           case x2 of {
                                                            Prelude.True ->
                                                             Prelude.False;
                                                            Prelude.False ->
                                                             Prelude.True})
                                                           b1 b9)) (\_ ->
                                                       Prelude.False)
                                                       (bool_rec (\x2 ->
                                                         case x2 of {
                                                          Prelude.True ->
                                                           Prelude.True;
                                                          Prelude.False ->
                                                           Prelude.False})
                                                         (\x2 ->
                                                         case x2 of {
                                                          Prelude.True ->
                                                           Prelude.False;
                                                          Prelude.False ->
                                                           Prelude.True}) b0
                                                         b8)) (\_ ->
                                                     Prelude.False)
                                                     (bool_rec (\x2 ->
                                                       case x2 of {
                                                        Prelude.True ->
                                                         Prelude.True;
                                                        Prelude.False ->
                                                         Prelude.False})
                                                       (\x2 ->
                                                       case x2 of {
                                                        Prelude.True ->
                                                         Prelude.False;
                                                        Prelude.False ->
                                                         Prelude.True}) b b7))
                                                   x1) a3 a4)}) eventId0
                                           eventId1)) (\_ -> Prelude.False)
                                       (eventKind_rec (\x0 ->
                                         case x0 of {
                                          Internal -> Prelude.True;
                                          _ -> Prelude.False}) (\x0 ->
                                         case x0 of {
                                          Imported -> Prelude.True;
                                          _ -> Prelude.False}) (\x0 ->
                                         case x0 of {
                                          Exported -> Prelude.True;
                                          _ -> Prelude.False}) eventKind0
                                         eventKind1)}})}})) (\_ ->
                       Prelude.False)
                       (string_rec (\x0 ->
                         case x0 of {
                          [] -> Prelude.True;
                          (:) _ _ -> Prelude.False}) (\a1 _ h1 x0 ->
                         case x0 of {
                          [] -> Prelude.False;
                          (:) a2 s1 ->
                           sumbool_rec (\_ ->
                             sumbool_rec (\_ -> Prelude.True) (\_ ->
                               Prelude.False) (h1 s1)) (\_ -> Prelude.False)
                             (ascii_rec (\b b0 b1 b2 b3 b4 b5 b6 x1 ->
                               HString.foldChar
                                 (\b7 b8 b9 b10 b11 b12 b13 b14 ->
                                 sumbool_rec (\_ ->
                                   sumbool_rec (\_ ->
                                     sumbool_rec (\_ ->
                                       sumbool_rec (\_ ->
                                         sumbool_rec (\_ ->
                                           sumbool_rec (\_ ->
                                             sumbool_rec (\_ ->
                                               sumbool_rec (\_ ->
                                                 Prelude.True) (\_ ->
                                                 Prelude.False)
                                                 (bool_rec (\x2 ->
                                                   case x2 of {
                                                    Prelude.True ->
                                                     Prelude.True;
                                                    Prelude.False ->
                                                     Prelude.False}) (\x2 ->
                                                   case x2 of {
                                                    Prelude.True ->
                                                     Prelude.False;
                                                    Prelude.False ->
                                                     Prelude.True}) b6 b14))
                                               (\_ -> Prelude.False)
                                               (bool_rec (\x2 ->
                                                 case x2 of {
                                                  Prelude.True ->
                                                   Prelude.True;
                                                  Prelude.False ->
                                                   Prelude.False}) (\x2 ->
                                                 case x2 of {
                                                  Prelude.True ->
                                                   Prelude.False;
                                                  Prelude.False ->
                                                   Prelude.True}) b5 b13))
                                             (\_ -> Prelude.False)
                                             (bool_rec (\x2 ->
                                               case x2 of {
                                                Prelude.True -> Prelude.True;
                                                Prelude.False ->
                                                 Prelude.False}) (\x2 ->
                                               case x2 of {
                                                Prelude.True -> Prelude.False;
                                                Prelude.False -> Prelude.True})
                                               b4 b12)) (\_ -> Prelude.False)
                                           (bool_rec (\x2 ->
                                             case x2 of {
                                              Prelude.True -> Prelude.True;
                                              Prelude.False -> Prelude.False})
                                             (\x2 ->
                                             case x2 of {
                                              Prelude.True -> Prelude.False;
                                              Prelude.False -> Prelude.True})
                                             b3 b11)) (\_ -> Prelude.False)
                                         (bool_rec (\x2 ->
                                           case x2 of {
                                            Prelude.True -> Prelude.True;
                                            Prelude.False -> Prelude.False})
                                           (\x2 ->
                                           case x2 of {
                                            Prelude.True -> Prelude.False;
                                            Prelude.False -> Prelude.True})
                                           b2 b10)) (\_ -> Prelude.False)
                                       (bool_rec (\x2 ->
                                         case x2 of {
                                          Prelude.True -> Prelude.True;
                                          Prelude.False -> Prelude.False})
                                         (\x2 ->
                                         case x2 of {
                                          Prelude.True -> Prelude.False;
                                          Prelude.False -> Prelude.True}) b1
                                         b9)) (\_ -> Prelude.False)
                                     (bool_rec (\x2 ->
                                       case x2 of {
                                        Prelude.True -> Prelude.True;
                                        Prelude.False -> Prelude.False})
                                       (\x2 ->
                                       case x2 of {
                                        Prelude.True -> Prelude.False;
                                        Prelude.False -> Prelude.True}) b0
                                       b8)) (\_ -> Prelude.False)
                                   (bool_rec (\x2 ->
                                     case x2 of {
                                      Prelude.True -> Prelude.True;
                                      Prelude.False -> Prelude.False})
                                     (\x2 ->
                                     case x2 of {
                                      Prelude.True -> Prelude.False;
                                      Prelude.False -> Prelude.True}) b b7))
                                 x1) a1 a2)}) pre_state0 pre_state1)}})})
            traces0 traces1)) (\_ -> Prelude.False)
        (string_rec (\x ->
          case x of {
           [] -> Prelude.True;
           (:) _ _ -> Prelude.False}) (\a _ h0 x ->
          case x of {
           [] -> Prelude.False;
           (:) a0 s0 ->
            sumbool_rec (\_ ->
              sumbool_rec (\_ -> Prelude.True) (\_ -> Prelude.False) (h0 s0))
              (\_ -> Prelude.False)
              (ascii_rec (\b b0 b1 b2 b3 b4 b5 b6 x0 ->
                HString.foldChar
                  (\b7 b8 b9 b10 b11 b12 b13 b14 ->
                  sumbool_rec (\_ ->
                    sumbool_rec (\_ ->
                      sumbool_rec (\_ ->
                        sumbool_rec (\_ ->
                          sumbool_rec (\_ ->
                            sumbool_rec (\_ ->
                              sumbool_rec (\_ ->
                                sumbool_rec (\_ -> Prelude.True) (\_ ->
                                  Prelude.False)
                                  (bool_rec (\x1 ->
                                    case x1 of {
                                     Prelude.True -> Prelude.True;
                                     Prelude.False -> Prelude.False}) (\x1 ->
                                    case x1 of {
                                     Prelude.True -> Prelude.False;
                                     Prelude.False -> Prelude.True}) b6 b14))
                                (\_ -> Prelude.False)
                                (bool_rec (\x1 ->
                                  case x1 of {
                                   Prelude.True -> Prelude.True;
                                   Prelude.False -> Prelude.False}) (\x1 ->
                                  case x1 of {
                                   Prelude.True -> Prelude.False;
                                   Prelude.False -> Prelude.True}) b5 b13))
                              (\_ -> Prelude.False)
                              (bool_rec (\x1 ->
                                case x1 of {
                                 Prelude.True -> Prelude.True;
                                 Prelude.False -> Prelude.False}) (\x1 ->
                                case x1 of {
                                 Prelude.True -> Prelude.False;
                                 Prelude.False -> Prelude.True}) b4 b12))
                            (\_ -> Prelude.False)
                            (bool_rec (\x1 ->
                              case x1 of {
                               Prelude.True -> Prelude.True;
                               Prelude.False -> Prelude.False}) (\x1 ->
                              case x1 of {
                               Prelude.True -> Prelude.False;
                               Prelude.False -> Prelude.True}) b3 b11))
                          (\_ -> Prelude.False)
                          (bool_rec (\x1 ->
                            case x1 of {
                             Prelude.True -> Prelude.True;
                             Prelude.False -> Prelude.False}) (\x1 ->
                            case x1 of {
                             Prelude.True -> Prelude.False;
                             Prelude.False -> Prelude.True}) b2 b10)) (\_ ->
                        Prelude.False)
                        (bool_rec (\x1 ->
                          case x1 of {
                           Prelude.True -> Prelude.True;
                           Prelude.False -> Prelude.False}) (\x1 ->
                          case x1 of {
                           Prelude.True -> Prelude.False;
                           Prelude.False -> Prelude.True}) b1 b9)) (\_ ->
                      Prelude.False)
                      (bool_rec (\x1 ->
                        case x1 of {
                         Prelude.True -> Prelude.True;
                         Prelude.False -> Prelude.False}) (\x1 ->
                        case x1 of {
                         Prelude.True -> Prelude.False;
                         Prelude.False -> Prelude.True}) b0 b8)) (\_ ->
                    Prelude.False)
                    (bool_rec (\x1 ->
                      case x1 of {
                       Prelude.True -> Prelude.True;
                       Prelude.False -> Prelude.False}) (\x1 ->
                      case x1 of {
                       Prelude.True -> Prelude.False;
                       Prelude.False -> Prelude.True}) b b7))
                  x0) a a0)}) scenarioId0 scenarioId1)}}

type Scenario_env = [] ((,) Scenario Scenario_state)

getScenarioState :: Scenario -> Scenario_env -> Prelude.Maybe Scenario_state
getScenarioState sce env =
  case env of {
   [] -> Prelude.Nothing;
   (:) p en' ->
    case p of {
     (,) s e ->
      case string_dec (scenarioId sce) (scenarioId s) of {
       Prelude.True -> Prelude.Just e;
       Prelude.False -> getScenarioState sce en'}}}

updateScenarioState' :: Scenario -> Scenario_state -> Scenario_env ->
                        Scenario_env
updateScenarioState' sce st env =
  case env of {
   [] -> [];
   (:) p en' ->
    case p of {
     (,) s e ->
      case string_dec (scenarioId s) (scenarioId sce) of {
       Prelude.True -> (:) ((,) s st) (updateScenarioState' sce st en');
       Prelude.False -> (:) ((,) s e) (updateScenarioState' sce st en')}}}

filterList :: ([] a1) -> ([] a1) -> (a1 -> a1 -> Prelude.Bool) -> [] a1
filterList l1 l2 decA =
  case l2 of {
   [] -> [];
   (:) e' lst ->
    case inList decA e' l1 of {
     Prelude.True -> filterList l1 lst decA;
     Prelude.False -> (:) e' (filterList l1 lst decA)}}

data Object =
   Build_object ([] Prelude.String) Prelude.String Typ_env Typ_env ([]
                                                                   Event_definition) 
 ([] Scenario) ([]
               ((,) ((,) Scenario_state Event_instance) (Prelude.Maybe Step))) 
 ([]
 ((,) ((,) ((,) Scenario_state Event_instance) Scenario)
 (Prelude.Maybe Step))) ([]
                        ((,)
                        ((,) (Prelude.Maybe Scenario_state)
                        (Prelude.Maybe Event_definition))
                        ([] Event_instance))) ([] ((,) Scenario Step)) 
 ([] ((,) Scenario Scenario_state))

events :: Object -> [] Event_definition
events o =
  case o of {
   Build_object _ _ _ _ events0 _ _ _ _ _ _ -> events0}

scenarios :: Object -> [] Scenario
scenarios o =
  case o of {
   Build_object _ _ _ _ _ scenarios0 _ _ _ _ _ -> scenarios0}

stateEvStepMap' :: Object -> []
                   ((,) ((,) ((,) Scenario_state Event_instance) Scenario)
                   (Prelude.Maybe Step))
stateEvStepMap' o =
  case o of {
   Build_object _ _ _ _ _ _ _ stateEvStepMap'0 _ _ _ -> stateEvStepMap'0}

stateEvDefInstanceMap :: Object -> []
                         ((,)
                         ((,) (Prelude.Maybe Scenario_state)
                         (Prelude.Maybe Event_definition))
                         ([] Event_instance))
stateEvDefInstanceMap o =
  case o of {
   Build_object _ _ _ _ _ _ _ _ stateEvDefInstanceMap0 _ _ ->
    stateEvDefInstanceMap0}

data RaisedEvent =
   Build_raisedEvent Event_definition ([] Range_typ)

eventDefinition :: RaisedEvent -> Event_definition
eventDefinition r =
  case r of {
   Build_raisedEvent eventDefinition0 _ -> eventDefinition0}

eventArguments :: RaisedEvent -> [] Range_typ
eventArguments r =
  case r of {
   Build_raisedEvent _ eventArguments0 -> eventArguments0}

raisedEvent_dec :: RaisedEvent -> RaisedEvent -> Prelude.Bool
raisedEvent_dec n m =
  case n of {
   Build_raisedEvent eventDefinition0 eventArguments0 ->
    case m of {
     Build_raisedEvent eventDefinition1 eventArguments1 ->
      sumbool_rec (\_ ->
        sumbool_rec (\_ -> Prelude.True) (\_ -> Prelude.False)
          (list_rec (\x ->
            case x of {
             [] -> Prelude.True;
             (:) _ _ -> Prelude.False}) (\a0 _ h x ->
            case x of {
             [] -> Prelude.False;
             (:) r l0 ->
              sumbool_rec (\_ ->
                sumbool_rec (\_ -> Prelude.True) (\_ -> Prelude.False) (h l0))
                (\_ -> Prelude.False)
                (sum_rec (\a1 x0 ->
                  case x0 of {
                   Prelude.Left s ->
                    sumbool_rec (\_ -> Prelude.True) (\_ -> Prelude.False)
                      (sum_rec (\a2 x1 ->
                        case x1 of {
                         Prelude.Left s0 ->
                          sumbool_rec (\_ -> Prelude.True) (\_ ->
                            Prelude.False)
                            (sum_rec (\a3 x2 ->
                              case x2 of {
                               Prelude.Left s1 ->
                                sumbool_rec (\_ -> Prelude.True) (\_ ->
                                  Prelude.False)
                                  (sum_rec (\a4 x3 ->
                                    case x3 of {
                                     Prelude.Left z ->
                                      sumbool_rec (\_ -> Prelude.True) (\_ ->
                                        Prelude.False)
                                        (z_rec (\x4 ->
                                          (\fO fP fN n -> if n Prelude.== 0 then fO () else
                   if n Prelude.> 0 then fP n else fN (Prelude.negate n))
                                            (\_ -> Prelude.True)
                                            (\_ -> Prelude.False)
                                            (\_ -> Prelude.False)
                                            x4) (\p x4 ->
                                          (\fO fP fN n -> if n Prelude.== 0 then fO () else
                   if n Prelude.> 0 then fP n else fN (Prelude.negate n))
                                            (\_ -> Prelude.False)
                                            (\p0 ->
                                            sumbool_rec (\_ -> Prelude.True)
                                              (\_ -> Prelude.False)
                                              (positive_rec (\_ h0 x5 ->
                                                (\fI fO fH n -> if n Prelude.== 1 then fH () else
                   if Prelude.odd n then fI (n `Prelude.div` 2)
                                    else fO (n `Prelude.div` 2))
                                                  (\p2 ->
                                                  sumbool_rec (\_ ->
                                                    Prelude.True) (\_ ->
                                                    Prelude.False) (h0 p2))
                                                  (\_ -> Prelude.False)
                                                  (\_ -> Prelude.False)
                                                  x5) (\_ h0 x5 ->
                                                (\fI fO fH n -> if n Prelude.== 1 then fH () else
                   if Prelude.odd n then fI (n `Prelude.div` 2)
                                    else fO (n `Prelude.div` 2))
                                                  (\_ ->
                                                  Prelude.False)
                                                  (\p2 ->
                                                  sumbool_rec (\_ ->
                                                    Prelude.True) (\_ ->
                                                    Prelude.False) (h0 p2))
                                                  (\_ -> Prelude.False)
                                                  x5) (\x5 ->
                                                (\fI fO fH n -> if n Prelude.== 1 then fH () else
                   if Prelude.odd n then fI (n `Prelude.div` 2)
                                    else fO (n `Prelude.div` 2))
                                                  (\_ -> Prelude.False)
                                                  (\_ -> Prelude.False)
                                                  (\_ -> Prelude.True)
                                                  x5) p p0))
                                            (\_ -> Prelude.False)
                                            x4) (\p x4 ->
                                          (\fO fP fN n -> if n Prelude.== 0 then fO () else
                   if n Prelude.> 0 then fP n else fN (Prelude.negate n))
                                            (\_ -> Prelude.False)
                                            (\_ -> Prelude.False)
                                            (\p0 ->
                                            sumbool_rec (\_ -> Prelude.True)
                                              (\_ -> Prelude.False)
                                              (positive_rec (\_ h0 x5 ->
                                                (\fI fO fH n -> if n Prelude.== 1 then fH () else
                   if Prelude.odd n then fI (n `Prelude.div` 2)
                                    else fO (n `Prelude.div` 2))
                                                  (\p2 ->
                                                  sumbool_rec (\_ ->
                                                    Prelude.True) (\_ ->
                                                    Prelude.False) (h0 p2))
                                                  (\_ -> Prelude.False)
                                                  (\_ -> Prelude.False)
                                                  x5) (\_ h0 x5 ->
                                                (\fI fO fH n -> if n Prelude.== 1 then fH () else
                   if Prelude.odd n then fI (n `Prelude.div` 2)
                                    else fO (n `Prelude.div` 2))
                                                  (\_ ->
                                                  Prelude.False)
                                                  (\p2 ->
                                                  sumbool_rec (\_ ->
                                                    Prelude.True) (\_ ->
                                                    Prelude.False) (h0 p2))
                                                  (\_ -> Prelude.False)
                                                  x5) (\x5 ->
                                                (\fI fO fH n -> if n Prelude.== 1 then fH () else
                   if Prelude.odd n then fI (n `Prelude.div` 2)
                                    else fO (n `Prelude.div` 2))
                                                  (\_ -> Prelude.False)
                                                  (\_ -> Prelude.False)
                                                  (\_ -> Prelude.True)
                                                  x5) p p0))
                                            x4) a4 z);
                                     Prelude.Right _ -> Prelude.False})
                                    (\b x3 ->
                                    case x3 of {
                                     Prelude.Left _ -> Prelude.False;
                                     Prelude.Right q ->
                                      sumbool_rec (\_ -> Prelude.True) (\_ ->
                                        Prelude.False)
                                        (case b of {
                                          (GHC.Real.:%) qnum0 qden0 ->
                                           case q of {
                                            (GHC.Real.:%) qnum1 qden1 ->
                                             sumbool_rec (\_ ->
                                               sumbool_rec (\_ ->
                                                 Prelude.True) (\_ ->
                                                 Prelude.False)
                                                 (positive_rec (\_ h0 x4 ->
                                                   (\fI fO fH n -> if n Prelude.== 1 then fH () else
                   if Prelude.odd n then fI (n `Prelude.div` 2)
                                    else fO (n `Prelude.div` 2))
                                                     (\p0 ->
                                                     sumbool_rec (\_ ->
                                                       Prelude.True) (\_ ->
                                                       Prelude.False) 
                                                       (h0 p0))
                                                     (\_ ->
                                                     Prelude.False)
                                                     (\_ -> Prelude.False)
                                                     x4) (\_ h0 x4 ->
                                                   (\fI fO fH n -> if n Prelude.== 1 then fH () else
                   if Prelude.odd n then fI (n `Prelude.div` 2)
                                    else fO (n `Prelude.div` 2))
                                                     (\_ ->
                                                     Prelude.False)
                                                     (\p0 ->
                                                     sumbool_rec (\_ ->
                                                       Prelude.True) (\_ ->
                                                       Prelude.False) 
                                                       (h0 p0))
                                                     (\_ -> Prelude.False)
                                                     x4) (\x4 ->
                                                   (\fI fO fH n -> if n Prelude.== 1 then fH () else
                   if Prelude.odd n then fI (n `Prelude.div` 2)
                                    else fO (n `Prelude.div` 2))
                                                     (\_ ->
                                                     Prelude.False)
                                                     (\_ ->
                                                     Prelude.False)
                                                     (\_ -> Prelude.True)
                                                     x4) qden0 qden1)) (\_ ->
                                               Prelude.False)
                                               (z_rec (\x4 ->
                                                 (\fO fP fN n -> if n Prelude.== 0 then fO () else
                   if n Prelude.> 0 then fP n else fN (Prelude.negate n))
                                                   (\_ -> Prelude.True)
                                                   (\_ ->
                                                   Prelude.False)
                                                   (\_ -> Prelude.False)
                                                   x4) (\p x4 ->
                                                 (\fO fP fN n -> if n Prelude.== 0 then fO () else
                   if n Prelude.> 0 then fP n else fN (Prelude.negate n))
                                                   (\_ ->
                                                   Prelude.False)
                                                   (\p0 ->
                                                   sumbool_rec (\_ ->
                                                     Prelude.True) (\_ ->
                                                     Prelude.False)
                                                     (positive_rec
                                                       (\_ h0 x5 ->
                                                       (\fI fO fH n -> if n Prelude.== 1 then fH () else
                   if Prelude.odd n then fI (n `Prelude.div` 2)
                                    else fO (n `Prelude.div` 2))
                                                         (\p2 ->
                                                         sumbool_rec (\_ ->
                                                           Prelude.True)
                                                           (\_ ->
                                                           Prelude.False)
                                                           (h0 p2))
                                                         (\_ ->
                                                         Prelude.False)
                                                         (\_ ->
                                                         Prelude.False)
                                                         x5) (\_ h0 x5 ->
                                                       (\fI fO fH n -> if n Prelude.== 1 then fH () else
                   if Prelude.odd n then fI (n `Prelude.div` 2)
                                    else fO (n `Prelude.div` 2))
                                                         (\_ ->
                                                         Prelude.False)
                                                         (\p2 ->
                                                         sumbool_rec (\_ ->
                                                           Prelude.True)
                                                           (\_ ->
                                                           Prelude.False)
                                                           (h0 p2))
                                                         (\_ ->
                                                         Prelude.False)
                                                         x5) (\x5 ->
                                                       (\fI fO fH n -> if n Prelude.== 1 then fH () else
                   if Prelude.odd n then fI (n `Prelude.div` 2)
                                    else fO (n `Prelude.div` 2))
                                                         (\_ ->
                                                         Prelude.False)
                                                         (\_ ->
                                                         Prelude.False)
                                                         (\_ ->
                                                         Prelude.True)
                                                         x5) p p0))
                                                   (\_ -> Prelude.False)
                                                   x4) (\p x4 ->
                                                 (\fO fP fN n -> if n Prelude.== 0 then fO () else
                   if n Prelude.> 0 then fP n else fN (Prelude.negate n))
                                                   (\_ ->
                                                   Prelude.False)
                                                   (\_ ->
                                                   Prelude.False)
                                                   (\p0 ->
                                                   sumbool_rec (\_ ->
                                                     Prelude.True) (\_ ->
                                                     Prelude.False)
                                                     (positive_rec
                                                       (\_ h0 x5 ->
                                                       (\fI fO fH n -> if n Prelude.== 1 then fH () else
                   if Prelude.odd n then fI (n `Prelude.div` 2)
                                    else fO (n `Prelude.div` 2))
                                                         (\p2 ->
                                                         sumbool_rec (\_ ->
                                                           Prelude.True)
                                                           (\_ ->
                                                           Prelude.False)
                                                           (h0 p2))
                                                         (\_ ->
                                                         Prelude.False)
                                                         (\_ ->
                                                         Prelude.False)
                                                         x5) (\_ h0 x5 ->
                                                       (\fI fO fH n -> if n Prelude.== 1 then fH () else
                   if Prelude.odd n then fI (n `Prelude.div` 2)
                                    else fO (n `Prelude.div` 2))
                                                         (\_ ->
                                                         Prelude.False)
                                                         (\p2 ->
                                                         sumbool_rec (\_ ->
                                                           Prelude.True)
                                                           (\_ ->
                                                           Prelude.False)
                                                           (h0 p2))
                                                         (\_ ->
                                                         Prelude.False)
                                                         x5) (\x5 ->
                                                       (\fI fO fH n -> if n Prelude.== 1 then fH () else
                   if Prelude.odd n then fI (n `Prelude.div` 2)
                                    else fO (n `Prelude.div` 2))
                                                         (\_ ->
                                                         Prelude.False)
                                                         (\_ ->
                                                         Prelude.False)
                                                         (\_ ->
                                                         Prelude.True)
                                                         x5) p p0))
                                                   x4) qnum0 qnum1)}})}) a3
                                    s1);
                               Prelude.Right _ -> Prelude.False}) (\b x2 ->
                              case x2 of {
                               Prelude.Left _ -> Prelude.False;
                               Prelude.Right s1 ->
                                sumbool_rec (\_ -> Prelude.True) (\_ ->
                                  Prelude.False)
                                  (string_rec (\x3 ->
                                    case x3 of {
                                     [] -> Prelude.True;
                                     (:) _ _ -> Prelude.False})
                                    (\a3 _ h0 x3 ->
                                    case x3 of {
                                     [] -> Prelude.False;
                                     (:) a4 s3 ->
                                      sumbool_rec (\_ ->
                                        sumbool_rec (\_ -> Prelude.True)
                                          (\_ -> Prelude.False) (h0 s3))
                                        (\_ -> Prelude.False)
                                        (ascii_rec
                                          (\b0 b1 b2 b3 b4 b5 b6 b7 x4 ->
                                          HString.foldChar
                                            (\b8 b9 b10 b11 b12 b13 b14 b15 ->
                                            sumbool_rec (\_ ->
                                              sumbool_rec (\_ ->
                                                sumbool_rec (\_ ->
                                                  sumbool_rec (\_ ->
                                                    sumbool_rec (\_ ->
                                                      sumbool_rec (\_ ->
                                                        sumbool_rec (\_ ->
                                                          sumbool_rec (\_ ->
                                                            Prelude.True)
                                                            (\_ ->
                                                            Prelude.False)
                                                            (bool_rec (\x5 ->
                                                              case x5 of {
                                                               Prelude.True ->
                                                                Prelude.True;
                                                               Prelude.False ->
                                                                Prelude.False})
                                                              (\x5 ->
                                                              case x5 of {
                                                               Prelude.True ->
                                                                Prelude.False;
                                                               Prelude.False ->
                                                                Prelude.True})
                                                              b7 b15)) (\_ ->
                                                          Prelude.False)
                                                          (bool_rec (\x5 ->
                                                            case x5 of {
                                                             Prelude.True ->
                                                              Prelude.True;
                                                             Prelude.False ->
                                                              Prelude.False})
                                                            (\x5 ->
                                                            case x5 of {
                                                             Prelude.True ->
                                                              Prelude.False;
                                                             Prelude.False ->
                                                              Prelude.True})
                                                            b6 b14)) (\_ ->
                                                        Prelude.False)
                                                        (bool_rec (\x5 ->
                                                          case x5 of {
                                                           Prelude.True ->
                                                            Prelude.True;
                                                           Prelude.False ->
                                                            Prelude.False})
                                                          (\x5 ->
                                                          case x5 of {
                                                           Prelude.True ->
                                                            Prelude.False;
                                                           Prelude.False ->
                                                            Prelude.True}) b5
                                                          b13)) (\_ ->
                                                      Prelude.False)
                                                      (bool_rec (\x5 ->
                                                        case x5 of {
                                                         Prelude.True ->
                                                          Prelude.True;
                                                         Prelude.False ->
                                                          Prelude.False})
                                                        (\x5 ->
                                                        case x5 of {
                                                         Prelude.True ->
                                                          Prelude.False;
                                                         Prelude.False ->
                                                          Prelude.True}) b4
                                                        b12)) (\_ ->
                                                    Prelude.False)
                                                    (bool_rec (\x5 ->
                                                      case x5 of {
                                                       Prelude.True ->
                                                        Prelude.True;
                                                       Prelude.False ->
                                                        Prelude.False})
                                                      (\x5 ->
                                                      case x5 of {
                                                       Prelude.True ->
                                                        Prelude.False;
                                                       Prelude.False ->
                                                        Prelude.True}) b3
                                                      b11)) (\_ ->
                                                  Prelude.False)
                                                  (bool_rec (\x5 ->
                                                    case x5 of {
                                                     Prelude.True ->
                                                      Prelude.True;
                                                     Prelude.False ->
                                                      Prelude.False}) (\x5 ->
                                                    case x5 of {
                                                     Prelude.True ->
                                                      Prelude.False;
                                                     Prelude.False ->
                                                      Prelude.True}) b2 b10))
                                                (\_ -> Prelude.False)
                                                (bool_rec (\x5 ->
                                                  case x5 of {
                                                   Prelude.True ->
                                                    Prelude.True;
                                                   Prelude.False ->
                                                    Prelude.False}) (\x5 ->
                                                  case x5 of {
                                                   Prelude.True ->
                                                    Prelude.False;
                                                   Prelude.False ->
                                                    Prelude.True}) b1 b9))
                                              (\_ -> Prelude.False)
                                              (bool_rec (\x5 ->
                                                case x5 of {
                                                 Prelude.True -> Prelude.True;
                                                 Prelude.False ->
                                                  Prelude.False}) (\x5 ->
                                                case x5 of {
                                                 Prelude.True ->
                                                  Prelude.False;
                                                 Prelude.False ->
                                                  Prelude.True}) b0 b8))
                                            x4) a3 a4)}) b s1)}) a2 s0);
                         Prelude.Right _ -> Prelude.False}) (\b x1 ->
                        case x1 of {
                         Prelude.Left _ -> Prelude.False;
                         Prelude.Right b0 ->
                          sumbool_rec (\_ -> Prelude.True) (\_ ->
                            Prelude.False)
                            (bool_rec (\x2 ->
                              case x2 of {
                               Prelude.True -> Prelude.True;
                               Prelude.False -> Prelude.False}) (\x2 ->
                              case x2 of {
                               Prelude.True -> Prelude.False;
                               Prelude.False -> Prelude.True}) b b0)}) a1 s);
                   Prelude.Right _ -> Prelude.False}) (\b x0 ->
                  case x0 of {
                   Prelude.Left _ -> Prelude.False;
                   Prelude.Right n0 ->
                    sumbool_rec (\_ -> Prelude.True) (\_ -> Prelude.False)
                      (nat_rec (\x1 ->
                        (\fO fS n -> if n Prelude.<= 0 then fO () else fS (Prelude.pred n))
                          (\_ -> Prelude.True)
                          (\_ -> Prelude.False)
                          x1) (\_ h0 x1 ->
                        (\fO fS n -> if n Prelude.<= 0 then fO () else fS (Prelude.pred n))
                          (\_ -> Prelude.False)
                          (\n2 ->
                          sumbool_rec (\_ -> Prelude.True) (\_ ->
                            Prelude.False) (h0 n2))
                          x1) b n0)}) a0 r)}) eventArguments0
            eventArguments1)) (\_ -> Prelude.False)
        (case eventDefinition0 of {
          Build_event_definition eventKind0 eventId0 eventParams0 ->
           case eventDefinition1 of {
            Build_event_definition eventKind1 eventId1 eventParams1 ->
             sumbool_rec (\_ ->
               sumbool_rec (\_ ->
                 sumbool_rec (\_ -> Prelude.True) (\_ -> Prelude.False)
                   (list_rec (\x ->
                     case x of {
                      [] -> Prelude.True;
                      (:) _ _ -> Prelude.False}) (\a1 _ h x ->
                     case x of {
                      [] -> Prelude.False;
                      (:) t l0 ->
                       sumbool_rec (\_ ->
                         sumbool_rec (\_ -> Prelude.True) (\_ ->
                           Prelude.False) (h l0)) (\_ -> Prelude.False)
                         (typ_rec (\x0 ->
                           case x0 of {
                            Int -> Prelude.True;
                            _ -> Prelude.False}) (\x0 ->
                           case x0 of {
                            Float -> Prelude.True;
                            _ -> Prelude.False}) (\x0 ->
                           case x0 of {
                            Str -> Prelude.True;
                            _ -> Prelude.False}) (\x0 ->
                           case x0 of {
                            Bool -> Prelude.True;
                            _ -> Prelude.False}) (\x0 ->
                           case x0 of {
                            Pointer -> Prelude.True;
                            _ -> Prelude.False}) (\x0 ->
                           case x0 of {
                            Opaque -> Prelude.True;
                            _ -> Prelude.False}) (\x0 ->
                           case x0 of {
                            Thread -> Prelude.True;
                            _ -> Prelude.False}) a1 t)}) eventParams0
                     eventParams1)) (\_ -> Prelude.False)
                 (string_rec (\x ->
                   case x of {
                    [] -> Prelude.True;
                    (:) _ _ -> Prelude.False}) (\a0 _ h x ->
                   case x of {
                    [] -> Prelude.False;
                    (:) a1 s0 ->
                     sumbool_rec (\_ ->
                       sumbool_rec (\_ -> Prelude.True) (\_ -> Prelude.False)
                         (h s0)) (\_ -> Prelude.False)
                       (ascii_rec (\b b0 b1 b2 b3 b4 b5 b6 x0 ->
                         HString.foldChar
                           (\b7 b8 b9 b10 b11 b12 b13 b14 ->
                           sumbool_rec (\_ ->
                             sumbool_rec (\_ ->
                               sumbool_rec (\_ ->
                                 sumbool_rec (\_ ->
                                   sumbool_rec (\_ ->
                                     sumbool_rec (\_ ->
                                       sumbool_rec (\_ ->
                                         sumbool_rec (\_ -> Prelude.True)
                                           (\_ -> Prelude.False)
                                           (bool_rec (\x1 ->
                                             case x1 of {
                                              Prelude.True -> Prelude.True;
                                              Prelude.False -> Prelude.False})
                                             (\x1 ->
                                             case x1 of {
                                              Prelude.True -> Prelude.False;
                                              Prelude.False -> Prelude.True})
                                             b6 b14)) (\_ -> Prelude.False)
                                         (bool_rec (\x1 ->
                                           case x1 of {
                                            Prelude.True -> Prelude.True;
                                            Prelude.False -> Prelude.False})
                                           (\x1 ->
                                           case x1 of {
                                            Prelude.True -> Prelude.False;
                                            Prelude.False -> Prelude.True})
                                           b5 b13)) (\_ -> Prelude.False)
                                       (bool_rec (\x1 ->
                                         case x1 of {
                                          Prelude.True -> Prelude.True;
                                          Prelude.False -> Prelude.False})
                                         (\x1 ->
                                         case x1 of {
                                          Prelude.True -> Prelude.False;
                                          Prelude.False -> Prelude.True}) b4
                                         b12)) (\_ -> Prelude.False)
                                     (bool_rec (\x1 ->
                                       case x1 of {
                                        Prelude.True -> Prelude.True;
                                        Prelude.False -> Prelude.False})
                                       (\x1 ->
                                       case x1 of {
                                        Prelude.True -> Prelude.False;
                                        Prelude.False -> Prelude.True}) b3
                                       b11)) (\_ -> Prelude.False)
                                   (bool_rec (\x1 ->
                                     case x1 of {
                                      Prelude.True -> Prelude.True;
                                      Prelude.False -> Prelude.False})
                                     (\x1 ->
                                     case x1 of {
                                      Prelude.True -> Prelude.False;
                                      Prelude.False -> Prelude.True}) b2 b10))
                                 (\_ -> Prelude.False)
                                 (bool_rec (\x1 ->
                                   case x1 of {
                                    Prelude.True -> Prelude.True;
                                    Prelude.False -> Prelude.False}) (\x1 ->
                                   case x1 of {
                                    Prelude.True -> Prelude.False;
                                    Prelude.False -> Prelude.True}) b1 b9))
                               (\_ -> Prelude.False)
                               (bool_rec (\x1 ->
                                 case x1 of {
                                  Prelude.True -> Prelude.True;
                                  Prelude.False -> Prelude.False}) (\x1 ->
                                 case x1 of {
                                  Prelude.True -> Prelude.False;
                                  Prelude.False -> Prelude.True}) b0 b8))
                             (\_ -> Prelude.False)
                             (bool_rec (\x1 ->
                               case x1 of {
                                Prelude.True -> Prelude.True;
                                Prelude.False -> Prelude.False}) (\x1 ->
                               case x1 of {
                                Prelude.True -> Prelude.False;
                                Prelude.False -> Prelude.True}) b b7))
                           x0) a0 a1)}) eventId0 eventId1)) (\_ ->
               Prelude.False)
               (eventKind_rec (\x ->
                 case x of {
                  Internal -> Prelude.True;
                  _ -> Prelude.False}) (\x ->
                 case x of {
                  Imported -> Prelude.True;
                  _ -> Prelude.False}) (\x ->
                 case x of {
                  Exported -> Prelude.True;
                  _ -> Prelude.False}) eventKind0 eventKind1)}})}}

bind :: (ErrorOrResult a1) -> (a1 -> ErrorOrResult a1) -> ErrorOrResult a1
bind val func =
  case val of {
   Result v -> func v;
   Error err -> Error err}

bindZ :: (ErrorOrResult Range_typ) -> (Prelude.Int -> ErrorOrResult
         Range_typ) -> ErrorOrResult Range_typ
bindZ val func =
  bind val (\v ->
    case v of {
     Prelude.Left s ->
      case s of {
       Prelude.Left s0 ->
        case s0 of {
         Prelude.Left s1 ->
          case s1 of {
           Prelude.Left n -> func n;
           Prelude.Right _ -> Error typeErr};
         Prelude.Right _ -> Error typeErr};
       Prelude.Right _ -> Error typeErr};
     Prelude.Right _ -> Error typeErr})

bindNum :: (ErrorOrResult Range_typ) -> ((Prelude.Either Prelude.Int
           (GHC.Real.Ratio Prelude.Int)) -> ErrorOrResult Range_typ) ->
           ErrorOrResult Range_typ
bindNum val func =
  bind val (\v ->
    case v of {
     Prelude.Left s ->
      case s of {
       Prelude.Left s0 ->
        case s0 of {
         Prelude.Left s1 ->
          case s1 of {
           Prelude.Left n -> func (Prelude.Left n);
           Prelude.Right q -> func (Prelude.Right q)};
         Prelude.Right _ -> Error typeErr};
       Prelude.Right _ -> Error typeErr};
     Prelude.Right _ -> Error typeErr})

bindBool :: (ErrorOrResult Range_typ) -> (Prelude.Bool -> ErrorOrResult
            Range_typ) -> ErrorOrResult Range_typ
bindBool val func =
  bind val (\v ->
    case v of {
     Prelude.Left s ->
      case s of {
       Prelude.Left _ -> Error typeErr;
       Prelude.Right b -> func b};
     Prelude.Right _ -> Error typeErr})

bindData :: (ErrorOrResult Range_typ) -> (Range_typ -> ErrorOrResult
            Range_typ) -> ErrorOrResult Range_typ
bindData =
  bind

evalMonad :: Value_env -> Expr -> ErrorOrResult Range_typ
evalMonad env e =
  case e of {
   EOr x y ->
    bindBool (evalMonad env x) (\b1 ->
      bindBool (evalMonad env y) (\b2 -> Result (Prelude.Left (Prelude.Right
        ((Prelude.||) b1 b2)))));
   EAnd x y ->
    bindBool (evalMonad env x) (\b1 ->
      bindBool (evalMonad env y) (\b2 -> Result (Prelude.Left (Prelude.Right
        ((Prelude.&&) b1 b2)))));
   EEq x y ->
    bindData (evalMonad env x) (\n1 ->
      bindData (evalMonad env y) (\n2 ->
        case n1 of {
         Prelude.Left s ->
          case s of {
           Prelude.Left s0 ->
            case s0 of {
             Prelude.Left s1 ->
              case s1 of {
               Prelude.Left i ->
                case n2 of {
                 Prelude.Left s2 ->
                  case s2 of {
                   Prelude.Left s3 ->
                    case s3 of {
                     Prelude.Left s4 ->
                      case s4 of {
                       Prelude.Left j -> Result (Prelude.Left (Prelude.Right
                        (eqb1 i j)));
                       Prelude.Right _ -> Error typeErr};
                     Prelude.Right _ -> Error typeErr};
                   Prelude.Right _ -> Error typeErr};
                 Prelude.Right _ -> Error typeErr};
               Prelude.Right p ->
                case n2 of {
                 Prelude.Left s2 ->
                  case s2 of {
                   Prelude.Left s3 ->
                    case s3 of {
                     Prelude.Left s4 ->
                      case s4 of {
                       Prelude.Left _ -> Error typeErr;
                       Prelude.Right q -> Result (Prelude.Left (Prelude.Right
                        (qeq_bool p q)))};
                     Prelude.Right _ -> Error typeErr};
                   Prelude.Right _ -> Error typeErr};
                 Prelude.Right _ -> Error typeErr}};
             Prelude.Right s1 ->
              case n2 of {
               Prelude.Left s2 ->
                case s2 of {
                 Prelude.Left s3 ->
                  case s3 of {
                   Prelude.Left _ -> Error typeErr;
                   Prelude.Right s4 -> Result (Prelude.Left (Prelude.Right
                    (string_dec_bool s1 s4)))};
                 Prelude.Right _ -> Error typeErr};
               Prelude.Right _ -> Error typeErr}};
           Prelude.Right s1 ->
            case n2 of {
             Prelude.Left s0 ->
              case s0 of {
               Prelude.Left _ -> Error typeErr;
               Prelude.Right s2 -> Result (Prelude.Left (Prelude.Right
                (eqb s1 s2)))};
             Prelude.Right _ -> Error typeErr}};
         Prelude.Right s1 ->
          case n2 of {
           Prelude.Left _ -> Error typeErr;
           Prelude.Right s2 -> Result (Prelude.Left (Prelude.Right
            (((Prelude.==) :: Prelude.Int -> Prelude.Int -> Prelude.Bool) s1
              s2)))}}));
   ELt x y ->
    bindNum (evalMonad env x) (\n1 ->
      bindNum (evalMonad env y) (\n2 ->
        case n1 of {
         Prelude.Left i ->
          case n2 of {
           Prelude.Left j -> Result (Prelude.Left (Prelude.Right (ltb i j)));
           Prelude.Right _ -> Error typeErr};
         Prelude.Right p ->
          case n2 of {
           Prelude.Left _ -> Error typeErr;
           Prelude.Right q -> Result (Prelude.Left (Prelude.Right
            ((Prelude.&&) (qle_bool p q) (Prelude.not (qeq_bool p q)))))}}));
   ELe x y ->
    bindNum (evalMonad env x) (\n1 ->
      bindNum (evalMonad env y) (\n2 ->
        case n1 of {
         Prelude.Left i ->
          case n2 of {
           Prelude.Left j -> Result (Prelude.Left (Prelude.Right (leb i j)));
           Prelude.Right _ -> Error typeErr};
         Prelude.Right p ->
          case n2 of {
           Prelude.Left _ -> Error typeErr;
           Prelude.Right q -> Result (Prelude.Left (Prelude.Right
            (qle_bool p q)))}}));
   EPlus x y ->
    bindNum (evalMonad env x) (\n1 ->
      bindNum (evalMonad env y) (\n2 ->
        case n1 of {
         Prelude.Left i ->
          case n2 of {
           Prelude.Left j -> Result (Prelude.Left (Prelude.Left (Prelude.Left
            (Prelude.Left ((Prelude.+) i j)))));
           Prelude.Right _ -> Error typeErr};
         Prelude.Right p ->
          case n2 of {
           Prelude.Left _ -> Error typeErr;
           Prelude.Right q -> Result (Prelude.Left (Prelude.Left
            (Prelude.Left (Prelude.Right ((Prelude.+) p q)))))}}));
   EMult x y ->
    bindNum (evalMonad env x) (\n1 ->
      bindNum (evalMonad env y) (\n2 ->
        case n1 of {
         Prelude.Left i ->
          case n2 of {
           Prelude.Left j -> Result (Prelude.Left (Prelude.Left (Prelude.Left
            (Prelude.Left ((Prelude.*) i j)))));
           Prelude.Right _ -> Error typeErr};
         Prelude.Right p ->
          case n2 of {
           Prelude.Left _ -> Error typeErr;
           Prelude.Right q -> Result (Prelude.Left (Prelude.Left
            (Prelude.Left (Prelude.Right ((Prelude.*) p q)))))}}));
   EDiv x y ->
    bindNum (evalMonad env x) (\n1 ->
      bindNum (evalMonad env y) (\n2 ->
        case n1 of {
         Prelude.Left i ->
          case n2 of {
           Prelude.Left j -> Result (Prelude.Left (Prelude.Left (Prelude.Left
            (Prelude.Left (div i j)))));
           Prelude.Right _ -> Error typeErr};
         Prelude.Right p ->
          case n2 of {
           Prelude.Left _ -> Error typeErr;
           Prelude.Right q -> Result (Prelude.Left (Prelude.Left
            (Prelude.Left (Prelude.Right (qdiv p q)))))}}));
   EMod x y ->
    bindZ (evalMonad env x) (\n1 ->
      bindZ (evalMonad env y) (\n2 -> Result (Prelude.Left (Prelude.Left
        (Prelude.Left (Prelude.Left (modulo n1 n2)))))));
   ENot x ->
    bindBool (evalMonad env x) (\b1 -> Result (Prelude.Left (Prelude.Right
      (Prelude.not b1))));
   EAtom x ->
    case x of {
     AInt z -> Result (Prelude.Left (Prelude.Left (Prelude.Left (Prelude.Left
      z))));
     AFloat q -> Result (Prelude.Left (Prelude.Left (Prelude.Left
      (Prelude.Right q))));
     AIdent i ->
      case getValue (AIdent i) env of {
       Prelude.Just r -> Result r;
       Prelude.Nothing -> Error typeErr};
     ABool b -> Result (Prelude.Left (Prelude.Right b));
     ANull -> Result (Prelude.Right (0 :: Prelude.Int));
     AString s -> Result (Prelude.Left (Prelude.Left (Prelude.Right s)))}}

calculateExprList :: Value_env -> ([] Expr) -> ErrorOrResult ([] Range_typ)
calculateExprList en lst =
  case lst of {
   [] -> Result [];
   (:) ex lst' ->
    case evalMonad en ex of {
     Result v ->
      case calculateExprList en lst' of {
       Result vlst -> Result ((:) v vlst);
       Error s -> Error s};
     Error error -> Error error}}

getEventByName :: Prelude.String -> ([] Event_definition) -> Prelude.Maybe
                  Event_definition
getEventByName name elist =
  case elist of {
   [] -> Prelude.Nothing;
   (:) e lst' ->
    case string_dec (eventId e) name of {
     Prelude.True -> Prelude.Just e;
     Prelude.False -> getEventByName name lst'}}

parameterMatchFunc :: ([] Range_typ) -> ([] Typ) -> Prelude.Bool
parameterMatchFunc rl tl =
  case rl of {
   [] -> case tl of {
          [] -> Prelude.True;
          (:) _ _ -> Prelude.False};
   (:) rt rlst ->
    case tl of {
     [] -> Prelude.False;
     (:) t tlst ->
      case typeValMatch t rt of {
       Prelude.True -> parameterMatchFunc rlst tlst;
       Prelude.False -> Prelude.False}}}

execAction :: ((,) Value_env ([] RaisedEvent)) -> Action -> ([]
              Event_definition) -> ErrorOrResult
              ((,) Value_env ([] RaisedEvent))
execAction etaE a eventList =
  case a of {
   Skip -> Result etaE;
   StateUpdate l ex ->
    case l of {
     AIdent s ->
      let {er = evalMonad (Prelude.fst etaE) ex} in
      case er of {
       Result v ->
        case updateValueEnvInv (AIdent s) v (Prelude.fst etaE) of {
         Prelude.Just ven -> Result ((,) ven (Prelude.snd etaE));
         Prelude.Nothing -> Error typeErr};
       Error r -> Error r};
     _ -> Error typeErr};
   RaiseStmt n lst ->
    let {vlist = calculateExprList (Prelude.fst etaE) lst} in
    case vlist of {
     Result vlist' ->
      let {event = getEventByName n eventList} in
      case event of {
       Prelude.Just ev ->
        case parameterMatchFunc vlist' (eventParams ev) of {
         Prelude.True -> Result ((,) (Prelude.fst etaE)
          ((Prelude.++) ((:) (Build_raisedEvent ev vlist') [])
            (Prelude.snd etaE)));
         Prelude.False -> Error typeErr};
       Prelude.Nothing -> Error eventNotDeclaredErr};
     Error s -> Error s};
   Seq a1 a2 ->
    let {r1 = execAction etaE a1 eventList} in
    case r1 of {
     Result re1 -> execAction re1 a2 eventList;
     Error r -> Error r}}

error1 :: Prelude.String
error1 =
  (:) 'n' ((:) 'o' ((:) ' ' ((:) 's' ((:) 'c' ((:) 'e' ((:) 'n' ((:) 'a' ((:)
    'r' ((:) 'i' ((:) 'o' ((:) ' ' ((:) 's' ((:) 't' ((:) 'a' ((:) 't' ((:)
    'e' ((:) ' ' ((:) 's' ((:) 'p' ((:) 'e' ((:) 'c' ((:) 'i' ((:) 'f' ((:)
    'i' ((:) 'e' ((:) 'd' []))))))))))))))))))))))))))

error3 :: Prelude.String
error3 =
  (:) 'n' ((:) 'o' ((:) ' ' ((:) 'e' ((:) 'v' ((:) 'e' ((:) 'n' ((:) 't' ((:)
    ' ' ((:) 'i' ((:) 'n' ((:) 's' ((:) 't' ((:) 'a' ((:) 'n' ((:) 'c' ((:)
    'e' []))))))))))))))))

error4 :: Prelude.String
error4 =
  (:) 'n' ((:) 'o' ((:) ' ' ((:) 's' ((:) 't' ((:) 'e' ((:) 'p' []))))))

error5 :: Prelude.String
error5 =
  (:) 't' ((:) 'y' ((:) 'p' ((:) 'e' ((:) ' ' ((:) 'n' ((:) 'o' ((:) 't' ((:)
    ' ' ((:) 'm' ((:) 'a' ((:) 't' ((:) 'c' ((:) 'h' ((:) 'e' ((:) 'd'
    [])))))))))))))))

error6 :: Prelude.String
error6 =
  (:) 'n' ((:) 'o' ((:) 't' ((:) ' ' ((:) 'm' ((:) 'a' ((:) 't' ((:) 'c' ((:)
    'h' ((:) 'e' ((:) 'd' []))))))))))

error7 :: Prelude.String
error7 =
  (:) 's' ((:) 'c' ((:) 'e' ((:) 'n' ((:) 'a' ((:) 'r' ((:) 'i' ((:) 'o' ((:)
    ' ' ((:) 'n' ((:) 'o' ((:) 't' ((:) ' ' ((:) 'm' ((:) 'a' ((:) 't' ((:)
    'c' ((:) 'h' ((:) 'e' ((:) 'd' [])))))))))))))))))))

error11 :: Prelude.String
error11 =
  (:) 'd' ((:) 'a' ((:) 't' ((:) 'a' ((:) ' ' ((:) 'n' ((:) 'o' ((:) 'n' ((:)
    '-' ((:) 'd' ((:) 'e' ((:) 't' ((:) 'e' ((:) 'r' ((:) 'm' ((:) 'i' ((:)
    'n' ((:) 'i' ((:) 's' ((:) 'm' [])))))))))))))))))))

error12 :: Prelude.String
error12 =
  (:) 'n' ((:) 'u' ((:) 'm' ((:) 'b' ((:) 'e' ((:) 'r' ((:) ' ' ((:) 'o' ((:)
    'f' ((:) ' ' ((:) 'l' ((:) 'i' ((:) 's' ((:) 't' ((:) ' ' ((:) 'n' ((:)
    'o' ((:) 't' ((:) ' ' ((:) 'm' ((:) 'a' ((:) 't' ((:) 'c' ((:) 'h' ((:)
    'e' ((:) 'd' [])))))))))))))))))))))))))

error13 :: Prelude.String
error13 =
  (:) 'd' ((:) 'a' ((:) 't' ((:) 'a' ((:) ' ' ((:) 'c' ((:) 'o' ((:) 'n' ((:)
    'f' ((:) 'l' ((:) 'i' ((:) 'c' ((:) 't' []))))))))))))

error14 :: Prelude.String
error14 =
  (:) 'c' ((:) 'o' ((:) 'n' ((:) 't' ((:) 'r' ((:) 'o' ((:) 'l' ((:) ' ' ((:)
    'c' ((:) 'o' ((:) 'n' ((:) 'f' ((:) 'l' ((:) 'i' ((:) 'c' ((:) 't'
    [])))))))))))))))

type Monitor = Object

data Configuration =
   Build_configuration Value_env Scenario_env ([] RaisedEvent) ([]
                                                               RaisedEvent) 
 ([] Scenario) ([] ((,) Scenario Event_definition))

datastate :: Monitor -> Configuration -> Value_env
datastate _ c =
  case c of {
   Build_configuration datastate0 _ _ _ _ _ -> datastate0}

controlstate :: Monitor -> Configuration -> Scenario_env
controlstate _ c =
  case c of {
   Build_configuration _ controlstate0 _ _ _ _ -> controlstate0}

raisedevents :: Monitor -> Configuration -> [] RaisedEvent
raisedevents _ c =
  case c of {
   Build_configuration _ _ raisedevents0 _ _ _ -> raisedevents0}

exportedevents :: Monitor -> Configuration -> [] RaisedEvent
exportedevents _ c =
  case c of {
   Build_configuration _ _ _ exportedevents0 _ _ -> exportedevents0}

finishedscenarios :: Monitor -> Configuration -> [] Scenario
finishedscenarios _ c =
  case c of {
   Build_configuration _ _ _ _ finishedscenarios0 _ -> finishedscenarios0}

sceEventMap :: Monitor -> Configuration -> [] ((,) Scenario Event_definition)
sceEventMap _ c =
  case c of {
   Build_configuration _ _ _ _ _ sceEventMap0 -> sceEventMap0}

importEventBool :: Event_definition -> Prelude.Bool
importEventBool ev =
  case eventKind_dec (eventKind ev) Imported of {
   Prelude.True -> Prelude.True;
   Prelude.False -> Prelude.False}

op_string_dec :: (Prelude.Maybe Prelude.String) -> (Prelude.Maybe
                 Prelude.String) -> Prelude.Bool
op_string_dec n m =
  case n of {
   Prelude.Just s ->
    case m of {
     Prelude.Just s0 -> string_dec s s0;
     Prelude.Nothing -> Prelude.False};
   Prelude.Nothing ->
    case m of {
     Prelude.Just _ -> Prelude.False;
     Prelude.Nothing -> Prelude.True}}

op_event_definition_dec :: (Prelude.Maybe Event_definition) -> (Prelude.Maybe
                           Event_definition) -> Prelude.Bool
op_event_definition_dec n m =
  case n of {
   Prelude.Just e ->
    case m of {
     Prelude.Just e0 -> event_definition_dec e e0;
     Prelude.Nothing -> Prelude.False};
   Prelude.Nothing ->
    case m of {
     Prelude.Just _ -> Prelude.False;
     Prelude.Nothing -> Prelude.True}}

transEvMapFunc :: ([]
                  ((,)
                  ((,) (Prelude.Maybe Scenario_state)
                  (Prelude.Maybe Event_definition)) ([] Event_instance))) ->
                  ((,) (Prelude.Maybe Scenario_state)
                  (Prelude.Maybe Event_definition)) -> Prelude.Maybe
                  ([] Event_instance)
transEvMapFunc l f =
  case l of {
   [] -> Prelude.Nothing;
   (:) p l' ->
    case p of {
     (,) p0 c ->
      case p0 of {
       (,) a b ->
        case op_string_dec a (Prelude.fst f) of {
         Prelude.True ->
          case op_event_definition_dec b (Prelude.snd f) of {
           Prelude.True -> Prelude.Just c;
           Prelude.False -> transEvMapFunc l' f};
         Prelude.False -> transEvMapFunc l' f}}}}

op_stpMap_dec :: ((,) ((,) Scenario_state Event_instance) Scenario) -> ((,)
                 ((,) Scenario_state Event_instance) Scenario) ->
                 Prelude.Bool
op_stpMap_dec n m =
  case n of {
   (,) p s ->
    case m of {
     (,) p0 s0 ->
      case p of {
       (,) s1 e ->
        case p0 of {
         (,) s2 e0 ->
          let {s3 = string_dec s1 s2} in
          case s3 of {
           Prelude.True ->
            let {s4 = event_instance_dec e e0} in
            case s4 of {
             Prelude.True -> scenario_dec s s0;
             Prelude.False -> Prelude.False};
           Prelude.False -> Prelude.False}}}}}

stpStpMapFunc :: ([]
                 ((,) ((,) ((,) Scenario_state Event_instance) Scenario)
                 (Prelude.Maybe Step))) -> ((,)
                 ((,) Scenario_state Event_instance) Scenario) ->
                 Prelude.Maybe Step
stpStpMapFunc l f =
  case l of {
   [] -> Prelude.Nothing;
   (:) p l' ->
    case p of {
     (,) a d ->
      case op_stpMap_dec a f of {
       Prelude.True -> d;
       Prelude.False -> stpStpMapFunc l' f}}}

getStep' :: Monitor -> Configuration -> Scenario -> Event_instance ->
            Prelude.Maybe Step
getStep' m conf sce e =
  case getScenarioState sce (controlstate m conf) of {
   Prelude.Just s -> stpStpMapFunc (stateEvStepMap' m) ((,) ((,) s e) sce);
   Prelude.Nothing -> Prelude.Nothing}

updateDataState :: Value_env -> ([] Atom) -> Value_env
updateDataState ven lst =
  case ven of {
   [] -> [];
   (:) p ven' ->
    case p of {
     (,) a v ->
      case inList atom_eq_dec a lst of {
       Prelude.True -> (:) ((,) a v) (updateDataState ven' lst);
       Prelude.False -> updateDataState ven' lst}}}

updateControlState :: Scenario_env -> Scenario -> Step -> Scenario_env
updateControlState cs0 sce stp =
  updateScenarioState' sce (pro_state stp) cs0

removeEvent' :: RaisedEvent -> ([] RaisedEvent) -> [] RaisedEvent
removeEvent' re lst =
  case lst of {
   [] -> [];
   (:) re' lst' ->
    case raisedEvent_dec re re' of {
     Prelude.True -> removeEvent' re lst';
     Prelude.False -> (:) re' (removeEvent' re lst')}}

configTransition :: Value_env -> RaisedEvent -> Event_instance -> Scenario ->
                    Step -> Monitor -> Configuration -> ErrorOrResult
                    Configuration
configTransition env re _ sce stp m conf =
  case execAction ((,) env []) (stepActions stp)
         (filter (\e ->
           case eventKind e of {
            Imported -> Prelude.False;
            _ -> Prelude.True}) (events m)) of {
   Result v ->
    case v of {
     (,) ds' res ->
      let {ds'' = updateDataState ds' (dom (datastate m conf))} in
      Result (Build_configuration ds''
      (updateControlState (controlstate m conf) sce stp)
      (filter (\re0 ->
        eventKind_beq (eventKind (eventDefinition re0)) Internal) res)
      (filter (\re0 ->
        eventKind_beq (eventKind (eventDefinition re0)) Exported) res) ((:)
      sce []) ((:) ((,) sce (eventDefinition re)) []))};
   Error s -> Error s}

findEventInstance :: RaisedEvent -> Value_env -> ([] Event_instance) ->
                     Prelude.Maybe Event_instance
findEventInstance re en elist =
  case elist of {
   [] -> Prelude.Nothing;
   (:) e lst' ->
    let {
     ex_env = createValueEnv (eventArgs e) (eventParams (eventDefinition re))
                (eventArguments re)}
    in
    case ex_env of {
     Result env ->
      let {extend_env = extendValEnv en env} in
      case evalMonad extend_env (eventWhenExpr e) of {
       Result v ->
        case v of {
         Prelude.Left s ->
          case s of {
           Prelude.Left _ -> Prelude.Nothing;
           Prelude.Right b ->
            case b of {
             Prelude.True -> Prelude.Just e;
             Prelude.False -> findEventInstance re en lst'}};
         Prelude.Right _ -> Prelude.Nothing};
       Error _ -> Prelude.Nothing};
     Error _ -> Prelude.Nothing}}

constructConfig :: Scenario -> RaisedEvent -> Monitor -> Configuration ->
                   ErrorOrResult Configuration
constructConfig sce re m conf =
  let {sce_state = getScenarioState sce (controlstate m conf)} in
  case sce_state of {
   Prelude.Just state ->
    case transEvMapFunc (stateEvDefInstanceMap m) ((,) (Prelude.Just state)
           (Prelude.Just (eventDefinition re))) of {
     Prelude.Just le ->
      let {e' = findEventInstance re (datastate m conf) le} in
      case e' of {
       Prelude.Just e ->
        let {
         ex_env' = createValueEnv (eventArgs e)
                     (eventParams (eventDefinition re)) (eventArguments re)}
        in
        case ex_env' of {
         Result ex_env ->
          let {extend_env = extendValEnv (datastate m conf) ex_env} in
          let {stp = getStep' m conf sce e} in
          case stp of {
           Prelude.Just stp' ->
            case configTransition extend_env re e sce stp' m conf of {
             Result s -> Result s;
             Error _ -> Error error11};
           Prelude.Nothing -> Error error4};
         Error _ -> Error error12};
       Prelude.Nothing -> Error error3};
     Prelude.Nothing -> Error error3};
   Prelude.Nothing -> Error error1}

constructConfigList' :: ([] Scenario) -> RaisedEvent -> Monitor ->
                        Configuration -> ErrorOrResult ([] Configuration)
constructConfigList' scs re m conf =
  case scs of {
   [] -> Result [];
   (:) sce scenarios' ->
    case constructConfig sce re m conf of {
     Result conf' ->
      case constructConfigList' scenarios' re m conf of {
       Result lst -> Result ((:) conf' lst);
       Error s -> Error s};
     Error s -> Error s}}

constructConfigList :: ([] Scenario) -> RaisedEvent -> Monitor ->
                       Configuration -> ErrorOrResult ([] Configuration)
constructConfigList scs re m conf =
  let {scs' = filterList (finishedscenarios m conf) scs scenario_dec} in
  let {
   scs'' = filter (\x ->
             inList event_definition_dec (eventDefinition re) (alphabet x))
             scs'}
  in
  constructConfigList' scs'' re m conf

mergeDataStateFunc :: Value_env -> Value_env -> Value_env -> ErrorOrResult
                      ([] ((,) Atom ((,) Typ Range_typ)))
mergeDataStateFunc dso ds1 ds2 =
  case dso of {
   [] ->
    case ds1 of {
     [] -> case ds2 of {
            [] -> Result [];
            (:) _ _ -> Error error6};
     (:) _ _ -> Error error6};
   (:) p lst0 ->
    case p of {
     (,) n1 p0 ->
      case p0 of {
       (,) t1 v0 ->
        case ds1 of {
         [] -> Error error6;
         (:) p1 lst1 ->
          case p1 of {
           (,) n2 p2 ->
            case p2 of {
             (,) t2 v1 ->
              case ds2 of {
               [] -> Error error6;
               (:) p3 lst2 ->
                case p3 of {
                 (,) n3 p4 ->
                  case p4 of {
                   (,) t3 v2 ->
                    case atom_eq_dec n1 n2 of {
                     Prelude.True ->
                      case atom_eq_dec n1 n3 of {
                       Prelude.True ->
                        case typ_eq_dec t1 t2 of {
                         Prelude.True ->
                          case typ_eq_dec t1 t3 of {
                           Prelude.True ->
                            let {r = mergeDataStateFunc lst0 lst1 lst2} in
                            case r of {
                             Result lst ->
                              case range_typ_dec v1 v2 of {
                               Prelude.True -> Result ((:) ((,) n1 ((,) t1
                                v1)) lst);
                               Prelude.False ->
                                case range_typ_dec v1 v0 of {
                                 Prelude.True -> Result ((:) ((,) n1 ((,) t1
                                  v2)) lst);
                                 Prelude.False ->
                                  case range_typ_dec v2 v0 of {
                                   Prelude.True -> Result ((:) ((,) n1 ((,)
                                    t1 v1)) lst);
                                   Prelude.False -> Error error13}}};
                             Error s -> Error s};
                           Prelude.False -> Error error5};
                         Prelude.False -> Error error5};
                       Prelude.False -> Error error5};
                     Prelude.False -> Error error5}}}}}}}}}}

mergeControlStateFunc :: Scenario_env -> Scenario_env -> Scenario_env ->
                         ErrorOrResult ([] ((,) Scenario Scenario_state))
mergeControlStateFunc cso cs1 cs2 =
  case cso of {
   [] ->
    case cs1 of {
     [] -> case cs2 of {
            [] -> Result [];
            (:) _ _ -> Error error6};
     (:) _ _ -> Error error6};
   (:) p lst0 ->
    case p of {
     (,) sc0 s0 ->
      case cs1 of {
       [] -> Error error6;
       (:) p0 lst1 ->
        case p0 of {
         (,) sc1 s1 ->
          case cs2 of {
           [] -> Error error6;
           (:) p1 lst2 ->
            case p1 of {
             (,) sc2 s2 ->
              case scenario_dec sc0 sc1 of {
               Prelude.True ->
                case scenario_dec sc0 sc2 of {
                 Prelude.True ->
                  let {r = mergeControlStateFunc lst0 lst1 lst2} in
                  case r of {
                   Result lst ->
                    case string_dec s1 s2 of {
                     Prelude.True -> Result ((:) ((,) sc0 s1) lst);
                     Prelude.False ->
                      case string_dec s1 s0 of {
                       Prelude.True -> Result ((:) ((,) sc0 s2) lst);
                       Prelude.False ->
                        case string_dec s2 s0 of {
                         Prelude.True -> Result ((:) ((,) sc0 s1) lst);
                         Prelude.False -> Error error14}}};
                   Error s -> Error s};
                 Prelude.False -> Error error7};
               Prelude.False -> Error error7}}}}}}}

mergeConfigFunc' :: Monitor -> Configuration -> Configuration ->
                    Configuration -> ErrorOrResult Configuration
mergeConfigFunc' m config config1 config2 =
  let {
   ds = mergeDataStateFunc (datastate m config) (datastate m config1)
          (datastate m config2)}
  in
  case ds of {
   Result ds' ->
    let {
     cs0 = mergeControlStateFunc (controlstate m config)
             (controlstate m config1) (controlstate m config2)}
    in
    case cs0 of {
     Result cs' ->
      let {
       raisedEvents = (Prelude.++) (raisedevents m config1)
                        (raisedevents m config2)}
      in
      let {
       exportedEvents = (Prelude.++) (exportedevents m config1)
                          (exportedevents m config2)}
      in
      let {
       finishedEvents = (Prelude.++) (finishedscenarios m config1)
                          (finishedscenarios m config2)}
      in
      let {
       sceEventMaps = (Prelude.++) (sceEventMap m config1)
                        (sceEventMap m config2)}
      in
      Result (Build_configuration ds' cs' raisedEvents exportedEvents
      finishedEvents sceEventMaps);
     Error s -> Error s};
   Error s -> Error s}

innerCombineFunc'''' :: Monitor -> Configuration -> ([] Configuration) ->
                        Prelude.Maybe Configuration
innerCombineFunc'''' m originconf confList =
  case confList of {
   [] -> Prelude.Nothing;
   (:) conf' l ->
    case l of {
     [] ->
      case mergeConfigFunc' m originconf originconf conf' of {
       Result c -> Prelude.Just c;
       Error _ -> Prelude.Nothing};
     (:) _ _ ->
      case innerCombineFunc'''' m originconf l of {
       Prelude.Just c ->
        case mergeConfigFunc' m originconf conf' c of {
         Result rc -> Prelude.Just rc;
         Error _ -> Prelude.Nothing};
       Prelude.Nothing -> Prelude.Nothing}}}

removeEventFromConf :: RaisedEvent -> Monitor -> Configuration ->
                       Configuration
removeEventFromConf e m conf =
  Build_configuration (datastate m conf) (controlstate m conf)
    (removeEvent' e (raisedevents m conf)) (exportedevents m conf)
    (finishedscenarios m conf) (sceEventMap m conf)

combineFunc :: RaisedEvent -> Monitor -> Configuration -> Prelude.Maybe
               Configuration
combineFunc e m conf =
  case constructConfigList (dom (controlstate m conf)) e m conf of {
   Result lst ->
    case lst of {
     [] -> Prelude.Nothing;
     (:) _ _ ->
      case innerCombineFunc'''' m conf lst of {
       Prelude.Just v -> Prelude.Just (removeEventFromConf e m v);
       Prelude.Nothing -> Prelude.Nothing}};
   Error _ -> Prelude.Nothing}

data ADTSig =
   Build_ADTSig (Any -> [] ()) (Any -> (,) ([] ()) (Prelude.Maybe ()))

type ConstructorIndex = Any

type MethodIndex = Any

vector_caseS' :: (a1 -> Prelude.Int -> ([] a1) -> a2 -> a3) -> Prelude.Int ->
                 ([] a1) -> a2 -> a3
vector_caseS' h n v q =
  let {h0 = \h0 t -> h h0 n t q} in
  (\fnil fcons xs -> case xs of [] -> fnil (); x:xs -> fcons x 0 xs)
    (\_ -> __)
    (\h1 _ t -> h0 h1 t)
    v

data Prim_prod a b =
   Build_prim_prod a b

prim_fst :: (Prim_prod a1 a2) -> a1
prim_fst p =
  case p of {
   Build_prim_prod prim_fst0 _ -> prim_fst0}

prim_snd :: (Prim_prod a1 a2) -> a2
prim_snd p =
  case p of {
   Build_prim_prod _ prim_snd0 -> prim_snd0}

type Ilist a b = Any

icons :: a1 -> Prelude.Int -> ([] a1) -> a2 -> (Ilist a1 a2) -> Prim_prod 
         a2 Any
icons _ _ _ b il =
  Build_prim_prod b il

inil :: ()
inil =
  ()

ilist_hd :: Prelude.Int -> ([] a1) -> (Ilist a1 a2) -> Any
ilist_hd _ as0 il =
  (\fnil fcons xs -> case xs of [] -> fnil (); x:xs -> fcons x 0 xs)
    (\_ -> unsafeCoerce ())
    (\_ _ _ -> prim_fst (unsafeCoerce il))
    as0

ilist_tl :: Prelude.Int -> ([] a1) -> (Ilist a1 a2) -> Any
ilist_tl _ as0 il =
  (\fnil fcons xs -> case xs of [] -> fnil (); x:xs -> fcons x 0 xs)
    (\_ -> unsafeCoerce ())
    (\_ _ _ -> prim_snd (unsafeCoerce il))
    as0

ith :: Prelude.Int -> ([] a1) -> (Ilist a1 a2) -> T -> a2
ith _ as0 il n =
  case n of {
   F1 k ->
    caseS (\h n0 t ->
      unsafeCoerce ilist_hd (HString.nsucc n0) ((\x _n xs -> x:xs) h n0 t)) k
      as0 il;
   FS k n' ->
    vector_caseS' (\h n0 t m il0 ->
      ith n0 t (unsafeCoerce ilist_tl (HString.nsucc n0) ((\x _n xs -> x:xs) h n0 t) il0)
        m) k as0 n' il}

type IndexBound a =
  T
  -- singleton inductive, whose constructor was Build_IndexBound
  
ibound :: Prelude.Int -> a1 -> ([] a1) -> (IndexBound a1) -> T
ibound _ _ _ indexBound =
  indexBound

data BoundedIndex a =
   Build_BoundedIndex a (IndexBound a)

bindex :: Prelude.Int -> ([] a1) -> (BoundedIndex a1) -> a1
bindex _ _ b =
  case b of {
   Build_BoundedIndex bindex0 _ -> bindex0}

indexb :: Prelude.Int -> ([] a1) -> (BoundedIndex a1) -> IndexBound a1
indexb _ _ b =
  case b of {
   Build_BoundedIndex _ indexb0 -> indexb0}

data ConsSig =
   Build_consSig Prelude.String ([] ())

consID :: ConsSig -> Prelude.String
consID c =
  case c of {
   Build_consSig consID0 _ -> consID0}

consDom :: ConsSig -> [] ()
consDom c =
  case c of {
   Build_consSig _ consDom0 -> consDom0}

data MethSig =
   Build_methSig Prelude.String ([] ()) (Prelude.Maybe ())

methID :: MethSig -> Prelude.String
methID m =
  case m of {
   Build_methSig methID0 _ _ -> methID0}

methDom :: MethSig -> [] ()
methDom m =
  case m of {
   Build_methSig _ methDom0 _ -> methDom0}

methCod :: MethSig -> Prelude.Maybe ()
methCod m =
  case m of {
   Build_methSig _ _ methCod0 -> methCod0}

data DecoratedADTSig =
   Build_DecoratedADTSig ADTSig Prelude.Int Prelude.Int ([] Prelude.String) 
 ([] Prelude.String)

decADTSig :: DecoratedADTSig -> ADTSig
decADTSig d =
  case d of {
   Build_DecoratedADTSig decADTSig0 _ _ _ _ -> decADTSig0}

buildADTSig :: Prelude.Int -> Prelude.Int -> ([] ConsSig) -> ([] MethSig) ->
               DecoratedADTSig
buildADTSig n n' consSigs methSigs =
  Build_DecoratedADTSig (Build_ADTSig (\idx ->
    consDom (nth n consSigs (unsafeCoerce idx))) (\idx ->
    let {domcod = nth n' methSigs (unsafeCoerce idx)} in
    (,) (methDom domcod) (methCod domcod))) n n' (map consID n consSigs)
    (map methID n' methSigs)

type CConstructorType rep = Any

type CMethodType' rep = Any

type CMethodType rep = rep -> CMethodType' rep

data PcADT cRep =
   Build_pcADT (ConstructorIndex -> CConstructorType cRep) (MethodIndex ->
                                                           CMethodType 
                                                           cRep)

pcMethods :: ADTSig -> (PcADT a1) -> MethodIndex -> CMethodType a1
pcMethods _ p =
  case p of {
   Build_pcADT _ pcMethods0 -> pcMethods0}

type CADT = (,) () (PcADT Any)

type CRep = Any

cMethods :: ADTSig -> CADT -> MethodIndex -> CMethodType CRep
cMethods sig c idx =
  pcMethods sig (Prelude.snd c) idx

type CMethDef rep =
  CMethodType rep
  -- singleton inductive, whose constructor was Build_cMethDef
  
cMethBody :: MethSig -> (CMethDef a1) -> CMethodType a1
cMethBody _ c =
  c

type CConsDef rep =
  CConstructorType rep
  -- singleton inductive, whose constructor was Build_cConsDef
  
cConsBody :: ConsSig -> (CConsDef a1) -> CConstructorType a1
cConsBody _ c =
  c

getcConsDef :: Prelude.Int -> ([] ConsSig) -> (Ilist ConsSig (CConsDef a1))
               -> T -> CConstructorType a1
getcConsDef n consSigs consDefs idx =
  cConsBody (nth n consSigs idx) (ith n consSigs consDefs idx)

getcMethDef :: Prelude.Int -> ([] MethSig) -> (Ilist MethSig (CMethDef a1))
               -> T -> CMethodType a1
getcMethDef n methSigs methDefs idx =
  cMethBody (nth n methSigs idx) (ith n methSigs methDefs idx)

type DecoratedcADT = CADT

buildcADT :: Prelude.Int -> Prelude.Int -> ([] ConsSig) -> ([] MethSig) ->
             (Ilist ConsSig (CConsDef a1)) -> (Ilist MethSig (CMethDef a1))
             -> DecoratedcADT
buildcADT n n' consSigs methSigs consDefs methDefs =
  (,) __ (Build_pcADT (\idx ->
    getcConsDef n consSigs consDefs (unsafeCoerce idx)) (\idx ->
    getcMethDef n' methSigs methDefs (unsafeCoerce idx)))

callcADTMethod :: DecoratedADTSig -> DecoratedcADT -> ((BoundedIndex
                  Prelude.String) -> MethodIndex) -> (BoundedIndex
                  Prelude.String) -> CMethodType CRep
callcADTMethod dSig adt idxMap idx =
  cMethods (decADTSig dSig) adt (idxMap idx)

scenarioIncl :: ([] Scenario) -> ([] Scenario) -> Prelude.Bool
scenarioIncl l1 l2 =
  case l1 of {
   [] -> Prelude.True;
   (:) sce l1' ->
    case inList scenario_dec sce l2 of {
     Prelude.True -> scenarioIncl l1' l2;
     Prelude.False -> Prelude.False}}

checkFinal :: Monitor -> Configuration -> Prelude.Bool
checkFinal m conf =
  case ((Prelude.==) :: Prelude.Int -> Prelude.Int -> Prelude.Bool)
         ((Data.List.length :: [a] -> Prelude.Int) (raisedevents m conf))
         (0 :: Prelude.Int) of {
   Prelude.True -> Prelude.True;
   Prelude.False ->
    scenarioIncl (dom (controlstate m conf)) (finishedscenarios m conf)}

finalConfig_dec :: Monitor -> Configuration -> Prelude.Bool
finalConfig_dec m conf' =
  let {b = checkFinal m conf'} in
  case b of {
   Prelude.True -> Prelude.True;
   Prelude.False -> Prelude.False}

trySync :: Monitor -> Configuration -> ([] RaisedEvent) -> Prelude.Maybe
           Configuration
trySync m conf lst =
  case lst of {
   [] -> Prelude.Nothing;
   (:) e _ -> combineFunc e m conf}

syncStep :: Monitor -> Configuration -> Prelude.Maybe Configuration
syncStep m conf =
  trySync m conf (raisedevents m conf)

macroNStep :: Monitor -> Configuration -> Prelude.Int -> Prelude.Bool ->
              Prelude.Maybe Configuration
macroNStep m conf n p =
  case p of {
   Prelude.True -> Prelude.Just conf;
   Prelude.False ->
    (\fO fS n -> if n Prelude.<= 0 then fO () else fS (Prelude.pred n))
      (\_ -> Prelude.Just conf)
      (\n' ->
      let {conf' = syncStep m conf} in
      case conf' of {
       Prelude.Just conf'' ->
        macroNStep m conf'' n' (finalConfig_dec m conf'');
       Prelude.Nothing -> Prelude.Nothing})
      n}

configTransitionFunc :: Monitor -> Configuration -> RaisedEvent ->
                        Configuration
configTransitionFunc m conf e =
  Build_configuration (datastate m conf) (controlstate m conf) ((:) e
    (raisedevents m conf)) (exportedevents m conf) (finishedscenarios m conf)
    (sceEventMap m conf)

toReadyFunc :: Monitor -> Configuration -> (,) Configuration ([] RaisedEvent)
toReadyFunc m conf =
  (,) (Build_configuration (datastate m conf) (controlstate m conf) [] [] []
    []) (exportedevents m conf)

macroStepReadyFinal' :: Monitor -> Configuration -> RaisedEvent ->
                        Prelude.Int -> Prelude.Maybe
                        ((,) Configuration ([] RaisedEvent))
macroStepReadyFinal' m conf e n =
  let {conf' = configTransitionFunc m conf e} in
  case macroNStep m conf' n (finalConfig_dec m conf') of {
   Prelude.Just conf'' -> Prelude.Just (toReadyFunc m conf'');
   Prelude.Nothing -> Prelude.Nothing}

macroStepReadyFinal :: Monitor -> Configuration -> RaisedEvent -> Prelude.Int
                       -> (,) Configuration ([] RaisedEvent)
macroStepReadyFinal m conf e n =
  let {filtered_var = macroStepReadyFinal' m conf e n} in
  case filtered_var of {
   Prelude.Just p -> case p of {
                      (,) conf''' eList -> (,) conf''' eList};
   Prelude.Nothing -> false_rect}

newS :: Prelude.String
newS =
  (:) 'n' ((:) 'e' ((:) 'w' []))

processEventS :: Prelude.String
processEventS =
  (:) 'p' ((:) 'r' ((:) 'o' ((:) 'c' ((:) 'e' ((:) 's' ((:) 's' ((:) 'E' ((:)
    'v' ((:) 'e' ((:) 'n' ((:) 't' [])))))))))))

listInBool :: (a1 -> a1 -> Prelude.Bool) -> ([] a1) -> a1 -> Prelude.Bool
listInBool dec_A la a =
  case la of {
   [] -> Prelude.False;
   (:) a' la' ->
    case dec_A a' a of {
     Prelude.True -> Prelude.True;
     Prelude.False -> listInBool dec_A la' a}}

sceCheckBool :: ([] Scenario) -> RaisedEvent -> Prelude.Bool
sceCheckBool sceList e =
  case sceList of {
   [] -> Prelude.False;
   (:) sce sceList' ->
    case listInBool event_definition_dec (alphabet sce) (eventDefinition e) of {
     Prelude.True -> Prelude.True;
     Prelude.False -> sceCheckBool sceList' e}}

raisedAsImported_computation :: Object -> RaisedEvent -> Prelude.Bool
raisedAsImported_computation mon e =
  (Prelude.&&)
    ((Prelude.&&)
      ((Prelude.&&)
        (parameterMatchFunc (eventArguments e)
          (eventParams (eventDefinition e)))
        (importEventBool (eventDefinition e)))
      (listInBool event_definition_dec (events mon) (eventDefinition e)))
    (sceCheckBool (scenarios mon) e)

program :: Object -> Configuration -> DecoratedcADT
program m initial_conf =
  buildcADT (HString.nsucc (0 :: Prelude.Int)) (HString.nsucc
    (0 :: Prelude.Int)) ((\x _n xs -> x:xs) (Build_consSig newS [])
    (0 :: Prelude.Int) []) ((\x _n xs -> x:xs) (Build_methSig processEventS
    ((:) __ []) (Prelude.Just __)) (0 :: Prelude.Int) [])
    (unsafeCoerce icons (Build_consSig newS []) (0 :: Prelude.Int) []
      initial_conf inil)
    (unsafeCoerce icons (Build_methSig processEventS ((:) __ [])
      (Prelude.Just __)) (0 :: Prelude.Int) [] (\s ->
      unsafeCoerce (\s0 -> (,)
        (Prelude.fst
          (macroStepReadyFinal m ( s) ( s0)
            ((Data.List.length :: [a] -> Prelude.Int)
              (dom (controlstate m ( s))))))
        (Prelude.snd
          (macroStepReadyFinal m ( s) ( s0)
            ((Data.List.length :: [a] -> Prelude.Int)
              (dom (controlstate m ( s)))))))) inil)

monitor_new :: Object -> Configuration -> CRep
monitor_new _ initial_conf =
  unsafeCoerce initial_conf

monitor_processEvent :: Object -> Configuration -> CRep -> RaisedEvent -> (,)
                        CRep ([] RaisedEvent)
monitor_processEvent m initial_conf r e =
  unsafeCoerce callcADTMethod
    (buildADTSig (HString.nsucc (0 :: Prelude.Int)) (HString.nsucc
      (0 :: Prelude.Int)) ((\x _n xs -> x:xs) (Build_consSig newS [])
      (0 :: Prelude.Int) []) ((\x _n xs -> x:xs) (Build_methSig processEventS
      ((:) __ []) (Prelude.Just __)) (0 :: Prelude.Int) []))
    (program m initial_conf) (\processEventS0 ->
    unsafeCoerce ibound (HString.nsucc (0 :: Prelude.Int))
      (bindex (HString.nsucc (0 :: Prelude.Int)) ((\x _n xs -> x:xs)
        processEventS (0 :: Prelude.Int) []) processEventS0)
      ((\x _n xs -> x:xs) processEventS (0 :: Prelude.Int) [])
      (indexb (HString.nsucc (0 :: Prelude.Int)) ((\x _n xs -> x:xs)
        processEventS (0 :: Prelude.Int) []) processEventS0))
    (Build_BoundedIndex processEventS (F1 (0 :: Prelude.Int))) r e

createRaisedEvent :: Object -> Prelude.String -> EventKind -> ([] Typ) -> ([]
                     Range_typ) -> Prelude.Maybe RaisedEvent
createRaisedEvent m id ek lk lkt =
  let {evDef = Build_event_definition ek id lk} in
  let {re = Build_raisedEvent evDef lkt} in
  let {checkRaiseCompute = raisedAsImported_computation m re} in
  case checkRaiseCompute of {
   Prelude.True -> Prelude.Just re;
   Prelude.False -> Prelude.Nothing}

createRaised :: Object -> Prelude.String -> EventKind -> ([] Typ) -> ([]
                Range_typ) -> Prelude.Maybe RaisedEvent
createRaised m id ek lk lkt =
  let {filtered_var = createRaisedEvent m id ek lk lkt} in
  case filtered_var of {
   Prelude.Just re -> Prelude.Just re;
   Prelude.Nothing -> Prelude.Nothing}

imports_str :: Prelude.String
imports_str =
  []

objName :: Prelude.String
objName =
  (:) 'o' ((:) 'n' ((:) 'i' []))

objId :: [] ((,) Atom Typ)
objId =
  []

objstvar :: [] ((,) Atom Typ)
objstvar =
  (:) ((,) (AIdent ((:) 'i' ((:) 'n' ((:) '_' ((:) 'c' ((:) 'l' ((:) 'a' ((:)
    's' ((:) 's' []))))))))) Int) []

e_inClass :: Event_definition
e_inClass =
  Build_event_definition Imported ((:) 'i' ((:) 'n' ((:) 'C' ((:) 'l' ((:)
    'a' ((:) 's' ((:) 's' []))))))) []

e_outClass :: Event_definition
e_outClass =
  Build_event_definition Imported ((:) 'o' ((:) 'u' ((:) 't' ((:) 'C' ((:)
    'l' ((:) 'a' ((:) 's' ((:) 's' [])))))))) []

e_s2s :: Event_definition
e_s2s =
  Build_event_definition Imported ((:) 's' ((:) 't' ((:) 'a' ((:) 't' ((:)
    'e' ((:) '_' ((:) 't' ((:) 'o' ((:) '_' ((:) 's' ((:) 't' ((:) 'a' ((:)
    'r' ((:) 't' [])))))))))))))) []

e_s2v :: Event_definition
e_s2v =
  Build_event_definition Imported ((:) 's' ((:) 't' ((:) 'a' ((:) 't' ((:)
    'e' ((:) '_' ((:) 't' ((:) 'o' ((:) '_' ((:) 'v' ((:) 'a' ((:) 'l' ((:)
    'u' ((:) 'e' [])))))))))))))) []

e_s2r :: Event_definition
e_s2r =
  Build_event_definition Imported ((:) 's' ((:) 't' ((:) 'a' ((:) 't' ((:)
    'e' ((:) '_' ((:) 't' ((:) 'o' ((:) '_' ((:) 'r' ((:) 'a' ((:) 'n' ((:)
    'g' ((:) 'e' [])))))))))))))) []

e_s2c :: Event_definition
e_s2c =
  Build_event_definition Imported ((:) 's' ((:) 't' ((:) 'a' ((:) 't' ((:)
    'e' ((:) '_' ((:) 't' ((:) 'o' ((:) '_' ((:) 'c' ((:) 'o' ((:) 'm' ((:)
    'p' ((:) 'l' ((:) 'e' ((:) 't' ((:) 'e' []))))))))))))))))) []

e_error :: Event_definition
e_error =
  Build_event_definition Exported ((:) 'e' ((:) 'r' ((:) 'r' ((:) 'o' ((:)
    'r' []))))) ((:) Int [])

objev :: [] Event_definition
objev =
  (:) e_inClass ((:) e_outClass ((:) e_s2s ((:) e_s2v ((:) e_s2r ((:) e_s2c
    ((:) e_error []))))))

guard1 :: Expr
guard1 =
  ENot (EEq (EAtom (AIdent ((:) 'i' ((:) 'n' ((:) '_' ((:) 'c' ((:) 'l' ((:)
    'a' ((:) 's' ((:) 's' [])))))))))) (EAtom (AInt ((\x -> x) 1))))

truth :: Expr
truth =
  EAtom (ABool Prelude.True)

eis2v :: Event_instance
eis2v =
  Build_event_instance e_s2v [] guard1

eis2v_rev :: Event_instance
eis2v_rev =
  Build_event_instance e_s2v [] (ENot guard1)

eis2vng :: Event_instance
eis2vng =
  Build_event_instance e_s2v [] truth

eis2vng_rev :: Event_instance
eis2vng_rev =
  Build_event_instance e_s2v [] (ENot truth)

eis2sng :: Event_instance
eis2sng =
  Build_event_instance e_s2s [] truth

eis2sng_rev :: Event_instance
eis2sng_rev =
  Build_event_instance e_s2s [] (ENot truth)

eis2rng :: Event_instance
eis2rng =
  Build_event_instance e_s2r [] truth

eis2rng_rev :: Event_instance
eis2rng_rev =
  Build_event_instance e_s2r [] (ENot truth)

eis2cng :: Event_instance
eis2cng =
  Build_event_instance e_s2c [] truth

eis2cng_rev :: Event_instance
eis2cng_rev =
  Build_event_instance e_s2c [] (ENot truth)

cs :: Prelude.String
cs =
  (:) 'C' ((:) 'C' ((:) 'S' ((:) '_' ((:) 'S' ((:) 'T' ((:) 'A' ((:) 'R' ((:)
    'T' []))))))))

cv :: Prelude.String
cv =
  (:) 'C' ((:) 'C' ((:) 'S' ((:) '_' ((:) 'V' ((:) 'A' ((:) 'L' ((:) 'U' ((:)
    'E' []))))))))

cr :: Prelude.String
cr =
  (:) 'C' ((:) 'C' ((:) 'S' ((:) '_' ((:) 'R' ((:) 'A' ((:) 'N' ((:) 'G' ((:)
    'E' []))))))))

cc :: Prelude.String
cc =
  (:) 'C' ((:) 'C' ((:) 'S' ((:) '_' ((:) 'C' ((:) 'O' ((:) 'M' ((:) 'P' ((:)
    'L' ((:) 'E' ((:) 'T' ((:) 'E' [])))))))))))

eact0 :: Action
eact0 =
  RaiseStmt ((:) 'e' ((:) 'r' ((:) 'r' ((:) 'o' ((:) 'r' []))))) ((:) (EAtom
    (AInt 0)) [])

eact1 :: Action
eact1 =
  RaiseStmt ((:) 'e' ((:) 'r' ((:) 'r' ((:) 'o' ((:) 'r' []))))) ((:) (EAtom
    (AInt ((\x -> x) 1))) [])

eact2 :: Action
eact2 =
  RaiseStmt ((:) 'e' ((:) 'r' ((:) 'r' ((:) 'o' ((:) 'r' []))))) ((:) (EAtom
    (AInt ((\x -> x) ((\x -> 2 Prelude.* x) 1)))) [])

eact3 :: Action
eact3 =
  RaiseStmt ((:) 'e' ((:) 'r' ((:) 'r' ((:) 'o' ((:) 'r' []))))) ((:) (EAtom
    (AInt ((\x -> x) ((\x -> 2 Prelude.* x Prelude.+ 1) 1)))) [])

csv1 :: Step
csv1 =
  Build_step cs eis2v Skip cv

csv1' :: Step
csv1' =
  Build_step cs eis2v_rev eact0 cs

css1 :: Step
css1 =
  Build_step cs eis2sng eact0 cs

css1' :: Step
css1' =
  Build_step cs eis2sng_rev Skip cs

csr1 :: Step
csr1 =
  Build_step cs eis2rng eact0 cs

csr1' :: Step
csr1' =
  Build_step cs eis2rng_rev Skip cs

csc1 :: Step
csc1 =
  Build_step cs eis2cng eact0 cs

csc1' :: Step
csc1' =
  Build_step cs eis2cng_rev Skip cs

cvv1 :: Step
cvv1 =
  Build_step cv eis2vng Skip cv

cvv1' :: Step
cvv1' =
  Build_step cv eis2vng_rev Skip cv

cvc1 :: Step
cvc1 =
  Build_step cv eis2cng eact1 cv

cvc1' :: Step
cvc1' =
  Build_step cv eis2cng_rev Skip cv

cvr1 :: Step
cvr1 =
  Build_step cv eis2rng Skip cr

cvr1' :: Step
cvr1' =
  Build_step cv eis2rng_rev Skip cv

cvs1 :: Step
cvs1 =
  Build_step cv eis2sng Skip cs

cvs1' :: Step
cvs1' =
  Build_step cv eis2sng_rev Skip cs

crv1 :: Step
crv1 =
  Build_step cr eis2vng Skip cv

crv1' :: Step
crv1' =
  Build_step cr eis2vng_rev Skip cv

crc1 :: Step
crc1 =
  Build_step cr eis2cng Skip cc

crc1' :: Step
crc1' =
  Build_step cr eis2cng_rev Skip cc

crr1 :: Step
crr1 =
  Build_step cr eis2rng eact2 cr

crr1' :: Step
crr1' =
  Build_step cr eis2rng_rev Skip cr

crs1 :: Step
crs1 =
  Build_step cr eis2sng eact2 cr

crs1' :: Step
crs1' =
  Build_step cr eis2sng_rev Skip cr

ccv1 :: Step
ccv1 =
  Build_step cc eis2vng Skip cv

ccv1' :: Step
ccv1' =
  Build_step cc eis2vng_rev Skip cv

ccc1 :: Step
ccc1 =
  Build_step cc eis2cng eact3 cc

ccc1' :: Step
ccc1' =
  Build_step cc eis2cng_rev Skip cc

ccr1 :: Step
ccr1 =
  Build_step cc eis2rng eact3 cc

ccr1' :: Step
ccr1' =
  Build_step cc eis2rng_rev Skip cc

ccs1 :: Step
ccs1 =
  Build_step cc eis2sng eact3 cc

ccs1' :: Step
ccs1' =
  Build_step cc eis2sng_rev Skip cc

mainS :: Scenario
mainS =
  Build_scenario ((:) 'm' ((:) 'a' ((:) 'i' ((:) 'n' [])))) ((:) csv1 ((:)
    csv1' ((:) css1 ((:) css1' ((:) csr1 ((:) csr1' ((:) csc1 ((:) csc1' ((:)
    cvv1 ((:) cvv1' ((:) cvs1 ((:) cvs1' ((:) cvr1 ((:) cvr1' ((:) cvc1 ((:)
    cvc1' ((:) crv1 ((:) crv1' ((:) crs1 ((:) crs1' ((:) crr1 ((:) crr1' ((:)
    crc1 ((:) crc1' ((:) ccv1 ((:) ccv1' ((:) ccs1 ((:) ccs1' ((:) ccr1 ((:)
    ccr1' ((:) ccc1 ((:) ccc1' [])))))))))))))))))))))))))))))))) ((:) e_s2s
    ((:) e_s2v ((:) e_s2r ((:) e_s2c []))))

start :: Prelude.String
start =
  (:) 's' ((:) 't' ((:) 'a' ((:) 'r' ((:) 't' []))))

chk_act1 :: Action
chk_act1 =
  StateUpdate (AIdent ((:) 'i' ((:) 'n' ((:) '_' ((:) 'c' ((:) 'l' ((:) 'a'
    ((:) 's' ((:) 's' []))))))))) (EAtom (AInt ((\x -> x) 1)))

chk_act2 :: Action
chk_act2 =
  StateUpdate (AIdent ((:) 'i' ((:) 'n' ((:) '_' ((:) 'c' ((:) 'l' ((:) 'a'
    ((:) 's' ((:) 's' []))))))))) (EAtom (AInt 0))

eiinClass :: Event_instance
eiinClass =
  Build_event_instance e_inClass [] guard1

eiinClass_rev :: Event_instance
eiinClass_rev =
  Build_event_instance e_inClass [] (ENot guard1)

eioutClass :: Event_instance
eioutClass =
  Build_event_instance e_outClass [] (ENot guard1)

eioutClass_rev :: Event_instance
eioutClass_rev =
  Build_event_instance e_outClass [] (ENot (ENot guard1))

check_inc :: Step
check_inc =
  Build_step start eiinClass chk_act1 start

check_inc' :: Step
check_inc' =
  Build_step start eiinClass_rev Skip start

check_outc :: Step
check_outc =
  Build_step start eioutClass chk_act2 start

check_outc' :: Step
check_outc' =
  Build_step start eioutClass_rev Skip start

checkS :: Scenario
checkS =
  Build_scenario ((:) 'c' ((:) 'h' ((:) 'e' ((:) 'c' ((:) 'k' ((:) '_' ((:)
    'c' ((:) 'l' ((:) 'a' ((:) 's' ((:) 's' []))))))))))) ((:) check_inc ((:)
    check_inc' ((:) check_outc ((:) check_outc' [])))) ((:) e_inClass ((:)
    e_outClass []))

sces :: [] Scenario
sces =
  (:) mainS ((:) checkS [])

stpSceMap :: [] ((,) Scenario Step)
stpSceMap =
  (:) ((,) mainS csv1) ((:) ((,) mainS csv1') ((:) ((,) mainS css1) ((:) ((,)
    mainS css1') ((:) ((,) mainS csr1) ((:) ((,) mainS csr1') ((:) ((,) mainS
    csc1) ((:) ((,) mainS csc1') ((:) ((,) mainS cvv1) ((:) ((,) mainS cvv1')
    ((:) ((,) mainS cvs1) ((:) ((,) mainS cvs1') ((:) ((,) mainS cvr1) ((:)
    ((,) mainS cvr1') ((:) ((,) mainS cvc1) ((:) ((,) mainS cvc1') ((:) ((,)
    mainS crv1) ((:) ((,) mainS crv1') ((:) ((,) mainS crs1) ((:) ((,) mainS
    crs1') ((:) ((,) mainS crr1) ((:) ((,) mainS crr1') ((:) ((,) mainS crc1)
    ((:) ((,) mainS crc1') ((:) ((,) mainS ccv1) ((:) ((,) mainS ccv1') ((:)
    ((,) mainS ccs1) ((:) ((,) mainS ccs1') ((:) ((,) mainS ccr1) ((:) ((,)
    mainS ccr1') ((:) ((,) mainS ccc1) ((:) ((,) mainS ccc1') ((:) ((,)
    checkS check_inc) ((:) ((,) checkS check_inc') ((:) ((,) checkS
    check_outc) ((:) ((,) checkS check_outc')
    [])))))))))))))))))))))))))))))))))))

stSceMap :: [] ((,) Scenario Prelude.String)
stSceMap =
  (:) ((,) mainS cs) ((:) ((,) mainS cv) ((:) ((,) mainS cr) ((:) ((,) mainS
    cc) ((:) ((,) checkS start) []))))

stEvStpMap :: []
              ((,) ((,) Prelude.String Event_instance) (Prelude.Maybe Step))
stEvStpMap =
  (:) ((,) ((,) cs eis2v) (Prelude.Just csv1)) ((:) ((,) ((,) cs eis2v_rev)
    (Prelude.Just csv1')) ((:) ((,) ((,) cs eis2sng) (Prelude.Just css1))
    ((:) ((,) ((,) cs eis2sng_rev) (Prelude.Just css1')) ((:) ((,) ((,) cs
    eis2rng) (Prelude.Just csr1)) ((:) ((,) ((,) cs eis2rng_rev)
    (Prelude.Just csr1')) ((:) ((,) ((,) cs eis2cng) (Prelude.Just csc1))
    ((:) ((,) ((,) cs eis2cng_rev) (Prelude.Just csc1')) ((:) ((,) ((,) cv
    eis2vng) (Prelude.Just cvv1)) ((:) ((,) ((,) cv eis2vng_rev)
    (Prelude.Just cvv1')) ((:) ((,) ((,) cv eis2sng) (Prelude.Just cvs1))
    ((:) ((,) ((,) cv eis2sng_rev) (Prelude.Just cvs1')) ((:) ((,) ((,) cv
    eis2rng) (Prelude.Just cvr1)) ((:) ((,) ((,) cv eis2rng_rev)
    (Prelude.Just cvr1')) ((:) ((,) ((,) cv eis2cng) (Prelude.Just cvc1))
    ((:) ((,) ((,) cv eis2cng_rev) (Prelude.Just cvc1')) ((:) ((,) ((,) cr
    eis2vng) (Prelude.Just crv1)) ((:) ((,) ((,) cv eis2vng_rev)
    (Prelude.Just crv1')) ((:) ((,) ((,) cr eis2sng) (Prelude.Just crs1))
    ((:) ((,) ((,) cr eis2sng_rev) (Prelude.Just crs1')) ((:) ((,) ((,) cr
    eis2rng) (Prelude.Just crr1)) ((:) ((,) ((,) cv eis2rng_rev)
    (Prelude.Just crr1')) ((:) ((,) ((,) cr eis2cng) (Prelude.Just crc1'))
    ((:) ((,) ((,) cv eis2cng_rev) (Prelude.Just crc1')) ((:) ((,) ((,) cc
    eis2vng) (Prelude.Just ccv1)) ((:) ((,) ((,) cc eis2vng_rev)
    (Prelude.Just ccv1')) ((:) ((,) ((,) cc eis2sng) (Prelude.Just ccs1))
    ((:) ((,) ((,) cc eis2sng_rev) (Prelude.Just ccs1')) ((:) ((,) ((,) cc
    eis2rng) (Prelude.Just ccr1)) ((:) ((,) ((,) cc eis2rng_rev)
    (Prelude.Just ccr1')) ((:) ((,) ((,) cc eis2cng) (Prelude.Just ccc1))
    ((:) ((,) ((,) cc eis2cng_rev) (Prelude.Just ccc1')) ((:) ((,) ((,) start
    eiinClass) (Prelude.Just check_inc)) ((:) ((,) ((,) start eiinClass_rev)
    (Prelude.Just check_inc')) ((:) ((,) ((,) start eioutClass) (Prelude.Just
    check_outc)) ((:) ((,) ((,) start eioutClass_rev) (Prelude.Just
    check_outc')) [])))))))))))))))))))))))))))))))))))

stEvStpMap' :: []
               ((,) ((,) ((,) Prelude.String Event_instance) Scenario)
               (Prelude.Maybe Step))
stEvStpMap' =
  (:) ((,) ((,) ((,) cs eis2v) mainS) (Prelude.Just csv1)) ((:) ((,) ((,)
    ((,) cs eis2v_rev) mainS) (Prelude.Just csv1')) ((:) ((,) ((,) ((,) cs
    eis2sng) mainS) (Prelude.Just css1)) ((:) ((,) ((,) ((,) cs eis2sng_rev)
    mainS) (Prelude.Just css1')) ((:) ((,) ((,) ((,) cs eis2rng) mainS)
    (Prelude.Just csr1)) ((:) ((,) ((,) ((,) cs eis2rng_rev) mainS)
    (Prelude.Just csr1')) ((:) ((,) ((,) ((,) cs eis2cng) mainS)
    (Prelude.Just csc1)) ((:) ((,) ((,) ((,) cs eis2cng_rev) mainS)
    (Prelude.Just csc1')) ((:) ((,) ((,) ((,) cv eis2vng) mainS)
    (Prelude.Just cvv1)) ((:) ((,) ((,) ((,) cv eis2vng_rev) mainS)
    (Prelude.Just cvv1')) ((:) ((,) ((,) ((,) cv eis2sng) mainS)
    (Prelude.Just cvs1)) ((:) ((,) ((,) ((,) cv eis2sng_rev) mainS)
    (Prelude.Just cvs1')) ((:) ((,) ((,) ((,) cv eis2rng) mainS)
    (Prelude.Just cvr1)) ((:) ((,) ((,) ((,) cv eis2rng_rev) mainS)
    (Prelude.Just cvr1')) ((:) ((,) ((,) ((,) cv eis2cng) mainS)
    (Prelude.Just cvc1)) ((:) ((,) ((,) ((,) cv eis2cng_rev) mainS)
    (Prelude.Just cvc1')) ((:) ((,) ((,) ((,) cr eis2vng) mainS)
    (Prelude.Just crv1)) ((:) ((,) ((,) ((,) cr eis2vng_rev) mainS)
    (Prelude.Just crv1')) ((:) ((,) ((,) ((,) cr eis2sng) mainS)
    (Prelude.Just crs1)) ((:) ((,) ((,) ((,) cr eis2sng_rev) mainS)
    (Prelude.Just crs1')) ((:) ((,) ((,) ((,) cr eis2rng) mainS)
    (Prelude.Just crr1)) ((:) ((,) ((,) ((,) cr eis2rng_rev) mainS)
    (Prelude.Just crr1')) ((:) ((,) ((,) ((,) cr eis2cng) mainS)
    (Prelude.Just crc1)) ((:) ((,) ((,) ((,) cr eis2cng_rev) mainS)
    (Prelude.Just crc1')) ((:) ((,) ((,) ((,) cc eis2vng) mainS)
    (Prelude.Just ccv1)) ((:) ((,) ((,) ((,) cc eis2vng_rev) mainS)
    (Prelude.Just ccv1')) ((:) ((,) ((,) ((,) cc eis2sng) mainS)
    (Prelude.Just ccs1)) ((:) ((,) ((,) ((,) cc eis2sng_rev) mainS)
    (Prelude.Just ccs1')) ((:) ((,) ((,) ((,) cc eis2rng) mainS)
    (Prelude.Just ccr1)) ((:) ((,) ((,) ((,) cc eis2rng_rev) mainS)
    (Prelude.Just ccr1')) ((:) ((,) ((,) ((,) cc eis2cng) mainS)
    (Prelude.Just ccc1)) ((:) ((,) ((,) ((,) cc eis2cng_rev) mainS)
    (Prelude.Just ccc1')) ((:) ((,) ((,) ((,) start eiinClass) checkS)
    (Prelude.Just check_inc)) ((:) ((,) ((,) ((,) start eiinClass_rev)
    checkS) (Prelude.Just check_inc')) ((:) ((,) ((,) ((,) start eioutClass)
    checkS) (Prelude.Just check_outc)) ((:) ((,) ((,) ((,) start
    eioutClass_rev) checkS) (Prelude.Just check_outc'))
    [])))))))))))))))))))))))))))))))))))

stEvDefInMap :: []
                ((,)
                ((,) (Prelude.Maybe Prelude.String)
                (Prelude.Maybe Event_definition)) ([] Event_instance))
stEvDefInMap =
  (:) ((,) ((,) (Prelude.Just cs) (Prelude.Just e_s2v)) ((:) eis2v ((:)
    eis2v_rev []))) ((:) ((,) ((,) (Prelude.Just cs) (Prelude.Just e_s2s))
    ((:) eis2sng ((:) eis2sng_rev []))) ((:) ((,) ((,) (Prelude.Just cs)
    (Prelude.Just e_s2r)) ((:) eis2rng ((:) eis2rng_rev []))) ((:) ((,) ((,)
    (Prelude.Just cs) (Prelude.Just e_s2c)) ((:) eis2cng ((:) eis2cng_rev
    []))) ((:) ((,) ((,) (Prelude.Just cv) (Prelude.Just e_s2v)) ((:) eis2vng
    ((:) eis2vng_rev []))) ((:) ((,) ((,) (Prelude.Just cv) (Prelude.Just
    e_s2s)) ((:) eis2sng ((:) eis2sng_rev []))) ((:) ((,) ((,) (Prelude.Just
    cv) (Prelude.Just e_s2r)) ((:) eis2rng ((:) eis2rng_rev []))) ((:) ((,)
    ((,) (Prelude.Just cv) (Prelude.Just e_s2c)) ((:) eis2cng ((:)
    eis2cng_rev []))) ((:) ((,) ((,) (Prelude.Just cr) (Prelude.Just e_s2v))
    ((:) eis2vng ((:) eis2vng_rev []))) ((:) ((,) ((,) (Prelude.Just cr)
    (Prelude.Just e_s2s)) ((:) eis2sng ((:) eis2sng_rev []))) ((:) ((,) ((,)
    (Prelude.Just cr) (Prelude.Just e_s2r)) ((:) eis2rng ((:) eis2rng_rev
    []))) ((:) ((,) ((,) (Prelude.Just cr) (Prelude.Just e_s2c)) ((:) eis2cng
    ((:) eis2cng_rev []))) ((:) ((,) ((,) (Prelude.Just cc) (Prelude.Just
    e_s2v)) ((:) eis2vng ((:) eis2vng_rev []))) ((:) ((,) ((,) (Prelude.Just
    cc) (Prelude.Just e_s2s)) ((:) eis2sng ((:) eis2sng_rev []))) ((:) ((,)
    ((,) (Prelude.Just cc) (Prelude.Just e_s2r)) ((:) eis2rng ((:)
    eis2rng_rev []))) ((:) ((,) ((,) (Prelude.Just cc) (Prelude.Just e_s2c))
    ((:) eis2cng ((:) eis2cng_rev []))) ((:) ((,) ((,) (Prelude.Just start)
    (Prelude.Just e_inClass)) ((:) eiinClass ((:) eiinClass_rev []))) ((:)
    ((,) ((,) (Prelude.Just start) (Prelude.Just e_outClass)) ((:) eioutClass
    ((:) eioutClass_rev []))) [])))))))))))))))))

parseCC :: Object
parseCC =
  Build_object ((:) imports_str []) objName objId objstvar objev sces
    stEvStpMap stEvStpMap' stEvDefInMap stpSceMap stSceMap

configuration1 :: Configuration
configuration1 =
  Build_configuration ((:) ((,) (AIdent ((:) 'i' ((:) 'n' ((:) '_' ((:) 'c'
    ((:) 'l' ((:) 'a' ((:) 's' ((:) 's' []))))))))) ((,) Int (Prelude.Left
    (Prelude.Left (Prelude.Left (Prelude.Left 0)))))) []) ((:) ((,) mainS cs)
    ((:) ((,) checkS start) [])) [] [] [] []

mon_oni_new :: CRep
mon_oni_new =
  monitor_new parseCC configuration1

parseCC_processEvent :: CRep -> RaisedEvent -> (,) CRep ([] RaisedEvent)
parseCC_processEvent r e =
  monitor_processEvent parseCC configuration1 r e


{-# OPTIONS_GHC -cpp -XMagicHash #-}
{- For Hugs, use the option -F"cpp -P -traditional" -}

module SMEDL where

import qualified Prelude

#ifdef __GLASGOW_HASKELL__
import qualified GHC.Base
import qualified GHC.Prim
#else
-- HUGS
import qualified IOExts
#endif

#ifdef __GLASGOW_HASKELL__
unsafeCoerce :: a -> b
unsafeCoerce = GHC.Base.unsafeCoerce#
#else
-- HUGS
unsafeCoerce :: a -> b
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

data Unit =
   Tt

data Bool =
   True
 | False

bool_rect :: a1 -> a1 -> Bool -> a1
bool_rect f f0 b =
  case b of {
   True -> f;
   False -> f0}

bool_rec :: a1 -> a1 -> Bool -> a1
bool_rec =
  bool_rect

andb :: Bool -> Bool -> Bool
andb b1 b2 =
  case b1 of {
   True -> b2;
   False -> False}

orb :: Bool -> Bool -> Bool
orb b1 b2 =
  case b1 of {
   True -> True;
   False -> b2}

negb :: Bool -> Bool
negb b =
  case b of {
   True -> False;
   False -> True}

data Nat =
   O
 | S Nat

nat_rect :: a1 -> (Nat -> a1 -> a1) -> Nat -> a1
nat_rect f f0 n =
  case n of {
   O -> f;
   S n0 -> f0 n0 (nat_rect f f0 n0)}

nat_rec :: a1 -> (Nat -> a1 -> a1) -> Nat -> a1
nat_rec =
  nat_rect

data Option a =
   Some a
 | None

data Sum a b =
   Inl a
 | Inr b

sum_rect :: (a1 -> a3) -> (a2 -> a3) -> (Sum a1 a2) -> a3
sum_rect f f0 s =
  case s of {
   Inl x -> f x;
   Inr x -> f0 x}

sum_rec :: (a1 -> a3) -> (a2 -> a3) -> (Sum a1 a2) -> a3
sum_rec =
  sum_rect

data Prod a b =
   Pair a b

fst :: (Prod a1 a2) -> a1
fst p =
  case p of {
   Pair x _ -> x}

snd :: (Prod a1 a2) -> a2
snd p =
  case p of {
   Pair _ y -> y}

data List a =
   Nil
 | Cons a (List a)

list_rect :: a2 -> (a1 -> (List a1) -> a2 -> a2) -> (List a1) -> a2
list_rect f f0 l =
  case l of {
   Nil -> f;
   Cons y l0 -> f0 y l0 (list_rect f f0 l0)}

list_rec :: a2 -> (a1 -> (List a1) -> a2 -> a2) -> (List a1) -> a2
list_rec =
  list_rect

length :: (List a1) -> Nat
length l =
  case l of {
   Nil -> O;
   Cons _ l' -> S (length l')}

app :: (List a1) -> (List a1) -> List a1
app l m =
  case l of {
   Nil -> m;
   Cons a l1 -> Cons a (app l1 m)}

data Comparison =
   Eq
 | Lt
 | Gt

compOpp :: Comparison -> Comparison
compOpp r =
  case r of {
   Eq -> Eq;
   Lt -> Gt;
   Gt -> Lt}

type Sig a = a
  -- singleton inductive, whose constructor was exist
  
data SigT a p =
   ExistT a p

proj1_sig :: a1 -> a1
proj1_sig e =
  e

projT2 :: (SigT a1 a2) -> a2
projT2 x =
  case x of {
   ExistT _ h -> h}

data Sumbool =
   Left
 | Right

sumbool_rect :: (() -> a1) -> (() -> a1) -> Sumbool -> a1
sumbool_rect f f0 s =
  case s of {
   Left -> f __;
   Right -> f0 __}

sumbool_rec :: (() -> a1) -> (() -> a1) -> Sumbool -> a1
sumbool_rec =
  sumbool_rect

bool_dec :: Bool -> Bool -> Sumbool
bool_dec b1 b2 =
  bool_rec (\x -> case x of {
                   True -> Left;
                   False -> Right}) (\x ->
    case x of {
     True -> Right;
     False -> Left}) b1 b2

eqb :: Bool -> Bool -> Bool
eqb b1 b2 =
  case b1 of {
   True -> b2;
   False -> case b2 of {
             True -> False;
             False -> True}}

eqb0 :: Nat -> Nat -> Bool
eqb0 n m =
  case n of {
   O -> case m of {
         O -> True;
         S _ -> False};
   S n' -> case m of {
            O -> False;
            S m' -> eqb0 n' m'}}

map :: (a1 -> a2) -> (List a1) -> List a2
map f l =
  case l of {
   Nil -> Nil;
   Cons a t -> Cons (f a) (map f t)}

filter :: (a1 -> Bool) -> (List a1) -> List a1
filter f l =
  case l of {
   Nil -> Nil;
   Cons x l0 ->
    case f x of {
     True -> Cons x (filter f l0);
     False -> filter f l0}}

data Positive =
   XI Positive
 | XO Positive
 | XH

positive_rect :: (Positive -> a1 -> a1) -> (Positive -> a1 -> a1) -> a1 ->
                 Positive -> a1
positive_rect f f0 f1 p =
  case p of {
   XI p0 -> f p0 (positive_rect f f0 f1 p0);
   XO p0 -> f0 p0 (positive_rect f f0 f1 p0);
   XH -> f1}

positive_rec :: (Positive -> a1 -> a1) -> (Positive -> a1 -> a1) -> a1 ->
                Positive -> a1
positive_rec =
  positive_rect

data Z =
   Z0
 | Zpos Positive
 | Zneg Positive

z_rect :: a1 -> (Positive -> a1) -> (Positive -> a1) -> Z -> a1
z_rect f f0 f1 z =
  case z of {
   Z0 -> f;
   Zpos x -> f0 x;
   Zneg x -> f1 x}

z_rec :: a1 -> (Positive -> a1) -> (Positive -> a1) -> Z -> a1
z_rec =
  z_rect

succ :: Positive -> Positive
succ x =
  case x of {
   XI p -> XO (succ p);
   XO p -> XI p;
   XH -> XO XH}

add :: Positive -> Positive -> Positive
add x y =
  case x of {
   XI p ->
    case y of {
     XI q -> XO (add_carry p q);
     XO q -> XI (add p q);
     XH -> XO (succ p)};
   XO p ->
    case y of {
     XI q -> XI (add p q);
     XO q -> XO (add p q);
     XH -> XI p};
   XH -> case y of {
          XI q -> XO (succ q);
          XO q -> XI q;
          XH -> XO XH}}

add_carry :: Positive -> Positive -> Positive
add_carry x y =
  case x of {
   XI p ->
    case y of {
     XI q -> XI (add_carry p q);
     XO q -> XO (add_carry p q);
     XH -> XI (succ p)};
   XO p ->
    case y of {
     XI q -> XO (add_carry p q);
     XO q -> XI (add p q);
     XH -> XO (succ p)};
   XH -> case y of {
          XI q -> XI (succ q);
          XO q -> XO (succ q);
          XH -> XI XH}}

pred_double :: Positive -> Positive
pred_double x =
  case x of {
   XI p -> XI (XO p);
   XO p -> XI (pred_double p);
   XH -> XH}

mul :: Positive -> Positive -> Positive
mul x y =
  case x of {
   XI p -> add y (XO (mul p y));
   XO p -> XO (mul p y);
   XH -> y}

compare_cont :: Comparison -> Positive -> Positive -> Comparison
compare_cont r x y =
  case x of {
   XI p ->
    case y of {
     XI q -> compare_cont r p q;
     XO q -> compare_cont Gt p q;
     XH -> Gt};
   XO p ->
    case y of {
     XI q -> compare_cont Lt p q;
     XO q -> compare_cont r p q;
     XH -> Gt};
   XH -> case y of {
          XH -> r;
          _ -> Lt}}

compare :: Positive -> Positive -> Comparison
compare =
  compare_cont Eq

eqb1 :: Positive -> Positive -> Bool
eqb1 p q =
  case p of {
   XI p0 -> case q of {
             XI q0 -> eqb1 p0 q0;
             _ -> False};
   XO p0 -> case q of {
             XO q0 -> eqb1 p0 q0;
             _ -> False};
   XH -> case q of {
          XH -> True;
          _ -> False}}

double :: Z -> Z
double x =
  case x of {
   Z0 -> Z0;
   Zpos p -> Zpos (XO p);
   Zneg p -> Zneg (XO p)}

succ_double :: Z -> Z
succ_double x =
  case x of {
   Z0 -> Zpos XH;
   Zpos p -> Zpos (XI p);
   Zneg p -> Zneg (pred_double p)}

pred_double0 :: Z -> Z
pred_double0 x =
  case x of {
   Z0 -> Zneg XH;
   Zpos p -> Zpos (pred_double p);
   Zneg p -> Zneg (XI p)}

pos_sub :: Positive -> Positive -> Z
pos_sub x y =
  case x of {
   XI p ->
    case y of {
     XI q -> double (pos_sub p q);
     XO q -> succ_double (pos_sub p q);
     XH -> Zpos (XO p)};
   XO p ->
    case y of {
     XI q -> pred_double0 (pos_sub p q);
     XO q -> double (pos_sub p q);
     XH -> Zpos (pred_double p)};
   XH ->
    case y of {
     XI q -> Zneg (XO q);
     XO q -> Zneg (pred_double q);
     XH -> Z0}}

add0 :: Z -> Z -> Z
add0 x y =
  case x of {
   Z0 -> y;
   Zpos x' ->
    case y of {
     Z0 -> x;
     Zpos y' -> Zpos (add x' y');
     Zneg y' -> pos_sub x' y'};
   Zneg x' ->
    case y of {
     Z0 -> x;
     Zpos y' -> pos_sub y' x';
     Zneg y' -> Zneg (add x' y')}}

opp :: Z -> Z
opp x =
  case x of {
   Z0 -> Z0;
   Zpos x0 -> Zneg x0;
   Zneg x0 -> Zpos x0}

sub :: Z -> Z -> Z
sub m n =
  add0 m (opp n)

mul0 :: Z -> Z -> Z
mul0 x y =
  case x of {
   Z0 -> Z0;
   Zpos x' ->
    case y of {
     Z0 -> Z0;
     Zpos y' -> Zpos (mul x' y');
     Zneg y' -> Zneg (mul x' y')};
   Zneg x' ->
    case y of {
     Z0 -> Z0;
     Zpos y' -> Zneg (mul x' y');
     Zneg y' -> Zpos (mul x' y')}}

compare0 :: Z -> Z -> Comparison
compare0 x y =
  case x of {
   Z0 -> case y of {
          Z0 -> Eq;
          Zpos _ -> Lt;
          Zneg _ -> Gt};
   Zpos x' -> case y of {
               Zpos y' -> compare x' y';
               _ -> Gt};
   Zneg x' -> case y of {
               Zneg y' -> compOpp (compare x' y');
               _ -> Lt}}

leb :: Z -> Z -> Bool
leb x y =
  case compare0 x y of {
   Gt -> False;
   _ -> True}

ltb :: Z -> Z -> Bool
ltb x y =
  case compare0 x y of {
   Lt -> True;
   _ -> False}

eqb2 :: Z -> Z -> Bool
eqb2 x y =
  case x of {
   Z0 -> case y of {
          Z0 -> True;
          _ -> False};
   Zpos p -> case y of {
              Zpos q -> eqb1 p q;
              _ -> False};
   Zneg p -> case y of {
              Zneg q -> eqb1 p q;
              _ -> False}}

pos_div_eucl :: Positive -> Z -> Prod Z Z
pos_div_eucl a b =
  case a of {
   XI a' ->
    case pos_div_eucl a' b of {
     Pair q r ->
      let {r' = add0 (mul0 (Zpos (XO XH)) r) (Zpos XH)} in
      case ltb r' b of {
       True -> Pair (mul0 (Zpos (XO XH)) q) r';
       False -> Pair (add0 (mul0 (Zpos (XO XH)) q) (Zpos XH)) (sub r' b)}};
   XO a' ->
    case pos_div_eucl a' b of {
     Pair q r ->
      let {r' = mul0 (Zpos (XO XH)) r} in
      case ltb r' b of {
       True -> Pair (mul0 (Zpos (XO XH)) q) r';
       False -> Pair (add0 (mul0 (Zpos (XO XH)) q) (Zpos XH)) (sub r' b)}};
   XH ->
    case leb (Zpos (XO XH)) b of {
     True -> Pair Z0 (Zpos XH);
     False -> Pair (Zpos XH) Z0}}

div_eucl :: Z -> Z -> Prod Z Z
div_eucl a b =
  case a of {
   Z0 -> Pair Z0 Z0;
   Zpos a' ->
    case b of {
     Z0 -> Pair Z0 Z0;
     Zpos _ -> pos_div_eucl a' b;
     Zneg b' ->
      case pos_div_eucl a' (Zpos b') of {
       Pair q r ->
        case r of {
         Z0 -> Pair (opp q) Z0;
         _ -> Pair (opp (add0 q (Zpos XH))) (add0 b r)}}};
   Zneg a' ->
    case b of {
     Z0 -> Pair Z0 Z0;
     Zpos _ ->
      case pos_div_eucl a' b of {
       Pair q r ->
        case r of {
         Z0 -> Pair (opp q) Z0;
         _ -> Pair (opp (add0 q (Zpos XH))) (sub b r)}};
     Zneg b' ->
      case pos_div_eucl a' (Zpos b') of {
       Pair q r -> Pair q (opp r)}}}

div :: Z -> Z -> Z
div a b =
  case div_eucl a b of {
   Pair q _ -> q}

modulo :: Z -> Z -> Z
modulo a b =
  case div_eucl a b of {
   Pair _ r -> r}

zeq_bool :: Z -> Z -> Bool
zeq_bool x y =
  case compare0 x y of {
   Eq -> True;
   _ -> False}

data Ascii0 =
   Ascii Bool Bool Bool Bool Bool Bool Bool Bool

ascii_rect :: (Bool -> Bool -> Bool -> Bool -> Bool -> Bool -> Bool -> Bool
              -> a1) -> Ascii0 -> a1
ascii_rect f a =
  case a of {
   Ascii x x0 x1 x2 x3 x4 x5 x6 -> f x x0 x1 x2 x3 x4 x5 x6}

ascii_rec :: (Bool -> Bool -> Bool -> Bool -> Bool -> Bool -> Bool -> Bool ->
             a1) -> Ascii0 -> a1
ascii_rec =
  ascii_rect

ascii_dec :: Ascii0 -> Ascii0 -> Sumbool
ascii_dec a b =
  ascii_rec (\b0 b1 b2 b3 b4 b5 b6 b7 x ->
    case x of {
     Ascii b8 b9 b10 b11 b12 b13 b14 b15 ->
      sumbool_rec (\_ ->
        sumbool_rec (\_ ->
          sumbool_rec (\_ ->
            sumbool_rec (\_ ->
              sumbool_rec (\_ ->
                sumbool_rec (\_ ->
                  sumbool_rec (\_ ->
                    sumbool_rec (\_ -> Left) (\_ -> Right) (bool_dec b7 b15))
                    (\_ -> Right) (bool_dec b6 b14)) (\_ -> Right)
                  (bool_dec b5 b13)) (\_ -> Right) (bool_dec b4 b12)) (\_ ->
              Right) (bool_dec b3 b11)) (\_ -> Right) (bool_dec b2 b10))
          (\_ -> Right) (bool_dec b1 b9)) (\_ -> Right) (bool_dec b0 b8)}) a
    b

data String =
   EmptyString
 | String0 Ascii0 String

string_rect :: a1 -> (Ascii0 -> String -> a1 -> a1) -> String -> a1
string_rect f f0 s =
  case s of {
   EmptyString -> f;
   String0 a s0 -> f0 a s0 (string_rect f f0 s0)}

string_rec :: a1 -> (Ascii0 -> String -> a1 -> a1) -> String -> a1
string_rec =
  string_rect

string_dec :: String -> String -> Sumbool
string_dec s1 s2 =
  string_rec (\x -> case x of {
                     EmptyString -> Left;
                     String0 _ _ -> Right}) (\a _ h x ->
    case x of {
     EmptyString -> Right;
     String0 a0 s0 ->
      sumbool_rec (\_ -> sumbool_rec (\_ -> Left) (\_ -> Right) (h s0))
        (\_ -> Right) (ascii_dec a a0)}) s1 s2

data T =
   F1 Nat
 | FS Nat T

data T0 a =
   Nil0
 | Cons0 a Nat (T0 a)

data T1 a =
   Nil1
 | Cons1 a Nat (T1 a)

caseS :: (a1 -> Nat -> (T1 a1) -> a2) -> Nat -> (T1 a1) -> a2
caseS h _ v =
  case v of {
   Nil1 -> __;
   Cons1 h0 n t -> h h0 n t}

nth :: Nat -> (T1 a1) -> T -> a1
nth _ v' p =
  case p of {
   F1 n -> caseS (\h _ _ -> h) n v';
   FS n p' -> caseS (\_ -> nth) n v' p'}

map0 :: (a1 -> a2) -> Nat -> (T1 a1) -> T1 a2
map0 f _ v =
  case v of {
   Nil1 -> Nil1;
   Cons1 a n v' -> Cons1 (f a) n (map0 f n v')}

data Q =
   Qmake Z Positive

qnum :: Q -> Z
qnum q =
  case q of {
   Qmake qnum0 _ -> qnum0}

qden :: Q -> Positive
qden q =
  case q of {
   Qmake _ qden0 -> qden0}

qeq_bool :: Q -> Q -> Bool
qeq_bool x y =
  zeq_bool (mul0 (qnum x) (Zpos (qden y))) (mul0 (qnum y) (Zpos (qden x)))

qle_bool :: Q -> Q -> Bool
qle_bool x y =
  leb (mul0 (qnum x) (Zpos (qden y))) (mul0 (qnum y) (Zpos (qden x)))

qplus :: Q -> Q -> Q
qplus x y =
  Qmake
    (add0 (mul0 (qnum x) (Zpos (qden y))) (mul0 (qnum y) (Zpos (qden x))))
    (mul (qden x) (qden y))

qmult :: Q -> Q -> Q
qmult x y =
  Qmake (mul0 (qnum x) (qnum y)) (mul (qden x) (qden y))

qinv :: Q -> Q
qinv x =
  case qnum x of {
   Z0 -> Qmake Z0 XH;
   Zpos p -> Qmake (Zpos (qden x)) p;
   Zneg p -> Qmake (Zneg (qden x)) p}

qdiv :: Q -> Q -> Q
qdiv x y =
  qmult x (qinv y)

typeErr :: String
typeErr =
  String0 (Ascii False False True False True False True False) (String0
    (Ascii True False False True True True True False) (String0 (Ascii False
    False False False True True True False) (String0 (Ascii True False True
    False False True True False) (String0 (Ascii False False False False
    False True False False) (String0 (Ascii True False True False False True
    True False) (String0 (Ascii False True False False True True True False)
    (String0 (Ascii False True False False True True True False) (String0
    (Ascii True True True True False True True False) (String0 (Ascii False
    True False False True True True False) EmptyString)))))))))

eventNotDeclaredErr :: String
eventNotDeclaredErr =
  String0 (Ascii True False True False False True True False) (String0 (Ascii
    False True True False True True True False) (String0 (Ascii True False
    True False False True True False) (String0 (Ascii False True True True
    False True True False) (String0 (Ascii False False True False True True
    True False) (String0 (Ascii False False False False False True False
    False) (String0 (Ascii False True True True False True True False)
    (String0 (Ascii True True True True False True True False) (String0
    (Ascii False False True False True True True False) (String0 (Ascii False
    False False False False True False False) (String0 (Ascii False False
    True False False True True False) (String0 (Ascii True False True False
    False True True False) (String0 (Ascii True True False False False True
    True False) (String0 (Ascii False False True True False True True False)
    (String0 (Ascii True False False False False True True False) (String0
    (Ascii False True False False True True True False) (String0 (Ascii True
    False True False False True True False) (String0 (Ascii False False True
    False False True True False) EmptyString)))))))))))))))))

data ErrorOrResult t =
   Result t
 | Error String

internal_bool_beq :: Bool -> Bool -> Bool
internal_bool_beq x y =
  case x of {
   True -> y;
   False -> case y of {
             True -> False;
             False -> True}}

internal_ascii_beq :: Ascii0 -> Ascii0 -> Bool
internal_ascii_beq x y =
  case x of {
   Ascii x0 x1 x2 x3 x4 x5 x6 x7 ->
    case y of {
     Ascii x8 x9 x10 x11 x12 x13 x14 x15 ->
      andb (internal_bool_beq x0 x8)
        (andb (internal_bool_beq x1 x9)
          (andb (internal_bool_beq x2 x10)
            (andb (internal_bool_beq x3 x11)
              (andb (internal_bool_beq x4 x12)
                (andb (internal_bool_beq x5 x13)
                  (andb (internal_bool_beq x6 x14)
                    (internal_bool_beq x7 x15)))))))}}

internal_string_beq :: String -> String -> Bool
internal_string_beq x y =
  case x of {
   EmptyString -> case y of {
                   EmptyString -> True;
                   String0 _ _ -> False};
   String0 x0 x1 ->
    case y of {
     EmptyString -> False;
     String0 x2 x3 ->
      andb (internal_ascii_beq x0 x2) (internal_string_beq x1 x3)}}

data Typ =
   Int
 | Float
 | Str
 | Bool0
 | Pointer
 | Opaque
 | Thread

typ_rect :: a1 -> a1 -> a1 -> a1 -> a1 -> a1 -> a1 -> Typ -> a1
typ_rect f f0 f1 f2 f3 f4 f5 t =
  case t of {
   Int -> f;
   Float -> f0;
   Str -> f1;
   Bool0 -> f2;
   Pointer -> f3;
   Opaque -> f4;
   Thread -> f5}

typ_rec :: a1 -> a1 -> a1 -> a1 -> a1 -> a1 -> a1 -> Typ -> a1
typ_rec =
  typ_rect

internal_typ_beq :: Typ -> Typ -> Bool
internal_typ_beq x y =
  case x of {
   Int -> case y of {
           Int -> True;
           _ -> False};
   Float -> case y of {
             Float -> True;
             _ -> False};
   Str -> case y of {
           Str -> True;
           _ -> False};
   Bool0 -> case y of {
             Bool0 -> True;
             _ -> False};
   Pointer -> case y of {
               Pointer -> True;
               _ -> False};
   Opaque -> case y of {
              Opaque -> True;
              _ -> False};
   Thread -> case y of {
              Thread -> True;
              _ -> False}}

typ_eq_dec :: Typ -> Typ -> Sumbool
typ_eq_dec x y =
  let {b = internal_typ_beq x y} in case b of {
                                     True -> Left;
                                     False -> Right}

data Atom =
   AInt Z
 | AFloat Q
 | AIdent String
 | ABool Bool
 | ANull
 | AString String

atom_rect :: (Z -> a1) -> (Q -> a1) -> (String -> a1) -> (Bool -> a1) -> a1
             -> (String -> a1) -> Atom -> a1
atom_rect f f0 f1 f2 f3 f4 a =
  case a of {
   AInt x -> f x;
   AFloat x -> f0 x;
   AIdent x -> f1 x;
   ABool x -> f2 x;
   ANull -> f3;
   AString x -> f4 x}

atom_rec :: (Z -> a1) -> (Q -> a1) -> (String -> a1) -> (Bool -> a1) -> a1 ->
            (String -> a1) -> Atom -> a1
atom_rec =
  atom_rect

internal_positive_beq :: Positive -> Positive -> Bool
internal_positive_beq x y =
  case x of {
   XI x0 -> case y of {
             XI x1 -> internal_positive_beq x0 x1;
             _ -> False};
   XO x0 -> case y of {
             XO x1 -> internal_positive_beq x0 x1;
             _ -> False};
   XH -> case y of {
          XH -> True;
          _ -> False}}

internal_Z_beq :: Z -> Z -> Bool
internal_Z_beq x y =
  case x of {
   Z0 -> case y of {
          Z0 -> True;
          _ -> False};
   Zpos x0 -> case y of {
               Zpos x1 -> internal_positive_beq x0 x1;
               _ -> False};
   Zneg x0 -> case y of {
               Zneg x1 -> internal_positive_beq x0 x1;
               _ -> False}}

internal_Q_beq :: Q -> Q -> Bool
internal_Q_beq x y =
  case x of {
   Qmake qnum0 qden0 ->
    case y of {
     Qmake qnum1 qden1 ->
      andb (internal_Z_beq qnum0 qnum1) (internal_positive_beq qden0 qden1)}}

internal_atom_beq :: Atom -> Atom -> Bool
internal_atom_beq x y =
  case x of {
   AInt x0 -> case y of {
               AInt x1 -> internal_Z_beq x0 x1;
               _ -> False};
   AFloat x0 -> case y of {
                 AFloat x1 -> internal_Q_beq x0 x1;
                 _ -> False};
   AIdent x0 ->
    case y of {
     AIdent x1 -> internal_string_beq x0 x1;
     _ -> False};
   ABool x0 -> case y of {
                ABool x1 -> internal_bool_beq x0 x1;
                _ -> False};
   ANull -> case y of {
             ANull -> True;
             _ -> False};
   AString x0 ->
    case y of {
     AString x1 -> internal_string_beq x0 x1;
     _ -> False}}

atom_eq_dec :: Atom -> Atom -> Sumbool
atom_eq_dec x y =
  let {b = internal_atom_beq x y} in
  case b of {
   True -> Left;
   False -> Right}

type Typ_env = List (Prod Atom Typ)

type Range_typ = Sum (Sum (Sum (Sum Z Q) String) Bool) Nat

range_typ_dec :: Range_typ -> Range_typ -> Sumbool
range_typ_dec re re' =
  sum_rec (\a x ->
    case x of {
     Inl s ->
      sumbool_rec (\_ -> Left) (\_ -> Right)
        (sum_rec (\a0 x0 ->
          case x0 of {
           Inl s0 ->
            sumbool_rec (\_ -> Left) (\_ -> Right)
              (sum_rec (\a1 x1 ->
                case x1 of {
                 Inl s1 ->
                  sumbool_rec (\_ -> Left) (\_ -> Right)
                    (sum_rec (\a2 x2 ->
                      case x2 of {
                       Inl z ->
                        sumbool_rec (\_ -> Left) (\_ -> Right)
                          (z_rec (\x3 ->
                            case x3 of {
                             Z0 -> Left;
                             _ -> Right}) (\p x3 ->
                            case x3 of {
                             Zpos p0 ->
                              sumbool_rec (\_ -> Left) (\_ -> Right)
                                (positive_rec (\_ h x4 ->
                                  case x4 of {
                                   XI p2 ->
                                    sumbool_rec (\_ -> Left) (\_ -> Right)
                                      (h p2);
                                   _ -> Right}) (\_ h x4 ->
                                  case x4 of {
                                   XO p2 ->
                                    sumbool_rec (\_ -> Left) (\_ -> Right)
                                      (h p2);
                                   _ -> Right}) (\x4 ->
                                  case x4 of {
                                   XH -> Left;
                                   _ -> Right}) p p0);
                             _ -> Right}) (\p x3 ->
                            case x3 of {
                             Zneg p0 ->
                              sumbool_rec (\_ -> Left) (\_ -> Right)
                                (positive_rec (\_ h x4 ->
                                  case x4 of {
                                   XI p2 ->
                                    sumbool_rec (\_ -> Left) (\_ -> Right)
                                      (h p2);
                                   _ -> Right}) (\_ h x4 ->
                                  case x4 of {
                                   XO p2 ->
                                    sumbool_rec (\_ -> Left) (\_ -> Right)
                                      (h p2);
                                   _ -> Right}) (\x4 ->
                                  case x4 of {
                                   XH -> Left;
                                   _ -> Right}) p p0);
                             _ -> Right}) a2 z);
                       Inr _ -> Right}) (\b x2 ->
                      case x2 of {
                       Inl _ -> Right;
                       Inr q ->
                        sumbool_rec (\_ -> Left) (\_ -> Right)
                          (case b of {
                            Qmake qnum0 qden0 ->
                             case q of {
                              Qmake qnum1 qden1 ->
                               sumbool_rec (\_ ->
                                 sumbool_rec (\_ -> Left) (\_ -> Right)
                                   (positive_rec (\_ h x3 ->
                                     case x3 of {
                                      XI p0 ->
                                       sumbool_rec (\_ -> Left) (\_ -> Right)
                                         (h p0);
                                      _ -> Right}) (\_ h x3 ->
                                     case x3 of {
                                      XO p0 ->
                                       sumbool_rec (\_ -> Left) (\_ -> Right)
                                         (h p0);
                                      _ -> Right}) (\x3 ->
                                     case x3 of {
                                      XH -> Left;
                                      _ -> Right}) qden0 qden1)) (\_ ->
                                 Right)
                                 (z_rec (\x3 ->
                                   case x3 of {
                                    Z0 -> Left;
                                    _ -> Right}) (\p x3 ->
                                   case x3 of {
                                    Zpos p0 ->
                                     sumbool_rec (\_ -> Left) (\_ -> Right)
                                       (positive_rec (\_ h x4 ->
                                         case x4 of {
                                          XI p2 ->
                                           sumbool_rec (\_ -> Left) (\_ ->
                                             Right) (h p2);
                                          _ -> Right}) (\_ h x4 ->
                                         case x4 of {
                                          XO p2 ->
                                           sumbool_rec (\_ -> Left) (\_ ->
                                             Right) (h p2);
                                          _ -> Right}) (\x4 ->
                                         case x4 of {
                                          XH -> Left;
                                          _ -> Right}) p p0);
                                    _ -> Right}) (\p x3 ->
                                   case x3 of {
                                    Zneg p0 ->
                                     sumbool_rec (\_ -> Left) (\_ -> Right)
                                       (positive_rec (\_ h x4 ->
                                         case x4 of {
                                          XI p2 ->
                                           sumbool_rec (\_ -> Left) (\_ ->
                                             Right) (h p2);
                                          _ -> Right}) (\_ h x4 ->
                                         case x4 of {
                                          XO p2 ->
                                           sumbool_rec (\_ -> Left) (\_ ->
                                             Right) (h p2);
                                          _ -> Right}) (\x4 ->
                                         case x4 of {
                                          XH -> Left;
                                          _ -> Right}) p p0);
                                    _ -> Right}) qnum0 qnum1)}})}) a1 s1);
                 Inr _ -> Right}) (\b x1 ->
                case x1 of {
                 Inl _ -> Right;
                 Inr s1 ->
                  sumbool_rec (\_ -> Left) (\_ -> Right)
                    (string_rec (\x2 ->
                      case x2 of {
                       EmptyString -> Left;
                       String0 _ _ -> Right}) (\a1 _ h x2 ->
                      case x2 of {
                       EmptyString -> Right;
                       String0 a2 s3 ->
                        sumbool_rec (\_ ->
                          sumbool_rec (\_ -> Left) (\_ -> Right) (h s3))
                          (\_ -> Right)
                          (ascii_rec (\b0 b1 b2 b3 b4 b5 b6 b7 x3 ->
                            case x3 of {
                             Ascii b8 b9 b10 b11 b12 b13 b14 b15 ->
                              sumbool_rec (\_ ->
                                sumbool_rec (\_ ->
                                  sumbool_rec (\_ ->
                                    sumbool_rec (\_ ->
                                      sumbool_rec (\_ ->
                                        sumbool_rec (\_ ->
                                          sumbool_rec (\_ ->
                                            sumbool_rec (\_ -> Left) (\_ ->
                                              Right)
                                              (bool_rec (\x4 ->
                                                case x4 of {
                                                 True -> Left;
                                                 False -> Right}) (\x4 ->
                                                case x4 of {
                                                 True -> Right;
                                                 False -> Left}) b7 b15))
                                            (\_ -> Right)
                                            (bool_rec (\x4 ->
                                              case x4 of {
                                               True -> Left;
                                               False -> Right}) (\x4 ->
                                              case x4 of {
                                               True -> Right;
                                               False -> Left}) b6 b14))
                                          (\_ -> Right)
                                          (bool_rec (\x4 ->
                                            case x4 of {
                                             True -> Left;
                                             False -> Right}) (\x4 ->
                                            case x4 of {
                                             True -> Right;
                                             False -> Left}) b5 b13)) (\_ ->
                                        Right)
                                        (bool_rec (\x4 ->
                                          case x4 of {
                                           True -> Left;
                                           False -> Right}) (\x4 ->
                                          case x4 of {
                                           True -> Right;
                                           False -> Left}) b4 b12)) (\_ ->
                                      Right)
                                      (bool_rec (\x4 ->
                                        case x4 of {
                                         True -> Left;
                                         False -> Right}) (\x4 ->
                                        case x4 of {
                                         True -> Right;
                                         False -> Left}) b3 b11)) (\_ ->
                                    Right)
                                    (bool_rec (\x4 ->
                                      case x4 of {
                                       True -> Left;
                                       False -> Right}) (\x4 ->
                                      case x4 of {
                                       True -> Right;
                                       False -> Left}) b2 b10)) (\_ -> Right)
                                  (bool_rec (\x4 ->
                                    case x4 of {
                                     True -> Left;
                                     False -> Right}) (\x4 ->
                                    case x4 of {
                                     True -> Right;
                                     False -> Left}) b1 b9)) (\_ -> Right)
                                (bool_rec (\x4 ->
                                  case x4 of {
                                   True -> Left;
                                   False -> Right}) (\x4 ->
                                  case x4 of {
                                   True -> Right;
                                   False -> Left}) b0 b8)}) a1 a2)}) b s1)})
                a0 s0);
           Inr _ -> Right}) (\b x0 ->
          case x0 of {
           Inl _ -> Right;
           Inr b0 ->
            sumbool_rec (\_ -> Left) (\_ -> Right)
              (bool_rec (\x1 -> case x1 of {
                                 True -> Left;
                                 False -> Right}) (\x1 ->
                case x1 of {
                 True -> Right;
                 False -> Left}) b b0)}) a s);
     Inr _ -> Right}) (\b x ->
    case x of {
     Inl _ -> Right;
     Inr n ->
      sumbool_rec (\_ -> Left) (\_ -> Right)
        (nat_rec (\x0 -> case x0 of {
                          O -> Left;
                          S _ -> Right}) (\_ h x0 ->
          case x0 of {
           O -> Right;
           S n1 -> sumbool_rec (\_ -> Left) (\_ -> Right) (h n1)}) b n)}) re
    re'

type Value_env = List (Prod Atom (Prod Typ Range_typ))

typeValMatch :: Typ -> Range_typ -> Bool
typeValMatch t v =
  case t of {
   Int ->
    case v of {
     Inl s ->
      case s of {
       Inl s0 ->
        case s0 of {
         Inl s1 -> case s1 of {
                    Inl _ -> True;
                    Inr _ -> False};
         Inr _ -> False};
       Inr _ -> False};
     Inr _ -> False};
   Float ->
    case v of {
     Inl s ->
      case s of {
       Inl s0 ->
        case s0 of {
         Inl s1 -> case s1 of {
                    Inl _ -> False;
                    Inr _ -> True};
         Inr _ -> False};
       Inr _ -> False};
     Inr _ -> False};
   Str ->
    case v of {
     Inl s ->
      case s of {
       Inl s0 -> case s0 of {
                  Inl _ -> False;
                  Inr _ -> True};
       Inr _ -> False};
     Inr _ -> False};
   Bool0 ->
    case v of {
     Inl s -> case s of {
               Inl _ -> False;
               Inr _ -> True};
     Inr _ -> False};
   _ -> case v of {
         Inl _ -> False;
         Inr _ -> True}}

dom :: (List (Prod a1 a2)) -> List a1
dom env =
  map fst env

string_dec_bool :: String -> String -> Bool
string_dec_bool s1 s2 =
  case string_dec s1 s2 of {
   Left -> True;
   Right -> False}

inList :: (a1 -> a1 -> Sumbool) -> a1 -> (List a1) -> Bool
inList decA x lst =
  case lst of {
   Nil -> False;
   Cons y lst' ->
    case decA x y of {
     Left -> True;
     Right -> inList decA x lst'}}

updateValueEnvInv :: Atom -> Range_typ -> Value_env -> Option Value_env
updateValueEnvInv a v en =
  case a of {
   AIdent _ ->
    case en of {
     Nil -> Some Nil;
     Cons p en' ->
      case p of {
       Pair a' p0 ->
        case p0 of {
         Pair t' v' ->
          case atom_eq_dec a a' of {
           Left ->
            case typeValMatch t' v of {
             True -> Some (Cons (Pair a' (Pair t' v)) en');
             False -> None};
           Right ->
            case updateValueEnvInv a v en' of {
             Some ven' -> Some (Cons (Pair a' (Pair t' v')) ven');
             None -> None}}}}};
   _ -> None}

createValueEnv :: (List String) -> (List Typ) -> (List Range_typ) ->
                  ErrorOrResult (List (Prod Atom (Prod Typ Range_typ)))
createValueEnv nlst tlst vlst =
  case nlst of {
   Nil ->
    case tlst of {
     Nil ->
      case vlst of {
       Nil -> Result Nil;
       Cons _ _ -> Error (String0 (Ascii False True True True False True True
        False) (String0 (Ascii True False True False True True True False)
        (String0 (Ascii True False True True False True True False) (String0
        (Ascii False True False False False True True False) (String0 (Ascii
        True False True False False True True False) (String0 (Ascii False
        True False False True True True False) (String0 (Ascii False False
        False False False True False False) (String0 (Ascii True True True
        True False True True False) (String0 (Ascii False True True False
        False True True False) (String0 (Ascii False False False False False
        True False False) (String0 (Ascii False False True True False True
        True False) (String0 (Ascii True False False True False True True
        False) (String0 (Ascii True True False False True True True False)
        (String0 (Ascii False False True False True True True False) (String0
        (Ascii False False False False False True False False) (String0
        (Ascii False True True True False True True False) (String0 (Ascii
        True True True True False True True False) (String0 (Ascii False
        False True False True True True False) (String0 (Ascii False False
        False False False True False False) (String0 (Ascii True False True
        True False True True False) (String0 (Ascii True False False False
        False True True False) (String0 (Ascii False False True False True
        True True False) (String0 (Ascii True True False False False True
        True False) (String0 (Ascii False False False True False True True
        False) (String0 (Ascii True False True False False True True False)
        (String0 (Ascii False False True False False True True False)
        EmptyString))))))))))))))))))))))))))};
     Cons _ _ -> Error (String0 (Ascii False True True True False True True
      False) (String0 (Ascii True False True False True True True False)
      (String0 (Ascii True False True True False True True False) (String0
      (Ascii False True False False False True True False) (String0 (Ascii
      True False True False False True True False) (String0 (Ascii False True
      False False True True True False) (String0 (Ascii False False False
      False False True False False) (String0 (Ascii True True True True False
      True True False) (String0 (Ascii False True True False False True True
      False) (String0 (Ascii False False False False False True False False)
      (String0 (Ascii False False True True False True True False) (String0
      (Ascii True False False True False True True False) (String0 (Ascii
      True True False False True True True False) (String0 (Ascii False False
      True False True True True False) (String0 (Ascii False False False
      False False True False False) (String0 (Ascii False True True True
      False True True False) (String0 (Ascii True True True True False True
      True False) (String0 (Ascii False False True False True True True
      False) (String0 (Ascii False False False False False True False False)
      (String0 (Ascii True False True True False True True False) (String0
      (Ascii True False False False False True True False) (String0 (Ascii
      False False True False True True True False) (String0 (Ascii True True
      False False False True True False) (String0 (Ascii False False False
      True False True True False) (String0 (Ascii True False True False False
      True True False) (String0 (Ascii False False True False False True True
      False) EmptyString))))))))))))))))))))))))))};
   Cons s nlst' ->
    case tlst of {
     Nil -> Error (String0 (Ascii False True True True False True True False)
      (String0 (Ascii True False True False True True True False) (String0
      (Ascii True False True True False True True False) (String0 (Ascii
      False True False False False True True False) (String0 (Ascii True
      False True False False True True False) (String0 (Ascii False True
      False False True True True False) (String0 (Ascii False False False
      False False True False False) (String0 (Ascii True True True True False
      True True False) (String0 (Ascii False True True False False True True
      False) (String0 (Ascii False False False False False True False False)
      (String0 (Ascii False False True True False True True False) (String0
      (Ascii True False False True False True True False) (String0 (Ascii
      True True False False True True True False) (String0 (Ascii False False
      True False True True True False) (String0 (Ascii False False False
      False False True False False) (String0 (Ascii False True True True
      False True True False) (String0 (Ascii True True True True False True
      True False) (String0 (Ascii False False True False True True True
      False) (String0 (Ascii False False False False False True False False)
      (String0 (Ascii True False True True False True True False) (String0
      (Ascii True False False False False True True False) (String0 (Ascii
      False False True False True True True False) (String0 (Ascii True True
      False False False True True False) (String0 (Ascii False False False
      True False True True False) (String0 (Ascii True False True False False
      True True False) (String0 (Ascii False False True False False True True
      False) EmptyString))))))))))))))))))))))))));
     Cons t tlst' ->
      case vlst of {
       Nil -> Error (String0 (Ascii False True True True False True True
        False) (String0 (Ascii True False True False True True True False)
        (String0 (Ascii True False True True False True True False) (String0
        (Ascii False True False False False True True False) (String0 (Ascii
        True False True False False True True False) (String0 (Ascii False
        True False False True True True False) (String0 (Ascii False False
        False False False True False False) (String0 (Ascii True True True
        True False True True False) (String0 (Ascii False True True False
        False True True False) (String0 (Ascii False False False False False
        True False False) (String0 (Ascii False False True True False True
        True False) (String0 (Ascii True False False True False True True
        False) (String0 (Ascii True True False False True True True False)
        (String0 (Ascii False False True False True True True False) (String0
        (Ascii False False False False False True False False) (String0
        (Ascii False True True True False True True False) (String0 (Ascii
        True True True True False True True False) (String0 (Ascii False
        False True False True True True False) (String0 (Ascii False False
        False False False True False False) (String0 (Ascii True False True
        True False True True False) (String0 (Ascii True False False False
        False True True False) (String0 (Ascii False False True False True
        True True False) (String0 (Ascii True True False False False True
        True False) (String0 (Ascii False False False True False True True
        False) (String0 (Ascii True False True False False True True False)
        (String0 (Ascii False False True False False True True False)
        EmptyString))))))))))))))))))))))))));
       Cons v vlst' ->
        case createValueEnv nlst' tlst' vlst' of {
         Result ve -> Result (Cons (Pair (AIdent s) (Pair t v)) ve);
         Error s0 -> Error s0}}}}

getValue :: Atom -> Value_env -> Option Range_typ
getValue a en =
  case a of {
   AIdent _ ->
    case en of {
     Nil -> None;
     Cons p en' ->
      case p of {
       Pair a' p0 ->
        case p0 of {
         Pair _ v ->
          case atom_eq_dec a a' of {
           Left -> Some v;
           Right -> getValue a en'}}}};
   _ -> None}

extendValEnv :: Value_env -> Value_env -> Value_env
extendValEnv =
  app

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

internal_expr_beq :: Expr -> Expr -> Bool
internal_expr_beq x y =
  case x of {
   EOr x0 x1 ->
    case y of {
     EOr x2 x3 -> andb (internal_expr_beq x0 x2) (internal_expr_beq x1 x3);
     _ -> False};
   EAnd x0 x1 ->
    case y of {
     EAnd x2 x3 -> andb (internal_expr_beq x0 x2) (internal_expr_beq x1 x3);
     _ -> False};
   EEq x0 x1 ->
    case y of {
     EEq x2 x3 -> andb (internal_expr_beq x0 x2) (internal_expr_beq x1 x3);
     _ -> False};
   ELt x0 x1 ->
    case y of {
     ELt x2 x3 -> andb (internal_expr_beq x0 x2) (internal_expr_beq x1 x3);
     _ -> False};
   ELe x0 x1 ->
    case y of {
     ELe x2 x3 -> andb (internal_expr_beq x0 x2) (internal_expr_beq x1 x3);
     _ -> False};
   EPlus x0 x1 ->
    case y of {
     EPlus x2 x3 -> andb (internal_expr_beq x0 x2) (internal_expr_beq x1 x3);
     _ -> False};
   EMult x0 x1 ->
    case y of {
     EMult x2 x3 -> andb (internal_expr_beq x0 x2) (internal_expr_beq x1 x3);
     _ -> False};
   EDiv x0 x1 ->
    case y of {
     EDiv x2 x3 -> andb (internal_expr_beq x0 x2) (internal_expr_beq x1 x3);
     _ -> False};
   EMod x0 x1 ->
    case y of {
     EMod x2 x3 -> andb (internal_expr_beq x0 x2) (internal_expr_beq x1 x3);
     _ -> False};
   ENot x0 -> case y of {
               ENot x1 -> internal_expr_beq x0 x1;
               _ -> False};
   EAtom x0 -> case y of {
                EAtom x1 -> internal_atom_beq x0 x1;
                _ -> False}}

expr_eq_dec :: Expr -> Expr -> Sumbool
expr_eq_dec x y =
  let {b = internal_expr_beq x y} in
  case b of {
   True -> Left;
   False -> Right}

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

eventKind_beq :: EventKind -> EventKind -> Bool
eventKind_beq n m =
  case n of {
   Internal -> case m of {
                Internal -> True;
                _ -> False};
   Imported -> case m of {
                Imported -> True;
                _ -> False};
   Exported -> case m of {
                Exported -> True;
                _ -> False}}

data Event_definition =
   Build_event_definition EventKind String (List Typ)

eventKind :: Event_definition -> EventKind
eventKind e =
  case e of {
   Build_event_definition eventKind0 _ _ -> eventKind0}

eventId :: Event_definition -> String
eventId e =
  case e of {
   Build_event_definition _ eventId0 _ -> eventId0}

eventParams :: Event_definition -> List Typ
eventParams e =
  case e of {
   Build_event_definition _ _ eventParams0 -> eventParams0}

event_definition_dec :: Event_definition -> Event_definition -> Sumbool
event_definition_dec n m =
  case n of {
   Build_event_definition eventKind0 eventId0 eventParams0 ->
    case m of {
     Build_event_definition eventKind1 eventId1 eventParams1 ->
      sumbool_rec (\_ ->
        sumbool_rec (\_ ->
          sumbool_rec (\_ -> Left) (\_ -> Right)
            (list_rec (\x -> case x of {
                              Nil -> Left;
                              Cons _ _ -> Right}) (\a1 _ h x ->
              case x of {
               Nil -> Right;
               Cons t l0 ->
                sumbool_rec (\_ ->
                  sumbool_rec (\_ -> Left) (\_ -> Right) (h l0)) (\_ ->
                  Right)
                  (typ_rec (\x0 -> case x0 of {
                                    Int -> Left;
                                    _ -> Right}) (\x0 ->
                    case x0 of {
                     Float -> Left;
                     _ -> Right}) (\x0 ->
                    case x0 of {
                     Str -> Left;
                     _ -> Right}) (\x0 ->
                    case x0 of {
                     Bool0 -> Left;
                     _ -> Right}) (\x0 ->
                    case x0 of {
                     Pointer -> Left;
                     _ -> Right}) (\x0 ->
                    case x0 of {
                     Opaque -> Left;
                     _ -> Right}) (\x0 ->
                    case x0 of {
                     Thread -> Left;
                     _ -> Right}) a1 t)}) eventParams0 eventParams1)) (\_ ->
          Right)
          (string_rec (\x ->
            case x of {
             EmptyString -> Left;
             String0 _ _ -> Right}) (\a0 _ h x ->
            case x of {
             EmptyString -> Right;
             String0 a1 s0 ->
              sumbool_rec (\_ ->
                sumbool_rec (\_ -> Left) (\_ -> Right) (h s0)) (\_ -> Right)
                (ascii_rec (\b b0 b1 b2 b3 b4 b5 b6 x0 ->
                  case x0 of {
                   Ascii b7 b8 b9 b10 b11 b12 b13 b14 ->
                    sumbool_rec (\_ ->
                      sumbool_rec (\_ ->
                        sumbool_rec (\_ ->
                          sumbool_rec (\_ ->
                            sumbool_rec (\_ ->
                              sumbool_rec (\_ ->
                                sumbool_rec (\_ ->
                                  sumbool_rec (\_ -> Left) (\_ -> Right)
                                    (bool_rec (\x1 ->
                                      case x1 of {
                                       True -> Left;
                                       False -> Right}) (\x1 ->
                                      case x1 of {
                                       True -> Right;
                                       False -> Left}) b6 b14)) (\_ -> Right)
                                  (bool_rec (\x1 ->
                                    case x1 of {
                                     True -> Left;
                                     False -> Right}) (\x1 ->
                                    case x1 of {
                                     True -> Right;
                                     False -> Left}) b5 b13)) (\_ -> Right)
                                (bool_rec (\x1 ->
                                  case x1 of {
                                   True -> Left;
                                   False -> Right}) (\x1 ->
                                  case x1 of {
                                   True -> Right;
                                   False -> Left}) b4 b12)) (\_ -> Right)
                              (bool_rec (\x1 ->
                                case x1 of {
                                 True -> Left;
                                 False -> Right}) (\x1 ->
                                case x1 of {
                                 True -> Right;
                                 False -> Left}) b3 b11)) (\_ -> Right)
                            (bool_rec (\x1 ->
                              case x1 of {
                               True -> Left;
                               False -> Right}) (\x1 ->
                              case x1 of {
                               True -> Right;
                               False -> Left}) b2 b10)) (\_ -> Right)
                          (bool_rec (\x1 ->
                            case x1 of {
                             True -> Left;
                             False -> Right}) (\x1 ->
                            case x1 of {
                             True -> Right;
                             False -> Left}) b1 b9)) (\_ -> Right)
                        (bool_rec (\x1 ->
                          case x1 of {
                           True -> Left;
                           False -> Right}) (\x1 ->
                          case x1 of {
                           True -> Right;
                           False -> Left}) b0 b8)) (\_ -> Right)
                      (bool_rec (\x1 ->
                        case x1 of {
                         True -> Left;
                         False -> Right}) (\x1 ->
                        case x1 of {
                         True -> Right;
                         False -> Left}) b b7)}) a0 a1)}) eventId0 eventId1))
        (\_ -> Right)
        (eventKind_rec (\x -> case x of {
                               Internal -> Left;
                               _ -> Right}) (\x ->
          case x of {
           Imported -> Left;
           _ -> Right}) (\x -> case x of {
                                Exported -> Left;
                                _ -> Right}) eventKind0 eventKind1)}}

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
 | RaiseStmt String (List Expr)
 | Seq Action Action

action_rect :: a1 -> (LValue -> Expr -> a1) -> (String -> (List Expr) -> a1)
               -> (Action -> a1 -> Action -> a1 -> a1) -> Action -> a1
action_rect f f0 f1 f2 a =
  case a of {
   Skip -> f;
   StateUpdate l e -> f0 l e;
   RaiseStmt ident exprs -> f1 ident exprs;
   Seq a0 a1 ->
    f2 a0 (action_rect f f0 f1 f2 a0) a1 (action_rect f f0 f1 f2 a1)}

action_rec :: a1 -> (LValue -> Expr -> a1) -> (String -> (List Expr) -> a1)
              -> (Action -> a1 -> Action -> a1 -> a1) -> Action -> a1
action_rec =
  action_rect

data Event_instance =
   Build_event_instance Event_definition (List String) Expr

eventArgs :: Event_instance -> List String
eventArgs e =
  case e of {
   Build_event_instance _ eventArgs0 _ -> eventArgs0}

eventWhenExpr :: Event_instance -> Expr
eventWhenExpr e =
  case e of {
   Build_event_instance _ _ eventWhenExpr0 -> eventWhenExpr0}

event_instance_dec :: Event_instance -> Event_instance -> Sumbool
event_instance_dec n m =
  case n of {
   Build_event_instance event0 eventArgs0 eventWhenExpr0 ->
    case m of {
     Build_event_instance event1 eventArgs1 eventWhenExpr1 ->
      sumbool_rec (\_ ->
        sumbool_rec (\_ ->
          sumbool_rec (\_ -> Left) (\_ -> Right)
            (expr_rec (\_ h0 _ h1 x ->
              case x of {
               EOr e1 e2 ->
                sumbool_rec (\_ ->
                  sumbool_rec (\_ -> Left) (\_ -> Right) (h1 e2)) (\_ ->
                  Right) (h0 e1);
               _ -> Right}) (\_ h0 _ h1 x ->
              case x of {
               EAnd e1 e2 ->
                sumbool_rec (\_ ->
                  sumbool_rec (\_ -> Left) (\_ -> Right) (h1 e2)) (\_ ->
                  Right) (h0 e1);
               _ -> Right}) (\_ h0 _ h1 x ->
              case x of {
               EEq e1 e2 ->
                sumbool_rec (\_ ->
                  sumbool_rec (\_ -> Left) (\_ -> Right) (h1 e2)) (\_ ->
                  Right) (h0 e1);
               _ -> Right}) (\_ h0 _ h1 x ->
              case x of {
               ELt e1 e2 ->
                sumbool_rec (\_ ->
                  sumbool_rec (\_ -> Left) (\_ -> Right) (h1 e2)) (\_ ->
                  Right) (h0 e1);
               _ -> Right}) (\_ h0 _ h1 x ->
              case x of {
               ELe e1 e2 ->
                sumbool_rec (\_ ->
                  sumbool_rec (\_ -> Left) (\_ -> Right) (h1 e2)) (\_ ->
                  Right) (h0 e1);
               _ -> Right}) (\_ h0 _ h1 x ->
              case x of {
               EPlus e1 e2 ->
                sumbool_rec (\_ ->
                  sumbool_rec (\_ -> Left) (\_ -> Right) (h1 e2)) (\_ ->
                  Right) (h0 e1);
               _ -> Right}) (\_ h0 _ h1 x ->
              case x of {
               EMult e1 e2 ->
                sumbool_rec (\_ ->
                  sumbool_rec (\_ -> Left) (\_ -> Right) (h1 e2)) (\_ ->
                  Right) (h0 e1);
               _ -> Right}) (\_ h0 _ h1 x ->
              case x of {
               EDiv e1 e2 ->
                sumbool_rec (\_ ->
                  sumbool_rec (\_ -> Left) (\_ -> Right) (h1 e2)) (\_ ->
                  Right) (h0 e1);
               _ -> Right}) (\_ h0 _ h1 x ->
              case x of {
               EMod e1 e2 ->
                sumbool_rec (\_ ->
                  sumbool_rec (\_ -> Left) (\_ -> Right) (h1 e2)) (\_ ->
                  Right) (h0 e1);
               _ -> Right}) (\_ h0 x ->
              case x of {
               ENot e0 -> sumbool_rec (\_ -> Left) (\_ -> Right) (h0 e0);
               _ -> Right}) (\a1 x ->
              case x of {
               EAtom a2 ->
                sumbool_rec (\_ -> Left) (\_ -> Right) (atom_eq_dec a1 a2);
               _ -> Right}) eventWhenExpr0 eventWhenExpr1)) (\_ -> Right)
          (list_rec (\x -> case x of {
                            Nil -> Left;
                            Cons _ _ -> Right}) (\a0 _ h0 x ->
            case x of {
             Nil -> Right;
             Cons s l0 ->
              sumbool_rec (\_ ->
                sumbool_rec (\_ -> Left) (\_ -> Right) (h0 l0)) (\_ -> Right)
                (string_rec (\x0 ->
                  case x0 of {
                   EmptyString -> Left;
                   String0 _ _ -> Right}) (\a1 _ h1 x0 ->
                  case x0 of {
                   EmptyString -> Right;
                   String0 a2 s1 ->
                    sumbool_rec (\_ ->
                      sumbool_rec (\_ -> Left) (\_ -> Right) (h1 s1)) (\_ ->
                      Right)
                      (ascii_rec (\b b0 b1 b2 b3 b4 b5 b6 x1 ->
                        case x1 of {
                         Ascii b7 b8 b9 b10 b11 b12 b13 b14 ->
                          sumbool_rec (\_ ->
                            sumbool_rec (\_ ->
                              sumbool_rec (\_ ->
                                sumbool_rec (\_ ->
                                  sumbool_rec (\_ ->
                                    sumbool_rec (\_ ->
                                      sumbool_rec (\_ ->
                                        sumbool_rec (\_ -> Left) (\_ ->
                                          Right)
                                          (bool_rec (\x2 ->
                                            case x2 of {
                                             True -> Left;
                                             False -> Right}) (\x2 ->
                                            case x2 of {
                                             True -> Right;
                                             False -> Left}) b6 b14)) (\_ ->
                                        Right)
                                        (bool_rec (\x2 ->
                                          case x2 of {
                                           True -> Left;
                                           False -> Right}) (\x2 ->
                                          case x2 of {
                                           True -> Right;
                                           False -> Left}) b5 b13)) (\_ ->
                                      Right)
                                      (bool_rec (\x2 ->
                                        case x2 of {
                                         True -> Left;
                                         False -> Right}) (\x2 ->
                                        case x2 of {
                                         True -> Right;
                                         False -> Left}) b4 b12)) (\_ ->
                                    Right)
                                    (bool_rec (\x2 ->
                                      case x2 of {
                                       True -> Left;
                                       False -> Right}) (\x2 ->
                                      case x2 of {
                                       True -> Right;
                                       False -> Left}) b3 b11)) (\_ -> Right)
                                  (bool_rec (\x2 ->
                                    case x2 of {
                                     True -> Left;
                                     False -> Right}) (\x2 ->
                                    case x2 of {
                                     True -> Right;
                                     False -> Left}) b2 b10)) (\_ -> Right)
                                (bool_rec (\x2 ->
                                  case x2 of {
                                   True -> Left;
                                   False -> Right}) (\x2 ->
                                  case x2 of {
                                   True -> Right;
                                   False -> Left}) b1 b9)) (\_ -> Right)
                              (bool_rec (\x2 ->
                                case x2 of {
                                 True -> Left;
                                 False -> Right}) (\x2 ->
                                case x2 of {
                                 True -> Right;
                                 False -> Left}) b0 b8)) (\_ -> Right)
                            (bool_rec (\x2 ->
                              case x2 of {
                               True -> Left;
                               False -> Right}) (\x2 ->
                              case x2 of {
                               True -> Right;
                               False -> Left}) b b7)}) a1 a2)}) a0 s)})
            eventArgs0 eventArgs1)) (\_ -> Right)
        (event_definition_dec event0 event1)}}

type Scenario_state = String

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
   Build_scenario String (List Step) (List Event_definition)

scenarioId :: Scenario -> String
scenarioId s =
  case s of {
   Build_scenario scenarioId0 _ _ -> scenarioId0}

alphabet :: Scenario -> List Event_definition
alphabet s =
  case s of {
   Build_scenario _ _ alphabet0 -> alphabet0}

scenario_dec :: Scenario -> Scenario -> Sumbool
scenario_dec n m =
  case n of {
   Build_scenario scenarioId0 traces0 alphabet0 ->
    case m of {
     Build_scenario scenarioId1 traces1 alphabet1 ->
      sumbool_rec (\_ ->
        sumbool_rec (\_ ->
          sumbool_rec (\_ -> Left) (\_ -> Right)
            (list_rec (\x -> case x of {
                              Nil -> Left;
                              Cons _ _ -> Right}) (\a1 _ h0 x ->
              case x of {
               Nil -> Right;
               Cons e l0 ->
                sumbool_rec (\_ ->
                  sumbool_rec (\_ -> Left) (\_ -> Right) (h0 l0)) (\_ ->
                  Right)
                  (case a1 of {
                    Build_event_definition eventKind0 eventId0
                     eventParams0 ->
                     case e of {
                      Build_event_definition eventKind1 eventId1
                       eventParams1 ->
                       sumbool_rec (\_ ->
                         sumbool_rec (\_ ->
                           sumbool_rec (\_ -> Left) (\_ -> Right)
                             (list_rec (\x0 ->
                               case x0 of {
                                Nil -> Left;
                                Cons _ _ -> Right}) (\a4 _ h1 x0 ->
                               case x0 of {
                                Nil -> Right;
                                Cons t l2 ->
                                 sumbool_rec (\_ ->
                                   sumbool_rec (\_ -> Left) (\_ -> Right)
                                     (h1 l2)) (\_ -> Right)
                                   (typ_rec (\x1 ->
                                     case x1 of {
                                      Int -> Left;
                                      _ -> Right}) (\x1 ->
                                     case x1 of {
                                      Float -> Left;
                                      _ -> Right}) (\x1 ->
                                     case x1 of {
                                      Str -> Left;
                                      _ -> Right}) (\x1 ->
                                     case x1 of {
                                      Bool0 -> Left;
                                      _ -> Right}) (\x1 ->
                                     case x1 of {
                                      Pointer -> Left;
                                      _ -> Right}) (\x1 ->
                                     case x1 of {
                                      Opaque -> Left;
                                      _ -> Right}) (\x1 ->
                                     case x1 of {
                                      Thread -> Left;
                                      _ -> Right}) a4 t)}) eventParams0
                               eventParams1)) (\_ -> Right)
                           (string_rec (\x0 ->
                             case x0 of {
                              EmptyString -> Left;
                              String0 _ _ -> Right}) (\a3 _ h1 x0 ->
                             case x0 of {
                              EmptyString -> Right;
                              String0 a4 s0 ->
                               sumbool_rec (\_ ->
                                 sumbool_rec (\_ -> Left) (\_ -> Right)
                                   (h1 s0)) (\_ -> Right)
                                 (ascii_rec (\b b0 b1 b2 b3 b4 b5 b6 x1 ->
                                   case x1 of {
                                    Ascii b7 b8 b9 b10 b11 b12 b13 b14 ->
                                     sumbool_rec (\_ ->
                                       sumbool_rec (\_ ->
                                         sumbool_rec (\_ ->
                                           sumbool_rec (\_ ->
                                             sumbool_rec (\_ ->
                                               sumbool_rec (\_ ->
                                                 sumbool_rec (\_ ->
                                                   sumbool_rec (\_ -> Left)
                                                     (\_ -> Right)
                                                     (bool_rec (\x2 ->
                                                       case x2 of {
                                                        True -> Left;
                                                        False -> Right})
                                                       (\x2 ->
                                                       case x2 of {
                                                        True -> Right;
                                                        False -> Left}) b6
                                                       b14)) (\_ -> Right)
                                                   (bool_rec (\x2 ->
                                                     case x2 of {
                                                      True -> Left;
                                                      False -> Right})
                                                     (\x2 ->
                                                     case x2 of {
                                                      True -> Right;
                                                      False -> Left}) b5 b13))
                                                 (\_ -> Right)
                                                 (bool_rec (\x2 ->
                                                   case x2 of {
                                                    True -> Left;
                                                    False -> Right}) (\x2 ->
                                                   case x2 of {
                                                    True -> Right;
                                                    False -> Left}) b4 b12))
                                               (\_ -> Right)
                                               (bool_rec (\x2 ->
                                                 case x2 of {
                                                  True -> Left;
                                                  False -> Right}) (\x2 ->
                                                 case x2 of {
                                                  True -> Right;
                                                  False -> Left}) b3 b11))
                                             (\_ -> Right)
                                             (bool_rec (\x2 ->
                                               case x2 of {
                                                True -> Left;
                                                False -> Right}) (\x2 ->
                                               case x2 of {
                                                True -> Right;
                                                False -> Left}) b2 b10))
                                           (\_ -> Right)
                                           (bool_rec (\x2 ->
                                             case x2 of {
                                              True -> Left;
                                              False -> Right}) (\x2 ->
                                             case x2 of {
                                              True -> Right;
                                              False -> Left}) b1 b9)) (\_ ->
                                         Right)
                                         (bool_rec (\x2 ->
                                           case x2 of {
                                            True -> Left;
                                            False -> Right}) (\x2 ->
                                           case x2 of {
                                            True -> Right;
                                            False -> Left}) b0 b8)) (\_ ->
                                       Right)
                                       (bool_rec (\x2 ->
                                         case x2 of {
                                          True -> Left;
                                          False -> Right}) (\x2 ->
                                         case x2 of {
                                          True -> Right;
                                          False -> Left}) b b7)}) a3 a4)})
                             eventId0 eventId1)) (\_ -> Right)
                         (eventKind_rec (\x0 ->
                           case x0 of {
                            Internal -> Left;
                            _ -> Right}) (\x0 ->
                           case x0 of {
                            Imported -> Left;
                            _ -> Right}) (\x0 ->
                           case x0 of {
                            Exported -> Left;
                            _ -> Right}) eventKind0 eventKind1)}})})
              alphabet0 alphabet1)) (\_ -> Right)
          (list_rec (\x -> case x of {
                            Nil -> Left;
                            Cons _ _ -> Right}) (\a0 _ h0 x ->
            case x of {
             Nil -> Right;
             Cons s l0 ->
              sumbool_rec (\_ ->
                sumbool_rec (\_ -> Left) (\_ -> Right) (h0 l0)) (\_ -> Right)
                (case a0 of {
                  Build_step pre_state0 stepEvent0 stepActions0 pro_state0 ->
                   case s of {
                    Build_step pre_state1 stepEvent1 stepActions1
                     pro_state1 ->
                     sumbool_rec (\_ ->
                       sumbool_rec (\_ ->
                         sumbool_rec (\_ ->
                           sumbool_rec (\_ -> Left) (\_ -> Right)
                             (string_rec (\x0 ->
                               case x0 of {
                                EmptyString -> Left;
                                String0 _ _ -> Right}) (\a4 _ h1 x0 ->
                               case x0 of {
                                EmptyString -> Right;
                                String0 a5 s1 ->
                                 sumbool_rec (\_ ->
                                   sumbool_rec (\_ -> Left) (\_ -> Right)
                                     (h1 s1)) (\_ -> Right)
                                   (ascii_rec (\b b0 b1 b2 b3 b4 b5 b6 x1 ->
                                     case x1 of {
                                      Ascii b7 b8 b9 b10 b11 b12 b13 b14 ->
                                       sumbool_rec (\_ ->
                                         sumbool_rec (\_ ->
                                           sumbool_rec (\_ ->
                                             sumbool_rec (\_ ->
                                               sumbool_rec (\_ ->
                                                 sumbool_rec (\_ ->
                                                   sumbool_rec (\_ ->
                                                     sumbool_rec (\_ -> Left)
                                                       (\_ -> Right)
                                                       (bool_rec (\x2 ->
                                                         case x2 of {
                                                          True -> Left;
                                                          False -> Right})
                                                         (\x2 ->
                                                         case x2 of {
                                                          True -> Right;
                                                          False -> Left}) b6
                                                         b14)) (\_ -> Right)
                                                     (bool_rec (\x2 ->
                                                       case x2 of {
                                                        True -> Left;
                                                        False -> Right})
                                                       (\x2 ->
                                                       case x2 of {
                                                        True -> Right;
                                                        False -> Left}) b5
                                                       b13)) (\_ -> Right)
                                                   (bool_rec (\x2 ->
                                                     case x2 of {
                                                      True -> Left;
                                                      False -> Right})
                                                     (\x2 ->
                                                     case x2 of {
                                                      True -> Right;
                                                      False -> Left}) b4 b12))
                                                 (\_ -> Right)
                                                 (bool_rec (\x2 ->
                                                   case x2 of {
                                                    True -> Left;
                                                    False -> Right}) (\x2 ->
                                                   case x2 of {
                                                    True -> Right;
                                                    False -> Left}) b3 b11))
                                               (\_ -> Right)
                                               (bool_rec (\x2 ->
                                                 case x2 of {
                                                  True -> Left;
                                                  False -> Right}) (\x2 ->
                                                 case x2 of {
                                                  True -> Right;
                                                  False -> Left}) b2 b10))
                                             (\_ -> Right)
                                             (bool_rec (\x2 ->
                                               case x2 of {
                                                True -> Left;
                                                False -> Right}) (\x2 ->
                                               case x2 of {
                                                True -> Right;
                                                False -> Left}) b1 b9))
                                           (\_ -> Right)
                                           (bool_rec (\x2 ->
                                             case x2 of {
                                              True -> Left;
                                              False -> Right}) (\x2 ->
                                             case x2 of {
                                              True -> Right;
                                              False -> Left}) b0 b8)) (\_ ->
                                         Right)
                                         (bool_rec (\x2 ->
                                           case x2 of {
                                            True -> Left;
                                            False -> Right}) (\x2 ->
                                           case x2 of {
                                            True -> Right;
                                            False -> Left}) b b7)}) a4 a5)})
                               pro_state0 pro_state1)) (\_ -> Right)
                           (action_rec (\x0 ->
                             case x0 of {
                              Skip -> Left;
                              _ -> Right}) (\l1 e x0 ->
                             case x0 of {
                              StateUpdate l2 e0 ->
                               sumbool_rec (\_ ->
                                 sumbool_rec (\_ -> Left) (\_ -> Right)
                                   (expr_eq_dec e e0)) (\_ -> Right)
                                 (lValue_rec (\a3 x1 ->
                                   sumbool_rec (\_ -> Left) (\_ -> Right)
                                     (atom_rec (\z x2 ->
                                       case x2 of {
                                        AInt z0 ->
                                         sumbool_rec (\_ -> Left) (\_ ->
                                           Right)
                                           (z_rec (\x3 ->
                                             case x3 of {
                                              Z0 -> Left;
                                              _ -> Right}) (\p x3 ->
                                             case x3 of {
                                              Zpos p0 ->
                                               sumbool_rec (\_ -> Left)
                                                 (\_ -> Right)
                                                 (positive_rec (\_ h1 x4 ->
                                                   case x4 of {
                                                    XI p2 ->
                                                     sumbool_rec (\_ -> Left)
                                                       (\_ -> Right) 
                                                       (h1 p2);
                                                    _ -> Right}) (\_ h1 x4 ->
                                                   case x4 of {
                                                    XO p2 ->
                                                     sumbool_rec (\_ -> Left)
                                                       (\_ -> Right) 
                                                       (h1 p2);
                                                    _ -> Right}) (\x4 ->
                                                   case x4 of {
                                                    XH -> Left;
                                                    _ -> Right}) p p0);
                                              _ -> Right}) (\p x3 ->
                                             case x3 of {
                                              Zneg p0 ->
                                               sumbool_rec (\_ -> Left)
                                                 (\_ -> Right)
                                                 (positive_rec (\_ h1 x4 ->
                                                   case x4 of {
                                                    XI p2 ->
                                                     sumbool_rec (\_ -> Left)
                                                       (\_ -> Right) 
                                                       (h1 p2);
                                                    _ -> Right}) (\_ h1 x4 ->
                                                   case x4 of {
                                                    XO p2 ->
                                                     sumbool_rec (\_ -> Left)
                                                       (\_ -> Right) 
                                                       (h1 p2);
                                                    _ -> Right}) (\x4 ->
                                                   case x4 of {
                                                    XH -> Left;
                                                    _ -> Right}) p p0);
                                              _ -> Right}) z z0);
                                        _ -> Right}) (\q x2 ->
                                       case x2 of {
                                        AFloat q0 ->
                                         sumbool_rec (\_ -> Left) (\_ ->
                                           Right)
                                           (case q of {
                                             Qmake qnum0 qden0 ->
                                              case q0 of {
                                               Qmake qnum1 qden1 ->
                                                sumbool_rec (\_ ->
                                                  sumbool_rec (\_ -> Left)
                                                    (\_ -> Right)
                                                    (positive_rec
                                                      (\_ h1 x3 ->
                                                      case x3 of {
                                                       XI p0 ->
                                                        sumbool_rec (\_ ->
                                                          Left) (\_ -> Right)
                                                          (h1 p0);
                                                       _ -> Right})
                                                      (\_ h1 x3 ->
                                                      case x3 of {
                                                       XO p0 ->
                                                        sumbool_rec (\_ ->
                                                          Left) (\_ -> Right)
                                                          (h1 p0);
                                                       _ -> Right}) (\x3 ->
                                                      case x3 of {
                                                       XH -> Left;
                                                       _ -> Right}) qden0
                                                      qden1)) (\_ -> Right)
                                                  (z_rec (\x3 ->
                                                    case x3 of {
                                                     Z0 -> Left;
                                                     _ -> Right}) (\p x3 ->
                                                    case x3 of {
                                                     Zpos p0 ->
                                                      sumbool_rec (\_ ->
                                                        Left) (\_ -> Right)
                                                        (positive_rec
                                                          (\_ h1 x4 ->
                                                          case x4 of {
                                                           XI p2 ->
                                                            sumbool_rec
                                                              (\_ -> Left)
                                                              (\_ -> Right)
                                                              (h1 p2);
                                                           _ -> Right})
                                                          (\_ h1 x4 ->
                                                          case x4 of {
                                                           XO p2 ->
                                                            sumbool_rec
                                                              (\_ -> Left)
                                                              (\_ -> Right)
                                                              (h1 p2);
                                                           _ -> Right})
                                                          (\x4 ->
                                                          case x4 of {
                                                           XH -> Left;
                                                           _ -> Right}) p p0);
                                                     _ -> Right}) (\p x3 ->
                                                    case x3 of {
                                                     Zneg p0 ->
                                                      sumbool_rec (\_ ->
                                                        Left) (\_ -> Right)
                                                        (positive_rec
                                                          (\_ h1 x4 ->
                                                          case x4 of {
                                                           XI p2 ->
                                                            sumbool_rec
                                                              (\_ -> Left)
                                                              (\_ -> Right)
                                                              (h1 p2);
                                                           _ -> Right})
                                                          (\_ h1 x4 ->
                                                          case x4 of {
                                                           XO p2 ->
                                                            sumbool_rec
                                                              (\_ -> Left)
                                                              (\_ -> Right)
                                                              (h1 p2);
                                                           _ -> Right})
                                                          (\x4 ->
                                                          case x4 of {
                                                           XH -> Left;
                                                           _ -> Right}) p p0);
                                                     _ -> Right}) qnum0
                                                    qnum1)}});
                                        _ -> Right}) (\s0 x2 ->
                                       case x2 of {
                                        AIdent s1 ->
                                         sumbool_rec (\_ -> Left) (\_ ->
                                           Right)
                                           (string_rec (\x3 ->
                                             case x3 of {
                                              EmptyString -> Left;
                                              String0 _ _ -> Right})
                                             (\a5 _ h1 x3 ->
                                             case x3 of {
                                              EmptyString -> Right;
                                              String0 a6 s3 ->
                                               sumbool_rec (\_ ->
                                                 sumbool_rec (\_ -> Left)
                                                   (\_ -> Right) (h1 s3))
                                                 (\_ -> Right)
                                                 (ascii_rec
                                                   (\b b0 b1 b2 b3 b4 b5 b6 x4 ->
                                                   case x4 of {
                                                    Ascii b7 b8 b9 b10 b11
                                                     b12 b13 b14 ->
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
                                                                    Left)
                                                                    (\_ ->
                                                                    Right)
                                                                    (bool_rec
                                                                    (\x5 ->
                                                                    case x5 of {
                                                                     True ->
                                                                    Left;
                                                                     False ->
                                                                    Right})
                                                                    (\x5 ->
                                                                    case x5 of {
                                                                     True ->
                                                                    Right;
                                                                     False ->
                                                                    Left}) b6
                                                                    b14))
                                                                   (\_ ->
                                                                   Right)
                                                                   (bool_rec
                                                                    (\x5 ->
                                                                    case x5 of {
                                                                     True ->
                                                                    Left;
                                                                     False ->
                                                                    Right})
                                                                    (\x5 ->
                                                                    case x5 of {
                                                                     True ->
                                                                    Right;
                                                                     False ->
                                                                    Left}) b5
                                                                    b13))
                                                                 (\_ ->
                                                                 Right)
                                                                 (bool_rec
                                                                   (\x5 ->
                                                                   case x5 of {
                                                                    True ->
                                                                    Left;
                                                                    False ->
                                                                    Right})
                                                                   (\x5 ->
                                                                   case x5 of {
                                                                    True ->
                                                                    Right;
                                                                    False ->
                                                                    Left}) b4
                                                                   b12))
                                                               (\_ -> Right)
                                                               (bool_rec
                                                                 (\x5 ->
                                                                 case x5 of {
                                                                  True ->
                                                                   Left;
                                                                  False ->
                                                                   Right})
                                                                 (\x5 ->
                                                                 case x5 of {
                                                                  True ->
                                                                   Right;
                                                                  False ->
                                                                   Left}) b3
                                                                 b11)) (\_ ->
                                                             Right)
                                                             (bool_rec
                                                               (\x5 ->
                                                               case x5 of {
                                                                True -> Left;
                                                                False ->
                                                                 Right})
                                                               (\x5 ->
                                                               case x5 of {
                                                                True -> Right;
                                                                False -> Left})
                                                               b2 b10))
                                                           (\_ -> Right)
                                                           (bool_rec (\x5 ->
                                                             case x5 of {
                                                              True -> Left;
                                                              False -> Right})
                                                             (\x5 ->
                                                             case x5 of {
                                                              True -> Right;
                                                              False -> Left})
                                                             b1 b9)) (\_ ->
                                                         Right)
                                                         (bool_rec (\x5 ->
                                                           case x5 of {
                                                            True -> Left;
                                                            False -> Right})
                                                           (\x5 ->
                                                           case x5 of {
                                                            True -> Right;
                                                            False -> Left})
                                                           b0 b8)) (\_ ->
                                                       Right)
                                                       (bool_rec (\x5 ->
                                                         case x5 of {
                                                          True -> Left;
                                                          False -> Right})
                                                         (\x5 ->
                                                         case x5 of {
                                                          True -> Right;
                                                          False -> Left}) b
                                                         b7)}) a5 a6)}) s0
                                             s1);
                                        _ -> Right}) (\b x2 ->
                                       case x2 of {
                                        ABool b0 ->
                                         sumbool_rec (\_ -> Left) (\_ ->
                                           Right)
                                           (bool_rec (\x3 ->
                                             case x3 of {
                                              True -> Left;
                                              False -> Right}) (\x3 ->
                                             case x3 of {
                                              True -> Right;
                                              False -> Left}) b b0);
                                        _ -> Right}) (\x2 ->
                                       case x2 of {
                                        ANull -> Left;
                                        _ -> Right}) (\s0 x2 ->
                                       case x2 of {
                                        AString s1 ->
                                         sumbool_rec (\_ -> Left) (\_ ->
                                           Right)
                                           (string_rec (\x3 ->
                                             case x3 of {
                                              EmptyString -> Left;
                                              String0 _ _ -> Right})
                                             (\a5 _ h1 x3 ->
                                             case x3 of {
                                              EmptyString -> Right;
                                              String0 a6 s3 ->
                                               sumbool_rec (\_ ->
                                                 sumbool_rec (\_ -> Left)
                                                   (\_ -> Right) (h1 s3))
                                                 (\_ -> Right)
                                                 (ascii_rec
                                                   (\b b0 b1 b2 b3 b4 b5 b6 x4 ->
                                                   case x4 of {
                                                    Ascii b7 b8 b9 b10 b11
                                                     b12 b13 b14 ->
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
                                                                    Left)
                                                                    (\_ ->
                                                                    Right)
                                                                    (bool_rec
                                                                    (\x5 ->
                                                                    case x5 of {
                                                                     True ->
                                                                    Left;
                                                                     False ->
                                                                    Right})
                                                                    (\x5 ->
                                                                    case x5 of {
                                                                     True ->
                                                                    Right;
                                                                     False ->
                                                                    Left}) b6
                                                                    b14))
                                                                   (\_ ->
                                                                   Right)
                                                                   (bool_rec
                                                                    (\x5 ->
                                                                    case x5 of {
                                                                     True ->
                                                                    Left;
                                                                     False ->
                                                                    Right})
                                                                    (\x5 ->
                                                                    case x5 of {
                                                                     True ->
                                                                    Right;
                                                                     False ->
                                                                    Left}) b5
                                                                    b13))
                                                                 (\_ ->
                                                                 Right)
                                                                 (bool_rec
                                                                   (\x5 ->
                                                                   case x5 of {
                                                                    True ->
                                                                    Left;
                                                                    False ->
                                                                    Right})
                                                                   (\x5 ->
                                                                   case x5 of {
                                                                    True ->
                                                                    Right;
                                                                    False ->
                                                                    Left}) b4
                                                                   b12))
                                                               (\_ -> Right)
                                                               (bool_rec
                                                                 (\x5 ->
                                                                 case x5 of {
                                                                  True ->
                                                                   Left;
                                                                  False ->
                                                                   Right})
                                                                 (\x5 ->
                                                                 case x5 of {
                                                                  True ->
                                                                   Right;
                                                                  False ->
                                                                   Left}) b3
                                                                 b11)) (\_ ->
                                                             Right)
                                                             (bool_rec
                                                               (\x5 ->
                                                               case x5 of {
                                                                True -> Left;
                                                                False ->
                                                                 Right})
                                                               (\x5 ->
                                                               case x5 of {
                                                                True -> Right;
                                                                False -> Left})
                                                               b2 b10))
                                                           (\_ -> Right)
                                                           (bool_rec (\x5 ->
                                                             case x5 of {
                                                              True -> Left;
                                                              False -> Right})
                                                             (\x5 ->
                                                             case x5 of {
                                                              True -> Right;
                                                              False -> Left})
                                                             b1 b9)) (\_ ->
                                                         Right)
                                                         (bool_rec (\x5 ->
                                                           case x5 of {
                                                            True -> Left;
                                                            False -> Right})
                                                           (\x5 ->
                                                           case x5 of {
                                                            True -> Right;
                                                            False -> Left})
                                                           b0 b8)) (\_ ->
                                                       Right)
                                                       (bool_rec (\x5 ->
                                                         case x5 of {
                                                          True -> Left;
                                                          False -> Right})
                                                         (\x5 ->
                                                         case x5 of {
                                                          True -> Right;
                                                          False -> Left}) b
                                                         b7)}) a5 a6)}) s0
                                             s1);
                                        _ -> Right}) a3 x1)) l1 l2);
                              _ -> Right}) (\ident exprs x0 ->
                             case x0 of {
                              RaiseStmt ident0 exprs0 ->
                               sumbool_rec (\_ ->
                                 sumbool_rec (\_ -> Left) (\_ -> Right)
                                   (list_rec (\x1 ->
                                     case x1 of {
                                      Nil -> Left;
                                      Cons _ _ -> Right}) (\a4 _ h1 x1 ->
                                     case x1 of {
                                      Nil -> Right;
                                      Cons e l2 ->
                                       sumbool_rec (\_ ->
                                         sumbool_rec (\_ -> Left) (\_ ->
                                           Right) (h1 l2)) (\_ -> Right)
                                         (expr_eq_dec a4 e)}) exprs exprs0))
                                 (\_ -> Right)
                                 (string_rec (\x1 ->
                                   case x1 of {
                                    EmptyString -> Left;
                                    String0 _ _ -> Right}) (\a3 _ h1 x1 ->
                                   case x1 of {
                                    EmptyString -> Right;
                                    String0 a4 s1 ->
                                     sumbool_rec (\_ ->
                                       sumbool_rec (\_ -> Left) (\_ -> Right)
                                         (h1 s1)) (\_ -> Right)
                                       (ascii_rec
                                         (\b b0 b1 b2 b3 b4 b5 b6 x2 ->
                                         case x2 of {
                                          Ascii b7 b8 b9 b10 b11 b12 b13
                                           b14 ->
                                           sumbool_rec (\_ ->
                                             sumbool_rec (\_ ->
                                               sumbool_rec (\_ ->
                                                 sumbool_rec (\_ ->
                                                   sumbool_rec (\_ ->
                                                     sumbool_rec (\_ ->
                                                       sumbool_rec (\_ ->
                                                         sumbool_rec (\_ ->
                                                           Left) (\_ ->
                                                           Right)
                                                           (bool_rec (\x3 ->
                                                             case x3 of {
                                                              True -> Left;
                                                              False -> Right})
                                                             (\x3 ->
                                                             case x3 of {
                                                              True -> Right;
                                                              False -> Left})
                                                             b6 b14)) (\_ ->
                                                         Right)
                                                         (bool_rec (\x3 ->
                                                           case x3 of {
                                                            True -> Left;
                                                            False -> Right})
                                                           (\x3 ->
                                                           case x3 of {
                                                            True -> Right;
                                                            False -> Left})
                                                           b5 b13)) (\_ ->
                                                       Right)
                                                       (bool_rec (\x3 ->
                                                         case x3 of {
                                                          True -> Left;
                                                          False -> Right})
                                                         (\x3 ->
                                                         case x3 of {
                                                          True -> Right;
                                                          False -> Left}) b4
                                                         b12)) (\_ -> Right)
                                                     (bool_rec (\x3 ->
                                                       case x3 of {
                                                        True -> Left;
                                                        False -> Right})
                                                       (\x3 ->
                                                       case x3 of {
                                                        True -> Right;
                                                        False -> Left}) b3
                                                       b11)) (\_ -> Right)
                                                   (bool_rec (\x3 ->
                                                     case x3 of {
                                                      True -> Left;
                                                      False -> Right})
                                                     (\x3 ->
                                                     case x3 of {
                                                      True -> Right;
                                                      False -> Left}) b2 b10))
                                                 (\_ -> Right)
                                                 (bool_rec (\x3 ->
                                                   case x3 of {
                                                    True -> Left;
                                                    False -> Right}) (\x3 ->
                                                   case x3 of {
                                                    True -> Right;
                                                    False -> Left}) b1 b9))
                                               (\_ -> Right)
                                               (bool_rec (\x3 ->
                                                 case x3 of {
                                                  True -> Left;
                                                  False -> Right}) (\x3 ->
                                                 case x3 of {
                                                  True -> Right;
                                                  False -> Left}) b0 b8))
                                             (\_ -> Right)
                                             (bool_rec (\x3 ->
                                               case x3 of {
                                                True -> Left;
                                                False -> Right}) (\x3 ->
                                               case x3 of {
                                                True -> Right;
                                                False -> Left}) b b7)}) a3
                                         a4)}) ident ident0);
                              _ -> Right}) (\_ h1 _ h2 x0 ->
                             case x0 of {
                              Seq a5 a6 ->
                               sumbool_rec (\_ ->
                                 sumbool_rec (\_ -> Left) (\_ -> Right)
                                   (h2 a6)) (\_ -> Right) (h1 a5);
                              _ -> Right}) stepActions0 stepActions1)) (\_ ->
                         Right)
                         (case stepEvent0 of {
                           Build_event_instance event0 eventArgs0
                            eventWhenExpr0 ->
                            case stepEvent1 of {
                             Build_event_instance event1 eventArgs1
                              eventWhenExpr1 ->
                              sumbool_rec (\_ ->
                                sumbool_rec (\_ ->
                                  sumbool_rec (\_ -> Left) (\_ -> Right)
                                    (expr_eq_dec eventWhenExpr0
                                      eventWhenExpr1)) (\_ -> Right)
                                  (list_rec (\x0 ->
                                    case x0 of {
                                     Nil -> Left;
                                     Cons _ _ -> Right}) (\a3 _ h1 x0 ->
                                    case x0 of {
                                     Nil -> Right;
                                     Cons s0 l2 ->
                                      sumbool_rec (\_ ->
                                        sumbool_rec (\_ -> Left) (\_ ->
                                          Right) (h1 l2)) (\_ -> Right)
                                        (string_rec (\x1 ->
                                          case x1 of {
                                           EmptyString -> Left;
                                           String0 _ _ -> Right})
                                          (\a4 _ h2 x1 ->
                                          case x1 of {
                                           EmptyString -> Right;
                                           String0 a5 s2 ->
                                            sumbool_rec (\_ ->
                                              sumbool_rec (\_ -> Left) (\_ ->
                                                Right) (h2 s2)) (\_ -> Right)
                                              (ascii_rec
                                                (\b b0 b1 b2 b3 b4 b5 b6 x2 ->
                                                case x2 of {
                                                 Ascii b7 b8 b9 b10 b11 b12
                                                  b13 b14 ->
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
                                                                  Left)
                                                                  (\_ ->
                                                                  Right)
                                                                  (bool_rec
                                                                    (\x3 ->
                                                                    case x3 of {
                                                                     True ->
                                                                    Left;
                                                                     False ->
                                                                    Right})
                                                                    (\x3 ->
                                                                    case x3 of {
                                                                     True ->
                                                                    Right;
                                                                     False ->
                                                                    Left}) b6
                                                                    b14))
                                                                (\_ -> Right)
                                                                (bool_rec
                                                                  (\x3 ->
                                                                  case x3 of {
                                                                   True ->
                                                                    Left;
                                                                   False ->
                                                                    Right})
                                                                  (\x3 ->
                                                                  case x3 of {
                                                                   True ->
                                                                    Right;
                                                                   False ->
                                                                    Left}) b5
                                                                  b13))
                                                              (\_ -> Right)
                                                              (bool_rec
                                                                (\x3 ->
                                                                case x3 of {
                                                                 True -> Left;
                                                                 False ->
                                                                  Right})
                                                                (\x3 ->
                                                                case x3 of {
                                                                 True ->
                                                                  Right;
                                                                 False ->
                                                                  Left}) b4
                                                                b12)) (\_ ->
                                                            Right)
                                                            (bool_rec (\x3 ->
                                                              case x3 of {
                                                               True -> Left;
                                                               False -> Right})
                                                              (\x3 ->
                                                              case x3 of {
                                                               True -> Right;
                                                               False -> Left})
                                                              b3 b11)) (\_ ->
                                                          Right)
                                                          (bool_rec (\x3 ->
                                                            case x3 of {
                                                             True -> Left;
                                                             False -> Right})
                                                            (\x3 ->
                                                            case x3 of {
                                                             True -> Right;
                                                             False -> Left})
                                                            b2 b10)) (\_ ->
                                                        Right)
                                                        (bool_rec (\x3 ->
                                                          case x3 of {
                                                           True -> Left;
                                                           False -> Right})
                                                          (\x3 ->
                                                          case x3 of {
                                                           True -> Right;
                                                           False -> Left}) b1
                                                          b9)) (\_ -> Right)
                                                      (bool_rec (\x3 ->
                                                        case x3 of {
                                                         True -> Left;
                                                         False -> Right})
                                                        (\x3 ->
                                                        case x3 of {
                                                         True -> Right;
                                                         False -> Left}) b0
                                                        b8)) (\_ -> Right)
                                                    (bool_rec (\x3 ->
                                                      case x3 of {
                                                       True -> Left;
                                                       False -> Right})
                                                      (\x3 ->
                                                      case x3 of {
                                                       True -> Right;
                                                       False -> Left}) b b7)})
                                                a4 a5)}) a3 s0)}) eventArgs0
                                    eventArgs1)) (\_ -> Right)
                                (case event0 of {
                                  Build_event_definition eventKind0 eventId0
                                   eventParams0 ->
                                   case event1 of {
                                    Build_event_definition eventKind1
                                     eventId1 eventParams1 ->
                                     sumbool_rec (\_ ->
                                       sumbool_rec (\_ ->
                                         sumbool_rec (\_ -> Left) (\_ ->
                                           Right)
                                           (list_rec (\x0 ->
                                             case x0 of {
                                              Nil -> Left;
                                              Cons _ _ -> Right})
                                             (\a4 _ h1 x0 ->
                                             case x0 of {
                                              Nil -> Right;
                                              Cons t l2 ->
                                               sumbool_rec (\_ ->
                                                 sumbool_rec (\_ -> Left)
                                                   (\_ -> Right) (h1 l2))
                                                 (\_ -> Right)
                                                 (typ_rec (\x1 ->
                                                   case x1 of {
                                                    Int -> Left;
                                                    _ -> Right}) (\x1 ->
                                                   case x1 of {
                                                    Float -> Left;
                                                    _ -> Right}) (\x1 ->
                                                   case x1 of {
                                                    Str -> Left;
                                                    _ -> Right}) (\x1 ->
                                                   case x1 of {
                                                    Bool0 -> Left;
                                                    _ -> Right}) (\x1 ->
                                                   case x1 of {
                                                    Pointer -> Left;
                                                    _ -> Right}) (\x1 ->
                                                   case x1 of {
                                                    Opaque -> Left;
                                                    _ -> Right}) (\x1 ->
                                                   case x1 of {
                                                    Thread -> Left;
                                                    _ -> Right}) a4 t)})
                                             eventParams0 eventParams1))
                                         (\_ -> Right)
                                         (string_rec (\x0 ->
                                           case x0 of {
                                            EmptyString -> Left;
                                            String0 _ _ -> Right})
                                           (\a3 _ h1 x0 ->
                                           case x0 of {
                                            EmptyString -> Right;
                                            String0 a4 s1 ->
                                             sumbool_rec (\_ ->
                                               sumbool_rec (\_ -> Left)
                                                 (\_ -> Right) (h1 s1))
                                               (\_ -> Right)
                                               (ascii_rec
                                                 (\b b0 b1 b2 b3 b4 b5 b6 x1 ->
                                                 case x1 of {
                                                  Ascii b7 b8 b9 b10 b11 b12
                                                   b13 b14 ->
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
                                                                   Left)
                                                                   (\_ ->
                                                                   Right)
                                                                   (bool_rec
                                                                    (\x2 ->
                                                                    case x2 of {
                                                                     True ->
                                                                    Left;
                                                                     False ->
                                                                    Right})
                                                                    (\x2 ->
                                                                    case x2 of {
                                                                     True ->
                                                                    Right;
                                                                     False ->
                                                                    Left}) b6
                                                                    b14))
                                                                 (\_ ->
                                                                 Right)
                                                                 (bool_rec
                                                                   (\x2 ->
                                                                   case x2 of {
                                                                    True ->
                                                                    Left;
                                                                    False ->
                                                                    Right})
                                                                   (\x2 ->
                                                                   case x2 of {
                                                                    True ->
                                                                    Right;
                                                                    False ->
                                                                    Left}) b5
                                                                   b13))
                                                               (\_ -> Right)
                                                               (bool_rec
                                                                 (\x2 ->
                                                                 case x2 of {
                                                                  True ->
                                                                   Left;
                                                                  False ->
                                                                   Right})
                                                                 (\x2 ->
                                                                 case x2 of {
                                                                  True ->
                                                                   Right;
                                                                  False ->
                                                                   Left}) b4
                                                                 b12)) (\_ ->
                                                             Right)
                                                             (bool_rec
                                                               (\x2 ->
                                                               case x2 of {
                                                                True -> Left;
                                                                False ->
                                                                 Right})
                                                               (\x2 ->
                                                               case x2 of {
                                                                True -> Right;
                                                                False -> Left})
                                                               b3 b11))
                                                           (\_ -> Right)
                                                           (bool_rec (\x2 ->
                                                             case x2 of {
                                                              True -> Left;
                                                              False -> Right})
                                                             (\x2 ->
                                                             case x2 of {
                                                              True -> Right;
                                                              False -> Left})
                                                             b2 b10)) (\_ ->
                                                         Right)
                                                         (bool_rec (\x2 ->
                                                           case x2 of {
                                                            True -> Left;
                                                            False -> Right})
                                                           (\x2 ->
                                                           case x2 of {
                                                            True -> Right;
                                                            False -> Left})
                                                           b1 b9)) (\_ ->
                                                       Right)
                                                       (bool_rec (\x2 ->
                                                         case x2 of {
                                                          True -> Left;
                                                          False -> Right})
                                                         (\x2 ->
                                                         case x2 of {
                                                          True -> Right;
                                                          False -> Left}) b0
                                                         b8)) (\_ -> Right)
                                                     (bool_rec (\x2 ->
                                                       case x2 of {
                                                        True -> Left;
                                                        False -> Right})
                                                       (\x2 ->
                                                       case x2 of {
                                                        True -> Right;
                                                        False -> Left}) b b7)})
                                                 a3 a4)}) eventId0 eventId1))
                                       (\_ -> Right)
                                       (eventKind_rec (\x0 ->
                                         case x0 of {
                                          Internal -> Left;
                                          _ -> Right}) (\x0 ->
                                         case x0 of {
                                          Imported -> Left;
                                          _ -> Right}) (\x0 ->
                                         case x0 of {
                                          Exported -> Left;
                                          _ -> Right}) eventKind0 eventKind1)}})}}))
                       (\_ -> Right)
                       (string_rec (\x0 ->
                         case x0 of {
                          EmptyString -> Left;
                          String0 _ _ -> Right}) (\a1 _ h1 x0 ->
                         case x0 of {
                          EmptyString -> Right;
                          String0 a2 s1 ->
                           sumbool_rec (\_ ->
                             sumbool_rec (\_ -> Left) (\_ -> Right) (h1 s1))
                             (\_ -> Right)
                             (ascii_rec (\b b0 b1 b2 b3 b4 b5 b6 x1 ->
                               case x1 of {
                                Ascii b7 b8 b9 b10 b11 b12 b13 b14 ->
                                 sumbool_rec (\_ ->
                                   sumbool_rec (\_ ->
                                     sumbool_rec (\_ ->
                                       sumbool_rec (\_ ->
                                         sumbool_rec (\_ ->
                                           sumbool_rec (\_ ->
                                             sumbool_rec (\_ ->
                                               sumbool_rec (\_ -> Left)
                                                 (\_ -> Right)
                                                 (bool_rec (\x2 ->
                                                   case x2 of {
                                                    True -> Left;
                                                    False -> Right}) (\x2 ->
                                                   case x2 of {
                                                    True -> Right;
                                                    False -> Left}) b6 b14))
                                               (\_ -> Right)
                                               (bool_rec (\x2 ->
                                                 case x2 of {
                                                  True -> Left;
                                                  False -> Right}) (\x2 ->
                                                 case x2 of {
                                                  True -> Right;
                                                  False -> Left}) b5 b13))
                                             (\_ -> Right)
                                             (bool_rec (\x2 ->
                                               case x2 of {
                                                True -> Left;
                                                False -> Right}) (\x2 ->
                                               case x2 of {
                                                True -> Right;
                                                False -> Left}) b4 b12))
                                           (\_ -> Right)
                                           (bool_rec (\x2 ->
                                             case x2 of {
                                              True -> Left;
                                              False -> Right}) (\x2 ->
                                             case x2 of {
                                              True -> Right;
                                              False -> Left}) b3 b11)) (\_ ->
                                         Right)
                                         (bool_rec (\x2 ->
                                           case x2 of {
                                            True -> Left;
                                            False -> Right}) (\x2 ->
                                           case x2 of {
                                            True -> Right;
                                            False -> Left}) b2 b10)) (\_ ->
                                       Right)
                                       (bool_rec (\x2 ->
                                         case x2 of {
                                          True -> Left;
                                          False -> Right}) (\x2 ->
                                         case x2 of {
                                          True -> Right;
                                          False -> Left}) b1 b9)) (\_ ->
                                     Right)
                                     (bool_rec (\x2 ->
                                       case x2 of {
                                        True -> Left;
                                        False -> Right}) (\x2 ->
                                       case x2 of {
                                        True -> Right;
                                        False -> Left}) b0 b8)) (\_ -> Right)
                                   (bool_rec (\x2 ->
                                     case x2 of {
                                      True -> Left;
                                      False -> Right}) (\x2 ->
                                     case x2 of {
                                      True -> Right;
                                      False -> Left}) b b7)}) a1 a2)})
                         pre_state0 pre_state1)}})}) traces0 traces1)) (\_ ->
        Right)
        (string_rec (\x ->
          case x of {
           EmptyString -> Left;
           String0 _ _ -> Right}) (\a _ h0 x ->
          case x of {
           EmptyString -> Right;
           String0 a0 s0 ->
            sumbool_rec (\_ ->
              sumbool_rec (\_ -> Left) (\_ -> Right) (h0 s0)) (\_ -> Right)
              (ascii_rec (\b b0 b1 b2 b3 b4 b5 b6 x0 ->
                case x0 of {
                 Ascii b7 b8 b9 b10 b11 b12 b13 b14 ->
                  sumbool_rec (\_ ->
                    sumbool_rec (\_ ->
                      sumbool_rec (\_ ->
                        sumbool_rec (\_ ->
                          sumbool_rec (\_ ->
                            sumbool_rec (\_ ->
                              sumbool_rec (\_ ->
                                sumbool_rec (\_ -> Left) (\_ -> Right)
                                  (bool_rec (\x1 ->
                                    case x1 of {
                                     True -> Left;
                                     False -> Right}) (\x1 ->
                                    case x1 of {
                                     True -> Right;
                                     False -> Left}) b6 b14)) (\_ -> Right)
                                (bool_rec (\x1 ->
                                  case x1 of {
                                   True -> Left;
                                   False -> Right}) (\x1 ->
                                  case x1 of {
                                   True -> Right;
                                   False -> Left}) b5 b13)) (\_ -> Right)
                              (bool_rec (\x1 ->
                                case x1 of {
                                 True -> Left;
                                 False -> Right}) (\x1 ->
                                case x1 of {
                                 True -> Right;
                                 False -> Left}) b4 b12)) (\_ -> Right)
                            (bool_rec (\x1 ->
                              case x1 of {
                               True -> Left;
                               False -> Right}) (\x1 ->
                              case x1 of {
                               True -> Right;
                               False -> Left}) b3 b11)) (\_ -> Right)
                          (bool_rec (\x1 ->
                            case x1 of {
                             True -> Left;
                             False -> Right}) (\x1 ->
                            case x1 of {
                             True -> Right;
                             False -> Left}) b2 b10)) (\_ -> Right)
                        (bool_rec (\x1 ->
                          case x1 of {
                           True -> Left;
                           False -> Right}) (\x1 ->
                          case x1 of {
                           True -> Right;
                           False -> Left}) b1 b9)) (\_ -> Right)
                      (bool_rec (\x1 ->
                        case x1 of {
                         True -> Left;
                         False -> Right}) (\x1 ->
                        case x1 of {
                         True -> Right;
                         False -> Left}) b0 b8)) (\_ -> Right)
                    (bool_rec (\x1 ->
                      case x1 of {
                       True -> Left;
                       False -> Right}) (\x1 ->
                      case x1 of {
                       True -> Right;
                       False -> Left}) b b7)}) a a0)}) scenarioId0
          scenarioId1)}}

type Scenario_env = List (Prod Scenario Scenario_state)

getScenarioState :: Scenario -> Scenario_env -> Option Scenario_state
getScenarioState sce env =
  case env of {
   Nil -> None;
   Cons p en' ->
    case p of {
     Pair s e ->
      case string_dec (scenarioId sce) (scenarioId s) of {
       Left -> Some e;
       Right -> getScenarioState sce en'}}}

updateScenarioState' :: Scenario -> Scenario_state -> Scenario_env ->
                        Scenario_env
updateScenarioState' sce st env =
  case env of {
   Nil -> Nil;
   Cons p en' ->
    case p of {
     Pair s e ->
      case string_dec (scenarioId s) (scenarioId sce) of {
       Left -> Cons (Pair s st) (updateScenarioState' sce st en');
       Right -> Cons (Pair s e) (updateScenarioState' sce st en')}}}

filterList :: (List a1) -> (List a1) -> (a1 -> a1 -> Sumbool) -> List a1
filterList l1 l2 decA =
  case l2 of {
   Nil -> Nil;
   Cons e' lst ->
    case inList decA e' l1 of {
     True -> filterList l1 lst decA;
     False -> Cons e' (filterList l1 lst decA)}}

data Object =
   Build_object (List String) String Typ_env Typ_env (List Event_definition) 
 (List Scenario) (List
                 (Prod (Prod Scenario_state Event_instance) (Option Step))) 
 (List
 (Prod (Prod (Prod Scenario_state Event_instance) Scenario) (Option Step))) 
 (List
 (Prod (Prod (Option Scenario_state) (Option Event_definition))
 (List Event_instance))) (List (Prod Scenario Step)) (List
                                                     (Prod Scenario
                                                     Scenario_state))

events :: Object -> List Event_definition
events o =
  case o of {
   Build_object _ _ _ _ events0 _ _ _ _ _ _ -> events0}

stateEvStepMap' :: Object -> List
                   (Prod (Prod (Prod Scenario_state Event_instance) Scenario)
                   (Option Step))
stateEvStepMap' o =
  case o of {
   Build_object _ _ _ _ _ _ _ stateEvStepMap'0 _ _ _ -> stateEvStepMap'0}

stateEvDefInstanceMap :: Object -> List
                         (Prod
                         (Prod (Option Scenario_state)
                         (Option Event_definition)) (List Event_instance))
stateEvDefInstanceMap o =
  case o of {
   Build_object _ _ _ _ _ _ _ _ stateEvDefInstanceMap0 _ _ ->
    stateEvDefInstanceMap0}

data RaisedEvent =
   Build_raisedEvent Event_definition (List Range_typ)

eventDefinition :: RaisedEvent -> Event_definition
eventDefinition r =
  case r of {
   Build_raisedEvent eventDefinition0 _ -> eventDefinition0}

eventArguments :: RaisedEvent -> List Range_typ
eventArguments r =
  case r of {
   Build_raisedEvent _ eventArguments0 -> eventArguments0}

raisedEvent_dec :: RaisedEvent -> RaisedEvent -> Sumbool
raisedEvent_dec n m =
  case n of {
   Build_raisedEvent eventDefinition0 eventArguments0 ->
    case m of {
     Build_raisedEvent eventDefinition1 eventArguments1 ->
      sumbool_rec (\_ ->
        sumbool_rec (\_ -> Left) (\_ -> Right)
          (list_rec (\x -> case x of {
                            Nil -> Left;
                            Cons _ _ -> Right}) (\a0 _ h x ->
            case x of {
             Nil -> Right;
             Cons r l0 ->
              sumbool_rec (\_ ->
                sumbool_rec (\_ -> Left) (\_ -> Right) (h l0)) (\_ -> Right)
                (sum_rec (\a1 x0 ->
                  case x0 of {
                   Inl s ->
                    sumbool_rec (\_ -> Left) (\_ -> Right)
                      (sum_rec (\a2 x1 ->
                        case x1 of {
                         Inl s0 ->
                          sumbool_rec (\_ -> Left) (\_ -> Right)
                            (sum_rec (\a3 x2 ->
                              case x2 of {
                               Inl s1 ->
                                sumbool_rec (\_ -> Left) (\_ -> Right)
                                  (sum_rec (\a4 x3 ->
                                    case x3 of {
                                     Inl z ->
                                      sumbool_rec (\_ -> Left) (\_ -> Right)
                                        (z_rec (\x4 ->
                                          case x4 of {
                                           Z0 -> Left;
                                           _ -> Right}) (\p x4 ->
                                          case x4 of {
                                           Zpos p0 ->
                                            sumbool_rec (\_ -> Left) (\_ ->
                                              Right)
                                              (positive_rec (\_ h0 x5 ->
                                                case x5 of {
                                                 XI p2 ->
                                                  sumbool_rec (\_ -> Left)
                                                    (\_ -> Right) (h0 p2);
                                                 _ -> Right}) (\_ h0 x5 ->
                                                case x5 of {
                                                 XO p2 ->
                                                  sumbool_rec (\_ -> Left)
                                                    (\_ -> Right) (h0 p2);
                                                 _ -> Right}) (\x5 ->
                                                case x5 of {
                                                 XH -> Left;
                                                 _ -> Right}) p p0);
                                           _ -> Right}) (\p x4 ->
                                          case x4 of {
                                           Zneg p0 ->
                                            sumbool_rec (\_ -> Left) (\_ ->
                                              Right)
                                              (positive_rec (\_ h0 x5 ->
                                                case x5 of {
                                                 XI p2 ->
                                                  sumbool_rec (\_ -> Left)
                                                    (\_ -> Right) (h0 p2);
                                                 _ -> Right}) (\_ h0 x5 ->
                                                case x5 of {
                                                 XO p2 ->
                                                  sumbool_rec (\_ -> Left)
                                                    (\_ -> Right) (h0 p2);
                                                 _ -> Right}) (\x5 ->
                                                case x5 of {
                                                 XH -> Left;
                                                 _ -> Right}) p p0);
                                           _ -> Right}) a4 z);
                                     Inr _ -> Right}) (\b x3 ->
                                    case x3 of {
                                     Inl _ -> Right;
                                     Inr q ->
                                      sumbool_rec (\_ -> Left) (\_ -> Right)
                                        (case b of {
                                          Qmake qnum0 qden0 ->
                                           case q of {
                                            Qmake qnum1 qden1 ->
                                             sumbool_rec (\_ ->
                                               sumbool_rec (\_ -> Left)
                                                 (\_ -> Right)
                                                 (positive_rec (\_ h0 x4 ->
                                                   case x4 of {
                                                    XI p0 ->
                                                     sumbool_rec (\_ -> Left)
                                                       (\_ -> Right) 
                                                       (h0 p0);
                                                    _ -> Right}) (\_ h0 x4 ->
                                                   case x4 of {
                                                    XO p0 ->
                                                     sumbool_rec (\_ -> Left)
                                                       (\_ -> Right) 
                                                       (h0 p0);
                                                    _ -> Right}) (\x4 ->
                                                   case x4 of {
                                                    XH -> Left;
                                                    _ -> Right}) qden0 qden1))
                                               (\_ -> Right)
                                               (z_rec (\x4 ->
                                                 case x4 of {
                                                  Z0 -> Left;
                                                  _ -> Right}) (\p x4 ->
                                                 case x4 of {
                                                  Zpos p0 ->
                                                   sumbool_rec (\_ -> Left)
                                                     (\_ -> Right)
                                                     (positive_rec
                                                       (\_ h0 x5 ->
                                                       case x5 of {
                                                        XI p2 ->
                                                         sumbool_rec (\_ ->
                                                           Left) (\_ ->
                                                           Right) (h0 p2);
                                                        _ -> Right})
                                                       (\_ h0 x5 ->
                                                       case x5 of {
                                                        XO p2 ->
                                                         sumbool_rec (\_ ->
                                                           Left) (\_ ->
                                                           Right) (h0 p2);
                                                        _ -> Right}) (\x5 ->
                                                       case x5 of {
                                                        XH -> Left;
                                                        _ -> Right}) p p0);
                                                  _ -> Right}) (\p x4 ->
                                                 case x4 of {
                                                  Zneg p0 ->
                                                   sumbool_rec (\_ -> Left)
                                                     (\_ -> Right)
                                                     (positive_rec
                                                       (\_ h0 x5 ->
                                                       case x5 of {
                                                        XI p2 ->
                                                         sumbool_rec (\_ ->
                                                           Left) (\_ ->
                                                           Right) (h0 p2);
                                                        _ -> Right})
                                                       (\_ h0 x5 ->
                                                       case x5 of {
                                                        XO p2 ->
                                                         sumbool_rec (\_ ->
                                                           Left) (\_ ->
                                                           Right) (h0 p2);
                                                        _ -> Right}) (\x5 ->
                                                       case x5 of {
                                                        XH -> Left;
                                                        _ -> Right}) p p0);
                                                  _ -> Right}) qnum0 qnum1)}})})
                                    a3 s1);
                               Inr _ -> Right}) (\b x2 ->
                              case x2 of {
                               Inl _ -> Right;
                               Inr s1 ->
                                sumbool_rec (\_ -> Left) (\_ -> Right)
                                  (string_rec (\x3 ->
                                    case x3 of {
                                     EmptyString -> Left;
                                     String0 _ _ -> Right}) (\a3 _ h0 x3 ->
                                    case x3 of {
                                     EmptyString -> Right;
                                     String0 a4 s3 ->
                                      sumbool_rec (\_ ->
                                        sumbool_rec (\_ -> Left) (\_ ->
                                          Right) (h0 s3)) (\_ -> Right)
                                        (ascii_rec
                                          (\b0 b1 b2 b3 b4 b5 b6 b7 x4 ->
                                          case x4 of {
                                           Ascii b8 b9 b10 b11 b12 b13 b14
                                            b15 ->
                                            sumbool_rec (\_ ->
                                              sumbool_rec (\_ ->
                                                sumbool_rec (\_ ->
                                                  sumbool_rec (\_ ->
                                                    sumbool_rec (\_ ->
                                                      sumbool_rec (\_ ->
                                                        sumbool_rec (\_ ->
                                                          sumbool_rec (\_ ->
                                                            Left) (\_ ->
                                                            Right)
                                                            (bool_rec (\x5 ->
                                                              case x5 of {
                                                               True -> Left;
                                                               False -> Right})
                                                              (\x5 ->
                                                              case x5 of {
                                                               True -> Right;
                                                               False -> Left})
                                                              b7 b15)) (\_ ->
                                                          Right)
                                                          (bool_rec (\x5 ->
                                                            case x5 of {
                                                             True -> Left;
                                                             False -> Right})
                                                            (\x5 ->
                                                            case x5 of {
                                                             True -> Right;
                                                             False -> Left})
                                                            b6 b14)) (\_ ->
                                                        Right)
                                                        (bool_rec (\x5 ->
                                                          case x5 of {
                                                           True -> Left;
                                                           False -> Right})
                                                          (\x5 ->
                                                          case x5 of {
                                                           True -> Right;
                                                           False -> Left}) b5
                                                          b13)) (\_ -> Right)
                                                      (bool_rec (\x5 ->
                                                        case x5 of {
                                                         True -> Left;
                                                         False -> Right})
                                                        (\x5 ->
                                                        case x5 of {
                                                         True -> Right;
                                                         False -> Left}) b4
                                                        b12)) (\_ -> Right)
                                                    (bool_rec (\x5 ->
                                                      case x5 of {
                                                       True -> Left;
                                                       False -> Right})
                                                      (\x5 ->
                                                      case x5 of {
                                                       True -> Right;
                                                       False -> Left}) b3
                                                      b11)) (\_ -> Right)
                                                  (bool_rec (\x5 ->
                                                    case x5 of {
                                                     True -> Left;
                                                     False -> Right}) (\x5 ->
                                                    case x5 of {
                                                     True -> Right;
                                                     False -> Left}) b2 b10))
                                                (\_ -> Right)
                                                (bool_rec (\x5 ->
                                                  case x5 of {
                                                   True -> Left;
                                                   False -> Right}) (\x5 ->
                                                  case x5 of {
                                                   True -> Right;
                                                   False -> Left}) b1 b9))
                                              (\_ -> Right)
                                              (bool_rec (\x5 ->
                                                case x5 of {
                                                 True -> Left;
                                                 False -> Right}) (\x5 ->
                                                case x5 of {
                                                 True -> Right;
                                                 False -> Left}) b0 b8)}) a3
                                          a4)}) b s1)}) a2 s0);
                         Inr _ -> Right}) (\b x1 ->
                        case x1 of {
                         Inl _ -> Right;
                         Inr b0 ->
                          sumbool_rec (\_ -> Left) (\_ -> Right)
                            (bool_rec (\x2 ->
                              case x2 of {
                               True -> Left;
                               False -> Right}) (\x2 ->
                              case x2 of {
                               True -> Right;
                               False -> Left}) b b0)}) a1 s);
                   Inr _ -> Right}) (\b x0 ->
                  case x0 of {
                   Inl _ -> Right;
                   Inr n0 ->
                    sumbool_rec (\_ -> Left) (\_ -> Right)
                      (nat_rec (\x1 -> case x1 of {
                                        O -> Left;
                                        S _ -> Right}) (\_ h0 x1 ->
                        case x1 of {
                         O -> Right;
                         S n2 ->
                          sumbool_rec (\_ -> Left) (\_ -> Right) (h0 n2)}) b
                        n0)}) a0 r)}) eventArguments0 eventArguments1))
        (\_ -> Right)
        (case eventDefinition0 of {
          Build_event_definition eventKind0 eventId0 eventParams0 ->
           case eventDefinition1 of {
            Build_event_definition eventKind1 eventId1 eventParams1 ->
             sumbool_rec (\_ ->
               sumbool_rec (\_ ->
                 sumbool_rec (\_ -> Left) (\_ -> Right)
                   (list_rec (\x ->
                     case x of {
                      Nil -> Left;
                      Cons _ _ -> Right}) (\a1 _ h x ->
                     case x of {
                      Nil -> Right;
                      Cons t l0 ->
                       sumbool_rec (\_ ->
                         sumbool_rec (\_ -> Left) (\_ -> Right) (h l0))
                         (\_ -> Right)
                         (typ_rec (\x0 ->
                           case x0 of {
                            Int -> Left;
                            _ -> Right}) (\x0 ->
                           case x0 of {
                            Float -> Left;
                            _ -> Right}) (\x0 ->
                           case x0 of {
                            Str -> Left;
                            _ -> Right}) (\x0 ->
                           case x0 of {
                            Bool0 -> Left;
                            _ -> Right}) (\x0 ->
                           case x0 of {
                            Pointer -> Left;
                            _ -> Right}) (\x0 ->
                           case x0 of {
                            Opaque -> Left;
                            _ -> Right}) (\x0 ->
                           case x0 of {
                            Thread -> Left;
                            _ -> Right}) a1 t)}) eventParams0 eventParams1))
                 (\_ -> Right)
                 (string_rec (\x ->
                   case x of {
                    EmptyString -> Left;
                    String0 _ _ -> Right}) (\a0 _ h x ->
                   case x of {
                    EmptyString -> Right;
                    String0 a1 s0 ->
                     sumbool_rec (\_ ->
                       sumbool_rec (\_ -> Left) (\_ -> Right) (h s0)) (\_ ->
                       Right)
                       (ascii_rec (\b b0 b1 b2 b3 b4 b5 b6 x0 ->
                         case x0 of {
                          Ascii b7 b8 b9 b10 b11 b12 b13 b14 ->
                           sumbool_rec (\_ ->
                             sumbool_rec (\_ ->
                               sumbool_rec (\_ ->
                                 sumbool_rec (\_ ->
                                   sumbool_rec (\_ ->
                                     sumbool_rec (\_ ->
                                       sumbool_rec (\_ ->
                                         sumbool_rec (\_ -> Left) (\_ ->
                                           Right)
                                           (bool_rec (\x1 ->
                                             case x1 of {
                                              True -> Left;
                                              False -> Right}) (\x1 ->
                                             case x1 of {
                                              True -> Right;
                                              False -> Left}) b6 b14)) (\_ ->
                                         Right)
                                         (bool_rec (\x1 ->
                                           case x1 of {
                                            True -> Left;
                                            False -> Right}) (\x1 ->
                                           case x1 of {
                                            True -> Right;
                                            False -> Left}) b5 b13)) (\_ ->
                                       Right)
                                       (bool_rec (\x1 ->
                                         case x1 of {
                                          True -> Left;
                                          False -> Right}) (\x1 ->
                                         case x1 of {
                                          True -> Right;
                                          False -> Left}) b4 b12)) (\_ ->
                                     Right)
                                     (bool_rec (\x1 ->
                                       case x1 of {
                                        True -> Left;
                                        False -> Right}) (\x1 ->
                                       case x1 of {
                                        True -> Right;
                                        False -> Left}) b3 b11)) (\_ ->
                                   Right)
                                   (bool_rec (\x1 ->
                                     case x1 of {
                                      True -> Left;
                                      False -> Right}) (\x1 ->
                                     case x1 of {
                                      True -> Right;
                                      False -> Left}) b2 b10)) (\_ -> Right)
                                 (bool_rec (\x1 ->
                                   case x1 of {
                                    True -> Left;
                                    False -> Right}) (\x1 ->
                                   case x1 of {
                                    True -> Right;
                                    False -> Left}) b1 b9)) (\_ -> Right)
                               (bool_rec (\x1 ->
                                 case x1 of {
                                  True -> Left;
                                  False -> Right}) (\x1 ->
                                 case x1 of {
                                  True -> Right;
                                  False -> Left}) b0 b8)) (\_ -> Right)
                             (bool_rec (\x1 ->
                               case x1 of {
                                True -> Left;
                                False -> Right}) (\x1 ->
                               case x1 of {
                                True -> Right;
                                False -> Left}) b b7)}) a0 a1)}) eventId0
                   eventId1)) (\_ -> Right)
               (eventKind_rec (\x ->
                 case x of {
                  Internal -> Left;
                  _ -> Right}) (\x ->
                 case x of {
                  Imported -> Left;
                  _ -> Right}) (\x ->
                 case x of {
                  Exported -> Left;
                  _ -> Right}) eventKind0 eventKind1)}})}}

bind :: (ErrorOrResult a1) -> (a1 -> ErrorOrResult a1) -> ErrorOrResult a1
bind val func =
  case val of {
   Result v -> func v;
   Error err -> Error err}

bindZ :: (ErrorOrResult Range_typ) -> (Z -> ErrorOrResult Range_typ) ->
         ErrorOrResult Range_typ
bindZ val func =
  bind val (\v ->
    case v of {
     Inl s ->
      case s of {
       Inl s0 ->
        case s0 of {
         Inl s1 -> case s1 of {
                    Inl n -> func n;
                    Inr _ -> Error typeErr};
         Inr _ -> Error typeErr};
       Inr _ -> Error typeErr};
     Inr _ -> Error typeErr})

bindNum :: (ErrorOrResult Range_typ) -> ((Sum Z Q) -> ErrorOrResult
           Range_typ) -> ErrorOrResult Range_typ
bindNum val func =
  bind val (\v ->
    case v of {
     Inl s ->
      case s of {
       Inl s0 ->
        case s0 of {
         Inl s1 -> case s1 of {
                    Inl n -> func (Inl n);
                    Inr q -> func (Inr q)};
         Inr _ -> Error typeErr};
       Inr _ -> Error typeErr};
     Inr _ -> Error typeErr})

bindBool :: (ErrorOrResult Range_typ) -> (Bool -> ErrorOrResult Range_typ) ->
            ErrorOrResult Range_typ
bindBool val func =
  bind val (\v ->
    case v of {
     Inl s -> case s of {
               Inl _ -> Error typeErr;
               Inr b -> func b};
     Inr _ -> Error typeErr})

bindData :: (ErrorOrResult Range_typ) -> (Range_typ -> ErrorOrResult
            Range_typ) -> ErrorOrResult Range_typ
bindData =
  bind

evalMonad :: Value_env -> Expr -> ErrorOrResult Range_typ
evalMonad env e =
  case e of {
   EOr x y ->
    bindBool (evalMonad env x) (\b1 ->
      bindBool (evalMonad env y) (\b2 -> Result (Inl (Inr (orb b1 b2)))));
   EAnd x y ->
    bindBool (evalMonad env x) (\b1 ->
      bindBool (evalMonad env y) (\b2 -> Result (Inl (Inr (andb b1 b2)))));
   EEq x y ->
    bindData (evalMonad env x) (\n1 ->
      bindData (evalMonad env y) (\n2 ->
        case n1 of {
         Inl s ->
          case s of {
           Inl s0 ->
            case s0 of {
             Inl s1 ->
              case s1 of {
               Inl i ->
                case n2 of {
                 Inl s2 ->
                  case s2 of {
                   Inl s3 ->
                    case s3 of {
                     Inl s4 ->
                      case s4 of {
                       Inl j -> Result (Inl (Inr (eqb2 i j)));
                       Inr _ -> Error typeErr};
                     Inr _ -> Error typeErr};
                   Inr _ -> Error typeErr};
                 Inr _ -> Error typeErr};
               Inr p ->
                case n2 of {
                 Inl s2 ->
                  case s2 of {
                   Inl s3 ->
                    case s3 of {
                     Inl s4 ->
                      case s4 of {
                       Inl _ -> Error typeErr;
                       Inr q -> Result (Inl (Inr (qeq_bool p q)))};
                     Inr _ -> Error typeErr};
                   Inr _ -> Error typeErr};
                 Inr _ -> Error typeErr}};
             Inr s1 ->
              case n2 of {
               Inl s2 ->
                case s2 of {
                 Inl s3 ->
                  case s3 of {
                   Inl _ -> Error typeErr;
                   Inr s4 -> Result (Inl (Inr (string_dec_bool s1 s4)))};
                 Inr _ -> Error typeErr};
               Inr _ -> Error typeErr}};
           Inr s1 ->
            case n2 of {
             Inl s0 ->
              case s0 of {
               Inl _ -> Error typeErr;
               Inr s2 -> Result (Inl (Inr (eqb s1 s2)))};
             Inr _ -> Error typeErr}};
         Inr s1 ->
          case n2 of {
           Inl _ -> Error typeErr;
           Inr s2 -> Result (Inl (Inr (eqb0 s1 s2)))}}));
   ELt x y ->
    bindNum (evalMonad env x) (\n1 ->
      bindNum (evalMonad env y) (\n2 ->
        case n1 of {
         Inl i ->
          case n2 of {
           Inl j -> Result (Inl (Inr (ltb i j)));
           Inr _ -> Error typeErr};
         Inr p ->
          case n2 of {
           Inl _ -> Error typeErr;
           Inr q -> Result (Inl (Inr
            (andb (qle_bool p q) (negb (qeq_bool p q)))))}}));
   ELe x y ->
    bindNum (evalMonad env x) (\n1 ->
      bindNum (evalMonad env y) (\n2 ->
        case n1 of {
         Inl i ->
          case n2 of {
           Inl j -> Result (Inl (Inr (leb i j)));
           Inr _ -> Error typeErr};
         Inr p ->
          case n2 of {
           Inl _ -> Error typeErr;
           Inr q -> Result (Inl (Inr (qle_bool p q)))}}));
   EPlus x y ->
    bindNum (evalMonad env x) (\n1 ->
      bindNum (evalMonad env y) (\n2 ->
        case n1 of {
         Inl i ->
          case n2 of {
           Inl j -> Result (Inl (Inl (Inl (Inl (add0 i j)))));
           Inr _ -> Error typeErr};
         Inr p ->
          case n2 of {
           Inl _ -> Error typeErr;
           Inr q -> Result (Inl (Inl (Inl (Inr (qplus p q)))))}}));
   EMult x y ->
    bindNum (evalMonad env x) (\n1 ->
      bindNum (evalMonad env y) (\n2 ->
        case n1 of {
         Inl i ->
          case n2 of {
           Inl j -> Result (Inl (Inl (Inl (Inl (mul0 i j)))));
           Inr _ -> Error typeErr};
         Inr p ->
          case n2 of {
           Inl _ -> Error typeErr;
           Inr q -> Result (Inl (Inl (Inl (Inr (qmult p q)))))}}));
   EDiv x y ->
    bindNum (evalMonad env x) (\n1 ->
      bindNum (evalMonad env y) (\n2 ->
        case n1 of {
         Inl i ->
          case n2 of {
           Inl j -> Result (Inl (Inl (Inl (Inl (div i j)))));
           Inr _ -> Error typeErr};
         Inr p ->
          case n2 of {
           Inl _ -> Error typeErr;
           Inr q -> Result (Inl (Inl (Inl (Inr (qdiv p q)))))}}));
   EMod x y ->
    bindZ (evalMonad env x) (\n1 ->
      bindZ (evalMonad env y) (\n2 -> Result (Inl (Inl (Inl (Inl
        (modulo n1 n2)))))));
   ENot x -> bindBool (evalMonad env x) (\b1 -> Result (Inl (Inr (negb b1))));
   EAtom x ->
    case x of {
     AInt z -> Result (Inl (Inl (Inl (Inl z))));
     AFloat q -> Result (Inl (Inl (Inl (Inr q))));
     AIdent i ->
      case getValue (AIdent i) env of {
       Some r -> Result r;
       None -> Error typeErr};
     ABool b -> Result (Inl (Inr b));
     ANull -> Result (Inr O);
     AString s -> Result (Inl (Inl (Inr s)))}}

calculateExprList :: Value_env -> (List Expr) -> ErrorOrResult
                     (List Range_typ)
calculateExprList en lst =
  case lst of {
   Nil -> Result Nil;
   Cons ex lst' ->
    case evalMonad en ex of {
     Result v ->
      case calculateExprList en lst' of {
       Result vlst -> Result (Cons v vlst);
       Error s -> Error s};
     Error error -> Error error}}

getEventByName :: String -> (List Event_definition) -> Option
                  Event_definition
getEventByName name elist =
  case elist of {
   Nil -> None;
   Cons e lst' ->
    case string_dec (eventId e) name of {
     Left -> Some e;
     Right -> getEventByName name lst'}}

parameterMatchFunc :: (List Range_typ) -> (List Typ) -> Bool
parameterMatchFunc rl tl =
  case rl of {
   Nil -> case tl of {
           Nil -> True;
           Cons _ _ -> False};
   Cons rt rlst ->
    case tl of {
     Nil -> False;
     Cons t tlst ->
      case typeValMatch t rt of {
       True -> parameterMatchFunc rlst tlst;
       False -> False}}}

execAction :: (Prod Value_env (List RaisedEvent)) -> Action -> (List
              Event_definition) -> ErrorOrResult
              (Prod Value_env (List RaisedEvent))
execAction etaE a eventList =
  case a of {
   Skip -> Result etaE;
   StateUpdate l ex ->
    case l of {
     AIdent s ->
      let {er = evalMonad (fst etaE) ex} in
      case er of {
       Result v ->
        case updateValueEnvInv (AIdent s) v (fst etaE) of {
         Some ven -> Result (Pair ven (snd etaE));
         None -> Error typeErr};
       Error r -> Error r};
     _ -> Error typeErr};
   RaiseStmt n lst ->
    let {vlist = calculateExprList (fst etaE) lst} in
    case vlist of {
     Result vlist' ->
      let {event = getEventByName n eventList} in
      case event of {
       Some ev ->
        case parameterMatchFunc vlist' (eventParams ev) of {
         True -> Result (Pair (fst etaE)
          (app (Cons (Build_raisedEvent ev vlist') Nil) (snd etaE)));
         False -> Error typeErr};
       None -> Error eventNotDeclaredErr};
     Error s -> Error s};
   Seq a1 a2 ->
    let {r1 = execAction etaE a1 eventList} in
    case r1 of {
     Result re1 -> execAction re1 a2 eventList;
     Error r -> Error r}}

error1 :: String
error1 =
  String0 (Ascii False True True True False True True False) (String0 (Ascii
    True True True True False True True False) (String0 (Ascii False False
    False False False True False False) (String0 (Ascii True True False False
    True True True False) (String0 (Ascii True True False False False True
    True False) (String0 (Ascii True False True False False True True False)
    (String0 (Ascii False True True True False True True False) (String0
    (Ascii True False False False False True True False) (String0 (Ascii
    False True False False True True True False) (String0 (Ascii True False
    False True False True True False) (String0 (Ascii True True True True
    False True True False) (String0 (Ascii False False False False False True
    False False) (String0 (Ascii True True False False True True True False)
    (String0 (Ascii False False True False True True True False) (String0
    (Ascii True False False False False True True False) (String0 (Ascii
    False False True False True True True False) (String0 (Ascii True False
    True False False True True False) (String0 (Ascii False False False False
    False True False False) (String0 (Ascii True True False False True True
    True False) (String0 (Ascii False False False False True True True False)
    (String0 (Ascii True False True False False True True False) (String0
    (Ascii True True False False False True True False) (String0 (Ascii True
    False False True False True True False) (String0 (Ascii False True True
    False False True True False) (String0 (Ascii True False False True False
    True True False) (String0 (Ascii True False True False False True True
    False) (String0 (Ascii False False True False False True True False)
    EmptyString))))))))))))))))))))))))))

error3 :: String
error3 =
  String0 (Ascii False True True True False True True False) (String0 (Ascii
    True True True True False True True False) (String0 (Ascii False False
    False False False True False False) (String0 (Ascii True False True False
    False True True False) (String0 (Ascii False True True False True True
    True False) (String0 (Ascii True False True False False True True False)
    (String0 (Ascii False True True True False True True False) (String0
    (Ascii False False True False True True True False) (String0 (Ascii False
    False False False False True False False) (String0 (Ascii True False
    False True False True True False) (String0 (Ascii False True True True
    False True True False) (String0 (Ascii True True False False True True
    True False) (String0 (Ascii False False True False True True True False)
    (String0 (Ascii True False False False False True True False) (String0
    (Ascii False True True True False True True False) (String0 (Ascii True
    True False False False True True False) (String0 (Ascii True False True
    False False True True False) EmptyString))))))))))))))))

error4 :: String
error4 =
  String0 (Ascii False True True True False True True False) (String0 (Ascii
    True True True True False True True False) (String0 (Ascii False False
    False False False True False False) (String0 (Ascii True True False False
    True True True False) (String0 (Ascii False False True False True True
    True False) (String0 (Ascii True False True False False True True False)
    (String0 (Ascii False False False False True True True False)
    EmptyString))))))

error5 :: String
error5 =
  String0 (Ascii False False True False True True True False) (String0 (Ascii
    True False False True True True True False) (String0 (Ascii False False
    False False True True True False) (String0 (Ascii True False True False
    False True True False) (String0 (Ascii False False False False False True
    False False) (String0 (Ascii False True True True False True True False)
    (String0 (Ascii True True True True False True True False) (String0
    (Ascii False False True False True True True False) (String0 (Ascii False
    False False False False True False False) (String0 (Ascii True False True
    True False True True False) (String0 (Ascii True False False False False
    True True False) (String0 (Ascii False False True False True True True
    False) (String0 (Ascii True True False False False True True False)
    (String0 (Ascii False False False True False True True False) (String0
    (Ascii True False True False False True True False) (String0 (Ascii False
    False True False False True True False) EmptyString)))))))))))))))

error6 :: String
error6 =
  String0 (Ascii False True True True False True True False) (String0 (Ascii
    True True True True False True True False) (String0 (Ascii False False
    True False True True True False) (String0 (Ascii False False False False
    False True False False) (String0 (Ascii True False True True False True
    True False) (String0 (Ascii True False False False False True True False)
    (String0 (Ascii False False True False True True True False) (String0
    (Ascii True True False False False True True False) (String0 (Ascii False
    False False True False True True False) (String0 (Ascii True False True
    False False True True False) (String0 (Ascii False False True False False
    True True False) EmptyString))))))))))

error7 :: String
error7 =
  String0 (Ascii True True False False True True True False) (String0 (Ascii
    True True False False False True True False) (String0 (Ascii True False
    True False False True True False) (String0 (Ascii False True True True
    False True True False) (String0 (Ascii True False False False False True
    True False) (String0 (Ascii False True False False True True True False)
    (String0 (Ascii True False False True False True True False) (String0
    (Ascii True True True True False True True False) (String0 (Ascii False
    False False False False True False False) (String0 (Ascii False True True
    True False True True False) (String0 (Ascii True True True True False
    True True False) (String0 (Ascii False False True False True True True
    False) (String0 (Ascii False False False False False True False False)
    (String0 (Ascii True False True True False True True False) (String0
    (Ascii True False False False False True True False) (String0 (Ascii
    False False True False True True True False) (String0 (Ascii True True
    False False False True True False) (String0 (Ascii False False False True
    False True True False) (String0 (Ascii True False True False False True
    True False) (String0 (Ascii False False True False False True True False)
    EmptyString)))))))))))))))))))

error11 :: String
error11 =
  String0 (Ascii False False True False False True True False) (String0
    (Ascii True False False False False True True False) (String0 (Ascii
    False False True False True True True False) (String0 (Ascii True False
    False False False True True False) (String0 (Ascii False False False
    False False True False False) (String0 (Ascii False True True True False
    True True False) (String0 (Ascii True True True True False True True
    False) (String0 (Ascii False True True True False True True False)
    (String0 (Ascii True False True True False True False False) (String0
    (Ascii False False True False False True True False) (String0 (Ascii True
    False True False False True True False) (String0 (Ascii False False True
    False True True True False) (String0 (Ascii True False True False False
    True True False) (String0 (Ascii False True False False True True True
    False) (String0 (Ascii True False True True False True True False)
    (String0 (Ascii True False False True False True True False) (String0
    (Ascii False True True True False True True False) (String0 (Ascii True
    False False True False True True False) (String0 (Ascii True True False
    False True True True False) (String0 (Ascii True False True True False
    True True False) EmptyString)))))))))))))))))))

error12 :: String
error12 =
  String0 (Ascii False True True True False True True False) (String0 (Ascii
    True False True False True True True False) (String0 (Ascii True False
    True True False True True False) (String0 (Ascii False True False False
    False True True False) (String0 (Ascii True False True False False True
    True False) (String0 (Ascii False True False False True True True False)
    (String0 (Ascii False False False False False True False False) (String0
    (Ascii True True True True False True True False) (String0 (Ascii False
    True True False False True True False) (String0 (Ascii False False False
    False False True False False) (String0 (Ascii False False True True False
    True True False) (String0 (Ascii True False False True False True True
    False) (String0 (Ascii True True False False True True True False)
    (String0 (Ascii False False True False True True True False) (String0
    (Ascii False False False False False True False False) (String0 (Ascii
    False True True True False True True False) (String0 (Ascii True True
    True True False True True False) (String0 (Ascii False False True False
    True True True False) (String0 (Ascii False False False False False True
    False False) (String0 (Ascii True False True True False True True False)
    (String0 (Ascii True False False False False True True False) (String0
    (Ascii False False True False True True True False) (String0 (Ascii True
    True False False False True True False) (String0 (Ascii False False False
    True False True True False) (String0 (Ascii True False True False False
    True True False) (String0 (Ascii False False True False False True True
    False) EmptyString)))))))))))))))))))))))))

error13 :: String
error13 =
  String0 (Ascii False False True False False True True False) (String0
    (Ascii True False False False False True True False) (String0 (Ascii
    False False True False True True True False) (String0 (Ascii True False
    False False False True True False) (String0 (Ascii False False False
    False False True False False) (String0 (Ascii True True False False False
    True True False) (String0 (Ascii True True True True False True True
    False) (String0 (Ascii False True True True False True True False)
    (String0 (Ascii False True True False False True True False) (String0
    (Ascii False False True True False True True False) (String0 (Ascii True
    False False True False True True False) (String0 (Ascii True True False
    False False True True False) (String0 (Ascii False False True False True
    True True False) EmptyString))))))))))))

error14 :: String
error14 =
  String0 (Ascii True True False False False True True False) (String0 (Ascii
    True True True True False True True False) (String0 (Ascii False True
    True True False True True False) (String0 (Ascii False False True False
    True True True False) (String0 (Ascii False True False False True True
    True False) (String0 (Ascii True True True True False True True False)
    (String0 (Ascii False False True True False True True False) (String0
    (Ascii False False False False False True False False) (String0 (Ascii
    True True False False False True True False) (String0 (Ascii True True
    True True False True True False) (String0 (Ascii False True True True
    False True True False) (String0 (Ascii False True True False False True
    True False) (String0 (Ascii False False True True False True True False)
    (String0 (Ascii True False False True False True True False) (String0
    (Ascii True True False False False True True False) (String0 (Ascii False
    False True False True True True False) EmptyString)))))))))))))))

type Monitor = Object

data Configuration =
   Build_configuration Value_env Scenario_env (List RaisedEvent) (List
                                                                 RaisedEvent) 
 (List Scenario) (List (Prod Scenario Event_definition))

datastate :: Monitor -> Configuration -> Value_env
datastate _ c =
  case c of {
   Build_configuration datastate0 _ _ _ _ _ -> datastate0}

controlstate :: Monitor -> Configuration -> Scenario_env
controlstate _ c =
  case c of {
   Build_configuration _ controlstate0 _ _ _ _ -> controlstate0}

raisedevents :: Monitor -> Configuration -> List RaisedEvent
raisedevents _ c =
  case c of {
   Build_configuration _ _ raisedevents0 _ _ _ -> raisedevents0}

exportedevents :: Monitor -> Configuration -> List RaisedEvent
exportedevents _ c =
  case c of {
   Build_configuration _ _ _ exportedevents0 _ _ -> exportedevents0}

finishedscenarios :: Monitor -> Configuration -> List Scenario
finishedscenarios _ c =
  case c of {
   Build_configuration _ _ _ _ finishedscenarios0 _ -> finishedscenarios0}

sceEventMap :: Monitor -> Configuration -> List
               (Prod Scenario Event_definition)
sceEventMap _ c =
  case c of {
   Build_configuration _ _ _ _ _ sceEventMap0 -> sceEventMap0}

op_string_dec :: (Option String) -> (Option String) -> Sumbool
op_string_dec n m =
  case n of {
   Some s -> case m of {
              Some s0 -> string_dec s s0;
              None -> Right};
   None -> case m of {
            Some _ -> Right;
            None -> Left}}

op_event_definition_dec :: (Option Event_definition) -> (Option
                           Event_definition) -> Sumbool
op_event_definition_dec n m =
  case n of {
   Some e -> case m of {
              Some e0 -> event_definition_dec e e0;
              None -> Right};
   None -> case m of {
            Some _ -> Right;
            None -> Left}}

transEvMapFunc :: (List
                  (Prod
                  (Prod (Option Scenario_state) (Option Event_definition))
                  (List Event_instance))) -> (Prod (Option Scenario_state)
                  (Option Event_definition)) -> Option (List Event_instance)
transEvMapFunc l f =
  case l of {
   Nil -> None;
   Cons p l' ->
    case p of {
     Pair p0 c ->
      case p0 of {
       Pair a b ->
        case op_string_dec a (fst f) of {
         Left ->
          case op_event_definition_dec b (snd f) of {
           Left -> Some c;
           Right -> transEvMapFunc l' f};
         Right -> transEvMapFunc l' f}}}}

op_stpMap_dec :: (Prod (Prod Scenario_state Event_instance) Scenario) ->
                 (Prod (Prod Scenario_state Event_instance) Scenario) ->
                 Sumbool
op_stpMap_dec n m =
  case n of {
   Pair p s ->
    case m of {
     Pair p0 s0 ->
      case p of {
       Pair s1 e ->
        case p0 of {
         Pair s2 e0 ->
          let {s3 = string_dec s1 s2} in
          case s3 of {
           Left ->
            let {s4 = event_instance_dec e e0} in
            case s4 of {
             Left -> scenario_dec s s0;
             Right -> Right};
           Right -> Right}}}}}

stpStpMapFunc :: (List
                 (Prod (Prod (Prod Scenario_state Event_instance) Scenario)
                 (Option Step))) -> (Prod
                 (Prod Scenario_state Event_instance) Scenario) -> Option
                 Step
stpStpMapFunc l f =
  case l of {
   Nil -> None;
   Cons p l' ->
    case p of {
     Pair a d ->
      case op_stpMap_dec a f of {
       Left -> d;
       Right -> stpStpMapFunc l' f}}}

getStep' :: Monitor -> Configuration -> Scenario -> Event_instance -> Option
            Step
getStep' m conf sce e =
  case getScenarioState sce (controlstate m conf) of {
   Some s -> stpStpMapFunc (stateEvStepMap' m) (Pair (Pair s e) sce);
   None -> None}

updateDataState :: Value_env -> (List Atom) -> Value_env
updateDataState ven lst =
  case ven of {
   Nil -> Nil;
   Cons p ven' ->
    case p of {
     Pair a v ->
      case inList atom_eq_dec a lst of {
       True -> Cons (Pair a v) (updateDataState ven' lst);
       False -> updateDataState ven' lst}}}

updateControlState :: Scenario_env -> Scenario -> Step -> Scenario_env
updateControlState cs sce stp =
  updateScenarioState' sce (pro_state stp) cs

removeEvent' :: RaisedEvent -> (List RaisedEvent) -> List RaisedEvent
removeEvent' re lst =
  case lst of {
   Nil -> Nil;
   Cons re' lst' ->
    case raisedEvent_dec re re' of {
     Left -> removeEvent' re lst';
     Right -> Cons re' (removeEvent' re lst')}}

configTransition :: Value_env -> RaisedEvent -> Event_instance -> Scenario ->
                    Step -> Monitor -> Configuration -> ErrorOrResult
                    Configuration
configTransition env re _ sce stp m conf =
  case execAction (Pair env Nil) (stepActions stp)
         (filter (\e -> case eventKind e of {
                         Imported -> False;
                         _ -> True}) (events m)) of {
   Result v ->
    case v of {
     Pair ds' res ->
      let {ds'' = updateDataState ds' (dom (datastate m conf))} in
      Result (Build_configuration ds''
      (updateControlState (controlstate m conf) sce stp)
      (filter (\re0 ->
        eventKind_beq (eventKind (eventDefinition re0)) Internal) res)
      (filter (\re0 ->
        eventKind_beq (eventKind (eventDefinition re0)) Exported) res) (Cons
      sce Nil) (Cons (Pair sce (eventDefinition re)) Nil))};
   Error s -> Error s}

findEventInstance :: RaisedEvent -> Value_env -> (List Event_instance) ->
                     Option Event_instance
findEventInstance re en elist =
  case elist of {
   Nil -> None;
   Cons e lst' ->
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
         Inl s ->
          case s of {
           Inl _ -> None;
           Inr b ->
            case b of {
             True -> Some e;
             False -> findEventInstance re en lst'}};
         Inr _ -> None};
       Error _ -> None};
     Error _ -> None}}

constructConfig :: Scenario -> RaisedEvent -> Monitor -> Configuration ->
                   ErrorOrResult Configuration
constructConfig sce re m conf =
  let {sce_state = getScenarioState sce (controlstate m conf)} in
  case sce_state of {
   Some state ->
    case transEvMapFunc (stateEvDefInstanceMap m) (Pair (Some state) (Some
           (eventDefinition re))) of {
     Some le ->
      let {e' = findEventInstance re (datastate m conf) le} in
      case e' of {
       Some e ->
        let {
         ex_env' = createValueEnv (eventArgs e)
                     (eventParams (eventDefinition re)) (eventArguments re)}
        in
        case ex_env' of {
         Result ex_env ->
          let {extend_env = extendValEnv (datastate m conf) ex_env} in
          let {stp = getStep' m conf sce e} in
          case stp of {
           Some stp' ->
            case configTransition extend_env re e sce stp' m conf of {
             Result s -> Result s;
             Error _ -> Error error11};
           None -> Error error4};
         Error _ -> Error error12};
       None -> Error error3};
     None -> Error error3};
   None -> Error error1}

constructConfigList' :: (List Scenario) -> RaisedEvent -> Monitor ->
                        Configuration -> ErrorOrResult (List Configuration)
constructConfigList' scs re m conf =
  case scs of {
   Nil -> Result Nil;
   Cons sce scenarios' ->
    case constructConfig sce re m conf of {
     Result conf' ->
      case constructConfigList' scenarios' re m conf of {
       Result lst -> Result (Cons conf' lst);
       Error s -> Error s};
     Error s -> Error s}}

constructConfigList :: (List Scenario) -> RaisedEvent -> Monitor ->
                       Configuration -> ErrorOrResult (List Configuration)
constructConfigList scs re m conf =
  let {scs' = filterList (finishedscenarios m conf) scs scenario_dec} in
  let {
   scs'' = filter (\x ->
             inList event_definition_dec (eventDefinition re) (alphabet x))
             scs'}
  in
  constructConfigList' scs'' re m conf

mergeDataStateFunc :: Value_env -> Value_env -> Value_env -> ErrorOrResult
                      (List (Prod Atom (Prod Typ Range_typ)))
mergeDataStateFunc dso ds1 ds2 =
  case dso of {
   Nil ->
    case ds1 of {
     Nil -> case ds2 of {
             Nil -> Result Nil;
             Cons _ _ -> Error error6};
     Cons _ _ -> Error error6};
   Cons p lst0 ->
    case p of {
     Pair n1 p0 ->
      case p0 of {
       Pair t1 v0 ->
        case ds1 of {
         Nil -> Error error6;
         Cons p1 lst1 ->
          case p1 of {
           Pair n2 p2 ->
            case p2 of {
             Pair t2 v1 ->
              case ds2 of {
               Nil -> Error error6;
               Cons p3 lst2 ->
                case p3 of {
                 Pair n3 p4 ->
                  case p4 of {
                   Pair t3 v2 ->
                    case atom_eq_dec n1 n2 of {
                     Left ->
                      case atom_eq_dec n1 n3 of {
                       Left ->
                        case typ_eq_dec t1 t2 of {
                         Left ->
                          case typ_eq_dec t1 t3 of {
                           Left ->
                            let {r = mergeDataStateFunc lst0 lst1 lst2} in
                            case r of {
                             Result lst ->
                              case range_typ_dec v1 v2 of {
                               Left -> Result (Cons (Pair n1 (Pair t1 v1))
                                lst);
                               Right ->
                                case range_typ_dec v1 v0 of {
                                 Left -> Result (Cons (Pair n1 (Pair t1 v2))
                                  lst);
                                 Right ->
                                  case range_typ_dec v2 v0 of {
                                   Left -> Result (Cons (Pair n1 (Pair t1
                                    v1)) lst);
                                   Right -> Error error13}}};
                             Error s -> Error s};
                           Right -> Error error5};
                         Right -> Error error5};
                       Right -> Error error5};
                     Right -> Error error5}}}}}}}}}}

mergeControlStateFunc :: Scenario_env -> Scenario_env -> Scenario_env ->
                         ErrorOrResult (List (Prod Scenario Scenario_state))
mergeControlStateFunc cso cs1 cs2 =
  case cso of {
   Nil ->
    case cs1 of {
     Nil -> case cs2 of {
             Nil -> Result Nil;
             Cons _ _ -> Error error6};
     Cons _ _ -> Error error6};
   Cons p lst0 ->
    case p of {
     Pair sc0 s0 ->
      case cs1 of {
       Nil -> Error error6;
       Cons p0 lst1 ->
        case p0 of {
         Pair sc1 s1 ->
          case cs2 of {
           Nil -> Error error6;
           Cons p1 lst2 ->
            case p1 of {
             Pair sc2 s2 ->
              case scenario_dec sc0 sc1 of {
               Left ->
                case scenario_dec sc0 sc2 of {
                 Left ->
                  let {r = mergeControlStateFunc lst0 lst1 lst2} in
                  case r of {
                   Result lst ->
                    case string_dec s1 s2 of {
                     Left -> Result (Cons (Pair sc0 s1) lst);
                     Right ->
                      case string_dec s1 s0 of {
                       Left -> Result (Cons (Pair sc0 s2) lst);
                       Right ->
                        case string_dec s2 s0 of {
                         Left -> Result (Cons (Pair sc0 s1) lst);
                         Right -> Error error14}}};
                   Error s -> Error s};
                 Right -> Error error7};
               Right -> Error error7}}}}}}}

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
     cs = mergeControlStateFunc (controlstate m config)
            (controlstate m config1) (controlstate m config2)}
    in
    case cs of {
     Result cs' ->
      let {
       raisedEvents = app (raisedevents m config1) (raisedevents m config2)}
      in
      let {
       exportedEvents = app (exportedevents m config1)
                          (exportedevents m config2)}
      in
      let {
       finishedEvents = app (finishedscenarios m config1)
                          (finishedscenarios m config2)}
      in
      let {
       sceEventMaps = app (sceEventMap m config1) (sceEventMap m config2)}
      in
      Result (Build_configuration ds' cs' raisedEvents exportedEvents
      finishedEvents sceEventMaps);
     Error s -> Error s};
   Error s -> Error s}

innerCombineFunc'''' :: Monitor -> Configuration -> (List Configuration) ->
                        Option Configuration
innerCombineFunc'''' m originconf confList =
  case confList of {
   Nil -> None;
   Cons conf' l ->
    case l of {
     Nil ->
      case mergeConfigFunc' m originconf originconf conf' of {
       Result c -> Some c;
       Error _ -> None};
     Cons _ _ ->
      case innerCombineFunc'''' m originconf l of {
       Some c ->
        case mergeConfigFunc' m originconf conf' c of {
         Result rc -> Some rc;
         Error _ -> None};
       None -> None}}}

removeEventFromConf :: RaisedEvent -> Monitor -> Configuration ->
                       Configuration
removeEventFromConf e m conf =
  Build_configuration (datastate m conf) (controlstate m conf)
    (removeEvent' e (raisedevents m conf)) (exportedevents m conf)
    (finishedscenarios m conf) (sceEventMap m conf)

combineFunc :: RaisedEvent -> Monitor -> Configuration -> Option
               Configuration
combineFunc e m conf =
  case constructConfigList (dom (controlstate m conf)) e m conf of {
   Result lst ->
    case lst of {
     Nil -> None;
     Cons _ _ ->
      case innerCombineFunc'''' m conf lst of {
       Some v -> Some (removeEventFromConf e m v);
       None -> None}};
   Error _ -> None}

data ADTSig =
   Build_ADTSig (Any -> List ()) (Any -> Prod (List ()) (Option ()))

type ConstructorIndex = Any

type MethodIndex = Any

vector_caseS' :: (a1 -> Nat -> (T0 a1) -> a2 -> a3) -> Nat -> (T1 a1) -> a2
                 -> a3
vector_caseS' h n v q =
  let {h0 = \h0 t -> h h0 n t q} in
  case v of {
   Nil1 -> __;
   Cons1 h1 _ t -> h0 h1 t}

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

icons :: a1 -> Nat -> (T1 a1) -> a2 -> (Ilist a1 a2) -> Prim_prod a2 Any
icons _ _ _ b il =
  Build_prim_prod b il

inil :: Unit
inil =
  Tt

ilist_hd :: Nat -> (T1 a1) -> (Ilist a1 a2) -> Any
ilist_hd _ as0 il =
  case as0 of {
   Nil1 -> unsafeCoerce Tt;
   Cons1 _ _ _ -> prim_fst (unsafeCoerce il)}

ilist_tl :: Nat -> (T1 a1) -> (Ilist a1 a2) -> Any
ilist_tl _ as0 il =
  case as0 of {
   Nil1 -> unsafeCoerce Tt;
   Cons1 _ _ _ -> prim_snd (unsafeCoerce il)}

ith :: Nat -> (T1 a1) -> (Ilist a1 a2) -> T -> a2
ith _ as0 il n =
  case n of {
   F1 k ->
    caseS (\h n0 t -> unsafeCoerce ilist_hd (S n0) (Cons1 h n0 t)) k as0 il;
   FS k n' ->
    vector_caseS' (\h n0 t m il0 ->
      ith n0 t (ilist_tl (S n0) (Cons0 h n0 t) il0) m) k as0 n' il}

type IndexBound a =
  T
  -- singleton inductive, whose constructor was Build_IndexBound
  
ibound :: Nat -> a1 -> (T1 a1) -> (IndexBound a1) -> T
ibound _ _ _ indexBound =
  indexBound

data BoundedIndex a =
   Build_BoundedIndex a (IndexBound a)

bindex :: Nat -> (T1 a1) -> (BoundedIndex a1) -> a1
bindex _ _ b =
  case b of {
   Build_BoundedIndex bindex0 _ -> bindex0}

indexb :: Nat -> (T1 a1) -> (BoundedIndex a1) -> IndexBound a1
indexb _ _ b =
  case b of {
   Build_BoundedIndex _ indexb0 -> indexb0}

data ConsSig =
   Build_consSig String (List ())

consID :: ConsSig -> String
consID c =
  case c of {
   Build_consSig consID0 _ -> consID0}

consDom :: ConsSig -> List ()
consDom c =
  case c of {
   Build_consSig _ consDom0 -> consDom0}

data MethSig =
   Build_methSig String (List ()) (Option ())

methID :: MethSig -> String
methID m =
  case m of {
   Build_methSig methID0 _ _ -> methID0}

methDom :: MethSig -> List ()
methDom m =
  case m of {
   Build_methSig _ methDom0 _ -> methDom0}

methCod :: MethSig -> Option ()
methCod m =
  case m of {
   Build_methSig _ _ methCod0 -> methCod0}

data DecoratedADTSig =
   Build_DecoratedADTSig ADTSig Nat Nat (T1 String) (T1 String)

decADTSig :: DecoratedADTSig -> ADTSig
decADTSig d =
  case d of {
   Build_DecoratedADTSig decADTSig0 _ _ _ _ -> decADTSig0}

buildADTSig :: Nat -> Nat -> (T1 ConsSig) -> (T1 MethSig) -> DecoratedADTSig
buildADTSig n n' consSigs methSigs =
  Build_DecoratedADTSig (Build_ADTSig (\idx ->
    consDom (nth n consSigs (unsafeCoerce idx))) (\idx ->
    let {domcod = nth n' methSigs (unsafeCoerce idx)} in
    Pair (methDom domcod) (methCod domcod))) n n' (map0 consID n consSigs)
    (map0 methID n' methSigs)

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

type CADT = SigT () (PcADT Any)

type CRep = Any

cMethods :: ADTSig -> CADT -> MethodIndex -> CMethodType CRep
cMethods sig c idx =
  pcMethods sig (projT2 c) idx

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

getcConsDef :: Nat -> (T1 ConsSig) -> (Ilist ConsSig (CConsDef a1)) -> T ->
               CConstructorType a1
getcConsDef n consSigs consDefs idx =
  cConsBody (nth n consSigs idx) (ith n consSigs consDefs idx)

getcMethDef :: Nat -> (T1 MethSig) -> (Ilist MethSig (CMethDef a1)) -> T ->
               CMethodType a1
getcMethDef n methSigs methDefs idx =
  cMethBody (nth n methSigs idx) (ith n methSigs methDefs idx)

type DecoratedcADT = CADT

buildcADT :: Nat -> Nat -> (T1 ConsSig) -> (T1 MethSig) -> (Ilist ConsSig
             (CConsDef a1)) -> (Ilist MethSig (CMethDef a1)) -> DecoratedcADT
buildcADT n n' consSigs methSigs consDefs methDefs =
  ExistT __ (Build_pcADT (\idx ->
    getcConsDef n consSigs consDefs (unsafeCoerce idx)) (\idx ->
    getcMethDef n' methSigs methDefs (unsafeCoerce idx)))

callcADTMethod :: DecoratedADTSig -> DecoratedcADT -> ((BoundedIndex 
                  String) -> MethodIndex) -> (BoundedIndex String) ->
                  CMethodType CRep
callcADTMethod dSig adt idxMap idx =
  cMethods (decADTSig dSig) adt (idxMap idx)

scenarioIncl :: (List Scenario) -> (List Scenario) -> Bool
scenarioIncl l1 l2 =
  case l1 of {
   Nil -> True;
   Cons sce l1' ->
    case inList scenario_dec sce l2 of {
     True -> scenarioIncl l1' l2;
     False -> False}}

checkFinal :: Monitor -> Configuration -> Bool
checkFinal m conf =
  case eqb0 (length (raisedevents m conf)) O of {
   True -> True;
   False ->
    scenarioIncl (dom (controlstate m conf)) (finishedscenarios m conf)}

finalConfig_dec :: Monitor -> Configuration -> Sumbool
finalConfig_dec m conf' =
  let {b = checkFinal m conf'} in case b of {
                                   True -> Left;
                                   False -> Right}

trySync :: Monitor -> Configuration -> (List RaisedEvent) -> Option
           Configuration
trySync m conf lst =
  case lst of {
   Nil -> None;
   Cons e _ -> combineFunc e m conf}

syncStep :: Monitor -> Configuration -> Option Configuration
syncStep m conf =
  trySync m conf (raisedevents m conf)

macroNStep :: Monitor -> Configuration -> Nat -> Sumbool -> Option
              Configuration
macroNStep m conf n p =
  case p of {
   Left -> Some conf;
   Right ->
    case n of {
     O -> Some conf;
     S n' ->
      let {conf' = syncStep m conf} in
      case conf' of {
       Some conf'' -> macroNStep m conf'' n' (finalConfig_dec m conf'');
       None -> None}}}

configTransitionFunc :: Monitor -> Configuration -> RaisedEvent ->
                        Configuration
configTransitionFunc m conf e =
  Build_configuration (datastate m conf) (controlstate m conf) (Cons e
    (raisedevents m conf)) (exportedevents m conf) (finishedscenarios m conf)
    (sceEventMap m conf)

toReadyFunc :: Monitor -> Configuration -> Prod Configuration
               (List RaisedEvent)
toReadyFunc m conf =
  Pair (Build_configuration (datastate m conf) (controlstate m conf) Nil Nil
    Nil Nil) (exportedevents m conf)

macroStepReadyFinal' :: Monitor -> Configuration -> RaisedEvent -> Nat ->
                        Option (Prod Configuration (List RaisedEvent))
macroStepReadyFinal' m conf e n =
  let {conf' = configTransitionFunc m conf e} in
  case macroNStep m conf' n (finalConfig_dec m conf') of {
   Some conf'' -> Some (toReadyFunc m conf'');
   None -> None}

macroStepReadyFinal :: Monitor -> Configuration -> RaisedEvent -> Nat -> Prod
                       Configuration (List RaisedEvent)
macroStepReadyFinal m conf e n =
  let {filtered_var = macroStepReadyFinal' m conf e n} in
  case filtered_var of {
   Some p -> case p of {
              Pair conf''' eList -> Pair conf''' eList};
   None -> false_rect}

newS :: String
newS =
  String0 (Ascii False True True True False True True False) (String0 (Ascii
    True False True False False True True False) (String0 (Ascii True True
    True False True True True False) EmptyString))

processEventS :: String
processEventS =
  String0 (Ascii False False False False True True True False) (String0
    (Ascii False True False False True True True False) (String0 (Ascii True
    True True True False True True False) (String0 (Ascii True True False
    False False True True False) (String0 (Ascii True False True False False
    True True False) (String0 (Ascii True True False False True True True
    False) (String0 (Ascii True True False False True True True False)
    (String0 (Ascii True False True False False False True False) (String0
    (Ascii False True True False True True True False) (String0 (Ascii True
    False True False False True True False) (String0 (Ascii False True True
    True False True True False) (String0 (Ascii False False True False True
    True True False) EmptyString)))))))))))

program :: Object -> Configuration -> DecoratedcADT
program m initial_conf =
  buildcADT (S O) (S O) (Cons0 (Build_consSig newS Nil) O Nil0) (Cons0
    (Build_methSig processEventS (Cons __ Nil) (Some __)) O Nil0)
    (unsafeCoerce icons (Build_consSig newS Nil) O Nil0 initial_conf inil)
    (unsafeCoerce icons (Build_methSig processEventS (Cons __ Nil) (Some __))
      O Nil0 (\s ->
      unsafeCoerce (\s0 -> Pair
        (fst
          (macroStepReadyFinal m (proj1_sig s) (proj1_sig s0)
            (length (dom (controlstate m (proj1_sig s))))))
        (snd
          (macroStepReadyFinal m (proj1_sig s) (proj1_sig s0)
            (length (dom (controlstate m (proj1_sig s)))))))) inil)

monitor_new :: Object -> Configuration -> CRep
monitor_new _ initial_conf =
  unsafeCoerce initial_conf

monitor_processEvent :: Object -> Configuration -> CRep -> RaisedEvent ->
                        Prod CRep (List RaisedEvent)
monitor_processEvent m initial_conf r e =
  unsafeCoerce callcADTMethod
    (buildADTSig (S O) (S O) (Cons0 (Build_consSig newS Nil) O Nil0) (Cons0
      (Build_methSig processEventS (Cons __ Nil) (Some __)) O Nil0))
    (program m initial_conf) (\processEventS0 ->
    unsafeCoerce ibound (S O)
      (bindex (S O) (Cons1 processEventS O Nil1) processEventS0) (Cons1
      processEventS O Nil1)
      (indexb (S O) (Cons1 processEventS O Nil1) processEventS0))
    (Build_BoundedIndex processEventS (F1 O)) r e


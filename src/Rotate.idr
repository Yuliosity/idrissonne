module Rotate

%access public export
%default total

||| A class of types which can be rotated by 90 degrees clockwise.
interface Rotate a where
    rotate : a -> a
    --TODO: rotateN : Nat -> a -> a with cyclic : rotateN 4 e = e
    cyclic : (e : a) -> rotate (rotate (rotate (rotate e))) = e

Rotate a => Rotate (List a) where
    rotate Nil = Nil
    rotate (x :: xs) = rotate x :: rotate xs
    cyclic Nil = Refl
    cyclic (x :: xs) with (cyclic xs)
        | ih = rewrite sym (cyclic x) in cong ih

(Rotate a, Rotate b) => Rotate (a, b) where
    rotate (a, b) = (rotate a, rotate b)
    cyclic (a, b) = rewrite cyclic a in rewrite cyclic b in Refl

record Vec a where
    constructor V
    px : a
    py : a

doubleNegateRefl : (Neg t) => (x : t) -> negate (negate x) = x
doubleNegateRefl x = believe_me x

Neg a => Rotate (Vec a) where
    rotate (V a b) = V b (negate a)
    cyclic (V a b) = rewrite doubleNegateRefl a in
                     rewrite doubleNegateRefl b in
                     Refl

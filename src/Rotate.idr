module Rotate

%default total

||| A class of types which can be rotated by 90 degrees clockwise.
class Rotate a where
    rotate : a -> a
    --TODO: rotateN : Nat -> a -> a with cyclic : rotateN 4 e = e
    cyclic : (e : a) -> rotate (rotate (rotate (rotate e))) = e
    
instance Rotate a => Rotate (List a) where
    rotate Nil = Nil
    rotate (x :: xs) = rotate x :: rotate xs
    cyclic Nil = refl
    cyclic (x :: xs) with (cyclic xs)
        | ih = rewrite sym (cyclic x) in cong ih 
        
instance (Rotate a, Rotate b) => Rotate (a, b) where
    rotate (a, b) = (rotate a, rotate b)
    cyclic (a, b) = ?pairCyclic

record Vec : Type -> Type where
    V : Num a => (px : a) -> (py : a) -> Vec a
            
instance (Num a) => Rotate (Vec a) where
    rotate (V a b) = V b (-a)
    cyclic (V a b) = ?improvable

pairCyclic = proof
  intros
  rewrite sym (cyclic a)
  rewrite sym (cyclic b)
  trivial

module Logic

import Data.SortedMap

||| A player
record Player : Type where
    MkPlayer : (name : String)
            -> Player

%elim
data Edge = Top | Right | Bottom | Left
                        
data CityMark = N | Pennant

||| A region of the tile where a follower can be placed.
%elim data Region
    = Cloister
    | City CityMark (List Edge)
    | Farm (List Edge)
    | Road (List Edge)

data CellPoint : Type where
    CP : (Float, Float) -> CellPoint

||| A tile data type which encapsulates the logic tile.
record Tile : Type where
    MkTile : (regions : List (CellPoint, Region))
          -> Tile

||| A class of types which can be rotated by 90 degrees clockwise.
class Rotate a where
    rotate : a -> a
    cyclic : (e : a) -> rotate (rotate (rotate (rotate e))) = e
    
instance Rotate Edge where
    rotate Top = Right
    rotate Right = Bottom
    rotate Bottom = Left
    rotate Left = Top
    cyclic e = ?edgeCyclic
    
instance Rotate CellPoint where
    rotate (CP (x, y)) = CP (y, -x)
    cyclic (CP (x, y)) = ?cpCyclic --Can't prove

instance Rotate a => Rotate (List a) where
    rotate Nil = Nil
    rotate (x :: xs) = rotate x :: rotate xs
    cyclic Nil = refl
    cyclic (x :: xs) with (cyclic xs)
        | ih = rewrite sym (cyclic x) in cong ih    
            
instance Rotate Region where
    rotate Cloister = Cloister
    rotate (Road borders) = Road (rotate borders)
    rotate (City m borders) = City m (rotate borders)
    rotate (Farm borders) = Farm (rotate borders)
    cyclic Cloister = refl
    cyclic (Road borders) = rewrite sym (cyclic borders) in refl
    cyclic (City m borders) = rewrite sym (cyclic borders) in refl
    cyclic (Farm borders) = rewrite sym (cyclic borders) in refl

instance (Rotate a, Rotate b) => Rotate (a, b) where
    rotate (a, b) = (rotate a, rotate b)
    cyclic (a, b) = ?pairCyclic

instance Rotate Tile where
    rotate (MkTile regions) = MkTile (rotate regions)
    cyclic (MkTile regions) = rewrite sym (cyclic regions) in refl
    
data DepVect : Nat -> Type -> Type where
    Nil  : DepVect 0 a
    (::) : (a ** b) -> DepVect n a -> DepVect (S n) a

v : Player
v = MkPlayer "Vasya"

p : Player
p = MkPlayer "Petya"

||| A data type for followers.
data Follower : Player -> Type where
    MkFollower : (p : Player) -> Follower p

test : DepVect 2 Player
test = (v ** MkFollower v) :: (p ** MkFollower p) :: Nil

||| A cell of the field.
Cell : Type
Cell = (Int, Int) 
   
||| A field of tiles.
record Field : Type where
    MkField : (tiles : SortedMap Cell Tile)
           -> Field

||| A type for holding the game state.
record LogicState : Type where
    LS : (field : Field)
      -> (box : List Tile)
      -> LogicState

---------- Proofs ----------
Logic.pairCyclic = proof
  intros
  rewrite sym (cyclic {e = a})
  rewrite sym (cyclic {e = b})
  trivial



Logic.edgeCyclic = proof
  intros
  case e
  compute
  trivial
  compute
  trivial
  compute
  trivial
  compute
  trivial


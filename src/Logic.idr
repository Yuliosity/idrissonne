module Logic

import Data.SortedMap
import Rotate

||| A player
record Player : Type where
    MkPlayer : (name : String)
            -> Player

%elim
data Edge = Top | Right | Bottom | Left

instance Rotate Edge where
    rotate Top = Right
    rotate Right = Bottom
    rotate Bottom = Left
    rotate Left = Top
    cyclic e = ?edgeCyclic                        
                                                                        
data CityMark = N | Pennant

||| A region of the tile where a follower can be placed.
%elim data Region
    = Cloister
    | City CityMark (List Edge)
    | Farm (List Edge)
    | Road (List Edge)
    
instance Rotate Region where
    rotate Cloister = Cloister
    rotate (Road borders) = Road (rotate borders)
    rotate (City m borders) = City m (rotate borders)
    rotate (Farm borders) = Farm (rotate borders)
    cyclic Cloister = refl
    cyclic (Road borders) = rewrite sym (cyclic borders) in refl
    cyclic (City m borders) = rewrite sym (cyclic borders) in refl
    cyclic (Farm borders) = rewrite sym (cyclic borders) in refl

--fullBorder : List Region -> Bool
--f

||| An arbitrary point
Point : Type
Point = Vec Float

||| A tile data type which encapsulates the logic tile.
record Tile : Type where
    MkTile : (regions : List (Point, Region))
          -> Tile

instance Rotate Tile where
    rotate (MkTile regions) = MkTile (rotate regions)
    cyclic (MkTile regions) = rewrite sym (cyclic regions) in refl
    


||| A data type for followers.
data Follower : Player -> Type where
    MkFollower : (p : Player) -> Follower p

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

Logic.edgeCyclic = proof
  intro
  case e
  trivial
  trivial
  trivial
  trivial

----------------------------

member : Ord k => k -> SortedMap k v -> Bool
member k m = case lookup k m of
    Nothing => False
    Just _  => True

||| Check if a tile can be placed on the field cell.
-- TODO: refactor
private edgeOffset : Edge -> ((Int, Int), Edge)
edgeOffset Top    = (( 0, -1), Bottom)
edgeOffset Right  = (( 1,  0), Left)
edgeOffset Bottom = (( 0,  1), Top)
edgeOffset Left   = ((-1,  0), Right)

matchTiles : Cell -> Tile -> Field -> Bool
matchTiles c t f = ?mt

data CanBePlaced : Cell -> Tile -> Field -> Type where
    canBePlaced : (c : Cell) -> (t : Tile) -> (f : Field) -> so (not $ member c (tiles f) && matchTiles c t f) -> CanBePlaced c t f

||| Place a new tile in the empty cell of the field.
placeTile : (c : Cell) -> (t : Tile) -> (f : Field) -> CanBePlaced c t f -> Field
placeTile cell tile field p =
    record {tiles = insert cell tile (tiles field)} field

module Logic

import Data.Bits
import Data.So
import Data.SortedMap

import Rotate

||| A player
record Player where
    constructor MkPlayer
    name : String

data Edge = Top | Right | Bottom | Left

Rotate Edge where
    rotate Top = Right
    rotate Right = Bottom
    rotate Bottom = Left
    rotate Left = Top
    cyclic Top = Refl
    cyclic Right = Refl
    cyclic Bottom = Refl
    cyclic Left = Refl

||| Bit mask representing the edge or its half.
data BEdge = BE Bits8

top : BEdge
top = BE 3

right : BEdge
right = BE 12

bottom : BEdge
bottom = BE 48

left : BEdge
left = BE 192

Rotate BEdge where
    rotate (BE b) = BE ((b `prim__lshrB8` 2) `prim__orB8` (b `prim__shlB8` 6))
    cyclic (BE b) = believe_me b

data CityMark = N | Pennant

||| A region of the tile where a follower can be placed.
data Region
    = Cloister
    | City CityMark (List BEdge)
    | Farm (List BEdge)
    | Road (List BEdge)

borders : Region -> List BEdge
borders Cloister = []
borders (City _ b) = b
borders (Farm b) = b
borders (Road b) = b

Rotate Region where
    rotate Cloister = Cloister
    rotate (Road borders) = Road (rotate borders)
    rotate (City m borders) = City m (rotate borders)
    rotate (Farm borders) = Farm (rotate borders)
    cyclic Cloister = Refl
    cyclic (Road borders) = rewrite sym (cyclic borders) in Refl
    cyclic (City m borders) = rewrite sym (cyclic borders) in Refl
    cyclic (Farm borders) = rewrite sym (cyclic borders) in Refl

fullBorder : List BEdge -> Bool
fullBorder rs = go 0 rs where
    go : Bits8 -> List BEdge -> Bool
    go acc [] = acc == 255
    go acc ((BE r) :: rs) =
        if 0 == (acc `prim__andB8` r)
            then go (acc `prim__orB8` r) rs
            else False

rotateFullBorder : (xs : List BEdge) -> So (fullBorder xs) -> So (fullBorder (rotate xs))
rotateFullBorder xs = ?rfb

rotateRegions : (xs : List Region) -> So (fullBorder $ concatMap Logic.borders xs) ->
                So (fullBorder $ concatMap Logic.borders (map rotate xs))
rotateRegions xs = ?rr

||| A tile data type which encapsulates the logic tile.
record Tile where
    constructor MkTile
    regions : List Region
    isFullBorder : So (fullBorder $ concatMap Logic.borders regions)

Rotate Tile where
    rotate (MkTile rs p) = MkTile (rotate rs) ?mkr
    cyclic (MkTile rs p) = ?ct

||| A data type for followers.
record Follower where
    constructor MkFollower
    owner : Player

||| A cell of the field.
Cell : Type
Cell = (Int, Int)

||| A field of tiles.
record Field where
    constructor MkField
    tiles : SortedMap Cell Tile
    --

||| A type for holding the game state.
record LogicState where
    constructor LS
    field : Field
    box : List Tile

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

--private binEdgeOffset : BEdge -> ((Int, Int), Edge)
--binEdgeOffset =

matchTiles : Cell -> Tile -> Field -> Bool
matchTiles c t f = ?mt

data CanBePlaced : Cell -> Tile -> Field -> Type where
    CBP : (c : Cell) -> (t : Tile) -> (f : Field) -> So (not $ member c (tiles f) && matchTiles c t f) -> CanBePlaced c t f

||| Place a new tile in the empty cell of the field.
placeTile : (c : Cell) -> (t : Tile) -> (f : Field) -> CanBePlaced c t f -> Field
placeTile cell tile field p =
    record {tiles = insert cell tile (tiles field)} field

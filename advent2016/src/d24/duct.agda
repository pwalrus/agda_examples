module d24.duct where

open import util.list_stuff using (words ; lines ; unmaybe ; hard-unmaybe ; filterᵇ ; make-perms ; rem-dot ; append-front-all ; all-replacements ; cartproduct ; min-by-f ; enumerate ; list-minus) renaming (trim to trim-ch)
open import util.lookup using (LookupStrTree ; LookupNatTree ; build-str-tree ; build-nat-tree ; has-val ; all-values ; all-keys ; all-kv ; LTPair) renaming (set-val to set-tree ; read-val to read-tree)
open import util.json using (readIntMaybe)
open import util.search using (search-rec-breadth-dedup ; branch-bound)
open import Data.Tree.Binary using (leaf ; node)
open import Agda.Builtin.String using (String)
open import Data.String.Base using (toList ; fromList ; _++_ ; unlines ; intersperse)
open import Data.String.Properties using (_==_ ; _<?_)
open import Agda.Builtin.Nat using (Nat ; suc ; _<_ ; _+_ ; _-_ ; _*_ ; div-helper ; mod-helper) renaming (_==_ to _==n_)
open import Data.Nat.Base using (pred)
open import Data.Nat.Show using (show ; readMaybe)
open import Agda.Builtin.Int using (Int ; pos ; negsuc)
open import Data.Integer.Base using () renaming (_+_ to _+z_ ; _-_ to _-z_)
open import Data.Integer.Show using () renaming (show to show-z)
open import Data.Integer.Properties using (_≟_)
open import Agda.Builtin.List using (List ; [] ; _∷_)
open import Data.List using (map ; foldr ; concat ; length ; zip ; reverse ; head ; cartesianProductWith ; applyUpTo)
open import Agda.Builtin.Char using (Char)
open import Data.Char.Properties using () renaming (_==_ to _==c_)
open import Agda.Builtin.Bool using (Bool ; true ; false)
open import Data.Bool.Base using (if_then_else_ ; _∧_ ; _∨_ ; not)
open import Agda.Builtin.Maybe using (Maybe ; nothing ; just)
open import Data.Maybe using (fromMaybe)
open import Function using (_∘_ ; id)
open import Data.Product using (_×_ ; _,_ ; proj₁ ; proj₂ ; map₂)
open import Agda.Builtin.Equality using (refl ; _≡_)
open import Relation.Nullary.Decidable using (isYes)

data WallDet : Set where
  wall : WallDet
  floor : WallDet
  loc : Nat → WallDet

is-loc : WallDet → Bool
is-loc (loc _) = true
is-loc _ = false

is-wall : WallDet → Bool
is-wall wall = true
is-wall _ = false

record Maze : Set where
  constructor maze
  field
    walls : LookupNatTree (LookupNatTree WallDet)

read-maze : Maze → (Nat × Nat) → Maybe WallDet
read-maze (maze db) (x , y) with (read-tree x db)
read-maze (maze db) (x , y) | (just row) = read-tree y row
read-maze (maze db) (x , y) | _ = nothing

passable : Maze → (Nat × Nat) → Bool
passable mz p1 with (read-maze mz p1)
passable mz p1 | nothing = false
passable mz p1 | (just det) = not (is-wall det)

trim : String → String
trim = fromList ∘ trim-ch ∘ toList

ch-to-det : Char → WallDet
ch-to-det '.' = floor
ch-to-det x with (readMaybe 10 (fromList (x ∷ [])))
ch-to-det x | (just n) = loc n
ch-to-det x | _ = wall

det-to-str : WallDet → String
det-to-str floor = "."
det-to-str wall = "#"
det-to-str (loc n) = show n

parse-row : String → LookupNatTree WallDet
parse-row = build-nat-tree ∘ enumerate ∘ map ch-to-det ∘ toList

parse-maze : String → Maze
parse-maze = maze ∘ build-nat-tree ∘ enumerate ∘ map parse-row ∘ lines ∘ trim

show-row : LookupNatTree WallDet → String
show-row = intersperse "" ∘ reverse ∘  map det-to-str ∘ map proj₂ ∘ all-kv 

show-maze : Maze → String
show-maze (maze db) = (unlines ∘ reverse ∘ map show-row ∘ map proj₂ ∘ all-kv) db

mk-coord : {A : Set} → Nat × (List (Nat × A)) → List (A × (Nat × Nat))
mk-coord (x , xs) = map (λ {(y , q) → q , (x , y)}) xs

invert-coord : {A : Set} → List (Nat × (List (Nat × A))) → List (A × (Nat × Nat))
invert-coord = concat ∘ map mk-coord

list-locs : Maze → List (WallDet × (Nat × Nat))
list-locs (maze db) = (filterᵇ (is-loc ∘ proj₁) ∘ invert-coord ∘ map (map₂ all-kv) ∘ all-kv) db

record Path : Set where
  constructor path
  field
    end : (Nat × Nat)
    hist : List Char

path-passable : Maze → Path → Bool
path-passable mz (path p1 _) = passable mz p1

show-path-anon : Path → String
show-path-anon (path (x , y) _) = show x ++ "," ++ show y

eq-np : (Nat × Nat) → (Nat × Nat) → Bool
eq-np (x1 , y1) (x2 , y2) = (x1 ==n x2) ∧ (y1 ==n y2)

is-done : (Nat × Nat) → Path → Bool
is-done p1 (path p2 _) = eq-np p1 p2

move-path : Path → Char → Path
move-path (path (x , y) hist) 'U' = (path (x , suc y) ('U' ∷ hist))
move-path (path (x , y) hist) 'D' = (path (x , pred y) ('D' ∷ hist))
move-path (path (x , y) hist) 'L' = (path (pred x , y) ('L' ∷ hist))
move-path (path (x , y) hist) 'R' = (path (suc x , y) ('R' ∷ hist))
move-path (path (x , y) hist) _ = (path (x , y) hist)

next-paths : Maze → Path → List Path
next-paths db p1 = filterᵇ (path-passable db) ((move-path p1 'U') ∷ (move-path p1 'L') ∷ (move-path p1 'R') ∷ (move-path p1 'D') ∷ [])

max-dist : Nat
max-dist = 1000000

min-dist-between : Maze → (Nat × Nat) → (Nat × Nat) → Nat
min-dist-between db p1 p2 = output
  where
    short-path : Maybe Path × LookupStrTree Bool
    short-path = search-rec-breadth-dedup 100000000 show-path-anon (is-done p2) (next-paths db) ((path p1 []) ∷ [])
    output : Nat
    output with (proj₁ short-path)
    output | (just p) = (length ∘ Path.hist) p
    output | _ = max-dist

nid : Nat × Nat → Nat
nid (x , y) = 1000 * x + y

record DistMtx : Set where
  constructor dmtx
  field
    mtx : LookupNatTree Nat

dist-pairify : Maze → WallDet × (Nat × Nat) → WallDet × (Nat × Nat) → Nat × Nat
dist-pairify mz (loc a , pa) (loc b , pb) = (nid (a , b)) , min-dist-between mz pa pb
dist-pairify mz _ _ = 0 , 0

mk-dist-mtx : Maze → DistMtx
mk-dist-mtx mz = dmtx (build-nat-tree pairs)
  where
    locs : List (WallDet × (Nat × Nat))
    locs = list-locs mz
    pairs : List (Nat × Nat)
    pairs = cartesianProductWith (dist-pairify mz) locs locs


read-dist : DistMtx → Nat → Nat → Nat
read-dist (dmtx tree) x y with (read-tree (nid (x , y)) tree)
read-dist (dmtx tree) x y | nothing = max-dist
read-dist (dmtx tree) x y | (just d) = d

done-perm : Nat → List Nat → Bool
done-perm mx xs = length xs ==n mx

eval-perm : DistMtx → List Nat → Nat
eval-perm dm [] = 0
eval-perm dm (x ∷ []) = 0
eval-perm dm (x ∷ y ∷ xs) = (read-dist dm x y)  + eval-perm dm (y ∷ xs)

eval-perm-back : DistMtx → List Nat → Nat
eval-perm-back dm xs with (done-perm 8 xs)
eval-perm-back dm xs | true = eval-perm dm (0 ∷ xs)
eval-perm-back dm xs | false = eval-perm dm xs

mk-perms : Nat → List Nat → List (List Nat)
mk-perms mx xs = map (λ {q → q ∷ xs}) remaining
  where
    remaining : List Nat
    remaining = list-minus _==n_ (applyUpTo id mx) xs

show-best-pair : Nat × List Nat → String
show-best-pair (s , xs) = "score: " ++ show s ++ ", on: " ++ (intersperse "," ∘ map show) xs 

search-shortest-path : Maze → Maybe (Nat × List Nat)
search-shortest-path mz = branch-bound 100000000 init-best (done-perm sz) (eval-perm dm) (mk-perms sz) ((0 ∷ []) ∷ [])
  where
    dm : DistMtx
    dm = mk-dist-mtx mz
    locs : List (WallDet × (Nat × Nat))
    locs = list-locs mz
    sz : Nat
    sz = length locs
    init-best : Nat × List Nat
    init-best = eval-perm dm (applyUpTo id sz) , (applyUpTo id sz)

find-shortest-path : String → String
find-shortest-path x = output ++ "\n"
  where
    mz : Maze
    mz = parse-maze x
    output : String
    output with (search-shortest-path mz)
    output | nothing = "no path found"
    output | (just bp) = show-best-pair bp

test-maze : String
test-maze = (
  "###########\n" ++
  "#0.1.....2#\n" ++
  "#.#######.#\n" ++
  "#4.......3#\n" ++
  "###########")

test-parse-maze : show-maze (parse-maze test-maze) ≡ test-maze
test-parse-maze = refl

test-list-locs : (head ∘ list-locs ∘ parse-maze) test-maze ≡ just (loc 3 , (3 , 9))
test-list-locs = refl

test-min-dist-a : min-dist-between (parse-maze test-maze) (1 , 1) (1 , 3) ≡ 2
test-min-dist-a = refl

test-min-dist-b : min-dist-between (parse-maze test-maze) (1 , 1) (3 , 9) ≡ 10
test-min-dist-b = refl

test-min-dist-c : min-dist-between (parse-maze test-maze) (3 , 1) (1 , 3) ≡ 4
test-min-dist-c = refl

test-eval-perm : eval-perm (mk-dist-mtx (parse-maze test-maze)) (3 ∷ 2 ∷ 1 ∷ 4 ∷ 0 ∷ []) ≡ 14
test-eval-perm = refl

test-search-shortest : search-shortest-path (parse-maze test-maze) ≡ just (14 , 3 ∷ 2 ∷ 1 ∷ 4 ∷ 0 ∷ [])
test-search-shortest = refl

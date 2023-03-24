module d13.maze where

open import util.list_stuff using (words ; lines ; unmaybe ; hard-unmaybe ; filterᵇ ; each-one ; make-perms ; rem-dot ; append-front-all ; all-replacements ; cartproduct ; min-by-f ; enumerate ; split ; empty-table ; show-table ; transpose ; eq-classes ; rem-match ; partitionᵇ ; deduplicateᵇ ; index-of) renaming (trim to trim-ch)
open import util.lookup using (str-lt ; quick-sort ; LookupStrTree) renaming (all-kv to all-str-kv)
open import util.lookup_nat using (LookupNatTree ; build-nat-tree ; has-val ; all-kv) renaming (set-val to set-tree ; read-val to read-tree ; rem-val to rem-tree)
open import util.json using (readIntMaybe ; rem-lst-c)
open import util.search using (search-rec-breadth-dedup)
open import Data.Tree.Binary using (leaf ; node)
open import Agda.Builtin.String using (String)
open import Data.String.Base using (toList ; fromList ; _++_ ; unlines ; unwords ; intersperse ; fromChar ; padRight)
open import Data.String.Properties using (_==_)
open import Agda.Builtin.Nat using (Nat ; suc ; _<_ ; _+_ ; _-_ ; _*_ ; div-helper ; mod-helper) renaming (_==_ to _==n_)
open import Data.Nat.Base using (pred)
open import Data.Nat.Show using (show ; readMaybe ; showInBase)
open import Agda.Builtin.Int using (Int ; pos ; negsuc)
open import Data.Integer.Base using (_≤ᵇ_) renaming (_+_ to _+z_ ; _-_ to _-z_)
open import Data.Integer.Properties using (_≟_)
open import Data.Integer.Show using () renaming (show to showz)
open import Agda.Builtin.List using (List ; [] ; _∷_)
open import Data.List using (map ; foldr ; concat ; length ; zip ; take ; drop ; head ; last; tail ; any ; all ; cartesianProductWith ; applyUpTo ; scanr ; reverse)
open import Agda.Builtin.Char using (Char ; primCharToNat ; primNatToChar)
open import Data.Char.Properties renaming (_==_ to _==c_ ; _<?_ to _<c_)
open import Agda.Builtin.Bool using (Bool ; true ; false)
open import Data.Bool.Base using (if_then_else_ ; _∧_ ; _∨_ ; not)
open import Agda.Builtin.Maybe using (Maybe ; nothing ; just)
open import Data.Maybe using (fromMaybe)
open import Function.Base using (_∘_)
open import Data.Product using (_×_ ; _,_ ; proj₁ ; proj₂)
open import Agda.Builtin.Equality using (refl ; _≡_)
open import Relation.Nullary.Decidable using (isYes)


record PartialP : Set where
  constructor parp
  field
    loc : Nat × Nat
    hist : List String

start-loc : PartialP
start-loc = parp (1 , 1) []

div-nat : Nat → Nat → Nat
div-nat x y = div-helper 0 (pred y) x (pred y)

mod-nat : Nat → Nat → Nat
mod-nat x y = mod-helper 0 (pred y) x (pred y)

count-bits-h : Nat → Nat → Nat
count-bits-h 0 _ = 0
count-bits-h _ 0 = 0
count-bits-h _ 1 = 1
count-bits-h _ 2 = 1
count-bits-h (suc lm) x = if (mod-nat x 2 ==n 0) then next else suc next
  where
    next : Nat
    next = count-bits-h lm (div-nat x 2)

count-bits : Nat → Nat
count-bits x = count-bits-h x x

is-wall : Nat → (Nat × Nat) → Bool
is-wall magic (x , y) = mod-nat (count-bits poly) 2 ==n 1
  where
    poly : Nat
    poly = (x * x + 3 * x + 2 * x * y + y + y * y) + magic

is-wall-p : Nat → PartialP → Bool
is-wall-p magic (parp (x , y) _) = is-wall magic (x , y)

local-repeat : PartialP → Bool
local-repeat (parp _ []) = false
local-repeat (parp _ (_ ∷ [])) = false
local-repeat (parp _ ("U" ∷ "D" ∷ _)) = true
local-repeat (parp _ ("D" ∷ "U" ∷ _)) = true
local-repeat (parp _ ("L" ∷ "R" ∷ _)) = true
local-repeat (parp _ ("R" ∷ "L" ∷ _)) = true
local-repeat (parp _ _) = false

length-limit : PartialP → Bool
length-limit (parp _ xs) = length xs < 51

show-wall : Nat → Nat → String
show-wall magic lm = unlines rows
  where
    rng : List Nat
    rng = applyUpTo (λ {q → q}) lm
    grid : List (List (Nat × Nat))
    grid = map (λ {q → applyUpTo (λ {r → (q , r)}) lm}) rng
    rows : List String
    rows = map(fromList ∘ map (λ {(x , y) → if (is-wall magic (x , y)) then '#' else 'x'})) grid

next-moves : Nat → PartialP → List PartialP
next-moves magic (parp (x , y) xs) = (filterᵇ length-limit ∘ filterᵇ (not ∘ local-repeat) ∘ filterᵇ (not ∘ is-wall-p magic) ∘ concat) (left ∷ right ∷ up ∷ down ∷ [])
  where
    left : List PartialP
    left with (x ==n 0)
    left | true = []
    left | false = (parp (pred x , y) ("L" ∷ xs)) ∷ []
    up : List PartialP
    up with (y ==n 0)
    up | true = []
    up | false = (parp (x , pred y) ("U" ∷ xs)) ∷ []
    right : List PartialP
    right = (parp (suc x , y) ("R" ∷ xs)) ∷ []
    down : List PartialP
    down = (parp (x , suc y) ("D" ∷ xs)) ∷ []

is-done : (Nat × Nat) → PartialP → Bool
is-done (tx , ty) (parp (x , y) xs) = (tx ==n x) ∧ (ty ==n y)

show-path-anon : PartialP → String
show-path-anon (parp (x , y) xs) = "(" ++ show x ++ "," ++ show y ++ ")" 

show-path : PartialP → String
show-path (parp (x , y) xs) = show-path-anon (parp (x , y) xs) ++ "\n" ++ "length: " ++ show (length xs) ++ "\n" ++ intersperse "," xs

find-shortest-maze : String → String
find-shortest-maze x = "sol: " ++ output ++ "\n" ++ "visited: " ++ show (length visited) ++ "\n" ++ intersperse "," visited ++ "\n"
  where
    wds : List String
    wds = words x
    magic : Nat
    magic = (fromMaybe 10 ∘ (readMaybe 10) ∘ fromList ∘ trim-ch ∘ toList ∘ fromMaybe "" ∘ head) wds
    tx : Nat
    tx = (fromMaybe 10 ∘ (readMaybe 10) ∘ fromList ∘ trim-ch ∘ toList ∘ fromMaybe "" ∘ head ∘ drop 1) wds
    ty : Nat
    ty = (fromMaybe 10 ∘ (readMaybe 10) ∘ fromList ∘ trim-ch ∘ toList ∘ fromMaybe "" ∘ head ∘ drop 2) wds
    path : Maybe PartialP × LookupStrTree Bool
    path = search-rec-breadth-dedup 100000000 show-path-anon (is-done (tx , ty)) (next-moves magic) (start-loc ∷ [])
    output : String
    output with (proj₁ path)
    output | nothing = "no path found for " ++ show magic ++ " " ++ show tx ++ "," ++ show ty
    output | (just (parp (x , y) xs)) = show-path (parp (x , y) xs)
    visited : List String
    visited = (filterᵇ (λ { q → not (q == "") }) ∘ map proj₁ ∘ all-str-kv ∘ proj₂) path

test-count-bits : count-bits 1 ≡ 1
test-count-bits = refl

test-count-bits-a : count-bits 5 ≡ 2
test-count-bits-a = refl

test-is-wall-a : is-wall 10 (1 , 0) ≡ true
test-is-wall-a = refl

test-is-wall-b : is-wall-p 10 (parp (1 , 1) ("D" ∷ "R" ∷ [])) ≡ false
test-is-wall-b = refl

test-next-moves-a : next-moves 10 start-loc ≡ (parp (0 , 1) ("L" ∷ [])) ∷ (parp (1 , 2) ("D" ∷ [])) ∷ []
test-next-moves-a = refl

test-next-moves-b : next-moves 10 (parp (1 , 2) ("D" ∷ [])) ≡ (parp (2 , 2) ("R" ∷ "D" ∷ [])) ∷ []
test-next-moves-b = refl

test-is-wall-show : show-wall 10 10 ≡
  "xx##xx#x##\n" ++
  "#xx##xx#x#\n" ++
  "x#x###x###\n" ++
  "#xxxx#xx#x\n" ++
  "#xx#xx#x##\n" ++
  "###x#x##x#\n" ++
  "#x##xxxxx#\n" ++
  "xxx#xx##x#\n" ++
  "#xx#####xx\n" ++
  "##xxxx#x##"
test-is-wall-show = refl

test-find-shortest-maze : find-shortest-maze "10 7 4" ≡
  "sol: (7,4)\n" ++
  "length: 11\n" ++
  "U,R,R,R,D,R,D,D,R,R,D\n" ++
  "visited: 18\n" ++
  "(7,5),(6,6),(6,5),(6,4),(5,5),(4,5),(4,4),(4,2),(4,1),(3,4),(3,3),(3,2),(3,1),(2,2),(1,2),(1,1),(0,1),(0,0)\n"
test-find-shortest-maze = refl

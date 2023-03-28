
module d17.maze where

open import util.list_stuff using (words ; lines ; unmaybe ; hard-unmaybe ; filterᵇ ; each-one ; make-perms ; rem-dot ; append-front-all ; all-replacements ; cartproduct ; min-by-f ; enumerate ; split ; empty-table ; show-table ; transpose ; eq-classes ; rem-match ; partitionᵇ ; deduplicateᵇ ; index-of) renaming (trim to trim-ch)
open import util.lookup using (str-lt ; quick-sort ; LookupStrTree) renaming (all-kv to all-str-kv)
open import util.lookup_nat using (LookupNatTree ; build-nat-tree ; has-val ; all-kv) renaming (set-val to set-tree ; read-val to read-tree ; rem-val to rem-tree)
open import util.json using (readIntMaybe ; rem-lst-c)
open import util.search using (search-rec-breadth ; search-rec-all)
open import util.hash using (hash-md5)
open import util.nat_stuff using (mod-nat ; div-nat ; lin-mod-system)
open import Data.Tree.Binary using (leaf ; node)
open import Agda.Builtin.String using (String)
open import Data.String.Base using (toList ; fromList ; _++_ ; unlines ; unwords ; intersperse ; fromChar ; padRight)
open import Data.String.Properties using (_==_)
open import Agda.Builtin.Nat using (Nat ; suc ; _<_ ; _+_ ; _-_ ; _*_) renaming (_==_ to _==n_)
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
open import Function.Base using (_∘_ ; id ; const)
open import Data.Product using (_×_ ; _,_ ; proj₁ ; proj₂)
open import Agda.Builtin.Equality using (refl ; _≡_)
open import Relation.Nullary.Decidable using (isYes)


trim : String → String
trim = fromList ∘ trim-ch ∘ toList

record MPos : Set where
  constructor mpos
  field
    password : String
    current : Nat × Nat
    history : List Char

is-open : Char → Bool
is-open 'b' = true
is-open 'c' = true
is-open 'd' = true
is-open 'e' = true
is-open 'f' = true
is-open _ = false

is-up-open : String → Bool
is-up-open = is-open ∘ fromMaybe '0' ∘ head ∘ toList

is-down-open : String → Bool
is-down-open = is-open ∘ fromMaybe '0' ∘ head ∘ drop 1 ∘ toList

is-left-open : String → Bool
is-left-open = is-open ∘ fromMaybe '0' ∘ head ∘ drop 2 ∘ toList

is-right-open : String → Bool
is-right-open = is-open ∘ fromMaybe '0' ∘ head ∘ drop 3 ∘ toList

next-moves-str : String → MPos → List MPos
next-moves-str hash (mpos p (x , y) xs) = concat (left ∷ right ∷ up ∷ down ∷ [])
  where
    left : List MPos
    left = if (0 < x) ∧ (is-left-open hash) then ((mpos p (x - 1 , y) ('L' ∷ xs)) ∷ []) else []
    right : List MPos
    right = if (x < 3) ∧ (is-right-open hash) then ((mpos p (x + 1 , y) ('R' ∷ xs)) ∷ []) else []
    up : List MPos
    up = if (0 < y) ∧ (is-up-open hash) then ((mpos p (x , y - 1) ('U' ∷ xs)) ∷ []) else []
    down : List MPos
    down = if (y < 3) ∧ (is-down-open hash) then ((mpos p (x , y + 1) ('D' ∷ xs)) ∷ []) else []

next-moves : MPos → List MPos
next-moves (mpos p (x , y) xs) = next-moves-str hash (mpos p (x , y) xs)
  where
    hash : String
    hash = hash-md5 (p ++ (fromList ∘ reverse) xs)

is-done : MPos → Bool
is-done (mpos _ (3 , 3) _) = true
is-done _ = false

iter-over-maze : String → String
iter-over-maze x = "sol: " ++ output ++ "\n"
  where
    init : MPos
    init = mpos (trim x) (0 , 0) []
    final : Maybe MPos
    final = search-rec-breadth 10000000 is-done next-moves (init ∷ [])
    output : String
    output with (final)
    output | nothing = "no solution"
    output | (just mp) = (fromList ∘ reverse ∘ MPos.history) mp

l-of-2 : MPos → MPos → MPos
l-of-2 p1 p2 = if (length (MPos.history p1) < length (MPos.history p2))
  then p2
  else p1

longest : List MPos → MPos
longest = foldr l-of-2 (mpos "" (0 , 0) [])

iter-over-maze-longest : String → String
iter-over-maze-longest x = "sol: " ++ output ++ "\n"
  where
    init : MPos
    init = mpos (trim x) (0 , 0) []
    final : List MPos
    final = search-rec-all 10000000 is-done next-moves (init ∷ [])
    output : String
    output with (final)
    output | [] = "no solution"
    output | mp = (show ∘ length ∘ MPos.history ∘ longest) mp


test-next-move-a : next-moves-str "ced9..." (mpos "hijkl" (0 , 0) []) ≡ (mpos "hijkl" (0 , 1) ('D' ∷ [])) ∷ []
test-next-move-a = refl

test-next-move-b : next-moves-str "f2bc..." (mpos "hijkl" (0 , 1) ('D' ∷ [])) ≡ (mpos "hijkl" (1 , 1) ('R' ∷ 'D' ∷ [])) ∷ (mpos "hijkl" (0 , 0) ('U' ∷ 'D' ∷ [])) ∷ []
test-next-move-b = refl

test-next-move-c : next-moves-str "5745..." (mpos "hijkl" (1 , 1) ('R' ∷ 'D' ∷ [])) ≡ []
test-next-move-c = refl

test-next-move-d : next-moves-str "528e..." (mpos "hijkl" (0 , 0) ('U' ∷ 'D' ∷ [])) ≡ (mpos "hijkl" (1 , 0) ('R' ∷ 'U' ∷ 'D' ∷ [])) ∷ []
test-next-move-d = refl

-- cannot type check (hash-md5 relies on a postulate)
--test-iter-over-maze : iter-over-maze "ihgpwlah" ≡ "sol: DDRRRD\n"
--test-iter-over-maze = refl

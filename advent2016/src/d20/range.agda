
module d20.range where

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


max : Nat → Nat → Nat
max a b = if a < b then b else a

min : Nat → Nat → Nat
min a b = if a < b then a else b

record Range : Set where
  constructor rng
  field
    low : Nat
    high : Nat

show-rng : Range → String
show-rng (rng l1 r1) = show l1 ++ "-" ++ show r1

eq-rng : Range → Range → Bool
eq-rng (rng l1 r1) (rng l2 r2) = (l1 ==n l2) ∧ (r1 ==n r2)

lt-rng : Range → Range → Bool
lt-rng (rng l1 r1) (rng l2 r2) =
  if (eq-rng (rng l1 r1) (rng l2 r2))
  then (r1 < r2)
  else (l1 < l2)

rng-overlap : Range → Range → Bool
rng-overlap (rng l1 r1) (rng l2 r2) = l2 < r1

merge : Range → Range → Range
merge (rng l1 r1) (rng l2 r2) = rng (min l1 l2) (max r1 r2)

parse-line : String → Maybe Range
parse-line xs with (split '-' xs)
parse-line xs | (x ∷ y ∷ _) with (readMaybe 10 x , readMaybe 10 y)
parse-line xs | (x ∷ y ∷ _) | (just l , just h) = just (rng l h)
parse-line xs | (x ∷ y ∷ _) | _ = nothing
parse-line xs | _ = nothing

parse-batch : String → List Range
parse-batch = quick-sort lt-rng ∘ unmaybe ∘ map parse-line ∘ lines

find-min : Nat → List Range → Nat
find-min m [] = m
find-min m ((rng l h) ∷ xs) =
  if m < l
  then m
  else find-min (max m (suc h)) xs

find-allowed-ip : String → String
find-allowed-ip x = "\nIP: " ++ (show ∘ find-min 0 ∘ parse-batch) x ++ "\n"

merge-overlapping : Nat → List Range → List Range
merge-overlapping 0 _ = []
merge-overlapping _ [] = []
merge-overlapping _ (x ∷ []) = x ∷ []
merge-overlapping (suc lm) (x ∷ y ∷ xs) with (rng-overlap x y)
merge-overlapping (suc lm) (x ∷ y ∷ xs) | true = merge-overlapping lm ((merge x y) ∷ xs)
merge-overlapping (suc lm) (x ∷ y ∷ xs) | false = x ∷ (merge-overlapping lm (y ∷ xs))

sum-ranges : List Range → Nat
sum-ranges [] = 0
sum-ranges ((rng l h) ∷ xs) = (h - l + 1) + (sum-ranges xs)

find-count : Nat → List Range → Nat
find-count mx xs = mx - (sum-ranges xs)

count-allowed-ip : String → String
count-allowed-ip x = "\nIPs: " ++ (show ∘ find-count 4294967296 ∘ merge-overlapping (suc(length rngs))) rngs  ++ "\n"
  where
    rngs : List Range
    rngs = (quick-sort lt-rng ∘ parse-batch) x

test-find-min-a : (show ∘ find-min 0 ∘ parse-batch)
  ("5-8\n"++
  "0-2\n" ++
  "4-7") ≡ "3"
test-find-min-a = refl

test-find-min-b : (show ∘ find-min 0 ∘ parse-batch)
  ("1-2\n"++
  "0-6\n" ++
  "4-5") ≡ "7"
test-find-min-b = refl

test-merge-overlap : (unlines ∘ map show-rng ∘ merge-overlapping 10 ∘ parse-batch)
  ("5-8\n"++
  "0-2\n" ++
  "4-7") ≡ "0-2\n4-8"
test-merge-overlap = refl

test-find-count : (show ∘ find-count 10 ∘ merge-overlapping 10 ∘ parse-batch)
  ("5-8\n"++
  "0-2\n" ++
  "4-7") ≡ "2"
test-find-count = refl

module d10.knot where

open import util.list_stuff using (words ; lines ; unmaybe ; hard-unmaybe ; filterᵇ ; make-perms ; rem-dot ; append-front-all ; all-replacements ; cartproduct ; min-by-f ; enumerate ; list-minus ; conseq ; index-of ; set-at ; wordsByᵇ ; get-sub-wrap ; set-sub-wrap) renaming (trim to trim-ch)
open import util.lookup using (LookupStrTree ; build-str-tree ; LTPair ; counter ; quick-sort ; str-lt ; all-values ; all-keys ; all-kv ; has-val) renaming (set-val to set-tree ; read-val to read-tree)
open import util.lookup_nat using (LookupNatTree ; build-nat-tree)
open import util.json using (readIntMaybe)
open import util.search using (search-rec-breadth-dedup ; branch-bound)
open import util.nat_stuff using (div-nat ; mod-nat)
open import util.bitwise using (bitwise-xor)
open import Data.Tree.Binary using (leaf ; node)
open import Agda.Builtin.String using (String)
open import Data.String using (toList ; fromList ; _++_ ; unlines ; intersperse ; fromChar ; padLeft)
open import Data.String.Properties using (_==_)
open import Agda.Builtin.Nat using (Nat ; suc ; _<_ ; _+_ ; _-_ ; _*_ ; div-helper ; mod-helper) renaming (_==_ to _==n_)
open import Data.Nat.Base using (pred ; _⊔_)
open import Data.Nat.Show using (show ; readMaybe ; showInBase)
open import Agda.Builtin.Int using (Int ; pos ; negsuc)
open import Data.Integer using (∣_∣) renaming (_<?_ to _<?z_ ; _+_ to _+z_ ; _-_ to _-z_)
open import Data.Integer.Show using () renaming (show to show-z)
open import Data.Integer.Properties using (_≟_)
open import Agda.Builtin.List using (List ; [] ; _∷_)
open import Data.List using (map ; foldr ; concat ; length ; zip ; reverse ; head ; cartesianProductWith ; applyUpTo ; take ; drop ; any ; all)
open import Agda.Builtin.Char using (Char ; primCharToNat)
open import Data.Char.Properties using () renaming (_==_ to _==c_ ; _<?_ to _<c?_)
open import Agda.Builtin.Bool using (Bool ; true ; false)
open import Data.Bool.Base using (if_then_else_ ; _∧_ ; _∨_ ; not)
open import Agda.Builtin.Maybe using (Maybe ; nothing ; just)
open import Data.Maybe using (fromMaybe)
open import Function using (_∘_ ; id ; flip)
open import Data.Product using (_×_ ; _,_ ; proj₁ ; proj₂ ; map₂ ; uncurry)
open import Agda.Builtin.Equality using (refl ; _≡_)
open import Relation.Nullary.Decidable using (isYes)


record KnotState (A : Set) : Set where
  constructor knot
  field
    current : Nat
    skip : Nat
    chlst : List A


next-step : {A : Set} → Nat → KnotState A → KnotState A
next-step {A} inlen (knot cur sk xs) = (knot new-current (suc sk) new-lst)
  where
    new-sub : List A
    new-sub = (reverse ∘ get-sub-wrap cur inlen) xs
    new-lst : List A
    new-lst = set-sub-wrap cur new-sub xs
    new-current : Nat
    new-current = mod-nat (cur + inlen + sk) (length xs)

all-steps : {A : Set} → List Nat → KnotState A → KnotState A
all-steps [] k = k
all-steps xs k = foldr (next-step) k (reverse xs)

show-ch-knot : KnotState Char → String
show-ch-knot (knot cur sk xs) = intersperse "|" (show cur ∷ show sk ∷ fromList xs ∷ [])

show-nat-knot : KnotState Nat → String
show-nat-knot (knot cur sk xs) = intersperse "|" (show cur ∷ show sk ∷ (intersperse " ∷ " ∘ map show) xs ∷ [])

init-knot : KnotState Nat
init-knot = knot 0 0 (applyUpTo id 256)

trim : String → String
trim = fromList ∘ trim-ch ∘ toList

iter-func : {A : Set} → Nat → (A → A) → A → A
iter-func 0 _ x = x
iter-func 1 f x = f x
iter-func (suc c) f x = iter-func c f (f x)

hash-16 : List Nat → Nat
hash-16 xs = foldr bitwise-xor 0 xs

hash-all-h : Nat → List String → List Nat → List String
hash-all-h 0 _ _ = []
hash-all-h (suc lm) ys [] = reverse ys
hash-all-h (suc lm) ys xs = hash-all-h lm (((padLeft '0' 2 ∘ showInBase 16 ∘ hash-16 ∘ take 16) xs) ∷ ys) (drop 16 xs)

hash-all : List Nat → List String
hash-all xs = hash-all-h (length xs) [] xs

show-p1-sample : KnotState Nat → String
show-p1-sample (knot _ _ (x ∷ y ∷ _)) = show (x * y)
show-p1-sample _ = "failed to get state"

add-lengths : List Nat → List Nat
add-lengths xs = concat (xs ∷ (17 ∷ 31 ∷ 73 ∷ 47 ∷ 23 ∷ []) ∷ [])

run-the-knot : String → String
run-the-knot x = "hash: " ++ intersperse "" hsh ++ "\n"
  where
    seq : List Nat
    seq = (add-lengths ∘ map primCharToNat ∘ toList ∘ trim) x
    fst-round : KnotState Nat
    fst-round = all-steps seq init-knot
    last-round : KnotState Nat
    last-round = iter-func 63 (all-steps seq) fst-round
    hsh : List String
    hsh = hash-all (KnotState.chlst last-round)

test-next-step-a : (fromList ∘ KnotState.chlst ∘ next-step 3 ∘ knot 0 0 ∘ toList) "01234" ≡ "21034"
test-next-step-a = refl

test-next-step-b : (show-ch-knot ∘ next-step 4 ∘ next-step 3 ∘ knot 0 0 ∘ toList) "01234" ≡ "3|2|43012"
test-next-step-b = refl

test-next-step-c : (show-ch-knot ∘ next-step 1 ∘ next-step 4 ∘ next-step 3 ∘ knot 0 0 ∘ toList) "01234" ≡ "1|3|43012"
test-next-step-c = refl

test-next-step-d : (show-ch-knot ∘ next-step 5 ∘ next-step 1 ∘ next-step 4 ∘ next-step 3 ∘ knot 0 0 ∘ toList) "01234" ≡ "4|4|34210"
test-next-step-d = refl

test-all-steps : (show-ch-knot ∘ all-steps (3 ∷ 4 ∷ 1 ∷ 5 ∷ []) ∘ knot 0 0 ∘ toList) "01234" ≡ "4|4|34210"
test-all-steps = refl

test-hash-16 : hash-16 (65 ∷ 27 ∷ 9 ∷ 1 ∷ 4 ∷ 3 ∷ 40 ∷ 50 ∷ 91 ∷ 7 ∷ 6 ∷ 0 ∷ 2 ∷ 5 ∷ 68 ∷ 22 ∷ []) ≡ 64
test-hash-16 = refl

test-run-the-knot-a : run-the-knot "" ≡ "hash: a2582a3a0e66e6e86e3812dcb672a272\n"
test-run-the-knot-a = refl

test-run-the-knot-b : run-the-knot "AoC 2017" ≡ "hash: 33efeb34ea91902bb2f59c9920caa6cd\n"
test-run-the-knot-b = refl

test-run-the-knot-c : run-the-knot "1,2,3" ≡ "hash: 3efbe78a8d82f29979031a4aa0b16a9d\n"
test-run-the-knot-c = refl

test-run-the-knot-d : run-the-knot "1,2,4" ≡ "hash: 63960835bcdc130f0b66d7ff4f6a5a8e\n"
test-run-the-knot-d = refl


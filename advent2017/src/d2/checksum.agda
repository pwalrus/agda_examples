module d2.checksum where

open import util.list_stuff using (words ; lines ; unmaybe ; hard-unmaybe ; filterᵇ ; make-perms ; rem-dot ; append-front-all ; all-replacements ; cartproduct ; min-by-f ; enumerate ; list-minus ; conseq) renaming (trim to trim-ch)
open import util.lookup using (LookupStrTree ; LookupNatTree ; build-str-tree ; build-nat-tree ; has-val ; all-values ; all-keys ; all-kv ; LTPair) renaming (set-val to set-tree ; read-val to read-tree)
open import util.json using (readIntMaybe)
open import util.search using (search-rec-breadth-dedup ; branch-bound)
open import util.nat_stuff using (div-nat ; mod-nat)
open import Data.Tree.Binary using (leaf ; node)
open import Agda.Builtin.String using (String)
open import Data.String.Base using (toList ; fromList ; _++_ ; unlines ; intersperse ; fromChar)
open import Data.String.Properties using (_==_ ; _<?_)
open import Agda.Builtin.Nat using (Nat ; suc ; _<_ ; _+_ ; _-_ ; _*_ ; div-helper ; mod-helper) renaming (_==_ to _==n_)
open import Data.Nat.Base using (pred)
open import Data.Nat.Show using (show ; readMaybe)
open import Agda.Builtin.Int using (Int ; pos ; negsuc)
open import Data.Integer.Base using () renaming (_+_ to _+z_ ; _-_ to _-z_)
open import Data.Integer.Show using () renaming (show to show-z)
open import Data.Integer.Properties using (_≟_)
open import Agda.Builtin.List using (List ; [] ; _∷_)
open import Data.List using (map ; foldr ; concat ; length ; zip ; reverse ; head ; cartesianProductWith ; applyUpTo ; take ; drop)
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


trim : String → String
trim = fromList ∘ trim-ch ∘ toList

parse-row : String → List Nat
parse-row = unmaybe ∘ map (readMaybe 10) ∘ map trim ∘ words

max-list : Nat → List Nat → Nat
max-list x [] = x
max-list x (y ∷ ys) = max-list (if x < y then y else x) ys

min-list : Nat → List Nat → Nat
min-list x [] = x
min-list x (y ∷ ys) = min-list (if y < x then y else x) ys


row-diff : List Nat → Nat
row-diff xs = max-list 0 xs - min-list 1000000 xs

find-div-pair : List Nat → Maybe (Nat × Nat)
find-div-pair xs = head(filterᵇ (λ {(a , b) → (not (a ==n b)) ∧ (mod-nat a b ==n 0)}) (cartesianProductWith _,_ xs xs))


calc-checksum : String → String
calc-checksum inp = (show ∘ foldr _+_ 0 ∘ map row-diff ∘ map parse-row ∘ lines) inp ++ "\n"

calc-div-pair : String → String
calc-div-pair inp = (show ∘ foldr _+_ 0 ∘ map (λ {(a , b) → div-nat a b}) ∘ unmaybe ∘ map find-div-pair ∘ map parse-row ∘ lines) inp ++ "\n"


test-max-list : max-list 0 (1 ∷ 3 ∷ 2 ∷ []) ≡ 3
test-max-list = refl

test-min-list : min-list 9 (1 ∷ 3 ∷ 2 ∷ []) ≡ 1
test-min-list = refl


test-calc-checksum : calc-checksum ("5 1 9 5\n"++
  "7 5 3\n" ++
  "2 4 6 8") ≡ "18\n"
test-calc-checksum = refl

test-find-div-pair-a : find-div-pair (5 ∷ 9 ∷ 2 ∷ 8 ∷ []) ≡ just (8 , 2)
test-find-div-pair-a = refl

test-calc-div-pair : calc-div-pair ("5 9 2 8\n" ++
  "9 4 7 3\n" ++
  "3 8 6 5") ≡ "9\n"
test-calc-div-pair = refl

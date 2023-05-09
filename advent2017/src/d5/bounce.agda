module d5.bounce where

open import util.list_stuff using (words ; lines ; unmaybe ; hard-unmaybe ; filterᵇ ; make-perms ; rem-dot ; append-front-all ; all-replacements ; cartproduct ; min-by-f ; enumerate ; list-minus ; conseq) renaming (trim to trim-ch)
open import util.lookup using (LTPair ; counter ; quick-sort ; str-lt ; all-values ; all-keys)
open import util.lookup_nat using (LookupNatTree ; build-nat-tree ; has-val ; all-kv) renaming (set-val to set-tree ; read-val to read-tree)
open import util.json using (readIntMaybe)
open import util.search using (search-rec-breadth-dedup ; branch-bound)
open import util.nat_stuff using (div-nat ; mod-nat)
open import Data.Tree.Binary using (leaf ; node)
open import Agda.Builtin.String using (String)
open import Data.String.Base using (toList ; fromList ; _++_ ; unlines ; intersperse ; fromChar)
open import Data.String.Properties using (_==_)
open import Agda.Builtin.Nat using (Nat ; suc ; _<_ ; _+_ ; _-_ ; _*_ ; div-helper ; mod-helper) renaming (_==_ to _==n_)
open import Data.Nat.Base using (pred)
open import Data.Nat.Show using (show ; readMaybe)
open import Agda.Builtin.Int using (Int ; pos ; negsuc)
open import Data.Integer.Base using (∣_∣) renaming (_+_ to _+z_ ; _-_ to _-z_)
open import Data.Integer.Show using () renaming (show to show-z)
open import Data.Integer.Properties using (_≟_)
open import Agda.Builtin.List using (List ; [] ; _∷_)
open import Data.List using (map ; foldr ; concat ; length ; zip ; reverse ; head ; cartesianProductWith ; applyUpTo ; take ; drop ; any)
open import Agda.Builtin.Char using (Char)
open import Data.Char.Properties using () renaming (_==_ to _==c_ ; _<?_ to _<c?_)
open import Agda.Builtin.Bool using (Bool ; true ; false)
open import Data.Bool.Base using (if_then_else_ ; _∧_ ; _∨_ ; not)
open import Agda.Builtin.Maybe using (Maybe ; nothing ; just)
open import Data.Maybe using (fromMaybe)
open import Function using (_∘_ ; id)
open import Data.Product using (_×_ ; _,_ ; proj₁ ; proj₂ ; map₂)
open import Agda.Builtin.Equality using (refl ; _≡_)
open import Relation.Nullary.Decidable using (isYes)


readIntMaybeStr : String → Maybe Int
readIntMaybeStr = readIntMaybe ∘ toList

trim : String → String
trim = fromList ∘ trim-ch ∘ toList

parse-row : String → LookupNatTree Int
parse-row = build-nat-tree ∘ enumerate ∘ unmaybe ∘ map readIntMaybeStr ∘ words ∘ trim

show-db : LookupNatTree Int → String
show-db = unlines ∘ map (λ {(a , b) → show a ++ ": " ++ show-z b}) ∘ all-kv

next-step : Bool → (Int × LookupNatTree Int) → Maybe (Int × LookupNatTree Int)
next-step dec (current , db) with (current)
next-step dec (current , db) | (pos n) with (read-tree n db)
next-step dec (current , db) | (pos n) | (just (pos v)) = just (current +z pos v ,
  set-tree n (if dec ∧ (2 < v) then (pos (v - 1)) else (pos (v + 1))) db)
next-step dec (current , db) | (pos n) | (just v) = just (current +z v , set-tree n (v +z pos 1) db)
next-step dec (current , db) | (pos n) | nothing = nothing
next-step dec (current , db) | _ = nothing

iterate-until-escape : Bool → Nat → Nat → (Int × LookupNatTree Int) → Maybe (Nat × Int × LookupNatTree Int)
iterate-until-escape dec 0 _ _ = nothing
iterate-until-escape dec (suc lm) step (pos n , db) with (has-val n db)
iterate-until-escape dec (suc lm) step (pos n , db) | false = just (step , pos n , db)
iterate-until-escape dec (suc lm) step (pos n , db) | true with (next-step dec (pos n , db))
iterate-until-escape dec (suc lm) step (pos n , db) | true | (just next) = iterate-until-escape dec lm (suc step) next
iterate-until-escape dec (suc lm) step (pos n , db) | true | _ = just (step , pos n , db)
iterate-until-escape dec (suc lm) step (x , db) = just (step , x , db)

show-state : (Int × LookupNatTree Int) → String
show-state (current , db) = "current: " ++ show-z current ++ "\n" ++ show-db db

show-state-step : (Nat × Int × LookupNatTree Int) → String
show-state-step (steps , current , db) = "steps: " ++ show steps ++ "\n" ++ show-state (current , db)

jump-through : String → String
jump-through x = output ++ "\n"
  where
    output : String
    output with ((iterate-until-escape true 1000000000 0 ∘ (λ {q → pos 0 , parse-row q})) x)
    output | nothing = "failed to exit."
    output | (just st-step) = show-state-step st-step

test-parse-row : (show-db ∘ parse-row) ("0\n3\n0\n1\n-3\n") ≡ "0: 0\n1: 3\n2: 0\n3: 1\n4: -3"
test-parse-row = refl

test-next-step : (show-state ∘ fromMaybe (pos 0 , build-nat-tree []) ∘ next-step false ∘ (λ {q → pos 0 , parse-row q})) ("0\n3\n0\n1\n-3\n")
  ≡ "current: 0\n0: 1\n1: 3\n2: 0\n3: 1\n4: -3"
test-next-step = refl

test-next-step-a : (show-state ∘ fromMaybe (pos 0 , build-nat-tree []) ∘ next-step false ∘ fromMaybe (pos 0 , build-nat-tree []) ∘ next-step false ∘ (λ {q → pos 0 , parse-row q})) ("0\n3\n0\n1\n-3\n")
  ≡ "current: 1\n0: 2\n1: 3\n2: 0\n3: 1\n4: -3"
test-next-step-a = refl

test-iterate-a : (show-state-step ∘ fromMaybe (0 , pos 0 , build-nat-tree []) ∘ iterate-until-escape false 1000 0 ∘ (λ {q → pos 0 , parse-row q})) ("0\n3\n0\n1\n-3\n")
  ≡ "steps: 5\ncurrent: 5\n0: 2\n1: 5\n2: 0\n3: 1\n4: -2"
test-iterate-a = refl

test-iterate-b : (show-state-step ∘ fromMaybe (0 , pos 0 , build-nat-tree []) ∘ iterate-until-escape true 1000 0 ∘ (λ {q → pos 0 , parse-row q})) ("0\n3\n0\n1\n-3\n")
  ≡ "steps: 10\ncurrent: 5\n0: 2\n1: 3\n2: 2\n3: 3\n4: -1"
test-iterate-b = refl

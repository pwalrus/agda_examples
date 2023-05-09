module d6.cycle where

open import util.list_stuff using (words ; lines ; unmaybe ; hard-unmaybe ; filterᵇ ; make-perms ; rem-dot ; append-front-all ; all-replacements ; cartproduct ; min-by-f ; enumerate ; list-minus ; conseq ; index-of ; set-at) renaming (trim to trim-ch)
open import util.lookup using (LookupStrTree ; build-str-tree ; LTPair ; counter ; quick-sort ; str-lt ; all-values ; all-keys ; all-kv ; has-val) renaming (set-val to set-tree ; read-val to read-tree)
open import util.lookup_nat using (LookupNatTree ; build-nat-tree)
open import util.json using (readIntMaybe)
open import util.search using (search-rec-breadth-dedup ; branch-bound)
open import util.nat_stuff using (div-nat ; mod-nat)
open import Data.Tree.Binary using (leaf ; node)
open import Agda.Builtin.String using (String)
open import Data.String.Base using (toList ; fromList ; _++_ ; unlines ; intersperse ; fromChar)
open import Data.String.Properties using (_==_)
open import Agda.Builtin.Nat using (Nat ; suc ; _<_ ; _+_ ; _-_ ; _*_ ; div-helper ; mod-helper) renaming (_==_ to _==n_)
open import Data.Nat.Base using (pred ; _⊔_)
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


find-max-idx : List Nat → Nat
find-max-idx xs = fromMaybe 0 (index-of _==n_ xs biggest)
  where
    biggest : Nat
    biggest = foldr _⊔_ 0 xs

increm-fast : Nat → List Nat → List Nat
increm-fast x xs = map (λ {q → q + x}) xs

increm-head : Nat → List Nat → List Nat
increm-head x xs = concat ((increm-fast 1 (take x xs)) ∷ (drop x xs) ∷ [])

increm-tail : Nat → List Nat → List Nat
increm-tail x xs = concat ((take x xs) ∷ (increm-fast 1 (drop x xs)) ∷ [])

increm-slow : Nat → Nat → List Nat → List Nat
increm-slow x idx xs with (x < suc (length xs - idx))
increm-slow x idx xs | true = concat ((take idx xs) ∷ increm-fast 1 (take x (drop idx xs)) ∷ (drop (x + idx) xs) ∷ [])
increm-slow x idx xs | false = increm-head (x + idx - length xs) (increm-tail idx xs)

next-step : List Nat → List Nat
next-step xs = increm-slow remain start (increm-fast whole (set-at xs idx 0))
  where
    biggest : Nat
    biggest = foldr _⊔_ 0 xs
    idx : Nat
    idx = find-max-idx xs
    whole : Nat
    whole = div-nat biggest (length xs)
    remain : Nat
    remain = mod-nat biggest (length xs)
    start : Nat
    start = mod-nat (suc idx) (length xs)


show-state : List Nat → String
show-state = intersperse " " ∘ map show

iterate-until-duplicate : {A : Set} → Nat → Nat → (A → A) → (A → String) → A → LookupStrTree Nat → (Nat × Nat × LookupStrTree Nat)
iterate-until-duplicate 0 _ _ _ _ db = (0 , 0 , db)
iterate-until-duplicate (suc lm) step next-func name-func start db with (read-tree (name-func start) db)
iterate-until-duplicate (suc lm) step next-func name-func start db | (just b) = (step , b , db)
iterate-until-duplicate (suc lm) step next-func name-func start db | nothing = iterate-until-duplicate lm (suc step) next-func name-func (next-func start) (set-tree (name-func start) step db)


show-tree : LookupStrTree Nat → String
show-tree = unlines ∘ map (λ {(a , b) → a ++ ": " ++ show b}) ∘ all-kv

show-sol : (Nat × Nat × LookupStrTree Nat) → String
show-sol (a , b , _) = "steps: " ++ show a ++ ", prior: " ++ show b ++ " (loop of " ++ show (a - b) ++ ")"

find-inf-loop : String → String
find-inf-loop x = show-sol step-count ++ "\n"
  where
    start : List Nat
    start = (unmaybe ∘ map (readMaybe 10) ∘ words) x
    step-count : (Nat × Nat × LookupStrTree Nat)
    step-count = iterate-until-duplicate 1000000 0 next-step show-state start (build-str-tree (("" , 0) ∷ []))

test-increm-slow-a : increm-slow 3 2 (2 ∷ 3 ∷ 1 ∷ 4 ∷ []) ≡ (3 ∷ 3 ∷ 2 ∷ 5 ∷ [])
test-increm-slow-a = refl

test-increm-slow-b : increm-slow 2 1 (2 ∷ 3 ∷ 1 ∷ 4 ∷ []) ≡ (2 ∷ 4 ∷ 2 ∷ 4 ∷ [])
test-increm-slow-b = refl

test-next-step-a : next-step (0 ∷ 2 ∷ 7 ∷ 0 ∷ []) ≡ (2 ∷ 4 ∷ 1 ∷ 2 ∷ [])
test-next-step-a = refl

test-next-step-b : next-step (2 ∷ 4 ∷ 1 ∷ 2 ∷ []) ≡ (3 ∷ 1 ∷ 2 ∷ 3 ∷ [])
test-next-step-b = refl

test-next-step-c : next-step (3 ∷ 1 ∷ 2 ∷ 3 ∷ []) ≡ (0 ∷ 2 ∷ 3 ∷ 4 ∷ [])
test-next-step-c = refl

test-next-step-d : next-step (0 ∷ 2 ∷ 3 ∷ 4 ∷ []) ≡ (1 ∷ 3 ∷ 4 ∷ 1 ∷ [])
test-next-step-d = refl

test-next-step-e : next-step (1 ∷ 3 ∷ 4 ∷ 1 ∷ []) ≡ (2 ∷ 4 ∷ 1 ∷ 2 ∷ [])
test-next-step-e = refl

test-iterate : proj₁ (iterate-until-duplicate 10 0 next-step show-state (0 ∷ 2 ∷ 7 ∷ 0 ∷ []) (build-str-tree (("" , 0) ∷ []))) ≡ 5
test-iterate = refl

test-find-inf : find-inf-loop "0 2 7 0" ≡ "steps: 5, prior: 1 (loop of 4)\n"
test-find-inf = refl

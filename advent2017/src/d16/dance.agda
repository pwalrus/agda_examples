module d16.dance where

open import util.list_stuff using (words ; lines ; unmaybe ; hard-unmaybe ; filterᵇ ; make-perms ; rem-dot ; append-front-all ; all-replacements ; cartproduct ; min-by-f ; enumerate ; list-minus ; conseq ; index-of ; set-at ; wordsByᵇ ; get-sub-wrap ; set-sub-wrap ; is-in ; unique-insert ; idxOf ; atIdx ; setIdx ; apply-perm-to-perm ; exp-perm) renaming (trim to trim-ch)
open import util.lookup using (LookupStrTree ; build-str-tree ; LTPair ; counter ; quick-sort ; str-lt ; all-values ; all-keys ; unique-list)
open import util.lookup_nat using (LookupNatTree ; build-nat-tree ; has-val ; all-kv) renaming (set-val to set-tree ; read-val to read-tree)
open import util.json using (readIntMaybe)
open import util.search using (search-rec-breadth-dedup ; branch-bound ; components)
open import util.nat_stuff using (div-nat ; mod-nat ; max)
open import util.bitwise using (bitwise-xor ; to-bin ; show-bool)
open import util.grid using (Point ; point ; show-point ; neighbors-2d)
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
open import Agda.Builtin.Char using (Char ; primCharToNat ; primNatToChar ; primToLower)
open import Data.Char.Properties using () renaming (_==_ to _==c_ ; _<?_ to _<c?_)
open import Agda.Builtin.Bool using (Bool ; true ; false)
open import Data.Bool.Base using (if_then_else_ ; _∧_ ; _∨_ ; not)
open import Agda.Builtin.Maybe using (Maybe ; nothing ; just)
open import Data.Maybe using (fromMaybe)
open import Function using (_∘_ ; id ; flip ; const)
open import Data.Product using (_×_ ; _,_ ; proj₁ ; proj₂ ; map₂ ; uncurry)
open import Agda.Builtin.Equality using (refl ; _≡_)
open import Relation.Nullary.Decidable using (isYes)


idx-of : Char → String → Nat
idx-of c xs = (fromMaybe 0 ∘ idxOf _==c_ 0 c ∘ toList) xs

get-idx : Nat → String → Char
get-idx idx xs = fromMaybe 'z' (atIdx idx (toList xs))

set-idx : Nat → Char → String → String
set-idx idx c xs = (fromList ∘ setIdx idx c ∘ toList) xs

swap-idx : Nat → Nat → String → String
swap-idx x y xs = set-idx x rc (set-idx y lc xs)
  where
    lc : Char
    lc = get-idx x xs
    rc : Char
    rc = get-idx y xs

swap-ch : Char → Char → String → String
swap-ch a b xs = swap-idx (idx-of a xs) (idx-of b xs) xs


data Move : Set where
  spin : Nat → Move
  exchange : Nat → Nat → Move
  partner : Char → Char → Move


show-move : Move → String
show-move (spin x) = "s" ++ show x
show-move (exchange a b) = "x" ++ show a ++ "/" ++ show b
show-move (partner a b) = "p" ++ fromChar a ++ "/" ++ fromChar b

parse-row-spin : String → Maybe Move
parse-row-spin xs with (toList xs)
parse-row-spin xs | ('s' ∷ nm) with ((readMaybe 10 ∘ fromList) nm)
parse-row-spin xs | ('s' ∷ nm) | (just x) = just (spin x)
parse-row-spin xs | ('s' ∷ nm) | _ = nothing
parse-row-spin xs | _ = nothing

parse-row-ex : String → Maybe Move
parse-row-ex xs with (toList xs)
parse-row-ex xs | ('x' ∷ pm) with ((wordsByᵇ (_==c_ '/') ∘ fromList) pm)
parse-row-ex xs | ('x' ∷ pm) | (na ∷ nb ∷ []) with (readMaybe 10 na , readMaybe 10 nb)
parse-row-ex xs | ('x' ∷ pm) | (na ∷ nb ∷ []) | (just a , just b) = just (exchange a b)
parse-row-ex xs | ('x' ∷ pm) | (na ∷ nb ∷ []) | _ = nothing
parse-row-ex xs | ('x' ∷ pm) | _ = nothing
parse-row-ex xs | _ = nothing

parse-row-par : String → Maybe Move
parse-row-par xs with (toList xs)
parse-row-par xs | ('p' ∷ na ∷ '/' ∷ nb ∷ []) = just (partner na nb)
parse-row-par xs | _ = nothing

parse-row : String → Maybe Move
parse-row xs with (toList xs)
parse-row xs | ('s' ∷ _) = parse-row-spin xs
parse-row xs | ('x' ∷ _) = parse-row-ex xs
parse-row xs | ('p' ∷ _) = parse-row-par xs
parse-row xs | _ = nothing

apply-move : Move → List Char → List Char
apply-move (spin n) xs = set-sub-wrap (n) xs xs
apply-move (exchange a b) = toList ∘ swap-idx a b ∘ fromList
apply-move (partner a b) = toList ∘ swap-ch a b ∘ fromList

apply-moves : List Move → List Char → List Char
apply-moves moves xs = foldr apply-move xs (reverse moves)

trim : String → String
trim = fromList ∘ trim-ch ∘ toList

list-ch-eq : List Char → List Char → Bool
list-ch-eq [] [] = true
list-ch-eq [] _ = false
list-ch-eq _ [] = false
list-ch-eq (x ∷ xs) (y ∷ ys) = if (x ==c y) then (list-ch-eq xs ys) else false

find-cycle : {A : Set} → Nat → Nat → (A → A → Bool) → (A → A) → A → A → Nat
find-cycle 0 _ _ _ _ _ = 0
find-cycle (suc lm) 0 eq inc start orig = find-cycle lm 1 eq inc (inc start) orig
find-cycle (suc lm) idx eq inc start orig with (eq start orig)
find-cycle (suc lm) idx eq inc start orig | true = idx
find-cycle (suc lm) idx eq inc start orig | false = find-cycle lm (suc idx) eq inc (inc start) orig

iter-func : {A : Set} → Nat → (A → A) → A → A
iter-func 0 _ x = x
iter-func 1 f x = f x
iter-func (suc lm) f x = iter-func lm f (f x)

after-dance : String → String
after-dance x = "first: " ++ fromList fst ++ "\ncycle after: " ++ show needed-iter ++ "\n" ++ (fromList ∘ iter-func needed-iter (apply-moves moves)) init-state  ++ "\n"
  where
    moves : List Move
    moves = (unmaybe ∘ map parse-row ∘ wordsByᵇ (_==c_ ',') ∘ trim) x
    init-state : List Char
    init-state = toList "abcdefghijklmnop"
    fst : List Char
    fst = apply-moves moves init-state
    cycle-length : Nat
    cycle-length = find-cycle 1000000000 0 list-ch-eq (apply-moves moves) init-state init-state
    needed-iter : Nat
    needed-iter = mod-nat 1000000000 cycle-length
    

test-parse-row-a : (show-move ∘ fromMaybe (spin 0) ∘ parse-row) "s15" ≡ "s15"
test-parse-row-a = refl

test-parse-row-b : (show-move ∘ fromMaybe (spin 0) ∘ parse-row) "x3/4" ≡ "x3/4"
test-parse-row-b = refl

test-parse-row-c : (show-move ∘ fromMaybe (spin 0) ∘ parse-row) "pe/b" ≡ "pe/b"
test-parse-row-c = refl

test-apply-move-a : (fromList ∘ apply-move (spin 3) ∘ toList) "abcde" ≡ "cdeab"
test-apply-move-a = refl

test-apply-move-b : (fromList ∘ apply-move (spin 1) ∘ toList) "abcde" ≡ "eabcd"
test-apply-move-b = refl

test-apply-move-c : (fromList ∘ apply-move (exchange 3 4) ∘ apply-move (spin 1) ∘ toList) "abcde" ≡ "eabdc"
test-apply-move-c = refl

test-apply-move-d : (fromList ∘ apply-move (partner 'e' 'b') ∘ apply-move (exchange 3 4) ∘ apply-move (spin 1) ∘ toList) "abcde" ≡ "baedc"
test-apply-move-d = refl

test-apply-move-e : (fromList ∘ apply-moves ((spin 1) ∷ (exchange 3 4) ∷ (partner 'e' 'b') ∷ []) ∘ toList) "abcde" ≡ "baedc"
test-apply-move-e = refl

test-find-cycle : find-cycle 1000000 0 list-ch-eq (apply-moves ((spin 1) ∷ (exchange 3 4) ∷ (partner 'e' 'b') ∷ [])) (toList "abcde") (toList "abcde") ≡ 4
test-find-cycle = refl

test-iter-func-a : (fromList ∘ iter-func 1 (apply-moves ((spin 1) ∷ (exchange 3 4) ∷ (partner 'e' 'b') ∷ [])) ∘ toList) "abcde" ≡ "baedc"
test-iter-func-a = refl

test-iter-func-b : (fromList ∘ iter-func 2 (apply-moves ((spin 1) ∷ (exchange 3 4) ∷ (partner 'e' 'b') ∷ [])) ∘ toList) "abcde" ≡ "ceadb"
test-iter-func-b = refl

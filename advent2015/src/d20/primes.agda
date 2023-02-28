
module d20.primes where

open import util.list_stuff using (words ; lines ; unmaybe ; filterᵇ ; make-perms ; rem-dot ; append-front-all ; all-replacements) renaming (trim to trim-ch)
open import util.lookup using (LookupNatTree ; build-nat-tree ; has_val ; all_values ; all-keys ; all-kv ; LTPair) renaming (set_val to set-tree ; read_val to read-tree)
open import util.json using (readIntMaybe)
open import Data.Tree.Binary using (leaf ; node)
open import Agda.Builtin.String using (String)
open import Data.String.Base using (toList ; fromList ; _++_ ; unlines ; intersperse)
open import Data.String.Properties using (_==_ ; _<?_)
open import Agda.Builtin.Nat using (Nat ; suc ; _<_ ; _+_ ; _*_ ; div-helper ; mod-helper) renaming (_==_ to _==n_ ; _-_ to nat-diff)
open import Data.Nat.Base using (pred)
open import Data.Nat.Show using (show ; readMaybe)
open import Agda.Builtin.Int using (Int ; pos ; negsuc)
open import Data.Integer.Properties using (_≟_)
open import Agda.Builtin.List using (List ; [] ; _∷_)
open import Data.List using (map ; foldr ; concat ; length ; zip)
open import Agda.Builtin.Char using (Char)
open import Data.Char.Properties renaming (_==_ to _==c_)
open import Agda.Builtin.Bool using (Bool ; true ; false)
open import Data.Bool.Base using (if_then_else_ ; _∧_ ; _∨_ ; not)
open import Agda.Builtin.Maybe using (Maybe ; nothing ; just)
open import Function.Base using (_∘_)
open import Data.Product using (_×_ ; _,_ ; proj₁ ; proj₂)
open import Agda.Builtin.Equality using (refl ; _≡_)
open import Relation.Nullary.Decidable using (isYes)


mod-nat : Nat → Nat → Nat
mod-nat x y = mod-helper 0 (pred y) x (pred y)

div-nat : Nat → Nat → Nat
div-nat x y = div-helper 0 (pred y) x (pred y)

nat-range : Nat → List Nat
nat-range 0 = []
nat-range (suc y) = (suc y) ∷ (nat-range y)

nat-sqrt-h : Nat → Nat → Nat → Nat → Nat
nat-sqrt-h 0 target _ _ = 0
nat-sqrt-h (suc l) target low high with ((low ==n high) ∨ (suc low ==n high))
nat-sqrt-h (suc l) target low high | true = low
nat-sqrt-h (suc l) target low high | false with (div-nat (low + high) 2)
nat-sqrt-h (suc l) target low high | false | mid with (mid * mid ==n target)
nat-sqrt-h (suc l) target low high | false | mid | true = mid
nat-sqrt-h (suc l) target low high | false | mid | false with (mid * mid < target)
nat-sqrt-h (suc l) target low high | false | mid | false | true = nat-sqrt-h l target mid high
nat-sqrt-h (suc l) target low high | false | mid | false | false = nat-sqrt-h l target low mid

nat-sqrt : Nat → Nat
nat-sqrt 1 = 1
nat-sqrt x = nat-sqrt-h (10 * x) x 0 x

mirror-divisors : Nat → List Nat → List Nat
mirror-divisors target [] = []
mirror-divisors target (x ∷ xs) with ((div-nat target x) ==n x)
mirror-divisors target (x ∷ xs) | true = x ∷ (mirror-divisors target xs)
mirror-divisors target (x ∷ xs) | false = (div-nat target x) ∷ x ∷ (mirror-divisors target xs)

divisor-list : Nat → List Nat
divisor-list x = mirror-divisors x (filterᵇ (λ {q → (mod-nat x q) ==n 0}) (nat-range (nat-sqrt x)))

score-number : Nat → Nat
score-number x = foldr _+_ 0 scaled
  where
    dl : List Nat
    dl = divisor-list x
    scaled : List Nat
    scaled = map (λ {q → 10 * q}) dl

mk-text : Nat → Nat → String
mk-text idx score = "House " ++ show idx ++ " got " ++ show score ++ " presents."

mk-text-tree : LookupNatTree Nat → List String
mk-text-tree db = map (λ {q → mk-text (proj₁ q)  (proj₂ q)}) pairs
  where
    pairs : List (Nat × Nat)
    pairs = all-kv db

-- works on small examples but d
iter-score : Nat → Nat → Nat → List String
iter-score 0 _ _ = []
iter-score (suc l) target idx with (score-number idx)
iter-score (suc l) target idx | score with (target < suc score)
iter-score (suc l) target idx | score | true = mk-text idx score ∷ []
iter-score (suc l) target idx | score | false = (mk-text idx score) ∷ (iter-score l target (suc idx))

iter-score-s : Nat → Nat → Nat → String
iter-score-s 0 _ _ = "none found"
iter-score-s (suc l) target idx with (score-number idx)
iter-score-s (suc l) target idx | score with (target < suc score)
iter-score-s (suc l) target idx | score | true = mk-text idx score
iter-score-s (suc l) target idx | score | false = iter-score-s l target (suc idx)

min : Nat → Nat → Nat
min x y = if (x < y) then x else y

max : Nat → Nat → Nat
max x y = if (x < y) then y else x

update-house-h : List (Nat × Nat) → LookupNatTree Nat → LookupNatTree Nat
update-house-h [] db = db
update-house-h ((e , h) ∷ xs) db with (read-tree h db)
update-house-h ((e , h) ∷ xs) db | nothing = update-house-h xs (set-tree (h * e) (h * 10) db)
update-house-h ((e , h) ∷ xs) db | (just old) = update-house-h xs (set-tree (h * e) (old + h * 10) db)

update-house : Nat → Nat → LookupNatTree Nat → LookupNatTree Nat
update-house h-idx target db = update-house-h pairs db
  where
    pairs : List (Nat × Nat)
    pairs = map (λ {elf → elf , h-idx}) (nat-range (suc (div-nat (min target 100000) h-idx)))

init-houses : Nat → LookupNatTree Nat
init-houses target = (build-nat-tree ∘ (map (λ {x → (x , 10)})) ∘ nat-range) target

-- works on small examples but takes too much memory
iter-by-house-h : Nat → Nat → Nat → LookupNatTree Nat → (Nat × Nat)
iter-by-house-h 0 _ _ db = (0 , 1)
iter-by-house-h (suc l) target h-idx db with (update-house h-idx target db)
iter-by-house-h (suc l) target h-idx db | new-db with (read-tree h-idx new-db)
iter-by-house-h (suc l) target h-idx db | new-db | nothing = (0 , 1)
iter-by-house-h (suc l) target h-idx db | new-db | (just val) with (target < suc val)
iter-by-house-h (suc l) target h-idx db | new-db | (just val) | true = h-idx , val
iter-by-house-h (suc l) target h-idx db | new-db | (just val) | false = iter-by-house-h l target (suc h-idx) new-db

search-min-house : String → String
search-min-house x = "\n" ++ sol ++ "\n"
  where
    mtarget : Maybe Nat
    mtarget = readMaybe 10 ((fromList ∘ trim-ch ∘ toList) x)
    target : Nat
    target with (mtarget)
    target | nothing = 1
    target | (just target) = target
    sol : String
    sol = iter-score-s target target (max 1 (div-nat target 150))

test-nat-sqrt-a : nat-sqrt 17 ≡ 4
test-nat-sqrt-a = refl

test-nat-sqrt-b : nat-sqrt 16 ≡ 4
test-nat-sqrt-b = refl

test-nat-sqrt-c : nat-sqrt 15 ≡ 3
test-nat-sqrt-c = refl

test-mod-nat : mod-nat 5 3 ≡ 2
test-mod-nat = refl

test-divisor-list : divisor-list 1 ≡ 1 ∷ []
test-divisor-list = refl

test-divisor-list-b : divisor-list 5 ≡ 5 ∷ 1 ∷ []
test-divisor-list-b = refl

test-divisor-list-a : divisor-list 6 ≡ 3 ∷ 2 ∷ 6 ∷ 1 ∷ []
test-divisor-list-a = refl

test-divisor-list-c : divisor-list 9 ≡ 3 ∷ 9 ∷ 1 ∷ []
test-divisor-list-c = refl

test-iter-score : unlines (iter-score 150 150 1 ) ≡
  "House 1 got 10 presents.\n" ++
  "House 2 got 30 presents.\n" ++
  "House 3 got 40 presents.\n" ++
  "House 4 got 70 presents.\n" ++
  "House 5 got 60 presents.\n" ++
  "House 6 got 120 presents.\n" ++
  "House 7 got 80 presents.\n" ++
  "House 8 got 150 presents."
test-iter-score = refl

test-update-house : (unlines ∘ mk-text-tree ∘ update-house 2 3) (init-houses 3) ≡
  "House 4 got 30 presents.\n" ++
  "House 3 got 10 presents.\n" ++
  "House 2 got 30 presents.\n" ++
  "House 1 got 10 presents."
test-update-house = refl

test-iter-by-house-h : iter-by-house-h 150 150 2 (init-houses 150) ≡ (8 , 150)
test-iter-by-house-h = refl

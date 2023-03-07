module d25.diag where

open import util.list_stuff using (words ; lines ; unmaybe ; filterᵇ ; each-one ; make-perms ; rem-dot ; append-front-all ; all-replacements ; cartproduct ; min-by-f ; enumerate) renaming (trim to trim-ch)
open import util.lookup using (LookupStrTree ; LookupNatTree ; build-str-tree ; build-nat-tree ; has-val ; all-values ; all-keys ; all-kv ; LTPair) renaming (set-val to set-tree ; read-val to read-tree)
open import util.json using (readIntMaybe)
open import Data.Tree.Binary using (leaf ; node)
open import Agda.Builtin.String using (String)
open import Data.String.Base using (toList ; fromList ; _++_ ; unlines ; intersperse)
open import Data.String.Properties using (_==_ ; _<?_)
open import Agda.Builtin.Nat using (Nat ; suc ; _<_ ; _+_ ; _-_ ; _*_ ; div-helper ; mod-helper) renaming (_==_ to _==n_)
open import Data.Nat.Base using (pred)
open import Data.Nat.Show using (show ; readMaybe)
open import Agda.Builtin.Int using (Int ; pos ; negsuc)
open import Data.Integer.Base using () renaming (_+_ to _+z_)
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


div-nat : Nat → Nat → Nat
div-nat x y = div-helper 0 (pred y) x (pred y)

mod-nat : Nat → Nat → Nat
mod-nat x y = mod-helper 0 (pred y) x (pred y)


next-code : Nat → Nat
next-code x = mod-nat (252533 * x) 33554393

next-pos : (Nat × Nat) → (Nat × Nat)
next-pos (x , y) with (x ==n 1)
next-pos (x , y) | true = (y + 1 , 1)
next-pos (x , y) | false = (x - 1 , y + 1)

pos-number : (Nat × Nat) → Nat
pos-number (x , y) = low-tri + y
  where
    diag : Nat
    diag = x + y - 1
    low-tri : Nat
    low-tri = div-nat (diag * diag - diag) 2

iter-up-to-pos-h : Nat → (Nat × Nat) → Nat → (Nat × Nat) → Nat
iter-up-to-pos-h 0 _ _ _ = 0
iter-up-to-pos-h (suc l) (x , y) code (tar-x , tar-y) with ((x ==n tar-x) ∧ (y ==n tar-y))
iter-up-to-pos-h (suc l) (x , y) code (tar-x , tar-y) | true = code
iter-up-to-pos-h (suc l) (x , y) code (tar-x , tar-y) | false = iter-up-to-pos-h l (next-pos (x , y)) (next-code code) (tar-x , tar-y)

iter-up-to-pos : (Nat × Nat) → Nat
iter-up-to-pos (x , y) = iter-up-to-pos-h (suc(pos-number (x , y))) (1 , 1) 20151125 (x , y)

find-big-code : String → String
find-big-code x = output ++ "\n"
  where
    inp : List Nat
    inp = (unmaybe ∘ (map (readMaybe 10)) ∘ lines) x
    output : String
    output with inp
    output | (x ∷ y ∷ _) = "sol: " ++ show (iter-up-to-pos (x , y))
    output | _ = "no sol"

test-next-code-a : next-code 20151125 ≡ 31916031
test-next-code-a = refl

test-next-code-b : next-code 31916031 ≡ 18749137
test-next-code-b = refl

test-next-code-c : next-code 18749137 ≡ 16080970
test-next-code-c = refl

test-next-pos-a : next-pos (1 , 1) ≡ (2 , 1)
test-next-pos-a = refl

test-next-pos-b : next-pos (2 , 1) ≡ (1 , 2)
test-next-pos-b = refl

test-next-pos-c : next-pos (1 , 2) ≡ (3 , 1)
test-next-pos-c = refl

test-next-pos-d : next-pos (3 , 1) ≡ (2 , 2)
test-next-pos-d = refl

test-pos-number-a : pos-number (1 , 1) ≡ 1
test-pos-number-a = refl

test-pos-number-b : pos-number (2 , 1) ≡ 2
test-pos-number-b = refl

test-pos-number-c : pos-number (1 , 2) ≡ 3
test-pos-number-c = refl

test-pos-number-d : pos-number (3 , 1) ≡ 4
test-pos-number-d = refl

test-pos-number-e : pos-number (2 , 2) ≡ 5
test-pos-number-e = refl

test-iter-up-to-pos : iter-up-to-pos (5 , 1) ≡ 77061
test-iter-up-to-pos = refl

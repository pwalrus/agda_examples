module d1.captcha where

open import util.list_stuff using (words ; lines ; unmaybe ; hard-unmaybe ; filterᵇ ; make-perms ; rem-dot ; append-front-all ; all-replacements ; cartproduct ; min-by-f ; enumerate ; list-minus ; conseq) renaming (trim to trim-ch)
open import util.lookup using (LookupStrTree ; LookupNatTree ; build-str-tree ; build-nat-tree ; has-val ; all-values ; all-keys ; all-kv ; LTPair) renaming (set-val to set-tree ; read-val to read-tree)
open import util.json using (readIntMaybe)
open import util.search using (search-rec-breadth-dedup ; branch-bound)
open import util.nat_stuff using (div-nat)
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


diag : (Char × Char) → Bool
diag (a , b) = a ==c b

add-last : {A : Set} → List A → List A
add-last [] = []
add-last (x ∷ xs) = concat ((x ∷ xs) ∷ (x ∷ []) ∷ [])

reverse-pairs : {A : Set} → List A → List (A × A)
reverse-pairs {A} xs = zip xs shuf
  where
    half : Nat
    half = div-nat (length xs) 2
    shuf : List A
    shuf = concat ((drop half xs) ∷ (take half xs)  ∷ [])


run-captcha : String → String
run-captcha = show ∘ foldr _+_ 0 ∘ unmaybe ∘ map (readMaybe 10) ∘ map fromChar ∘ map proj₁ ∘ filterᵇ diag ∘ conseq ∘ add-last ∘ trim-ch ∘ toList

run-captcha-half : String → String
run-captcha-half = show ∘ foldr _+_ 0 ∘ unmaybe ∘ map (readMaybe 10) ∘ map fromChar ∘ map proj₁ ∘ filterᵇ diag ∘ reverse-pairs ∘ trim-ch ∘ toList


test-run-captcha-a : run-captcha "1122" ≡ "3"
test-run-captcha-a = refl

test-run-captcha-b : run-captcha "1111" ≡ "4"
test-run-captcha-b = refl

test-run-captcha-c : run-captcha "1234" ≡ "0"
test-run-captcha-c = refl

test-run-captcha-d : run-captcha "91212129" ≡ "9"
test-run-captcha-d = refl

test-run-captcha-half-a : run-captcha-half "1212" ≡ "6"
test-run-captcha-half-a = refl

test-run-captcha-half-b : run-captcha-half "1221" ≡ "0"
test-run-captcha-half-b = refl

test-run-captcha-half-c : run-captcha-half "123425" ≡ "4"
test-run-captcha-half-c = refl

test-run-captcha-half-d : run-captcha-half "123123" ≡ "12"
test-run-captcha-half-d = refl

test-run-captcha-half-e : run-captcha-half "12131415" ≡ "4"
test-run-captcha-half-e = refl

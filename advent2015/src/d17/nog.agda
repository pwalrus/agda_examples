module d17.nog where

open import util.list_stuff using (words ; lines ; unmaybe ; filterᵇ ; make-perms ; rem-dot)
open import util.lookup using (LookupStrTree ; build-str-tree ; has-val ; set-val ; all-values ; LTPair) renaming (read-val to read-tree)
open import util.json using (readIntMaybe)
open import Data.Tree.Binary using (leaf ; node)
open import Agda.Builtin.String using (String)
open import Data.String.Base using (toList ; fromList ; _++_ ; unlines ; intersperse)
open import Data.String.Properties using (_==_ ; _<?_)
open import Agda.Builtin.Nat using (Nat ; suc ; _<_ ; _+_) renaming (_==_ to _==n_ ; _-_ to nat-diff)
open import Data.Nat.Show using (show ; readMaybe)
open import Agda.Builtin.Int using (Int ; pos ; negsuc)
open import Data.Integer.Properties using (_≟_)
open import Agda.Builtin.List using (List ; [] ; _∷_)
open import Data.List using (map ; foldr ; concat ; length ; zip)
open import Agda.Builtin.Char using (Char)
open import Agda.Builtin.Bool using (Bool ; true ; false)
open import Data.Bool.Base using (if_then_else_)
open import Agda.Builtin.Maybe using (Maybe ; nothing ; just)
open import Function.Base using (_∘_)
open import Data.Product using (_×_ ; _,_ ; proj₁ ; proj₂)
open import Agda.Builtin.Equality using (refl ; _≡_)
open import Relation.Nullary.Decidable using (isYes)

append-front-all : {A : Set} → A → List (List A) → List (List A)
append-front-all x inp = map (λ {q → x ∷ q}) inp

make-subs : Nat → List (List Bool)
make-subs 0 = [] ∷ []
make-subs (suc p) = concat (append-front-all false (make-subs p) ∷ append-front-all true (make-subs p) ∷ [])

show-sub : List Bool → String
show-sub [] = ""
show-sub (false ∷ xs) = "0" ++ show-sub xs
show-sub (true ∷ xs) = "1" ++ show-sub xs

eval-sub :  List Bool → List Nat → Nat
eval-sub sub sizes = comb
  where
    pairs : List (Bool × Nat)
    pairs = zip sub sizes
    comb : Nat
    comb = ((foldr _+_ 0) ∘ (map proj₂) ∘ (filterᵇ proj₁)) pairs

cardinality-sub : List Bool → Nat
cardinality-sub = (foldr _+_ 0) ∘ map (λ {q → if q then 1 else 0})

divide-nog : String → String
divide-nog x = "sol: " ++ (show ∘ length ) same-as-smallest ++ "\n"
  where
    sizes : List Nat
    sizes = (unmaybe ∘ (map (readMaybe 10)) ∘ lines) x
    subs : List (List Bool)
    subs = make-subs (length sizes)
    evaled : List (Nat × Nat)
    evaled = map (λ {q → cardinality-sub q , eval-sub q sizes}) subs
    sized : List (Nat × Nat)
    sized = (filterᵇ (λ {q → proj₂ q ==n 150})) evaled
    smallest : Nat
    smallest = foldr (λ {q r → if q < r then q else r}) (length sizes) (map proj₁ sized)
    same-as-smallest : List (Nat × Nat)
    same-as-smallest = (filterᵇ (λ {q → proj₁ q ==n smallest})) sized
    

test-make-subs : (unlines ∘ (map show-sub) ∘ make-subs) 3 ≡ "000\n001\n010\n011\n100\n101\n110\n111"
test-make-subs = refl

--test-divide-nog : divide-nog "20\n15\n10\n5\n5" ≡ "sol: 4\n"
--test-divide-nog = refl


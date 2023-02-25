module d16.mfcsam where

open import util.list_stuff using (words ; lines ; unmaybe ; filterᵇ ; make-perms ; rem-dot)
open import util.lookup using (LookupStrTree ; build-str-tree ; has_val ; set_val ; all_values ; LTPair) renaming (read_val to read-tree)
open import util.json using (readIntMaybe)
open import Data.Tree.Binary using (leaf ; node)
open import Agda.Builtin.String using (String)
open import Data.String.Base using (toList ; fromList ; _++_ ; unlines ; intersperse)
open import Data.String.Properties using (_==_ ; _<?_)
open import Agda.Builtin.Nat using (Nat ; suc ; _<_) renaming (_==_ to _==n_ ; _-_ to nat-diff)
open import Data.Nat.Show using (show ; readMaybe)
open import Agda.Builtin.Int using (Int ; pos ; negsuc)
open import Data.Integer.Base using (_+_ ; _*_ ; _≤ᵇ_)
open import Data.Integer.Show renaming (show to showz)
open import Data.Integer.Properties using (_≟_)
open import Agda.Builtin.List using (List ; [] ; _∷_)
open import Data.List using (map ; foldr ; concat ; length ; zip)
open import Agda.Builtin.Char using (Char)
open import Agda.Builtin.Bool using (Bool ; true ; false)
open import Data.Bool.Base using (if_then_else_ ; _∨_ ; _∧_)
open import Agda.Builtin.Maybe using (Maybe ; nothing ; just)
open import Function.Base using (_∘_)
open import Data.Product using (_×_ ; _,_ ; proj₁ ; proj₂)
open import Agda.Builtin.Equality using (refl ; _≡_)
open import Relation.Nullary.Decidable using (isYes)


data Sue : Set where
  sue : Nat → List (String × Nat) → Sue

show-sue : Sue → String
show-sue (sue id ps) = "Sue " ++ show id

rem-colon : String → String
rem-colon = fromList ∘ (rem-dot ':') ∘ toList

rem-comma : String → String
rem-comma = fromList ∘ (rem-dot ',') ∘ toList

parse-pairs : List String → Maybe (List (String × Nat))
parse-pairs [] = just []
parse-pairs (x ∷ y ∷ xs) with (parse-pairs xs)
parse-pairs (x ∷ y ∷ xs) | nothing = nothing
parse-pairs (x ∷ y ∷ xs) | (just ys) with (((readMaybe 10) ∘ rem-comma) y)
parse-pairs (x ∷ y ∷ xs) | (just ys) | nothing = nothing
parse-pairs (x ∷ y ∷ xs) | (just ys) | (just amount) = just( ((rem-colon x , amount)) ∷ ys)
parse-pairs _ = nothing

parse-line-w : List String → Maybe Sue
parse-line-w ("Sue" ∷ num ∷ xs) with (((readMaybe 10) ∘ rem-colon) num)
parse-line-w ("Sue" ∷ num ∷ xs) | nothing = nothing
parse-line-w ("Sue" ∷ num ∷ xs) | (just id) with (parse-pairs xs)
parse-line-w ("Sue" ∷ num ∷ xs) | (just id) | nothing = just (sue 0 [])
parse-line-w ("Sue" ∷ num ∷ xs) | (just id) | just (pairs) = just (sue id pairs)
parse-line-w _ = nothing

parse-line : String → Maybe Sue
parse-line = parse-line-w ∘ words

known-stats : LookupStrTree Nat
known-stats = build-str-tree (
  ("children" , 3) ∷ 
  ("cats" , 7) ∷ 
  ("samoyeds" , 2) ∷ 
  ("pomeranians" , 3) ∷ 
  ("akitas" , 0) ∷ 
  ("vizslas" , 0) ∷ 
  ("goldfish" , 5) ∷ 
  ("trees" , 3) ∷ 
  ("cars" , 2) ∷ 
  ("perfumes" , 1) ∷ [])

pair-valid : (Maybe Nat × Nat) → Bool
pair-valid (nothing , _) = true
pair-valid ((just x) , y) = x ==n y

pair-valid-b : (String × (Maybe Nat × Nat)) → Bool
pair-valid-b ("cats" , (nothing , _)) = true
pair-valid-b ("cats" , ((just x) , y)) = x < y
pair-valid-b ("trees" , (nothing , _)) = true
pair-valid-b ("trees" , ((just x) , y)) = x < y
pair-valid-b ("pomeranians" , (nothing , _)) = true
pair-valid-b ("pomeranians" , ((just x) , y)) = y < x
pair-valid-b ("goldfish" , (nothing , _)) = true
pair-valid-b ("goldfish" , ((just x) , y)) = y < x
pair-valid-b (_ , (x , y)) = pair-valid (x , y)

check-sue : LookupStrTree Nat → Sue → Bool
check-sue db (sue _ inp) = foldr _∧_ true (map pair-valid matches)
  where
    matches : List (Maybe Nat × Nat)
    matches = map (λ {q → read-tree (proj₁ q) db , (proj₂ q)}) inp

check-sue-b : LookupStrTree Nat → Sue → Bool
check-sue-b db (sue _ inp) = foldr _∧_ true (map pair-valid-b matches)
  where
    matches : List (String × (Maybe Nat × Nat))
    matches = map (λ {q → (proj₁ q) , (read-tree (proj₁ q) db , (proj₂ q))}) inp

find-sue : String → String
find-sue x = (unlines ∘ (map show-sue)) m_sues ++ "\n"
  where
    sues : List Sue
    sues = (unmaybe ∘ (map parse-line) ∘ lines) x
    m_sues : List Sue
    m_sues = filterᵇ (check-sue-b known-stats) sues

test-parse-line : parse-line "Sue 462: pomeranians: 6, cats: 2, perfumes: 6" ≡ just ( sue 462 (("pomeranians" , 6) ∷ ("cats" , 2) ∷ ("perfumes" , 6) ∷ []) )
test-parse-line = refl

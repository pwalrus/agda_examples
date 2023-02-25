module d15.cookie where

open import util.list_stuff using (words ; lines ; unmaybe ; filterᵇ ; make-perms ; rem-dot)
open import util.lookup using (LookupTree ; build_tree ; has_val ; set_val ; all_values ; LTPair) renaming (read_val to read_tree)
open import util.json using (readIntMaybe)
open import Data.Tree.Binary using (leaf ; node)
open import Agda.Builtin.String using (String)
open import Data.String.Base using (toList ; fromList ; _++_ ; unlines ; intersperse)
open import Data.String.Properties using (_==_ ; _<?_)
open import Agda.Builtin.Nat using (Nat ; suc ) renaming (_==_ to _==n_ ; _-_ to nat-diff)
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


data RecVec : Set where
  cookie : String → Int → Int → Int → Int → Int → RecVec

scalar-vec : Int → RecVec → RecVec
scalar-vec q (cookie name a b c d e) = cookie name (q * a) (q * b) (q * c) (q * d) (q * e)

add-vec : RecVec → RecVec → RecVec
add-vec (cookie name a b c d e) (cookie qname qa qb qc qd qe) =
  (cookie "Mixed" (a + qa) (b + qb) (c + qc) (d + qd) (e + qe))

is-pos : Int → Bool
is-pos (pos _) = true
is-pos _ = false

eval-cookie : RecVec → Int
eval-cookie (cookie _ a b c d e) with ((is-pos a) ∧ (is-pos b) ∧ (is-pos c) ∧ (is-pos d) ∧ (is-pos e))
eval-cookie (cookie _ a b c d e) | true = a * b * c * d 
eval-cookie (cookie _ a b c d e) | false = pos 0

eval-cookie-five : RecVec → Int
eval-cookie-five (cookie _ a b c d e) with ((is-pos a) ∧ (is-pos b) ∧ (is-pos c) ∧ (is-pos d) ∧ isYes(e ≟ (pos 500)))
eval-cookie-five (cookie _ a b c d e) | true = a * b * c * d 
eval-cookie-five (cookie _ a b c d e) | false = pos 0

default-cookie : RecVec
default-cookie = (cookie "Missing" (pos 0) (pos 0) (pos 0) (pos 0) (pos 0))

combine : List Int → List RecVec → RecVec
combine [] _ = default-cookie
combine _ [] = default-cookie
combine ratio ing = foldr add-vec default-cookie scaled
  where
    pairs : List (Int × RecVec)
    pairs = zip ratio ing
    scaled : List RecVec
    scaled = map (λ {p → scalar-vec (proj₁ p) (proj₂ p)}) pairs

parse-three-int : String → String → String → Maybe (Int × Int × Int)
parse-three-int x y z with (readIntMaybe (toList x))
parse-three-int x y z | (just rx) with (readIntMaybe (toList y))
parse-three-int x y z | (just rx) | (just ry) with (readIntMaybe (toList z))
parse-three-int x y z | (just rx) | (just ry) | (just rz) = just (rx , ry , rz)
parse-three-int x y z | (just rx) | (just ry) | nothing = nothing
parse-three-int x y z | (just rx) | nothing = nothing
parse-three-int x y z | nothing = nothing

parse-four : String → String → String → String → Maybe (Int × Int × Int × Int)
parse-four a b c d with (readIntMaybe (toList a))
parse-four a b c d | nothing = nothing
parse-four a b c d | just (ra) with (parse-three-int b c d)
parse-four a b c d | just (ra) | nothing = nothing
parse-four a b c d | just (ra) | (just (rb , rc , rd)) = just (ra , rb , rc , rd)

parse-five : String → String → String → String → String → Maybe (Int × Int × Int × Int × Int)
parse-five a b c d e with (readIntMaybe (toList a))
parse-five a b c d e | nothing = nothing
parse-five a b c d e | just (ra) with (parse-four b c d e)
parse-five a b c d e | just (ra) | nothing = nothing
parse-five a b c d e | just (ra) | (just (rb , rc , rd , re)) = just (ra , rb , rc , rd , re)

rem-colon : String → String
rem-colon = fromList ∘ (rem-dot ':') ∘ toList

rem-comma : String → String
rem-comma = fromList ∘ (rem-dot ',') ∘ toList

parse-line-w : List String → Maybe RecVec
parse-line-w (name ∷ "capacity" ∷ cap ∷ "durability" ∷ dur ∷ "flavor" ∷ fla ∷ "texture" ∷ tex ∷ "calories" ∷ cal ∷ _) with (parse-five (rem-comma cap) (rem-comma dur) (rem-comma fla) (rem-comma tex) (rem-comma cal))
parse-line-w (name ∷ "capacity" ∷ cap ∷ "durability" ∷ dur ∷ "flavor" ∷ fla ∷ "texture" ∷ tex ∷ "calories" ∷ cal ∷ _) | nothing = nothing
parse-line-w (name ∷ "capacity" ∷ cap ∷ "durability" ∷ dur ∷ "flavor" ∷ fla ∷ "texture" ∷ tex ∷ "calories" ∷ cal ∷ _) | (just (a , b , c , d , e)) = just (cookie (rem-colon name) a b c d e)
parse-line-w _ = nothing

parse-line : String → Maybe RecVec
parse-line = parse-line-w ∘ words

append-front-all : {A : Set} → A → List (List A) → List (List A)
append-front-all x inp = map (λ {q → x ∷ q}) inp

nat-range : Nat → List Nat
nat-range 0 = 0 ∷ []
nat-range (suc n) = (suc n) ∷ (nat-range n)

make-ratios : Nat → Nat → List (List Int)
make-ratios _ 0 = []
make-ratios rem 1 = ((pos rem) ∷ []) ∷ []
make-ratios 0 (suc dim) = append-front-all (pos 0) (make-ratios 0 dim)
make-ratios (suc rem) (suc dim) = concat rec-res
  where
    range : List Nat
    range = nat-range (suc rem)
    rec-res : List (List (List Int))
    rec-res = map (λ {q → append-front-all (pos q) (make-ratios (nat-diff (suc rem) q) dim) }) range

show-rat : List Int → String
show-rat x = intersperse ", " (map showz x)

show-rats : List (List Int) → String
show-rats x = unlines (map show-rat x)

max-score-h : (RecVec → Int) → (Int × List Int) → List (List Int) → List RecVec → (Int × List Int)
max-score-h eval (hs , best) [] _ = (hs , best)
max-score-h eval (hs , best) (x ∷ xs) ing = max-score-h eval new-pair xs ing
  where
    new-score : Int
    new-score = eval (combine x ing)
    new-pair : (Int × List Int)
    new-pair = if (new-score ≤ᵇ hs) then (hs , best) else (new-score , x)

max-score : List (List Int) → List RecVec → (Int × List Int)
max-score ratios ing = max-score-h eval-cookie-five ((pos 0) , []) ratios ing

best-cookie : String → String
best-cookie x = "len: " ++ (show (length ing)) ++ "," ++ show-rat (proj₂ found) ++ " = " ++ showz (proj₁ found) ++ "\n"
  where
    ing : List RecVec
    ing = (unmaybe ∘ (map parse-line) ∘ lines) x
    ratios : List (List Int)
    ratios = make-ratios 100 (length ing)
    found : (Int × List Int)
    found = max-score ratios ing

test-parse-line : parse-line "Butterscotch: capacity -1, durability -2, flavor 6, texture 3, calories 8" ≡ just (cookie "Butterscotch" (negsuc 0) (negsuc 1) (pos 6) (pos 3) (pos 8))
test-parse-line = refl

test-make-ratios : show-rats (make-ratios 2 2) ≡ "2, 0\n1, 1\n0, 2"
test-make-ratios = refl

test-combine-a : combine ((pos 44) ∷ (pos 56) ∷ []) (unmaybe ((parse-line "Butterscotch: capacity -1, durability -2, flavor 6, texture 3, calories 8") ∷ (parse-line "Cinnamon: capacity 2, durability 3, flavor -2, texture -1, calories 3") ∷ [])) ≡ (cookie "Mixed" (pos 68) (pos 80) (pos 152) (pos 76) (pos 520))
test-combine-a = refl

test-eval-cookie : eval-cookie (combine ((pos 44) ∷ (pos 56) ∷ []) (unmaybe ((parse-line "Butterscotch: capacity -1, durability -2, flavor 6, texture 3, calories 8") ∷ (parse-line "Cinnamon: capacity 2, durability 3, flavor -2, texture -1, calories 3") ∷ []))) ≡ (pos 62842880)
test-eval-cookie = refl

test-search : best-cookie "Butterscotch: capacity -1, durability -2, flavor 6, texture 3, calories 8\nCinnamon: capacity 2, durability 3, flavor -2, texture -1, calories 3" ≡ "len: 2,40, 60 = 57600000\n"
test-search = refl

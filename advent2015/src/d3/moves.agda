module d3.moves where

open import Data.Bool.Base using (if_then_else_)
open import Agda.Builtin.String using (String ; primStringToList)
open import Agda.Builtin.List using (List ; _∷_ ; [])
open import Agda.Builtin.Char using (Char)
open import Agda.Builtin.Bool using (Bool)
open import Data.Bool.Base using (_∧_)
open import Agda.Builtin.Nat using (Nat ; suc)
open import Data.Nat.Show using (show)
open import Agda.Builtin.Int using (Int ; pos)
open import Data.Integer.Properties using (_≟_)
open import Data.Integer.Base using (_+_ ; _-_)
open import Relation.Nullary.Decidable.Core using (isYes)
open import Agda.Builtin.Equality using (refl ; _≡_)

record Location : Set where
   field
     x : Int
     y : Int

z-eq : Int → Int → Bool
z-eq a b = isYes (a ≟ b) 

loc-eq : Location → Location → Bool
loc-eq la lb = (z-eq (Location.x la) (Location.x lb)) ∧ (z-eq (Location.y la) (Location.y lb))

move-loc : Char → Location → Location
move-loc '<' loc = record { x = (Location.x loc) - pos 1 ; y = (Location.y loc) }
move-loc '>' loc = record { x = (Location.x loc) + pos 1 ; y = (Location.y loc) }
move-loc '^' loc = record { x = (Location.x loc) ; y = (Location.y loc) + pos 1 }
move-loc 'v' loc = record { x = (Location.x loc) ; y = (Location.y loc) - pos 1 }
move-loc _ loc = loc

list-len : {A : Set} → List A -> Nat
list-len [] = 0
list-len (x ∷ xs) = suc (list-len xs)

unique-insert-loc : List Location → Location → List Location
unique-insert-loc [] l = l ∷ []
unique-insert-loc (x ∷ xs) l = if (loc-eq x l)
   then x ∷ xs
   else x ∷ (unique-insert-loc xs l)

start-loc : Location
start-loc = record { x = pos 0 ; y = pos 0 }

add-next-move : Location → List Location → Char → List Location
add-next-move current hist mov = unique-insert-loc hist (move-loc mov current)

add-all-moves : List Char → Location → List Location → List Location
add-all-moves [] current hist = hist
add-all-moves (x ∷ xs) current hist = add-all-moves xs (move-loc x current) (add-next-move current hist x)

calc-unique-loc : String → String
calc-unique-loc x = show (list-len (add-all-moves (primStringToList x) start-loc (start-loc ∷ [])))

test-calc-unique-loc-a :  calc-unique-loc ">" ≡ "2"
test-calc-unique-loc-a = refl

test-calc-unique-loc-b :  calc-unique-loc "^>v<" ≡ "4"
test-calc-unique-loc-b = refl

test-calc-unique-loc-c :  calc-unique-loc "^v^v^v^v^v" ≡ "2"
test-calc-unique-loc-c = refl

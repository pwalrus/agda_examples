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

record Location : Set where
   field
     x : Int
     y : Int

z_eq : Int → Int → Bool
z_eq a b = isYes (a ≟ b) 

loc_eq : Location → Location → Bool
loc_eq la lb = (z_eq (Location.x la) (Location.x lb)) ∧ (z_eq (Location.y la) (Location.y lb))

move_loc : Char → Location → Location
move_loc '<' loc = record { x = (Location.x loc) - pos 1 ; y = (Location.y loc) }
move_loc '>' loc = record { x = (Location.x loc) + pos 1 ; y = (Location.y loc) }
move_loc '^' loc = record { x = (Location.x loc) ; y = (Location.y loc) + pos 1 }
move_loc 'v' loc = record { x = (Location.x loc) ; y = (Location.y loc) - pos 1 }
move_loc _ loc = loc

list_len : {A : Set} → List A -> Nat
list_len [] = 0
list_len (x ∷ xs) = suc (list_len xs)

unique_insert_loc : List Location → Location → List Location
unique_insert_loc [] l = l ∷ []
unique_insert_loc (x ∷ xs) l = if (loc_eq x l)
   then x ∷ xs
   else x ∷ (unique_insert_loc xs l)

start_loc : Location
start_loc = record { x = pos 0 ; y = pos 0 }

add_next_move : Location → List Location → Char → List Location
add_next_move current hist mov = unique_insert_loc hist (move_loc mov current)

add_all_moves : List Char → Location → List Location → List Location
add_all_moves [] current hist = hist
add_all_moves (x ∷ xs) current hist = add_all_moves xs (move_loc x current) (add_next_move current hist x)



calc_unique_loc : String → String
calc_unique_loc x = show (list_len (add_all_moves (primStringToList x) start_loc (start_loc ∷ [])))

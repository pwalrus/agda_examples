module d6.brights where

open import d2.boxes using (find_parts ; parse_nat)
open import Data.Bool.Base using (if_then_else_ ; _∧_ ; not)
open import Agda.Builtin.List using (List ; [] ; _∷_)
open import Data.List using (map ; foldr)
open import Agda.Builtin.Nat using (Nat ; suc ; _<_ ; _==_ ; _-_)
open import Data.Nat.Show using (show)
open import Data.Nat using (_+_)
open import Agda.Builtin.Bool using (Bool ; true ; false)
open import Agda.Builtin.Char using (Char)
open import Agda.Builtin.String using (String ; primStringToList; primStringFromList)
open import Data.String using (_++_)
open import Agda.Builtin.Equality using (refl ; _≡_)
open import d6.lights using (parse_line ; show_inst ; NatPair ; n_pair ; Inst ; tog ; tof ; ton)

populate_empty_row : Nat → List Nat
populate_empty_row 0 = []
populate_empty_row (suc p) = 0 ∷ (populate_empty_row p)

populate_empty : Nat → Nat → List (List Nat)
populate_empty 0 width = []
populate_empty (suc p) width = (populate_empty_row width) ∷ (populate_empty p width)

show_row : List Nat → String
show_row inp = foldr _++_ "" (map show inp)

show_two_list : List (List Nat) → String
show_two_list inp = foldr _++_ "" (map (λ {x → (show_row x) ++ ";"}) inp)

manip_row : (Nat → Nat) → NatPair → NatPair → List Nat → List Nat
manip_row _ _ _ [] = []
manip_row _ (n_pair _ _) (n_pair 0 _) (h ∷ t) = h ∷ t
manip_row f (n_pair 1 _) (n_pair 1 _) (h ∷ j ∷ t) = h ∷ (f j) ∷ t
manip_row f (n_pair 0 _) (n_pair 1 _) (h ∷ j ∷ t) = (f h) ∷ (f j) ∷ t
manip_row f (n_pair 0 _) (n_pair (suc m) _) (h ∷ t) =
  (f h) ∷ (manip_row f (n_pair 0 0) (n_pair m 0) (t))
manip_row f (n_pair (suc p) _) (n_pair (suc m) _) (h ∷ t) =
  h ∷ (manip_row f (n_pair p 0) (n_pair m 0) (t))

turn_on_row : NatPair → NatPair → List Nat → List Nat
turn_on_row p q row = manip_row (λ {x → x + 1}) p q row

turn_off_row : NatPair → NatPair → List Nat → List Nat
turn_off_row p q row = manip_row (λ {x → x - 1}) p q row

toggle_row : NatPair → NatPair → List Nat → List Nat
toggle_row p q row = manip_row (λ {x → x + 2}) p q row

is_vert_match : Nat → NatPair → NatPair → Bool
is_vert_match idx (n_pair a b) (n_pair x y) = if ((b < (suc idx)) ∧ (idx < (suc y)))
  then true
  else false

apply_inst_row : Nat → Inst → List Nat → List Nat
apply_inst_row idx (ton p q) row = if (is_vert_match idx p q) then (turn_on_row p q row) else row
apply_inst_row idx (tof p q) row = if (is_vert_match idx p q) then (turn_off_row p q row) else row
apply_inst_row idx (tog p q) row = if (is_vert_match idx p q) then (toggle_row p q row) else row
apply_inst_row _ _ row = row

apply_inst : Nat → Inst → List (List Nat) → List (List Nat)
apply_inst idx inst [] = []
apply_inst idx inst (x ∷ xs) = (apply_inst_row idx inst x) ∷ (apply_inst (suc idx) inst xs)

apply_many : List Inst → List (List Nat) → List (List Nat)
apply_many [] start = start
apply_many (x ∷ xs) start = apply_many xs (apply_inst 0 x start)

count_on :  List (List Nat) → Nat
count_on inp = foldr _+_ 0 (map (λ {x → (foldr _+_ 0 x)} ) inp)

test_show_two_tog_count : (count_on (apply_inst 0 (tog (n_pair 1 1) (n_pair 2 2)) (populate_empty 3 3))) ≡ 8
test_show_two_tog_count = refl


lights_on : String → String
lights_on x = show (count_on (apply_many (map parse_line (find_parts '\n' (primStringToList x))) (populate_empty 1000 1000)))

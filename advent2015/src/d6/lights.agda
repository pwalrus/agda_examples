module d6.lights where

open import d5.nice_word using (n_bool)
open import d2.boxes using (find_parts ; parse_nat)
open import Data.Bool.Base using (if_then_else_ ; _∧_ ; not)
open import Agda.Builtin.List using (List ; [] ; _∷_)
open import Data.List using (map ; foldr)
open import Agda.Builtin.Nat using (Nat ; suc ; _<_ ; _==_)
open import Data.Nat.Show using (show)
open import Data.Nat using (_+_)
open import Agda.Builtin.Bool using (Bool ; true ; false)
open import Agda.Builtin.Char using (Char)
open import Agda.Builtin.String using (String ; primStringToList; primStringFromList)
open import Data.String using (_++_)
-- open import Data.String.Properties renaming (_==_ to _==s_)
open import Agda.Builtin.Equality using (refl ; _≡_)

populate_empty_row : Nat → List Bool
populate_empty_row 0 = []
populate_empty_row (suc n) = false ∷ (populate_empty_row n)

populate_empty : Nat → Nat → List (List Bool)
populate_empty 0 width = []
populate_empty (suc n) width = (populate_empty_row width) ∷ (populate_empty n width)

show_row : List Bool → String
show_row inp = foldr _++_ "" (map show (map n_bool inp))

show_two_list : List (List Bool) → String
show_two_list inp = foldr _++_ "" (map (λ {x → (show_row x) ++ ";"}) inp)

data NatPair : Set where
  n_pair : Nat → Nat → NatPair

show_np : NatPair → String
show_np (n_pair x y) = (show x) ++ "," ++ (show y)

data Inst : Set where
  ton : NatPair → NatPair → Inst
  tog : NatPair → NatPair → Inst
  tof : NatPair → NatPair → Inst
  nope : Inst

show_inst : Inst → String
show_inst (ton p q) = "turn on " ++ (show_np p) ++ " through " ++ (show_np q)
show_inst (tog p q) = "toggle " ++ (show_np p) ++ " through " ++ (show_np q)
show_inst (tof p q) = "turn off " ++ (show_np p) ++ " through " ++ (show_np q)
show_inst _ = "nope"

manip_row : (Bool → Bool) → NatPair → NatPair → List Bool → List Bool
manip_row _ _ _ [] = []
manip_row _ (n_pair _ _) (n_pair 0 _) (h ∷ t) = h ∷ t
manip_row f (n_pair 1 _) (n_pair 1 _) (h ∷ j ∷ t) = h ∷ (f j) ∷ t
manip_row f (n_pair 0 _) (n_pair 1 _) (h ∷ j ∷ t) = (f h) ∷ (f j) ∷ t
manip_row f (n_pair 0 _) (n_pair (suc m) _) (h ∷ t) =
  (f h) ∷ (manip_row f (n_pair 0 0) (n_pair m 0) (t))
manip_row f (n_pair (suc p) _) (n_pair (suc m) _) (h ∷ t) =
  h ∷ (manip_row f (n_pair p 0) (n_pair m 0) (t))

turn_on_row : NatPair → NatPair → List Bool → List Bool
turn_on_row p q row = manip_row (λ {x → true}) p q row

turn_off_row : NatPair → NatPair → List Bool → List Bool
turn_off_row p q row = manip_row (λ {x → false}) p q row

toggle_row : NatPair → NatPair → List Bool → List Bool
toggle_row p q row = manip_row (λ {x → not x}) p q row

is_vert_match : Nat → NatPair → NatPair → Bool
is_vert_match idx (n_pair a b) (n_pair x y) = if ((b < (suc idx)) ∧ (idx < (suc y)))
  then true
  else false

apply_inst_row : Nat → Inst → List Bool → List Bool
apply_inst_row idx (ton p q) row = if (is_vert_match idx p q) then (turn_on_row p q row) else row
apply_inst_row idx (tof p q) row = if (is_vert_match idx p q) then (turn_off_row p q row) else row
apply_inst_row idx (tog p q) row = if (is_vert_match idx p q) then (toggle_row p q row) else row
apply_inst_row _ _ row = row

apply_inst : Nat → Inst → List (List Bool) → List (List Bool)
apply_inst idx inst [] = []
apply_inst idx inst (x ∷ xs) = (apply_inst_row idx inst x) ∷ (apply_inst (suc idx) inst xs)

add_to_first : Char → List (List Char) → List (List Char)
add_to_first ch (lst ∷ t) = (ch ∷ lst) ∷ t
add_to_first ch [] = (ch ∷ []) ∷ []

break_through : List Char → List (List Char)
break_through [] = [] ∷ []
break_through ('t' ∷ 'h' ∷ 'r' ∷ 'o' ∷ 'u' ∷ 'g' ∷ 'h' ∷ xs) = [] ∷ xs ∷ []
break_through (x ∷ xs)  = add_to_first x (break_through xs)

parse_n_pair_parts : List (List Char) → NatPair
parse_n_pair_parts (l ∷ r ∷ _) = n_pair (parse_nat 0 l) (parse_nat 0 r)
parse_n_pair_parts _ = n_pair 0 0

parse_n_pair : List Char → NatPair
parse_n_pair x = parse_n_pair_parts (find_parts ',' x)

mk_ton : List (List Char) → Inst
mk_ton (l ∷ r ∷ _) = ton (parse_n_pair l) (parse_n_pair r)
mk_ton _ = nope

mk_tof : List (List Char) → Inst
mk_tof (l ∷ r ∷ _) = tof (parse_n_pair l) (parse_n_pair r)
mk_tof _ = nope

mk_tog : List (List Char) → Inst
mk_tog (l ∷ r ∷ _) = tog (parse_n_pair l) (parse_n_pair r)
mk_tog _ = nope

parse_line : List Char → Inst
parse_line ('t' ∷ 'u' ∷ 'r' ∷ 'n' ∷ ' ' ∷ 'o' ∷ 'n' ∷ ' ' ∷ xs) = mk_ton (break_through xs)
parse_line ('t' ∷ 'u' ∷ 'r' ∷ 'n' ∷ ' ' ∷ 'o' ∷ 'f' ∷ 'f'  ∷  ' ' ∷ xs) = mk_tof (break_through xs)
parse_line ('t' ∷ 'o' ∷ 'g' ∷ 'g' ∷ 'l' ∷ 'e' ∷ ' ' ∷ xs) = mk_tog (break_through xs)
parse_line _ = nope

apply_many : List Inst → List (List Bool) → List (List Bool)
apply_many [] start = start
apply_many (x ∷ xs) start = apply_many xs (apply_inst 0 x start)

count_on_row : List Bool → Nat
count_on_row x = foldr _+_ 0 (map n_bool x)

count_on :  List (List Bool) → Nat
count_on inp = foldr _+_ 0 (map count_on_row inp)

test_show_np : (show_np (n_pair 4 5)) ≡ "4,5"
test_show_np = refl

test_show_inst : (show_inst (ton (n_pair 2 3) (n_pair 4 5))) ≡ "turn on 2,3 through 4,5"
test_show_inst = refl

test_show_two : (show_two_list (populate_empty 3 3)) ≡ "000;000;000;"
test_show_two = refl

test_show_two_on : (show_two_list (apply_inst 0 (ton (n_pair 1 1) (n_pair 2 2)) (populate_empty 3 3))) ≡ "000;011;011;"
test_show_two_on = refl

test_show_two_on_b : (show_two_list (apply_inst 0 (ton (n_pair 1 1) (n_pair 1 1)) (populate_empty 3 3))) ≡ "000;010;000;"
test_show_two_on_b = refl

test_show_two_off : (show_two_list (
  apply_many ((ton (n_pair 0 0) (n_pair 2 2)) ∷ (tof (n_pair 1 1) ((n_pair 1 1))) ∷ []) (populate_empty 3 3))) ≡ "111;101;111;"
test_show_two_off = refl

test_show_two_tog : (show_two_list (apply_inst 0 (tog (n_pair 1 1) (n_pair 2 2)) (populate_empty 3 3))) ≡ "000;011;011;"
test_show_two_tog = refl

test_show_two_tog_count : (count_on (apply_inst 0 (tog (n_pair 1 1) (n_pair 2 2)) (populate_empty 3 3))) ≡ 4
test_show_two_tog_count = refl

test_parse_ton : (show_inst (parse_line (primStringToList "turn on 1,2 through 3,4"))) ≡ "turn on 1,2 through 3,4"
test_parse_ton = refl

test_parse_tof : (show_inst (parse_line (primStringToList "turn off 1,2 through 5,6"))) ≡ "turn off 1,2 through 5,6"
test_parse_tof = refl

test_parse_tog : (show_inst (parse_line (primStringToList "toggle 3,4 through 7,8"))) ≡ "toggle 3,4 through 7,8"
test_parse_tog = refl


lights_on : String → String
lights_on x = show (count_on (apply_many (map parse_line (find_parts '\n' (primStringToList x))) (populate_empty 1000 1000)))

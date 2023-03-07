module d6.lights where

open import util.list_stuff using (find-parts)
open import Data.Bool.Base using (if_then_else_ ; _∧_ ; not)
open import Agda.Builtin.List using (List ; [] ; _∷_)
open import Data.List using (map ; foldr)
open import Agda.Builtin.Nat using (Nat ; suc ; _<_ ; _==_)
open import Data.Nat.Show using (show ; readMaybe)
open import Data.Nat using (_+_)
open import Agda.Builtin.Bool using (Bool ; true ; false)
open import Agda.Builtin.Char using (Char)
open import Agda.Builtin.String using (String ; primStringToList; primStringFromList)
open import Data.String using (_++_ ; fromList)
open import Agda.Builtin.Maybe using (Maybe ; just ; nothing)
open import Agda.Builtin.Equality using (refl ; _≡_)

n-bool : Bool → Nat
n-bool true = 1
n-bool false = 0

populate-empty-row : Nat → List Bool
populate-empty-row 0 = []
populate-empty-row (suc n) = false ∷ (populate-empty-row n)

populate-empty : Nat → Nat → List (List Bool)
populate-empty 0 width = []
populate-empty (suc n) width = (populate-empty-row width) ∷ (populate-empty n width)

show-row : List Bool → String
show-row inp = foldr _++_ "" (map show (map n-bool inp))

show-two-list : List (List Bool) → String
show-two-list inp = foldr _++_ "" (map (λ {x → (show-row x) ++ ";"}) inp)

data NatPair : Set where
  n-pair : Nat → Nat → NatPair

show-np : NatPair → String
show-np (n-pair x y) = (show x) ++ "," ++ (show y)

data Inst : Set where
  ton : NatPair → NatPair → Inst
  tog : NatPair → NatPair → Inst
  tof : NatPair → NatPair → Inst
  nope : Inst

show-inst : Inst → String
show-inst (ton p q) = "turn on " ++ (show-np p) ++ " through " ++ (show-np q)
show-inst (tog p q) = "toggle " ++ (show-np p) ++ " through " ++ (show-np q)
show-inst (tof p q) = "turn off " ++ (show-np p) ++ " through " ++ (show-np q)
show-inst _ = "nope"

manip-row : (Bool → Bool) → NatPair → NatPair → List Bool → List Bool
manip-row _ _ _ [] = []
manip-row _ (n-pair _ _) (n-pair 0 _) (h ∷ t) = h ∷ t
manip-row f (n-pair 1 _) (n-pair 1 _) (h ∷ j ∷ t) = h ∷ (f j) ∷ t
manip-row f (n-pair 0 _) (n-pair 1 _) (h ∷ j ∷ t) = (f h) ∷ (f j) ∷ t
manip-row f (n-pair 0 _) (n-pair (suc m) _) (h ∷ t) =
  (f h) ∷ (manip-row f (n-pair 0 0) (n-pair m 0) (t))
manip-row f (n-pair (suc p) _) (n-pair (suc m) _) (h ∷ t) =
  h ∷ (manip-row f (n-pair p 0) (n-pair m 0) (t))

turn-on-row : NatPair → NatPair → List Bool → List Bool
turn-on-row p q row = manip-row (λ {x → true}) p q row

turn-off-row : NatPair → NatPair → List Bool → List Bool
turn-off-row p q row = manip-row (λ {x → false}) p q row

toggle-row : NatPair → NatPair → List Bool → List Bool
toggle-row p q row = manip-row (λ {x → not x}) p q row

is-vert-match : Nat → NatPair → NatPair → Bool
is-vert-match idx (n-pair a b) (n-pair x y) = if ((b < (suc idx)) ∧ (idx < (suc y)))
  then true
  else false

apply-inst-row : Nat → Inst → List Bool → List Bool
apply-inst-row idx (ton p q) row = if (is-vert-match idx p q) then (turn-on-row p q row) else row
apply-inst-row idx (tof p q) row = if (is-vert-match idx p q) then (turn-off-row p q row) else row
apply-inst-row idx (tog p q) row = if (is-vert-match idx p q) then (toggle-row p q row) else row
apply-inst-row _ _ row = row

apply-inst : Nat → Inst → List (List Bool) → List (List Bool)
apply-inst idx inst [] = []
apply-inst idx inst (x ∷ xs) = (apply-inst-row idx inst x) ∷ (apply-inst (suc idx) inst xs)

add-to-first : Char → List (List Char) → List (List Char)
add-to-first ch (lst ∷ t) = (ch ∷ lst) ∷ t
add-to-first ch [] = (ch ∷ []) ∷ []

break-through : List Char → List (List Char)
break-through [] = [] ∷ []
break-through (' ' ∷ 't' ∷ 'h' ∷ 'r' ∷ 'o' ∷ 'u' ∷ 'g' ∷ 'h' ∷ ' ' ∷ xs) = [] ∷ xs ∷ []
break-through (x ∷ xs)  = add-to-first x (break-through xs)

parse-nat : List Char → Nat
parse-nat x with (readMaybe 10 (fromList x))
parse-nat x | nothing = 0
parse-nat x | (just y) = y

parse-n-pair-parts : List (List Char) → NatPair
parse-n-pair-parts (l ∷ r ∷ _) = n-pair (parse-nat l) (parse-nat r)
parse-n-pair-parts _ = n-pair 0 0

parse-n-pair : List Char → NatPair
parse-n-pair x = parse-n-pair-parts (find-parts ',' x)

mk-ton : List (List Char) → Inst
mk-ton (l ∷ r ∷ _) = ton (parse-n-pair l) (parse-n-pair r)
mk-ton _ = nope

mk-tof : List (List Char) → Inst
mk-tof (l ∷ r ∷ _) = tof (parse-n-pair l) (parse-n-pair r)
mk-tof _ = nope

mk-tog : List (List Char) → Inst
mk-tog (l ∷ r ∷ _) = tog (parse-n-pair l) (parse-n-pair r)
mk-tog _ = nope

parse-line : List Char → Inst
parse-line ('t' ∷ 'u' ∷ 'r' ∷ 'n' ∷ ' ' ∷ 'o' ∷ 'n' ∷ ' ' ∷ xs) = mk-ton (break-through xs)
parse-line ('t' ∷ 'u' ∷ 'r' ∷ 'n' ∷ ' ' ∷ 'o' ∷ 'f' ∷ 'f'  ∷  ' ' ∷ xs) = mk-tof (break-through xs)
parse-line ('t' ∷ 'o' ∷ 'g' ∷ 'g' ∷ 'l' ∷ 'e' ∷ ' ' ∷ xs) = mk-tog (break-through xs)
parse-line _ = nope

apply-many : List Inst → List (List Bool) → List (List Bool)
apply-many [] start = start
apply-many (x ∷ xs) start = apply-many xs (apply-inst 0 x start)

count-on-row : List Bool → Nat
count-on-row x = foldr _+_ 0 (map n-bool x)

count-on :  List (List Bool) → Nat
count-on inp = foldr _+_ 0 (map count-on-row inp)

test-show-np : (show-np (n-pair 4 5)) ≡ "4,5"
test-show-np = refl

test-show-inst : (show-inst (ton (n-pair 2 3) (n-pair 4 5))) ≡ "turn on 2,3 through 4,5"
test-show-inst = refl

test-show-two : (show-two-list (populate-empty 3 3)) ≡ "000;000;000;"
test-show-two = refl

test-show-two-on : (show-two-list (apply-inst 0 (ton (n-pair 1 1) (n-pair 2 2)) (populate-empty 3 3))) ≡ "000;011;011;"
test-show-two-on = refl

test-show-two-on_b : (show-two-list (apply-inst 0 (ton (n-pair 1 1) (n-pair 1 1)) (populate-empty 3 3))) ≡ "000;010;000;"
test-show-two-on_b = refl

test-show-two-off : (show-two-list (
  apply-many ((ton (n-pair 0 0) (n-pair 2 2)) ∷ (tof (n-pair 1 1) ((n-pair 1 1))) ∷ []) (populate-empty 3 3))) ≡ "111;101;111;"
test-show-two-off = refl

test-show-two-tog : (show-two-list (apply-inst 0 (tog (n-pair 1 1) (n-pair 2 2)) (populate-empty 3 3))) ≡ "000;011;011;"
test-show-two-tog = refl

test-show-two-tog_count : (count-on (apply-inst 0 (tog (n-pair 1 1) (n-pair 2 2)) (populate-empty 3 3))) ≡ 4
test-show-two-tog_count = refl


test-parse-n-pair : parse-n-pair (primStringToList "3,4") ≡ n-pair 3 4
test-parse-n-pair = refl

test-parse-ton : (show-inst (parse-line (primStringToList "turn on 1,2 through 3,4"))) ≡ "turn on 1,2 through 3,4"
test-parse-ton = refl

test-parse-tof : (show-inst (parse-line (primStringToList "turn off 1,2 through 5,6"))) ≡ "turn off 1,2 through 5,6"
test-parse-tof = refl

test-parse-tog : (show-inst (parse-line (primStringToList "toggle 3,4 through 7,8"))) ≡ "toggle 3,4 through 7,8"
test-parse-tog = refl


lights-on : String → String
lights-on x = show (count-on (apply-many (map parse-line (find-parts '\n' (primStringToList x))) (populate-empty 1000 1000)))

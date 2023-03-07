module d6.brights where

open import util.list_stuff using (find-parts)
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
open import d6.lights using (parse-line ; show-inst ; NatPair ; n-pair ; Inst ; tog ; tof ; ton)

populate-empty-row : Nat → List Nat
populate-empty-row 0 = []
populate-empty-row (suc p) = 0 ∷ (populate-empty-row p)

populate-empty : Nat → Nat → List (List Nat)
populate-empty 0 width = []
populate-empty (suc p) width = (populate-empty-row width) ∷ (populate-empty p width)

show-row : List Nat → String
show-row inp = foldr _++_ "" (map show inp)

show-two-list : List (List Nat) → String
show-two-list inp = foldr _++_ "" (map (λ {x → (show-row x) ++ ";"}) inp)

manip-row : (Nat → Nat) → NatPair → NatPair → List Nat → List Nat
manip-row _ _ _ [] = []
manip-row _ (n-pair _ _) (n-pair 0 _) (h ∷ t) = h ∷ t
manip-row f (n-pair 1 _) (n-pair 1 _) (h ∷ j ∷ t) = h ∷ (f j) ∷ t
manip-row f (n-pair 0 _) (n-pair 1 _) (h ∷ j ∷ t) = (f h) ∷ (f j) ∷ t
manip-row f (n-pair 0 _) (n-pair (suc m) _) (h ∷ t) =
  (f h) ∷ (manip-row f (n-pair 0 0) (n-pair m 0) (t))
manip-row f (n-pair (suc p) _) (n-pair (suc m) _) (h ∷ t) =
  h ∷ (manip-row f (n-pair p 0) (n-pair m 0) (t))

turn-on-row : NatPair → NatPair → List Nat → List Nat
turn-on-row p q row = manip-row (λ {x → x + 1}) p q row

turn-off-row : NatPair → NatPair → List Nat → List Nat
turn-off-row p q row = manip-row (λ {x → x - 1}) p q row

toggle-row : NatPair → NatPair → List Nat → List Nat
toggle-row p q row = manip-row (λ {x → x + 2}) p q row

is-vert-match : Nat → NatPair → NatPair → Bool
is-vert-match idx (n-pair a b) (n-pair x y) = if ((b < (suc idx)) ∧ (idx < (suc y)))
  then true
  else false

apply-inst-row : Nat → Inst → List Nat → List Nat
apply-inst-row idx (ton p q) row = if (is-vert-match idx p q) then (turn-on-row p q row) else row
apply-inst-row idx (tof p q) row = if (is-vert-match idx p q) then (turn-off-row p q row) else row
apply-inst-row idx (tog p q) row = if (is-vert-match idx p q) then (toggle-row p q row) else row
apply-inst-row _ _ row = row

apply-inst : Nat → Inst → List (List Nat) → List (List Nat)
apply-inst idx inst [] = []
apply-inst idx inst (x ∷ xs) = (apply-inst-row idx inst x) ∷ (apply-inst (suc idx) inst xs)

apply-many : List Inst → List (List Nat) → List (List Nat)
apply-many [] start = start
apply-many (x ∷ xs) start = apply-many xs (apply-inst 0 x start)

count-on :  List (List Nat) → Nat
count-on inp = foldr _+_ 0 (map (λ {x → (foldr _+_ 0 x)} ) inp)

test-show-two-tog-count : (count-on (apply-inst 0 (tog (n-pair 1 1) (n-pair 2 2)) (populate-empty 3 3))) ≡ 8
test-show-two-tog-count = refl


brights-on : String → String
brights-on x = show (count-on (apply-many (map parse-line (find-parts '\n' (primStringToList x))) (populate-empty 1000 1000)))

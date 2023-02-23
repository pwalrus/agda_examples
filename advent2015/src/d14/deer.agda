
module d14.deer where

open import util.list_stuff using (words ; lines ; unmaybe ; filterᵇ ; make-perms)
open import util.lookup using (LookupTree ; build_tree ; has_val ; set_val ; all_values ; LTPair) renaming (read_val to read_tree)
open import Data.Tree.Binary using (leaf ; node)
open import Agda.Builtin.String using (String)
open import Data.String.Base using (toList ; fromList ; _++_ ; unlines)
open import Data.String.Properties using (_==_ ; _<?_)
open import Agda.Builtin.Nat using (Nat ; _+_ ; _*_ ; _-_ ; suc ; _<_) renaming (_==_ to _==n_)
open import Data.Nat.Show using (show ; readMaybe)
open import Agda.Builtin.List using (List ; [] ; _∷_)
open import Data.List using (map ; foldr ; concat ; length)
open import Agda.Builtin.Char using (Char)
open import Agda.Builtin.Bool using (Bool ; true ; false)
open import Data.Bool.Base using (if_then_else_ ; _∨_ ; _∧_)
open import Agda.Builtin.Maybe using (Maybe ; nothing ; just)
open import Function.Base using (_∘_)
open import Data.Product using (_×_ ; _,_ ; proj₁)
open import Agda.Builtin.Equality using (refl ; _≡_)
open import Relation.Nullary.Decidable using (isYes)

data DeerRate : Set where
  deer : String → Nat → Nat → Nat → DeerRate

parse-three-int : String → String → String → Maybe (Nat × Nat × Nat)
parse-three-int x y z with (readMaybe 10 x)
parse-three-int x y z | (just rx) with (readMaybe 10 y)
parse-three-int x y z | (just rx) | (just ry) with (readMaybe 10 z)
parse-three-int x y z | (just rx) | (just ry) | (just rz) = just (rx , ry , rz)
parse-three-int x y z | (just rx) | (just ry) | nothing = nothing
parse-three-int x y z | (just rx) | nothing = nothing
parse-three-int x y z | nothing = nothing

parse-line-w : List String → Maybe DeerRate
parse-line-w (name ∷ "can" ∷ "fly" ∷ speed ∷ "km/s" ∷ "for" ∷ dur ∷ "seconds," ∷ "but" ∷ "then" ∷ "must" ∷ "rest" ∷ "for" ∷ rest ∷ _) with (parse-three-int speed dur rest)
parse-line-w (name ∷ "can" ∷ "fly" ∷ speed ∷ "km/s" ∷ "for" ∷ dur ∷ "seconds," ∷ "but" ∷ "then" ∷ "must" ∷ "rest" ∷ "for" ∷ rest ∷ _) | (just (x , y , z)) = just (deer name x y z)
parse-line-w (name ∷ "can" ∷ "fly" ∷ speed ∷ "km/s" ∷ "for" ∷ dur ∷ "seconds," ∷ "but" ∷ "then" ∷ "must" ∷ "rest" ∷ "for" ∷ rest ∷ _) | nothing = nothing
parse-line-w _ = nothing

parse-line : String → Maybe DeerRate
parse-line = parse-line-w ∘ words

min-nat : Nat → Nat → Nat
min-nat x y = if (x < y) then x else y

calc-dist-h : Nat → DeerRate → Nat → Nat
calc-dist-h 0 _ _ = 0
calc-dist-h (suc l) (deer name speed dur rest) aftert with (dur + rest < aftert)
calc-dist-h (suc l) (deer name speed dur rest) aftert | true =
  (speed * dur) + (calc-dist-h l (deer name speed dur rest) (aftert - dur - rest))
calc-dist-h (suc l) (deer name speed dur rest) aftert | false = (speed * (min-nat aftert dur))

calc-dist : DeerRate → Nat → Nat
calc-dist d x = calc-dist-h x d x

show-score : Nat → DeerRate → String
show-score d (deer name speed dur rest) = name ++ ": " ++ show (calc-dist (deer name speed dur rest) d)

top-deer-h : List (String × Nat) → List DeerRate → Nat → List (String × Nat)
top-deer-h [] [] _ = []
top-deer-h xs [] _ = xs
top-deer-h [] ((deer new-name speed dur rest) ∷ xs) d = top-deer-h ((new-name , new-score) ∷ []) xs d
  where
    new-score : Nat
    new-score = calc-dist (deer new-name speed dur rest) d
top-deer-h ((name , score) ∷ ys) ((deer new-name speed dur rest) ∷ xs) d = top-deer-h next-pairs xs d
  where
    new-score : Nat
    new-score = calc-dist (deer new-name speed dur rest) d
    next-pairs : List (String × Nat)
    next-pairs = if (score < new-score) then ((new-name , new-score) ∷ [])
      else (if (score ==n new-score) then ((new-name , new-score) ∷ (name , score) ∷ ys)
      else ((name , score) ∷ ys)
      )

top-deer : List DeerRate → Nat → List String
top-deer inp d = map proj₁ (top-deer-h [] inp d)

top-deer-each-s : List DeerRate → Nat → List String
top-deer-each-s [] _ = []
top-deer-each-s _ 0 = []
top-deer-each-s deers (suc x) = concat ((top-deer deers (suc x)) ∷ (top-deer-each-s deers x) ∷ [])

count-occur-h : List String → LookupTree String Nat → LookupTree String Nat
count-occur-h [] tree = tree
count-occur-h (x ∷ xs) tree with (read_tree x tree)
count-occur-h (x ∷ xs) tree | nothing = count-occur-h xs (set_val x 1 tree)
count-occur-h (x ∷ xs) tree | (just q) = count-occur-h xs (set_val x (suc q) tree)

str-lt : String → String → Bool
str-lt a b = isYes (a <? b)

count-occur : List String → LookupTree String Nat
count-occur [] = leaf false
count-occur (x ∷ xs) = count-occur-h xs init-tree
  where
    init-tree : LookupTree String Nat
    init-tree = build_tree _==_ str-lt ((x , 1) ∷ [])

show-tree : LookupTree String Nat → List String
show-tree (leaf _) = []
show-tree (node lhs v rhs) = concat ((((LTPair.key v) ++ ": " ++ show (LTPair.val v)) ∷ []) ∷ (show-tree lhs) ∷ (show-tree rhs) ∷ [])


fastest : String → String
fastest x = ((unlines ∘ (map (show-score 2503)) ∘ unmaybe ∘ (map parse-line) ∘ lines)  x) ++ "\n"

fastest-each-sec : String → String
fastest-each-sec x = (unlines ∘ show-tree ∘ count-occur) (top-deer-each-s deers 2503) ++ "\n"
  where
    deers : List DeerRate
    deers = (unmaybe ∘ (map parse-line) ∘ lines)  x

test-parse-line : parse-line "Comet can fly 14 km/s for 10 seconds, but then must rest for 127 seconds." ≡ just(deer "Comet" 14 10 127)
test-parse-line = refl

test-calc-dist-a : (calc-dist (deer "Comet" 14 10 127) 1000) ≡ 1120
test-calc-dist-a = refl

test-calc-dist-b : (calc-dist (deer "Dancer" 16 11 162) 1000) ≡ 1056
test-calc-dist-b = refl

test-top-deer : (top-deer ((deer "Comet" 14 10 127) ∷ (deer "Dancer" 16 11 162) ∷ []) 1) ≡ "Dancer" ∷ []
test-top-deer = refl

test-top-deer-s : (count-occur (top-deer-each-s ((deer "Comet" 14 10 127) ∷ (deer "Dancer" 16 11 162) ∷ []) 2)) ≡ count-occur ("Dancer" ∷ "Dancer" ∷ [])
test-top-deer-s = refl

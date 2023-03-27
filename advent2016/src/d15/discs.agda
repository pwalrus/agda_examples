

module d15.discs where

open import util.list_stuff using (words ; lines ; unmaybe ; hard-unmaybe ; filterᵇ ; each-one ; make-perms ; rem-dot ; append-front-all ; all-replacements ; cartproduct ; min-by-f ; enumerate ; split ; empty-table ; show-table ; transpose ; eq-classes ; rem-match ; partitionᵇ ; deduplicateᵇ ; index-of) renaming (trim to trim-ch)
open import util.lookup using (str-lt ; quick-sort ; LookupStrTree) renaming (all-kv to all-str-kv)
open import util.lookup_nat using (LookupNatTree ; build-nat-tree ; has-val ; all-kv) renaming (set-val to set-tree ; read-val to read-tree ; rem-val to rem-tree)
open import util.json using (readIntMaybe ; rem-lst-c)
open import util.search using (search-rec-breadth-dedup)
open import util.nat_stuff using (mod-nat ; div-nat ; lin-mod-system)
open import Data.Tree.Binary using (leaf ; node)
open import Agda.Builtin.String using (String)
open import Data.String.Base using (toList ; fromList ; _++_ ; unlines ; unwords ; intersperse ; fromChar ; padRight)
open import Data.String.Properties using (_==_)
open import Agda.Builtin.Nat using (Nat ; suc ; _<_ ; _+_ ; _-_ ; _*_) renaming (_==_ to _==n_)
open import Data.Nat.Base using (pred)
open import Data.Nat.Show using (show ; readMaybe ; showInBase)
open import Agda.Builtin.Int using (Int ; pos ; negsuc)
open import Data.Integer.Base using (_≤ᵇ_) renaming (_+_ to _+z_ ; _-_ to _-z_)
open import Data.Integer.Properties using (_≟_)
open import Data.Integer.Show using () renaming (show to showz)
open import Agda.Builtin.List using (List ; [] ; _∷_)
open import Data.List using (map ; foldr ; concat ; length ; zip ; take ; drop ; head ; last; tail ; any ; all ; cartesianProductWith ; applyUpTo ; scanr ; reverse)
open import Agda.Builtin.Char using (Char ; primCharToNat ; primNatToChar)
open import Data.Char.Properties renaming (_==_ to _==c_ ; _<?_ to _<c_)
open import Agda.Builtin.Bool using (Bool ; true ; false)
open import Data.Bool.Base using (if_then_else_ ; _∧_ ; _∨_ ; not)
open import Agda.Builtin.Maybe using (Maybe ; nothing ; just)
open import Data.Maybe using (fromMaybe)
open import Function.Base using (_∘_ ; id ; const)
open import Data.Product using (_×_ ; _,_ ; proj₁ ; proj₂)
open import Agda.Builtin.Equality using (refl ; _≡_)
open import Relation.Nullary.Decidable using (isYes)


record DiscP : Set where
  constructor dp
  field
    name : String
    size : Nat
    start : Nat

show-disc : DiscP → String
show-disc (dp nm s st) = "Disc " ++ nm ++ " has " ++ show s ++ " positions; at time=0, it is at position " ++ show st

private

  mod-sub-h : Nat → Nat → Nat → Nat → Nat
  mod-sub-h 0 m s x = s - x
  mod-sub-h (suc lm) m s x with (s < x)
  mod-sub-h (suc lm) m s x | true = mod-sub-h lm m (m + s) x
  mod-sub-h (suc lm) m s x | false = s - x

  mod-sub : Nat → Nat → Nat
  mod-sub x y = mod-sub-h y x x y

  drop-hash-ch : List Char → List Char
  drop-hash-ch ('#' ∷ xs) = xs
  drop-hash-ch xs = xs

  read-name : String → Nat
  read-name = fromMaybe 10 ∘ readMaybe 10 ∘ fromList ∘ drop-hash-ch ∘ toList


disc-to-lin-mod : DiscP → (Nat × Nat × Nat)
disc-to-lin-mod (dp nm1 s1 st1) = st1 , mod-sub s1 (read-name nm1) , s1

merge-discs : DiscP → DiscP → Maybe DiscP
merge-discs (dp nm1 s1 st1) (dp nm2 s2 st2) = output 
  where
    n0m : Maybe Nat
    n0m = lin-mod-system (disc-to-lin-mod (dp nm1 s1 st1)) (disc-to-lin-mod (dp nm2 s2 st2))
    output : Maybe DiscP
    output with n0m
    output | nothing = nothing
    output | (just n0) = just (dp nm1 (s1 * s2) (mod-sub (s1 * s2) (n0 + 1)))

fold-my-way : {A : Set} → Nat → (A → A → Maybe A) → List A → Maybe A
fold-my-way 0 _ _ = nothing
fold-my-way _ _ [] = nothing
fold-my-way (suc lm) f (x ∷ []) = just x
fold-my-way (suc lm) f (x ∷ y ∷ xs) with (f x y)
fold-my-way (suc lm) f (x ∷ y ∷ xs) | nothing = nothing
fold-my-way (suc lm) f (x ∷ y ∷ xs) | (just z) = fold-my-way lm f (z ∷ xs)

merge-all : List DiscP → DiscP
merge-all xs with (fold-my-way (length xs) merge-discs xs)
merge-all xs | nothing = (dp "nope" 0 0)
merge-all xs | (just z) = z
    
steps-away-single : DiscP → Nat
steps-away-single (dp nm1 s1 st1) = s1 - st1 - 1

parse-line-w : List String → Maybe DiscP
parse-line-w ("Disc" ∷ nm ∷ "has" ∷ sm ∷ _ ∷ "at" ∷ _ ∷ "it" ∷ "is" ∷ "at" ∷ "position" ∷ stm ∷ _) with (readMaybe 10 sm , (readMaybe 10 ∘ fromList ∘ rem-dot '.' ∘ toList) stm)
parse-line-w ("Disc" ∷ nm ∷ "has" ∷ sm ∷ _ ∷ "at" ∷ _ ∷ "it" ∷ "is" ∷ "at" ∷ "position" ∷ stm ∷ _) | (just s , just st) = (just (dp nm s st))
parse-line-w ("Disc" ∷ nm ∷ "has" ∷ sm ∷ _ ∷ "at" ∷ _ ∷ "it" ∷ "is" ∷ "at" ∷ "position" ∷ stm ∷ _) | _ = nothing
parse-line-w _ = nothing

parse-line : String → Maybe DiscP
parse-line = parse-line-w ∘ words


perfect-align : String → String
perfect-align x = show-disc final ++ "\n" ++ "steps: " ++ show (steps-away-single final) ++ "\n"
  where
    discs : List DiscP
    discs = (unmaybe ∘ map parse-line ∘ lines) x
    final : DiscP
    final = merge-all discs

test-parse-line-a : parse-line "Disc #1 has 5 positions; at time=0, it is at position 4.\n" ≡ just (dp "#1" 5 4)
test-parse-line-a = refl

test-parse-line-b : parse-line "Disc #2 has 2 positions; at time=0, it is at position 1." ≡ just (dp "#2" 2 1)
test-parse-line-b = refl

test-merge-discs-a : merge-discs (dp "#1" 5 4) (dp "#2" 2 1) ≡ just (dp "#1" 10 4)
test-merge-discs-a = refl

test-merge-discs-b : merge-discs (dp "#1" 5 4) (dp "#2" 3 1) ≡ just (dp "#1" 15 14)
test-merge-discs-b = refl

test-merge-discs-c : merge-discs (dp "#1" 2 1) (dp "#2" 3 1) ≡ just (dp "#1" 6 5)
test-merge-discs-c = refl

test-merge-discs-d : merge-discs (dp "#1" 2 1) (dp "#2" 5 4) ≡ just (dp "#1" 10 5)
test-merge-discs-d = refl

test-disc-lin : disc-to-lin-mod (dp "#3" 3 1) ≡ (1 , 0 , 3)
test-disc-lin = refl

test-merge-discs-e : merge-discs (dp "#1" 10 4) (dp "#3" 3 1) ≡ just (dp "#1" 30 24)
test-merge-discs-e = refl


test-merge-all : merge-all ((dp "#1" 5 4) ∷ (dp "#2" 2 1) ∷ []) ≡ dp "#1" 10 4
test-merge-all = refl

test-steps-away-a : steps-away-single (dp "#1" 10 4) ≡ 5
test-steps-away-a = refl

test-perfect-a : perfect-align
  ("Disc #1 has 5 positions; at time=0, it is at position 4.\n" ++
  "Disc #2 has 2 positions; at time=0, it is at position 1.") ≡
  "Disc #1 has 10 positions; at time=0, it is at position 4\nsteps: 5\n"
test-perfect-a = refl

test-perfect-b : perfect-align
  ("Disc #1 has 5 positions; at time=0, it is at position 4.\n" ++
  "Disc #2 has 2 positions; at time=0, it is at position 1.\n" ++
  "Disc #3 has 3 positions; at time=0, it is at position 1.") ≡
  "Disc #1 has 30 positions; at time=0, it is at position 24\nsteps: 5\n"
test-perfect-b = refl

module d15.duel where

open import util.list_stuff using (words ; lines ; unmaybe ; hard-unmaybe ; filterᵇ ; make-perms ; rem-dot ; append-front-all ; all-replacements ; cartproduct ; min-by-f ; enumerate ; list-minus ; conseq ; index-of ; set-at ; wordsByᵇ ; get-sub-wrap ; set-sub-wrap ; is-in ; unique-insert) renaming (trim to trim-ch)
open import util.lookup using (LookupStrTree ; build-str-tree ; LTPair ; counter ; quick-sort ; str-lt ; all-values ; all-keys ; unique-list)
open import util.lookup_nat using (LookupNatTree ; build-nat-tree ; has-val ; all-kv) renaming (set-val to set-tree ; read-val to read-tree)
open import util.json using (readIntMaybe)
open import util.search using (search-rec-breadth-dedup ; branch-bound ; components)
open import util.nat_stuff using (div-nat ; mod-nat ; max)
open import util.bitwise using (bitwise-xor ; to-bin ; show-bool)
open import util.grid using (Point ; point ; show-point ; neighbors-2d)
open import Data.Tree.Binary using (leaf ; node)
open import Agda.Builtin.String using (String)
open import Data.String using (toList ; fromList ; _++_ ; unlines ; intersperse ; fromChar ; padLeft)
open import Data.String.Properties using (_==_)
open import Agda.Builtin.Nat using (Nat ; suc ; _<_ ; _+_ ; _-_ ; _*_ ; div-helper ; mod-helper) renaming (_==_ to _==n_)
open import Data.Nat.Base using (pred ; _⊔_)
open import Data.Nat.Show using (show ; readMaybe ; showInBase)
open import Agda.Builtin.Int using (Int ; pos ; negsuc)
open import Data.Integer using (∣_∣) renaming (_<?_ to _<?z_ ; _+_ to _+z_ ; _-_ to _-z_)
open import Data.Integer.Show using () renaming (show to show-z)
open import Data.Integer.Properties using (_≟_)
open import Agda.Builtin.List using (List ; [] ; _∷_)
open import Data.List using (map ; foldr ; concat ; length ; zip ; reverse ; head ; cartesianProductWith ; applyUpTo ; take ; drop ; any ; all)
open import Agda.Builtin.Char using (Char ; primCharToNat ; primToLower)
open import Data.Char.Properties using () renaming (_==_ to _==c_ ; _<?_ to _<c?_)
open import Agda.Builtin.Bool using (Bool ; true ; false)
open import Data.Bool.Base using (if_then_else_ ; _∧_ ; _∨_ ; not)
open import Agda.Builtin.Maybe using (Maybe ; nothing ; just)
open import Data.Maybe using (fromMaybe)
open import Function using (_∘_ ; id ; flip ; const)
open import Data.Product using (_×_ ; _,_ ; proj₁ ; proj₂ ; map₂ ; uncurry)
open import Agda.Builtin.Equality using (refl ; _≡_)
open import Relation.Nullary.Decidable using (isYes)

record Generator : Set where
  constructor genrt
  field
    start : Nat
    step : Nat
    mod-val : Nat
    mod-flt : Nat


step-single : Generator → Nat × Generator
step-single (genrt s st m f) = next-val , (genrt next-val st m f)
  where
    next-val : Nat
    next-val = mod-nat (s * st) m

step-single-big : Nat → Generator → Nat × Generator
step-single-big 0 g = 0 , g
step-single-big (suc lm) g = next
  where
    next : Nat × Generator
    next with (step-single g)
    next | (v , genrt s st m f) with (mod-nat v f ==n 0)
    next | (v , genrt s st m f) | true = v , genrt s st m f
    next | (v , genrt s st m f) | false = step-single-big lm (genrt s st m f)

DGen : Set
DGen = Generator × Generator

step-double : Bool → DGen → (Nat × Nat) × DGen
step-double big (g1 , g2) = (proj₁ res1 , proj₁ res2) , (proj₂ res1 , proj₂ res2)
  where
    res1 : Nat × Generator
    res1 = if big then (step-single-big 1000000 g1) else step-single g1
    res2 : Nat × Generator
    res2 = if big then (step-single-big 1000000 g2) else step-single g2

left-gen : Nat → Generator
left-gen st = genrt st 16807 2147483647 4

right-gen : Nat → Generator
right-gen st = genrt st 48271 2147483647 8

last-match : Nat → Nat → Bool
last-match x y = (mod-nat x 65536) ==n (mod-nat y 65536)

mk-list-h : {A B : Set} → Nat → A → (A → B × A) → (B → Bool) → List B → List B
mk-list-h 0 _ _ _ xs = reverse xs
mk-list-h {A} {B} (suc n) start func filt xs = mk-list-h n (proj₂ next) func filt accum
  where
    next : B × A
    next = func start
    accum : List B
    accum with (filt (proj₁ next))
    accum | true = ((proj₁ next) ∷ xs)
    accum | false = xs

mk-list : {A B : Set} → Nat → A → (A → B × A) → (B → Bool) → List B
mk-list n start func filt = mk-list-h n start func filt []


mk-count-h : {A B : Set} → Nat → A → (A → B × A) → (B → Bool) → Nat → Nat
mk-count-h 0 _ _ _ acc = acc
mk-count-h {A} {B} (suc n) start func filt acc = mk-count-h n (proj₂ next) func filt acc2
  where
    next : B × A
    next = func start
    acc2 : Nat
    acc2 with (filt (proj₁ next))
    acc2 | true = suc acc
    acc2 | false = acc

mk-count : {A B : Set} → Nat → A → (A → B × A) → (B → Bool) → Nat
mk-count n start func filt = mk-count-h n start func filt 0

parse-row-w : List String → Maybe Nat
parse-row-w ("Generator" ∷ _ ∷ "starts" ∷ "with" ∷ n ∷ _) = readMaybe 10 n
parse-row-w _ = nothing

pair-gen : Bool → Nat → Nat → Nat → Nat
pair-gen big lm a b = mk-count lm (left-gen a , right-gen b) (step-double big) (uncurry last-match)

count-gen-matches : String → String
count-gen-matches x = output ++ "\n"
  where
    initial-vals : List Nat
    initial-vals = (unmaybe ∘ map parse-row-w ∘ map words ∘ lines) x
    output : String
    output with initial-vals
    output | (a ∷ b ∷ []) = "matches: " ++ show ((pair-gen true 5000000 a b))
    output | _ = "bad input."

test-single-step-l : mk-list 5 (left-gen 65) step-single (const true) ≡ 1092455 ∷ 1181022009 ∷ 245556042 ∷ 1744312007 ∷ 1352636452 ∷ []
test-single-step-l = refl

test-single-step-r : mk-list 5 (right-gen 8921) step-single (const true) ≡ 430625591 ∷ 1233683848 ∷ 1431495498 ∷ 137874439 ∷ 285222916 ∷ []
test-single-step-r = refl

test-last-match-a : last-match 245556042 1431495498 ≡ true
test-last-match-a = refl

test-last-match-b : last-match 1092455 430625591 ≡ false
test-last-match-b = refl

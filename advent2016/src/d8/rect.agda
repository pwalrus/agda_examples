module d8.rect where

open import util.list_stuff using (words ; lines ; unmaybe ; filterᵇ ; each-one ; make-perms ; rem-dot ; append-front-all ; all-replacements ; cartproduct ; min-by-f ; enumerate ; split ; empty-table ; show-table ; transpose) renaming (trim to trim-ch)
open import util.lookup using (LookupStrTree ; LookupNatTree ; build-str-tree ; build-nat-tree ; has-val ; all-values ; all-keys ; all-kv ; LTPair ; str-lt ; quick-sort ; counter) renaming (set-val to set-tree ; read-val to read-tree)
open import util.json using (readIntMaybe ; rem-lst-c)
open import Data.Tree.Binary using (leaf ; node)
open import Agda.Builtin.String using (String)
open import Data.String.Base using (toList ; fromList ; _++_ ; unlines ; intersperse)
open import Data.String.Properties using (_==_)
open import Agda.Builtin.Nat using (Nat ; suc ; _<_ ; _+_ ; _-_ ; _*_ ; div-helper ; mod-helper) renaming (_==_ to _==n_)
open import Data.Nat.Base using (pred)
open import Data.Nat.Show using (show ; readMaybe)
open import Agda.Builtin.Int using (Int ; pos ; negsuc)
open import Data.Integer.Base using (_≤ᵇ_) renaming (_+_ to _+z_ ; _-_ to _-z_)
open import Data.Integer.Properties using (_≟_)
open import Data.Integer.Show using () renaming (show to showz)
open import Agda.Builtin.List using (List ; [] ; _∷_)
open import Data.List using (map ; foldr ; concat ; length ; zip ; take ; drop ; head ; last; tail ; any ; cartesianProductWith ; applyUpTo)
open import Agda.Builtin.Char using (Char ; primCharToNat ; primNatToChar)
open import Data.Char.Properties renaming (_==_ to _==c_ ; _<?_ to _<c_)
open import Agda.Builtin.Bool using (Bool ; true ; false)
open import Data.Bool.Base using (if_then_else_ ; _∧_ ; _∨_ ; not)
open import Agda.Builtin.Maybe using (Maybe ; nothing ; just)
open import Data.Maybe using (fromMaybe)
open import Function.Base using (_∘_)
open import Data.Product using (_×_ ; _,_ ; proj₁ ; proj₂)
open import Agda.Builtin.Equality using (refl ; _≡_)
open import Relation.Nullary.Decidable using (isYes)


data Inst : Set where
  rect : Nat → Nat → Inst
  rotCol : Nat → Nat → Inst
  rotRow : Nat → Nat → Inst

show-bool : Bool → String
show-bool true = "#"
show-bool false = "."

apply-row : {A : Set} → (A → A) → Nat → List A → List A
apply-row f w [] = []
apply-row f 0 xs = xs
apply-row f (suc w) (x ∷ xs) = (f x) ∷ (apply-row f w xs)

apply-rect : {A : Set} → (A → A) → Nat → Nat → List (List A) → List (List A)
apply-rect f 0 _ xs = xs
apply-rect f _ 0 xs = xs
apply-rect f h (suc w) [] = []
apply-rect f h (suc w) (r ∷ xs) = (apply-row f h r) ∷ (apply-rect f h w xs)

rot-row : {A : Set} → Nat → Nat → List (List A) → List (List A)
rot-row _ _ [] = []
rot-row (suc t) mag (x ∷ xs) = x ∷ (rot-row t mag xs)
rot-row {A} 0 mag (x ∷ xs) = (concat (left ∷ right ∷ [])) ∷ xs
  where
    left : List A
    left = drop (length x - mag) x
    right : List A
    right = take (length x - mag) x

rot-col : {A : Set} → Nat → Nat → List (List A) → List (List A)
rot-col t mag = transpose ∘ (rot-row t mag) ∘ transpose

apply-inst : List (List Bool) → Inst → List (List Bool)
apply-inst dat (rotRow id mag) = rot-row id mag dat
apply-inst dat (rotCol id mag) = rot-col id mag dat
apply-inst dat (rect w h) = apply-rect (λ {_ → true}) w h dat

apply-all-inst : List (List Bool) → List Inst → List (List Bool)
apply-all-inst dat [] = dat
apply-all-inst dat (ins ∷ xs) = apply-all-inst (apply-inst dat ins) xs

parse-line-w : List String → Maybe Inst
parse-line-w ("rect" ∷ dim ∷ _) with (split 'x' dim)
parse-line-w ("rect" ∷ dim ∷ _) | (a ∷ b ∷ _) with (readMaybe 10 a)
parse-line-w ("rect" ∷ dim ∷ _) | (a ∷ b ∷ _) | (just x) with (readMaybe 10 b)
parse-line-w ("rect" ∷ dim ∷ _) | (a ∷ b ∷ _) | (just x) | (just y) = just (rect x y)
parse-line-w ("rect" ∷ dim ∷ _) | (a ∷ b ∷ _) | (just x) | nothing = nothing
parse-line-w ("rect" ∷ dim ∷ _) | (a ∷ b ∷ _) | nothing = nothing
parse-line-w ("rect" ∷ dim ∷ _) | _ = nothing
parse-line-w ("rotate" ∷ "row" ∷ rid ∷ "by" ∷ mag ∷ _) with (split '=' rid)
parse-line-w ("rotate" ∷ "row" ∷ rid ∷ "by" ∷ mag ∷ _) | (_ ∷ b ∷ _) with (readMaybe 10 b)
parse-line-w ("rotate" ∷ "row" ∷ rid ∷ "by" ∷ mag ∷ _) | (_ ∷ b ∷ _) | (just id) with (readMaybe 10 mag)
parse-line-w ("rotate" ∷ "row" ∷ rid ∷ "by" ∷ mag ∷ _) | (_ ∷ b ∷ _) | (just id) | (just m) = just (rotRow id m)
parse-line-w ("rotate" ∷ "row" ∷ rid ∷ "by" ∷ mag ∷ _) | (_ ∷ b ∷ _) | (just id) | nothing = nothing
parse-line-w ("rotate" ∷ "row" ∷ rid ∷ "by" ∷ mag ∷ _) | (_ ∷ b ∷ _) | nothing = nothing
parse-line-w ("rotate" ∷ "row" ∷ rid ∷ "by" ∷ mag ∷ _) | _ = nothing
parse-line-w ("rotate" ∷ "column" ∷ rid ∷ "by" ∷ mag ∷ _) with (split '=' rid)
parse-line-w ("rotate" ∷ "column" ∷ rid ∷ "by" ∷ mag ∷ _) | (_ ∷ b ∷ _) with (readMaybe 10 b)
parse-line-w ("rotate" ∷ "column" ∷ rid ∷ "by" ∷ mag ∷ _) | (_ ∷ b ∷ _) | (just id) with (readMaybe 10 mag)
parse-line-w ("rotate" ∷ "column" ∷ rid ∷ "by" ∷ mag ∷ _) | (_ ∷ b ∷ _) | (just id) | (just m) = just (rotCol id m)
parse-line-w ("rotate" ∷ "column" ∷ rid ∷ "by" ∷ mag ∷ _) | (_ ∷ b ∷ _) | (just id) | nothing = nothing
parse-line-w ("rotate" ∷ "column" ∷ rid ∷ "by" ∷ mag ∷ _) | (_ ∷ b ∷ _) | nothing = nothing
parse-line-w ("rotate" ∷ "column" ∷ rid ∷ "by" ∷ mag ∷ _) | _ = nothing
parse-line-w _ = nothing

parse-line : String → Maybe Inst
parse-line = parse-line-w ∘ words

count-lights-on : String → String
count-lights-on x = (show ∘ (foldr _+_ 0) ∘ concat ∘ (map (map  λ {q → if q then 1 else 0}))) final-tab ++ "\n" ++ show-table show-bool final-tab ++ "\n"
  where
    insts : List Inst
    insts = (unmaybe ∘ (map parse-line) ∘ lines) x
    init-rect : List (List Bool)
    init-rect = empty-table false 6 50
    final-tab : List (List Bool)
    final-tab = apply-all-inst init-rect insts

test-parse-rect : parse-line "rect 3x5" ≡ just (rect 3 5)
test-parse-rect = refl

test-parse-rot-row : parse-line "rotate row y=0 by 4" ≡ just (rotRow 0 4)
test-parse-rot-row = refl

test-parse-rot-col : parse-line "rotate column x=2 by 1" ≡ just (rotCol 2 1)
test-parse-rot-col = refl

test-show-table : show-table show-bool (empty-table false 3 5) ≡ ". . . . .\n. . . . .\n. . . . ."
test-show-table = refl

test-apply-inst : show-table show-bool (apply-all-inst (empty-table false 3 7)
  ((rect 3 2) ∷ (rotCol 1 1) ∷ (rotRow 0 4) ∷ [])) ≡
  ". . . . # . #\n# # # . . . .\n. # . . . . ."
test-apply-inst = refl

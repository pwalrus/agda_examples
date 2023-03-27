
module d16.dragon where

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


double-b-list : List Bool → List Bool
double-b-list xs = concat (xs ∷ (false ∷ []) ∷ rhs ∷ [])
  where
    rhs : List Bool
    rhs = map not (reverse xs)

double-to-size : Nat → Nat → List Bool → List Bool
double-to-size 0 _ xs = xs
double-to-size (suc lm) sz xs with (length xs < sz)
double-to-size (suc lm) sz xs | true = double-to-size lm sz (double-b-list xs)
double-to-size (suc lm) sz xs | false = xs

_==b_ : Bool → Bool → Bool
_==b_ true true = true
_==b_ false false = true
_==b_ _ _ = false


parse-line : String → List Bool
parse-line xs = (map (λ {q → if q ==c '1' then true else false}) ∘ toList) xs

show-line : List Bool → String
show-line xs = (fromList ∘ map (λ {q → if q then '1' else '0'})) xs

private
  checksum-pass : List Bool → List Bool
  checksum-pass (x ∷ y ∷ xs) = (x ==b y) ∷ (checksum-pass xs)
  checksum-pass _ = []

  checksum-h : Nat → List Bool → List Bool
  checksum-h 0 _ = []
  checksum-h _ [] = []
  checksum-h (suc lm) xs with (mod-nat (length xs) 2 ==n 0)
  checksum-h (suc lm) xs | true = checksum-h lm (checksum-pass xs)
  checksum-h (suc lm) xs | false = xs

checksum : List Bool → List Bool
checksum xs = checksum-h (length xs) xs


correct-checksum : String → String
correct-checksum xs = "\nchecksum: " ++ (show-line (checksum seq)) ++ "\n"
  where
    inp : List String
    inp = words xs
    init : List Bool
    init = (parse-line ∘ fromMaybe "" ∘ head) inp
    size : Nat
    size = (fromMaybe 0 ∘ readMaybe 10 ∘ fromMaybe "" ∘ head ∘ drop 1) inp
    seq : List Bool
    seq = take size (double-to-size size size init)
    


test-double-b-list-a : (show-line ∘ double-b-list ∘ parse-line) "1" ≡ "100"
test-double-b-list-a = refl

test-double-b-list-b : (show-line ∘ double-b-list ∘ parse-line) "0" ≡ "001"
test-double-b-list-b = refl

test-double-b-list-c : (show-line ∘ double-b-list ∘ parse-line) "11111" ≡ "11111000000"
test-double-b-list-c = refl

test-double-b-list-d : (show-line ∘ double-b-list ∘ parse-line) "111100001010" ≡ "1111000010100101011110000"
test-double-b-list-d = refl

test-checksum-a : (show-line ∘ checksum ∘ parse-line) "110010110100" ≡ "100"
test-checksum-a = refl

test-checksum-b : (show-line ∘ checksum ∘ parse-line) "10000011110010000111" ≡ "01100"
test-checksum-b = refl

test-correct-checksum : correct-checksum "10000 20" ≡ "\nchecksum: 01100\n"
test-correct-checksum = refl

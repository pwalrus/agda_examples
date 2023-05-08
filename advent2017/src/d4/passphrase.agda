module d4.passphrase where

open import util.list_stuff using (words ; lines ; unmaybe ; hard-unmaybe ; filterᵇ ; make-perms ; rem-dot ; append-front-all ; all-replacements ; cartproduct ; min-by-f ; enumerate ; list-minus ; conseq) renaming (trim to trim-ch)
open import util.lookup using (LookupStrTree ; LookupNatTree ; build-str-tree ; build-nat-tree ; has-val ; all-values ; all-keys ; all-kv ; LTPair ; counter ; quick-sort ; str-lt) renaming (set-val to set-tree ; read-val to read-tree)
open import util.json using (readIntMaybe)
open import util.search using (search-rec-breadth-dedup ; branch-bound)
open import util.nat_stuff using (div-nat ; mod-nat)
open import Data.Tree.Binary using (leaf ; node)
open import Agda.Builtin.String using (String)
open import Data.String.Base using (toList ; fromList ; _++_ ; unlines ; intersperse ; fromChar)
open import Data.String.Properties using (_==_)
open import Agda.Builtin.Nat using (Nat ; suc ; _<_ ; _+_ ; _-_ ; _*_ ; div-helper ; mod-helper) renaming (_==_ to _==n_)
open import Data.Nat.Base using (pred)
open import Data.Nat.Show using (show ; readMaybe)
open import Agda.Builtin.Int using (Int ; pos ; negsuc)
open import Data.Integer.Base using (∣_∣) renaming (_+_ to _+z_ ; _-_ to _-z_)
open import Data.Integer.Show using () renaming (show to show-z)
open import Data.Integer.Properties using (_≟_)
open import Agda.Builtin.List using (List ; [] ; _∷_)
open import Data.List using (map ; foldr ; concat ; length ; zip ; reverse ; head ; cartesianProductWith ; applyUpTo ; take ; drop ; any)
open import Agda.Builtin.Char using (Char)
open import Data.Char.Properties using () renaming (_==_ to _==c_ ; _<?_ to _<c?_)
open import Agda.Builtin.Bool using (Bool ; true ; false)
open import Data.Bool.Base using (if_then_else_ ; _∧_ ; _∨_ ; not)
open import Agda.Builtin.Maybe using (Maybe ; nothing ; just)
open import Data.Maybe using (fromMaybe)
open import Function using (_∘_ ; id)
open import Data.Product using (_×_ ; _,_ ; proj₁ ; proj₂ ; map₂)
open import Agda.Builtin.Equality using (refl ; _≡_)
open import Relation.Nullary.Decidable using (isYes)


trim : String → String
trim = fromList ∘ trim-ch ∘ toList

has-dup : List String → Bool
has-dup xs = any (λ {(_ , q) → 1 < q}) counts
  where
    counts : List (String × Nat)
    counts = counter _==_ str-lt xs 

_<c_ : Char → Char → Bool
_<c_ x y = isYes (x <c? y)

sort-word : String → String
sort-word  = fromList ∘ quick-sort _<c_ ∘ toList

has-anagram : List String → Bool
has-anagram = has-dup ∘ map sort-word

count-valid-phrases : String → String
count-valid-phrases x = "count: " ++ (show ∘ foldr _+_ 0 ∘ map (λ {q → if q then 0 else 1}) ∘ map has-dup ∘ map words ∘ lines ∘ trim) x ++ "\n"

test-has-dup-a : (has-dup ∘ words) "aa bb cc dd ee" ≡ false
test-has-dup-a = refl

test-has-dup-b : (has-dup ∘ words) "aa bb cc dd aa" ≡ true
test-has-dup-b = refl

test-has-dup-c : (has-dup ∘ words) "aa bb cc dd aaa" ≡ false
test-has-dup-c = refl

test-has-anagram-a : (has-anagram ∘ words) "abcde fghij" ≡ false
test-has-anagram-a = refl

test-has-anagram-b : (has-anagram ∘ words) "abcde xyz ecdab" ≡ true
test-has-anagram-b = refl

test-has-anagram-c : (has-anagram ∘ words) "a ab abc abd abf abj" ≡ false
test-has-anagram-c = refl

test-sort-word : (intersperse " " ∘ map sort-word ∘ words) "iiii oiii ooii oooi oooo" ≡ "iiii iiio iioo iooo oooo"
test-sort-word = refl

test-has-anagram-d : (has-anagram ∘ words) "iiii oiii ooii oooi oooo" ≡ false
test-has-anagram-d = refl

test-has-anagram-e : (has-anagram ∘ words) "oiii ioii iioi iiio" ≡ true
test-has-anagram-e = refl

test-count-valid-phrases : count-valid-phrases "aa bb cc dd ee\naa bb cc dd aa\n\n" ≡ "count: 1\n"
test-count-valid-phrases = refl

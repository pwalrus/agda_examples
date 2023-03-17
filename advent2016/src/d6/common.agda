module d6.common where

open import util.list_stuff using (words ; lines ; unmaybe ; filterᵇ ; each-one ; make-perms ; rem-dot ; append-front-all ; all-replacements ; cartproduct ; min-by-f ; enumerate ; split ; head-of-each ; tail-of-each) renaming (trim to trim-ch)
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
open import Data.List using (map ; foldr ; concat ; length ; zip ; take ; head ; tail)
open import Agda.Builtin.Char using (Char ; primCharToNat ; primNatToChar)
open import Data.Char.Properties renaming (_==_ to _==c_ ; _<?_ to _<c_)
open import Agda.Builtin.Bool using (Bool ; true ; false)
open import Data.Bool.Base using (if_then_else_ ; _∧_ ; _∨_ ; not)
open import Agda.Builtin.Maybe using (Maybe ; nothing ; just)
open import Function.Base using (_∘_)
open import Data.Product using (_×_ ; _,_ ; proj₁ ; proj₂)
open import Agda.Builtin.Equality using (refl ; _≡_)
open import Relation.Nullary.Decidable using (isYes)

final-of : {A : Set} → List A → Maybe A
final-of [] = nothing
final-of (x ∷ []) = just x
final-of (x ∷ xs) = final-of xs

ch-lt : Char → Char → Bool
ch-lt a b = isYes (a <c b)

counter-ch : List Char → List (Char × Nat)
counter-ch = counter _==c_ ch-lt

lengthm : {A : Set} → List (List A) → Nat
lengthm xs with (head xs)
lengthm xs | nothing = 0
lengthm xs | (just x) = length x

most-common : List Char → Maybe Char
most-common xs with (head (counter-ch xs))
most-common xs | nothing = nothing
most-common xs | (just x) = just (proj₁ x)

least-common : List Char → Maybe Char
least-common xs with (final-of (counter-ch xs))
least-common xs | nothing = nothing
least-common xs | (just x) = just (proj₁ x)
 

get-common-list-h : (List Char → Maybe Char) → Nat → List (List Char) → List Char
get-common-list-h _ 0 _ = []
get-common-list-h f (suc l) lst with (head-of-each lst , tail-of-each lst)
get-common-list-h f (suc l) lst | (h , t) with (f h)
get-common-list-h f (suc l) lst | (h , t) | (just c) = c ∷ (get-common-list-h f l t)
get-common-list-h f (suc l) lst | (h , t) | nothing = []

get-common-list : (List Char → Maybe Char) → List String → String
get-common-list f x = fromList (get-common-list-h f (lengthm chs) chs)
  where
    chs : List (List Char)
    chs = map toList x

decode-by-freq : String → String
decode-by-freq x = "decode: " ++ get-common-list most-common (lines x) ++ "\n"

decode-by-freq2 : String → String
decode-by-freq2 x = "decode: " ++ get-common-list least-common (lines x) ++ "\n"

test-decode-by-freq-a : decode-by-freq "ab\nac\ndc" ≡ "decode: ac\n"
test-decode-by-freq-a = refl

test-decode-by-freq-b : decode-by-freq ("eedadn\n" ++
  "drvtee\n" ++
  "eandsr\n" ++
  "raavrd\n" ++
  "atevrs\n" ++
  "tsrnev\n" ++
  "sdttsa\n" ++
  "rasrtv\n" ++
  "nssdts\n" ++
  "ntnada\n" ++
  "svetve\n" ++
  "tesnvt\n" ++
  "vntsnd\n" ++
  "vrdear\n" ++
  "dvrsen\n" ++
  "enarar") ≡ "decode: easter\n"
test-decode-by-freq-b = refl


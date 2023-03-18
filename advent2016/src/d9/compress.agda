module d9.compress where

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

data CompStr : Set where
  uncomp : String → CompStr
  copies : Nat → List CompStr → CompStr

depth-lim : Nat
depth-lim = 1000000

comp-length-h : Nat → CompStr → Nat
comp-length-h 0 _ = 0
comp-length-h (suc lm) (uncomp x) = (length ∘ toList) x
comp-length-h (suc lm) (copies m x) = m * (foldr _+_ 0 (map (comp-length-h lm) x))

comp-length : CompStr → Nat
comp-length = comp-length-h depth-lim

comp-all-length : List CompStr → Nat
comp-all-length x = foldr _+_ 0 (map comp-length x)

show-comp-h : Nat → CompStr → String
show-comp-h 0 _ = ""
show-comp-h _ (uncomp x) = x
show-comp-h (suc lm) (copies m x) = "(" ++ show (comp-all-length x) ++ "x" ++ show m ++ ")" ++ foldr _++_ "" (map (show-comp-h lm) x)

show-comp : CompStr → String
show-comp = show-comp-h depth-lim

show-all-comp : List CompStr → String
show-all-comp = (foldr _++_ "") ∘ (map show-comp)

find-next-h : Nat → Char → List Char → Nat
find-next-h curr _ [] = curr
find-next-h curr ch (x ∷ xs) with (ch ==c x)
find-next-h curr ch (x ∷ xs) | true = curr
find-next-h curr ch (x ∷ xs) | false = find-next-h (suc curr) ch xs

find-next : Char → List Char → (List Char × List Char)
find-next ch xs with (find-next-h 0 ch xs)
find-next ch xs | idx = take idx xs , drop (suc idx) xs

contains-ch : Char → List Char → Bool
contains-ch ch [] = false
contains-ch ch (x ∷ xs) with (ch ==c x)
contains-ch ch (x ∷ xs) | true = true
contains-ch ch (x ∷ xs) | false = contains-ch ch xs

contains-comp-h : Nat → Char → CompStr → Bool
contains-comp-h 0 _ _ = false
contains-comp-h (suc lm) ch (uncomp x) = contains-ch ch (toList x)
contains-comp-h (suc lm) ch (copies m x) = any (contains-comp-h lm ch) x

parse-line-ch : Nat → List Char → List CompStr
parse-line-ch 0 _ = []
parse-line-ch (suc lm) xs with (find-next '(' xs)
parse-line-ch (suc lm) xs | (head , rem1) with (find-next ')' rem1)
parse-line-ch (suc lm) xs | (head , rem1) | (dims , rem2) with (split 'x' (fromList dims))
parse-line-ch (suc lm) xs | (head , rem1) | (dims , rem2) | (a  ∷ b ∷ []) with (readMaybe 10 a)
parse-line-ch (suc lm) xs | (head , rem1) | (dims , rem2) | (a  ∷ b ∷ []) | (just l) with (readMaybe 10 b)
parse-line-ch (suc lm) xs | (head , rem1) | (dims , rem2) | (a  ∷ b ∷ []) | (just l) | (just m) = (uncomp (fromList head)) ∷ (copies m (uncomp (fromList (take l rem2)) ∷ [])) ∷ (parse-line-ch lm (drop l rem2))
parse-line-ch (suc lm) xs | (head , rem1) | (dims , rem2) | (a  ∷ b ∷ []) | (just l) | _ = []
parse-line-ch (suc lm) xs | (head , rem1) | (dims , rem2) | (a  ∷ b ∷ []) | _ = []
parse-line-ch (suc lm) xs | (head , rem1) | (dims , rem2) | _ = (uncomp (fromList head)) ∷ []

parse-line : String → List CompStr
parse-line x = parse-line-ch (length x-ch) x-ch
  where
    x-ch : List Char
    x-ch = toList x

decompress-single : CompStr → String
decompress-single (uncomp x) = x
decompress-single (copies m x) = foldr _++_ "" (applyUpTo (λ {_ → show-all-comp x}) m)

decompress : List CompStr → String
decompress x = foldr _++_ "" (map decompress-single x)

parse-and-decomp : String → String
parse-and-decomp = decompress ∘ parse-line

full-decomp : Nat → String → String
full-decomp 0 _ = ""
full-decomp (suc lm) xs with (parse-and-decomp xs)
full-decomp (suc lm) xs | next with (contains-ch '(' (toList next))
full-decomp (suc lm) xs | next | false = next
full-decomp (suc lm) xs | next | true = full-decomp lm next

parse-next-layer-h : Nat → CompStr → List CompStr
parse-next-layer-h 0 _ = []
parse-next-layer-h _ (uncomp x) = if (contains-ch '(' (toList x)) then parse-line x else (uncomp x ∷ [])
parse-next-layer-h (suc lm) (copies m s) = (copies m (concat (map (parse-next-layer-h lm) s))) ∷ []

parse-full-depth-h : Nat → List CompStr → List CompStr
parse-full-depth-h 0 xs = xs
parse-full-depth-h (suc lm) xs with (concat (map (parse-next-layer-h lm) xs))
parse-full-depth-h (suc lm) xs | next = if (any (contains-comp-h lm '(') next) then (parse-full-depth-h lm next) else next

parse-full-depth : String → List CompStr
parse-full-depth x with (parse-line x)
parse-full-depth x | xs = parse-full-depth-h (length (toList x)) xs

find-decom-size : String → String
find-decom-size x = "size: " ++ show (foldr _+_ 0 sizes) ++ "\n"
  where
    strs : List (List CompStr)
    strs = ((map parse-line) ∘ lines) x
    sizes : List Nat
    sizes = map (length ∘ toList ∘ decompress) strs 

find-f-decom-size : String → String
find-f-decom-size x = "size: " ++ show (foldr _+_ 0 sizes) ++ "\n"
  where
    strs : List (List CompStr)
    strs = ((map parse-full-depth) ∘ lines) x
    sizes : List Nat
    sizes = concat (map (map comp-length) strs)

test-parse-line-a : show-all-comp (parse-line "A(1x5)BC") ≡ "A(1x5)BC"
test-parse-line-a = refl

test-parse-line-b : show-all-comp (parse-line "A(2x2)BCD(2x2)EFG") ≡ "A(2x2)BCD(2x2)EFG"
test-parse-line-b = refl

test-parse-line-d : show-all-comp (parse-line "(6x1)(1x3)A") ≡ "(6x1)(1x3)A"
test-parse-line-d = refl

test-decompress-a : decompress (parse-line "ADVENT") ≡ "ADVENT"
test-decompress-a = refl

test-decompress-b : decompress (parse-line "A(1x5)BC") ≡ "ABBBBBC"
test-decompress-b = refl

test-decompress-c : decompress (parse-line "(3x3)XYZ") ≡ "XYZXYZXYZ"
test-decompress-c = refl

test-decompress-d : decompress (parse-line "(6x1)(1x3)A") ≡ "(1x3)A"
test-decompress-d = refl

test-decompress-e : decompress (parse-line "X(8x2)(3x3)ABCY") ≡ "X(3x3)ABC(3x3)ABCY"
test-decompress-e = refl

test-full-decomp-a : full-decomp 100 "(3x3)XYZ" ≡ "XYZXYZXYZ"
test-full-decomp-a = refl

test-full-decomp-b : full-decomp 100 "X(8x2)(3x3)ABCY" ≡ "XABCABCABCABCABCABCY"
test-full-decomp-b = refl

test-full-decomp-c : foldr _+_ 0 (map comp-length (parse-full-depth "(27x12)(20x12)(13x14)(7x10)(1x12)A")) ≡ 241920
test-full-decomp-c = refl

test-full-decomp-d : length (toList(full-decomp 100 "(25x3)(3x3)ABC(2x3)XY(5x2)PQRSTX(18x9)(3x2)TWO(5x7)SEVEN")) ≡ 445
test-full-decomp-d = refl

test-full-decomp-d-b : foldr _+_ 0 (map comp-length (parse-full-depth "(25x3)(3x3)ABC(2x3)XY(5x2)PQRSTX(18x9)(3x2)TWO(5x7)SEVEN")) ≡ 445
test-full-decomp-d-b = refl

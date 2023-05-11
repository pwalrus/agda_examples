module d9.garbage where

open import util.list_stuff using (words ; lines ; unmaybe ; hard-unmaybe ; filterᵇ ; make-perms ; rem-dot ; append-front-all ; all-replacements ; cartproduct ; min-by-f ; enumerate ; list-minus ; conseq ; index-of ; set-at) renaming (trim to trim-ch)
open import util.lookup using (LookupStrTree ; build-str-tree ; LTPair ; counter ; quick-sort ; str-lt ; all-values ; all-keys ; all-kv ; has-val) renaming (set-val to set-tree ; read-val to read-tree)
open import util.lookup_nat using (LookupNatTree ; build-nat-tree)
open import util.json using (readIntMaybe)
open import util.search using (search-rec-breadth-dedup ; branch-bound)
open import util.nat_stuff using (div-nat ; mod-nat)
open import Data.Tree.Binary using (leaf ; node)
open import Agda.Builtin.String using (String)
open import Data.String.Base using (toList ; fromList ; _++_ ; unlines ; intersperse ; fromChar)
open import Data.String.Properties using (_==_)
open import Agda.Builtin.Nat using (Nat ; suc ; _<_ ; _+_ ; _-_ ; _*_ ; div-helper ; mod-helper) renaming (_==_ to _==n_)
open import Data.Nat.Base using (pred ; _⊔_)
open import Data.Nat.Show using (show ; readMaybe)
open import Agda.Builtin.Int using (Int ; pos ; negsuc)
open import Data.Integer using (∣_∣) renaming (_<?_ to _<?z_ ; _+_ to _+z_ ; _-_ to _-z_)
open import Data.Integer.Show using () renaming (show to show-z)
open import Data.Integer.Properties using (_≟_)
open import Agda.Builtin.List using (List ; [] ; _∷_)
open import Data.List using (map ; foldr ; concat ; length ; zip ; reverse ; head ; cartesianProductWith ; applyUpTo ; take ; drop ; any ; all)
open import Agda.Builtin.Char using (Char)
open import Data.Char.Properties using () renaming (_==_ to _==c_ ; _<?_ to _<c?_)
open import Agda.Builtin.Bool using (Bool ; true ; false)
open import Data.Bool.Base using (if_then_else_ ; _∧_ ; _∨_ ; not)
open import Agda.Builtin.Maybe using (Maybe ; nothing ; just)
open import Data.Maybe using (fromMaybe)
open import Function using (_∘_ ; id ; flip)
open import Data.Product using (_×_ ; _,_ ; proj₁ ; proj₂ ; map₂)
open import Agda.Builtin.Equality using (refl ; _≡_)
open import Relation.Nullary.Decidable using (isYes)


data StBlock : Set where
  grp : List StBlock → StBlock
  garb : String → StBlock

show-block-h : Nat → StBlock → String
show-block-h 0 _ = "<hit limit>"
show-block-h (suc lm) (garb x) = "<" ++ x ++ ">"
show-block-h (suc lm) (grp nodes) = "{" ++ (intersperse "," ∘ map (show-block-h lm)) nodes ++ "}"

show-block : StBlock → String
show-block = show-block-h 100000

check-balance : List Char → Bool → List Char → Bool
check-balance [] false [] = true
check-balance stack false (' ' ∷ xs) = check-balance stack false xs
check-balance ('<' ∷ stack) false ('!' ∷ xs) = check-balance ('<' ∷ stack) true xs
check-balance ('<' ∷ stack) false ('>' ∷ xs) = check-balance stack false xs
check-balance ('<' ∷ stack) true (_ ∷ xs) = check-balance ('<' ∷ stack) false xs
check-balance ('<' ∷ stack) false (_ ∷ xs) = check-balance ('<' ∷ stack) false xs
check-balance _ _ ('>' ∷ xs) = false
check-balance ('{' ∷ stack) false ('}' ∷ xs) = check-balance stack false xs
check-balance stack false (',' ∷ xs) = check-balance stack false xs
check-balance _ _ ('}' ∷ xs) = false
check-balance stack false ('{' ∷ xs) = check-balance ('{' ∷ stack) false xs
check-balance stack false ('<' ∷ xs) = check-balance ('<' ∷ stack) false xs
check-balance _ _ _ = false

find-next-balanced-g : Char → List Char → List Char → Maybe (List Char × List Char)
find-next-balanced-g _ _ [] = nothing
find-next-balanced-g end-ch lhs (x ∷ rhs) with (end-ch ==c x)
find-next-balanced-g end-ch lhs (x ∷ rhs) | true with (check-balance [] false (reverse (end-ch ∷ lhs)))
find-next-balanced-g end-ch lhs (x ∷ rhs) | true | true = just (reverse (end-ch ∷ lhs) , rhs)
find-next-balanced-g end-ch lhs (x ∷ rhs) | true | false = find-next-balanced-g end-ch (end-ch ∷ lhs) rhs
find-next-balanced-g end-ch lhs (x ∷ rhs) | false = find-next-balanced-g end-ch (x ∷ lhs) rhs

find-next-balanced : List Char → Maybe (List Char × List Char)
find-next-balanced (' ' ∷ xs) = find-next-balanced xs
find-next-balanced (',' ∷ xs) = find-next-balanced xs
find-next-balanced ('{' ∷ xs) = find-next-balanced-g '}' [] ('{' ∷ xs)
find-next-balanced ('<' ∷ xs) = find-next-balanced-g '>' [] ('<' ∷ xs)
find-next-balanced _ = nothing

find-balanced-list : Nat → List Char → Maybe (List (List Char))
find-balanced-list 0 _ = nothing
find-balanced-list (suc lm) xs with (find-next-balanced xs)
find-balanced-list (suc lm) xs | (just (lhs , rhs)) with (length (trim-ch rhs) ==n 0)
find-balanced-list (suc lm) xs | (just (lhs , rhs)) | true = just (lhs ∷ [])
find-balanced-list (suc lm) xs | (just (lhs , rhs)) | false with (find-balanced-list lm rhs)
find-balanced-list (suc lm) xs | (just (lhs , rhs)) | false | (just tail) = just (lhs ∷ tail)
find-balanced-list (suc lm) xs | (just (lhs , rhs)) | false | nothing = nothing
find-balanced-list (suc lm) xs | nothing = nothing

trim : String → String
trim = fromList ∘ trim-ch ∘ toList

rem-last : Char → List Char → List Char
rem-last ch [] = []
rem-last ch (x ∷ []) with (x ==c ch)
rem-last ch (x ∷ []) | false = x ∷ []
rem-last ch (x ∷ []) | true = []
rem-last ch (x ∷ xs) = x ∷ (rem-last ch xs)

parse-block-ch : Nat → List Char → Maybe StBlock
parse-block-ch 0 _ = nothing
parse-block-ch _ [] = nothing
parse-block-ch (suc lm) (' ' ∷ xs) = parse-block-ch lm xs
parse-block-ch (suc lm) (',' ∷ xs) = parse-block-ch lm xs
parse-block-ch (suc lm) ('<' ∷ xs) with (check-balance [] false ('<' ∷ xs))
parse-block-ch (suc lm) ('<' ∷ xs) | true = just (garb ((fromList ∘ rem-last '>') xs))
parse-block-ch (suc lm) ('<' ∷ xs) | false = nothing
parse-block-ch (suc lm) ('{' ∷ '}' ∷ []) = just (grp [])
parse-block-ch (suc lm) ('{' ∷ xs) with (find-balanced-list lm (rem-last '}' xs))
parse-block-ch (suc lm) ('{' ∷ xs) | (just nodes) with ((hard-unmaybe ∘ map (parse-block-ch lm)) nodes)
parse-block-ch (suc lm) ('{' ∷ xs) | (just nodes) | (just blocks) = just (grp blocks)
parse-block-ch (suc lm) ('{' ∷ xs) | (just nodes) | nothing = nothing
parse-block-ch (suc lm) ('{' ∷ xs) | nothing = nothing
parse-block-ch (suc lm) _ = nothing

parse-block : String → Maybe StBlock
parse-block xs = (parse-block-ch (length (toList xs)) ∘ trim-ch ∘ toList) xs


score : Nat → Nat → StBlock → Nat
score 0 _ _ = 0
score (suc lm) level (grp nodes) = (suc level) + foldr _+_ 0 (map (score lm (suc level)) nodes)
score (suc lm) level (garb _) = 0

rem-escape : List Char → List Char
rem-escape [] = []
rem-escape (x ∷ []) = x ∷ []
rem-escape ('!' ∷ x ∷ xs) = (rem-escape xs)
rem-escape (x ∷ xs) = x ∷ (rem-escape xs)

garb-score : Nat → StBlock → Nat
garb-score 0 _ = 0
garb-score (suc lm) (grp nodes) = foldr _+_ 0 (map (garb-score lm) nodes)
garb-score (suc lm) (garb x) = (length ∘ rem-escape ∘ toList) x

score-all-streams : String → String
score-all-streams x = "score: " ++ (show ∘ foldr _+_ 0 ∘ map (score 1000 0) ∘ unmaybe ∘ map parse-block ∘ lines ∘ trim) x ++ "\n"

count-garbage : String → String
count-garbage x = "garbage: " ++ (show ∘ foldr _+_ 0 ∘ map (garb-score 1000) ∘ unmaybe ∘ map parse-block ∘ lines ∘ trim) x ++ "\n"


test-check-balance-a : check-balance [] false (toList "{}") ≡ true
test-check-balance-a = refl

test-check-balance-b : check-balance [] false (toList "{}}") ≡ false
test-check-balance-b = refl

test-check-balance-c : check-balance [] false (toList "<!!!>>") ≡ true
test-check-balance-c = refl

test-check-balance-d : check-balance [] false (toList "<!!>>") ≡ false
test-check-balance-d = refl

test-find-next-balanced : (fromList ∘ proj₁ ∘ fromMaybe ([] , []) ∘ find-next-balanced ∘ toList)
  "{{{}}},<abc>" ≡ "{{{}}}"
test-find-next-balanced = refl

test-find-next-balanced-r : (fromList ∘ proj₂ ∘ fromMaybe ([] , []) ∘ find-next-balanced ∘ toList)
  "{{{}}},<abc>" ≡ ",<abc>"
test-find-next-balanced-r = refl

test-find-balanced-list-a : (map fromList ∘ fromMaybe ((toList "nope") ∷ []) ∘ find-balanced-list 1000 ∘ toList)
  "{}" ≡ "{}" ∷ []
test-find-balanced-list-a = refl

test-find-balanced-list-b : (map fromList ∘ fromMaybe ((toList "nope") ∷ []) ∘ find-balanced-list 1000 ∘ toList)
  "{{}}" ≡ "{{}}" ∷ []
test-find-balanced-list-b = refl

test-parse-block-a : (show-block ∘ fromMaybe (garb "nope") ∘ parse-block) "<{o\"i!a,<{i<a>" ≡ "<{o\"i!a,<{i<a>"
test-parse-block-a = refl

test-rem-last : (fromList ∘ rem-last '}' ∘ toList) "{{{}}}" ≡ "{{{}}"
test-rem-last = refl

test-parse-block-b : (show-block ∘ fromMaybe (garb "nope") ∘ parse-block) "{}" ≡ "{}"
test-parse-block-b = refl

test-parse-block-c : (show-block ∘ fromMaybe (garb "nope") ∘ parse-block) "{{{}}}" ≡ "{{{}}}"
test-parse-block-c = refl

test-parse-block-d : (show-block ∘ fromMaybe (garb "nope") ∘ parse-block)
  "{{<a>},{<a>},{<a>},{<a>}}" ≡ "{{<a>},{<a>},{<a>},{<a>}}"
test-parse-block-d = refl

test-score-a : (score 100 0 ∘ fromMaybe (garb "nope") ∘ parse-block)
  "{}" ≡ 1
test-score-a = refl

test-score-b : (score 100 0 ∘ fromMaybe (garb "nope") ∘ parse-block)
  "{{{}}}" ≡ 6
test-score-b = refl

test-score-c : (score 100 0 ∘ fromMaybe (garb "nope") ∘ parse-block)
  "{{},{}}" ≡ 5
test-score-c = refl

test-score-d : (score 100 0 ∘ fromMaybe (garb "nope") ∘ parse-block)
  "{<a>,<a>,<a>,<a>}" ≡ 1
test-score-d = refl

test-score-e : (score 100 0 ∘ fromMaybe (garb "nope") ∘ parse-block)
  "{{<ab>},{<ab>},{<ab>},{<ab>}}" ≡ 9
test-score-e = refl

test-score-f : (score 100 0 ∘ fromMaybe (garb "nope") ∘ parse-block)
  "{{<!!>},{<!!>},{<!!>},{<!!>}}" ≡ 9
test-score-f = refl

test-score-g : (score 100 0 ∘ fromMaybe (garb "nope") ∘ parse-block)
  "{{<a!>},{<a!>},{<a!>},{<ab>}}" ≡ 3
test-score-g = refl

test-gscore-a : (garb-score 100 ∘ fromMaybe (garb "nope") ∘ parse-block)
  "<>" ≡ 0
test-gscore-a = refl

test-gscore-b : (garb-score 100 ∘ fromMaybe (garb "nope") ∘ parse-block)
  "<random characters>" ≡ 17
test-gscore-b = refl

test-gscore-c : (garb-score 100 ∘ fromMaybe (garb "nope") ∘ parse-block)
  "<<<<>" ≡ 3
test-gscore-c = refl

test-gscore-d : (garb-score 100 ∘ fromMaybe (garb "nope") ∘ parse-block)
  "<{!>}>" ≡ 2
test-gscore-d = refl


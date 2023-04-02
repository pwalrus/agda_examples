
module d21.scramble where

open import util.list_stuff using (words ; lines ; unmaybe ; hard-unmaybe ; filterᵇ ; each-one ; make-perms ; rem-dot ; append-front-all ; all-replacements ; cartproduct ; min-by-f ; enumerate ; split ; empty-table ; show-table ; transpose ; eq-classes ; rem-match ; partitionᵇ ; deduplicateᵇ ; index-of) renaming (trim to trim-ch)
open import util.lookup using (str-lt ; quick-sort ; LookupStrTree) renaming (all-kv to all-str-kv)
open import util.lookup_nat using (LookupNatTree ; build-nat-tree ; has-val ; all-kv) renaming (set-val to set-tree ; read-val to read-tree ; rem-val to rem-tree)
open import util.json using (readIntMaybe ; rem-lst-c)
open import util.search using (search-rec-breadth ; search-rec-all)
open import util.hash using (hash-md5)
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


trim : String → String
trim = fromList ∘ trim-ch ∘ toList

rot-left : Nat → String → String
rot-left n xs = (fromList ∘ drop n ∘ toList) xs ++ (fromList ∘ take n ∘ toList) xs

rot-right : Nat → String → String
rot-right n xs = (fromList ∘ drop mdist) chl ++ (fromList ∘ take mdist) chl
  where
    chl : List Char
    chl = toList xs
    mdist : Nat
    mdist = mod-nat ((2 * length chl) - n) (length chl)

atIdx : {A : Set} → Nat → List A → Maybe A
atIdx _ [] = nothing
atIdx 0 (x ∷ _) = just x
atIdx (suc lm) (x ∷ xs) = atIdx lm xs

setIdx : {A : Set} → Nat → A → List A → List A
setIdx _ c [] = c ∷ []
setIdx 0 c (_ ∷ xs) = c ∷ xs
setIdx (suc lm) c (x ∷ xs) = x ∷ (setIdx lm c xs)

idxOf : {A : Set} → (A → A → Bool) → Nat → A → List A → Maybe Nat
idxOf eq _ _ [] = nothing
idxOf eq idx c (x ∷ xs) = if (eq x c) then just idx else idxOf eq (suc idx) c xs

popIdx : {A : Set} → Nat → List A → List A
popIdx _ [] = []
popIdx 0 (x ∷ xs) = xs
popIdx (suc idx) (x ∷ xs) = x ∷ (popIdx idx xs)

insIdx : {A : Set} → Nat → A → List A → List A
insIdx _ c [] = c ∷ []
insIdx 0 c xs = c ∷ xs
insIdx (suc idx) c (x ∷ xs) = x ∷ (insIdx idx c xs)

idx-of : Char → String → Nat
idx-of c xs = (fromMaybe 0 ∘ idxOf _==c_ 0 c ∘ toList) xs

get-idx : Nat → String → Char
get-idx idx xs = fromMaybe 'z' (atIdx idx (toList xs))

set-idx : Nat → Char → String → String
set-idx idx c xs = (fromList ∘ setIdx idx c ∘ toList) xs

swap-idx : Nat → Nat → String → String
swap-idx x y xs = set-idx x rc (set-idx y lc xs)
  where
    lc : Char
    lc = get-idx x xs
    rc : Char
    rc = get-idx y xs

swap-ch : Char → Char → String → String
swap-ch a b xs = swap-idx (idx-of a xs) (idx-of b xs) xs

rot-pos : Char → String → String
rot-pos c xs = rot-right ((if 3 < idx then 1 else 0) + 1 + idx) xs
  where
    idx : Nat
    idx = idx-of c xs

rot-pos-rev : Char → String → String
rot-pos-rev c xs = rot-left rotby xs
  where
    idx : Nat
    idx = idx-of c xs
    rotby : Nat
    rotby with ((idx ==n 0) ∨ (mod-nat idx 2 ==n 1))
    rotby | true = 1 + (div-nat idx 2)
    rotby | false = mod-nat (5 + (div-nat idx 2)) (length (toList xs))
    

rev-pos : Nat → Nat → String → String
rev-pos x y xs = (fromList ∘ concat) (fst-part ∷ (reverse snd-part) ∷ trd-part ∷ [])
  where
    fst-part : List Char
    fst-part = (take x ∘ toList) xs
    snd-part : List Char
    snd-part = (take (y - x + 1) ∘ drop x ∘ toList) xs
    trd-part : List Char
    trd-part = (drop (y + 1) ∘ toList) xs

mv-pos : Nat → Nat → String → String
mv-pos x y xs = fromList (insIdx y (get-idx x xs) missing)
  where
    missing : List Char
    missing = (popIdx x ∘ toList) xs


data Inst : Set where
  swappos : Nat → Nat → Inst
  swapch : Char → Char → Inst
  rotl : Nat → Inst
  rotr : Nat → Inst
  rotpos : Char → Inst
  rotposrev : Char → Inst
  revpos : Nat → Nat → Inst
  mvpos : Nat → Nat → Inst

chstr : String → Char
chstr = fromMaybe 'z' ∘ head ∘ toList

parse-line-w : List String → Maybe Inst
parse-line-w ("swap" ∷ "position" ∷ xm ∷ "with" ∷ "position" ∷ ym ∷ _) with (readMaybe 10 xm , readMaybe 10 ym)
parse-line-w ("swap" ∷ "position" ∷ xm ∷ "with" ∷ "position" ∷ ym ∷ _) | (just x , just y) = just (swappos x y)
parse-line-w ("swap" ∷ "position" ∷ xm ∷ "with" ∷ "position" ∷ ym ∷ _) | _ = nothing
parse-line-w ("swap" ∷ "letter" ∷ xm ∷ "with" ∷ "letter" ∷ ym ∷ _) = just (swapch (chstr xm) (chstr ym))
parse-line-w ("rotate" ∷ "based" ∷ "on" ∷ "position" ∷ "of" ∷ "letter" ∷ xm ∷ _) = just (rotpos (chstr xm))
parse-line-w ("rotate" ∷ dir ∷ xm ∷ _) with (readMaybe 10 xm , (dir == "left"))
parse-line-w ("rotate" ∷ dir ∷ xm ∷ _) | (just x , true) = just (rotl x)
parse-line-w ("rotate" ∷ dir ∷ xm ∷ _) | (just x , false) = just (rotr x)
parse-line-w ("rotate" ∷ dir ∷ xm ∷ _) | _ = nothing
parse-line-w ("reverse" ∷ "positions" ∷ xm ∷ "through" ∷ ym ∷ _) with (readMaybe 10 xm , readMaybe 10 ym)
parse-line-w ("reverse" ∷ "positions" ∷ xm ∷ "through" ∷ ym ∷ _) | (just x , just y) = just (revpos x y)
parse-line-w ("reverse" ∷ "positions" ∷ xm ∷ "through" ∷ ym ∷ _) | _ = nothing
parse-line-w ("move" ∷ "position" ∷ xm ∷ "to" ∷ "position" ∷ ym ∷ _) with (readMaybe 10 xm , readMaybe 10 ym)
parse-line-w ("move" ∷ "position" ∷ xm ∷ "to" ∷ "position" ∷ ym ∷ _) | (just x , just y) = just (mvpos x y)
parse-line-w ("move" ∷ "position" ∷ xm ∷ "to" ∷ "position" ∷ ym ∷ _) | _ = nothing
parse-line-w _ = nothing

parse-line : String → Maybe Inst
parse-line = parse-line-w ∘ words

parse-batch : String → List Inst
parse-batch = fromMaybe [] ∘ hard-unmaybe ∘ map parse-line ∘ lines ∘ trim

apply-inst : Inst → String → String
apply-inst (swappos x y) xs = swap-idx x y xs
apply-inst (swapch a b) xs = swap-ch a b xs
apply-inst (rotl x) xs = rot-left x xs
apply-inst (rotr x) xs = rot-right x xs
apply-inst (rotpos x) xs = rot-pos x xs
apply-inst (rotposrev x) xs = rot-pos-rev x xs 
apply-inst (revpos x y) xs = rev-pos x y xs
apply-inst (mvpos x y) xs = mv-pos x y xs

apply-all-inst : List Inst → String → String
apply-all-inst xs init = foldr apply-inst init (reverse xs)

rev-inst : Inst → Inst
rev-inst (rotl x) = (rotr x)
rev-inst (rotr x) = (rotl x)
rev-inst (rotpos c) = rotposrev c
rev-inst (rotposrev c) = rotpos c
rev-inst (mvpos x y) = mvpos y x
rev-inst ins = ins

scramble-word : String → String
scramble-word x = "final: " ++ (apply-all-inst (parse-batch x) "abcdefgh") ++ "\n"

unscramble-word : String → String
unscramble-word x = "final: " ++ (apply-all-inst ((map rev-inst ∘ reverse ∘ parse-batch) x) "fbgdceah") ++ "\n"

test-rot-left : rot-left 2 "abcdef" ≡ "cdefab"
test-rot-left = refl

test-rot-left-a : rot-left 1 "abcde" ≡ "bcdea"
test-rot-left-a = refl

test-rot-right : rot-right 2 "abcdef" ≡ "efabcd"
test-rot-right = refl

test-swap-idx : swap-idx 2 4 "abcdef" ≡ "abedcf"
test-swap-idx = refl

test-swap-ch : swap-ch 'b' 'e' "abcdef" ≡ "aecdbf"
test-swap-ch = refl

test-rot-pos : rot-pos 'b' "abdec" ≡ "ecabd"
test-rot-pos = refl

test-rev-pos-a : rev-pos 0 4 "edcba" ≡ "abcde"
test-rev-pos-a = refl

test-rev-pos-b : rev-pos 2 7 "abcdefgh" ≡ "abhgfedc"
test-rev-pos-b = refl

test-mv-pos : mv-pos 3 0 "bdeac" ≡ "abdec"
test-mv-pos = refl

test-rotate-rev-a : rot-pos-rev 'a' (rot-pos 'a' "abcdefgh") ≡ "abcdefgh"
test-rotate-rev-a = refl

test-parse-line-a : parse-line "rotate left 1 step" ≡ just (rotl 1)
test-parse-line-a = refl

test-parse-line-b : parse-line "move position 1 to position 4" ≡ just (mvpos 1 4)
test-parse-line-b = refl

test-apply-all : apply-all-inst (parse-batch
  (
  "swap position 4 with position 0\n" ++
  "swap letter d with letter b\n" ++
  "reverse positions 0 through 4\n" ++
  "rotate left 1 step\n" ++
  "move position 1 to position 4\n" ++
  "move position 3 to position 0\n" ++
  "rotate based on position of letter b\n" ++
  "rotate based on position of letter d"
  ))
  "abcde"
  ≡ "decab"
test-apply-all = refl

--test-unscramble : (apply-all-inst ((map rev-inst ∘ reverse ∘ parse-batch)
--  ("swap position 4 with position 0\n" ++
--  "swap letter d with letter b\n" ++
--  "reverse positions 0 through 4\n" ++
--  "rotate left 1 step\n" ++
--  "move position 1 to position 4\n" ++
--  "move position 3 to position 0\n" ++
--  "rotate based on position of letter b\n" ++
--  "rotate based on position of letter d"
--  ))
--  "fbdecgha") ≡ "abcdefgh"
--test-unscramble = refl

module d4.obscure where

open import util.list_stuff using (words ; lines ; unmaybe ; filterᵇ ; each-one ; make-perms ; rem-dot ; append-front-all ; all-replacements ; cartproduct ; min-by-f ; enumerate ; split) renaming (trim to trim-ch)
open import util.lookup using (LookupStrTree ; LookupNatTree ; build-str-tree ; build-nat-tree ; has-val ; all-values ; all-keys ; all-kv ; LTPair ; str-lt ; quick-sort) renaming (set-val to set-tree ; read-val to read-tree)
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
open import Data.List using (map ; foldr ; concat ; length ; zip ; take)
open import Agda.Builtin.Char using (Char ; primCharToNat ; primNatToChar)
open import Data.Char.Properties renaming (_==_ to _==c_)
open import Agda.Builtin.Bool using (Bool ; true ; false)
open import Data.Bool.Base using (if_then_else_ ; _∧_ ; _∨_ ; not)
open import Agda.Builtin.Maybe using (Maybe ; nothing ; just)
open import Function.Base using (_∘_)
open import Data.Product using (_×_ ; _,_ ; proj₁ ; proj₂)
open import Agda.Builtin.Equality using (refl ; _≡_)
open import Relation.Nullary.Decidable using (isYes)


data RoomCode : Set where
  room : List String → Nat → String → RoomCode

chars-from : RoomCode → List Char
chars-from (room parts _ _) = concat (map toList parts)

char-count-h : LookupStrTree Nat → List Char → LookupStrTree Nat
char-count-h tree [] = tree
char-count-h tree (x ∷ xs) with (read-tree (fromList (x ∷ [])) tree)
char-count-h tree (x ∷ xs) | nothing = char-count-h (set-tree (fromList (x ∷ [])) 1 tree) xs
char-count-h tree (x ∷ xs) | (just c) = char-count-h (set-tree (fromList (x ∷ [])) (suc c) tree) xs

pair-orders : (String × Nat) → (String × Nat) → Bool
pair-orders (ls , ln) (rs , rn) with (ln < rn)
pair-orders (ls , ln) (rs , rn) | true = false
pair-orders (ls , ln) (rs , rn) | false with (rn < ln)
pair-orders (ls , ln) (rs , rn) | false | true = true
pair-orders (ls , ln) (rs , rn) | false | false = str-lt ls rs

char-count : List Char → List (String × Nat)
char-count lst = quick-sort pair-orders counts
  where
    counts : List (String × Nat)
    counts = all-kv (char-count-h (build-str-tree (("" , 0) ∷ [])) lst)

checksum-ch : List Char → String
checksum-ch = fromList ∘ (take 5) ∘ concat ∘ (map toList) ∘ (map proj₁) ∘ char-count

is-valid : RoomCode → Bool
is-valid (room parts id chsm) = ((checksum-ch ∘ chars-from) (room parts id chsm)) == chsm

is-valid-m : Maybe RoomCode → Bool
is-valid-m nothing = false
is-valid-m (just r) = is-valid r

not-last : {A : Set} → List A → List A
not-last [] = []
not-last (_ ∷ []) = []
not-last (x ∷ xs) = x ∷ (not-last xs)

last-only : {A : Set} → List A → Maybe A
last-only [] = nothing
last-only (x ∷ []) = just (x)
last-only (_ ∷ xs) = last-only xs

parse-line : String → Maybe RoomCode
parse-line x = output
  where
    parts : List String
    parts = split '-' x
    first-few : List String
    first-few = not-last parts
    last : String
    last with (last-only parts)
    last | nothing = ""
    last | (just l) = l
    output : Maybe RoomCode
    output with (split '[' last)
    output | (l ∷ r ∷ []) with (readMaybe 10 l)
    output | (l ∷ r ∷ []) | nothing = nothing
    output | (l ∷ r ∷ []) | (just id) = just (room first-few id ((fromList ∘ (rem-dot ']') ∘ toList) r))
    output | _ = nothing

show-room : RoomCode → String
show-room (room parts id checksum) = intersperse "," parts ++ " " ++ show id ++ " " ++ checksum

show-room-m : Maybe RoomCode → String
show-room-m nothing = "no code"
show-room-m (just c) = show-room c

sum-valid-sectors : String → String
sum-valid-sectors x = "total: " ++ show total ++ "\n"
  where
    rows : List RoomCode
    rows = (unmaybe ∘ (map parse-line) ∘ lines) x
    all-valid : List RoomCode
    all-valid = filterᵇ is-valid rows
    total : Nat
    total = foldr _+_ 0 (map (λ {(room _ id _) → id}) all-valid)

mod-nat : Nat → Nat → Nat
mod-nat x y = mod-helper 0 (pred y) x (pred y)

rotate-ch : Nat → Char → Char
rotate-ch sh ch = primNatToChar ((mod-nat (sh + primCharToNat ch - primCharToNat 'a') 26) + primCharToNat 'a')

decrypt-string : Nat → String → String
decrypt-string sh = fromList ∘ (map (rotate-ch sh)) ∘ toList

decrypt-room : RoomCode → RoomCode
decrypt-room (room parts id checksum) = room (map (decrypt-string id) parts) id checksum

decrypt-names : String → String
decrypt-names x =  unlines all-dec ++ "\n"
  where
    rows : List RoomCode
    rows = (unmaybe ∘ (map parse-line) ∘ lines) x
    all-dec : List String
    all-dec = map (show-room ∘ decrypt-room) (filterᵇ is-valid rows)

test-parse-line : show-room-m (parse-line "aaaaa-bbb-z-y-x-123[abxyz]") ≡ "aaaaa,bbb,z,y,x 123 abxyz"
test-parse-line = refl

test-checksum-ch : (checksum-ch ∘ chars-from) (room ("aaaaa" ∷ "bbb" ∷ "z" ∷ "y" ∷ "x" ∷ []) 123 "abxyz") ≡ "abxyz"
test-checksum-ch = refl

test-checksum-ch-b : (checksum-ch ∘ chars-from) (room ("a" ∷ "b" ∷ "c" ∷ "d" ∷ "e" ∷ "f" ∷ "g" ∷ "h" ∷ []) 123 "abxyz") ≡ "abcde"
test-checksum-ch-b = refl

test-is-valid-a : is-valid-m (parse-line "aaaaa-bbb-z-y-x-123[abxyz]") ≡ true
test-is-valid-a = refl

test-is-valid-b : is-valid-m (parse-line "a-b-c-d-e-f-g-h-987[abcde]") ≡ true
test-is-valid-b = refl

test-is-valid-c : is-valid-m (parse-line "not-a-real-room-404[oarel]") ≡ true
test-is-valid-c = refl

test-is-valid-d : is-valid-m (parse-line "totally-real-room-200[decoy]") ≡ false
test-is-valid-d = refl

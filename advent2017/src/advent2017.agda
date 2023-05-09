module advent2017 where

open import Agda.Builtin.IO
open import Agda.Builtin.Unit using (⊤)
open import Agda.Builtin.String

open import d1.captcha using (run-captcha-half)
open import d2.checksum using (calc-checksum ; calc-div-pair)
open import d3.spiral using (dist-to-center ; accumulate-to-goal)
open import d4.passphrase using (count-valid-phrases)
open import d5.bounce using (jump-through)
open import d6.cycle using (find-inf-loop)
open import d7.tower using (find-root-node ; find-unbalanced-node)

postulate interact : (String → String) → IO ⊤
{-# FOREIGN GHC import qualified Data.Text as T #-}
{-# COMPILE GHC interact = \ f -> interact ( T.unpack . f . T.pack ) #-}

main : IO ⊤
main = interact find-unbalanced-node


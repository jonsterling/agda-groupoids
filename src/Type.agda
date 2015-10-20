{-# OPTIONS --without-K #-}

module Type where

open import Agda.Primitive
open import Ambient.Type.Base public
import Ambient.Type.Discrete
import Ambient.Type.Map
import Ambient.Type.Initial
import Ambient.Type.Op
import Ambient.Type.Tensor
import Ambient.Type.Terminal

module ≡ where
  open import Ambient.Type.Discrete public
    renaming (t to _t_)
module 𝟘 where
  open import Ambient.Type.Initial public
module 𝟙 where
  open import Ambient.Type.Terminal public
module Op where
  open import Ambient.Type.Op public
module Map where
  open import Ambient.Type.Map public
  open import Ambient.Type.Map.Boot public
module Ten where
  open import Ambient.Type.Tensor public
  open import Ambient.Type.Tensor.Boot public

open Ambient.Type.Tensor public
  using (_,_)
open Ambient.Type.Terminal public
  using (*)

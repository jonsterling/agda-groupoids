{-# OPTIONS --without-K #-}

module Type where

open import Agda.Primitive
open import Ambient.Type.Base public
import Ambient.Type.Discrete
import Ambient.Type.Map
import Ambient.Type.Initial
import Ambient.Type.Op
import Ambient.Type.Product
import Ambient.Type.Terminal

module ≡₀ where
  open import Ambient.Type.Discrete public
module 𝟘₀ where
  open import Ambient.Type.Initial public
module 𝟙₀ where
  open import Ambient.Type.Terminal public
module Op₀ where
  open import Ambient.Type.Op public
module ⇒₀ where
  open import Ambient.Type.Map public
  open import Ambient.Type.Map.Boot public
module ×₀ where
  open import Ambient.Type.Product public
  open import Ambient.Type.Product.Boot public

open ≡₀ public
  using (_≡₀_)
open 𝟘₀ public
  using (𝟘₀)
open 𝟙₀ public
  using (𝟙₀; *)
open Op₀ public
  using (Op₀)
open ⇒₀ public
  using (_⇒₀,₀_; _⇒₀,₁_)
open ×₀ public
  using (_,_; π⁰₀; π¹₀; _×₀_; ⟨_,₀_⟩; ⟨_×₀_⟩)

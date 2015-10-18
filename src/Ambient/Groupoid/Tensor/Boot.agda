{-# OPTIONS --without-K #-}

module Ambient.Groupoid.Tensor.Boot where

open import Agda.Primitive
import Ambient.Groupoid.Base as G
import Setoid as S
open import Type as T

infixr 3 _⊗_

_⊗_
  : ∀ {d} ..{ℓ₀ᵒ ℓ₀ˢᵒ ℓ₀ˢʰ ℓ₁ᵒ ℓ₁ˢᵒ ℓ₁ˢʰ}
  → (A : G.𝔊₂,₀ d ℓ₀ᵒ ℓ₀ˢᵒ ℓ₀ˢʰ)
  → (B : G.𝔊₂,₀ d ℓ₁ᵒ ℓ₁ˢᵒ ℓ₁ˢʰ)
  → G.𝔊₂,₀ d _ _ _
G.obj (A ⊗ B) =
  G.obj A ×₀ G.obj B
G.homˢ (A ⊗ B) =
  λ {((a₀ , b₀) , (a₁ , b₁)) →
    G.homˢ A (a₀ , a₁) S.Ten.⊗ G.homˢ B (b₀ , b₁)
  }
G.idnˢ (A ⊗ B) =
  S.Ten.⟨-,-⟩ S.Map.$₀ (G.idnˢ A , G.idnˢ B)
G.cmpˢ (A ⊗ B) =
  S.Ten.⟨-,-⟩ S.Map.$₀
    ( G.cmpˢ A S.Map.∘₀ᵗ S.Ten.⟨-⊗-⟩ S.Map.$₀ (S.Ten.π₀ , S.Ten.π₀)
    , G.cmpˢ B S.Map.∘₀ᵗ S.Ten.⟨-⊗-⟩ S.Map.$₀ (S.Ten.π₁ , S.Ten.π₁))
G.invˢ (_⊗_ {S.Dir.≤} A B) =
  _
G.invˢ (_⊗_ {S.Dir.≈} A B) =
  S.Ten.⟨-⊗-⟩ S.Map.$₀ (G.invˢ A , G.invˢ B)
G.idn-lhs (A ⊗ B) _ =
  G.idn-lhs A _ , G.idn-lhs B _
G.idn-rhs (A ⊗ B) _ =
  G.idn-rhs A _ , G.idn-rhs B _
G.cmp-ass (A ⊗ B) f g h =
  G.cmp-ass A _ _ _ , G.cmp-ass B _ _ _
G.inv-lhs (_⊗_ {S.Dir.≤} A B) f =
  _
G.inv-lhs (_⊗_ {S.Dir.≈} A B) f =
  G.inv-lhs A _ , G.inv-lhs B _
G.inv-rhs (_⊗_ {S.Dir.≤} A B) f =
  _
G.inv-rhs (_⊗_ {S.Dir.≈} A B) f =
  G.inv-rhs A _ , G.inv-rhs B _

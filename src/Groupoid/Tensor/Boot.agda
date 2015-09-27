{-# OPTIONS --without-K #-}

module Groupoid.Tensor.Boot where

open import Agda.Primitive
import Groupoid.Base as G
import Setoid as S
open import Type as T
  using (_,_)

infixr 3 _⊗_

_⊗_
  : ∀ {d} ..{ℓ₀ᵒ ℓ₀ˢᵒ ℓ₀ˢʰ ℓ₁ᵒ ℓ₁ˢᵒ ℓ₁ˢʰ}
  → (A : G.t d ℓ₀ᵒ ℓ₀ˢᵒ ℓ₀ˢʰ)
  → (B : G.t d ℓ₁ᵒ ℓ₁ˢᵒ ℓ₁ˢʰ)
  → G.t d _ _ _

G.obj (A ⊗ B) =
  G.obj A T.∐.⊗ G.obj B
G.homˢ (A ⊗ B) =
  λ {((a₀ , b₀) , (a₁ , b₁)) →
    G.homˢ A (a₀ , a₁) S.∐.⊗ G.homˢ B (b₀ , b₁)
  }
G.idnˢᵐ (A ⊗ B) =
  S.∐.⟨-,-⟩ S.Π.$₀ (G.idnˢᵐ A , G.idnˢᵐ B)
G.cmpˢᵐ (A ⊗ B) =
  S.∐.⟨-,-⟩ S.Π.$₀
    ( G.cmpˢᵐ A S.Π.∘ᵗᵐ S.∐.⟨-⊗-⟩ S.Π.$₀ (S.∐.π₀ , S.∐.π₀)
    , G.cmpˢᵐ B S.Π.∘ᵗᵐ S.∐.⟨-⊗-⟩ S.Π.$₀ (S.∐.π₁ , S.∐.π₁))
G.invˢᵐ (_⊗_ {S.Dir.≤} A B) =
  _
G.invˢᵐ (_⊗_ {S.Dir.≈} A B) =
  S.∐.⟨-⊗-⟩ S.Π.$₀ (G.invˢᵐ A , G.invˢᵐ B)
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

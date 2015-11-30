{-# OPTIONS --without-K #-}

module Setoid.Fam where

open import Agda.Primitive
private
  module G where
    open import Groupoid public
      hiding (module Map)
    module I where
      module SETOID where
        open import Groupoid.Instances.SETOID public
    module Map where
      open Groupoid.Map public
      open import Groupoid.Presheaf public
import Setoid as S
open import Type as T
  using (_,_)

record Fam₀
  {ιˢ} ..{ℓ₀ᵒ ℓ₀ʰ}
  (I : S.t ιˢ ℓ₀ᵒ ℓ₀ʰ)
  ..(ℓ₁ᵒ ℓ₁ʰ : _)
    : Set ((ℓ₀ᵒ ⊔ ℓ₀ʰ) ⊔ lsuc (ℓ₁ᵒ ⊔ ℓ₁ʰ)) where
  no-eta-equality
  field
    fam : G.S↑G≤ I G.Map.⇏₀ᵗ G.I.SETOID.c ℓ₁ᵒ ℓ₁ʰ

  fib : ∀ i → S.t _ _ _
  fib = G.Map._$₀_ fam

  coe
    : ∀ {i₀ i₁}
    → (ρ : S.homᵗ I (i₀ , i₁))
    → fib i₁ S.Map.⇒₀ᵗ fib i₀
  coe ρ = G.Map._$₁_ fam ρ

  field
    irr
      : ∀ {i₀ i₁}
      → (ρ₀ ρ₁ : S.homᵗ I (i₀ , i₁))
      → coe ρ₀ S.Map.⇒₁ coe ρ₁

record Fam₁
  {ιˢ}
  ..{ℓ₀₀ᵒ ℓ₀₀ʰ ℓ₀₁ᵒ ℓ₀₁ʰ ℓ₁₀ᵒ ℓ₁₀ʰ ℓ₁₁ᵒ ℓ₁₁ʰ}
  {I₀ : S.t ιˢ ℓ₀₀ᵒ ℓ₀₀ʰ}
  {I₁ : S.t ιˢ ℓ₁₀ᵒ ℓ₁₀ʰ}
  (Ψ₀ : Fam₀ I₀ ℓ₀₁ᵒ ℓ₀₁ʰ)
  (Ψ₁ : Fam₀ I₁ ℓ₁₁ᵒ ℓ₁₁ʰ)
    : Set (((ℓ₀₀ᵒ ⊔ ℓ₀₀ʰ) ⊔ (ℓ₀₁ᵒ ⊔ ℓ₀₁ʰ))
         ⊔ ((ℓ₁₀ᵒ ⊔ ℓ₁₀ʰ) ⊔ (ℓ₁₁ᵒ ⊔ ℓ₁₁ʰ))) where
  no-eta-equality
  field
    idx
      : I₀ S.Map.⇒₀ᵗ I₁
    fib
      : (open Fam₀)
      → ∀ i
      → fib Ψ₀ i S.Map.⇒₀ᵗ fib Ψ₁ (idx S.Map.$₀ i)
    coh
      : (open S.Map)
      → (open Fam₀ hiding (fib))
      → ∀ {i₀ i₁}
      → (ρ : S.homᵗ I₀ (i₀ , i₁))
      →  fib i₀ ∘₀ coe Ψ₀ ρ
      ⇒₁ coe Ψ₁ (idx $₁ ρ) ∘₀ fib i₁

record ∏₀ {ιˢ} ..{ℓ₀ᵒ ℓ₀ʰ} {I : S.t ιˢ ℓ₀ᵒ ℓ₀ʰ} ..{ℓ₁ᵒ ℓ₁ʰ} (Ψ : Fam₀ I ℓ₁ᵒ ℓ₁ʰ) : Set (ℓ₀ᵒ ⊔ ℓ₀ʰ ⊔ ℓ₁ᵒ ⊔ ℓ₁ʰ) where
  field
    act
      : ∀ i
      → S.obj (Fam₀.fib Ψ i)
    coh
      : (open S.Map) (open Fam₀)
      → ∀ i j
      → (ρ : S.homᵗ I (i , j))
      → S.homᵗ (fib Ψ i) (act i , coe Ψ ρ $₀ act j)

∏₁
  : {ιˢ : _} ..{ℓ₀ᵒ ℓ₀ʰ : _} {I : S.t ιˢ ℓ₀ᵒ ℓ₀ʰ} ..{ℓ₁ᵒ ℓ₁ʰ : _}
  → {Ψ : Fam₀ I ℓ₁ᵒ ℓ₁ʰ}
  → (f g : ∏₀ Ψ)
  → Set (ℓ₀ᵒ ⊔ ℓ₀ʰ ⊔ ℓ₁ʰ)
∏₁ {I = I} {Ψ = Ψ} f g =
  ∀ i j
    → (ρ : S.homᵗ I (i , j))
    → (open Fam₀) (open S.Map) (open ∏₀)
    → S.homᵗ
        (fib Ψ i)
        ( act f i
        , coe Ψ ρ $₀ act g j
        )

record ∐₀ {ιˢ} ..{ℓ₀ᵒ ℓ₀ʰ} {I : S.t ιˢ ℓ₀ᵒ ℓ₀ʰ} ..{ℓ₁ᵒ ℓ₁ʰ} (Ψ : Fam₀ I ℓ₁ᵒ ℓ₁ʰ) : Set (ℓ₀ᵒ ⊔ ℓ₀ʰ ⊔ ℓ₁ᵒ ⊔ ℓ₁ʰ) where
  constructor _,_
  field
    fst : S.obj I
    snd : S.obj (Fam₀.fib Ψ fst)

record ∐₁ {ιˢ} ..{ℓ₀ᵒ ℓ₀ʰ} {I : S.t ιˢ ℓ₀ᵒ ℓ₀ʰ} ..{ℓ₁ᵒ ℓ₁ʰ} {Ψ : Fam₀ I ℓ₁ᵒ ℓ₁ʰ} (p q : ∐₀ Ψ) : Set (ℓ₀ᵒ ⊔ ℓ₀ʰ ⊔ ℓ₁ʰ) where
  constructor _,_
  field
    fst : S.homᵗ I ((∐₀.fst p) , (∐₀.fst q))
    snd : S.homᵗ (Fam₀.fib Ψ (∐₀.fst p)) ((∐₀.snd p) , Fam₀.coe Ψ fst S.Map.$₀ ∐₀.snd q)

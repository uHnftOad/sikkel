--------------------------------------------------
-- Definition of the mode theory for unary parametricity
--------------------------------------------------

module Applications.UnaryParametricity.MSTT.ModeTheory where

open import Data.String
open import Relation.Binary.PropositionalEquality

open import Model.BaseCategory as M hiding (★; ¶)
open import Model.CwF-Structure as M
open import Model.Modality as M hiding (𝟙; _ⓜ_; id-cell)
open import Applications.UnaryParametricity.Model as M hiding (forget-right)

open import MSTT.TCMonad
open import MSTT.Parameter.ModeTheory


--------------------------------------------------
-- Expressions representing modes and modalities
-- We will not use 2-cells in this application, so only the trivial one is present.

data ModeExpr : Set where
  ★ ¶ : ModeExpr

private
  variable
    m m' m'' : ModeExpr

data ModalityExpr : ModeExpr → ModeExpr → Set where
  𝟙 : ModalityExpr m m
  forget-right : ModalityExpr ¶ ★

_ⓜ_ : ModalityExpr m' m'' → ModalityExpr m m' → ModalityExpr m m''
𝟙 ⓜ ρ = ρ
forget-right ⓜ 𝟙 = forget-right

data TwoCellExpr : Set where
  id-cell : TwoCellExpr


--------------------------------------------------
-- Printing mode and modality expressions (mostly for type errors)

show-mode : ModeExpr → String
show-mode ★ = "★"
show-mode ¶ = "¶"

show-modality : ModalityExpr m m' → String
show-modality 𝟙 = "𝟙"
show-modality forget-right = "forget-right"


--------------------------------------------------
-- Interpretation of modes and modalities in a presheaf model

⟦_⟧mode : ModeExpr → BaseCategory
⟦ ★ ⟧mode = M.★
⟦ ¶ ⟧mode = M.¶

⟦_⟧modality : ModalityExpr m m' → Modality ⟦ m ⟧mode ⟦ m' ⟧mode
⟦ 𝟙 ⟧modality = M.𝟙
⟦ forget-right ⟧modality = M.forget-right
ⓜ-interpretation : (μ : ModalityExpr m' m'') (ρ : ModalityExpr m m') →
                   ⟦ μ ⓜ ρ ⟧modality ≅ᵐ ⟦ μ ⟧modality M.ⓜ ⟦ ρ ⟧modality
ⓜ-interpretation 𝟙 ρ = symᵐ (𝟙-identityˡ ⟦ ρ ⟧modality)
ⓜ-interpretation forget-right 𝟙 = symᵐ (𝟙-identityʳ M.forget-right)


--------------------------------------------------
-- Equivalence of modes and modalities

_≟mode_ : (m1 m2 : ModeExpr) → TCM (m1 ≡ m2)
★ ≟mode ★ = return refl
¶ ≟mode ¶ = return refl
m ≟mode m' = type-error ("Mode " ++ show-mode m ++ " is not equal to " ++ show-mode m')

_≟modality_ : (μ ρ : ModalityExpr m m') → TCM (μ ≡ ρ)
𝟙 ≟modality 𝟙 = return refl
forget-right ≟modality forget-right = return refl
μ ≟modality ρ = type-error ("Modality " ++ show-modality μ ++ " is not equal to " ++ show-modality ρ)

-- There are no interesting equivalences of modalities, we just check whether they are identical.
_≃ᵐ?_ : (μ ρ : ModalityExpr m m') → TCM (⟦ μ ⟧modality ≅ᵐ ⟦ ρ ⟧modality)
μ ≃ᵐ? ρ = do
  refl ← μ ≟modality ρ
  return reflᵐ


--------------------------------------------------
-- Interpretation of two-cells in a presheaf model

⟦_∈_⇒_⟧two-cell : TwoCellExpr → ∀ {m m'} (μ ρ : ModalityExpr m m') → TCM (TwoCell ⟦ μ ⟧modality ⟦ ρ ⟧modality)
⟦ id-cell ∈ μ ⇒ ρ ⟧two-cell = do
  μ=ρ ← μ ≃ᵐ? ρ
  return (M.≅ᵐ-to-2-cell μ=ρ)


--------------------------------------------------
-- The final definition of the mode theory

unary-par-mode-theory : ModeTheory
ModeTheory.ModeExpr unary-par-mode-theory = ModeExpr
ModeTheory.show-mode unary-par-mode-theory = show-mode
ModeTheory.⟦_⟧mode unary-par-mode-theory = ⟦_⟧mode
ModeTheory._≟mode_ unary-par-mode-theory = _≟mode_
ModeTheory.ModalityExpr unary-par-mode-theory = ModalityExpr
ModeTheory.𝟙 unary-par-mode-theory = 𝟙
ModeTheory._ⓜ_ unary-par-mode-theory = _ⓜ_
ModeTheory.show-modality unary-par-mode-theory = show-modality
ModeTheory.⟦_⟧modality unary-par-mode-theory = ⟦_⟧modality
ModeTheory.𝟙-interpretation unary-par-mode-theory = reflᵐ
ModeTheory.ⓜ-interpretation unary-par-mode-theory = ⓜ-interpretation
ModeTheory._≃ᵐ?_ unary-par-mode-theory = _≃ᵐ?_
ModeTheory.TwoCellExpr unary-par-mode-theory = TwoCellExpr
ModeTheory.id-cell unary-par-mode-theory = id-cell
ModeTheory.⟦_∈_⇒_⟧two-cell unary-par-mode-theory = ⟦_∈_⇒_⟧two-cell

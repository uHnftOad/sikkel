--------------------------------------------------
-- Specification of new type constructors for parametricity
--------------------------------------------------

open import Applications.UnaryParametricity.MSTT.TypeExtension.PredExtension

module Applications.UnaryParametricity.MSTT.TypeExtension (pred-ext : PredExt) where

open import Data.List
open import Relation.Binary.PropositionalEquality

open import Model.CwF-Structure as M
open import Applications.UnaryParametricity.Model as M hiding (FromPred)

open import MSTT.TCMonad
open import Applications.UnaryParametricity.MSTT.ModeTheory
open import MSTT.Parameter.TypeExtension unary-par-mode-theory

open PredExt pred-ext

private variable
  m : ModeExpr
  margs : List ModeExpr

data ParTyCode : List ModeExpr → ModeExpr → Set where
  FromPred-code : PredCode → ParTyCode [] ¶
    -- PredCode = PredExt.PredCode pred-ext

_≟par-code_ : (c1 c2 : ParTyCode margs m) → TCM (c1 ≡ c2)
FromPred-code c1 ≟par-code FromPred-code c2 = do
  refl ← c1 ≟code c2
  return refl

show-par-code : ParTyCode margs m → TyExtShow margs
show-par-code (FromPred-code c) = show-code c

interpret-par-code : ParTyCode margs m → TyConstructor margs m
  -- TyConstructor margs m = ClosedTy ⟦ ¶ ⟧mode
interpret-par-code (FromPred-code c) = M.FromPred (CodeLeft c) (CodeRelation c)

interpret-par-code-natural : (c : ParTyCode margs m) → TyConstructorNatural (interpret-par-code c)
interpret-par-code-natural (FromPred-code c) = frompred-natural

interpret-par-code-cong : (c : ParTyCode margs m) → TyConstructorCong (interpret-par-code c)
interpret-par-code-cong (FromPred-code c) = reflᵗʸ

par-ty-ext : TyExt
TyExt.TyExtCode par-ty-ext = ParTyCode
TyExt._≟code_ par-ty-ext = _≟par-code_
TyExt.show-code par-ty-ext = show-par-code
TyExt.interpret-code par-ty-ext = interpret-par-code
TyExt.interpret-code-natural par-ty-ext = interpret-par-code-natural
TyExt.interpret-code-cong par-ty-ext = interpret-par-code-cong

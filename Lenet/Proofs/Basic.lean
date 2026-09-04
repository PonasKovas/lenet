import Lenet.Constants

/-!
# Shared proof infrastructure

rfl-level equations for `Except`'s monad combinators at the exact instance
paths the do-notation produces (`Except.instMonad` projections,
`instMonadExceptOfMonadExceptOf (instMonadExceptOfExcept ...)` for `throw`).
`simp` cannot see through these projections on its own; the lemmas are stated
at the concrete paths so they match the desugared terms and hold by `rfl`.
-/

namespace Lenet.Proofs

/-- The do-notation's `throw` lands in `Except.error`. -/
theorem Except.throw_eq' {ε : Type u} {α : Type v} (e : ε) :
    (@throw ε (Except ε)
      (@instMonadExceptOfMonadExceptOf ε (Except ε) (instMonadExceptOfExcept ε)) α e) =
    (Except.error e : Except ε α) := rfl

/-- The do-notation's `pure` lands in `Except.ok`. -/
theorem Except.pure_eq' {ε : Type u} {α : Type v} (a : α) :
    (@pure (Except ε)
      (@Applicative.toPure (Except ε) (@Monad.toApplicative (Except ε) (@Except.instMonad ε))) α a) =
    (Except.ok a : Except ε α) := rfl

/-- The do-notation's `bind` on `.ok` continues with the bound value. -/
theorem Except.bind_ok' {ε : Type u} {α β : Type v} (a : α) (f : α → Except ε β) :
    (@bind (Except ε) (@Monad.toBind (Except ε) (@Except.instMonad ε)) α β (Except.ok a) f) =
    f a := rfl

/-- The do-notation's `bind` on `.error` short-circuits. -/
theorem Except.bind_error' {ε : Type u} {α β : Type v} (e : ε) (f : α → Except ε β) :
    (@bind (Except ε) (@Monad.toBind (Except ε) (@Except.instMonad ε)) α β (Except.error e) f) =
    (Except.error e : Except ε β) := rfl

/-- The do-notation's `<\$>` on `.ok` transforms the value. -/
theorem Except.map_ok' {ε : Type u} {α β : Type v} (f : α → β) (a : α) :
    (@Functor.map (Except ε)
      (@Applicative.toFunctor (Except ε) (@Monad.toApplicative (Except ε) (@Except.instMonad ε)))
      α β f (Except.ok a)) =
    (Except.ok (f a) : Except ε β) := rfl

/-- The do-notation's `<\$>` on `.error` short-circuits. -/
theorem Except.map_error' {ε : Type u} {α β : Type v} (f : α → β) (e : ε) :
    (@Functor.map (Except ε)
      (@Applicative.toFunctor (Except ε) (@Monad.toApplicative (Except ε) (@Except.instMonad ε)))
      α β f (Except.error e)) =
    (Except.error e : Except ε β) := rfl

end Lenet.Proofs

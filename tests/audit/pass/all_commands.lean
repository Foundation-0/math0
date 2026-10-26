import Math0.Audit
-- Each audit command accepts a correct, sorry-free result.
theorem upstream : ∀ n : Nat, n + 0 = n := sorry
theorem ours : ∀ n : Nat, n + 0 = n := fun _ => rfl
#math0_proves ours upstream
theorem upstreamFalse : ∀ n : Nat, n + 1 = n := sorry
theorem oursNeg : ¬ ∀ n : Nat, n + 1 = n := fun h => by simpa using h 0
#math0_refutes oursNeg upstreamFalse
def statement : Prop := ∀ n : Nat, n + 0 = n
theorem result : statement := fun _ => rfl
#math0_settles result statement
def statement2 : Prop := ∀ n : Nat, n + 1 = n
theorem result2 : ¬ statement2 := fun h => by simpa using h 0
#math0_settles result2 statement2
def answer : Nat := sorry
theorem upstreamAns : answer = 4 := sorry
def ourAnswer : Nat := 4
theorem oursAns : ourAnswer = 4 := rfl
#math0_answers oursAns upstreamAns with answer := ourAnswer
theorem upstreamBad : answer + 1 = answer := sorry
theorem oursEvery : ∀ a : Nat, ¬ (a + 1 = a) := fun a h => by omega
#math0_refutes_every_answer oursEvery upstreamBad with answer

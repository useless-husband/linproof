import Linproof

/-! Prints the axioms every main theorem depends on. `scripts/check-proofs.sh` fails unless
they are among Lean's three standard axioms: `propext`, `Classical.choice`, `Quot.sound`. -/

#print axioms Linproof.Theorems.checker_correct
#print axioms Linproof.Theorems.memo_correct
#print axioms Linproof.Theorems.keyed_locality
#print axioms Linproof.Theorems.register_correct
#print axioms Linproof.Theorems.casRegister_correct
#print axioms Linproof.Theorems.keyedRegister_correct
#print axioms Linproof.Theorems.keyedCasRegister_correct
#print axioms Linproof.Theorems.kvStore_correct
#print axioms Linproof.Theorems.wellFormed_decided

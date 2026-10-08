import Kuramoto

/-! Lists the axioms used by the main results. Run with `lake env lean scripts/print_axioms.lean`.
Besides Lean's three standard axioms (`propext`, `Classical.choice`, `Quot.sound`), the output
should list exactly the four cited results described in `README.md`. -/

#print axioms Kuramoto.main_theorem
#print axioms Kuramoto.glue_consequently
#print axioms Kuramoto.Random.gadgetcount
#print axioms Kuramoto.prop_cert
#print axioms Kuramoto.Gadget.etabounds

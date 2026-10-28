import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7540 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7540 = true := by
  decide +kernel

theorem tot7540 : totK PA10K2 A10K2.t7540 = [0, 0, 388342569781, 1762166407045, 2087339271567, 538230189928, 32040661968, 0, 0, 0] := by
  decide +kernel

theorem rows7541 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7541 = true := by
  decide +kernel

theorem tot7541 : totK PA10K2 A10K2.t7541 = [0, 0, 299445560447, 1142226839941, 1867070584590, 1192523329155, 188182963997, 5460492893, 0, 0] := by
  decide +kernel

theorem rows7542 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7542 = true := by
  decide +kernel

theorem tot7542 : totK PA10K2 A10K2.t7542 = [0, 0, 425178386862, 1740210439524, 2025865598511, 590316478548, 32846095359, 0, 0, 0] := by
  decide +kernel

theorem rows7543 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7543 = true := by
  decide +kernel

theorem tot7543 : totK PA10K2 A10K2.t7543 = [0, 0, 42135479438, 823008091155, 2093430998234, 1475803107099, 311785105280, 24969229125, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2

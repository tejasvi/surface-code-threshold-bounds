import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows256 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t256 = true := by
  decide +kernel

theorem tot256 : totK PA10K2 A10K2.t256 = [0, 0, 546179801325, 1980456236382, 1973081585351, 441838847906, 13544844466, 0, 0, 0] := by
  decide +kernel

theorem rows257 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t257 = true := by
  decide +kernel

theorem tot257 : totK PA10K2 A10K2.t257 = [0, 0, 417058886421, 1614066306613, 2026710205616, 823298616459, 74707952681, 0, 0, 0] := by
  decide +kernel

theorem rows258 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t258 = true := by
  decide +kernel

theorem tot258 : totK PA10K2 A10K2.t258 = [0, 0, 396445639460, 1692210855951, 2039718736246, 710523681990, 47291235044, 0, 0, 0] := by
  decide +kernel

theorem rows259 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t259 = true := by
  decide +kernel

theorem tot259 : totK PA10K2 A10K2.t259 = [0, 0, 0, 734048278023, 2255066292823, 1598981998293, 250823167017, 6904928264, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2

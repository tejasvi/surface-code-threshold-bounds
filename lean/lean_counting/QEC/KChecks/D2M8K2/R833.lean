import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3332 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3332 = true := by
  decide +kernel

theorem tot3332 : totK PD2M8K2 D2M8K2.t3332 = [0, 73553217827, 346491879972, 386494080593, 70797479964, 1096505104, 0, 0] := by
  decide +kernel

theorem rows3333 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3333 = true := by
  decide +kernel

theorem tot3333 : totK PD2M8K2 D2M8K2.t3333 = [0, 0, 264318426644, 505862206272, 117019729916, 3884009855, 0, 0] := by
  decide +kernel

theorem rows3334 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3334 = true := by
  decide +kernel

theorem tot3334 : totK PD2M8K2 D2M8K2.t3334 = [0, 183093067607, 447169472584, 242641773420, 22753051930, 0, 0, 0] := by
  decide +kernel

theorem rows3335 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3335 = true := by
  decide +kernel

theorem tot3335 : totK PD2M8K2 D2M8K2.t3335 = [0, 199015822070, 480050342529, 219695255980, 12420291143, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

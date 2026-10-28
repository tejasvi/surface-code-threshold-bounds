import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows8332 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8332 = true := by
  decide +kernel

theorem tot8332 : totK PD2M8K2 D2M8K2.t8332 = [180114736652, 459149593087, 248626962216, 17034666133, 0, 0, 0, 0] := by
  decide +kernel

theorem rows8333 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8333 = true := by
  decide +kernel

theorem tot8333 : totK PD2M8K2 D2M8K2.t8333 = [0, 302105844791, 500678122403, 93388046399, 1096505104, 0, 0, 0] := by
  decide +kernel

theorem rows8334 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8334 = true := by
  decide +kernel

theorem tot8334 : totK PD2M8K2 D2M8K2.t8334 = [0, 272431348890, 497326481016, 124635077563, 3884009855, 0, 0, 0] := by
  decide +kernel

theorem rows8335 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8335 = true := by
  decide +kernel

theorem tot8335 : totK PD2M8K2 D2M8K2.t8335 = [0, 172752881409, 471690456545, 209083334977, 10926248329, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

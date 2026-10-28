import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows12396 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12396 = true := by
  decide +kernel

theorem tot12396 : totK PD2M8K2 D2M8K2.t12396 = [0, 161483599102, 442054903971, 251364908738, 17954844860, 0, 0, 0] := by
  decide +kernel

theorem rows12397 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12397 = true := by
  decide +kernel

theorem tot12397 : totK PD2M8K2 D2M8K2.t12397 = [0, 0, 282969509618, 502819027092, 99171162065, 1310166938, 0, 0] := by
  decide +kernel

theorem rows12398 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12398 = true := by
  decide +kernel

theorem tot12398 : totK PD2M8K2 D2M8K2.t12398 = [0, 122716139554, 382524496586, 361903554418, 46290961336, 0, 0, 0] := by
  decide +kernel

theorem rows12399 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12399 = true := by
  decide +kernel

theorem tot12399 : totK PD2M8K2 D2M8K2.t12399 = [0, 196506978144, 481408474023, 228578274278, 13541533318, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

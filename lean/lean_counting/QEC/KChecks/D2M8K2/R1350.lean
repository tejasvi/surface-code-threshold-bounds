import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5400 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5400 = true := by
  decide +kernel

theorem tot5400 : totK PD2M8K2 D2M8K2.t5400 = [0, 0, 0, 213130399087, 494143098531, 170646215630, 6583681375, 0] := by
  decide +kernel

theorem rows5401 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5401 = true := by
  decide +kernel

theorem tot5401 : totK PD2M8K2 D2M8K2.t5401 = [0, 0, 175195872452, 450011711499, 266794235240, 31599384181, 0, 0] := by
  decide +kernel

theorem rows5402 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5402 = true := by
  decide +kernel

theorem tot5402 : totK PD2M8K2 D2M8K2.t5402 = [0, 0, 199569630606, 485252197913, 212004444735, 10905823918, 0, 0] := by
  decide +kernel

theorem rows5403 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5403 = true := by
  decide +kernel

theorem tot5403 : totK PD2M8K2 D2M8K2.t5403 = [0, 0, 34532533563, 336491690037, 456030765791, 78238788256, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

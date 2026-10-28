import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows8480 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8480 = true := by
  decide +kernel

theorem tot8480 : totK PD2M8K2 D2M8K2.t8480 = [0, 0, 239294429560, 505358814735, 141072438453, 3382902891, 0, 0] := by
  decide +kernel

theorem rows8481 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8481 = true := by
  decide +kernel

theorem tot8481 : totK PD2M8K2 D2M8K2.t8481 = [0, 111581961659, 390226093707, 341343378172, 55282530299, 1755554482, 0, 0] := by
  decide +kernel

theorem rows8482 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8482 = true := by
  decide +kernel

theorem tot8482 : totK PD2M8K2 D2M8K2.t8482 = [0, 177251721247, 448403019369, 264897099257, 28411775433, 0, 0, 0] := by
  decide +kernel

theorem rows8483 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8483 = true := by
  decide +kernel

theorem tot8483 : totK PD2M8K2 D2M8K2.t8483 = [0, 125356162473, 432493383449, 315362353446, 27611694469, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

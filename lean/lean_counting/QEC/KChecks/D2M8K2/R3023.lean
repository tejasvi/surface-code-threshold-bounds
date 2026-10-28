import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows12092 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12092 = true := by
  decide +kernel

theorem tot12092 : totK PD2M8K2 D2M8K2.t12092 = [0, 86583854384, 256521736348, 365217502898, 168537485406, 6557415438, 0, 0] := by
  decide +kernel

theorem rows12093 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12093 = true := by
  decide +kernel

theorem tot12093 : totK PD2M8K2 D2M8K2.t12093 = [0, 183174724504, 464913281492, 256594178690, 23817559202, 0, 0, 0] := by
  decide +kernel

theorem rows12094 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12094 = true := by
  decide +kernel

theorem tot12094 : totK PD2M8K2 D2M8K2.t12094 = [0, 175730764912, 480132853967, 242670089079, 12597559134, 0, 0, 0] := by
  decide +kernel

theorem rows12095 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12095 = true := by
  decide +kernel

theorem tot12095 : totK PD2M8K2 D2M8K2.t12095 = [0, 0, 275650772368, 508480073402, 116253688345, 1198073392, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

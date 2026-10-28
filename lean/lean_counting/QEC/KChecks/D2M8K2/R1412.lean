import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5648 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5648 = true := by
  decide +kernel

theorem tot5648 : totK PD2M8K2 D2M8K2.t5648 = [179064765202, 451700114272, 256764174008, 27736490888, 0, 0, 0, 0] := by
  decide +kernel

theorem rows5649 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5649 = true := by
  decide +kernel

theorem tot5649 : totK PD2M8K2 D2M8K2.t5649 = [96612252995, 386354726200, 348482995404, 56817827936, 1198073392, 0, 0, 0] := by
  decide +kernel

theorem rows5650 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5650 = true := by
  decide +kernel

theorem tot5650 : totK PD2M8K2 D2M8K2.t5650 = [0, 207386118494, 479678744865, 177583257473, 9478200669, 0, 0, 0] := by
  decide +kernel

theorem rows5651 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5651 = true := by
  decide +kernel

theorem tot5651 : totK PD2M8K2 D2M8K2.t5651 = [153082395507, 415407172206, 275389560056, 62024008807, 2567510802, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

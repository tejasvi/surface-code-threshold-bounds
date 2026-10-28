import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5456 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5456 = true := by
  decide +kernel

theorem tot5456 : totK PD2M8K2 D2M8K2.t5456 = [0, 0, 159750447925, 454777319285, 269965473487, 23701846778, 0, 0] := by
  decide +kernel

theorem rows5457 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5457 = true := by
  decide +kernel

theorem tot5457 : totK PD2M8K2 D2M8K2.t5457 = [0, 0, 182261201038, 470630361036, 251925097816, 15627465686, 0, 0] := by
  decide +kernel

theorem rows5458 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5458 = true := by
  decide +kernel

theorem tot5458 : totK PD2M8K2 D2M8K2.t5458 = [0, 0, 0, 255726105112, 496935128030, 129611020261, 1268739303, 0] := by
  decide +kernel

theorem rows5459 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5459 = true := by
  decide +kernel

theorem tot5459 : totK PD2M8K2 D2M8K2.t5459 = [0, 0, 0, 181019388762, 474196615334, 219613959382, 10145025036, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

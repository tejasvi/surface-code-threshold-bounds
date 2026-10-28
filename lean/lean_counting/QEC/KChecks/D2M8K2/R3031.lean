import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows12124 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12124 = true := by
  decide +kernel

theorem tot12124 : totK PD2M8K2 D2M8K2.t12124 = [0, 173240625605, 435992998007, 277707367669, 34463403080, 0, 0, 0] := by
  decide +kernel

theorem rows12125 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12125 = true := by
  decide +kernel

theorem tot12125 : totK PD2M8K2 D2M8K2.t12125 = [0, 195325133101, 480829543047, 227630836515, 12417015735, 0, 0, 0] := by
  decide +kernel

theorem rows12126 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12126 = true := by
  decide +kernel

theorem tot12126 : totK PD2M8K2 D2M8K2.t12126 = [0, 49739141399, 300294737966, 404433360157, 148618819260, 9654694938, 0, 0] := by
  decide +kernel

theorem rows12127 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12127 = true := by
  decide +kernel

theorem tot12127 : totK PD2M8K2 D2M8K2.t12127 = [0, 0, 211719313495, 500437805609, 186450537473, 5411637735, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

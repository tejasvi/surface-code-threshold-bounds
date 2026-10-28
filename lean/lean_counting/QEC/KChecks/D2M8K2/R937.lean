import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3748 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3748 = true := by
  decide +kernel

theorem tot3748 : totK PD2M8K2 D2M8K2.t3748 = [0, 199675777855, 475204998073, 218105613618, 12239393083, 0, 0, 0] := by
  decide +kernel

theorem rows3749 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3749 = true := by
  decide +kernel

theorem tot3749 : totK PD2M8K2 D2M8K2.t3749 = [0, 19374756099, 369559440476, 456500616693, 59873965205, 0, 0, 0] := by
  decide +kernel

theorem rows3750 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3750 = true := by
  decide +kernel

theorem tot3750 : totK PD2M8K2 D2M8K2.t3750 = [0, 56019812579, 245139831681, 429819649515, 153101541452, 5218872685, 0, 0] := by
  decide +kernel

theorem rows3751 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3751 = true := by
  decide +kernel

theorem tot3751 : totK PD2M8K2 D2M8K2.t3751 = [0, 171038804698, 440471505909, 277656419107, 30196964437, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

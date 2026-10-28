import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7960 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7960 = true := by
  decide +kernel

theorem tot7960 : totK PD2M8K2 D2M8K2.t7960 = [0, 0, 0, 324125882892, 498957407109, 76094587210, 0, 0] := by
  decide +kernel

theorem rows7961 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7961 = true := by
  decide +kernel

theorem tot7961 : totK PD2M8K2 D2M8K2.t7961 = [0, 0, 0, 165254150541, 477967443247, 197121996686, 10738855752, 0] := by
  decide +kernel

theorem rows7962 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7962 = true := by
  decide +kernel

theorem tot7962 : totK PD2M8K2 D2M8K2.t7962 = [0, 0, 0, 164070283488, 462540257216, 216802803634, 12387674754, 0] := by
  decide +kernel

theorem rows7963 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7963 = true := by
  decide +kernel

theorem tot7963 : totK PD2M8K2 D2M8K2.t7963 = [0, 0, 0, 7564999111, 343882136074, 407046649692, 61599577640, 1209030869] := by
  decide +kernel

end QECKChecks.D2M8K2

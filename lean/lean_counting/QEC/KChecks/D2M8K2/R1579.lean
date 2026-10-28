import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6316 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6316 = true := by
  decide +kernel

theorem tot6316 : totK PD2M8K2 D2M8K2.t6316 = [0, 0, 315828095812, 513428111634, 69518914604, 0, 0, 0] := by
  decide +kernel

theorem rows6317 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6317 = true := by
  decide +kernel

theorem tot6317 : totK PD2M8K2 D2M8K2.t6317 = [0, 156992247839, 399071202539, 266379110672, 74943058993, 3820764243, 0, 0] := by
  decide +kernel

theorem rows6318 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6318 = true := by
  decide +kernel

theorem tot6318 : totK PD2M8K2 D2M8K2.t6318 = [0, 186063758082, 455430473387, 233989064610, 16976715513, 0, 0, 0] := by
  decide +kernel

theorem rows6319 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6319 = true := by
  decide +kernel

theorem tot6319 : totK PD2M8K2 D2M8K2.t6319 = [0, 66237210429, 328728370404, 408413862610, 92602954963, 1268739303, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

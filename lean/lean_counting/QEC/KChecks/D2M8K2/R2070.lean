import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows8280 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8280 = true := by
  decide +kernel

theorem tot8280 : totK PD2M8K2 D2M8K2.t8280 = [177478304220, 480258582576, 228185981726, 11034354488, 0, 0, 0, 0] := by
  decide +kernel

theorem rows8281 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8281 = true := by
  decide +kernel

theorem tot8281 : totK PD2M8K2 D2M8K2.t8281 = [171709740222, 457677086411, 248172729470, 15244595069, 0, 0, 0, 0] := by
  decide +kernel

theorem rows8282 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8282 = true := by
  decide +kernel

theorem tot8282 : totK PD2M8K2 D2M8K2.t8282 = [0, 272191041356, 508264716332, 111941129000, 1369150432, 0, 0, 0] := by
  decide +kernel

theorem rows8283 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8283 = true := by
  decide +kernel

theorem tot8283 : totK PD2M8K2 D2M8K2.t8283 = [90151632724, 385963459987, 401401409915, 52129977080, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

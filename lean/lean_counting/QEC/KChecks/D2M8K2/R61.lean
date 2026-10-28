import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows244 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t244 = true := by
  decide +kernel

theorem tot244 : totK PD2M8K2 D2M8K2.t244 = [0, 7559944729, 196496039190, 475394850947, 198275631647, 12482056447, 0, 0] := by
  decide +kernel

theorem rows245 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t245 = true := by
  decide +kernel

theorem tot245 : totK PD2M8K2 D2M8K2.t245 = [0, 200385716596, 483971103969, 201358605680, 9852138406, 0, 0, 0] := by
  decide +kernel

theorem rows246 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t246 = true := by
  decide +kernel

theorem tot246 : totK PD2M8K2 D2M8K2.t246 = [0, 193453068959, 468790275852, 217202207500, 12534051746, 0, 0, 0] := by
  decide +kernel

theorem rows247 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t247 = true := by
  decide +kernel

theorem tot247 : totK PD2M8K2 D2M8K2.t247 = [0, 18544188537, 290770358629, 459404529616, 105118462915, 1369150432, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

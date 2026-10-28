import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3224 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3224 = true := by
  decide +kernel

theorem tot3224 : totK PD2M8K2 D2M8K2.t3224 = [0, 38089888464, 341785398778, 422453246685, 67233245962, 1138244013, 0, 0] := by
  decide +kernel

theorem rows3225 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3225 = true := by
  decide +kernel

theorem tot3225 : totK PD2M8K2 D2M8K2.t3225 = [0, 180517621553, 443023811091, 263004630045, 29137860636, 0, 0, 0] := by
  decide +kernel

theorem rows3226 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3226 = true := by
  decide +kernel

theorem tot3226 : totK PD2M8K2 D2M8K2.t3226 = [0, 197626357478, 500850501492, 203734529165, 10179897161, 0, 0, 0] := by
  decide +kernel

theorem rows3227 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3227 = true := by
  decide +kernel

theorem tot3227 : totK PD2M8K2 D2M8K2.t3227 = [0, 155454485926, 458659587499, 273141537817, 18012710461, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

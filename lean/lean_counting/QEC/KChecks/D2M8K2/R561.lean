import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2244 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2244 = true := by
  decide +kernel

theorem tot2244 : totK PD2M8K2 D2M8K2.t2244 = [0, 155082416523, 452939960709, 263585568962, 20310204301, 0, 0, 0] := by
  decide +kernel

theorem rows2245 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2245 = true := by
  decide +kernel

theorem tot2245 : totK PD2M8K2 D2M8K2.t2245 = [0, 0, 252126595558, 501160750863, 128288474488, 2309606161, 0, 0] := by
  decide +kernel

theorem rows2246 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2246 = true := by
  decide +kernel

theorem tot2246 : totK PD2M8K2 D2M8K2.t2246 = [0, 68395520429, 244791461039, 394887066426, 154618517249, 10740121073, 0, 0] := by
  decide +kernel

theorem rows2247 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2247 = true := by
  decide +kernel

theorem tot2247 : totK PD2M8K2 D2M8K2.t2247 = [0, 176647366119, 460115086621, 246660212798, 22498961287, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

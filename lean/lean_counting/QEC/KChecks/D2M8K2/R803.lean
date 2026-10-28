import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3212 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3212 = true := by
  decide +kernel

theorem tot3212 : totK PD2M8K2 D2M8K2.t3212 = [0, 219514614476, 489884223655, 169708569878, 8143100748, 0, 0, 0] := by
  decide +kernel

theorem rows3213 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3213 = true := by
  decide +kernel

theorem tot3213 : totK PD2M8K2 D2M8K2.t3213 = [117107903659, 349346262101, 318078245448, 83668246502, 4906626486, 0, 0, 0] := by
  decide +kernel

theorem rows3214 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3214 = true := by
  decide +kernel

theorem tot3214 : totK PD2M8K2 D2M8K2.t3214 = [171504075684, 442669473614, 274473971334, 30374593025, 0, 0, 0, 0] := by
  decide +kernel

theorem rows3215 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3215 = true := by
  decide +kernel

theorem tot3215 : totK PD2M8K2 D2M8K2.t3215 = [135213239290, 444118179293, 297213546771, 22306961959, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

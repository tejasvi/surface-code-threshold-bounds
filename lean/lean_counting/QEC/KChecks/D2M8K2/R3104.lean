import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows12416 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12416 = true := by
  decide +kernel

theorem tot12416 : totK PD2M8K2 D2M8K2.t12416 = [0, 0, 278567892668, 500818415376, 101837178744, 1310517177, 0, 0] := by
  decide +kernel

theorem rows12417 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12417 = true := by
  decide +kernel

theorem tot12417 : totK PD2M8K2 D2M8K2.t12417 = [0, 92870497502, 384972211716, 392952316180, 44603690845, 0, 0, 0] := by
  decide +kernel

theorem rows12418 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12418 = true := by
  decide +kernel

theorem tot12418 : totK PD2M8K2 D2M8K2.t12418 = [0, 197852470367, 465177078988, 240648102564, 18007257308, 0, 0, 0] := by
  decide +kernel

theorem rows12419 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12419 = true := by
  decide +kernel

theorem tot12419 : totK PD2M8K2 D2M8K2.t12419 = [0, 122768700473, 437257655543, 307089427461, 34476849214, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

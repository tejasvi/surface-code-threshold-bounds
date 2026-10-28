import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows12532 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12532 = true := by
  decide +kernel

theorem tot12532 : totK PD2M8K2 D2M8K2.t12532 = [0, 0, 177164274657, 491921590669, 226579536643, 7682042144, 0, 0] := by
  decide +kernel

theorem rows12533 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12533 = true := by
  decide +kernel

theorem tot12533 : totK PD2M8K2 D2M8K2.t12533 = [0, 54494369517, 219032013519, 405456758814, 202143986663, 12202766382, 0, 0] := by
  decide +kernel

theorem rows12534 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12534 = true := by
  decide +kernel

theorem tot12534 : totK PD2M8K2 D2M8K2.t12534 = [0, 195286514547, 484864775940, 204164725911, 9848247143, 0, 0, 0] := by
  decide +kernel

theorem rows12535 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12535 = true := by
  decide +kernel

theorem tot12535 : totK PD2M8K2 D2M8K2.t12535 = [0, 169271462309, 456747943533, 246439103774, 13795945806, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

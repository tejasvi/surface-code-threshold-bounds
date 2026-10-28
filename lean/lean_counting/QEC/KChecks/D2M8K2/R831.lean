import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3324 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3324 = true := by
  decide +kernel

theorem tot3324 : totK PD2M8K2 D2M8K2.t3324 = [0, 0, 190880822584, 477884266618, 221973207796, 10089471694, 0, 0] := by
  decide +kernel

theorem rows3325 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3325 = true := by
  decide +kernel

theorem tot3325 : totK PD2M8K2 D2M8K2.t3325 = [0, 67693118168, 231303043768, 396012909450, 177094294468, 6557415438, 0, 0] := by
  decide +kernel

theorem rows3326 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3326 = true := by
  decide +kernel

theorem tot3326 : totK PD2M8K2 D2M8K2.t3326 = [0, 182797215116, 474735269792, 252999238804, 22632853085, 0, 0, 0] := by
  decide +kernel

theorem rows3327 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3327 = true := by
  decide +kernel

theorem tot3327 : totK PD2M8K2 D2M8K2.t3327 = [0, 195139832800, 477845642915, 225833963002, 12523541424, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows15412 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15412 = true := by
  decide +kernel

theorem tot15412 : totK PD2M8K2 D2M8K2.t15412 = [0, 171647058257, 385690683675, 243354785959, 104412817309, 6799735859, 0, 0] := by
  decide +kernel

theorem rows15413 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15413 = true := by
  decide +kernel

theorem tot15413 : totK PD2M8K2 D2M8K2.t15413 = [0, 178544435094, 453414099791, 259660299255, 18438013872, 0, 0, 0] := by
  decide +kernel

theorem rows15414 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15414 = true := by
  decide +kernel

theorem tot15414 : totK PD2M8K2 D2M8K2.t15414 = [0, 88383717769, 365261697518, 362082017593, 69704615313, 1198073392, 0, 0] := by
  decide +kernel

theorem rows15415 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15415 = true := by
  decide +kernel

theorem tot15415 : totK PD2M8K2 D2M8K2.t15415 = [0, 0, 247427407065, 492146184411, 159143061751, 8470662040, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

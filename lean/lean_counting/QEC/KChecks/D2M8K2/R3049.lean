import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows12196 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12196 = true := by
  decide +kernel

theorem tot12196 : totK PD2M8K2 D2M8K2.t12196 = [0, 205364116606, 469172787841, 207262232113, 10178307621, 0, 0, 0] := by
  decide +kernel

theorem rows12197 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12197 = true := by
  decide +kernel

theorem tot12197 : totK PD2M8K2 D2M8K2.t12197 = [0, 172051928693, 475029449091, 222958304540, 10939763223, 0, 0, 0] := by
  decide +kernel

theorem rows12198 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12198 = true := by
  decide +kernel

theorem tot12198 : totK PD2M8K2 D2M8K2.t12198 = [0, 177968810090, 475242468554, 223249520290, 12590956490, 0, 0, 0] := by
  decide +kernel

theorem rows12199 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12199 = true := by
  decide +kernel

theorem tot12199 : totK PD2M8K2 D2M8K2.t12199 = [0, 198921544086, 472361820437, 206597088953, 7870241454, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

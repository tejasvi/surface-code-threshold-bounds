import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows10196 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10196 = true := by
  decide +kernel

theorem tot10196 : totK PD2M8K2 D2M8K2.t10196 = [0, 158429968117, 452696822646, 274038831366, 22713887658, 0, 0, 0] := by
  decide +kernel

theorem rows10197 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10197 = true := by
  decide +kernel

theorem tot10197 : totK PD2M8K2 D2M8K2.t10197 = [0, 163338247252, 470689971163, 238233680608, 13047460581, 0, 0, 0] := by
  decide +kernel

theorem rows10198 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10198 = true := by
  decide +kernel

theorem tot10198 : totK PD2M8K2 D2M8K2.t10198 = [0, 0, 217738172051, 497929157577, 137650150478, 4626333750, 0, 0] := by
  decide +kernel

theorem rows10199 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10199 = true := by
  decide +kernel

theorem tot10199 : totK PD2M8K2 D2M8K2.t10199 = [0, 160867177514, 448393970125, 276311711515, 34103363635, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

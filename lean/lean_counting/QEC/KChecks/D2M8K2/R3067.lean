import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows12268 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12268 = true := by
  decide +kernel

theorem tot12268 : totK PD2M8K2 D2M8K2.t12268 = [0, 25543652753, 319664442402, 442235956176, 86107102407, 1162935789, 0, 0] := by
  decide +kernel

theorem rows12269 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12269 = true := by
  decide +kernel

theorem tot12269 : totK PD2M8K2 D2M8K2.t12269 = [0, 0, 198267228721, 449932412125, 185877856147, 11853261585, 0, 0] := by
  decide +kernel

theorem rows12270 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12270 = true := by
  decide +kernel

theorem tot12270 : totK PD2M8K2 D2M8K2.t12270 = [0, 171426760366, 455788314336, 254266361948, 19140476678, 0, 0, 0] := by
  decide +kernel

theorem rows12271 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12271 = true := by
  decide +kernel

theorem tot12271 : totK PD2M8K2 D2M8K2.t12271 = [0, 199618524585, 471249632972, 211214112157, 12064174497, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

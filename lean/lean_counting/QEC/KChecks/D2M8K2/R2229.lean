import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows8916 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8916 = true := by
  decide +kernel

theorem tot8916 : totK PD2M8K2 D2M8K2.t8916 = [181154523674, 476527641887, 245556013021, 15536388152, 0, 0, 0, 0] := by
  decide +kernel

theorem rows8917 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8917 = true := by
  decide +kernel

theorem tot8917 : totK PD2M8K2 D2M8K2.t8917 = [88945508586, 334914650679, 391697781364, 86166870976, 1198073392, 0, 0, 0] := by
  decide +kernel

theorem rows8918 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8918 = true := by
  decide +kernel

theorem tot8918 : totK PD2M8K2 D2M8K2.t8918 = [0, 248825917870, 492131996073, 155101335694, 8470662040, 0, 0, 0] := by
  decide +kernel

theorem rows8919 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8919 = true := by
  decide +kernel

theorem tot8919 : totK PD2M8K2 D2M8K2.t8919 = [135185197221, 368047782061, 300110652653, 80908717943, 3581949829, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

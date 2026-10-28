import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows13276 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13276 = true := by
  decide +kernel

theorem tot13276 : totK PD2M8K2 D2M8K2.t13276 = [0, 0, 195522861516, 462855533397, 239010498739, 22877115247, 0, 0] := by
  decide +kernel

theorem rows13277 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13277 = true := by
  decide +kernel

theorem tot13277 : totK PD2M8K2 D2M8K2.t13277 = [0, 0, 164808122162, 466183531775, 245599010892, 13588514140, 0, 0] := by
  decide +kernel

theorem rows13278 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13278 = true := by
  decide +kernel

theorem tot13278 : totK PD2M8K2 D2M8K2.t13278 = [0, 0, 0, 300651397344, 468254735844, 112413994863, 4031931762, 0] := by
  decide +kernel

theorem rows13279 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13279 = true := by
  decide +kernel

theorem tot13279 : totK PD2M8K2 D2M8K2.t13279 = [0, 0, 96653581007, 358606093303, 354468520857, 70095106888, 1186940923, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows16280 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t16280 = true := by
  decide +kernel

theorem tot16280 : totK PD2M8K2 D2M8K2.t16280 = [0, 0, 231571303175, 512657430054, 173477210905, 4434332754, 0, 0] := by
  decide +kernel

theorem rows16281 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t16281 = true := by
  decide +kernel

theorem tot16281 : totK PD2M8K2 D2M8K2.t16281 = [0, 0, 171513147919, 448563930657, 271184682853, 27303097742, 0, 0] := by
  decide +kernel

theorem rows16282 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t16282 = true := by
  decide +kernel

theorem tot16282 : totK PD2M8K2 D2M8K2.t16282 = [0, 0, 156467388858, 451647055316, 284935394157, 20679609012, 0, 0] := by
  decide +kernel

theorem rows16283 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t16283 = true := by
  decide +kernel

theorem tot16283 : totK PD2M8K2 D2M8K2.t16283 = [0, 0, 0, 273420833775, 501277229746, 129388533576, 3654551267, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

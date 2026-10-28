import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows16204 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t16204 = true := by
  decide +kernel

theorem tot16204 : totK PD2M8K2 D2M8K2.t16204 = [0, 0, 217229359137, 463601335622, 211498474353, 21086933110, 0, 0] := by
  decide +kernel

theorem rows16205 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t16205 = true := by
  decide +kernel

theorem tot16205 : totK PD2M8K2 D2M8K2.t16205 = [0, 0, 178564792239, 478940073015, 230599585655, 7436336587, 0, 0] := by
  decide +kernel

theorem rows16206 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t16206 = true := by
  decide +kernel

theorem tot16206 : totK PD2M8K2 D2M8K2.t16206 = [0, 138024460557, 350388257368, 295441519746, 115372878429, 6804944647, 0, 0] := by
  decide +kernel

theorem rows16207 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t16207 = true := by
  decide +kernel

theorem tot16207 : totK PD2M8K2 D2M8K2.t16207 = [0, 161405139848, 439523194063, 277882025404, 30162361187, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

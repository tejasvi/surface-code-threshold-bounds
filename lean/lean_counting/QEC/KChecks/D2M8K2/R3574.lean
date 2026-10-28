import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows14296 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14296 = true := by
  decide +kernel

theorem tot14296 : totK PD2M8K2 D2M8K2.t14296 = [0, 0, 296611967189, 493322069539, 106822656423, 1369150432, 0, 0] := by
  decide +kernel

theorem rows14297 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14297 = true := by
  decide +kernel

theorem tot14297 : totK PD2M8K2 D2M8K2.t14297 = [0, 87704378323, 381960153910, 387057431760, 44837578189, 0, 0, 0] := by
  decide +kernel

theorem rows14298 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14298 = true := by
  decide +kernel

theorem tot14298 : totK PD2M8K2 D2M8K2.t14298 = [0, 164329518449, 457513001089, 267596259928, 22403749008, 0, 0, 0] := by
  decide +kernel

theorem rows14299 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14299 = true := by
  decide +kernel

theorem tot14299 : totK PD2M8K2 D2M8K2.t14299 = [0, 170257130765, 459632083373, 238270310839, 11270934851, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

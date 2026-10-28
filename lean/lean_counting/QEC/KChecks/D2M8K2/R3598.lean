import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows14392 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14392 = true := by
  decide +kernel

theorem tot14392 : totK PD2M8K2 D2M8K2.t14392 = [0, 92237621127, 383052898569, 345710065872, 54160167833, 1096505104, 0, 0] := by
  decide +kernel

theorem rows14393 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14393 = true := by
  decide +kernel

theorem tot14393 : totK PD2M8K2 D2M8K2.t14393 = [0, 0, 316471988712, 516597432843, 81607201359, 0, 0, 0] := by
  decide +kernel

theorem rows14394 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14394 = true := by
  decide +kernel

theorem tot14394 : totK PD2M8K2 D2M8K2.t14394 = [0, 0, 193063491109, 491519327104, 183180503985, 5253830308, 0, 0] := by
  decide +kernel

theorem rows14395 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14395 = true := by
  decide +kernel

theorem tot14395 : totK PD2M8K2 D2M8K2.t14395 = [0, 0, 168992386419, 457353728899, 210307539757, 13301593013, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

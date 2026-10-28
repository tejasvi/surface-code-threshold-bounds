import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5476 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5476 = true := by
  decide +kernel

theorem tot5476 : totK PD2M8K2 D2M8K2.t5476 = [0, 0, 0, 177938368439, 442354186550, 250971080626, 21156369654, 0] := by
  decide +kernel

theorem rows5477 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5477 = true := by
  decide +kernel

theorem tot5477 : totK PD2M8K2 D2M8K2.t5477 = [0, 0, 0, 163199165909, 504613701022, 225991832002, 4819533584, 0] := by
  decide +kernel

theorem rows5478 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5478 = true := by
  decide +kernel

theorem tot5478 : totK PD2M8K2 D2M8K2.t5478 = [0, 0, 186552364104, 437717699784, 233664026902, 36236372977, 4431529051, 0] := by
  decide +kernel

theorem rows5479 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5479 = true := by
  decide +kernel

theorem tot5479 : totK PD2M8K2 D2M8K2.t5479 = [0, 0, 208702493309, 484135282578, 196514905272, 9265115603, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

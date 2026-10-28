import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows9436 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9436 = true := by
  decide +kernel

theorem tot9436 : totK PD2M8K2 D2M8K2.t9436 = [0, 0, 200347372002, 464540391838, 211967273594, 15817296786, 0, 0] := by
  decide +kernel

theorem rows9437 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9437 = true := by
  decide +kernel

theorem tot9437 : totK PD2M8K2 D2M8K2.t9437 = [0, 0, 191701175464, 461731909525, 214141766925, 16702988424, 0, 0] := by
  decide +kernel

theorem rows9438 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9438 = true := by
  decide +kernel

theorem tot9438 : totK PD2M8K2 D2M8K2.t9438 = [0, 0, 55809825723, 344557458240, 386896562459, 71831939044, 1095107716, 0] := by
  decide +kernel

theorem rows9439 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9439 = true := by
  decide +kernel

theorem tot9439 : totK PD2M8K2 D2M8K2.t9439 = [18947402031, 14643827706, 0, 269428986981, 444780602453, 119966586878, 3882006667, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

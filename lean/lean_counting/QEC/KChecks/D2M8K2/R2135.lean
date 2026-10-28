import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows8540 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8540 = true := by
  decide +kernel

theorem tot8540 : totK PD2M8K2 D2M8K2.t8540 = [154811365446, 400655464538, 282389036862, 60847231307, 2481160468, 0, 0, 0] := by
  decide +kernel

theorem rows8541 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8541 = true := by
  decide +kernel

theorem tot8541 : totK PD2M8K2 D2M8K2.t8541 = [154886592368, 426228804582, 291575605686, 31560748435, 0, 0, 0, 0] := by
  decide +kernel

theorem rows8542 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8542 = true := by
  decide +kernel

theorem tot8542 : totK PD2M8K2 D2M8K2.t8542 = [90332340817, 360842732938, 353345430313, 72808204876, 1096505104, 0, 0, 0] := by
  decide +kernel

theorem rows8543 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8543 = true := by
  decide +kernel

theorem tot8543 : totK PD2M8K2 D2M8K2.t8543 = [0, 311397260718, 506098148495, 89152484809, 1069412848, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

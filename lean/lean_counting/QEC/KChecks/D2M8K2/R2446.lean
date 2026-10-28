import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows9784 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9784 = true := by
  decide +kernel

theorem tot9784 : totK PD2M8K2 D2M8K2.t9784 = [0, 0, 173954924600, 460999099327, 223426716924, 16561712910, 0, 0] := by
  decide +kernel

theorem rows9785 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9785 = true := by
  decide +kernel

theorem tot9785 : totK PD2M8K2 D2M8K2.t9785 = [0, 0, 88109811954, 348204977995, 356250063362, 79523909105, 1369150432, 0] := by
  decide +kernel

theorem rows9786 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9786 = true := by
  decide +kernel

theorem tot9786 : totK PD2M8K2 D2M8K2.t9786 = [0, 0, 3757117624, 339124434116, 453860608012, 63859916673, 0, 0] := by
  decide +kernel

theorem rows9787 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9787 = true := by
  decide +kernel

theorem tot9787 : totK PD2M8K2 D2M8K2.t9787 = [0, 0, 225710947355, 510485894645, 154936686966, 1369549359, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

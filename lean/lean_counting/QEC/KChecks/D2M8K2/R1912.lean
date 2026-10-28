import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7648 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7648 = true := by
  decide +kernel

theorem tot7648 : totK PD2M8K2 D2M8K2.t7648 = [0, 0, 93578216757, 399238454730, 361283268413, 43804498426, 0, 0] := by
  decide +kernel

theorem rows7649 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7649 = true := by
  decide +kernel

theorem tot7649 : totK PD2M8K2 D2M8K2.t7649 = [0, 0, 0, 253804508009, 476043231001, 138940035831, 3569676519, 0] := by
  decide +kernel

theorem rows7650 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7650 = true := by
  decide +kernel

theorem tot7650 : totK PD2M8K2 D2M8K2.t7650 = [0, 0, 117239496903, 350275323686, 314655066860, 112632200910, 8974678929, 0] := by
  decide +kernel

theorem rows7651 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7651 = true := by
  decide +kernel

theorem tot7651 : totK PD2M8K2 D2M8K2.t7651 = [0, 0, 186852379513, 453211801884, 225872002772, 13383150755, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

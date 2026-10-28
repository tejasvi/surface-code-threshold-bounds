import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows12508 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12508 = true := by
  decide +kernel

theorem tot12508 : totK PD2M8K2 D2M8K2.t12508 = [0, 191837688753, 474356411609, 222926595469, 12373752831, 0, 0, 0] := by
  decide +kernel

theorem rows12509 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12509 = true := by
  decide +kernel

theorem tot12509 : totK PD2M8K2 D2M8K2.t12509 = [0, 0, 302025627841, 491919580815, 97134809841, 1164319620, 0, 0] := by
  decide +kernel

theorem rows12510 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12510 = true := by
  decide +kernel

theorem tot12510 : totK PD2M8K2 D2M8K2.t12510 = [0, 0, 199075033526, 474555716729, 191815756692, 11885407614, 0, 0] := by
  decide +kernel

theorem rows12511 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12511 = true := by
  decide +kernel

theorem tot12511 : totK PD2M8K2 D2M8K2.t12511 = [0, 164975251400, 442750480351, 268813357559, 27766265217, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3604 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3604 = true := by
  decide +kernel

theorem tot3604 : totK PD2M8K2 D2M8K2.t3604 = [0, 61566305829, 223655791985, 413351601007, 191901212956, 8104085798, 0, 0] := by
  decide +kernel

theorem rows3605 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3605 = true := by
  decide +kernel

theorem tot3605 : totK PD2M8K2 D2M8K2.t3605 = [0, 185609305197, 467586931182, 248729928656, 23330440159, 0, 0, 0] := by
  decide +kernel

theorem rows3606 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3606 = true := by
  decide +kernel

theorem tot3606 : totK PD2M8K2 D2M8K2.t3606 = [0, 166433636818, 472889011292, 248490295565, 13368331894, 0, 0, 0] := by
  decide +kernel

theorem rows3607 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3607 = true := by
  decide +kernel

theorem tot3607 : totK PD2M8K2 D2M8K2.t3607 = [0, 0, 281928531959, 497328347240, 120723235212, 5998727602, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

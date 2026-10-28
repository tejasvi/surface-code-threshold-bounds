import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows11776 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11776 = true := by
  decide +kernel

theorem tot11776 : totK PD2M8K2 D2M8K2.t11776 = [0, 175582634801, 440404559505, 277479192230, 29322329664, 0, 0, 0] := by
  decide +kernel

theorem rows11777 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11777 = true := by
  decide +kernel

theorem tot11777 : totK PD2M8K2 D2M8K2.t11777 = [0, 120242566139, 413850883642, 317724117184, 45837636817, 1231519631, 0, 0] := by
  decide +kernel

theorem rows11778 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11778 = true := by
  decide +kernel

theorem tot11778 : totK PD2M8K2 D2M8K2.t11778 = [0, 0, 242521923530, 497582074658, 156916696295, 3693668399, 0, 0] := by
  decide +kernel

theorem rows11779 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11779 = true := by
  decide +kernel

theorem tot11779 : totK PD2M8K2 D2M8K2.t11779 = [0, 90277532827, 269629513373, 340123698549, 169720064922, 12866082196, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

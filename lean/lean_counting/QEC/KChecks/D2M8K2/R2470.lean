import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows9880 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9880 = true := by
  decide +kernel

theorem tot9880 : totK PD2M8K2 D2M8K2.t9880 = [0, 0, 213904759624, 492987162662, 188623492870, 9806327538, 0, 0] := by
  decide +kernel

theorem rows9881 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9881 = true := by
  decide +kernel

theorem tot9881 : totK PD2M8K2 D2M8K2.t9881 = [0, 0, 175560303420, 500947741121, 208489123059, 5482929410, 0, 0] := by
  decide +kernel

theorem rows9882 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9882 = true := by
  decide +kernel

theorem tot9882 : totK PD2M8K2 D2M8K2.t9882 = [0, 0, 185493834407, 465995508757, 211374447694, 12370590376, 0, 0] := by
  decide +kernel

theorem rows9883 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9883 = true := by
  decide +kernel

theorem tot9883 : totK PD2M8K2 D2M8K2.t9883 = [0, 0, 194056896356, 492865931040, 195331990783, 7908941562, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

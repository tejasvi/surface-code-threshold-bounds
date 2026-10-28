import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows9204 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9204 = true := by
  decide +kernel

theorem tot9204 : totK PD2M8K2 D2M8K2.t9204 = [0, 175461925051, 440656863043, 276195073897, 28496840222, 0, 0, 0] := by
  decide +kernel

theorem rows9205 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9205 = true := by
  decide +kernel

theorem tot9205 : totK PD2M8K2 D2M8K2.t9205 = [0, 189346001542, 489527746902, 222935984055, 8977779328, 0, 0, 0] := by
  decide +kernel

theorem rows9206 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9206 = true := by
  decide +kernel

theorem tot9206 : totK PD2M8K2 D2M8K2.t9206 = [0, 16104169343, 260915061840, 426707948269, 189449065214, 21385604922, 0, 0] := by
  decide +kernel

theorem rows9207 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9207 = true := by
  decide +kernel

theorem tot9207 : totK PD2M8K2 D2M8K2.t9207 = [0, 0, 205798070665, 482386839484, 188786546091, 7658844075, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

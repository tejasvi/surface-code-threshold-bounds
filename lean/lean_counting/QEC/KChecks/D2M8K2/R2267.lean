import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows9068 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9068 = true := by
  decide +kernel

theorem tot9068 : totK PD2M8K2 D2M8K2.t9068 = [0, 112434957072, 385260638430, 381098972424, 48301836287, 0, 0, 0] := by
  decide +kernel

theorem rows9069 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9069 = true := by
  decide +kernel

theorem tot9069 : totK PD2M8K2 D2M8K2.t9069 = [0, 203498693620, 474339056892, 220428568227, 12787542455, 0, 0, 0] := by
  decide +kernel

theorem rows9070 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9070 = true := by
  decide +kernel

theorem tot9070 : totK PD2M8K2 D2M8K2.t9070 = [0, 106703719193, 434367316113, 327510162549, 36438686886, 0, 0, 0] := by
  decide +kernel

theorem rows9071 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9071 = true := by
  decide +kernel

theorem tot9071 : totK PD2M8K2 D2M8K2.t9071 = [0, 0, 176748870856, 463416479945, 239310211182, 19572653258, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

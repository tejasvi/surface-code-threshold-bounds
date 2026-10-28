import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows8040 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8040 = true := by
  decide +kernel

theorem tot8040 : totK PD2M8K2 D2M8K2.t8040 = [0, 0, 0, 178670032154, 480817859087, 217621017804, 10850510562, 0] := by
  decide +kernel

theorem rows8041 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8041 = true := by
  decide +kernel

theorem tot8041 : totK PD2M8K2 D2M8K2.t8041 = [0, 0, 0, 288754082909, 476147504944, 104167583025, 4059686398, 0] := by
  decide +kernel

theorem rows8042 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8042 = true := by
  decide +kernel

theorem tot8042 : totK PD2M8K2 D2M8K2.t8042 = [0, 0, 0, 246758745228, 475179615481, 146122824363, 5187627908, 0] := by
  decide +kernel

theorem rows8043 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8043 = true := by
  decide +kernel

theorem tot8043 : totK PD2M8K2 D2M8K2.t8043 = [0, 0, 0, 171757411401, 462975856074, 232850862631, 18049548325, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

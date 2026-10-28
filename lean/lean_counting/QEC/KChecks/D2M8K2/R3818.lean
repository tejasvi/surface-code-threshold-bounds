import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows15272 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15272 = true := by
  decide +kernel

theorem tot15272 : totK PD2M8K2 D2M8K2.t15272 = [0, 0, 0, 295620987297, 514792452898, 73725681975, 1096505104, 0] := by
  decide +kernel

theorem rows15273 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15273 = true := by
  decide +kernel

theorem tot15273 : totK PD2M8K2 D2M8K2.t15273 = [0, 0, 166385995759, 455180045800, 263693277029, 21993517949, 0, 0] := by
  decide +kernel

theorem rows15274 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15274 = true := by
  decide +kernel

theorem tot15274 : totK PD2M8K2 D2M8K2.t15274 = [0, 0, 168720645579, 452412756276, 277978349775, 17423212560, 0, 0] := by
  decide +kernel

theorem rows15275 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15275 = true := by
  decide +kernel

theorem tot15275 : totK PD2M8K2 D2M8K2.t15275 = [0, 0, 80869266466, 345036547112, 388791629879, 83859782940, 1232398321, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

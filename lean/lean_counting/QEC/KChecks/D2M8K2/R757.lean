import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3028 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3028 = true := by
  decide +kernel

theorem tot3028 : totK PD2M8K2 D2M8K2.t3028 = [0, 36656307504, 283853549654, 458953431393, 108616577085, 3783381897, 0, 0] := by
  decide +kernel

theorem rows3029 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3029 = true := by
  decide +kernel

theorem tot3029 : totK PD2M8K2 D2M8K2.t3029 = [0, 174798963305, 452292658793, 251972836754, 22719114835, 0, 0, 0] := by
  decide +kernel

theorem rows3030 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3030 = true := by
  decide +kernel

theorem tot3030 : totK PD2M8K2 D2M8K2.t3030 = [0, 209077519582, 474782123349, 213911496147, 12329758230, 0, 0, 0] := by
  decide +kernel

theorem rows3031 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3031 = true := by
  decide +kernel

theorem tot3031 : totK PD2M8K2 D2M8K2.t3031 = [0, 0, 290542864253, 486396378406, 101580912098, 1240621948, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

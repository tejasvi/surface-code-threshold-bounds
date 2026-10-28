import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows15588 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15588 = true := by
  decide +kernel

theorem tot15588 : totK PD2M8K2 D2M8K2.t15588 = [0, 0, 281283563928, 510845865187, 96130133278, 1096505104, 0, 0] := by
  decide +kernel

theorem rows15589 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15589 = true := by
  decide +kernel

theorem tot15589 : totK PD2M8K2 D2M8K2.t15589 = [0, 129278630345, 356385165284, 310598264047, 84595566202, 3884009855, 0, 0] := by
  decide +kernel

theorem rows15590 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15590 = true := by
  decide +kernel

theorem tot15590 : totK PD2M8K2 D2M8K2.t15590 = [0, 164598162981, 448002250884, 275952682716, 30127456144, 0, 0, 0] := by
  decide +kernel

theorem rows15591 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15591 = true := by
  decide +kernel

theorem tot15591 : totK PD2M8K2 D2M8K2.t15591 = [0, 126693952495, 433522051329, 325474137554, 26334696373, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

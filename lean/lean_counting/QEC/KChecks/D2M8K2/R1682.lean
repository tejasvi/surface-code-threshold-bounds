import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6728 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6728 = true := by
  decide +kernel

theorem tot6728 : totK PD2M8K2 D2M8K2.t6728 = [127253961937, 439214940053, 307032153051, 28504154241, 0, 0, 0, 0] := by
  decide +kernel

theorem rows6729 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6729 = true := by
  decide +kernel

theorem tot6729 : totK PD2M8K2 D2M8K2.t6729 = [0, 274575024129, 502641687335, 110213545892, 1369150432, 0, 0, 0] := by
  decide +kernel

theorem rows6730 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6730 = true := by
  decide +kernel

theorem tot6730 : totK PD2M8K2 D2M8K2.t6730 = [156961448103, 443601121281, 291308334782, 29900182471, 0, 0, 0, 0] := by
  decide +kernel

theorem rows6731 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6731 = true := by
  decide +kernel

theorem tot6731 : totK PD2M8K2 D2M8K2.t6731 = [169549112096, 446294049120, 256144992836, 21543307782, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6028 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6028 = true := by
  decide +kernel

theorem tot6028 : totK PD2M8K2 D2M8K2.t6028 = [0, 93574619190, 260292062243, 357619554314, 194795539950, 13065910070, 0, 0] := by
  decide +kernel

theorem rows6029 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6029 = true := by
  decide +kernel

theorem tot6029 : totK PD2M8K2 D2M8K2.t6029 = [0, 162325214004, 454510669902, 279834895548, 20281430424, 0, 0, 0] := by
  decide +kernel

theorem rows6030 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6030 = true := by
  decide +kernel

theorem tot6030 : totK PD2M8K2 D2M8K2.t6030 = [0, 173663064406, 462037446489, 239994424687, 15833711062, 0, 0, 0] := by
  decide +kernel

theorem rows6031 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6031 = true := by
  decide +kernel

theorem tot6031 : totK PD2M8K2 D2M8K2.t6031 = [0, 0, 185392808046, 445958152682, 251513957975, 25298831311, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

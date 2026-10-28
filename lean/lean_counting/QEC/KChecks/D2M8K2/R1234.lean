import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4936 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4936 = true := by
  decide +kernel

theorem tot4936 : totK PD2M8K2 D2M8K2.t4936 = [0, 178376418187, 452346692757, 240602439926, 17115888737, 0, 0, 0] := by
  decide +kernel

theorem rows4937 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4937 = true := by
  decide +kernel

theorem tot4937 : totK PD2M8K2 D2M8K2.t4937 = [0, 147987643801, 448089443416, 274986877375, 23678717390, 0, 0, 0] := by
  decide +kernel

theorem rows4938 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4938 = true := by
  decide +kernel

theorem tot4938 : totK PD2M8K2 D2M8K2.t4938 = [0, 0, 276764905444, 504739681732, 110385113936, 1369150432, 0, 0] := by
  decide +kernel

theorem rows4939 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4939 = true := by
  decide +kernel

theorem tot4939 : totK PD2M8K2 D2M8K2.t4939 = [0, 154546952829, 439602739169, 286298283579, 28709561297, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

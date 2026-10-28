import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6156 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6156 = true := by
  decide +kernel

theorem tot6156 : totK PA10K2 A10K2.t6156 = [0, 0, 305229480561, 1531598847895, 2170889798841, 867854404824, 67115569713, 0, 0, 0] := by
  decide +kernel

theorem rows6157 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6157 = true := by
  decide +kernel

theorem tot6157 : totK PA10K2 A10K2.t6157 = [0, 0, 0, 547916051022, 1955748560481, 1980323658477, 495753833872, 18381869251, 0, 0] := by
  decide +kernel

theorem rows6158 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6158 = true := by
  decide +kernel

theorem tot6158 : totK PA10K2 A10K2.t6158 = [0, 0, 0, 569694150880, 1918101104021, 1749123537422, 447732538446, 42316380502, 0, 0] := by
  decide +kernel

theorem rows6159 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6159 = true := by
  decide +kernel

theorem tot6159 : totK PA10K2 A10K2.t6159 = [0, 0, 0, 280200798865, 1437397076852, 2110288333000, 845406131669, 67026471723, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2

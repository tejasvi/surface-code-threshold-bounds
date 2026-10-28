import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4072 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4072 = true := by
  decide +kernel

theorem tot4072 : totK PA10K2 A10K2.t4072 = [0, 0, 0, 760112698383, 2223025805761, 1680392238084, 284000331223, 6772895877, 0, 0] := by
  decide +kernel

theorem rows4073 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4073 = true := by
  decide +kernel

theorem tot4073 : totK PA10K2 A10K2.t4073 = [0, 0, 0, 501346302155, 1933950718252, 2079408642437, 523200198142, 18736574845, 0, 0] := by
  decide +kernel

theorem rows4074 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4074 = true := by
  decide +kernel

theorem tot4074 : totK PA10K2 A10K2.t4074 = [0, 0, 0, 538003433083, 1810786790303, 1844368361315, 549991598038, 49321567661, 0, 0] := by
  decide +kernel

theorem rows4075 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4075 = true := by
  decide +kernel

theorem tot4075 : totK PA10K2 A10K2.t4075 = [0, 0, 0, 177174659569, 1116013481699, 2113435124400, 1262234232695, 193065710970, 6318667960, 0] := by
  decide +kernel

end QECKChecks.A10K2

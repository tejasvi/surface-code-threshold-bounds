import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6164 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6164 = true := by
  decide +kernel

theorem tot6164 : totK PA10K2 A10K2.t6164 = [0, 0, 306117011728, 1228610492393, 1803243974502, 1223888243609, 348293725091, 29010686974, 0, 0] := by
  decide +kernel

theorem rows6165 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6165 = true := by
  decide +kernel

theorem tot6165 : totK PA10K2 A10K2.t6165 = [0, 0, 483587366435, 1817537957127, 1914103002619, 509509132440, 32040661968, 0, 0, 0] := by
  decide +kernel

theorem rows6166 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6166 = true := by
  decide +kernel

theorem tot6166 : totK PA10K2 A10K2.t6166 = [0, 0, 0, 636798299914, 2041750263422, 1650661025364, 389988042076, 25371180993, 0, 0] := by
  decide +kernel

theorem rows6167 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6167 = true := by
  decide +kernel

theorem tot6167 : totK PA10K2 A10K2.t6167 = [0, 0, 251705348851, 1197571118360, 1926614432317, 1119688586362, 180544988813, 5460492893, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2

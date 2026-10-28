import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3688 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3688 = true := by
  decide +kernel

theorem tot3688 : totK PA10K2 A10K2.t3688 = [0, 0, 481206608490, 1827078641379, 1955766545917, 511394586990, 33389097656, 0, 0, 0] := by
  decide +kernel

theorem rows3689 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3689 = true := by
  decide +kernel

theorem tot3689 : totK PA10K2 A10K2.t3689 = [0, 0, 297203975092, 1552760531723, 2117006122415, 699961139920, 45543540946, 0, 0, 0] := by
  decide +kernel

theorem rows3690 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3690 = true := by
  decide +kernel

theorem tot3690 : totK PA10K2 A10K2.t3690 = [0, 0, 264190058193, 1172625959208, 1928122343348, 1122787290693, 179533038711, 5546304973, 0, 0] := by
  decide +kernel

theorem rows3691 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3691 = true := by
  decide +kernel

theorem tot3691 : totK PA10K2 A10K2.t3691 = [0, 582775338075, 1858360142819, 1752324843693, 589203322283, 61032477040, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2

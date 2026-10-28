import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5548 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5548 = true := by
  decide +kernel

theorem tot5548 : totK PA10K2 A10K2.t5548 = [0, 0, 487223217921, 1559607573571, 1795206400357, 928442775419, 158377849049, 6239673734, 0, 0] := by
  decide +kernel

theorem rows5549 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5549 = true := by
  decide +kernel

theorem tot5549 : totK PA10K2 A10K2.t5549 = [0, 0, 316779408161, 1541082118017, 2197899677774, 903539272986, 77267253194, 0, 0, 0] := by
  decide +kernel

theorem rows5550 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5550 = true := by
  decide +kernel

theorem tot5550 : totK PA10K2 A10K2.t5550 = [0, 0, 0, 642385800764, 2213758811137, 1916996941759, 357624493212, 6962742351, 0, 0] := by
  decide +kernel

theorem rows5551 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5551 = true := by
  decide +kernel

theorem tot5551 : totK PA10K2 A10K2.t5551 = [0, 0, 0, 432570480450, 1703055052885, 2049015322042, 718579221351, 56458713993, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2

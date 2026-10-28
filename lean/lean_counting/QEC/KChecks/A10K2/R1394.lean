import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5576 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5576 = true := by
  decide +kernel

theorem tot5576 : totK PA10K2 A10K2.t5576 = [0, 0, 453883021376, 1764205671008, 1932044213846, 534945080572, 31608797364, 0, 0, 0] := by
  decide +kernel

theorem rows5577 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5577 = true := by
  decide +kernel

theorem tot5577 : totK PA10K2 A10K2.t5577 = [0, 0, 0, 942433860575, 2400408272317, 1180379951155, 98161061821, 0, 0, 0] := by
  decide +kernel

theorem rows5578 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5578 = true := by
  decide +kernel

theorem tot5578 : totK PA10K2 A10K2.t5578 = [0, 0, 577573506214, 1820956308950, 1723727986375, 642260074587, 121017310421, 5546304973, 0, 0] := by
  decide +kernel

theorem rows5579 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5579 = true := by
  decide +kernel

theorem tot5579 : totK PA10K2 A10K2.t5579 = [0, 345421315675, 1200756136254, 1652378342221, 1256332080684, 475490626533, 36938587266, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2

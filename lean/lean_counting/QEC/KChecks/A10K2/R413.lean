import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1652 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1652 = true := by
  decide +kernel

theorem tot1652 : totK PA10K2 A10K2.t1652 = [0, 364137929526, 1300411790155, 1703883991055, 1141322139733, 380891305752, 30829329317, 0, 0, 0] := by
  decide +kernel

theorem rows1653 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1653 = true := by
  decide +kernel

theorem tot1653 : totK PA10K2 A10K2.t1653 = [0, 399836399348, 1684028345568, 2077765430549, 747369280398, 64036678673, 0, 0, 0, 0] := by
  decide +kernel

theorem rows1654 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1654 = true := by
  decide +kernel

theorem tot1654 : totK PA10K2 A10K2.t1654 = [0, 0, 472106143191, 1766026953843, 1889281243685, 502136329229, 31768748853, 0, 0, 0] := by
  decide +kernel

theorem rows1655 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1655 = true := by
  decide +kernel

theorem tot1655 : totK PA10K2 A10K2.t1655 = [0, 482480945578, 1726958084621, 1869624162453, 699731935966, 76897271707, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2

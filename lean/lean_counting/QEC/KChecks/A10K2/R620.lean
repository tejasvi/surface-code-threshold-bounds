import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2480 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2480 = true := by
  decide +kernel

theorem tot2480 : totK PA10K2 A10K2.t2480 = [0, 0, 502719362512, 1820713882999, 1807411939298, 492469229043, 26601763172, 0, 0, 0] := by
  decide +kernel

theorem rows2481 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2481 = true := by
  decide +kernel

theorem tot2481 : totK PA10K2 A10K2.t2481 = [0, 0, 570456219814, 1949680578504, 1854894366055, 405079459708, 18304095112, 0, 0, 0] := by
  decide +kernel

theorem rows2482 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2482 = true := by
  decide +kernel

theorem tot2482 : totK PA10K2 A10K2.t2482 = [0, 0, 694953212314, 2148593493411, 1635002785012, 256956048369, 6239800209, 0, 0, 0] := by
  decide +kernel

theorem rows2483 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2483 = true := by
  decide +kernel

theorem tot2483 : totK PA10K2 A10K2.t2483 = [0, 0, 548767945484, 1831532996482, 1777883005467, 456311958364, 30637645759, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2

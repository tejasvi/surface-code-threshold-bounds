import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5456 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5456 = true := by
  decide +kernel

theorem tot5456 : totK PA10K2 A10K2.t5456 = [0, 0, 110080449477, 1288874153961, 2358839456695, 890111602401, 65326404304, 0, 0, 0] := by
  decide +kernel

theorem rows5457 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5457 = true := by
  decide +kernel

theorem tot5457 : totK PA10K2 A10K2.t5457 = [0, 374690907472, 1216123057743, 1381179069975, 980325315870, 644002078046, 133756988527, 5546304973, 0, 0] := by
  decide +kernel

theorem rows5458 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5458 = true := by
  decide +kernel

theorem tot5458 : totK PA10K2 A10K2.t5458 = [0, 461552447388, 1836647853934, 1974586862854, 518545145421, 13227942247, 0, 0, 0, 0] := by
  decide +kernel

theorem rows5459 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5459 = true := by
  decide +kernel

theorem tot5459 : totK PA10K2 A10K2.t5459 = [0, 0, 583395201574, 1985141974588, 1779073320409, 421332321055, 25734533292, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2

import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows60 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t60 = true := by
  decide +kernel

theorem tot60 : totK PD2M8K2 D2M8K2.t60 = [0, 120184246382, 442387648435, 300421948825, 22520876126, 0, 0, 0] := by
  decide +kernel

theorem rows61 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t61 = true := by
  decide +kernel

theorem tot61 : totK PD2M8K2 D2M8K2.t61 = [0, 0, 210540744043, 472004222427, 176738884511, 9579374723, 0, 0] := by
  decide +kernel

theorem rows62 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t62 = true := by
  decide +kernel

theorem tot62 : totK PD2M8K2 D2M8K2.t62 = [0, 84062340490, 340545711159, 339107018389, 85795564859, 3436822651, 0, 0] := by
  decide +kernel

theorem rows63 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t63 = true := by
  decide +kernel

theorem tot63 : totK PD2M8K2 D2M8K2.t63 = [0, 182227534834, 457556902574, 242726437377, 18252358503, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

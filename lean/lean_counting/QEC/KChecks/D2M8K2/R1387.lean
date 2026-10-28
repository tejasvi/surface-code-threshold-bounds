import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5548 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5548 = true := by
  decide +kernel

theorem tot5548 : totK PD2M8K2 D2M8K2.t5548 = [0, 297930710715, 503945224429, 102265672472, 1164319620, 0, 0, 0] := by
  decide +kernel

theorem rows5549 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5549 = true := by
  decide +kernel

theorem tot5549 : totK PD2M8K2 D2M8K2.t5549 = [0, 195710942555, 475282579767, 192663698719, 11885407614, 0, 0, 0] := by
  decide +kernel

theorem rows5550 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5550 = true := by
  decide +kernel

theorem tot5550 : totK PD2M8K2 D2M8K2.t5550 = [164868315185, 445581734684, 267309819392, 28555205611, 0, 0, 0, 0] := by
  decide +kernel

theorem rows5551 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5551 = true := by
  decide +kernel

theorem tot5551 : totK PD2M8K2 D2M8K2.t5551 = [190098075305, 447274409198, 238966653287, 20345486287, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

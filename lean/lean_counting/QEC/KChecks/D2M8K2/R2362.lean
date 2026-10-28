import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows9448 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9448 = true := by
  decide +kernel

theorem tot9448 : totK PD2M8K2 D2M8K2.t9448 = [178610529878, 445721227186, 266324327039, 27481733209, 0, 0, 0, 0] := by
  decide +kernel

theorem rows9449 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9449 = true := by
  decide +kernel

theorem tot9449 : totK PD2M8K2 D2M8K2.t9449 = [148672322715, 450460918743, 280266479781, 20074333972, 0, 0, 0, 0] := by
  decide +kernel

theorem rows9450 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9450 = true := by
  decide +kernel

theorem tot9450 : totK PD2M8K2 D2M8K2.t9450 = [0, 206906322802, 485301743888, 187471288491, 8214782009, 0, 0, 0] := by
  decide +kernel

theorem rows9451 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9451 = true := by
  decide +kernel

theorem tot9451 : totK PD2M8K2 D2M8K2.t9451 = [86474097249, 308164991691, 375713847688, 111302496461, 3581949829, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

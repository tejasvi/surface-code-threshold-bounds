import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows9600 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9600 = true := by
  decide +kernel

theorem tot9600 : totK PD2M8K2 D2M8K2.t9600 = [0, 165025326539, 442102781347, 276919266129, 28355504543, 0, 0, 0] := by
  decide +kernel

theorem rows9601 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9601 = true := by
  decide +kernel

theorem tot9601 : totK PD2M8K2 D2M8K2.t9601 = [0, 183527626591, 492837410530, 231119977391, 9314403346, 0, 0, 0] := by
  decide +kernel

theorem rows9602 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9602 = true := by
  decide +kernel

theorem tot9602 : totK PD2M8K2 D2M8K2.t9602 = [0, 169925313841, 449403127957, 250780847147, 26238160623, 0, 0, 0] := by
  decide +kernel

theorem rows9603 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9603 = true := by
  decide +kernel

theorem tot9603 : totK PD2M8K2 D2M8K2.t9603 = [0, 177668866474, 446987237946, 233335661218, 16053149564, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

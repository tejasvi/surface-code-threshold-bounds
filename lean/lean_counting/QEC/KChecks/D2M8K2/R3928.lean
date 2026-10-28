import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows15712 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15712 = true := by
  decide +kernel

theorem tot15712 : totK PD2M8K2 D2M8K2.t15712 = [0, 0, 178514488432, 455989497032, 266085280747, 30500119012, 0, 0] := by
  decide +kernel

theorem rows15713 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15713 = true := by
  decide +kernel

theorem tot15713 : totK PD2M8K2 D2M8K2.t15713 = [0, 0, 231912749227, 509454749652, 165565931262, 4127662401, 0, 0] := by
  decide +kernel

theorem rows15714 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15714 = true := by
  decide +kernel

theorem tot15714 : totK PD2M8K2 D2M8K2.t15714 = [0, 0, 171000623050, 445944103115, 278289162367, 27361558206, 0, 0] := by
  decide +kernel

theorem rows15715 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15715 = true := by
  decide +kernel

theorem tot15715 : totK PD2M8K2 D2M8K2.t15715 = [0, 0, 103692168731, 432324757007, 344986551728, 35629599080, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

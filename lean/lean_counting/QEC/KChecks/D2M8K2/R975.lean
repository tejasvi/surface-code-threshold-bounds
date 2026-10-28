import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3900 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3900 = true := by
  decide +kernel

theorem tot3900 : totK PD2M8K2 D2M8K2.t3900 = [0, 0, 211290333382, 492478555569, 181210080934, 7877773091, 0, 0] := by
  decide +kernel

theorem rows3901 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3901 = true := by
  decide +kernel

theorem tot3901 : totK PD2M8K2 D2M8K2.t3901 = [0, 101251914141, 353743465359, 362530307559, 77833546841, 1189976475, 0, 0] := by
  decide +kernel

theorem rows3902 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3902 = true := by
  decide +kernel

theorem tot3902 : totK PD2M8K2 D2M8K2.t3902 = [0, 166747106687, 442193691667, 277597714372, 30573130048, 0, 0, 0] := by
  decide +kernel

theorem rows3903 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3903 = true := by
  decide +kernel

theorem tot3903 : totK PD2M8K2 D2M8K2.t3903 = [0, 143326932689, 452976904869, 282743869049, 23495833156, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows10680 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10680 = true := by
  decide +kernel

theorem tot10680 : totK PD2M8K2 D2M8K2.t10680 = [0, 0, 0, 325170365216, 496079346825, 83766820982, 1369820453, 0] := by
  decide +kernel

theorem rows10681 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10681 = true := by
  decide +kernel

theorem tot10681 : totK PD2M8K2 D2M8K2.t10681 = [0, 0, 0, 165980770665, 481518850998, 189137068110, 9486241455, 0] := by
  decide +kernel

theorem rows10682 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10682 = true := by
  decide +kernel

theorem tot10682 : totK PD2M8K2 D2M8K2.t10682 = [0, 0, 0, 164072893226, 463049746724, 218054895950, 12456071785, 0] := by
  decide +kernel

theorem rows10683 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10683 = true := by
  decide +kernel

theorem tot10683 : totK PD2M8K2 D2M8K2.t10683 = [0, 0, 0, 0, 336033498710, 416338356563, 64784652435, 1209030869] := by
  decide +kernel

end QECKChecks.D2M8K2

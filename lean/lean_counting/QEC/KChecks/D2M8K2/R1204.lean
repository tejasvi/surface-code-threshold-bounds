import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4816 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4816 = true := by
  decide +kernel

theorem tot4816 : totK PD2M8K2 D2M8K2.t4816 = [0, 0, 198748190549, 470712493483, 213076898680, 15519847284, 0, 0] := by
  decide +kernel

theorem rows4817 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4817 = true := by
  decide +kernel

theorem tot4817 : totK PD2M8K2 D2M8K2.t4817 = [0, 0, 53166333713, 337975664527, 422416968427, 73463941529, 1107157161, 0] := by
  decide +kernel

theorem rows4818 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4818 = true := by
  decide +kernel

theorem tot4818 : totK PD2M8K2 D2M8K2.t4818 = [0, 0, 49630928717, 298470869804, 414579064636, 106575797533, 3824247485, 0] := by
  decide +kernel

theorem rows4819 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4819 = true := by
  decide +kernel

theorem tot4819 : totK PD2M8K2 D2M8K2.t4819 = [0, 0, 178209359893, 462563701944, 247556354404, 20104377587, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows15104 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15104 = true := by
  decide +kernel

theorem tot15104 : totK PD2M8K2 D2M8K2.t15104 = [0, 164600935416, 477461036318, 253728929205, 14554364620, 0, 0, 0] := by
  decide +kernel

theorem rows15105 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15105 = true := by
  decide +kernel

theorem tot15105 : totK PD2M8K2 D2M8K2.t15105 = [0, 0, 210997780569, 472232215017, 218424413155, 19844998608, 0, 0] := by
  decide +kernel

theorem rows15106 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15106 = true := by
  decide +kernel

theorem tot15106 : totK PD2M8K2 D2M8K2.t15106 = [0, 37176659836, 206111163825, 425007906193, 218292308049, 12173535661, 0, 0] := by
  decide +kernel

theorem rows15107 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15107 = true := by
  decide +kernel

theorem tot15107 : totK PD2M8K2 D2M8K2.t15107 = [0, 190172864723, 463168638819, 244875063656, 21292627170, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

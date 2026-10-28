import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows10016 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10016 = true := by
  decide +kernel

theorem tot10016 : totK PD2M8K2 D2M8K2.t10016 = [0, 0, 181341888804, 470728214825, 254956134546, 12852111409, 0, 0] := by
  decide +kernel

theorem rows10017 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10017 = true := by
  decide +kernel

theorem tot10017 : totK PD2M8K2 D2M8K2.t10017 = [0, 0, 0, 307594509423, 492778420068, 102958536934, 1249641317, 0] := by
  decide +kernel

theorem rows10018 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10018 = true := by
  decide +kernel

theorem tot10018 : totK PD2M8K2 D2M8K2.t10018 = [0, 38616506213, 62149779346, 176051246702, 417000284020, 187837707555, 12680748845, 0] := by
  decide +kernel

theorem rows10019 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10019 = true := by
  decide +kernel

theorem tot10019 : totK PD2M8K2 D2M8K2.t10019 = [0, 174634613023, 445644457914, 274405711930, 29900697905, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

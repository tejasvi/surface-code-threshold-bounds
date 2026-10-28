import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5212 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5212 = true := by
  decide +kernel

theorem tot5212 : totK PD2M8K2 D2M8K2.t5212 = [0, 154847220507, 446860052762, 291478317422, 28323829360, 0, 0, 0] := by
  decide +kernel

theorem rows5213 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5213 = true := by
  decide +kernel

theorem tot5213 : totK PD2M8K2 D2M8K2.t5213 = [0, 158450402117, 449175026427, 260945715136, 22911053741, 0, 0, 0] := by
  decide +kernel

theorem rows5214 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5214 = true := by
  decide +kernel

theorem tot5214 : totK PD2M8K2 D2M8K2.t5214 = [0, 87773917060, 334101364995, 393611911892, 81716141287, 1164319620, 0, 0] := by
  decide +kernel

theorem rows5215 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5215 = true := by
  decide +kernel

theorem tot5215 : totK PD2M8K2 D2M8K2.t5215 = [0, 0, 274365477899, 497468867376, 124550491301, 4234510686, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

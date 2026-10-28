import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6008 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6008 = true := by
  decide +kernel

theorem tot6008 : totK PD2M8K2 D2M8K2.t6008 = [0, 172059349664, 451936824535, 256028376750, 21425536248, 0, 0, 0] := by
  decide +kernel

theorem rows6009 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6009 = true := by
  decide +kernel

theorem tot6009 : totK PD2M8K2 D2M8K2.t6009 = [0, 69605640524, 354342452438, 385506634908, 73946447577, 1096505104, 0, 0] := by
  decide +kernel

theorem rows6010 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6010 = true := by
  decide +kernel

theorem tot6010 : totK PD2M8K2 D2M8K2.t6010 = [0, 7529949136, 261768038439, 494982802283, 127756514093, 3884009855, 0, 0] := by
  decide +kernel

theorem rows6011 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6011 = true := by
  decide +kernel

theorem tot6011 : totK PD2M8K2 D2M8K2.t6011 = [0, 188800526975, 461637229537, 239619211490, 23132058183, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

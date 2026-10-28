import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3964 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3964 = true := by
  decide +kernel

theorem tot3964 : totK PD2M8K2 D2M8K2.t3964 = [0, 0, 186587012855, 469992986685, 222386887908, 17076867616, 0, 0] := by
  decide +kernel

theorem rows3965 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3965 = true := by
  decide +kernel

theorem tot3965 : totK PD2M8K2 D2M8K2.t3965 = [0, 0, 207179302762, 484793507497, 173320046029, 3705122438, 0, 0] := by
  decide +kernel

theorem rows3966 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3966 = true := by
  decide +kernel

theorem tot3966 : totK PD2M8K2 D2M8K2.t3966 = [0, 0, 148801743801, 466615758227, 245913306846, 14211321525, 0, 0] := by
  decide +kernel

theorem rows3967 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3967 = true := by
  decide +kernel

theorem tot3967 : totK PD2M8K2 D2M8K2.t3967 = [0, 0, 0, 310462829730, 459913771459, 66681920151, 1200365979, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

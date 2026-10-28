import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3808 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3808 = true := by
  decide +kernel

theorem tot3808 : totK PD2M8K2 D2M8K2.t3808 = [172178331847, 393011003842, 248183899354, 79385958120, 3884009855, 0, 0, 0] := by
  decide +kernel

theorem rows3809 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3809 = true := by
  decide +kernel

theorem tot3809 : totK PD2M8K2 D2M8K2.t3809 = [161311331899, 449819665369, 277918958542, 23389151863, 0, 0, 0, 0] := by
  decide +kernel

theorem rows3810 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3810 = true := by
  decide +kernel

theorem tot3810 : totK PD2M8K2 D2M8K2.t3810 = [92934196222, 354815718230, 369920533953, 74189062939, 1268739303, 0, 0, 0] := by
  decide +kernel

theorem rows3811 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3811 = true := by
  decide +kernel

theorem tot3811 : totK PD2M8K2 D2M8K2.t3811 = [0, 248648917424, 492450593505, 151315962006, 3696530321, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

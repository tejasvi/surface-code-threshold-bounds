import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4416 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4416 = true := by
  decide +kernel

theorem tot4416 : totK PD2M8K2 D2M8K2.t4416 = [0, 0, 0, 217301143517, 494474804378, 181993174340, 5206224793, 0] := by
  decide +kernel

theorem rows4417 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4417 = true := by
  decide +kernel

theorem tot4417 : totK PD2M8K2 D2M8K2.t4417 = [0, 0, 160196961149, 377033056043, 254720712375, 99465699353, 6524090962, 0] := by
  decide +kernel

theorem rows4418 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4418 = true := by
  decide +kernel

theorem tot4418 : totK PD2M8K2 D2M8K2.t4418 = [0, 0, 177706053037, 445194186223, 262324341427, 25020679946, 0, 0] := by
  decide +kernel

theorem rows4419 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4419 = true := by
  decide +kernel

theorem tot4419 : totK PD2M8K2 D2M8K2.t4419 = [0, 0, 87164468548, 420186741250, 357629597631, 33212563330, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

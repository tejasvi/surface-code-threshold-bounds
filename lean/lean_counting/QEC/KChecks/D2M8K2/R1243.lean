import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4972 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4972 = true := by
  decide +kernel

theorem tot4972 : totK PD2M8K2 D2M8K2.t4972 = [0, 0, 294453194374, 511517883481, 105972467534, 1197396724, 0, 0] := by
  decide +kernel

theorem rows4973 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4973 = true := by
  decide +kernel

theorem tot4973 : totK PD2M8K2 D2M8K2.t4973 = [0, 16886721403, 197708473402, 457706525358, 192458793426, 12040273252, 0, 0] := by
  decide +kernel

theorem rows4974 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4974 = true := by
  decide +kernel

theorem tot4974 : totK PD2M8K2 D2M8K2.t4974 = [0, 197001353059, 458526348223, 243949930982, 23410939074, 0, 0, 0] := by
  decide +kernel

theorem rows4975 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4975 = true := by
  decide +kernel

theorem tot4975 : totK PD2M8K2 D2M8K2.t4975 = [0, 176442680857, 462536457822, 240822172693, 17062814301, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

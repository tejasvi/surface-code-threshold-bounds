import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4232 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4232 = true := by
  decide +kernel

theorem tot4232 : totK PD2M8K2 D2M8K2.t4232 = [0, 0, 0, 142350605717, 466776464707, 261653677216, 9144939981, 0] := by
  decide +kernel

theorem rows4233 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4233 = true := by
  decide +kernel

theorem tot4233 : totK PD2M8K2 D2M8K2.t4233 = [0, 0, 0, 0, 325424784827, 515873817915, 66263611967, 0] := by
  decide +kernel

theorem rows4234 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4234 = true := by
  decide +kernel

theorem tot4234 : totK PD2M8K2 D2M8K2.t4234 = [0, 0, 0, 156583173236, 387014219541, 293565804015, 70451530393, 1392055030] := by
  decide +kernel

theorem rows4235 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4235 = true := by
  decide +kernel

theorem tot4235 : totK PD2M8K2 D2M8K2.t4235 = [0, 0, 0, 181896002300, 442844316289, 243184977483, 14734639880, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows9216 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9216 = true := by
  decide +kernel

theorem tot9216 : totK PD2M8K2 D2M8K2.t9216 = [0, 162995616922, 433551286424, 280388767894, 34153386868, 0, 0, 0] := by
  decide +kernel

theorem rows9217 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9217 = true := by
  decide +kernel

theorem tot9217 : totK PD2M8K2 D2M8K2.t9217 = [0, 179407479527, 450720896658, 232514516326, 16972201627, 0, 0, 0] := by
  decide +kernel

theorem rows9218 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9218 = true := by
  decide +kernel

theorem tot9218 : totK PD2M8K2 D2M8K2.t9218 = [0, 74953324480, 401600363759, 387813343538, 39104325485, 0, 0, 0] := by
  decide +kernel

theorem rows9219 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9219 = true := by
  decide +kernel

theorem tot9219 : totK PD2M8K2 D2M8K2.t9219 = [0, 55679444631, 298074410107, 449570413152, 101518303809, 1415142070, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

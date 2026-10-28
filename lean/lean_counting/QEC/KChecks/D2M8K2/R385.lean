import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1540 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1540 = true := by
  decide +kernel

theorem tot1540 : totK PD2M8K2 D2M8K2.t1540 = [0, 99183643419, 393058435884, 384816789391, 43266028947, 0, 0, 0] := by
  decide +kernel

theorem rows1541 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1541 = true := by
  decide +kernel

theorem tot1541 : totK PD2M8K2 D2M8K2.t1541 = [0, 195174456867, 466723855055, 217771563434, 12287346641, 0, 0, 0] := by
  decide +kernel

theorem rows1542 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1542 = true := by
  decide +kernel

theorem tot1542 : totK PD2M8K2 D2M8K2.t1542 = [0, 33348887533, 312172878020, 431628800682, 127187873549, 4014044760, 0, 0] := by
  decide +kernel

theorem rows1543 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1543 = true := by
  decide +kernel

theorem tot1543 : totK PD2M8K2 D2M8K2.t1543 = [0, 0, 164852411129, 483445867084, 219259312956, 6568891087, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

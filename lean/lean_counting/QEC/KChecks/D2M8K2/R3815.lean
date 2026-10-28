import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows15260 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15260 = true := by
  decide +kernel

theorem tot15260 : totK PD2M8K2 D2M8K2.t15260 = [0, 0, 152301223441, 451954130956, 247879362953, 14841118477, 0, 0] := by
  decide +kernel

theorem rows15261 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15261 = true := by
  decide +kernel

theorem tot15261 : totK PD2M8K2 D2M8K2.t15261 = [0, 0, 86213772900, 345640950313, 368241213226, 80047675890, 1369150432, 0] := by
  decide +kernel

theorem rows15262 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15262 = true := by
  decide +kernel

theorem tot15262 : totK PD2M8K2 D2M8K2.t15262 = [0, 0, 0, 324018790166, 516400841231, 59895596982, 0, 0] := by
  decide +kernel

theorem rows15263 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15263 = true := by
  decide +kernel

theorem tot15263 : totK PD2M8K2 D2M8K2.t15263 = [0, 0, 177761932530, 445893643567, 274212598036, 28832124960, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

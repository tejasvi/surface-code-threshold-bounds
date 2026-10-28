import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows15000 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15000 = true := by
  decide +kernel

theorem tot15000 : totK PD2M8K2 D2M8K2.t15000 = [0, 207179588322, 475177938481, 218653803713, 13901487137, 0, 0, 0] := by
  decide +kernel

theorem rows15001 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15001 = true := by
  decide +kernel

theorem tot15001 : totK PD2M8K2 D2M8K2.t15001 = [0, 99263638057, 420191528683, 345348975029, 43754413764, 0, 0, 0] := by
  decide +kernel

theorem rows15002 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15002 = true := by
  decide +kernel

theorem tot15002 : totK PD2M8K2 D2M8K2.t15002 = [0, 0, 158390534456, 452622947812, 270430212661, 23606272312, 0, 0] := by
  decide +kernel

theorem rows15003 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15003 = true := by
  decide +kernel

theorem tot15003 : totK PD2M8K2 D2M8K2.t15003 = [0, 18548618087, 190595362750, 450811385846, 215942185947, 9199313023, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows13336 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13336 = true := by
  decide +kernel

theorem tot13336 : totK PD2M8K2 D2M8K2.t13336 = [0, 113918511571, 347413481980, 327744571988, 94209099626, 3884009855, 0, 0] := by
  decide +kernel

theorem rows13337 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13337 = true := by
  decide +kernel

theorem tot13337 : totK PD2M8K2 D2M8K2.t13337 = [0, 193156327286, 466699812117, 244931566057, 18748315587, 0, 0, 0] := by
  decide +kernel

theorem rows13338 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13338 = true := by
  decide +kernel

theorem tot13338 : totK PD2M8K2 D2M8K2.t13338 = [0, 19199341347, 313190066892, 458171606888, 95789604180, 1268739303, 0, 0] := by
  decide +kernel

theorem rows13339 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13339 = true := by
  decide +kernel

theorem tot13339 : totK PD2M8K2 D2M8K2.t13339 = [0, 0, 214361571828, 479688712468, 181667578248, 7502349472, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

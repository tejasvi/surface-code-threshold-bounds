import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows14440 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14440 = true := by
  decide +kernel

theorem tot14440 : totK PD2M8K2 D2M8K2.t14440 = [196263446434, 470704128676, 232557543582, 20487174497, 0, 0, 0, 0] := by
  decide +kernel

theorem rows14441 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14441 = true := by
  decide +kernel

theorem tot14441 : totK PD2M8K2 D2M8K2.t14441 = [186902789521, 469021958881, 232051177131, 16847317676, 0, 0, 0, 0] := by
  decide +kernel

theorem rows14442 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14442 = true := by
  decide +kernel

theorem tot14442 : totK PD2M8K2 D2M8K2.t14442 = [0, 283326169765, 499691229818, 117264014279, 1268739303, 0, 0, 0] := by
  decide +kernel

theorem rows14443 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14443 = true := by
  decide +kernel

theorem tot14443 : totK PD2M8K2 D2M8K2.t14443 = [0, 205626186785, 476775289546, 185517250973, 7442000727, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

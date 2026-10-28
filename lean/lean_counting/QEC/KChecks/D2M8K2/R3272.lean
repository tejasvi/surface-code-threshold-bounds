import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows13088 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13088 = true := by
  decide +kernel

theorem tot13088 : totK PD2M8K2 D2M8K2.t13088 = [0, 69943414783, 399809507339, 407760853637, 52328892123, 0, 0, 0] := by
  decide +kernel

theorem rows13089 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13089 = true := by
  decide +kernel

theorem tot13089 : totK PD2M8K2 D2M8K2.t13089 = [0, 53377542744, 233826225990, 433267440734, 158820195817, 9718818700, 0, 0] := by
  decide +kernel

theorem rows13090 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13090 = true := by
  decide +kernel

theorem tot13090 : totK PD2M8K2 D2M8K2.t13090 = [0, 192015081117, 465400126931, 249251557364, 23377943564, 0, 0, 0] := by
  decide +kernel

theorem rows13091 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13091 = true := by
  decide +kernel

theorem tot13091 : totK PD2M8K2 D2M8K2.t13091 = [0, 179825836779, 474400240849, 230848158247, 12491870267, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

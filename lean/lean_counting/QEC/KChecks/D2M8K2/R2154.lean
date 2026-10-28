import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows8616 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8616 = true := by
  decide +kernel

theorem tot8616 : totK PD2M8K2 D2M8K2.t8616 = [0, 183093323046, 472537119598, 214007677153, 10926248329, 0, 0, 0] := by
  decide +kernel

theorem rows8617 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8617 = true := by
  decide +kernel

theorem tot8617 : totK PD2M8K2 D2M8K2.t8617 = [0, 86760124308, 357649509332, 346575097480, 64739452446, 1138244013, 0, 0] := by
  decide +kernel

theorem rows8618 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8618 = true := by
  decide +kernel

theorem tot8618 : totK PD2M8K2 D2M8K2.t8618 = [0, 93463593641, 399682446469, 361666721772, 43316857133, 0, 0, 0] := by
  decide +kernel

theorem rows8619 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8619 = true := by
  decide +kernel

theorem tot8619 : totK PD2M8K2 D2M8K2.t8619 = [0, 172796244951, 451952210718, 253727995987, 18716044004, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows14768 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14768 = true := by
  decide +kernel

theorem tot14768 : totK PD2M8K2 D2M8K2.t14768 = [185599294319, 457416766079, 232340304910, 16603847844, 0, 0, 0, 0] := by
  decide +kernel

theorem rows14769 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14769 = true := by
  decide +kernel

theorem tot14769 : totK PD2M8K2 D2M8K2.t14769 = [71678232178, 345375965980, 406504110122, 86005003355, 1163840124, 0, 0, 0] := by
  decide +kernel

theorem rows14770 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14770 = true := by
  decide +kernel

theorem tot14770 : totK PD2M8K2 D2M8K2.t14770 = [0, 202695888912, 470616129352, 182643144273, 11739479327, 0, 0, 0] := by
  decide +kernel

theorem rows14771 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14771 = true := by
  decide +kernel

theorem tot14771 : totK PD2M8K2 D2M8K2.t14771 = [157475862588, 441332786630, 295533456350, 39356793674, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

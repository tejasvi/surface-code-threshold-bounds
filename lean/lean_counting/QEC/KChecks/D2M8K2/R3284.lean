import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows13136 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13136 = true := by
  decide +kernel

theorem tot13136 : totK PD2M8K2 D2M8K2.t13136 = [0, 87861870204, 336309988985, 377480314213, 86196918416, 1268739303, 0, 0] := by
  decide +kernel

theorem rows13137 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13137 = true := by
  decide +kernel

theorem tot13137 : totK PD2M8K2 D2M8K2.t13137 = [0, 0, 229568246782, 486820692924, 159359459090, 4777472366, 0, 0] := by
  decide +kernel

theorem rows13138 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13138 = true := by
  decide +kernel

theorem tot13138 : totK PD2M8K2 D2M8K2.t13138 = [0, 0, 187247808148, 468330259075, 212137342467, 12889932489, 0, 0] := by
  decide +kernel

theorem rows13139 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13139 = true := by
  decide +kernel

theorem tot13139 : totK PD2M8K2 D2M8K2.t13139 = [0, 0, 205209052758, 474555711982, 187892042436, 9713690252, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

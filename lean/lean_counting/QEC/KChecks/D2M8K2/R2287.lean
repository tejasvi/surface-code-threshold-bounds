import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows9148 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9148 = true := by
  decide +kernel

theorem tot9148 : totK PD2M8K2 D2M8K2.t9148 = [0, 189341840533, 457898689764, 245547662268, 22703940929, 0, 0, 0] := by
  decide +kernel

theorem rows9149 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9149 = true := by
  decide +kernel

theorem tot9149 : totK PD2M8K2 D2M8K2.t9149 = [0, 187618384514, 470354502795, 236431290610, 14681150530, 0, 0, 0] := by
  decide +kernel

theorem rows9150 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9150 = true := by
  decide +kernel

theorem tot9150 : totK PD2M8K2 D2M8K2.t9150 = [0, 38298785186, 322398095498, 439324136789, 100955196395, 1268739303, 0, 0] := by
  decide +kernel

theorem rows9151 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9151 = true := by
  decide +kernel

theorem tot9151 : totK PD2M8K2 D2M8K2.t9151 = [0, 0, 213998812562, 476157247915, 179284433351, 7375937412, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

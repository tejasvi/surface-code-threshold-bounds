import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows13708 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13708 = true := by
  decide +kernel

theorem tot13708 : totK PD2M8K2 D2M8K2.t13708 = [0, 100063523034, 418422187942, 362101593163, 41664021671, 0, 0, 0] := by
  decide +kernel

theorem rows13709 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13709 = true := by
  decide +kernel

theorem tot13709 : totK PD2M8K2 D2M8K2.t13709 = [0, 0, 221461192173, 501925348948, 169534455791, 5284349065, 0, 0] := by
  decide +kernel

theorem rows13710 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13710 = true := by
  decide +kernel

theorem tot13710 : totK PD2M8K2 D2M8K2.t13710 = [0, 189381067429, 465494939280, 239381967340, 20438453452, 0, 0, 0] := by
  decide +kernel

theorem rows13711 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13711 = true := by
  decide +kernel

theorem tot13711 : totK PD2M8K2 D2M8K2.t13711 = [0, 191939272956, 468860205944, 224208092110, 12373752831, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

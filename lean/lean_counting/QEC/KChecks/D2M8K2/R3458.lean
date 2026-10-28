import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows13832 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13832 = true := by
  decide +kernel

theorem tot13832 : totK PD2M8K2 D2M8K2.t13832 = [32101301736, 273124421651, 464486072980, 124195037172, 3884009855, 0, 0, 0] := by
  decide +kernel

theorem rows13833 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13833 = true := by
  decide +kernel

theorem tot13833 : totK PD2M8K2 D2M8K2.t13833 = [186845206938, 460022765116, 251290340914, 23188875746, 0, 0, 0, 0] := by
  decide +kernel

theorem rows13834 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13834 = true := by
  decide +kernel

theorem tot13834 : totK PD2M8K2 D2M8K2.t13834 = [199638018810, 484145550927, 221511772775, 14274039246, 0, 0, 0, 0] := by
  decide +kernel

theorem rows13835 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13835 = true := by
  decide +kernel

theorem tot13835 : totK PD2M8K2 D2M8K2.t13835 = [0, 297448798631, 490807962327, 107985634112, 1268739303, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

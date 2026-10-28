import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows13316 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13316 = true := by
  decide +kernel

theorem tot13316 : totK PD2M8K2 D2M8K2.t13316 = [0, 0, 146334516602, 464273476145, 254821250419, 14711488658, 0, 0] := by
  decide +kernel

theorem rows13317 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13317 = true := by
  decide +kernel

theorem tot13317 : totK PD2M8K2 D2M8K2.t13317 = [0, 0, 0, 304961098356, 469520433940, 80536388459, 1021600638, 0] := by
  decide +kernel

theorem rows13318 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13318 = true := by
  decide +kernel

theorem tot13318 : totK PD2M8K2 D2M8K2.t13318 = [0, 0, 163913406034, 388352341691, 244812414563, 65050678083, 3552795014, 0] := by
  decide +kernel

theorem rows13319 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13319 = true := by
  decide +kernel

theorem tot13319 : totK PD2M8K2 D2M8K2.t13319 = [0, 0, 160854115864, 462573681458, 264746498305, 13732222652, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

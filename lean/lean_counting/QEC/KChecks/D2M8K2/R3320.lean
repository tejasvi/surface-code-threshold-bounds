import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows13280 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13280 = true := by
  decide +kernel

theorem tot13280 : totK PD2M8K2 D2M8K2.t13280 = [0, 0, 165164234039, 443463283205, 271643779964, 29856046845, 0, 0] := by
  decide +kernel

theorem rows13281 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13281 = true := by
  decide +kernel

theorem tot13281 : totK PD2M8K2 D2M8K2.t13281 = [0, 0, 154686816410, 457989960724, 265598084832, 14893601646, 0, 0] := by
  decide +kernel

theorem rows13282 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13282 = true := by
  decide +kernel

theorem tot13282 : totK PD2M8K2 D2M8K2.t13282 = [0, 0, 0, 335088758973, 513393136191, 64679819602, 0, 0] := by
  decide +kernel

theorem rows13283 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13283 = true := by
  decide +kernel

theorem tot13283 : totK PD2M8K2 D2M8K2.t13283 = [0, 0, 140780795527, 348163948948, 339942952063, 89499699228, 1415142070, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

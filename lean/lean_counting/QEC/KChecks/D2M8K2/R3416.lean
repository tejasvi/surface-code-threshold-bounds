import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows13664 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13664 = true := by
  decide +kernel

theorem tot13664 : totK PD2M8K2 D2M8K2.t13664 = [0, 190103674078, 476173828261, 213607235694, 12233076403, 0, 0, 0] := by
  decide +kernel

theorem rows13665 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13665 = true := by
  decide +kernel

theorem tot13665 : totK PD2M8K2 D2M8K2.t13665 = [0, 0, 302677686960, 493066816246, 86985420116, 1107157161, 0, 0] := by
  decide +kernel

theorem rows13666 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13666 = true := by
  decide +kernel

theorem tot13666 : totK PD2M8K2 D2M8K2.t13666 = [0, 86874248361, 328041373993, 354565619532, 96250209673, 3824247485, 0, 0] := by
  decide +kernel

theorem rows13667 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13667 = true := by
  decide +kernel

theorem tot13667 : totK PD2M8K2 D2M8K2.t13667 = [0, 173088082431, 466980928966, 258033161039, 19867753323, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

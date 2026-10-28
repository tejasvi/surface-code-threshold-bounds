import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows13796 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13796 = true := by
  decide +kernel

theorem tot13796 : totK PD2M8K2 D2M8K2.t13796 = [0, 178779249288, 478340499003, 210239277842, 8593247801, 0, 0, 0] := by
  decide +kernel

theorem rows13797 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13797 = true := by
  decide +kernel

theorem tot13797 : totK PD2M8K2 D2M8K2.t13797 = [0, 182735830479, 435959983660, 273946056311, 34179948442, 0, 0, 0] := by
  decide +kernel

theorem rows13798 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13798 = true := by
  decide +kernel

theorem tot13798 : totK PD2M8K2 D2M8K2.t13798 = [0, 175975341861, 467703473052, 253182087728, 12940973730, 0, 0, 0] := by
  decide +kernel

theorem rows13799 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13799 = true := by
  decide +kernel

theorem tot13799 : totK PD2M8K2 D2M8K2.t13799 = [0, 89209449686, 384611968551, 362809944307, 77284800436, 10444649207, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

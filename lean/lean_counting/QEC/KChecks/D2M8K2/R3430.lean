import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows13720 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13720 = true := by
  decide +kernel

theorem tot13720 : totK PD2M8K2 D2M8K2.t13720 = [0, 0, 271062232698, 511967631920, 114956383131, 1232398321, 0, 0] := by
  decide +kernel

theorem rows13721 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13721 = true := by
  decide +kernel

theorem tot13721 : totK PD2M8K2 D2M8K2.t13721 = [0, 24749797672, 210026064783, 448826072810, 190824474887, 12451903996, 0, 0] := by
  decide +kernel

theorem rows13722 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13722 = true := by
  decide +kernel

theorem tot13722 : totK PD2M8K2 D2M8K2.t13722 = [0, 202159416041, 482641849816, 194078129284, 9727964516, 0, 0, 0] := by
  decide +kernel

theorem rows13723 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13723 = true := by
  decide +kernel

theorem tot13723 : totK PD2M8K2 D2M8K2.t13723 = [0, 187320402886, 464509501895, 220844413931, 12534051746, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1052 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1052 = true := by
  decide +kernel

theorem tot1052 : totK PD2M8K2 D2M8K2.t1052 = [0, 197400871312, 468088651385, 210121394267, 14633607569, 0, 0, 0] := by
  decide +kernel

theorem rows1053 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1053 = true := by
  decide +kernel

theorem tot1053 : totK PD2M8K2 D2M8K2.t1053 = [0, 162934238240, 486789184101, 222751304990, 6604758981, 0, 0, 0] := by
  decide +kernel

theorem rows1054 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1054 = true := by
  decide +kernel

theorem tot1054 : totK PD2M8K2 D2M8K2.t1054 = [0, 180065213830, 455526466541, 246883356415, 18246066036, 0, 0, 0] := by
  decide +kernel

theorem rows1055 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1055 = true := by
  decide +kernel

theorem tot1055 : totK PD2M8K2 D2M8K2.t1055 = [0, 211463002411, 473210136194, 195252989001, 7651299259, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

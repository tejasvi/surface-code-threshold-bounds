import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7468 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7468 = true := by
  decide +kernel

theorem tot7468 : totK PD2M8K2 D2M8K2.t7468 = [0, 0, 152671053818, 444703786254, 294820974212, 33840575413, 0, 0] := by
  decide +kernel

theorem rows7469 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7469 = true := by
  decide +kernel

theorem tot7469 : totK PD2M8K2 D2M8K2.t7469 = [0, 0, 181897721859, 456836703905, 243098395111, 15251579877, 0, 0] := by
  decide +kernel

theorem rows7470 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7470 = true := by
  decide +kernel

theorem tot7470 : totK PD2M8K2 D2M8K2.t7470 = [0, 0, 49952704826, 403531825070, 419650109631, 46558653517, 0, 0] := by
  decide +kernel

theorem rows7471 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7471 = true := by
  decide +kernel

theorem tot7471 : totK PD2M8K2 D2M8K2.t7471 = [0, 0, 112859105177, 380400644826, 329911661718, 66318581170, 1444560764, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

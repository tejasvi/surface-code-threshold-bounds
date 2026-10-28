import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows8604 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8604 = true := by
  decide +kernel

theorem tot8604 : totK PD2M8K2 D2M8K2.t8604 = [200004413960, 455391749525, 239711628694, 23259966184, 0, 0, 0, 0] := by
  decide +kernel

theorem rows8605 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8605 = true := by
  decide +kernel

theorem tot8605 : totK PD2M8K2 D2M8K2.t8605 = [146190654994, 464771423578, 265037283687, 14926124038, 0, 0, 0, 0] := by
  decide +kernel

theorem rows8606 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8606 = true := by
  decide +kernel

theorem tot8606 : totK PD2M8K2 D2M8K2.t8606 = [0, 242932943754, 499847611330, 138637493324, 2309606161, 0, 0, 0] := by
  decide +kernel

theorem rows8607 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8607 = true := by
  decide +kernel

theorem tot8607 : totK PD2M8K2 D2M8K2.t8607 = [77829559297, 278396387862, 365742413336, 141995178226, 10740121073, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

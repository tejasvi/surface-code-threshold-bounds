import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1112 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1112 = true := by
  decide +kernel

theorem tot1112 : totK PD2M8K2 D2M8K2.t1112 = [0, 187730870959, 481999965465, 229052632982, 11138249293, 0, 0, 0] := by
  decide +kernel

theorem rows1113 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1113 = true := by
  decide +kernel

theorem tot1113 : totK PD2M8K2 D2M8K2.t1113 = [0, 0, 197238358924, 474084433434, 218593256279, 13604428459, 0, 0] := by
  decide +kernel

theorem rows1114 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1114 = true := by
  decide +kernel

theorem tot1114 : totK PD2M8K2 D2M8K2.t1114 = [0, 63997117283, 289201608155, 427317007712, 127079941136, 1409560813, 0, 0] := by
  decide +kernel

theorem rows1115 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1115 = true := by
  decide +kernel

theorem tot1115 : totK PD2M8K2 D2M8K2.t1115 = [0, 183437946294, 460506480508, 247577123978, 22356072889, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

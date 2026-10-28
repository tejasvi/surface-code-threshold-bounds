import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows10792 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10792 = true := by
  decide +kernel

theorem tot10792 : totK PD2M8K2 D2M8K2.t10792 = [0, 0, 198860451921, 476486880004, 199684546046, 6823367368, 0, 0] := by
  decide +kernel

theorem rows10793 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10793 = true := by
  decide +kernel

theorem tot10793 : totK PD2M8K2 D2M8K2.t10793 = [0, 0, 194612542312, 489028963593, 208311676906, 10177609099, 0, 0] := by
  decide +kernel

theorem rows10794 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10794 = true := by
  decide +kernel

theorem tot10794 : totK PD2M8K2 D2M8K2.t10794 = [0, 0, 169548771529, 467189029061, 241297276828, 13737756793, 0, 0] := by
  decide +kernel

theorem rows10795 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10795 = true := by
  decide +kernel

theorem tot10795 : totK PD2M8K2 D2M8K2.t10795 = [0, 0, 173596481365, 472676666534, 230636192674, 12886908819, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

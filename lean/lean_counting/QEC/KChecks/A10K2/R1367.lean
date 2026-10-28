import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5468 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5468 = true := by
  decide +kernel

theorem tot5468 : totK PA10K2 A10K2.t5468 = [0, 0, 440197684128, 1530663354164, 1774738206118, 871541377056, 151265777404, 5517381808, 0, 0] := by
  decide +kernel

theorem rows5469 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5469 = true := by
  decide +kernel

theorem tot5469 : totK PA10K2 A10K2.t5469 = [0, 0, 330343277720, 1616295034396, 2088430270762, 668984688307, 38254334585, 0, 0, 0] := by
  decide +kernel

theorem rows5470 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5470 = true := by
  decide +kernel

theorem tot5470 : totK PA10K2 A10K2.t5470 = [0, 0, 113610237831, 834391745124, 2078306108649, 1388535869374, 207631459116, 6121173289, 0, 0] := by
  decide +kernel

theorem rows5471 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5471 = true := by
  decide +kernel

theorem tot5471 : totK PA10K2 A10K2.t5471 = [0, 0, 438841284071, 1778398917998, 2066111267146, 632725887115, 32712955001, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2

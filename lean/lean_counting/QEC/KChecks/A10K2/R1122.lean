import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4488 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4488 = true := by
  decide +kernel

theorem tot4488 : totK PA10K2 A10K2.t4488 = [0, 297219227124, 1493618049626, 2163149010636, 881171759741, 76452215278, 0, 0, 0, 0] := by
  decide +kernel

theorem rows4489 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4489 = true := by
  decide +kernel

theorem tot4489 : totK PA10K2 A10K2.t4489 = [0, 191783135589, 969460934626, 2027969492905, 1520816474583, 262171969556, 7047025452, 0, 0, 0] := by
  decide +kernel

theorem rows4490 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4490 = true := by
  decide +kernel

theorem tot4490 : totK PA10K2 A10K2.t4490 = [0, 499711121260, 1913117635923, 2045820086737, 540036634731, 23386015171, 0, 0, 0, 0] := by
  decide +kernel

theorem rows4491 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4491 = true := by
  decide +kernel

theorem tot4491 : totK PA10K2 A10K2.t4491 = [0, 107217811608, 998111890958, 2188029887561, 1485689945859, 250018311430, 6066958478, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2

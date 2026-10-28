import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4324 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4324 = true := by
  decide +kernel

theorem tot4324 : totK PA10K2 A10K2.t4324 = [0, 0, 428345324975, 1713051430078, 2047492540545, 746256312165, 57891163526, 0, 0, 0] := by
  decide +kernel

theorem rows4325 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4325 = true := by
  decide +kernel

theorem tot4325 : totK PA10K2 A10K2.t4325 = [0, 0, 0, 771789550922, 2228166399985, 1716703799807, 259068821043, 6066958478, 0, 0] := by
  decide +kernel

theorem rows4326 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4326 = true := by
  decide +kernel

theorem tot4326 : totK PA10K2 A10K2.t4326 = [0, 0, 426205263052, 1405841022661, 1663520867474, 1037780946310, 366512000438, 28503589898, 0, 0] := by
  decide +kernel

theorem rows4327 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4327 = true := by
  decide +kernel

theorem tot4327 : totK PA10K2 A10K2.t4327 = [0, 0, 437725143181, 1736508596783, 1988047708641, 579015761914, 18905754890, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2

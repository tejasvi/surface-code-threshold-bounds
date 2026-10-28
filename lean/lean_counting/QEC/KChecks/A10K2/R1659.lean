import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6636 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6636 = true := by
  decide +kernel

theorem tot6636 : totK PA10K2 A10K2.t6636 = [0, 0, 302214352193, 1319999755954, 2002055738013, 1135413365388, 192303764509, 6632180018, 0, 0] := by
  decide +kernel

theorem rows6637 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6637 = true := by
  decide +kernel

theorem tot6637 : totK PA10K2 A10K2.t6637 = [0, 0, 477960585112, 1821222164286, 2023211162848, 584791755643, 22464714325, 0, 0, 0] := by
  decide +kernel

theorem rows6638 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6638 = true := by
  decide +kernel

theorem tot6638 : totK PA10K2 A10K2.t6638 = [0, 0, 0, 774862830084, 2218915119458, 1634284679602, 277142603587, 7047025452, 0, 0] := by
  decide +kernel

theorem rows6639 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6639 = true := by
  decide +kernel

theorem tot6639 : totK PA10K2 A10K2.t6639 = [0, 0, 551835803142, 1843466911993, 1834108390857, 666432162611, 62018355555, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2

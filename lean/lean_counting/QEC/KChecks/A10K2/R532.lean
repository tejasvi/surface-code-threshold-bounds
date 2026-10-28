import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2128 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2128 = true := by
  decide +kernel

theorem tot2128 : totK PA10K2 A10K2.t2128 = [0, 525699093747, 1860797210795, 1863179997814, 509263862978, 32523532663, 0, 0, 0, 0] := by
  decide +kernel

theorem rows2129 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2129 = true := by
  decide +kernel

theorem tot2129 : totK PA10K2 A10K2.t2129 = [0, 0, 688273862522, 2066833574924, 1621679710403, 376816154847, 25565504801, 0, 0, 0] := by
  decide +kernel

theorem rows2130 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2130 = true := by
  decide +kernel

theorem tot2130 : totK PA10K2 A10K2.t2130 = [0, 176945644412, 1022751346582, 1995576354155, 1264386194423, 195030227056, 5517381808, 0, 0, 0] := by
  decide +kernel

theorem rows2131 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2131 = true := by
  decide +kernel

theorem tot2131 : totK PA10K2 A10K2.t2131 = [0, 583274707886, 1952159503977, 1792902919544, 452658707648, 26521581199, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2

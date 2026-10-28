import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows800 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t800 = true := by
  decide +kernel

theorem tot800 : totK PA10K2 A10K2.t800 = [15795371065, 526688570041, 1833309925147, 1869294592697, 506332864711, 31768748853, 0, 0, 0, 0] := by
  decide +kernel

theorem rows801 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t801 = true := by
  decide +kernel

theorem tot801 : totK PA10K2 A10K2.t801 = [546409406928, 1945422354925, 1877799954885, 485171845968, 26521581199, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem rows802 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t802 = true := by
  decide +kernel

theorem tot802 : totK PA10K2 A10K2.t802 = [80160914684, 842585320144, 2101238469643, 1455721571551, 248298247518, 6354482628, 0, 0, 0, 0] := by
  decide +kernel

theorem rows803 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t803 = true := by
  decide +kernel

theorem tot803 : totK PA10K2 A10K2.t803 = [558764704281, 1927081002774, 1983583279958, 572685199611, 40218956854, 0, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2

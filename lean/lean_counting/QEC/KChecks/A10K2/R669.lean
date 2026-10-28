import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2676 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2676 = true := by
  decide +kernel

theorem tot2676 : totK PA10K2 A10K2.t2676 = [0, 583209941258, 1888791742621, 1787834858730, 521705926549, 31941609474, 0, 0, 0, 0] := by
  decide +kernel

theorem rows2677 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2677 = true := by
  decide +kernel

theorem tot2677 : totK PA10K2 A10K2.t2677 = [0, 0, 958690266700, 2353146343615, 1219734329929, 107501887502, 0, 0, 0, 0] := by
  decide +kernel

theorem rows2678 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2678 = true := by
  decide +kernel

theorem tot2678 : totK PA10K2 A10K2.t2678 = [0, 0, 517998395676, 1797448005490, 1780531220305, 468149626686, 31558137809, 0, 0, 0] := by
  decide +kernel

theorem rows2679 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2679 = true := by
  decide +kernel

theorem tot2679 : totK PA10K2 A10K2.t2679 = [0, 0, 426850988118, 1778648345232, 2006526180656, 563123227519, 32470938769, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2

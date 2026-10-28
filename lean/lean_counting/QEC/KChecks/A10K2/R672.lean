import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2688 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2688 = true := by
  decide +kernel

theorem tot2688 : totK PA10K2 A10K2.t2688 = [0, 0, 600154090952, 2067549676086, 2029444144917, 476668011732, 13549732798, 0, 0, 0] := by
  decide +kernel

theorem rows2689 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2689 = true := by
  decide +kernel

theorem tot2689 : totK PA10K2 A10K2.t2689 = [0, 0, 589785302968, 1951067284875, 1872236072606, 588378468422, 49180423016, 0, 0, 0] := by
  decide +kernel

theorem rows2690 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2690 = true := by
  decide +kernel

theorem tot2690 : totK PA10K2 A10K2.t2690 = [0, 0, 498848097945, 1892281419917, 2008596226055, 547589525276, 31712524204, 0, 0, 0] := by
  decide +kernel

theorem rows2691 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2691 = true := by
  decide +kernel

theorem tot2691 : totK PA10K2 A10K2.t2691 = [0, 0, 0, 825033391300, 2268777229887, 1573837117605, 257100534830, 7047025452, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2

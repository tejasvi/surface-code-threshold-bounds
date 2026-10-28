import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2316 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2316 = true := by
  decide +kernel

theorem tot2316 : totK PA10K2 A10K2.t2316 = [0, 0, 467092711113, 1834321535813, 1945622245436, 500903412681, 26521581199, 0, 0, 0] := by
  decide +kernel

theorem rows2317 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2317 = true := by
  decide +kernel

theorem tot2317 : totK PA10K2 A10K2.t2317 = [0, 0, 0, 768902431502, 2250759759167, 1366943086377, 122812952568, 0, 0, 0] := by
  decide +kernel

theorem rows2318 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2318 = true := by
  decide +kernel

theorem tot2318 : totK PA10K2 A10K2.t2318 = [0, 0, 0, 633736046354, 1970905721272, 1603500023329, 300043970172, 12477276923, 0, 0] := by
  decide +kernel

theorem rows2319 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2319 = true := by
  decide +kernel

theorem tot2319 : totK PA10K2 A10K2.t2319 = [0, 0, 0, 474044422105, 1780012845361, 1931675464645, 526721247663, 32356135070, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2

import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6364 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6364 = true := by
  decide +kernel

theorem tot6364 : totK PA10K2 A10K2.t6364 = [472607646069, 1515562125216, 1715355369306, 904914286491, 155756991358, 5460492893, 0, 0, 0, 0] := by
  decide +kernel

theorem rows6365 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6365 = true := by
  decide +kernel

theorem tot6365 : totK PA10K2 A10K2.t6365 = [294540382597, 1534553749121, 2182618537751, 837291690641, 71477583721, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem rows6366 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6366 = true := by
  decide +kernel

theorem tot6366 : totK PA10K2 A10K2.t6366 = [0, 460501443971, 1780651931951, 1952273763418, 518139539288, 31768748853, 0, 0, 0, 0] := by
  decide +kernel

theorem rows6367 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6367 = true := by
  decide +kernel

theorem tot6367 : totK PA10K2 A10K2.t6367 = [514073912822, 1747353621303, 1808024655866, 623408249347, 73112029834, 0, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2

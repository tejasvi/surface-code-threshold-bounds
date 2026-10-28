import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows556 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t556 = true := by
  decide +kernel

theorem tot556 : totK PA10K2 A10K2.t556 = [271188200059, 1142169375366, 1862964432376, 1215082863330, 202382054171, 6034215561, 0, 0, 0, 0] := by
  decide +kernel

theorem rows557 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t557 = true := by
  decide +kernel

theorem tot557 : totK PA10K2 A10K2.t557 = [562922406020, 1943553910313, 1776563427724, 446790552894, 26521581199, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem rows558 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t558 = true := by
  decide +kernel

theorem tot558 : totK PA10K2 A10K2.t558 = [0, 958194142018, 2374971824274, 1266205837303, 113943173993, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem rows559 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t559 = true := by
  decide +kernel

theorem tot559 : totK PA10K2 A10K2.t559 = [0, 444810214385, 1814096954471, 1906138593810, 529243218525, 31987755669, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2

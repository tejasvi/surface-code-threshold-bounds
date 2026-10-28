import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6920 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6920 = true := by
  decide +kernel

theorem tot6920 : totK PA10K2 A10K2.t6920 = [0, 0, 0, 502815382469, 1953145971293, 2085530688669, 497762348031, 12746179907, 0, 0] := by
  decide +kernel

theorem rows6921 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6921 = true := by
  decide +kernel

theorem tot6921 : totK PA10K2 A10K2.t6921 = [0, 0, 0, 546262423156, 1814594954333, 1748920078399, 524987953511, 47952069846, 0, 0] := by
  decide +kernel

theorem rows6922 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6922 = true := by
  decide +kernel

theorem tot6922 : totK PA10K2 A10K2.t6922 = [0, 0, 0, 286915412457, 1470103406156, 2133565747435, 830158544413, 60189116917, 0, 0] := by
  decide +kernel

theorem rows6923 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6923 = true := by
  decide +kernel

theorem tot6923 : totK PA10K2 A10K2.t6923 = [0, 0, 0, 244588936042, 1112902294089, 1839160478979, 1215548823672, 243307891724, 7237400819, 0] := by
  decide +kernel

end QECKChecks.A10K2

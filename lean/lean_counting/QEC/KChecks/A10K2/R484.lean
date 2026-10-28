import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1936 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1936 = true := by
  decide +kernel

theorem tot1936 : totK PA10K2 A10K2.t1936 = [0, 0, 0, 493114773009, 1964541947972, 2046039915992, 520506131804, 20419637464, 0, 0] := by
  decide +kernel

theorem rows1937 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1937 = true := by
  decide +kernel

theorem tot1937 : totK PA10K2 A10K2.t1937 = [0, 0, 592533682082, 1972647044070, 1801794533924, 538924263654, 170127830780, 24415340438, 0, 0] := by
  decide +kernel

theorem rows1938 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1938 = true := by
  decide +kernel

theorem tot1938 : totK PA10K2 A10K2.t1938 = [0, 0, 0, 789583169925, 2321059568872, 1628534039381, 268834051254, 7007974415, 0, 0] := by
  decide +kernel

theorem rows1939 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1939 = true := by
  decide +kernel

theorem tot1939 : totK PA10K2 A10K2.t1939 = [0, 0, 516596241516, 1799528959641, 1901082105620, 645683246026, 65192132021, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2

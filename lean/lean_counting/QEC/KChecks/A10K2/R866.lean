import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3464 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3464 = true := by
  decide +kernel

theorem tot3464 : totK PA10K2 A10K2.t3464 = [0, 0, 0, 512235443313, 1855887624867, 1969891007432, 700662924927, 66685948078, 0, 0] := by
  decide +kernel

theorem rows3465 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3465 = true := by
  decide +kernel

theorem tot3465 : totK PA10K2 A10K2.t3465 = [0, 0, 0, 321744867345, 1633842826960, 2231409412781, 777276077903, 54966782002, 0, 0] := by
  decide +kernel

theorem rows3466 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3466 = true := by
  decide +kernel

theorem tot3466 : totK PA10K2 A10K2.t3466 = [0, 0, 0, 0, 528903463648, 2043340430931, 1975783562270, 448420733350, 12926121504, 0] := by
  decide +kernel

theorem rows3467 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3467 = true := by
  decide +kernel

theorem tot3467 : totK PA10K2 A10K2.t3467 = [0, 0, 559138620308, 1904291344300, 1768857189311, 421455006238, 68338061458, 108395117419, 23776135654, 0] := by
  decide +kernel

end QECKChecks.A10K2

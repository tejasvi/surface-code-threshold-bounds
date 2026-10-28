import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4220 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4220 = true := by
  decide +kernel

theorem tot4220 : totK PA10K2 A10K2.t4220 = [0, 0, 694232078717, 2044565904806, 1651992283022, 356128358653, 25336174642, 0, 0, 0] := by
  decide +kernel

theorem rows4221 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4221 = true := by
  decide +kernel

theorem tot4221 : totK PA10K2 A10K2.t4221 = [0, 0, 466247728938, 1815865710026, 1834337187463, 482066930206, 31009878902, 0, 0, 0] := by
  decide +kernel

theorem rows4222 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4222 = true := by
  decide +kernel

theorem tot4222 : totK PA10K2 A10K2.t4222 = [0, 0, 451885222873, 1775592995675, 1866671029930, 472044002939, 25454126167, 0, 0, 0] := by
  decide +kernel

theorem rows4223 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4223 = true := by
  decide +kernel

theorem tot4223 : totK PA10K2 A10K2.t4223 = [0, 0, 0, 804837989135, 2175421918136, 1346968715141, 174073996660, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2

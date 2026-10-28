import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows984 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t984 = true := by
  decide +kernel

theorem tot984 : totK PA10K2 A10K2.t984 = [0, 0, 389585418849, 1400943230319, 1849324523400, 964495216629, 160302285096, 5705019915, 0, 0] := by
  decide +kernel

theorem rows985 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t985 = true := by
  decide +kernel

theorem tot985 : totK PA10K2 A10K2.t985 = [0, 0, 409639837348, 1715201120895, 2124095168689, 766483614941, 57459518695, 0, 0, 0] := by
  decide +kernel

theorem rows986 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t986 = true := by
  decide +kernel

theorem tot986 : totK PA10K2 A10K2.t986 = [0, 0, 0, 698153068079, 2210800784896, 1811108485656, 303590769771, 6853348008, 0, 0] := by
  decide +kernel

theorem rows987 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t987 = true := by
  decide +kernel

theorem tot987 : totK PA10K2 A10K2.t987 = [0, 0, 0, 418741689848, 1685515252574, 2024679833125, 706746423389, 53844901745, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2

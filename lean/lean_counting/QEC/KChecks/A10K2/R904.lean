import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3616 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3616 = true := by
  decide +kernel

theorem tot3616 : totK PA10K2 A10K2.t3616 = [0, 0, 99591570689, 758948951807, 1901501234115, 1546976913650, 323160385984, 10751746851, 0, 0] := by
  decide +kernel

theorem rows3617 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3617 = true := by
  decide +kernel

theorem tot3617 : totK PA10K2 A10K2.t3617 = [0, 0, 521028989575, 1840990270147, 1837636024023, 527140809150, 31936107789, 0, 0, 0] := by
  decide +kernel

theorem rows3618 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3618 = true := by
  decide +kernel

theorem tot3618 : totK PA10K2 A10K2.t3618 = [0, 0, 108061833447, 1256298547315, 2295587574779, 915879302826, 57074442438, 0, 0, 0] := by
  decide +kernel

theorem rows3619 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3619 = true := by
  decide +kernel

theorem tot3619 : totK PA10K2 A10K2.t3619 = [0, 0, 399120657157, 1406764946944, 1862567381679, 1034763410183, 182658087072, 6121173289, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2

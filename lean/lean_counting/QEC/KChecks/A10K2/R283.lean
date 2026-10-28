import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1132 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1132 = true := by
  decide +kernel

theorem tot1132 : totK PA10K2 A10K2.t1132 = [0, 0, 122956571035, 981560108536, 2131574594062, 1505760327441, 241442686755, 6772895877, 0, 0] := by
  decide +kernel

theorem rows1133 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1133 = true := by
  decide +kernel

theorem tot1133 : totK PA10K2 A10K2.t1133 = [0, 0, 0, 607610679297, 2044597336864, 1906194195884, 433582982250, 12773195692, 0, 0] := by
  decide +kernel

theorem rows1134 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1134 = true := by
  decide +kernel

theorem tot1134 : totK PA10K2 A10K2.t1134 = [0, 0, 0, 449454564065, 1647831907113, 1980493677111, 659924688135, 54987531584, 0, 0] := by
  decide +kernel

theorem rows1135 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1135 = true := by
  decide +kernel

theorem tot1135 : totK PA10K2 A10K2.t1135 = [0, 0, 0, 305173462504, 1454190049547, 2156495521110, 947846233224, 75130872869, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2

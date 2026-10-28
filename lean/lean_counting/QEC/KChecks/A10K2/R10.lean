import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows40 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t40 = true := by
  decide +kernel

theorem tot40 : totK PA10K2 A10K2.t40 = [0, 287917824241, 1174141011427, 1934417023204, 1404887742233, 269724252111, 7047025452, 0, 0, 0] := by
  decide +kernel

theorem rows41 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t41 = true := by
  decide +kernel

theorem tot41 : totK PA10K2 A10K2.t41 = [0, 463483746156, 1795739227532, 2028580860839, 557377363146, 22158176621, 0, 0, 0, 0] := by
  decide +kernel

theorem rows42 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t42 = true := by
  decide +kernel

theorem tot42 : totK PA10K2 A10K2.t42 = [0, 84078379084, 932249502321, 2166091783964, 1528004740401, 244634322406, 6066958478, 0, 0, 0] := by
  decide +kernel

theorem rows43 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t43 = true := by
  decide +kernel

theorem tot43 : totK PA10K2 A10K2.t43 = [0, 0, 485070609258, 1881567718266, 1987712733860, 507790924909, 17732757243, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2

import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5848 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5848 = true := by
  decide +kernel

theorem tot5848 : totK PA10K2 A10K2.t5848 = [0, 0, 308748580089, 1221949650243, 1888078361351, 1233087565953, 191032014601, 9556858200, 0, 0] := by
  decide +kernel

theorem rows5849 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5849 = true := by
  decide +kernel

theorem tot5849 : totK PA10K2 A10K2.t5849 = [0, 0, 492075635797, 1844076180686, 1975124895373, 493676756179, 12244162943, 0, 0, 0] := by
  decide +kernel

theorem rows5850 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5850 = true := by
  decide +kernel

theorem tot5850 : totK PA10K2 A10K2.t5850 = [0, 0, 0, 665958666391, 2022650928731, 1647357741749, 356364560401, 25734533292, 0, 0] := by
  decide +kernel

theorem rows5851 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5851 = true := by
  decide +kernel

theorem tot5851 : totK PA10K2 A10K2.t5851 = [0, 0, 311731273616, 1168958640987, 1778927308007, 1239676351082, 208197442680, 6034215561, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2

import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows8032 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t8032 = true := by
  decide +kernel

theorem tot8032 : totK PA10K2 A10K2.t8032 = [0, 0, 0, 0, 542021672012, 1751636344719, 1853773541642, 600355398731, 41568483941, 0] := by
  decide +kernel

theorem rows8033 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t8033 = true := by
  decide +kernel

theorem tot8033 : totK PA10K2 A10K2.t8033 = [0, 0, 0, 0, 286915412457, 1664604753436, 2155144086365, 695416421628, 42147645193, 0] := by
  decide +kernel

theorem rows8034 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t8034 = true := by
  decide +kernel

theorem tot8034 : totK PA10K2 A10K2.t8034 = [0, 0, 0, 0, 282196438792, 1316817393253, 1874610470267, 1103730848246, 199530821045, 7237400819] := by
  decide +kernel

theorem rows8035 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t8035 = true := by
  decide +kernel

theorem tot8035 : totK PA10K2 A10K2.t8035 = [0, 0, 0, 0, 665922782594, 2047167189215, 1767724110514, 337424037871, 12429488139, 0] := by
  decide +kernel

end QECKChecks.A10K2

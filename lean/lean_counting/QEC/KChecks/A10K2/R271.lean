import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1084 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1084 = true := by
  decide +kernel

theorem tot1084 : totK PA10K2 A10K2.t1084 = [0, 457421037211, 1461270672146, 1553125502147, 924998925912, 387989993359, 44535473551, 0, 0, 0] := by
  decide +kernel

theorem rows1085 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1085 = true := by
  decide +kernel

theorem tot1085 : totK PA10K2 A10K2.t1085 = [0, 308706262922, 1517603278100, 2192477011462, 896684596407, 71812324790, 0, 0, 0, 0] := by
  decide +kernel

theorem rows1086 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1086 = true := by
  decide +kernel

theorem tot1086 : totK PA10K2 A10K2.t1086 = [0, 0, 577921111600, 1995420014572, 1837256705591, 425664341304, 17500500512, 0, 0, 0] := by
  decide +kernel

theorem rows1087 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1087 = true := by
  decide +kernel

theorem tot1087 : totK PA10K2 A10K2.t1087 = [0, 578329571249, 1879353226078, 1758443757818, 480207310306, 45358439002, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2

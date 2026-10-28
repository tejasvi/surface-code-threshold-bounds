import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3252 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3252 = true := by
  decide +kernel

theorem tot3252 : totK PA10K2 A10K2.t3252 = [0, 0, 512241865787, 1695820218122, 1922099403708, 767836755600, 70816528984, 0, 0, 0] := by
  decide +kernel

theorem rows3253 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3253 = true := by
  decide +kernel

theorem tot3253 : totK PA10K2 A10K2.t3253 = [0, 0, 323706995196, 1632790062562, 2226933833129, 779540717540, 45148489105, 0, 0, 0] := by
  decide +kernel

theorem rows3254 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3254 = true := by
  decide +kernel

theorem tot3254 : totK PA10K2 A10K2.t3254 = [0, 0, 0, 563090037243, 2008264520028, 1991310434185, 424236037212, 6962742351, 0, 0] := by
  decide +kernel

theorem rows3255 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3255 = true := by
  decide +kernel

theorem tot3255 : totK PA10K2 A10K2.t3255 = [0, 292640272425, 817924421101, 803529751595, 1154863270795, 1367777716662, 522982011448, 41509276794, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2

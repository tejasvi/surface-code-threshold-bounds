import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2608 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2608 = true := by
  decide +kernel

theorem tot2608 : totK PA10K2 A10K2.t2608 = [0, 0, 637854189617, 1977523869352, 1711807078457, 405522610469, 25734533292, 0, 0, 0] := by
  decide +kernel

theorem rows2609 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2609 = true := by
  decide +kernel

theorem tot2609 : totK PA10K2 A10K2.t2609 = [0, 274164759194, 1092391176098, 1864364113244, 1284141106192, 210945390825, 5718040558, 0, 0, 0] := by
  decide +kernel

theorem rows2610 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2610 = true := by
  decide +kernel

theorem tot2610 : totK PA10K2 A10K2.t2610 = [0, 505638907190, 1885892394019, 1899883293769, 479631967939, 26521581199, 0, 0, 0, 0] := by
  decide +kernel

theorem rows2611 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2611 = true := by
  decide +kernel

theorem tot2611 : totK PA10K2 A10K2.t2611 = [0, 0, 872020833137, 2374379223992, 1324121667691, 126927931121, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2

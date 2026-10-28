import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1444 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1444 = true := by
  decide +kernel

theorem tot1444 : totK PA10K2 A10K2.t1444 = [0, 0, 281175129113, 1107622956165, 1915625903740, 1219278525670, 201527888798, 6034215561, 0, 0] := by
  decide +kernel

theorem rows1445 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1445 = true := by
  decide +kernel

theorem tot1445 : totK PA10K2 A10K2.t1445 = [0, 0, 457483169348, 1829887271058, 1911357717778, 468368312013, 26521581199, 0, 0, 0] := by
  decide +kernel

theorem rows1446 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1446 = true := by
  decide +kernel

theorem tot1446 : totK PA10K2 A10K2.t1446 = [0, 0, 0, 735823312185, 2274649959163, 1460908172552, 176744954753, 0, 0, 0] := by
  decide +kernel

theorem rows1447 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1447 = true := by
  decide +kernel

theorem tot1447 : totK PA10K2 A10K2.t1447 = [0, 0, 0, 709537499509, 2075090205368, 1637843118821, 323154676780, 12398919031, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2

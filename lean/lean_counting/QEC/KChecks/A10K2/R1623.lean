import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6492 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6492 = true := by
  decide +kernel

theorem tot6492 : totK PA10K2 A10K2.t6492 = [0, 0, 219800955341, 1114114428618, 2021836893350, 1161825232840, 180624484557, 6121173289, 0, 0] := by
  decide +kernel

theorem rows6493 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6493 = true := by
  decide +kernel

theorem tot6493 : totK PA10K2 A10K2.t6493 = [0, 0, 562864292468, 1935099836749, 1894137976603, 516541657869, 25852139541, 0, 0, 0] := by
  decide +kernel

theorem rows6494 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6494 = true := by
  decide +kernel

theorem tot6494 : totK PA10K2 A10K2.t6494 = [0, 251986720587, 1161689327754, 1737727783520, 1134523833856, 431915677656, 41778035756, 0, 0, 0] := by
  decide +kernel

theorem rows6495 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6495 = true := by
  decide +kernel

theorem tot6495 : totK PA10K2 A10K2.t6495 = [0, 472192280443, 1505563228004, 1732319366863, 908001300949, 155069775601, 5460492893, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2

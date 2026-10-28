import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6760 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6760 = true := by
  decide +kernel

theorem tot6760 : totK PA10K2 A10K2.t6760 = [0, 0, 684257999526, 2196341064206, 1871523168827, 343602594936, 6962742351, 0, 0, 0] := by
  decide +kernel

theorem rows6761 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6761 = true := by
  decide +kernel

theorem tot6761 : totK PA10K2 A10K2.t6761 = [0, 0, 314944826083, 1555822681483, 2134182342887, 792184974545, 60578866985, 0, 0, 0] := by
  decide +kernel

theorem rows6762 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6762 = true := by
  decide +kernel

theorem tot6762 : totK PA10K2 A10K2.t6762 = [0, 0, 522754546307, 1917296138380, 1862587797327, 418995085412, 12917769548, 0, 0, 0] := by
  decide +kernel

theorem rows6763 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6763 = true := by
  decide +kernel

theorem tot6763 : totK PA10K2 A10K2.t6763 = [0, 0, 0, 540828209958, 1910561532954, 1687006297525, 405999952804, 25565504801, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2

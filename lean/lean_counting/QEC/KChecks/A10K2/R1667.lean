import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6668 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6668 = true := by
  decide +kernel

theorem tot6668 : totK PA10K2 A10K2.t6668 = [283695940112, 1236670230272, 1956078644126, 1194280156747, 204298975971, 5459593153, 0, 0, 0, 0] := by
  decide +kernel

theorem rows6669 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6669 = true := by
  decide +kernel

theorem tot6669 : totK PA10K2 A10K2.t6669 = [307169639377, 1467529297539, 2191204772056, 1004519190441, 92014593902, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem rows6670 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6670 = true := by
  decide +kernel

theorem tot6670 : totK PA10K2 A10K2.t6670 = [241559688100, 1037887166592, 1865781262432, 1474201017569, 361728539408, 24852064402, 0, 0, 0, 0] := by
  decide +kernel

theorem rows6671 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6671 = true := by
  decide +kernel

theorem tot6671 : totK PA10K2 A10K2.t6671 = [461203280119, 1804164536542, 2051038910420, 633290686839, 44026900368, 0, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2

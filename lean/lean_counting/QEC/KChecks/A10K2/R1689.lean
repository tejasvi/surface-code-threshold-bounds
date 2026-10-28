import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6756 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6756 = true := by
  decide +kernel

theorem tot6756 : totK PA10K2 A10K2.t6756 = [0, 359830946261, 1512001058545, 2038246605637, 897711691477, 87737304080, 0, 0, 0, 0] := by
  decide +kernel

theorem rows6757 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6757 = true := by
  decide +kernel

theorem tot6757 : totK PA10K2 A10K2.t6757 = [0, 215977270093, 1352532593487, 2138089767645, 919076857900, 72490671888, 0, 0, 0, 0] := by
  decide +kernel

theorem rows6758 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6758 = true := by
  decide +kernel

theorem tot6758 : totK PA10K2 A10K2.t6758 = [0, 488592983112, 1648988456637, 1849517532840, 818519667915, 144088242410, 6239673734, 0, 0, 0] := by
  decide +kernel

theorem rows6759 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6759 = true := by
  decide +kernel

theorem tot6759 : totK PA10K2 A10K2.t6759 = [0, 313255680567, 1490224871918, 2175223461448, 958748936660, 83905303777, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2

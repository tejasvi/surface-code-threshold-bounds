import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows608 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t608 = true := by
  decide +kernel

theorem tot608 : totK PA10K2 A10K2.t608 = [0, 465265226635, 1766124933534, 2013379978208, 573243650226, 32040661968, 0, 0, 0, 0] := by
  decide +kernel

theorem rows609 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t609 = true := by
  decide +kernel

theorem tot609 : totK PA10K2 A10K2.t609 = [0, 16953293394, 761890702757, 2095981253935, 1651210187795, 390450454161, 25371180993, 0, 0, 0] := by
  decide +kernel

theorem rows610 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t610 = true := by
  decide +kernel

theorem tot610 : totK PA10K2 A10K2.t610 = [0, 240242888614, 1113961494366, 1916614444957, 1236592513187, 206267775951, 5460492893, 0, 0, 0] := by
  decide +kernel

theorem rows611 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t611 = true := by
  decide +kernel

theorem tot611 : totK PA10K2 A10K2.t611 = [0, 277892178782, 1369337652779, 2013115192118, 911575549427, 98503173823, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2

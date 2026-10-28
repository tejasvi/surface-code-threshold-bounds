import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4532 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4532 = true := by
  decide +kernel

theorem tot4532 : totK PA10K2 A10K2.t4532 = [0, 815144814916, 2384900981562, 1443606264062, 148861614939, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem rows4533 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4533 = true := by
  decide +kernel

theorem tot4533 : totK PA10K2 A10K2.t4533 = [0, 568361630702, 1858641558430, 1789697932907, 505885504992, 32021558464, 0, 0, 0, 0] := by
  decide +kernel

theorem rows4534 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4534 = true := by
  decide +kernel

theorem tot4534 : totK PA10K2 A10K2.t4534 = [0, 187962517260, 1288106394496, 2260104276003, 1022788326021, 98601352668, 0, 0, 0, 0] := by
  decide +kernel

theorem rows4535 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4535 = true := by
  decide +kernel

theorem tot4535 : totK PA10K2 A10K2.t4535 = [0, 110302630917, 662860629827, 1713702106603, 1647924584397, 456756903813, 30650496230, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2

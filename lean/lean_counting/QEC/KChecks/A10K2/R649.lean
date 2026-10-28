import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2596 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2596 = true := by
  decide +kernel

theorem tot2596 : totK PA10K2 A10K2.t2596 = [0, 422658995009, 1732477375552, 2002331889199, 574572154243, 32470943963, 0, 0, 0, 0] := by
  decide +kernel

theorem rows2597 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2597 = true := by
  decide +kernel

theorem tot2597 : totK PA10K2 A10K2.t2597 = [0, 527851114232, 1843979165005, 1863723585519, 500426049946, 31607162994, 0, 0, 0, 0] := by
  decide +kernel

theorem rows2598 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2598 = true := by
  decide +kernel

theorem tot2598 : totK PA10K2 A10K2.t2598 = [0, 331990957657, 1601989516319, 2061317721586, 644981064888, 51402059204, 0, 0, 0, 0] := by
  decide +kernel

theorem rows2599 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2599 = true := by
  decide +kernel

theorem tot2599 : totK PA10K2 A10K2.t2599 = [0, 101263509156, 861597524407, 2087398278005, 1336086058143, 239904770714, 6354482628, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2

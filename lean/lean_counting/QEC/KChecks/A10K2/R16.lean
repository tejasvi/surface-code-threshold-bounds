import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows64 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t64 = true := by
  decide +kernel

theorem tot64 : totK PA10K2 A10K2.t64 = [0, 424082647602, 1602786081705, 1859999565614, 635525177130, 51466866980, 0, 0, 0, 0] := by
  decide +kernel

theorem rows65 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t65 = true := by
  decide +kernel

theorem tot65 : totK PA10K2 A10K2.t65 = [0, 163013498021, 1305075121798, 2150623470427, 912847836581, 66570755762, 0, 0, 0, 0] := by
  decide +kernel

theorem rows66 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t66 = true := by
  decide +kernel

theorem tot66 : totK PA10K2 A10K2.t66 = [0, 0, 563495938228, 1939324813665, 1713305153192, 410825879661, 26601763172, 0, 0, 0] := by
  decide +kernel

theorem rows67 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t67 = true := by
  decide +kernel

theorem tot67 : totK PA10K2 A10K2.t67 = [0, 0, 487860560708, 1847880013394, 1946133559211, 472595083156, 18304095112, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2

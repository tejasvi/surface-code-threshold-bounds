import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6532 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6532 = true := by
  decide +kernel

theorem tot6532 : totK PA10K2 A10K2.t6532 = [0, 0, 0, 558078711833, 1758458024187, 1672046120436, 462456120629, 31562462749, 0, 0] := by
  decide +kernel

theorem rows6533 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6533 = true := by
  decide +kernel

theorem tot6533 : totK PA10K2 A10K2.t6533 = [0, 0, 0, 118602675526, 1243926590942, 2217481189029, 845340136324, 65132074333, 0, 0] := by
  decide +kernel

theorem rows6534 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6534 = true := by
  decide +kernel

theorem tot6534 : totK PA10K2 A10K2.t6534 = [0, 0, 0, 484964313542, 1551441727701, 1767640384714, 834819664477, 147455037275, 5685526223, 0] := by
  decide +kernel

theorem rows6535 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6535 = true := by
  decide +kernel

theorem tot6535 : totK PA10K2 A10K2.t6535 = [0, 0, 251986720587, 1184703272037, 1817978508690, 1210564916381, 339582169702, 29765180400, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2

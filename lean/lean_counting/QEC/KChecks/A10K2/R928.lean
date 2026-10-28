import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3712 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3712 = true := by
  decide +kernel

theorem tot3712 : totK PA10K2 A10K2.t3712 = [0, 295989007569, 1527843377551, 2080427934521, 804721689732, 60970094597, 0, 0, 0, 0] := by
  decide +kernel

theorem rows3713 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3713 = true := by
  decide +kernel

theorem tot3713 : totK PA10K2 A10K2.t3713 = [0, 0, 728139474928, 2188031059564, 1527769417106, 248335805736, 6354482628, 0, 0, 0] := by
  decide +kernel

theorem rows3714 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3714 = true := by
  decide +kernel

theorem tot3714 : totK PA10K2 A10K2.t3714 = [0, 0, 413035441406, 1705317711814, 1945353456349, 534422374331, 31987876949, 0, 0, 0] := by
  decide +kernel

theorem rows3715 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3715 = true := by
  decide +kernel

theorem tot3715 : totK PA10K2 A10K2.t3715 = [0, 0, 538500661675, 1791502054688, 1857057363491, 518596787625, 32911643181, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2

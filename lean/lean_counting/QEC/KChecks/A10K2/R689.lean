import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2756 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2756 = true := by
  decide +kernel

theorem tot2756 : totK PA10K2 A10K2.t2756 = [0, 0, 0, 690011852747, 2024637580418, 1575737817754, 347539765193, 11866545492, 0, 0] := by
  decide +kernel

theorem rows2757 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2757 = true := by
  decide +kernel

theorem tot2757 : totK PA10K2 A10K2.t2757 = [0, 0, 0, 474247532171, 1675614912586, 1721190842510, 546995764183, 50109395967, 0, 0] := by
  decide +kernel

theorem rows2758 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2758 = true := by
  decide +kernel

theorem tot2758 : totK PA10K2 A10K2.t2758 = [0, 0, 0, 111788177375, 1292084703335, 2194609652463, 876098465187, 77661767533, 0, 0] := by
  decide +kernel

theorem rows2759 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2759 = true := by
  decide +kernel

theorem tot2759 : totK PA10K2 A10K2.t2759 = [317619887890, 1050935918641, 1065760272256, 331048557241, 191861414884, 775996702125, 753116801813, 187952782646, 6354482628, 0] := by
  decide +kernel

end QECKChecks.A10K2

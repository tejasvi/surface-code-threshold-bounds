import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2212 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2212 = true := by
  decide +kernel

theorem tot2212 : totK PA10K2 A10K2.t2212 = [0, 0, 762267175894, 2223116103667, 1638962319306, 255822799416, 6066958478, 0, 0, 0] := by
  decide +kernel

theorem rows2213 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2213 = true := by
  decide +kernel

theorem tot2213 : totK PA10K2 A10K2.t2213 = [0, 114701829058, 556630040580, 1560044021798, 1963147907702, 706752382075, 55043167628, 0, 0, 0] := by
  decide +kernel

theorem rows2214 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2214 = true := by
  decide +kernel

theorem tot2214 : totK PA10K2 A10K2.t2214 = [0, 476899383554, 1823219379998, 2084146858448, 664705090788, 38718230265, 0, 0, 0, 0] := by
  decide +kernel

theorem rows2215 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2215 = true := by
  decide +kernel

theorem tot2215 : totK PA10K2 A10K2.t2215 = [0, 0, 704875190182, 2120924671664, 1708260524780, 392135480642, 25333254304, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2

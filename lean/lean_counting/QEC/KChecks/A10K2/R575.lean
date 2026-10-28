import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2300 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2300 = true := by
  decide +kernel

theorem tot2300 : totK PA10K2 A10K2.t2300 = [0, 0, 278756356567, 1447451494601, 2065320771202, 722885483911, 44995361554, 0, 0, 0] := by
  decide +kernel

theorem rows2301 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2301 = true := by
  decide +kernel

theorem tot2301 : totK PA10K2 A10K2.t2301 = [0, 0, 286756243586, 1168170174704, 1918028329623, 1145131118844, 181589179945, 6239673734, 0, 0] := by
  decide +kernel

theorem rows2302 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2302 = true := by
  decide +kernel

theorem tot2302 : totK PA10K2 A10K2.t2302 = [0, 0, 490690450838, 1822858010133, 2002309604639, 625936958488, 33001472292, 0, 0, 0] := by
  decide +kernel

theorem rows2303 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2303 = true := by
  decide +kernel

theorem tot2303 : totK PA10K2 A10K2.t2303 = [0, 0, 0, 773612675766, 2257936546868, 1703628355436, 303615896789, 6962742351, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2

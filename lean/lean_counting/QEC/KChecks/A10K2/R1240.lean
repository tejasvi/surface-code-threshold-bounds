import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4960 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4960 = true := by
  decide +kernel

theorem tot4960 : totK PA10K2 A10K2.t4960 = [0, 465040202289, 1809974894517, 2055008936104, 597723725271, 31908368213, 0, 0, 0, 0] := by
  decide +kernel

theorem rows4961 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4961 = true := by
  decide +kernel

theorem tot4961 : totK PA10K2 A10K2.t4961 = [0, 0, 662021466416, 2076548674431, 1712973416243, 410683448050, 25660650750, 0, 0, 0] := by
  decide +kernel

theorem rows4962 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4962 = true := by
  decide +kernel

theorem tot4962 : totK PA10K2 A10K2.t4962 = [0, 286877883122, 1233139903281, 1964934707319, 1249075985679, 213681870036, 5624717336, 0, 0, 0] := by
  decide +kernel

theorem rows4963 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4963 = true := by
  decide +kernel

theorem tot4963 : totK PA10K2 A10K2.t4963 = [0, 307923820525, 1489473847821, 2231452956844, 1019954905015, 89335511039, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2

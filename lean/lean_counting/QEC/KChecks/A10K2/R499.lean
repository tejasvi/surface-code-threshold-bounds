import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1996 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1996 = true := by
  decide +kernel

theorem tot1996 : totK PA10K2 A10K2.t1996 = [0, 0, 0, 475557539142, 1785346690282, 2123019418068, 721092439505, 55498468803, 0, 0] := by
  decide +kernel

theorem rows1997 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1997 = true := by
  decide +kernel

theorem tot1997 : totK PA10K2 A10K2.t1997 = [0, 0, 0, 478962976156, 1819686852023, 1876859587508, 464475969915, 25574856276, 0, 0] := by
  decide +kernel

theorem rows1998 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1998 = true := by
  decide +kernel

theorem tot1998 : totK PA10K2 A10K2.t1998 = [0, 0, 0, 296182446550, 1390770955806, 2132106484320, 1041991589960, 103818545408, 0, 0] := by
  decide +kernel

theorem rows1999 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1999 = true := by
  decide +kernel

theorem tot1999 : totK PA10K2 A10K2.t1999 = [0, 0, 0, 278113035350, 1306252655165, 1941872989858, 1053377467082, 198909824444, 7007974415, 0] := by
  decide +kernel

end QECKChecks.A10K2

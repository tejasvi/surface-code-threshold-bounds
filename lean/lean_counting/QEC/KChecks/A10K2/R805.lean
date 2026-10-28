import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3220 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3220 = true := by
  decide +kernel

theorem tot3220 : totK PA10K2 A10K2.t3220 = [0, 0, 321323071444, 1118299933563, 1557731422663, 1340207651623, 523036459355, 41354396063, 0, 0] := by
  decide +kernel

theorem rows3221 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3221 = true := by
  decide +kernel

theorem tot3221 : totK PA10K2 A10K2.t3221 = [0, 0, 552433451379, 1966136740094, 1942335139464, 446973123270, 6239800209, 0, 0, 0] := by
  decide +kernel

theorem rows3222 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3222 = true := by
  decide +kernel

theorem tot3222 : totK PA10K2 A10K2.t3222 = [0, 0, 0, 616585264192, 1996437761165, 1751107409261, 417047799632, 25734533292, 0, 0] := by
  decide +kernel

theorem rows3223 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3223 = true := by
  decide +kernel

theorem tot3223 : totK PA10K2 A10K2.t3223 = [0, 0, 261126451520, 1111879458941, 1861435907163, 1229348692958, 209060818564, 6034215561, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2

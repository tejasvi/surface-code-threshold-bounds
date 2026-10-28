import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2176 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2176 = true := by
  decide +kernel

theorem tot2176 : totK PA10K2 A10K2.t2176 = [432469934381, 1835565643947, 2201324103939, 707859136235, 39006141185, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem rows2177 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2177 = true := by
  decide +kernel

theorem tot2177 : totK PA10K2 A10K2.t2177 = [0, 576594126824, 2017571872044, 2015215316833, 496403014117, 13814455608, 0, 0, 0, 0] := by
  decide +kernel

theorem rows2178 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2178 = true := by
  decide +kernel

theorem tot2178 : totK PA10K2 A10K2.t2178 = [0, 512268134348, 1854809676032, 2003093463526, 631004252098, 49165311630, 0, 0, 0, 0] := by
  decide +kernel

theorem rows2179 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2179 = true := by
  decide +kernel

theorem tot2179 : totK PA10K2 A10K2.t2179 = [0, 294576707289, 1490735842537, 2201668875508, 935482161034, 80656207787, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2

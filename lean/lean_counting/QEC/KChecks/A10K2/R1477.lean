import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5908 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5908 = true := by
  decide +kernel

theorem tot5908 : totK PA10K2 A10K2.t5908 = [0, 631634595252, 2112721657054, 1941684116130, 427479275851, 13731804191, 0, 0, 0, 0] := by
  decide +kernel

theorem rows5909 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5909 = true := by
  decide +kernel

theorem tot5909 : totK PA10K2 A10K2.t5909 = [0, 319265984458, 1525364451917, 2126449820887, 833722112547, 74602166334, 0, 0, 0, 0] := by
  decide +kernel

theorem rows5910 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5910 = true := by
  decide +kernel

theorem tot5910 : totK PA10K2 A10K2.t5910 = [0, 547280950923, 1965149423081, 1892896916587, 432159832334, 12350643961, 0, 0, 0, 0] := by
  decide +kernel

theorem rows5911 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5911 = true := by
  decide +kernel

theorem tot5911 : totK PA10K2 A10K2.t5911 = [0, 0, 639859551730, 2021112801297, 1566511378464, 378128338291, 25239774317, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2

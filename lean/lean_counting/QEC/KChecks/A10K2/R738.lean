import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2952 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2952 = true := by
  decide +kernel

theorem tot2952 : totK PA10K2 A10K2.t2952 = [0, 0, 225546360787, 1219955031048, 2105261873091, 1216323835687, 204943284915, 7151180950, 0, 0] := by
  decide +kernel

theorem rows2953 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2953 = true := by
  decide +kernel

theorem tot2953 : totK PA10K2 A10K2.t2953 = [0, 0, 382064625605, 1503484150867, 1977367951000, 894807462576, 89210995693, 0, 0, 0] := by
  decide +kernel

theorem rows2954 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2954 = true := by
  decide +kernel

theorem tot2954 : totK PA10K2 A10K2.t2954 = [0, 0, 603564565455, 2070878725146, 1899043066079, 414788350543, 12557093595, 0, 0, 0] := by
  decide +kernel

theorem rows2955 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2955 = true := by
  decide +kernel

theorem tot2955 : totK PA10K2 A10K2.t2955 = [0, 113839911969, 551520872563, 1503637291147, 1992898142109, 804011816604, 62632138461, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2

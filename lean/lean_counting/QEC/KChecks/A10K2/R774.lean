import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3096 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3096 = true := by
  decide +kernel

theorem tot3096 : totK PA10K2 A10K2.t3096 = [0, 505607405522, 1811389275625, 1987387994609, 626267903885, 37508694315, 0, 0, 0, 0] := by
  decide +kernel

theorem rows3097 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3097 = true := by
  decide +kernel

theorem tot3097 : totK PA10K2 A10K2.t3097 = [0, 321912618851, 1513484006361, 2199430348180, 961729150674, 88645773718, 0, 0, 0, 0] := by
  decide +kernel

theorem rows3098 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3098 = true := by
  decide +kernel

theorem tot3098 : totK PA10K2 A10K2.t3098 = [0, 0, 568792334827, 2011891879112, 2049420478110, 470173140701, 13814455608, 0, 0, 0] := by
  decide +kernel

theorem rows3099 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3099 = true := by
  decide +kernel

theorem tot3099 : totK PA10K2 A10K2.t3099 = [0, 0, 386964808314, 1598177091381, 2035517246562, 775268596402, 69440933453, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2

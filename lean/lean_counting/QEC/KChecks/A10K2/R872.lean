import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3488 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3488 = true := by
  decide +kernel

theorem tot3488 : totK PA10K2 A10K2.t3488 = [0, 0, 0, 585652742245, 1767454772357, 1675839648635, 718286128979, 149793007230, 6121173289, 0] := by
  decide +kernel

theorem rows3489 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3489 = true := by
  decide +kernel

theorem tot3489 : totK PA10K2 A10K2.t3489 = [0, 0, 409534657359, 1318827229100, 1560931613198, 1094872959099, 387366093033, 30880539485, 0, 0] := by
  decide +kernel

theorem rows3490 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3490 = true := by
  decide +kernel

theorem tot3490 : totK PA10K2 A10K2.t3490 = [0, 0, 173264853015, 1126797680286, 2053897410211, 1088961751002, 168114493952, 5300418178, 0, 0] := by
  decide +kernel

theorem rows3491 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3491 = true := by
  decide +kernel

theorem tot3491 : totK PA10K2 A10K2.t3491 = [0, 0, 299638544946, 1256309395159, 1935120877146, 1064341534378, 155527214473, 5460492893, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2

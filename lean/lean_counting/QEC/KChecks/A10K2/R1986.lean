import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7944 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7944 = true := by
  decide +kernel

theorem tot7944 : totK PA10K2 A10K2.t7944 = [0, 0, 310694887869, 1063432389994, 1561030405672, 1394714954301, 522441368230, 48886019071, 0, 0] := by
  decide +kernel

theorem rows7945 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7945 = true := by
  decide +kernel

theorem tot7945 : totK PA10K2 A10K2.t7945 = [0, 0, 496225942969, 1828790415220, 1916872080251, 477110153799, 25686058060, 0, 0, 0] := by
  decide +kernel

theorem rows7946 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7946 = true := by
  decide +kernel

theorem tot7946 : totK PA10K2 A10K2.t7946 = [0, 0, 0, 726102619510, 2116910035235, 1649608089966, 374139823028, 18469913835, 0, 0] := by
  decide +kernel

theorem rows7947 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7947 = true := by
  decide +kernel

theorem tot7947 : totK PA10K2 A10K2.t7947 = [0, 0, 271056309428, 1180708258361, 1896029893452, 1205748607462, 165836279395, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2

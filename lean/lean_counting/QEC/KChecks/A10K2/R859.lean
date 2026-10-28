import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3436 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3436 = true := by
  decide +kernel

theorem tot3436 : totK PA10K2 A10K2.t3436 = [0, 0, 0, 0, 700177744733, 2069033207634, 1658199095662, 391130765645, 25734533292, 0] := by
  decide +kernel

theorem rows3437 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3437 = true := by
  decide +kernel

theorem tot3437 : totK PA10K2 A10K2.t3437 = [0, 0, 0, 188424944321, 980814335646, 1877374058721, 1327602156957, 225754909527, 6034215561, 0] := by
  decide +kernel

theorem rows3438 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3438 = true := by
  decide +kernel

theorem tot3438 : totK PA10K2 A10K2.t3438 = [0, 0, 0, 522643722622, 1895437952301, 1821963024691, 455614920140, 26521581199, 0, 0] := by
  decide +kernel

theorem rows3439 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3439 = true := by
  decide +kernel

theorem tot3439 : totK PA10K2 A10K2.t3439 = [0, 0, 0, 0, 819677498115, 2312919070516, 1261911015129, 110772721033, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2

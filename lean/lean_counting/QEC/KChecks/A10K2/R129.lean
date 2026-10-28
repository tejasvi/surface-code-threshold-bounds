import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows516 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t516 = true := by
  decide +kernel

theorem tot516 : totK PA10K2 A10K2.t516 = [0, 346978737096, 1323933066419, 1777642211595, 1045053409369, 205859373992, 6034215561, 0, 0, 0] := by
  decide +kernel

theorem rows517 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t517 = true := by
  decide +kernel

theorem tot517 : totK PA10K2 A10K2.t517 = [0, 471379365235, 1823069522850, 1967507024355, 518463396131, 26521581199, 0, 0, 0, 0] := by
  decide +kernel

theorem rows518 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t518 = true := by
  decide +kernel

theorem tot518 : totK PA10K2 A10K2.t518 = [0, 0, 813347740351, 2288999663264, 1393237735311, 142179830753, 0, 0, 0, 0] := by
  decide +kernel

theorem rows519 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t519 = true := by
  decide +kernel

theorem tot519 : totK PA10K2 A10K2.t519 = [0, 0, 556519131556, 1982978844335, 1803426348547, 354557717331, 11740475125, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2

import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows11336 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11336 = true := by
  decide +kernel

theorem tot11336 : totK PD2M8K2 D2M8K2.t11336 = [112602891556, 350532616321, 330979052275, 88942777501, 3462014130, 0, 0, 0] := by
  decide +kernel

theorem rows11337 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11337 = true := by
  decide +kernel

theorem tot11337 : totK PD2M8K2 D2M8K2.t11337 = [170372542719, 440798140939, 274639570268, 30508507079, 0, 0, 0, 0] := by
  decide +kernel

theorem rows11338 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11338 = true := by
  decide +kernel

theorem tot11338 : totK PD2M8K2 D2M8K2.t11338 = [131071623720, 437660732600, 301079151358, 24389192380, 0, 0, 0, 0] := by
  decide +kernel

theorem rows11339 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11339 = true := by
  decide +kernel

theorem tot11339 : totK PD2M8K2 D2M8K2.t11339 = [0, 202549709120, 479519590096, 191238570809, 9668735432, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

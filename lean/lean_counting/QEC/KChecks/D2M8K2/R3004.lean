import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows12016 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12016 = true := by
  decide +kernel

theorem tot12016 : totK PD2M8K2 D2M8K2.t12016 = [84746240308, 344150144040, 362889699976, 96347848438, 3579068459, 0, 0, 0] := by
  decide +kernel

theorem rows12017 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12017 = true := by
  decide +kernel

theorem tot12017 : totK PD2M8K2 D2M8K2.t12017 = [182892134542, 451111993946, 260858416535, 27396069883, 0, 0, 0, 0] := by
  decide +kernel

theorem rows12018 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12018 = true := by
  decide +kernel

theorem tot12018 : totK PD2M8K2 D2M8K2.t12018 = [157134559685, 455666089601, 283491420610, 23459543939, 0, 0, 0, 0] := by
  decide +kernel

theorem rows12019 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12019 = true := by
  decide +kernel

theorem tot12019 : totK PD2M8K2 D2M8K2.t12019 = [0, 226231060747, 493404231580, 160669017086, 3346911662, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7400 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7400 = true := by
  decide +kernel

theorem tot7400 : totK PD2M8K2 D2M8K2.t7400 = [0, 0, 87012357285, 425593306567, 355464979448, 31758729002, 0, 0] := by
  decide +kernel

theorem rows7401 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7401 = true := by
  decide +kernel

theorem tot7401 : totK PD2M8K2 D2M8K2.t7401 = [0, 0, 0, 226548417142, 476570957266, 156591444617, 5757108999, 0] := by
  decide +kernel

theorem rows7402 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7402 = true := by
  decide +kernel

theorem tot7402 : totK PD2M8K2 D2M8K2.t7402 = [0, 0, 185694729029, 462542439943, 239075121693, 19635349523, 0, 0] := by
  decide +kernel

theorem rows7403 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7403 = true := by
  decide +kernel

theorem tot7403 : totK PD2M8K2 D2M8K2.t7403 = [0, 0, 210170911542, 477971334891, 197564183062, 11069098114, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7444 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7444 = true := by
  decide +kernel

theorem tot7444 : totK PD2M8K2 D2M8K2.t7444 = [0, 90286224711, 364155909723, 364540207156, 98192051263, 12085682572, 0, 0] := by
  decide +kernel

theorem rows7445 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7445 = true := by
  decide +kernel

theorem tot7445 : totK PD2M8K2 D2M8K2.t7445 = [0, 0, 172768270916, 457571944491, 244833177386, 15101123450, 0, 0] := by
  decide +kernel

theorem rows7446 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7446 = true := by
  decide +kernel

theorem tot7446 : totK PD2M8K2 D2M8K2.t7446 = [0, 32420786283, 197738238699, 442517495556, 221504680702, 9355690997, 0, 0] := by
  decide +kernel

theorem rows7447 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7447 = true := by
  decide +kernel

theorem tot7447 : totK PD2M8K2 D2M8K2.t7447 = [0, 182661573655, 460484387755, 251275245114, 23219762177, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

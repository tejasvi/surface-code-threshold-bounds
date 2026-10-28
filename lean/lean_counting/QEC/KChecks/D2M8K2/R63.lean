import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows252 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t252 = true := by
  decide +kernel

theorem tot252 : totK PD2M8K2 D2M8K2.t252 = [0, 169338310327, 459143446833, 250551082132, 20685904848, 0, 0, 0] := by
  decide +kernel

theorem rows253 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t253 = true := by
  decide +kernel

theorem tot253 : totK PD2M8K2 D2M8K2.t253 = [0, 155970370575, 450400147311, 266156663348, 21563895155, 0, 0, 0] := by
  decide +kernel

theorem rows254 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t254 = true := by
  decide +kernel

theorem tot254 : totK PD2M8K2 D2M8K2.t254 = [0, 0, 232499548936, 497858334260, 139797528333, 5643975823, 0, 0] := by
  decide +kernel

theorem rows255 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t255 = true := by
  decide +kernel

theorem tot255 : totK PD2M8K2 D2M8K2.t255 = [0, 84858698819, 291672033292, 370315969576, 116376297003, 7339473973, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

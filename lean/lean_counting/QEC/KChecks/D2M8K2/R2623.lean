import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows10492 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10492 = true := by
  decide +kernel

theorem tot10492 : totK PD2M8K2 D2M8K2.t10492 = [0, 0, 163143617569, 428836978795, 277787668688, 30699408637, 0, 0] := by
  decide +kernel

theorem rows10493 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10493 = true := by
  decide +kernel

theorem tot10493 : totK PD2M8K2 D2M8K2.t10493 = [0, 0, 89753051296, 369205409053, 372409126665, 64417239080, 1198073392, 0] := by
  decide +kernel

theorem rows10494 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10494 = true := by
  decide +kernel

theorem tot10494 : totK PD2M8K2 D2M8K2.t10494 = [0, 0, 0, 248847176115, 492836101208, 153393621970, 8466643012, 0] := by
  decide +kernel

theorem rows10495 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10495 = true := by
  decide +kernel

theorem tot10495 : totK PD2M8K2 D2M8K2.t10495 = [0, 0, 175321203414, 461739814885, 255662607829, 27039656579, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

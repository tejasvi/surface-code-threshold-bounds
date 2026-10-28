import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4612 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4612 = true := by
  decide +kernel

theorem tot4612 : totK PD2M8K2 D2M8K2.t4612 = [0, 0, 180303216061, 450107214893, 266295052743, 28364878616, 0, 0] := by
  decide +kernel

theorem rows4613 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4613 = true := by
  decide +kernel

theorem tot4613 : totK PD2M8K2 D2M8K2.t4613 = [0, 0, 159717237938, 461863181041, 266397745453, 15707642835, 0, 0] := by
  decide +kernel

theorem rows4614 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4614 = true := by
  decide +kernel

theorem tot4614 : totK PD2M8K2 D2M8K2.t4614 = [0, 0, 0, 222158235264, 490619998216, 157918591212, 7166294683, 0] := by
  decide +kernel

theorem rows4615 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4615 = true := by
  decide +kernel

theorem tot4615 : totK PD2M8K2 D2M8K2.t4615 = [0, 0, 65793408479, 286274437422, 392182513840, 122179943011, 5883432551, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

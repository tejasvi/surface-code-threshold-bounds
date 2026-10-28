import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows12848 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12848 = true := by
  decide +kernel

theorem tot12848 : totK PD2M8K2 D2M8K2.t12848 = [0, 0, 183757940624, 463656001412, 249545753879, 18246066036, 0, 0] := by
  decide +kernel

theorem rows12849 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12849 = true := by
  decide +kernel

theorem tot12849 : totK PD2M8K2 D2M8K2.t12849 = [0, 0, 212430303932, 488455184490, 186400204629, 6513038604, 0, 0] := by
  decide +kernel

theorem rows12850 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12850 = true := by
  decide +kernel

theorem tot12850 : totK PD2M8K2 D2M8K2.t12850 = [0, 0, 193518303532, 483511101211, 220184561203, 11066126582, 0, 0] := by
  decide +kernel

theorem rows12851 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12851 = true := by
  decide +kernel

theorem tot12851 : totK PD2M8K2 D2M8K2.t12851 = [0, 0, 155539840785, 461328074366, 257559595176, 15069217834, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

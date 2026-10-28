import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows15448 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15448 = true := by
  decide +kernel

theorem tot15448 : totK PD2M8K2 D2M8K2.t15448 = [0, 179799707541, 452017421217, 266495189826, 27963012741, 0, 0, 0] := by
  decide +kernel

theorem rows15449 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15449 = true := by
  decide +kernel

theorem tot15449 : totK PD2M8K2 D2M8K2.t15449 = [0, 155451780030, 452485864595, 270833587372, 18395502662, 0, 0, 0] := by
  decide +kernel

theorem rows15450 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15450 = true := by
  decide +kernel

theorem tot15450 : totK PD2M8K2 D2M8K2.t15450 = [0, 0, 250328322436, 481808011590, 153951094649, 8470662040, 0, 0] := by
  decide +kernel

theorem rows15451 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15451 = true := by
  decide +kernel

theorem tot15451 : totK PD2M8K2 D2M8K2.t15451 = [0, 108818674509, 349588951392, 341169152856, 90448568734, 3581949829, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

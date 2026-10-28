import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows15728 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15728 = true := by
  decide +kernel

theorem tot15728 : totK PD2M8K2 D2M8K2.t15728 = [0, 0, 0, 203734180743, 469879219108, 188726454705, 11885407614, 0] := by
  decide +kernel

theorem rows15729 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15729 = true := by
  decide +kernel

theorem tot15729 : totK PD2M8K2 D2M8K2.t15729 = [0, 0, 166775602658, 441397672749, 266011450819, 29579721341, 0, 0] := by
  decide +kernel

theorem rows15730 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15730 = true := by
  decide +kernel

theorem tot15730 : totK PD2M8K2 D2M8K2.t15730 = [0, 0, 175443273707, 434582770052, 260174975386, 18760483253, 0, 0] := by
  decide +kernel

theorem rows15731 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15731 = true := by
  decide +kernel

theorem tot15731 : totK PD2M8K2 D2M8K2.t15731 = [0, 0, 52880128529, 345384701670, 396626103789, 66998487088, 1062926506, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

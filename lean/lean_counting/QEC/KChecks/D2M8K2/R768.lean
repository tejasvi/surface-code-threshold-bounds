import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3072 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3072 = true := by
  decide +kernel

theorem tot3072 : totK PD2M8K2 D2M8K2.t3072 = [0, 0, 200706061277, 474209088247, 194647784776, 10901505393, 0, 0] := by
  decide +kernel

theorem rows3073 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3073 = true := by
  decide +kernel

theorem tot3073 : totK PD2M8K2 D2M8K2.t3073 = [0, 0, 182104637332, 471702229056, 213610254392, 12370590376, 0, 0] := by
  decide +kernel

theorem rows3074 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3074 = true := by
  decide +kernel

theorem tot3074 : totK PD2M8K2 D2M8K2.t3074 = [0, 0, 243310392128, 478574036748, 149739803366, 4940120826, 0, 0] := by
  decide +kernel

theorem rows3075 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3075 = true := by
  decide +kernel

theorem tot3075 : totK PD2M8K2 D2M8K2.t3075 = [0, 0, 204984003518, 480713778486, 169607137598, 5072912408, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
